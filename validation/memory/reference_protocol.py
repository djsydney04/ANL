"""Strict bounded reference-driver report validation."""
import json
import re
import oracle as O
STATUSES = {'value': 0, 'trap': 2, 'resource_limit': 3, 'transition_limit': 5,
            'rejected': 1, 'error': 4}
LIMITS = {'depth', 'expression_fuel', 'slots', 'live_cells', 'fill_fuel', 'tuple_fields'}
ADMIN_REASON = 'administrative transition budget exhausted'
ERROR_PREFIXES = ('usage', 'invalid_path_argument', 'invalid_fuel_argument',
    'invalid_transition_argument', 'core_input_limit', 'response_plan_input_limit',
    'core_io_error', 'response_plan_io_error', 'decoder_error', 'internal_start_error',
    'internal_state_error', 'trace_event_limit', 'output_byte_limit', 'output_io_error')
OUTER_KEYS = ('schema', 'status', 'semantic_revision', 'allocation_profile', 'fuel',
              'transition_budget', 'resource_reason', 'reason', 'meter', 'trace')
METER_CAPS = {'active_slots': 65536, 'live_cells': 1048576,
              'tuple_fields': 1048576, 'expression_depth': 256}


def reason_prefix(reason, allowed):
    O.need(any(reason == p or reason.startswith(p + ': ') for p in allowed), 'unknown diagnostic prefix')


def strict_report(data):
    # All unquoted numbers in this output protocol are profile/site uint64s.
    # json.loads otherwise normalizes -0 to 0 before the existing typed oracle.
    def members(pairs):
        result = {}
        for key, value in pairs:
            O.need(key not in result, 'duplicate JSON member: ' + key)
            result[key] = value
        return result
    def natural(text):
        O.need(len(text) <= 20 and re.fullmatch(r'(0|[1-9][0-9]*)', text) is not None,
               'noncanonical unquoted natural')
        value = int(text)
        O.need(value < 2**64, 'unquoted natural exceeds uint64')
        return value
    def noninteger(text):
        raise O.Failure('non-natural JSON number: ' + text)
    return json.loads(data.decode('utf-8', errors='strict'), object_pairs_hook=members,
                      parse_int=natural, parse_float=noninteger, parse_constant=noninteger)


def meter(value, row):
    O.keys(value, ('fuel_remaining', *METER_CAPS))
    numbers = {k: O.decimal(v) for k, v in value.items()}
    O.need(numbers['fuel_remaining'] <= row['fuel'], 'remaining fuel exceeds supplied fuel')
    for key, cap in METER_CAPS.items():
        O.need(numbers[key] <= cap, 'meter exceeds ' + key + ' bound')
    return numbers


def live_projection(events):
    """One final bounded scan; trace shape/LIFO pairing was checked already."""
    owners = []
    cells = 0
    for event in events:
        if event['kind'] == 'request' and event['response'] == 'success':
            size = int(event['length'])
            owners.append(size)
            cells += size
        elif event['kind'] == 'empty_open':
            owners.append(0)
        elif event['kind'] in ('release', 'empty_close'):
            cells -= owners.pop()
    return len(owners), cells


def protocol(record, row, sites):
    """Invalid/incomplete protocol is incomplete evidence, never a passing row."""
    try:
        O.need(type(record['exit']) is int and record['exit'] in STATUSES.values(), 'unknown exit code')
        O.need(type(record['stderr']) is bytes and not record['stderr'], 'unexpected stderr')
        data = record['stdout']
        O.need(type(data) is bytes and 0 < len(data) <= 8388608, 'stdout capture bound or missing output')
        O.need(data.startswith(b'{') and data.endswith(b'}\n'), 'require exactly one object and final LF')
        report = strict_report(data[:-1])
        O.keys(report, OUTER_KEYS)
        O.need(report['schema'] == 'anl-memory-reference-run-v1', 'outer schema')
        O.need(report['semantic_revision'] == O.REVISION, 'outer revision')
        status = report['status']
        O.need(type(status) is str and status in STATUSES, 'unknown status')
        O.need(record['exit'] == STATUSES[status], 'status/exit disagreement')
        O.need(O.decimal(report['fuel']) == row['fuel'], 'reported invocation fuel differs')
        O.need(O.decimal(report['transition_budget']) == row['transitions'], 'reported transition budget differs')
        reason = report['reason']
        O.need(type(reason) is str and len(reason.encode('utf-8')) <= 1024, 'reason byte bound/type')
        profile = report['allocation_profile']
        if profile is not None:
            O.profile(profile)
            O.need(O.same(profile, row['profile']), 'checked profile differs from input')
        numbers = None if report['meter'] is None else meter(report['meter'], row)
        O.need(numbers is None or profile is not None, 'meter before checked profile')
        if status != 'resource_limit':
            O.need(report['resource_reason'] is None, 'resource reason on non-resource status')
        if status in ('rejected', 'error'):
            O.need(report['trace'] is None, 'trace on rejected/error report')
            if status == 'rejected':
                O.need(numbers is None, 'rejected report has meter')
                reason_prefix(reason, ('core_invalid', 'response_plan_invalid'))
                if row['status'] == 'rejected':
                    O.need(profile is None and reason.startswith('core_invalid'), 'invalid Core claimed checked profile/plan rejection')
            else:
                reason_prefix(reason, ERROR_PREFIXES)
            return report
        O.need(profile is not None and numbers is not None and report['trace'] is not None, 'run report has null projection')
        trace = O.validate_trace(report['trace'], profile, sites)
        O.need(len(trace['events']) <= row['transitions'], 'trace grows faster than transition budget')
        owners, cells = live_projection(trace['events'])
        O.need(numbers['live_cells'] == cells, 'meter/live trace cells disagree')
        O.need(numbers['active_slots'] >= owners, 'meter has fewer slots than live owners')
        completion = trace['completion']
        if status in ('value', 'trap'):
            O.need(reason == '' and completion['kind'] == status, 'terminal completion/reason mismatch')
            if status == 'value':
                O.need(numbers['active_slots'] == 0 and cells == 0, 'normal completion retains reservations')
        elif status == 'resource_limit':
            limit = report['resource_reason']
            O.need(type(limit) is str and limit in LIMITS and reason == limit, 'resource reason mismatch')
            O.need(O.same(completion, {'kind': 'resource_limit'}), 'resource completion mismatch')
        else:
            O.need(reason == ADMIN_REASON and O.same(completion, {'kind': 'infrastructure', 'reason': ADMIN_REASON}),
                   'administrative completion/reason mismatch')
        return report
    except (O.Failure, ValueError, TypeError, KeyError, RecursionError, OverflowError) as error:
        raise O.Inconclusive('malformed/incomplete reference protocol: ' + str(error)) from error


