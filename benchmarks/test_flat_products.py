"""Material integrity/gate boundaries; no compiler builds or timing trials."""
import copy
import gzip
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
import flat_products as bench


class FlatProductIntegrity(unittest.TestCase):
    def test_existing_gate_mutations_and_independent_oracles(self):
        result=bench.self_test()
        self.assertEqual(result['pure_gate_mutations_rejected'],5)
        self.assertEqual(result['external_workloads_invoked'],0)
        expected=bench.strict_json((bench.HERE/'cases/flat-products/tuples/manifest.json').read_text())['expression_gates'][1]['expected']
        mutant=copy.deepcopy(expected);mutant['value'][1]=1;mutant['value'][4]=0
        with self.assertRaises(bench.GateFailure):bench.require_json(json.dumps(mutant),expected,'numeric values cannot stand in for booleans')

    def test_complete_checkout_boundary(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);(root/'src').mkdir()
            content={'Cargo.toml':b'[package]','Cargo.lock':b'locked','rust-toolchain.toml':b'pinned','src/lib.rs':b'pub fn entry() {}'}
            for name,data in content.items():(root/name).write_bytes(data)
            expected={name:hashlib.sha256(data).hexdigest() for name,data in content.items()}
            absent=['build.rs','.cargo','rust-toolchain']
            bench.check_checkout(root,expected,absent)
            for name in ['build.rs','rust-toolchain','src/unlisted.rs']:
                with self.subTest(unexpected=name):
                    path=root/name;path.write_text('changed')
                    with self.assertRaises(bench.GateFailure):bench.check_checkout(root,expected,absent)
                    path.unlink()
            (root/'.cargo').mkdir();(root/'.cargo/config.toml').write_text('[build]')
            with self.assertRaises(bench.GateFailure):bench.check_checkout(root,expected,absent)
            (root/'.cargo/config.toml').unlink();(root/'.cargo').rmdir()
            (root/'src/lib.rs').unlink()
            with self.assertRaises(bench.GateFailure):bench.check_checkout(root,expected,absent)
            (root/'src/lib.rs').symlink_to(root/'Cargo.toml')
            with self.assertRaises(bench.GateFailure):bench.check_checkout(root,expected,absent)

    def test_retained_recipe_rejects_different_work(self):
        for singleton in (False,True):
            core=bench.retained_core(singleton)
            self.assertEqual(bench.retained_slot_bound(core),16448)
            core['functions'][1]['body']['arguments'][0]['value']='62'
            with self.assertRaises(bench.GateFailure):bench.retained_slot_bound(core)

    def test_all_official_records_and_corruption(self):
        with gzip.open(bench.HERE/'results/flat-products-macos-arm64.json.gz','rt') as stream:raw=json.load(stream)
        index=json.loads((bench.HERE/'results/flat-products-run-index.json').read_text())
        self.assertEqual(bench.audit_historical(raw,index)['runs'],10)
        name=next(iter(raw['runs']));removed=raw['runs'].pop(name)
        with self.assertRaises(bench.GateFailure):bench.audit_historical(raw,index)
        raw['runs'][name]=removed
        removed['report']['jobs'][0]['samples']['baseline'][0]['wall_ns']+=1
        with self.assertRaises(bench.GateFailure):bench.audit_historical(raw,index)

    def test_measured_controller_is_preserved(self):
        with gzip.open(bench.HERE/'results/flat-products-measurement-snapshot.json.gz','rt') as stream:snapshot=json.load(stream)
        public=Path(bench.__file__).read_text()
        def between(text,start,end):return text[text.index(start):text.index(end,text.index(start))]
        execute=between(public,'def execute(',"\ndef command(").replace('relative_to(OUTPUT)','relative_to(P)')
        rounds=between(public,"            report['round_load_average']=[]","            review=[")
        for historical in snapshot['historical_controllers'].values():
            text=historical['text']
            self.assertEqual(execute,between(text,'def execute(',"\ndef command("))
            self.assertEqual(rounds,between(text,"            report['round_load_average']=[]","            review=["))


if __name__=='__main__':unittest.main()
