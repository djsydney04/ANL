"""Bounded child capture with retained partial output and failure metadata."""
from pathlib import Path
import hashlib,json,os,selectors,signal,subprocess,time
from oracle import Failure,Inconclusive,need,sha
HERE=Path(__file__).resolve().parent
CONTROLS=("ANL_MEMORY_TRACE","ANL_MEMORY_REPLAY")
def save(path,value):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(value,sort_keys=True,indent=2)+"\n")
class Runner:
    def __init__(self, root, manifest):
        self.root = root
        self.manifest = manifest
        self.count = 0
        self.records = []
        self.environment = os.environ.copy()
        for key in CONTROLS:
            self.environment.pop(key, None)
        for key in list(self.environment):
            if key.startswith("ANL_CORPUS_"):
                self.environment.pop(key, None)

    def run(self, label, argv, env=None, timeout=None, stdout_limit=None, poll=None):
        self.count += 1
        folder = self.root / "commands" / f"{self.count:04d}-{label}"
        folder.mkdir(parents=True, exist_ok=False)
        environment = self.environment.copy()
        for key, value in (env or {}).items():
            if value is None:
                environment.pop(key, None)
            else:
                environment[key] = str(value)
        timeout = timeout or self.manifest["command_timeout_seconds"]
        limits = dict(stdout=stdout_limit or self.manifest["stdout_limit"],
                      stderr=self.manifest["stderr_limit"])
        captured = {name:bytearray() for name in limits}
        command = [str(x) for x in argv]
        metadata = dict(argv=command, cwd=str(HERE), timeout_seconds=timeout,
                        limits=limits, environment_changes={k:(None if v is None else str(v))
                                                           for k,v in (env or {}).items()},
                        complete=False, exit=None)
        save(folder / "command.json", metadata)
        process = None
        selector = selectors.DefaultSelector()
        problem = None
        try:
            process = subprocess.Popen(command, cwd=HERE, env=environment, stdin=subprocess.DEVNULL,
                                       stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                       start_new_session=True)
            for name, pipe in (("stdout",process.stdout),("stderr",process.stderr)):
                selector.register(pipe, selectors.EVENT_READ, name)
            deadline = time.monotonic() + timeout
            while selector.get_map():
                if poll:
                    poll()
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    raise Inconclusive("external command deadline exceeded")
                for key, _ in selector.select(min(0.05, remaining)):
                    chunk = os.read(key.fileobj.fileno(), 65536)
                    if not chunk:
                        selector.unregister(key.fileobj)
                        continue
                    name = key.data
                    room = limits[name] + 1 - len(captured[name])
                    captured[name].extend(chunk[:max(room,0)])
                    if len(captured[name]) > limits[name]:
                        raise Inconclusive(name + " external capture bound exceeded")
            if poll:
                poll()
            process.wait(timeout=max(0.01,deadline-time.monotonic()))
            metadata["exit"] = process.returncode
            metadata["complete"] = True
            if process.returncode < 0:
                raise Inconclusive("child terminated by signal")
        except (Exception, KeyboardInterrupt) as error:
            problem = error
            metadata["failure"] = str(error)
            if process is not None:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                try:process.wait(timeout=3)
                except subprocess.TimeoutExpired:metadata["reap_failure"]=True
                metadata["exit"] = process.returncode
        finally:
            selector.close()
            if process is not None:
                for pipe in (process.stdout,process.stderr):
                    if pipe:
                        pipe.close()
            for name, data in captured.items():
                (folder / name).write_bytes(data)
                metadata[name+"_sha256"] = sha(data)
                metadata[name+"_bytes"] = len(data)
            save(folder / "command.json", metadata)
            self.records.append(str(folder.relative_to(self.root)))
        if problem:
            kind=Inconclusive if isinstance(problem,(Inconclusive,subprocess.TimeoutExpired,KeyboardInterrupt)) else Failure
            raise kind(label + ": " + str(problem))
        return dict(exit=metadata["exit"], stdout=bytes(captured["stdout"]),
                    stderr=bytes(captured["stderr"]), folder=folder)

