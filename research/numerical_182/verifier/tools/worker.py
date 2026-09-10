"""Execute one frozen producer; relocate JSON paths, never numerical values/hashes."""
import json, os, runpy, sys, traceback
from pathlib import Path

job = json.loads(Path(sys.argv[1]).read_text())
root = Path(job['root']).resolve()
entry = root / job['entry']
loads = json.loads
reads = set()
def relocate(value):
    if isinstance(value, str) and 'prime_gaps_20260903/' in value and value.startswith('/'):
        return str(root / value.split('prime_gaps_20260903/', 1)[1])
    if isinstance(value, list): return [relocate(x) for x in value]
    if isinstance(value, dict): return {relocate(k): relocate(v) for k,v in value.items()}
    return value
json.loads = lambda *a, **kw: relocate(loads(*a, **kw))
os.chdir(root)
sys.dont_write_bytecode = True
sys.path[:0] = [str(entry.parent), str(root/'runtime')]
sys.argv = [str(entry), *job['arguments']]
if sys.flags.optimize: raise RuntimeError('Python assertions must be enabled')
def audit(event, args):
    if event == 'open' and isinstance(args[0], (str, bytes, os.PathLike)):
        p = Path(os.fsdecode(args[0])).absolute()
        mode, flags = args[1:]
        writing = (isinstance(mode,str) and any(c in mode for c in 'wax+')) or flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)
        if writing and not p.is_relative_to(root): raise PermissionError('Write outside isolated workspace: '+str(p))
        if p.is_relative_to(root):
            rel = str(p.relative_to(root))
            if not writing:
                reads.add(rel)
                if rel in job.get('forbid_reads',[]): raise PermissionError('Historical production output read refused: '+rel)
        elif 'prime_gaps_20260903/' in str(p): raise PermissionError('Original host path read refused: '+str(p))
    if event.startswith('socket.') or event in ('subprocess.Popen','os.system'):
        raise PermissionError('Offline numerical worker forbids '+event)
sys.addaudithook(audit)
try:
    if job.get('function') == 'sweep_without_reuse':
        module = runpy.run_path(str(entry), run_name='external_vendor')
        module['sweep'](root/job['trial'], root/job['output'], block=48, precision=224, bits=224, reuse_pilot=None)
    else:
        runpy.run_path(str(entry), run_name='__main__')
finally:
    (root/job['access_log']).write_text(json.dumps(sorted(reads),indent=2)+'\n')
