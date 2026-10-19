#!/usr/bin/env python3
"""Run every checker on every certificate, plus negative controls, and write the logs.

Usage, from the repository root:

    python3 checkers/run_all.py

For each JSON file in data/ and calibration/ this runs check_a.py, check_b.py and ref37_v2.py and writes
logs/<file>.log. It then builds negative controls in build/negative/ (face 0 dropped from every certificate; on
venn8_37_halfturn_a.json also one face reversed and one label merged into another), adds the two targeted controls
in checkers/negative/ (each violates exactly one condition, condition 3 or the vertex links; see
checkers/negative/README.md), runs all three checkers on each, and requires every one of them to reject it (nonzero
exit status). Results go to logs/negative_controls.log and logs/SUMMARY.log.

Requirements enforced (exit status 1 if any fails):
  - every file in data/ and calibration/ passes check_a.py, check_b.py and ref37_v2.py;
  - every negative control is rejected by all three checkers;
  - on each targeted control, each checker's output contains the expected reason.
Only the Python standard library is used.
"""
import copy
import glob
import hashlib
import json
import os
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CHECKERS = ['checkers/check_a.py', 'checkers/check_b.py', 'checkers/ref37_v2.py']
# Targeted controls (checkers/negative/README.md): file -> (label, expected substring of each checker's output).
TARGETED = {
    'checkers/negative/t05_curve3_two_circles.json':
        ('t05 (n=3): only condition 3 fails', {
            'checkers/check_a.py': 'curve 2: a half is disconnected',
            'checkers/check_b.py': 'curve 2: not a single closed curve',
            'checkers/ref37_v2.py': 'BGMV cond 3: curve 2 side 1 not connected'}),
    'checkers/negative/t01_two_spheres_pinched_at_0_and_15.json':
        ('t01 (n=4): only the vertex links fail', {
            'checkers/check_a.py': 'corners do not form one rotation cycle',
            'checkers/check_b.py': 'corners are not one disk',
            'checkers/ref37_v2.py': 'vertices have a link that is not a single cycle'}),
}


def sha256(path):
    return hashlib.sha256(open(os.path.join(ROOT, path), 'rb').read()).hexdigest()


def run(checker, path):
    """Run one checker on one file (paths relative to the repository root). Returns (exit code, output, seconds).
    Python 3.9+ puts the absolute script path into tracebacks; the repository's absolute path is replaced by '.'
    so that logs do not depend on where the repository lives."""
    t = time.time()
    r = subprocess.run([sys.executable, checker, path], cwd=ROOT, capture_output=True, text=True)
    out = (r.stdout + (('\n[stderr]\n' + r.stderr) if r.stderr else '')).replace(ROOT, '.')
    return r.returncode, out, time.time() - t


def verdict(code, out):
    if code == 0:
        return 'PASS'
    return 'FAIL' if ('FAIL' in out and 'Traceback' not in out) else 'REJECTED (exception)'


def main():
    os.chdir(ROOT)
    files = sorted(glob.glob('data/*.json')) + sorted(glob.glob('calibration/*.json'))
    hdr = [f'python {sys.version.split()[0]}', f'run at {time.strftime("%Y-%m-%d %H:%M:%S %Z")}']
    hdr += [f'{sha256(c)}  {c}' for c in CHECKERS]
    summary = ['# Positive runs (every file is expected to PASS all three checkers)', *hdr, '',
               f'{"file":46s} {"n":>3s} {"F":>5s}  check_a  check_b  ref37_v2']
    ok = True
    for f in files:
        d = json.load(open(f))
        lines = [f'input: {f}', f'input sha256: {sha256(f)}', *hdr, '']
        res = []
        for c in CHECKERS:
            code, out, sec = run(c, f)
            v = verdict(code, out)
            res.append(v)
            lines += [f'===== {sys.executable.split("/")[-1]} {c} {f}', f'exit status {code} ({v}), {sec:.2f} s',
                      out.rstrip(), '']
            if v != 'PASS':
                ok = False
        name = os.path.splitext(os.path.basename(f))[0]
        open(f'logs/{name}.log', 'w').write('\n'.join(lines) + '\n')
        summary.append(f'{f:46s} {d["n"]:3d} {len(d["faces"]):5d}  {res[0]:7s}  {res[1]:7s}  {res[2]}')
        print(summary[-1], flush=True)

    # negative controls
    os.makedirs('build/negative', exist_ok=True)
    controls = []
    for f in files:
        d = json.load(open(f))
        name = os.path.splitext(os.path.basename(f))[0]
        a = copy.deepcopy(d)
        a['faces'] = a['faces'][1:]
        controls.append((f'{name}: face 0 dropped', f'build/negative/{name}_dropface0.json', a))
    d = json.load(open('data/venn8_37_halfturn_a.json'))
    b = copy.deepcopy(d)
    b['faces'][0]['vertices'] = b['faces'][0]['vertices'][::-1]
    controls.append(('venn8_37_halfturn_a: face 0 reversed', 'build/negative/venn8_37_halfturn_a_reverse0.json', b))
    c = copy.deepcopy(d)
    for fc in c['faces']:
        fc['vertices'] = [254 if x == 255 else x for x in fc['vertices']]
    controls.append(('venn8_37_halfturn_a: label 255 replaced by 254', 'build/negative/venn8_37_halfturn_a_merge.json',
                     c))
    for path, (label, _) in TARGETED.items():
        controls.append((label, path, None))           # committed input, used as it is
    neg =['# Negative controls: every checker must reject every mutated certificate (nonzero exit status)', *hdr, '']
    summary += ['', '# Negative controls (every checker must reject)', '',
                f'{"control":48s} check_a  check_b  ref37_v2']
    for label, path, dd in controls:
        if dd is not None:
            json.dump(dd, open(path, 'w'))
        expect = TARGETED.get(path, (None, {}))[1]
        res = []
        neg.append(f'===== {label}  ({path}, sha256 {sha256(path)})')
        for ch in CHECKERS:
            code, out, sec = run(ch, path)
            v = verdict(code, out)
            res.append(v)
            body = [l.strip() for l in out.rstrip().splitlines()]
            if 'FAIL' in body:                       # check_a / check_b: reasons follow a bare FAIL line
                reasons = body[body.index('FAIL') + 1:]
            else:                                    # ref37_v2: lines 'FAIL: reason'
                reasons = [l for l in body if l.startswith('FAIL:')]
            if expect:                               # targeted control: every reason, and the expected one
                found = expect[ch] in out
                neg.append(f'  {ch}: exit status {code} -> {v}; expected reason "{expect[ch]}" present: {found}')
                neg += [f'      {r[:150]}' for r in reasons]
                if not found:
                    ok = False
            else:
                neg.append(f'  {ch}: exit status {code} -> {v}; first reason: {(reasons or [""])[0][:150]}')
            if v == 'REJECTED (exception)':
                neg.append(f'      (the checker then raised: {body[-1][:150]})')
            if code == 0:
                ok = False
        neg.append('')
        summary.append(f'{label:48s} {res[0]:7s}  {res[1]:7s}  {res[2]}')
        print(summary[-1], flush=True)
    open('logs/negative_controls.log', 'w').write('\n'.join(neg) + '\n')
    summary += ['', 'ALL REQUIREMENTS MET' if ok else 'SOME REQUIREMENT FAILED']
    open('logs/SUMMARY.log', 'w').write('\n'.join(summary) + '\n')
    print(summary[-1])
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
