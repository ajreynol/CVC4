#!/usr/bin/env python3

import signal
import subprocess
import sys

# result_differs_binary.py [expected1] [expected2] [binary1] [binary2] [cli opts]* [benchmark]

def handler(sig, frame):
    print("Aborted")
    sys.exit(1)


signal.signal(signal.SIGTERM, handler)


def run(cmd):
    res = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    return res.stdout.decode('utf8').strip()

argList = sys.argv
argList.pop(0)
expected1 = argList.pop(0)
expected2 = argList.pop(0)
binary1 = argList.pop(0)
binary2 = argList.pop(0)
# solverA, optionsA, each as separate elements of list
argList.insert(0, binary1)
A = run(argList)

# solverB, optionsB, each as separate elements of list
argList.pop(0)
argList.insert(0, binary2)
B = run(argList)

print(f'{expected1}')
print(f'{expected2}')

if A not in [expected1, expected2]:
    print(f'Unexpected output for A: {A}')
    sys.exit(2)

if B not in [expected1, expected2]:
    print(f'Unexpected output for B: {B}')
    sys.exit(2)

print(f'{A} / {B}')
if A == B:
    sys.exit(0)
else:
    sys.exit(1)

