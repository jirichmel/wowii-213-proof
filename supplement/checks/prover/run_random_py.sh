#!/bin/bash
cd "$(dirname "$0")"
( python3 pdom.py named; for n in 10 11 12 13; do python3 pdom.py rnd $n 2000 $n 3; done; for n in 16 20 30 40; do python3 pdom.py rnd $n 2000 $n 3; done ) > logs/py_rnd.txt 2>&1
( for n in 12 13 16 17 20 26 32 40 50; do python3 pdom.py hub $n 5000 $((n+100)) 3; done ) > logs/py_hub.txt 2>&1
