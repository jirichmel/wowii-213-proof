#!/bin/bash
# consolidated random tests of proof.md (prover-claimC); logs in logs/
cd "$(dirname "$0")"
( for n in 12 16 17 20 26 32 40 50 64; do ./cdom hub $n 200000 5 $n; done ) > logs/c_hub.txt 2>&1
( for n in 12 16 20 26 32 40 64; do ./cdom shape $n 50000 5 $n; done ) > logs/c_shape.txt 2>&1
( for n in 16 17 20 24 32 48; do ./cdom anneal $n 300000 3 $n; done ) > logs/c_anneal.txt 2>&1
( for n in 10 12 16 24 40; do ./cdom rnd $n 5000 3 $n; done ) > logs/c_rnd.txt 2>&1
