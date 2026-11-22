#!/bin/bash
# random / structured / annealed runs of rnd (see rnd.c header). Logs in logs/.
cd "$(dirname "$0")"
run_mode() { # mode trials nex
  mode=$1; tr=$2; nex=$3; out=logs/rnd_$mode.txt; : > $out
  for n in $(seq 10 2 40); do for seed in 1 2 3; do ./rnd $mode $n $tr $((n*100+seed)) $nex >> $out; done; done
}
run_mode closure 2000 24 &
run_mode hub 2000 24 &
run_mode c2a 2000 24 &
run_mode hubk 2000 24 &
( : > logs/rnd_anneal.txt; for n in $(seq 12 2 40); do for seed in 1 2 3 4; do ./rnd anneal $n 20000 $((n*1000+seed)) 20 >> logs/rnd_anneal.txt; done; done ) &
( : > logs/rnd_hyp.txt; for n in 11 12 13 14 15 16 17 18 19 20; do ./rnd hyp $n 3000 $n >> logs/rnd_hyp.txt; done ) &
wait
echo ALL DONE
