#!/bin/bash
# Replay: build, probe vCPUs, run the benchmark pinned to one vCPU, merge into results/.
# usage: ./run_bench.sh <vcpu> <label> [full|reduced] [reps]
set -e
cd "$(dirname "$0")"
CPU=${1:?vcpu}; LABEL=${2:?label}; MODE=${3:-full}; REPS=${4:-15}
gcc -O2 -mavx2 -mfma -ffp-contract=off bench.c -o bench -lm
gcc -O2 -mavx2 cpuprobe.c -o cpuprobe
R=../results
{ echo "# $(date -u) label=$LABEL vcpu=$CPU mode=$MODE reps=$REPS"; echo "# loadavg before: $(cat /proc/loadavg)"; } > $R/bench_log_$LABEL.txt
taskset -c $CPU ./bench $MODE $LABEL $REPS > $R/bench_raw_$LABEL.jsonl 2>> $R/bench_log_$LABEL.txt
taskset -c $CPU ./bench setup $LABEL >> $R/bench_raw_$LABEL.jsonl 2>> $R/bench_log_$LABEL.txt
echo "# loadavg after: $(cat /proc/loadavg)" >> $R/bench_log_$LABEL.txt
