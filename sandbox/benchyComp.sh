#!/bin/bash
echo "Usage: benchyComp count step start resultname, where the benchmarked values are generated by [start + step * n | n <- [1..count]]"

stack install sandbox

arg=""

for i in $(seq 1 $1)
do
 let j=$i*$2+$3
 c="'benchinv ${j}' "
 arg=$arg$c
done

for i in $(seq 1 $1)
do
 let j=$i*$2+$3
 c="'./Last-PAKCS ${j}' "
 arg=$arg$c
done

for i in $(seq 1 $1)
do
 let j=$i*$2+$3
 c="'././Last-KiCS ${j}' "
 arg=$arg$c
done

# for i in $(seq 1 $1)
# do
#  let j=$i*$2+$3
#  c="'benchinv CBNHandler ${j}' "
#  arg=$arg$c
# done

current_time=$(date "+%Y-%m-%d-%H-%M-%S")

cmd="bench --output benchmarks/$4-$current_time.html --csv benchmarks/$4-$current_time.csv $arg"
echo $cmd
eval $cmd
firefox benchmarks/$4-$current_time.html
