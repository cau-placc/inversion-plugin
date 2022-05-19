#!/bin/bash

csv_file="benchmark$(date "+%Y-%m-%d-%H-%M-%S").csv" # CSV file name
benchmarks='mps' # List of benchmarks to perform
repeats=10 # Number of repeats for a single benchmark
processors=$(grep ^cpu\\scores /proc/cpuinfo | uniq |  awk '{print $4}') # Get number of physical processors

# Build benchmark suite
stack build sandbox:main --flag inversion-plugin:use-what4

# Run benchmark suite
for benchmark in ${benchmarks}
do
    echo -n ${benchmark} >> ${csv_file} # Start a new line with the benchmark name in the CSV file
    for ((threads = 1; threads <= ${processors} ; threads *= 2))
    do
        echo -n "Run ${benchmark} with ${threads} thread(s)"
        run_time_average=0
        for ((run = 1; run <= ${repeats} ; run++))
        do
            run_command="stack exec main -- ${benchmark} ${threads}"
            echo -n "."
            run_time=$(/usr/bin/time -f "%e" -a ${run_command} 2>&1)
            run_time_average=$(echo "print((${run_time_average}*(${run}-1)+${run_time})/${run})" | python)
        done
        # ...and append it to the current line in the CSV file
        echo -n " ${run_time_average}" >> ${csv_file}
        echo
    done
    # End current line in the CSV file
    echo >> ${csv_file}
done
