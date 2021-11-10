#!/bin/bash
#SBATCH -N 1
#SBATCH --exclusive
#SBATCH -t 240:00:00
#SBATCH --partition=lanka-v3
#SBATCH --array 1-1%8
#SBATCH --exclude lanka[25,35-48]
# want lanka[26,27,28,29,31,32,33,34]

#export SCRATCH=/data/scratch/pahrens
#export PATH="$SCRATCH/julia:$PATH"
#export JULIA_DEPOT_PATH=/data/scratch/pahrens/.julia
#export MATRIXDEPOT_DATA=/data/scratch/pahrens/MatrixData

cd $SCRATCH/Pigeon.jl/results
cat /sys/devices/system/cpu/intel_pstate/no_turbo

if [[ $SLURM_ARRAY_TASK_ID -eq 1 ]]
then
  srun --cpu-bind=sockets julia --project=. spmv2.jl
elif [[ $SLURM_ARRAY_TASK_ID -eq 2 ]]
then
  srun --cpu-bind=sockets julia --project=. spgemm.jl
elif [[ $SLURM_ARRAY_TASK_ID -eq 3 ]]
then
  srun --cpu-bind=sockets julia --project=. spgemm2.jl
elif [[ $SLURM_ARRAY_TASK_ID -eq 4 ]]
then
  srun --cpu-bind=sockets julia --project=. sspgemm.jl
elif [[ $SLURM_ARRAY_TASK_ID -eq 5 ]]
then
  srun --cpu-bind=sockets julia --project=. spgemma.jl
elif [[ $SLURM_ARRAY_TASK_ID -eq 6 ]]
then
  srun --cpu-bind=sockets julia --project=. spgemmh.jl
elif [[ $SLURM_ARRAY_TASK_ID -eq 7 ]]
then
  srun --cpu-bind=sockets julia --project=. bpctd.jl
elif [[ $SLURM_ARRAY_TASK_ID -eq 8 ]]
then
  srun --cpu-bind=sockets julia --project=. bpcdd.jl
fi
