using Plots
pyplot()
using BSON
using JSON
using Statistics

names = [
	"bpcdd",
	"bpctd",
	"spgemm",
	"spgemm2",
	"sspgemm",
	"spgemmh",
    "spmv",
    "spmv2",
    "spmv3",
    "mttkrp",
]