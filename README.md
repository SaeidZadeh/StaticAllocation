# StaticAllocation for Robotic Network Cloud Systems
## Paper

[Optimal Algorithm Allocation for Robotic Network Cloud Systems](https://arxiv.org/abs/2104.12710)

## Descriptions
The code for the paper Optimal Algorithm Allocation for Robotic Network Cloud Systems 

We begin by describing the graph of all algorithms, the average execution time of each algorithm to be executed on each node, the average communication time (data transmission speed) between two adjacent node, and the constraints on memory. 

The code is designed to solve the static allocation of a fixed graph of algorithms on non-isomorphic, randomly generated architectures. The solution can be obtained using a single architecture with known constraints on memory and data transmission speed. 

The result is the solution with the lowest response time and memory requirements of all the edge nodes (the smallest distance to the origin). 

All packages (libraries) to execute the code are included in the code.

## Requirements
Install the requirements in a R environment with `packages(pcalg,igraph,combinat,statgraph,arrangements)`.


## Citation
```
@misc{https://doi.org/10.48550/arxiv.2104.12710,
  doi = {10.48550/ARXIV.2104.12710},
  url = {https://arxiv.org/abs/2104.12710},
  author = {Alirezazadeh, Saeid and Correia, André and Alexandre, Luís A.},
  keywords = {Robotics (cs.RO), FOS: Computer and information sciences, FOS: Computer and information sciences},
  title = {Optimal Algorithm Allocation for Robotic Network Cloud Systems},
  publisher = {arXiv},
  year = {2021},
  copyright = {arXiv.org perpetual, non-exclusive license}
}
```
