## Compiling

To build, type 'make'. You will need a GCC compiler.

## Running

./PathLAD-Plus -p pattern.txt -t target.txt -f -s 3600

Files
-----

Makefile: make an executable (main) and test on 2 subgraph isomorphism instances 

allDiff.c compatibility.c graph.c lad.c domains.c main.c: source files

pattern.txt: example of non labelled pattern graph

target.txt: example of target graph

README: this file

Usage
-----

-p FILE  Input pattern graph (mandatory)

-t FILE  Input target graph (mandatory)

-s INT   Set CPU time limit in seconds (default: 60)

-f       Stop at first solution (default: search for all solutions)

-v       Print solutions (default: only number of solutions)

-h       Print this help message

Graph format
------------

Pattern and target graphs should be defined in two text files. The format of these files is defined as follows:
- The first line only contains the number n of vertices.
- Each following line gives, for each vertex i, the number of successors of i followed by the list of successors of i.
- Nodes must be numbered from 0 and, if there is an edge from i to j and an edge from j to i, then j must be a successor of i and i must be a successor of j.

