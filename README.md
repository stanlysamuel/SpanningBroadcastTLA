# Spanning Broadcast Algorithm in TLA+
This repository hosts the model of the Spannning Broadcast Algorithm; Algorithm 1 in the book Distributed Computing by Attiya and Welch.

## Introduction 

The model has four constants `P`, `ROOT`, `CHILDREN`, and `PARENT` that model the parameters of the system.

`P` models the set of nodes in the spanning tree.
`ROOT` is the root of spanning tree,
`CHILDREN` is a map mapping processes to their children
`PARENT` is a map mapping processes to their parent.

The definition `TypeOK` contains constraints for the above constants.

A possible instantiation of the above parameters for the model is shown below:

```
P <- {"p1", "p2", "p3"}
ROOT <- {"p1"}
CHILDREN <- [p1 |-> {"p2", "p3"}, p2 |-> {}, p3 |-> {}]
PARENT <- [p1 |-> {}, p2 |-> {"p1", "p2"}, p3 |-> {}]
```