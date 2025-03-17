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
PARENT <- [p1 |-> {}, p2 |-> {"p1"}, p3 |-> {"p1"}]
```

## Overall Idea

The intuiton is to have three kind of actions:
1. Sending a message from process `p` to `q`
2. Computing a message in process `p` which consists of two parts:
    1. Transfer message from input buffer of local process to output buffer of each child
    2. Mark process as terminated once all output buffers of the children are filled.