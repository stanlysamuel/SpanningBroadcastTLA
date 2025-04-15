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

Each process has a single input buffer and an output buffer for each child. Since we are dealing with a single message broadcast algorithm, we can consider each buffer to store a Boolean value. Initially, all buffers are set to FALSE, except the input buffer of the ROOT node, which denotes a message to be sent, defined in `TCInit`.

The intuiton is to have two kind of actions:
1. Sending a message from process `p` to `q` defined in `SendFromPToQ(p,q)`.
2. Computing a message in process `p` which consists of two parts, defined in `Compute(p)`:
    1. Transfer message from input buffer of `p` to the output buffer of `p` for each child.
    2. Mark process as terminated.


## Comments on version 1

1. TLC says stuttering when it should not. We need to figure out this bug.
2. This version uses tuples which is not good for readability. Will use records instead.
3. ~~Need to separate variables from constants.~~
4. Try the above example in different tools.