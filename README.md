# Spanning Broadcast Algorithm in TLA+ and Quint
This repository hosts the model of the Spannning Broadcast Algorithm; Algorithm 1 in the book Distributed Computing by Attiya and Welch.

## Introduction 

The model has four constants `P`, `ROOT`, `CHILDREN`, and `PARENT` that model the parameters of the system.

`P` models the set of nodes in the spanning tree.
`ROOT` is the root of spanning tree,
`CHILDREN` is a map mapping processes to their children
`PARENT` is a map mapping processes to their parent.

The definition `SBConstOK` contains constraints for the above constants.

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

## Comments
1. Replaced Tuples with Records for ease of readability
2. [Possible TLC bug?] The `SBSoundness` property must hold but TLC reports that it is violated. The property states that eventually every process will terminate which does hold in the every run of the model. However, while checking the property, TLC does not check the entire run, assumes that the run would stutter after an invalid state, and reports a violation.

## The Quint model

The file `spanningbroadcast.qnt` recreates the TLA+ model of the spanning broadcast algoirithm written in `SpanningBroadcast.tla`. 

## Discussion

In both models, there is an invariant property and a temporal property.

### Invariant Property
The invariant property states that it is always the case that some process never terminates. 
In both models, this property is violated as expected.

The invariant property in TLA+:
```
SBNoTermination ==  
  (*************************************************************************)
  (* Invariant on non-termination                        *)
  (*************************************************************************)
               (\E p \in P: Terminated(p) = FALSE)
```
The invariant property in Quint:

```
// Invariant on non-termination (Safety)
val no_termination = P.exists(p => configuration.get(p).terminated == false)
```

### Temporal (Liveness) Property

The temporal property states that eventually all processes terminate.

The temporal property in TLA+:

```
SBSoundness ==  
  (*************************************************************************)
  (* Eventually, all processes recieve the message (liveness property on termination)                        *)
  (*************************************************************************)
               <> (\A p \in P: Terminated(p) = TRUE)
```

The temporal property in Quint:

```
// Temporal property on termination (Liveness) [Note: Doesn't seem to be supported yet]
temporal termination = eventually(P.forall(p => configuration.get(p).terminated == true))
```

In Quint, temporal properties does not seem to be supported yet.
In TLA+, the TLC model checker returns a violation which should not be the case.
