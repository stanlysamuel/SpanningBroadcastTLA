------------------------- MODULE SpanningBroadcast -------------------------

(***************************************************************************)
(* This specification talks about the "Spanning Broadcast Algorithm" *)
(* Algorithm 1 in the book Distributed Computing by Attiya and Welch *)
(***************************************************************************)
EXTENDS FiniteSets

CONSTANT P, ROOT, CHILDREN, PARENT      \* The set of participating processes, the root, and the spanning tree as a directed graph (CHILDREN, PARENT)

VARIABLE  configuration  \* configuration[p] is the state of process p.
-----------------------------------------------------------------------------

ParentType == P
ChildrenType == (SUBSET P)
TerminatedType == BOOLEAN
OutbufType == [P -> BOOLEAN]

\* Initial value of the output buffer. It assigns true to the children of the root, denoting a message to be sent to each child.
InitOutBuf(p) == 
    IF p \in ROOT
    THEN [q \in P  |-> IF q \in CHILDREN[p] THEN TRUE ELSE FALSE]
    ELSE [p1 |-> FALSE, p2 |-> FALSE, p3 |-> FALSE]

\*Leaves == {p \in P : CHILDREN[p] = {}} \* Not used

TCTypeOK == 
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
    /\ configuration \in [P -> ParentType \X ChildrenType \X TerminatedType \X OutbufType]
    /\ \A p \in P : ((PARENT[p] \intersect CHILDREN[p]) = {}) \* Spanning tree must have no cycles
    /\ \A p \in P : ( p \in ROOT => PARENT[p] = {}) \* Root has no parent
    /\ \neg (\E p \in P : PARENT[p] = {} /\ CHILDREN[p] = {}) \* No disconnected nodes.
    /\ \A p \in P : (PARENT[p] = {} \/ Cardinality(PARENT[p]) = 1) \* Parent has at most one node
    /\ \A p \in ROOT : ( p \in P) \* Root must be a member of the spanning tree.
    /\ Cardinality(ROOT) = 1 \* Root must be a singleton set.
        
TCInit == 
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
    configuration = [p \in P |-> <<PARENT[p], CHILDREN[p], FALSE, InitOutBuf(p)>>]

=============================================================================
\* Modification History
\* Last modified Mon Mar 17 12:15:04 IST 2025 by stanly
\* Created Thu Mar 06 16:45:20 IST 2025 by stanly
