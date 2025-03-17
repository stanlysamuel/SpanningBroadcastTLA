------------------------- MODULE SpanningBroadcast -------------------------

(***************************************************************************)
(* This specification talks about the "Spanning Broadcast Algorithm" *)
(* Algorithm 1 in the book Distributed Computing by Attiya and Welch *)
(***************************************************************************)
EXTENDS FiniteSets

CONSTANT P, ROOT, CHILDREN, PARENT      \* The set of participating processes, the root, and the spanning tree as a directed graph (CHILDREN, PARENT)

VARIABLE  configuration  \* configuration[p] is the state of process p.
-----------------------------------------------------------------------------

\* Definitions for testing purposes
TestInitState == [ p1 |->
         <<{}, {"p2", "p3"}, TRUE, [p1 |-> FALSE, p2 |-> TRUE, p3 |-> TRUE]>>,
     p2 |->
         << {"p1", "p2"},
            {},
            FALSE,
            [p1 |-> FALSE, p2 |-> FALSE, p3 |-> FALSE] >>,
     p3 |-> <<{}, {}, FALSE, [p1 |-> FALSE, p2 |-> FALSE, p3 |-> FALSE]>> ]
     
TestDef1 == \E p \in P : TestInitState[p] = <<{}, {"p2", "p3"}, TRUE, [p1 |-> FALSE, p2 |-> TRUE, p3 |-> TRUE]>>
TestDef2 == TestInitState["p1"][4] = [p1 |-> FALSE, p2 |-> TRUE, p3 |-> TRUE]
TestDef3 == TestInitState["p1"][4]["p1"] = FALSE

\* QinOutbufP(p,q) is true if process p's output buffer is true for process q.
QinOutbufOfP(p,q) == configuration[p][4][q]

ParentType == P
ChildrenType == (SUBSET P)
TerminatedType == BOOLEAN
OutbufType == [P -> BOOLEAN]

\* Initial value of the output buffer. It assigns true to the children of the root, denoting a message to be sent to each child.
InitOutbufType(p) == 
    IF p \in ROOT
    THEN [q \in P  |-> IF q \in CHILDREN[p] THEN TRUE ELSE FALSE]
    ELSE [p1 |-> FALSE, p2 |-> FALSE, p3 |-> FALSE]

\* Initial value of the TerminatedType. We assume that the root starts in a terminated state, since the output buffer for each child is set with a message.
InitTerminatedType(p) == 
    IF p \in ROOT
    THEN TRUE
    ELSE FALSE
    
\*  Terminated(p) == configuration[p][3]
 
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
    configuration = [p \in P |-> <<PARENT[p], CHILDREN[p], InitTerminatedType(p), InitOutbufType(p)>>]

canSendAndCompute == \E p,q \in P : QinOutbufOfP(p,q) /\ q \in CHILDREN[p]

SendFromPToQAndComputeInQ(p,q,r) ==  

      /\ QinOutbufOfP(p,q) = TRUE
      /\ configuration' = [configuration EXCEPT ![q][3] = TRUE, ![p][4][q] = FALSE, ![q][4][r] = TRUE]

TCNext ==  
  (*************************************************************************)
  (* The next-state action.                                                *)
  (*************************************************************************)

      /\ canSendAndCompute
      /\ \E p,q \in P : \A r \in CHILDREN[q]: SendFromPToQAndComputeInQ(p,q,r)

=============================================================================
\* Modification History
\* Last modified Mon Mar 17 16:21:33 IST 2025 by stanly
\* Created Thu Mar 06 16:45:20 IST 2025 by stanly
