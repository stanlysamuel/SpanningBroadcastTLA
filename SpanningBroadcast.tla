------------------------- MODULE SpanningBroadcast -------------------------

(***************************************************************************)
(* This specification talks about the "Spanning Broadcast Algorithm" *)
(* Algorithm 1 in the book Distributed Computing by Attiya and Welch *)
(***************************************************************************)
EXTENDS FiniteSets

CONSTANT P, ROOT, CHILDREN, PARENT      \* The set of participating processes, the root, and the spanning tree as a directed graph (CHILDREN, PARENT)

VARIABLE  configuration  \* configuration[p] is the state of process p.
-----------------------------------------------------------------------------

ParentType == (SUBSET P) \* empty set only in the case of root and singleton set otherwise
ChildrenType == (SUBSET P) \* empty in the case of leaves and non-empty otherwise.
TerminatedType == BOOLEAN
OutbufType == [P -> BOOLEAN]
InbufType == BOOLEAN

\* Initial value of the input buffer. It assigns true to the children of the root, denoting a message to be sent to each child.

InitInbufType(p) == 
    IF p \in ROOT
        THEN TRUE
        ELSE FALSE
        
\* Initial value of the output buffer is FALSE for all.
InitOutbufType == [q \in P |-> FALSE]

\* Initial value of the TerminatedType.
InitTerminatedType == FALSE
    
\* QinOutbufP(p,q) is true if process p's output buffer is true for process q.
\* QinOutbufOfP(p,q) == configuration[p][4][q] \* Not used

\* Terminated(p) == configuration[p][3] \* Not used
 
\*Leaves == {p \in P : CHILDREN[p] = {}} \* Not used

TCTypeOK == 
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
    /\ configuration \in [P -> ParentType \X ChildrenType \X TerminatedType \X OutbufType \X InbufType]
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
    configuration = [p \in P |-> <<PARENT[p], CHILDREN[p], InitTerminatedType, InitOutbufType, InitInbufType(p)>>]

SendFromPToQ(p,q) ==  

    /\ configuration[p][4][q] = TRUE \* outbuf[p][q] is TRUE
    /\ configuration' = 
        [configuration EXCEPT   ![q][5] = TRUE, \* inbuf[q] is TRUE
                                ![p][4][q] = FALSE] \* outbuf[p][q] is false

\* If an input buffer has a message, then mark a corresponding child's output buffer in the parent's node as TRUE
Compute(p) == /\ configuration[p][5] = TRUE \* input buffer for p is true
                /\ configuration' = 
                    [configuration EXCEPT 
                        ![p][4] = [q \in P |-> IF q \in CHILDREN[p] 
                                                THEN TRUE 
                                                ELSE FALSE], \* Store message in each output buffer of process p.
                        ![p][3] = TRUE, \* Mark p as terminated
                        ![p][5] = FALSE] \* Mark input buffer as empty
                        
  (*************************************************************************)
  (* The next-state action.                                                *)
  (*************************************************************************)
TCNext == \E p,q \in P : Compute(p) \/ SendFromPToQ(p,q)

=============================================================================
\* Modification History
\* Last modified Tue Mar 18 14:36:47 IST 2025 by stanly
\* Created Thu Mar 06 16:45:20 IST 2025 by stanly
