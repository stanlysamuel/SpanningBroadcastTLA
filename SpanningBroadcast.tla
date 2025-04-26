------------------------- MODULE SpanningBroadcast -------------------------

(***************************************************************************)
(* This specification talks about the "Spanning Broadcast Algorithm" *)
(* Algorithm 1 in the book Distributed Computing by Attiya and Welch *)
(***************************************************************************)
EXTENDS FiniteSets

CONSTANT P, ROOT, CHILDREN, PARENT      \* The set of participating processes, the root, and the spanning tree as a directed graph (CHILDREN, PARENT)
ASSUME CHILDREN \in [P -> SUBSET P] \* Each process has a set of children

VARIABLE  configuration \* configuration[p] is the state of process p.
-----------------------------------------------------------------------------
(***************************************************************************)
(* Types (denoting the state of each process) *)
(***************************************************************************)

ParentType == (SUBSET P) \* empty set only in the case of root; singleton set otherwise
ChildrenType == (SUBSET P) \* empty in the case of leaves; non-empty otherwise.
TerminatedType == BOOLEAN
OutbufType == [P -> BOOLEAN]
InbufType == BOOLEAN

(***************************************************************************)
(* Initial values of each type *)
(***************************************************************************)

\* Initial value of the input buffer. It assigns true to the input buffer of the root, and false for the rest.
InitInbufType(p) == 
    IF p \in ROOT
        THEN TRUE
        ELSE FALSE
        
\* Initial value of the output buffer is FALSE for all.
InitOutbufType == [q \in P |-> FALSE]

\* Initial value of the TerminatedType.
InitTerminatedType == FALSE
        
(***************************************************************************)
(* Definitions for a given process p (for reference) *)
(***************************************************************************)

Inbuf(p) == configuration[p].inbuf
Outbuf(p) == configuration[p].outbuf
Terminated(p) == configuration[p].terminated
OutbufQinP(p,q) == configuration[p].outbuf[q] \* OutbufQinP(p,q) is true if process p has a message for process in q in the respective output buffer.

SBConstOK ==
    (*************************************************************************)
    (* The type-correctness invariant (constants)                                  *)
    (*************************************************************************)
    \*Constraints on P
    /\ Cardinality(P) # 0 \* The set of processes is not empty
    
    \*Constraints on ROOT
    /\ Cardinality(ROOT) = 1 \* Root must be a singleton set.
    /\ \A p \in P : ( p \in ROOT => PARENT[p] = {}) \* Root has no parent
    /\ \A p \in ROOT : ( p \in P) \* Root must be a member of the spanning tree.
   
    \*Constraints on PARENT, CHILDREN (not complete, need transitive closure)
    /\ \A p \in P : PARENT[p] \in ParentType
    /\ \A p \in P : CHILDREN[p] \in ParentType
    /\ \A p \in P : ((PARENT[p] \intersect CHILDREN[p]) = {}) \* Spanning tree must have no cycles (weak, need transitive closure).
    /\ \neg (\E p \in P : PARENT[p] = {} /\ CHILDREN[p] = {}) \* No disconnected nodes (weak, need transitive closure).
    /\ \A p \in P : (PARENT[p] = {} \/ Cardinality(PARENT[p]) = 1) \* Parent has at most one node
    
SBTypeOK == 
  (*************************************************************************)
  (* The type-correctness invariant (variables)                                     *)
  (*************************************************************************)
    /\ configuration \in [P -> [inbuf: InbufType , outbuf: OutbufType , terminated: TerminatedType]]
        
SBInit == 
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
    configuration = [p \in P |-> [inbuf |-> InitInbufType(p), outbuf |-> InitOutbufType, terminated |-> InitTerminatedType]]

(*************************************************************************)
(* Actions                                                               *)
(*************************************************************************)
  
SendFromPToQ(p,q) ==  

    /\ configuration[p].outbuf[q] = TRUE \* outbuf[p][q] is TRUE
    /\ configuration' = 
        [configuration EXCEPT   ![q].inbuf = TRUE, \* inbuf[q] is TRUE
                                ![p].outbuf[q] = FALSE] \* outbuf[p][q] is false

\* If an input buffer has a message, then mark a corresponding child's output buffer in the parent's node as TRUE
Compute(p) == 
    /\ configuration[p].inbuf = TRUE \* input buffer for p is true
    /\ configuration' = 
        [configuration EXCEPT 
            ![p].outbuf = [q \in P |-> IF q \in CHILDREN[p] 
                                    THEN TRUE 
                                    ELSE FALSE], \* Store message in each output buffer of process p.
            ![p].terminated = TRUE, \* Mark p as terminated
            ![p].inbuf = FALSE] \* Mark input buffer as empty

SBNext ==
  (*************************************************************************)
  (* The next-state action.                                                *)
  (*************************************************************************)
            \E p,q \in P : Compute(p) \/ SendFromPToQ(p,q)

-----------------------------------------------------------------------------
SBSoundness ==  
  (*************************************************************************)
  (* Eventually, all processes recieve the message (liveness property on termination)                        *)
  (*************************************************************************)
               <> (\A p \in P: Terminated(p) = TRUE)

-----------------------------------------------------------------------------
SBNoTermination ==  
  (*************************************************************************)
  (* Invariant on non-termination                        *)
  (*************************************************************************)
               (\E p \in P: Terminated(p) = FALSE)

\* BEGIN: Definitions for testing purposes
\*TestInitState == [  p1 |->
\*         <<TRUE, [p1 |-> FALSE, p2 |-> FALSE, p3 |-> FALSE], TRUE>>,
\*                    p2 |->
\*         <<FALSE, [p1 |-> FALSE, p2 |-> FALSE, p3 |-> FALSE], FALSE >>,
\*                    p3 |-> 
\*         <<FALSE, [p1 |-> FALSE, p2 |-> FALSE, p3 |-> FALSE], FALSE>> ]
\*     
\*TestDef1 == \E p \in P : TestInitState[p] = <<TRUE, [p1 |-> FALSE, p2 |-> TRUE, p3 |-> TRUE], TRUE>>
\*TestDef2 == TestInitState["p1"][2] = [p1 |-> FALSE, p2 |-> TRUE, p3 |-> TRUE]
\*TestDef3 == TestInitState["p1"][2]["p1"] = FALSE
\* END: Definitions for testing purposes

=============================================================================
\* Modification History
\* Last modified Tue Apr 15 19:14:00 IST 2025 by stanly
\* Created Thu Mar 06 16:45:20 IST 2025 by stanly
