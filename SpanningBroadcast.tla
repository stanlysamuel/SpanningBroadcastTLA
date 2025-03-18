------------------------- MODULE SpanningBroadcast -------------------------

(***************************************************************************)
(* This specification talks about the "Spanning Broadcast Algorithm" *)
(* Algorithm 1 in the book Distributed Computing by Attiya and Welch *)
(***************************************************************************)
EXTENDS FiniteSets

CONSTANT P, ROOT, CHILDREN, PARENT      \* The set of participating processes, the root, and the spanning tree as a directed graph (CHILDREN, PARENT)

VARIABLE  configuration  \* configuration[p] is the state of process p.
-----------------------------------------------------------------------------

\* BEGIN: Definitions for testing purposes
TestInitState == [  p1 |->
         <<{}, {"p2", "p3"}, TRUE, [p1 |-> FALSE, p2 |-> FALSE, p3 |-> FALSE], TRUE>>,
                    p2 |->
         << {"p1", "p2"}, {}, FALSE, [p1 |-> FALSE, p2 |-> FALSE, p3 |-> FALSE], FALSE >>,
                    p3 |-> 
         <<{}, {}, FALSE, [p1 |-> FALSE, p2 |-> FALSE, p3 |-> FALSE], FALSE>> ]
     
TestDef1 == \E p \in P : TestInitState[p] = <<{}, {"p2", "p3"}, TRUE, [p1 |-> FALSE, p2 |-> TRUE, p3 |-> TRUE], TRUE>>
TestDef2 == TestInitState["p1"][4] = [p1 |-> FALSE, p2 |-> TRUE, p3 |-> TRUE]
TestDef3 == TestInitState["p1"][4]["p1"] = FALSE
\* END: Definitions for testing purposes

(***************************************************************************)
(* Types (denoting the state of each process) *)
(***************************************************************************)

ParentType == (SUBSET P) \* empty set only in the case of root and singleton set otherwise
ChildrenType == (SUBSET P) \* empty in the case of leaves and non-empty otherwise.
TerminatedType == BOOLEAN
OutbufType == [P -> BOOLEAN]
InbufType == BOOLEAN

(***************************************************************************)
(* Initial values of each type *)
(***************************************************************************)
   
\* Initial value of the ParentType.
InitParentType(p) == PARENT[p]
     
\* Initial value of the ChildrenType.
InitChildrenType(p) == CHILDREN[p]

\* Initial value of the TerminatedType.
InitTerminatedType == FALSE

\* Initial value of the output buffer is FALSE for all.
InitOutbufType == [q \in P |-> FALSE]

\* Initial value of the input buffer. It assigns true to the input buffer of the root, and false for the rest.
InitInbufType(p) == 
    IF p \in ROOT
        THEN TRUE
        ELSE FALSE
        
(***************************************************************************)
(* Definitions for a given process p (for reference) *)
(***************************************************************************)

Parent(p) == configuration[p][1]
Children(p) == configuration[p][2]
Terminated(p) == configuration[p][3]
Outbuf(p) == configuration[p][4]
Inbuf(p) == configuration[p][5]
OutbufQinP(p,q) == configuration[p][4][q] \* OutbufQinP(p,q) is true if process p has a message for process in q in the respective output buffer.

SBTypeOK == 
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
        
SBInit == 
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
    configuration = [p \in P |-> <<InitParentType(p), InitChildrenType(p) , InitTerminatedType, InitOutbufType, InitInbufType(p)>>]


(*************************************************************************)
(* Actions                                                               *)
(*************************************************************************)
  
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

SBNext ==
  (*************************************************************************)
  (* The next-state action.                                                *)
  (*************************************************************************)
            \E p,q \in P : Compute(p) \/ SendFromPToQ(p,q)

-----------------------------------------------------------------------------
SBSoundness ==  
  (*************************************************************************)
  (* Eventually, all processes recieve the message                         *)
  (*************************************************************************)
                <> (\A p \in P: Terminated(p) = TRUE)
=============================================================================
\* Modification History
\* Last modified Tue Mar 18 17:38:58 IST 2025 by stanly
\* Created Thu Mar 06 16:45:20 IST 2025 by stanly
