------------------------- MODULE SpanningBroadcast -------------------------

(***************************************************************************)
(* This specification talks about the "Spanning Broadcast Algorithm" *)
(* Distributed Systems Algo 1.                                      *)
(***************************************************************************)
CONSTANT P, ROOT, CHILDREN, PARENT      \* The set of participating processes, the root, and the network graph

VARIABLE  configuration  \* configuration[p] is the state of process p.
-----------------------------------------------------------------------------

Parent == P
Children == (SUBSET P)
Terminated == BOOLEAN

Leaves == {p \in P : CHILDREN[p] = {}}

TCTypeOK == 
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
\*  /\ configuration \in [P -> {"working", "prepared", "committed", "aborted"}]
    /\ configuration \in [P -> Parent \X Children \X Terminated]
    /\ \A p \in P : ((PARENT[p] \intersect CHILDREN[p]) = {}) \* Spanning tree must have no cycles
    /\ \A p \in P : ( p \in ROOT => PARENT[p] = {}) \* Root has no parent
    /\ \neg (\E p \in P : PARENT[p] = {} /\ CHILDREN[p] = {})
\*    /\ parent \in P
\*    /\ children \in SUBSET P
\*    /\ terminated \in BOOLEAN
        
TCInit ==   configuration = [p \in P |-> <<PARENT[p], CHILDREN[p], FALSE>>]
\*TCInit ==   
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)

\*canCommit == \A r \in RM : rmState[r] \in {"prepared", "committed"}
\*  (*************************************************************************)
\*  (* True iff all RMs are in the "prepared" or "committed" state.          *)
\*  (*************************************************************************)
\*
\*notCommitted == \A r \in RM : rmState[r] # "committed" 
\*  (*************************************************************************)
\*  (* True iff no resource manager has decided to commit.                   *)
\*  (*************************************************************************)
\*-----------------------------------------------------------------------------
\*(***************************************************************************)
\*(* We now define the actions that may be performed by the RMs, and then    *)
\*(* define the complete next-state action of the specification to be the    *)
\*(* disjunction of the possible RM actions.                                 *)
\*(***************************************************************************)
\*Prepare(r) == /\ rmState[r] = "working"
\*              /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
\*
\*Decide(r)  == \/ /\ rmState[r] = "prepared"
\*                 /\ canCommit
\*                 /\ rmState' = [rmState EXCEPT ![r] = "committed"]
\*              \/ /\ rmState[r] \in {"working", "prepared"}
\*                 /\ notCommitted
\*                 /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
\*
\*TCNext ==   /\ parent' = parent
\*            /\ children' = children 
\*            /\ terminated' = terminated
\*TCNext == \E r \in RM : Prepare(r) \/ Decide(r)
  (*************************************************************************)
  (* The next-state action.                                                *)
  (*************************************************************************)
\*-----------------------------------------------------------------------------
\*TCConsistent ==  
\*  (*************************************************************************)
\*  (* A state predicate asserting that two RMs have not arrived at          *)
\*  (* conflicting decisions.  It is an invariant of the specification.      *)
\*  (*************************************************************************)
\*  \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
\*                       /\ rmState[r2] = "committed"
\*-----------------------------------------------------------------------------
\*(***************************************************************************)
\*(* The following part of the spec is not discussed in Video Lecture 5.  It *)
\*(* will be explained in Video Lecture 8.                                   *)
\*(***************************************************************************)
\*TCSpec == TCInit /\ [][TCNext]_rmState
\*  (*************************************************************************)
\*  (* The complete specification of the protocol written as a temporal      *)
\*  (* formula.                                                              *)
\*  (*************************************************************************)
\*
\*THEOREM TCSpec => [](TCTypeOK /\ TCConsistent)
\*  (*************************************************************************)
\*  (* This theorem asserts the truth of the temporal formula whose meaning  *)
\*  (* is that the state predicate TCTypeOK /\ TCInvariant is an invariant   *)
\*  (* of the specification TCSpec.  Invariance of this conjunction is       *)
\*  (* equivalent to invariance of both of the formulas TCTypeOK and         *)
\*  (* TCConsistent.                                                         *)
\*  (*************************************************************************)

=============================================================================
\* Modification History
\* Last modified Thu Mar 13 20:26:16 IST 2025 by stanly
\* Created Thu Mar 06 16:45:20 IST 2025 by stanly
