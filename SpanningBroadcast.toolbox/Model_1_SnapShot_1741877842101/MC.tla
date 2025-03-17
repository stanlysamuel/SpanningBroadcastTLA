---- MODULE MC ----
EXTENDS SpanningBroadcast, TLC

\* CONSTANT definitions @modelParameterConstants:0P
const_1741877840062923000 == 
{"p1", "p2", "p3"}
----

\* CONSTANT definitions @modelParameterConstants:1ROOT
const_1741877840062924000 == 
{"p1"}
----

\* CONSTANT definitions @modelParameterConstants:2CHILDREN
const_1741877840062925000 == 
[p1 |-> {"p2", "p3"}, p2 |-> {}, p3 |-> {}]
----

\* CONSTANT definitions @modelParameterConstants:3PARENT
const_1741877840062926000 == 
[p1 |-> {}, p2 |-> {"p1"}, p3 |-> {}]
----

\* Constant expression definition @modelExpressionEval
const_expr_1741877840062927000 == 
\neg (\E p \in P : PARENT[p] = {} /\ CHILDREN[p] = {})
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1741877840062927000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_1741877840062928000 ==
FALSE/\configuration = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1741877840062929000 ==
FALSE/\configuration' = configuration
----
=============================================================================
\* Modification History
\* Created Thu Mar 13 20:27:20 IST 2025 by stanly
