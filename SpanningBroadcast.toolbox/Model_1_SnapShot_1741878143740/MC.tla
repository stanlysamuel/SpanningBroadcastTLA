---- MODULE MC ----
EXTENDS SpanningBroadcast, TLC

\* CONSTANT definitions @modelParameterConstants:0P
const_1741878141707937000 == 
{"p1", "p2", "p3"}
----

\* CONSTANT definitions @modelParameterConstants:1ROOT
const_1741878141707938000 == 
{"p1"}
----

\* CONSTANT definitions @modelParameterConstants:2CHILDREN
const_1741878141707939000 == 
[p1 |-> {"p2", "p3"}, p2 |-> {}, p3 |-> {}]
----

\* CONSTANT definitions @modelParameterConstants:3PARENT
const_1741878141707940000 == 
[p1 |-> {}, p2 |-> {"p1"}, p3 |-> {}]
----

\* Constant expression definition @modelExpressionEval
const_expr_1741878141707941000 == 
\A p \in P : (PARENT[p] = {} \/ Cardinality(PARENT[p]) = 1)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1741878141707941000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_1741878141707942000 ==
FALSE/\configuration = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1741878141707943000 ==
FALSE/\configuration' = configuration
----
=============================================================================
\* Modification History
\* Created Thu Mar 13 20:32:21 IST 2025 by stanly
