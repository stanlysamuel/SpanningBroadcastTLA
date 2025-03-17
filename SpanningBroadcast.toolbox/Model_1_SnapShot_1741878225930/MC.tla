---- MODULE MC ----
EXTENDS SpanningBroadcast, TLC

\* CONSTANT definitions @modelParameterConstants:0P
const_1741878223899951000 == 
{"p1", "p2", "p3"}
----

\* CONSTANT definitions @modelParameterConstants:1ROOT
const_1741878223899952000 == 
{"p1"}
----

\* CONSTANT definitions @modelParameterConstants:2CHILDREN
const_1741878223899953000 == 
[p1 |-> {"p2", "p3"}, p2 |-> {}, p3 |-> {}]
----

\* CONSTANT definitions @modelParameterConstants:3PARENT
const_1741878223899954000 == 
[p1 |-> {}, p2 |-> {"p1", "p2"}, p3 |-> {}]
----

\* Constant expression definition @modelExpressionEval
const_expr_1741878223899955000 == 
\A p \in P : (PARENT[p] = {} \/ Cardinality(PARENT[p]) = 1)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1741878223899955000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_1741878223899956000 ==
FALSE/\configuration = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1741878223899957000 ==
FALSE/\configuration' = configuration
----
=============================================================================
\* Modification History
\* Created Thu Mar 13 20:33:43 IST 2025 by stanly
