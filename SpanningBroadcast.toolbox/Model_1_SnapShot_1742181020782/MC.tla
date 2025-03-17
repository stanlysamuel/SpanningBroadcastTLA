---- MODULE MC ----
EXTENDS SpanningBroadcast, TLC

\* CONSTANT definitions @modelParameterConstants:0P
const_17421810182219000 == 
{"p1", "p2", "p3"}
----

\* CONSTANT definitions @modelParameterConstants:1ROOT
const_174218101822110000 == 
{"p1"}
----

\* CONSTANT definitions @modelParameterConstants:2CHILDREN
const_174218101822111000 == 
[p1 |-> {"p2", "p3"}, p2 |-> {}, p3 |-> {}]
----

\* CONSTANT definitions @modelParameterConstants:3PARENT
const_174218101822112000 == 
[p1 |-> {}, p2 |-> {"p1", "p2"}, p3 |-> {}]
----

\* Constant expression definition @modelExpressionEval
const_expr_174218101822113000 == 
[P -> [CHILDREN[P] -> BOOLEAN]]
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_174218101822113000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_174218101822114000 ==
FALSE/\configuration = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_174218101822115000 ==
FALSE/\configuration' = configuration
----
=============================================================================
\* Modification History
\* Created Mon Mar 17 08:40:18 IST 2025 by stanly
