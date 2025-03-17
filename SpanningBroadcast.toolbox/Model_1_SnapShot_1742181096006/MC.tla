---- MODULE MC ----
EXTENDS SpanningBroadcast, TLC

\* CONSTANT definitions @modelParameterConstants:0P
const_174218109390223000 == 
{"p1", "p2", "p3"}
----

\* CONSTANT definitions @modelParameterConstants:1ROOT
const_174218109390324000 == 
{"p1"}
----

\* CONSTANT definitions @modelParameterConstants:2CHILDREN
const_174218109390325000 == 
[p1 |-> {"p2", "p3"}, p2 |-> {}, p3 |-> {}]
----

\* CONSTANT definitions @modelParameterConstants:3PARENT
const_174218109390326000 == 
[p1 |-> {}, p2 |-> {"p1", "p2"}, p3 |-> {}]
----

\* Constant expression definition @modelExpressionEval
const_expr_174218109390327000 == 
P
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_174218109390327000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_174218109390328000 ==
FALSE/\configuration = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_174218109390329000 ==
FALSE/\configuration' = configuration
----
=============================================================================
\* Modification History
\* Created Mon Mar 17 08:41:33 IST 2025 by stanly
