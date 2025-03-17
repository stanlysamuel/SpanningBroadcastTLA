---- MODULE MC ----
EXTENDS SpanningBroadcast, TLC

\* CONSTANT definitions @modelParameterConstants:0P
const_174218111266351000 == 
{"p1", "p2", "p3"}
----

\* CONSTANT definitions @modelParameterConstants:1ROOT
const_174218111266352000 == 
{"p1"}
----

\* CONSTANT definitions @modelParameterConstants:2CHILDREN
const_174218111266353000 == 
[p1 |-> {"p2", "p3"}, p2 |-> {}, p3 |-> {}]
----

\* CONSTANT definitions @modelParameterConstants:3PARENT
const_174218111266354000 == 
[p1 |-> {}, p2 |-> {"p1", "p2"}, p3 |-> {}]
----

\* Constant expression definition @modelExpressionEval
const_expr_174218111266355000 == 
CHILDREN[P]
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_174218111266355000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_174218111266356000 ==
FALSE/\configuration = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_174218111266357000 ==
FALSE/\configuration' = configuration
----
=============================================================================
\* Modification History
\* Created Mon Mar 17 08:41:52 IST 2025 by stanly
