---- MODULE MC ----
EXTENDS SpanningBroadcast, TLC

\* CONSTANT definitions @modelParameterConstants:0P
const_1741878345533965000 == 
{"p1", "p2", "p3"}
----

\* CONSTANT definitions @modelParameterConstants:1ROOT
const_1741878345533966000 == 
{"p1"}
----

\* CONSTANT definitions @modelParameterConstants:2CHILDREN
const_1741878345533967000 == 
[p1 |-> {"p2", "p3"}, p2 |-> {}, p3 |-> {}]
----

\* CONSTANT definitions @modelParameterConstants:3PARENT
const_1741878345533968000 == 
[p1 |-> {}, p2 |-> {"p1", "p2"}, p3 |-> {}]
----

\* Constant expression definition @modelExpressionEval
const_expr_1741878345533969000 == 
TCTypeOK
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1741878345533969000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_1741878345533970000 ==
FALSE/\configuration = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1741878345533971000 ==
FALSE/\configuration' = configuration
----
=============================================================================
\* Modification History
\* Created Thu Mar 13 20:35:45 IST 2025 by stanly
