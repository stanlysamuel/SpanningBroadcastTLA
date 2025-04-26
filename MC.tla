---- MODULE MC ----
EXTENDS TLC, SpanningBroadcast

MC_P == {"A", "B", "C"}
MC_ROOT == {"A"}
MC_CHILDREN == [A |-> {"B", "C"}, B |-> {}, C |-> {}]
MC_PARENT == [A |-> {}, B |-> {"A"}, C |-> {"A"}]


====