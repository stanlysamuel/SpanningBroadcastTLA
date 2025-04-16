module spanningbroadcast {

    // Constants
    // const P: Set[str]
    // const ROOT: Set[str]
    // const CHILDREN: str -> Set[str]
    // const PARENT: str -> Set[str]

    pure val P = Set("p1", "p2", "p3")
    pure val ROOT = Set("p1")
    pure val CHILDREN = Map("p1" -> Set("p2", "p3"), "p2" -> Set(), "p3" -> Set())
    pure val PARENT = Map("p1" -> Set(), "p2" -> Set("p1"), "p3" -> Set("p1"))

    // Process state
    var configuration: str -> {inbuf: bool, outbuf: str -> bool, terminated: bool}

    // Initial state action
    action init = {
        configuration' = P.mapBy(x => {inbuf: if (x.in(ROOT)) true else false, 
                                outbuf: P.mapBy(x => false), 
                                terminated: false})
    }

    // Message sending action
    action SendFromPToQ =  {
        nondet p = oneOf(P)
        nondet q = oneOf(P)
        all{
        configuration.get(p).outbuf.get(q) == true,
        configuration' = configuration
            .put(q, {inbuf: true, outbuf: configuration.get(q).outbuf, terminated: configuration.get(q).terminated})
            .put(p, {inbuf: configuration.get(p).inbuf, outbuf: configuration.get(p).outbuf.put(q, false), terminated: configuration.get(p).terminated})
        }
    }
    
    // Computation action
    action Compute =  {
        nondet p = oneOf(P)
        all{
        configuration.get(p).inbuf == true,
        configuration' = configuration
            .put(p, {inbuf: false, outbuf: P.mapBy(q => if (q.in(CHILDREN.get(p))) true else false), terminated: true})
        }
    }
    
    // Next state relation
    action step = {
        any{
            SendFromPToQ,
            Compute,
        }
    }

// Invariant on non-termination (Safety)
val no_termination = P.exists(p => configuration.get(p).terminated == false)

// Invariant on termination (Liveness) [Note: Doesn't seem to be supported yet]
temporal termination = eventually(P.forall(p => configuration.get(p).terminated == true))
}