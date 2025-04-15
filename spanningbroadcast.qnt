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

    // // Initial value functions
    // def InitInbufType(p): bool =
    //     if (p.in(ROOT)) true else false

    // def InitOutbufType(): str -> bool =
    //     P.mapBy(x => false)

    // pure def InitTerminatedType() = false

    // Initial state action
    action SBInit = {
        configuration' = P.mapBy(x => {inbuf: if (x.in(ROOT)) true else false, 
                                outbuf: P.mapBy(x => false), 
                                terminated: false})
    }

    // // Message sending action
    // action SendFromPToQ(p, q) = {
    //     configuration.get(p).outbuf.get(q) and
    //     configuration' = configuration
    //                     .set(q, configuration.get(q).with(inbuf = true))
    //                     .set(p, configuration.get(p).with(outbuf = configuration.get(p).outbuf.set(q, false)))
    // }

    // // Computation action
    // action Compute(p) = {
    //     configuration.get(p).inbuf and
    //     configuration' = configuration
    //                     .set(p, {inbuf: false,
    //                             outbuf: Map(q -> (q in CHILDREN.get(p)) | q <- P),
    //                             terminated: true})
    // }

    // // Next state relation
    // action SBNext() = {
    //     some(p <- P, q <- P)(Compute(p) or SendFromPToQ(p, q))
    // }

    // module SpanningBroadcast {
//   // Constants
//   const P: Set[int]
//   const ROOT: Set[int]
//   const CHILDREN: Map[int, Set[int]]
//   const PARENT: Map[int, Set[int]]

//   // Type definitions
//   type ParentType = Set[int]
//   type ChildrenType = Set[int]
//   type TerminatedType = bool
//   type OutbufType = Map[int, bool]
//   type InbufType = bool

//   // Process state
//   var configuration: Map[int, {inbuf: bool, outbuf: Map[int, bool], terminated: bool}]

//   // Initial value functions
//   def InitInbufType(p): bool =
//     if (p in ROOT) true else false

//   def InitOutbufType(): Map[int, bool] =
//     Map(q -> false | q <- P)

//   def InitTerminatedType(): bool = false

//   // Helper functions
//   def Inbuf(p): bool = configuration.get(p).inbuf
//   def Outbuf(p): Map[int, bool] = configuration.get(p).outbuf
//   def Terminated(p): bool = configuration.get(p).terminated
//   def OutbufQinP(p, q): bool = configuration.get(p).outbuf.get(q)

//   // Constants invariant
//   def SBConstOK(): bool =
//     // Constraints on P
//     Set.size(P) > 0 and
    
//     // Constraints on ROOT
//     Set.size(ROOT) == 1 and
//     all(p <- P)(p in ROOT implies Set.size(PARENT.get(p)) == 0) and
//     all(p <- ROOT)(p in P) and
    
//     // Constraints on PARENT and CHILDREN
//     all(p <- P)(PARENT.get(p) is Set[int]) and
//     all(p <- P)(CHILDREN.get(p) is Set[int]) and
//     all(p <- P)(Set.size(Set.intersect(PARENT.get(p), CHILDREN.get(p))) == 0) and
//     !(some(p <- P)(Set.size(PARENT.get(p)) == 0 and Set.size(CHILDREN.get(p)) == 0)) and
//     all(p <- P)(Set.size(PARENT.get(p)) == 0 or Set.size(PARENT.get(p)) == 1)

//   // Type invariant
//   def SBTypeOK(): bool =
//     configuration is Map[int, {inbuf: bool, outbuf: Map[int, bool], terminated: bool}]

//   // Initial state action
//   action SBInit() = {
//     configuration' = Map(p -> {inbuf: InitInbufType(p), 
//                              outbuf: InitOutbufType(), 
//                              terminated: false} 
//                        | p <- P)
//   }

//   // Message sending action
//   action SendFromPToQ(p, q) = {
//     configuration.get(p).outbuf.get(q) and
//     configuration' = configuration
//                       .set(q, configuration.get(q).with(inbuf = true))
//                       .set(p, configuration.get(p).with(outbuf = configuration.get(p).outbuf.set(q, false)))
//   }

//   // Computation action
//   action Compute(p) = {
//     configuration.get(p).inbuf and
//     configuration' = configuration
//                       .set(p, {inbuf: false,
//                               outbuf: Map(q -> (q in CHILDREN.get(p)) | q <- P),
//                               terminated: true})
//   }

//   // Next state relation
//   action SBNext() = {
//     some(p <- P, q <- P)(Compute(p) or SendFromPToQ(p, q))
//   }

//   // Temporal property
//   temporal SBSoundness() = {
//     eventually(all(p <- P)(Terminated(p)))
//   }

//   // System definition
//   system specification = {
//     SBInit(),
//     always(SBConstOK() and SBTypeOK()),
//     step(SBNext()),
//     SBSoundness()
//   }
// }
// 
}