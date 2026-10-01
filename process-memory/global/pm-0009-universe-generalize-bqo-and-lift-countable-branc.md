---
id: pm-0009-universe-generalize-bqo-and-lift-countable-branc
type: interface-decision
status: active
coarse_node: global
created: {cycle: 18, request_id: 103}
---

A faithful tagged hierarchy over `Q : Type u` with arbitrary nonempty `Type u`-indexed nodes lives in `Type (u+1)`, so `Bqo`, `MultiSequence`, `LocallyConstant`, and `BadMultiSequence` must remain universe-polymorphic before `Bqo (PowerRel r)` can be formed. Moreover, the constructor of the adopted `PowerQ` requires its branch index in exactly `Type u`: for an arbitrary universe `u`, plain `Nat : Type 0` does not elaborate as that index. Hereditarily countable erasures, the countable nodes in the front-tree recursion of paper lines 1559-1563, and countable tail nodes used at lines 1592-1595 must use `ULift.{u}` of `Nat` or of the relevant countable subtype. The internal hereditary code may still be `Nat`-branching, and a nonempty countable family indexed by `I : Type u` is represented by a surjection `Nat -> I` followed by this universe lift.
