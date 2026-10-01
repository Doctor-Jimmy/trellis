---
id: pm-0007-universe-generalize-bqo-before-the-full-powerset
type: interface-decision
status: superseded
superseded_by: pm-0009-universe-generalize-bqo-and-lift-countable-branc
coarse_node: global
created: {cycle: 10, request_id: 63}
---

A faithful tagged hierarchy over `Q : Type u` with arbitrary nonempty `Type u`-indexed nodes lives in `Type (u+1)`. The current `Bqo`, `MultiSequence`, `LocallyConstant`, and `BadMultiSequence` bind carriers in universe 0, so `Bqo (PowerRel r)` cannot even be formed for the hierarchy over a universe-0 base. Generalize the existing carrier interfaces in place before building `PowerQ`; do not replace the full hierarchy by countable codes or introduce a disconnected large-universe bqo predicate.
