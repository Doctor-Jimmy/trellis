---
id: pm-0011-quantify-a-sub-front-s-base-existentially
type: constraint
status: active
coarse_node: global
created: {cycle: 52, request_id: 226}
---

For a front F on X and F' contained in F, the paper's sub-front characterization is `(there exists Y with Front F' Y) iff there exists an infinite Z contained in X with F' = FrontRestrict F Z`. A statement `Front F' Y iff exists Z, ...` with Z independent of the fixed Y is false: take F to be the singleton front `[Nat]^1`, F'=F, and Y empty. The right side holds with Z=Nat, while `Front F empty` contradicts the required infinitude of the base. The trivial front is why one should existentially quantify the front base rather than simply force Z=Y in all cases.
