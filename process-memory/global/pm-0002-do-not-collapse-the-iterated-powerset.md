---
id: pm-0002-do-not-collapse-the-iterated-powerset
type: constraint
status: active
coarse_node: global
created: {cycle: 1, request_id: 1}
---

The configured target `cor PowerQPresBqo` concerns the full well-founded hierarchy of nonempty iterated powersets, not the first-level domination order on Set Q. Paper lines 1362-1374 define transfinite iteration, and lines 1404-1419 give four atom/set cases. A faithful Lean representation therefore needs tagged well-founded PSet-style trees (or an equivalent extensional quotient); plain Set Q is sufficient only for the separate Rado target at lines 985-987.
