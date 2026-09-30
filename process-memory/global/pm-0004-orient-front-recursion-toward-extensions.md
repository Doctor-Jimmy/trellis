---
id: pm-0004-orient-front-recursion-toward-extensions
type: refuted-route
status: active
coarse_node: global
created: {cycle: 5, request_id: 33}
---

The recursion at paper lines 1559-1563 defines `TildeF(s)` using `TildeF(t)` for strict extensions `t` of `s`. In Lean, `WellFounded r` permits a recursive call from `s` to `t` when `r t s`; therefore the required relation is `r child parent` iff `parent` is a proper initial segment of `child`. A theorem whose relation is instead `r shorter longer` has the opposite orientation and cannot justify this recursion, even though that relation is trivially well-founded by decreasing finite-set cardinality. Add or repair an extension-oriented well-foundedness theorem before constructing `TildeF`.
