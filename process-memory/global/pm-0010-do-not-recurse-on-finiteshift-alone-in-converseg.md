---
id: pm-0010-do-not-recurse-on-finiteshift-alone-in-converseg
type: refuted-route
status: active
coarse_node: global
created: {cycle: 22, request_id: 123}
---

In the converse game of paper lines 1569-1570, `FiniteShift s t` alone is too weak as the recursive invariant. For the front consisting of all four-element subsets of the naturals, `s={0,1,2}` and `t={1}` are finite-shift related and both nonterminal, but the legal right extension `{1,3}` cannot be a shifted prefix of any infinite set whose unshifted prefix extends `{0,1,2}`: such a shifted enumeration must begin `1,2`. The paper's reachable states carry more information, namely a finite bridge `u_i`: while left is nonterminal, `u_i` is its prescribed one-point extension; while right is nonterminal, right is the finite tail of `u_i`; terminal sides remain corresponding initial segments. Adjoining the right response (or a fresh dummy point for a terminal right side) preserves this bridge, and only at terminal nodes is it converted to `FiniteShift`.
