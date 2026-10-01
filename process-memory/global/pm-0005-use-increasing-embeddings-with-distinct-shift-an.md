---
id: pm-0005-use-increasing-embeddings-with-distinct-shift-an
type: interface-decision
status: active
coarse_node: global
created: {cycle: 6, request_id: 41}
---

Represent infinite subsets of the naturals and the paper's monoid IIf by strictly increasing embeddings Nat into Nat, and represent continuity into a discrete type by finite-prefix local constancy (paper lines 1264-1271 and 1690-1709). Keep two composition actions distinct. Shift is right composition of the varying enumeration: `ShiftMap x = x composed with SuccSeq`. Restriction to the fixed subbase enumerated by `z` is left-fixed composition: the varying enumeration is `z composed with x`, hence `MultiSequenceRestrict h z x = h (IncSeqComp z x)`. In the Tablet convention `RightComp z x = x composed with z`, so it must not define subbase restriction. The noncommuting witness `z(n)=2*n`, `x(n)=n+1` gives `(RightComp z x)(0)=1` but `(IncSeqComp z x)(0)=2`. For an arbitrary base `X`, the fixed enumeration must have type `BaseIncSeq X`.
