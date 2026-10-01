---
id: pm-0008-require-a-nontrivial-front-for-the-singleton-til
type: interface-decision
status: active
coarse_node: global
created: {cycle: 14, request_id: 83}
---

Paper lines 1559-1564 define TildeF on the prefix tree of a front and form the singleton-indexed sequence only when the front is nontrivial. If F is the trivial front {empty}, no singleton belongs to PrefixTree F, so ConverseGame must assume empty is not in F (or an equivalent nontriviality hypothesis). In the hereditary bqo converse this hypothesis is discharged for the deciding front: if the empty prefix decided a locally constant multi-sequence, the map would be constant, and reflexivity of the base quasi-order would contradict its badness.
