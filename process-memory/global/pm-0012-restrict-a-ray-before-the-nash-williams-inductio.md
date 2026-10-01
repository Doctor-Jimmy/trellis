---
id: pm-0012-restrict-a-ray-before-the-nash-williams-inductio
type: refuted-route
status: active
coarse_node: global
created: {cycle: 52, request_id: 226}
---

In the Nash-Williams diagonal construction, applying the induction hypothesis to the full ray F_n only returns some infinite homogeneous restriction base inside X/n; it cannot be required afterward to lie in an independently prescribed nested tail A. Infinite subsets of X/n may be disjoint. At each stage one must first form the restricted front K = F_n|A, observe that its prefix tree is a subtree of the ray tree and hence has smaller rank than F, and apply the induction hypothesis to K. The resulting base is then contained in A by construction, exactly as in the paper's recursive use of `F_{n_k}|(X_{k-1}/n_k)`.
