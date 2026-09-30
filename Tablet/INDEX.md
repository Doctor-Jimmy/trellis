# Tablet Index

| Name | Env | Kind | Status | Labels | Title | Imports |
|------|-----|------|--------|--------|-------|---------|
| BadMultiSequence | definition | definition | closed | - | - | LocallyConstant, ShiftMap |
| BaireContinuous | definition | definition | closed | - | - | PrefixAgree |
| BlockSigma | definition | definition | closed | - | - | OrbitPoint |
| BlockSigmaContinuous | lemma | proof | open | - | - | BlockSigma, OrbitBlockCoverage, PrefixAgree |
| BlockSigmaEmbedding | lemma | proof | open | - | - | BlockSigma, IncSeq, OrbitBlockCoverage |
| BlockSigmaIntertwines | lemma | proof | open | - | - | BlockSigma, OrbitBlockCoverage, RightComp, SuccSeq |
| Bqo | definition | definition | closed | - | - | BadMultiSequence, LocallyConstant |
| ContMor | definition | definition | closed | - | - | ContinuousHom |
| ContMorEq | definition | definition | closed | - | - | ContMor |
| ContinuousHom | definition | definition | closed | - | - | BaireContinuous |
| EmapLemma | lemma | proof | open | - | - | BlockSigmaContinuous, BlockSigmaEmbedding, BlockSigmaIntertwines, ContMor, FirstMovedPoint, RightComp, ShiftMap |
| FirstMovedPoint | lemma | proof | open | - | - | IncSeqId, IncSeqPointwiseLe |
| GoodMultiSequence | definition | definition | closed | - | - | LocallyConstant, ShiftMap |
| IncSeq | definition | definition | closed | - | - | Preamble |
| IncSeqComp | definition | definition | closed | - | - | IncSeq |
| IncSeqId | definition | definition | closed | - | - | IncSeq |
| IncSeqPointwiseLe | lemma | proof | open | - | - | IncSeq |
| LocallyConstant | definition | definition | closed | - | - | MultiSequence, PrefixAgree |
| MainProp | theorem | proof | open | - | MainProp | ContMorEq, EmapLemma, RmapLemma |
| MultiSequence | definition | definition | closed | - | - | IncSeq |
| OrbitBlock | definition | definition | closed | - | - | OrbitPoint |
| OrbitBlockCoverage | lemma | proof | open | - | - | OrbitBlock, OrbitEmbedding, OrbitUnbounded |
| OrbitEmbedding | lemma | proof | open | - | - | IncSeq, OrbitPoint |
| OrbitPoint | definition | definition | closed | - | - | IncSeq |
| OrbitUnbounded | lemma | proof | open | - | - | OrbitEmbedding, OrbitPoint |
| Preamble | preamble | preamble | closed | - | - | - |
| PrefixAgree | definition | definition | closed | - | - | IncSeq |
| RightComp | definition | definition | closed | - | - | IncSeqComp |
| RmapLemma | lemma | proof | open | - | - | ContMor, FirstMovedPoint, OrbitEmbedding, RightComp, ShiftMap |
| ShiftMap | definition | definition | closed | - | - | RightComp, SuccSeq |
| SuccSeq | definition | definition | closed | - | - | IncSeq |

**Total:** 30 nodes | **Closed:** 19 | **Open:** 11
