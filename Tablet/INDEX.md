# Tablet Index

| Name | Env | Kind | Status | Labels | Title | Imports |
|------|-----|------|--------|--------|-------|---------|
| BadMultiSequence | definition | definition | closed | - | - | LocallyConstant, ShiftMap |
| BaireContinuous | definition | definition | closed | - | - | PrefixAgree |
| BetterRel | definition | definition | closed | - | - | ContinuousRelHom, ShiftMap |
| BlockSigma | definition | definition | closed | - | - | OrbitPoint |
| BlockSigmaContinuous | lemma | proof | open | - | - | BlockSigma, OrbitBlockCoverage, PrefixAgree |
| BlockSigmaEmbedding | lemma | proof | open | - | - | BlockSigma, IncSeq, OrbitBlockCoverage |
| BlockSigmaIntertwines | lemma | proof | open | - | - | BlockSigma, OrbitBlockCoverage, RightComp, SuccSeq |
| BooleanInfinitePigeonhole | lemma | proof | open | - | Infinite pigeonhole | Preamble |
| Bqo | definition | definition | closed | - | - | BadMultiSequence, LocallyConstant |
| BqoIffGeneralShift | corollary | proof | open | - | - | BadMultiSequence, Bqo, GBetterRel, GBetterRelIff, IncSeqId, RightComp, ShiftMap, SuccSeq |
| ContMor | definition | definition | closed | - | - | ContinuousHom |
| ContMorEq | definition | definition | closed | - | - | ContMor |
| ContinuousHom | definition | definition | closed | - | - | BaireContinuous |
| ContinuousRelHom | definition | definition | closed | - | - | LocallyConstant |
| EmapLemma | lemma | proof | open | - | - | BlockSigmaContinuous, BlockSigmaEmbedding, BlockSigmaIntertwines, ContMor, FirstMovedPoint, RightComp, ShiftMap |
| FirstMovedPoint | lemma | proof | open | - | - | IncSeqId, IncSeqPointwiseLe |
| Front | definition | definition | closed | - | Explicit front | FrontBase, InitialSegment, ProperPrefixSet |
| FrontBase | definition | definition | closed | - | - | Preamble |
| FrontRayClosure | lemma | proof | open | - | Ray closure | Front, Ray, TailSet |
| FrontRestrict | definition | definition | closed | - | - | Preamble |
| FrontRestriction | lemma | proof | open | - | Restriction closure | Front, FrontRestrict |
| FrontTreeWellFounded | lemma | proof | open | - | Well-founded prefix tree | Front, PrefixTree, ProperInitialSegment |
| GBetterRel | definition | definition | closed | - | - | ContinuousRelHom, RightComp |
| GBetterRelIff | theorem | proof | open | - | g-BQO | BetterRel, Bqo, GBetterRel, IncSeqId, MainProp |
| GoodMultiSequence | definition | definition | closed | - | - | LocallyConstant, ShiftMap |
| IncSeq | definition | definition | closed | - | - | Preamble |
| IncSeqComp | definition | definition | closed | - | - | IncSeq |
| IncSeqId | definition | definition | closed | - | - | IncSeq |
| IncSeqPointwiseLe | lemma | proof | open | - | - | IncSeq |
| InitialSegment | definition | definition | closed | - | - | Preamble |
| LocallyConstant | definition | definition | closed | - | - | MultiSequence, PrefixAgree |
| MainProp | theorem | proof | open | - | MainProp | ContMorEq, EmapLemma, RmapLemma |
| MultiSequence | definition | definition | closed | - | - | IncSeq |
| NashWilliams | theorem | proof | open | - | Nash--Williams | BooleanInfinitePigeonhole, Front, FrontRayClosure, FrontRestrict, FrontRestriction, FrontTreeWellFounded |
| OrbitBlock | definition | definition | closed | - | - | OrbitPoint |
| OrbitBlockCoverage | lemma | proof | open | - | - | OrbitBlock, OrbitEmbedding, OrbitUnbounded |
| OrbitEmbedding | lemma | proof | open | - | - | IncSeq, OrbitPoint |
| OrbitPoint | definition | definition | closed | - | - | IncSeq |
| OrbitUnbounded | lemma | proof | open | - | - | OrbitEmbedding, OrbitPoint |
| Preamble | preamble | preamble | closed | - | - | - |
| PrefixAgree | definition | definition | closed | - | - | IncSeq |
| PrefixTree | definition | definition | closed | - | - | InitialSegment |
| ProperInitialSegment | definition | definition | closed | - | - | InitialSegment |
| ProperPrefixSet | definition | definition | closed | - | - | Preamble |
| Ray | definition | definition | closed | - | - | Preamble |
| RightComp | definition | definition | closed | - | - | IncSeqComp |
| RmapLemma | lemma | proof | open | - | - | ContMor, FirstMovedPoint, OrbitEmbedding, RightComp, ShiftMap |
| ShiftMap | definition | definition | closed | - | - | RightComp, SuccSeq |
| SubFrontCharacterization | lemma | proof | open | - | Sub-fronts | Front, FrontRestrict, FrontRestriction |
| SuccSeq | definition | definition | closed | - | - | IncSeq |
| SuperNW | theorem | proof | open | - | - | NashWilliams, SuperSequence |
| SuperSequence | definition | definition | closed | - | - | Front |
| TailSet | definition | definition | closed | - | - | Preamble |

**Total:** 52 nodes | **Closed:** 32 | **Open:** 20
