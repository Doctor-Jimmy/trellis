# Tablet Index

| Name | Env | Kind | Status | Labels | Title | Imports |
|------|-----|------|--------|--------|-------|---------|
| BadMultiRestrict | lemma | proof | open | - | Badness under restriction | BadMultiSequence, MultiSequenceRestrict, RestrictionShift |
| BadMultiSequence | definition | definition | closed | - | - | LocallyConstant, ShiftMap |
| BadMultiToSuper | lemma | proof | open | - | Multi-sequence badness gives super-sequence badness | BadMultiSequence, BadSuperSequence, DecidingFrontSet, DecidingPrefix, DecidingValue |
| BadPairSequence | definition | definition | closed | - | Bad sequence of sequences | IncreasingPair |
| BadSuperRestrict | lemma | proof | open | - | Badness under sub-front restriction | BadSuperSequence, SuperSequenceRestrict |
| BadSuperSequence | definition | definition | closed | - | - | FiniteShift, SuperSequence |
| BadSuperToBase | lemma | proof | open | - | Super-sequence badness gives base badness | BadSuperSequence, BaseBad, BaseLocallyConstant, SuperSequenceExtension |
| BaireContinuous | definition | definition | closed | - | - | PrefixAgree |
| BaseBad | definition | definition | closed | - | - | BaseMultiSequence, BaseShift |
| BaseBqoRestriction | lemma | proof | open | - | Base invariance of the bqo restriction property | BaseLocallyConstant, BaseRestrict, Bqo, InfiniteSetEnumeration, PerfectMultiSequence, ShiftDichotomy |
| BaseIncSeq | definition | definition | closed | - | - | IncSeq |
| BaseLocallyConstant | definition | definition | closed | - | - | BaseMultiSequence, PrefixAgree |
| BaseMultiSequence | definition | definition | closed | - | - | BaseIncSeq |
| BasePerfect | definition | definition | closed | - | - | BaseMultiSequence, BaseShift |
| BaseRestrict | definition | definition | closed | - | - | BaseMultiSequence, IncSeqComp, MultiSequence |
| BaseRightComp | definition | definition | closed | - | - | BaseIncSeq, RightComp |
| BaseShift | definition | definition | closed | - | - | BaseIncSeq, ShiftMap |
| BetterRel | definition | definition | closed | - | - | ContinuousRelHom, ShiftMap |
| BlockSigma | definition | definition | closed | - | - | OrbitPoint |
| BlockSigmaContinuous | lemma | proof | open | - | - | BlockSigma, OrbitBlockCoverage, PrefixAgree |
| BlockSigmaEmbedding | lemma | proof | open | - | - | BlockSigma, IncSeq, OrbitBlockCoverage |
| BlockSigmaIntertwines | lemma | proof | open | - | - | BlockSigma, OrbitBlockCoverage, RightComp, SuccSeq |
| BooleanInfinitePigeonhole | lemma | proof | open | - | Infinite pigeonhole | Preamble |
| Bqo | definition | definition | closed | - | - | BadMultiSequence, LocallyConstant |
| BqoIffGeneralShift | corollary | proof | open | - | - | BadMultiSequence, Bqo, GBetterRel, GBetterRelIff, IncSeqId, RightComp, ShiftMap, SuccSeq |
| CardinalityFront | definition | definition | closed | - | Constant-cardinality front | Preamble |
| CardinalityFrontIsFront | lemma | proof | open | - | - | CardinalityFront, Front |
| ContMor | definition | definition | closed | - | - | ContinuousHom |
| ContMorEq | definition | definition | closed | - | - | ContMor |
| ContinuousHom | definition | definition | closed | - | - | BaireContinuous |
| ContinuousRelHom | definition | definition | closed | - | - | LocallyConstant |
| DecidingFront | lemma | proof | open | - | Minimal deciding prefixes form a front | DecidingFrontSet, Front |
| DecidingFrontSet | definition | definition | closed | - | - | DecidingPrefix, ProperInitialSegment |
| DecidingPrefix | definition | definition | closed | - | - | LocallyConstant, ProperInitialSegment, ProperPrefixSet |
| DecidingValue | lemma | proof | open | - | Value map on the deciding front | DecidingFront, FinitePrefixExtension |
| EmapLemma | lemma | proof | open | - | - | BlockSigmaContinuous, BlockSigmaEmbedding, BlockSigmaIntertwines, ContMor, FirstMovedPoint, RightComp, ShiftMap |
| FinitePrefixExtension | lemma | proof | open | - | Infinite extension of a finite prefix | IncSeq, ProperPrefixSet |
| FiniteShift | definition | definition | closed | - | - | ProperPrefixSet, ShiftMap |
| FirstMovedPoint | lemma | proof | open | - | - | IncSeqId, IncSeqPointwiseLe |
| Front | definition | definition | closed | - | Explicit front | FrontBase, InitialSegment, ProperPrefixSet |
| FrontBase | definition | definition | closed | - | - | Preamble |
| FrontPrefix | definition | definition | closed | - | - | Front, IncSeq |
| FrontPrefixExists | lemma | proof | open | - | Front member existence | FrontPrefix |
| FrontPrefixUnique | lemma | proof | open | - | Front member uniqueness | FrontPrefix |
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
| IncreasingPair | definition | definition | closed | - | - | Preamble |
| InfiniteSetEnumeration | lemma | proof | open | - | Increasing enumeration of an infinite set | IncSeq |
| InitialSegment | definition | definition | closed | - | - | Preamble |
| LocallyConstant | definition | definition | closed | - | - | MultiSequence, PrefixAgree |
| MainProp | theorem | proof | open | - | MainProp | ContMorEq, EmapLemma, RmapLemma |
| MultiSequence | definition | definition | closed | - | - | IncSeq |
| MultiSequenceRestrict | definition | definition | closed | - | - | IncSeqComp, MultiSequence |
| NashWilliams | theorem | proof | open | - | Nash--Williams | BooleanInfinitePigeonhole, Front, FrontRayClosure, FrontRestrict, FrontRestriction, FrontTreeWellFounded |
| NoBadPerfectSuper | lemma | proof | open | - | A super-sequence is not both perfect and bad | BadSuperSequence, FrontPrefixExists, InfiniteSetEnumeration, PerfectSuperSequence |
| OrbitBlock | definition | definition | closed | - | - | OrbitPoint |
| OrbitBlockCoverage | lemma | proof | open | - | - | OrbitBlock, OrbitEmbedding, OrbitUnbounded |
| OrbitEmbedding | lemma | proof | open | - | - | IncSeq, OrbitPoint |
| OrbitPoint | definition | definition | closed | - | - | IncSeq |
| OrbitUnbounded | lemma | proof | open | - | - | OrbitEmbedding, OrbitPoint |
| PerfectBaseToSuper | lemma | proof | open | - | Perfect base extensions yield perfect sub-super-sequences | BaseRestrict, FrontRestriction, PerfectMultiSequence, PerfectSuperSequence, SuperSequenceExtension, SuperSequenceRestrict |
| PerfectMultiRestrict | lemma | proof | open | - | Perfectness under restriction | MultiSequenceRestrict, PerfectMultiSequence, RestrictionShift |
| PerfectMultiSequence | definition | definition | closed | - | - | MultiSequence, ShiftMap |
| PerfectMultiToSuper | lemma | proof | open | - | Multi-sequence perfectness gives super-sequence perfectness | DecidingFrontSet, DecidingPrefix, PerfectMultiSequence, PerfectSuperSequence |
| PerfectSuperRestrict | lemma | proof | open | - | Perfectness under sub-front restriction | PerfectSuperSequence, SuperSequenceRestrict |
| PerfectSuperSequence | definition | definition | closed | - | - | FiniteShift, SuperSequence |
| PerfectSuperToBase | lemma | proof | open | - | Super-sequence perfectness gives base perfectness | BaseLocallyConstant, BasePerfect, PerfectSuperSequence, SuperSequenceExtension |
| PerfectSuperToMulti | lemma | proof | open | - | Perfect sub-super-sequences give perfect sub-multi-sequences | DecidingFrontSet, LocallyConstant, MultiSequenceRestrict, PerfectMultiSequence, PerfectSuperSequence, SuperSequenceRestrict |
| PowerWqoBadPairSequence | lemma | proof | open | - | Bad-witness characterization | BadPairSequence, SetDomination |
| Preamble | preamble | preamble | closed | - | - | - |
| PrefixAgree | definition | definition | closed | - | - | IncSeq |
| PrefixTree | definition | definition | closed | - | - | InitialSegment |
| ProperInitialSegment | definition | definition | closed | - | - | InitialSegment |
| ProperPrefixSet | definition | definition | closed | - | - | Preamble |
| QuadrupleHomogeneous | lemma | proof | open | - | Homogeneous quadruples | CardinalityFrontIsFront, NashWilliams |
| RadoEmbedding | theorem | proof | open | - | Rado embedding | InfiniteSetEnumeration, PowerWqoBadPairSequence, QuadrupleHomogeneous, RadoOrder, RelationEmbedding, TripleHomogeneous |
| RadoOrder | definition | definition | closed | - | Rado order | IncreasingPair |
| Ray | definition | definition | closed | - | - | Preamble |
| RelationEmbedding | definition | definition | closed | - | Relation embedding | Preamble |
| RestrictionLocallyConstant | lemma | proof | open | - | Restriction preserves local constancy | LocallyConstant, MultiSequenceRestrict |
| RestrictionShift | lemma | proof | open | - | Restriction and shift | MultiSequenceRestrict, ShiftMap |
| RightComp | definition | definition | closed | - | - | IncSeqComp |
| RmapLemma | lemma | proof | open | - | - | ContMor, FirstMovedPoint, OrbitEmbedding, RightComp, ShiftMap |
| SetDomination | definition | definition | closed | - | Domination on subsets | Preamble |
| ShiftDichotomy | lemma | proof | open | - | Perfect-or-bad shift dichotomy | BadMultiSequence, DecidingFront, DecidingValue, InfiniteSetEnumeration, MultiSequenceRestrict, NashWilliams, PerfectMultiSequence, RestrictionShift |
| ShiftMap | definition | definition | closed | - | - | RightComp, SuccSeq |
| SubFrontCharacterization | lemma | proof | open | - | Sub-fronts | Front, FrontRestrict, FrontRestriction |
| Subarr | corollary | proof | open | lem:subarr | Sub-arrays and super-sequences | BadMultiRestrict, BadMultiToSuper, BadSuperRestrict, BaseBqoRestriction, DecidingFront, DecidingValue, NoBadPerfectSuper, PerfectBaseToSuper, PerfectSuperToMulti, RestrictionLocallyConstant, ShiftDichotomy, SuperSequenceExtension |
| SuccSeq | definition | definition | closed | - | - | IncSeq |
| SuperNW | theorem | proof | open | - | - | NashWilliams, SuperSequence |
| SuperSequence | definition | definition | closed | - | - | Front |
| SuperSequenceExtension | lemma | proof | open | - | Extension from a front | BaseLocallyConstant, FrontPrefixExists, FrontPrefixUnique, SuperSequence |
| SuperSequenceRestrict | definition | definition | closed | - | - | SuperSequence |
| TailSet | definition | definition | closed | - | - | Preamble |
| TripleHomogeneous | lemma | proof | open | - | Homogeneous triples | CardinalityFrontIsFront, NashWilliams |

**Total:** 103 nodes | **Closed:** 55 | **Open:** 48
