# Tablet Index

| Name | Env | Kind | Status | Labels | Title | Imports |
|------|-----|------|--------|--------|-------|---------|
| BadMultiRestrict | lemma | proof | closed | - | Badness under restriction | BadMultiSequence, MultiSequenceRestrict, RestrictionShift |
| BadMultiSequence | definition | definition | closed | - | - | LocallyConstant, ShiftMap |
| BadMultiToNontrivialSuper | lemma | proof | closed | - | A bad multi-sequence has a nontrivial deciding front | BadMultiSequence, BadMultiToSuper, DecidingFront, DecidingFrontSet, DecidingValue, IncSeqId, ShiftMap |
| BadMultiToSuper | lemma | proof | closed | - | Multi-sequence badness gives super-sequence badness | BadMultiSequence, BadSuperSequence, DecidingFrontSet, DecidingPrefix, DecidingValue |
| BadPairSequence | definition | definition | closed | - | Bad sequence of sequences | IncreasingPair |
| BadSuperRestrict | lemma | proof | closed | - | Badness under sub-front restriction | BadSuperSequence, SuperSequenceRestrict |
| BadSuperSequence | definition | definition | closed | - | - | FiniteShift, SuperSequence |
| BadSuperToBase | lemma | proof | open | - | Super-sequence badness gives base badness | BadSuperSequence, BaseBad, BaseIncSeq, BaseLocallyConstant, BaseShift, FiniteShift, FrontPrefix, ProperPrefixSet, SuperSequence, SuperSequenceExtension |
| BaireContinuous | definition | definition | closed | - | - | PrefixAgree |
| BaseBad | definition | definition | closed | - | - | BaseMultiSequence, BaseShift |
| BaseBqoRestriction | lemma | proof | closed | - | Base invariance of the bqo restriction property | BaseLocallyConstant, BaseRestrict, Bqo, InfiniteSetEnumeration, PerfectMultiSequence, RestrictionLocallyConstant, ShiftDichotomy |
| BaseIncSeq | definition | definition | closed | - | - | IncSeq |
| BaseLocallyConstant | definition | definition | closed | - | - | BaseMultiSequence, PrefixAgree |
| BaseMultiSequence | definition | definition | closed | - | - | BaseIncSeq |
| BasePerfect | definition | definition | closed | - | - | BaseMultiSequence, BaseShift |
| BaseRestrict | definition | definition | closed | - | - | BaseMultiSequence, IncSeqComp, MultiSequence |
| BaseRightComp | definition | definition | closed | - | - | BaseIncSeq, RightComp |
| BaseShift | definition | definition | closed | - | - | BaseIncSeq, ShiftMap |
| BetterRel | definition | definition | closed | - | - | ContinuousRelHom, ShiftMap |
| BlockSigma | definition | definition | closed | - | - | OrbitPoint |
| BlockSigmaContinuous | lemma | proof | closed | - | - | BlockSigma, OrbitBlockCoverage, PrefixAgree |
| BlockSigmaEmbedding | lemma | proof | closed | - | - | BlockSigma, IncSeq, OrbitBlockCoverage |
| BlockSigmaIntertwines | lemma | proof | closed | - | - | BlockSigma, OrbitBlockCoverage, RightComp, SuccSeq |
| BooleanInfinitePigeonhole | lemma | proof | closed | - | Infinite pigeonhole | Preamble |
| Bqo | definition | definition | closed | - | - | BadMultiSequence, LocallyConstant |
| BqoHerCtblWellF | theorem | proof | closed | - | - | BqoHerCtblWqo, HerCtblWqoIffWellFounded |
| BqoHerCtblWqo | theorem | proof | closed | - | - | BadMultiToNontrivialSuper, BqoImpliesWqo, ConverseGame, PowerQPresBqo, TildeFHerCtbl, TildeFSingleton |
| BqoIffGeneralShift | corollary | proof | open | - | - | BadMultiSequence, Bqo, GBetterRel, GBetterRelIff, IncSeqId, RightComp, ShiftMap, SuccSeq |
| BqoImpliesWqo | lemma | proof | closed | - | Better quasi-order implies well quasi-order | Bqo |
| CardinalityFront | definition | definition | closed | - | Constant-cardinality front | Preamble |
| CardinalityFrontIsFront | lemma | proof | closed | - | - | CardinalityFront, Front, InfiniteSetEnumeration |
| ContMor | definition | definition | closed | - | - | ContinuousHom |
| ContMorEq | definition | definition | closed | - | - | ContMor |
| ContinuousHom | definition | definition | closed | - | - | BaireContinuous |
| ContinuousRelHom | definition | definition | closed | - | - | LocallyConstant |
| ConverseGame | lemma | proof | closed | - | Converse game | BadSuperSequence, FrontBridgeInit, FrontBridgeStep, FrontBridgeTerminal, HerCtblRel, PowerRelAtomAtom, PowerRelAtomNode, PowerRelNodeAtom, PowerRelNodeNode, TildeFSingleton |
| DecidingFront | lemma | proof | closed | - | Minimal deciding prefixes form a front | DecidingFrontAgreement, DecidingFrontMinimal, DecidingFrontSet, Front, InfiniteSetEnumeration |
| DecidingFrontAgreement | helper | proof | closed | - | Finite-prefix agreement | PrefixAgree, ProperPrefixSet |
| DecidingFrontInitialTrans | helper | proof | closed | - | Transitivity of finite initial segments | InitialSegment |
| DecidingFrontMinimal | helper | proof | closed | - | Minimal deciding prefix extraction | DecidingFrontInitialTrans, DecidingFrontSet |
| DecidingFrontSet | definition | definition | closed | - | - | DecidingPrefix, ProperInitialSegment |
| DecidingPrefix | definition | definition | closed | - | - | LocallyConstant, ProperInitialSegment, ProperPrefixSet |
| DecidingValue | lemma | proof | closed | - | Value map on the deciding front | DecidingFront, FinitePrefixExtension |
| EmapLemma | lemma | proof | closed | - | - | BlockSigmaContinuous, BlockSigmaEmbedding, BlockSigmaIntertwines, ContMor, FirstMovedPoint, RightComp, ShiftMap |
| FinitePrefixExtension | lemma | proof | closed | - | Infinite extension of a finite prefix | IncSeq, ProperPrefixSet |
| FiniteShift | definition | definition | closed | - | - | ProperPrefixSet, ShiftMap |
| FirstMovedPoint | lemma | proof | closed | - | - | IncSeqId, IncSeqPointwiseLe |
| Front | definition | definition | closed | - | Explicit front | FrontBase, InitialSegment, ProperPrefixSet |
| FrontBase | definition | definition | closed | - | - | Preamble |
| FrontBridge | definition | definition | closed | - | Finite bridge state | Front, FrontBridgeTail, PrefixTree, ProperInitialSegment |
| FrontBridgeInit | lemma | proof | closed | - | Initial bridge | FrontBridge, FrontTreeOrderedExtension, FrontTreeSingleton |
| FrontBridgeStep | lemma | proof | closed | - | Bridge response transition | FrontBridge, FrontBridgeTailInsert, FrontTreeOrderedExtension, InitialSegmentInsert |
| FrontBridgeTail | definition | definition | closed | - | Finite bridge tail | InitialSegment |
| FrontBridgeTailInsert | helper | proof | closed | - | Appending a larger point to the finite bridge tail | FrontBridgeTail |
| FrontBridgeTerminal | lemma | proof | closed | - | A terminal bridge gives a finite shift | FiniteShift, FrontBridge, InfiniteSetEnumeration |
| FrontNontrivialBase | helper | proof | closed | - | Nontrivial front members and base | Front |
| FrontPrefix | definition | definition | closed | - | - | Front, IncSeq |
| FrontPrefixExists | lemma | proof | closed | - | Front member existence | FrontPrefix |
| FrontPrefixUnique | lemma | proof | closed | - | Front member uniqueness | FrontPrefix |
| FrontRayBase | helper | proof | closed | - | Base of a nontrivial ray | Front, FrontNontrivialBase, FrontRayDense, FrontRayPrefixFree, Ray, TailSet |
| FrontRayClosure | lemma | proof | closed | - | Ray closure | Front, FrontNontrivialBase, FrontRayBase, FrontRayDense, FrontRayPrefixFree, Ray, TailSet |
| FrontRayDense | helper | proof | closed | - | Density of a ray | FrontNontrivialBase, Ray, TailSet |
| FrontRayPrefixFree | helper | proof | closed | - | Prefix-freeness of a ray | Front, Ray |
| FrontRestrict | definition | definition | closed | - | - | Preamble |
| FrontRestriction | lemma | proof | closed | - | Restriction closure | Front, FrontRestrict |
| FrontTreeImmediateExtensions | lemma | proof | closed | - | Immediate extensions in the front tree | Front, PrefixTree, ProperInitialSegment |
| FrontTreeOrderedExtension | lemma | proof | closed | - | All ordered one-point extensions remain in the tree | FrontTreeWellFounded |
| FrontTreeSingleton | lemma | proof | closed | - | Singletons belong to a nontrivial full-base tree | Front, PrefixTree |
| FrontTreeWellFounded | lemma | proof | closed | - | Well-founded prefix tree | Front, PrefixTree, ProperInitialSegment |
| GBetterRel | definition | definition | closed | - | - | ContinuousRelHom, RightComp |
| GBetterRelIff | theorem | proof | open | - | g-BQO | BetterRel, Bqo, ContinuousRelHom, DecidingFront, DecidingValue, Front, GBetterRel, IncSeq, IncSeqComp, IncSeqId, InfiniteSetEnumeration, LocallyConstant, MainProp, MultiSequenceRestrict, NashWilliams, PrefixAgree, ProperPrefixSet, RestrictionLocallyConstant, RightComp |
| GoodMultiSequence | definition | definition | closed | - | - | LocallyConstant, ShiftMap |
| HerCtblCode | definition | definition | closed | - | - | Preamble |
| HerCtblCodeErase | definition | definition | closed | - | - | HerCtblCode, PowerQ |
| HerCtblNodeClosure | lemma | proof | closed | - | Countable hereditary-node closure | HerCtblCodeErase, HerCtblPower, PowerPresentationEqEquivalence |
| HerCtblPower | definition | definition | closed | - | - | HereditarilyCountable |
| HerCtblPowerIsPreorder | lemma | proof | closed | - | The hereditary countable carrier is a preorder | HerCtblRel, PowerQIsPreorder |
| HerCtblRel | definition | definition | closed | - | - | HerCtblPower, PowerRel |
| HerCtblWqoIffWellFounded | helper | proof | closed | - | Hereditary WQO and strict well-foundedness | HerCtblNodeClosure, HerCtblPowerIsPreorder, HerCtblRel, PowerRelNodeNode, PowerRelRefl |
| HereditarilyCountable | definition | definition | closed | - | - | HerCtblCodeErase, PowerPresentationEq |
| HereditarilyCountableAtom | lemma | proof | closed | - | Atoms are hereditarily countable | HereditarilyCountable, PowerPresentationEqEquivalence |
| HereditarilyCountablePresentationInvariant | lemma | proof | closed | - | Hereditary countability is presentation invariant | HereditarilyCountable, PowerPresentationEqEquivalence |
| IncSeq | definition | definition | closed | - | - | Preamble |
| IncSeqComp | definition | definition | closed | - | - | IncSeq |
| IncSeqId | definition | definition | closed | - | - | IncSeq |
| IncSeqPointwiseLe | lemma | proof | closed | - | - | IncSeq |
| IncreasingPair | definition | definition | closed | - | - | Preamble |
| InfiniteSetEnumeration | lemma | proof | closed | - | Increasing enumeration of an infinite set | IncSeq |
| InitialSegment | definition | definition | closed | - | - | Preamble |
| InitialSegmentInsert | helper | proof | closed | - | Transporting an initial segment through an appended point | InitialSegment |
| LocallyConstant | definition | definition | closed | - | - | MultiSequence, PrefixAgree |
| MainProp | theorem | proof | closed | - | MainProp | ContMorEq, EmapLemma, RmapLemma |
| MultiSequence | definition | definition | closed | - | - | IncSeq |
| MultiSequenceRestrict | definition | definition | closed | - | - | IncSeqComp, MultiSequence |
| NashWilliams | theorem | proof | closed | - | Nash--Williams | BooleanInfinitePigeonhole, Front, FrontRayClosure, FrontRestrict, FrontRestriction, FrontTreeWellFounded, InitialSegmentInsert, SubFrontCharacterization |
| NoBadPerfectSuper | lemma | proof | closed | - | A super-sequence is not both perfect and bad | BadSuperSequence, BaseShift, FrontPrefixExists, InfiniteSetEnumeration, PerfectSuperSequence |
| OrbitBlock | definition | definition | closed | - | - | OrbitPoint |
| OrbitBlockCoverage | lemma | proof | closed | - | - | OrbitBlock, OrbitEmbedding, OrbitUnbounded |
| OrbitEmbedding | lemma | proof | closed | - | - | IncSeq, OrbitPoint |
| OrbitPoint | definition | definition | closed | - | - | IncSeq |
| OrbitUnbounded | lemma | proof | closed | - | - | OrbitEmbedding, OrbitPoint |
| PerfectBaseToSuper | lemma | proof | closed | - | Perfect base extensions yield perfect sub-super-sequences | BaseIncSeq, BaseRestrict, FiniteShift, Front, FrontPrefix, FrontRestrict, FrontRestriction, IncSeq, IncSeqComp, InfiniteSetEnumeration, InitialSegment, PerfectMultiSequence, PerfectSuperSequence, ProperPrefixSet, RestrictionShift, ShiftMap, SuperSequence, SuperSequenceExtension, SuperSequenceRestrict |
| PerfectMultiRestrict | lemma | proof | open | - | Perfectness under restriction | MultiSequenceRestrict, PerfectMultiSequence, RestrictionShift |
| PerfectMultiSequence | definition | definition | closed | - | - | MultiSequence, ShiftMap |
| PerfectMultiToSuper | lemma | proof | open | - | Multi-sequence perfectness gives super-sequence perfectness | DecidingFrontSet, DecidingPrefix, PerfectMultiSequence, PerfectSuperSequence |
| PerfectSuperRestrict | lemma | proof | open | - | Perfectness under sub-front restriction | PerfectSuperSequence, SuperSequenceRestrict |
| PerfectSuperSequence | definition | definition | closed | - | - | FiniteShift, SuperSequence |
| PerfectSuperToBase | lemma | proof | open | - | Super-sequence perfectness gives base perfectness | BaseLocallyConstant, BasePerfect, BaseShift, FiniteShift, FrontPrefix, FrontPrefixExists, PerfectSuperSequence, ProperPrefixSet, ShiftMap, SuperSequenceExtension |
| PerfectSuperToMulti | lemma | proof | open | - | Perfect sub-super-sequences give perfect sub-multi-sequences | DecidingFrontSet, DecidingValue, FiniteShift, Front, InfiniteSetEnumeration, LocallyConstant, MultiSequenceRestrict, PerfectMultiSequence, PerfectSuperSequence, RestrictionShift, SuperSequenceRestrict |
| PowerChild | definition | definition | closed | - | - | PowerQ |
| PowerChildSupport | lemma | proof | closed | - | Support decreases along a child | PowerChild, PowerSupport |
| PowerChildWellFounded | lemma | proof | closed | - | Well-founded hierarchy descent | PowerChild |
| PowerCopiedFailureMove | lemma | proof | closed | - | Failure and legal moves in the copied triangle | BadMultiSequence, PowerCopiedLeft, PowerIResponseFailure, PowerIResponseLegal |
| PowerCopiedFiniteDependence | lemma | proof | closed | - | Finite dependence of a copied move | PowerCopiedLeft |
| PowerCopiedFiniteTerminal | lemma | proof | closed | - | Finite terminal dependence | PowerCopiedFiniteDependence, PowerCopiedTerminalAt, PowerCopiedTerminates |
| PowerCopiedLeft | definition | definition | closed | - | - | MultiSequence, PowerIResponse, PowerShiftIter |
| PowerCopiedOrbitDependence | lemma | proof | closed | - | Finite dependence on the enumeration orbit | PowerCopiedLeft |
| PowerCopiedShiftIdentity | lemma | proof | closed | - | Stabilization under the shift | PowerCopiedLeft, PowerShiftIterShift |
| PowerCopiedSupport | lemma | proof | closed | - | Support of the copied left values | PowerCopiedFailureMove, PowerMoveInSupport |
| PowerCopiedTerminalAt | definition | definition | closed | - | - | PowerCopiedLeft |
| PowerCopiedTerminalShift | lemma | proof | closed | - | The terminal atom stabilizes under shifting | PowerCopiedFiniteTerminal, PowerCopiedShiftIdentity |
| PowerCopiedTerminalSupport | lemma | proof | closed | - | The terminal atom lies in the original support | PowerCopiedSupport, PowerCopiedTerminalAt, PowerCopiedTerminates |
| PowerCopiedTerminates | lemma | proof | closed | - | Every copied row reaches atoms | PowerCopiedFailureMove, PowerCopiedTerminalAt, PowerGameDescentWellFounded |
| PowerFiniteOrbitConstancy | lemma | proof | closed | - | A finite shift orbit is decided by one finite prefix | LocallyConstant, PowerShiftIterPrefixAgree |
| PowerGameDescent | definition | definition | closed | - | - | PowerChild |
| PowerGameDescentWellFounded | lemma | proof | closed | - | Well-foundedness of copied pair descent | PowerChildWellFounded, PowerGameDescent |
| PowerIResponse | definition | definition | closed | - | - | PowerMove |
| PowerIResponseFailure | lemma | proof | closed | - | The canonical response preserves failure | PowerIResponseLegal |
| PowerIResponseLegal | lemma | proof | closed | - | The canonical response is legal | PowerIResponseWitness |
| PowerIResponseWitness | lemma | proof | closed | - | A failed comparison has a canonical one-round response | PowerIResponse, PowerRelAtomAtom, PowerRelAtomNode, PowerRelNodeAtom, PowerRelNodeNode |
| PowerMove | definition | definition | closed | - | - | PowerChild, PowerRel |
| PowerMoveInSupport | lemma | proof | closed | - | Moves stay in support | PowerChildSupport, PowerMove |
| PowerPresentationEq | definition | definition | closed | - | - | PowerQ |
| PowerPresentationEqEquivalence | lemma | proof | closed | - | Structural equivalence is an equivalence relation | PowerPresentationEq |
| PowerQ | definition | definition | closed | - | - | Preamble |
| PowerQIsPreorder | lemma | proof | closed | - | The lifted relation is a preorder | PowerRelTrans |
| PowerQPresBqo | corollary | proof | closed | - | - | Bqo, PowerQReflection |
| PowerQReflection | theorem | proof | closed | - | Reflection to the base quasi-order | PowerCopiedFailureMove, PowerCopiedOrbitDependence, PowerCopiedTerminalShift, PowerCopiedTerminalSupport, PowerFiniteOrbitConstancy |
| PowerRel | definition | definition | closed | - | - | PowerChildWellFounded |
| PowerRelAtomAtom | lemma | proof | closed | - | Atom--atom reduction | PowerRel |
| PowerRelAtomNode | lemma | proof | closed | - | Atom--node reduction | PowerRel |
| PowerRelCongrLeft | lemma | proof | closed | - | Left presentation invariance | PowerPresentationEqEquivalence, PowerRelAtomAtom, PowerRelAtomNode, PowerRelNodeAtom, PowerRelNodeNode |
| PowerRelCongrRight | lemma | proof | closed | - | Right presentation invariance | PowerRelCongrLeft |
| PowerRelNodeAtom | lemma | proof | closed | - | Node--atom reduction | PowerRel |
| PowerRelNodeNode | lemma | proof | closed | - | Node--node reduction | PowerRel |
| PowerRelRefl | lemma | proof | closed | - | Reflexivity of the lifted relation | PowerRelCongrRight |
| PowerRelTrans | lemma | proof | closed | - | Transitivity of the lifted relation | PowerRelRefl |
| PowerShiftIter | definition | definition | closed | - | - | ShiftMap |
| PowerShiftIterPrefixAgree | lemma | proof | closed | - | Finite-prefix agreement survives finitely many shifts | PowerShiftIter, PrefixAgree |
| PowerShiftIterShift | lemma | proof | closed | - | Shift iterates commute with the first shift | PowerShiftIter |
| PowerSupport | definition | definition | closed | - | - | PowerQ |
| PowerSupportInvariant | lemma | proof | closed | - | Support respects presentation equivalence | PowerPresentationEq, PowerSupport |
| PowerSupportNonempty | lemma | proof | closed | - | Nonempty support | PowerSupport |
| PowerWqoBadPairSequence | lemma | proof | closed | - | Bad-witness characterization | BadPairSequence, SetDomination |
| Preamble | preamble | preamble | closed | - | - | - |
| PrefixAgree | definition | definition | closed | - | - | IncSeq |
| PrefixTree | definition | definition | closed | - | - | InitialSegment |
| ProperInitialSegment | definition | definition | closed | - | - | InitialSegment |
| ProperPrefixSet | definition | definition | closed | - | - | Preamble |
| QuadrupleHomogeneous | lemma | proof | closed | - | Homogeneous quadruples | CardinalityFrontIsFront, NashWilliams |
| RadoEmbedding | theorem | proof | closed | - | Rado embedding | InfiniteSetEnumeration, PowerWqoBadPairSequence, QuadrupleHomogeneous, RadoOrder, RelationEmbedding, TripleHomogeneous |
| RadoOrder | definition | definition | closed | - | Rado order | IncreasingPair |
| Ray | definition | definition | closed | - | - | Preamble |
| RelationEmbedding | definition | definition | closed | - | Relation embedding | Preamble |
| RestrictionLocallyConstant | lemma | proof | closed | - | Restriction preserves local constancy | LocallyConstant, MultiSequenceRestrict |
| RestrictionShift | lemma | proof | closed | - | Restriction and shift | MultiSequenceRestrict, ShiftMap |
| RightComp | definition | definition | closed | - | - | IncSeqComp |
| RmapLemma | lemma | proof | closed | - | - | ContMor, FirstMovedPoint, OrbitEmbedding, RightComp, ShiftMap |
| SetDomination | definition | definition | closed | - | Domination on subsets | Preamble |
| ShiftDichotomy | lemma | proof | closed | - | Perfect-or-bad shift dichotomy | BadMultiSequence, DecidingFront, DecidingValue, InfiniteSetEnumeration, MultiSequenceRestrict, NashWilliams, PerfectMultiSequence, RestrictionShift |
| ShiftMap | definition | definition | closed | - | - | RightComp, SuccSeq |
| SubFrontCharacterization | lemma | proof | closed | - | Sub-fronts | Front, FrontRestrict, FrontRestriction |
| Subarr | corollary | proof | open | lem:subarr | Sub-arrays and super-sequences | BadMultiRestrict, BadMultiToSuper, BadSuperRestrict, BaseBqoRestriction, DecidingFront, DecidingValue, NoBadPerfectSuper, PerfectBaseToSuper, PerfectSuperToMulti, RestrictionLocallyConstant, ShiftDichotomy, SuperSequenceExtension |
| SuccSeq | definition | definition | closed | - | - | IncSeq |
| SuperNW | theorem | proof | closed | - | - | NashWilliams, SuperSequence |
| SuperSequence | definition | definition | closed | - | - | Front |
| SuperSequenceExtension | lemma | proof | closed | - | Extension from a front | BaseLocallyConstant, FrontPrefixExists, FrontPrefixUnique, SuperSequence |
| SuperSequenceRestrict | definition | definition | closed | - | - | SuperSequence |
| TailSet | definition | definition | closed | - | - | Preamble |
| TildeF | definition | definition | closed | - | - | FrontTreeImmediateExtensions, FrontTreeWellFounded, PowerQ, SuperSequence |
| TildeFAtomIffFront | lemma | proof | closed | - | Atoms occur exactly at front nodes | TildeF, TildeFFrontEquation, TildeFNonfrontEquation |
| TildeFFrontEquation | lemma | proof | closed | - | Front recursion equation | SuperSequence, TildeF |
| TildeFHerCtbl | lemma | proof | closed | - | Hereditary countability of the front recursion | FrontTreeImmediateExtensions, HerCtblNodeClosure, HereditarilyCountableAtom, TildeF, TildeFFrontEquation, TildeFNonfrontEquation |
| TildeFNonfrontEquation | lemma | proof | closed | - | Non-front recursion equation | FrontTreeImmediateExtensions, TildeF |
| TildeFSingleton | definition | definition | closed | - | - | FrontTreeSingleton, TildeF, TildeFHerCtbl |
| TripleHomogeneous | lemma | proof | closed | - | Homogeneous triples | CardinalityFrontIsFront, NashWilliams |

**Total:** 185 nodes | **Closed:** 176 | **Open:** 9
