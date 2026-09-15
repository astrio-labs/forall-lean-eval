import Submission

/-!
Round-eight checkpoint: uniform finite carrier and candidate algebra.

Checked obligations include dependent Pi formation, coherent application,
finite lambda beta equality, candidate introduction/elimination, universe
reification and elimination, and conversion after canonicalization.
Both universe operations satisfy coordinate causality. Type equality on
coherent data also preserves the encoded universe value.

The source interpreter has not been constructed uniformly. No BoundedModel
above three, higher-bound normalization theorem, or source-bound descent
is claimed here. The root strong_normalization admission remains explicit.

Next obligation: define source evaluation by coordinate induction, prove
each coordinate depends only on the retained environment prefix, and prove
weakening and substitution for that evaluation. Connect its inferred
carriers to this algebra and prove the BoundedModel conversion laws.

A successor stage should produce value j and carrier j+1 simultaneously
by structural recursion on terms, using the preceding stage for carriers
of chosen types in application and abstraction. At the last coordinate
the second component is the candidate. The highest source universe needs
its separate terminal case; no decoder or bound descent is assumed there.
-/

-- CompletePrefixes
#print axioms Submission.Helpers.CarrierTelescope.Complete
#print axioms Submission.Helpers.CarrierTelescope.Complete.ordered
#print axioms Submission.Helpers.CarrierTelescope.Complete.snoc
#print axioms Submission.Helpers.UniversePrefix.Full
#print axioms Submission.Helpers.UniversePrefix.full_empty
#print axioms Submission.Helpers.UniversePrefix.Full.next
#print axioms Submission.Helpers.UniversePrefix.fromValues_full
#print axioms Submission.Helpers.carrierFieldPrefix_full
#print axioms Submission.Helpers.CarrierTelescope.Compatible
#print axioms Submission.Helpers.CarrierRepresentation.recover_value
#print axioms Submission.Helpers.CarrierTelescope.section_project_at
#print axioms Submission.Helpers.universeOutputValues_reverse
#print axioms Submission.Helpers.UniversePrefix.arguments_recover

-- CoherentUniverseDecoding
#print axioms Submission.Helpers.TowerFamily.AgreeBelow
#print axioms Submission.Helpers.TowerFamily.DependsBelow
#print axioms Submission.Helpers.UniversePrefix.read_store_coherent
#print axioms Submission.Helpers.UniversePrefix.read_store_candidate_coherent
#print axioms Submission.Helpers.universeProductCode_congr
#print axioms Submission.Helpers.UniversePrefix.read_store_product_coherent

-- CausalCarriers
#print axioms Submission.Helpers.CarrierTelescope.compatible_snoc
#print axioms Submission.Helpers.CarrierTelescope.compatible_set_below
#print axioms Submission.Helpers.CarrierTelescope.compatible_section
#print axioms Submission.Helpers.CausalGridType
#print axioms Submission.Helpers.uniformSortType
#print axioms Submission.Helpers.CausalGridType.telescopeAt
#print axioms Submission.Helpers.CausalGridType.full
#print axioms Submission.Helpers.CausalGridType.arguments
#print axioms Submission.Helpers.CausalGridType.Coherent
#print axioms Submission.Helpers.CausalGridType.compatible_iff
#print axioms Submission.Helpers.CausalGridType.recover
#print axioms Submission.Helpers.CausalGridType.section_coherent
#print axioms Submission.Helpers.CausalGridType.Formed
#print axioms Submission.Helpers.uniformSortType_formed

-- GridBinding
#print axioms Submission.Helpers.CarrierTelescope.GridForm.snoc
#print axioms Submission.Helpers.CausalGridType.telescope_formed
#print axioms Submission.Helpers.CausalGridType.telescope_within
#print axioms Submission.Helpers.gridBindingObject
#print axioms Submission.Helpers.gridBindingObject_formed
#print axioms Submission.Helpers.CausalGridFamily
#print axioms Submission.Helpers.gridPiDomain
#print axioms Submission.Helpers.gridPiCodomain
#print axioms Submission.Helpers.gridPiCode
#print axioms Submission.Helpers.gridPiApplyAt
#print axioms Submission.Helpers.gridPiCode_formed

-- GridApplication
#print axioms Submission.Helpers.TowerFamily.AgreeBelow.refl
#print axioms Submission.Helpers.TowerFamily.AgreeBelow.mono
#print axioms Submission.Helpers.CarrierTelescope.project_congr
#print axioms Submission.Helpers.CausalGridType.arguments_congr
#print axioms Submission.Helpers.GridApplicationPrefix
#print axioms Submission.Helpers.GridApplicationPrefix.congr
#print axioms Submission.Helpers.GridApplicationPrefix.empty
#print axioms Submission.Helpers.gridPiCode_causal
#print axioms Submission.Helpers.gridPiApplyAt_congr
#print axioms Submission.Helpers.GridApplicationPrefix.step
#print axioms Submission.Helpers.gridApplicationPrefix
#print axioms Submission.Helpers.gridPiType
#print axioms Submission.Helpers.gridPiType_formed
#print axioms Submission.Helpers.gridApplication
#print axioms Submission.Helpers.gridApplicationPrefix_agree
#print axioms Submission.Helpers.gridApplication_at
#print axioms Submission.Helpers.gridApplication_coherent

-- GridCompletion
#print axioms Submission.Helpers.CausalGridType.Coherent.mono
#print axioms Submission.Helpers.CausalGridType.coherent_extend
#print axioms Submission.Helpers.CausalGridType.normalize
#print axioms Submission.Helpers.CausalGridType.normalize_coherent
#print axioms Submission.Helpers.CausalGridType.normalize_agree
#print axioms Submission.Helpers.CausalGridType.normalize_recover
#print axioms Submission.Helpers.CausalGridType.complete_recover
#print axioms Submission.Helpers.gridPiType_formed_coherent

-- UniverseArguments
#print axioms Submission.Helpers.universeArgumentLift
#print axioms Submission.Helpers.universeArgumentSlice
#print axioms Submission.Helpers.universeArgumentValue_cast
#print axioms Submission.Helpers.universeArgumentLift_at
#print axioms Submission.Helpers.universeArgumentLift_low
#print axioms Submission.Helpers.universeArgumentLift_congr
#print axioms Submission.Helpers.gridValue_eq_point
#print axioms Submission.Helpers.UniversePrefix.lift_arguments_recover

-- UniverseTypePrefix
#print axioms Submission.Helpers.universeTypePrefix
#print axioms Submission.Helpers.universeTypeField
#print axioms Submission.Helpers.universeTypePrefix_full
#print axioms Submission.Helpers.formedType_low_values
#print axioms Submission.Helpers.universeTypePrefix_compatible
#print axioms Submission.Helpers.universeTypePrefix_recover

-- UniverseReification
#print axioms Submission.Helpers.CausalGridPredicate
#print axioms Submission.Helpers.universeReify
#print axioms Submission.Helpers.universeReify_proper
#print axioms Submission.Helpers.universeReify_final
#print axioms Submission.Helpers.universeReify_prefix
#print axioms Submission.Helpers.universeReify_code
#print axioms Submission.Helpers.universeReify_decode
#print axioms Submission.Helpers.universeReify_candidate
#print axioms Submission.Helpers.universeReifyValues
#print axioms Submission.Helpers.universeReifyValues_at
#print axioms Submission.Helpers.universeReifyValues_active_code
#print axioms Submission.Helpers.universeReifyValues_typed

-- PropReification
#print axioms Submission.Helpers.propReifyValues
#print axioms Submission.Helpers.propReifyValues_bottom
#print axioms Submission.Helpers.propReifyValues_typed
#print axioms Submission.Helpers.propValueCandidate
#print axioms Submission.Helpers.prop_coherent_values
#print axioms Submission.Helpers.propReifyValues_candidate

-- GridPiCandidates
#print axioms Submission.Helpers.gridPiPredicate
#print axioms Submission.Helpers.gridPiPredicate_apply
#print axioms Submission.Helpers.positiveGridPiType
#print axioms Submission.Helpers.positiveGridPiPredicate
#print axioms Submission.Helpers.positiveGridPiType_formed
#print axioms Submission.Helpers.gridPi_universe_decode
#print axioms Submission.Helpers.gridPi_universe_candidate
#print axioms Submission.Helpers.gridPi_prop_candidate

-- GridLambda
#print axioms Submission.Helpers.CausalGridMap
#print axioms Submission.Helpers.gridLambdaAt
#print axioms Submission.Helpers.gridLambdaPrefix
#print axioms Submission.Helpers.gridLambda
#print axioms Submission.Helpers.gridLambdaPrefix_agree
#print axioms Submission.Helpers.gridLambda_at
#print axioms Submission.Helpers.gridLambda_coherent
#print axioms Submission.Helpers.grid_argument_recover
#print axioms Submission.Helpers.gridPiApplyAt_lambda

-- GridBeta
#print axioms Submission.Helpers.gridLambda_beta_coordinate
#print axioms Submission.Helpers.gridLambda_beta
#print axioms Submission.Helpers.FiniteGridValue
#print axioms Submission.Helpers.FiniteGridValue.ofTower
#print axioms Submission.Helpers.FiniteGridValue.ofTower_congr
#print axioms Submission.Helpers.gridLambda_beta_finite
#print axioms Submission.Helpers.gridPiPredicate_lambda

-- FiniteGridOperations
#print axioms Submission.Helpers.FiniteGridValue.toTower
#print axioms Submission.Helpers.FiniteGridValue.toTower_at
#print axioms Submission.Helpers.FiniteGridValue.ofTower_toTower
#print axioms Submission.Helpers.FiniteGridValue.toTower_ofTower
#print axioms Submission.Helpers.CausalGridType.Coherent.congr
#print axioms Submission.Helpers.CausalGridType.Valid
#print axioms Submission.Helpers.CausalGridType.valid_ofTower
#print axioms Submission.Helpers.CausalGridType.finitePoint
#print axioms Submission.Helpers.CausalGridType.finitePoint_valid
#print axioms Submission.Helpers.CausalGridPredicate.ofFinite
#print axioms Submission.Helpers.finiteGridApplication
#print axioms Submission.Helpers.finiteGridLambda
#print axioms Submission.Helpers.finiteGridApplication_valid
#print axioms Submission.Helpers.finiteGridLambda_valid
#print axioms Submission.Helpers.finiteGridLambda_beta

-- FiniteGridTypes
#print axioms Submission.Helpers.FiniteGridValue.project_congr
#print axioms Submission.Helpers.FiniteGridType
#print axioms Submission.Helpers.FiniteGridType.Valid
#print axioms Submission.Helpers.FiniteGridType.Formed
#print axioms Submission.Helpers.FiniteGridType.point
#print axioms Submission.Helpers.FiniteGridType.point_valid
#print axioms Submission.Helpers.FiniteGridType.sort
#print axioms Submission.Helpers.FiniteGridType.sort_formed
#print axioms Submission.Helpers.FiniteGridFamily
#print axioms Submission.Helpers.FiniteGridFamily.toCausal
#print axioms Submission.Helpers.finiteTypeApplication
#print axioms Submission.Helpers.finitePiType
#print axioms Submission.Helpers.finiteTypeApplication_valid
#print axioms Submission.Helpers.finitePiType_formed
#print axioms Submission.Helpers.finitePiType_candidate_apply
#print axioms Submission.Helpers.FiniteGridMap
#print axioms Submission.Helpers.FiniteGridMap.toCausal
#print axioms Submission.Helpers.finiteTypeLambda
#print axioms Submission.Helpers.finiteTypeLambda_valid
#print axioms Submission.Helpers.finiteTypeLambda_beta
#print axioms Submission.Helpers.finitePiType_candidate_lambda

-- FiniteGridUniverses
#print axioms Submission.Helpers.FiniteGridType.reify
#print axioms Submission.Helpers.finiteUniversePrefix
#print axioms Submission.Helpers.finiteUniverseCode
#print axioms Submission.Helpers.finiteUniverseCandidate
#print axioms Submission.Helpers.FiniteGridType.reify_at
#print axioms Submission.Helpers.finiteUniversePrefix_reify
#print axioms Submission.Helpers.FiniteGridType.reify_valid
#print axioms Submission.Helpers.finiteUniverseCode_reify
#print axioms Submission.Helpers.finiteUniverseCandidate_reify
#print axioms Submission.Helpers.FiniteGridType.reifyProp
#print axioms Submission.Helpers.finitePropCandidate
#print axioms Submission.Helpers.finitePropCandidate_ofTower
#print axioms Submission.Helpers.FiniteGridType.reifyProp_valid
#print axioms Submission.Helpers.finitePropCandidate_reify
#print axioms Submission.Helpers.positiveFinitePiType
#print axioms Submission.Helpers.positiveFinitePiType_formed
#print axioms Submission.Helpers.finitePi_universe_code
#print axioms Submission.Helpers.finitePi_universe_candidate
#print axioms Submission.Helpers.finitePi_prop_candidate

-- FiniteGridConversion
#print axioms Submission.Helpers.FiniteGridTypeEq
#print axioms Submission.Helpers.FiniteGridTypeEq.coherent_forward
#print axioms Submission.Helpers.FiniteGridTypeEq.coherent_backward
#print axioms Submission.Helpers.FiniteGridTypeEq.valid_iff
#print axioms Submission.Helpers.FiniteGridTypeEq.normalize_eq
#print axioms Submission.Helpers.FiniteGridType.normalizeValue
#print axioms Submission.Helpers.FiniteGridType.normalizeValue_valid
#print axioms Submission.Helpers.FiniteGridType.normalizeValue_eq
#print axioms Submission.Helpers.FiniteGridType.canonicalCandidate
#print axioms Submission.Helpers.FiniteGridType.canonicalCandidate_eq
#print axioms Submission.Helpers.FiniteGridTypeEq.canonicalCandidate_eq
#print axioms Submission.Helpers.FiniteGridTypeEq.refl
#print axioms Submission.Helpers.FiniteGridTypeEq.symm
#print axioms Submission.Helpers.FiniteGridTypeEq.trans

-- DecodedUniverseTypes
#print axioms Submission.Helpers.rawFiniteUniverseCode
#print axioms Submission.Helpers.rawFiniteUniverseCode_congr
#print axioms Submission.Helpers.rawFiniteUniverseCode_formed
#print axioms Submission.Helpers.decodedUniverseCarrier
#print axioms Submission.Helpers.decodedUniverseCarrier_low
#print axioms Submission.Helpers.universeCode_cast
#print axioms Submission.Helpers.decodedUniverseCarrier_at
#print axioms Submission.Helpers.decodedUniverseCarrier_causal
#print axioms Submission.Helpers.decodedUniverseCarrier_formed
#print axioms Submission.Helpers.decodeUniverseType
#print axioms Submission.Helpers.decodeUniverseType_formed
#print axioms Submission.Helpers.decodedUniverseCarrier_reify
#print axioms Submission.Helpers.decodeUniverseType_reify
#print axioms Submission.Helpers.decodeUniverseType_reify_conversion
#print axioms Submission.Helpers.decodePropType
#print axioms Submission.Helpers.decodePropType_formed
#print axioms Submission.Helpers.decodePropType_reify
#print axioms Submission.Helpers.decodePropType_reify_conversion

-- CanonicalPiCandidates
#print axioms Submission.Helpers.FiniteGridType.sort_canonicalCandidate
#print axioms Submission.Helpers.finitePiType_canonical_product
#print axioms Submission.Helpers.finitePiType_canonical_apply
#print axioms Submission.Helpers.finitePiType_canonical_lambda

-- UniverseDecoderCausality
#print axioms Submission.Helpers.finiteUniversePrefix_congr
#print axioms Submission.Helpers.rawFiniteUniverseCode_stored_congr
#print axioms Submission.Helpers.decodedUniverseCarrier_stored_congr
#print axioms Submission.Helpers.decodeUniverseFamily
#print axioms Submission.Helpers.decodePropFamily
#print axioms Submission.Helpers.FiniteGridValue.eq_of_agree

-- UniverseReifierCausality
#print axioms Submission.Helpers.universeTypePrefix_congr
#print axioms Submission.Helpers.universeReify_proper_congr
#print axioms Submission.Helpers.FiniteGridFamily.reifyMap
#print axioms Submission.Helpers.FiniteGridFamily.reifyPropMap
#print axioms Submission.Helpers.FiniteGridFamily.reifyMap_valid
#print axioms Submission.Helpers.FiniteGridFamily.reifyPropMap_valid

-- UniverseCoherentSections
#print axioms Submission.Helpers.universeTypePrefix_coherent
#print axioms Submission.Helpers.universeArgumentSlice_lift
#print axioms Submission.Helpers.universeTypePrefix_section_coherent

-- UniverseValueConversion
#print axioms Submission.Helpers.FiniteGridTypeEq.universePrefix
#print axioms Submission.Helpers.FiniteGridTypeEq.universeReify
#print axioms Submission.Helpers.FiniteGridTypeEq.reify_eq
#print axioms Submission.Helpers.FiniteGridTypeEq.reifyProp_eq

#check Submission.Helpers.finitePiType_formed
#check Submission.Helpers.finiteTypeApplication_valid
#check Submission.Helpers.finiteTypeLambda_beta
#check Submission.Helpers.finitePiType_candidate_apply
#check Submission.Helpers.finitePiType_candidate_lambda
#check Submission.Helpers.finitePiType_canonical_product
#check Submission.Helpers.finitePi_universe_code
#check Submission.Helpers.finitePi_universe_candidate
#check Submission.Helpers.finitePi_prop_candidate
#check Submission.Helpers.decodeUniverseType_reify
#check Submission.Helpers.decodeUniverseType_reify_conversion
#check Submission.Helpers.decodePropType_reify
#check Submission.Helpers.FiniteGridTypeEq.canonicalCandidate_eq
#check Submission.Helpers.decodedUniverseCarrier_stored_congr
#check Submission.Helpers.FiniteGridFamily.reifyMap
#check Submission.Helpers.FiniteGridTypeEq.reify_eq

-- Previously checked normalization and explicit admitted controls.
#print axioms Submission.Helpers.bound_three_normalization
#print axioms Submission.LeanEval.ProgramVerification.CoCStrongNormalization.strong_normalization
#print axioms Submission.LeanEval.ProgramVerification.CoCStrongNormalization.consistency
