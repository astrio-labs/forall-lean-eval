import Submission

/- This audit checks the new semantic tower laws. The root normalization
   theorem still has its explicit admitted uniform-model obligation. -/

-- UniversePrefix
#print axioms Submission.Helpers.CarrierTelescope.Ordered.all
#print axioms Submission.Helpers.CarrierTelescope.Ordered.empty
#print axioms Submission.Helpers.CarrierTelescope.Ordered.snoc
#print axioms Submission.Helpers.UniversePrefix.next_roundtrip

-- UniversePrefixBoundary
#print axioms Submission.Helpers.UniversePrefix.candidate_roundtrip

-- UniverseInterpretation
#print axioms Submission.Helpers.CarrierObject.ofDataEq_code
#print axioms Submission.Helpers.UniversePrefix.decode_encode
#print axioms Submission.Helpers.UniversePrefix.encode_code
#print axioms Submission.Helpers.UniversePrefix.shiftObject_image
#print axioms Submission.Helpers.UniversePrefix.shiftObject_formation

-- TelescopeProjection
#print axioms Submission.Helpers.TowerFamily.set_same
#print axioms Submission.Helpers.TowerFamily.set_other
#print axioms Submission.Helpers.CarrierTelescope.project_set_below
#print axioms Submission.Helpers.CarrierTelescope.project_section

-- RetractedFamilies
#print axioms Submission.Helpers.family_encode_decode
#print axioms Submission.Helpers.family_decode_admissible
#print axioms Submission.Helpers.family_decode_encode_iff

-- UniverseFamilies
#print axioms Submission.Helpers.universeOutputCodes_image
#print axioms Submission.Helpers.universeOutputCodes_image_iff
#print axioms Submission.Helpers.universeOutputCodes_formed
#print axioms Submission.Helpers.UniversePrefix.family_roundtrip

-- UniverseValues
#print axioms Submission.Helpers.UniversePrefix.decodeCode_encodeCode
#print axioms Submission.Helpers.UniversePrefix.shiftCodeObject_code
#print axioms Submission.Helpers.UniversePrefix.fromValues_congr
#print axioms Submission.Helpers.UniversePrefix.fromValues_next

-- UniformSorts
#print axioms Submission.Helpers.GridFormation.cast
#print axioms Submission.Helpers.carrierGridCandidateCode_image
#print axioms Submission.Helpers.carrierGridCandidateCode_formation
#print axioms Submission.Helpers.universeSortAt_formation
#print axioms Submission.Helpers.universeSortAt_congr
#print axioms Submission.Helpers.uniformSortCode_formation
#print axioms Submission.Helpers.uniformSortCode_lower
#print axioms Submission.Helpers.uniformSortCode_congr
#print axioms Submission.Helpers.universeSortAt_cast
#print axioms Submission.Helpers.uniformSortCode_at

-- UniverseMachine
#print axioms Submission.Helpers.CarrierTelescope.project_snoc
#print axioms Submission.Helpers.UniverseMachine.step_project
#print axioms Submission.Helpers.universeMachine_trace
#print axioms Submission.Helpers.universeSortAt_canonical

-- LiteralSorts
#print axioms Submission.Helpers.UniversePrefix.shiftCandidateObject_code
#print axioms Submission.Helpers.UniversePrefix.decodeCandidate_encodeCandidate
#print axioms Submission.Helpers.literalSortPrefix_succ
#print axioms Submission.Helpers.literalSortValue_proper
#print axioms Submission.Helpers.literalSortValue_final
#print axioms Submission.Helpers.literalSortValue_prefix
#print axioms Submission.Helpers.literalSortValue_code
#print axioms Submission.Helpers.gridValueCast_family
#print axioms Submission.Helpers.literalSortFullValues_at
#print axioms Submission.Helpers.literalSortFullValues_typed_code
#print axioms Submission.Helpers.literalSortFullValues_candidate

-- UniformLiterals
#print axioms Submission.Helpers.sortLiteralValue_proper
#print axioms Submission.Helpers.sortLiteralValue_final
#print axioms Submission.Helpers.sortLiteralValue_prefix
#print axioms Submission.Helpers.sortLiteralValue_code
#print axioms Submission.Helpers.sortLiteralValues_at
#print axioms Submission.Helpers.sortLiteralValues_active_code
#print axioms Submission.Helpers.sortLiteralValues_typed_code
#print axioms Submission.Helpers.sortLiteralValues_candidate
#print axioms Submission.Helpers.sortLiteralValues_typed_code_cast
#print axioms Submission.Helpers.boundedLiteralValues_typed_code

-- UniverseProducts
#print axioms Submission.Helpers.UniversePrefix.read_store_iff
#print axioms Submission.Helpers.UniversePrefix.read_store_formed
#print axioms Submission.Helpers.UniversePrefix.read_store_projected
#print axioms Submission.Helpers.universeProductCode_formation
#print axioms Submission.Helpers.UniversePrefix.read_store_products
#print axioms Submission.Helpers.UniversePrefix.read_store_candidate

#check Submission.Helpers.UniversePrefix.decode_encode
#check Submission.Helpers.UniversePrefix.family_roundtrip
#check Submission.Helpers.uniformSortCode_formation
#check Submission.Helpers.uniformSortCode_congr
#check Submission.Helpers.universeMachine_trace
#check Submission.Helpers.universeSortAt_canonical
#check Submission.Helpers.boundedLiteralValues_typed_code
#check Submission.Helpers.sortLiteralValues_candidate
#check Submission.Helpers.UniversePrefix.read_store_products
#check Submission.Helpers.UniversePrefix.read_store_candidate

#print axioms Submission.Helpers.bound_three_normalization
#print axioms Submission.LeanEval.ProgramVerification.CoCStrongNormalization.strong_normalization
#print axioms Submission.LeanEval.ProgramVerification.CoCStrongNormalization.consistency
