import Submission

/-!
This checkpoint adds a source interpretation at every bound `p + 5`, through
its second value and third carrier coordinates. It proves typed decoding,
substitution, reduction and carrier conversion, without an SN premise.

The generic grid results apply at arbitrary rows, coordinates, image depths,
and finite telescope lengths. They describe semantic carrier representations
and exact code images; they do not assert descent of the source typing bound.

Still open: the source interpretation through every coordinate, including
the candidate-valued boundary, and the full realizability fundamental theorem.
In particular no `BoundedModel 4`, nor `forall n >= 4, Nonempty (BoundedModel n)`,
is claimed here. The admitted original strong_normalization remains honest.

Next obligation: use dependent telescope extension and graded image decoding
to define a uniform universe interpretation, then prove its source sort and
product equations, including the bottom boundary.
-/

#print axioms Submission.Helpers.carrierGrid_universe_twice_roundtrip
#print axioms Submission.Helpers.carrierGrid_universe_twice_bottom_roundtrip
#print axioms Submission.Helpers.CarrierTelescope.representPi_roundtrip
#print axioms Submission.Helpers.carrierGrid_universe_telescope_roundtrip
#print axioms Submission.Helpers.carrierGrid_universe_telescope_bottom_roundtrip
#print axioms Submission.Helpers.carrierGridUniverseTelescopeBottom_small
#print axioms Submission.Helpers.GridCodeImage.indices
#print axioms Submission.Helpers.GridCodeImage.mono
#print axioms Submission.Helpers.gridCodeImage_arrow
#print axioms Submission.Helpers.gridCodeImage_all
#print axioms Submission.Helpers.gridCodeImage_pi
#print axioms Submission.Helpers.gridFormation_arrow
#print axioms Submission.Helpers.gridFormation_all
#print axioms Submission.Helpers.gridFormation_pi
#print axioms Submission.Helpers.carrierGridHorizontal_small
#print axioms Submission.Helpers.carrierGridHorizontal_default
#print axioms Submission.Helpers.GridCodeImage.horizontal
#print axioms Submission.Helpers.GridFormation.horizontal
#print axioms Submission.Helpers.GridFormation.prefix
#print axioms Submission.Helpers.firstGridShape_formation
#print axioms Submission.Helpers.upperGridSemantics_formation
#print axioms Submission.Helpers.secondLayerSemantics_formation
#print axioms Submission.Helpers.carrierGridTelescopeCode_formation
#print axioms Submission.Helpers.carrierGridBinderCode_formation
#print axioms Submission.Helpers.carrierGridImageCodes_image
#print axioms Submission.Helpers.carrierGridImageCodes_encode_decode_iff
#print axioms Submission.Helpers.carrierGridImageCodes_family_iff
#print axioms Submission.Helpers.gridFormation_family_decode_encode
#print axioms Submission.Helpers.carrierGridImageEmbedding_value_roundtrip
#print axioms Submission.Helpers.carrierGrid_binder_image_decode_encode
#print axioms Submission.Helpers.CarrierTelescope.snoc_roundtrip
#print axioms Submission.Helpers.carrierGrid_universe_extend_roundtrip
#print axioms Submission.Helpers.secondLayerSemantics_typed_code
#print axioms Submission.Helpers.secondLayerSemantics_pi
#print axioms Submission.Helpers.secondLayerSemantics_form
#print axioms Submission.Helpers.secondLayerEncode_typed_code
#print axioms Submission.Helpers.secondLayerDecode_encode_low
#print axioms Submission.Helpers.secondLayerDecode_encode_middle
#print axioms Submission.Helpers.secondLayerDecode_encode_high
#print axioms Submission.Helpers.secondLayerSemantics_decode
#print axioms Submission.Helpers.secondGridApply_congr
#print axioms Submission.Helpers.secondGridLambda_congr
#print axioms Submission.Helpers.secondLayerProduct_congr
#print axioms Submission.Helpers.secondLayerSemantics_lam
#print axioms Submission.Helpers.secondLayerSemantics_app
#print axioms Submission.Helpers.secondLayerSemantics_ren
#print axioms Submission.Helpers.secondLayerSemantics_substitute_related
#print axioms Submission.Helpers.secondLayerSemantics_subst_value
#print axioms Submission.Helpers.secondLayerSemantics_subst_carrier
#print axioms Submission.Helpers.secondLayerSemantics_context_conversion
#print axioms Submission.Helpers.secondLayerSemantics_beta_value
#print axioms Submission.Helpers.secondLayerSemantics_step
#print axioms Submission.Helpers.secondLayerSemantics_carrier_conv
#print axioms Submission.Helpers.thirdGridShape_conv
#print axioms Submission.Helpers.inferredThirdGrid_eq
#print axioms Submission.Helpers.thirdGridShape_ren
#print axioms Submission.Helpers.inferredThirdGrid_ren
#print axioms Submission.Helpers.thirdGridShape_subst
#print axioms Submission.Helpers.ThirdGridContext.up
#print axioms Submission.Helpers.ThirdGridContext.var_code
#print axioms Submission.Helpers.inferredThirdGrid_step
#print axioms Submission.Helpers.thirdGrid_environments
#print axioms Submission.Helpers.bound_three_fundamental
#print axioms Submission.Helpers.bound_three_normalization

#check Submission.Helpers.secondLayerSemantics_decode
#check Submission.Helpers.secondLayerSemantics_subst_carrier
#check Submission.Helpers.secondLayerSemantics_carrier_conv
#check Submission.Helpers.carrierGridBinderCode_formation
#check Submission.Helpers.carrierGrid_binder_image_decode_encode
#check Submission.Helpers.carrierGrid_universe_extend_roundtrip
#check Submission.Helpers.thirdGrid_environments
