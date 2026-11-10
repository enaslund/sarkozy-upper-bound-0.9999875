module

public import Sarkozy
public import Lean.Util.CollectAxioms

@[expose] public section

/-!
Inspect the axiom dependency closure of *every* declaration in our namespace.
This command inspects declarations; it does not add declarations or proof terms.
It rejects sorryAx, custom axioms, and native-decide/compiler trust axioms.
The accepted axioms are the standard foundations used by mathlib.
-/

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`Sarkozy).isPrefixOf name then
      let axioms ← collectAxioms name
      let unexpected := axioms.filter (!allowed.contains ·)
      unless unexpected.isEmpty do
        throwError "{name} depends on forbidden axioms: {unexpected}"
      count := count + 1
  if count == 0 then
    throwError "No Sarkozy declarations were audited"
  logInfo m!"Axiom audit passed for {count} Sarkozy declarations."

#print axioms Sarkozy.powerSavingBound_of_jointClosing
#print axioms Sarkozy.titleBound_of_scaledEnergyEstimate
#print axioms Sarkozy.ClosingLedger.theta_le_rounded
#print axioms Sarkozy.squareStepChild_free
#print axioms Sarkozy.restoration_le_mean
#print axioms Sarkozy.FourierModel.powerSavingBound
#print axioms Sarkozy.slot_signed_holder
#print axioms Sarkozy.mean_fourierLift
#print axioms Sarkozy.FourierArithmetic.uniform_lift_moment_density
#print axioms Sarkozy.FourierArithmetic.uniform_prefixed_indicator_moment
#print axioms Sarkozy.PrefixedResidueModel.powerSavingBound
#print axioms Sarkozy.mixedLpBound_of_centered_small
#print axioms Sarkozy.mixedLpBound_typed_mixture
#print axioms Sarkozy.FiniteLaw.lpNorm_uniform_convexity
#print axioms Sarkozy.mixedLpBound_of_centered_tolerance
#print axioms Sarkozy.powerGap_le_curvature

-- Added 1 November 2026 (second session): headline theorems of the new packages.
#print axioms Sarkozy.Comparison.paperMain_powerSavingBound
#print axioms Sarkozy.Comparison.PrimitiveLedger.theta_lt_cap
#print axioms Sarkozy.Comparison.ClosingEstimates.rawComparison
#print axioms Sarkozy.Comparison.frame_of_brackets
#print axioms Sarkozy.Comparison.wrap_summation
#print axioms Sarkozy.Comparison.folded_energy
#print axioms Sarkozy.Comparison.abs_term_le_folded
#print axioms Sarkozy.Comparison.total_reprice
#print axioms Sarkozy.MixedLpBound.tensor
#print axioms Sarkozy.eventually_mixedLpBound_of_density_and_centeredL2
#print axioms Sarkozy.mixedLpBound_typed_mixture_coarse
#print axioms Sarkozy.Labellings.two_root
#print axioms Sarkozy.Labellings.weil_even
#print axioms Sarkozy.Labellings.soft_count_bound
#print axioms Sarkozy.Labellings.extension_bounds
#print axioms Sarkozy.Labellings.extCount_bounds
#print axioms Sarkozy.Labellings.graphLaw_uniform_density
#print axioms Sarkozy.IndexSupport.index_support_lemma
#print axioms Sarkozy.IndexSupport.one_cut_coupling
#print axioms Sarkozy.IndexSupport.unsplit_cut_mean_step
#print axioms Sarkozy.Functional.paperPrefixed_powerSavingBound
#print axioms Sarkozy.RecordExpansion.energy_sub_eq_sum_selections
#print axioms Sarkozy.RecordExpansion.abs_energy_sub_le_of_envelopes
#print axioms Sarkozy.RecordExpansion.first_stage_lower_bound
#print axioms Sarkozy.RecordExpansion.abs_energy_sub_le_replacement
#print axioms Sarkozy.Peyre.peyre_finite
#print axioms Sarkozy.Peyre.peyre_prefix
#print axioms Sarkozy.Peyre.cond_decorrelation_maxCorr
#print axioms Sarkozy.Kernel.prop_kernel20
#print axioms Sarkozy.Kernel.prop_kernel20_twentieth
#print axioms Sarkozy.Kernel.prop_kernel20_squareDifferenceFree
#print axioms Sarkozy.Kernel.cor_kernel20_admissible

#print axioms Sarkozy.Comparison.selection_factor_reprice
#print axioms Sarkozy.Recentering.recentering_bound
#print axioms Sarkozy.Certificates.tail_coefficients_bounds
#print axioms Sarkozy.Labellings.four_count
#print axioms Sarkozy.Labellings.mainCount_cancel
#print axioms Sarkozy.Labellings.weilBound_of_target
#print axioms Sarkozy.cliqueLaw_slotReflectionPositive
#print axioms Sarkozy.cliqueLaw_uniformMarginals
#print axioms Sarkozy.cliqueLaw_invariant
#print axioms Sarkozy.cliqueLaw_exception_le
#print axioms Sarkozy.cliquePrefixLaw_slotReflectionPositive
#print axioms Sarkozy.Hensel.isSquare_zmod_pow
#print axioms Sarkozy.Characters.norm_gaussSum
#print axioms Sarkozy.Characters.norm_jacobiSum
#print axioms Sarkozy.Extraction.sortedWitnessKernel_opBound
#print axioms Sarkozy.SecondOrder.abs_tau_le
#print axioms Sarkozy.SecondOrder.moving_root_uniform
#print axioms Sarkozy.SecondOrder.moving_root_conditional
#print axioms Sarkozy.SecondOrder.starW_eq_tau
#print axioms Sarkozy.SecondOrder.ordered_orthogonality
#print axioms Sarkozy.SecondOrder.pivot_second_moment
#print axioms Sarkozy.SecondOrder.pivot_first_moment
#print axioms Sarkozy.SecondOrder.ordered_star
#print axioms Sarkozy.SecondOrder.star_mean
#print axioms Sarkozy.SecondOrder.starBEven_eq_prod
#print axioms Sarkozy.SecondOrder.wt_second_cond
#print axioms Sarkozy.SecondOrder.wt_second_weil
#print axioms Sarkozy.SecondOrder.wt_cond_first
#print axioms Sarkozy.SecondOrder.wt_cross
#print axioms Sarkozy.SecondOrder.wt_norm_sum
#print axioms Sarkozy.SecondOrder.graphPinned
#print axioms Sarkozy.Labellings.four_count_density
#print axioms Sarkozy.DistinctChoice.esym_ge
#print axioms Sarkozy.DistinctChoice.distinct_choice_piece
#print axioms Sarkozy.DistinctChoice.distinct_choice_mixed
#print axioms Sarkozy.SecondOrder.raw_pair_full
#print axioms Sarkozy.SecondOrder.raw_pair_distinct
#print axioms Sarkozy.SecondOrder.second_map_bound
#print axioms Sarkozy.SecondOrder.star_mean_graph
#print axioms Sarkozy.SecondOrder.ordered_star_graph
#print axioms Sarkozy.SecondOrder.RD_norm
#print axioms Sarkozy.SecondOrder.R_row_norm
#print axioms Sarkozy.Labellings.extCount_bounds_pair
#print axioms Sarkozy.Labellings.graded_isErrorPair
#print axioms Sarkozy.powerSavingBound_iff_target
#print axioms Sarkozy.InvariantPair.invariant_pair_mixedLpBound
#print axioms Sarkozy.CliqueCopies.mixedLpBound_copyLaw
#print axioms Sarkozy.CliqueCopies.clique_copies_slots
#print axioms Sarkozy.MixedLpBound.random_perm
#print axioms Sarkozy.cliqueIidLaw_positive
#print axioms Sarkozy.cliqueIidLaw_uniformMarginals
#print axioms Sarkozy.Labellings.recordGraphLaw_invariant
#print axioms Sarkozy.Labellings.recordGraphLaw_half_marginal
#print axioms Sarkozy.cliqueIidLaw_invariant
#print axioms Sarkozy.cliqueIidLaw_support_sub

-- Added 1 November 2026, end of the second session: the workers' headline theorems.
#print axioms Sarkozy.Angles.kassabov_angle_inequality
#print axioms Sarkozy.Angles.allpin_elementary
#print axioms Sarkozy.InfluenceGlue.allpin_graph
#print axioms Sarkozy.InfluenceGlue.middle_negative_b
#print axioms Sarkozy.Spectral.spectral_criterion_uniform
#print axioms Sarkozy.Spectral.direct_star_explicit
#print axioms Sarkozy.Spectral.glue_mucentre_star_closed
#print axioms Sarkozy.Spectral.stars_c
#print axioms Sarkozy.Spectral.cut_blocks
#print axioms Sarkozy.Spectral.tensorcomp_block_supp
#print axioms Sarkozy.TheoremC.ComparisonData.theoremC_reduced
#print axioms Sarkozy.PaperFrame.paperMain_powerSavingBound_canonical
#print axioms Sarkozy.PaperFrame.paperMain_powerSavingBound_concrete_ref
#print axioms Sarkozy.PaperFrame.paper_fibre_energy_le_canonical
#print axioms Sarkozy.DensityUpgrade.coupled_spectator_estimate
#print axioms Sarkozy.DensityUpgrade.conditioning_collision_bound
#print axioms Sarkozy.Extraction.witnessKernel_opBound_twoCycles
#print axioms Sarkozy.Extraction.coverRows_le
#print axioms Sarkozy.Cancellation.density_can_of_pair_laws
#print axioms Sarkozy.Cancellation.pairUniform_accepted_false
#print axioms Sarkozy.TheoremC.Glue.densityCancellation_of_pairLawForm
#print axioms Sarkozy.SpectralC.degone_block
#print axioms Sarkozy.SpectralC.gram_comparison
#print axioms Sarkozy.SpectralC.hidden_feature_star
#print axioms Sarkozy.Peyre.peyre_finite_l2
#print axioms Sarkozy.Influence.pinpair_odd
#print axioms Sarkozy.Influence.pinned_influence_b
#print axioms Sarkozy.Cuts.tensor_lower_sub
#print axioms Sarkozy.Cuts.SpecData.block_cut_lower
#print axioms Sarkozy.Cuts.swap_lower
#print axioms Sarkozy.TailMoment.single_label_of_weil
#print axioms Sarkozy.DensityDC.density_structured_dc_tailPrimes
#print axioms Sarkozy.DensityDC.density_structured_dc_tailPrimes_theta
#print axioms Sarkozy.DensityDC.tensorLaw_atoms_transport
#print axioms Sarkozy.Structured.density_structured_theta
#print axioms Sarkozy.Structured.density_structured_theta_production
#print axioms Sarkozy.Structured.envelopeBound_of_terms
#print axioms Sarkozy.Structured.repair_neumann
#print axioms Sarkozy.Mixing.prefix_conductor_blocks
#print axioms Sarkozy.Mixing.pair_support
#print axioms Sarkozy.Mixing.pair_support_on
#print axioms Sarkozy.TraceMixing.graphLaw_R4
#print axioms Sarkozy.TraceMixing.tail_R4
#print axioms Sarkozy.TraceMixing.features_norm_bound
#print axioms Sarkozy.TraceMixing.tripleOp_ge
#print axioms Sarkozy.TraceMixing.disjOp_eigen

-- Added 1 November 2026, last work window (18:00–18:35 UTC).
#print axioms Sarkozy.Labellings.patternLaw_fold_invariant
#print axioms Sarkozy.Labellings.fixed_reflections
#print axioms Sarkozy.Labellings.foldGraphLaw_layerSwap
#print axioms Sarkozy.Labellings.root_card_edges
#print axioms Sarkozy.Labellings.root_automorphisms
#print axioms Sarkozy.Labellings.layer12_automorphisms
#print axioms Sarkozy.TraceMixing.class_three_ii
#print axioms Sarkozy.TraceMixing.class_three_iii_ratio
#print axioms Sarkozy.SecondOrder.direct_star_inputs
#print axioms Sarkozy.Certificates.e_law_numerics
#print axioms Sarkozy.Structured.sharpFirstTerms_of_folded
#print axioms Sarkozy.Structured.envelopeEnergies_of_terms
#print axioms Sarkozy.Structured.fixedIntervalEnvelopeEnergies_of_terms
#print axioms Sarkozy.TraceMixing.density_structured_theta_few
#print axioms Sarkozy.TraceMixing.density_structured_theta_two_occ
#print axioms Sarkozy.TraceMixing.production_pairs_of_index
#print axioms Sarkozy.TraceMixing.label_bound_fails
#print axioms Sarkozy.Cancellation.densityCancellation_of_steps
#print axioms Sarkozy.Cancellation.paper_encoding
#print axioms Sarkozy.Cancellation.tailLaw_mix
#print axioms Sarkozy.DensityUpgrade.strongF_two_layer
#print axioms Sarkozy.DensityUpgrade.upperDiagonal_L70

-- Added 1 November 2026, 18:40–18:50 UTC.
#print axioms Sarkozy.EdgeGate.edge_gate_band
#print axioms Sarkozy.Labellings.corner_table
#print axioms Sarkozy.EdgeGate.edge_moment_band
#print axioms Sarkozy.EdgeGate.invariant_pair_edge
#print axioms Sarkozy.EdgeGate.mixedLpBound_iff_conditioningUnitMixed
#print axioms Sarkozy.Certificates.clique36_binomial_gate
#print axioms Sarkozy.Certificates.clique36_denominator_gate

#print axioms Sarkozy.MainAnchor.main_anchor_paper
#print axioms Sarkozy.MainAnchor.main_anchor
#print axioms Sarkozy.LedgerAnchor.ComparisonData.theoremC_classes_reduced_anchor_of_ledger
#print axioms Sarkozy.Param.Params.anchor_valid
#print axioms Sarkozy.TheoremCParam.Structured.envelopeBoundNonneg_of_terms
#print axioms Sarkozy.CancellationSteps.densityCancellation_paper
#print axioms Sarkozy.CancellationSteps.densityCancellation_of_data
#print axioms Sarkozy.CancellationSteps.densityCancellation_of_standing
#print axioms Sarkozy.CancellationSteps.prime_lt_P4_dispatch
#print axioms Sarkozy.TailUnit.tailLawFamily_unit
#print axioms Sarkozy.TailUnit.hunit_of_tailLaws
#print axioms Sarkozy.TailUnit.tail_badComponent_not_unit
#print axioms Sarkozy.DLK.fourCycle_iff_spectral
#print axioms Sarkozy.DLK.principal_opBound
#print axioms Sarkozy.DLK.witnessKernel_opBound_twoCycles_of_fourCycle
#print axioms Sarkozy.DLK.glue_matching_twoCycles_of_fourCycle
#print axioms Sarkozy.ExtractionK.grouped_extraction_paper
#print axioms Sarkozy.ExtractionK.grouped_extraction_specData
#print axioms Sarkozy.ExtractionK.pinned_collision_opBound
#print axioms Sarkozy.DensityMoments.cell_gates
#print axioms Sarkozy.DensityMoments.coupled_spectator_estimate_hasSharpBound
#print axioms Sarkozy.DensityMoments.middle_packet_unit_mixed_proved
#print axioms Sarkozy.Interpolation.riesz_thorin_bilinear
#print axioms Sarkozy.Interpolation.invariant_pair_three_halves
#print axioms Sarkozy.Interpolation.square_pair_moment_band
#print axioms Sarkozy.Interpolation.upperDiagonal_L70_proved
#print axioms Sarkozy.EnvelopeInputs.abs_tensor_energy_le_unchanged_atoms
#print axioms Sarkozy.EnvelopeInputs.abs_folded_energy_le_unchanged_atoms
#print axioms Sarkozy.JointRows.Coll.joint_rows_a_full
#print axioms Sarkozy.JointRows.Restrict.joint_rows_a_paley
#print axioms Sarkozy.JointRows.Restrict.joint_potential_paley
#print axioms Sarkozy.JointRows.Sector.hsector_holds
#print axioms Sarkozy.JointRows.PaleyGauss.paley_paleyLike
#print axioms Sarkozy.JointRows.StarOps.wOp_gram
#print axioms Sarkozy.JointRows.StarOps.pure_block_identity
#print axioms Sarkozy.JointRows.joint_blocks_rp'
#print axioms Sarkozy.SpectralD.Cx.spectral_criterion_cut_S1
#print axioms Sarkozy.SpectralD.Cx.PA_density
#print axioms Sarkozy.PartV.tailDatum_gates
#print axioms Sarkozy.PartV.tailTilde_split
#print axioms Sarkozy.TraceMixing.class_three_iii_density
#print axioms Sarkozy.TraceMixing.one_layer_density
#print axioms Sarkozy.EnvelopeInputsBlock.main_anchor_paper_block_final
#print axioms Sarkozy.IndexCert.main_anchor_paper_block_cert
#print axioms Sarkozy.BlockAnchor.main_anchor_paper_block
#print axioms Sarkozy.EnvelopeInputsBlock.main_anchor_paper_block_inputs
#print axioms Sarkozy.IndexCert.main_anchor_paper_cert
#print axioms Sarkozy.EnvelopeInputsParam.main_anchor_paper_inputs
#print axioms Sarkozy.IndexCert.paperRI_le_anchorLedger
#print axioms Sarkozy.IndexCert.paperIndexBound
#print axioms Sarkozy.BlockAnchor.toy_partition_L₀_le
#print axioms Sarkozy.BlockAnchor.merged_paper_L₀_ge
#print axioms Sarkozy.TheoremCBlock.densityCancellation_paper_block
#print axioms Sarkozy.Misc.matchingReservedBound_block
#print axioms Sarkozy.EnvelopeInputsBlock.paper_indexMomentBound_block
#print axioms Sarkozy.PartVRecords.tailLawFamily_mixing
#print axioms Sarkozy.PartVRecords.FrameData.gram_cp3
#print axioms Sarkozy.DensityMoments.coupled_spectator_estimate_sharpDecomp
#print axioms Sarkozy.SpectralD.Root.LL20_criterion
#print axioms Sarkozy.SpectralD.Root.LL22_criterion
#print axioms Sarkozy.SpectralD.Cx.spectral_criterion_cut_full
#print axioms Sarkozy.UpperReference.Cert.rootCaps_P3
#print axioms Sarkozy.PartVLaws.main_anchor_paper_block_v2
#print axioms Sarkozy.Target.thetaSmall_of_thetaSmallRR
#print axioms Sarkozy.Target.sarkozyBound_mono
#print axioms Sarkozy.Target.sarkozyBound_epsTarget_of_epsAnchor
#print axioms Sarkozy.MainTarget.main_target_paper_block
#print axioms Sarkozy.TargetLedger.targetLedger_theta_lt
#print axioms Sarkozy.TargetLedger.targetLedger_bounds
#print axioms Sarkozy.TargetLedger.ComparisonData.theoremC_classes_reduced_target_of_ledger
#print axioms Sarkozy.MainTarget.paperRIAt_le_targetLedger
#print axioms Sarkozy.FirstStagePaper.main_target_paper_block_A1
#print axioms Sarkozy.FirstStagePaper.block_delta_norm_le
#print axioms Sarkozy.FirstStagePaper.blockSharp_of_block
#print axioms Sarkozy.TailCorr.tailInputsCorr_of_core
#print axioms Sarkozy.SpectralOne.spectral_criterion_cut_full_one_paper
#print axioms Sarkozy.SpectralOne.LL20_criterion_one
#print axioms Sarkozy.TailCorrCore.tailInputsCorr_of_core1
#print axioms Sarkozy.GramBracketPaper.main_target_paper_block_A2

-- The exact spectral-to-reflection bridge for the upper and tail laws (6 November 2026).
#print axioms Sarkozy.Spectral.cutOp_below
#print axioms Sarkozy.PartVLaws.FieldGraphs.lamOf_eq_graphLaw
#print axioms Sarkozy.PartVLaws.FieldGraphs.layer_diagonalHalf
#print axioms Sarkozy.PartVLaws.FieldGraphs.tail_layerCap
#print axioms Sarkozy.PartVLaws.FieldGraphs.chamberHalfEquiv_edges
#print axioms Sarkozy.PartVLaws.FieldGraphs.foldForm_eq_halfLaw
#print axioms Sarkozy.PartVLaws.FieldGraphs.rootEnv_of_cutOp
#print axioms Sarkozy.PartVLaws.FieldGraphs.tail_rootEnv_two
#print axioms Sarkozy.PartVLaws.FieldGraphs.tail_rootEnv_one
#print axioms Sarkozy.PartVLaws.FieldGraphs.tail_rootEnv_of_LL20
#print axioms Sarkozy.PartVLaws.FieldGraphs.tail_layerCap_of_LL22
#print axioms Sarkozy.TailCorrCore.tailSpectralCore1_of_operatorBounds
#print axioms Sarkozy.TailCorrCore.tailInputsCorr_of_operatorBounds
#print axioms Sarkozy.TailCorrCore.tailInputsValid_of_operatorBounds

-- Soundness of certificate graph data, witness checks, components, and arithmetic.
#print axioms Sarkozy.F3Kernel.GraphData.mem_cross20
#print axioms Sarkozy.F3Kernel.GraphData.mem_cross22
#print axioms Sarkozy.F3Kernel.GraphData.adj20
#print axioms Sarkozy.F3Kernel.GraphData.adj22
#print axioms Sarkozy.F3Kernel.bits_spread
#print axioms Sarkozy.F3Kernel.bit_spread_mul
#print axioms Sarkozy.F3Kernel.isWitness_of_checks
#print axioms Sarkozy.F3Kernel.isCover_of_checks
#print axioms Sarkozy.F3Kernel.Components.LL20_table_four
#print axioms Sarkozy.F3Kernel.Components.entry_sound
#print axioms Sarkozy.F3Kernel.leafCheck_trace
#print axioms Sarkozy.F3Kernel.LeafTrace.LL20_components
#print axioms Sarkozy.F3Kernel.LeafTrace.LL22_components
#print axioms Sarkozy.F3Kernel.LeafTrace.product_bound
#print axioms Sarkozy.F3Kernel.LeafTrace.orderX_vmask
#print axioms Sarkozy.F3Kernel.LeafTrace.orderY_vmask
#print axioms Sarkozy.F3Kernel.leafCheck_LL20_valid
#print axioms Sarkozy.F3Kernel.leafCheck_LL22_valid

-- Root masks, connector decisions, and complete accepted class bodies.
#print axioms Sarkozy.F3Kernel.decM_before_rank
#print axioms Sarkozy.F3Kernel.classRoot_compressed
#print axioms Sarkozy.F3Kernel.classRoot_coherent
#print axioms Sarkozy.F3Kernel.classRoot_mem_compressedPartition
#print axioms Sarkozy.F3Kernel.classRoot_nonstars
#print axioms Sarkozy.F3Kernel.LL20_checkedRoot_validRecords
#print axioms Sarkozy.F3Kernel.LL22_checkedRoot_validRecords
#print axioms Sarkozy.F3Kernel.LL20_chunk_validRecords
#print axioms Sarkozy.F3Kernel.LL22_chunk_validRecords
#print axioms Sarkozy.F3Kernel.classRoot_key_injective
#print axioms Sarkozy.F3Kernel.classRoot_classes_disjoint
#print axioms Sarkozy.F3Kernel.run_rootKeys
#print axioms Sarkozy.F3Kernel.chunk_isExactPartition
#print axioms Sarkozy.F3Kernel.chunk_nonstar_partition

-- Packed counts, scan order, witness edges, and the complete leaf exponent.
#print axioms Sarkozy.F3Kernel.LeafTrace.ordX_lt_iff_scan
#print axioms Sarkozy.F3Kernel.LeafTrace.ordY_lt_iff_scan
#print axioms Sarkozy.F3Kernel.signature_packCounts
#print axioms Sarkozy.F3Kernel.LL20_adjacencyCounts
#print axioms Sarkozy.F3Kernel.LL22_adjacencyCounts
#print axioms Sarkozy.F3Kernel.signature_countState_eq_card
#print axioms Sarkozy.F3Kernel.witSwitch_exponent
#print axioms Sarkozy.F3Kernel.LeafTrace.coverScanX_vertices
#print axioms Sarkozy.F3Kernel.LeafTrace.coverScanY_vertices
#print axioms Sarkozy.F3Kernel.LeafTrace.eX_eq_ordT
#print axioms Sarkozy.F3Kernel.LeafTrace.eY_eq_ordT
#print axioms Sarkozy.F3Kernel.LeafTrace.exponent_eq_recordExp

-- Full SWAR semantics and unconditional free-degree encodings in accepted chunks.
#print axioms Sarkozy.F3Kernel.swarByteStage_eq_counts
#print axioms Sarkozy.F3Kernel.swar_encodeLanes
#print axioms Sarkozy.F3Kernel.MatrixWord.swar_rows
#print axioms Sarkozy.F3Kernel.MatrixWord.swar_cols
#print axioms Sarkozy.F3Kernel.freeDegreeCounts_of_matrixWords
#print axioms Sarkozy.F3Kernel.classRoot_matrixWords
#print axioms Sarkozy.F3Kernel.run_matrixWords
#print axioms Sarkozy.F3Kernel.LL20_chunk_freeDegreeCounts
#print axioms Sarkozy.F3Kernel.LL22_chunk_freeDegreeCounts

-- Exact products and mathematical coefficient bounds.
#print axioms Sarkozy.F3Kernel.sideProd_counts
#print axioms Sarkozy.F3Kernel.countProd_eq_finset
#print axioms Sarkozy.F3Kernel.sideCountProd_ordered
#print axioms Sarkozy.F3Kernel.sideProd_ordered
#print axioms Sarkozy.F3Kernel.LeafTrace.product_eq_recordProduct
#print axioms Sarkozy.F3Kernel.LeafTrace.recordProduct_bound
#print axioms Sarkozy.F3Kernel.LeafTrace.leafCoef_bound
#print axioms Sarkozy.F3Kernel.LeafTrace.gpLeafCoef_bound
#print axioms Sarkozy.F3Kernel.GraphData.graph20_adjacencyCounts
#print axioms Sarkozy.F3Kernel.GraphData.graph22_adjacencyCounts
#print axioms Sarkozy.F3Kernel.LL20_chunk_gpLeafCoef_bound
#print axioms Sarkozy.F3Kernel.LL22_chunk_gpLeafCoef_bound

-- Exact free-edge totals, root masses, and complete chains of chunks.
#print axioms Sarkozy.F3Kernel.lane64_mul_LANE0
#print axioms Sarkozy.F3Kernel.LeafTrace.free_eq_card
#print axioms Sarkozy.F3Kernel.classRoot_freeCount
#print axioms Sarkozy.F3Kernel.run_cmass
#print axioms Sarkozy.F3Kernel.chunk_mass_eq_rootMass
#print axioms Sarkozy.F3Kernel.LL20_nonstarMass
#print axioms Sarkozy.F3Kernel.LL22_nonstarMass
#print axioms Sarkozy.F3Kernel.chunks_tiling
#print axioms Sarkozy.F3Kernel.chunks_mass_card
#print axioms Sarkozy.F3Kernel.LL20_chunks_full_partition
#print axioms Sarkozy.F3Kernel.LL22_chunks_full_partition

-- Coefficient accumulators and the complete certificate-to-operator implication.
#print axioms Sarkozy.F3Kernel.leafOutputs_sound
#print axioms Sarkozy.F3Kernel.chunks_accumulator
#print axioms Sarkozy.F3Kernel.chunksOutput_bounds
#print axioms Sarkozy.F3Kernel.chunksOutputs_nodup
#print axioms Sarkozy.F3Kernel.chunks_groupedCoefficient_le
#print axioms Sarkozy.F3Kernel.chunks_coefficientPolynomial_le
#print axioms Sarkozy.F3Kernel.chunks_nonstar_bound
#print axioms Sarkozy.F3Kernel.LL20_chunks_nonstar_bound
#print axioms Sarkozy.F3Kernel.LL22_chunks_nonstar_bound

-- Production factor tables at their actual numerical anchor, 2^60.
#print axioms Sarkozy.F3Kernel.leafS_le_row_bound
#print axioms Sarkozy.F3Kernel.GraphData.leafS_m20
#print axioms Sarkozy.F3Kernel.GraphData.leafS_rho20
#print axioms Sarkozy.F3Kernel.GraphData.leafS_m22
#print axioms Sarkozy.F3Kernel.GraphData.leafS_rho22
#print axioms Sarkozy.F3Kernel.LL20_gradedTableBounds
#print axioms Sarkozy.F3Kernel.LL22_gradedTableBounds
#print axioms Sarkozy.F3Kernel.chunksAccepted_append

-- Vertex transport and fully rational coefficient bounds.
#print axioms Sarkozy.F3Kernel.nonstar_bound_equiv
#print axioms Sarkozy.F3Kernel.LL20_paper_nonstar_bound
#print axioms Sarkozy.F3Kernel.LL22_paper_nonstar_bound
#print axioms Sarkozy.F3Kernel.completionFactor_anchor_le
#print axioms Sarkozy.F3Kernel.certificatePolynomial_le_caps

-- Complete 902,545-leaf certificates and the original paper's nonstar forms.
#print axioms Sarkozy.F3Kernel.LL20_full_partition
#print axioms Sarkozy.F3Kernel.LL22_full_partition
#print axioms Sarkozy.F3Kernel.LL20_full_accumulators
#print axioms Sarkozy.F3Kernel.LL22_full_accumulators
#print axioms Sarkozy.F3Kernel.LL20_full_nonstar_bound
#print axioms Sarkozy.F3Kernel.LL22_full_nonstar_bound

-- Endpoint decay, root finite tests, and uniform collision estimates.
#print axioms Sarkozy.F3Kernel.productionPolynomial_endpoint
#print axioms Sarkozy.F3Kernel.LL20_nsOp_tail
#print axioms Sarkozy.F3Kernel.LL22_nsOp_tail
#print axioms Sarkozy.SpectralD.Cx.LL20_tail_finiteTest
#print axioms Sarkozy.SpectralD.Cx.LL22_tail_finiteTest
#print axioms Sarkozy.SpectralD.collisionDnat_uniform
#print axioms Sarkozy.SpectralD.LL20_collOp_tail
#print axioms Sarkozy.SpectralD.LL22_collOp_tail

-- Root tail spectral estimates, 6 November 2026.
#print axioms Sarkozy.SecondOrder.pivotBudgets_of_card
#print axioms Sarkozy.SecondOrder.starMstar_uniform
#print axioms Sarkozy.SecondOrder.starZstar_uniform
#print axioms Sarkozy.SpectralD.graphCountError_le_coarse
#print axioms Sarkozy.SpectralD.LL20_starMstar
#print axioms Sarkozy.SpectralD.LL22_starZstar
#print axioms Sarkozy.SpectralD.tail_perpendicular_scalar
#print axioms Sarkozy.SpectralD.LL20_tail_expansion_bounds
#print axioms Sarkozy.SpectralD.LL22_tail_expansion_bounds
#print axioms Sarkozy.SpectralD.Rcut_tail
#print axioms Sarkozy.SpectralD.Rprime_tail
#print axioms Sarkozy.SpectralD.tail_devConst
#print axioms Sarkozy.SpectralD.betaG_tail_row
#print axioms Sarkozy.SpectralD.bX_tail_row
#print axioms Sarkozy.SpectralD.small_rowX_tail
#print axioms Sarkozy.SpectralD.small_rowV_tail
#print axioms Sarkozy.SpectralD.tail_etaQ
#print axioms Sarkozy.SpectralD.tail_epsilonV
#print axioms Sarkozy.SpectralD.coupling_error_tail
#print axioms Sarkozy.SpectralD.etaB_tail
#print axioms Sarkozy.SpectralD.tail_analytic_inputs
#print axioms Sarkozy.SpectralD.Root.LL20_tail_three
#print axioms Sarkozy.SpectralD.Root.LL22_tail_three

-- Root tail completion and uniform estimates for the nine smaller cuts.
#print axioms Sarkozy.SpectralD.Root.LL20_tail
#print axioms Sarkozy.SpectralD.Root.LL22_tail
#print axioms Sarkozy.PartVLaws.FieldGraphs.tail_rootEnv_LL20
#print axioms Sarkozy.PartVLaws.FieldGraphs.tail_layerCap_LL22
#print axioms Sarkozy.TailCorrCore.tailCutBounds_of_small
#print axioms Sarkozy.SpectralD.small_nonstar_bound
#print axioms Sarkozy.SpectralD.small_nsOp_tail
#print axioms Sarkozy.PartVLaws.FieldGraphs.SmallCut.cross_pairs
#print axioms Sarkozy.SpectralD.AtMost.small_tail_expansion_bounds
#print axioms Sarkozy.SpectralD.AtMost.tail_analytic_inputs
#print axioms Sarkozy.SpectralD.AtMost.tail_criterion
#print axioms Sarkozy.SpectralD.qform_nonneg_of_gaussian_factor

-- All eleven tail cut bounds, including the nine graph-checked smaller cuts.
#print axioms Sarkozy.SpectralD.finiteTest_of_scaled_matrix
#print axioms Sarkozy.SpectralD.AtMost.tail_criterion_tight
#print axioms Sarkozy.SpectralD.SmallMatrices.models
#print axioms Sarkozy.SpectralD.SmallMatrices.tests
#print axioms Sarkozy.SpectralD.SmallMatrices.residuals
#print axioms Sarkozy.SpectralD.SmallMatrices.finiteTest
#print axioms Sarkozy.SpectralD.SmallMatrices.tail_bound
#print axioms Sarkozy.TailCorrCore.tailCutBounds
#print axioms Sarkozy.TailCorrCore.tailInputsCorr_of_rowBounds

-- Both-prime-class star estimates for the ten conditional tail rows.
#print axioms Sarkozy.JointRows.StarOps.sum_paley_sq_eq_odd
#print axioms Sarkozy.JointRows.StarOps.pureKernel_bound_odd
#print axioms Sarkozy.JointRows.StarOps.rowStar_multiplier_bound_support
#print axioms Sarkozy.JointRows.StarOps.meanKernelPrime_bound
#print axioms Sarkozy.JointRows.StarOps.starKernel_bound_odd
#print axioms Sarkozy.Labellings.character_admissible_bound
#print axioms Sarkozy.JointRows.PinCoordinate.mean_tail
#print axioms Sarkozy.PartVLaws.FieldGraphs.RowCase.row_gram
#print axioms Sarkozy.PartVLaws.FieldGraphs.RowCase.col_gram
#print axioms Sarkozy.PartVLaws.FieldGraphs.RowCase.product_star_bound
#print axioms Sarkozy.PartVLaws.FieldGraphs.RowCase.strict_star_bound

-- Full raw kernels and normalized reference charts for all ten tail rows.
#print axioms Sarkozy.JointRows.PinTail.nonstar_monomial
#print axioms Sarkozy.JointRows.PinTail.nonstar_bound
#print axioms Sarkozy.JointRows.PinTail.collision_bound
#print axioms Sarkozy.JointRows.PinTail.raw_perp
#print axioms Sarkozy.JointRows.Coll.strict_product_weight
#print axioms Sarkozy.JointRows.StarOps.star_full_tail
#print axioms Sarkozy.JointRows.chart_bound_of_norm
#print axioms Sarkozy.PartVLaws.FieldGraphs.RowCase.pinData_allowed
#print axioms Sarkozy.PartVLaws.FieldGraphs.RowCase.finLaw_weight
#print axioms Sarkozy.PartVLaws.FieldGraphs.RowCase.fin_raw_bound
#print axioms Sarkozy.PartVLaws.FieldGraphs.RowCase.fin_raw_full
#print axioms Sarkozy.PartVLaws.FieldGraphs.RowCase.fin_mass_error
#print axioms Sarkozy.PartVLaws.FieldGraphs.RowCase.fin_marginal_error
#print axioms Sarkozy.PartVLaws.FieldGraphs.RowCase.fin_chart_bound

-- The actual conditional rows and complete tail-input obligation.
#print axioms Sarkozy.JointRows.Coll.rawKer_indicator
#print axioms Sarkozy.JointRows.chart_variance_bound
#print axioms Sarkozy.JointRows.KernelCorr.transport
#print axioms Sarkozy.PartVLaws.FieldGraphs.RowCase.pack_mem_iff
#print axioms Sarkozy.PartVLaws.FieldGraphs.RowCase.low_completion_count
#print axioms Sarkozy.PartVLaws.FieldGraphs.RowCase.high_completion_count
#print axioms Sarkozy.PartVLaws.FieldGraphs.RowCase.row_density_lower
#print axioms Sarkozy.PartVLaws.FieldGraphs.RowCase.row_joint_weight
#print axioms Sarkozy.PartVLaws.FieldGraphs.RowCase.conditional_row_correlation
#print axioms Sarkozy.PartVLaws.FieldGraphs.RowCase.conditional_row_norm
#print axioms Sarkozy.TailCorrCore.tailRowBounds
#print axioms Sarkozy.TailCorrCore.tailInputsCorr
#print axioms Sarkozy.TailCorrCore.tailInputsValid
#print axioms Sarkozy.GramBracketPaper.A2BlockDataTarget.ofProvedTail

-- All 33 middle-piece completion and protection certificates.
#print axioms Sarkozy.MiddleRecords.CompletionData.record_endpoints
#print axioms Sarkozy.MiddleRecords.pieceWeights_completes
#print axioms Sarkozy.MiddleRecords.pieceWeights_protects
#print axioms Sarkozy.MiddleRecords.pieceWeights_protection_rounding
#print axioms Sarkozy.MiddleRecords.pieceWeights_root_slack
#print axioms Sarkozy.GramBracketPaper.GramInputs.ofRecordedPieces

-- The exact coherent dictionary, its symmetries, and the Weil score bound.
#print axioms Sarkozy.PartV.CoherentDictionary.generated39_perm
#print axioms Sarkozy.PartV.CoherentDictionary.dictionary39_invariant
#print axioms Sarkozy.PartV.CoherentDictionary.dictionary39_layerSwap
#print axioms Sarkozy.PartV.CoherentDictionary.dictionary39_score_bound
#print axioms Sarkozy.PartV.CoherentDictionary.dictionary39_weight_bounds
#print axioms Sarkozy.PartV.CoherentDictionary.dictionary39_chamber_cases
#print axioms Sarkozy.PartV.CoherentDictionary.dictionary39_layer_cases
#print axioms Sarkozy.PartV.CoherentDictionary.dictionary39_case_counts
#print axioms Sarkozy.PartV.middleBlockReference_coherent39_layerSwap

-- The coherent chamber matrix at the selected parameters, in exact arithmetic.
#print axioms Sarkozy.PositiveRoots.CoherentMatrix.coefficient_eq
#print axioms Sarkozy.PositiveRoots.CoherentMatrix.model_checks
#print axioms Sarkozy.PositiveRoots.CoherentMatrix.checked_matrix_nonneg
#print axioms Sarkozy.PositiveRoots.CoherentMatrix.selected_chamber_bound

-- All 310 upper-band records and their 32,550 completion inequalities.
#print axioms Sarkozy.UpperRecords.CompletionData.record_endpoints
#print axioms Sarkozy.UpperRecords.CompletionData.record_completes
#print axioms Sarkozy.UpperRecords.bandWeightsOK
#print axioms Sarkozy.UpperRecords.band_budget
#print axioms Sarkozy.PartVLaws.UpperBlockInputs.ofBand

-- Coherent traces with one repeated label and exact covariance support counts.
#print axioms Sarkozy.PartV.CoherentDictionary.trace_pin
#print axioms Sarkozy.PartV.CoherentDictionary.collect_eval
#print axioms Sarkozy.PartV.CoherentDictionary.pin_complete
#print axioms Sarkozy.PartV.CoherentDictionary.pin_collections
#print axioms Sarkozy.PartV.CoherentDictionary.dictionary39_single_pin_bound
#print axioms Sarkozy.PartV.CoherentDictionary.dictionary39_single_pin_weight
#print axioms Sarkozy.PartV.CoherentDictionary.covarianceCase_valid
#print axioms Sarkozy.PartV.CoherentDictionary.covariance_cost_totals
#print axioms Sarkozy.PartV.CoherentDictionary.coherent_even_matching_budget

-- Both coherent endpoint matrices, all invariant mean gates, and the parameter interval.
#print axioms Sarkozy.PositiveRoots.CoherentMean.core_mean_bound
#print axioms Sarkozy.PositiveRoots.CoherentMean.mixed_mean_bound
#print axioms Sarkozy.PositiveRoots.CoherentMean.layer_mean_bound
#print axioms Sarkozy.PositiveRoots.CoherentEndpoint.chamber_bound
#print axioms Sarkozy.PositiveRoots.CoherentEndpoint.layer_bound
#print axioms Sarkozy.PositiveRoots.CoherentOldChamber.old_restricted
#print axioms Sarkozy.PositiveRoots.CoherentOldChamber.old_chamber_bound
#print axioms Sarkozy.PositiveRoots.CoherentOldLayer.old_layer_bound
#print axioms Sarkozy.PositiveRoots.CoherentParameters.alpha_bounds
#print axioms Sarkozy.PositiveRoots.CoherentParameters.chamber_bound
#print axioms Sarkozy.PositiveRoots.CoherentParameters.layer_bound
#print axioms Sarkozy.PositiveRoots.CoherentParameters.mean_bound
#print axioms Sarkozy.PositiveRoots.CoherentParameters.mean_prices_below
#print axioms Sarkozy.PositiveRoots.CoherentParameters.selected_chamber_bound
#print axioms Sarkozy.PositiveRoots.CoherentParameters.selected_mean_price

-- Auxiliary diagonal products, exact one-sided collection, and deleted-point errors.
#print axioms Sarkozy.PartV.CoherentDictionary.diagonal_constant
#print axioms Sarkozy.PartV.CoherentDictionary.oneSided_count
#print axioms Sarkozy.PartV.CoherentDictionary.oneSided_pairs
#print axioms Sarkozy.PartV.CoherentDictionary.oneSided_absolute_mass
#print axioms Sarkozy.PartV.CoherentDictionary.oneSided_trace
#print axioms Sarkozy.PartV.CoherentDictionary.evaluation_mul
#print axioms Sarkozy.PartV.CoherentDictionary.traceProduct_error
#print axioms Sarkozy.PartV.CoherentDictionary.auxiliary_diagonal
#print axioms Sarkozy.PartV.CoherentDictionary.auxiliary_diagonal_error
#print axioms Sarkozy.PartV.CoherentDictionary.auxiliary_diagonal_split_error
#print axioms Sarkozy.PartV.CoherentDictionary.auxiliary_diagonal_kernel_error
#print axioms Sarkozy.PartV.CoherentDictionary.dictionary39_unrestricted
#print axioms Sarkozy.PartV.CoherentDictionary.dictionary39_unrestricted_weight
#print axioms Sarkozy.PartV.CoherentDictionary.Cancellation.trace_error
#print axioms Sarkozy.PartV.CoherentDictionary.exists_injective_cancellation
#print axioms Sarkozy.PartV.CoherentDictionary.trace_partial_cancellation_bound
#print axioms Sarkozy.PartV.CoherentDictionary.dictionary39_partial_bound_of_even
#print axioms Sarkozy.PartV.CoherentDictionary.Cancellation.fiber_parity
#print axioms Sarkozy.PartV.CoherentDictionary.cancellation_matching
#print axioms Sarkozy.PartV.CubePins.card_pins
#print axioms Sarkozy.PartV.CubePins.mass_matchings_budget
#print axioms Sarkozy.PartV.CoherentDictionary.cancellation_matchingEvent
#print axioms Sarkozy.PartV.CoherentDictionary.halfSupport_matching_budget
#print axioms Sarkozy.PartV.CoherentDictionary.exceptional_mass
#print axioms Sarkozy.PartV.CoherentDictionary.rawCrossKernel_le
#print axioms Sarkozy.PartV.CoherentDictionary.chamber_exceptional_mass
#print axioms Sarkozy.PartV.CoherentDictionary.layer_exceptional_mass
#print axioms Sarkozy.PartV.CoherentDictionary.raw_collision_weight_mass
#print axioms Sarkozy.L20Cap.card_G6
#print axioms Sarkozy.L20Cap.G6_density
#print axioms Sarkozy.PartV.CoherentDictionary.chamberEquiv_edges
#print axioms Sarkozy.PartV.CoherentDictionary.chamber_half_nonempty
#print axioms Sarkozy.PartV.CoherentDictionary.chamber_half_density
#print axioms Sarkozy.PartV.CoherentDictionary.chamber_exceptional_mass_graph
#print axioms Sarkozy.PartV.CoherentDictionary.chamber_collision_weight_mass_graph
#print axioms Sarkozy.Extraction.collision_rowSum_signed_incident_le
#print axioms Sarkozy.Extraction.collision_rowSum2_signed_incident_le
#print axioms Sarkozy.L20Cap.balanced_gamma
#print axioms Sarkozy.L20Cap.balancedRho_eq
#print axioms Sarkozy.L20Cap.balancedPoly_sum
#print axioms Sarkozy.L20Cap.balanced_incident_le
#print axioms Sarkozy.L20Cap.balanced_collision_row
#print axioms Sarkozy.L20Cap.hD_balanced
#print axioms Sarkozy.PartV.CoherentDictionary.chamber_raw_kernel
#print axioms Sarkozy.PartV.CoherentDictionary.chamber_collision_mass_balanced
#print axioms Sarkozy.PartV.CoherentDictionary.chamber_collision_weight_balanced
#print axioms Sarkozy.PartV.CoherentDictionary.weightedChamberCollision_symm
#print axioms Sarkozy.PartV.CoherentDictionary.weightedChamberCollision_schur

-- Actual coherent feature frames and one-sided Fourier matrix orders.
#print axioms Sarkozy.PositiveRoots.CoherentFrame.graph_pivot_density
#print axioms Sarkozy.PositiveRoots.CoherentFrame.graph_feature_entry
#print axioms Sarkozy.PositiveRoots.CoherentFrame.graph_synthesis
#print axioms Sarkozy.PositiveRoots.CoherentFrame.graph_analysis
#print axioms Sarkozy.PositiveRoots.CoherentFrame.graph_starPart_norm
#print axioms Sarkozy.PositiveRoots.lower_bound_submatrix
#print axioms Sarkozy.SpectralD.StarMatrix.blockForm_lower
#print axioms Sarkozy.PositiveRoots.CoherentFrame.selected_chamber_lower
#print axioms Sarkozy.PositiveRoots.CoherentFrame.chamber_parameter_lower
#print axioms Sarkozy.PositiveRoots.CoherentFrame.graph_layer_lower

-- Physical trace-pair factorization and the full coherent score norm.
#print axioms Sarkozy.SpectralD.StarMatrix.tracePair_scaled_factor
#print axioms Sarkozy.PositiveRoots.CoherentFrame.chamberCoeff_eq
#print axioms Sarkozy.PositiveRoots.CoherentFrame.chamberCoeff_norm
#print axioms Sarkozy.PositiveRoots.CoherentFrame.chamber_score_factor
#print axioms Sarkozy.PositiveRoots.CoherentFrame.physical_leading_identity
#print axioms Sarkozy.PositiveRoots.CoherentFrame.selected_physical_leading_lower
#print axioms Sarkozy.JointRows.StarOps.rawStar_analysis
#print axioms Sarkozy.SpectralC.normLe_average
#print axioms Sarkozy.SpectralC.matrixFeature_norm
#print axioms Sarkozy.PositiveRoots.CoherentFrame.cube_score_kernel
#print axioms Sarkozy.PositiveRoots.CoherentFrame.cube_score_norm
#print axioms Sarkozy.PositiveRoots.CoherentFrame.chamber_score_norm

-- Invariant means and the complete physical leading chamber order.
#print axioms Sarkozy.PositiveRoots.CoherentFrame.core_character_frame
#print axioms Sarkozy.PositiveRoots.CoherentFrame.mixedMean_fixed_frame
#print axioms Sarkozy.PositiveRoots.CoherentFrame.halfLaw_private_compression
#print axioms Sarkozy.PositiveRoots.CoherentFrame.chamber_mean_block_synthesis
#print axioms Sarkozy.PositiveRoots.CoherentFrame.chamber_mixed_mean_synthesis
#print axioms Sarkozy.PositiveRoots.CoherentFrame.scoreMeanForm_blocks
#print axioms Sarkozy.PositiveRoots.CoherentFrame.chamber_scoreMeanForm_lower
#print axioms Sarkozy.PositiveRoots.CoherentFrame.invariant_branch_below
#print axioms Sarkozy.SpectralD.StarMatrix.translation_energy_split
#print axioms Sarkozy.SpectralD.StarMatrix.featAdj_invariant
#print axioms Sarkozy.SpectralD.StarMatrix.meanStarAdj_average
#print axioms Sarkozy.PositiveRoots.CoherentFrame.selected_physical_leading_centered_lower
#print axioms Sarkozy.PositiveRoots.CoherentFrame.parameter_physical_leading_centered_lower

#print axioms Sarkozy.PositiveRoots.CoherentFrame.selected_leading_real_lower
#print axioms Sarkozy.PositiveRoots.CoherentFrame.chamber_leading_real_norm

#print axioms Sarkozy.SpectralC.TwoLabel.starProduct_distinct_sq
#print axioms Sarkozy.SpectralC.TwoLabel.starProduct_equal_sq
#print axioms Sarkozy.L20Cap.card_coreT
#print axioms Sarkozy.L20Cap.coreLaw_cube_comparison
#print axioms Sarkozy.Cuts.swap_decorated_multiplier_norm
#print axioms Sarkozy.PositiveRoots.CoherentFrame.core_product_map_sq
#print axioms Sarkozy.PositiveRoots.CoherentFrame.private_product_map_sq
#print axioms Sarkozy.PositiveRoots.CoherentFrame.coherent_offdiag_bound
#print axioms Sarkozy.PositiveRoots.CoherentFrame.coherent_square_physical
#print axioms Sarkozy.PositiveRoots.CoherentFrame.coherent_offdiag_actual

-- Full coherent covariance and the projected auxiliary diagonal.
#print axioms Sarkozy.PartV.CoherentDictionary.diagonal_block_coefficients
#print axioms Sarkozy.PartV.CoherentDictionary.diagonal_block_coverage
#print axioms Sarkozy.PartV.CoherentDictionary.diagonal_blocks_eval
#print axioms Sarkozy.PartV.CoherentDictionary.twoSided_collect_eval
#print axioms Sarkozy.PositiveRoots.CoherentFrame.diagonal_private_budget
#print axioms Sarkozy.PositiveRoots.CoherentFrame.diagonal_core_budget
#print axioms Sarkozy.PositiveRoots.CoherentFrame.diagonal_cross_budget
#print axioms Sarkozy.PositiveRoots.CoherentFrame.core_singleton_map_sq
#print axioms Sarkozy.PositiveRoots.CoherentFrame.chamberTrace_core_private
#print axioms Sarkozy.PositiveRoots.CoherentFrame.chamber_diagonal_remainder_bound
#print axioms Sarkozy.PositiveRoots.CoherentFrame.chamberTwoSided_rectangle_bound
#print axioms Sarkozy.PositiveRoots.CoherentFrame.coherent_covariance_actual
#print axioms Sarkozy.PositiveRoots.CoherentFrame.coherent_covariance_actual_26400
#print axioms Sarkozy.Cuts.projectedDiagonal_gram
#print axioms Sarkozy.Cuts.diagonal_parts_orthogonal
#print axioms Sarkozy.Cuts.diagonal_parts_energy_exact

-- Actual coherent product inputs and the physical Z feature.
#print axioms Sarkozy.PositiveRoots.CoherentFrame.core_rawStar_mean_zero_norm
#print axioms Sarkozy.PositiveRoots.CoherentFrame.abs_starMean_graded
#print axioms Sarkozy.PositiveRoots.CoherentFrame.core_variableDiagonal_paper_norm
#print axioms Sarkozy.PositiveRoots.CoherentFrame.core_reducedStarProduct_norm
#print axioms Sarkozy.PositiveRoots.CoherentFrame.core_reducedStarProduct_norm_9_5
#print axioms Sarkozy.PositiveRoots.CoherentFrame.coreZProduct_residual_norm
#print axioms Sarkozy.PositiveRoots.CoherentFrame.coreZExceptional_bound
#print axioms Sarkozy.PositiveRoots.CoherentFrame.coreZProduct_physical
#print axioms Sarkozy.PositiveRoots.CoherentFrame.coreZProduct_physical_bound

-- The centered Z Gram and the complete 42-class rectangle certificate.
#print axioms Sarkozy.PositiveRoots.CoherentFrame.coreZKernel_norm_full
#print axioms Sarkozy.L20Cap.RectangleCertificate.partition_exact
#print axioms Sarkozy.L20Cap.RectangleCertificate.records_valid
#print axioms Sarkozy.L20Cap.RectangleCertificate.coefficient_sum
#print axioms Sarkozy.L20Cap.rectangle_nonstar_norm_282_target

#print axioms Sarkozy.Variance.WeightedMoment.weightedIdentity_verified
#print axioms Sarkozy.Variance.WeightedMoment.rootMarginal_ii_second_lamF_verified

-- Actual mass variation, centered rectangle, and the soft-kernel gap.
#print axioms Sarkozy.PositiveRoots.CoherentFrame.rectangle_mass_variation_small_40
#print axioms Sarkozy.PositiveRoots.CoherentFrame.rectangle_centered_norm_small_40
#print axioms Sarkozy.Cuts.swap_norm_deflated
#print axioms Sarkozy.L20Cap.rectangle_constant_gap
#print axioms Sarkozy.PositiveRoots.CoherentFrame.Ksoft_sub_one_norm_small_40
#print axioms Sarkozy.JointClosing.main_target_paper_block_joint
#print axioms Sarkozy.JointClosing.main_target_paper_block_joint_prefix
#print axioms Sarkozy.JointClosing.theoremC_joint_reduced_target_of_ledger
#print axioms Sarkozy.BlockSpecPaper.main_target_paper_joint_B1
#print axioms Sarkozy.BlockSpecPaper.main_target_paper_joint_B1_charges
#print axioms Sarkozy.ComparisonLawPaper.main_target_paper_block_B2
#print axioms Sarkozy.ClassBoundsPaper.main_target_paper_block_B4
#print axioms Sarkozy.ClassBoundsPaper.savings_cert
#print axioms Sarkozy.MainFinal.main_target_paper_final
#print axioms Sarkozy.PaperNumbers.main_target_paper_joint_N1_hist
#print axioms Sarkozy.PaperNumbers.costB_le
#print axioms Sarkozy.PaperNumbers.costL_le
#print axioms Sarkozy.BlockAdapter.main_target_paper_joint_B6
#print axioms Sarkozy.BlockAdapter.middleE21Caps_proved
#print axioms Sarkozy.BlockAdapter.upperLayerCaps_EE
#print axioms Sarkozy.EnvelopeEnergiesPaper.paperStageMoments_proved
#print axioms Sarkozy.MiddleComparison.comparisonInputsOfData
#print axioms Sarkozy.EnvelopeEnergiesPaper.abs_block_energy_le_unchanged
#print axioms Sarkozy.MainFinal2.main_target_paper_final2
#print axioms Sarkozy.MainFinal2.main_target_f1_final2
#print axioms Sarkozy.AnalyticCells.main_target_f1
#print axioms Sarkozy.MainFinal3.main_target_paper_final3
#print axioms Sarkozy.CliqueDeletion.paperCliqueDeletion
#print axioms Sarkozy.SignedEstimates.paperMiddleEstimates
#print axioms Sarkozy.NumericalFields.main_target_paper_final_E3
#print axioms Sarkozy.NumericalFields.upperBand_le_bandBound
#print axioms Sarkozy.EnvPrefix.main_target_paper_final3b
#print axioms Sarkozy.EnvPrefix.hCLpre_proved
#print axioms Sarkozy.ClassData.paper_classCost_le
#print axioms Sarkozy.ClassData.jointBound_target_allocJ
#print axioms Sarkozy.MainFinalJ.main_target_paper_final3c
#print axioms Sarkozy.MainFinalJ.main_target_paper_finalJ
#print axioms Sarkozy.ClassData.ledger_room
#print axioms Sarkozy.ClassData.allocJ_of_completed
#print axioms Sarkozy.MainFinalF1.main_target_f1_final3c
#print axioms Sarkozy.TargetGoal.main_goal_f1
#print axioms Sarkozy.F7Repair.hybrid_sum_π_le
#print axioms Sarkozy.F7Repair.hybrid_C_le
#print axioms Sarkozy.DensityFibre.envHdiffL_of_folded
#print axioms Sarkozy.MainFinalF1b.main_target_f1_final3d
#print axioms Sarkozy.MainFinalF1b.main_goal_f1b
#print axioms Sarkozy.DensityChain.envMeanBound_of_restoration
#print axioms Sarkozy.DensityChain.fixMeanBound_of_restoration
#print axioms Sarkozy.TailCorrelations.tailRp
#print axioms Sarkozy.TailCorrelations.tailCorr2
#print axioms Sarkozy.MainFinalF1c.main_goal_f1c
#print axioms Sarkozy.MainFinalF1c.tailTC_le_allowance
#print axioms Sarkozy.HsumProof.hsum_paperKappa
#print axioms Sarkozy.HsumProof.main_goal_f1P
#print axioms Sarkozy.MainFinalF1d.main_goal_f1d
#print axioms Sarkozy.MiddleRefinement.main_goal_f1e
#print axioms Sarkozy.MiddleRefinement.hmid_check
#print axioms Sarkozy.UpperRepair.main_goal_f1s
#print axioms Sarkozy.UpperRepair.main_goal_f1e
#print axioms Sarkozy.MainCombined.main_goal_f1g
#print axioms Sarkozy.DensityChain2.restoration_block
#print axioms Sarkozy.DensityChain2.fixMeanBound_paperFinal
#print axioms Sarkozy.MainCombined.main_goal_f1h
#print axioms Sarkozy.SignedGram.main_goal_f1f
#print axioms Sarkozy.MainCombined.main_goal_f1i
#print axioms Sarkozy.NormBoundsPaper.main_goal_hn
#print axioms Sarkozy.UpperCapsPaper.main_goal_f1i_ucp
#print axioms Sarkozy.UpperCapsPaper.upperCapTables_holds
#print axioms Sarkozy.PrimeGram.main_goal_f1j
#print axioms Sarkozy.NormBoundsPaper2.main_goal_nb2
#print axioms Sarkozy.MainCombined2.main_goal_f1k
#print axioms Sarkozy.ThetaOne.main_goal_theta1
#print axioms Sarkozy.ThetaOne.sharpFirstTerms_of_wholeFolded
#print axioms Sarkozy.ThetaOne.fixMeanBound_theta1
#print axioms Sarkozy.ThetaOne.envMeanBoundL_theta1
#print axioms Sarkozy.ThetaOne.envMeanBoundR_theta1
#print axioms Sarkozy.ThetaOne.hfold_satisfiable
#print axioms Sarkozy.TargetLedger.targetLedger_theta_lt
#print axioms Sarkozy.ThetaOne.FixMeansTheta1.toFixMeansInputs
#print axioms Sarkozy.ThetaOne.EnvMeansTheta1.toEnvMeansInputs
#print axioms Sarkozy.ThetaOne.SharpPartsBase.toSharpParts2
#print axioms Sarkozy.ThetaOne.paperAtomMap_paperBlockOf_surjective
#print axioms Sarkozy.MainCombined2.main_goal_theta1k
#print axioms Sarkozy.SharpBase.main_goal_theta1_sh2
#print axioms Sarkozy.MeanCredit.completion_le
#print axioms Sarkozy.MeanCredit.upperFree_room
#print axioms Sarkozy.MeanCredit.jointBound_ofCM
#print axioms Sarkozy.NormBoundsPaper3.main_goal_nb3
#print axioms Sarkozy.NormBoundsPaper3.match_skew_paper
#print axioms Sarkozy.SharpBase2.main_goal_theta1_sh3
#print axioms Sarkozy.SignedDecomp.main_goal_theta1k_sd2
#print axioms Sarkozy.SignedDecomp.comp80_paper
#print axioms Sarkozy.MeanCredit2.meanValue_ge
#print axioms Sarkozy.MeanCredit2.jointBound_paper
#print axioms Sarkozy.MeanCredit2.split_hypotheses_satisfiable
#print axioms Sarkozy.NormBoundsPaper4.eOrthPaperInput
#print axioms Sarkozy.NormBoundsPaper4.main_goal_nb4
#print axioms Sarkozy.Companion.main_goal_companion
#print axioms Sarkozy.Companion.numerics_satisfiable
#print axioms Sarkozy.CompSharp.comp34_paper
#print axioms Sarkozy.CompSharp.hNr4_of_symSkew38
#print axioms Sarkozy.Rebase.main_goal_rebased
#print axioms Sarkozy.Rebase.targetSaving_eq_epsGoal
#print axioms Sarkozy.Rebase.SignedDecompNew.toSD
#print axioms Sarkozy.Rebase.gate73_80_check
#print axioms Sarkozy.Rebase.foldSides38_paperKappa
#print axioms Sarkozy.Rebase.foldSides34_paperKappa
#print axioms Sarkozy.TargetLedger.targetLedger_theta_lt
#print axioms Sarkozy.SignedDecomp.gate73_check
#print axioms Sarkozy.Rebase.hNr4_paperKappa
#print axioms Sarkozy.Rebase.paperKappa_symSkewSides
#print axioms Sarkozy.FoldSymSkew.hNr4_rb
#print axioms Sarkozy.FoldSymSkew.rb_check
#print axioms Sarkozy.FoldSymSkew.paper_table_fails
#print axioms Sarkozy.SignedDecompCrude.signedDecompInputs_proved
#print axioms Sarkozy.SignedDecompCrude.hNr4_proved
#print axioms Sarkozy.SignedDecompCrude.gate21_check
#print axioms Sarkozy.CompanionND.main_goal_rebased_nd
#print axioms Sarkozy.CompanionND.main_goal_rebased_of_nd
#print axioms Sarkozy.ClassSlack.main_goal_rebased_cg
#print axioms Sarkozy.ClassSlack.noMean_room
#print axioms Sarkozy.SharpSums.SharpSumInputsL.toSharpBaseInputsPT
#print axioms Sarkozy.ClassSlack.main_goal_rebased_cg0
#print axioms Sarkozy.SharpSums.main_goal_rebased_sum
#print axioms Sarkozy.LargeSums.largeSumPTFixL_proved
#print axioms Sarkozy.LargeSums.largeSumPTFixR_proved
#print axioms Sarkozy.LargeSums.largeSumPTEnvL_proved
#print axioms Sarkozy.LargeSums.largeSumPTEnvR_proved
#print axioms Sarkozy.LargeSums.main_goal_rebased_lp
#print axioms Sarkozy.SharpFirst.sfFold_proved
#print axioms Sarkozy.SharpFirst.sfRem_proved
#print axioms Sarkozy.SharpFirst.main_goal_rebased_sr
#print axioms Sarkozy.E1Closure.e1Large_proved
#print axioms Sarkozy.E1Closure.e1SubSmall_proved
#print axioms Sarkozy.E1Closure.e1CoupSmall_proved
#print axioms Sarkozy.E1Closure.main_goal_rebased_ec
#print axioms Sarkozy.BlockInputs.main_goal_rebased_ba
#print axioms Sarkozy.BlockInputs.main_goal_rebased_baec
#print axioms Sarkozy.LetterTotals.symTotal_le_front
#print axioms Sarkozy.LetterTotals.skewTotal_le_front
#print axioms Sarkozy.LetterTotals.SForm_add_AForm
#print axioms Sarkozy.LetterTotals.SForm_le_ledgers
#print axioms Sarkozy.LetterTotals.main_goal_rebased_hx
#print axioms Sarkozy.BlockRows.middleBlockRows_of_cert
#print axioms Sarkozy.BlockRows.upperBandRowsV2_of_cert
#print axioms Sarkozy.BlockRows.main_goal_rebased_rw
#print axioms Sarkozy.LetterTotals2.totalsLe_front
#print axioms Sarkozy.LetterTotals2.series_mono
#print axioms Sarkozy.LetterTotals2.hC_of_le
#print axioms Sarkozy.LetterTotals2.CompanionObligationsHX2.toRW
#print axioms Sarkozy.LetterTotals2.CompanionObligationsHX2.ofRW
#print axioms Sarkozy.LetterTotals2.CompanionObligationsHX2.ofRW_toRW
#print axioms Sarkozy.LetterTotals2.CompanionObligationsHX2.nonempty_iff
#print axioms Sarkozy.LetterTotals2.main_goal_rebased_hx2
#print axioms Sarkozy.OpsCore.main_goal_rebased_ops
#print axioms Sarkozy.OpsCore.CompanionObligationsOps.toEC
#print axioms Sarkozy.OpsCore.CompanionObligationsOps.ofEC
#print axioms Sarkozy.OpsCore.OpsInputs.toOps
#print axioms Sarkozy.OpsCore.star_tensor_error
#print axioms Sarkozy.OpsCore.fold_leadOK_atom
#print axioms Sarkozy.OpsCore.A3_proj12_paper
#print axioms Sarkozy.OpsCore.hbg_hρ_of_phiBudgetClass
#print axioms Sarkozy.OpsFeature.actual_feature_frame_proved
#print axioms Sarkozy.OpsFeature.actual_hcor_proved
#print axioms Sarkozy.OpsFeature.edge03_block_proved
#print axioms Sarkozy.OpsFeature.matching_frame_actual_Q3
#print axioms Sarkozy.OpsFeature.hdom_of_units
#print axioms Sarkozy.OpsFeature.hUa_fold_block
#print axioms Sarkozy.OpsFeature.chart_lead
#print axioms Sarkozy.OpsFeature.hspec_two
#print axioms Sarkozy.OpsSteps.paperDegreeOpsT
#print axioms Sarkozy.OpsSteps.step4_fine
#print axioms Sarkozy.OpsSteps.step4_uniform
#print axioms Sarkozy.OpsSteps.envelopeBoundNonneg_front
#print axioms Sarkozy.OpsSteps.hE1_of_envelope
#print axioms Sarkozy.OpsSteps.rCan_class_sum
#print axioms Sarkozy.OpsSteps.block_sym_norm_le
#print axioms Sarkozy.OpsSteps.hcapH_of_caps
#print axioms Sarkozy.OpsVariance.varConjunct_noCredit_front
#print axioms Sarkozy.OpsVariance.varStepsAt_credit
#print axioms Sarkozy.OpsVariance.recordsZeroMarginal_front
#print axioms Sarkozy.OpsVariance.hres_fold_front
#print axioms Sarkozy.OpsVariance.hres_aligned_front
#print axioms Sarkozy.OpsVariance.foldCen_global_front
#print axioms Sarkozy.OpsVariance.hRes_variance
#print axioms Sarkozy.SignedComponents.ofFoldM_N_eq
#print axioms Sarkozy.SignedComponents.ofFoldM_N_le
#print axioms Sarkozy.SignedComponents.ofFoldM_price_sum_le_of
#print axioms Sarkozy.MainFinalF1c.specNormAt_of_bounds
#print axioms Sarkozy.MainFinalF1c.specPrices_at
#print axioms Sarkozy.MainFinalF1c.ComparisonPartsTC.toK1_prices
#print axioms Sarkozy.CompanionND.CompanionFrontND.prices_eq_bounds
#print axioms Sarkozy.OpsVariance.matchPrice_atomM
#print axioms Sarkozy.BudgetLinks.UpperSlack.zero
#print axioms Sarkozy.BudgetLinks.UpperSlack.selUpper
#print axioms Sarkozy.BudgetLinks.exists_slack
#print axioms Sarkozy.BudgetLinks.ops_transfer
#print axioms Sarkozy.BudgetLinks.CompanionObligationsBL.toEC
#print axioms Sarkozy.BudgetLinks.CompanionObligationsBL.ofEC
#print axioms Sarkozy.BudgetLinks.CompanionObligationsBL.nonempty_iff
#print axioms Sarkozy.BudgetLinks.main_goal_rebased_bl
