module

public import Sarkozy.IndexSupport.CoupledIndex
public import Sarkozy.IndexSupport.InclusionLaw
public import Sarkozy.IndexSupport.GeneralIndex
public import Sarkozy.IndexSupport.Reindex
public import Sarkozy.IndexSupport.CRT
public import Sarkozy.IndexSupport.Examples

/-!
# Index-support package (WP-S): entry point

Imports the whole package. Main results:

* `Sarkozy.IndexSupport.index_support_lemma` — `lem:record:common-mean` (Index-support
  lemma), filtration form; `common_mean`, `form_le_energies`, `mean_le_energy` — its
  abstract sector-system form (any revelation law with `δ_s ≤ Pr(s retained)`).
* `Sarkozy.IndexSupport.one_cut_coupling` — `lem:hyb:coupling` (One-cut coupling
  inequality), whole-coordinate case.
* `Sarkozy.IndexSupport.signedIndexOp_sectorOperator` — `cor:index-support-frame`(i).
* `Sarkozy.IndexSupport.signed_index_bounds`, `cut_signed_index_bounds`,
  `cut_signed_index_bounds_of_product` — `cor:index-support-frame`(iii) and
  `eq:cp:mean-step`; `vmean_productHalf_of_mean`, `act_productHalf` — the
  construction-independent part of (ii).
* `Sarkozy.IndexSupport.piKron_two_sub_expansion` — the operator expansion behind
  `eq:record:expansion`.
* `Chain.residues`, `Chain.whole`, `Chain.ofLabels`, `residue_conv_hypotheses`,
  `shift_rangeBound`, `depthReveal_whole`, `depthReveal_ofLabels` — the paper's coordinate
  instances; `coupled_index_sectorOperator` — `cor:index-support-frame`(i) for the coupled
  index of `def:hyb:coupled` in product coordinates.
* `expect_prod_eq`, `prod_le_expect_prod`, `containProb_independent` — the remark on
  inclusion laws after `lem:record:common-mean`.
* `signedOp_sectorOperator`, `signedOp_bounds` — `cor:index-support-frame`(i),(iii) for
  arbitrary per-query index spaces with abstract sector systems and revelations.
* `coupled_index_mean_step` — `eq:cp:mean-step` for the coupled index in product
  coordinates.
* `SectorSystem.reindex`, `SectorOperator.reindex`, `Revelation.reindex`,
  `pairing_comp_equiv`, `vmean_comp_equiv`, `Revelation.energy_reindex` — transport along a
  relabelling of the index space (e.g. the Chinese remainder isomorphism).
* `crtEquiv`, `unsplitTransition_eq`, `unsplit_sectorOperator`, `unsplit_bounds`,
  `unsplitRevelation_reveal_mod` (`Z^𝒥 = E[Z | b, s mod D_𝒥]`), `unsplit_cut_mean_step` — the same results on the paper's
  unsplit index `ℤ/Kℤ × ℤ/M_0ℤ` (`def:hyb:coupled`(a),(c)).
* `Examples.lean` — non-vacuity `example`s for the main theorems.
-/
