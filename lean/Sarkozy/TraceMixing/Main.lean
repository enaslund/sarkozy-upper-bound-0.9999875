module

public import Sarkozy.TraceMixing.R4
public import Sarkozy.TraceMixing.Vertex
public import Sarkozy.TraceMixing.Paley
public import Sarkozy.TraceMixing.TailMixing
public import Sarkozy.TraceMixing.VertexTuple
public import Sarkozy.TraceMixing.PaleyFeatures3
public import Sarkozy.TraceMixing.PaleyPerturb
public import Sarkozy.TraceMixing.DisjointTriple
public import Sarkozy.TraceMixing.DisjointTripleOrdered
public import Sarkozy.TraceMixing.ProductionFromIndex

/-!
# The trace lemma for conditional mixing (WP-S, third to fifth packages): entry point

`lem:trace-mixing` of `paper/sections/12_labellings.tex` and the mixing hypothesis (R4) for
graph laws, in the `def:mixing` formalization `Sarkozy.Mixing.IsGammaMixing`.

* (a) one slot — `trace_mixing_slot` (the paper's hypothesis `e_d(p, n-1) ≤ w < 1`),
  `trace_mixing_slot_graded`, `isMixing_graphLaw_slot`; ingredients `twin_bound` (the trace
  step without characters), `gramSlot_translate`, `gramSlot_dilate`, `trace_gramSlot_le`,
  `srcWeight_graphSlot` (uniform one-slot marginals). Any finite field of odd characteristic.
* (b) a pair, trace form — `trace_mixing_pair`, `isMixing_graphLaw_pair`; the pair law is
  `Unif(Ω)` (`srcWeight_pairJoint`); `phiPair_pairJoint` and `sum_sq_condMatrix_pairJoint`
  identify the two terms with `φ_y = (p-1)/2 · c_y/|Φ| - 1` and `E[1/|Φ|]`. Abstract form
  `pair_trace_bound`, nonzero frequencies `fourier_step` (characters of `𝔽_p`).
* (c) a pair, explicit form — `trace_mixing_explicit` (bound `explicitBound`), from the counts
  `card_pairAdm_ge_main`, `diffCount_le_main`, `diffCount_generic_main`,
  `card_nongeneric_le` and `phi_row_bound`.
* (d) seventy-two vertices of degree at most twenty — `trace_mixing_slot_72` (`2^22/p`) and
  `trace_mixing_pair_72` (`2^92/p`), for `p ≥ 2^512`.
* (R4) — `isGammaMixing_graphLaw_slot`, `isGammaMixing_graphLaw_pair`, `graphLaw_R4`
  (`γ = 255/1024`, `p ≥ 2^512`, assuming `Sarkozy.Target.Weil`).
* `lem:graphs:vertex`(a) — `graphLaw_weight_affine`, `srcWeight_graphSlot`; (b) —
  `condMatrix_graphSlot`, `card_slotAdmissible_ge`, `condDensity_graphSlot_le`,
  `condMatrix_slot_of_density`.
* `lem:paley-triple`(a)–(c) — `card_sign_pair`, `paley_tournament`, `card_out`, `card_in`,
  `card_common_out`, `card_common_in`, `card_path`, `sum_chi_mul_chi`, `paleyOp_const`,
  `paleyOp_adjoint`, `norm_paleyOp`, `paleyOp_mean`, `paleyOp_sq`; (d) — `card_fibre0`,
  `condExp0_x2`, `condExp0_x1`, `hfSum_x0`, `hfSum_x1`, `hfSum_x2`, `hfSum_shift`, `hfSum_x0_x2`,
  `hfSum_x0_x1`, `hfSum_x1_x2`, `hfSum_x2_x0`, `hfSum_x1_x0`, `hfSum_x2_x1`, `sum_opE2_sq`,
  `sum_opE1_sq`, `paleyRho1_le`, `paleyRho'_le`, `gram_bound`; (e) — `hfSum_A1`,
  `hfSum_A2`, `featA3_const`, `hfSum_featA3`, `hfSum_A1_A1`, `hfSum_A2_A2`, `hfSum_A1_A2`,
  `hfSum_V0_A1`, `hfSum_V0_A2`, `hfSum_V0_A3`, `hfSum_V0_Axi`, `hfSum_V1_A3`, `hfSum_V2_A3`,
  `hfSum_A1_A3`, `hfSum_A2_A3`, `hfSum_A3_A3`, `A3_coef_le`, `features_norm_bound`;
  (f) — `inner_perturb`, `norm_perturb`.
* `lem:record:tail-mixing`(a), (b) and (R4) for the tail laws as mixtures with the root —
  `tail_slot_bound`, `tail_pair_bound`, `srcWeight_pairJoint_tail`, `tail_mixing_S`, `tail_R4`.
* `sec:frontier:empty-triple-negative` — (a), first assertions: `card_disjTriple`,
  `tripleOp_one`, `tripleOp_selfAdjoint`, `tripleOp_eq_zero_of_symm`, `disjOp_one`,
  `disjOp_fixed` (eigenvalue `1` ↔ constants), `disjOp_eigen` (`λ₁ = -3/(n-3)`),
  `disjForm_eigen2` (`λ₂`), `disjForm_eigen3` (`λ₃`),
  `tripleOp_eq_disjOp` (`T = 6⁻¹ T̄` through the unordered triple); (b):
  `tripleOp_le` (`T ⪯ I`), `tripleOp_ge` (`T ⪰ -3/(n-3) I` on `L²(𝒯)`), `tripleOp_abs_le`
  (`‖T - J‖ ≤ 3/(n-3)`), `disjForm_ge`, `disjOp_ge`, `disjOp_abs_le`, `disjOp_attained` —
  by an elementary Cauchy–Schwarz argument replacing the harmonic decomposition.
* `prop:density:production` from the coupled index law (fifth package) —
  `density_structured_theta_of_pairs`, `pairs_of_twoOccurrence`, `expect_prod_rpow_le_prod`,
  `density_structured_theta_few`, `production_pairs_of_index`, `density_structured_theta_index`,
  `label_bound_of_pair_indep`, `label_bound_fails`, `density_structured_theta_two_occ`.
* `lem:graphs:vertex`(c)–(e) — `upperProd_le_RY`, `marginalJ_support`, `sum_marginalJ`,
  `marginalJ_density`, `marginalJ_density_bounds`, `marginal_of_density_ratio`,
  `marginal_delete`, `lowerProd_append`, `tupleProd_le_lowerProd`, `tuple_support`,
  `tuple_density`, `tupleProd_ge`, `tuple_density_coarse`.

Not imported here: `Sarkozy.TraceMixing.InfluenceBridge` (`deg_ofLabellings`, the degree of
WP-P's `Influence.ofLabellings G` is `degree G`), which depends on `Sarkozy.Influence`.
-/
