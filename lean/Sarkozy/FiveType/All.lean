module

public import Sarkozy.FiveType.Datum
public import Sarkozy.FiveType.CutForms
public import Sarkozy.FiveType.Invariance
public import Sarkozy.FiveType.Rows
public import Sarkozy.FiveType.RowJoint
public import Sarkozy.FiveType.Criteria
public import Sarkozy.FiveType.Graded
public import Sarkozy.FiveType.FoldDataRemark
public import Sarkozy.FiveType.PolarizationOrders
public import Sarkozy.FiveType.PolarizationTensor
public import Sarkozy.FiveType.PolarizationSupport
public import Sarkozy.FiveType.ReflectionTable
public import Sarkozy.FiveType.JointBlocks
public import Sarkozy.FiveType.BlocksRP
public import Sarkozy.FiveType.TwoCoordinate
public import Sarkozy.FiveType.ReservedCut
public import Sarkozy.FiveType.ReservedCutOne
public import Sarkozy.FiveType.Sanity
public import Sarkozy.FiveType.JointBlocksSanity
public import Sarkozy.FiveType.TwoCoordinateSanity

/-!
# The five-type completion (`subsec:five-type`), umbrella

Source: `paper/sections/17_completion_repair.tex`, `def:five-type-datum`,
`def:two-coordinate-five-type`, `lem:five-type` (a)–(f), `cor:joint-completion-blocks`.

* `Datum` — `def:five-type-datum`; components, `π_t`, `𝒬_a`; `FoldData`, `JointData`.
* `CutForms`, `Invariance` — `lem:five-type`(a): the cut forms (`Datum.cut_forms`), the
  `𝒢₆`-invariance of `𝒬_a` (`Datum.Q_inv6`), chamber transport (`rpAll_of_inv6`), and the
  inner-product bound (`inner_lower_of_opNorm`).
* `Rows`, `RowJoint` — the row inequalities `Φ_b ≥ 0` of (b), (c), (f); the form version of
  `cor:joint-row-split` (`joint_block_split`).
* `Criteria` — (b) `Datum.full_norm_criterion`/`full_norm_rp`, (c) `Datum.schur_criterion`/
  `schur_rp`, (f) `Datum.joint_schur_criterion`/`joint_schur_rp`, graded forms.
* `FoldDataRemark` — `rem:five-type-fold-data`: fold data from marginal densities and a
  maximal-correlation bound (`foldData_of_marginals`).
* `Graded` — end-to-end graded versions `Datum.full_norm_rp_graded`, `schur_rp_graded`,
  `joint_rp_graded`.
* `PolarizationOrders` — `lem:tr:polarization`: `eq:polarization` (form version), (a) and the
  two orders of (b) (`Datum.polarization_a`, `Datum.polarization_b`, `polarization_b_diag`).
* `PolarizationTensor` — `lem:tr:polarization`(c) (both claims) and the last claim of (d)
  (`polarization_c_first`, `polarization_c_second`, `polarization_d_blocks`).
* `PolarizationSupport` — the corner-block form of (b): `A`, `D`, `K` supported on `𝒰×𝒰`,
  `𝒱×𝒱`, `𝒰×𝒱` when `ν^b({b}) = 0` (`Datum.A_support`, `D_support`, `K_support`), `Kᵀ` for `F_2`.
* `ReflectionTable` — `tab:reflection`, row by row.
* `TwoCoordinate` — `def:two-coordinate-five-type` and (d) (`TwoCoord.two_coordinate_rp`).
* `ReservedCut`, `ReservedCutOne` — (e), two coordinates (`Reserved.reserved_rp_two`) and one
  coordinate (`ReservedOne.reserved_rp_one`).
* `JointBlocks` — `cor:joint-completion-blocks` (`Blocks.joint_completion_blocks`,
  `Blocks.joint_completion_graded`), with `lem:joint-rows` (b), (c) as hypotheses.
* `BlocksRP` — the corollary composed with (f): block rows at every `b ∈ supp ν` and the
  completion inequalities give `RPAll` (`Datum.joint_blocks_rp`).
* `Sanity`, `JointBlocksSanity`, `TwoCoordinateSanity` — toy instances (non-vacuity).
-/
