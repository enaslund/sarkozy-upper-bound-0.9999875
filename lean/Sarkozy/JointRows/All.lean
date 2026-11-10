module

public import Sarkozy.JointRows.Weighted
public import Sarkozy.JointRows.RowsB
public import Sarkozy.JointRows.RowsC
public import Sarkozy.JointRows.Discharge
public import Sarkozy.JointRows.RowsAPrelim
public import Sarkozy.JointRows.RowsA
public import Sarkozy.JointRows.ScaledKernel
public import Sarkozy.JointRows.MarginalRatio
public import Sarkozy.JointRows.LawEquivChart
public import Sarkozy.JointRows.UniformIndicator
public import Sarkozy.JointRows.RowsAChain
public import Sarkozy.JointRows.RowsAGate
public import Sarkozy.JointRows.Potential
public import Sarkozy.JointRows.RowsASanity
public import Sarkozy.JointRows.DischargeSanity
public import Sarkozy.JointRows.Sector
public import Sarkozy.JointRows.SectorGate
public import Sarkozy.JointRows.SectorSanity
public import Sarkozy.JointRows.Restrict
public import Sarkozy.JointRows.RestrictPotential
public import Sarkozy.JointRows.Eig
public import Sarkozy.JointRows.EigSanity
public import Sarkozy.JointRows.PaleyGauss
public import Sarkozy.JointRows.PaleyCx
public import Sarkozy.JointRows.PotentialPaley
public import Sarkozy.JointRows.StarNorms
public import Sarkozy.JointRows.StarAssembly
public import Sarkozy.JointRows.StarExpansion
public import Sarkozy.JointRows.StarFeatures
public import Sarkozy.JointRows.StarHoeffding
public import Sarkozy.JointRows.StarSanity
public import Sarkozy.JointRows.StarOps
public import Sarkozy.JointRows.StarOpsBounds
public import Sarkozy.JointRows.StarPure
public import Sarkozy.JointRows.StarContract
public import Sarkozy.JointRows.RawStarFrame
public import Sarkozy.JointRows.StarJoint
public import Sarkozy.JointRows.StarJointRows
public import Sarkozy.JointRows.StarRowsA
public import Sarkozy.JointRows.StarBridge
public import Sarkozy.JointRows.StarFull
public import Sarkozy.JointRows.CollBridge
public import Sarkozy.JointRows.CollRows
public import Sarkozy.JointRows.CollExpansion
public import Sarkozy.JointRows.CollNonstar
public import Sarkozy.JointRows.CollRowsFull
public import Sarkozy.JointRows.CollLambda
public import Sarkozy.JointRows.CollSanity
public import Sarkozy.JointRows.StarTailBound
public import Sarkozy.JointRows.StarGramCount
public import Sarkozy.JointRows.PinnedCoordinateMeans
public import Sarkozy.JointRows.PinnedTailScalars
public import Sarkozy.JointRows.PinnedRemainder
public import Sarkozy.JointRows.StarFullTail
public import Sarkozy.JointRows.AllowedProduct
public import Sarkozy.JointRows.LawEquiv
public import Sarkozy.JointRows.ChartBound
public import Sarkozy.JointRows.PinnedChartScalars

/-!
# Joint fold and matching rows (`lem:joint-rows`, `lem:joint-potential`), umbrella

Source: `paper/sections/16_extraction.tex`, `lem:joint-rows` (a)–(c) and `lem:joint-potential`.

* `Weighted` — weighted kernel matrices, per-prime positive semidefinite blocks, and block
  tensorization (`psd_tprod_blocks`, `lem:record:block-gram`).
* `RowsB` — `lem:joint-rows`(b) (`jointRows_b`); it discharges `Blocks.JointRowsB`
  (`jointRowsB_holds`).
* `RowsC` — `lem:joint-rows`(c) (`jointRows_c`); it discharges `Blocks.JointRowsC`
  (`jointRowsC_holds`).
* `Discharge` — `cor:joint-completion-blocks` and its composition with `lem:five-type`(f) without
  the `lem:joint-rows` hypotheses (`joint_completion_blocks'`, `blockJointData'`,
  `joint_blocks_rp'`).
* `RowsAPrelim`, `RowsA`, `RowsAChain`, `RowsAGate` — `lem:joint-rows`(a)
  (`RowsA.joint_rows_a_gate`, `RowsA.joint_rows_a`), with the cited inputs as hypotheses.
* `Potential` — `lem:joint-potential` (`Potential.joint_potential`).
* `Sector`, `SectorGate` — the `Φ̂`-sector reduction of `𝕄` (the hypothesis `hsector` of (a)),
  proved without complexification (`Sector.qMat_lower`, `Sector.hsector_holds`), and (a) from
  the gate with it discharged (`Sector.joint_rows_a_sector`).
* `Restrict` — `lem:restriction`(a) gives `hrestr` (`Restrict.hrestr_holds`); (a) for pinned
  rows with `hrestr` and `hsector` discharged (`Restrict.joint_rows_a_pinned`).
* `RestrictPotential` — `lem:joint-potential` for pinned rows with `hrestr` discharged
  (`Restrict.joint_potential_pinned`).
* `Eig` — the eigenspace bound `heig` of `lem:joint-potential` (`Eig.heig_holds`), and the pure
  part with it discharged (`Eig.pure_part_potential_eig`).
* `PaleyGauss` — the normalized Paley operator `Φ̂` for `p ≡ 3 (mod 4)` satisfies `Eig.PaleyLike`
  (`PaleyGauss.paley_paleyLike`, from Mathlib's `J(χ, χ) = -χ(-1)`), and `heig` for it
  (`PaleyGauss.heig_paley`).
* `PaleyCx` — `ℋ = L²_0(𝔽_p)` with `Φ̂` is a `Sector.CxStruct` (`PaleyGauss.cxStruct_paley`), and
  `Restrict.joint_rows_a_paley`: (a) for pinned rows with `hrestr`, `hsector`, `hJ` discharged.
* `PotentialPaley` — `Restrict.joint_potential_paley`: `lem:joint-potential` for pinned rows with
  `hrestr` and the pure-part bound discharged (the latter via `heig` at the actual `Φ̂`).
* `StarNorms`, `StarAssembly`, `StarExpansion`, `StarFeatures`, `StarHoeffding` —
  `prop:conditional-star`(b),(c): the norm bookkeeping of `T_mean` (`Star.mean_block_bound`,
  `Star.norm_matrix_two`), the contractions (`Star.hoeffding_orthogonal`,
  `Star.contraction_of_orthogonal`, `Star.prod_gamma_le`), the star expansions, the decay, the
  conclusion `Star.star_norm_bound`, and `Star.joint_star_inputs` (the hypotheses `hdec`, `hV`,
  `hmean` of (a) from per-row decompositions).
* `StarOps`, `StarOpsBounds`, `StarPure`, `StarContract` — `prop:conditional-star`(b) on the
  actual χ-kernels: the feature maps `W_S`, `U_i` and their adjoints, the Gram identity
  (`StarOps.wOp_gram`), `‖W_S‖ ≤ √κ r` (`StarOps.wOp_norm_le`), `‖W_S 𝟙_Ω‖² ≤ r² + ν_χ^{|S|}`
  (`StarOps.wOp_decay`), `T_pure = κ r 𝓕_X M(Φ̂) 𝓕_Y^*` (`StarOps.pure_block_identity`), and the
  contraction `‖𝓕_X^* f‖ ≤ ‖f‖` (`StarOps.featStar_norm_le`).
* `StarJoint`, `StarJointRows`, `StarRowsA` — the joint assembly of `lem:joint-rows`(a): the
  grouped `𝒵`, `𝒜` and features (`StarOps.qMat_jointFeat`), `K_⋆ = K_pure + K_mean`
  (`StarOps.starKernel_eq`), `hdec` (`StarOps.qTc_star_decomp`), `hV` (`StarOps.norm_starFeat_le`),
  and `Restrict.joint_rows_a_star`: (a) for pinned rows with the actual star kernels, `hdec`/`hV`
  discharged.
* `StarBridge`, `StarFull` — fork C1-P's star kernel equals the explicit one
  (`StarOps.starKer_eq_starKernel`), and `Coll.joint_rows_a_full`: (a) for the concrete pinned
  rows, combining C1-P's discharges with `hdec`/`hV`.
* `CollBridge`, `CollRows`, `CollExpansion`, `CollNonstar`, `CollRowsFull`, `CollLambda`
  (fork C1-P) — `lem:spec:expansion` with `prop:pinned-collision` and `prop:pinned-extraction`
  for the concrete pinned rows: `Coll.formBound_of_opBound`, `Coll.formBound_pinKer`,
  `Coll.rawKer_expansion`, `Coll.formBound_nsKer`, `Coll.pinLambda`, and the restatements
  `Coll.joint_rows_a_coll`, `Coll.joint_rows_a_pinrow` (and the `joint_potential` ones).
* `RowsASanity`, `DischargeSanity`, `SectorSanity`, `EigSanity`, `StarSanity`, `CollSanity` — toy
  instances
  (`EigSanity`: the normalized Paley operator at `p = 3` satisfies `PaleyLike`).
-/
