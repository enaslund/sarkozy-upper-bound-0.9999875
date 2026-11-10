module

public import Sarkozy.ExtractionK.Grouped
public import Sarkozy.ExtractionK.KernelBridge
public import Sarkozy.ExtractionK.GroupedNorm

@[expose] public section

/-!
# Leaf bound and nonstar coefficients (`cor:extraction-leaf`, `eq:leaf-factors`)

`paper/sections/16_extraction.tex`, the definitions `eq:leaf-factors` and `cor:extraction-leaf`
(a), with the monotone-factor condition `eq:monotone-signature`.

## Definitions (`eq:leaf-factors`)

For the half graph `G⁺` (an oriented graph `G` on `U`) and cross signs `ς` with symmetric support:
`leafR ς i = r_i = |N(i)|`, `leafD G ς i = d_i = d⁰_i + r_i`, `leafDelta G ς = Δ = max_i d_i`,
`leafH0 G i s = h⁰_i(s) = max(0, s - d⁰_i)` (truncated subtraction), the weights
`weightM G ς i j = w^m_{ij} = 2^{c^U(i,j)}` and `weightRho G ς i j = w^ρ_{ij} = 2^{mg(j,i) + c^U(j,i)}`,
`leafSigma ς w i h = σ_i`, the sum of the `h` smallest weights `w_{ij}` over `j ∈ N(i)` (the
minimum of `∑_{j ∈ H} w_{ij}` over the sets `H ⊆ N(i)` with `|H| = h`; `0` if there is none),
`leafS G ς w s = max_{i : d_i ≥ s} (∑_{j ∈ U⁺} w_{ij} - σ_i(h⁰_i(s))/2)` (`0` if no vertex has
`d_i ≥ s`; for `s ≤ Δ` the set is nonempty), so `S_m = leafS G ς (weightM G ς)`,
`S_ρ = leafS G ς (weightRho G ς)`, and
`leafFm = 𝖿_m(s) = (1 + e_s(q, n) + r² 2^s S_m(s))/(1 - ê)`,
`leafFrho = 𝖿_ρ(s) = (1 + e_s(q, 2n) + r² 2^s S_ρ(s))/(1 - ê)`.

## Results

* `intF_le_leafFm`, `coverRowF_le_leafFrho`: the comparisons of the proof of (a),
  `F_u ≤ 𝖿_m(s_u)` for an integrated vertex and `F_b ≤ 𝖿_ρ(s_b)` for a cover vertex.
* `recordFactor_le_leafProd`: `∏_v F_v ≤ ∏_{u ∈ U_x ∪ U_z} 𝖿_m(s_u) ∏_{b ∈ C_x ∪ C_z} 𝖿_ρ(s_b)`.
* `extraction_leaf`: **`cor:extraction-leaf`(a)** with a kernel constant `c_ker` (the bound
  `c_ker r^k 2^{ex/2} R_full² (1 - ê)^{-k} ∏ 𝖿^{1/2} ‖f‖ ‖h‖`), from `grouped_extraction`;
  `extraction_leaf_twoCycles` (`F = 𝔽_p`, `c_ker = 2^β`, `ex* = ex + 2β`, with
  `cor:dl:normalized`(a) as the hypothesis `FourCycleBound p`) and `extraction_leaf_acyclic`
  (`c_ker = 1`) are the statement of the paper.
* `leafFm_mono`, `leafFrho_mono`, `extraction_leaf_stored`: under `eq:monotone-signature` the
  factor functions are nondecreasing on `{0, …, Δ}`, and the bound holds with stored numbers
  `s'_v ∈ [s_v, Δ]`.

* `extraction_leaf_twoCycles_norm`: (a) in operator-norm form, `‖T_𝒞 h‖_μ ≤ B ‖h‖_μ` (from
  `grouped_extraction_norm`).
* `extraction_leaf_partition`, `extraction_leaf_partition_grouped`: **`cor:extraction-leaf`(b)**.
  For an exact partition `𝔓` of the nonstar subsets (`IsExactPartition … (nonstars Ex)`) into
  classes with fixed records (`LeafRecordData`, `LeafRecordData.Valid`), if
  `ê(Q) = e_{Δ⁺}(Q, n) < 1` at a real `Q > 0`, then for every prime `p ≥ Q`
  `|⟨f, T_ns h⟩_μ| ≤ ∑_k C_k(Q) p^{-k/2} ‖f‖_μ ‖h‖_μ`, `C_k(Q)` the sum of the class coefficients
  `leafCoef` of witness size `k` at `r = Q^{-1/2}`. The monotonicity in `q` that the paper takes
  from `lem:majorant` is proved directly (`leafCoef_anti`: every count error, `r²`, `ê` and
  `R_full` decrease with `q`). `extraction_leaf_partition_stored`: the same with stored numbers
  (`LeafStored`, `leafCoefStored`) under `eq:monotone-signature`.

## Hypotheses

Weil's theorem `WeilBound` (literature input); in the `𝔽_p` statements the four-cycle bound
`FourCycleBound p` (`cor:dl:normalized`(a)), as in `lem:matching:kernel`(b). Of (S1) only
`e_{d⁰_i}(q, n) ≤ ê < 1` (in (b): `e_{Δ⁺}(Q, n) < 1`) is used.
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

section LeafDefs

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- `r_i = |N(i)|`, the cross degree. -/
def leafR (ς : U → U → ℤ) (i : U) : ℕ := (rowsN ς i).card

/-- `d_i = d⁰_i + r_i`. -/
def leafD (G : OrientedGraph U) (ς : U → U → ℤ) (i : U) : ℕ := rowsDeg0 G i + leafR ς i

/-- `Δ = max_i d_i`. -/
def leafDelta (G : OrientedGraph U) (ς : U → U → ℤ) : ℕ := univ.sup (leafD G ς)

/-- `h⁰_i(s) = max(0, s - d⁰_i)`. -/
def leafH0 (G : OrientedGraph U) (i : U) (s : ℕ) : ℕ := s - rowsDeg0 G i

/-- `w^m_{ij} = 2^{c^U(i, j)}` (`eq:leaf-factors`). -/
noncomputable def weightM (G : OrientedGraph U) (ς : U → U → ℤ) (i j : U) : ℝ :=
  2 ^ rowsCU G ς i j

/-- `w^ρ_{ij} = 2^{mg(j, i) + c^U(j, i)}` (`eq:leaf-factors`). -/
noncomputable def weightRho (G : OrientedGraph U) (ς : U → U → ℤ) (i j : U) : ℝ :=
  2 ^ (rowsMg G ς j i + rowsCU G ς j i)

/-- `σ_i`: the sum of the `h` smallest of the weights `w_{ij}`, `j ∈ N(i)`, i.e. the minimum of
`∑_{j ∈ H} w_{ij}` over the sets `H ⊆ N(i)` with `|H| = h` (`0` if `h > |N(i)|`). -/
noncomputable def leafSigma (ς : U → U → ℤ) (w : U → U → ℝ) (i : U) (h : ℕ) : ℝ :=
  if hne : ((rowsN ς i).powersetCard h).Nonempty then
    ((rowsN ς i).powersetCard h).inf' hne (fun H => ∑ j ∈ H, w i j)
  else 0

/-- `S(s) = max_{i : d_i ≥ s} (∑_{j ∈ U⁺} w_{ij} - σ_i(h⁰_i(s))/2)` (`eq:leaf-factors`; `0` if
no vertex has `d_i ≥ s`). -/
noncomputable def leafS (G : OrientedGraph U) (ς : U → U → ℤ) (w : U → U → ℝ) (s : ℕ) : ℝ :=
  if hne : (univ.filter fun i => s ≤ leafD G ς i).Nonempty then
    (univ.filter fun i => s ≤ leafD G ς i).sup' hne
      (fun i => ∑ j, w i j - leafSigma ς w i (leafH0 G i s) / 2)
  else 0

/-- `𝖿_m(s) = (1 + e_s(q, n) + r² 2^s S_m(s))/(1 - ê)` (`eq:leaf-factors`). -/
noncomputable def leafFm (G : OrientedGraph U) (ς : U → U → ℤ) (q : ℝ) (n : ℕ) (ehat : ℝ)
    (s : ℕ) : ℝ :=
  (1 + coarseError s q n + (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s * leafS G ς (weightM G ς) s) /
    (1 - ehat)

/-- `𝖿_ρ(s) = (1 + e_s(q, 2n) + r² 2^s S_ρ(s))/(1 - ê)` (`eq:leaf-factors`). -/
noncomputable def leafFrho (G : OrientedGraph U) (ς : U → U → ℤ) (q : ℝ) (n : ℕ) (ehat : ℝ)
    (s : ℕ) : ℝ :=
  (1 + coarseError s q (2 * n) + (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s * leafS G ς (weightRho G ς) s) /
    (1 - ehat)

/-- The product of the leaf factors with given numbers `s_v` on the four sets `U_x`, `C_z`, `U_z`,
`C_x` of a record (`U_x = U \ (V ∪ C_x)`, `U_z = U \ (W ∪ C_z)`). -/
noncomputable def leafProdOf (G : OrientedGraph U) (ς : U → U → ℤ) (q : ℝ) (n : ℕ) (ehat : ℝ)
    (V W Cx Cz : Finset U) (sUx sCz sUz sCx : U → ℕ) : ℝ :=
  (∏ u ∈ univ \ (V ∪ Cx), leafFm G ς q n ehat (sUx u)) *
    (∏ b ∈ Cz, leafFrho G ς q n ehat (sCz b)) *
    (∏ u ∈ univ \ (W ∪ Cz), leafFm G ς q n ehat (sUz u)) *
    ∏ b ∈ Cx, leafFrho G ς q n ehat (sCx b)

/-- The product of the leaf factors of a record with its own counts `s_v`
(`cor:extraction-leaf`(a)): `∏_{u ∈ U_x ∪ U_z} 𝖿_m(s_u) ∏_{b ∈ C_x ∪ C_z} 𝖿_ρ(s_b)`, the counts of
`U_z` and `C_x` being those of the transposed record. -/
noncomputable def leafProd (G : OrientedGraph U) (ς : U → U → ℤ) (q : ℝ) (n : ℕ) (ehat : ℝ)
    (Fr : Finset (U × U)) (V W Cx Cz : Finset U) (ordX ordZ : U → ℕ) : ℝ :=
  leafProdOf G ς q n ehat V W Cx Cz (intS G ordX Fr)
    (coverRowS G Cz ordZ (Fr.filter (fun e => e.2 ∈ Cz)))
    (intS G ordZ (Fr.image Prod.swap))
    (coverRowS G Cx ordX ((Fr.image Prod.swap).filter (fun e => e.2 ∈ Cx)))

end LeafDefs

/-! ## The weights and the special sums -/

section Weights

variable {U : Type*} [Fintype U] [DecidableEq U]

theorem weightM_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) (i j : U) :
    0 ≤ weightM G ς i j := by
  unfold weightM
  positivity

theorem weightRho_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) (i j : U) :
    0 ≤ weightRho G ς i j := by
  unfold weightRho
  positivity

omit [DecidableEq U] in
/-- `σ_i(h) ≤ ∑_{j ∈ H} w_{ij}` for every `H ⊆ N(i)` with at least `h` elements (nonnegative
weights). -/
theorem leafSigma_le (ς : U → U → ℤ) (w : U → U → ℝ) (hw : ∀ i j, 0 ≤ w i j) (i : U)
    {h : ℕ} {H : Finset U} (hHN : H ⊆ rowsN ς i) (hcard : h ≤ H.card) :
    leafSigma ς w i h ≤ ∑ j ∈ H, w i j := by
  obtain ⟨H', hH'H, hH'card⟩ := exists_subset_card_eq hcard
  have hmem : H' ∈ (rowsN ς i).powersetCard h := mem_powersetCard.mpr ⟨hH'H.trans hHN, hH'card⟩
  have hne : ((rowsN ς i).powersetCard h).Nonempty := ⟨H', hmem⟩
  unfold leafSigma
  split_ifs
  exact (inf'_le _ hmem).trans (sum_le_sum_of_subset_of_nonneg hH'H fun j _ _ => hw i j)

omit [DecidableEq U] in
theorem leafSigma_le_sum (ς : U → U → ℤ) (w : U → U → ℝ) (hw : ∀ i j, 0 ≤ w i j) (i : U)
    (h : ℕ) : leafSigma ς w i h ≤ ∑ j ∈ rowsN ς i, w i j := by
  unfold leafSigma
  split_ifs with hne
  · obtain ⟨H, hH⟩ := hne
    refine (inf'_le _ hH).trans ?_
    exact sum_le_sum_of_subset_of_nonneg (mem_powersetCard.mp hH).1 fun j _ _ => hw i j
  · exact sum_nonneg fun j _ => hw i j

/-- A vertex with `d_i ≥ s` gives a lower bound for `S(s)`. -/
theorem le_leafS (G : OrientedGraph U) (ς : U → U → ℤ) (w : U → U → ℝ) {s : ℕ} {i : U}
    (hi : s ≤ leafD G ς i) :
    ∑ j, w i j - leafSigma ς w i (leafH0 G i s) / 2 ≤ leafS G ς w s := by
  have hmem : i ∈ univ.filter fun i => s ≤ leafD G ς i := mem_filter.mpr ⟨mem_univ _, hi⟩
  unfold leafS
  split_ifs with h'
  · exact le_sup' (fun i => ∑ j, w i j - leafSigma ς w i (leafH0 G i s) / 2) hmem
  · exact absurd ⟨i, hmem⟩ h'

theorem leafS_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) (w : U → U → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (s : ℕ) : 0 ≤ leafS G ς w s := by
  unfold leafS
  split_ifs with hne
  · obtain ⟨i, hi⟩ := hne
    refine le_trans ?_ (le_sup' (fun i => ∑ j, w i j - leafSigma ς w i (leafH0 G i s) / 2) hi)
    have h1 := leafSigma_le_sum ς w hw i (leafH0 G i s)
    have h2 : ∑ j ∈ rowsN ς i, w i j ≤ ∑ j, w i j :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) fun j _ _ => hw i j
    have h3 : 0 ≤ ∑ j ∈ rowsN ς i, w i j := sum_nonneg fun j _ => hw i j
    linarith
  · exact le_rfl

omit [Fintype U] in
/-- `∑_{b ∈ C} w_b 2^{-[b ∈ H]} = ∑_{b ∈ C} w_b - ½ ∑_{b ∈ H} w_b` for `H ⊆ C`. -/
theorem sum_half_on (C H : Finset U) (hHC : H ⊆ C) (w : U → ℝ) :
    ∑ b ∈ C, w b * (if b ∈ H then (2 : ℝ)⁻¹ else 1) = ∑ b ∈ C, w b - (∑ b ∈ H, w b) / 2 := by
  have h1 : ∀ b ∈ C, w b * (if b ∈ H then (2 : ℝ)⁻¹ else 1) =
      w b - (if b ∈ H then w b / 2 else 0) := by
    intro b _
    split_ifs <;> ring
  rw [sum_congr rfl h1, sum_sub_distrib, sum_ite, sum_const_zero, add_zero, ← sum_div]
  congr 2
  rw [filter_mem_eq_inter, inter_eq_right.mpr hHC]

end Weights

/-! ## The comparisons `F_v ≤ 𝖿(s_v)` -/

section Compare

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- `F_u ≤ 𝖿_m(s_u)` for an integrated vertex `u` (proof of `cor:extraction-leaf`(a)): its free
partners `H_u` lie in the cover `C` of the other copy and in `N(u)` (support symmetry), so the
special sum is at most `∑_{b ∈ U⁺} w^m_{ub} - ½ σ^m_u(s_u) ≤ S_m(s_u)`, as
`|H_u| = s_u - t_u ≥ h⁰_u(s_u)` and `d_u ≥ s_u`; and `1 - e_{t_u}(q, n) ≥ 1 - ê`. -/
theorem intF_le_leafFm (G : OrientedGraph U) (ς : U → U → ℤ)
    (hsymm : ∀ j k, ς j k ≠ 0 → ς k j ≠ 0) {q : ℝ} {n : ℕ} {ehat : ℝ}
    (hehat : ∀ i, coarseError (rowsDeg0 G i) q n ≤ ehat) (hehat1 : ehat < 1)
    (ord : U → ℕ) (Fr : Finset (U × U)) (hFr : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) (C : Finset U)
    (u : U) (hHC : intH Fr u ⊆ C) :
    intF G ς q n ord Fr C u ≤ leafFm G ς q n ehat (intS G ord Fr u) := by
  set s := intS G ord Fr u with hs
  set t := ordT G ord u
  have htd : t ≤ rowsDeg0 G u := ordT_le_deg G ord u
  have het : coarseError t q n ≤ ehat := coarseError_ordT_le G hehat ord u
  have he0 := coarseError_nonneg (q := q) (Nat.cast_nonneg n) s
  have h1e : 0 < 1 - ehat := by linarith
  have h1t : 0 < 1 - coarseError t q n := by linarith
  -- `H_u ⊆ N(u)`
  have hHN : intH Fr u ⊆ rowsN ς u := by
    intro b hb
    simp only [intH, mem_filter, mem_univ, true_and] at hb
    simp only [rowsN, mem_filter, mem_univ, true_and]
    exact hsymm u b (hFr (u, b) hb)
  -- the special sum
  have hsp : ∑ b ∈ C, (2 : ℝ) ^ intExp G ς Fr u b ≤ leafS G ς (weightM G ς) s := by
    simp only [intExp_two_zpow]
    rw [sum_half_on C (intH Fr u) hHC (fun b => (2 : ℝ) ^ rowsCU G ς u b)]
    have hcard : leafH0 G u s ≤ (intH Fr u).card := by
      unfold leafH0
      simp only [hs, intS]
      omega
    have hsig := leafSigma_le ς (weightM G ς) (weightM_nonneg G ς) u hHN hcard
    have hds : s ≤ leafD G ς u := by
      simp only [hs, intS, leafD, leafR]
      have := card_le_card hHN
      omega
    have hS := le_leafS G ς (weightM G ς) hds
    have hCU : ∑ b ∈ C, (2 : ℝ) ^ rowsCU G ς u b ≤ ∑ j, weightM G ς u j :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) fun j _ _ => weightM_nonneg G ς u j
    simp only [weightM] at hsig hS hCU ⊢
    linarith
  -- the factor
  unfold intF intNum leafFm
  have hnum : 0 ≤ 1 + coarseError s q n +
      (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s * ∑ b ∈ C, (2 : ℝ) ^ intExp G ς Fr u b :=
    add_nonneg (by linarith) (mul_nonneg (by positivity) (sum_nonneg fun b _ => by positivity))
  calc (1 + coarseError s q n + (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s *
          ∑ b ∈ C, (2 : ℝ) ^ intExp G ς Fr u b) / (1 - coarseError t q n)
      ≤ (1 + coarseError s q n + (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s *
          ∑ b ∈ C, (2 : ℝ) ^ intExp G ς Fr u b) / (1 - ehat) :=
        div_le_div_of_nonneg_left hnum h1e (by linarith)
    _ ≤ _ := by
        refine div_le_div_of_nonneg_right ?_ h1e.le
        have : (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s * ∑ b ∈ C, (2 : ℝ) ^ intExp G ς Fr u b ≤
            (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s * leafS G ς (weightM G ς) s :=
          mul_le_mul_of_nonneg_left hsp (by positivity)
        linarith

/-- `F_b ≤ 𝖿_ρ(s_b)` for a cover vertex `b` (proof of `cor:extraction-leaf`(a)): `H_b ⊆ N(b)`,
`|H_b| = s_b - t_b ≥ h⁰_b(s_b)`, `d_b ≥ s_b`, and `1 - e_{t_b}(q, n) ≥ 1 - ê`. -/
theorem coverRowF_le_leafFrho (G : OrientedGraph U) (ς : U → U → ℤ) {q : ℝ} {n : ℕ}
    {ehat : ℝ} (hehat : ∀ i, coarseError (rowsDeg0 G i) q n ≤ ehat) (hehat1 : ehat < 1)
    (C : Finset U) (ord : U → ℕ) (H : Finset (U × U)) (hH : ∀ e ∈ H, ς e.1 e.2 ≠ 0) (b : U) :
    coverRowF G ς q n C ord H b ≤ leafFrho G ς q n ehat (coverRowS G C ord H b) := by
  set s := coverRowS G C ord H b with hs
  set t := coverRowT G C ord b
  have htd : t ≤ rowsDeg0 G b := coverRow_nbrCount_le G _ b
  have het : coarseError t q n ≤ ehat :=
    (coarseError_mono (Nat.cast_nonneg n) htd).trans (hehat b)
  have he0 := coarseError_nonneg (q := q) (by positivity : (0 : ℝ) ≤ 2 * n) s
  have h1e : 0 < 1 - ehat := by linarith
  have h1t : 0 < 1 - coarseError t q n := by linarith
  have hHN : coverRowH H b ⊆ rowsN ς b := by
    intro a ha
    simp only [coverRowH, mem_filter, mem_univ, true_and] at ha
    simp only [rowsN, mem_filter, mem_univ, true_and]
    exact hH (a, b) ha
  have hsp : ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b ≤ leafS G ς (weightRho G ς) s := by
    simp only [coverRow_two_zpow_exp]
    rw [sum_half_on univ (coverRowH H b) (subset_univ _)
      (fun j => (2 : ℝ) ^ (rowsMg G ς j b + rowsCU G ς j b))]
    have hcard : leafH0 G b s ≤ (coverRowH H b).card := by
      unfold leafH0
      simp only [hs, coverRowS]
      omega
    have hsig := leafSigma_le ς (weightRho G ς) (weightRho_nonneg G ς) b hHN hcard
    have hds : s ≤ leafD G ς b := by
      simp only [hs, coverRowS, leafD, leafR]
      have := card_le_card hHN
      omega
    have hS := le_leafS G ς (weightRho G ς) hds
    simp only [weightRho] at hsig hS ⊢
    linarith
  unfold coverRowF leafFrho
  have hnum : 0 ≤ 1 + coarseError s q (2 * n) +
      (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s * ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b :=
    add_nonneg (by linarith) (mul_nonneg (by positivity) (sum_nonneg fun j _ => by positivity))
  calc (1 + coarseError s q (2 * n) + (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s *
          ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b) / (1 - coarseError t q n)
      ≤ (1 + coarseError s q (2 * n) + (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s *
          ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b) / (1 - ehat) :=
        div_le_div_of_nonneg_left hnum h1e (by linarith)
    _ ≤ _ := by
        refine div_le_div_of_nonneg_right ?_ h1e.le
        have : (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s * ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b ≤
            (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s * leafS G ς (weightRho G ς) s :=
          mul_le_mul_of_nonneg_left hsp (by positivity)
        linarith

theorem intF_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) {q : ℝ} {n : ℕ} {ehat : ℝ}
    (hehat : ∀ i, coarseError (rowsDeg0 G i) q n ≤ ehat) (hehat1 : ehat < 1) (ord : U → ℕ)
    (Fr : Finset (U × U)) (C : Finset U) (u : U) : 0 ≤ intF G ς q n ord Fr C u := by
  unfold intF intNum
  have het := coarseError_ordT_le G hehat ord u
  have he0 := coarseError_nonneg (q := q) (Nat.cast_nonneg (α := ℝ) n) (intS G ord Fr u)
  refine div_nonneg (add_nonneg (by linarith) (mul_nonneg (by positivity)
    (sum_nonneg fun b _ => by positivity))) (by linarith)

theorem coverRowF_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) {q : ℝ} {n : ℕ} {ehat : ℝ}
    (hehat : ∀ i, coarseError (rowsDeg0 G i) q n ≤ ehat) (hehat1 : ehat < 1) (C : Finset U)
    (ord : U → ℕ) (H : Finset (U × U)) (b : U) : 0 ≤ coverRowF G ς q n C ord H b := by
  unfold coverRowF
  have het : coarseError (coverRowT G C ord b) q n ≤ ehat :=
    (coarseError_mono (Nat.cast_nonneg n) (coverRow_nbrCount_le G _ b)).trans (hehat b)
  have he0 := coarseError_nonneg (q := q) (by positivity : (0 : ℝ) ≤ 2 * n)
    (coverRowS G C ord H b)
  refine div_nonneg (add_nonneg (by linarith) (mul_nonneg (by positivity)
    (sum_nonneg fun b _ => by positivity))) (by linarith)

/-- `∏_v F_v ≤ ∏_{u ∈ U_x ∪ U_z} 𝖿_m(s_u) ∏_{b ∈ C_x ∪ C_z} 𝖿_ρ(s_b)` (proof of
`cor:extraction-leaf`(a)); `hFr1`, `hFr2` are the cover condition (VC_k) for the free pairs. -/
theorem recordFactor_le_leafProd (G : OrientedGraph U) (ς : U → U → ℤ)
    (hanti : ∀ j k, ς k j = -ς j k) {q : ℝ} {n : ℕ} {ehat : ℝ}
    (hehat : ∀ i, coarseError (rowsDeg0 G i) q n ≤ ehat) (hehat1 : ehat < 1)
    (Fr : Finset (U × U)) (hFr : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) (V W Cx Cz : Finset U)
    (hFr1 : ∀ e ∈ Fr, e.1 ∉ Cx → e.2 ∈ Cz) (hFr2 : ∀ e ∈ Fr, e.2 ∉ Cz → e.1 ∈ Cx)
    (ordX ordZ : U → ℕ) :
    recordFactor G ς q n Fr V W Cx Cz ordX ordZ ≤ leafProd G ς q n ehat Fr V W Cx Cz ordX ordZ := by
  have hsymm : ∀ j k, ς j k ≠ 0 → ς k j ≠ 0 := fun j k h => by
    rw [hanti j k]
    exact neg_ne_zero.mpr h
  have hFrT : ∀ e ∈ Fr.image Prod.swap, ς e.1 e.2 ≠ 0 := by
    intro e he
    obtain ⟨e₀, he₀, rfl⟩ := mem_image.mp he
    exact hsymm _ _ (hFr e₀ he₀)
  have h1 : ∏ u ∈ univ \ (V ∪ Cx), intF G ς q n ordX Fr Cz u ≤
      ∏ u ∈ univ \ (V ∪ Cx), leafFm G ς q n ehat (intS G ordX Fr u) := by
    refine prod_le_prod₀ (fun u _ => intF_nonneg G ς hehat hehat1 ordX Fr Cz u) fun u hu => ?_
    refine intF_le_leafFm G ς hsymm hehat hehat1 ordX Fr hFr Cz u fun b hb => ?_
    simp only [intH, mem_filter, mem_univ, true_and] at hb
    have hu' : u ∉ Cx := by
      simp only [mem_sdiff, mem_univ, true_and, mem_union, not_or] at hu
      exact hu.2
    exact hFr1 (u, b) hb hu'
  have h2 : ∏ b ∈ Cz, coverRowF G ς q n Cz ordZ (Fr.filter (fun e => e.2 ∈ Cz)) b ≤
      ∏ b ∈ Cz, leafFrho G ς q n ehat (coverRowS G Cz ordZ (Fr.filter (fun e => e.2 ∈ Cz)) b) :=
    prod_le_prod₀ (fun b _ => coverRowF_nonneg G ς hehat hehat1 _ _ _ b) fun b _ =>
      coverRowF_le_leafFrho G ς hehat hehat1 Cz ordZ _ (fun e he => hFr e (mem_filter.mp he).1) b
  have h3 : ∏ u ∈ univ \ (W ∪ Cz), intF G ς q n ordZ (Fr.image Prod.swap) Cx u ≤
      ∏ u ∈ univ \ (W ∪ Cz), leafFm G ς q n ehat (intS G ordZ (Fr.image Prod.swap) u) := by
    refine prod_le_prod₀ (fun u _ => intF_nonneg G ς hehat hehat1 ordZ _ Cx u) fun u hu => ?_
    refine intF_le_leafFm G ς hsymm hehat hehat1 ordZ _ hFrT Cx u fun a ha => ?_
    simp only [intH, mem_filter, mem_univ, true_and] at ha
    obtain ⟨e₀, he₀, he⟩ := mem_image.mp ha
    have hu' : u ∉ Cz := by
      simp only [mem_sdiff, mem_univ, true_and, mem_union, not_or] at hu
      exact hu.2
    have h1' : e₀.2 = u := by rw [← Prod.fst_swap, he]
    have h2' : e₀.1 = a := by rw [← Prod.snd_swap, he]
    rw [← h2']
    exact hFr2 e₀ he₀ (by rw [h1']; exact hu')
  have h4 : ∏ b ∈ Cx, coverRowF G ς q n Cx ordX
        ((Fr.image Prod.swap).filter (fun e => e.2 ∈ Cx)) b ≤
      ∏ b ∈ Cx, leafFrho G ς q n ehat
        (coverRowS G Cx ordX ((Fr.image Prod.swap).filter (fun e => e.2 ∈ Cx)) b) :=
    prod_le_prod₀ (fun b _ => coverRowF_nonneg G ς hehat hehat1 _ _ _ b) fun b _ =>
      coverRowF_le_leafFrho G ς hehat hehat1 Cx ordX _
        (fun e he => hFrT e (mem_filter.mp he).1) b
  unfold recordFactor leafProd leafProdOf
  have p1 := prod_nonneg fun u (_ : u ∈ univ \ (V ∪ Cx)) =>
    intF_nonneg G ς hehat hehat1 ordX Fr Cz u
  have p2 := prod_nonneg fun b (_ : b ∈ Cz) =>
    coverRowF_nonneg G ς hehat hehat1 Cz ordZ (Fr.filter (fun e => e.2 ∈ Cz)) b
  have p3 := prod_nonneg fun u (_ : u ∈ univ \ (W ∪ Cz)) =>
    intF_nonneg G ς hehat hehat1 ordZ (Fr.image Prod.swap) Cx u
  have p4 := prod_nonneg fun b (_ : b ∈ Cx) =>
    coverRowF_nonneg G ς hehat hehat1 Cx ordX ((Fr.image Prod.swap).filter (fun e => e.2 ∈ Cx)) b
  have q1 := le_trans p1 h1
  have q2 := le_trans p2 h2
  have q3 := le_trans p3 h3
  exact mul_le_mul (mul_le_mul (mul_le_mul h1 h2 p2 q1) h3 p3 (mul_nonneg q1 q2)) h4 p4
    (mul_nonneg (mul_nonneg q1 q2) q3)

end Compare

/-! ## `cor:extraction-leaf`(a) -/

section LeafBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

theorem rowsR_univ_ge_one (G : OrientedGraph U) {q : ℝ} {n : ℕ}
    (he : ∀ i, coarseError (rowsDeg0 G i) q n < 1) : 1 ≤ rowsR G q n univ := by
  unfold rowsR
  refine one_le_prod₀ fun i _ => ?_
  have h0 := coarseError_nonneg (q := q) (Nat.cast_nonneg (α := ℝ) n) (rowsDeg0 G i)
  have h1 := he i
  rw [one_le_div (by linarith)]
  linarith

/-- **`cor:extraction-leaf`(a)**, with a kernel constant `c_ker` (the hypothesis of
`lem:matching:extractionk`): `|∑_{S ∈ 𝒞} ⟨f, T_S h⟩_μ| ≤ c_ker r^k 2^{ex(𝒞)/2} R_full²
(1 - ê)^{-k} ∏_{u ∈ U_x ∪ U_z} 𝖿_m(s_u)^{1/2} ∏_{b ∈ C_x ∪ C_z} 𝖿_ρ(s_b)^{1/2} ‖f‖_μ ‖h‖_μ`
(the product is `leafProd`, under one square root). The factor `R_full² ≥ 1` is kept as in the
paper; `grouped_extraction` gives the bound without it. -/
theorem extraction_leaf (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n) {ehat : ℝ}
    (hehat : ∀ i, coarseError (rowsDeg0 G i) (Fintype.card F) n ≤ ehat) (hehat1 : ehat < 1)
    (Ex P A : Finset (U × U)) (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0) (hcls : IsClassDatum Ex (P, A))
    {k : ℕ} (w : Fin k → U × U) (hw : IsWitness Ex P A w) (Cx Cz : Finset U)
    (hcov : IsCover Ex P A w Cx Cz) (ordX ordZ : U → ℕ) (hordX : Function.Injective ordX)
    (hordZ : Function.Injective ordZ) (hX0 : ∀ a ∈ Cx, ∀ b, b ∉ Cx → ordX a < ordX b)
    (hZ0 : ∀ a ∈ Cz, ∀ b, b ∉ Cz → ordZ a < ordZ b)
    (hX1 : ∀ a, a ∉ univ \ (witV w ∪ Cx) → ∀ b ∈ univ \ (witV w ∪ Cx), ordX a < ordX b)
    (hZ1 : ∀ a, a ∉ univ \ (witW w ∪ Cz) → ∀ b ∈ univ \ (witW w ∪ Cz), ordZ a < ordZ b)
    {cker : ℝ} (hcker : 0 ≤ cker)
    (hker : Sarkozy.Influence.OpBound (injTuples F (witV w)) (injTuples F (witW w))
      (rectKer ς P (witV w) (witW w)) (cker * Real.sqrt (Fintype.card F) ^ k))
    (f h : (U → F) → ℝ) :
    |(graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
        (∑ S ∈ cls Ex P A, ∏ e ∈ S, chiPair ς e x x') * h x'))| ≤
      cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        Real.sqrt (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
          leafProd G ς (Fintype.card F) n ehat (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) *
        rowsR G (Fintype.card F) n univ ^ 2 / (1 - ehat) ^ k *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by
  refine (grouped_extraction hW G ς hς hanti hne hn hehat hehat1 Ex P A hEx hcls w hw Cx Cz hcov
    ordX ordZ hordX hordZ hX0 hZ0 hX1 hZ1 hcker hker f h).trans ?_
  -- the cover condition for the free pairs
  have hFr' : ∀ e ∈ Ex \ (P ∪ A), e.1 ∈ Cx ∨ e.2 ∈ Cz := by
    intro e he
    refine hcov.cover e (mem_union_right _ he) fun hr => ?_
    have := hw.decided e (mem_sdiff.mp he).1 hr.1 hr.2
    exact (mem_sdiff.mp he).2 (mem_union.mpr this)
  have hPF := recordFactor_le_leafProd G ς hanti hehat hehat1 (Ex \ (P ∪ A))
    (fun e he => hEx e (mem_sdiff.mp he).1) (witV w) (witW w) Cx Cz
    (fun e he h1 => (hFr' e he).resolve_left h1) (fun e he h2 => (hFr' e he).resolve_right h2)
    ordX ordZ
  have hR : 1 ≤ rowsR G (Fintype.card F) n univ ^ 2 := by
    have := rowsR_univ_ge_one G (q := (Fintype.card F : ℝ)) (n := n)
      (fun i => lt_of_le_of_lt (hehat i) hehat1)
    nlinarith
  have h1e : 0 < 1 - ehat := by linarith
  have hsq : Real.sqrt (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
        recordFactor G ς (Fintype.card F) n (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) ≤
      Real.sqrt (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
        leafProd G ς (Fintype.card F) n ehat (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) *
        rowsR G (Fintype.card F) n univ ^ 2 := by
    refine (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hPF (by positivity))).trans ?_
    exact le_mul_of_one_le_right (Real.sqrt_nonneg _) hR
  set X := cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k / (1 - ehat) ^ k *
    Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
    Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) with hX
  have hX0 : 0 ≤ X := by positivity
  calc cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        Real.sqrt (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
          recordFactor G ς (Fintype.card F) n (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) /
        (1 - ehat) ^ k *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2))
      = X * Real.sqrt (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
          recordFactor G ς (Fintype.card F) n (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) := by
        rw [hX]
        ring
    _ ≤ X * (Real.sqrt (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
          leafProd G ς (Fintype.card F) n ehat (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) *
          rowsR G (Fintype.card F) n univ ^ 2) := mul_le_mul_of_nonneg_left hsq hX0
    _ = _ := by
        rw [hX]
        ring

end LeafBound

/-! ## `F = 𝔽_p`: the kernel constants of `lem:matching:kernel` -/

section ZModLeaf

variable {p : ℕ} [Fact p.Prime]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- **`cor:extraction-leaf`(a)**, the statement of the paper: for `F = 𝔽_p` and a witness
digraph whose strongly connected components have at most two vertices, `c_ker = 2^{β(𝒞)}`
(`lem:matching:kernel`(b), via `IsWitness.rectKer_opBound_twoCycles`; the four-cycle bound
`cor:dl:normalized`(a) is the hypothesis `FourCycleBound p`), and
`|∑_{S ∈ 𝒞} ⟨f, T_S h⟩_μ| ≤ r^k 2^{ex*(𝒞)/2} R_full² (1 - ê)^{-k}
∏_{u ∈ U_x ∪ U_z} 𝖿_m(s_u)^{1/2} ∏_{b ∈ C_x ∪ C_z} 𝖿_ρ(s_b)^{1/2} ‖f‖_μ ‖h‖_μ`,
`ex* = ex + 2β`, `r = p^{-1/2}`. -/
theorem extraction_leaf_twoCycles (hW : WeilBound (ZMod p)) (hp2 : p ≠ 2)
    (h4 : FourCycleBound p)
    (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings (ZMod p) G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n) {ehat : ℝ}
    (hehat : ∀ i, coarseError (rowsDeg0 G i) p n ≤ ehat) (hehat1 : ehat < 1)
    (Ex P A : Finset (U × U)) (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0) (hcls : IsClassDatum Ex (P, A))
    {k : ℕ} (w : Fin k → U × U) (hw : IsWitness Ex P A w)
    (hcard : ∀ i, (twoCycleComponent (witnessIdx P w) i).card ≤ 2)
    (Cx Cz : Finset U) (hcov : IsCover Ex P A w Cx Cz) (ordX ordZ : U → ℕ)
    (hordX : Function.Injective ordX) (hordZ : Function.Injective ordZ)
    (hX0 : ∀ a ∈ Cx, ∀ b, b ∉ Cx → ordX a < ordX b)
    (hZ0 : ∀ a ∈ Cz, ∀ b, b ∉ Cz → ordZ a < ordZ b)
    (hX1 : ∀ a, a ∉ univ \ (witV w ∪ Cx) → ∀ b ∈ univ \ (witV w ∪ Cx), ordX a < ordX b)
    (hZ1 : ∀ a, a ∉ univ \ (witW w ∪ Cz) → ∀ b ∈ univ \ (witW w ∪ Cz), ordZ a < ordZ b)
    (f h : (U → ZMod p) → ℝ) :
    |(graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
        (∑ S ∈ cls Ex P A, ∏ e ∈ S, chiPair ς e x x') * h x'))| ≤
      (Real.sqrt p)⁻¹ ^ k *
        Real.sqrt (2 ^ (recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ +
            2 * twoCycleCount (witnessIdx P w)) *
          leafProd G ς p n ehat (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) *
        rowsR G p n univ ^ 2 / (1 - ehat) ^ k *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by
  have hςP := sign_pm_of_ne_zero hς (fun e he => hEx e (hcls.1 he))
  have hk := IsWitness.rectKer_opBound_twoCycles hw hp2 h4 ς hςP hcard
  have hker : Sarkozy.Influence.OpBound (injTuples (ZMod p) (witV w))
      (injTuples (ZMod p) (witW w)) (rectKer ς P (witV w) (witW w))
      (2 ^ twoCycleCount (witnessIdx P w) * Real.sqrt (Fintype.card (ZMod p)) ^ k) := by
    rw [ZMod.card]
    exact hk
  have hehat' : ∀ i, coarseError (rowsDeg0 G i) (Fintype.card (ZMod p)) n ≤ ehat := by
    rw [ZMod.card]
    exact hehat
  have hL := extraction_leaf hW G ς hς hanti hne hn hehat' hehat1 Ex P A hEx hcls w hw Cx Cz
    hcov ordX ordZ hordX hordZ hX0 hZ0 hX1 hZ1 (by positivity) hker f h
  rw [ZMod.card] at hL
  refine hL.trans (le_of_eq ?_)
  have e : (2 : ℝ) ^ (recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ +
        2 * twoCycleCount (witnessIdx P w)) *
        leafProd G ς p n ehat (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ =
      ((2 : ℝ) ^ twoCycleCount (witnessIdx P w)) ^ 2 *
        (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
          leafProd G ς p n ehat (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) := by
    rw [pow_add, pow_mul']
    ring
  rw [e, Real.sqrt_mul (sq_nonneg ((2 : ℝ) ^ twoCycleCount (witnessIdx P w))),
    Real.sqrt_sq (by positivity)]
  ring

/-- **`cor:extraction-leaf`(a)** for an acyclic witness digraph (`c_ker = 1`,
`lem:matching:kernel`(a); no hypothesis beyond Weil's theorem). -/
theorem extraction_leaf_acyclic (hW : WeilBound (ZMod p)) (hp2 : p ≠ 2)
    (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings (ZMod p) G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n) {ehat : ℝ}
    (hehat : ∀ i, coarseError (rowsDeg0 G i) p n ≤ ehat) (hehat1 : ehat < 1)
    (Ex P A : Finset (U × U)) (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0) (hcls : IsClassDatum Ex (P, A))
    {k : ℕ} (w : Fin k → U × U) (hw : IsWitness Ex P A w)
    (hac : IsAcyclicWitness (witnessIdx P w))
    (Cx Cz : Finset U) (hcov : IsCover Ex P A w Cx Cz) (ordX ordZ : U → ℕ)
    (hordX : Function.Injective ordX) (hordZ : Function.Injective ordZ)
    (hX0 : ∀ a ∈ Cx, ∀ b, b ∉ Cx → ordX a < ordX b)
    (hZ0 : ∀ a ∈ Cz, ∀ b, b ∉ Cz → ordZ a < ordZ b)
    (hX1 : ∀ a, a ∉ univ \ (witV w ∪ Cx) → ∀ b ∈ univ \ (witV w ∪ Cx), ordX a < ordX b)
    (hZ1 : ∀ a, a ∉ univ \ (witW w ∪ Cz) → ∀ b ∈ univ \ (witW w ∪ Cz), ordZ a < ordZ b)
    (f h : (U → ZMod p) → ℝ) :
    |(graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
        (∑ S ∈ cls Ex P A, ∏ e ∈ S, chiPair ς e x x') * h x'))| ≤
      (Real.sqrt p)⁻¹ ^ k *
        Real.sqrt (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
          leafProd G ς p n ehat (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) *
        rowsR G p n univ ^ 2 / (1 - ehat) ^ k *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by
  have hςP := sign_pm_of_ne_zero hς (fun e he => hEx e (hcls.1 he))
  have hk := IsWitness.rectKer_opBound_acyclic hw hp2 ς hςP hac
  have hker : Sarkozy.Influence.OpBound (injTuples (ZMod p) (witV w))
      (injTuples (ZMod p) (witW w)) (rectKer ς P (witV w) (witW w))
      (1 * Real.sqrt (Fintype.card (ZMod p)) ^ k) := by
    rw [ZMod.card, one_mul]
    exact hk
  have hehat' : ∀ i, coarseError (rowsDeg0 G i) (Fintype.card (ZMod p)) n ≤ ehat := by
    rw [ZMod.card]
    exact hehat
  have hL := extraction_leaf hW G ς hς hanti hne hn hehat' hehat1 Ex P A hEx hcls w hw Cx Cz
    hcov ordX ordZ hordX hordZ hX0 hZ0 hX1 hZ1 zero_le_one hker f h
  rw [ZMod.card, one_mul] at hL
  exact hL

end ZModLeaf

/-! ## The monotone-factor condition (`eq:monotone-signature`) -/

section Monotone

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- A function nondecreasing at every step `s → s + 1` with `s < Δ` is nondecreasing on
`{0, …, Δ}`. -/
theorem mono_upto {g : ℕ → ℝ} {Δ : ℕ} (hg : ∀ s, s < Δ → g s ≤ g (s + 1)) {s s' : ℕ}
    (h1 : s ≤ s') (h2 : s' ≤ Δ) : g s ≤ g s' := by
  revert h2
  induction s', h1 using Nat.le_induction with
  | base => exact fun _ => le_rfl
  | succ m _ ih => exact fun h2 => (ih (by omega)).trans (hg m (by omega))

/-- The monotone-factor condition `eq:monotone-signature` for a weight function `w`:
`2^s S(s) ≤ 2^{s+1} S(s+1)` for `0 ≤ s < Δ`. -/
def LeafMonotone (G : OrientedGraph U) (ς : U → U → ℤ) (w : U → U → ℝ) : Prop :=
  ∀ s, s < leafDelta G ς → (2 : ℝ) ^ s * leafS G ς w s ≤ 2 ^ (s + 1) * leafS G ς w (s + 1)

theorem leafFm_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) {q : ℝ} {n : ℕ} {ehat : ℝ}
    (hehat1 : ehat < 1) (s : ℕ) : 0 ≤ leafFm G ς q n ehat s := by
  unfold leafFm
  have he0 := coarseError_nonneg (q := q) (Nat.cast_nonneg (α := ℝ) n) s
  have hS := leafS_nonneg G ς (weightM G ς) (weightM_nonneg G ς) s
  exact div_nonneg (add_nonneg (by linarith) (mul_nonneg (by positivity) hS)) (by linarith)

theorem leafFrho_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) {q : ℝ} {n : ℕ} {ehat : ℝ}
    (hehat1 : ehat < 1) (s : ℕ) : 0 ≤ leafFrho G ς q n ehat s := by
  unfold leafFrho
  have he0 := coarseError_nonneg (q := q) (by positivity : (0 : ℝ) ≤ 2 * n) s
  have hS := leafS_nonneg G ς (weightRho G ς) (weightRho_nonneg G ς) s
  exact div_nonneg (add_nonneg (by linarith) (mul_nonneg (by positivity) hS)) (by linarith)

/-- **`cor:extraction-leaf`(a), monotone factors**: under `eq:monotone-signature`, `𝖿_m` is
nondecreasing on `{0, …, Δ}`. -/
theorem leafFm_mono (G : OrientedGraph U) (ς : U → U → ℤ) (hmono : LeafMonotone G ς (weightM G ς))
    {q : ℝ} {n : ℕ} {ehat : ℝ} (hehat1 : ehat < 1) {s s' : ℕ} (h1 : s ≤ s')
    (h2 : s' ≤ leafDelta G ς) : leafFm G ς q n ehat s ≤ leafFm G ς q n ehat s' := by
  unfold leafFm
  refine div_le_div_of_nonneg_right ?_ (by linarith)
  have he := coarseError_mono (q := q) (Nat.cast_nonneg (α := ℝ) n) h1
  have hg := mono_upto (g := fun s => (2 : ℝ) ^ s * leafS G ς (weightM G ς) s) hmono h1 h2
  have hr : (0 : ℝ) ≤ (Real.sqrt q)⁻¹ ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hg hr
  simp only [mul_assoc] at this ⊢
  linarith

/-- **`cor:extraction-leaf`(a), monotone factors**: under `eq:monotone-signature`, `𝖿_ρ` is
nondecreasing on `{0, …, Δ}`. -/
theorem leafFrho_mono (G : OrientedGraph U) (ς : U → U → ℤ)
    (hmono : LeafMonotone G ς (weightRho G ς)) {q : ℝ} {n : ℕ} {ehat : ℝ} (hehat1 : ehat < 1)
    {s s' : ℕ} (h1 : s ≤ s') (h2 : s' ≤ leafDelta G ς) :
    leafFrho G ς q n ehat s ≤ leafFrho G ς q n ehat s' := by
  unfold leafFrho
  refine div_le_div_of_nonneg_right ?_ (by linarith)
  have he := coarseError_mono (q := q) (by positivity : (0 : ℝ) ≤ 2 * n) h1
  have hg := mono_upto (g := fun s => (2 : ℝ) ^ s * leafS G ς (weightRho G ς) s) hmono h1 h2
  have hr : (0 : ℝ) ≤ (Real.sqrt q)⁻¹ ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hg hr
  simp only [mul_assoc] at this ⊢
  linarith

/-- With stored numbers `s'_v ∈ [s_v, Δ]` the product of the leaf factors only grows
(`cor:extraction-leaf`(a), under `eq:monotone-signature`). -/
theorem leafProdOf_mono (G : OrientedGraph U) (ς : U → U → ℤ)
    (hm : LeafMonotone G ς (weightM G ς)) (hρ : LeafMonotone G ς (weightRho G ς)) {q : ℝ}
    {n : ℕ} {ehat : ℝ} (hehat1 : ehat < 1) (V W Cx Cz : Finset U)
    (sUx sCz sUz sCx sUx' sCz' sUz' sCx' : U → ℕ)
    (h1 : ∀ u ∈ univ \ (V ∪ Cx), sUx u ≤ sUx' u ∧ sUx' u ≤ leafDelta G ς)
    (h2 : ∀ b ∈ Cz, sCz b ≤ sCz' b ∧ sCz' b ≤ leafDelta G ς)
    (h3 : ∀ u ∈ univ \ (W ∪ Cz), sUz u ≤ sUz' u ∧ sUz' u ≤ leafDelta G ς)
    (h4 : ∀ b ∈ Cx, sCx b ≤ sCx' b ∧ sCx' b ≤ leafDelta G ς) :
    leafProdOf G ς q n ehat V W Cx Cz sUx sCz sUz sCx ≤
      leafProdOf G ς q n ehat V W Cx Cz sUx' sCz' sUz' sCx' := by
  unfold leafProdOf
  have a1 : ∏ u ∈ univ \ (V ∪ Cx), leafFm G ς q n ehat (sUx u) ≤
      ∏ u ∈ univ \ (V ∪ Cx), leafFm G ς q n ehat (sUx' u) :=
    prod_le_prod₀ (fun u _ => leafFm_nonneg G ς hehat1 _) fun u hu =>
      leafFm_mono G ς hm hehat1 (h1 u hu).1 (h1 u hu).2
  have a2 : ∏ b ∈ Cz, leafFrho G ς q n ehat (sCz b) ≤ ∏ b ∈ Cz, leafFrho G ς q n ehat (sCz' b) :=
    prod_le_prod₀ (fun b _ => leafFrho_nonneg G ς hehat1 _) fun b hb =>
      leafFrho_mono G ς hρ hehat1 (h2 b hb).1 (h2 b hb).2
  have a3 : ∏ u ∈ univ \ (W ∪ Cz), leafFm G ς q n ehat (sUz u) ≤
      ∏ u ∈ univ \ (W ∪ Cz), leafFm G ς q n ehat (sUz' u) :=
    prod_le_prod₀ (fun u _ => leafFm_nonneg G ς hehat1 _) fun u hu =>
      leafFm_mono G ς hm hehat1 (h3 u hu).1 (h3 u hu).2
  have a4 : ∏ b ∈ Cx, leafFrho G ς q n ehat (sCx b) ≤ ∏ b ∈ Cx, leafFrho G ς q n ehat (sCx' b) :=
    prod_le_prod₀ (fun b _ => leafFrho_nonneg G ς hehat1 _) fun b hb =>
      leafFrho_mono G ς hρ hehat1 (h4 b hb).1 (h4 b hb).2
  have p1 := prod_nonneg fun u (_ : u ∈ univ \ (V ∪ Cx)) => leafFm_nonneg G ς hehat1 (q := q)
    (n := n) (sUx u)
  have p2 := prod_nonneg fun b (_ : b ∈ Cz) => leafFrho_nonneg G ς hehat1 (q := q) (n := n) (sCz b)
  have p3 := prod_nonneg fun u (_ : u ∈ univ \ (W ∪ Cz)) => leafFm_nonneg G ς hehat1 (q := q)
    (n := n) (sUz u)
  have p4 := prod_nonneg fun b (_ : b ∈ Cx) => leafFrho_nonneg G ς hehat1 (q := q) (n := n) (sCx b)
  have q1 := le_trans p1 a1
  have q2 := le_trans p2 a2
  have q3 := le_trans p3 a3
  exact mul_le_mul (mul_le_mul (mul_le_mul a1 a2 p2 q1) a3 p3 (mul_nonneg q1 q2)) a4 p4
    (mul_nonneg (mul_nonneg q1 q2) q3)

end Monotone

/-! ## Stored numbers -/

section Stored

variable {p : ℕ} [Fact p.Prime]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- **`cor:extraction-leaf`(a) with stored numbers**: under the monotone-factor condition
`eq:monotone-signature` (for `S_m` and `S_ρ`), the bound of `extraction_leaf_twoCycles` holds with
the counts `s_v` replaced by any stored numbers `s'_v` with `s_v ≤ s'_v ≤ Δ`. -/
theorem extraction_leaf_twoCycles_stored (hW : WeilBound (ZMod p)) (hp2 : p ≠ 2)
    (h4 : FourCycleBound p)
    (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings (ZMod p) G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n) {ehat : ℝ}
    (hehat : ∀ i, coarseError (rowsDeg0 G i) p n ≤ ehat) (hehat1 : ehat < 1)
    (Ex P A : Finset (U × U)) (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0) (hcls : IsClassDatum Ex (P, A))
    {k : ℕ} (w : Fin k → U × U) (hw : IsWitness Ex P A w)
    (hcard : ∀ i, (twoCycleComponent (witnessIdx P w) i).card ≤ 2)
    (Cx Cz : Finset U) (hcov : IsCover Ex P A w Cx Cz) (ordX ordZ : U → ℕ)
    (hordX : Function.Injective ordX) (hordZ : Function.Injective ordZ)
    (hX0 : ∀ a ∈ Cx, ∀ b, b ∉ Cx → ordX a < ordX b)
    (hZ0 : ∀ a ∈ Cz, ∀ b, b ∉ Cz → ordZ a < ordZ b)
    (hX1 : ∀ a, a ∉ univ \ (witV w ∪ Cx) → ∀ b ∈ univ \ (witV w ∪ Cx), ordX a < ordX b)
    (hZ1 : ∀ a, a ∉ univ \ (witW w ∪ Cz) → ∀ b ∈ univ \ (witW w ∪ Cz), ordZ a < ordZ b)
    (hm : LeafMonotone G ς (weightM G ς)) (hρ : LeafMonotone G ς (weightRho G ς))
    (sUx' sCz' sUz' sCx' : U → ℕ)
    (hs1 : ∀ u ∈ univ \ (witV w ∪ Cx),
      intS G ordX (Ex \ (P ∪ A)) u ≤ sUx' u ∧ sUx' u ≤ leafDelta G ς)
    (hs2 : ∀ b ∈ Cz, coverRowS G Cz ordZ ((Ex \ (P ∪ A)).filter (fun e => e.2 ∈ Cz)) b ≤ sCz' b ∧
      sCz' b ≤ leafDelta G ς)
    (hs3 : ∀ u ∈ univ \ (witW w ∪ Cz),
      intS G ordZ ((Ex \ (P ∪ A)).image Prod.swap) u ≤ sUz' u ∧ sUz' u ≤ leafDelta G ς)
    (hs4 : ∀ b ∈ Cx, coverRowS G Cx ordX
        (((Ex \ (P ∪ A)).image Prod.swap).filter (fun e => e.2 ∈ Cx)) b ≤ sCx' b ∧
      sCx' b ≤ leafDelta G ς)
    (f h : (U → ZMod p) → ℝ) :
    |(graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
        (∑ S ∈ cls Ex P A, ∏ e ∈ S, chiPair ς e x x') * h x'))| ≤
      (Real.sqrt p)⁻¹ ^ k *
        Real.sqrt (2 ^ (recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ +
            2 * twoCycleCount (witnessIdx P w)) *
          leafProdOf G ς p n ehat (witV w) (witW w) Cx Cz sUx' sCz' sUz' sCx') *
        rowsR G p n univ ^ 2 / (1 - ehat) ^ k *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by
  refine (extraction_leaf_twoCycles hW hp2 h4 G ς hς hanti hne hn hehat hehat1 Ex P A hEx hcls
    w hw hcard Cx Cz hcov ordX ordZ hordX hordZ hX0 hZ0 hX1 hZ1 f h).trans ?_
  have hle : leafProd G ς p n ehat (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ ≤
      leafProdOf G ς p n ehat (witV w) (witW w) Cx Cz sUx' sCz' sUz' sCx' :=
    leafProdOf_mono G ς hm hρ hehat1 _ _ _ _ _ _ _ _ _ _ _ _ hs1 hs2 hs3 hs4
  have h1e : 0 < 1 - ehat := by linarith
  have hsq := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hle
    (by positivity : (0 : ℝ) ≤ 2 ^ (recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ +
      2 * twoCycleCount (witnessIdx P w))))
  have hR : 0 ≤ rowsR G p n univ ^ 2 := sq_nonneg _
  gcongr

end Stored

/-! ## `cor:extraction-leaf`(b): the nonstar coefficients -/

section Partition

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The data of a record of a class (`def:extraction:records`): a witness `w` of size `k`, a cover
`(C_x, C_z)` and orders of the two copies, fixed independently of `p`. -/
structure LeafRecordData (U : Type*) where
  /-- the witness size -/
  k : ℕ
  /-- the witness pairs -/
  w : Fin k → U × U
  /-- the cover in the `x`-copy -/
  Cx : Finset U
  /-- the cover in the `x'`-copy -/
  Cz : Finset U
  /-- the order of the `x`-copy -/
  ordX : U → ℕ
  /-- the order of the `x'`-copy -/
  ordZ : U → ℕ

/-- The conditions on a record of the class `c = (P, A)` (`def:extraction:witness`,
`def:extraction:records`): (W_k), (VC_k), orders with the cover first and the integrated set
last, and a witness digraph with strongly connected components of at most two vertices. -/
structure LeafRecordData.Valid (R : LeafRecordData U) (Ex : Finset (U × U))
    (c : Finset (U × U) × Finset (U × U)) : Prop where
  witness : IsWitness Ex c.1 c.2 R.w
  cover : IsCover Ex c.1 c.2 R.w R.Cx R.Cz
  injX : Function.Injective R.ordX
  injZ : Function.Injective R.ordZ
  segX0 : ∀ a ∈ R.Cx, ∀ b, b ∉ R.Cx → R.ordX a < R.ordX b
  segZ0 : ∀ a ∈ R.Cz, ∀ b, b ∉ R.Cz → R.ordZ a < R.ordZ b
  segX1 : ∀ a, a ∉ univ \ (witV R.w ∪ R.Cx) → ∀ b ∈ univ \ (witV R.w ∪ R.Cx),
    R.ordX a < R.ordX b
  segZ1 : ∀ a, a ∉ univ \ (witW R.w ∪ R.Cz) → ∀ b ∈ univ \ (witW R.w ∪ R.Cz),
    R.ordZ a < R.ordZ b
  twoCycles : ∀ i, (twoCycleComponent (witnessIdx c.1 R.w) i).card ≤ 2

/-- `ê = e_{Δ⁺}(q, n)`, `Δ⁺ = max_i d⁰_i`. -/
noncomputable def leafEhat (G : OrientedGraph U) (q : ℝ) (n : ℕ) : ℝ :=
  coarseError (univ.sup (rowsDeg0 G)) q n

/-- The coefficient of a class with a record in `C_k(q)` (`cor:extraction-leaf`(b)):
`2^{ex*/2} R_full² (1 - ê)^{-k} ∏_u 𝖿_m(s_u)^{1/2} ∏_b 𝖿_ρ(s_b)^{1/2}`, evaluated at `r = q^{-1/2}`. -/
noncomputable def leafCoef (G : OrientedGraph U) (ς : U → U → ℤ) (q : ℝ) (n : ℕ)
    (Ex : Finset (U × U)) (c : Finset (U × U) × Finset (U × U)) (R : LeafRecordData U) : ℝ :=
  Real.sqrt (2 ^ (recordExp G (Ex \ (c.1 ∪ c.2)) (witV R.w) (witW R.w) R.ordX R.ordZ +
      2 * twoCycleCount (witnessIdx c.1 R.w)) *
    leafProd G ς q n (leafEhat G q n) (Ex \ (c.1 ∪ c.2)) (witV R.w) (witW R.w) R.Cx R.Cz R.ordX
      R.ordZ) * rowsR G q n univ ^ 2 / (1 - leafEhat G q n) ^ R.k

omit [DecidableEq U] in
theorem leaf_coarseError_anti (t : ℕ) {n' : ℝ} (hn' : 0 ≤ n') {Q q : ℝ} (hQ : 0 < Q)
    (hQq : Q ≤ q) : coarseError t q n' ≤ coarseError t Q n' := by
  unfold coarseError
  have hr : (Real.sqrt q)⁻¹ ≤ (Real.sqrt Q)⁻¹ :=
    inv_anti₀ (Real.sqrt_pos.mpr hQ) (Real.sqrt_le_sqrt hQq)
  have hr0 : 0 ≤ (Real.sqrt q)⁻¹ := by positivity
  have hh : 0 ≤ coarseH t := by
    unfold coarseH
    rcases Nat.lt_or_ge t 2 with ht | ht
    · interval_cases t <;> norm_num
    · have h1 : (2 : ℝ) ≤ t := by exact_mod_cast ht
      have h2 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ t := by positivity
      linarith
  refine mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hr hh)
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr 2) hn')) (by positivity)

theorem coarseError_le_leafEhat (G : OrientedGraph U) (q : ℝ) (n : ℕ) (i : U) :
    coarseError (rowsDeg0 G i) q n ≤ leafEhat G q n :=
  coarseError_mono (Nat.cast_nonneg n) (le_sup (f := rowsDeg0 G) (mem_univ i))

theorem leafEhat_anti (G : OrientedGraph U) {n : ℕ} {Q q : ℝ} (hQ : 0 < Q) (hQq : Q ≤ q) :
    leafEhat G q n ≤ leafEhat G Q n :=
  leaf_coarseError_anti _ (Nat.cast_nonneg n) hQ hQq

/-- The leaf factor `𝖿_m(s)` is nonincreasing in `q` (`r = q^{-1/2}`, `ê = e_{Δ⁺}(q, n)`). -/
theorem leafFm_anti (G : OrientedGraph U) (ς : U → U → ℤ) {n : ℕ} {Q q : ℝ} (hQ : 0 < Q)
    (hQq : Q ≤ q) (hS1 : leafEhat G Q n < 1) (s : ℕ) :
    leafFm G ς q n (leafEhat G q n) s ≤ leafFm G ς Q n (leafEhat G Q n) s := by
  unfold leafFm
  have he := leafEhat_anti G (n := n) hQ hQq
  have hes := leaf_coarseError_anti s (Nat.cast_nonneg (α := ℝ) n) hQ hQq
  have he0 := coarseError_nonneg (q := q) (Nat.cast_nonneg (α := ℝ) n) s
  have hS := leafS_nonneg G ς (weightM G ς) (weightM_nonneg G ς) s
  have hr : (Real.sqrt q)⁻¹ ^ 2 ≤ (Real.sqrt Q)⁻¹ ^ 2 :=
    pow_le_pow_left₀ (by positivity)
      (inv_anti₀ (Real.sqrt_pos.mpr hQ) (Real.sqrt_le_sqrt hQq)) 2
  have hmul : (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s * leafS G ς (weightM G ς) s ≤
      (Real.sqrt Q)⁻¹ ^ 2 * 2 ^ s * leafS G ς (weightM G ς) s :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hr (by positivity)) hS
  have hm0 : 0 ≤ (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s * leafS G ς (weightM G ς) s :=
    mul_nonneg (by positivity) hS
  exact div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith)

/-- The leaf factor `𝖿_ρ(s)` is nonincreasing in `q`. -/
theorem leafFrho_anti (G : OrientedGraph U) (ς : U → U → ℤ) {n : ℕ} {Q q : ℝ} (hQ : 0 < Q)
    (hQq : Q ≤ q) (hS1 : leafEhat G Q n < 1) (s : ℕ) :
    leafFrho G ς q n (leafEhat G q n) s ≤ leafFrho G ς Q n (leafEhat G Q n) s := by
  unfold leafFrho
  have he := leafEhat_anti G (n := n) hQ hQq
  have hes := leaf_coarseError_anti s (by positivity : (0 : ℝ) ≤ 2 * n) hQ hQq
  have he0 := coarseError_nonneg (q := q) (by positivity : (0 : ℝ) ≤ 2 * n) s
  have hS := leafS_nonneg G ς (weightRho G ς) (weightRho_nonneg G ς) s
  have hr : (Real.sqrt q)⁻¹ ^ 2 ≤ (Real.sqrt Q)⁻¹ ^ 2 :=
    pow_le_pow_left₀ (by positivity)
      (inv_anti₀ (Real.sqrt_pos.mpr hQ) (Real.sqrt_le_sqrt hQq)) 2
  have hmul : (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s * leafS G ς (weightRho G ς) s ≤
      (Real.sqrt Q)⁻¹ ^ 2 * 2 ^ s * leafS G ς (weightRho G ς) s :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hr (by positivity)) hS
  have hm0 : 0 ≤ (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s * leafS G ς (weightRho G ς) s :=
    mul_nonneg (by positivity) hS
  exact div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith)

theorem leafProdOf_anti (G : OrientedGraph U) (ς : U → U → ℤ) {n : ℕ} {Q q : ℝ} (hQ : 0 < Q)
    (hQq : Q ≤ q) (hS1 : leafEhat G Q n < 1) (V W Cx Cz : Finset U)
    (sUx sCz sUz sCx : U → ℕ) :
    leafProdOf G ς q n (leafEhat G q n) V W Cx Cz sUx sCz sUz sCx ≤
      leafProdOf G ς Q n (leafEhat G Q n) V W Cx Cz sUx sCz sUz sCx := by
  have hq1 : leafEhat G q n < 1 := lt_of_le_of_lt (leafEhat_anti G hQ hQq) hS1
  unfold leafProdOf
  have a1 := prod_le_prod₀ (s := univ \ (V ∪ Cx))
    (fun u _ => leafFm_nonneg G ς hq1 (q := q) (n := n) (sUx u))
    (fun u _ => leafFm_anti G ς hQ hQq hS1 (sUx u))
  have a2 := prod_le_prod₀ (s := Cz)
    (fun b _ => leafFrho_nonneg G ς hq1 (q := q) (n := n) (sCz b))
    (fun b _ => leafFrho_anti G ς hQ hQq hS1 (sCz b))
  have a3 := prod_le_prod₀ (s := univ \ (W ∪ Cz))
    (fun u _ => leafFm_nonneg G ς hq1 (q := q) (n := n) (sUz u))
    (fun u _ => leafFm_anti G ς hQ hQq hS1 (sUz u))
  have a4 := prod_le_prod₀ (s := Cx)
    (fun b _ => leafFrho_nonneg G ς hq1 (q := q) (n := n) (sCx b))
    (fun b _ => leafFrho_anti G ς hQ hQq hS1 (sCx b))
  have p1 := prod_nonneg fun u (_ : u ∈ univ \ (V ∪ Cx)) => leafFm_nonneg G ς hq1 (q := q)
    (n := n) (sUx u)
  have p2 := prod_nonneg fun b (_ : b ∈ Cz) => leafFrho_nonneg G ς hq1 (q := q) (n := n) (sCz b)
  have p3 := prod_nonneg fun u (_ : u ∈ univ \ (W ∪ Cz)) => leafFm_nonneg G ς hq1 (q := q)
    (n := n) (sUz u)
  have p4 := prod_nonneg fun b (_ : b ∈ Cx) => leafFrho_nonneg G ς hq1 (q := q) (n := n) (sCx b)
  have q1 := le_trans p1 a1
  have q2 := le_trans p2 a2
  have q3 := le_trans p3 a3
  exact mul_le_mul (mul_le_mul (mul_le_mul a1 a2 p2 q1) a3 p3 (mul_nonneg q1 q2)) a4 p4
    (mul_nonneg (mul_nonneg q1 q2) q3)

theorem rowsR_univ_anti (G : OrientedGraph U) {n : ℕ} {Q q : ℝ} (hQ : 0 < Q) (hQq : Q ≤ q)
    (hS1 : leafEhat G Q n < 1) : rowsR G q n univ ≤ rowsR G Q n univ := by
  unfold rowsR
  refine prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_)
  · have h0 := coarseError_nonneg (q := q) (Nat.cast_nonneg (α := ℝ) n) (rowsDeg0 G i)
    have h1 := (coarseError_le_leafEhat G q n i).trans_lt
      (lt_of_le_of_lt (leafEhat_anti G hQ hQq) hS1)
    exact div_nonneg (by linarith) (by linarith)
  · have h0 := coarseError_nonneg (q := q) (Nat.cast_nonneg (α := ℝ) n) (rowsDeg0 G i)
    have h1 := leaf_coarseError_anti (rowsDeg0 G i) (Nat.cast_nonneg (α := ℝ) n) hQ hQq
    have h2 := (coarseError_le_leafEhat G Q n i).trans_lt hS1
    exact div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith)

/-- The class coefficient is nonincreasing in `q` (proof of `cor:extraction-leaf`(b); the paper
uses `lem:majorant`, here the monotonicity is proved directly). -/
theorem leafCoef_anti (G : OrientedGraph U) (ς : U → U → ℤ) {n : ℕ} {Q q : ℝ} (hQ : 0 < Q)
    (hQq : Q ≤ q) (hS1 : leafEhat G Q n < 1) (Ex : Finset (U × U))
    (c : Finset (U × U) × Finset (U × U)) (R : LeafRecordData U) :
    leafCoef G ς q n Ex c R ≤ leafCoef G ς Q n Ex c R := by
  have he := leafEhat_anti G (n := n) hQ hQq
  have hq1 : leafEhat G q n < 1 := lt_of_le_of_lt he hS1
  have hP := leafProdOf_anti G ς hQ hQq hS1 (witV R.w) (witW R.w) R.Cx R.Cz
    (intS G R.ordX (Ex \ (c.1 ∪ c.2)))
    (coverRowS G R.Cz R.ordZ ((Ex \ (c.1 ∪ c.2)).filter (fun e => e.2 ∈ R.Cz)))
    (intS G R.ordZ ((Ex \ (c.1 ∪ c.2)).image Prod.swap))
    (coverRowS G R.Cx R.ordX (((Ex \ (c.1 ∪ c.2)).image Prod.swap).filter
      (fun e => e.2 ∈ R.Cx)))
  have hR := rowsR_univ_anti G hQ hQq hS1
  have hR0 : 0 ≤ rowsR G q n univ :=
    le_trans zero_le_one (rowsR_univ_ge_one G (fun i => (coarseError_le_leafEhat G q n i).trans_lt
      hq1))
  unfold leafCoef
  have hsq := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hP
    (by positivity : (0 : ℝ) ≤ 2 ^ (recordExp G (Ex \ (c.1 ∪ c.2)) (witV R.w) (witW R.w) R.ordX
      R.ordZ + 2 * twoCycleCount (witnessIdx c.1 R.w))))
  have hR2 : rowsR G q n univ ^ 2 ≤ rowsR G Q n univ ^ 2 := pow_le_pow_left₀ hR0 hR 2
  have hnum := mul_le_mul hsq hR2 (sq_nonneg _) (Real.sqrt_nonneg _)
  refine div_le_div₀ (mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)) hnum
    (pow_pos (by linarith) _) (pow_le_pow_left₀ (by linarith) (by linarith) _)

end Partition

section PartitionBound

variable {p : ℕ} [Fact p.Prime]
variable {U : Type*} [Fintype U] [DecidableEq U]

theorem leaf_expect_finset_sum {Ω ι : Type*} [Fintype Ω] (μ : Sarkozy.FiniteLaw Ω) (s : Finset ι)
    (g : ι → Ω → ℝ) : μ.expect (fun ω => ∑ c ∈ s, g c ω) = ∑ c ∈ s, μ.expect (g c) := by
  unfold Sarkozy.FiniteLaw.expect
  simp_rw [mul_sum]
  exact sum_comm

/-- **`cor:extraction-leaf`(b)**: for an exact partition `𝔓` of the nonstar subsets of `E_×`
into classes with fixed records (`LeafRecordData.Valid`: witness digraphs with strongly
connected components of at most two vertices), if `ê(Q) = e_{Δ⁺}(Q, n) < 1` at a real `Q > 0`
(the part of (S1) at `Q` used), then for every prime `p ≥ Q`
`|⟨f, T_ns h⟩_μ| ≤ ∑_{𝒞 ∈ 𝔓} p^{-k_𝒞/2} C_𝒞(Q) ‖f‖_μ ‖h‖_μ`, `C_𝒞(Q)` the coefficient
`leafCoef` of the class evaluated at `r = Q^{-1/2}`; `∑_k C_k(Q) p^{-k/2}` is this sum grouped by
the witness size (`extraction_leaf_partition_grouped`). The four-cycle bound
(`cor:dl:normalized`(a)) is the hypothesis `FourCycleBound p`. -/
theorem extraction_leaf_partition (hW : WeilBound (ZMod p)) (hp2 : p ≠ 2)
    (h4 : FourCycleBound p) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings (ZMod p) G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n)
    (Ex : Finset (U × U)) (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0)
    (𝔓 : Finset (Finset (U × U) × Finset (U × U)))
    (h𝔓 : IsExactPartition Ex 𝔓 (nonstars Ex))
    (rec : Finset (U × U) × Finset (U × U) → LeafRecordData U)
    (hrec : ∀ c ∈ 𝔓, (rec c).Valid Ex c) {Q : ℝ} (hQ : 0 < Q) (hQp : Q ≤ p)
    (hS1 : leafEhat G Q n < 1) (f h : (U → ZMod p) → ℝ) :
    |(graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
        (∑ S ∈ nonstars Ex, ∏ e ∈ S, chiPair ς e x x') * h x'))| ≤
      (∑ c ∈ 𝔓, (Real.sqrt p)⁻¹ ^ (rec c).k * leafCoef G ς Q n Ex c (rec c)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by
  set μ := graphLaw G hne
  -- the nonstar sum over the partition
  have hsplit : ∀ x x' : U → ZMod p, ∑ S ∈ nonstars Ex, ∏ e ∈ S, chiPair ς e x x' =
      ∑ c ∈ 𝔓, ∑ S ∈ cls Ex c.1 c.2, ∏ e ∈ S, chiPair ς e x x' := by
    intro x x'
    rw [← h𝔓.2.2, sum_biUnion h𝔓.2.1]
  have hlin : μ.expect (fun x => f x * μ.expect (fun x' =>
      (∑ S ∈ nonstars Ex, ∏ e ∈ S, chiPair ς e x x') * h x')) =
      ∑ c ∈ 𝔓, μ.expect (fun x => f x * μ.expect (fun x' =>
        (∑ S ∈ cls Ex c.1 c.2, ∏ e ∈ S, chiPair ς e x x') * h x')) := by
    simp_rw [hsplit, sum_mul]
    rw [← leaf_expect_finset_sum]
    refine μ.expect_congr fun x => ?_
    rw [leaf_expect_finset_sum, mul_sum]
  rw [hlin]
  have hpQ : (0 : ℝ) < p := lt_of_lt_of_le hQ hQp
  have hp1 : leafEhat G p n < 1 := lt_of_le_of_lt (leafEhat_anti G hQ hQp) hS1
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [sum_mul, sum_mul]
  refine sum_le_sum fun c hc => ?_
  have hv := hrec c hc
  have hcls : IsClassDatum Ex (c.1, c.2) := h𝔓.1 c hc
  have hb := extraction_leaf_twoCycles hW hp2 h4 G ς hς hanti hne hn
    (coarseError_le_leafEhat G p n) hp1 Ex c.1 c.2 hEx hcls (rec c).w hv.witness hv.twoCycles
    (rec c).Cx (rec c).Cz hv.cover (rec c).ordX (rec c).ordZ hv.injX hv.injZ hv.segX0 hv.segZ0
    hv.segX1 hv.segZ1 f h
  refine hb.trans ?_
  have hco := leafCoef_anti G ς hQ hQp hS1 Ex c (rec c)
  unfold leafCoef at hco
  have hX : 0 ≤ (Real.sqrt p)⁻¹ ^ (rec c).k * Real.sqrt (μ.expect (fun x => f x ^ 2)) *
      Real.sqrt (μ.expect (fun x => h x ^ 2)) := by positivity
  calc (Real.sqrt p)⁻¹ ^ (rec c).k *
        Real.sqrt (2 ^ (recordExp G (Ex \ (c.1 ∪ c.2)) (witV (rec c).w) (witW (rec c).w)
            (rec c).ordX (rec c).ordZ + 2 * twoCycleCount (witnessIdx c.1 (rec c).w)) *
          leafProd G ς p n (leafEhat G p n) (Ex \ (c.1 ∪ c.2)) (witV (rec c).w) (witW (rec c).w)
            (rec c).Cx (rec c).Cz (rec c).ordX (rec c).ordZ) *
        rowsR G p n univ ^ 2 / (1 - leafEhat G p n) ^ (rec c).k *
        Real.sqrt (μ.expect (fun x => f x ^ 2)) * Real.sqrt (μ.expect (fun x => h x ^ 2))
      = ((Real.sqrt p)⁻¹ ^ (rec c).k * Real.sqrt (μ.expect (fun x => f x ^ 2)) *
          Real.sqrt (μ.expect (fun x => h x ^ 2))) *
        (Real.sqrt (2 ^ (recordExp G (Ex \ (c.1 ∪ c.2)) (witV (rec c).w) (witW (rec c).w)
            (rec c).ordX (rec c).ordZ + 2 * twoCycleCount (witnessIdx c.1 (rec c).w)) *
          leafProd G ς p n (leafEhat G p n) (Ex \ (c.1 ∪ c.2)) (witV (rec c).w) (witW (rec c).w)
            (rec c).Cx (rec c).Cz (rec c).ordX (rec c).ordZ) *
        rowsR G p n univ ^ 2 / (1 - leafEhat G p n) ^ (rec c).k) := by ring
    _ ≤ ((Real.sqrt p)⁻¹ ^ (rec c).k * Real.sqrt (μ.expect (fun x => f x ^ 2)) *
          Real.sqrt (μ.expect (fun x => h x ^ 2))) * leafCoef G ς Q n Ex c (rec c) :=
        mul_le_mul_of_nonneg_left hco hX
    _ = _ := by ring

/-- **`cor:extraction-leaf`(b), grouped by the witness size**:
`|⟨f, T_ns h⟩_μ| ≤ ∑_k C_k(Q) p^{-k/2} ‖f‖_μ ‖h‖_μ`, `C_k(Q)` the sum of the coefficients of the
classes of witness size `k`. -/
theorem extraction_leaf_partition_grouped (hW : WeilBound (ZMod p)) (hp2 : p ≠ 2)
    (h4 : FourCycleBound p) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings (ZMod p) G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n)
    (Ex : Finset (U × U)) (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0)
    (𝔓 : Finset (Finset (U × U) × Finset (U × U)))
    (h𝔓 : IsExactPartition Ex 𝔓 (nonstars Ex))
    (rec : Finset (U × U) × Finset (U × U) → LeafRecordData U)
    (hrec : ∀ c ∈ 𝔓, (rec c).Valid Ex c) {Q : ℝ} (hQ : 0 < Q) (hQp : Q ≤ p)
    (hS1 : leafEhat G Q n < 1) (f h : (U → ZMod p) → ℝ) :
    |(graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
        (∑ S ∈ nonstars Ex, ∏ e ∈ S, chiPair ς e x x') * h x'))| ≤
      (∑ k ∈ 𝔓.image (fun c => (rec c).k),
          (∑ c ∈ 𝔓.filter (fun c => (rec c).k = k), leafCoef G ς Q n Ex c (rec c)) *
            (Real.sqrt p)⁻¹ ^ k) *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by
  refine (extraction_leaf_partition hW hp2 h4 G ς hς hanti hne hn Ex hEx 𝔓 h𝔓 rec hrec hQ hQp
    hS1 f h).trans (le_of_eq ?_)
  congr 2
  rw [← sum_fiberwise_of_maps_to (g := fun c => (rec c).k) (t := 𝔓.image (fun c => (rec c).k))
    (fun c hc => mem_image_of_mem _ hc)]
  refine sum_congr rfl fun k _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun c hc => ?_
  rw [(mem_filter.mp hc).2]
  ring

end PartitionBound

/-! ## Stored numbers in the coefficients, and the operator-norm form -/

section StoredPartition

variable {p : ℕ} [Fact p.Prime]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- Stored numbers `s'_v` for the four sets `U_x`, `C_z`, `U_z`, `C_x` of a record. -/
structure LeafStored (U : Type*) where
  /-- on `U_x` -/
  sUx : U → ℕ
  /-- on `C_z` -/
  sCz : U → ℕ
  /-- on `U_z` -/
  sUz : U → ℕ
  /-- on `C_x` -/
  sCx : U → ℕ

/-- The stored numbers dominate the counts `s_v` of the record and are at most `Δ`. -/
def LeafStored.Dominates (st : LeafStored U) (G : OrientedGraph U) (ς : U → U → ℤ)
    (Ex : Finset (U × U)) (c : Finset (U × U) × Finset (U × U)) (R : LeafRecordData U) :
    Prop :=
  (∀ u ∈ univ \ (witV R.w ∪ R.Cx),
      intS G R.ordX (Ex \ (c.1 ∪ c.2)) u ≤ st.sUx u ∧ st.sUx u ≤ leafDelta G ς) ∧
    (∀ b ∈ R.Cz, coverRowS G R.Cz R.ordZ ((Ex \ (c.1 ∪ c.2)).filter (fun e => e.2 ∈ R.Cz)) b ≤
      st.sCz b ∧ st.sCz b ≤ leafDelta G ς) ∧
    (∀ u ∈ univ \ (witW R.w ∪ R.Cz),
      intS G R.ordZ ((Ex \ (c.1 ∪ c.2)).image Prod.swap) u ≤ st.sUz u ∧
        st.sUz u ≤ leafDelta G ς) ∧
    (∀ b ∈ R.Cx, coverRowS G R.Cx R.ordX
        (((Ex \ (c.1 ∪ c.2)).image Prod.swap).filter (fun e => e.2 ∈ R.Cx)) b ≤ st.sCx b ∧
      st.sCx b ≤ leafDelta G ς)

/-- The coefficient of a class computed from stored numbers (`cor:extraction-leaf`(b)). -/
noncomputable def leafCoefStored (G : OrientedGraph U) (ς : U → U → ℤ) (q : ℝ) (n : ℕ)
    (Ex : Finset (U × U)) (c : Finset (U × U) × Finset (U × U)) (R : LeafRecordData U)
    (st : LeafStored U) : ℝ :=
  Real.sqrt (2 ^ (recordExp G (Ex \ (c.1 ∪ c.2)) (witV R.w) (witW R.w) R.ordX R.ordZ +
      2 * twoCycleCount (witnessIdx c.1 R.w)) *
    leafProdOf G ς q n (leafEhat G q n) (witV R.w) (witW R.w) R.Cx R.Cz st.sUx st.sCz st.sUz
      st.sCx) * rowsR G q n univ ^ 2 / (1 - leafEhat G q n) ^ R.k

theorem leafCoef_le_stored (G : OrientedGraph U) (ς : U → U → ℤ)
    (hm : LeafMonotone G ς (weightM G ς)) (hρ : LeafMonotone G ς (weightRho G ς)) {q : ℝ}
    {n : ℕ} (hS1 : leafEhat G q n < 1) (Ex : Finset (U × U))
    (c : Finset (U × U) × Finset (U × U)) (R : LeafRecordData U) (st : LeafStored U)
    (hst : st.Dominates G ς Ex c R) :
    leafCoef G ς q n Ex c R ≤ leafCoefStored G ς q n Ex c R st := by
  unfold leafCoef leafCoefStored
  have hle := leafProdOf_mono G ς hm hρ hS1 (q := q) (n := n) (witV R.w) (witW R.w) R.Cx R.Cz
    _ _ _ _ st.sUx st.sCz st.sUz st.sCx hst.1 hst.2.1 hst.2.2.1 hst.2.2.2
  have hsq := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hle
    (by positivity : (0 : ℝ) ≤ 2 ^ (recordExp G (Ex \ (c.1 ∪ c.2)) (witV R.w) (witW R.w) R.ordX
      R.ordZ + 2 * twoCycleCount (witnessIdx c.1 R.w))))
  have h1e : 0 < 1 - leafEhat G q n := by linarith
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)

/-- **`cor:extraction-leaf`(b) with stored numbers**: under the monotone-factor condition
`eq:monotone-signature`, the bound of `extraction_leaf_partition` holds with the coefficients
computed from stored numbers `s'_v ∈ [s_v, Δ]`. -/
theorem extraction_leaf_partition_stored (hW : WeilBound (ZMod p)) (hp2 : p ≠ 2)
    (h4 : FourCycleBound p) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings (ZMod p) G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n)
    (Ex : Finset (U × U)) (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0)
    (𝔓 : Finset (Finset (U × U) × Finset (U × U)))
    (h𝔓 : IsExactPartition Ex 𝔓 (nonstars Ex))
    (rec : Finset (U × U) × Finset (U × U) → LeafRecordData U)
    (hrec : ∀ c ∈ 𝔓, (rec c).Valid Ex c)
    (hm : LeafMonotone G ς (weightM G ς)) (hρ : LeafMonotone G ς (weightRho G ς))
    (st : Finset (U × U) × Finset (U × U) → LeafStored U)
    (hst : ∀ c ∈ 𝔓, (st c).Dominates G ς Ex c (rec c)) {Q : ℝ} (hQ : 0 < Q) (hQp : Q ≤ p)
    (hS1 : leafEhat G Q n < 1) (f h : (U → ZMod p) → ℝ) :
    |(graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
        (∑ S ∈ nonstars Ex, ∏ e ∈ S, chiPair ς e x x') * h x'))| ≤
      (∑ c ∈ 𝔓, (Real.sqrt p)⁻¹ ^ (rec c).k * leafCoefStored G ς Q n Ex c (rec c) (st c)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by
  refine (extraction_leaf_partition hW hp2 h4 G ς hς hanti hne hn Ex hEx 𝔓 h𝔓 rec hrec hQ hQp
    hS1 f h).trans ?_
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)
  exact sum_le_sum fun c hc => mul_le_mul_of_nonneg_left
    (leafCoef_le_stored G ς hm hρ hS1 Ex c (rec c) (st c) (hst c hc)) (by positivity)

/-- **`cor:extraction-leaf`(a), operator-norm form**: `‖T_𝒞 h‖_μ² ≤ B² ‖h‖_μ²`, i.e.
`‖T_𝒞‖ ≤ B = r^k 2^{ex*/2} R_full² (1 - ê)^{-k} ∏ 𝖿^{1/2}`, with
`(T_𝒞 h)(x) = E_{x'}[∑_{S ∈ 𝒞} χ_S(x, x') h(x')]` (from `grouped_extraction_norm`). -/
theorem extraction_leaf_twoCycles_norm (hW : WeilBound (ZMod p)) (hp2 : p ≠ 2)
    (h4 : FourCycleBound p)
    (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings (ZMod p) G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n) {ehat : ℝ}
    (hehat : ∀ i, coarseError (rowsDeg0 G i) p n ≤ ehat) (hehat1 : ehat < 1)
    (Ex P A : Finset (U × U)) (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0) (hcls : IsClassDatum Ex (P, A))
    {k : ℕ} (w : Fin k → U × U) (hw : IsWitness Ex P A w)
    (hcard : ∀ i, (twoCycleComponent (witnessIdx P w) i).card ≤ 2)
    (Cx Cz : Finset U) (hcov : IsCover Ex P A w Cx Cz) (ordX ordZ : U → ℕ)
    (hordX : Function.Injective ordX) (hordZ : Function.Injective ordZ)
    (hX0 : ∀ a ∈ Cx, ∀ b, b ∉ Cx → ordX a < ordX b)
    (hZ0 : ∀ a ∈ Cz, ∀ b, b ∉ Cz → ordZ a < ordZ b)
    (hX1 : ∀ a, a ∉ univ \ (witV w ∪ Cx) → ∀ b ∈ univ \ (witV w ∪ Cx), ordX a < ordX b)
    (hZ1 : ∀ a, a ∉ univ \ (witW w ∪ Cz) → ∀ b ∈ univ \ (witW w ∪ Cz), ordZ a < ordZ b)
    (h : (U → ZMod p) → ℝ) :
    (graphLaw G hne).expect (fun x => ((graphLaw G hne).expect (fun x' =>
        (∑ S ∈ cls Ex P A, ∏ e ∈ S, chiPair ς e x x') * h x')) ^ 2) ≤
      ((Real.sqrt p)⁻¹ ^ k *
        Real.sqrt (2 ^ (recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ +
            2 * twoCycleCount (witnessIdx P w)) *
          leafProd G ς p n ehat (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) *
        rowsR G p n univ ^ 2 / (1 - ehat) ^ k) ^ 2 *
        (graphLaw G hne).expect (fun x => h x ^ 2) := by
  have hςP := sign_pm_of_ne_zero hς (fun e he => hEx e (hcls.1 he))
  have hk := IsWitness.rectKer_opBound_twoCycles hw hp2 h4 ς hςP hcard
  have hker : Sarkozy.Influence.OpBound (injTuples (ZMod p) (witV w))
      (injTuples (ZMod p) (witW w)) (rectKer ς P (witV w) (witW w))
      (2 ^ twoCycleCount (witnessIdx P w) * Real.sqrt (Fintype.card (ZMod p)) ^ k) := by
    rw [ZMod.card]
    exact hk
  have hehat' : ∀ i, coarseError (rowsDeg0 G i) (Fintype.card (ZMod p)) n ≤ ehat := by
    rw [ZMod.card]
    exact hehat
  have hN := grouped_extraction_norm hW G ς hς hanti hne hn hehat' hehat1 Ex P A hEx hcls w hw
    Cx Cz hcov ordX ordZ hordX hordZ hX0 hZ0 hX1 hZ1 (by positivity) hker h
  rw [ZMod.card] at hN
  refine hN.trans (mul_le_mul_of_nonneg_right ?_ ((graphLaw G hne).second_moment_nonneg h))
  -- the constant
  have hFr' : ∀ e ∈ Ex \ (P ∪ A), e.1 ∈ Cx ∨ e.2 ∈ Cz := by
    intro e he
    refine hcov.cover e (mem_union_right _ he) fun hr => ?_
    have := hw.decided e (mem_sdiff.mp he).1 hr.1 hr.2
    exact (mem_sdiff.mp he).2 (mem_union.mpr this)
  have hPF := recordFactor_le_leafProd G ς hanti hehat hehat1 (Ex \ (P ∪ A))
    (fun e he => hEx e (mem_sdiff.mp he).1) (witV w) (witW w) Cx Cz
    (fun e he h1 => (hFr' e he).resolve_left h1) (fun e he h2 => (hFr' e he).resolve_right h2)
    ordX ordZ
  have hR : 1 ≤ rowsR G p n univ ^ 2 := by
    have := rowsR_univ_ge_one G (q := (p : ℝ)) (n := n) (fun i => lt_of_le_of_lt (hehat i) hehat1)
    nlinarith
  have h1e : 0 < 1 - ehat := by linarith
  have e : (2 : ℝ) ^ (recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ +
        2 * twoCycleCount (witnessIdx P w)) *
        leafProd G ς p n ehat (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ =
      ((2 : ℝ) ^ twoCycleCount (witnessIdx P w)) ^ 2 *
        (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
          leafProd G ς p n ehat (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) := by
    rw [pow_add, pow_mul']
    ring
  rw [e, Real.sqrt_mul (sq_nonneg ((2 : ℝ) ^ twoCycleCount (witnessIdx P w))),
    Real.sqrt_sq (by positivity)]
  have hsq : Real.sqrt (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
        recordFactor G ς p n (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) ≤
      Real.sqrt (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
        leafProd G ς p n ehat (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) *
        rowsR G p n univ ^ 2 :=
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hPF (by positivity))).trans
      (le_mul_of_one_le_right (Real.sqrt_nonneg _) hR)
  have hB0 : 0 ≤ 2 ^ twoCycleCount (witnessIdx P w) * (Real.sqrt p)⁻¹ ^ k *
      Real.sqrt (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
        recordFactor G ς p n (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) /
      (1 - ehat) ^ k := by positivity
  refine pow_le_pow_left₀ hB0 ?_ 2
  have hc : 0 ≤ 2 ^ twoCycleCount (witnessIdx P w) * (Real.sqrt p)⁻¹ ^ k / (1 - ehat) ^ k := by
    positivity
  calc 2 ^ twoCycleCount (witnessIdx P w) * (Real.sqrt p)⁻¹ ^ k *
        Real.sqrt (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
          recordFactor G ς p n (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) / (1 - ehat) ^ k
      = (2 ^ twoCycleCount (witnessIdx P w) * (Real.sqrt p)⁻¹ ^ k / (1 - ehat) ^ k) *
          Real.sqrt (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
            recordFactor G ς p n (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) := by ring
    _ ≤ (2 ^ twoCycleCount (witnessIdx P w) * (Real.sqrt p)⁻¹ ^ k / (1 - ehat) ^ k) *
          (Real.sqrt (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
            leafProd G ς p n ehat (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) *
          rowsR G p n univ ^ 2) := mul_le_mul_of_nonneg_left hsq hc
    _ = _ := by ring

end StoredPartition

end Sarkozy.ExtractionK
