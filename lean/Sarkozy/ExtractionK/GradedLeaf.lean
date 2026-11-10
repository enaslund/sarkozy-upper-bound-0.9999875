module

public import Sarkozy.ExtractionK.GradedExtraction
public import Sarkozy.ExtractionK.Leaf

@[expose] public section

/-!
# Graded errors, III: `cor:extraction-leaf`(a) for an error function

`paper/sections/16_extraction.tex`, `cor:extraction-leaf`(a) with the paragraph *Graded errors*
of `subsec:extraction:partition`: the leaf factors `𝖿_m`, `𝖿_ρ` of `eq:leaf-factors`
(`grLeafFm`, `grLeafFrho`, `grLeafProd`) and `R_full` (`grRowsR`) with an error function `e`
(`GrErr`), the comparisons `F_v ≤ 𝖿(s_v)` (`gr_intF_le_leafFm`, `gr_coverRowF_le_leafFrho`,
`gr_recordFactor_le_leafProd`; the proofs of `Leaf.lean`, which use the error only through
`e_{t_v} ≤ ê`), `gr_extraction_leaf` (any `c_ker`), `gr_extraction_leaf_twoCycles` (`𝔽_p`,
`c_ker = 2^β`, hypothesis `FourCycleBound p`), and **`gr_extraction_leaf_twoCycles_graded`**: the
graded instance `e = e^-_t(n')` (`grGraded`).
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction


section GrLeafDefs

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- `𝖿_m(s) = (1 + e_s(n) + r² 2^s 𝖲_m(s))/(1 - ê)` (`eq:leaf-factors`) for an error function `e`. -/
noncomputable def grLeafFm (G : OrientedGraph U) (ς : U → U → ℤ) (e : ℕ → ℝ → ℝ) (q : ℝ) (n : ℕ)
    (ehat : ℝ) (s : ℕ) : ℝ :=
  (1 + e s n + (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s * leafS G ς (weightM G ς) s) / (1 - ehat)

/-- `𝖿_ρ(s) = (1 + e_s(2n) + r² 2^s 𝖲_ρ(s))/(1 - ê)` (`eq:leaf-factors`) for an error function. -/
noncomputable def grLeafFrho (G : OrientedGraph U) (ς : U → U → ℤ) (e : ℕ → ℝ → ℝ) (q : ℝ)
    (n : ℕ) (ehat : ℝ) (s : ℕ) : ℝ :=
  (1 + e s (2 * n) + (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s * leafS G ς (weightRho G ς) s) / (1 - ehat)

/-- The product of the leaf factors with given numbers `s_v` (error function `e`). -/
noncomputable def grLeafProdOf (G : OrientedGraph U) (ς : U → U → ℤ) (e : ℕ → ℝ → ℝ) (q : ℝ)
    (n : ℕ) (ehat : ℝ) (V W Cx Cz : Finset U) (sUx sCz sUz sCx : U → ℕ) : ℝ :=
  (∏ u ∈ univ \ (V ∪ Cx), grLeafFm G ς e q n ehat (sUx u)) *
    (∏ b ∈ Cz, grLeafFrho G ς e q n ehat (sCz b)) *
    (∏ u ∈ univ \ (W ∪ Cz), grLeafFm G ς e q n ehat (sUz u)) *
    ∏ b ∈ Cx, grLeafFrho G ς e q n ehat (sCx b)

/-- The product of the leaf factors of a record with its own counts (error function `e`). -/
noncomputable def grLeafProd (G : OrientedGraph U) (ς : U → U → ℤ) (e : ℕ → ℝ → ℝ) (q : ℝ)
    (n : ℕ) (ehat : ℝ) (Fr : Finset (U × U)) (V W Cx Cz : Finset U) (ordX ordZ : U → ℕ) : ℝ :=
  grLeafProdOf G ς e q n ehat V W Cx Cz (intS G ordX Fr)
    (coverRowS G Cz ordZ (Fr.filter (fun e => e.2 ∈ Cz)))
    (intS G ordZ (Fr.image Prod.swap))
    (coverRowS G Cx ordX ((Fr.image Prod.swap).filter (fun e => e.2 ∈ Cx)))

/-- `R_Y = ∏_{i ∈ Y} (1 + e_{d⁰_i}(n))/(1 - e_{d⁰_i}(n))` for an error function `e`. -/
noncomputable def grRowsR (G : OrientedGraph U) (e : ℕ → ℝ → ℝ) (n : ℕ) (Y : Finset U) : ℝ :=
  ∏ i ∈ Y, (1 + e (rowsDeg0 G i) n) / (1 - e (rowsDeg0 G i) n)

theorem gr_rowsR_ge_one (G : OrientedGraph U) {q : ℝ} {n : ℕ} {e : ℕ → ℝ → ℝ}
    (he : GrErr q n e) (h : ∀ i, e (rowsDeg0 G i) n < 1) : 1 ≤ grRowsR G e n univ := by
  unfold grRowsR
  refine one_le_prod₀ fun i _ => ?_
  have h0 := he.nonneg (rowsDeg0 G i) n (Nat.cast_nonneg n)
  have h1 := h i
  rw [one_le_div (by linarith)]
  linarith

end GrLeafDefs

section GrCompare

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- `F_u ≤ 𝖿_m(s_u)` for an integrated vertex `u` (proof of `cor:extraction-leaf`(a)): its free
partners `H_u` lie in the cover `C` of the other copy and in `N(u)` (support symmetry), so the
special sum is at most `∑_{b ∈ U⁺} w^m_{ub} - ½ σ^m_u(s_u) ≤ S_m(s_u)`, as
`|H_u| = s_u - t_u ≥ h⁰_u(s_u)` and `d_u ≥ s_u`; and `1 - e_{t_u}(q, n) ≥ 1 - ê`. -/
theorem gr_intF_le_leafFm (G : OrientedGraph U) (ς : U → U → ℤ)
    (hsymm : ∀ j k, ς j k ≠ 0 → ς k j ≠ 0) {q : ℝ} {n : ℕ} {e : ℕ → ℝ → ℝ} {ehat : ℝ}
    (he : GrErr q n e) (hehat : ∀ i, e (rowsDeg0 G i) n ≤ ehat) (hehat1 : ehat < 1)
    (ord : U → ℕ) (Fr : Finset (U × U)) (hFr : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) (C : Finset U)
    (u : U) (hHC : intH Fr u ⊆ C) :
    grIntF G ς e q n ord Fr C u ≤ grLeafFm G ς e q n ehat (intS G ord Fr u) := by
  set s := intS G ord Fr u with hs
  set t := ordT G ord u
  have htd : t ≤ rowsDeg0 G u := ordT_le_deg G ord u
  have het : e t n ≤ ehat := gr_err_ordT_le G he hehat ord u
  have he0 := he.nonneg s n (Nat.cast_nonneg n)
  have h1e : 0 < 1 - ehat := by linarith
  have h1t : 0 < 1 - e t n := by linarith
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
  unfold grIntF grIntNum grLeafFm
  have hnum : 0 ≤ 1 + e s n +
      (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s * ∑ b ∈ C, (2 : ℝ) ^ intExp G ς Fr u b :=
    add_nonneg (by linarith) (mul_nonneg (by positivity) (sum_nonneg fun b _ => by positivity))
  calc (1 + e s n + (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s *
          ∑ b ∈ C, (2 : ℝ) ^ intExp G ς Fr u b) / (1 - e t n)
      ≤ (1 + e s n + (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s *
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
theorem gr_coverRowF_le_leafFrho (G : OrientedGraph U) (ς : U → U → ℤ) {q : ℝ} {n : ℕ} {e : ℕ → ℝ → ℝ}
    {ehat : ℝ} (he : GrErr q n e) (hehat : ∀ i, e (rowsDeg0 G i) n ≤ ehat) (hehat1 : ehat < 1)
    (C : Finset U) (ord : U → ℕ) (H : Finset (U × U)) (hH : ∀ e ∈ H, ς e.1 e.2 ≠ 0) (b : U) :
    grCoverF G ς e q n C ord H b ≤ grLeafFrho G ς e q n ehat (coverRowS G C ord H b) := by
  set s := coverRowS G C ord H b with hs
  set t := coverRowT G C ord b
  have htd : t ≤ rowsDeg0 G b := coverRow_nbrCount_le G _ b
  have het : e t n ≤ ehat :=
    (he.mono n (Nat.cast_nonneg n) _ _ htd).trans (hehat b)
  have he0 := he.nonneg s (2 * n) (by positivity)
  have h1e : 0 < 1 - ehat := by linarith
  have h1t : 0 < 1 - e t n := by linarith
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
  unfold grCoverF grLeafFrho
  have hnum : 0 ≤ 1 + e s (2 * n) +
      (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s * ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b :=
    add_nonneg (by linarith) (mul_nonneg (by positivity) (sum_nonneg fun j _ => by positivity))
  calc (1 + e s (2 * n) + (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s *
          ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b) / (1 - e t n)
      ≤ (1 + e s (2 * n) + (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s *
          ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b) / (1 - ehat) :=
        div_le_div_of_nonneg_left hnum h1e (by linarith)
    _ ≤ _ := by
        refine div_le_div_of_nonneg_right ?_ h1e.le
        have : (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s * ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b ≤
            (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s * leafS G ς (weightRho G ς) s :=
          mul_le_mul_of_nonneg_left hsp (by positivity)
        linarith

theorem gr_intF_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) {q : ℝ} {n : ℕ} {e : ℕ → ℝ → ℝ} {ehat : ℝ}
    (he : GrErr q n e) (hehat : ∀ i, e (rowsDeg0 G i) n ≤ ehat) (hehat1 : ehat < 1) (ord : U → ℕ)
    (Fr : Finset (U × U)) (C : Finset U) (u : U) : 0 ≤ grIntF G ς e q n ord Fr C u := by
  unfold grIntF grIntNum
  have het := gr_err_ordT_le G he hehat ord u
  have he0 := he.nonneg (intS G ord Fr u) n (Nat.cast_nonneg n)
  refine div_nonneg (add_nonneg (by linarith) (mul_nonneg (by positivity)
    (sum_nonneg fun b _ => by positivity))) (by linarith)

theorem gr_coverRowF_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) {q : ℝ} {n : ℕ} {e : ℕ → ℝ → ℝ} {ehat : ℝ}
    (he : GrErr q n e) (hehat : ∀ i, e (rowsDeg0 G i) n ≤ ehat) (hehat1 : ehat < 1) (C : Finset U)
    (ord : U → ℕ) (H : Finset (U × U)) (b : U) : 0 ≤ grCoverF G ς e q n C ord H b := by
  unfold grCoverF
  have het : e (coverRowT G C ord b) n ≤ ehat :=
    (he.mono n (Nat.cast_nonneg n) _ _ (coverRow_nbrCount_le G _ b)).trans (hehat b)
  have he0 := he.nonneg (coverRowS G C ord H b) (2 * n) (by positivity)
  refine div_nonneg (add_nonneg (by linarith) (mul_nonneg (by positivity)
    (sum_nonneg fun b _ => by positivity))) (by linarith)

/-- `∏_v F_v ≤ ∏_{u ∈ U_x ∪ U_z} 𝖿_m(s_u) ∏_{b ∈ C_x ∪ C_z} 𝖿_ρ(s_b)` (proof of
`cor:extraction-leaf`(a)); `hFr1`, `hFr2` are the cover condition (VC_k) for the free pairs. -/
theorem gr_recordFactor_le_leafProd (G : OrientedGraph U) (ς : U → U → ℤ)
    (hanti : ∀ j k, ς k j = -ς j k) {q : ℝ} {n : ℕ} {e : ℕ → ℝ → ℝ} {ehat : ℝ}
    (he : GrErr q n e) (hehat : ∀ i, e (rowsDeg0 G i) n ≤ ehat) (hehat1 : ehat < 1)
    (Fr : Finset (U × U)) (hFr : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) (V W Cx Cz : Finset U)
    (hFr1 : ∀ e ∈ Fr, e.1 ∉ Cx → e.2 ∈ Cz) (hFr2 : ∀ e ∈ Fr, e.2 ∉ Cz → e.1 ∈ Cx)
    (ordX ordZ : U → ℕ) :
    grRecordFactor G ς e q n Fr V W Cx Cz ordX ordZ ≤ grLeafProd G ς e q n ehat Fr V W Cx Cz ordX ordZ := by
  have hsymm : ∀ j k, ς j k ≠ 0 → ς k j ≠ 0 := fun j k h => by
    rw [hanti j k]
    exact neg_ne_zero.mpr h
  have hFrT : ∀ e ∈ Fr.image Prod.swap, ς e.1 e.2 ≠ 0 := by
    intro e he
    obtain ⟨e₀, he₀, rfl⟩ := mem_image.mp he
    exact hsymm _ _ (hFr e₀ he₀)
  have h1 : ∏ u ∈ univ \ (V ∪ Cx), grIntF G ς e q n ordX Fr Cz u ≤
      ∏ u ∈ univ \ (V ∪ Cx), grLeafFm G ς e q n ehat (intS G ordX Fr u) := by
    refine prod_le_prod₀ (fun u _ => gr_intF_nonneg G ς he hehat hehat1 ordX Fr Cz u) fun u hu => ?_
    refine gr_intF_le_leafFm G ς hsymm he hehat hehat1 ordX Fr hFr Cz u fun b hb => ?_
    simp only [intH, mem_filter, mem_univ, true_and] at hb
    have hu' : u ∉ Cx := by
      simp only [mem_sdiff, mem_univ, true_and, mem_union, not_or] at hu
      exact hu.2
    exact hFr1 (u, b) hb hu'
  have h2 : ∏ b ∈ Cz, grCoverF G ς e q n Cz ordZ (Fr.filter (fun e => e.2 ∈ Cz)) b ≤
      ∏ b ∈ Cz, grLeafFrho G ς e q n ehat (coverRowS G Cz ordZ (Fr.filter (fun e => e.2 ∈ Cz)) b) :=
    prod_le_prod₀ (fun b _ => gr_coverRowF_nonneg G ς he hehat hehat1 _ _ _ b) fun b _ =>
      gr_coverRowF_le_leafFrho G ς he hehat hehat1 Cz ordZ _ (fun e he => hFr e (mem_filter.mp he).1) b
  have h3 : ∏ u ∈ univ \ (W ∪ Cz), grIntF G ς e q n ordZ (Fr.image Prod.swap) Cx u ≤
      ∏ u ∈ univ \ (W ∪ Cz), grLeafFm G ς e q n ehat (intS G ordZ (Fr.image Prod.swap) u) := by
    refine prod_le_prod₀ (fun u _ => gr_intF_nonneg G ς he hehat hehat1 ordZ _ Cx u) fun u hu => ?_
    refine gr_intF_le_leafFm G ς hsymm he hehat hehat1 ordZ _ hFrT Cx u fun a ha => ?_
    simp only [intH, mem_filter, mem_univ, true_and] at ha
    obtain ⟨e₀, he₀, he⟩ := mem_image.mp ha
    have hu' : u ∉ Cz := by
      simp only [mem_sdiff, mem_univ, true_and, mem_union, not_or] at hu
      exact hu.2
    have h1' : e₀.2 = u := by rw [← Prod.fst_swap, he]
    have h2' : e₀.1 = a := by rw [← Prod.snd_swap, he]
    rw [← h2']
    exact hFr2 e₀ he₀ (by rw [h1']; exact hu')
  have h4 : ∏ b ∈ Cx, grCoverF G ς e q n Cx ordX
        ((Fr.image Prod.swap).filter (fun e => e.2 ∈ Cx)) b ≤
      ∏ b ∈ Cx, grLeafFrho G ς e q n ehat
        (coverRowS G Cx ordX ((Fr.image Prod.swap).filter (fun e => e.2 ∈ Cx)) b) :=
    prod_le_prod₀ (fun b _ => gr_coverRowF_nonneg G ς he hehat hehat1 _ _ _ b) fun b _ =>
      gr_coverRowF_le_leafFrho G ς he hehat hehat1 Cx ordX _
        (fun e he => hFrT e (mem_filter.mp he).1) b
  unfold grRecordFactor grLeafProd grLeafProdOf
  have p1 := prod_nonneg fun u (_ : u ∈ univ \ (V ∪ Cx)) =>
    gr_intF_nonneg G ς he hehat hehat1 ordX Fr Cz u
  have p2 := prod_nonneg fun b (_ : b ∈ Cz) =>
    gr_coverRowF_nonneg G ς he hehat hehat1 Cz ordZ (Fr.filter (fun e => e.2 ∈ Cz)) b
  have p3 := prod_nonneg fun u (_ : u ∈ univ \ (W ∪ Cz)) =>
    gr_intF_nonneg G ς he hehat hehat1 ordZ (Fr.image Prod.swap) Cx u
  have p4 := prod_nonneg fun b (_ : b ∈ Cx) =>
    gr_coverRowF_nonneg G ς he hehat hehat1 Cx ordX ((Fr.image Prod.swap).filter (fun e => e.2 ∈ Cx)) b
  have q1 := le_trans p1 h1
  have q2 := le_trans p2 h2
  have q3 := le_trans p3 h3
  exact mul_le_mul (mul_le_mul (mul_le_mul h1 h2 p2 q1) h3 p3 (mul_nonneg q1 q2)) h4 p4
    (mul_nonneg (mul_nonneg q1 q2) q3)


end GrCompare

section GrLeafBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- **`cor:extraction-leaf`(a)**, with a kernel constant `c_ker` (the hypothesis of
`lem:matching:extractionk`): `|∑_{S ∈ 𝒞} ⟨f, T_S h⟩_μ| ≤ c_ker r^k 2^{ex(𝒞)/2} R_full²
(1 - ê)^{-k} ∏_{u ∈ U_x ∪ U_z} 𝖿_m(s_u)^{1/2} ∏_{b ∈ C_x ∪ C_z} 𝖿_ρ(s_b)^{1/2} ‖f‖_μ ‖h‖_μ`
(the product is `leafProd`, under one square root). The factor `R_full² ≥ 1` is kept as in the
paper; `grouped_extraction` gives the bound without it. -/
theorem gr_extraction_leaf (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n) (e : ℕ → ℝ → ℝ)
    (he : GrErr (Fintype.card F) n e) {ehat : ℝ}
    (hehat : ∀ i, e (rowsDeg0 G i) n ≤ ehat) (hehat1 : ehat < 1)
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
          grLeafProd G ς e (Fintype.card F) n ehat (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) *
        grRowsR G e n univ ^ 2 / (1 - ehat) ^ k *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by
  refine (gr_grouped_extraction hW G ς hς hanti hne hn e he hehat hehat1 Ex P A hEx hcls w hw Cx Cz hcov
    ordX ordZ hordX hordZ hX0 hZ0 hX1 hZ1 hcker hker f h).trans ?_
  -- the cover condition for the free pairs
  have hFr' : ∀ e ∈ Ex \ (P ∪ A), e.1 ∈ Cx ∨ e.2 ∈ Cz := by
    intro e he
    refine hcov.cover e (mem_union_right _ he) fun hr => ?_
    have := hw.decided e (mem_sdiff.mp he).1 hr.1 hr.2
    exact (mem_sdiff.mp he).2 (mem_union.mpr this)
  have hPF := gr_recordFactor_le_leafProd G ς hanti he hehat hehat1 (Ex \ (P ∪ A))
    (fun e he => hEx e (mem_sdiff.mp he).1) (witV w) (witW w) Cx Cz
    (fun e he h1 => (hFr' e he).resolve_left h1) (fun e he h2 => (hFr' e he).resolve_right h2)
    ordX ordZ
  have hR : 1 ≤ grRowsR G e n univ ^ 2 := by
    have := gr_rowsR_ge_one G he (fun i => lt_of_le_of_lt (hehat i) hehat1)
    nlinarith
  have h1e : 0 < 1 - ehat := by linarith
  have hsq : Real.sqrt (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
        grRecordFactor G ς e (Fintype.card F) n (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) ≤
      Real.sqrt (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
        grLeafProd G ς e (Fintype.card F) n ehat (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) *
        grRowsR G e n univ ^ 2 := by
    refine (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hPF (by positivity))).trans ?_
    exact le_mul_of_one_le_right (Real.sqrt_nonneg _) hR
  set X := cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k / (1 - ehat) ^ k *
    Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
    Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) with hX
  have hX0 : 0 ≤ X := by positivity
  calc cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        Real.sqrt (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
          grRecordFactor G ς e (Fintype.card F) n (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) /
        (1 - ehat) ^ k *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2))
      = X * Real.sqrt (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
          grRecordFactor G ς e (Fintype.card F) n (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) := by
        rw [hX]
        ring
    _ ≤ X * (Real.sqrt (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
          grLeafProd G ς e (Fintype.card F) n ehat (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) *
          grRowsR G e n univ ^ 2) := mul_le_mul_of_nonneg_left hsq hX0
    _ = _ := by
        rw [hX]
        ring

end GrLeafBound

section GrZModLeaf

variable {p : ℕ} [Fact p.Prime]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- **`cor:extraction-leaf`(a)**, the statement of the paper: for `F = 𝔽_p` and a witness
digraph whose strongly connected components have at most two vertices, `c_ker = 2^{β(𝒞)}`
(`lem:matching:kernel`(b), via `IsWitness.rectKer_opBound_twoCycles`; the four-cycle bound
`cor:dl:normalized`(a) is the hypothesis `FourCycleBound p`), and
`|∑_{S ∈ 𝒞} ⟨f, T_S h⟩_μ| ≤ r^k 2^{ex*(𝒞)/2} R_full² (1 - ê)^{-k}
∏_{u ∈ U_x ∪ U_z} 𝖿_m(s_u)^{1/2} ∏_{b ∈ C_x ∪ C_z} 𝖿_ρ(s_b)^{1/2} ‖f‖_μ ‖h‖_μ`,
`ex* = ex + 2β`, `r = p^{-1/2}`. -/
theorem gr_extraction_leaf_twoCycles (hW : WeilBound (ZMod p)) (hp2 : p ≠ 2)
    (h4 : FourCycleBound p)
    (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings (ZMod p) G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n)
    (e : ℕ → ℝ → ℝ) (he : GrErr p n e) {ehat : ℝ}
    (hehat : ∀ i, e (rowsDeg0 G i) n ≤ ehat) (hehat1 : ehat < 1)
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
          grLeafProd G ς e p n ehat (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) *
        grRowsR G e n univ ^ 2 / (1 - ehat) ^ k *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by
  have hςP := sign_pm_of_ne_zero hς (fun e he => hEx e (hcls.1 he))
  have hk := IsWitness.rectKer_opBound_twoCycles hw hp2 h4 ς hςP hcard
  have hker : Sarkozy.Influence.OpBound (injTuples (ZMod p) (witV w))
      (injTuples (ZMod p) (witW w)) (rectKer ς P (witV w) (witW w))
      (2 ^ twoCycleCount (witnessIdx P w) * Real.sqrt (Fintype.card (ZMod p)) ^ k) := by
    rw [ZMod.card]
    exact hk
  have he' : GrErr (Fintype.card (ZMod p)) n e := by
    rw [ZMod.card]
    exact he
  have hL := gr_extraction_leaf hW G ς hς hanti hne hn e he' hehat hehat1 Ex P A hEx hcls w hw Cx Cz
    hcov ordX ordZ hordX hordZ hX0 hZ0 hX1 hZ1 (by positivity) hker f h
  rw [ZMod.card] at hL
  refine hL.trans (le_of_eq ?_)
  have e : (2 : ℝ) ^ (recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ +
        2 * twoCycleCount (witnessIdx P w)) *
        grLeafProd G ς e p n ehat (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ =
      ((2 : ℝ) ^ twoCycleCount (witnessIdx P w)) ^ 2 *
        (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
          grLeafProd G ς e p n ehat (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) := by
    rw [pow_add, pow_mul']
    ring
  rw [e, Real.sqrt_mul (sq_nonneg ((2 : ℝ) ^ twoCycleCount (witnessIdx P w))),
    Real.sqrt_sq (by positivity)]
  ring


/-- **`cor:extraction-leaf`(a) with the graded error pair** (*Graded errors*,
`def:graphs:error-pair`): `extraction_leaf_twoCycles` with every count error replaced by
`e^-_t(n') = (𝔈_t + 2^t n')/p` (`grGraded`), in `𝖿_m`, `𝖿_ρ`, `R_full` and `ê`. Hypotheses:
`WeilBound (ZMod p)` and `FourCycleBound p` (`cor:dl:normalized`(a)). -/
theorem gr_extraction_leaf_twoCycles_graded (hW : WeilBound (ZMod p)) (hp2 : p ≠ 2)
    (h4 : FourCycleBound p)
    (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings (ZMod p) G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n) {ehat : ℝ}
    (hehat : ∀ i, grGraded p (rowsDeg0 G i) n ≤ ehat) (hehat1 : ehat < 1)
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
          grLeafProd G ς (grGraded p) p n ehat (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX
            ordZ) *
        grRowsR G (grGraded p) n univ ^ 2 / (1 - ehat) ^ k *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) :=
  gr_extraction_leaf_twoCycles hW hp2 h4 G ς hς hanti hne hn (grGraded p)
    (grErr_graded (by exact_mod_cast (Fact.out : p.Prime).pos) n) hehat hehat1 Ex P A hEx hcls w
    hw hcard Cx Cz hcov ordX ordZ hordX hordZ hX0 hZ0 hX1 hZ1 f h

end GrZModLeaf

end Sarkozy.ExtractionK
