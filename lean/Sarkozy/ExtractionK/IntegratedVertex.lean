module

public import Sarkozy.ExtractionK.Defs

@[expose] public section

/-!
# Grouped extraction, Step 6: the integrated vertices (`eq:extraction:mbound`)

`paper/sections/16_extraction.tex`, `lem:matching:extractionk`, Step 6 of the proof, with the
vertex factors `F_u` (`u ∈ U_x`) of `def:extraction:records` (`intNum`, `intF` in
`ExtractionK/Defs.lean`). Inputs: `lem:extraction-merged-count` (`merged_count_le_fintype'`),
the sequential summation of `lem:extraction-rows` (`coverRow_seq_upper`) and `extCount_univ`.

## Setting

As in `ExtractionK/Defs.lean`: a finite field `F` with `q` elements (`WeilBound F` is Weil's
theorem, the literature input of `lem:extension`), the half graph `G⁺` an oriented graph `G` on
`U`, cross signs `ς ∈ {0, ±1}`, the free pairs `Fr` (all with `ς ≠ 0`), the integrated set
`U_x` and the `x'`-cover `C_z`, with `H_u = {b : (u, b) ∈ Fr} ⊆ C_z` for `u ∈ U_x` (this is
(VC_k) for the free pairs at `u`, which lie outside the rectangle). The labels of the `x`-copy
are inserted along a global order `ord` (injective) in which `U_x` comes last, so
`t_u = ordT G ord u` counts the neighbours of `u` in `V ∪ C_x` and those earlier in `U_x`. The
labels `c'` of `C_z` are injective on `C_z`; the labels `x₀` of `X \ U_x = V ∪ C_x` are feasible
there.

## Results

* `integrated_extSum_le` is `eq:extraction:mbound` in summed form: the sum over the completions
  `x ∈ 𝓘⁺` of `x₀` of `Θ⁺_U(x, c') = ∏_{(u,b) ∈ Fr, u ∈ U_x} (1 + χ(ς_{ub}(c'_b - x_u)))` is at
  most `2^{κ^f} ∏_{u ∈ U_x} q 2^{-t_u} (1 + e_{s_u}(q, n) + r² 2^{s_u} ∑_{b ∈ C_z}
  2^{c^U(u,b) - [b ∈ H_u]})`. Dividing by the lower count `|𝒴| ≥ ∏_u q 2^{-t_u}(1 - e_{t_u})`
  gives the paper's `m(v, c, c') ≤ 2^{κ^f} ∏_u F_u`.
* `integrated_oneVertex` is the one-vertex bound of Step 6 (generic values by
  `lem:extraction-merged-count`, special values `c'_b` by `intWHat_special_le`).
* `kappaFixed_le_coverRowKappa` is the last sentence of Step 6, `κ^f ≤ κ_{C_z}(x, c')`;
  `kappaFixed_congr` says that `κ^f` reads only the fixed labels.

## Deviation from the paper (bookkeeping only)

The paper divides each `ŵ_u` by `2^{κ^r_u}`, the merges with earlier *integrated* vertices, and
keeps `2^{κ^f_u}` in the one-vertex bound. Here `ŵ_u` is divided by `2^{κ_u}`, all merges at
`u` (`intMerges`), so that the one-vertex bound is uniform in the earlier labels, and the fixed
merges are restored as the global factor `2^{κ^f}` (`intW_prod_le`). The two bookkeepings give
the same bound. Only the coarse error `e_t(q, n)` is used.
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

section Integrated

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- `w_u(z) = ∏_{b ∈ H_u} (1 + χ(ς_{ub}(c'_b - z)))`, the free factors of an integrated vertex
`u` with label `z`. -/
noncomputable def intW (ς : U → U → ℤ) (Fr : Finset (U × U)) (c' : U → F) (u : U) (z : F) :
    ℝ :=
  ∏ b ∈ intH Fr u, (1 + (quadraticChar F ((ς u b : F) * (c' b - z)) : ℝ))

/-- `ŵ_u(z) = w_u(z) 2^{∑_{b ∈ C_z} c^U(u, b) [z = c'_b]}`: for `c'` injective on `C_z` this is
`w_u(z) 2^{c^U(u,b)}` if `z = c'_b` with `b ∈ C_z`, and `w_u(z)` otherwise (Step 6). -/
noncomputable def intWHat (G : OrientedGraph U) (ς : U → U → ℤ) (Fr : Finset (U × U))
    (Cz : Finset U) (c' : U → F) (u : U) (z : F) : ℝ :=
  intW ς Fr c' u z * 2 ^ (∑ b ∈ Cz, if z = c' b then rowsCU G ς u b else 0)

/-- `κ_u(y)`, the merges at `u`: pairs `(i, b)` with `i` a `G⁺`-neighbour of `u` earlier in
`ord`, `b ∈ H_u` and `y_i = c'_b`. -/
def intMerges (G : OrientedGraph U) (ord : U → ℕ) (Fr : Finset (U × U)) (c' y : U → F)
    (u : U) : ℕ :=
  ∑ i ∈ (coverRowEarlier univ ord u).filter (fun i => (i, u) ∈ G.E ∨ (u, i) ∈ G.E),
    ∑ b ∈ intH Fr u, if y i = c' b then 1 else 0

/-- The weight `φ_u(y) = ŵ_u(y_u) 2^{-κ_u(y)}` for `u ∈ U_x`, and `1` for the other vertices. -/
noncomputable def intPhi (G : OrientedGraph U) (ς : U → U → ℤ) (ord : U → ℕ)
    (Fr : Finset (U × U)) (Ux Cz : Finset U) (c' : U → F) (u : U) (y : U → F) : ℝ :=
  if u ∈ Ux then intWHat G ς Fr Cz c' u (y u) * ((2 : ℝ) ^ intMerges G ord Fr c' y u)⁻¹ else 1

theorem intW_nonneg (ς : U → U → ℤ) (Fr : Finset (U × U)) (c' : U → F) (u : U) (z : F) :
    0 ≤ intW ς Fr c' u z :=
  prod_nonneg fun _ _ => (coverRow_one_add_chi _).1

theorem intWHat_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) (Fr : Finset (U × U))
    (Cz : Finset U) (c' : U → F) (u : U) (z : F) : 0 ≤ intWHat G ς Fr Cz c' u z :=
  mul_nonneg (intW_nonneg ς Fr c' u z) (by positivity)

theorem intPhi_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) (ord : U → ℕ)
    (Fr : Finset (U × U)) (Ux Cz : Finset U) (c' : U → F) (u : U) (y : U → F) :
    0 ≤ intPhi G ς ord Fr Ux Cz c' u y := by
  unfold intPhi
  split_ifs
  · exact mul_nonneg (intWHat_nonneg G ς Fr Cz c' u _) (by positivity)
  · exact zero_le_one

/-- `Θ⁺_U = ∏_{(u,b) ∈ Fr, u ∈ U_x} (1 + χ_{ub}) = ∏_{u ∈ U_x} w_u(x_u)`. -/
theorem prod_free_eq_prod_intW (ς : U → U → ℤ) (Fr : Finset (U × U)) (Ux : Finset U)
    (x c' : U → F) :
    ∏ e ∈ Fr.filter (fun e => e.1 ∈ Ux), (1 + chiPair ς e x c') =
      ∏ u ∈ Ux, intW ς Fr c' u (x u) := by
  unfold intW chiPair
  refine prod_finset_product' (Fr.filter fun e => e.1 ∈ Ux) Ux (intH Fr)
    (f := fun u b => 1 + (quadraticChar F ((ς u b : F) * (c' b - x u)) : ℝ)) ?_
  intro e
  simp only [mem_filter, intH, mem_univ, true_and, Prod.mk.eta]
  exact and_comm

/-- `2^{c^U(u,b) - [b ∈ H_u]} = 2^{c^U(u,b)} · (1/2 if b ∈ H_u, 1 otherwise)`. -/
theorem intExp_two_zpow (G : OrientedGraph U) (ς : U → U → ℤ) (Fr : Finset (U × U))
    (u b : U) : (2 : ℝ) ^ intExp G ς Fr u b =
      2 ^ rowsCU G ς u b * if b ∈ intH Fr u then (2 : ℝ)⁻¹ else 1 := by
  unfold intExp
  split_ifs
  · rw [zpow_sub₀ two_ne_zero, zpow_natCast, zpow_one, div_eq_mul_inv]
  · rw [sub_zero, zpow_natCast, mul_one]

/-- At a special value `c'_b` (`b ∈ C_z`, `c'` injective on `C_z`):
`ŵ_u(c'_b) ≤ 2^{h_u} 2^{c^U(u,b) - [b ∈ H_u]}`; the factor of `b` itself, if `b ∈ H_u`, is
`1 + χ(0) = 1`. -/
theorem intWHat_special_le (G : OrientedGraph U) (ς : U → U → ℤ) (Fr : Finset (U × U))
    (Cz : Finset U) (c' : U → F) (hc' : ∀ a ∈ Cz, ∀ b ∈ Cz, c' a = c' b → a = b)
    (u b : U) (hb : b ∈ Cz) :
    intWHat G ς Fr Cz c' u (c' b) ≤ 2 ^ (intH Fr u).card * (2 : ℝ) ^ intExp G ς Fr u b := by
  have hsum : (∑ b' ∈ Cz, if c' b = c' b' then rowsCU G ς u b' else 0) = rowsCU G ς u b := by
    rw [sum_eq_single_of_mem b hb]
    · simp
    · intro b' hb' hne
      have : c' b ≠ c' b' := fun h => hne (hc' b hb b' hb' h).symm
      simp [this]
  have hg0 : ∀ b' ∈ intH Fr u,
      0 ≤ 1 + (quadraticChar F ((ς u b' : F) * (c' b' - c' b)) : ℝ) :=
    fun b' _ => (coverRow_one_add_chi _).1
  have hg2 : ∀ b' ∈ intH Fr u,
      1 + (quadraticChar F ((ς u b' : F) * (c' b' - c' b)) : ℝ) ≤ 2 :=
    fun b' _ => (coverRow_one_add_chi _).2
  have hP : intW ς Fr c' u (c' b) ≤
      2 ^ (intH Fr u).card * if b ∈ intH Fr u then (2 : ℝ)⁻¹ else 1 := by
    unfold intW
    split_ifs with hbH
    · rw [← mul_prod_erase _ _ hbH]
      simp only [sub_self, mul_zero, quadraticChar_zero, Int.cast_zero, add_zero, one_mul]
      have hcard : (intH Fr u).card = ((intH Fr u).erase b).card + 1 := by
        rw [card_erase_of_mem hbH]
        have := card_pos.mpr ⟨b, hbH⟩
        omega
      rw [hcard, pow_succ, mul_assoc, mul_inv_cancel₀ two_ne_zero, mul_one]
      calc ∏ b' ∈ (intH Fr u).erase b,
            (1 + (quadraticChar F ((ς u b' : F) * (c' b' - c' b)) : ℝ))
          ≤ ∏ _b' ∈ (intH Fr u).erase b, (2 : ℝ) :=
            prod_le_prod₀ (fun b' hb' => hg0 b' (mem_of_mem_erase hb'))
              (fun b' hb' => hg2 b' (mem_of_mem_erase hb'))
        _ = 2 ^ ((intH Fr u).erase b).card := prod_const 2
    · rw [mul_one]
      calc ∏ b' ∈ intH Fr u, (1 + (quadraticChar F ((ς u b' : F) * (c' b' - c' b)) : ℝ))
          ≤ ∏ _b' ∈ intH Fr u, (2 : ℝ) := prod_le_prod₀ hg0 hg2
        _ = 2 ^ (intH Fr u).card := prod_const 2
  unfold intWHat
  rw [hsum, intExp_two_zpow]
  have hpos : (0 : ℝ) ≤ 2 ^ rowsCU G ς u b := by positivity
  calc intW ς Fr c' u (c' b) * 2 ^ rowsCU G ς u b
      ≤ (2 ^ (intH Fr u).card * if b ∈ intH Fr u then (2 : ℝ)⁻¹ else 1) *
          2 ^ rowsCU G ς u b := mul_le_mul_of_nonneg_right hP hpos
    _ = _ := by ring

/-- **The one-vertex bound of Step 6.** Let `u ∈ U_x` and let `y` be feasible on the vertices
earlier than `u`. Summing `ŵ_u(z) 2^{-κ_u(y)}` over the admissible labels `z` of `u` gives at most
`q 2^{-t_u}(1 + e_{s_u}(q, n) + r² 2^{s_u} ∑_{b ∈ C_z} 2^{c^U(u,b) - [b ∈ H_u]})`. The generic
labels `z ∉ c'(C_z)` are counted by `lem:extraction-merged-count` (`merged_count_le_fintype'`,
with the `κ_u` merged roots), the special labels `z = c'_b` by `intWHat_special_le`.
`WeilBound F` is Weil's theorem (literature input). -/
theorem integrated_oneVertex (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (n : ℕ)
    (Fr : Finset (U × U)) (hFr : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0)
    (Ux Cz : Finset U) (hH : ∀ e ∈ Fr, e.1 ∈ Ux → e.2 ∈ Cz) (ord : U → ℕ)
    (c' : U → F) (hc' : ∀ a ∈ Cz, ∀ b ∈ Cz, c' a = c' b → a = b)
    (u : U) (hu : u ∈ Ux) (y : U → F) (hy : Feasible F G (coverRowEarlier univ ord u) y) :
    ∑ z ∈ vertexAdmissible G (coverRowEarlier univ ord u) y u,
        intWHat G ς Fr Cz c' u z * ((2 : ℝ) ^ intMerges G ord Fr c' y u)⁻¹ ≤
      Fintype.card F * (2 : ℝ)⁻¹ ^ ordT G ord u *
        intNum G ς (Fintype.card F) n ord Fr Cz u := by
  set A := coverRowEarlier univ ord u with hA
  set μ := intMerges G ord Fr c' y u with hμ
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hμinv0 : (0 : ℝ) ≤ ((2 : ℝ) ^ μ)⁻¹ := by positivity
  have hμinv1 : ((2 : ℝ) ^ μ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hHbFr : ∀ b ∈ intH Fr u, (u, b) ∈ Fr := fun b hb => by simpa [intH] using hb
  rw [← sum_filter_add_sum_filter_not (vertexAdmissible G A y u) (fun z => z ∈ Cz.image c')]
  -- the special labels `c'_b`, `b ∈ C_z`
  have hii : ∑ z ∈ (vertexAdmissible G A y u).filter (fun z => z ∈ Cz.image c'),
      intWHat G ς Fr Cz c' u z * ((2 : ℝ) ^ μ)⁻¹ ≤
        ∑ b ∈ Cz, 2 ^ (intH Fr u).card * (2 : ℝ) ^ intExp G ς Fr u b := by
    calc ∑ z ∈ (vertexAdmissible G A y u).filter (fun z => z ∈ Cz.image c'),
          intWHat G ς Fr Cz c' u z * ((2 : ℝ) ^ μ)⁻¹
        ≤ ∑ z ∈ (vertexAdmissible G A y u).filter (fun z => z ∈ Cz.image c'),
            intWHat G ς Fr Cz c' u z :=
          sum_le_sum fun z _ => mul_le_of_le_one_right (intWHat_nonneg G ς Fr Cz c' u z) hμinv1
      _ ≤ ∑ z ∈ Cz.image c', intWHat G ς Fr Cz c' u z :=
          sum_le_sum_of_subset_of_nonneg (fun z hz => (mem_filter.mp hz).2)
            (fun z _ _ => intWHat_nonneg G ς Fr Cz c' u z)
      _ = ∑ b ∈ Cz, intWHat G ς Fr Cz c' u (c' b) :=
          sum_image fun a ha b hb h => hc' a ha b hb h
      _ ≤ _ := sum_le_sum fun b hb => intWHat_special_le G ς Fr Cz c' hc' u b hb
  -- the other labels: `lem:extraction-merged-count`
  set NA := A.filter (fun i => (i, u) ∈ G.E ∨ (u, i) ∈ G.E) with hNA
  set Hb := intH Fr u with hHb
  let β : NA → F := fun i => y i
  have hβ : Function.Injective β := fun i j h =>
    Subtype.ext (hy.1 i (mem_filter.mp i.2).1 j (mem_filter.mp j.2).1 h)
  let γ : Hb → F := fun b => c' b
  have hγ : Function.Injective γ := fun a b h =>
    Subtype.ext (hc' a (hH (u, a) (hHbFr a a.2) hu) b (hH (u, b) (hHbFr b b.2) hu) h)
  have hm1 : quadraticChar F (-1) = 1 ∨ quadraticChar F (-1) = -1 :=
    quadraticChar_dichotomy (neg_ne_zero.mpr one_ne_zero)
  let s : NA → ℤ := fun i => if (i.1, u) ∈ G.E then 1 else quadraticChar F (-1)
  have hs : ∀ i, s i = 1 ∨ s i = -1 := fun i => by
    simp only [s]
    split_ifs
    · exact Or.inl rfl
    · exact hm1
  let s' : Hb → ℤ := fun b => quadraticChar F (-(ς u b.1 : F))
  have hs' : ∀ b, s' b = 1 ∨ s' b = -1 := fun b => by
    have hb : ς u b.1 ≠ 0 := hFr (u, b.1) (hHbFr b.1 b.2)
    have hne : -(ς u b.1 : F) ≠ 0 := by
      rcases hς u b.1 with h | h | h
      · exact absurd h hb
      · rw [h]; simp
      · rw [h]; simp
    exact quadraticChar_dichotomy hne
  set 𝒳 : Finset F := A.image y ∪ Cz.image c' with h𝒳
  have hβX : ∀ i, β i ∈ 𝒳 := fun i =>
    mem_union_left _ (mem_image_of_mem y (mem_filter.mp i.2).1)
  have hγX : ∀ b, γ b ∈ 𝒳 := fun b =>
    mem_union_right _ (mem_image_of_mem c' (hH (u, b.1) (hHbFr b.1 b.2) hu))
  have hmc := merged_count_le_fintype' hW β hβ γ hγ s hs s' hs' 𝒳 hβX hγX
    (n' := (n : ℝ)) (by positivity)
  have hset : (vertexAdmissible G A y u).filter (fun z => z ∉ Cz.image c') =
      univ.filter (fun z => z ∉ 𝒳 ∧ ∀ i, quadraticChar F (z - β i) = s i) := by
    ext c
    simp only [vertexAdmissible, mem_filter, mem_univ, true_and, h𝒳, mem_union, not_or]
    constructor
    · rintro ⟨⟨hc, hin, hout⟩, hcX⟩
      refine ⟨⟨hc, hcX⟩, fun i => ?_⟩
      have hi := (mem_filter.mp i.2).2
      simp only [s, β]
      split_ifs with h
      · exact hin i (mem_filter.mp i.2).1 h
      · have hvu : (u, i.1) ∈ G.E := hi.resolve_left h
        have h1 := hout i (mem_filter.mp i.2).1 hvu
        have : y i - c = -1 * (c - y i) := by ring
        rw [this, map_mul] at h1
        rcases hm1 with h' | h' <;> rw [h'] at h1 ⊢ <;> linarith
    · rintro ⟨⟨hc, hcX⟩, hall⟩
      refine ⟨⟨hc, fun i hi he => ?_, fun i hi he => ?_⟩, hcX⟩
      · have hmem : i ∈ NA := mem_filter.mpr ⟨hi, Or.inl he⟩
        have := hall ⟨i, hmem⟩
        simpa [s, β, he] using this
      · have hmem : i ∈ NA := mem_filter.mpr ⟨hi, Or.inr he⟩
        have hnot : (i, u) ∉ G.E := G.oriented u i he
        have h1 := hall ⟨i, hmem⟩
        simp only [s, β, hnot, ↓reduceIte] at h1
        have : y i - c = -1 * (c - y i) := by ring
        rw [this, map_mul, h1]
        rcases hm1 with h' | h' <;> rw [h'] <;> norm_num
  have hsummand : ∀ z ∈ univ.filter (fun z => z ∉ 𝒳 ∧ ∀ i, quadraticChar F (z - β i) = s i),
      intWHat G ς Fr Cz c' u z = ∏ l, ((1 : ℝ) + s' l * quadraticChar F (z - γ l)) := by
    intro z hz
    have hzX : z ∉ Cz.image c' := fun h => (mem_filter.mp hz).2.1 (mem_union_right _ h)
    have hne : ∀ b ∈ Cz, z ≠ c' b := fun b hb h => hzX (mem_image.mpr ⟨b, hb, h.symm⟩)
    unfold intWHat
    rw [sum_eq_zero fun b hb => by simp only [hne b hb, ↓reduceIte], pow_zero, mul_one]
    unfold intW
    rw [← prod_coe_sort Hb]
    refine prod_congr rfl fun b _ => ?_
    have : (ς u b.1 : F) * (c' b.1 - z) = (-(ς u b.1 : F)) * (z - c' b.1) := by ring
    simp only [s', γ, this, map_mul, Int.cast_mul]
  have hcardι : Fintype.card NA = ordT G ord u := by
    rw [Fintype.card_coe]
    rfl
  have hcardκ : Fintype.card Hb = Hb.card := Fintype.card_coe _
  have hmerge : mergedCount β γ = μ := by
    unfold mergedCount
    calc (univ.filter fun il : NA × Hb => β il.1 = γ il.2).card
        = ∑ il : NA × Hb, if β il.1 = γ il.2 then 1 else 0 := card_filter _ _
      _ = ∑ i : NA, ∑ b : Hb, if β i = γ b then 1 else 0 := Fintype.sum_prod_type _
      _ = ∑ i : NA, ∑ b ∈ Hb, if y i = c' b then 1 else 0 :=
          sum_congr rfl fun i _ => sum_coe_sort Hb (fun b => if y i = c' b then 1 else 0)
      _ = ∑ i ∈ NA, ∑ b ∈ Hb, if y i = c' b then 1 else 0 :=
          sum_coe_sort NA (fun i => ∑ b ∈ Hb, if y i = c' b then 1 else 0)
      _ = μ := rfl
  have hS : intS G ord Fr u = ordT G ord u + Hb.card := rfl
  have hi : ∑ z ∈ (vertexAdmissible G A y u).filter (fun z => z ∉ Cz.image c'),
      intWHat G ς Fr Cz c' u z * ((2 : ℝ) ^ μ)⁻¹ ≤
        Fintype.card F * (2 : ℝ)⁻¹ ^ ordT G ord u *
          (1 + coarseError (intS G ord Fr u) (Fintype.card F) n) := by
    rw [← sum_mul, hset, sum_congr rfl hsummand]
    rw [hcardι, hcardκ, hmerge, ← hS] at hmc
    calc (∑ z ∈ univ.filter (fun z => z ∉ 𝒳 ∧ ∀ i, quadraticChar F (z - β i) = s i),
          ∏ l, ((1 : ℝ) + s' l * quadraticChar F (z - γ l))) * ((2 : ℝ) ^ μ)⁻¹
        ≤ (Fintype.card F * (2 : ℝ)⁻¹ ^ ordT G ord u * 2 ^ μ *
            (1 + coarseError (intS G ord Fr u) (Fintype.card F) n)) *
            ((2 : ℝ) ^ μ)⁻¹ := mul_le_mul_of_nonneg_right hmc hμinv0
      _ = _ := by field_simp
  have hid : (Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ ordT G ord u *
      ((Real.sqrt (Fintype.card F))⁻¹ ^ 2 * 2 ^ intS G ord Fr u *
        ∑ b ∈ Cz, (2 : ℝ) ^ intExp G ς Fr u b) =
      ∑ b ∈ Cz, 2 ^ Hb.card * (2 : ℝ) ^ intExp G ς Fr u b := by
    rw [coverRow_r_sq hq0, ← mul_sum, hS, pow_add]
    have h2 : (2 : ℝ)⁻¹ ^ ordT G ord u * 2 ^ ordT G ord u = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow]
    calc (Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ ordT G ord u *
          ((Fintype.card F : ℝ)⁻¹ * (2 ^ ordT G ord u * 2 ^ Hb.card) *
            ∑ b ∈ Cz, (2 : ℝ) ^ intExp G ς Fr u b)
        = ((Fintype.card F : ℝ) * (Fintype.card F : ℝ)⁻¹) *
            ((2 : ℝ)⁻¹ ^ ordT G ord u * 2 ^ ordT G ord u) *
            (2 ^ Hb.card * ∑ b ∈ Cz, (2 : ℝ) ^ intExp G ς Fr u b) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hq0.ne', h2, one_mul, one_mul]
  have hnum : intNum G ς (Fintype.card F) n ord Fr Cz u =
      1 + coarseError (intS G ord Fr u) (Fintype.card F) n +
        (Real.sqrt (Fintype.card F))⁻¹ ^ 2 * 2 ^ intS G ord Fr u *
          ∑ b ∈ Cz, (2 : ℝ) ^ intExp G ς Fr u b := rfl
  rw [hnum]
  calc ∑ z ∈ (vertexAdmissible G A y u).filter (fun z => z ∈ Cz.image c'),
        intWHat G ς Fr Cz c' u z * ((2 : ℝ) ^ μ)⁻¹ +
      ∑ z ∈ (vertexAdmissible G A y u).filter (fun z => z ∉ Cz.image c'),
        intWHat G ς Fr Cz c' u z * ((2 : ℝ) ^ μ)⁻¹
      ≤ ∑ b ∈ Cz, 2 ^ Hb.card * (2 : ℝ) ^ intExp G ς Fr u b +
          Fintype.card F * (2 : ℝ)⁻¹ ^ ordT G ord u *
            (1 + coarseError (intS G ord Fr u) (Fintype.card F) n) :=
        add_le_add hii hi
    _ = _ := by rw [← hid]; ring

omit [Field F] [Fintype F] in
/-- **Step 6, the merge count**: for `y` agreeing with `x₀` off `U_x`,
`∑_{u ∈ U_x} κ_u(y) ≤ ∑_{u ∈ U_x} ∑_{b ∈ C_z} c^U(u, b) [y_u = c'_b] + κ^f`. A merge `(i, b)` at
`u` with `i ∈ U_x` and `y_i = c'_b` has `u ∈ Adj(i)` and `u ∈ N(b)`, so an integrated `i` with
`y_i = c'_b` causes at most `c^U(i, b)` merges; the merges with `i ∉ U_x` are those of `κ^f`. -/
theorem intMerges_sum_le (G : OrientedGraph U) (ς : U → U → ℤ) (ord : U → ℕ)
    (Fr : Finset (U × U)) (hFr : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) (Ux Cz : Finset U)
    (hH : ∀ e ∈ Fr, e.1 ∈ Ux → e.2 ∈ Cz) (hseg : ∀ a, a ∉ Ux → ∀ b ∈ Ux, ord a < ord b)
    (x₀ c' y : U → F) (hy : ∀ i, i ∉ Ux → y i = x₀ i) :
    ∑ u ∈ Ux, intMerges G ord Fr c' y u ≤
      (∑ u ∈ Ux, ∑ b ∈ Cz, if y u = c' b then rowsCU G ς u b else 0) +
        kappaFixed G Fr Ux x₀ c' := by
  set T : U → U → U → ℕ := fun u i b =>
    if ((u, i) ∈ G.E ∨ (i, u) ∈ G.E) ∧ ς u b ≠ 0 ∧ y i = c' b then 1 else 0 with hT
  -- split the earlier neighbours into integrated (`∈ U_x`) and fixed (`∉ U_x`) ones
  have hsplit : ∀ u ∈ Ux, intMerges G ord Fr c' y u =
      (∑ i ∈ ((coverRowEarlier univ ord u).filter
          (fun i => (i, u) ∈ G.E ∨ (u, i) ∈ G.E)).filter (fun i => i ∈ Ux),
        ∑ b ∈ intH Fr u, if y i = c' b then 1 else 0) +
      ∑ i ∈ univ.filter (fun i => i ∉ Ux ∧ ((i, u) ∈ G.E ∨ (u, i) ∈ G.E)),
        ∑ b ∈ intH Fr u, if x₀ i = c' b then 1 else 0 := by
    intro u hu
    unfold intMerges
    rw [← sum_filter_add_sum_filter_not ((coverRowEarlier univ ord u).filter
      (fun i => (i, u) ∈ G.E ∨ (u, i) ∈ G.E)) (fun i => i ∈ Ux)]
    have hset : ((coverRowEarlier univ ord u).filter
        (fun i => (i, u) ∈ G.E ∨ (u, i) ∈ G.E)).filter (fun i => i ∉ Ux) =
        univ.filter (fun i => i ∉ Ux ∧ ((i, u) ∈ G.E ∨ (u, i) ∈ G.E)) := by
      ext i
      simp only [coverRowEarlier, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨⟨_, hadj⟩, hi⟩
        exact ⟨hi, hadj⟩
      · rintro ⟨hi, hadj⟩
        exact ⟨⟨hseg i hi u hu, hadj⟩, hi⟩
    congr 1
    exact sum_congr hset fun i hi => by rw [hy i (mem_filter.mp hi).2.1]
  -- the integrated part
  have hint : ∀ u ∈ Ux, (∑ i ∈ ((coverRowEarlier univ ord u).filter
          (fun i => (i, u) ∈ G.E ∨ (u, i) ∈ G.E)).filter (fun i => i ∈ Ux),
        ∑ b ∈ intH Fr u, if y i = c' b then 1 else 0) ≤ ∑ i ∈ Ux, ∑ b ∈ Cz, T u i b := by
    intro u hu
    calc (∑ i ∈ ((coverRowEarlier univ ord u).filter
            (fun i => (i, u) ∈ G.E ∨ (u, i) ∈ G.E)).filter (fun i => i ∈ Ux),
          ∑ b ∈ intH Fr u, if y i = c' b then 1 else 0)
        = ∑ i ∈ ((coverRowEarlier univ ord u).filter
            (fun i => (i, u) ∈ G.E ∨ (u, i) ∈ G.E)).filter (fun i => i ∈ Ux),
          ∑ b ∈ intH Fr u, T u i b := by
          refine sum_congr rfl fun i hi => sum_congr rfl fun b hb => ?_
          have hadj : (i, u) ∈ G.E ∨ (u, i) ∈ G.E := (mem_filter.mp (mem_filter.mp hi).1).2
          have hς' : ς u b ≠ 0 := hFr (u, b) (by simpa [intH] using hb)
          simp only [hT, hadj.symm, hς', ne_eq, not_false_eq_true, true_and]
      _ ≤ ∑ i ∈ Ux, ∑ b ∈ intH Fr u, T u i b :=
          sum_le_sum_of_subset (fun i hi => (mem_filter.mp hi).2)
      _ ≤ ∑ i ∈ Ux, ∑ b ∈ Cz, T u i b := by
          refine sum_le_sum fun i _ => sum_le_sum_of_subset fun b hb => ?_
          exact hH (u, b) (by simpa [intH] using hb) hu
  have hc : ∀ i b, ∑ u, T u i b = if y i = c' b then rowsCU G ς i b else 0 := by
    intro i b
    split_ifs with hyb
    · unfold rowsCU rowsAdj rowsN
      rw [filter_filter, card_filter]
      refine sum_congr rfl fun u _ => ?_
      simp [hT, hyb]
    · refine sum_eq_zero fun u _ => ?_
      simp only [hT, hyb, and_false, ↓reduceIte]
  calc ∑ u ∈ Ux, intMerges G ord Fr c' y u
      = (∑ u ∈ Ux, ∑ i ∈ ((coverRowEarlier univ ord u).filter
          (fun i => (i, u) ∈ G.E ∨ (u, i) ∈ G.E)).filter (fun i => i ∈ Ux),
          ∑ b ∈ intH Fr u, if y i = c' b then 1 else 0) + kappaFixed G Fr Ux x₀ c' := by
        rw [sum_congr rfl hsplit, sum_add_distrib]
        rfl
    _ ≤ (∑ u ∈ Ux, ∑ i ∈ Ux, ∑ b ∈ Cz, T u i b) + kappaFixed G Fr Ux x₀ c' :=
        Nat.add_le_add_right (sum_le_sum hint) _
    _ ≤ (∑ u, ∑ i ∈ Ux, ∑ b ∈ Cz, T u i b) + kappaFixed G Fr Ux x₀ c' :=
        Nat.add_le_add_right (sum_le_sum_of_subset (subset_univ _)) _
    _ = (∑ i ∈ Ux, ∑ b ∈ Cz, ∑ u, T u i b) + kappaFixed G Fr Ux x₀ c' := by
        congr 1
        calc ∑ u, ∑ i ∈ Ux, ∑ b ∈ Cz, T u i b = ∑ i ∈ Ux, ∑ u, ∑ b ∈ Cz, T u i b := sum_comm
          _ = ∑ i ∈ Ux, ∑ b ∈ Cz, ∑ u, T u i b := sum_congr rfl fun i _ => sum_comm
    _ = _ := by
        congr 1
        exact sum_congr rfl fun i _ => sum_congr rfl fun b _ => hc i b

/-- **Step 6, the merge weights**: for `y` agreeing with `x₀` off `U_x`,
`∏_{u ∈ U_x} w_u(y_u) ≤ 2^{κ^f} ∏_{u ∈ U_x} ŵ_u(y_u) 2^{-κ_u(y)}`. -/
theorem intW_prod_le (G : OrientedGraph U) (ς : U → U → ℤ) (ord : U → ℕ)
    (Fr : Finset (U × U)) (hFr : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) (Ux Cz : Finset U)
    (hH : ∀ e ∈ Fr, e.1 ∈ Ux → e.2 ∈ Cz) (hseg : ∀ a, a ∉ Ux → ∀ b ∈ Ux, ord a < ord b)
    (x₀ c' y : U → F) (hy : ∀ i, i ∉ Ux → y i = x₀ i) :
    ∏ u ∈ Ux, intW ς Fr c' u (y u) ≤
      2 ^ kappaFixed G Fr Ux x₀ c' * ∏ u ∈ Ux, intPhi G ς ord Fr Ux Cz c' u y := by
  have hphi : ∏ u ∈ Ux, intPhi G ς ord Fr Ux Cz c' u y =
      (∏ u ∈ Ux, intW ς Fr c' u (y u)) *
        2 ^ (∑ u ∈ Ux, ∑ b ∈ Cz, if y u = c' b then rowsCU G ς u b else 0) *
        ((2 : ℝ) ^ (∑ u ∈ Ux, intMerges G ord Fr c' y u))⁻¹ := by
    rw [prod_congr rfl fun u hu => (by simp only [intPhi, hu, ↓reduceIte] :
      intPhi G ς ord Fr Ux Cz c' u y =
        intWHat G ς Fr Cz c' u (y u) * ((2 : ℝ) ^ intMerges G ord Fr c' y u)⁻¹)]
    unfold intWHat
    rw [prod_mul_distrib, prod_mul_distrib, prod_inv_distrib, prod_pow_eq_pow_sum,
      prod_pow_eq_pow_sum]
  have hle := intMerges_sum_le G ς ord Fr hFr Ux Cz hH hseg x₀ c' y hy
  have hW0 : 0 ≤ ∏ u ∈ Ux, intW ς Fr c' u (y u) :=
    prod_nonneg fun u _ => intW_nonneg ς Fr c' u _
  have h2 : (1 : ℝ) ≤
      2 ^ (∑ u ∈ Ux, ∑ b ∈ Cz, if y u = c' b then rowsCU G ς u b else 0) *
        2 ^ kappaFixed G Fr Ux x₀ c' *
        ((2 : ℝ) ^ (∑ u ∈ Ux, intMerges G ord Fr c' y u))⁻¹ := by
    rw [← pow_add, ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
    exact pow_le_pow_right₀ (by norm_num) hle
  rw [hphi]
  calc ∏ u ∈ Ux, intW ς Fr c' u (y u) = (∏ u ∈ Ux, intW ς Fr c' u (y u)) * 1 :=
        (mul_one _).symm
    _ ≤ (∏ u ∈ Ux, intW ς Fr c' u (y u)) *
          (2 ^ (∑ u ∈ Ux, ∑ b ∈ Cz, if y u = c' b then rowsCU G ς u b else 0) *
            2 ^ kappaFixed G Fr Ux x₀ c' *
            ((2 : ℝ) ^ (∑ u ∈ Ux, intMerges G ord Fr c' y u))⁻¹) :=
        mul_le_mul_of_nonneg_left h2 hW0
    _ = _ := by ring

/-- **`eq:extraction:mbound`** (Step 6 of `lem:matching:extractionk`), in summed form. Let the
labels `x₀` of `V ∪ C_x = X \ U_x` be feasible, the labels `c'` of `C_z` injective on `C_z`, and
`H_u ⊆ C_z` for `u ∈ U_x`. Label `U_x` along `ord` (after all other vertices). Then the sum over
the completions `x ∈ 𝓘⁺` of `x₀` of `Θ⁺_U(x, c') = ∏_{(u,b) ∈ Fr, u ∈ U_x} (1 + χ_{ub}(x, c'))` is
at most `2^{κ^f} ∏_{u ∈ U_x} q 2^{-t_u}(1 + e_{s_u}(q, n) + r² 2^{s_u}
∑_{b ∈ C_z} 2^{c^U(u,b) - [b ∈ H_u]})`. `WeilBound F` is Weil's theorem (literature input). -/
theorem integrated_extSum_le (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (n : ℕ)
    (Fr : Finset (U × U)) (hFr : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0)
    (Ux Cz : Finset U) (hH : ∀ e ∈ Fr, e.1 ∈ Ux → e.2 ∈ Cz)
    (ord : U → ℕ) (hord : Function.Injective ord)
    (hseg : ∀ a, a ∉ Ux → ∀ b ∈ Ux, ord a < ord b)
    (c' : U → F) (hc' : ∀ a ∈ Cz, ∀ b ∈ Cz, c' a = c' b → a = b)
    (x₀ : U → F) (hx₀ : Feasible F G (univ \ Ux) x₀) :
    coverRowExtSum G (univ \ Ux) x₀
        (fun x => ∏ e ∈ Fr.filter (fun e => e.1 ∈ Ux), (1 + chiPair ς e x c')) ≤
      2 ^ kappaFixed G Fr Ux x₀ c' *
        ∏ u ∈ Ux, ((Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ ordT G ord u *
          intNum G ς (Fintype.card F) n ord Fr Cz u) := by
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  set M : U → ℝ := fun b => if b ∈ Ux then (Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ ordT G ord b *
      intNum G ς (Fintype.card F) n ord Fr Cz b else Fintype.card F with hM
  have hnum0 : ∀ b, 0 ≤ intNum G ς (Fintype.card F) n ord Fr Cz b := fun b => by
    unfold intNum
    have he := coarseError_nonneg (q := (Fintype.card F : ℝ)) (Nat.cast_nonneg n)
      (intS G ord Fr b)
    have hs : 0 ≤ ∑ b' ∈ Cz, (2 : ℝ) ^ intExp G ς Fr b b' :=
      sum_nonneg fun _ _ => by positivity
    exact add_nonneg (add_nonneg zero_le_one he) (mul_nonneg (by positivity) hs)
  have hM0 : ∀ b, 0 ≤ M b := fun b => by
    simp only [hM]
    split_ifs
    · exact mul_nonneg (by positivity) (hnum0 b)
    · exact hq0.le
  have hloc : ∀ b ∈ (univ : Finset U), ∀ y y' : U → F,
      (∀ a ∈ (univ : Finset U), ord a ≤ ord b → y a = y' a) →
        intPhi G ς ord Fr Ux Cz c' b y = intPhi G ς ord Fr Ux Cz c' b y' := by
    intro b _ y y' hyy
    unfold intPhi
    split_ifs
    · have hm : intMerges G ord Fr c' y b = intMerges G ord Fr c' y' b := by
        unfold intMerges
        refine sum_congr rfl fun i hi => ?_
        have hi' : ord i < ord b := by
          simpa [coverRowEarlier] using (mem_filter.mp hi).1
        rw [hyy i (mem_univ i) hi'.le]
      rw [hyy b (mem_univ b) le_rfl, hm]
    · rfl
  have hstep : ∀ b ∈ (univ : Finset U), ∀ x' : U → F,
      Feasible F G (coverRowEarlier univ ord b) x' →
        ∑ c ∈ vertexAdmissible G (coverRowEarlier univ ord b) x' b,
          intPhi G ς ord Fr Ux Cz c' b (Function.update x' b c) ≤ M b := by
    intro b _ x' hx'
    by_cases hb : b ∈ Ux
    · have hupd : ∀ c, intPhi G ς ord Fr Ux Cz c' b (Function.update x' b c) =
          intWHat G ς Fr Cz c' b c * ((2 : ℝ) ^ intMerges G ord Fr c' x' b)⁻¹ := by
        intro c
        have hm : intMerges G ord Fr c' (Function.update x' b c) b =
            intMerges G ord Fr c' x' b := by
          unfold intMerges
          refine sum_congr rfl fun i hi => ?_
          have hib : i ≠ b := by
            rintro rfl
            have : ord i < ord i := by simpa [coverRowEarlier] using (mem_filter.mp hi).1
            exact lt_irrefl _ this
          rw [Function.update_of_ne hib]
        simp only [intPhi, hb, ↓reduceIte, Function.update_self, hm]
      rw [sum_congr rfl fun c _ => hupd c]
      simp only [hM, hb, ↓reduceIte]
      exact integrated_oneVertex hW G ς hς n Fr hFr Ux Cz hH ord c' hc' b hb x' hx'
    · simp only [intPhi, hM, hb, ↓reduceIte, sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast card_le_univ _
  have hK : ∀ y : U → F, Feasible F G univ y → (extCount G univ y : ℝ) ≤ 1 := fun y hy => by
    rw [extCount_univ G hy, Nat.cast_one]
  have hseq := coverRow_seq_upper G (C := univ) (ord := ord) (fun a _ b _ h => hord h)
    (intPhi G ς ord Fr Ux Cz c') M 1 (fun b y => intPhi_nonneg G ς ord Fr Ux Cz c' b y) hM0
    zero_le_one hloc hstep hK Ux.card Ux rfl (subset_univ _)
    (fun b hb b' _ hb' => hseg b' hb' b hb) x₀ hx₀
  have hMprod : ∏ b ∈ Ux, M b = ∏ u ∈ Ux, ((Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ ordT G ord u *
      intNum G ς (Fintype.card F) n ord Fr Cz u) :=
    prod_congr rfl fun b hb => by simp only [hM, hb, ↓reduceIte]
  have hpt : ∀ y ∈ (injLabellings F G).filter (fun y => ∀ a ∈ univ \ Ux, y a = x₀ a),
      ∏ e ∈ Fr.filter (fun e => e.1 ∈ Ux), (1 + chiPair ς e y c') ≤
        2 ^ kappaFixed G Fr Ux x₀ c' * ∏ u ∈ Ux, intPhi G ς ord Fr Ux Cz c' u y := by
    intro y hy
    rw [prod_free_eq_prod_intW]
    refine intW_prod_le G ς ord Fr hFr Ux Cz hH hseg x₀ c' y fun i hi => ?_
    exact (mem_filter.mp hy).2 i (mem_sdiff.mpr ⟨mem_univ i, hi⟩)
  calc coverRowExtSum G (univ \ Ux) x₀
        (fun x => ∏ e ∈ Fr.filter (fun e => e.1 ∈ Ux), (1 + chiPair ς e x c'))
      ≤ ∑ y ∈ (injLabellings F G).filter (fun y => ∀ a ∈ univ \ Ux, y a = x₀ a),
          2 ^ kappaFixed G Fr Ux x₀ c' * ∏ u ∈ Ux, intPhi G ς ord Fr Ux Cz c' u y := by
        unfold coverRowExtSum
        exact sum_le_sum hpt
    _ = 2 ^ kappaFixed G Fr Ux x₀ c' * coverRowExtSum G (univ \ Ux) x₀
          (fun y => ∏ u ∈ Ux, intPhi G ς ord Fr Ux Cz c' u y) := by
        unfold coverRowExtSum
        rw [mul_sum]
    _ ≤ 2 ^ kappaFixed G Fr Ux x₀ c' * (1 * ∏ b ∈ Ux, M b) :=
        mul_le_mul_of_nonneg_left hseq (by positivity)
    _ = _ := by rw [one_mul, hMprod]

omit [Field F] [Fintype F] in
/-- `κ^f` reads only the fixed labels `x_i`, `i ∉ U_x`. -/
theorem kappaFixed_congr (G : OrientedGraph U) (Fr : Finset (U × U)) (Ux : Finset U)
    {x y : U → F} (h : ∀ i, i ∉ Ux → x i = y i) (c' : U → F) :
    kappaFixed G Fr Ux x c' = kappaFixed G Fr Ux y c' := by
  unfold kappaFixed
  refine sum_congr rfl fun u _ => sum_congr rfl fun i hi => ?_
  rw [h i (mem_filter.mp hi).2.1]

omit [Field F] [Fintype F] in
/-- The last sentence of Step 6: `κ^f ≤ κ_{C_z}(x, c')` (`coverRowKappa`, the weight of
`lem:extraction-rows`); a pair `(i, b)` with `x_i = c'_b` is a merge at most at the
`c^U(i, b)` vertices of `Adj(i) ∩ N(b)`. -/
theorem kappaFixed_le_coverRowKappa (G : OrientedGraph U) (ς : U → U → ℤ)
    (Fr : Finset (U × U)) (hFr : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) (Ux Cz : Finset U)
    (hH : ∀ e ∈ Fr, e.1 ∈ Ux → e.2 ∈ Cz) (x c' : U → F) :
    kappaFixed G Fr Ux x c' ≤ coverRowKappa G ς Cz x c' := by
  set T : U → U → U → ℕ := fun u i b =>
    if ((u, i) ∈ G.E ∨ (i, u) ∈ G.E) ∧ ς u b ≠ 0 ∧ x i = c' b then 1 else 0 with hT
  have hc : ∀ i b, ∑ u, T u i b = if c' b = x i then rowsCU G ς i b else 0 := by
    intro i b
    split_ifs with hyb
    · unfold rowsCU rowsAdj rowsN
      rw [filter_filter, card_filter]
      refine sum_congr rfl fun u _ => ?_
      simp [hT, hyb]
    · refine sum_eq_zero fun u _ => ?_
      have : x i ≠ c' b := fun h => hyb h.symm
      simp only [hT, this, and_false, ↓reduceIte]
  calc kappaFixed G Fr Ux x c'
      = ∑ u ∈ Ux, ∑ i ∈ univ.filter (fun i => i ∉ Ux ∧ ((i, u) ∈ G.E ∨ (u, i) ∈ G.E)),
          ∑ b ∈ intH Fr u, T u i b := by
        unfold kappaFixed
        refine sum_congr rfl fun u _ => sum_congr rfl fun i hi => sum_congr rfl fun b hb => ?_
        have hadj : (i, u) ∈ G.E ∨ (u, i) ∈ G.E := (mem_filter.mp hi).2.2
        have hς' : ς u b ≠ 0 := hFr (u, b) (by simpa [intH] using hb)
        simp only [hT, hadj.symm, hς', ne_eq, not_false_eq_true, true_and]
    _ ≤ ∑ u ∈ Ux, ∑ i, ∑ b ∈ Cz, T u i b := by
        refine sum_le_sum fun u hu => ?_
        refine (sum_le_sum_of_subset (subset_univ _)).trans (sum_le_sum fun i _ => ?_)
        refine sum_le_sum_of_subset fun b hb => ?_
        exact hH (u, b) (by simpa [intH] using hb) hu
    _ ≤ ∑ u, ∑ i, ∑ b ∈ Cz, T u i b := sum_le_sum_of_subset (subset_univ _)
    _ = ∑ b ∈ Cz, ∑ i, ∑ u, T u i b := by
        calc ∑ u, ∑ i, ∑ b ∈ Cz, T u i b = ∑ i, ∑ u, ∑ b ∈ Cz, T u i b := sum_comm
          _ = ∑ i, ∑ b ∈ Cz, ∑ u, T u i b := sum_congr rfl fun i _ => sum_comm
          _ = ∑ b ∈ Cz, ∑ i, ∑ u, T u i b := sum_comm
    _ = coverRowKappa G ς Cz x c' := by
        unfold coverRowKappa
        exact sum_congr rfl fun b _ => sum_congr rfl fun i _ => hc i b

end Integrated

end Sarkozy.ExtractionK
