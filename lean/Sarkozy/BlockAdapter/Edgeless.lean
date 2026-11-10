module

public import Sarkozy.BlockAdapter.E21

@[expose] public section

/-!
# The per-prime cap of the cut of an edgeless graph

The argument of `E21.lean` for any spectral data `D` whose graph has no edges (for instance the
layer cut of the upper `E × E` graph `G_{EE,2}`, `UpperEE.lean`): with `n = |U⁺|`, the half law is
uniform on the injective maps `U⁺ → 𝔽_p`, the cut kernel is the disjointness indicator, and

* `edgeless_upper`: `A ⪯ 1` (the row means are `Z` on the support, by the transitivity of the
  permutations of `𝔽_p`);
* `edgeless_cutZ_ge`: `Z ≥ 1 - n²/p`;
* **`edgeless_cutCap`**: `-g p^{-1/2} ⪯ A ⪯ 1 + B/p` whenever `n²/(p - n²) ≤ g p^{-1/2}`,
  `p > n²` and `B ≥ 0`;
* `edgeless_gate`: the condition `n²/(p - n²) ≤ g p^{-1/2}` from `g ≤ 1`, `n² ≤ X`,
  `(n² + g)² ≤ g² X` and `X ≤ p` (no square roots).
-/

open scoped InnerProductSpace
open Finset

namespace Sarkozy.BlockAdapter

open Sarkozy Sarkozy.Labellings Sarkozy.PartV Sarkozy.Cuts

section Edgeless

variable {U : Type} [Fintype U] [DecidableEq U] (D : SpecData U) (hE : D.G.E = ∅)
  {p : ℕ} [Fact p.Prime]

include hE

theorem edgeless_crossPairs : D.crossPairs = ∅ := by
  ext q
  simp [SpecData.crossPairs, SpecData.sgn, hE]

theorem edgeless_cutK (x x' : D.cut.Half → ZMod p) :
    D.cutK x x' = if Disjoint (univ.image x) (univ.image x') then 1 else 0 := by
  rw [SpecData.cutK_eq_prod, edgeless_crossPairs D hE, Finset.prod_empty, mul_one]

theorem edgeless_half_mem_iff (x : D.cut.Half → ZMod p) :
    x ∈ injLabellings (ZMod p) D.halfGraph ↔ Function.Injective x := by
  rw [mem_injLabellings_iff_feasible]
  simp [Feasible, SpecData.halfGraph, hE, Function.Injective]

variable (hne : (injLabellings (ZMod p) D.G).Nonempty)

theorem edgeless_weight_comp (σ : Equiv.Perm (ZMod p)) (x : D.cut.Half → ZMod p) :
    (D.halfLaw hne).weight (⇑σ ∘ x) = (D.halfLaw hne).weight x := by
  simp only [SpecData.halfLaw, graphLaw, edgeless_half_mem_iff D hE, σ.injective.of_comp_iff]

theorem edgeless_injective_of_weight {x : D.cut.Half → ZMod p}
    (hx : (D.halfLaw hne).weight x ≠ 0) : Function.Injective x := by
  rw [← edgeless_half_mem_iff D hE]
  by_contra h
  apply hx
  simp only [SpecData.halfLaw, graphLaw, h, ↓reduceIte]

theorem edgeless_cutK_comp (σ : Equiv.Perm (ZMod p)) (x x' : D.cut.Half → ZMod p) :
    D.cutK (⇑σ ∘ x) (⇑σ ∘ x') = D.cutK x x' := by
  rw [edgeless_cutK D hE, edgeless_cutK D hE, ← Finset.image_image, ← Finset.image_image]
  simp only [Finset.disjoint_image σ.injective]

omit hE in
/-- The row mean `R(x) = E_{x'} K(x, x')`. -/
noncomputable def edgeRow (x : D.cut.Half → ZMod p) : ℝ :=
  ∑ y, (D.halfLaw hne).weight y * D.cutK x y

theorem edgeRow_comp (σ : Equiv.Perm (ZMod p)) (x : D.cut.Half → ZMod p) :
    edgeRow D hne (⇑σ ∘ x) = edgeRow D hne x := by
  unfold edgeRow
  refine (Fintype.sum_equiv (postcomp σ) _ _ fun y => ?_).symm
  change _ = (D.halfLaw hne).weight (⇑σ ∘ y) * D.cutK (⇑σ ∘ x) (⇑σ ∘ y)
  rw [edgeless_weight_comp D hE, edgeless_cutK_comp D hE]

omit hE in
theorem edge_cutZ_eq : D.cutZ hne = ∑ y, (D.halfLaw hne).weight y * edgeRow D hne y := by
  unfold SpecData.cutZ
  rw [FiniteLaw.expect_product]
  rfl

theorem edgeRow_eq_cutZ (x : D.cut.Half → ZMod p) (hx : (D.halfLaw hne).weight x ≠ 0) :
    edgeRow D hne x = D.cutZ hne := by
  have hxi := edgeless_injective_of_weight D hE hne hx
  have hconst : ∀ y, (D.halfLaw hne).weight y ≠ 0 → edgeRow D hne y = edgeRow D hne x := by
    intro y hy
    obtain ⟨σ, hσ⟩ := exists_perm_comp_eq hxi (edgeless_injective_of_weight D hE hne hy)
    rw [← hσ, edgeRow_comp D hE]
  rw [edge_cutZ_eq]
  calc edgeRow D hne x = ∑ y, (D.halfLaw hne).weight y * edgeRow D hne x := by
        rw [← Finset.sum_mul, (D.halfLaw hne).total, one_mul]
    _ = ∑ y, (D.halfLaw hne).weight y * edgeRow D hne y :=
        Finset.sum_congr rfl fun y _ => by
          by_cases hy : (D.halfLaw hne).weight y = 0
          · rw [hy, zero_mul, zero_mul]
          · rw [hconst y hy]

omit hE in
theorem edge_vertex (d : D.cut.Half) (c : ZMod p) :
    ∑ y, (D.halfLaw hne).weight y * (if y d = c then (1 : ℝ) else 0) = 1 / p := by
  have h := graphLaw_vertex_uniform D.halfGraph (D.half_nonempty hne) d
    (fun z => if z = c then (1 : ℝ) else 0)
  change (D.halfLaw hne).expect (fun y => if y d = c then (1 : ℝ) else 0) = _
  rw [show D.halfLaw hne = graphLaw D.halfGraph (D.half_nonempty hne) from rfl, h,
    FiniteLaw.expect_uniform]
  simp [ZMod.card]

omit hE in
/-- The number of coincidences `x_c = x'_d`. -/
noncomputable def edgeColl (x y : D.cut.Half → ZMod p) : ℝ :=
  ∑ c, ∑ d, if x c = y d then (1 : ℝ) else 0

theorem one_sub_cutK_le_edgeColl (x y : D.cut.Half → ZMod p) :
    1 - D.cutK x y ≤ edgeColl D x y := by
  rw [edgeless_cutK D hE]
  have hnn : ∀ c d, (0 : ℝ) ≤ if x c = y d then (1 : ℝ) else 0 := fun c d => by
    split_ifs <;> norm_num
  by_cases h : Disjoint (univ.image x) (univ.image y)
  · simp only [h, ↓reduceIte, sub_self]
    exact Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun d _ => hnn c d
  · simp only [h, ↓reduceIte, sub_zero]
    obtain ⟨a, ha, hb⟩ := Finset.not_disjoint_iff.mp h
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨d, -, hd⟩ := Finset.mem_image.mp hb
    have h1 : (if x c = y d then (1 : ℝ) else 0) = 1 := by simp [hd]
    calc (1 : ℝ) = if x c = y d then (1 : ℝ) else 0 := h1.symm
      _ ≤ ∑ d', if x c = y d' then (1 : ℝ) else 0 :=
          Finset.single_le_sum (fun d' _ => hnn c d') (Finset.mem_univ d)
      _ ≤ edgeColl D x y :=
          Finset.single_le_sum (f := fun c' => ∑ d', if x c' = y d' then (1 : ℝ) else 0)
            (fun c' _ => Finset.sum_nonneg fun d' _ => hnn c' d') (Finset.mem_univ c)

omit hE in
theorem edgeColl_row (x : D.cut.Half → ZMod p) :
    ∑ y, (D.halfLaw hne).weight y * edgeColl D x y =
      (Fintype.card D.cut.Half : ℝ) ^ 2 / p := by
  unfold edgeColl
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ c d, ∑ y, (D.halfLaw hne).weight y * (if x c = y d then (1 : ℝ) else 0) =
      1 / p := by
    intro c d
    rw [← edge_vertex D hne d (x c)]
    exact Finset.sum_congr rfl fun y _ => by simp only [eq_comm]
  rw [Finset.sum_congr rfl fun c _ => (Finset.sum_comm.trans
    (Finset.sum_congr rfl fun d _ => h c d))]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

omit hE in
theorem edgeColl_col (y : D.cut.Half → ZMod p) :
    ∑ x, (D.halfLaw hne).weight x * edgeColl D x y =
      (Fintype.card D.cut.Half : ℝ) ^ 2 / p := by
  unfold edgeColl
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ c d, ∑ x, (D.halfLaw hne).weight x * (if x c = y d then (1 : ℝ) else 0) =
      1 / p := fun c d => edge_vertex D hne c (y d)
  rw [Finset.sum_congr rfl fun c _ => (Finset.sum_comm.trans
    (Finset.sum_congr rfl fun d _ => h c d))]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

theorem edgeless_cutK_le_one (x y : D.cut.Half → ZMod p) : D.cutK x y ≤ 1 := by
  rw [edgeless_cutK D hE]
  split_ifs <;> norm_num

/-- `Z ≥ 1 - n²/p`. -/
theorem edgeless_cutZ_ge :
    1 - (Fintype.card D.cut.Half : ℝ) ^ 2 / p ≤ D.cutZ hne := by
  have hR : ∀ x, 1 - (Fintype.card D.cut.Half : ℝ) ^ 2 / p ≤ edgeRow D hne x := by
    intro x
    have h1 : ∑ y, (D.halfLaw hne).weight y * (1 - edgeColl D x y) ≤ edgeRow D hne x :=
      Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
        (by linarith [one_sub_cutK_le_edgeColl D hE x y]) ((D.halfLaw hne).nonneg y)
    have h2 : ∑ y, (D.halfLaw hne).weight y * (1 - edgeColl D x y) =
        1 - (Fintype.card D.cut.Half : ℝ) ^ 2 / p := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib, (D.halfLaw hne).total,
        edgeColl_row D hne x]
    linarith
  rw [edge_cutZ_eq]
  calc 1 - (Fintype.card D.cut.Half : ℝ) ^ 2 / p =
        ∑ x, (D.halfLaw hne).weight x * (1 - (Fintype.card D.cut.Half : ℝ) ^ 2 / p) := by
        rw [← Finset.sum_mul, (D.halfLaw hne).total, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun x _ =>
        mul_le_mul_of_nonneg_left (hR x) ((D.halfLaw hne).nonneg x)

omit hne in
/-- **The per-prime cap of the cut of an edgeless graph.** -/
theorem edgeless_cutCap {g B : ℝ} (hB : 0 ≤ B)
    (hp : (Fintype.card D.cut.Half : ℝ) ^ 2 < p)
    (hg : (Fintype.card D.cut.Half : ℝ) ^ 2 / ((p : ℝ) - (Fintype.card D.cut.Half : ℝ) ^ 2) ≤
      g * (√(p : ℝ))⁻¹)
    (hne : (injLabellings (ZMod p) D.G).Nonempty) (v : EuclideanSpace ℝ (D.cut.Half → ZMod p)) :
    -(g * (√(p : ℝ))⁻¹) * ‖v‖ ^ 2 ≤ ⟪v, Spectral.cutOp D hne v⟫_ℝ ∧
      ⟪v, Spectral.cutOp D hne v⟫_ℝ ≤ (1 + B / p) * ‖v‖ ^ 2 := by
  set n2 : ℝ := (Fintype.card D.cut.Half : ℝ) ^ 2 with hn2
  have hZpos := D.cutZ_pos hne
  have hZge := edgeless_cutZ_ge D hE hne
  have hn0 : 0 ≤ n2 := by positivity
  have hp0 : (0 : ℝ) < p := by linarith
  have hv := sq_nonneg ‖v‖
  constructor
  · have h := kernel_quad_lower (D.halfLaw hne) D.cutK (edgeColl D) (edgeless_cutK_le_one D hE)
      (one_sub_cutK_le_edgeColl D hE) hZpos (fun x => (edgeColl_row D hne x).le)
      (fun y => (edgeColl_col D hne y).le) v
    have hc : n2 / (p : ℝ) / D.cutZ hne ≤ g * (√(p : ℝ))⁻¹ := by
      have hZ' : ((p : ℝ) - n2) / p ≤ D.cutZ hne := by
        have : ((p : ℝ) - n2) / p = 1 - n2 / p := by field_simp
        rw [this]
        exact hZge
      have hpos : 0 < ((p : ℝ) - n2) / p := div_pos (by linarith) hp0
      calc n2 / (p : ℝ) / D.cutZ hne ≤ n2 / (p : ℝ) / (((p : ℝ) - n2) / p) :=
            div_le_div_of_nonneg_left (by positivity) hpos hZ'
        _ = n2 / ((p : ℝ) - n2) := by
            field_simp
        _ ≤ _ := hg
    calc -(g * (√(p : ℝ))⁻¹) * ‖v‖ ^ 2 ≤ -(n2 / (p : ℝ) / D.cutZ hne) * ‖v‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) hv
      _ ≤ _ := h
  · have h := kernel_quad_upper (D.halfLaw hne) D.cutK (fun x y => D.cutK_nonneg x y)
      (fun x y => D.cutK_symm y x) hZpos (fun x hx => (edgeRow_eq_cutZ D hE hne x hx).le) v
    have hBp : 0 ≤ B / p := div_nonneg hB hp0.le
    calc _ ≤ ‖v‖ ^ 2 := h
      _ ≤ (1 + B / p) * ‖v‖ ^ 2 := by nlinarith

end Edgeless

/-- **The gate without square roots**: `g ≤ 1`, `N ≤ X`, `(N + g)² ≤ g² X` and `X ≤ p` give
`N/(p - N) ≤ g p^{-1/2}` (with `N = n²`), and `N < p` when `N ≥ 1`. -/
theorem edgeless_gate {g N X p : ℝ} (hg : 0 < g) (hg1 : g ≤ 1) (hN : 1 ≤ N)
    (hNX : N ^ 2 ≤ X) (hgX : (N + g) ^ 2 ≤ g ^ 2 * X) (hXp : X ≤ p) :
    N < p ∧ N / (p - N) ≤ g * (√p)⁻¹ := by
  have hX0 : 0 ≤ X := le_trans (sq_nonneg _) hNX
  have hp0 : 0 ≤ p := le_trans hX0 hXp
  set s := √p with hs
  have hsq : s ^ 2 = p := Real.sq_sqrt hp0
  have hs0 : 0 ≤ s := Real.sqrt_nonneg p
  -- `s ≥ N` and `g s ≥ N + g`
  have hsN : N ≤ s := by
    rw [hs]
    exact Real.le_sqrt_of_sq_le (hNX.trans hXp)
  have hgs : N + g ≤ g * s := by
    have h1 : (N + g) ^ 2 ≤ (g * s) ^ 2 := by
      rw [mul_pow, hsq]
      exact hgX.trans (mul_le_mul_of_nonneg_left hXp (sq_nonneg g))
    have h2 : 0 ≤ g * s := mul_nonneg hg.le hs0
    nlinarith [sq_nonneg (N + g - g * s), sq_nonneg (N + g + g * s)]
  have hNp : N < p := by
    have : N < s ^ 2 := by nlinarith
    linarith
  refine ⟨hNp, ?_⟩
  have hspos : 0 < s := lt_of_lt_of_le (by linarith) hsN
  rw [div_le_iff₀ (by linarith), ← div_eq_mul_inv, div_mul_eq_mul_div, le_div_iff₀ hspos]
  -- `N s ≤ g (s² - N)`
  rw [← hsq]
  nlinarith

end Sarkozy.BlockAdapter
