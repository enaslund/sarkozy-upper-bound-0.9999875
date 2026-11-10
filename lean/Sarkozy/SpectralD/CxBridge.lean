module

public import Sarkozy.SpectralD.CxExpansion
public import Sarkozy.ExtractionK.Compressed
public import Sarkozy.ExtractionK.GroupedNorm
public import Sarkozy.Extraction.CollisionStrata

@[expose] public section

/-!
# From `L²(μ)` kernel bounds to WP-A's operator bounds

X1's extraction bounds (`ExtractionK.grouped_extraction_norm` and its corollaries) and the
collision bounds of `Extraction` are stated in `L²(μ)`:
`E_x (E_{x'} k(x, x') h(x'))² ≤ B² E h²` for all `h`. `kernelOp_norm_le_of_expect` turns such a
bound into `‖T_k v‖ ≤ B ‖v‖` for WP-A's realization `Spectral.kernelOp μ k` on
`EuclideanSpace ℝ Ω` (the weights `√μ` are absorbed by `h = v/√μ` on the support of `μ`).

New material for this paper.
-/

namespace Sarkozy.SpectralD.Cx

open Finset
open scoped BigOperators InnerProductSpace

variable {Ω : Type*} [Fintype Ω]

/-- **`L²(μ)` bound ⇒ operator bound** for WP-A's `kernelOp`. -/
theorem kernelOp_norm_le_of_expect (μ : FiniteLaw Ω) (k : Ω → Ω → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ g : Ω → ℝ, μ.expect (fun x => (μ.expect (fun x' => k x x' * g x')) ^ 2) ≤
      B ^ 2 * μ.expect (fun x => g x ^ 2))
    (v : EuclideanSpace ℝ Ω) : ‖Spectral.kernelOp μ k v‖ ≤ B * ‖v‖ := by
  classical
  set g : Ω → ℝ := fun x => if μ.weight x = 0 then 0 else v.ofLp x / √(μ.weight x) with hg
  have hrow : ∀ x', √(μ.weight x') * v.ofLp x' = μ.weight x' * g x' := by
    intro x'
    by_cases h0 : μ.weight x' = 0
    · simp [hg, h0]
    · have hpos : 0 < μ.weight x' := lt_of_le_of_ne (μ.nonneg x') (Ne.symm h0)
      have hs : √(μ.weight x') ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
      simp only [hg, h0, ↓reduceIte]
      field_simp
      rw [Real.sq_sqrt (μ.nonneg x')]
      ring
  have hK : ∀ x, (Spectral.kernelOp μ k v).ofLp x =
      √(μ.weight x) * μ.expect (fun x' => k x x' * g x') := by
    intro x
    rw [Spectral.kernelOp_ofLp]
    unfold FiniteLaw.expect
    rw [mul_sum]
    refine sum_congr rfl fun x' _ => ?_
    have := hrow x'
    calc √(μ.weight x) * k x x' * √(μ.weight x') * v.ofLp x'
        = √(μ.weight x) * k x x' * (√(μ.weight x') * v.ofLp x') := by ring
      _ = √(μ.weight x) * (μ.weight x' * (k x x' * g x')) := by rw [this]; ring
  have hL : ‖Spectral.kernelOp μ k v‖ ^ 2 =
      μ.expect (fun x => (μ.expect (fun x' => k x x' * g x')) ^ 2) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    show _ = ∑ x, μ.weight x * (μ.expect (fun x' => k x x' * g x')) ^ 2
    refine sum_congr rfl fun x _ => ?_
    rw [hK x, mul_pow, Real.sq_sqrt (μ.nonneg x)]
  have hR : μ.expect (fun x => g x ^ 2) ≤ ‖v‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    unfold FiniteLaw.expect
    refine sum_le_sum fun x _ => ?_
    by_cases h0 : μ.weight x = 0
    · simp [hg, h0, sq_nonneg]
    · have hpos : 0 < μ.weight x := lt_of_le_of_ne (μ.nonneg x) (Ne.symm h0)
      have hs : √(μ.weight x) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
      simp only [hg, h0, ↓reduceIte]
      rw [div_pow, Real.sq_sqrt (μ.nonneg x)]
      field_simp
      exact le_refl _
  have hsq : ‖Spectral.kernelOp μ k v‖ ^ 2 ≤ (B * ‖v‖) ^ 2 := by
    rw [hL, mul_pow]
    exact (h g).trans (mul_le_mul_of_nonneg_left hR (sq_nonneg B))
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hB (norm_nonneg _)) two_ne_zero).mp hsq

/-- **Bilinear `L²(μ)` bound ⇒ operator bound** (the form of X1's extraction theorems). -/
theorem kernelOp_norm_le_of_bilinear (μ : FiniteLaw Ω) (k : Ω → Ω → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ f g : Ω → ℝ, |μ.expect (fun x => f x * μ.expect (fun x' => k x x' * g x'))| ≤
      B * Real.sqrt (μ.expect (fun x => f x ^ 2)) * Real.sqrt (μ.expect (fun x => g x ^ 2)))
    (v : EuclideanSpace ℝ Ω) : ‖Spectral.kernelOp μ k v‖ ≤ B * ‖v‖ := by
  refine kernelOp_norm_le_of_expect μ k hB (fun g => ?_) v
  set F : Ω → ℝ := fun x => μ.expect (fun x' => k x x' * g x') with hF
  have h0 : 0 ≤ μ.expect (fun x => F x ^ 2) := μ.second_moment_nonneg F
  have h1 : 0 ≤ μ.expect (fun x => g x ^ 2) := μ.second_moment_nonneg g
  have e : μ.expect (fun x => F x ^ 2) = μ.expect (fun x => F x * μ.expect (fun x' => k x x' * g x')) :=
    μ.expect_congr fun x => sq (F x)
  refine ExtractionK.le_sq_mul_of_le_sqrt h0 h1 ?_
  calc μ.expect (fun x => F x ^ 2) ≤ |μ.expect (fun x => F x * μ.expect (fun x' => k x x' * g x'))| := by
        rw [e]; exact le_abs_self _
    _ ≤ B * Real.sqrt (μ.expect (fun x => F x ^ 2)) * Real.sqrt (μ.expect (fun x => g x ^ 2)) :=
        h F g

/-- **Matrix bound on `Inj` ⇒ operator bound** for the graph law (the normalization of
`Extraction`'s collision bounds: `OpBound 𝓘 𝓘 (K/|𝓘|) D`). -/
theorem kernelOp_norm_le_of_opBound {V : Type*} [Fintype V] [DecidableEq V] {p : ℕ} [Fact p.Prime]
    (G : Labellings.OrientedGraph V) (hne : (Labellings.injLabellings (ZMod p) G).Nonempty)
    (K : (V → ZMod p) → (V → ZMod p) → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (h : Sarkozy.Influence.OpBound (Labellings.injLabellings (ZMod p) G)
      (Labellings.injLabellings (ZMod p) G)
      (fun x x' => K x x' / (Labellings.injLabellings (ZMod p) G).card) D)
    (v : EuclideanSpace ℝ (V → ZMod p)) :
    ‖Spectral.kernelOp (Labellings.graphLaw G hne) K v‖ ≤ D * ‖v‖ := by
  classical
  set I := Labellings.injLabellings (ZMod p) G with hI
  have hN : (0 : ℝ) < I.card := by exact_mod_cast card_pos.mpr hne
  have hw : ∀ x, (Labellings.graphLaw G hne).weight x = if x ∈ I then 1 / (I.card : ℝ) else 0 :=
    fun x => rfl
  have hsq : ∀ x, √((Labellings.graphLaw G hne).weight x) =
      if x ∈ I then √(1 / (I.card : ℝ)) else 0 := by
    intro x; rw [hw]; split_ifs <;> simp
  have hss : √(1 / (I.card : ℝ)) * √(1 / (I.card : ℝ)) = 1 / I.card :=
    Real.mul_self_sqrt (by positivity)
  have hK : ∀ x, (Spectral.kernelOp (Labellings.graphLaw G hne) K v).ofLp x =
      if x ∈ I then ∑ x' ∈ I, K x x' / I.card * v.ofLp x' else 0 := by
    intro x
    rw [Spectral.kernelOp_ofLp]
    by_cases hx : x ∈ I
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hx), ← sum_filter_add_sum_filter_not univ
        (fun x' => x' ∈ I)]
      have h2 : ∑ x' ∈ univ.filter (fun x' => ¬ x' ∈ I), √((Labellings.graphLaw G hne).weight x) *
          K x x' * √((Labellings.graphLaw G hne).weight x') * v.ofLp x' = 0 := by
        refine sum_eq_zero fun x' hx' => ?_
        rw [mem_filter] at hx'
        rw [hsq x', ite_eq_right_of_eq_false _ _ (eq_false hx'.2)]
        ring
      rw [h2, add_zero, filter_mem_eq_inter, univ_inter]
      refine sum_congr rfl fun x' hx' => ?_
      rw [hsq x, hsq x', ite_eq_left_of_eq_true _ _ (eq_true hx),
        ite_eq_left_of_eq_true _ _ (eq_true hx')]
      calc √(1 / (I.card : ℝ)) * K x x' * √(1 / (I.card : ℝ)) * v.ofLp x'
          = (√(1 / (I.card : ℝ)) * √(1 / (I.card : ℝ))) * K x x' * v.ofLp x' := by ring
        _ = K x x' / I.card * v.ofLp x' := by rw [hss]; ring
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hx)]
      refine sum_eq_zero fun x' _ => ?_
      rw [hsq x, ite_eq_right_of_eq_false _ _ (eq_false hx)]
      ring
  have hL : ‖Spectral.kernelOp (Labellings.graphLaw G hne) K v‖ ^ 2 =
      ∑ x ∈ I, (∑ x' ∈ I, K x x' / I.card * v.ofLp x') ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, ← sum_filter_add_sum_filter_not univ (fun x => x ∈ I)]
    have h2 : ∑ x ∈ univ.filter (fun x => ¬ x ∈ I),
        ((Spectral.kernelOp (Labellings.graphLaw G hne) K v) x) ^ 2 = 0 := by
      refine sum_eq_zero fun x hx => ?_
      rw [mem_filter] at hx
      have := hK x
      rw [ite_eq_right_of_eq_false _ _ (eq_false hx.2)] at this
      simp [this]
    rw [h2, add_zero, filter_mem_eq_inter, univ_inter]
    refine sum_congr rfl fun x hx => ?_
    have := hK x
    rw [ite_eq_left_of_eq_true _ _ (eq_true hx)] at this
    simp [this]
  have hR : ∑ x' ∈ I, v.ofLp x' ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun x _ _ => sq_nonneg _)
  have hsq2 : ‖Spectral.kernelOp (Labellings.graphLaw G hne) K v‖ ^ 2 ≤ (D * ‖v‖) ^ 2 := by
    rw [hL, mul_pow]
    exact (h (fun x' => v.ofLp x')).trans (mul_le_mul_of_nonneg_left hR (sq_nonneg D))
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hD (norm_nonneg _)) two_ne_zero).mp hsq2

section Cut

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W] (D : Cuts.SpecData W)

/-- `K_coll` is `Extraction`'s collision kernel `collisionKernelColl` for `ς = D.sgn`. -/
lemma collKer_eq (x x' : D.cut.Half → ZMod p) :
    collKer D x x' = Extraction.collisionKernelColl D.sgn x x' := by
  classical
  unfold collKer Extraction.collisionKernelColl Extraction.collisionCommon
  by_cases hd : Disjoint (univ.image x) (univ.image x')
  · have h0 : (univ.image x ∩ univ.image x').card = 0 := by
      rw [card_eq_zero]; exact disjoint_iff_inter_eq_empty.mp hd
    simp only [hd, h0, ↓reduceIte]
    simp
  · have h1 : 1 ≤ (univ.image x ∩ univ.image x').card := by
      rw [Nat.one_le_iff_ne_zero, Ne, card_eq_zero]
      exact fun h => hd (disjoint_iff_inter_eq_empty.mpr h)
    simp only [hd, h1, ↓reduceIte]
    rfl

end Cut

end Sarkozy.SpectralD.Cx
