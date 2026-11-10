module

public import Sarkozy.ExtractionK.SoftCollision
public import Sarkozy.Extraction.CollisionStrata

@[expose] public section

/-!
# Soft coincidences with at least two common labels (`cor:soft-kernels`(b), `lem:oct24-collision`(b))

`paper/sections/16_extraction.tex`, `cor:soft-kernels`(b) for the part of `T_coll` on the pairs with
at least two common labels (`collision_opBound2`, `Extraction/CollisionStrata.lean`), with the
method of `SoftCollision.lean`: `skCollKer2`, `sk_collKer2_expand` (convex combination of Boolean
kernels of restricted, flipped signs), `sk_collisionD2_mono` (`Υ_k` and `Ξ` are nondecreasing in
the support), `sk_coll_rowSum2_le`, `sk_collKer2_swap`, and **`sk_soft_collision_opBound2`**:
`‖T^D_coll,≥2‖ ≤ D_{≥2}` for `|D_e| ≤ 1`, antisymmetric signs and `χ(-1) = -1` if some `D_e < 0`.
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

section SkColl2

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The soft collision kernel with at least two common labels:
`1{|x(U⁺) ∩ x'(U⁺)| ≥ 2} ∏_{e ∈ E_×} (1 + D_e χ_e(x, x'))`. -/
noncomputable def skCollKer2 (ς : U → U → ℤ) (D : U × U → ℝ) (x x' : U → F) : ℝ :=
  if 2 ≤ collisionCommon x x' then
    ∏ e ∈ collisionCross ς, (1 + D e * (quadraticChar F ((ς e.1 e.2 : F) * (x' e.2 - x e.1)) : ℝ))
  else 0

/-- **The convex decomposition** of the soft collision kernel. -/
theorem sk_collKer2_expand (ς : U → U → ℤ) (D : U × U → ℝ)
    (hneg : ∀ e, D e < 0 → quadraticChar F (-1) = -1) (x x' : U → F) :
    skCollKer2 ς D x x' = ∑ T ∈ (collisionCross ς).powerset,
      skW D (collisionCross ς) T * collisionKernel2 (skCollSgn ς D T) x x' := by
  unfold skCollKer2 collisionKernel2
  split_ifs with h
  · have hF : ∏ e ∈ collisionCross ς,
        (1 + D e * (quadraticChar F ((ς e.1 e.2 : F) * (x' e.2 - x e.1)) : ℝ)) =
        ∏ e ∈ collisionCross ς, (|D e| * (1 + (quadraticChar F
          ((skCollSgn ς D (collisionCross ς) e.1 e.2 : F) * (x' e.2 - x e.1)) : ℝ)) +
            (1 - |D e|)) :=
      prod_congr rfl fun e he => sk_coll_flip_identity ς D he (hneg e) x x'
    rw [hF, prod_add]
    refine sum_congr rfl fun T hT => ?_
    rw [mem_powerset] at hT
    unfold collisionKernel skW
    rw [sk_collCross_sgn ς D hT, prod_mul_distrib]
    have hTe : ∏ e ∈ T, (1 + (quadraticChar F
        ((skCollSgn ς D (collisionCross ς) e.1 e.2 : F) * (x' e.2 - x e.1)) : ℝ)) =
        ∏ e ∈ T, (1 + (quadraticChar F ((skCollSgn ς D T e.1 e.2 : F) * (x' e.2 - x e.1)) : ℝ)) := by
      refine prod_congr rfl fun e he => ?_
      unfold skCollSgn
      simp only [Prod.mk.eta, he, hT he, ↓reduceIte]
    rw [hTe]
    ring
  · simp

omit [DecidableEq U] in
theorem sk_collKer2_nonneg (ς : U → U → ℤ) (D : U × U → ℝ) (hD : ∀ e, |D e| ≤ 1)
    (x x' : U → F) : 0 ≤ skCollKer2 ς D x x' := by
  unfold skCollKer2
  split_ifs
  · exact prod_nonneg fun e _ => sk_pin_omega_factor_nonneg' (D e) (hD e) _
  · exact le_rfl

/-- Exchanging the two labellings in the soft collision kernel. -/
theorem sk_collKer2_swap (ς : U → U → ℤ) (D : U × U → ℝ) (x x' : U → F) :
    skCollKer2 ς D x x' = skCollKer2 (skT ς) (fun e => D e.swap) x' x := by
  unfold skCollKer2 collisionCommon
  rw [inter_comm]
  split_ifs
  · have hc : collisionCross (skT ς) = (collisionCross ς).image Prod.swap := by
      ext e
      unfold collisionCross skT
      simp only [mem_filter, mem_univ, true_and, mem_image, neg_ne_zero]
      constructor
      · intro h
        exact ⟨e.swap, h, Prod.swap_swap e⟩
      · rintro ⟨e', he', rfl⟩
        simpa using he'
    rw [hc, prod_image (fun a _ b _ h => Prod.swap_injective h)]
    refine prod_congr rfl fun e _ => ?_
    simp only [skT, Prod.fst_swap, Prod.snd_swap, Prod.swap_swap, Int.cast_neg]
    congr 3
    ring_nf
  · rfl


theorem sk_collisionTk_mono (G : OrientedGraph U) {ς ς' : U → U → ℤ}
    (h : ∀ i, rowsN ς' i ⊆ rowsN ς i) (π : ℕ → U → ℕ) (k : ℕ) (i : U) :
    collisionTk G ς' π k i ≤ collisionTk G ς π k i := by
  unfold collisionTk collisionR
  have hc := card_le_card (h i)
  omega

/-- `D_{≥2}` (`lem:oct24-collision`(b)) is nondecreasing in the support of the signs. -/
theorem sk_collisionD2_mono (G : OrientedGraph U) {ς ς' : U → U → ℤ}
    (h : ∀ i, rowsN ς' i ⊆ rowsN ς i) (π : ℕ → U → ℕ) {q : ℝ} (hq : 0 < q) {n : ℕ}
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) q n < 1) :
    collisionD2 G ς' π q n ≤ collisionD2 G ς π q n := by
  unfold collisionD2
  have hL : 0 < collisionLint G q n := prod_pos fun v _ => by linarith [hS1 v]
  have hn2 : (0 : ℝ) ≤ 2 * n := by positivity
  have hXi0 : 0 ≤ collisionXi G ς' q := by
    unfold collisionXi collisionA
    positivity
  have hXi : collisionXi G ς' q ≤ collisionXi G ς q := by
    unfold collisionXi
    refine mul_le_mul_of_nonneg_left (sum_le_sum fun i _ => sum_le_sum fun j _ =>
      sk_collisionA_mono G h i j) (by positivity)
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun k _ => ?_) (inv_nonneg.mpr hL.le)
  have hU0 : 0 ≤ collisionUpsK G ς' π q n k := prod_nonneg fun i _ => by
    linarith [coarseError_nonneg (q := q) hn2 (collisionTk G ς' π k i)]
  have hU : collisionUpsK G ς' π q n k ≤ collisionUpsK G ς π q n k := by
    unfold collisionUpsK
    refine prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_)
    · linarith [coarseError_nonneg (q := q) hn2 (collisionTk G ς' π k i)]
    · linarith [coarseError_mono (q := q) hn2 (sk_collisionTk_mono G h π k i)]
  refine mul_le_mul hU (div_le_div_of_nonneg_right (pow_le_pow_left₀ hXi0 hXi k)
    (by positivity)) (div_nonneg (pow_nonneg hXi0 k) (by positivity)) (le_trans hU0 hU)

theorem sk_collisionD2_congr (G : OrientedGraph U) {ς ς' : U → U → ℤ}
    (h : ∀ i, rowsN ς' i = rowsN ς i) (π : ℕ → U → ℕ) (q : ℝ) (n : ℕ) :
    collisionD2 G ς' π q n = collisionD2 G ς π q n := by
  have hN : rowsN ς' = rowsN ς := funext h
  unfold collisionD2 collisionUpsK collisionTk collisionXi collisionA collisionR rowsMg
  rw [hN]

/-- Row sums of the soft collision kernel with at least two common labels: `≤ D_{≥2}`. -/
theorem sk_coll_rowSum2_le (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hne : (injLabellings F G).Nonempty)
    {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (π : ℕ → U → ℕ)
    (hπ : ∀ k, Function.Injective (π k))
    (D : U × U → ℝ) (hD : ∀ e, |D e| ≤ 1) (hneg : ∀ e, D e < 0 → quadraticChar F (-1) = -1)
    (x : U → F) (hx : Function.Injective x) :
    ∑ x' ∈ injLabellings F G, skCollKer2 ς D x x' / (injLabellings F G).card ≤
      collisionD2 G ς π (Fintype.card F) n := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hw0 : ∀ T ∈ (collisionCross ς).powerset, 0 ≤ skW D (collisionCross ς) T :=
    fun T _ => skW_nonneg (fun e _ => hD e) T
  have hT : ∀ T ∈ (collisionCross ς).powerset,
      ∑ x' ∈ injLabellings F G, collisionKernel2 (skCollSgn ς D T) x x' /
        (injLabellings F G).card ≤ collisionD2 G ς π (Fintype.card F) n := by
    intro T _
    have h := collision_rowSum2_le hW G (skCollSgn ς D T) (sk_collSgn_values hς D T) hne hn hS1 π
      hπ x hx
    rw [coverRow_expect_graphLaw] at h
    rw [← sum_div]
    exact h.trans (sk_collisionD2_mono G (sk_rowsN_collSgn_subset ς D T) π hq hS1)
  simp only [sk_collKer2_expand ς D hneg x]
  calc ∑ x' ∈ injLabellings F G, (∑ T ∈ (collisionCross ς).powerset,
        skW D (collisionCross ς) T * collisionKernel2 (skCollSgn ς D T) x x') /
          (injLabellings F G).card
      = ∑ T ∈ (collisionCross ς).powerset, skW D (collisionCross ς) T *
          ∑ x' ∈ injLabellings F G, collisionKernel2 (skCollSgn ς D T) x x' /
            (injLabellings F G).card := by
        simp only [sum_div, mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun T _ => sum_congr rfl fun x' _ => by ring
    _ ≤ ∑ T ∈ (collisionCross ς).powerset, skW D (collisionCross ς) T *
          collisionD2 G ς π (Fintype.card F) n :=
        sum_le_sum fun T hT' => mul_le_mul_of_nonneg_left (hT T hT') (hw0 T hT')
    _ = _ := by rw [← sum_mul, skW_sum, one_mul]

/-- **`cor:soft-kernels`(b) for `lem:oct24-collision`(b)**: the soft collision operator with at least
two common labels has norm at most `D_{≥2}` (`collision_opBound2`), for `|D_e| ≤ 1`, antisymmetric
signs and `χ(-1) = -1` if some `D_e < 0`. -/
theorem sk_soft_collision_opBound2 (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (π : ℕ → U → ℕ)
    (hπ : ∀ k, Function.Injective (π k))
    (D : U × U → ℝ) (hD : ∀ e, |D e| ≤ 1) (hneg : ∀ e, D e < 0 → quadraticChar F (-1) = -1) :
    Sarkozy.Influence.OpBound (injLabellings F G) (injLabellings F G)
      (fun x x' => skCollKer2 ς D x x' / (injLabellings F G).card)
      (collisionD2 G ς π (Fintype.card F) n) := by
  have hN : (0 : ℝ) < (injLabellings F G).card := by exact_mod_cast card_pos.mpr hne
  have hinj : ∀ x ∈ injLabellings F G, Function.Injective x := fun x hx a b h => by
    simp only [injLabellings, mem_filter, mem_univ, true_and] at hx
    exact hx.1 a (mem_univ _) b (mem_univ _) h
  have hrow : ∀ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G,
      skCollKer2 ς D x x' / (injLabellings F G).card ≤ collisionD2 G ς π (Fintype.card F) n :=
    fun x hx => sk_coll_rowSum2_le hW G ς hς hne hn hS1 π hπ D hD hneg x (hinj x hx)
  have hsupp : ∀ i, rowsN (skT ς) i = rowsN ς i := by
    intro i
    unfold rowsN skT
    exact filter_congr fun j _ => by rw [hanti i j]
  have hcol : ∀ x' ∈ injLabellings F G, ∑ x ∈ injLabellings F G,
      skCollKer2 ς D x x' / (injLabellings F G).card ≤ collisionD2 G ς π (Fintype.card F) n := by
    intro x' hx'
    have h := sk_coll_rowSum2_le hW G (skT ς) (skT_values ς hς) hne hn hS1 π hπ
      (fun e => D e.swap) (fun e => hD e.swap) (fun e he => hneg e.swap he) x' (hinj x' hx')
    rw [sk_collisionD2_congr G hsupp] at h
    calc ∑ x ∈ injLabellings F G, skCollKer2 ς D x x' / (injLabellings F G).card
        = ∑ x ∈ injLabellings F G, skCollKer2 (skT ς) (fun e => D e.swap) x' x /
            (injLabellings F G).card :=
          sum_congr rfl fun x _ => by rw [sk_collKer2_swap]
      _ ≤ _ := h
  obtain ⟨x0, hx0⟩ := hne
  have hD1 : 0 ≤ collisionD2 G ς π (Fintype.card F) n :=
    le_trans (sum_nonneg fun x' _ => div_nonneg (sk_collKer2_nonneg ς D hD x0 x') hN.le)
      (hrow x0 hx0)
  have h := Sarkozy.Influence.opBound_schur (R := injLabellings F G) (C := injLabellings F G)
    (fun x x' => div_nonneg (sk_collKer2_nonneg ς D hD x x') hN.le) hD1 hD1 hrow hcol
  rwa [Real.sqrt_mul_self hD1] at h

end SkColl2

end Sarkozy.ExtractionK
