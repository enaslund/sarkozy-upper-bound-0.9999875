module

public import Sarkozy.L20Cap.StarsX1
public import Sarkozy.Extraction.CollisionCorollaries

/-!
# The collision part in WP-FI's form (`prop:l20-collisions`(a), the input `D`)

`paper/sections/20_middle_reference.tex`, `prop:l20-collisions`(a): the collision part
`T_coll = K_soft 𝟙_{¬Disj}` of the L20 kernel is bounded by the Schur test, with the row sums of
`cor:incident-weights`. Here:

* `schur_test`: a symmetric nonnegative kernel whose rows (on the support of the law) have mean
  at most `R` has form norm at most `R`;
* `Ksoft_eq_collisionKernel`, `Disj_iff`, **`collK_eq`**: `T_coll` is WP-FI's
  `collisionKernel1 + collisionKernel2` of `D₂₀` at the labels (one common label, at least two);
* **`hD_of_incident`**: WP-FI's `collision_rowSum_incident_le` and
  `collision_rowSum2_incident_le` on `λ_p(G6) = μ_p` give the hypothesis `hD` of the caps, for any
  `D` at least `collisionIncident1 + collisionIncident2` at every admissible half;
* `hD_of_oct24`: with WP-FI's `lem:oct24-collision` row sums instead, `hD` holds with the
  explicit, uniform `D = D_1 + D_{≥2}` (weaker than the paper's `D_bal`);
* `ord_val_spec`, `pi_val_spec`: the order data can be met (coordinate orders).
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.L20Cap

open Sarkozy Sarkozy.Recentering Sarkozy.Cuts Sarkozy.Labellings Sarkozy.Extraction
  Sarkozy.ExtractionK

section Schur

variable {Ω : Type*} [Fintype Ω]

/-- **The Schur test** for a symmetric nonnegative kernel. -/
theorem schur_test (ν : FiniteLaw Ω) (K : Ω → Ω → ℝ) (hK0 : ∀ x y, 0 ≤ K x y)
    (hKs : ∀ x y, K x y = K y x) {R : ℝ}
    (hR : ∀ x, 0 < ν.weight x → ν.expect (fun y => K x y) ≤ R) (f : Ω → ℝ) :
    |kernelForm ν ν K f f| ≤ R * nrm ν f ^ 2 := by
  rw [kernelForm_apply, nrm_sq_expect]
  unfold FiniteLaw.expect
  set w := ν.weight with hw
  have hw0 : ∀ x, 0 ≤ w x := ν.nonneg
  -- the double sum
  have e1 : ∑ x, w x * (f x * ∑ y, w y * (K x y * f y)) =
      ∑ x, ∑ y, w x * w y * K x y * (f x * f y) := by
    refine sum_congr rfl fun x _ => ?_
    rw [mul_sum, mul_sum]
    exact sum_congr rfl fun y _ => by ring
  rw [e1]
  have e2 : |∑ x, ∑ y, w x * w y * K x y * (f x * f y)| ≤
      ∑ x, ∑ y, w x * w y * K x y * ((f x ^ 2 + f y ^ 2) / 2) := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun y _ => ?_)
    have h0 : 0 ≤ w x * w y * K x y := mul_nonneg (mul_nonneg (hw0 x) (hw0 y)) (hK0 x y)
    rw [abs_mul, abs_of_nonneg h0]
    refine mul_le_mul_of_nonneg_left ?_ h0
    rw [abs_mul]
    nlinarith [sq_nonneg (|f x| - |f y|), sq_abs (f x), sq_abs (f y), abs_nonneg (f x),
      abs_nonneg (f y)]
  have e3 : ∑ x, ∑ y, w x * w y * K x y * ((f x ^ 2 + f y ^ 2) / 2) =
      ∑ x, w x * f x ^ 2 * ∑ y, w y * K x y := by
    have hs : ∑ x, ∑ y, w x * w y * K x y * f y ^ 2 = ∑ x, ∑ y, w x * w y * K x y * f x ^ 2 := by
      rw [sum_comm]
      refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
      rw [hKs y x]
      ring
    have hsplit : ∑ x, ∑ y, w x * w y * K x y * ((f x ^ 2 + f y ^ 2) / 2) =
        (∑ x, ∑ y, w x * w y * K x y * f x ^ 2 + ∑ x, ∑ y, w x * w y * K x y * f y ^ 2) / 2 := by
      rw [← sum_add_distrib, sum_div]
      refine sum_congr rfl fun x _ => ?_
      rw [← sum_add_distrib, sum_div]
      exact sum_congr rfl fun y _ => by ring
    rw [hsplit, hs]
    have : ∀ x, ∑ y, w x * w y * K x y * f x ^ 2 = w x * f x ^ 2 * ∑ y, w y * K x y := by
      intro x
      rw [mul_sum]
      exact sum_congr rfl fun y _ => by ring
    simp only [this]
    ring
  rw [e3] at e2
  refine e2.trans ?_
  rw [mul_sum]
  refine sum_le_sum fun x _ => ?_
  by_cases hx : 0 < w x
  · have := hR x hx
    unfold FiniteLaw.expect at this
    have h2 : 0 ≤ w x * f x ^ 2 := mul_nonneg (hw0 x) (sq_nonneg _)
    calc w x * f x ^ 2 * ∑ y, w y * K x y ≤ w x * f x ^ 2 * R :=
          mul_le_mul_of_nonneg_left this h2
      _ = R * (w x * f x ^ 2) := by ring
  · have : w x = 0 := le_antisymm (not_lt.mp hx) (hw0 x)
    simp [this]

end Schur

section Coll

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Nonempty (CoreT F)]
  [Nonempty (PairT F)]

omit [Nonempty (CoreT F)] [Nonempty (PairT F)] in
/-- `K_soft` is WP-FI's `collisionKernel` of `D₂₀` at the labels. -/
theorem Ksoft_eq_collisionKernel (hm1 : quadraticChar F (-1) = -1) (x x' : CoreT F × PairT F) :
    Ksoft x x' = collisionKernel D20Z (labels x) (labels x') := by
  rw [Ksoft_eq_softKernel hm1]
  unfold softKernel collisionKernel collisionCross
  have hcD : ∀ i j, crossD i j = (D20Z i j : ℝ) := fun i j => by rw [crossD_eq_D20]; rfl
  rw [prod_filter_of_ne]
  · rw [← Fintype.prod_prod_type']
    refine prod_congr rfl fun e _ => ?_
    rw [hcD]
    by_cases h0 : D20Z e.1 e.2 = 0
    · simp [h0]
    · have := chiPair_supp hm1 h0 (labels x) (labels x')
      unfold chiPair at this
      rw [this]
  · intro e _ he h0
    apply he
    simp [h0]

omit [Nonempty (CoreT F)] [Nonempty (PairT F)] in
theorem Disj_iff (x x' : CoreT F × PairT F) :
    Disj x x' ↔ collisionCommon (labels x) (labels x') = 0 := by
  unfold Disj collisionCommon
  rw [card_eq_zero, ← disjoint_iff_inter_eq_empty, disjoint_left]
  constructor
  · intro h a ha ha'
    obtain ⟨i, -, hi⟩ := mem_image.mp ha
    obtain ⟨j, -, hj⟩ := mem_image.mp ha'
    exact h i j (hi.trans hj.symm)
  · intro h i j hij
    exact h (mem_image_of_mem _ (mem_univ i)) (hij ▸ mem_image_of_mem _ (mem_univ j))

omit [Nonempty (CoreT F)] [Nonempty (PairT F)] in
/-- **`T_coll` is WP-FI's collision kernel** `collisionKernel1 + collisionKernel2` of `D₂₀`. -/
theorem collK_eq (hm1 : quadraticChar F (-1) = -1) (x x' : CoreT F × PairT F) :
    collK x x' = collisionKernel1 D20Z (labels x) (labels x') +
      collisionKernel2 D20Z (labels x) (labels x') := by
  unfold collK collisionKernel1 collisionKernel2
  rw [Ksoft_eq_collisionKernel hm1]
  by_cases hd : Disj x x'
  · have h0 := (Disj_iff x x').mp hd
    simp [hd, h0]
  · have h0 : collisionCommon (labels x) (labels x') ≠ 0 := fun h => hd ((Disj_iff x x').mpr h)
    rcases (by omega : collisionCommon (labels x) (labels x') = 1 ∨
      2 ≤ collisionCommon (labels x) (labels x')) with h | h
    · simp [hd, h]
    · have h1 : collisionCommon (labels x) (labels x') ≠ 1 := by omega
      simp [hd, h, h1]

omit [Nonempty (CoreT F)] [Nonempty (PairT F)] in
theorem collK_nonneg (hm1 : quadraticChar F (-1) = -1) (x x' : CoreT F × PairT F) :
    0 ≤ collK x x' := by
  unfold collK
  split_ifs
  · exact le_refl _
  · unfold Ksoft Rk
    have a1 := Kz_nonneg hm1 x.1.2 x'.2.1.1
    have a2 := Kz_nonneg hm1 x.1.2 x'.2.1.2
    have a3 := Kz_nonneg hm1 x'.1.2 x.2.1.1
    have a4 := Kz_nonneg hm1 x'.1.2 x.2.1.2
    positivity

omit [Nonempty (CoreT F)] [Nonempty (PairT F)] in
theorem collK_symm (x x' : CoreT F × PairT F) : collK x x' = collK x' x := by
  unfold collK
  by_cases hd : Disj x x'
  · have hd' : Disj x' x := Disj_symm hd
    simp [hd, hd']
  · have hd' : ¬ Disj x' x := fun h => hd (Disj_symm h)
    simp only [hd, hd', ↓reduceIte]
    exact Ksoft_symm x x'

/-- **`hD` from `cor:incident-weights`** (`prop:l20-collisions`(a)): WP-FI's row sums of the
collision kernels on `λ_p(G6) = μ_p` (`collision_rowSum_incident_le`,
`collision_rowSum2_incident_le`) and the Schur test give `|⟨f, T_coll f⟩| ≤ D‖f‖²` for any `D`
at least `collisionIncident1 + collisionIncident2` at every admissible half. -/
theorem hD_of_incident (hm1 : quadraticChar F (-1) = -1) (hW : WeilBound F)
    (h6 : 6 ≤ Fintype.card F)
    (hS1 : ∀ v, coarseError (rowsDeg0 G6 v) (Fintype.card F) 6 < 1)
    (ord : Fin 6 → Fin 6 → Fin 6 → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (π : ℕ → Fin 6 → ℕ) (hπ : ∀ k, Function.Injective (π k)) {D : ℝ}
    (hDle : ∀ x : CoreT F × PairT F, Avoid x →
      collisionIncident1 G6 D20Z ord (Fintype.card F) 6 (labels x) +
        collisionIncident2 G6 D20Z π (Fintype.card F) 6 (labels x) ≤ D)
    (f : CoreT F × PairT F → ℝ) :
    |kernelForm (halfLaw h6) (halfLaw h6) collK f f| ≤ D * nrm (halfLaw h6) f ^ 2 := by
  have hne := injLabellings_G6_nonempty (F := F) h6
  have hς : ∀ j k, D20Z j k = 0 ∨ D20Z j k = 1 ∨ D20Z j k = -1 := by decide
  have hn : Fintype.card (Fin 6) ≤ 6 := by simp
  refine schur_test (halfLaw h6) collK (collK_nonneg hm1) collK_symm (fun x hx => ?_) f
  have hAx : Avoid x := by
    by_contra h
    rw [halfLaw_weight_off h6 h] at hx
    exact lt_irrefl _ hx
  have hmem := (labels_mem x).mpr hAx
  rw [mem_injLabellings_iff_feasible] at hmem
  have hinj : Function.Injective (labels x) := fun a b hab =>
    hmem.1 a (mem_univ _) b (mem_univ _) hab
  have e : (halfLaw h6).expect (fun y => collK x y) = (graphLaw G6 hne).expect (fun z' =>
      collisionKernel1 D20Z (labels x) z' + collisionKernel2 D20Z (labels x) z') := by
    rw [graphLaw_eq_halfLaw h6 hne]
    exact (halfLaw h6).expect_congr fun y => collK_eq hm1 x y
  rw [e, FiniteLaw.expect_add]
  have h1 := collision_rowSum_incident_le hW G6 D20Z hς hne hn hS1 ord hord (labels x) hinj
  have h2 := collision_rowSum2_incident_le hW G6 D20Z hς hne hn hS1 π hπ (labels x) hinj
  exact (add_le_add h1 h2).trans (hDle x hAx)

/-- **`hD` from `lem:oct24-collision`** (a uniform, explicit `D`): WP-FI's row sums
`collision_rowSum_le`, `collision_rowSum2_le` and the Schur test give
`|⟨f, T_coll f⟩| ≤ (D_1 + D_{≥2})‖f‖²`. The paper's `D_bal` of `prop:l20-collisions`(a) is
sharper (it uses the incident weights and the row charges of L20, `hD_of_incident`). -/
theorem hD_of_oct24 (hm1 : quadraticChar F (-1) = -1) (hW : WeilBound F)
    (h6 : 6 ≤ Fintype.card F)
    (hS1 : ∀ v, coarseError (rowsDeg0 G6 v) (Fintype.card F) 6 < 1)
    (ord : Fin 6 → Fin 6 → Fin 6 → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (π : ℕ → Fin 6 → ℕ) (hπ : ∀ k, Function.Injective (π k)) (f : CoreT F × PairT F → ℝ) :
    |kernelForm (halfLaw h6) (halfLaw h6) collK f f| ≤
      (collisionD1 G6 D20Z ord (Fintype.card F) 6 + collisionD2 G6 D20Z π (Fintype.card F) 6) *
        nrm (halfLaw h6) f ^ 2 := by
  have hne := injLabellings_G6_nonempty (F := F) h6
  have hς : ∀ j k, D20Z j k = 0 ∨ D20Z j k = 1 ∨ D20Z j k = -1 := by decide
  have hn : Fintype.card (Fin 6) ≤ 6 := by simp
  refine schur_test (halfLaw h6) collK (collK_nonneg hm1) collK_symm (fun x hx => ?_) f
  have hAx : Avoid x := by
    by_contra h
    rw [halfLaw_weight_off h6 h] at hx
    exact lt_irrefl _ hx
  have hmem := (labels_mem x).mpr hAx
  rw [mem_injLabellings_iff_feasible] at hmem
  have hinj : Function.Injective (labels x) := fun a b hab =>
    hmem.1 a (mem_univ _) b (mem_univ _) hab
  have e : (halfLaw h6).expect (fun y => collK x y) = (graphLaw G6 hne).expect (fun z' =>
      collisionKernel1 D20Z (labels x) z' + collisionKernel2 D20Z (labels x) z') := by
    rw [graphLaw_eq_halfLaw h6 hne]
    exact (halfLaw h6).expect_congr fun y => collK_eq hm1 x y
  rw [e, FiniteLaw.expect_add]
  exact add_le_add (collision_rowSum_le hW G6 D20Z hς hne hn hS1 ord hord (labels x) hinj)
    (collision_rowSum2_le hW G6 D20Z hς hne hn hS1 π hπ (labels x) hinj)

end Coll

/-- The coordinate order, for the order data of `hD_of_incident`. -/
def ordVal (_ _ : Fin 6) (ℓ : Fin 6) : ℕ := ℓ.val

/-- The coordinate orders, for the order data of `hD_of_incident`. -/
def piVal (_ : ℕ) (u : Fin 6) : ℕ := u.val

/-- Non-vacuity of the order data of `hD_of_incident`. -/
theorem ord_val_spec : ∀ i j : Fin 6, ∀ ℓ ℓ' : Fin 6, ℓ ≠ i → ℓ' ≠ i →
    ordVal i j ℓ = ordVal i j ℓ' → ℓ = ℓ' := fun _ _ _ _ _ _ h => Fin.val_injective h

theorem pi_val_spec : ∀ k : ℕ, Function.Injective (piVal k) := fun _ => Fin.val_injective

end Sarkozy.L20Cap
