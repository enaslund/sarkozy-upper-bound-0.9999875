module

public import Sarkozy.SpectralC.HiddenFeature

@[expose] public section

/-!
# Conditional expectations and `lem:hidden-feature`

`paper/sections/14_spectral.tex`, `lem:hidden-feature`. For a law `μ` on labellings and a set `A`
of coordinates, `condE μ A F` is the conditional expectation `Π_A F = E_μ[F | x_A]` (`agree`,
`cmass`). It contracts in `L²(μ)` (`condE_contract`, from Jensen on each class,
`norm_condE_sq_le`, and the law of total expectation, `sum_mu_class`) and satisfies the tower
property `Π_A Π_B = Π_A` for `A ⊆ B` (`condE_tower`).

The conditional law of one coordinate is `condLaw μ j x t = ν_j(t | x)`. `Π_{U∖j} V_j` is the
kernel map of `ν_j` (`condE_vert`). For `j ∈ S`, `Π_{U∖j} W_S` is the kernel map of
`p⁻¹ φ_j ψ_{S∖j}` (`condE_star`, `prod_update`). Both kernels are covariant when `μ` is invariant
(`condLaw_cov`, `pivotKer_cov`).

With the kernel bounds of `Sarkozy.SpectralC.HiddenFeature`, this gives `lem:hidden-feature`
(`p ≡ 3 (mod 4)`; `j ∉ O`; conditional probabilities of `x_j` at most `D/p`):
* `hidden_feature_vert`: `‖Π_O V_j‖² ≤ q(D − 1)/(1 − q)`;
* `hidden_feature_star` (`j ∈ S`): `‖Π_O(W_S/r)‖² ≤ q(D − 1)/(1 − q)`.

The statements are in squared form on `L²_0`, that is `‖Π_O V_j‖ ≤ r((D − 1)/(1 − q))^{1/2}` and
the same for `W_S/r`. Only the law `μ` (invariant, a probability) is assumed: no independence of
the unobserved coordinates is used.

New material for this paper.
-/

namespace Sarkozy.SpectralC

open Finset Complex Sarkozy.Characters
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

/-- `x'` agrees with `x` on `A`. -/
def agree (A : Finset U) (x x' : U → ZMod p) : Prop := ∀ i ∈ A, x' i = x i

instance (A : Finset U) (x x' : U → ZMod p) : Decidable (agree A x x') := by
  unfold agree; infer_instance

omit [Fact p.Prime] [Fintype U] [DecidableEq U] in
lemma agree_comm {A : Finset U} {x x' : U → ZMod p} : agree A x x' ↔ agree A x' x :=
  ⟨fun h i hi => (h i hi).symm, fun h i hi => (h i hi).symm⟩

omit [Fact p.Prime] [Fintype U] [DecidableEq U] in
lemma agree_trans {A : Finset U} {x x' x'' : U → ZMod p} (h1 : agree A x x') (h2 : agree A x' x'') :
    agree A x x'' := fun i hi => (h2 i hi).trans (h1 i hi)

omit [Fact p.Prime] [Fintype U] [DecidableEq U] in
lemma agree_mono {A B : Finset U} (hAB : A ⊆ B) {x x' : U → ZMod p} (h : agree B x x') :
    agree A x x' := fun i hi => h i (hAB hi)

/-- The mass `μ(x' : x'_A = x_A)`. -/
noncomputable def cmass (μ : (U → ZMod p) → ℝ) (A : Finset U) (x : U → ZMod p) : ℝ :=
  ∑ x', if agree A x x' then μ x' else 0

/-- The conditional expectation `(Π_A F)(x) = E_μ[F | x_A]`. -/
noncomputable def condE (μ : (U → ZMod p) → ℝ) (A : Finset U) (F : (U → ZMod p) → ℂ)
    (x : U → ZMod p) : ℂ :=
  (∑ x', if agree A x x' then (μ x' : ℂ) * F x' else 0) / (cmass μ A x : ℂ)

lemma cmass_congr (μ : (U → ZMod p) → ℝ) (A : Finset U) {x x' : U → ZMod p}
    (h : agree A x x') : cmass μ A x = cmass μ A x' := by
  unfold cmass
  refine sum_congr rfl fun y _ => ?_
  have : agree A x y ↔ agree A x' y :=
    ⟨fun hy => agree_trans (agree_comm.mp h) hy, fun hy => agree_trans h hy⟩
  by_cases hy : agree A x y
  · rw [ite_eq_left hy, ite_eq_left (this.mp hy)]
  · rw [ite_eq_right hy, ite_eq_right (fun h' => hy (this.mpr h'))]

lemma mu_le_cmass (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (A : Finset U) (x : U → ZMod p) :
    μ x ≤ cmass μ A x := by
  unfold cmass
  have h0 : ∀ y ∈ univ, 0 ≤ (if agree A x y then μ y else 0) := fun y _ => by
    split_ifs
    · exact hμ0 y
    · exact le_refl 0
  have h := single_le_sum (f := fun y => if agree A x y then μ y else 0) h0 (mem_univ x)
  have hx : agree A x x := fun i _ => rfl
  rwa [ite_eq_left hx] at h

lemma cmass_nonneg (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (A : Finset U) (x : U → ZMod p) :
    0 ≤ cmass μ A x := by
  unfold cmass
  exact sum_nonneg fun y _ => by split_ifs; exact hμ0 y; exact le_refl 0

/-- The inner sums: `∑_{x ~ x'} μ(x)/m(x) = 1` when `m(x') ≠ 0`. -/
lemma sum_class_div (μ : (U → ZMod p) → ℝ) (A : Finset U) (x' : U → ZMod p)
    (hm : cmass μ A x' ≠ 0) :
    ∑ x, (if agree A x' x then μ x / cmass μ A x else 0) = 1 := by
  have h : ∀ x, (if agree A x' x then μ x / cmass μ A x else 0) =
      (if agree A x' x then μ x else 0) / cmass μ A x' := by
    intro x
    by_cases hx : agree A x' x
    · rw [ite_eq_left hx, ite_eq_left hx, cmass_congr μ A hx]
    · rw [ite_eq_right hx, ite_eq_right hx, zero_div]
  rw [sum_congr rfl fun x _ => h x, ← sum_div]
  exact div_self hm

/-- The law of total expectation: `E_μ[Π_A G] = E_μ[G]`. -/
lemma sum_mu_class (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (A : Finset U)
    (G : (U → ZMod p) → ℝ) :
    ∑ x, μ x * ((∑ x', if agree A x x' then μ x' * G x' else 0) / cmass μ A x) =
      ∑ x, μ x * G x := by
  have h1 : ∀ x, μ x * ((∑ x', if agree A x x' then μ x' * G x' else 0) / cmass μ A x) =
      ∑ x', if agree A x' x then μ x' * G x' * (μ x / cmass μ A x) else 0 := by
    intro x
    rw [sum_div, mul_sum]
    refine sum_congr rfl fun x' _ => ?_
    by_cases h : agree A x x'
    · rw [ite_eq_left h, ite_eq_left (agree_comm.mp h)]; ring
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (agree_comm.mpr h'))]; simp
  rw [sum_congr rfl fun x _ => h1 x, sum_comm]
  refine sum_congr rfl fun x' _ => ?_
  have h2 : ∑ x, (if agree A x' x then μ x' * G x' * (μ x / cmass μ A x) else 0) =
      μ x' * G x' * ∑ x, (if agree A x' x then μ x / cmass μ A x else 0) := by
    rw [mul_sum]; refine sum_congr rfl fun x _ => ?_; split_ifs <;> ring
  rw [h2]
  by_cases hm : cmass μ A x' = 0
  · have : μ x' = 0 := le_antisymm (hm ▸ mu_le_cmass μ hμ0 A x') (hμ0 x')
    rw [this]; ring
  · rw [sum_class_div μ A x' hm, mul_one]

/-- Jensen on one class: `|Π_A F|² ≤ Π_A |F|²`. -/
lemma norm_condE_sq_le (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (A : Finset U)
    (F : (U → ZMod p) → ℂ) (x : U → ZMod p) :
    ‖condE μ A F x‖ ^ 2 ≤
      (∑ x', if agree A x x' then μ x' * ‖F x'‖ ^ 2 else 0) / cmass μ A x := by
  by_cases hm : cmass μ A x = 0
  · unfold condE; rw [hm]; simp
  · have hm0 : 0 < cmass μ A x := lt_of_le_of_ne (cmass_nonneg μ hμ0 A x) (Ne.symm hm)
    have hS : ‖∑ x', if agree A x x' then (μ x' : ℂ) * F x' else 0‖ ≤
        ∑ x', if agree A x x' then μ x' * ‖F x'‖ else 0 := by
      refine (norm_sum_le _ _).trans (sum_le_sum fun x' _ => ?_)
      split_ifs
      · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hμ0 x')]
      · simp
    have hCS : (∑ x', if agree A x x' then μ x' * ‖F x'‖ else 0) ^ 2 ≤
        cmass μ A x * ∑ x', if agree A x x' then μ x' * ‖F x'‖ ^ 2 else 0 := by
      unfold cmass
      apply sum_sq_le_sum_mul_sum_of_sq_le_mul
      · intro x' _; split_ifs; exact hμ0 x'; exact le_refl 0
      · intro x' _; split_ifs; exact mul_nonneg (hμ0 x') (sq_nonneg _); exact le_refl 0
      · intro x' _; split_ifs <;> nlinarith
    have hS2 : ‖∑ x', if agree A x x' then (μ x' : ℂ) * F x' else 0‖ ^ 2 ≤
        cmass μ A x * ∑ x', if agree A x x' then μ x' * ‖F x'‖ ^ 2 else 0 :=
      (pow_le_pow_left₀ (norm_nonneg _) hS 2).trans hCS
    unfold condE
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hm0.le, div_pow,
      div_le_div_iff₀ (by positivity) hm0]
    nlinarith

/-- **Conditional expectations contract**: `‖Π_A F‖_μ ≤ ‖F‖_μ`. -/
theorem condE_contract (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (A : Finset U)
    (F : (U → ZMod p) → ℂ) :
    ∑ x, μ x * ‖condE μ A F x‖ ^ 2 ≤ ∑ x, μ x * ‖F x‖ ^ 2 := by
  calc ∑ x, μ x * ‖condE μ A F x‖ ^ 2
      ≤ ∑ x, μ x * ((∑ x', if agree A x x' then μ x' * ‖F x'‖ ^ 2 else 0) / cmass μ A x) :=
        sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (norm_condE_sq_le μ hμ0 A F x) (hμ0 x)
    _ = ∑ x, μ x * ‖F x‖ ^ 2 := sum_mu_class μ hμ0 A (fun x => ‖F x‖ ^ 2)

/-- **The tower property**: `Π_A Π_B = Π_A` for `A ⊆ B`. -/
theorem condE_tower (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) {A B : Finset U}
    (hAB : A ⊆ B) (F : (U → ZMod p) → ℂ) (x : U → ZMod p) :
    condE μ A (condE μ B F) x = condE μ A F x := by
  unfold condE
  congr 1
  have h1 : ∀ x', (if agree A x x' then (μ x' : ℂ) *
      ((∑ x'', if agree B x' x'' then (μ x'' : ℂ) * F x'' else 0) / (cmass μ B x' : ℂ)) else 0) =
      ∑ x'', if agree B x'' x' then (μ x'' : ℂ) * F x'' *
        (if agree A x x'' then (μ x' : ℂ) / (cmass μ B x' : ℂ) else 0) else 0 := by
    intro x'
    by_cases hx' : agree A x x'
    · rw [ite_eq_left hx', sum_div, mul_sum]
      refine sum_congr rfl fun x'' _ => ?_
      by_cases h2 : agree B x' x''
      · have h3 : agree A x x'' := agree_trans hx' (agree_mono hAB h2)
        rw [ite_eq_left h2, ite_eq_left (agree_comm.mp h2), ite_eq_left h3]
        ring
      · rw [ite_eq_right h2, ite_eq_right (fun h' => h2 (agree_comm.mpr h'))]
        simp
    · rw [ite_eq_right hx']
      symm
      refine sum_eq_zero fun x'' _ => ?_
      by_cases h2 : agree B x'' x'
      · have h3 : ¬ agree A x x'' := fun h' =>
          hx' (agree_trans h' (agree_mono hAB h2))
        rw [ite_eq_left h2, ite_eq_right h3, mul_zero]
      · rw [ite_eq_right h2]
  rw [sum_congr rfl fun x' _ => h1 x', sum_comm]
  refine sum_congr rfl fun x'' _ => ?_
  have h4 : ∑ x', (if agree B x'' x' then (μ x'' : ℂ) * F x'' *
      (if agree A x x'' then (μ x' : ℂ) / (cmass μ B x' : ℂ) else 0) else 0) =
      (if agree A x x'' then (μ x'' : ℂ) * F x'' *
        ((∑ x', if agree B x'' x' then μ x' / cmass μ B x' else 0 : ℝ) : ℂ) else 0) := by
    by_cases h3 : agree A x x''
    · rw [ite_eq_left h3]
      push_cast
      rw [mul_sum]
      refine sum_congr rfl fun x' _ => ?_
      split_ifs <;> simp
    · rw [ite_eq_right h3]
      exact sum_eq_zero fun x' _ => by split_ifs <;> simp
  rw [h4]
  by_cases h3 : agree A x x''
  · rw [ite_eq_left h3, ite_eq_left h3]
    by_cases hm : cmass μ B x'' = 0
    · have : μ x'' = 0 := le_antisymm (hm ▸ mu_le_cmass μ hμ0 B x'') (hμ0 x'')
      rw [this]; simp
    · rw [sum_class_div μ B x'' hm]; simp
  · rw [ite_eq_right h3, ite_eq_right h3]

/-! ## The conditional law of one coordinate -/

/-- The conditional law `ν_j(t | x) = μ(x[j ↦ t]) / μ(x' : x'_{U∖j} = x_{U∖j})`. -/
noncomputable def condLaw (μ : (U → ZMod p) → ℝ) (j : U) (x : U → ZMod p) (t : ZMod p) : ℝ :=
  μ (Function.update x j t) / cmass μ (univ.erase j) x

omit [Fact p.Prime] in
lemma agree_erase_iff (j : U) (x x' : U → ZMod p) :
    agree (univ.erase j) x x' ↔ Function.update x j (x' j) = x' := by
  constructor
  · intro h
    funext i
    by_cases hi : i = j
    · subst hi; rw [Function.update_self]
    · rw [Function.update_of_ne hi]; exact (h i (mem_erase.mpr ⟨hi, mem_univ _⟩)).symm
  · intro h i hi
    rw [← h, Function.update_of_ne (ne_of_mem_erase hi)]

lemma sum_agree_erase {M : Type*} [AddCommMonoid M] (j : U) (x : U → ZMod p)
    (f : (U → ZMod p) → M) :
    ∑ x', (if agree (univ.erase j) x x' then f x' else 0) = ∑ t, f (Function.update x j t) := by
  rw [← sum_filter]
  have himg : univ.filter (fun x' => agree (univ.erase j) x x') =
      univ.image (fun t => Function.update x j t) := by
    ext x'
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro h; exact ⟨x' j, (agree_erase_iff j x x').mp h⟩
    · rintro ⟨t, rfl⟩
      intro i hi
      rw [Function.update_of_ne (ne_of_mem_erase hi)]
  rw [himg, sum_image (fun t _ t' _ h => Function.update_injective x j h)]

lemma cmass_erase (μ : (U → ZMod p) → ℝ) (j : U) (x : U → ZMod p) :
    cmass μ (univ.erase j) x = ∑ t, μ (Function.update x j t) := by
  unfold cmass
  exact sum_agree_erase j x μ

/-- `Π_{U∖j} V_j` is the kernel map of the conditional law of `x_j`. -/
lemma condE_vert (μ : (U → ZMod p) → ℝ) (j : U) (h : ZMod p → ℂ) (x : U → ZMod p) :
    condE μ (univ.erase j) (fun x' => h (x' j)) x = kerMap (condLaw μ j) h x := by
  unfold condE kerMap condLaw
  dsimp only
  rw [sum_agree_erase j x (fun x' => (μ x' : ℂ) * h (x' j)), sum_div]
  refine sum_congr rfl fun t _ => ?_
  rw [Function.update_self]
  push_cast
  ring

lemma condLaw_nonneg (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (j : U) (x : U → ZMod p)
    (t : ZMod p) : 0 ≤ condLaw μ j x t :=
  div_nonneg (hμ0 _) (cmass_nonneg μ hμ0 _ x)

lemma sum_condLaw (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (j : U) (x : U → ZMod p)
    (hx : μ x ≠ 0) : ∑ t, condLaw μ j x t = 1 := by
  have hm : cmass μ (univ.erase j) x ≠ 0 :=
    (lt_of_lt_of_le (lt_of_le_of_ne (hμ0 x) (Ne.symm hx)) (mu_le_cmass μ hμ0 _ x)).ne'
  unfold condLaw
  rw [← sum_div, ← cmass_erase]
  exact div_self hm

omit [Fintype U] in
lemma update_affLab (s c : ZMod p) (x : U → ZMod p) (j : U) (t : ZMod p) :
    Function.update (affLab s c x) j (s * t + c) = affLab s c (Function.update x j t) := by
  funext i
  by_cases hi : i = j
  · subst hi; simp [affLab]
  · simp [affLab, Function.update_of_ne hi]

/-- The conditional law is covariant. -/
lemma condLaw_cov (μ : (U → ZMod p) → ℝ)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (j : U) (s c : ZMod p) (hs : s ≠ 0) (hsq : IsSquare s) (x : U → ZMod p) (t : ZMod p) :
    condLaw μ j (affLab s c x) (s * t + c) = condLaw μ j x t := by
  have hbij : Function.Bijective (fun b : ZMod p => s * b + c) := by
    constructor
    · intro b b' hb
      exact mul_left_cancel₀ hs (by simpa using hb)
    · intro b
      exact ⟨s⁻¹ * (b - c), by field_simp; ring⟩
  have hm : cmass μ (univ.erase j) (affLab s c x) = cmass μ (univ.erase j) x := by
    rw [cmass_erase, cmass_erase,
      ← hbij.sum_comp (fun b => μ (Function.update (affLab s c x) j b))]
    refine sum_congr rfl fun t _ => ?_
    rw [update_affLab, hinv s c _ hs hsq]
  unfold condLaw
  rw [hm, update_affLab, hinv s c _ hs hsq]

lemma condLaw_kerMap_cov (μ : (U → ZMod p) → ℝ)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (j : U) (s c : ZMod p) (hs : s ≠ 0) (hsq : IsSquare s) (h : ZMod p → ℂ)
    (x : U → ZMod p) :
    kerMap (condLaw μ j) (fun a => h (s * a + c)) x =
      kerMap (condLaw μ j) h (affLab s c x) := by
  have hbij : Function.Bijective (fun b : ZMod p => s * b + c) := by
    constructor
    · intro b b' hb
      exact mul_left_cancel₀ hs (by simpa using hb)
    · intro b
      exact ⟨s⁻¹ * (b - c), by field_simp; ring⟩
  unfold kerMap
  rw [← hbij.sum_comp (fun b => (condLaw μ j (affLab s c x) b : ℂ) * h b)]
  refine sum_congr rfl fun a _ => ?_
  rw [condLaw_cov μ hinv j s c hs hsq x a]

/-- **`lem:hidden-feature`, the singleton** (`p ≡ 3 (mod 4)`): for `j ∉ O` with conditional
probabilities `ν_j(t | x) ≤ D/p`, `‖Π_O V_j h‖²_μ ≤ q(D − 1)/(1 − q) ‖h‖²` on `L²_0`, that is
`‖Π_O V_j‖ ≤ r((D − 1)/(1 − q))^{1/2}`. -/
theorem hidden_feature_vert (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (O : Finset U) (j : U) (hj : j ∉ O) {D : ℝ}
    (hD : ∀ x t, μ x ≠ 0 → condLaw μ j x t ≤ D / p) (h : ZMod p → ℂ) (hh : meanC h = 0) :
    ∑ x, μ x * ‖condE μ O (fun x' => h (x' j)) x‖ ^ 2 ≤
      (p : ℝ)⁻¹ * (D - 1) / (1 - (p : ℝ)⁻¹) * l2sq h := by
  have hO : O ⊆ univ.erase j := fun i hi => mem_erase.mpr ⟨fun h' => hj (h' ▸ hi), mem_univ _⟩
  have htow : ∀ x, condE μ O (fun x' => h (x' j)) x =
      condE μ O (condE μ (univ.erase j) (fun x' => h (x' j))) x :=
    fun x => (condE_tower μ hμ0 hO _ x).symm
  have hG : condE μ (univ.erase j) (fun x' => h (x' j)) = kerMap (condLaw μ j) h :=
    funext fun x => condE_vert μ j h x
  calc ∑ x, μ x * ‖condE μ O (fun x' => h (x' j)) x‖ ^ 2
      = ∑ x, μ x * ‖condE μ O (kerMap (condLaw μ j) h) x‖ ^ 2 := by
        refine sum_congr rfl fun x _ => ?_
        rw [htow x, hG]
    _ ≤ ∑ x, μ x * ‖kerMap (condLaw μ j) h x‖ ^ 2 := condE_contract μ hμ0 O _
    _ ≤ (p : ℝ)⁻¹ * (D - 1) / (1 - (p : ℝ)⁻¹) * l2sq h :=
        markov_kernel_bound hp2 hp3 (labAction μ hinv) hμ0 hμ1 (condLaw μ j)
          (fun s c hs hsq h' x => condLaw_kerMap_cov μ hinv j s c hs hsq h' x)
          (condLaw_nonneg μ hμ0 j) (fun x hx => sum_condLaw μ hμ0 j x hx)
          (fun x t hx => hD x t hx) h hh

/-! ## The star part -/

/-- `ψ_{S∖j}(z, x) = ∏_{i ∈ S∖j} χ(z − x_i)`. -/
noncomputable def psiRest (S : Finset U) (j : U) (x : U → ZMod p) (z : ZMod p) : ℝ :=
  ∏ i ∈ S.erase j, chiRe (z - x i)

omit [Fintype U] in
lemma abs_chiRe_le (t : ZMod p) : |chiRe t| ≤ 1 := by
  unfold chiRe
  by_cases h0 : t = 0
  · rw [h0, quadraticChar_zero]; simp
  · rcases quadraticChar_dichotomy h0 with h1 | h1 <;> rw [h1] <;> simp

omit [Fintype U] in
lemma abs_psiRest_le (S : Finset U) (j : U) (x : U → ZMod p) (z : ZMod p) :
    |psiRest S j x z| ≤ 1 := by
  unfold psiRest
  rw [abs_prod]
  exact prod_le_one₀ (fun i _ => abs_nonneg _) (fun i _ => abs_chiRe_le _)

omit [Fintype U] in
/-- `ψ_S(z, x[j ↦ t]) = χ(z − t) ψ_{S∖j}(z, x)` for `j ∈ S`. -/
lemma prod_update (S : Finset U) {j : U} (hj : j ∈ S) (x : U → ZMod p) (t z : ZMod p) :
    ∏ i ∈ S, chiRe (z - Function.update x j t i) = chiRe (z - t) * psiRest S j x z := by
  unfold psiRest
  rw [← mul_prod_erase S _ hj, Function.update_self]
  congr 1
  refine prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (ne_of_mem_erase hi)]

/-- `Π_{U∖j} W_S` is the kernel map of `p⁻¹ φ_j ψ_{S∖j}` (`j ∈ S`). -/
lemma condE_star (μ : (U → ZMod p) → ℝ) (S : Finset U) {j : U} (hj : j ∈ S)
    (h : ZMod p → ℂ) (x : U → ZMod p) :
    condE μ (univ.erase j) (kerMap (starKer S) h) x =
      kerMap (pivotKer (condLaw μ j) (psiRest S j)) h x := by
  unfold condE kerMap pivotKer condLaw starKer
  rw [sum_agree_erase j x (fun x' => (μ x' : ℂ) * ∑ a, ((p : ℝ)⁻¹ *
    ∏ i ∈ S, chiRe (a - x' i) : ℝ) * h a), sum_div]
  simp_rw [prod_update S hj x]
  simp only [mul_sum, sum_div]
  rw [sum_comm]
  refine sum_congr rfl fun a _ => ?_
  push_cast
  rw [sum_mul, sum_mul]
  refine sum_congr rfl fun t _ => ?_
  ring

omit [Fintype U] in
lemma psiRest_cov (S : Finset U) (j : U) (s c : ZMod p) (hs : s ≠ 0) (hsq : IsSquare s)
    (x : U → ZMod p) (z : ZMod p) : psiRest S j (affLab s c x) (s * z + c) = psiRest S j x z := by
  unfold psiRest affLab
  refine prod_congr rfl fun i _ => ?_
  rw [show s * z + c - (s * x i + c) = s * (z - x i) by ring, chiRe_mul, chiRe_of_isSquare hs hsq,
    one_mul]

lemma pivotKer_cov (μ : (U → ZMod p) → ℝ)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (S : Finset U) (j : U) (s c : ZMod p) (hs : s ≠ 0) (hsq : IsSquare s) (x : U → ZMod p)
    (z : ZMod p) :
    pivotKer (condLaw μ j) (psiRest S j) (affLab s c x) (s * z + c) =
      pivotKer (condLaw μ j) (psiRest S j) x z := by
  have hbij : Function.Bijective (fun b : ZMod p => s * b + c) := by
    constructor
    · intro b b' hb
      exact mul_left_cancel₀ hs (by simpa using hb)
    · intro b
      exact ⟨s⁻¹ * (b - c), by field_simp; ring⟩
  unfold pivotKer
  rw [psiRest_cov S j s c hs hsq x z]
  congr 2
  rw [← hbij.sum_comp (fun b => condLaw μ j (affLab s c x) b * chiRe (s * z + c - b))]
  refine sum_congr rfl fun t _ => ?_
  rw [condLaw_cov μ hinv j s c hs hsq x t,
    show s * z + c - (s * t + c) = s * (z - t) by ring, chiRe_mul, chiRe_of_isSquare hs hsq,
    one_mul]

lemma pivotKer_kerMap_cov (μ : (U → ZMod p) → ℝ)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (S : Finset U) (j : U) (s c : ZMod p) (hs : s ≠ 0) (hsq : IsSquare s) (h : ZMod p → ℂ)
    (x : U → ZMod p) :
    kerMap (pivotKer (condLaw μ j) (psiRest S j)) (fun a => h (s * a + c)) x =
      kerMap (pivotKer (condLaw μ j) (psiRest S j)) h (affLab s c x) := by
  have hbij : Function.Bijective (fun b : ZMod p => s * b + c) := by
    constructor
    · intro b b' hb
      exact mul_left_cancel₀ hs (by simpa using hb)
    · intro b
      exact ⟨s⁻¹ * (b - c), by field_simp; ring⟩
  unfold kerMap
  rw [← hbij.sum_comp (fun b => (pivotKer (condLaw μ j) (psiRest S j) (affLab s c x) b : ℂ) * h b)]
  refine sum_congr rfl fun a _ => ?_
  rw [pivotKer_cov μ hinv S j s c hs hsq x a]

/-- **`lem:hidden-feature`, the star** (`p ≡ 3 (mod 4)`): for `j ∈ S`, `j ∉ O`, with conditional
probabilities `ν_j(t | x) ≤ D/p`, `‖Π_O W_S h‖²_μ ≤ q · q(D − 1)/(1 − q) ‖h‖²` on `L²_0`, that is
`‖Π_O(W_S/r)‖ ≤ r((D − 1)/(1 − q))^{1/2}`. -/
theorem hidden_feature_star (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (O S : Finset U) (j : U) (hjS : j ∈ S) (hj : j ∉ O) {D : ℝ}
    (hD : ∀ x t, μ x ≠ 0 → condLaw μ j x t ≤ D / p) (h : ZMod p → ℂ) (hh : meanC h = 0) :
    ∑ x, μ x * ‖condE μ O (kerMap (starKer S) h) x‖ ^ 2 ≤
      (p : ℝ)⁻¹ * ((p : ℝ)⁻¹ * (D - 1) / (1 - (p : ℝ)⁻¹)) * l2sq h := by
  have hO : O ⊆ univ.erase j := fun i hi => mem_erase.mpr ⟨fun h' => hj (h' ▸ hi), mem_univ _⟩
  have hG : condE μ (univ.erase j) (kerMap (starKer S) h) =
      kerMap (pivotKer (condLaw μ j) (psiRest S j)) h :=
    funext fun x => condE_star μ S hjS h x
  calc ∑ x, μ x * ‖condE μ O (kerMap (starKer S) h) x‖ ^ 2
      = ∑ x, μ x * ‖condE μ O (kerMap (pivotKer (condLaw μ j) (psiRest S j)) h) x‖ ^ 2 := by
        refine sum_congr rfl fun x _ => ?_
        rw [← condE_tower μ hμ0 hO _ x, hG]
    _ ≤ ∑ x, μ x * ‖kerMap (pivotKer (condLaw μ j) (psiRest S j)) h x‖ ^ 2 :=
        condE_contract μ hμ0 O _
    _ ≤ (p : ℝ)⁻¹ * ((p : ℝ)⁻¹ * (D - 1) / (1 - (p : ℝ)⁻¹)) * l2sq h :=
        pivot_kernel_bound hp2 hp3 (labAction μ hinv) hμ0 hμ1 (condLaw μ j)
          (condLaw_nonneg μ hμ0 j) (fun x hx => sum_condLaw μ hμ0 j x hx) hD (psiRest S j)
          (abs_psiRest_le S j)
          (fun s c hs hsq h' x => pivotKer_kerMap_cov μ hinv S j s c hs hsq h' x) h hh

end Sarkozy.SpectralC
