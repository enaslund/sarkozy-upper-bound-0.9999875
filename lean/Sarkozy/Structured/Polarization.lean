module

public import Sarkozy.RecordExpansion.SubsetExpansion
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Polarization (`lem:tr:polarization`, the displayed inequality and part (d))

`lem:tr:polarization` (`paper/sections/17_completion_repair.tex`, brief F).

* `polarization`: the displayed inequality `eq:polarization`. For kernels `T_F, T_E, T_E'`
  on `L²(ν^b)` with `‖T_F - J‖ ≤ e_F` and `‖T_E - J‖, ‖T_E' - J‖ ≤ e_E`, and real `U, V`
  with means `u, v`,
  `⟨U, T_E U⟩ + ⟨V, T_E' V⟩ - 2⟨U, T_F V⟩ ≥ (u - v)² - (e_F + e_E)(‖U‖² + ‖V‖²)`.
  The setting is any real inner product space with a vector `𝟙`. The projection onto the
  constants is `J f = ⟨𝟙, f⟩ 𝟙` (`constProj`), the mean of `U` is `⟨𝟙, U⟩`, and the
  operator bounds are stated pointwise, `‖(T - J) f‖ ≤ e ‖f‖`. For `L²(ν^b)` and the
  constant function `𝟙`, `‖𝟙‖ = 1` and these are the paper's objects. The inequality does
  not need `‖𝟙‖ = 1`.
* `tensor_two_sign_positive`: part (d). If `κ_j ± ζ_j ⪰_ϑ 0` for both signs at every
  factor, then `⊗_j κ_j ± ⊗_j ζ_j ⪰_ϑ 0` for both signs. The paper's proof is the
  identity `⊗κ - ⊗ζ = 2^{-k} ∑_σ (1 - σ_1⋯σ_k) ⊗(κ + σζ)`. Here the same nonnegative
  expansion is written in the halves `P_j = (κ_j + ζ_j)/2`, `M_j = (κ_j - ζ_j)/2`:
  `⊗κ ∓ ⊗ζ = ∑_f (1 ∓ ∏_j s_j(f)) ⊗_j (f_j ? P_j : M_j)`, with `s_j(f) = ±1`.
* `tensor_sub_eq_sign_sum` and `tensor_sign_positive`: the identity of (d) as the paper
  writes it, and the positivity of each product on its right side, with its coefficient
  `1 - σ_1⋯σ_k ≥ 0`.

Parts (a)–(c), which concern the components of a five-type datum
(`def:five-type-datum`), are not formalized here.
-/

@[expose] public section

open Finset
open scoped BigOperators RealInnerProductSpace

namespace Sarkozy.Structured

/-! ## The displayed inequality -/

section Inner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The projection onto the constants, `J f = ⟨𝟙, f⟩ 𝟙`. -/
noncomputable def constProj (one f : H) : H := ⟪one, f⟫ • one

theorem inner_constProj (one U V : H) : ⟪U, constProj one V⟫ = ⟪one, V⟫ * ⟪one, U⟫ := by
  unfold constProj
  rw [real_inner_smul_right, real_inner_comm one U]

/-- `⟨U, T V⟩ = ⟨𝟙, V⟩⟨𝟙, U⟩ + ⟨U, (T - J) V⟩` and `|⟨U, (T - J)V⟩| ≤ e ‖U‖ ‖V‖`. -/
theorem inner_kernel_bounds (one : H) (T : H →ₗ[ℝ] H) {e : ℝ}
    (hT : ∀ f, ‖T f - constProj one f‖ ≤ e * ‖f‖) (U V : H) :
    |⟪U, T V⟫ - ⟪one, V⟫ * ⟪one, U⟫| ≤ e * (‖U‖ * ‖V‖) := by
  have h1 : ⟪U, T V⟫ - ⟪one, V⟫ * ⟪one, U⟫ = ⟪U, T V - constProj one V⟫ := by
    rw [inner_sub_right, inner_constProj]
  rw [h1]
  calc |⟪U, T V - constProj one V⟫| ≤ ‖U‖ * ‖T V - constProj one V‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ ‖U‖ * (e * ‖V‖) := mul_le_mul_of_nonneg_left (hT V) (norm_nonneg _)
    _ = e * (‖U‖ * ‖V‖) := by ring

/-- **`eq:polarization`** (`lem:tr:polarization`):
`⟨U, T_E U⟩ + ⟨V, T_E' V⟩ - 2⟨U, T_F V⟩ ≥ (u - v)² - (e_F + e_E)(‖U‖² + ‖V‖²)`, with
`u = ⟨𝟙, U⟩`, `v = ⟨𝟙, V⟩` and `‖(T - J) f‖ ≤ e ‖f‖`. -/
theorem polarization (one : H) (TF TE TE' : H →ₗ[ℝ] H) {eF eE : ℝ} (heF : 0 ≤ eF)
    (hF : ∀ f, ‖TF f - constProj one f‖ ≤ eF * ‖f‖)
    (hE : ∀ f, ‖TE f - constProj one f‖ ≤ eE * ‖f‖)
    (hE' : ∀ f, ‖TE' f - constProj one f‖ ≤ eE * ‖f‖) (U V : H) :
    (⟪one, U⟫ - ⟪one, V⟫) ^ 2 - (eF + eE) * (‖U‖ ^ 2 + ‖V‖ ^ 2) ≤
      ⟪U, TE U⟫ + ⟪V, TE' V⟫ - 2 * ⟪U, TF V⟫ := by
  have h1 := abs_le.mp (inner_kernel_bounds one TE hE U U)
  have h2 := abs_le.mp (inner_kernel_bounds one TE' hE' V V)
  have h3 := abs_le.mp (inner_kernel_bounds one TF hF U V)
  have hUV : ‖U‖ * ‖V‖ * 2 ≤ ‖U‖ ^ 2 + ‖V‖ ^ 2 := by
    nlinarith [sq_nonneg (‖U‖ - ‖V‖)]
  have h4 : eF * (‖U‖ * ‖V‖) * 2 ≤ eF * (‖U‖ ^ 2 + ‖V‖ ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hUV heF]
  have hU2 : ‖U‖ * ‖U‖ = ‖U‖ ^ 2 := (sq _).symm
  have hV2 : ‖V‖ * ‖V‖ = ‖V‖ ^ 2 := (sq _).symm
  rw [hU2] at h1
  rw [hV2] at h2
  nlinarith [h1.1, h2.1, h3.2, h4]

end Inner

/-! ## Part (d): both signs for tensor products -/

section Tensor

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]

/-- **`lem:tr:polarization`(d)**: if `κ_j + ζ_j ⪰_ϑ 0` and `κ_j - ζ_j ⪰_ϑ 0` at every
factor, then `⊗κ - ⊗ζ ⪰_ϑ 0` and `⊗κ + ⊗ζ ⪰_ϑ 0`. -/
theorem tensor_two_sign_positive (c : ReflectionCut V) (κ ζ : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (hp : ∀ j, c.Positive (κ j + ζ j)) (hm : ∀ j, c.Positive (κ j - ζ j)) :
    c.Positive (tensorLaw κ - tensorLaw ζ) ∧ c.Positive (tensorLaw κ + tensorLaw ζ) := by
  set P : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ := fun j => (1 / 2 : ℝ) • (κ j + ζ j) with hPdef
  set M : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ := fun j => (1 / 2 : ℝ) • (κ j - ζ j) with hMdef
  have hP : ∀ j, c.Positive (P j) := fun j => (hp j).smul (by norm_num)
  have hM : ∀ j, c.Positive (M j) := fun j => (hm j).smul (by norm_num)
  have hκ : κ = fun j => M j + P j := by
    funext j
    simp only [hPdef, hMdef]
    module
  have hζ : ζ = fun j => ((-1 : ℝ) • M j) + P j := by
    funext j
    simp only [hPdef, hMdef]
    module
  -- the expansions
  set Tf : (J → Bool) → ((V → ∀ j, X j) → ℝ) →ₗ[ℝ] ℝ :=
    fun f => tensorLaw (fun j => if f j then P j else M j) with hTf
  set sgn : (J → Bool) → ℝ := fun f => ∏ j, (if f j then (1 : ℝ) else -1) with hsgn
  have hTpos : ∀ f, c.Positive (Tf f) := by
    intro f
    apply ReflectionCut.Positive.tensor
    intro j
    by_cases hj : f j
    · simp only [hj, ite_true]
      exact hP j
    · simp only [hj, Bool.false_eq_true, ite_false]
      exact hM j
  have hκexp : tensorLaw κ = ∑ f : J → Bool, Tf f := by
    rw [hκ, Sarkozy.RecordExpansion.tensorLaw_add_eq_sum]
  have hζexp : tensorLaw ζ = ∑ f : J → Bool, sgn f • Tf f := by
    rw [hζ, Sarkozy.RecordExpansion.tensorLaw_add_eq_sum]
    apply sum_congr rfl
    intro f _
    have h : (fun j => if f j then P j else (-1 : ℝ) • M j) =
        fun j => (if f j then (1 : ℝ) else -1) • (if f j then P j else M j) := by
      funext j
      by_cases hj : f j
      · simp [hj]
      · simp [hj]
    rw [h, Sarkozy.RecordExpansion.tensorLaw_smul]
  have hsgn1 : ∀ f, |sgn f| ≤ 1 := by
    intro f
    simp only [hsgn]
    rw [Finset.abs_prod]
    apply le_of_eq
    apply prod_eq_one
    intro j _
    by_cases hj : f j
    · simp [hj]
    · simp [hj]
  constructor
  · have hdiff : tensorLaw κ - tensorLaw ζ = ∑ f : J → Bool, (1 - sgn f) • Tf f := by
      rw [hκexp, hζexp, ← sum_sub_distrib]
      apply sum_congr rfl
      intro f _
      module
    rw [hdiff]
    apply ReflectionCut.Positive.sum
    intro f _
    exact (hTpos f).smul (by linarith [(abs_le.mp (hsgn1 f)).2])
  · have hsum : tensorLaw κ + tensorLaw ζ = ∑ f : J → Bool, (1 + sgn f) • Tf f := by
      rw [hκexp, hζexp, ← sum_add_distrib]
      apply sum_congr rfl
      intro f _
      module
    rw [hsum]
    apply ReflectionCut.Positive.sum
    intro f _
    exact (hTpos f).smul (by linarith [(abs_le.mp (hsgn1 f)).1])

/-- **`lem:tr:polarization`(d), the identity**:
`⊗κ_j - ⊗ζ_j = 2^{-k} ∑_{σ ∈ {±1}^k} (1 - σ_1⋯σ_k) ⊗(κ_j + σ_j ζ_j)`, `k = |J|`, with the
signs `σ_j = ±1` indexed by `f : J → Bool`. -/
theorem tensor_sub_eq_sign_sum (κ ζ : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) :
    tensorLaw κ - tensorLaw ζ =
      ((2 : ℝ) ^ Fintype.card J)⁻¹ • ∑ f : J → Bool,
        (1 - ∏ j, (if f j then (1 : ℝ) else -1)) •
          tensorLaw (fun j => κ j + (if f j then (1 : ℝ) else -1) • ζ j) := by
  set P : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ := fun j => (1 / 2 : ℝ) • (κ j + ζ j) with hPdef
  set M : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ := fun j => (1 / 2 : ℝ) • (κ j - ζ j) with hMdef
  set Tf : (J → Bool) → ((V → ∀ j, X j) → ℝ) →ₗ[ℝ] ℝ :=
    fun f => tensorLaw (fun j => if f j then P j else M j) with hTf
  set sgn : (J → Bool) → ℝ := fun f => ∏ j, (if f j then (1 : ℝ) else -1) with hsgn
  have hκ : κ = fun j => M j + P j := by
    funext j
    simp only [hPdef, hMdef]
    module
  have hζ : ζ = fun j => ((-1 : ℝ) • M j) + P j := by
    funext j
    simp only [hPdef, hMdef]
    module
  have hκexp : tensorLaw κ = ∑ f : J → Bool, Tf f := by
    rw [hκ, Sarkozy.RecordExpansion.tensorLaw_add_eq_sum]
  have hζexp : tensorLaw ζ = ∑ f : J → Bool, sgn f • Tf f := by
    rw [hζ, Sarkozy.RecordExpansion.tensorLaw_add_eq_sum]
    apply sum_congr rfl
    intro f _
    have h : (fun j => if f j then P j else (-1 : ℝ) • M j) =
        fun j => (if f j then (1 : ℝ) else -1) • (if f j then P j else M j) := by
      funext j
      by_cases hj : f j
      · simp [hj]
      · simp [hj]
    rw [h, Sarkozy.RecordExpansion.tensorLaw_smul]
  have hterm : ∀ f : J → Bool,
      tensorLaw (fun j => κ j + (if f j then (1 : ℝ) else -1) • ζ j) =
        (2 : ℝ) ^ Fintype.card J • Tf f := by
    intro f
    have h : (fun j => κ j + (if f j then (1 : ℝ) else -1) • ζ j) =
        fun j => (2 : ℝ) • (if f j then P j else M j) := by
      funext j
      by_cases hj : f j
      · simp only [hj, ite_true, one_smul, hPdef]
        module
      · simp only [hj, Bool.false_eq_true, ite_false, hMdef]
        module
    rw [h, Sarkozy.RecordExpansion.tensorLaw_smul, prod_const, card_univ]
  rw [sum_congr rfl (fun f _ => by rw [hterm f]), hκexp, hζexp, ← sum_sub_distrib, smul_sum]
  apply sum_congr rfl
  intro f _
  rw [smul_smul, smul_smul]
  have e : Tf f - sgn f • Tf f = (1 - sgn f) • Tf f := by module
  rw [e]
  congr 1
  simp only [hsgn]
  field_simp

/-- **`lem:tr:polarization`(d)**: every product on the right of `tensor_sub_eq_sign_sum` is
`⪰_ϑ 0`, with a nonnegative coefficient `1 - σ_1⋯σ_k`. -/
theorem tensor_sign_positive (c : ReflectionCut V) (κ ζ : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (hp : ∀ j, c.Positive (κ j + ζ j)) (hm : ∀ j, c.Positive (κ j - ζ j)) (f : J → Bool) :
    c.Positive (tensorLaw (fun j => κ j + (if f j then (1 : ℝ) else -1) • ζ j)) ∧
      0 ≤ 1 - ∏ j, (if f j then (1 : ℝ) else -1) := by
  constructor
  · apply ReflectionCut.Positive.tensor
    intro j
    by_cases hj : f j
    · rw [ite_eq_left hj, one_smul]
      exact hp j
    · rw [ite_eq_right hj]
      have e : κ j + (-1 : ℝ) • ζ j = κ j - ζ j := by module
      rw [e]
      exact hm j
  · have h : |∏ j, (if f j then (1 : ℝ) else -1)| ≤ 1 := by
      rw [Finset.abs_prod]
      apply le_of_eq
      apply prod_eq_one
      intro j _
      by_cases hj : f j
      · simp [hj]
      · simp [hj]
    linarith [(abs_le.mp h).2]

end Tensor

end Sarkozy.Structured
