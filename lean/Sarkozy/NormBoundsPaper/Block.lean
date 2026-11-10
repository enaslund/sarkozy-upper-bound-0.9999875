module

public import Sarkozy.NormBoundsPaper.Eigen

@[expose] public section

/-!
# The block norms of the constant replacement (`lem:record:accepting-c2`)

`paper/sections/21_middle_records.tex`, `lem:record:accepting-c2`.

On a block of primes `p_i ≡ 3 (4)`, all `≥ b ≥ 7`, the old constant law has the kernel
`K_D(d) = ∏_i k_D(d_i)` and the replacement `K_P(d) = ∏_i k_P(d_i)` relative to the uniform law
(`KD`, `KP`). The symmetric and skew parts of the change are the kernels
`K^s(d) = ½(K_P(d) + K_P(−d)) − K_D(d)` and `K^a(d) = ½(K_P(d) − K_P(−d))` (`Ksym`, `Kskew`; `K_D`
is even). Proved here:

* **`khat_Ksym_le`**: every eigenvalue of `K^s` is at most `γ_b² = r²/(1 − 1/b)²`;
* **`khat_Kskew_le`**: every eigenvalue of `K^a` is at most `γ_b = r/(1 − 1/b)`;
* **`form_Ksym_le`**, **`form_Kskew_le`**: the corresponding bounds of the forms
  `∑_{a,b} K(b − a) f(a) g(b)` against `‖f‖₂ ‖g‖₂` (`conv_form_le`).

These are the paper's "exact-support bounds … without a factor for the number of primes".
-/

namespace Sarkozy.NormBoundsPaper

open Finset Complex Sarkozy.SpectralC
open scoped BigOperators ComplexConjugate

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- The old constant kernel `K_D(d) = ∏_i k_D(d_i)`. -/
noncomputable def KD (d : ∀ i, ZMod (pr i)) : ℝ := ∏ i, kD (pr i) (d i)

/-- The replacement kernel `K_P(d) = ∏_i k_P(d_i)`. -/
noncomputable def KP (d : ∀ i, ZMod (pr i)) : ℝ := ∏ i, kP (pr i) (d i)

/-- The symmetric part of the change, `½(K_P(d) + K_P(−d)) − K_D(d)`. -/
noncomputable def Ksym (d : ∀ i, ZMod (pr i)) : ℝ := (1 / 2) * (KP pr d + KP pr (-d)) - KD pr d

/-- The skew part of the change, `½(K_P(d) − K_P(−d))`. -/
noncomputable def Kskew (d : ∀ i, ZMod (pr i)) : ℝ := (1 / 2) * (KP pr d - KP pr (-d))

variable {pr}

theorem khat_KP (ξ : ∀ i, ZMod (pr i)) : khat (KP pr) ξ = ∏ i, hat1 (kP (pr i)) (ξ i) :=
  khat_prod (fun i => kP (pr i)) ξ

theorem khat_KD (ξ : ∀ i, ZMod (pr i)) : khat (KD pr) ξ = ∏ i, hat1 (kD (pr i)) (ξ i) :=
  khat_prod (fun i => kD (pr i)) ξ

theorem khat_Ksym (ξ : ∀ i, ZMod (pr i)) :
    khat (Ksym pr) ξ = (((khat (KP pr) ξ).re : ℝ) : ℂ) - khat (KD pr) ξ := by
  have h : Ksym pr = fun d => (1 / 2) * (KP pr d + KP pr (-d)) - KD pr d := rfl
  rw [h, khat_sub (fun d => (1 / 2) * (KP pr d + KP pr (-d))),
    khat_smul (1 / 2) (fun d => KP pr d + KP pr (-d)), khat_add, khat_neg, Complex.re_eq_add_conj]
  push_cast
  ring

theorem khat_Kskew (ξ : ∀ i, ZMod (pr i)) :
    khat (Kskew pr) ξ = (((khat (KP pr) ξ).im : ℝ) : ℂ) * I := by
  have h : Kskew pr = fun d => (1 / 2) * (KP pr d - KP pr (-d)) := rfl
  rw [h, khat_smul (1 / 2) (fun d => KP pr d - KP pr (-d)), khat_sub, khat_neg,
    Complex.im_eq_sub_conj]
  push_cast
  field_simp

omit [DecidableEq ι] in
/-- The eigenvalues restricted to the support `T = {i : ξ_i ≠ 0}`. -/
theorem prod_support (hp2 : ∀ i, pr i ≠ 2) (ξ : ∀ i, ZMod (pr i)) :
    (∏ i, hat1 (kP (pr i)) (ξ i) =
        ∏ i ∈ univ.filter (fun i => ξ i ≠ 0), hat1 (kP (pr i)) (ξ i)) ∧
      ∏ i, hat1 (kD (pr i)) (ξ i) =
        ((∏ i ∈ univ.filter (fun i => ξ i ≠ 0), (-(1 / ((pr i : ℝ) - 1))) : ℝ) : ℂ) := by
  rw [prod_filter, prod_filter]
  push_cast
  constructor
  · refine prod_congr rfl fun i _ => ?_
    by_cases h : ξ i = 0
    · rw [h, hatP_zero (hp2 i)]
      simp
    · simp [h]
  · refine prod_congr rfl fun i _ => ?_
    by_cases h : ξ i = 0
    · rw [h, hatD_eq]
      simp
    · simp [h, hatD_ne h]

/-- **The eigenvalue bounds of the constant change** (`lem:record:accepting-c2`): on a block of
primes `≡ 3 (4)`, all at least `b ≥ 7`, every eigenvalue of the symmetric part is at most `γ_b²`
and every eigenvalue of the skew part at most `γ_b` in absolute value. -/
theorem eig_bounds (hmod : ∀ i, pr i % 4 = 3) {b : ℝ} (hb : 7 ≤ b)
    (hbp : ∀ i, b ≤ (pr i : ℝ)) (ξ : ∀ i, ZMod (pr i)) :
    ‖khat (Ksym pr) ξ‖ ≤ gam b ^ 2 ∧ ‖khat (Kskew pr) ξ‖ ≤ gam b := by
  have hp2 : ∀ i, pr i ≠ 2 := fun i h => by have := hmod i; rw [h] at this; norm_num at this
  obtain ⟨hρ0, hη0, hρ1, hη1, hργ, h3⟩ := paper_numbers hb
  set T := univ.filter (fun i => ξ i ≠ 0)
  have hw : ∀ i ∈ T, ξ i ≠ 0 := fun i hi => (mem_filter.mp hi).2
  have hpb : ∀ i, Real.sqrt (pr i) / ((pr i : ℝ) - 1) ≤ gam b ∧
      1 / ((pr i : ℝ) - 1) ≤ eta b ∧ ((pr i : ℝ) + 1) / ((pr i : ℝ) - 1) ^ 2 ≤ rho b ^ 2 :=
    fun i => prime_le_least hb (hbp i)
  have hS := support_bounds T (fun i => hat1 (kP (pr i)) (ξ i)) (fun i => 1 / ((pr i : ℝ) - 1))
    (fun i hi => hatP_re (hp2 i) (hmod i) (hw i hi))
    (fun i _ => by
      have : (1 : ℝ) < pr i := p_gt_one
      exact (one_div_pos.mpr (by linarith)).le)
    (fun i _ => (hpb i).2.1)
    (fun i hi => by
      have h := hatP_norm_sq (hp2 i) (hmod i) (hw i hi)
      have : ‖hat1 (kP (pr i)) (ξ i)‖ ^ 2 ≤ rho b ^ 2 := h ▸ (hpb i).2.2
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) hρ0 (by norm_num)).mp this)
    (fun i hi => by rw [hatP_im (hp2 i) (hmod i) (hw i hi)]; exact (hpb i).1)
    hρ0 hη0 hρ1 hη1 hργ h3
  obtain ⟨hP, hD⟩ := prod_support hp2 ξ
  constructor
  · rw [khat_Ksym, khat_KP, khat_KD, hP, hD, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    exact hS.1
  · rw [khat_Kskew, khat_KP, hP, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
    exact hS.2

/-- **The symmetric form bound of the constant change**: `|∑_{a,b} K^s(b − a) f(a) g(b)| ≤
γ_b² ‖f‖₂ ‖g‖₂`. -/
theorem form_Ksym_le (hmod : ∀ i, pr i % 4 = 3) {b : ℝ} (hb : 7 ≤ b) (hbp : ∀ i, b ≤ (pr i : ℝ))
    (f g : (∀ i, ZMod (pr i)) → ℝ) :
    |∑ a, ∑ c, Ksym pr (c - a) * f a * g c| ≤
      gam b ^ 2 * Real.sqrt (∑ a, f a ^ 2) * Real.sqrt (∑ c, g c ^ 2) :=
  conv_form_le (Ksym pr) f g fun ξ => (eig_bounds hmod hb hbp ξ).1

/-- **The skew form bound of the constant change**: `|∑_{a,b} K^a(b − a) f(a) g(b)| ≤
γ_b ‖f‖₂ ‖g‖₂`. -/
theorem form_Kskew_le (hmod : ∀ i, pr i % 4 = 3) {b : ℝ} (hb : 7 ≤ b) (hbp : ∀ i, b ≤ (pr i : ℝ))
    (f g : (∀ i, ZMod (pr i)) → ℝ) :
    |∑ a, ∑ c, Kskew pr (c - a) * f a * g c| ≤
      gam b * Real.sqrt (∑ a, f a ^ 2) * Real.sqrt (∑ c, g c ^ 2) :=
  conv_form_le (Kskew pr) f g fun ξ => (eig_bounds hmod hb hbp ξ).2

end Sarkozy.NormBoundsPaper
