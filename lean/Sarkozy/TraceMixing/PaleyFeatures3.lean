module

public import Sarkozy.TraceMixing.PaleyFeatures2

/-!
# Features (`lem:paley-triple`(e), `A_3^* A_3`)

`paper/sections/12_labellings.tex`, `lem:paley-triple`(e), in the notation of
`Sarkozy.TraceMixing.PaleyFeatures` (`q = qF`, `D = fibreSize F`).

* `count_pair`: the number of `x₀` with `(x₁, x₂) = (a, b)` is `[a ≠ b](q - 2)/2 - χ(b - a)/2`
  (the paper's `(p - 2 - χ(a - b))/2` for the pair `(x₂, x₁) = (a, b)`).
* `hfSum_psi_psi`: `∑_{H_F} ψ(x₁) ψ(x₂) = (q - 2)/2 ((∑ ψ)² - ∑ ψ²)` for every `ψ`: the
  antisymmetric part of the pair kernel integrates to zero against symmetric functions.
* `hfSum_A3_A3`: **`A_3^* A_3 = (q² - 2q - 1)/(q²(q - 1)) I` on `H_0`**, the paper's
  `(1 - 2q - q²)/(p - 1) I` at `q = 1/p`; it is at most `q⁻¹ I` (`A3_coef_le`), the paper's
  `⪯ qI`.

The proof expands `A_3 g · A_3 h = ∑_{t,t'} q⁻² g(t) h(t') ψ_{tt'}(x₁) ψ_{tt'}(x₂)` with
`ψ_{tt'} = χ(t - ·) χ(t' - ·)`, and uses `∑ ψ_{tt'} = q[t = t'] - 1`, `∑ ψ_{tt'}² = q - 2 + [t = t']`.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.TraceMixing

open Sarkozy.Labellings

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `χ` as an integer. -/
local notation "χ" => quadraticChar F

/-- `q = |F|` as a real number. -/
local notation "qF" => (Fintype.card F : ℝ)

/-- **The pair kernel of `(x₁, x₂)`.** -/
theorem count_pair (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (a b : F) :
    (∑ s, if fibre0 s a b then (1 : ℝ) else 0) =
      (if a = b then 0 else (qF - 2) / 2) - (χ (b - a) : ℝ) / 2 := by
  by_cases hab : a = b
  · rw [hab]
    simp [fibre0]
  have e1 (s : F) : (if fibre0 s a b then (1 : ℝ) else 0) =
      (if χ (b - s) = 1 then 1 else 0) - (if s = a then (if χ (b - a) = 1 then 1 else 0) else 0) := by
    unfold fibre0
    by_cases hs : s = a
    · rw [hs]
      simp
    · simp [hs, hab]
  simp only [e1, Finset.sum_sub_distrib, Finset.sum_ite_eq', mem_univ, ite_true]
  rw [Finset.sum_boole, ite_eq_right hab]
  have hin : (2 : ℝ) * ((univ.filter fun s => χ (b - s) = 1).card : ℝ) = qF - 1 := by
    exact_mod_cast card_in hF h3 b
  have hind := two_mul_indicator_real (F := F) (b - a)
  have hsq : ((χ (b - a) : ℤ) : ℝ) ^ 2 = 1 := by
    have := chi_sq_eq (F := F) (b - a)
    rw [ite_eq_right (sub_ne_zero.mpr (Ne.symm hab))] at this
    exact_mod_cast this
  rw [hsq] at hind
  linarith

/-- `∑_{H_F} f(x₁) g(x₂) = ∑_{a,b} K(a, b) f(a) g(b)` with the pair kernel. -/
theorem hfSum_x1x2_kernel (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (f g : F → ℝ) :
    hfSum (fun _ a b => f a * g b) =
      ∑ a, ∑ b, ((if a = b then 0 else (qF - 2) / 2) - (χ (b - a) : ℝ) / 2) * (f a * g b) := by
  unfold hfSum
  rw [Finset.sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine sum_congr rfl fun b _ => ?_
  rw [← count_pair hF h3 a b, Finset.sum_mul]
  refine sum_congr rfl fun s _ => ?_
  split_ifs <;> ring

/-- **`∑_{H_F} ψ(x₁) ψ(x₂) = (q - 2)/2 ((∑ ψ)² - ∑ ψ²)`.** -/
theorem hfSum_psi_psi (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (ψ : F → ℝ) :
    hfSum (fun _ a b => ψ a * ψ b) = (qF - 2) / 2 * ((∑ a, ψ a) ^ 2 - ∑ a, ψ a ^ 2) := by
  rw [hfSum_x1x2_kernel hF h3 ψ ψ]
  have hanti : ∑ a, ∑ b, (χ (b - a) : ℝ) * (ψ a * ψ b) = 0 := by
    have h1 : ∑ a, ∑ b, (χ (b - a) : ℝ) * (ψ a * ψ b) =
        ∑ a, ∑ b, (χ (a - b) : ℝ) * (ψ b * ψ a) := Finset.sum_comm
    have h2 : ∑ a, ∑ b, (χ (a - b) : ℝ) * (ψ b * ψ a) =
        -∑ a, ∑ b, (χ (b - a) : ℝ) * (ψ a * ψ b) := by
      rw [← Finset.sum_neg_distrib]
      refine sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine sum_congr rfl fun b _ => ?_
      have : (χ (a - b) : ℝ) = -(χ (b - a) : ℝ) := by exact_mod_cast chi_swap h3 a b
      rw [this]
      ring
    linarith
  have hdiag : ∑ a, ∑ b, (if a = b then (0 : ℝ) else (qF - 2) / 2) * (ψ a * ψ b) =
      (qF - 2) / 2 * ((∑ a, ψ a) ^ 2 - ∑ a, ψ a ^ 2) := by
    have e (a : F) : ∑ b, (if a = b then (0 : ℝ) else (qF - 2) / 2) * (ψ a * ψ b) =
        (qF - 2) / 2 * (ψ a * ∑ b, ψ b - ψ a ^ 2) := by
      have e' (b : F) : (if a = b then (0 : ℝ) else (qF - 2) / 2) * (ψ a * ψ b) =
          (qF - 2) / 2 * (ψ a * ψ b) - (if a = b then (qF - 2) / 2 * (ψ a * ψ b) else 0) := by
        split_ifs <;> ring
      simp only [e', Finset.sum_sub_distrib, Finset.sum_ite_eq, mem_univ, ite_true,
        ← Finset.mul_sum]
      ring
    simp only [e]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_mul, sq]
  have e3 : ∑ a, ∑ b, ((if a = b then 0 else (qF - 2) / 2) - (χ (b - a) : ℝ) / 2) * (ψ a * ψ b) =
      ∑ a, ∑ b, (if a = b then (0 : ℝ) else (qF - 2) / 2) * (ψ a * ψ b) -
        1 / 2 * ∑ a, ∑ b, (χ (b - a) : ℝ) * (ψ a * ψ b) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine sum_congr rfl fun b _ => ?_
    ring
  rw [e3, hanti, hdiag]
  ring

/-- `∑_a χ(t - a) χ(t' - a) = q [t = t'] - 1`. -/
theorem sum_phi_mul_phi (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (t t' : F) :
    ∑ a, (χ (t - a) : ℝ) * (χ (t' - a) : ℝ) = (if t = t' then qF else 0) - 1 := by
  have := sum_chi_mul_chi hF t t'
  have e : ∑ a, (χ (t - a) : ℝ) * (χ (t' - a) : ℝ) = ∑ a, (χ (a - t) : ℝ) * (χ (a - t') : ℝ) := by
    refine sum_congr rfl fun a _ => ?_
    have h1 : (χ (t - a) : ℝ) = -(χ (a - t) : ℝ) := by exact_mod_cast chi_swap h3 t a
    have h2 : (χ (t' - a) : ℝ) = -(χ (a - t') : ℝ) := by exact_mod_cast chi_swap h3 t' a
    rw [h1, h2]
    ring
  rw [e]
  have e2 : ∑ a, (χ (a - t) : ℝ) * (χ (a - t') : ℝ) =
      (((if t = t' then (Fintype.card F : ℤ) else 0) - 1 : ℤ) : ℝ) := by
    rw [← this]
    push_cast
    rfl
  rw [e2]
  split_ifs <;> push_cast <;> ring

/-- `∑_a (χ(t - a) χ(t' - a))² = q - 2 + [t = t']`. -/
theorem sum_phi_mul_phi_sq (t t' : F) :
    ∑ a, ((χ (t - a) : ℝ) * (χ (t' - a) : ℝ)) ^ 2 = qF - 2 + (if t = t' then 1 else 0) := by
  have esq (u a : F) : (χ (u - a) : ℝ) ^ 2 = 1 - (if a = u then 1 else 0) := by
    have := chi_sq_eq (F := F) (u - a)
    by_cases hu : a = u
    · subst hu
      simp
    · rw [ite_eq_right (sub_ne_zero.mpr (Ne.symm hu))] at this
      rw [ite_eq_right hu, sub_zero]
      exact_mod_cast this
  have e2 (a : F) : ((χ (t - a) : ℝ) * (χ (t' - a) : ℝ)) ^ 2 =
      1 - (if a = t then 1 else 0) - (if a = t' then 1 else 0) +
        (if a = t then (if t = t' then 1 else 0) else 0) := by
    rw [mul_pow, esq t a, esq t' a]
    by_cases ht : a = t
    · by_cases ht' : a = t'
      · subst ht
        subst ht'
        simp
      · subst ht
        simp [ht']
    · by_cases ht' : a = t'
      · subst ht'
        simp [ht]
      · simp [ht, ht']
  simp only [e2, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, Finset.sum_ite_eq', mem_univ, ite_true]
  ring

/-- **`A_3^* A_3 = (q² - 2q - 1)/(q²(q - 1)) I` on `H_0`.** -/
theorem hfSum_A3_A3 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (g h : F → ℝ)
    (hg : ∑ s, g s = 0) (hh : ∑ s, h s = 0) :
    hfSum (fun _ a b => featA3 g a b * featA3 h a b) =
      fibreSize F * ((qF ^ 2 - 2 * qF - 1) / (qF ^ 2 * (qF - 1)) * ∑ s, g s * h s) := by
  have hq3 := three_le_card_of_char_ne_two hF
  have hq0 : qF ≠ 0 := by linarith
  have hq1 : qF - 1 ≠ 0 := by linarith
  have e : hfSum (fun _ a b => featA3 g a b * featA3 h a b) =
      hfSum (fun (_ : F) a b => ∑ t, -(qF⁻¹ * g t) * ∑ t', -(qF⁻¹ * h t') *
        (((χ (t - a) : ℝ) * (χ (t' - a) : ℝ)) * ((χ (t - b) : ℝ) * (χ (t' - b) : ℝ)))) := by
    congr 1
    funext x a b
    rw [featA3_eq g hg, featA3_eq h hh, Finset.sum_mul]
    refine sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine sum_congr rfl fun t' _ => ?_
    ring
  rw [e, hfSum_sum (fun t => -(qF⁻¹ * g t)) (fun t (_ : F) a b => ∑ t', -(qF⁻¹ * h t') *
    (((χ (t - a) : ℝ) * (χ (t' - a) : ℝ)) * ((χ (t - b) : ℝ) * (χ (t' - b) : ℝ))))]
  have ht (t : F) : hfSum (fun (_ : F) a b => ∑ t', -(qF⁻¹ * h t') *
      (((χ (t - a) : ℝ) * (χ (t' - a) : ℝ)) * ((χ (t - b) : ℝ) * (χ (t' - b) : ℝ)))) =
      ∑ t', -(qF⁻¹ * h t') * ((qF - 2) / 2 *
        (((if t = t' then qF else 0) - 1) ^ 2 - (qF - 2 + (if t = t' then 1 else 0)))) := by
    rw [hfSum_sum (fun t' => -(qF⁻¹ * h t')) (fun t' (_ : F) a b =>
      ((χ (t - a) : ℝ) * (χ (t' - a) : ℝ)) * ((χ (t - b) : ℝ) * (χ (t' - b) : ℝ)))]
    refine sum_congr rfl fun t' _ => ?_
    congr 1
    rw [hfSum_psi_psi hF h3 (fun a => (χ (t - a) : ℝ) * (χ (t' - a) : ℝ)),
      sum_phi_mul_phi hF h3 t t', sum_phi_mul_phi_sq t t']
  simp only [ht]
  have hin (t : F) : ∑ t', -(qF⁻¹ * h t') * ((qF - 2) / 2 *
      (((if t = t' then qF else 0) - 1) ^ 2 - (qF - 2 + (if t = t' then 1 else 0)))) =
      -(qF⁻¹ * h t) * ((qF - 2) / 2 * (qF ^ 2 - 2 * qF - 1)) := by
    have e1 (t' : F) : -(qF⁻¹ * h t') * ((qF - 2) / 2 *
        (((if t = t' then qF else 0) - 1) ^ 2 - (qF - 2 + (if t = t' then 1 else 0)))) =
        -(qF⁻¹ * (qF - 2) / 2 * (3 - qF)) * h t' +
          (if t = t' then -(qF⁻¹ * h t') * ((qF - 2) / 2 * (qF ^ 2 - 2 * qF - 1)) else 0) := by
      split_ifs <;> ring
    simp only [e1, Finset.sum_add_distrib, ← Finset.mul_sum, hh, mul_zero, zero_add,
      Finset.sum_ite_eq, mem_univ, ite_true]
  simp only [hin]
  have e3 : ∑ t, -(qF⁻¹ * g t) * (-(qF⁻¹ * h t) * ((qF - 2) / 2 * (qF ^ 2 - 2 * qF - 1))) =
      qF⁻¹ * qF⁻¹ * ((qF - 2) / 2 * (qF ^ 2 - 2 * qF - 1)) * ∑ t, g t * h t := by
    rw [Finset.mul_sum]
    exact sum_congr rfl fun t _ => by ring
  rw [e3]
  unfold fibreSize
  field_simp

omit [Field F] [DecidableEq F] in
/-- `(q² - 2q - 1)/(q²(q - 1)) ≤ q⁻¹` (the paper's `A_3^* A_3 ⪯ qI`). -/
theorem A3_coef_le (hq : (3 : ℝ) ≤ qF) :
    (qF ^ 2 - 2 * qF - 1) / (qF ^ 2 * (qF - 1)) ≤ qF⁻¹ := by
  have hq0 : 0 < qF := by linarith
  have hd : 0 < qF ^ 2 * (qF - 1) := mul_pos (by positivity) (by linarith)
  rw [div_le_iff₀ hd]
  have : qF⁻¹ * (qF ^ 2 * (qF - 1)) = qF * (qF - 1) := by
    field_simp
  rw [this]
  nlinarith

/-- `2 ∑ u (a h + b P h) ≤ (|a| + |b| r)(∑ u² + ∑ h²)` for `h ∈ H_0`, `r = q^{-1/2} = ‖P‖`. -/
theorem two_sum_mul_lin_le (hF : ringChar F ≠ 2) (u h : F → ℝ) (hh : ∑ s, h s = 0) (a b : ℝ) :
    2 * ∑ s, u s * (a * h s + b * paleyOp h s) ≤
      (|a| + |b| * Real.sqrt qF⁻¹) * (∑ s, u s ^ 2 + ∑ s, h s ^ 2) := by
  have hq0 : (0 : ℝ) < qF := by exact_mod_cast Fintype.card_pos
  have hr : 0 < Real.sqrt qF⁻¹ := Real.sqrt_pos.mpr (inv_pos.mpr hq0)
  have hr2 : Real.sqrt qF⁻¹ ^ 2 = qF⁻¹ := Real.sq_sqrt (inv_nonneg.mpr hq0.le)
  have hP2 := sum_paleyOp_sq hF h hh
  have h1 : |2 * ∑ s, u s * h s| ≤ ∑ s, u s ^ 2 + ∑ s, h s ^ 2 := by
    have p1 := two_sum_mul_le (B := ∑ s, h s ^ 2) u h one_pos (by rw [one_pow, one_mul])
    have p2 := two_sum_mul_le (B := ∑ s, h s ^ 2) u (fun s => -h s) one_pos (by simp)
    have e : ∑ s, u s * -h s = -∑ s, u s * h s := by
      rw [← Finset.sum_neg_distrib]
      exact sum_congr rfl fun s _ => by ring
    rw [e] at p2
    rw [abs_le]
    constructor <;> linarith
  have h2 : |2 * ∑ s, u s * paleyOp h s| ≤ Real.sqrt qF⁻¹ * (∑ s, u s ^ 2 + ∑ s, h s ^ 2) := by
    have p1 := two_sum_mul_le (B := ∑ s, h s ^ 2) u (paleyOp h) hr (by rw [hP2, hr2])
    have p2 := two_sum_mul_le (B := ∑ s, h s ^ 2) u (fun s => -paleyOp h s) hr
      (by simp only [neg_sq]; rw [hP2, hr2])
    have e : ∑ s, u s * -paleyOp h s = -∑ s, u s * paleyOp h s := by
      rw [← Finset.sum_neg_distrib]
      exact sum_congr rfl fun s _ => by ring
    rw [e] at p2
    rw [abs_le]
    constructor <;> linarith
  have e : 2 * ∑ s, u s * (a * h s + b * paleyOp h s) =
      a * (2 * ∑ s, u s * h s) + b * (2 * ∑ s, u s * paleyOp h s) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact sum_congr rfl fun s _ => by ring
  rw [e]
  have ha : a * (2 * ∑ s, u s * h s) ≤ |a| * (∑ s, u s ^ 2 + ∑ s, h s ^ 2) :=
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg a))
  have hb : b * (2 * ∑ s, u s * paleyOp h s) ≤
      |b| * (Real.sqrt qF⁻¹ * (∑ s, u s ^ 2 + ∑ s, h s ^ 2)) :=
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left h2 (abs_nonneg b))
  nlinarith [ha, hb]

variable (F) in
/-- `γ² = 1 + (1 + 2r)/(q - 2)`, `r = q^{-1/2}` (the paper's `1 + q(1 + 2r)/(1 - 2q)` at
`q = 1/p`). -/
noncomputable def featGammaSq : ℝ := 1 + (1 + 2 * Real.sqrt qF⁻¹) / (qF - 2)

/-- **`‖(A_1, A_2, A_3)‖ ≤ r γ` on `H_0³`** (`lem:paley-triple`(e)): for `h₁, h₂, h₃ ∈ H_0`,
`∑_{H_F} (A_1 h₁ + A_2 h₂ + A_3 h₃)² ≤ D q⁻¹ γ² (∑ h₁² + ∑ h₂² + ∑ h₃²)`, that is
`E_{ν_F}(A_1 h₁ + A_2 h₂ + A_3 h₃)² ≤ r² γ² (‖h₁‖² + ‖h₂‖² + ‖h₃‖²)`. The proof is the Schur test
on the matrix of the norms of the blocks `A_i^* A_j`, as in the paper. -/
theorem features_norm_bound (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3)
    (h₁ h₂ h₃ : F → ℝ) (hh₁ : ∑ s, h₁ s = 0) (hh₂ : ∑ s, h₂ s = 0) (hh₃ : ∑ s, h₃ s = 0) :
    hfSum (fun _ a b => (paleyOp h₁ b + paleyOp h₂ a + featA3 h₃ a b) ^ 2) ≤
      fibreSize F * (qF⁻¹ * featGammaSq F) * (∑ s, h₁ s ^ 2 + ∑ s, h₂ s ^ 2 + ∑ s, h₃ s ^ 2) := by
  have hq3 := three_le_card_of_char_ne_two hF
  have hq0 : qF ≠ 0 := by linarith
  have hq1 : qF - 1 ≠ 0 := by linarith
  have hq2 : qF - 2 ≠ 0 := by linarith
  have hD := fibreSize_pos hF
  have hexp : hfSum (fun _ a b => (paleyOp h₁ b + paleyOp h₂ a + featA3 h₃ a b) ^ 2) =
      hfSum (fun _ _ b => paleyOp h₁ b * paleyOp h₁ b) +
        hfSum (fun _ a _ => paleyOp h₂ a * paleyOp h₂ a) +
        hfSum (fun _ a b => featA3 h₃ a b * featA3 h₃ a b) +
        2 * hfSum (fun _ a b => paleyOp h₂ a * paleyOp h₁ b) +
        2 * hfSum (fun _ a b => paleyOp h₁ b * featA3 h₃ a b) +
        2 * hfSum (fun _ a b => paleyOp h₂ a * featA3 h₃ a b) := by
    unfold hfSum
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine sum_congr rfl fun s _ => sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    split_ifs <;> ring
  rw [hexp, hfSum_A1_A1 hF h3 h₁ h₁ hh₁, hfSum_A2_A2 hF h3 h₂ h₂ hh₂,
    hfSum_A3_A3 hF h3 h₃ h₃ hh₃ hh₃, hfSum_A1_A2 hF h3 h₁ h₂ hh₂, hfSum_A1_A3 hF h3 h₁ h₃ hh₃,
    hfSum_A2_A3 hF h3 h₂ h₃ hh₃]
  have hsq (k : F → ℝ) : ∑ s, k s * k s = ∑ s, k s ^ 2 := sum_congr rfl fun s _ => (sq _).symm
  rw [hsq h₁, hsq h₂, hsq h₃]
  have e12 : ∑ s, h₁ s * (-(h₂ s) / (qF * (qF - 1)) + paleyOp h₂ s / ((qF - 1) * (qF - 2))) =
      ∑ s, h₁ s * (-1 / (qF * (qF - 1)) * h₂ s + 1 / ((qF - 1) * (qF - 2)) * paleyOp h₂ s) :=
    sum_congr rfl fun s _ => by ring
  have e13 : ∑ s, h₁ s * (-(h₃ s) / (qF * ((qF - 1) * (qF - 2))) + paleyOp h₃ s / (qF * (qF - 1))) =
      ∑ s, h₁ s * (-1 / (qF * ((qF - 1) * (qF - 2))) * h₃ s + 1 / (qF * (qF - 1)) * paleyOp h₃ s) :=
    sum_congr rfl fun s _ => by ring
  have e23 : ∑ s, h₂ s * (h₃ s / (qF * ((qF - 1) * (qF - 2))) + paleyOp h₃ s / (qF * (qF - 1))) =
      ∑ s, h₂ s * (1 / (qF * ((qF - 1) * (qF - 2))) * h₃ s + 1 / (qF * (qF - 1)) * paleyOp h₃ s) :=
    sum_congr rfl fun s _ => by ring
  rw [e12, e13, e23]
  have c12 := two_sum_mul_lin_le hF h₁ h₂ hh₂ (-1 / (qF * (qF - 1))) (1 / ((qF - 1) * (qF - 2)))
  have c13 := two_sum_mul_lin_le hF h₁ h₃ hh₃ (-1 / (qF * ((qF - 1) * (qF - 2))))
    (1 / (qF * (qF - 1)))
  have c23 := two_sum_mul_lin_le hF h₂ h₃ hh₃ (1 / (qF * ((qF - 1) * (qF - 2))))
    (1 / (qF * (qF - 1)))
  have hB : 0 < (qF - 1) * (qF - 2) := mul_pos (by linarith) (by linarith)
  have hq1' : 0 < qF * (qF - 1) := mul_pos (by linarith) (by linarith)
  have hqB : 0 < qF * ((qF - 1) * (qF - 2)) := mul_pos (by linarith) hB
  have a12 : |(-1 / (qF * (qF - 1)))| = 1 / (qF * (qF - 1)) := by
    rw [abs_div, abs_neg, abs_one, abs_of_pos hq1']
  have b12 : |1 / ((qF - 1) * (qF - 2))| = 1 / ((qF - 1) * (qF - 2)) :=
    abs_of_pos (div_pos one_pos hB)
  have a13 : |(-1 / (qF * ((qF - 1) * (qF - 2))))| = 1 / (qF * ((qF - 1) * (qF - 2))) := by
    rw [abs_div, abs_neg, abs_one, abs_of_pos hqB]
  have b13 : |1 / (qF * (qF - 1))| = 1 / (qF * (qF - 1)) := abs_of_pos (div_pos one_pos hq1')
  have a23 : |1 / (qF * ((qF - 1) * (qF - 2)))| = 1 / (qF * ((qF - 1) * (qF - 2))) :=
    abs_of_pos (div_pos one_pos hqB)
  rw [a12, b12] at c12
  rw [a13, b13] at c13
  rw [a23, b13] at c23
  have hc3 := A3_coef_le (F := F) hq3
  have hr0 : 0 ≤ Real.sqrt qF⁻¹ := Real.sqrt_nonneg _
  have hm : 1 / (qF * ((qF - 1) * (qF - 2))) + 1 / (qF * (qF - 1)) * Real.sqrt qF⁻¹ ≤
      1 / (qF * (qF - 1)) + 1 / ((qF - 1) * (qF - 2)) * Real.sqrt qF⁻¹ := by
    have k1 : 1 / (qF * ((qF - 1) * (qF - 2))) ≤ 1 / (qF * (qF - 1)) := by
      apply one_div_le_one_div_of_le hq1'
      nlinarith
    have k2 : 1 / (qF * (qF - 1)) ≤ 1 / ((qF - 1) * (qF - 2)) := by
      apply one_div_le_one_div_of_le hB
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right k2 hr0]
  have hR : qF⁻¹ * featGammaSq F = qF⁻¹ + (1 / (qF * (qF - 1)) + 1 / ((qF - 1) * (qF - 2)) *
      Real.sqrt qF⁻¹) + (1 / (qF * ((qF - 1) * (qF - 2))) + 1 / (qF * (qF - 1)) * Real.sqrt qF⁻¹) := by
    unfold featGammaSq
    field_simp
    ring
  rw [hR]
  set r := Real.sqrt qF⁻¹
  set m12 := 1 / (qF * (qF - 1)) + 1 / ((qF - 1) * (qF - 2)) * r
  set m13 := 1 / (qF * ((qF - 1) * (qF - 2))) + 1 / (qF * (qF - 1)) * r
  set c3 := (qF ^ 2 - 2 * qF - 1) / (qF ^ 2 * (qF - 1))
  set S1 := ∑ s, h₁ s ^ 2
  set S2 := ∑ s, h₂ s ^ 2
  set S3 := ∑ s, h₃ s ^ 2
  have hS3 : 0 ≤ S3 := Finset.sum_nonneg fun s _ => sq_nonneg _
  have key : qF⁻¹ * S1 + qF⁻¹ * S2 + c3 * S3 +
      2 * ∑ s, h₁ s * (-1 / (qF * (qF - 1)) * h₂ s + 1 / ((qF - 1) * (qF - 2)) * paleyOp h₂ s) +
      2 * ∑ s, h₁ s * (-1 / (qF * ((qF - 1) * (qF - 2))) * h₃ s + 1 / (qF * (qF - 1)) * paleyOp h₃ s) +
      2 * ∑ s, h₂ s * (1 / (qF * ((qF - 1) * (qF - 2))) * h₃ s + 1 / (qF * (qF - 1)) * paleyOp h₃ s) ≤
      (qF⁻¹ + m12 + m13) * (S1 + S2 + S3) := by
    linarith [mul_le_mul_of_nonneg_right hc3 hS3, mul_le_mul_of_nonneg_right hm hS3]
  have := mul_le_mul_of_nonneg_left key hD.le
  linarith

end Sarkozy.TraceMixing
