module

public import Sarkozy.TraceMixing.PaleyGram

/-!
# Features (`lem:paley-triple`(e), first part)

`paper/sections/12_labellings.tex`, `lem:paley-triple`(e), over a finite field `F` with `q`
elements (`qF`), `q ≡ 3 (mod 4)`, in the notation of `Sarkozy.TraceMixing.PaleyGram`
(`hfSum` is the sum over `H_F`, `D = fibreSize F`, weak forms
`∑_{H_F} (A g)(x) (B h)(x) = D ∑_s g(s) (A^* B h)(s)`). The features are `A_1 h = (P h)(x₂)`,
`A_2 h = (P h)(x₁)` and `A_3 h = featA3 h x₁ x₂`,
`(A_3 h)(x) = -E_s[χ(s - x₁) χ(s - x₂) h(s)] - q⁻¹ E h` (the paper's `-q E h` with `q = 1/p`).

* Constants and means: `paleyOp_const` (`A_1 1 = A_2 1 = 0`), `featA3_const` (`A_3 1 = 0` on
  `H_F`), `hfSum_A1`, `hfSum_A2`, `hfSum_featA3` (each `A_j h` has `ν_F`-mean zero).
* On `H_0`: `hfSum_A1_A1`, `hfSum_A2_A2` (`A_1^* A_1 = A_2^* A_2 = q⁻¹ I`, the paper's `qI`),
  `hfSum_A1_A2` (`A_1^* A_2 = -I/(q(q - 1)) + P/((q - 1)(q - 2))`), `hfSum_V0_A1`
  (`V_0^* A_1 = -(I + P)/(q - 1)`), `hfSum_V0_A2` (`V_0^* A_2 = I/((q - 1)(q - 2)) - P/(q - 1)`).
* Tools: `sum_paleyOp_mul` (`⟨P g, P h⟩ = q⁻¹ ⟨g, h⟩` on `H_0`), `hfSum_lin`, `hfSum_phi_phi`
  (`∑_{H_F} φ(x₁) φ(x₂) = -D ∑ φ²/(q - 1)` for `φ ∈ H_0`).

* `V_0^*` of the features: `hfSum_V0_A3` (`V_0^* A_3 = 2I/(q(q - 1)(q - 2))`, via
  `fibreSum_phi_phi`, `E[χ(t - x₁) χ(t - x₂) | x₀ = s] = ([t ≠ s] - (q - 1)/2)/D`) and
  `hfSum_V0_Axi` (`V_0^* A_ξ = a_ξ I + b_ξ P`).

The identities `V_1^* A_3`, `V_2^* A_3`, `A_1^* A_3`, `A_2^* A_3` are in
`Sarkozy.TraceMixing.PaleyFeatures2`; `A_3^* A_3` and the norm bound `‖(A_1, A_2, A_3)‖ ≤ r γ` are
in `Sarkozy.TraceMixing.PaleyFeatures3`.
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

/-- **`⟨P g, P h⟩ = q⁻¹ ⟨g, h⟩` on `H_0`.** -/
theorem sum_paleyOp_mul (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (g h : F → ℝ)
    (hh : ∑ s, h s = 0) :
    ∑ s, paleyOp g s * paleyOp h s = qF⁻¹ * ∑ s, g s * h s := by
  rw [paleyOp_adjoint h3 g (paleyOp h)]
  simp only [paleyOp_sq hF h3 h hh]
  rw [← Finset.sum_neg_distrib, Finset.mul_sum]
  exact sum_congr rfl fun s _ => by ring

/-- **`A_1 h = (P h)(x₂)` has `ν_F`-mean zero.** -/
theorem hfSum_A1 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h : F → ℝ) :
    hfSum (fun _ _ b => paleyOp h b) = 0 := by
  rw [hfSum_x2 hF h3, paleyOp_mean hF h, mul_zero]

/-- **`A_2 h = (P h)(x₁)` has `ν_F`-mean zero.** -/
theorem hfSum_A2 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h : F → ℝ) :
    hfSum (fun _ a _ => paleyOp h a) = 0 := by
  rw [hfSum_x1 hF h3, paleyOp_mean hF h, mul_zero]

/-- **`A_1^* A_1 = q⁻¹ I` on `H_0`.** -/
theorem hfSum_A1_A1 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (g h : F → ℝ)
    (hh : ∑ s, h s = 0) :
    hfSum (fun _ _ b => paleyOp g b * paleyOp h b) = fibreSize F * (qF⁻¹ * ∑ s, g s * h s) := by
  rw [hfSum_x2 hF h3, sum_paleyOp_mul hF h3 g h hh]

/-- **`A_2^* A_2 = q⁻¹ I` on `H_0`.** -/
theorem hfSum_A2_A2 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (g h : F → ℝ)
    (hh : ∑ s, h s = 0) :
    hfSum (fun _ a _ => paleyOp g a * paleyOp h a) = fibreSize F * (qF⁻¹ * ∑ s, g s * h s) := by
  rw [hfSum_x1 hF h3, sum_paleyOp_mul hF h3 g h hh]

/-- **`A_1^* A_2 = -I/(q(q - 1)) + P/((q - 1)(q - 2))` on `H_0`** (the paper's
`-qI/(p - 1) + P/((p - 1)(p - 2))` with `q = 1/p`). -/
theorem hfSum_A1_A2 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (g h : F → ℝ)
    (hh : ∑ s, h s = 0) :
    hfSum (fun _ a b => paleyOp h a * paleyOp g b) =
      fibreSize F * ∑ s, g s * (-(h s) / (qF * (qF - 1)) + paleyOp h s / ((qF - 1) * (qF - 2))) := by
  have hq3 := three_le_card_of_char_ne_two hF
  have hq0 : qF ≠ 0 := by linarith
  have hq1 : qF - 1 ≠ 0 := by linarith
  have hq2 : qF - 2 ≠ 0 := by linarith
  rw [hfSum_x2_x1 hF h3 (paleyOp g) (paleyOp h) (paleyOp_mean hF g)]
  congr 1
  have hPP := sum_paleyOp_mul hF h3 g h hh
  have hadj := paleyOp_adjoint h3 g h
  have hPPh : ∑ a, paleyOp g a * paleyOp (paleyOp h) a = -qF⁻¹ * ∑ a, paleyOp g a * h a := by
    rw [Finset.mul_sum]
    exact sum_congr rfl fun a _ => by rw [paleyOp_sq hF h3 h hh a]; ring
  have eL : ∑ a, paleyOp g a * ((-((qF - 2) * paleyOp h a) + qF * paleyOp (paleyOp h) a) /
      ((qF - 1) * (qF - 2))) =
      (-((qF - 2) * ∑ a, paleyOp g a * paleyOp h a) + qF * ∑ a, paleyOp g a * paleyOp (paleyOp h) a) /
        ((qF - 1) * (qF - 2)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
      Finset.sum_div]
    exact sum_congr rfl fun s _ => by ring
  have eR : ∑ s, g s * (-(h s) / (qF * (qF - 1)) + paleyOp h s / ((qF - 1) * (qF - 2))) =
      -(∑ s, g s * h s) / (qF * (qF - 1)) + (∑ s, g s * paleyOp h s) / ((qF - 1) * (qF - 2)) := by
    rw [← Finset.sum_neg_distrib, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    exact sum_congr rfl fun s _ => by ring
  rw [eL, eR, hPPh, hPP, hadj]
  field_simp

/-- **`V_0^* A_1 = -(I + P)/(q - 1)` on `H_0`.** -/
theorem hfSum_V0_A1 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (g h : F → ℝ)
    (hh : ∑ s, h s = 0) :
    hfSum (fun s _ b => g s * paleyOp h b) = fibreSize F * ∑ s, g s * (-(h s + paleyOp h s) / (qF - 1)) := by
  have hq3 := three_le_card_of_char_ne_two hF
  have hq0 : qF ≠ 0 := by linarith
  have hq1 : qF - 1 ≠ 0 := by linarith
  rw [hfSum_x0_x2 hF g (paleyOp h) (paleyOp_mean hF h)]
  congr 1
  refine sum_congr rfl fun s _ => ?_
  rw [opE2, paleyOp_sq hF h3 h hh s]
  field_simp
  ring

/-- **`V_0^* A_2 = I/((q - 1)(q - 2)) - P/(q - 1)` on `H_0`.** -/
theorem hfSum_V0_A2 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (g h : F → ℝ)
    (hh : ∑ s, h s = 0) :
    hfSum (fun s a _ => g s * paleyOp h a) =
      fibreSize F * ∑ s, g s * (h s / ((qF - 1) * (qF - 2)) - paleyOp h s / (qF - 1)) := by
  have hq3 := three_le_card_of_char_ne_two hF
  have hq0 : qF ≠ 0 := by linarith
  have hq1 : qF - 1 ≠ 0 := by linarith
  have hq2 : qF - 2 ≠ 0 := by linarith
  rw [hfSum_x0_x1 hF g (paleyOp h) (paleyOp_mean hF h)]
  congr 1
  refine sum_congr rfl fun s _ => ?_
  rw [opE1, paleyOp_sq hF h3 h hh s]
  field_simp
  ring

/-- `(A_3 h)(x)` at `(x₁, x₂) = (a, b)`: `-E_s[χ(s - a) χ(s - b) h(s)] - q⁻¹ E h`, written as
`∑_s (-q⁻¹ h(s)) χ(s - a) χ(s - b) - q⁻¹ (q⁻¹ ∑ h)`. -/
noncomputable def featA3 (h : F → ℝ) (a b : F) : ℝ :=
  ∑ s, -(qF⁻¹ * h s) * ((χ (s - a) : ℝ) * (χ (s - b) : ℝ)) - qF⁻¹ * (qF⁻¹ * ∑ s, h s)

/-- **`A_3 1 = 0` on `H_F`** (where `x₁ ≠ x₂`). -/
theorem featA3_const (hF : ringChar F ≠ 2) {a b : F} (hab : a ≠ b) :
    featA3 (fun _ => (1 : ℝ)) a b = 0 := by
  have hq0 : qF ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h1 : ∑ s, (χ (s - a) : ℝ) * (χ (s - b) : ℝ) = -1 := by
    have := sum_chi_mul_chi hF a b
    rw [ite_eq_right hab, zero_sub] at this
    exact_mod_cast this
  unfold featA3
  have e : ∑ s, -(qF⁻¹ * (fun _ => (1 : ℝ)) s) * ((χ (s - a) : ℝ) * (χ (s - b) : ℝ)) =
      -qF⁻¹ * ∑ s, (χ (s - a) : ℝ) * (χ (s - b) : ℝ) := by
    rw [Finset.mul_sum]
    exact sum_congr rfl fun s _ => by ring
  rw [e, h1]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [inv_mul_cancel₀ hq0]
  ring

/-- `∑_u χ(s - u) = 0`. -/
theorem sum_chi_sub (hF : ringChar F ≠ 2) (s : F) : ∑ u, (χ (s - u) : ℝ) = 0 := by
  have : ∑ u, χ (s - u) = 0 := by
    rw [← quadraticChar_sum_zero hF]
    exact Equiv.sum_comp (Equiv.subLeft s) (fun x => χ x)
  exact_mod_cast this

/-- `∑_u χ(s - u)² = q - 1`. -/
theorem sum_chi_sub_sq (s : F) : ∑ u, (χ (s - u) : ℝ) ^ 2 = qF - 1 := by
  have h1 (u : F) : (χ (s - u) : ℝ) ^ 2 = 1 - (if u = s then 1 else 0) := by
    have := chi_sq_eq (F := F) (s - u)
    by_cases hu : u = s
    · subst hu
      simp
    · rw [ite_eq_right (sub_ne_zero.mpr (Ne.symm hu))] at this
      rw [ite_eq_right hu, sub_zero]
      exact_mod_cast this
  simp only [h1, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, Finset.sum_ite_eq', mem_univ, ite_true]

/-- `hfSum` of `∑_s w(s) G_s(x) - c`. -/
theorem hfSum_lin (w : F → ℝ) (G : F → F → F → F → ℝ) (c : ℝ) :
    hfSum (fun x a b => ∑ s, w s * G s x a b - c) =
      ∑ s, w s * hfSum (G s) - c * hfSum (F := F) (fun _ _ _ => 1) := by
  unfold hfSum
  have e (x a b : F) : (if fibre0 x a b then ∑ s, w s * G s x a b - c else 0) =
      ∑ s, w s * (if fibre0 x a b then G s x a b else 0) - c * (if fibre0 x a b then 1 else 0) := by
    split_ifs
    · ring
    · simp
  simp only [e, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  symm
  rw [Finset.sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

/-- **`∑_{H_F} φ(x₁) φ(x₂) = -D ∑ φ²/(q - 1)` for `φ ∈ H_0`.** -/
theorem hfSum_phi_phi (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (φ : F → ℝ)
    (hφ : ∑ u, φ u = 0) :
    hfSum (fun _ a b => φ a * φ b) = -(fibreSize F * ∑ u, φ u ^ 2) / (qF - 1) := by
  have hq3 := three_le_card_of_char_ne_two hF
  have hq1 : qF - 1 ≠ 0 := by linarith
  have hq2 : qF - 2 ≠ 0 := by linarith
  have hPh := sum_paleyOp_mul_self h3 φ
  rw [hfSum_x1_x2 hF h3 φ φ hφ]
  unfold opE1
  have e : ∑ u, φ u * (-((qF - 2) * φ u + qF * paleyOp φ u) / ((qF - 1) * (qF - 2))) =
      -((qF - 2) * ∑ u, φ u ^ 2 + qF * ∑ u, paleyOp φ u * φ u) / ((qF - 1) * (qF - 2)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib,
      Finset.sum_div]
    exact sum_congr rfl fun u _ => by ring
  rw [e, hPh]
  field_simp
  ring

/-- **`A_3 h` has `ν_F`-mean zero.** -/
theorem hfSum_featA3 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h : F → ℝ) :
    hfSum (fun _ a b => featA3 h a b) = 0 := by
  have hq3 := three_le_card_of_char_ne_two hF
  have hq0 : qF ≠ 0 := by linarith
  have hq1 : qF - 1 ≠ 0 := by linarith
  have hG (s : F) : hfSum (fun _ a b => (χ (s - a) : ℝ) * (χ (s - b) : ℝ)) = -fibreSize F := by
    rw [hfSum_phi_phi hF h3 (fun u => (χ (s - u) : ℝ)) (sum_chi_sub hF s), sum_chi_sub_sq s]
    field_simp
  unfold featA3
  rw [hfSum_lin (fun s => -(qF⁻¹ * h s)) (fun s _ a b => (χ (s - a) : ℝ) * (χ (s - b) : ℝ))
    (qF⁻¹ * (qF⁻¹ * ∑ s, h s))]
  simp only [hG, hfSum_one hF]
  have e : ∑ s, -(qF⁻¹ * h s) * -fibreSize F = qF⁻¹ * fibreSize F * ∑ s, h s := by
    rw [Finset.mul_sum]
    exact sum_congr rfl fun s _ => by ring
  rw [e]
  have hqq : qF⁻¹ * qF = 1 := inv_mul_cancel₀ hq0
  linear_combination (-(qF⁻¹ * fibreSize F * ∑ s, h s)) * hqq

/-- `(P φ_t)(s) = q⁻¹ - [s = t]` for `φ_t = χ(t - ·)` (`q ≡ 3 (mod 4)`). -/
theorem paleyOp_phi (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (s t : F) :
    paleyOp (fun u => (χ (t - u) : ℝ)) s = qF⁻¹ - (if s = t then 1 else 0) := by
  have hq0 : qF ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have e1 : ∑ u, (χ (u - s) : ℝ) * (χ (t - u) : ℝ) = -∑ u, (χ (u - s) : ℝ) * (χ (u - t) : ℝ) := by
    rw [← Finset.sum_neg_distrib]
    refine sum_congr rfl fun u _ => ?_
    have : (χ (t - u) : ℝ) = -(χ (u - t) : ℝ) := by exact_mod_cast chi_swap h3 t u
    rw [this]
    ring
  have e2 : ∑ u, (χ (u - s) : ℝ) * (χ (u - t) : ℝ) = (if s = t then qF else 0) - 1 := by
    have := sum_chi_mul_chi hF s t
    have e : ∑ u, (χ (u - s) : ℝ) * (χ (u - t) : ℝ) =
        (((if s = t then (Fintype.card F : ℤ) else 0) - 1 : ℤ) : ℝ) := by
      rw [← this]
      push_cast
      rfl
    rw [e]
    split_ifs <;> push_cast <;> ring
  unfold paleyOp
  rw [e1, e2]
  have hqq : qF⁻¹ * qF = 1 := inv_mul_cancel₀ hq0
  split_ifs
  · linear_combination (-1 : ℝ) * hqq
  · ring

/-- `∑_{b : s → b} χ(t - b)² = (q - 1)/2 - [s → t]`. -/
theorem sum_out_chi_sq (hF : ringChar F ≠ 2) (s t : F) :
    ∑ b, (if χ (b - s) = 1 then (χ (t - b) : ℝ) ^ 2 else 0) =
      (qF - 1) / 2 - (if χ (t - s) = 1 then 1 else 0) := by
  have e (b : F) : (if χ (b - s) = 1 then (χ (t - b) : ℝ) ^ 2 else 0) =
      (if χ (b - s) = 1 then (1 : ℝ) else 0) -
        (if b = t then (if χ (t - s) = 1 then 1 else 0) else 0) := by
    by_cases hbt : b = t
    · rw [hbt]
      simp
    · have h1 : (χ (t - b) : ℝ) ^ 2 = 1 := by
        have := chi_sq_eq (F := F) (t - b)
        rw [ite_eq_right (sub_ne_zero.mpr (Ne.symm hbt))] at this
        exact_mod_cast this
      rw [h1, ite_eq_right hbt, sub_zero]
  simp only [e, Finset.sum_sub_distrib, Finset.sum_ite_eq', mem_univ, ite_true]
  rw [Finset.sum_boole]
  have hout : (2 : ℝ) * ((univ.filter fun b => χ (b - s) = 1).card : ℝ) = qF - 1 := by
    exact_mod_cast card_out hF s
  linarith

/-- **`E[χ(t - x₁) χ(t - x₂) | x₀ = s]`**, as a fibre sum: `[t ≠ s] - (q - 1)/2`. -/
theorem fibreSum_phi_phi (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (s t : F) :
    ∑ a, ∑ b, (if fibre0 s a b then (χ (t - a) : ℝ) * (χ (t - b) : ℝ) else 0) =
      (if t = s then 0 else 1) - (qF - 1) / 2 := by
  have hq0 : qF ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [fibre_sum_comm (fun _ a b => (χ (t - a) : ℝ) * (χ (t - b) : ℝ)) s]
  have h1 (b : F) : (if χ (b - s) = 1 then
      ∑ a, (if fibre0 s a b then (χ (t - a) : ℝ) * (χ (t - b) : ℝ) else 0) else 0) =
      -((χ (t - s) : ℝ) * (if χ (b - s) = 1 then (χ (t - b) : ℝ) else 0)) -
        (if χ (b - s) = 1 then (χ (t - b) : ℝ) ^ 2 else 0) := by
    split_ifs with hb
    · rw [inner_sum_fibre hb (fun a => (χ (t - a) : ℝ) * (χ (t - b) : ℝ))]
      simp only [← Finset.sum_mul, sum_chi_sub hF t]
      ring
    · ring
  simp only [h1, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
  have hS1 := sum_out_eq (fun u => (χ (t - u) : ℝ)) (sum_chi_sub hF t) s
  beta_reduce at hS1
  rw [paleyOp_phi hF h3 s t] at hS1
  rw [sum_out_chi_sq hF s t]
  by_cases hts : t = s
  · subst hts
    simp
  · have hst : ¬s = t := fun h => hts h.symm
    rw [ite_eq_right hst, sub_zero, mul_inv_cancel₀ hq0] at hS1
    rw [ite_eq_right hts]
    rcases quadraticChar_dichotomy (sub_ne_zero.mpr hts) with hc | hc
    · rw [hc] at hS1 ⊢
      norm_num at hS1 ⊢
      linarith
    · rw [hc] at hS1 ⊢
      norm_num at hS1 ⊢
      linarith

/-- **`V_0^* A_3 = 2I/(q(q - 1)(q - 2))` on `H_0`** (the paper's `2I/(p(p - 1)(p - 2))`). -/
theorem hfSum_V0_A3 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (g h : F → ℝ)
    (hh : ∑ s, h s = 0) :
    hfSum (fun s a b => g s * featA3 h a b) =
      fibreSize F * ∑ s, g s * (2 * h s / (qF * (qF - 1) * (qF - 2))) := by
  have hq3 := three_le_card_of_char_ne_two hF
  have hq0 : qF ≠ 0 := by linarith
  have hq1 : qF - 1 ≠ 0 := by linarith
  have hq2 : qF - 2 ≠ 0 := by linarith
  rw [hfSum_mul_x0 hF g (fun _ a b => featA3 h a b)]
  congr 1
  refine sum_congr rfl fun s _ => ?_
  congr 1
  have hnum : ∑ a, ∑ b, (if fibre0 s a b then featA3 h a b else 0) = qF⁻¹ * h s := by
    unfold featA3
    simp only [hh, mul_zero, sub_zero]
    have e1 (a b : F) : (if fibre0 s a b then
        ∑ t, -(qF⁻¹ * h t) * ((χ (t - a) : ℝ) * (χ (t - b) : ℝ)) else 0) =
        ∑ t, -(qF⁻¹ * h t) * (if fibre0 s a b then (χ (t - a) : ℝ) * (χ (t - b) : ℝ) else 0) := by
      split_ifs
      · rfl
      · simp
    have e : ∑ a, ∑ b, (if fibre0 s a b then
        ∑ t, -(qF⁻¹ * h t) * ((χ (t - a) : ℝ) * (χ (t - b) : ℝ)) else 0) =
        ∑ t, -(qF⁻¹ * h t) *
          ∑ a, ∑ b, (if fibre0 s a b then (χ (t - a) : ℝ) * (χ (t - b) : ℝ) else 0) := by
      simp only [e1, Finset.mul_sum]
      symm
      rw [Finset.sum_comm]
      refine sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
    rw [e]
    simp only [fibreSum_phi_phi hF h3 s]
    have e2 (t : F) : -(qF⁻¹ * h t) * ((if t = s then 0 else 1) - (qF - 1) / 2) =
        qF⁻¹ * (qF - 1) / 2 * h t - qF⁻¹ * h t + (if t = s then qF⁻¹ * h t else 0) := by
      split_ifs <;> ring
    simp only [e2, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hh,
      Finset.sum_ite_eq', mem_univ, ite_true]
    ring
  unfold condExp0
  rw [hnum, fibre_card hF s]
  unfold fibreSize
  field_simp

/-- **`V_0^* A_ξ = a_ξ I + b_ξ P` on `H_0`**, `A_ξ = ξ₁ A_1 + ξ₂ A_2 + ξ₃ A_3`,
`a_ξ = -ξ₁/(q - 1) + ξ₂/((q - 1)(q - 2)) + 2ξ₃/(q(q - 1)(q - 2))`, `b_ξ = -(ξ₁ + ξ₂)/(q - 1)`
(the paper's formulas at `q = 1/p`). -/
theorem hfSum_V0_Axi (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (ξ₁ ξ₂ ξ₃ : ℝ)
    (g h : F → ℝ) (hh : ∑ s, h s = 0) :
    hfSum (fun s a b => g s * (ξ₁ * paleyOp h b + ξ₂ * paleyOp h a + ξ₃ * featA3 h a b)) =
      fibreSize F * ∑ s, g s *
        ((-ξ₁ / (qF - 1) + ξ₂ / ((qF - 1) * (qF - 2)) + 2 * ξ₃ / (qF * (qF - 1) * (qF - 2))) * h s +
          (-(ξ₁ + ξ₂) / (qF - 1)) * paleyOp h s) := by
  have hq3 := three_le_card_of_char_ne_two hF
  have hq0 : qF ≠ 0 := by linarith
  have hq1 : qF - 1 ≠ 0 := by linarith
  have hq2 : qF - 2 ≠ 0 := by linarith
  have hsplit : hfSum (fun s a b => g s * (ξ₁ * paleyOp h b + ξ₂ * paleyOp h a + ξ₃ * featA3 h a b)) =
      ξ₁ * hfSum (fun s _ b => g s * paleyOp h b) + ξ₂ * hfSum (fun s a _ => g s * paleyOp h a) +
        ξ₃ * hfSum (fun s a b => g s * featA3 h a b) := by
    unfold hfSum
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine sum_congr rfl fun s _ => sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    split_ifs <;> ring
  rw [hsplit, hfSum_V0_A1 hF h3 g h hh, hfSum_V0_A2 hF h3 g h hh, hfSum_V0_A3 hF h3 g h hh]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine sum_congr rfl fun s _ => ?_
  field_simp
  ring

end Sarkozy.TraceMixing
