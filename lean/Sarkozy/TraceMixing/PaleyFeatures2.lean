module

public import Sarkozy.TraceMixing.PaleyFeatures

/-!
# Features (`lem:paley-triple`(e), the identities with `A_3`)

`paper/sections/12_labellings.tex`, `lem:paley-triple`(e), continued, in the notation of
`Sarkozy.TraceMixing.PaleyFeatures` (`q = qF`, `D = fibreSize F`, `B = (q - 1)(q - 2)`). On `H_0`:

* `hfSum_V1_A3`: `V_1^* A_3 = -I/(q(q - 1)) + P/B`;
* `hfSum_V2_A3`: `V_2^* A_3 = -I/(q(q - 1)) - P/B`;
* `hfSum_A1_A3`: `A_1^* A_3 = -I/(q B) + P/(q(q - 1))`;
* `hfSum_A2_A3`: `A_2^* A_3 = I/(q B) + P/(q(q - 1))`

(the paper's formulas at `q = 1/p`). Tools: `hfSum_sum`, `featA3_eq`, `hfSum_x2_x1_any`
(`V_2^* V_1 φ` for `φ ∈ H_0` against any test function), `phi_mul_opE1_phi`,
`phi_mul_opV21_phi`, `sum_w_K`, `sum_swap_mul`.
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

/-- `hfSum` of `∑_s w(s) G_s(x)`. -/
theorem hfSum_sum (w : F → ℝ) (G : F → F → F → F → ℝ) :
    hfSum (fun x a b => ∑ s, w s * G s x a b) = ∑ s, w s * hfSum (G s) := by
  have h := hfSum_lin w G 0
  simp only [sub_zero, zero_mul] at h
  exact h

/-- On `H_0`, `A_3 h = ∑_t (-q⁻¹ h(t)) φ_t(x₁) φ_t(x₂)`, `φ_t = χ(t - ·)`. -/
theorem featA3_eq (h : F → ℝ) (hh : ∑ s, h s = 0) (a b : F) :
    featA3 h a b = ∑ t, -(qF⁻¹ * h t) * ((χ (t - a) : ℝ) * (χ (t - b) : ℝ)) := by
  unfold featA3
  rw [hh, mul_zero, mul_zero, sub_zero]

omit [Field F] [DecidableEq F] in
/-- Exchanging the sums in `∑_t w_t (D ∑_b g(b) K_t(b))`. -/
theorem sum_swap_mul (w g : F → ℝ) (D : ℝ) (K : F → F → ℝ) :
    ∑ t, w t * (D * ∑ b, g b * K t b) = D * ∑ b, g b * ∑ t, w t * K t b := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun b _ => sum_congr rfl fun t _ => by ring

/-- `φ_t(a) (V_0^* V_1 φ_t)(a) = (-(q - 2) - χ(t - a))/B + [t = a] (q - 2)/B`. -/
theorem phi_mul_opE1_phi (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (t a : F) :
    (χ (t - a) : ℝ) * opE1 (fun u => (χ (t - u) : ℝ)) a =
      ((-1) * (qF - 2) + (-1) * (χ (t - a) : ℝ)) / ((qF - 1) * (qF - 2)) +
        (if t = a then (qF - 2) / ((qF - 1) * (qF - 2)) else 0) := by
  have hq0 : qF ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  by_cases hta : t = a
  · subst hta
    simp
    ring
  · have hsq : (χ (t - a) : ℝ) ^ 2 = 1 := by
      have := chi_sq_eq (F := F) (t - a)
      rw [ite_eq_right (sub_ne_zero.mpr hta)] at this
      exact_mod_cast this
    have hqq : qF * qF⁻¹ = 1 := mul_inv_cancel₀ hq0
    unfold opE1
    beta_reduce
    rw [paleyOp_phi hF h3 a t, ite_eq_right hta, add_zero, ite_eq_right (fun h => hta h.symm),
      sub_zero, mul_div_assoc']
    congr 1
    linear_combination (-(qF - 2)) * hsq + (-(χ (t - a) : ℝ)) * hqq

/-- `φ_t(b) (V_2^* V_1 φ_t)(b) = (-(q - 2) + χ(t - b))/B + [t = b] (q - 2)/B`. -/
theorem phi_mul_opV21_phi (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (t b : F) :
    (χ (t - b) : ℝ) * ((-((qF - 2) * (χ (t - b) : ℝ)) +
        qF * paleyOp (fun u => (χ (t - u) : ℝ)) b) / ((qF - 1) * (qF - 2))) =
      ((-1) * (qF - 2) + 1 * (χ (t - b) : ℝ)) / ((qF - 1) * (qF - 2)) +
        (if t = b then (qF - 2) / ((qF - 1) * (qF - 2)) else 0) := by
  have hq0 : qF ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  by_cases htb : t = b
  · subst htb
    simp
    ring
  · have hsq : (χ (t - b) : ℝ) ^ 2 = 1 := by
      have := chi_sq_eq (F := F) (t - b)
      rw [ite_eq_right (sub_ne_zero.mpr htb)] at this
      exact_mod_cast this
    have hqq : qF * qF⁻¹ = 1 := mul_inv_cancel₀ hq0
    rw [paleyOp_phi hF h3 b t, ite_eq_right htb, add_zero, ite_eq_right (fun h => htb h.symm),
      sub_zero, mul_div_assoc']
    congr 1
    linear_combination (-(qF - 2)) * hsq + (χ (t - b) : ℝ) * hqq

/-- `∑_t (-q⁻¹ h(t)) ((σ(q - 2) + τ χ(t - a))/B + [t = a](q - 2)/B)
= -h(a)/(q(q - 1)) - τ (P h)(a)/B` for `h ∈ H_0`. -/
theorem sum_w_K (hF : ringChar F ≠ 2) (h : F → ℝ) (hh : ∑ s, h s = 0) (σ τ : ℝ) (a : F) :
    ∑ t, -(qF⁻¹ * h t) * ((σ * (qF - 2) + τ * (χ (t - a) : ℝ)) / ((qF - 1) * (qF - 2)) +
      (if t = a then (qF - 2) / ((qF - 1) * (qF - 2)) else 0)) =
      -(h a) / (qF * (qF - 1)) - τ * paleyOp h a / ((qF - 1) * (qF - 2)) := by
  have hq3 := three_le_card_of_char_ne_two hF
  have hq0 : qF ≠ 0 := by linarith
  have hq1 : qF - 1 ≠ 0 := by linarith
  have hq2 : qF - 2 ≠ 0 := by linarith
  simp only [mul_add, mul_ite, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq', mem_univ,
    ite_true]
  have e : ∑ t, -(qF⁻¹ * h t) * ((σ * (qF - 2) + τ * (χ (t - a) : ℝ)) / ((qF - 1) * (qF - 2))) =
      -(qF⁻¹ * (σ * (qF - 2)) * ∑ t, h t + qF⁻¹ * τ * ∑ t, (χ (t - a) : ℝ) * h t) /
        ((qF - 1) * (qF - 2)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib,
      Finset.sum_div]
    exact sum_congr rfl fun t _ => by ring
  rw [e, hh]
  unfold paleyOp
  field_simp
  ring

/-- **`V_1^* A_3 = -I/(q(q - 1)) + P/((q - 1)(q - 2))` on `H_0`.** -/
theorem hfSum_V1_A3 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (g h : F → ℝ)
    (hh : ∑ s, h s = 0) :
    hfSum (fun _ a b => g a * featA3 h a b) =
      fibreSize F * ∑ a, g a * (-(h a) / (qF * (qF - 1)) + paleyOp h a / ((qF - 1) * (qF - 2))) := by
  have e : hfSum (fun _ a b => g a * featA3 h a b) =
      hfSum (fun (_ : F) a b =>
        ∑ t, -(qF⁻¹ * h t) * ((g a * (χ (t - a) : ℝ)) * (χ (t - b) : ℝ))) := by
    congr 1
    funext x a b
    rw [featA3_eq h hh, Finset.mul_sum]
    exact sum_congr rfl fun t _ => by ring
  rw [e, hfSum_sum (fun t => -(qF⁻¹ * h t))
    (fun t (_ : F) a b => (g a * (χ (t - a) : ℝ)) * (χ (t - b) : ℝ))]
  have ht (t : F) : hfSum (fun (_ : F) a b => (g a * (χ (t - a) : ℝ)) * (χ (t - b) : ℝ)) =
      fibreSize F * ∑ a, g a * (((-1) * (qF - 2) + (-1) * (χ (t - a) : ℝ)) / ((qF - 1) * (qF - 2)) +
        (if t = a then (qF - 2) / ((qF - 1) * (qF - 2)) else 0)) := by
    rw [hfSum_x1_x2 hF h3 (fun a => g a * (χ (t - a) : ℝ)) (fun b => (χ (t - b) : ℝ))
      (sum_chi_sub hF t)]
    congr 1
    refine sum_congr rfl fun a _ => ?_
    rw [mul_assoc, phi_mul_opE1_phi hF h3 t a]
  simp only [ht]
  rw [sum_swap_mul]
  congr 1
  refine sum_congr rfl fun a _ => ?_
  rw [sum_w_K hF h hh (-1) (-1) a]
  ring

/-- **`V_2^* V_1 φ = (-(q - 2)φ + qPφ)/((q - 1)(q - 2))` for `φ ∈ H_0`**, against any test
function `ψ`. -/
theorem hfSum_x2_x1_any (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (φ ψ : F → ℝ)
    (hφ : ∑ s, φ s = 0) :
    hfSum (fun _ a b => φ a * ψ b) =
      fibreSize F * ∑ b, ψ b * ((-((qF - 2) * φ b) + qF * paleyOp φ b) / ((qF - 1) * (qF - 2))) := by
  have hq0 : qF ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  set m : ℝ := qF⁻¹ * ∑ s, ψ s with hm
  have hψ0 : ∑ s, (ψ s - m) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hm, ← mul_assoc,
      mul_inv_cancel₀ hq0, one_mul, sub_self]
  have h1 := hfSum_x2_x1 hF h3 (fun s => ψ s - m) φ hψ0
  have h2 : hfSum (fun _ a b => φ a * ψ b) =
      hfSum (fun _ a b => φ a * (ψ b - m)) + m * hfSum (fun _ a _ => φ a) := by
    unfold hfSum
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine sum_congr rfl fun s _ => sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    split_ifs <;> ring
  rw [h2, h1, hfSum_x1 hF h3, hφ, mul_zero, mul_zero, add_zero]
  congr 1
  have hK : ∑ b, (-((qF - 2) * φ b) + qF * paleyOp φ b) / ((qF - 1) * (qF - 2)) = 0 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hφ, paleyOp_mean hF φ]
    simp
  have e : ∑ b, (ψ b - m) * ((-((qF - 2) * φ b) + qF * paleyOp φ b) / ((qF - 1) * (qF - 2))) =
      ∑ b, ψ b * ((-((qF - 2) * φ b) + qF * paleyOp φ b) / ((qF - 1) * (qF - 2))) -
        m * ∑ b, (-((qF - 2) * φ b) + qF * paleyOp φ b) / ((qF - 1) * (qF - 2)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact sum_congr rfl fun b _ => by ring
  rw [e, hK, mul_zero, sub_zero]

/-- **`V_2^* A_3 = -I/(q(q - 1)) - P/((q - 1)(q - 2))` on `H_0`.** -/
theorem hfSum_V2_A3 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (g h : F → ℝ)
    (hh : ∑ s, h s = 0) :
    hfSum (fun _ a b => g b * featA3 h a b) =
      fibreSize F * ∑ b, g b * (-(h b) / (qF * (qF - 1)) - paleyOp h b / ((qF - 1) * (qF - 2))) := by
  have e : hfSum (fun _ a b => g b * featA3 h a b) =
      hfSum (fun (_ : F) a b =>
        ∑ t, -(qF⁻¹ * h t) * ((χ (t - a) : ℝ) * (g b * (χ (t - b) : ℝ)))) := by
    congr 1
    funext x a b
    rw [featA3_eq h hh, Finset.mul_sum]
    exact sum_congr rfl fun t _ => by ring
  rw [e, hfSum_sum (fun t => -(qF⁻¹ * h t))
    (fun t (_ : F) a b => (χ (t - a) : ℝ) * (g b * (χ (t - b) : ℝ)))]
  have ht (t : F) : hfSum (fun (_ : F) a b => (χ (t - a) : ℝ) * (g b * (χ (t - b) : ℝ))) =
      fibreSize F * ∑ b, g b * (((-1) * (qF - 2) + 1 * (χ (t - b) : ℝ)) / ((qF - 1) * (qF - 2)) +
        (if t = b then (qF - 2) / ((qF - 1) * (qF - 2)) else 0)) := by
    rw [hfSum_x2_x1_any hF h3 (fun a => (χ (t - a) : ℝ)) (fun b => g b * (χ (t - b) : ℝ))
      (sum_chi_sub hF t)]
    congr 1
    refine sum_congr rfl fun b _ => ?_
    rw [mul_assoc, phi_mul_opV21_phi hF h3 t b]
  simp only [ht]
  rw [sum_swap_mul]
  congr 1
  refine sum_congr rfl fun b _ => ?_
  rw [sum_w_K hF h hh (-1) 1 b]
  ring

/-- **`A_1^* A_3 = -I/(q(q - 1)(q - 2)) + P/(q(q - 1))` on `H_0`** (the paper's
`-qI/((p - 1)(p - 2)) + qP/(p - 1)`). -/
theorem hfSum_A1_A3 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (g h : F → ℝ)
    (hh : ∑ s, h s = 0) :
    hfSum (fun _ a b => paleyOp g b * featA3 h a b) =
      fibreSize F * ∑ s, g s *
        (-(h s) / (qF * ((qF - 1) * (qF - 2))) + paleyOp h s / (qF * (qF - 1))) := by
  have hq3 := three_le_card_of_char_ne_two hF
  have hq0 : qF ≠ 0 := by linarith
  have hq1 : qF - 1 ≠ 0 := by linarith
  have hq2 : qF - 2 ≠ 0 := by linarith
  rw [hfSum_V2_A3 hF h3 (paleyOp g) h hh]
  congr 1
  have hPP := sum_paleyOp_mul hF h3 g h hh
  have hadj := paleyOp_adjoint h3 g h
  have eL : ∑ b, paleyOp g b * (-(h b) / (qF * (qF - 1)) - paleyOp h b / ((qF - 1) * (qF - 2))) =
      -(∑ b, paleyOp g b * h b) / (qF * (qF - 1)) -
        (∑ b, paleyOp g b * paleyOp h b) / ((qF - 1) * (qF - 2)) := by
    rw [← Finset.sum_neg_distrib, Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
    exact sum_congr rfl fun b _ => by ring
  have eR : ∑ s, g s * (-(h s) / (qF * ((qF - 1) * (qF - 2))) + paleyOp h s / (qF * (qF - 1))) =
      -(∑ s, g s * h s) / (qF * ((qF - 1) * (qF - 2))) + (∑ s, g s * paleyOp h s) / (qF * (qF - 1)) := by
    rw [← Finset.sum_neg_distrib, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    exact sum_congr rfl fun s _ => by ring
  rw [eL, eR, hadj, hPP]
  field_simp
  ring

/-- **`A_2^* A_3 = I/(q(q - 1)(q - 2)) + P/(q(q - 1))` on `H_0`** (the paper's
`qI/((p - 1)(p - 2)) + qP/(p - 1)`). -/
theorem hfSum_A2_A3 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (g h : F → ℝ)
    (hh : ∑ s, h s = 0) :
    hfSum (fun _ a b => paleyOp g a * featA3 h a b) =
      fibreSize F * ∑ s, g s *
        (h s / (qF * ((qF - 1) * (qF - 2))) + paleyOp h s / (qF * (qF - 1))) := by
  have hq3 := three_le_card_of_char_ne_two hF
  have hq0 : qF ≠ 0 := by linarith
  have hq1 : qF - 1 ≠ 0 := by linarith
  have hq2 : qF - 2 ≠ 0 := by linarith
  rw [hfSum_V1_A3 hF h3 (paleyOp g) h hh]
  congr 1
  have hPP := sum_paleyOp_mul hF h3 g h hh
  have hadj := paleyOp_adjoint h3 g h
  have eL : ∑ a, paleyOp g a * (-(h a) / (qF * (qF - 1)) + paleyOp h a / ((qF - 1) * (qF - 2))) =
      -(∑ a, paleyOp g a * h a) / (qF * (qF - 1)) +
        (∑ a, paleyOp g a * paleyOp h a) / ((qF - 1) * (qF - 2)) := by
    rw [← Finset.sum_neg_distrib, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    exact sum_congr rfl fun a _ => by ring
  have eR : ∑ s, g s * (h s / (qF * ((qF - 1) * (qF - 2))) + paleyOp h s / (qF * (qF - 1))) =
      (∑ s, g s * h s) / (qF * ((qF - 1) * (qF - 2))) + (∑ s, g s * paleyOp h s) / (qF * (qF - 1)) := by
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    exact sum_congr rfl fun s _ => by ring
  rw [eL, eR, hadj, hPP]
  field_simp
  ring

end Sarkozy.TraceMixing
