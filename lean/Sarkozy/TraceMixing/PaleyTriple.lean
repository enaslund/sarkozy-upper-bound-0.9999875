module

public import Sarkozy.TraceMixing.PaleySquare

/-!
# Directed triples (`lem:paley-triple`(d), first formulas)

`paper/sections/12_labellings.tex`, `lem:paley-triple`(d), over any finite field `F` with `q`
elements and odd characteristic. `H_F` is the set of triples `(x₀, x₁, x₂)` with `x₁` distinct
from `x₀, x₂` and `x₀ → x₂` (`χ(x₂ - x₀) = 1`, which forces `x₀ ≠ x₂`); `ν_F` is the uniform
law on `H_F`. Under `ν_F` the conditional expectation given `x₀ = s` is the average over the
fibre `{(x₁, x₂) : (s, x₁, x₂) ∈ H_F}` (`condExp0`).

* `card_fibre0`: the fibre has `(q - 1)(q - 2)/2` elements (so `x₀` is uniform).
* `condExp0_x2`: `V_0^* V_2 = (q P - I)/(q - 1)` on the mean-zero functions, the paper's
  `(P - q I)/(1 - q)` with `q = 1/p`.
* `condExp0_x1`: `V_0^* V_1 = -(I + V_0^* V_2)/(q - 2)` on the mean-zero functions.

The remaining formulas of (d), the norms `ϱ`, `ϱ₁`, `ϱ'` and the Gram bound are in
`Sarkozy.TraceMixing.PaleyGram`; part (e) is in `Sarkozy.TraceMixing.PaleyFeatures`,
`PaleyFeatures2` and `PaleyFeatures3`.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.TraceMixing

open Sarkozy.Labellings

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `χ` as an integer. -/
local notation "χ" => quadraticChar F

/-- The fibre condition of `H_F` over `x₀ = s`. -/
def fibre0 (s a b : F) : Prop := s ≠ a ∧ a ≠ b ∧ χ (b - s) = 1

instance (s a b : F) : Decidable (fibre0 s a b) := by
  unfold fibre0
  infer_instance

/-- `E_{ν_F}[G | x₀ = s]`: the average of `G(s, x₁, x₂)` over the fibre. -/
noncomputable def condExp0 (G : F → F → F → ℝ) (s : F) : ℝ :=
  (∑ a, ∑ b, if fibre0 s a b then G s a b else 0) /
    (∑ a, ∑ b, if fibre0 s a b then (1 : ℝ) else 0)

/-- The indicator of `χ(x) = 1`, as a real number: `2 [χ(x) = 1] = χ(x)² + χ(x)`. -/
theorem two_mul_indicator_real (x : F) :
    2 * (if χ x = 1 then (1 : ℝ) else 0) = ((χ x : ℤ) : ℝ) ^ 2 + ((χ x : ℤ) : ℝ) := by
  have h := two_mul_indicator (F := F) x (Or.inl rfl : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1)
  have h' : ((2 * (if χ x = 1 then (1 : ℤ) else 0) : ℤ) : ℝ) =
      (((χ x) ^ 2 + 1 * χ x : ℤ) : ℝ) := by rw [h]
  push_cast at h'
  rw [one_mul] at h'
  convert h' using 2

/-- For `χ(b - s) = 1`, the inner sum over `x₁`: `∑_a [a ≠ s, a ≠ b] g(a) = ∑ g - g(s) - g(b)`. -/
theorem inner_sum_fibre {s b : F} (hb : χ (b - s) = 1) (g : F → ℝ) :
    ∑ a, (if fibre0 s a b then g a else 0) = ∑ a, g a - g s - g b := by
  have hsb : s ≠ b := by
    intro h
    rw [h, sub_self, quadraticChar_zero] at hb
    exact zero_ne_one hb
  have h1 (a : F) : (if fibre0 s a b then g a else 0) =
      g a - (if a = s then g a else 0) - (if a = b then g a else 0) := by
    unfold fibre0
    by_cases has : a = s
    · subst has
      simp [hsb]
    · by_cases hab : a = b
      · subst hab
        simp [has]
      · simp [has, hab, Ne.symm has, hb]
  simp only [h1, Finset.sum_sub_distrib, Finset.sum_ite_eq', mem_univ, ite_true]

/-- The fibre sum of a function of `x₁` and `x₂`, summed over `x₂` outside. -/
theorem fibre_sum_comm (G : F → F → F → ℝ) (s : F) :
    ∑ a, ∑ b, (if fibre0 s a b then G s a b else 0) =
      ∑ b, if χ (b - s) = 1 then ∑ a, (if fibre0 s a b then G s a b else 0) else 0 := by
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro b _
  split_ifs with hb
  · rfl
  · apply Finset.sum_eq_zero
    intro a _
    unfold fibre0
    rw [ite_eq_right (fun h => hb h.2.2)]

/-- **The fibres have `(q - 1)(q - 2)/2` elements.** -/
theorem card_fibre0 (hF : ringChar F ≠ 2) (s : F) :
    2 * ∑ a, ∑ b, (if fibre0 s a b then (1 : ℝ) else 0) =
      ((Fintype.card F : ℝ) - 1) * ((Fintype.card F : ℝ) - 2) := by
  rw [fibre_sum_comm (fun _ _ _ => (1 : ℝ)) s]
  have h1 (b : F) : (if χ (b - s) = 1 then ∑ a, (if fibre0 s a b then (1 : ℝ) else 0) else 0) =
      (if χ (b - s) = 1 then (1 : ℝ) else 0) * ((Fintype.card F : ℝ) - 2) := by
    split_ifs with hb
    · rw [inner_sum_fibre hb (fun _ => (1 : ℝ))]
      simp only [sum_const, card_univ, nsmul_eq_mul, mul_one, one_mul]
      ring
    · ring
  simp only [h1]
  rw [← Finset.sum_mul, ← mul_assoc, Finset.mul_sum]
  have hout := card_out hF s
  have hcard : ((univ.filter fun b => χ (b - s) = 1).card : ℝ) =
      ∑ b, (if χ (b - s) = 1 then (1 : ℝ) else 0) := by rw [Finset.sum_boole]
  have h2 : 2 * ∑ b, (if χ (b - s) = 1 then (1 : ℝ) else 0) = (Fintype.card F : ℝ) - 1 := by
    rw [← hcard]
    exact_mod_cast hout
  rw [← Finset.mul_sum, h2]

/-- `∑_{b : s → b} g(b) = (q (P g)(s) - g(s))/2` for `∑ g = 0`. -/
theorem sum_out_eq (g : F → ℝ) (hg : ∑ x, g x = 0) (s : F) :
    2 * ∑ b, (if χ (b - s) = 1 then g b else 0) =
      (Fintype.card F : ℝ) * paleyOp g s - g s := by
  have hq0 : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h1 (b : F) : 2 * (if χ (b - s) = 1 then g b else 0) =
      (((χ (b - s) : ℤ) : ℝ) ^ 2 + ((χ (b - s) : ℤ) : ℝ)) * g b := by
    rw [← two_mul_indicator_real]
    split_ifs <;> ring
  have hsq (b : F) : ((χ (b - s) : ℤ) : ℝ) ^ 2 = 1 - (if b = s then 1 else 0) := by
    have := chi_sq_eq (F := F) (b - s)
    by_cases h : b = s
    · subst h
      simp
    · rw [ite_eq_right (sub_ne_zero.mpr h)] at this
      rw [ite_eq_right h, sub_zero]
      exact_mod_cast this
  rw [Finset.mul_sum]
  simp only [h1, hsq, add_mul, Finset.sum_add_distrib, sub_mul, one_mul, ite_mul, zero_mul,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', mem_univ, ite_true, hg]
  unfold paleyOp
  rw [← mul_assoc, mul_inv_cancel₀ hq0, one_mul]
  ring

/-- **`V_0^* V_2 = (q P - I)/(q - 1)` on the mean-zero functions** (the paper's
`(P - qI)/(1 - q)`, `q = 1/p`). -/
theorem condExp0_x2 (hF : ringChar F ≠ 2) (h : F → ℝ) (hh : ∑ x, h x = 0) (s : F) :
    condExp0 (fun _ _ b => h b) s =
      ((Fintype.card F : ℝ) * paleyOp h s - h s) / ((Fintype.card F : ℝ) - 1) := by
  have hq3 : (3 : ℝ) ≤ Fintype.card F := by
    have h2 : 2 < Fintype.card F := by
      have h1 : 2 ≤ Fintype.card F := Fintype.one_lt_card
      have hodd := FiniteField.odd_card_of_char_ne_two hF
      rcases h1.lt_or_eq with h | h
      · exact h
      · rw [← h] at hodd
        exact absurd hodd (by decide)
    exact_mod_cast h2
  have hnum : 2 * ∑ a, ∑ b, (if fibre0 s a b then h b else 0) =
      ((Fintype.card F : ℝ) - 2) * ((Fintype.card F : ℝ) * paleyOp h s - h s) := by
    rw [fibre_sum_comm (fun _ _ b => h b) s]
    have h1 (b : F) : (if χ (b - s) = 1 then ∑ a, (if fibre0 s a b then h b else 0) else 0) =
        ((Fintype.card F : ℝ) - 2) * (if χ (b - s) = 1 then h b else 0) := by
      split_ifs with hb
      · rw [inner_sum_fibre hb (fun _ => h b)]
        simp only [sum_const, card_univ, nsmul_eq_mul]
        ring
      · ring
    simp only [h1]
    rw [← Finset.mul_sum, mul_left_comm, sum_out_eq h hh s]
  have hden := card_fibre0 hF s
  unfold condExp0
  have hd0 : ((Fintype.card F : ℝ) - 1) * ((Fintype.card F : ℝ) - 2) ≠ 0 := by
    apply mul_ne_zero <;> linarith
  have hq1 : (Fintype.card F : ℝ) - 1 ≠ 0 := by linarith
  have hq2 : (Fintype.card F : ℝ) - 2 ≠ 0 := by linarith
  rw [div_eq_div_iff (by intro h0; rw [h0, mul_zero] at hden; exact hd0 hden.symm) hq1]
  have e1 : (∑ a, ∑ b, (if fibre0 s a b then h b else 0)) =
      ((Fintype.card F : ℝ) - 2) * ((Fintype.card F : ℝ) * paleyOp h s - h s) / 2 := by
    rw [← hnum]
    ring
  have e2 : (∑ a, ∑ b, (if fibre0 s a b then (1 : ℝ) else 0)) =
      ((Fintype.card F : ℝ) - 1) * ((Fintype.card F : ℝ) - 2) / 2 := by
    rw [← hden]
    ring
  rw [e1, e2]
  ring

/-- **`V_0^* V_1 = -(I + V_0^* V_2)/(q - 2)` on the mean-zero functions**: given `x₀` and `x₂`,
`x₁` is uniform on the other `q - 2` labels. -/
theorem condExp0_x1 (hF : ringChar F ≠ 2) (h : F → ℝ) (hh : ∑ x, h x = 0) (s : F) :
    condExp0 (fun _ a _ => h a) s =
      -(h s + condExp0 (fun _ _ b => h b) s) / ((Fintype.card F : ℝ) - 2) := by
  have hq3 : (3 : ℝ) ≤ Fintype.card F := by
    have h2 : 2 < Fintype.card F := by
      have h1 : 2 ≤ Fintype.card F := Fintype.one_lt_card
      have hodd := FiniteField.odd_card_of_char_ne_two hF
      rcases h1.lt_or_eq with h | h
      · exact h
      · rw [← h] at hodd
        exact absurd hodd (by decide)
    exact_mod_cast h2
  have hq1 : (Fintype.card F : ℝ) - 1 ≠ 0 := by linarith
  have hq2 : (Fintype.card F : ℝ) - 2 ≠ 0 := by linarith
  set D : ℝ := ∑ a, ∑ b, (if fibre0 s a b then (1 : ℝ) else 0) with hD
  have hden : 2 * D = ((Fintype.card F : ℝ) - 1) * ((Fintype.card F : ℝ) - 2) := card_fibre0 hF s
  have hD0 : D ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hden
    have : ((Fintype.card F : ℝ) - 1) * ((Fintype.card F : ℝ) - 2) ≠ 0 := mul_ne_zero hq1 hq2
    exact this hden.symm
  -- the numerator for `h(x₁)`
  have hnum1 : ∑ a, ∑ b, (if fibre0 s a b then h a else 0) =
      -(((Fintype.card F : ℝ) - 1) / 2 * h s) - ∑ b, (if χ (b - s) = 1 then h b else 0) := by
    rw [fibre_sum_comm (fun _ a _ => h a) s]
    have h1 (b : F) : (if χ (b - s) = 1 then ∑ a, (if fibre0 s a b then h a else 0) else 0) =
        -(h s * (if χ (b - s) = 1 then 1 else 0)) - (if χ (b - s) = 1 then h b else 0) := by
      split_ifs with hb
      · rw [inner_sum_fibre hb h, hh]
        ring
      · ring
    simp only [h1, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
    have hout := card_out hF s
    have hcard : ((univ.filter fun b => χ (b - s) = 1).card : ℝ) =
        ∑ b, (if χ (b - s) = 1 then (1 : ℝ) else 0) := by rw [Finset.sum_boole]
    have h2 : ∑ b, (if χ (b - s) = 1 then (1 : ℝ) else 0) = ((Fintype.card F : ℝ) - 1) / 2 := by
      rw [← hcard]
      have : (2 : ℝ) * ((univ.filter fun b => χ (b - s) = 1).card : ℝ) =
          (Fintype.card F : ℝ) - 1 := by exact_mod_cast hout
      linarith
    rw [h2]
    ring
  -- the numerator for `h(x₂)`
  have hnum2 : ∑ a, ∑ b, (if fibre0 s a b then h b else 0) =
      ((Fintype.card F : ℝ) - 2) * ∑ b, (if χ (b - s) = 1 then h b else 0) := by
    rw [fibre_sum_comm (fun _ _ b => h b) s]
    have h1 (b : F) : (if χ (b - s) = 1 then ∑ a, (if fibre0 s a b then h b else 0) else 0) =
        ((Fintype.card F : ℝ) - 2) * (if χ (b - s) = 1 then h b else 0) := by
      split_ifs with hb
      · rw [inner_sum_fibre hb (fun _ => h b)]
        simp only [sum_const, card_univ, nsmul_eq_mul]
        ring
      · ring
    simp only [h1]
    rw [← Finset.mul_sum]
  have hDval : D = ((Fintype.card F : ℝ) - 1) * ((Fintype.card F : ℝ) - 2) / 2 := by
    linarith [hden]
  unfold condExp0
  rw [← hD, hnum1, hnum2, hDval]
  field_simp
  ring

end Sarkozy.TraceMixing
