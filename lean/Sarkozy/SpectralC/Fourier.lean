module

public import Sarkozy.Characters.GaussJacobi

@[expose] public section

/-!
# Single-variable Fourier analysis on `𝔽_p` (`subsec:spec:fourier`)

`paper/sections/14_spectral.tex`, `subsec:spec:fourier`. On `L²(𝔽_p)` with the uniform
probability, `⟨f, g⟩ = E_a \overline{f(a)} g(a)` (`ip`); the characters `e_ξ(a) = e(ξa/p)`
(`ech`) form an orthonormal basis (`ip_ech_ech`), `ĝ(ξ) = ⟨e_ξ, g⟩` (`fcoef`), with
inversion (`fourier_inv`) and Parseval (`ip_eq_sum_fcoef`).

New material for this paper (Mathlib's `AddChar.sum_mulShift` gives the orthogonality).
-/

namespace Sarkozy.SpectralC

open Finset Complex
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime]

/-- The character `e_ξ(a) = e(ξa/p)`. -/
noncomputable def ech (ξ a : ZMod p) : ℂ := ZMod.stdAddChar (ξ * a)

/-- The inner product of `L²(𝔽_p)` for the uniform probability, conjugate-linear in the first
variable: `⟨f, g⟩ = E_a \overline{f(a)} g(a)`. -/
noncomputable def ip (f g : ZMod p → ℂ) : ℂ := (p : ℂ)⁻¹ * ∑ a, conj (f a) * g a

/-- The Fourier coefficient `ĝ(ξ) = ⟨e_ξ, g⟩`. -/
noncomputable def fcoef (g : ZMod p → ℂ) (ξ : ZMod p) : ℂ := ip (ech ξ) g

lemma p_ne_zero_C : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

lemma ech_zero_left (a : ZMod p) : ech (0 : ZMod p) a = 1 := by
  simp [ech]

lemma conj_ech (ξ a : ZMod p) : conj (ech ξ a) = ech (-ξ) a := by
  unfold ech
  rw [neg_mul, AddChar.map_neg_eq_conj]

lemma ech_add_left (ξ η a : ZMod p) : ech (ξ + η) a = ech ξ a * ech η a := by
  unfold ech
  rw [add_mul, AddChar.map_add_eq_mul]

lemma ech_add_right (ξ a b : ZMod p) : ech ξ (a + b) = ech ξ a * ech ξ b := by
  unfold ech
  rw [mul_add, AddChar.map_add_eq_mul]

lemma norm_ech (ξ a : ZMod p) : ‖ech ξ a‖ = 1 := by
  unfold ech
  simp [ZMod.stdAddChar_apply]

/-- `∑_a e_ξ(a) = p [ξ = 0]`. -/
lemma sum_ech (ξ : ZMod p) : ∑ a, ech ξ a = if ξ = 0 then (p : ℂ) else 0 := by
  have h := AddChar.sum_mulShift (ψ := (ZMod.stdAddChar : AddChar (ZMod p) ℂ)) ξ
    (ZMod.isPrimitive_stdAddChar p)
  unfold ech
  simp_rw [mul_comm ξ]
  rw [h, ZMod.card]
  split_ifs <;> simp

/-- **Orthonormality**: `⟨e_ξ, e_η⟩ = [ξ = η]`. -/
theorem ip_ech_ech (ξ η : ZMod p) : ip (ech ξ) (ech η) = if ξ = η then 1 else 0 := by
  unfold ip
  have h : ∀ a, conj (ech ξ a) * ech η a = ech (η - ξ) a := by
    intro a
    rw [conj_ech, ← ech_add_left]
    ring_nf
  simp_rw [h]
  rw [sum_ech]
  by_cases hξη : ξ = η
  · rw [ite_eq_left (by rw [hξη, sub_self]), ite_eq_left hξη, inv_mul_cancel₀ p_ne_zero_C]
  · rw [ite_eq_right (fun h0 => hξη (sub_eq_zero.mp h0).symm), ite_eq_right hξη, mul_zero]

lemma ech_comm (ξ a : ZMod p) : ech ξ a = ech a ξ := by
  unfold ech
  rw [mul_comm]

lemma ech_neg_mul (ξ a b : ZMod p) : ech (-ξ) b * ech ξ a = ech (a - b) ξ := by
  unfold ech
  rw [← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- **Fourier inversion**: `g = ∑_ξ ĝ(ξ) e_ξ`. -/
theorem fourier_inv (g : ZMod p → ℂ) (a : ZMod p) : g a = ∑ ξ, fcoef g ξ * ech ξ a := by
  unfold fcoef ip
  have h : ∀ ξ, (p : ℂ)⁻¹ * (∑ b, conj (ech ξ b) * g b) * ech ξ a =
      (p : ℂ)⁻¹ * ∑ b, g b * ech (a - b) ξ := by
    intro ξ
    rw [mul_assoc, sum_mul]
    congr 1
    apply sum_congr rfl
    intro b _
    rw [conj_ech, ← ech_neg_mul ξ a b]
    ring
  simp_rw [h]
  rw [← mul_sum, sum_comm]
  have h2 : ∀ b, ∑ ξ, g b * ech (a - b) ξ = if b = a then g b * (p : ℂ) else 0 := by
    intro b
    rw [← mul_sum]
    have := sum_ech (p := p) (a - b)
    rw [this]
    by_cases hb : b = a
    · rw [ite_eq_left (by rw [hb, sub_self]), ite_eq_left hb]
    · rw [ite_eq_right (fun h0 => hb (sub_eq_zero.mp h0).symm), ite_eq_right hb, mul_zero]
  simp_rw [h2]
  rw [sum_ite_eq' univ a, ite_eq_left (mem_univ a), mul_comm, mul_assoc,
    mul_inv_cancel₀ p_ne_zero_C, mul_one]

/-- **Parseval**: `⟨f, g⟩ = ∑_ξ \overline{f̂(ξ)} ĝ(ξ)`. -/
theorem ip_eq_sum_fcoef (f g : ZMod p → ℂ) :
    ip f g = ∑ ξ, conj (fcoef f ξ) * fcoef g ξ := by
  have hf : ∀ a, conj (f a) = ∑ ξ, conj (fcoef f ξ) * conj (ech ξ a) := by
    intro a
    conv_lhs => rw [fourier_inv f a]
    rw [map_sum]
    apply sum_congr rfl
    intro ξ _
    rw [map_mul]
  calc ip f g = (p : ℂ)⁻¹ * ∑ a, (∑ ξ, conj (fcoef f ξ) * conj (ech ξ a)) * g a := by
        unfold ip
        congr 1
        apply sum_congr rfl
        intro a _
        rw [hf a]
    _ = ∑ ξ, conj (fcoef f ξ) * ((p : ℂ)⁻¹ * ∑ a, conj (ech ξ a) * g a) := by
        simp_rw [sum_mul, mul_sum]
        rw [sum_comm]
        apply sum_congr rfl
        intro ξ _
        apply sum_congr rfl
        intro a _
        ring
    _ = ∑ ξ, conj (fcoef f ξ) * fcoef g ξ := rfl

/-- `ĝ(0) = E g`. -/
lemma fcoef_zero (g : ZMod p → ℂ) : fcoef g 0 = (p : ℂ)⁻¹ * ∑ a, g a := by
  unfold fcoef ip
  simp [ech_zero_left]

/-- `⟨g, g⟩ = E|g|²`, a nonnegative real. -/
lemma ip_self (g : ZMod p → ℂ) : ip g g = (((p : ℝ)⁻¹ * ∑ a, ‖g a‖ ^ 2 : ℝ) : ℂ) := by
  unfold ip
  push_cast
  congr 1
  apply sum_congr rfl
  intro a _
  rw [mul_comm, Complex.mul_conj', ← Complex.ofReal_pow]

end Sarkozy.SpectralC
