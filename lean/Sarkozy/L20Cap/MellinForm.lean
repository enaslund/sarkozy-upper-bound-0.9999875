module

public import Sarkozy.L20Cap.MellinH7
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# `H_u ⪰ -(3r + q - q²) I` from the proposed H7 (`lem:rectangle-mellin`, the lower bound)

`paper/sections/20a_rectangle_gram.tex`, `lem:rectangle-mellin`, last claim, at `F = 𝔽_p`. The
multiplicative characters `χ` of `𝔽_p` (`p - 1` of them) diagonalize the multiplicative
convolution `H_0` on `𝔽_p^×` (`H0_eigen`); with `f̂(χ) = ∑_w f(w)χ(w⁻¹)`:
* `fhat_inversion`: `∑_χ f̂(χ)χ(v) = (p - 1) f(v)` on `𝔽_p^×` (orthogonality of the characters,
  Mathlib's `DirichletCharacter.sum_char_inv_mul_char_eq`);
* `fhat_parseval`: `∑_χ |f̂(χ)|² = (p - 1)∑_v f(v)²`;
* `H0_form_eq`: `∑_{v,w} f(v)H_0(v, w)f(w) = (p - 1)⁻¹ ∑_χ λ_χ |f̂(χ)|²`;
* **`H0_form_lower`**: with H7 (`Target.SymSquareMellin`),
  `∑_{v,w ≠ 0} f(v)H_0(v, w)f(w) ≥ -(3r + q - q²)∑_{v ≠ 0} f(v)²`;
* **`Hu_form_lower`**: the same for every `u`, on `𝔽_p ∖ {u}` (translation, `Tu_transl`).
-/

@[expose] public section

open scoped BigOperators ComplexConjugate
open Finset

namespace Sarkozy.L20Cap

variable (p : ℕ) [Fact p.Prime]

/-- `f̂(χ) = ∑_w f(w) χ(w⁻¹)`. -/
noncomputable def fhat (f : ZMod p → ℝ) (χ : MulChar (ZMod p) ℂ) : ℂ :=
  ∑ w, (f w : ℂ) * χ w⁻¹

theorem char_orth (w v : ZMod p) (hw : w ≠ 0) :
    ∑ χ : MulChar (ZMod p) ℂ, χ w⁻¹ * χ v = if w = v then ((p - 1 : ℕ) : ℂ) else 0 := by
  have hu : IsUnit w := isUnit_iff_ne_zero.mpr hw
  have := DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu v
  rw [Nat.totient_prime (Fact.out : p.Prime)] at this
  exact this

theorem fhat_inversion (f : ZMod p → ℝ) (hf0 : f 0 = 0) {v : ZMod p} (hv : v ≠ 0) :
    ∑ χ : MulChar (ZMod p) ℂ, fhat p f χ * χ v = ((p - 1 : ℕ) : ℂ) * (f v : ℂ) := by
  unfold fhat
  simp only [sum_mul]
  rw [sum_comm]
  have e : ∀ w : ZMod p, ∑ χ : MulChar (ZMod p) ℂ, (f w : ℂ) * χ w⁻¹ * χ v =
      if w = v then ((p - 1 : ℕ) : ℂ) * (f w : ℂ) else 0 := by
    intro w
    by_cases hw : w = 0
    · subst hw
      have hv' : (0 : ZMod p) ≠ v := Ne.symm hv
      simp [hf0, hv']
    · rw [show (∑ χ : MulChar (ZMod p) ℂ, (f w : ℂ) * χ w⁻¹ * χ v) =
          (f w : ℂ) * ∑ χ : MulChar (ZMod p) ℂ, χ w⁻¹ * χ v by
        rw [mul_sum]; exact sum_congr rfl fun χ _ => by ring, char_orth p w v hw]
      split_ifs <;> ring
  rw [sum_congr rfl fun w _ => e w, sum_ite_eq' univ v]
  simp

theorem conj_char_inv (χ : MulChar (ZMod p) ℂ) (w : ZMod p) : conj (χ w⁻¹) = χ w := by
  have h := MulChar.star_apply' χ w⁻¹
  rw [MulChar.inv_apply', inv_inv] at h
  exact h

theorem conj_fhat (f : ZMod p → ℝ) (χ : MulChar (ZMod p) ℂ) :
    conj (fhat p f χ) = ∑ v, (f v : ℂ) * χ v := by
  unfold fhat
  rw [map_sum]
  refine sum_congr rfl fun v _ => ?_
  rw [map_mul, Complex.conj_ofReal, conj_char_inv]

theorem fhat_parseval (f : ZMod p → ℝ) (hf0 : f 0 = 0) :
    ∑ χ : MulChar (ZMod p) ℂ, fhat p f χ * conj (fhat p f χ) =
      ((p - 1 : ℕ) : ℂ) * ∑ v, ((f v ^ 2 : ℝ) : ℂ) := by
  simp only [conj_fhat, mul_sum]
  rw [sum_comm]
  have e : ∀ v : ZMod p, ∑ χ : MulChar (ZMod p) ℂ, fhat p f χ * ((f v : ℂ) * χ v) =
      (f v : ℂ) * (((p - 1 : ℕ) : ℂ) * (f v : ℂ)) := by
    intro v
    by_cases hv : v = 0
    · subst hv; simp [hf0]
    · rw [← fhat_inversion p f hf0 hv, mul_sum]
      exact sum_congr rfl fun χ _ => by ring
  rw [sum_congr rfl fun v _ => e v]
  push_cast
  exact sum_congr rfl fun v _ => by ring

/-- **The quadratic form of `H_0` in the character basis**:
`∑_{v,w} f(v)H_0(v, w)f(w) = (p - 1)⁻¹ ∑_χ λ_χ |f̂(χ)|²`. -/
theorem H0_form_eq (f : ZMod p → ℝ) (hf0 : f 0 = 0) :
    ((∑ v, ∑ w, f v * Hu (0 : ZMod p) v w * f w : ℝ) : ℂ) =
      (((p - 1 : ℕ) : ℂ))⁻¹ * ∑ χ : MulChar (ZMod p) ℂ,
        (∑ t, (Hu (0 : ZMod p) 1 t : ℂ) * χ t) * (fhat p f χ * conj (fhat p f χ)) := by
  have hn : ((p - 1 : ℕ) : ℂ) ≠ 0 := by
    have : 2 ≤ p := (Fact.out : p.Prime).two_le
    exact_mod_cast (by omega : p - 1 ≠ 0)
  -- `H f = (p - 1)⁻¹ ∑_χ f̂(χ) λ_χ χ`
  have hHf : ∀ v : ZMod p, v ≠ 0 → ∑ w, (Hu (0 : ZMod p) v w : ℂ) * (f w : ℂ) =
      (((p - 1 : ℕ) : ℂ))⁻¹ * ∑ χ : MulChar (ZMod p) ℂ,
        fhat p f χ * ((∑ t, (Hu (0 : ZMod p) 1 t : ℂ) * χ t) * χ v) := by
    intro v hv
    have hf : ∀ w : ZMod p, (f w : ℂ) =
        (((p - 1 : ℕ) : ℂ))⁻¹ * ∑ χ : MulChar (ZMod p) ℂ, fhat p f χ * χ w := by
      intro w
      by_cases hw : w = 0
      · subst hw; simp [hf0, MulChar.map_zero]
      · rw [fhat_inversion p f hf0 hw]; field_simp
    simp only [hf, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun χ _ => ?_
    rw [← H0_eigen χ hv, mul_sum, mul_sum]
    exact sum_congr rfl fun w _ => by ring
  push_cast
  have e : ∀ v : ZMod p, ((f v : ℂ)) * ∑ w, (Hu (0 : ZMod p) v w : ℂ) * (f w : ℂ) =
      (((p - 1 : ℕ) : ℂ))⁻¹ * ∑ χ : MulChar (ZMod p) ℂ,
        (∑ t, (Hu (0 : ZMod p) 1 t : ℂ) * χ t) * (fhat p f χ * ((f v : ℂ) * χ v)) := by
    intro v
    by_cases hv : v = 0
    · subst hv; simp [hf0, MulChar.map_zero]
    · rw [hHf v hv, mul_sum, mul_sum, mul_sum]
      exact sum_congr rfl fun χ _ => by ring
  have e2 : ∑ v, ∑ w, (f v : ℂ) * (Hu (0 : ZMod p) v w : ℂ) * (f w : ℂ) =
      ∑ v, (f v : ℂ) * ∑ w, (Hu (0 : ZMod p) v w : ℂ) * (f w : ℂ) := by
    refine sum_congr rfl fun v _ => ?_
    rw [mul_sum]; exact sum_congr rfl fun w _ => by ring
  rw [e2, sum_congr rfl fun v _ => e v, ← mul_sum]
  congr 1
  rw [sum_comm]
  refine sum_congr rfl fun χ _ => ?_
  rw [← mul_sum, ← mul_sum, conj_fhat]

/-- **`H_0 ⪰ -(3r + q - q²) I` on `𝔽_p^×`** (`lem:rectangle-mellin`, the lower bound), from the
proposed H7: in the character basis the form is `(p - 1)⁻¹ ∑_χ λ_χ |f̂(χ)|²`, every `λ_χ` with
`χ ≠ 1` is at least `-(3r + q - q²)` (`eigen_lower`), `λ_1 ≥ 0`, and Parseval. -/
theorem H0_form_lower (hH7 : Target.SymSquareMellin) (hp2 : p ≠ 2) (f : ZMod p → ℝ)
    (hf0 : f 0 = 0) :
    -(3 / Real.sqrt p + (p : ℝ)⁻¹ - (p : ℝ)⁻¹ ^ 2) * ∑ v, f v ^ 2 ≤
      ∑ v, ∑ w, f v * Hu (0 : ZMod p) v w * f w := by
  set c := 3 / Real.sqrt p + (p : ℝ)⁻¹ - (p : ℝ)⁻¹ ^ 2 with hc
  have hp2' : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hn0 : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < p - 1)
  set N : MulChar (ZMod p) ℂ → ℝ := fun χ => Complex.normSq (fhat p f χ) with hNdef
  have hN : ∀ χ, fhat p f χ * conj (fhat p f χ) = (N χ : ℂ) := fun χ => Complex.mul_conj _
  have hN0 : ∀ χ, 0 ≤ N χ := fun χ => Complex.normSq_nonneg _
  -- Parseval
  have hpars : ∑ χ : MulChar (ZMod p) ℂ, N χ = ((p - 1 : ℕ) : ℝ) * ∑ v, f v ^ 2 := by
    have h := fhat_parseval p f hf0
    simp only [hN] at h
    exact_mod_cast h
  -- the form in the character basis, real parts
  set lam : MulChar (ZMod p) ℂ → ℂ := fun χ => ∑ t, (Hu (0 : ZMod p) 1 t : ℂ) * χ t with hlam
  have hQ := H0_form_eq p f hf0
  simp only [hN] at hQ
  have hQre : ∑ v, ∑ w, f v * Hu (0 : ZMod p) v w * f w =
      ((p - 1 : ℕ) : ℝ)⁻¹ * ∑ χ : MulChar (ZMod p) ℂ, (lam χ).re * N χ := by
    have h := congrArg Complex.re hQ
    rw [Complex.ofReal_re] at h
    rw [h]
    have e : (((p - 1 : ℕ) : ℂ))⁻¹ = ((((p - 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [e, Complex.re_ofReal_mul, Complex.re_sum]
    congr 1
    refine sum_congr rfl fun χ _ => ?_
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  -- each eigenvalue is at least `-c`
  have hc0 : 0 ≤ c := by
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
    have h1 : (p : ℝ)⁻¹ ^ 2 ≤ (p : ℝ)⁻¹ := by
      have : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp1
      nlinarith [inv_nonneg.mpr (le_trans zero_le_one hp1)]
    have h2 : 0 ≤ 3 / Real.sqrt p := div_nonneg (by norm_num) (Real.sqrt_nonneg _)
    linarith
  have hlow : ∀ χ : MulChar (ZMod p) ℂ, -c ≤ (lam χ).re := by
    intro χ
    by_cases hχ : χ = 1
    · subst hχ
      have : 0 ≤ (lam 1).re := by
        simp only [hlam, Complex.re_sum]
        refine sum_nonneg fun t _ => ?_
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        refine mul_nonneg (sq_nonneg _) ?_
        by_cases ht : t = 0
        · subst ht; simp [MulChar.map_zero]
        · rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr ht)]; simp
      linarith
    · exact eigen_lower hH7 p hp2 hχ
  rw [hQre]
  have hsum : -c * ∑ χ : MulChar (ZMod p) ℂ, N χ ≤ ∑ χ : MulChar (ZMod p) ℂ, (lam χ).re * N χ := by
    rw [mul_sum]
    exact sum_le_sum fun χ _ => mul_le_mul_of_nonneg_right (hlow χ) (hN0 χ)
  rw [hpars] at hsum
  have hinv : 0 < ((p - 1 : ℕ) : ℝ)⁻¹ := inv_pos.mpr hn0
  have := mul_le_mul_of_nonneg_left hsum hinv.le
  calc -c * ∑ v, f v ^ 2 = ((p - 1 : ℕ) : ℝ)⁻¹ * (-c * (((p - 1 : ℕ) : ℝ) * ∑ v, f v ^ 2)) := by
        field_simp
    _ ≤ _ := this

/-- **`H_u ⪰ -(3r + q - q²) I` on `𝔽_p ∖ {u}`** (`lem:rectangle-mellin`), from the proposed H7,
for every `u` (translate `u` to `0`). -/
theorem Hu_form_lower (hH7 : Target.SymSquareMellin) (hp2 : p ≠ 2) (u : ZMod p)
    (g : ZMod p → ℝ) (hgu : g u = 0) :
    -(3 / Real.sqrt p + (p : ℝ)⁻¹ - (p : ℝ)⁻¹ ^ 2) * ∑ v, g v ^ 2 ≤
      ∑ v, ∑ w, g v * Hu u v w * g w := by
  set f : ZMod p → ℝ := fun x => g (x + u) with hfdef
  have hf0 : f 0 = 0 := by simp [hfdef, hgu]
  have h := H0_form_lower p hH7 hp2 f hf0
  have e1 : ∑ v, g v ^ 2 = ∑ v, f v ^ 2 :=
    (Fintype.sum_equiv (Equiv.addRight u) (fun v => f v ^ 2) (fun v => g v ^ 2)
      fun v => by simp [hfdef]).symm
  have e2 : ∑ v, ∑ w, g v * Hu u v w * g w = ∑ v, ∑ w, f v * Hu (0 : ZMod p) v w * f w := by
    symm
    refine Fintype.sum_equiv (Equiv.addRight u) _ _ fun v => ?_
    refine Fintype.sum_equiv (Equiv.addRight u) _ _ fun w => ?_
    simp only [Equiv.coe_addRight, hfdef]
    unfold Hu
    rw [Tu_transl u (v + u) (w + u)]
    simp
  rw [e1, e2]
  exact h

end Sarkozy.L20Cap
