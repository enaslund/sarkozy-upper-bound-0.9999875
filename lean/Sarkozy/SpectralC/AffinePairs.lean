module

public import Sarkozy.SpectralC.Gauss

@[expose] public section

/-!
# `Aff_p`-invariant kernels and pair laws (`lem:spec:affpair`)

`paper/sections/14_spectral.tex`, `lem:spec:affpair`. `Aff_p = {z ↦ sz + c : s ∈ Q_p, c ∈ 𝔽_p}`
acts diagonally on `𝔽_p²` (`IsAffInv`).

* `affInv_orbit`: an invariant `κ` is constant on the three orbits (the diagonal,
  `Ω = {b − a ∈ Q_p}`, `Ω' = {b − a ∉ Q_p ∪ {0}}`): `κ = α 1_diag + β₊ 1_Ω + β₋ 1_Ω'`;
* `kerOp_decomp`: then `K_κ = (α − (β₊+β₋)/2) I/p + ((β₊+β₋)/2) J + ((β₊−β₋)/2) C`
  (the identity used in the proof of (d)(i));
* `affInv_eigen` (part (a)): `K_κ e_ξ = λ_ξ e_ξ` with
  `λ_0 = α/p + ((p−1)/p)(β₊+β₋)/2` and `λ_ξ = (α − (β₊+β₋)/2)/p + c_ξ (β₊−β₋)/2` (`ξ ≠ 0`);
* `affPair_law` (part (b)): for an `Aff_p`-invariant pair law, `π^= = Pr(u = v)`,
  `D = E χ(v − u)`, the law is constant on the orbits, `π⁺ + π⁻ = 1 − π^=`, `π⁺ − π⁻ = D`, and
  for mean-zero `g, h`,
  `E[\overline{g(u)} h(v)] = π^= ⟨g,h⟩ − ((1−π^=)/(p−1)) ⟨g,h⟩ + (p/(p−1)) D ⟨g, Ch⟩`
  (`eq:spec:affpair`);
* `condExp_translation_zero` (part (d)(iii)): for a translation-invariant law on `𝔽_p^W` and a
  translation-invariant `f` of mean zero, `E[f(x) | x_w] = 0`.

New material for this paper.
-/

namespace Sarkozy.SpectralC

open Finset Complex Sarkozy.Characters
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime]

/-- `Aff_p`-invariance of a kernel on `𝔽_p²`: `κ(sa + c, sb + c) = κ(a, b)` for every nonzero
square `s` and every `c`. -/
def IsAffInv {α : Type*} (κ : ZMod p → ZMod p → α) : Prop :=
  ∀ s c a b : ZMod p, s ≠ 0 → IsSquare s → κ (s * a + c) (s * b + c) = κ a b

/-- The kernel operator `(K_κ h)(a) = E_b κ(a, b) h(b)`. -/
noncomputable def kerOp (κ : ZMod p → ZMod p → ℂ) (h : ZMod p → ℂ) (a : ZMod p) : ℂ :=
  (p : ℂ)⁻¹ * ∑ b, κ a b * h b

/-- The mean `E h`. -/
noncomputable def meanC (h : ZMod p → ℂ) : ℂ := (p : ℂ)⁻¹ * ∑ a, h a

lemma oddChar (hp2 : p ≠ 2) : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]

lemma chiC_of_isSquare {t : ZMod p} (ht : t ≠ 0) (hs : IsSquare t) : chiC p t = 1 := by
  rw [chiC_apply, (quadraticChar_one_iff_isSquare ht).mpr hs]
  simp

lemma chiC_of_not_isSquare {t : ZMod p} (hs : ¬ IsSquare t) : chiC p t = -1 := by
  rw [chiC_apply, quadraticChar_neg_one_iff_not_isSquare.mpr hs]
  simp

/-- **The orbits of `Aff_p` on `𝔽_p²`**: an invariant kernel is constant on the diagonal, on
`Ω` and on `Ω'`; `n` is any fixed nonsquare. -/
theorem affInv_orbit {α : Type*} (κ : ZMod p → ZMod p → α) (hκ : IsAffInv κ) {n : ZMod p}
    (hn : ¬ IsSquare n) (a b : ZMod p) :
    κ a b = if a = b then κ 0 0 else if IsSquare (b - a) then κ 0 1 else κ 0 n := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn ⟨0, by ring⟩
  by_cases hab : a = b
  · subst hab
    rw [ite_eq_left rfl]
    have h := hκ 1 a 0 0 one_ne_zero ⟨1, by ring⟩
    simpa using h
  · rw [ite_eq_right hab]
    have hd : b - a ≠ 0 := fun h => hab (sub_eq_zero.mp h).symm
    by_cases hs : IsSquare (b - a)
    · rw [ite_eq_left hs]
      have h := hκ (b - a) a 0 1 hd hs
      simpa using h
    · rw [ite_eq_right hs]
      set t := (b - a) * n⁻¹ with ht
      have ht0 : t ≠ 0 := mul_ne_zero hd (inv_ne_zero hn0)
      have htn : t * n = b - a := by rw [ht, mul_assoc, inv_mul_cancel₀ hn0, mul_one]
      have hts : IsSquare t := by
        have h1 : chiC p (b - a) = chiC p t * chiC p n := by rw [← map_mul, htn]
        rw [chiC_of_not_isSquare hs, chiC_of_not_isSquare hn] at h1
        have h2 : chiC p t = 1 := by linear_combination h1
        rw [chiC_apply] at h2
        have h3 : quadraticChar (ZMod p) t = 1 := by exact_mod_cast h2
        exact (quadraticChar_one_iff_isSquare ht0).mp h3
      have h := hκ t a 0 n ht0 hts
      rw [htn, mul_zero, zero_add, sub_add_cancel] at h
      exact h

/-- The orbit decomposition in terms of `χ`:
`α 1_diag + β₊ 1_Ω + β₋ 1_Ω' = (α − (β₊+β₋)/2)[a = b] + (β₊+β₋)/2 + ((β₊−β₋)/2) χ(b − a)`. -/
lemma orbit_eq_chi (α βp βm : ℂ) (a b : ZMod p) :
    (if a = b then α else if IsSquare (b - a) then βp else βm) =
      (α - (βp + βm) / 2) * (if a = b then 1 else 0) + (βp + βm) / 2 +
        (βp - βm) / 2 * chiC p (b - a) := by
  by_cases hab : a = b
  · subst hab
    rw [ite_eq_left rfl, ite_eq_left rfl, sub_self, chiC_zero]
    ring
  · have hd : b - a ≠ 0 := fun h => hab (sub_eq_zero.mp h).symm
    rw [ite_eq_right hab, ite_eq_right hab]
    by_cases hs : IsSquare (b - a)
    · rw [ite_eq_left hs, chiC_of_isSquare hd hs]
      ring
    · rw [ite_eq_right hs, chiC_of_not_isSquare hs]
      ring

/-- **The kernel operator of an orbit-constant kernel** (proof of `lem:spec:affpair`(d)(i)):
`K_κ h = (α − (β₊+β₋)/2) h/p + ((β₊+β₋)/2) E h + ((β₊−β₋)/2) C h`. -/
theorem kerOp_decomp (κ : ZMod p → ZMod p → ℂ) (α βp βm : ℂ)
    (hκ : ∀ a b, κ a b = if a = b then α else if IsSquare (b - a) then βp else βm)
    (h : ZMod p → ℂ) (a : ZMod p) :
    kerOp κ h a = (α - (βp + βm) / 2) / p * h a + (βp + βm) / 2 * meanC h +
      (βp - βm) / 2 * gaussOp h a := by
  unfold kerOp meanC gaussOp
  simp_rw [hκ, orbit_eq_chi (p := p)]
  simp_rw [add_mul, sum_add_distrib, mul_add]
  have h1 : ∑ b, (α - (βp + βm) / 2) * (if a = b then (1 : ℂ) else 0) * h b =
      (α - (βp + βm) / 2) * h a := by
    simp_rw [mul_assoc, ← mul_sum]
    congr 1
    rw [sum_eq_single a]
    · simp
    · intro b _ hb; rw [ite_eq_right (Ne.symm hb), zero_mul]
    · intro h0; exact absurd (mem_univ a) h0
  rw [h1]
  simp_rw [mul_assoc, ← mul_sum]
  ring

lemma meanC_ech (ξ : ZMod p) : meanC (ech ξ) = if ξ = 0 then 1 else 0 := by
  unfold meanC
  rw [sum_ech]
  split_ifs
  · exact inv_mul_cancel₀ p_ne_zero_C
  · exact mul_zero _

/-- **`lem:spec:affpair`(a)**: an `Aff_p`-invariant kernel is `α 1_diag + β₊ 1_Ω + β₋ 1_Ω'`, and
`K_κ e_ξ = λ_ξ e_ξ` with `λ_0 = α/p + ((p−1)/p)(β₊+β₋)/2` and
`λ_ξ = (α − (β₊+β₋)/2)/p + c_ξ (β₊−β₋)/2` for `ξ ≠ 0`. -/
theorem affInv_eigen (hp2 : p ≠ 2) (κ : ZMod p → ZMod p → ℂ) (hκ : IsAffInv κ) :
    ∃ α βp βm : ℂ,
      (∀ a b, κ a b = if a = b then α else if IsSquare (b - a) then βp else βm) ∧
      (∀ a, kerOp κ (ech 0) a = (α / p + ((p : ℂ) - 1) / p * ((βp + βm) / 2)) * ech 0 a) ∧
      (∀ ξ, ξ ≠ 0 → ∀ a, kerOp κ (ech ξ) a =
        ((α - (βp + βm) / 2) / p + gaussEig ξ * ((βp - βm) / 2)) * ech ξ a) := by
  obtain ⟨n, hn⟩ := FiniteField.exists_nonsquare (oddChar (p := p) hp2)
  have horb := affInv_orbit κ hκ hn
  refine ⟨κ 0 0, κ 0 1, κ 0 n, horb, ?_, ?_⟩
  · intro a
    rw [kerOp_decomp κ _ _ _ horb, meanC_ech, ite_eq_left rfl, gaussOp_ech hp2, gaussEig_zero,
      ech_zero_left]
    field_simp [p_ne_zero_C (p := p)]
    ring
  · intro ξ hξ a
    rw [kerOp_decomp κ _ _ _ horb, meanC_ech, ite_eq_right hξ, gaussOp_ech hp2]
    ring

/-! ## Pair laws (`lem:spec:affpair`(b)) -/

lemma sum_chiC_sub (hp2 : p ≠ 2) (a : ZMod p) : ∑ b, chiC p (b - a) = 0 := by
  rw [Fintype.sum_equiv (Equiv.subRight a) (fun b => chiC p (b - a)) (fun t => chiC p t)
    (fun b => rfl), sum_chiC hp2]

lemma sum_chiC_sub_sq (a : ZMod p) : ∑ b, chiC p (b - a) ^ 2 = (p : ℂ) - 1 := by
  rw [Fintype.sum_equiv (Equiv.subRight a) (fun b => chiC p (b - a) ^ 2) (fun t => chiC p t ^ 2)
    (fun b => rfl)]
  rw [← add_sum_erase _ _ (mem_univ (0 : ZMod p)), chiC_zero]
  have h : ∀ t ∈ univ.erase (0 : ZMod p), chiC p t ^ 2 = 1 := by
    intro t ht
    rw [mem_erase] at ht
    rw [chiC_apply]
    rcases quadraticChar_dichotomy ht.1 with h | h <;> rw [h] <;> norm_num
  rw [sum_congr rfl h, sum_const, card_erase_of_mem (mem_univ _), card_univ, ZMod.card]
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  rw [nsmul_eq_mul, mul_one, Nat.cast_sub hp1, Nat.cast_one]
  ring

/-- **`lem:spec:affpair`(b), pair laws.** Let `π` be an `Aff_p`-invariant probability on `𝔽_p²`
(the law of `(u, v)`), `π^= = Pr(u = v)`, `D = E χ(v − u)`, `π⁺ = Pr(v − u ∈ Q_p)`,
`π⁻ = Pr(v − u ∉ Q_p ∪ {0})`. Then the law is constant on each orbit (a mixture of the uniform
laws on the diagonal, `Ω`, `Ω'`), `π⁺ + π⁻ = 1 − π^=`, `π⁺ − π⁻ = D`, and for mean-zero `g, h`
`E[\overline{g(u)} h(v)] = π^= ⟨g,h⟩ − ((1−π^=)/(p−1)) ⟨g,h⟩ + (p/(p−1)) D ⟨g, Ch⟩`
(`eq:spec:affpair`). -/
theorem affPair_law (hp2 : p ≠ 2) (π : ZMod p → ZMod p → ℝ) (hπ1 : ∑ a, ∑ b, π a b = 1)
    (hinv : IsAffInv π) {n : ZMod p} (hn : ¬ IsSquare n) :
    let πeq : ℝ := ∑ a, π a a
    let πp : ℝ := ∑ a, ∑ b, if a ≠ b ∧ IsSquare (b - a) then π a b else 0
    let πm : ℝ := ∑ a, ∑ b, if a ≠ b ∧ ¬ IsSquare (b - a) then π a b else 0
    let D : ℂ := ∑ a, ∑ b, (π a b : ℂ) * chiC p (b - a)
    (∀ a b, π a b = if a = b then π 0 0 else if IsSquare (b - a) then π 0 1 else π 0 n) ∧
      πp + πm = 1 - πeq ∧ (πp - πm : ℂ) = D ∧
      ∀ g h : ZMod p → ℂ, meanC g = 0 → meanC h = 0 →
        ∑ a, ∑ b, (π a b : ℂ) * conj (g a) * h b =
          (πeq : ℂ) * ip g h - (1 - πeq) / ((p : ℂ) - 1) * ip g h +
            (p : ℂ) / ((p : ℂ) - 1) * D * ip g (gaussOp h) := by
  intro πeq πp πm D
  have horb := affInv_orbit π hinv hn
  refine ⟨horb, ?_, ?_, ?_⟩
  · -- the three orbits partition `𝔽_p²`
    have h : ∀ a b, π a b = (if a = b then π a b else 0) +
        (if a ≠ b ∧ IsSquare (b - a) then π a b else 0) +
        (if a ≠ b ∧ ¬ IsSquare (b - a) then π a b else 0) := by
      intro a b
      by_cases hab : a = b
      · simp [hab]
      · by_cases hs : IsSquare (b - a) <;> simp [hab, hs]
    have h2 : ∑ a, ∑ b, (if a = b then π a b else 0) = πeq := by
      apply sum_congr rfl
      intro a _
      rw [sum_ite_eq univ a, ite_eq_left (mem_univ a)]
    have htot : ∑ a, ∑ b, π a b = πeq + πp + πm := by
      conv_lhs => rw [show (fun a => ∑ b, π a b) = fun a => ∑ b, ((if a = b then π a b else 0) +
        (if a ≠ b ∧ IsSquare (b - a) then π a b else 0) +
        (if a ≠ b ∧ ¬ IsSquare (b - a) then π a b else 0)) from funext fun a =>
          sum_congr rfl fun b _ => h a b]
      simp_rw [sum_add_distrib]
      rw [h2]
    linarith
  · -- `π⁺ − π⁻ = E χ(v − u)`
    have h : ∀ a b, (π a b : ℂ) * chiC p (b - a) =
        ((if a ≠ b ∧ IsSquare (b - a) then π a b else 0 : ℝ) : ℂ) -
          ((if a ≠ b ∧ ¬ IsSquare (b - a) then π a b else 0 : ℝ) : ℂ) := by
      intro a b
      by_cases hab : a = b
      · subst hab; simp [chiC_zero]
      · have hd : b - a ≠ 0 := fun h0 => hab (sub_eq_zero.mp h0).symm
        by_cases hs : IsSquare (b - a)
        · simp [hab, hs, chiC_of_isSquare hd hs]
        · simp [hab, hs, chiC_of_not_isSquare hs]
    show ((πp : ℝ) : ℂ) - ((πm : ℝ) : ℂ) = D
    simp only [πp, πm, D]
    push_cast
    simp_rw [h, sum_sub_distrib]
  · intro g h hg hh
    -- the kernel `κ = p² π` and its decomposition
    set κ : ZMod p → ZMod p → ℂ := fun a b => (p : ℂ) ^ 2 * (π a b : ℂ) with hκdef
    set A : ℂ := (p : ℂ) ^ 2 * π 0 0 - ((p : ℂ) ^ 2 * π 0 1 + (p : ℂ) ^ 2 * π 0 n) / 2 with hA
    set B : ℂ := ((p : ℂ) ^ 2 * π 0 1 + (p : ℂ) ^ 2 * π 0 n) / 2 with hB
    set Cc : ℂ := ((p : ℂ) ^ 2 * π 0 1 - (p : ℂ) ^ 2 * π 0 n) / 2 with hCc
    have hκ : ∀ a b, κ a b = if a = b then (p : ℂ) ^ 2 * π 0 0 else
        if IsSquare (b - a) then (p : ℂ) ^ 2 * π 0 1 else (p : ℂ) ^ 2 * π 0 n := by
      intro a b
      simp only [hκdef]
      rw [horb a b]
      split_ifs <;> rfl
    have hκχ : ∀ a b, κ a b = A * (if a = b then 1 else 0) + B + Cc * chiC p (b - a) := by
      intro a b
      rw [hκ, orbit_eq_chi]
    have hpC := p_ne_zero_C (p := p)
    -- the three moments of `κ`
    have hm1 : ∑ a, ∑ b, κ a b = A * p + B * (p : ℂ) ^ 2 := by
      simp_rw [hκχ, sum_add_distrib, ← mul_sum, sum_chiC_sub hp2]
      simp only [sum_ite_eq, mem_univ, ite_true, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
      ring
    have hm2 : ∑ a, κ a a = (p : ℂ) * (A + B) := by
      simp_rw [hκχ, sub_self, chiC_zero]
      simp only [ite_true, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
      ring
    have hm3 : ∑ a, ∑ b, κ a b * chiC p (b - a) = Cc * ((p : ℂ) * ((p : ℂ) - 1)) := by
      simp_rw [hκχ, add_mul, sum_add_distrib, mul_assoc, ← mul_sum]
      have hz : ∀ a, ∑ b, (if a = b then (1 : ℂ) else 0) * chiC p (b - a) = 0 := by
        intro a
        rw [sum_eq_single a]
        · rw [sub_self, chiC_zero, mul_zero]
        · intro b _ hb; rw [ite_eq_right (Ne.symm hb), zero_mul]
        · intro h0; exact absurd (mem_univ a) h0
      simp_rw [hz, sum_chiC_sub hp2, ← sq, sum_chiC_sub_sq]
      simp only [mul_zero, sum_const_zero, zero_add, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
    -- the probabilities in terms of `A, B, Cc`
    have hk1 : ∑ a, ∑ b, κ a b = (p : ℂ) ^ 2 * ((∑ a, ∑ b, π a b : ℝ) : ℂ) := by
      simp only [hκdef, Complex.ofReal_sum, mul_sum]
    have hk2 : ∑ a, κ a a = (p : ℂ) ^ 2 * (πeq : ℂ) := by
      simp only [hκdef, πeq, Complex.ofReal_sum, mul_sum]
    have hk3 : ∑ a, ∑ b, κ a b * chiC p (b - a) = (p : ℂ) ^ 2 * D := by
      simp only [hκdef, D, mul_sum, mul_assoc]
    have R1 : A + B * p = p := by
      have h1 := hk1.symm.trans hm1
      rw [hπ1, Complex.ofReal_one, mul_one] at h1
      apply mul_left_cancel₀ hpC
      linear_combination -h1
    have R2 : A + B = p * πeq := by
      have h1 := hk2.symm.trans hm2
      apply mul_left_cancel₀ hpC
      linear_combination -h1
    have R3 : Cc * ((p : ℂ) - 1) = p * D := by
      have h1 := hk3.symm.trans hm3
      apply mul_left_cancel₀ hpC
      linear_combination -h1
    -- the bilinear form
    have hbil : ∑ a, ∑ b, (π a b : ℂ) * conj (g a) * h b = ip g (kerOp κ h) := by
      unfold ip kerOp
      simp only [hκdef]
      simp_rw [mul_sum]
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro b _
      field_simp
    rw [hbil]
    have hK : ∀ a, kerOp κ h a = A / p * h a + Cc * gaussOp h a := by
      intro a
      rw [kerOp_decomp κ _ _ _ hκ, hh]
      simp only [hA, hB, hCc]
      ring
    have hip : ip g (kerOp κ h) = A / p * ip g h + Cc * ip g (gaussOp h) := by
      unfold ip
      simp_rw [hK, mul_add, sum_add_distrib, mul_add]
      congr 1
      · rw [mul_sum, mul_sum, mul_sum]; apply sum_congr rfl; intro a _; ring
      · rw [mul_sum, mul_sum, mul_sum]; apply sum_congr rfl; intro a _; ring
    rw [hip]
    have hp1 : (p : ℂ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
      intro h0
      have h1 : ((p : ℂ) - 1).re = 0 := by rw [h0]; simp
      simp at h1
      linarith
    have hA' : A = p * πeq - B := by linear_combination R2
    have hB' : B = p * (1 - πeq) / ((p : ℂ) - 1) := by
      rw [eq_div_iff hp1]
      linear_combination R1 - R2
    have hC' : Cc = p * D / ((p : ℂ) - 1) := by
      rw [eq_div_iff hp1]
      exact R3
    rw [hA', hB', hC']
    field_simp

/-! ## Translation-invariant laws (`lem:spec:affpair`(d)(iii)) -/

/-- **`lem:spec:affpair`(d)(iii)**: if the law of `x ∈ 𝔽_p^W` is invariant under the
simultaneous translations `x ↦ x + c𝟙` and `f(x + c𝟙) = f(x)` with `E f(x) = 0`, then
`E[f(x) | x_w] = 0` (as an unnormalized conditional sum, for every value `t` of `x_w`). -/
theorem condExp_translation_zero {W : Type*} [Fintype W] [DecidableEq W]
    (π : (W → ZMod p) → ℝ) (hπ : ∀ x c, π (x + fun _ => c) = π x)
    (f : (W → ZMod p) → ℝ) (hf : ∀ x c, f (x + fun _ => c) = f x)
    (hmean : ∑ x, π x * f x = 0) (w : W) (t : ZMod p) :
    ∑ x ∈ univ.filter (fun x => x w = t), π x * f x = 0 := by
  set g : ZMod p → ℝ := fun t => ∑ x ∈ univ.filter (fun x => x w = t), π x * f x with hg
  have hshift : ∀ t c, g (t + c) = g t := by
    intro t c
    simp only [hg]
    apply sum_nbij' (fun x => x - fun _ => c) (fun x => x + fun _ => c)
    · intro x hx
      rw [mem_filter] at hx ⊢
      refine ⟨mem_univ _, ?_⟩
      simp [hx.2]
    · intro x hx
      rw [mem_filter] at hx ⊢
      refine ⟨mem_univ _, ?_⟩
      simp [hx.2]
    · intro x _; simp
    · intro x _; simp
    · intro x _
      have h1 := hπ (x - fun _ => c) c
      have h2 := hf (x - fun _ => c) c
      simp only [sub_add_cancel] at h1 h2
      rw [h1, h2]
  have hconst : ∀ s, g s = g 0 := by
    intro s
    have := hshift 0 s
    rwa [zero_add] at this
  have htot : ∑ s, g s = ∑ x, π x * f x := by
    simp only [hg]
    exact sum_fiberwise univ (fun x : W → ZMod p => x w) (fun x => π x * f x)
  rw [hmean] at htot
  simp_rw [hconst] at htot
  rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul] at htot
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h0 : g 0 = 0 := by
    rcases mul_eq_zero.mp htot with h | h
    · exact absurd h hp0
    · exact h
  show g t = 0
  rw [hconst, h0]

end Sarkozy.SpectralC
