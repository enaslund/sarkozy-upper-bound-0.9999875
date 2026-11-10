module

public import Sarkozy.TraceMixing.Kernel

/-!
# The nonzero frequencies of the pair operator (`lem:trace-mixing`(b))

`paper/sections/12_labellings.tex`, proof of `lem:trace-mixing`(b), "Nonzero frequencies".
For the pair `(z_u, z_v)` use the coordinates `(x, y)`, `z_v = x + y`; the translations act on
`x` and on the conditioning labels, the square dilations on `x`, `y` and the labels.

`fourier_step` is the abstract form: let `K r x y` be a kernel (the conditional operator from
the pair to the other labels, row `r`), with weights `t r ≥ 0` on the rows, such that
translating `x` by `β` is undone by a bijection `τ_β` of the rows, and dilating `(x, y)` by a
nonzero square `α` by a bijection `σ_α`. Then for every `f` whose averages over `x` vanish
(`∑_x f(x, y) = 0` for each `y`, the space `⊕_{k≠0} H_k` of the paper),
`∑_r t_r (∑_{x,y} K_r(x,y) f(x,y))² ≤ 2/(p-1) · tr · ∑_{x,y} f(x,y)²`,
`tr = ∑_r t_r ∑_{x,y} K_r(x,y)²`.

The proof is the paper's, with explicit sums over the additive characters `e(kx)` of `𝔽_p`:
the frequencies `k` are orthogonal after averaging over translations (`Parseval`), each
frequency is bounded by its trace `τ_k` (Cauchy–Schwarz), `τ` is constant on the square classes
(dilations), and `∑_k τ_k = p · tr` (Parseval).
-/

@[expose] public section

open Finset Complex
open scoped BigOperators ComplexConjugate

namespace Sarkozy.TraceMixing

variable {p : ℕ} [Fact p.Prime]

/-- The additive character `e(t) = exp(2πi t/p)` of `𝔽_p`. -/
noncomputable def ech (t : ZMod p) : ℂ := (ZMod.stdAddChar t : ℂ)

theorem ech_add (a b : ZMod p) : ech (a + b) = ech a * ech b := by
  unfold ech
  rw [AddChar.map_add_eq_mul]

theorem ech_zero : ech (0 : ZMod p) = 1 := by
  unfold ech
  rw [AddChar.map_zero_eq_one]

theorem norm_ech (t : ZMod p) : ‖ech t‖ = 1 := by
  unfold ech
  simp [ZMod.stdAddChar_apply]

theorem ech_mul_conj_self (b : ZMod p) : ech b * conj (ech b) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_ech]
  simp

theorem ech_sub (a b : ZMod p) : ech (a - b) = ech a * conj (ech b) := by
  have h : ech (a - b) * ech b = ech a := by rw [← ech_add, sub_add_cancel]
  calc ech (a - b) = ech (a - b) * (ech b * conj (ech b)) := by rw [ech_mul_conj_self, mul_one]
    _ = ech a * conj (ech b) := by rw [← mul_assoc, h]

/-- Orthogonality: `∑_k e(k t) = p [t = 0]`. -/
theorem sum_ech_mul (t : ZMod p) : ∑ k, ech (k * t) = if t = 0 then (p : ℂ) else 0 := by
  unfold ech
  rw [AddChar.sum_mulShift t (ZMod.isPrimitive_stdAddChar p)]
  split_ifs <;> simp [ZMod.card]

theorem sq_norm_eq_mul_conj (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- **Parseval** on `𝔽_p`: `∑_k ‖∑_x c(x) e(kx)‖² = p ∑_x ‖c(x)‖²`. -/
theorem parseval (c : ZMod p → ℂ) :
    ∑ k, ‖∑ x, c x * ech (k * x)‖ ^ 2 = p * ∑ x, ‖c x‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_natCast]
  have h1 (k : ZMod p) : (∑ x, c x * ech (k * x)) * conj (∑ x, c x * ech (k * x)) =
      ∑ x, ∑ x', c x * conj (c x') * ech (k * (x - x')) := by
    rw [map_sum, Finset.sum_mul_sum]
    apply sum_congr rfl
    intro x _
    apply sum_congr rfl
    intro x' _
    rw [map_mul, mul_sub, ech_sub]
    ring
  have h2 : ∑ k, ∑ x, ∑ x', c x * conj (c x') * ech (k * (x - x')) =
      ∑ x, ∑ x', c x * conj (c x') * ∑ k, ech (k * (x - x')) := by
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro x' _
    rw [Finset.mul_sum]
  have h3 (x x' : ZMod p) : c x * conj (c x') * ∑ k, ech (k * (x - x')) =
      if x' = x then (p : ℂ) * (c x * conj (c x)) else 0 := by
    rw [sum_ech_mul]
    by_cases h : x' = x
    · subst h
      simp only [sub_self, ite_true]
      ring
    · have hne : x - x' ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
      rw [ite_eq_right hne, ite_eq_right h, mul_zero]
  calc ∑ k, ((‖∑ x, c x * ech (k * x)‖ ^ 2 : ℝ) : ℂ)
      = ∑ k, (∑ x, c x * ech (k * x)) * conj (∑ x, c x * ech (k * x)) := by
        simp only [sq_norm_eq_mul_conj]
    _ = ∑ k, ∑ x, ∑ x', c x * conj (c x') * ech (k * (x - x')) := by simp only [h1]
    _ = ∑ x, ∑ x', c x * conj (c x') * ∑ k, ech (k * (x - x')) := h2
    _ = ∑ x, (p : ℂ) * (c x * conj (c x)) := by
        simp only [h3, Finset.sum_ite_eq', mem_univ, ite_true]
    _ = (p : ℂ) * ∑ x, ((‖c x‖ ^ 2 : ℝ) : ℂ) := by
        rw [Finset.mul_sum]
        simp only [sq_norm_eq_mul_conj]

/-- **Fourier inversion** on `𝔽_p`: `a(x) = p⁻¹ ∑_k â(k) e(kx)`,
`â(k) = ∑_x a(x) conj(e(kx))`. -/
theorem inversion (a : ZMod p → ℂ) (x : ZMod p) :
    a x = (p : ℂ)⁻¹ * ∑ k, (∑ x', a x' * conj (ech (k * x'))) * ech (k * x) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h1 : ∑ k, (∑ x', a x' * conj (ech (k * x'))) * ech (k * x) =
      ∑ x', a x' * ∑ k, ech (k * (x - x')) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro x' _
    apply sum_congr rfl
    intro k _
    rw [mul_sub, ech_sub]
    ring
  have h2 (x' : ZMod p) : a x' * ∑ k, ech (k * (x - x')) =
      if x' = x then (p : ℂ) * a x else 0 := by
    rw [sum_ech_mul]
    by_cases h : x' = x
    · subst h
      simp only [sub_self, ite_true]
      ring
    · have hne : x - x' ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
      rw [ite_eq_right hne, ite_eq_right h, mul_zero]
  rw [h1]
  simp only [h2, Finset.sum_ite_eq', mem_univ, ite_true]
  field_simp

/-- Cauchy–Schwarz for complex sums. -/
theorem norm_sum_mul_sq_le {ι : Type*} [Fintype ι] (a b : ι → ℂ) :
    ‖∑ i, a i * b i‖ ^ 2 ≤ (∑ i, ‖a i‖ ^ 2) * ∑ i, ‖b i‖ ^ 2 := by
  have h1 : ‖∑ i, a i * b i‖ ≤ ∑ i, ‖a i‖ * ‖b i‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp only [norm_mul]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq univ (fun i => ‖a i‖) (fun i => ‖b i‖)
  have h0 : 0 ≤ ‖∑ i, a i * b i‖ := norm_nonneg _
  calc ‖∑ i, a i * b i‖ ^ 2 ≤ (∑ i, ‖a i‖ * ‖b i‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ ≤ _ := h2

theorem real_sq_eq_norm_sq (x : ℝ) : x ^ 2 = ‖(x : ℂ)‖ ^ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **The nonzero-frequency bound of `lem:trace-mixing`(b).** -/
theorem fourier_step (hp2 : p ≠ 2) {R : Type*} [Fintype R] (t : R → ℝ) (ht : ∀ r, 0 ≤ t r)
    (K : R → ZMod p → ZMod p → ℝ) (τ : ZMod p → R ≃ R)
    (hKt : ∀ β r x y, K (τ β r) (x + β) y = K r x y) (htt : ∀ β r, t (τ β r) = t r)
    (σ : ZMod p → R ≃ R)
    (hKd : ∀ α : ZMod p, quadraticChar (ZMod p) α = 1 → ∀ r x y,
      K (σ α r) (α * x) (α * y) = K r x y)
    (htd : ∀ α : ZMod p, quadraticChar (ZMod p) α = 1 → ∀ r, t (σ α r) = t r)
    (f : ZMod p → ZMod p → ℝ) (hf : ∀ y, ∑ x, f x y = 0) :
    ∑ r, t r * (∑ x, ∑ y, K r x y * f x y) ^ 2 ≤
      2 / ((p : ℝ) - 1) * (∑ r, t r * ∑ x, ∑ y, K r x y ^ 2) * ∑ x, ∑ y, f x y ^ 2 := by
  have hpP : p.Prime := Fact.out
  have hp3 : (3 : ℝ) ≤ p := by
    have h2 : 2 ≤ p := hpP.two_le
    have : 3 ≤ p := by omega
    exact_mod_cast this
  have hpR0 : (0 : ℝ) < p := by linarith
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hpP.ne_zero
  set T : R → ℝ := fun r => ∑ x, ∑ y, K r x y * f x y with hT
  set L : R → ZMod p → ZMod p → ℂ := fun r k y => ∑ x, (K r x y : ℂ) * ech (k * x) with hL
  set Fh : ZMod p → ZMod p → ℂ := fun k y => ∑ x, (f x y : ℂ) * conj (ech (k * x)) with hFh
  set Λ : R → ZMod p → ℂ := fun r k => ∑ y, Fh k y * L r k y with hΛ
  set tr : ℝ := ∑ r, t r * ∑ x, ∑ y, K r x y ^ 2 with htr
  -- Step A: the translates of a row
  have hperm : ∀ H : ZMod p → ZMod p → ZMod p → ℂ,
      ∑ x, ∑ y, ∑ k, H x y k = ∑ k, ∑ y, ∑ x, H x y k := by
    intro H
    calc ∑ x, ∑ y, ∑ k, H x y k = ∑ x, ∑ k, ∑ y, H x y k := by
          apply sum_congr rfl
          intro x _
          exact Finset.sum_comm
      _ = ∑ k, ∑ x, ∑ y, H x y k := Finset.sum_comm
      _ = ∑ k, ∑ y, ∑ x, H x y k := by
          apply sum_congr rfl
          intro k _
          exact Finset.sum_comm
  have hA (β : ZMod p) (r : R) :
      ((T (τ β r) : ℝ) : ℂ) = (p : ℂ)⁻¹ * ∑ k, Λ r k * ech (β * k) := by
    have h1 : T (τ β r) = ∑ x, ∑ y, K r x y * f (x + β) y := by
      simp only [hT]
      rw [← Equiv.sum_comp (Equiv.addRight β)]
      apply sum_congr rfl
      intro x _
      apply sum_congr rfl
      intro y _
      simp only [Equiv.coe_addRight]
      rw [hKt]
    have h2 (x y : ZMod p) : ((f (x + β) y : ℝ) : ℂ) =
        (p : ℂ)⁻¹ * ∑ k, Fh k y * ech (k * x) * ech (β * k) := by
      rw [inversion (fun x' => ((f x' y : ℝ) : ℂ)) (x + β)]
      congr 1
      apply sum_congr rfl
      intro k _
      rw [mul_add, ech_add, mul_comm k β]
      simp only [hFh]
      ring
    rw [h1]
    push_cast
    calc ∑ x, ∑ y, ((K r x y : ℝ) : ℂ) * ((f (x + β) y : ℝ) : ℂ)
        = ∑ x, ∑ y, (p : ℂ)⁻¹ * ∑ k, ((K r x y : ℝ) : ℂ) * Fh k y * ech (k * x) *
            ech (β * k) := by
          apply sum_congr rfl
          intro x _
          apply sum_congr rfl
          intro y _
          rw [h2 x y, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          apply sum_congr rfl
          intro k _
          ring
      _ = (p : ℂ)⁻¹ * ∑ x, ∑ y, ∑ k, ((K r x y : ℝ) : ℂ) * Fh k y * ech (k * x) *
            ech (β * k) := by
          rw [Finset.mul_sum]
          apply sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
      _ = (p : ℂ)⁻¹ * ∑ k, ∑ y, ∑ x, ((K r x y : ℝ) : ℂ) * Fh k y * ech (k * x) *
            ech (β * k) := by
          rw [hperm]
      _ = (p : ℂ)⁻¹ * ∑ k, Λ r k * ech (β * k) := by
          congr 1
          apply sum_congr rfl
          intro k _
          simp only [hΛ, hL, Finset.sum_mul, Finset.mul_sum]
          apply sum_congr rfl
          intro y _
          apply sum_congr rfl
          intro x _
          ring
  -- Step B: averaging over the translations
  have hB (r : R) : ∑ β, T (τ β r) ^ 2 = (p : ℝ)⁻¹ * ∑ k, ‖Λ r k‖ ^ 2 := by
    have h1 (β : ZMod p) : T (τ β r) ^ 2 = ((p : ℝ)⁻¹) ^ 2 * ‖∑ k, Λ r k * ech (β * k)‖ ^ 2 := by
      rw [real_sq_eq_norm_sq, hA, norm_mul, mul_pow, norm_inv, Complex.norm_natCast]
    simp only [h1]
    rw [← Finset.mul_sum, parseval (Λ r)]
    field_simp
  -- Step C: the energy as a sum over frequencies
  have hC : ∑ r, t r * T r ^ 2 = ((p : ℝ) ^ 2)⁻¹ * ∑ r, t r * ∑ k, ‖Λ r k‖ ^ 2 := by
    have h1 (β : ZMod p) : ∑ r, t r * T (τ β r) ^ 2 = ∑ r, t r * T r ^ 2 := by
      calc ∑ r, t r * T (τ β r) ^ 2 = ∑ r, t (τ β r) * T (τ β r) ^ 2 := by simp only [htt]
        _ = ∑ r, t r * T r ^ 2 := Equiv.sum_comp (τ β) (fun r => t r * T r ^ 2)
    have h2 : (p : ℝ) * ∑ r, t r * T r ^ 2 = ∑ r, t r * ∑ β, T (τ β r) ^ 2 := by
      calc (p : ℝ) * ∑ r, t r * T r ^ 2 = ∑ β : ZMod p, ∑ r, t r * T (τ β r) ^ 2 := by
            simp only [h1, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
        _ = ∑ r, t r * ∑ β, T (τ β r) ^ 2 := by
            rw [Finset.sum_comm]
            simp only [Finset.mul_sum]
    simp only [hB] at h2
    have h3 : ∑ r, t r * ((p : ℝ)⁻¹ * ∑ k, ‖Λ r k‖ ^ 2) =
        (p : ℝ)⁻¹ * ∑ r, t r * ∑ k, ‖Λ r k‖ ^ 2 := by
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro r _
      ring
    rw [h3] at h2
    have hp0 : (p : ℝ) ≠ 0 := hpR0.ne'
    calc ∑ r, t r * T r ^ 2 = (p : ℝ)⁻¹ * ((p : ℝ) * ∑ r, t r * T r ^ 2) := by
          rw [← mul_assoc, inv_mul_cancel₀ hp0, one_mul]
      _ = (p : ℝ)⁻¹ * ((p : ℝ)⁻¹ * ∑ r, t r * ∑ k, ‖Λ r k‖ ^ 2) := by rw [h2]
      _ = ((p : ℝ) ^ 2)⁻¹ * ∑ r, t r * ∑ k, ‖Λ r k‖ ^ 2 := by
          rw [← mul_assoc, ← mul_inv, ← sq]
  -- Step D: frequency zero vanishes
  have hD (r : R) : Λ r 0 = 0 := by
    simp only [hΛ, hFh, zero_mul, ech_zero, map_one, mul_one]
    apply Finset.sum_eq_zero
    intro y _
    have : ∑ x, ((f x y : ℝ) : ℂ) = 0 := by exact_mod_cast hf y
    rw [this, zero_mul]
  -- Step F: the frequency traces
  set τk : ZMod p → ℝ := fun k => ∑ r, t r * ∑ y, ‖L r k y‖ ^ 2 with hτk
  have hτ0 (k : ZMod p) : 0 ≤ τk k :=
    Finset.sum_nonneg (fun r _ => mul_nonneg (ht r)
      (Finset.sum_nonneg (fun y _ => sq_nonneg _)))
  have hFsum : ∑ k, τk k = p * tr := by
    have h1 (r : R) (y : ZMod p) : ∑ k, ‖L r k y‖ ^ 2 = p * ∑ x, K r x y ^ 2 := by
      simp only [hL]
      rw [parseval (fun x => ((K r x y : ℝ) : ℂ))]
      congr 1
      apply sum_congr rfl
      intro x _
      rw [← real_sq_eq_norm_sq]
    calc ∑ k, τk k = ∑ r, t r * ∑ y, ∑ k, ‖L r k y‖ ^ 2 := by
          simp only [hτk, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply sum_congr rfl
          intro r _
          rw [Finset.sum_comm]
      _ = ∑ r, t r * ∑ y, (p : ℝ) * ∑ x, K r x y ^ 2 := by simp only [h1]
      _ = p * tr := by
          simp only [htr, Finset.mul_sum]
          apply sum_congr rfl
          intro r _
          rw [Finset.sum_comm]
          apply sum_congr rfl
          intro x _
          apply sum_congr rfl
          intro y _
          ring
  -- Step G: the frequency traces are constant on the square classes
  have hG (α : ZMod p) (hα : quadraticChar (ZMod p) α = 1) (k : ZMod p) : τk (α * k) = τk k := by
    have hα0 : α ≠ 0 := by
      intro h
      rw [h, quadraticChar_zero] at hα
      exact zero_ne_one hα
    have hLd (r : R) (y : ZMod p) : L (σ α r) k (α * y) = L r (α * k) y := by
      simp only [hL]
      rw [← Equiv.sum_comp (Equiv.mulLeft₀ α hα0)]
      apply sum_congr rfl
      intro x _
      show ((K (σ α r) (α * x) (α * y) : ℝ) : ℂ) * ech (k * (α * x)) =
        ((K r x y : ℝ) : ℂ) * ech (α * k * x)
      rw [hKd α hα]
      congr 2
      ring
    simp only [hτk]
    calc ∑ r, t r * ∑ y, ‖L r (α * k) y‖ ^ 2 = ∑ r, t r * ∑ y, ‖L (σ α r) k (α * y)‖ ^ 2 := by
          simp only [hLd]
      _ = ∑ r, t (σ α r) * ∑ y, ‖L (σ α r) k y‖ ^ 2 := by
          apply sum_congr rfl
          intro r _
          rw [htd α hα]
          congr 1
          exact Equiv.sum_comp (Equiv.mulLeft₀ α hα0) (fun y => ‖L (σ α r) k y‖ ^ 2)
      _ = ∑ r, t r * ∑ y, ‖L r k y‖ ^ 2 :=
          Equiv.sum_comp (σ α) (fun r => t r * ∑ y, ‖L r k y‖ ^ 2)
  -- Step H: each nonzero frequency is at most `2/(p-1)` of the total
  have hH (k : ZMod p) (hk : k ≠ 0) : τk k ≤ 2 / ((p : ℝ) - 1) * (p * tr) := by
    have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
    obtain ⟨ν, hνsq⟩ := FiniteField.exists_nonsquare hF
    have hν : quadraticChar (ZMod p) ν = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hνsq
    have hν0 : ν ≠ 0 := fun h => hνsq (h ▸ IsSquare.zero)
    have hclass {a b : ZMod p} (ha : a ≠ 0) (hab : quadraticChar (ZMod p) a =
        quadraticChar (ZMod p) b) : τk b = τk a := by
      have h := hG (b * a⁻¹) (quadraticChar_ratio ha hab) a
      rwa [mul_assoc, inv_mul_cancel₀ ha, mul_one] at h
    have hone : quadraticChar (ZMod p) (1 : ZMod p) = 1 := map_one _
    have hpair (k' : ZMod p) (hk' : k' ≠ 0) : τk k' + τk (ν * k') = τk 1 + τk ν := by
      rcases quadraticChar_dichotomy hk' with h | h
      · have e1 : τk k' = τk 1 := hclass (a := 1) (b := k') one_ne_zero (by rw [hone, h])
        have e2 : τk (ν * k') = τk ν :=
          hclass (a := ν) (b := ν * k') hν0 (by rw [map_mul, h, hν]; ring)
        rw [e1, e2]
      · have e1 : τk k' = τk ν := hclass (a := ν) (b := k') hν0 (by rw [hν, h])
        have e2 : τk (ν * k') = τk 1 :=
          hclass (a := 1) (b := ν * k') one_ne_zero (by rw [map_mul, h, hν, hone]; ring)
        rw [e1, e2]
        ring
    set c := τk 1 + τk ν with hc
    have hsum2 : ∑ k', (τk k' + τk (ν * k')) = (p : ℝ) * c + (2 * τk 0 - c) := by
      have h1 (k' : ZMod p) : τk k' + τk (ν * k') = c + (if k' = 0 then 2 * τk 0 - c else 0) := by
        by_cases h0 : k' = 0
        · subst h0
          simp only [mul_zero, ite_true]
          ring
        · rw [hpair k' h0, ite_eq_right h0, add_zero]
      simp only [h1, Finset.sum_add_distrib, sum_const, card_univ, ZMod.card, nsmul_eq_mul,
        Finset.sum_ite_eq', mem_univ, ite_true]
    have hshift : ∑ k', τk (ν * k') = ∑ k', τk k' :=
      Equiv.sum_comp (Equiv.mulLeft₀ ν hν0) τk
    rw [Finset.sum_add_distrib, hshift, hFsum] at hsum2
    have hck : τk k ≤ c := by
      rcases quadraticChar_dichotomy hk with h | h
      · have e1 : τk k = τk 1 := hclass (a := 1) (b := k) one_ne_zero (by rw [hone, h])
        rw [e1]
        linarith [hτ0 ν]
      · have e1 : τk k = τk ν := hclass (a := ν) (b := k) hν0 (by rw [hν, h])
        rw [e1]
        linarith [hτ0 1]
    have hc_le : c ≤ 2 / ((p : ℝ) - 1) * (p * tr) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      have := hτ0 0
      nlinarith
    linarith
  -- Step I: Parseval for `f`
  have hI : ∑ k, ∑ y, ‖Fh k y‖ ^ 2 = p * ∑ x, ∑ y, f x y ^ 2 := by
    have hconj (k y : ZMod p) : Fh k y = conj (∑ x, ((f x y : ℝ) : ℂ) * ech (k * x)) := by
      simp only [hFh, map_sum, map_mul, Complex.conj_ofReal]
    have h1 (y : ZMod p) : ∑ k, ‖Fh k y‖ ^ 2 = p * ∑ x, f x y ^ 2 := by
      simp only [hconj, RCLike.norm_conj]
      rw [parseval (fun x => ((f x y : ℝ) : ℂ))]
      congr 1
      apply sum_congr rfl
      intro x _
      rw [← real_sq_eq_norm_sq]
    rw [Finset.sum_comm]
    simp only [h1]
    rw [← Finset.mul_sum, Finset.sum_comm]
  -- Step J: combine
  have htr0 : 0 ≤ tr := Finset.sum_nonneg (fun r _ => mul_nonneg (ht r)
    (Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ => sq_nonneg _))))
  set M : ℝ := 2 / ((p : ℝ) - 1) * (p * tr) with hM
  have hM0 : 0 ≤ M := mul_nonneg (div_nonneg (by norm_num) (by linarith))
    (mul_nonneg hpR0.le htr0)
  have hJ (k : ZMod p) : ∑ r, t r * ‖Λ r k‖ ^ 2 ≤ M * ∑ y, ‖Fh k y‖ ^ 2 := by
    by_cases hk : k = 0
    · subst hk
      rw [Finset.sum_eq_zero (fun r _ => by rw [hD r, norm_zero]; ring)]
      exact mul_nonneg hM0 (Finset.sum_nonneg (fun y _ => sq_nonneg _))
    · have h1 (r : R) : t r * ‖Λ r k‖ ^ 2 ≤ t r * ((∑ y, ‖L r k y‖ ^ 2) * ∑ y, ‖Fh k y‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (ht r)
        have := norm_sum_mul_sq_le (fun y => Fh k y) (fun y => L r k y)
        simp only [hΛ]
        linarith
      calc ∑ r, t r * ‖Λ r k‖ ^ 2
          ≤ ∑ r, t r * ((∑ y, ‖L r k y‖ ^ 2) * ∑ y, ‖Fh k y‖ ^ 2) := Finset.sum_le_sum (fun r _ => h1 r)
        _ = τk k * ∑ y, ‖Fh k y‖ ^ 2 := by
            have e : τk k * ∑ y, ‖Fh k y‖ ^ 2 =
                ∑ r, t r * ((∑ y, ‖L r k y‖ ^ 2) * ∑ y, ‖Fh k y‖ ^ 2) := by
              simp only [hτk]
              rw [Finset.sum_mul]
              apply sum_congr rfl
              intro r _
              ring
            rw [e]
        _ ≤ M * ∑ y, ‖Fh k y‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (hH k hk) (Finset.sum_nonneg (fun y _ => sq_nonneg _))
  have hsumJ : ∑ r, t r * ∑ k, ‖Λ r k‖ ^ 2 ≤ M * (p * ∑ x, ∑ y, f x y ^ 2) := by
    calc ∑ r, t r * ∑ k, ‖Λ r k‖ ^ 2 = ∑ k, ∑ r, t r * ‖Λ r k‖ ^ 2 := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
      _ ≤ ∑ k, M * ∑ y, ‖Fh k y‖ ^ 2 := Finset.sum_le_sum (fun k _ => hJ k)
      _ = M * (p * ∑ x, ∑ y, f x y ^ 2) := by rw [← Finset.mul_sum, hI]
  have hgoal : ∑ r, t r * T r ^ 2 ≤ 2 / ((p : ℝ) - 1) * tr * ∑ x, ∑ y, f x y ^ 2 := by
    rw [hC]
    have hp2' : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
    calc ((p : ℝ) ^ 2)⁻¹ * ∑ r, t r * ∑ k, ‖Λ r k‖ ^ 2
        ≤ ((p : ℝ) ^ 2)⁻¹ * (M * (p * ∑ x, ∑ y, f x y ^ 2)) :=
          mul_le_mul_of_nonneg_left hsumJ (inv_nonneg.mpr hp2'.le)
      _ = 2 / ((p : ℝ) - 1) * tr * ∑ x, ∑ y, f x y ^ 2 := by
          rw [hM]
          field_simp
  exact hgoal

end Sarkozy.TraceMixing
