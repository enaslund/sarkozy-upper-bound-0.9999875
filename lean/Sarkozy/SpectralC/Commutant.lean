module

public import Sarkozy.SpectralC.AffinePairs

@[expose] public section

/-!
# The commutant of `Aff_p` (`lem:spec:affpair`(d)(i))

`paper/sections/14_spectral.tex`, `lem:spec:affpair`(d)(i). A real operator `T` on `L²(𝔽_p)`
(a real kernel `T a b`, `(Th)(a) = ∑_b T(a, b) h(b)`) that commutes with the operators
`h ↦ h ∘ γ`, `γ ∈ Aff_p`, is `α_T I + β_T J + γ_T C` with real `α_T, β_T, γ_T`
(`commutant_decomp`), and on `L²_0(𝔽_p)` it is `α_T I + γ_T C` (`commutant_on_meanZero`).
For `p ≡ 3 (mod 4)` it is a normal operator with `‖Th‖² = (α_T² + q γ_T²)‖h‖²` on `L²_0`
(`commutant_norm`), `α_T = tr(T)/(p − 1)` and `γ_T = tr(C^*T)/(1 − q)` for the traces on
`L²_0` (`commutant_traces`), and it is self-adjoint on `L²_0` if and only if `γ_T = 0`
(`commutant_selfAdjoint_iff`).

New material for this paper.
-/

namespace Sarkozy.SpectralC

open Finset Complex Sarkozy.Characters
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime]

/-- The operator of a real kernel: `(Th)(a) = ∑_b T(a, b) h(b)`. -/
noncomputable def matOp (T : ZMod p → ZMod p → ℝ) (h : ZMod p → ℂ) (a : ZMod p) : ℂ :=
  ∑ b, (T a b : ℂ) * h b

/-- The trace on `L²_0(𝔽_p)` in the basis `e_ξ`, `ξ ≠ 0`. -/
noncomputable def trace0 (X : (ZMod p → ℂ) → ZMod p → ℂ) : ℂ :=
  ∑ ξ ∈ univ.filter (fun ξ : ZMod p => ξ ≠ 0), ip (ech ξ) (X (ech ξ))

/-- Commuting with `h ↦ h ∘ γ` makes the kernel invariant. -/
lemma kernel_inv_of_commute (T : ZMod p → ZMod p → ℝ)
    (hT : ∀ (s c : ZMod p), s ≠ 0 → IsSquare s → ∀ (h : ZMod p → ℂ) (a : ZMod p),
      matOp T (fun b => h (s * b + c)) a = matOp T h (s * a + c)) :
    IsAffInv (fun a b => (T a b : ℂ)) := by
  intro s c a b hs hsq
  have h := hT s c hs hsq (fun t => if t = s * b + c then 1 else 0) a
  unfold matOp at h
  have hinj : ∀ t, (s * t + c = s * b + c) ↔ t = b := by
    intro t
    constructor
    · intro h1; exact mul_left_cancel₀ hs (by linear_combination h1)
    · intro h1; rw [h1]
  simp_rw [hinj] at h
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true] at h
  exact h.symm

/-- **`lem:spec:affpair`(d)(i), the decomposition**: `T = α_T I + β_T J + γ_T C` with real
coefficients. -/
theorem commutant_decomp (hp2 : p ≠ 2) (T : ZMod p → ZMod p → ℝ)
    (hT : ∀ (s c : ZMod p), s ≠ 0 → IsSquare s → ∀ (h : ZMod p → ℂ) (a : ZMod p),
      matOp T (fun b => h (s * b + c)) a = matOp T h (s * a + c)) :
    ∃ αT βT γT : ℝ, ∀ (h : ZMod p → ℂ) (a : ZMod p),
      matOp T h a = αT * h a + βT * meanC h + γT * gaussOp h a := by
  obtain ⟨n, hn⟩ := FiniteField.exists_nonsquare (oddChar (p := p) hp2)
  have hinv := kernel_inv_of_commute T hT
  -- `κ = p T`
  set κ : ZMod p → ZMod p → ℂ := fun a b => (p : ℂ) * (T a b : ℂ) with hκ
  have hκinv : IsAffInv κ := by
    intro s c a b hs hsq
    simp only [hκ]
    have h1 := hinv s c a b hs hsq
    simp only at h1
    rw [h1]
  have horb := affInv_orbit κ hκinv hn
  have hpC := p_ne_zero_C (p := p)
  have hop : ∀ h a, matOp T h a = kerOp κ h a := by
    intro h a
    unfold matOp kerOp
    simp only [hκ]
    rw [mul_sum]
    apply sum_congr rfl; intro b _
    field_simp
  refine ⟨(p : ℝ) * (T 0 0 - (T 0 1 + T 0 n) / 2) / p, (p : ℝ) * ((T 0 1 + T 0 n) / 2),
    (p : ℝ) * ((T 0 1 - T 0 n) / 2), ?_⟩
  intro h a
  rw [hop, kerOp_decomp κ _ _ _ horb]
  simp only [hκ]
  push_cast
  ring

/-- **`lem:spec:affpair`(d)(i)**: on `L²_0(𝔽_p)`, `T = α_T I + γ_T C`. -/
theorem commutant_on_meanZero (hp2 : p ≠ 2) (T : ZMod p → ZMod p → ℝ)
    (hT : ∀ (s c : ZMod p), s ≠ 0 → IsSquare s → ∀ (h : ZMod p → ℂ) (a : ZMod p),
      matOp T (fun b => h (s * b + c)) a = matOp T h (s * a + c)) :
    ∃ αT γT : ℝ, ∀ (h : ZMod p → ℂ), meanC h = 0 → ∀ a,
      matOp T h a = αT * h a + γT * gaussOp h a := by
  obtain ⟨αT, βT, γT, hdec⟩ := commutant_decomp hp2 T hT
  refine ⟨αT, γT, fun h hh a => ?_⟩
  rw [hdec, hh, mul_zero, add_zero]

/-- `c_ξ` is purely imaginary for `p ≡ 3 (mod 4)`: `|α + γ c_ξ|² = α² + q γ²` for `ξ ≠ 0`. -/
lemma normSq_eig_three (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (α γ : ℝ) {ξ : ZMod p} (hξ : ξ ≠ 0) :
    ‖(α : ℂ) + (γ : ℂ) * gaussEig ξ‖ ^ 2 = α ^ 2 + (p : ℝ)⁻¹ * γ ^ 2 := by
  have hcases := (epsG_cases (p := p) hp2).2 hp3
  have hχ : chiC p ξ = 1 ∨ chiC p ξ = -1 := by
    rw [chiC_apply]
    rcases quadraticChar_dichotomy hξ with h | h <;> rw [h] <;> simp
  have hr : (rp p) ^ 2 = (p : ℝ)⁻¹ := by
    unfold rp
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg p)]
  unfold gaussEig
  rw [← Complex.normSq_eq_norm_sq]
  rcases hcases with he | he <;> rcases hχ with hc | hc <;> rw [he, hc] <;>
    simp [Complex.normSq_apply] <;> nlinarith [hr]

/-- **`lem:spec:affpair`(d)(i), the norm** (`p ≡ 3 (mod 4)`): on `L²_0`,
`‖Th‖² = (α_T² + q γ_T²) ‖h‖²`; so `α_T I + γ_T C` is a normal operator of norm
`(α_T² + q γ_T²)^{1/2}` there. -/
theorem commutant_norm (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (αT γT : ℝ) (h : ZMod p → ℂ)
    (hh : meanC h = 0) :
    l2sq (fun a : ZMod p => (αT : ℂ) * h a + (γT : ℂ) * gaussOp h a) =
      (αT ^ 2 + (p : ℝ)⁻¹ * γT ^ 2) * l2sq h := by
  rw [l2sq_eq_sum_fcoef, l2sq_eq_sum_fcoef, mul_sum]
  apply sum_congr rfl
  intro ξ _
  have hlin : fcoef (fun a : ZMod p => (αT : ℂ) * h a + (γT : ℂ) * gaussOp h a) ξ =
      ((αT : ℂ) + (γT : ℂ) * gaussEig ξ) * fcoef h ξ := by
    unfold fcoef ip
    simp_rw [mul_add, sum_add_distrib, mul_add]
    have h1 := fcoef_gaussOp hp2 h ξ
    unfold fcoef ip at h1
    rw [show ∑ a, conj (ech ξ a) * (↑γT * gaussOp h a) =
      (γT : ℂ) * ∑ a, conj (ech ξ a) * gaussOp h a by rw [mul_sum]; apply sum_congr rfl; intro a _; ring]
    rw [mul_left_comm, h1]
    rw [show ∑ a, conj (ech ξ a) * (↑αT * h a) = (αT : ℂ) * ∑ a, conj (ech ξ a) * h a by
      rw [mul_sum]; apply sum_congr rfl; intro a _; ring]
    ring
  rw [hlin, norm_mul, mul_pow]
  by_cases hξ : ξ = 0
  · have h0 : fcoef h ξ = 0 := by
      rw [hξ, fcoef_zero]
      unfold meanC at hh
      exact hh
    rw [h0]
    simp
  · rw [normSq_eig_three hp2 hp3 αT γT hξ]

lemma conj_ip (f g : ZMod p → ℂ) : conj (ip f g) = ip g f := by
  unfold ip
  rw [map_mul, map_inv₀, Complex.conj_natCast, map_sum]
  congr 1
  apply sum_congr rfl; intro a _
  rw [map_mul, Complex.conj_conj, mul_comm]

lemma sum_gaussEig_ne_zero (hp2 : p ≠ 2) :
    ∑ ξ ∈ univ.filter (fun ξ : ZMod p => ξ ≠ 0), gaussEig ξ = 0 := by
  rw [sum_filter]
  have h : ∀ ξ : ZMod p, (if ξ ≠ 0 then gaussEig ξ else 0) = gaussEig ξ := by
    intro ξ
    by_cases hξ : ξ = 0
    · rw [ite_eq_right (not_not.mpr hξ), hξ, gaussEig_zero]
    · rw [ite_eq_left hξ]
  simp_rw [h]
  unfold gaussEig
  rw [← sum_mul, ← sum_mul, sum_chiC hp2, zero_mul, zero_mul]

lemma card_ne_zero_filter :
    ((univ.filter (fun ξ : ZMod p => ξ ≠ 0)).card : ℂ) = (p : ℂ) - 1 := by
  rw [filter_ne', card_erase_of_mem (mem_univ _), card_univ, ZMod.card]
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  rw [Nat.cast_sub hp1, Nat.cast_one]

lemma ip_ech_smul (ξ : ZMod p) (z : ℂ) : ip (ech ξ) (fun a => z * ech ξ a) = z := by
  unfold ip
  have h2 : ∑ a, conj (ech ξ a) * (z * ech ξ a) = z * ∑ a, conj (ech ξ a) * ech ξ a := by
    rw [mul_sum]; apply sum_congr rfl; intro a _; ring
  rw [h2]
  have h3 := ip_ech_ech (p := p) ξ ξ
  unfold ip at h3
  rw [ite_eq_left rfl] at h3
  rw [mul_left_comm, h3, mul_one]

/-- **`lem:spec:affpair`(d)(i), the traces**: `tr(α I + γ C) = (p − 1) α` and
`tr(C^*(α I + γ C)) = (1 − q) γ` on `L²_0`. -/
theorem commutant_traces (hp2 : p ≠ 2) (αT γT : ℝ) :
    trace0 (fun (h : ZMod p → ℂ) (a : ZMod p) => (αT : ℂ) * h a + (γT : ℂ) * gaussOp h a) =
        ((p : ℂ) - 1) * αT ∧
      trace0 (fun (h : ZMod p → ℂ) (a : ZMod p) =>
          gaussOpAdj (fun b => (αT : ℂ) * h b + (γT : ℂ) * gaussOp h b) a) =
        (1 - (p : ℂ)⁻¹) * γT := by
  have hT : ∀ ξ : ZMod p, (fun a => (αT : ℂ) * ech ξ a + (γT : ℂ) * gaussOp (ech ξ) a) =
      fun a => ((αT : ℂ) + (γT : ℂ) * gaussEig ξ) * ech ξ a := by
    intro ξ; funext a; rw [gaussOp_ech hp2]; ring
  constructor
  · simp only [trace0]
    simp_rw [hT, ip_ech_smul]
    rw [sum_add_distrib, sum_const, ← mul_sum, sum_gaussEig_ne_zero hp2, nsmul_eq_mul,
      card_ne_zero_filter]
    ring
  · simp only [trace0]
    have hadj : ∀ ξ : ZMod p, ip (ech ξ) (gaussOpAdj (fun b => (αT : ℂ) * ech ξ b +
        (γT : ℂ) * gaussOp (ech ξ) b)) =
        conj (gaussEig ξ) * ((αT : ℂ) + (γT : ℂ) * gaussEig ξ) := by
      intro ξ
      rw [← conj_ip, ← ip_gaussOp, conj_ip, hT]
      have hC : gaussOp (ech ξ) = fun a => gaussEig ξ * ech ξ a := funext (gaussOp_ech hp2 ξ)
      rw [hC]
      unfold ip
      have h2 : ∑ a, conj (gaussEig ξ * ech ξ a) * (((αT : ℂ) + (γT : ℂ) * gaussEig ξ) *
          ech ξ a) = conj (gaussEig ξ) * ((αT : ℂ) + (γT : ℂ) * gaussEig ξ) *
            ∑ a, conj (ech ξ a) * ech ξ a := by
        rw [mul_sum]; apply sum_congr rfl; intro a _; rw [map_mul]; ring
      rw [h2]
      have h3 := ip_ech_ech (p := p) ξ ξ
      unfold ip at h3
      rw [ite_eq_left rfl] at h3
      rw [mul_left_comm, h3, mul_one]
    simp_rw [hadj, mul_add, sum_add_distrib, ← sum_mul, ← map_sum, sum_gaussEig_ne_zero hp2,
      map_zero, zero_mul, zero_add]
    have hsq : ∀ ξ ∈ univ.filter (fun ξ : ZMod p => ξ ≠ 0),
        conj (gaussEig ξ) * ((γT : ℂ) * gaussEig ξ) = (γT : ℂ) * (p : ℂ)⁻¹ := by
      intro ξ hξ
      have hξ0 : ξ ≠ 0 := (mem_filter.mp hξ).2
      rw [mul_left_comm, mul_comm (conj _), Complex.mul_conj', norm_gaussEig hp2 hξ0]
      unfold rp
      push_cast
      rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg p)]
      push_cast
      ring
    rw [sum_congr rfl hsq, sum_const, nsmul_eq_mul, card_ne_zero_filter]
    have hpC := p_ne_zero_C (p := p)
    field_simp

/-- **`lem:spec:affpair`(d)(i), self-adjointness** (`p ≡ 3 (mod 4)`): `α_T I + γ_T C` is
self-adjoint on `L²_0` if and only if `γ_T = 0`. -/
theorem commutant_selfAdjoint_iff (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (αT γT : ℝ) :
    (∀ f g : ZMod p → ℂ, meanC f = 0 → meanC g = 0 →
        ip f (fun a => (αT : ℂ) * g a + (γT : ℂ) * gaussOp g a) =
          ip (fun a => (αT : ℂ) * f a + (γT : ℂ) * gaussOp f a) g) ↔ γT = 0 := by
  have hm1 : chiC p (-1) = -1 := by
    rw [chiC_neg_one hp2, ZMod.χ₄_nat_three_mod_four hp3]; simp
  -- `C^* = −C`
  have hadj : ∀ f g : ZMod p → ℂ, ip (gaussOp f) g = -ip f (gaussOp g) := by
    intro f g
    rw [ip_gaussOp]
    have : gaussOpAdj f = fun a => -gaussOp f a := by
      funext a
      unfold gaussOpAdj gaussOp
      rw [← mul_neg, ← sum_neg_distrib]
      congr 1
      apply sum_congr rfl; intro b _
      rw [conj_chiC, show a - b = -1 * (b - a) by ring, map_mul, hm1]
      ring
    rw [this]
    unfold ip
    rw [← mul_neg, ← sum_neg_distrib]
    congr 1
    apply sum_congr rfl; intro a _
    rw [map_neg]
    ring
  have hlin : ∀ f g : ZMod p → ℂ,
      ip f (fun a => (αT : ℂ) * g a + (γT : ℂ) * gaussOp g a) =
        (αT : ℂ) * ip f g + (γT : ℂ) * ip f (gaussOp g) := by
    intro f g
    unfold ip
    simp only [mul_add, sum_add_distrib, mul_sum]
    congr 1 <;> apply sum_congr rfl <;> intro a _ <;> ring
  have hlin' : ∀ f g : ZMod p → ℂ,
      ip (fun a => (αT : ℂ) * f a + (γT : ℂ) * gaussOp f a) g =
        (αT : ℂ) * ip f g + (γT : ℂ) * ip (gaussOp f) g := by
    intro f g
    unfold ip
    simp only [map_add, map_mul, Complex.conj_ofReal, add_mul, sum_add_distrib, mul_add, mul_sum]
    congr 1 <;> apply sum_congr rfl <;> intro a _ <;> ring
  constructor
  · intro h
    have h1 : (1 : ZMod p) ≠ 0 := one_ne_zero
    have hm : meanC (ech (1 : ZMod p)) = 0 := by rw [meanC_ech, ite_eq_right h1]
    have h2 := h (ech (1 : ZMod p)) (ech (1 : ZMod p)) hm hm
    rw [hlin, hlin', hadj] at h2
    have hc : ip (ech (1 : ZMod p)) (gaussOp (ech (1 : ZMod p))) = gaussEig (1 : ZMod p) := by
      have hC : gaussOp (ech (1 : ZMod p)) = fun a => gaussEig (1 : ZMod p) * ech 1 a :=
        funext (gaussOp_ech hp2 1)
      rw [hC, ip_ech_smul]
    rw [hc] at h2
    have hne : gaussEig (1 : ZMod p) ≠ 0 := by
      intro h0
      have := norm_gaussEig hp2 h1
      rw [h0, norm_zero] at this
      unfold rp at this
      have hp : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast (Fact.out : p.Prime).pos)
      exact absurd this.symm (inv_pos.mpr hp).ne'
    have h3 : (2 : ℂ) * (γT : ℂ) * gaussEig (1 : ZMod p) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp h3 with h4 | h4
    · rcases mul_eq_zero.mp h4 with h5 | h5
      · norm_num at h5
      · exact_mod_cast h5
    · exact absurd h4 hne
  · intro h0 f g _ _
    rw [hlin, hlin', h0]
    simp

end Sarkozy.SpectralC
