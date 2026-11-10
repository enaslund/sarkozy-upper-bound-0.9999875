module

public import Sarkozy.DLK.Normalized
public import Sarkozy.SecondOrder.RawPairMaps

/-!
# The remainder of the raw pair maps (`cor:raw-pair-maps`(b)), from `thm:dl:K`

`paper/sections/15_second_order.tex`, `cor:raw-pair-maps`(b), in the conventions of
`SecondOrder/RawPairMaps.lean`: `q = 1/p`, `r = p^{-1/2}`, `ψ_y(s) = χ(s - y₀)χ(s - y₁)`, `y`
uniform on the ordered pairs of distinct labels, `L²(𝔽_p²)` with uniform probability,
`(SF)(y) = E_{s,u} ψ_y(s)ψ_y(u) F(s, u)`, `d = √p 1_{s=u}` and `R = S - r(1 - 2q) 1⟨d, ·⟩`, whose
row at `y` is `(s, u) ↦ ψ_y(s)ψ_y(u) - r(1 - 2q) d(s, u)`. WP's `RawPairMaps.lean` proves the
diagonal pieces (`S_diag`, `RD_norm`, `R_row_norm`) and leaves the off-diagonal piece, which needs
`cor:dl:normalized`, unformalized. Here:

* `affine_opBound`: the affine four-cycle kernel `K(y, (s, u)) = ψ_y(s)ψ_y(u)` has `ℓ²` norm at most
  `2p` on the pairs of distinct elements (`cor:dl:normalized`(a), all signs `+1`).
* `raw_pair_offdiag`: **on the functions vanishing on the diagonal, `R = S` has norm at most
  `2q/√(1 - q)`**: `E_y (SF)(y)² ≤ (4q²/(1 - q)) ‖F‖²`.
* `raw_pair_remainder`: **`‖R‖² ≤ c₀ q²`, `c₀ = 4/(1 - q) + 2q`** (`eq:raw-pair-split`), for every
  `F ∈ L²(𝔽_p²)`: the split `F = λd + Df + F'` of the paper, `RF = RDf + SF'`, `RD_norm` and
  `raw_pair_offdiag`, and the weighted Cauchy–Schwarz inequality
  `(a + b)² ≤ (1 + t)a² + (1 + 1/t)b²` with `t = 2/(q(1 - q))`.

With `S_diag` (`Sd = r(1 - 2q)`, so `Rd = 0`) and `R_row_norm` (rows of norm at most one) this
completes `cor:raw-pair-maps`(b); the tensor-product remark of (a) is not formalized.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.DLK

open Sarkozy Sarkozy.Influence Sarkozy.Extraction Sarkozy.SecondOrder

variable {p : ℕ} [Fact p.Prime]

theorem chiRe_eq_chiR (a : ZMod p) : chiRe a = chiR a := rfl

/-- **The affine four-cycle operator bound** (`cor:dl:normalized`(a), `a = b = 2`, all signs `+1`),
from `thm:dl:K`: the kernel `K(x, z) = χ((z₁ - x₁)(z₁ - x₂)(z₂ - x₁)(z₂ - x₂))` on the ordered pairs
of distinct elements has `ℓ²` operator norm at most `2p`. -/
theorem affine_opBound (hDLK : Target.FourCycle) (hp2 : p ≠ 2) :
    OpBound (twoCycleOffDiag p) (twoCycleOffDiag p) affineKernel (2 * (p : ℝ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  exact opBound_of_quadForm _ _ (fun x _ z _ => affineKernel_symm x z) (by positivity)
    (fourCycleAffine_of_fourCycle hDLK hp2)

/-- `ψ_y(s) ψ_y(u) = K(y, (s, u))`: the kernel of `S` is the affine four-cycle kernel, with the pair
`y` in the role of `x`. -/
theorem psi_psi_eq (y : ZMod p × ZMod p) (s u : ZMod p) :
    chiRe (s - y.1) * chiRe (s - y.2) * (chiRe (u - y.1) * chiRe (u - y.2)) =
      affineKernel y (s, u) := by
  unfold affineKernel
  simp only [chiRe_eq_chiR, chiR_mul]

/-- **`cor:raw-pair-maps`(b), the off-diagonal piece**, from `thm:dl:K`: for `F` vanishing on the
diagonal `{s = u}` and `y` uniform on the ordered pairs of distinct labels,
`E_y (SF)(y)² ≤ (4q²/(1 - q)) E_{s,u} F(s, u)²`, i.e. `‖R F‖ = ‖S F‖ ≤ (2q/√(1 - q)) ‖F‖`. -/
theorem raw_pair_offdiag (hDLK : Target.FourCycle) (hp2 : p ≠ 2) (F : ZMod p → ZMod p → ℝ)
    (hF : ∀ s, F s s = 0) :
    (1 / ((p : ℝ) * (p - 1))) * ∑ y ∈ univ.filter (fun y : ZMod p × ZMod p => y.1 ≠ y.2),
        ((1 / (p : ℝ) ^ 2) * ∑ s, ∑ u, chiRe (s - y.1) * chiRe (s - y.2) *
          (chiRe (u - y.1) * chiRe (u - y.2)) * F s u) ^ 2 ≤
      4 * (1 / (p : ℝ)) ^ 2 / (1 - 1 / (p : ℝ)) * ((1 / (p : ℝ) ^ 2) * ∑ s, ∑ u, F s u ^ 2) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hGd : ∀ z : ZMod p × ZMod p, z.1 = z.2 → F z.1 z.2 = 0 := by
    rintro ⟨s, u⟩ h
    simp only at h
    rw [h, hF]
  have hop := affine_opBound hDLK hp2 (fun z => F z.1 z.2)
  have e1 : ∀ y : ZMod p × ZMod p, ∑ s, ∑ u, chiRe (s - y.1) * chiRe (s - y.2) *
      (chiRe (u - y.1) * chiRe (u - y.2)) * F s u =
      ∑ z ∈ twoCycleOffDiag p, affineKernel y z * F z.1 z.2 := by
    intro y
    rw [sum_offDiag_eq _ fun z hz => by rw [hGd z hz, mul_zero], Fintype.sum_prod_type]
    exact sum_congr rfl fun s _ => sum_congr rfl fun u _ => by rw [psi_psi_eq]
  have e2 : ∑ z ∈ twoCycleOffDiag p, F z.1 z.2 ^ 2 = ∑ s, ∑ u, F s u ^ 2 := by
    rw [sum_offDiag_eq _ fun z hz => by rw [hGd z hz]; ring, Fintype.sum_prod_type]
  have hfilt : univ.filter (fun y : ZMod p × ZMod p => y.1 ≠ y.2) = twoCycleOffDiag p := rfl
  rw [hfilt]
  simp_rw [e1]
  rw [e2] at hop
  have e3 : ∑ y ∈ twoCycleOffDiag p,
      ((1 / (p : ℝ) ^ 2) * ∑ z ∈ twoCycleOffDiag p, affineKernel y z * F z.1 z.2) ^ 2 =
      (1 / (p : ℝ) ^ 2) ^ 2 *
        ∑ y ∈ twoCycleOffDiag p, (∑ z ∈ twoCycleOffDiag p, affineKernel y z * F z.1 z.2) ^ 2 := by
    rw [mul_sum]
    exact sum_congr rfl fun y _ => by ring
  rw [e3]
  have hS : 0 ≤ ∑ s, ∑ u, F s u ^ 2 := sum_nonneg fun s _ => sum_nonneg fun u _ => sq_nonneg _
  have hpp : (0 : ℝ) < (p : ℝ) * (p - 1) := by nlinarith
  calc 1 / ((p : ℝ) * (p - 1)) * ((1 / (p : ℝ) ^ 2) ^ 2 *
        ∑ y ∈ twoCycleOffDiag p, (∑ z ∈ twoCycleOffDiag p, affineKernel y z * F z.1 z.2) ^ 2)
      ≤ 1 / ((p : ℝ) * (p - 1)) * ((1 / (p : ℝ) ^ 2) ^ 2 *
          ((2 * (p : ℝ)) ^ 2 * ∑ s, ∑ u, F s u ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hop (by positivity)
    _ = 4 * (1 / (p : ℝ)) ^ 2 / (1 - 1 / (p : ℝ)) * ((1 / (p : ℝ) ^ 2) * ∑ s, ∑ u, F s u ^ 2) := by
        have hne : (p : ℝ) - 1 ≠ 0 := by linarith
        field_simp
        ring

/-- The pointwise split `RF = RDf + SF'` (`cor:raw-pair-maps`(b)): for `y₀ ≠ y₁`, with
`g(s) = F(s, s)`, `g₀ = g - E g` and `F'` the off-diagonal part of `F`,
`(RF)(y) = -p⁻²(g₀(y₀) + g₀(y₁)) + E_{s,u} ψ_y(s)ψ_y(u) F'(s, u)`. -/
theorem raw_pair_split {y : ZMod p × ZMod p} (hy : y.1 ≠ y.2) (F : ZMod p → ZMod p → ℝ) :
    (1 / (p : ℝ) ^ 2) * ∑ s, ∑ u, (chiRe (s - y.1) * chiRe (s - y.2) *
        (chiRe (u - y.1) * chiRe (u - y.2)) -
        (1 / Real.sqrt p) * (1 - 2 / (p : ℝ)) * (Real.sqrt p * (if s = u then 1 else 0))) * F s u =
      -((1 / (p : ℝ) ^ 2) * ((F y.1 y.1 - (1 / (p : ℝ)) * ∑ t, F t t) +
          (F y.2 y.2 - (1 / (p : ℝ)) * ∑ t, F t t))) +
        (1 / (p : ℝ) ^ 2) * ∑ s, ∑ u, chiRe (s - y.1) * chiRe (s - y.2) *
          (chiRe (u - y.1) * chiRe (u - y.2)) * (if s = u then 0 else F s u) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hs0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hc : (1 / Real.sqrt p) * (1 - 2 / (p : ℝ)) * Real.sqrt p = 1 - 2 / (p : ℝ) := by
    field_simp
  have e1 : ∀ s u, (chiRe (s - y.1) * chiRe (s - y.2) * (chiRe (u - y.1) * chiRe (u - y.2)) -
      (1 / Real.sqrt p) * (1 - 2 / (p : ℝ)) * (Real.sqrt p * (if s = u then 1 else 0))) * F s u =
      chiRe (s - y.1) * chiRe (s - y.2) * (chiRe (u - y.1) * chiRe (u - y.2)) *
        (if s = u then 0 else F s u) +
      (if s = u then (chiRe (s - y.1) * chiRe (s - y.2)) ^ 2 * F s s -
        (1 - 2 / (p : ℝ)) * F s s else 0) := by
    intro s u
    by_cases h : s = u
    · subst h
      simp only [↓reduceIte, mul_one, mul_zero, zero_add]
      rw [← mul_assoc, hc]
      ring
    · simp only [h, ↓reduceIte, mul_zero, sub_zero, add_zero]
  simp_rw [e1, sum_add_distrib]
  simp only [sum_ite_eq, mem_univ, ↓reduceIte]
  rw [sum_sub_distrib, sum_psi_sq_mul hy (fun s => F s s), ← mul_sum]
  field_simp
  ring

/-- The norm split: `E g₀² + ‖F'‖² ≤ ‖F‖²` for `g₀ = g - E g`, `g(s) = F(s, s)`, `F'` the
off-diagonal part (counting form). -/
theorem raw_pair_norm_split (F : ZMod p → ZMod p → ℝ) :
    ∑ s, (F s s - (1 / (p : ℝ)) * ∑ t, F t t) ^ 2 +
        ∑ s, ∑ u, (if s = u then 0 else F s u) ^ 2 ≤ ∑ s, ∑ u, F s u ^ 2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hsplit : ∑ s, ∑ u, F s u ^ 2 = ∑ s, F s s ^ 2 + ∑ s, ∑ u, (if s = u then 0 else F s u) ^ 2 := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun s _ => ?_
    have e : ∀ u, F s u ^ 2 = (if s = u then F s s ^ 2 else 0) + (if s = u then 0 else F s u) ^ 2 := by
      intro u
      by_cases h : s = u
      · subst h; simp
      · simp [h]
    rw [sum_congr rfl fun u _ => e u, sum_add_distrib, sum_ite_eq]
    simp
  have hvar : ∑ s, (F s s - (1 / (p : ℝ)) * ∑ t, F t t) ^ 2 =
      ∑ s, F s s ^ 2 - (1 / (p : ℝ)) * (∑ t, F t t) ^ 2 := by
    have e : ∀ s, (F s s - (1 / (p : ℝ)) * ∑ t, F t t) ^ 2 =
        F s s ^ 2 - 2 * (1 / (p : ℝ)) * (∑ t, F t t) * F s s +
          (1 / (p : ℝ)) ^ 2 * (∑ t, F t t) ^ 2 := fun s => by ring
    rw [sum_congr rfl fun s _ => e s, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const,
      card_univ, ZMod.card, nsmul_eq_mul]
    field_simp
    ring
  rw [hsplit, hvar]
  have : 0 ≤ (1 / (p : ℝ)) * (∑ t, F t t) ^ 2 := by positivity
  linarith

/-- **`cor:raw-pair-maps`(b): `‖R‖² ≤ c₀ q²`, `c₀ = 4/(1 - q) + 2q`** (`eq:raw-pair-split`), from
`thm:dl:K`: for every `F ∈ L²(𝔽_p²)` and `y` uniform on the ordered pairs of distinct labels,
`E_y (RF)(y)² ≤ (4/(1 - q) + 2q) q² ‖F‖²`, where `(RF)(y) = E_{s,u} (ψ_y(s)ψ_y(u) - r(1 - 2q)
d(s, u)) F(s, u)` and `d = √p 1_{s=u}`. -/
theorem raw_pair_remainder (hDLK : Target.FourCycle) (hp2 : p ≠ 2) (F : ZMod p → ZMod p → ℝ) :
    (1 / ((p : ℝ) * (p - 1))) * ∑ y ∈ univ.filter (fun y : ZMod p × ZMod p => y.1 ≠ y.2),
        ((1 / (p : ℝ) ^ 2) * ∑ s, ∑ u, (chiRe (s - y.1) * chiRe (s - y.2) *
          (chiRe (u - y.1) * chiRe (u - y.2)) -
          (1 / Real.sqrt p) * (1 - 2 / (p : ℝ)) * (Real.sqrt p * (if s = u then 1 else 0))) *
            F s u) ^ 2 ≤
      (4 / (1 - 1 / (p : ℝ)) + 2 * (1 / (p : ℝ))) * (1 / (p : ℝ)) ^ 2 *
        ((1 / (p : ℝ) ^ 2) * ∑ s, ∑ u, F s u ^ 2) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hs0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hpp : (0 : ℝ) < (p : ℝ) * (p - 1) := by nlinarith
  set m : ℝ := (1 / (p : ℝ)) * ∑ t, F t t with hm
  set g₀ : ZMod p → ℝ := fun s => F s s - m with hg₀
  set F' : ZMod p → ZMod p → ℝ := fun s u => if s = u then 0 else F s u with hF'
  set A : ZMod p × ZMod p → ℝ := fun y => -((1 / (p : ℝ) ^ 2) * (g₀ y.1 + g₀ y.2)) with hA
  set B : ZMod p × ZMod p → ℝ := fun y => (1 / (p : ℝ) ^ 2) * ∑ s, ∑ u,
    chiRe (s - y.1) * chiRe (s - y.2) * (chiRe (u - y.1) * chiRe (u - y.2)) * F' s u with hB
  set Y := univ.filter (fun y : ZMod p × ZMod p => y.1 ≠ y.2) with hY
  -- the pointwise split
  have hsplit : ∀ y ∈ Y, (1 / (p : ℝ) ^ 2) * ∑ s, ∑ u, (chiRe (s - y.1) * chiRe (s - y.2) *
      (chiRe (u - y.1) * chiRe (u - y.2)) -
      (1 / Real.sqrt p) * (1 - 2 / (p : ℝ)) * (Real.sqrt p * (if s = u then 1 else 0))) * F s u =
      A y + B y := fun y hy => raw_pair_split (mem_filter.mp hy).2 F
  rw [sum_congr rfl fun y hy => by rw [hsplit y hy]]
  -- the weighted Cauchy–Schwarz inequality
  set t : ℝ := 2 * (p : ℝ) ^ 2 / ((p : ℝ) - 1) with ht
  have ht0 : 0 < t := by
    have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  have hcs : ∀ a b : ℝ, (a + b) ^ 2 ≤ (1 + t) * a ^ 2 + (1 + 1 / t) * b ^ 2 := by
    intro a b
    have e : (1 + t) * a ^ 2 + (1 + 1 / t) * b ^ 2 - (a + b) ^ 2 = (t * a - b) ^ 2 / t := by
      field_simp
      ring
    have : 0 ≤ (t * a - b) ^ 2 / t := div_nonneg (sq_nonneg _) ht0.le
    linarith
  -- the bound for `A` (`RD_norm`, with `f = g₀/√p`)
  have hg₀sum : ∑ s, g₀ s / Real.sqrt p = 0 := by
    rw [← sum_div]
    simp only [hg₀, sum_sub_distrib, sum_const, card_univ, ZMod.card, nsmul_eq_mul, hm]
    field_simp
    ring
  have hRD := RD_norm (p := p) (f := fun s => g₀ s / Real.sqrt p) hg₀sum
  have eA : ∀ y : ZMod p × ZMod p, ((1 / (p : ℝ)) * (1 / Real.sqrt p) *
      (g₀ y.1 / Real.sqrt p + g₀ y.2 / Real.sqrt p)) ^ 2 = A y ^ 2 := by
    intro y
    simp only [hA]
    have h4 : Real.sqrt p ^ 4 = (p : ℝ) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hp0.le]
    field_simp
    rw [h4]
  have eA2 : (1 / (p : ℝ)) * ∑ s, (g₀ s / Real.sqrt p) ^ 2 = (1 / (p : ℝ) ^ 2) * ∑ s, g₀ s ^ 2 := by
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun s _ => ?_
    rw [div_pow, Real.sq_sqrt hp0.le]
    field_simp
  simp only [eA] at hRD
  rw [eA2] at hRD
  -- the bound for `B` (`raw_pair_offdiag`)
  have hBb := raw_pair_offdiag hDLK hp2 F' (fun s => by simp [hF'])
  -- combine
  have hsum : ∑ y ∈ Y, (A y + B y) ^ 2 ≤ (1 + t) * ∑ y ∈ Y, A y ^ 2 + (1 + 1 / t) * ∑ y ∈ Y, B y ^ 2 := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_le_sum fun y _ => hcs (A y) (B y)
  have hnorm := raw_pair_norm_split (p := p) F
  have hN0 : 0 ≤ ∑ s, g₀ s ^ 2 := sum_nonneg fun s _ => sq_nonneg _
  have hN1 : 0 ≤ ∑ s, ∑ u, F' s u ^ 2 := sum_nonneg fun s _ => sum_nonneg fun u _ => sq_nonneg _
  have hc1 : (1 + t) * (2 * (1 / (p : ℝ)) ^ 3) =
      (4 / (1 - 1 / (p : ℝ)) + 2 * (1 / (p : ℝ))) * (1 / (p : ℝ)) ^ 2 := by
    have hne : (p : ℝ) - 1 ≠ 0 := by linarith
    simp only [ht]
    field_simp
    ring
  have hc2 : (1 + 1 / t) * (4 * (1 / (p : ℝ)) ^ 2 / (1 - 1 / (p : ℝ))) =
      (4 / (1 - 1 / (p : ℝ)) + 2 * (1 / (p : ℝ))) * (1 / (p : ℝ)) ^ 2 := by
    have hne : (p : ℝ) - 1 ≠ 0 := by linarith
    simp only [ht]
    field_simp
    ring
  set c : ℝ := (4 / (1 - 1 / (p : ℝ)) + 2 * (1 / (p : ℝ))) * (1 / (p : ℝ)) ^ 2 with hc
  have hc0 : 0 ≤ c := by
    have : (0 : ℝ) < 1 - 1 / (p : ℝ) := by
      rw [sub_pos, div_lt_one hp0]; exact hp1
    positivity
  have hnorm' : ∑ s, g₀ s ^ 2 + ∑ s, ∑ u, F' s u ^ 2 ≤ ∑ s, ∑ u, F s u ^ 2 := hnorm
  calc 1 / ((p : ℝ) * (p - 1)) * ∑ y ∈ Y, (A y + B y) ^ 2
      ≤ 1 / ((p : ℝ) * (p - 1)) * ((1 + t) * ∑ y ∈ Y, A y ^ 2 + (1 + 1 / t) * ∑ y ∈ Y, B y ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (1 + t) * (1 / ((p : ℝ) * (p - 1)) * ∑ y ∈ Y, A y ^ 2) +
          (1 + 1 / t) * (1 / ((p : ℝ) * (p - 1)) * ∑ y ∈ Y, B y ^ 2) := by ring
    _ ≤ (1 + t) * (2 * (1 / (p : ℝ)) ^ 3 * ((1 / (p : ℝ) ^ 2) * ∑ s, g₀ s ^ 2)) +
          (1 + 1 / t) * (4 * (1 / (p : ℝ)) ^ 2 / (1 - 1 / (p : ℝ)) *
            ((1 / (p : ℝ) ^ 2) * ∑ s, ∑ u, F' s u ^ 2)) := by
        have h1t : 0 ≤ 1 + t := by linarith
        have h1t' : 0 ≤ 1 + 1 / t := by positivity
        exact add_le_add (mul_le_mul_of_nonneg_left hRD h1t) (mul_le_mul_of_nonneg_left hBb h1t')
    _ = c * ((1 / (p : ℝ) ^ 2) * (∑ s, g₀ s ^ 2 + ∑ s, ∑ u, F' s u ^ 2)) := by
        rw [show (1 + t) * (2 * (1 / (p : ℝ)) ^ 3 * ((1 / (p : ℝ) ^ 2) * ∑ s, g₀ s ^ 2)) =
            c * ((1 / (p : ℝ) ^ 2) * ∑ s, g₀ s ^ 2) by rw [← mul_assoc, hc1],
          show (1 + 1 / t) * (4 * (1 / (p : ℝ)) ^ 2 / (1 - 1 / (p : ℝ)) *
            ((1 / (p : ℝ) ^ 2) * ∑ s, ∑ u, F' s u ^ 2)) =
            c * ((1 / (p : ℝ) ^ 2) * ∑ s, ∑ u, F' s u ^ 2) by rw [← mul_assoc, hc2]]
        ring
    _ ≤ c * ((1 / (p : ℝ) ^ 2) * ∑ s, ∑ u, F s u ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hc0
        exact mul_le_mul_of_nonneg_left hnorm' (by positivity)

end Sarkozy.DLK
