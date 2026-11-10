module

public import Sarkozy.Labellings.Extension
public import Sarkozy.Target
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# `lem:push:localvariance` (b)(ii): the two-variable bounds

`paper/sections/14_spectral.tex`, proof of `lem:push:localvariance` (b), paragraph
*Two-variable bounds*: the step where `thm:dl:H2` enters. It enters verbatim, as the hypothesis
`Sarkozy.Target.TwoVariable` (H4); nothing else is assumed (the two-root identity `eq:two-root`
is `Sarkozy.Labellings.two_root`, unconditional).

* `pairSum A B = ∑_{y,y'} χ(f_A(y) f_B(y') (y' - y))`, `f_A = ∏_{a ∈ A}(X - a)`.
* `pairSum_empty_left`, `pairSum_empty_right`: it vanishes if `A = ∅` or `B = ∅` (the sum over
  the variable of degree zero is a complete character sum); `pairSum_singleton`: for
  `A = {α}`, `B = {β}` it equals `p χ(β - α)` (two-root identity).
* `abs_pairSum_le`: `|pairSum A B| ≤ p 𝐜(|A|, |B|)`, where `twoVarCoeff p a b` is the paper's
  vector `𝐜(a, b)` evaluated at `(1, r, r²)`: `0` if `ab = 0`, `1` if `a = b = 1`, `𝓑(a, b, 0)`
  if `a ≥ 2` and `𝓑(b, a, 0)` if `a < 2 ≤ b` (`eq:dl:B` is `Target.twoVarBound`). From
  `Target.TwoVariable` and `𝓑(·, ·, s) ≤ 𝓑(·, ·, 0)` (`twoVarBound_le_zero`).
* `two_variable_bound`: the bound of (ii) for an edge `uv`, before the excluded values are
  restored. With optional centres `O_u`, `O_v` (signs `s_β`, `t_γ` of modulus at most one),
  forced centres `F_u`, `F_v`, and the centres at each vertex distinct (`O_u ∩ F_u = ∅`,
  `O_v ∩ F_v = ∅`), the sum over `(y_u, y_v) ∈ 𝔽_p²` of
  `∏_{β ∈ O_u}(1 + s_β χ(y_u - β)) ∏_{γ ∈ O_v}(1 + t_γ χ(y_v - γ)) χ(f_{F_u}(y_u)) χ(f_{F_v}(y_v))
  χ(y_v - y_u)` has modulus at most
  `p ∑_{i ≤ d_u, j ≤ d_v} binom(d_u, i) binom(d_v, j) 𝐜(i + f_u, j + f_v)`;
  `two_variable_bound_avg` divides by `p²`: the average is at most `r²(C₀ + r C₁ + r² C₂)`.
  (The orientation of the edge `uv` and the signs of the forced characters only multiply the
  sum by a sign, which does not change the bound.)

* `soft_product_bounds`, `soft_product_sum_le`: `0 ≤ ρ̃ ≤ 2^{d}`, `ρ̃ = 2^{d} 1_{constraints}` off
  the roots, and `E ρ̃ ≤ 2^{d}|Φ|/p + d 2^{d}/p`.
* `two_variable_restricted`: the two combined, the bound (ii) for the edge `uv` on the
  restricted domain, `r²(C₀ + rC₁ + r²C₂) + 2n r²(2^{d_u} s_v + 2^{d_v} s_u)` after dividing by
  `p²` (the factor `∏_{i ∈ S ∖ {u,v}} α⁺⁺_i` from the frozen labels is not included).
* `restoration_bound`: restoring the excluded values changes the average by at most
  `(m/p)(A_max s_b + B_max s_a)`, i.e. `2n r²(2^{d_u} s_v + 2^{d_v} s_u)`.

Not formalized here: the matching bounds (i) (which use `lem:matching:kernel`) and the
conditioning that reduces `C_k` to these averages; the coincidence and linear parts are in
`Sarkozy.Spectral.Coincidence` and `Sarkozy.Spectral.LocalVariance`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.Spectral

variable {p : ℕ} [Fact p.Prime]

theorem ringChar_zmod_ne_two (hp2 : p ≠ 2) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  exact hp2

/-- `∑_{y,y'} χ(f_A(y) f_B(y') (y' - y))` with `f_A = ∏_{a ∈ A}(X - a)`. -/
def pairSum (A B : Finset (ZMod p)) : ℤ :=
  ∑ y, ∑ z, quadraticChar (ZMod p) ((∏ a ∈ A, (y - a)) * (∏ b ∈ B, (z - b)) * (z - y))

/-- The coefficient `𝐜(a, b)` of `lem:push:localvariance` (b)(ii), evaluated at `(1, r, r²)`. -/
noncomputable def twoVarCoeff (p a b : ℕ) : ℝ :=
  if a = 0 ∨ b = 0 then 0 else if a = 1 ∧ b = 1 then 1
  else if 2 ≤ a then Target.twoVarBound p a b 0 else Target.twoVarBound p b a 0

omit [Fact p.Prime] in
/-- `𝓑(m, n, s) ≤ 𝓑(m, n, 0)`. -/
theorem twoVarBound_le_zero (p m n s : ℕ) :
    Target.twoVarBound p m n s ≤ Target.twoVarBound p m n 0 := by
  simp only [Target.twoVarBound, Nat.cast_zero, sub_zero]
  have h1 : (0 : ℝ) ≤ (Target.gam m : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg h1 h2]

/-- `|χ(a)| ≤ 1`. -/
theorem abs_quadraticChar_le_one (a : ZMod p) :
    |((quadraticChar (ZMod p) a : ℤ) : ℝ)| ≤ 1 := by
  rcases quadraticChar_isQuadratic (ZMod p) a with h | h | h <;> simp [h]

theorem sum_char_sub_left (hp2 : p ≠ 2) (z : ZMod p) :
    ∑ y, quadraticChar (ZMod p) (z - y) = 0 := by
  rw [← quadraticChar_sum_zero (ringChar_zmod_ne_two hp2)]
  exact Fintype.sum_equiv (Equiv.subLeft z) _ _ (fun _ => rfl)

theorem sum_char_sub_right (hp2 : p ≠ 2) (y : ZMod p) :
    ∑ z, quadraticChar (ZMod p) (z - y) = 0 := by
  rw [← quadraticChar_sum_zero (ringChar_zmod_ne_two hp2)]
  exact Fintype.sum_equiv (Equiv.subRight y) _ _ (fun _ => rfl)

theorem pairSum_empty_left (hp2 : p ≠ 2) (B : Finset (ZMod p)) : pairSum ∅ B = 0 := by
  unfold pairSum
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun z _ => ?_
  simp only [Finset.prod_empty, one_mul, map_mul]
  rw [← Finset.mul_sum, sum_char_sub_left hp2, mul_zero]

theorem pairSum_empty_right (hp2 : p ≠ 2) (A : Finset (ZMod p)) : pairSum A ∅ = 0 := by
  unfold pairSum
  refine Finset.sum_eq_zero fun y _ => ?_
  simp only [Finset.prod_empty, mul_one, map_mul]
  rw [← Finset.mul_sum, sum_char_sub_right hp2, mul_zero]

/-- **The case `deg f = deg g = 1`** (two-root identity `eq:two-root`):
`∑_{y,y'} χ((y - α)(y' - β)(y' - y)) = p χ(β - α)`. -/
theorem pairSum_singleton (hp2 : p ≠ 2) (α β : ZMod p) :
    pairSum {α} {β} = p * quadraticChar (ZMod p) (β - α) := by
  have hF := ringChar_zmod_ne_two hp2
  -- the inner sum `∑_{y'} χ((y' - β)(y' - y)) = p [y = β] - 1`
  have hW : ∀ y : ZMod p, ∑ z, quadraticChar (ZMod p) ((z - β) * (z - y)) =
      (if y = β then (p : ℤ) else 0) - 1 := by
    intro y
    by_cases hy : y = β
    · subst hy
      have h1 : ∀ z : ZMod p, quadraticChar (ZMod p) ((z - y) * (z - y)) =
          1 - if z = y then 1 else 0 := by
        intro z
        by_cases hz : z = y
        · simp [hz]
        · rw [← sq, quadraticChar_sq_one' (sub_ne_zero.mpr hz)]
          simp [hz]
      rw [Finset.sum_congr rfl fun z _ => h1 z, Finset.sum_sub_distrib, Finset.sum_ite_eq']
      simp [ZMod.card]
    · have hne : β ≠ y := Ne.symm hy
      have h2 := Labellings.two_root hF hne
      simp only [Labellings.rootSum, Finset.prod_pair hne] at h2
      rw [h2]
      simp [hy]
  unfold pairSum
  simp only [Finset.prod_singleton]
  have e : ∀ y : ZMod p, ∑ z, quadraticChar (ZMod p) ((y - α) * (z - β) * (z - y)) =
      quadraticChar (ZMod p) (y - α) * ((if y = β then (p : ℤ) else 0) - 1) := by
    intro y
    rw [← hW y, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [mul_assoc, map_mul]
  rw [Finset.sum_congr rfl fun y _ => e y]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rw [sum_char_sub_right hp2 α]
  ring

/-- **The pair sums from `thm:dl:H2`**: `|pairSum A B| ≤ p 𝐜(|A|, |B|)`. -/
theorem abs_pairSum_le (hTV : Target.TwoVariable) (hp2 : p ≠ 2) (A B : Finset (ZMod p)) :
    |(pairSum A B : ℝ)| ≤ p * twoVarCoeff p A.card B.card := by
  unfold twoVarCoeff
  by_cases h0 : A.card = 0 ∨ B.card = 0
  · rw [ite_eq_left h0]
    rcases h0 with h | h
    · rw [Finset.card_eq_zero.mp h, pairSum_empty_left hp2]
      simp
    · rw [Finset.card_eq_zero.mp h, pairSum_empty_right hp2]
      simp
  rw [ite_eq_right h0]
  push Not at h0
  by_cases h11 : A.card = 1 ∧ B.card = 1
  · rw [ite_eq_left h11]
    obtain ⟨α, hα⟩ := Finset.card_eq_one.mp h11.1
    obtain ⟨β, hβ⟩ := Finset.card_eq_one.mp h11.2
    rw [hα, hβ, pairSum_singleton hp2, Int.cast_mul, Int.cast_natCast, abs_mul, Nat.abs_cast,
      mul_one]
    have := abs_quadraticChar_le_one (β - α)
    nlinarith [this, (Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
  rw [ite_eq_right h11]
  by_cases h2 : 2 ≤ A.card
  · rw [ite_eq_left h2]
    have hc : (-1 : ZMod p) ≠ 0 := neg_ne_zero.mpr one_ne_zero
    have h := hTV p hp2 A B (-1) 1 hc one_ne_zero h2 (Nat.one_le_iff_ne_zero.mpr h0.2)
    dsimp only at h
    have e : pairSum A B = ∑ y, ∑ z, quadraticChar (ZMod p)
        ((-1 * ∏ x ∈ A, (y - x)) * (1 * ∏ x ∈ B, (z - x)) * (y - z)) := by
      unfold pairSum
      refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
      congr 1
      ring
    rw [e]
    exact h.1.trans (mul_le_mul_of_nonneg_left (twoVarBound_le_zero _ _ _ _) (Nat.cast_nonneg _))
  · rw [ite_eq_right h2]
    have hA1 : A.card = 1 := by omega
    have hB2 : 2 ≤ B.card := by
      by_contra hB
      exact h11 ⟨hA1, by omega⟩
    have h := hTV p hp2 B A 1 1 one_ne_zero one_ne_zero hB2 (by omega)
    dsimp only at h
    have e : pairSum A B = ∑ y, ∑ z, quadraticChar (ZMod p)
        ((1 * ∏ x ∈ B, (y - x)) * (1 * ∏ x ∈ A, (z - x)) * (y - z)) := by
      unfold pairSum
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
      congr 1
      ring
    rw [e]
    exact h.1.trans (mul_le_mul_of_nonneg_left (twoVarBound_le_zero _ _ _ _) (Nat.cast_nonneg _))

omit [Fact p.Prime] in
/-- Grouping a double sum over subsets by cardinalities. -/
theorem sum_powerset_powerset_card (Ou Ov : Finset (ZMod p)) (c : ℕ → ℕ → ℝ) :
    ∑ I ∈ Ou.powerset, ∑ J ∈ Ov.powerset, c I.card J.card =
      ∑ i ∈ range (Ou.card + 1), ∑ j ∈ range (Ov.card + 1),
        (Ou.card.choose i : ℝ) * (Ov.card.choose j : ℝ) * c i j := by
  have h1 : ∀ m : ℕ, ∑ J ∈ Ov.powerset, c m J.card =
      ∑ j ∈ range (Ov.card + 1), (Ov.card.choose j : ℝ) * c m j :=
    fun m => (Finset.sum_powerset_apply_card (fun k => c m k)).trans
      (Finset.sum_congr rfl fun j _ => nsmul_eq_mul _ _)
  rw [Finset.sum_congr rfl fun I _ => h1 I.card]
  rw [(Finset.sum_powerset_apply_card
    (fun k => ∑ j ∈ range (Ov.card + 1), (Ov.card.choose j : ℝ) * c k j)).trans
      (Finset.sum_congr rfl fun i _ => nsmul_eq_mul _ _)]
  simp only [Finset.mul_sum, mul_assoc]

/-- **`lem:push:localvariance` (b)(ii), the character-sum bound for an edge `uv`.** The optional
centres `O_u`, `O_v` carry signs `s_β`, `t_γ` with `|s_β|, |t_γ| ≤ 1`; the forced centres
`F_u`, `F_v` are disjoint from them. Expanding the optional factors, every term is a pair sum
bounded by `abs_pairSum_le` (that is, by `Target.TwoVariable`, the two-root identity, or zero). -/
theorem two_variable_bound (hTV : Target.TwoVariable) (hp2 : p ≠ 2)
    (Ou Ov Fu Fv : Finset (ZMod p)) (hu : Disjoint Ou Fu) (hv : Disjoint Ov Fv)
    (su sv : ZMod p → ℤ) (hsu : ∀ β, |su β| ≤ 1) (hsv : ∀ γ, |sv γ| ≤ 1) :
    |((∑ y, ∑ z, (∏ β ∈ Ou, (1 + su β * quadraticChar (ZMod p) (y - β))) *
        (∏ γ ∈ Ov, (1 + sv γ * quadraticChar (ZMod p) (z - γ))) *
        quadraticChar (ZMod p) (∏ β ∈ Fu, (y - β)) *
        quadraticChar (ZMod p) (∏ γ ∈ Fv, (z - γ)) * quadraticChar (ZMod p) (z - y) : ℤ) : ℝ)| ≤
      p * ∑ i ∈ range (Ou.card + 1), ∑ j ∈ range (Ov.card + 1),
        (Ou.card.choose i : ℝ) * (Ov.card.choose j : ℝ) *
          twoVarCoeff p (i + Fu.card) (j + Fv.card) := by
  -- the expansion of the optional factors
  have hexp : ∀ y z : ZMod p, (∏ β ∈ Ou, (1 + su β * quadraticChar (ZMod p) (y - β))) *
      (∏ γ ∈ Ov, (1 + sv γ * quadraticChar (ZMod p) (z - γ))) *
      quadraticChar (ZMod p) (∏ β ∈ Fu, (y - β)) *
      quadraticChar (ZMod p) (∏ γ ∈ Fv, (z - γ)) * quadraticChar (ZMod p) (z - y) =
      ∑ I ∈ Ou.powerset, ∑ J ∈ Ov.powerset, (∏ β ∈ I, su β) * (∏ γ ∈ J, sv γ) *
        quadraticChar (ZMod p) ((∏ β ∈ I ∪ Fu, (y - β)) * (∏ γ ∈ J ∪ Fv, (z - γ)) * (z - y)) := by
    intro y z
    rw [Finset.prod_one_add, Finset.prod_one_add, Finset.sum_mul_sum]
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun I hI => Finset.sum_congr rfl fun J hJ => ?_
    have hI' : Disjoint I Fu := Finset.disjoint_of_subset_left (Finset.mem_powerset.mp hI) hu
    have hJ' : Disjoint J Fv := Finset.disjoint_of_subset_left (Finset.mem_powerset.mp hJ) hv
    rw [Finset.prod_union hI', Finset.prod_union hJ']
    simp only [map_mul, map_prod, Finset.prod_mul_distrib]
    ring
  -- summing over `(y_u, y_v)`
  have hsum : ∑ y, ∑ z, (∏ β ∈ Ou, (1 + su β * quadraticChar (ZMod p) (y - β))) *
      (∏ γ ∈ Ov, (1 + sv γ * quadraticChar (ZMod p) (z - γ))) *
      quadraticChar (ZMod p) (∏ β ∈ Fu, (y - β)) *
      quadraticChar (ZMod p) (∏ γ ∈ Fv, (z - γ)) * quadraticChar (ZMod p) (z - y) =
      ∑ I ∈ Ou.powerset, ∑ J ∈ Ov.powerset, (∏ β ∈ I, su β) * (∏ γ ∈ J, sv γ) *
        pairSum (I ∪ Fu) (J ∪ Fv) := by
    rw [Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => hexp y z]
    set T : Finset (ZMod p) → Finset (ZMod p) → ZMod p → ZMod p → ℤ := fun I J y z =>
      (∏ β ∈ I, su β) * (∏ γ ∈ J, sv γ) *
        quadraticChar (ZMod p) ((∏ β ∈ I ∪ Fu, (y - β)) * (∏ γ ∈ J ∪ Fv, (z - γ)) * (z - y))
      with hT
    calc ∑ y, ∑ z, ∑ I ∈ Ou.powerset, ∑ J ∈ Ov.powerset, T I J y z
        = ∑ y, ∑ I ∈ Ou.powerset, ∑ z, ∑ J ∈ Ov.powerset, T I J y z :=
          Finset.sum_congr rfl fun y _ => Finset.sum_comm
      _ = ∑ y, ∑ I ∈ Ou.powerset, ∑ J ∈ Ov.powerset, ∑ z, T I J y z :=
          Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun I _ => Finset.sum_comm
      _ = ∑ I ∈ Ou.powerset, ∑ y, ∑ J ∈ Ov.powerset, ∑ z, T I J y z := Finset.sum_comm
      _ = ∑ I ∈ Ou.powerset, ∑ J ∈ Ov.powerset, ∑ y, ∑ z, T I J y z :=
          Finset.sum_congr rfl fun I _ => Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ => ?_
          simp only [hT, pairSum, Finset.mul_sum]
  -- the termwise bound
  have hterm : ∀ I ∈ Ou.powerset, ∀ J ∈ Ov.powerset,
      |(∏ β ∈ I, (su β : ℝ)) * (∏ γ ∈ J, (sv γ : ℝ)) * (pairSum (I ∪ Fu) (J ∪ Fv) : ℝ)| ≤
        p * twoVarCoeff p (I.card + Fu.card) (J.card + Fv.card) := by
    intro I hI J hJ
    have hI' : Disjoint I Fu := Finset.disjoint_of_subset_left (Finset.mem_powerset.mp hI) hu
    have hJ' : Disjoint J Fv := Finset.disjoint_of_subset_left (Finset.mem_powerset.mp hJ) hv
    have hσ : |∏ β ∈ I, (su β : ℝ)| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun β _ => by exact_mod_cast hsu β)
    have hτ : |∏ γ ∈ J, (sv γ : ℝ)| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun γ _ => by exact_mod_cast hsv γ)
    have hP := abs_pairSum_le hTV hp2 (I ∪ Fu) (J ∪ Fv)
    rw [Finset.card_union_of_disjoint hI', Finset.card_union_of_disjoint hJ'] at hP
    rw [abs_mul, abs_mul]
    have h1 : |∏ β ∈ I, (su β : ℝ)| * |∏ γ ∈ J, (sv γ : ℝ)| ≤ 1 :=
      (mul_le_mul hσ hτ (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
    calc |∏ β ∈ I, (su β : ℝ)| * |∏ γ ∈ J, (sv γ : ℝ)| * |(pairSum (I ∪ Fu) (J ∪ Fv) : ℝ)|
        ≤ 1 * |(pairSum (I ∪ Fu) (J ∪ Fv) : ℝ)| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hP
  rw [hsum]
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_prod]
  calc _ ≤ ∑ I ∈ Ou.powerset, |∑ J ∈ Ov.powerset, (∏ β ∈ I, (su β : ℝ)) *
        (∏ γ ∈ J, (sv γ : ℝ)) * (pairSum (I ∪ Fu) (J ∪ Fv) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ I ∈ Ou.powerset, ∑ J ∈ Ov.powerset, |(∏ β ∈ I, (su β : ℝ)) *
        (∏ γ ∈ J, (sv γ : ℝ)) * (pairSum (I ∪ Fu) (J ∪ Fv) : ℝ)| :=
        Finset.sum_le_sum fun I _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ I ∈ Ou.powerset, ∑ J ∈ Ov.powerset,
        (p : ℝ) * twoVarCoeff p (I.card + Fu.card) (J.card + Fv.card) :=
        Finset.sum_le_sum fun I hI => Finset.sum_le_sum fun J hJ => hterm I hI J hJ
    _ = p * ∑ I ∈ Ou.powerset, ∑ J ∈ Ov.powerset,
        twoVarCoeff p (I.card + Fu.card) (J.card + Fv.card) := by
        simp only [Finset.mul_sum]
    _ = _ := by
        rw [sum_powerset_powerset_card Ou Ov (fun i j => twoVarCoeff p (i + Fu.card) (j + Fv.card))]

/-- **The average form** of `two_variable_bound`: dividing by `p²`, with `r = p^{-1/2}`, the
average over `(y_u, y_v) ∈ 𝔽_p²` is at most `r² ∑_{i,j} binom(d_u, i) binom(d_v, j)
𝐜(i + f_u, j + f_v) = r²(C₀ + r C₁ + r² C₂)`. -/
theorem two_variable_bound_avg (hTV : Target.TwoVariable) (hp2 : p ≠ 2)
    (Ou Ov Fu Fv : Finset (ZMod p)) (hu : Disjoint Ou Fu) (hv : Disjoint Ov Fv)
    (su sv : ZMod p → ℤ) (hsu : ∀ β, |su β| ≤ 1) (hsv : ∀ γ, |sv γ| ≤ 1) :
    |((∑ y, ∑ z, (∏ β ∈ Ou, (1 + su β * quadraticChar (ZMod p) (y - β))) *
        (∏ γ ∈ Ov, (1 + sv γ * quadraticChar (ZMod p) (z - γ))) *
        quadraticChar (ZMod p) (∏ β ∈ Fu, (y - β)) *
        quadraticChar (ZMod p) (∏ γ ∈ Fv, (z - γ)) * quadraticChar (ZMod p) (z - y) : ℤ) : ℝ)| /
        (p : ℝ) ^ 2 ≤
      (1 / Real.sqrt p) ^ 2 * ∑ i ∈ range (Ou.card + 1), ∑ j ∈ range (Ov.card + 1),
        (Ou.card.choose i : ℝ) * (Ov.card.choose j : ℝ) *
          twoVarCoeff p (i + Fu.card) (j + Fv.card) := by
  have h := two_variable_bound hTV hp2 Ou Ov Fu Fv hu hv su sv hsu hsv
  have hp : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  rw [div_pow, Real.sq_sqrt hp.le, one_pow, div_le_iff₀ (by positivity)]
  refine h.trans_eq ?_
  field_simp

/-! ### The soft products -/

/-- **The soft product** `ρ̃(y) = ∏_{β ∈ O}(1 + s_β χ(y - β))` with signs `s_β = ±1` lies in
`[0, 2^{|O|}]`, and off its roots it is `2^{|O|}` times the indicator of its constraints
`s_β χ(y - β) = 1` (proof of `lem:push:localvariance` (b)(ii)). -/
theorem soft_product_bounds (O : Finset (ZMod p)) (s : ZMod p → ℤ)
    (hs : ∀ β ∈ O, s β = 1 ∨ s β = -1) (y : ZMod p) :
    0 ≤ ∏ β ∈ O, (1 + s β * quadraticChar (ZMod p) (y - β)) ∧
    ∏ β ∈ O, (1 + s β * quadraticChar (ZMod p) (y - β)) ≤ 2 ^ O.card ∧
    (y ∉ O → ∏ β ∈ O, (1 + s β * quadraticChar (ZMod p) (y - β)) =
      2 ^ O.card * (if ∀ β ∈ O, s β * quadraticChar (ZMod p) (y - β) = 1 then 1 else 0)) := by
  have hfac : ∀ β ∈ O, 0 ≤ 1 + s β * quadraticChar (ZMod p) (y - β) ∧
      1 + s β * quadraticChar (ZMod p) (y - β) ≤ 2 := by
    intro β hβ
    rcases quadraticChar_isQuadratic (ZMod p) (y - β) with h | h | h <;>
      rcases hs β hβ with h' | h' <;> simp [h, h']
  refine ⟨Finset.prod_nonneg fun β hβ => (hfac β hβ).1, ?_, fun hy => ?_⟩
  · calc ∏ β ∈ O, (1 + s β * quadraticChar (ZMod p) (y - β)) ≤ ∏ _β ∈ O, (2 : ℤ) :=
          Finset.prod_le_prod₀ (fun β hβ => (hfac β hβ).1) (fun β hβ => (hfac β hβ).2)
      _ = 2 ^ O.card := Finset.prod_const 2
  · by_cases hall : ∀ β ∈ O, s β * quadraticChar (ZMod p) (y - β) = 1
    · rw [ite_eq_left hall, mul_one, Finset.prod_congr rfl fun β hβ => by rw [hall β hβ]]
      norm_num [Finset.prod_const]
    · rw [ite_eq_right hall, mul_zero]
      push Not at hall
      obtain ⟨β, hβ, hne⟩ := hall
      refine Finset.prod_eq_zero hβ ?_
      have hyβ : y - β ≠ 0 := sub_ne_zero.mpr fun h => hy (h ▸ hβ)
      rcases quadraticChar_dichotomy hyβ with h | h <;> rcases hs β hβ with h' | h' <;>
        simp_all

/-- **The average of a soft product** (proof of `lem:push:localvariance` (b)(ii),
`E ρ̃_u ≤ s_u = α⁺⁺_u + d_u 2^{d_u} r²` after dividing by `p`):
`∑_y ρ̃(y) ≤ 2^{|O|} #{y ∉ O : its constraints hold} + |O| 2^{|O|}`. -/
theorem soft_product_sum_le (O : Finset (ZMod p)) (s : ZMod p → ℤ)
    (hs : ∀ β ∈ O, s β = 1 ∨ s β = -1) :
    ∑ y, ∏ β ∈ O, (1 + s β * quadraticChar (ZMod p) (y - β)) ≤
      2 ^ O.card * ((Finset.univ.filter fun y => y ∉ O ∧
        ∀ β ∈ O, s β * quadraticChar (ZMod p) (y - β) = 1).card : ℤ) + O.card * 2 ^ O.card := by
  rw [← Finset.sum_add_sum_compl O]
  have h1 : ∑ y ∈ O, ∏ β ∈ O, (1 + s β * quadraticChar (ZMod p) (y - β)) ≤
      O.card * 2 ^ O.card := by
    calc ∑ y ∈ O, ∏ β ∈ O, (1 + s β * quadraticChar (ZMod p) (y - β))
        ≤ ∑ _y ∈ O, (2 : ℤ) ^ O.card :=
          Finset.sum_le_sum fun y _ => (soft_product_bounds O s hs y).2.1
      _ = O.card * 2 ^ O.card := by rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : ∑ y ∈ Oᶜ, ∏ β ∈ O, (1 + s β * quadraticChar (ZMod p) (y - β)) =
      2 ^ O.card * ((Finset.univ.filter fun y => y ∉ O ∧
        ∀ β ∈ O, s β * quadraticChar (ZMod p) (y - β) = 1).card : ℤ) := by
    have hset : (Oᶜ.filter fun y => ∀ β ∈ O, s β * quadraticChar (ZMod p) (y - β) = 1) =
        Finset.univ.filter fun y => y ∉ O ∧
          ∀ β ∈ O, s β * quadraticChar (ZMod p) (y - β) = 1 := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_compl, Finset.mem_univ, true_and]
    rw [Finset.sum_congr rfl fun y hy => (soft_product_bounds O s hs y).2.2
      (Finset.mem_compl.mp hy), ← Finset.mul_sum, Finset.sum_boole, hset]
  rw [h2]
  linarith

/-! ### Restoring the excluded values -/

omit [Fact p.Prime] in
/-- **Restoring the excluded values** (proof of `lem:push:localvariance` (b)(ii)): for weights
`0 ≤ a ≤ A_max`, `0 ≤ b ≤ B_max` with averages `E a ≤ s_a`, `E b ≤ s_b`, a kernel `|k| ≤ 1`, and
excluded sets of at most `m` labels for each variable, the restricted sum differs from the full
one by at most `m (A_max s_b + B_max s_a) |F|`; dividing by `|F|² = p²`, the averages differ by
at most `(m/p)(A_max s_b + B_max s_a)` (with `m = 2n`, `A_max = 2^{d_u}`, `B_max = 2^{d_v}`:
`2n r² (2^{d_u} s_v + 2^{d_v} s_u)`). -/
theorem restoration_bound {F : Type*} [Fintype F] [DecidableEq F] [Nonempty F] (a b : F → ℝ)
    (k : F → F → ℝ) (Xu Xv : Finset F) {Amax Bmax sa sb : ℝ} {m : ℕ} (ha0 : ∀ y, 0 ≤ a y)
    (hb0 : ∀ y, 0 ≤ b y) (haM : ∀ y, a y ≤ Amax) (hbM : ∀ y, b y ≤ Bmax)
    (hsa : ∑ y, a y ≤ sa * Fintype.card F) (hsb : ∑ y, b y ≤ sb * Fintype.card F)
    (hk : ∀ y z, |k y z| ≤ 1) (hXu : Xu.card ≤ m) (hXv : Xv.card ≤ m) :
    |∑ y, ∑ z, a y * b z * k y z - ∑ y ∈ Xuᶜ, ∑ z ∈ Xvᶜ, a y * b z * k y z| ≤
      m * (Amax * sb + Bmax * sa) * Fintype.card F := by
  set f : F → F → ℝ := fun y z => a y * b z * k y z with hf
  have hfab : ∀ y z, |f y z| ≤ a y * b z := fun y z => by
    rw [hf, abs_mul, abs_of_nonneg (mul_nonneg (ha0 y) (hb0 z))]
    exact mul_le_of_le_one_right (mul_nonneg (ha0 y) (hb0 z)) (hk y z)
  have hAmax : 0 ≤ Amax := (ha0 (Classical.arbitrary F)).trans (haM _)
  -- the split
  have hsplit : ∑ y, ∑ z, f y z - ∑ y ∈ Xuᶜ, ∑ z ∈ Xvᶜ, f y z =
      ∑ y ∈ Xu, ∑ z, f y z + ∑ y ∈ Xuᶜ, ∑ z ∈ Xv, f y z := by
    rw [← Finset.sum_add_sum_compl Xu (fun y => ∑ z, f y z)]
    have : ∀ y, ∑ z, f y z = ∑ z ∈ Xv, f y z + ∑ z ∈ Xvᶜ, f y z := fun y =>
      (Finset.sum_add_sum_compl Xv (f y)).symm
    rw [Finset.sum_congr rfl fun y (_ : y ∈ Xuᶜ) => this y, Finset.sum_add_distrib]
    ring
  rw [hsplit]
  -- the two parts
  have hsb0 : ∀ y, ∑ z, a y * b z ≤ a y * (sb * Fintype.card F) := fun y => by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hsb (ha0 y)
  have h1 : |∑ y ∈ Xu, ∑ z, f y z| ≤ m * Amax * (sb * Fintype.card F) := by
    calc |∑ y ∈ Xu, ∑ z, f y z| ≤ ∑ y ∈ Xu, ∑ z, a y * b z :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ =>
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z _ => hfab y z))
      _ ≤ ∑ y ∈ Xu, Amax * (sb * Fintype.card F) := Finset.sum_le_sum fun y _ =>
          (hsb0 y).trans (mul_le_mul_of_nonneg_right (haM y)
            ((Finset.sum_nonneg fun z _ => hb0 z).trans hsb))
      _ = Xu.card * (Amax * (sb * Fintype.card F)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ m * (Amax * (sb * Fintype.card F)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hXu)
            (mul_nonneg hAmax ((Finset.sum_nonneg fun z _ => hb0 z).trans hsb))
      _ = m * Amax * (sb * Fintype.card F) := by ring
  have hBmax : 0 ≤ Bmax := (hb0 (Classical.arbitrary F)).trans (hbM _)
  have h2 : |∑ y ∈ Xuᶜ, ∑ z ∈ Xv, f y z| ≤ (sa * Fintype.card F) * (m * Bmax) := by
    calc |∑ y ∈ Xuᶜ, ∑ z ∈ Xv, f y z| ≤ ∑ y ∈ Xuᶜ, ∑ z ∈ Xv, a y * b z :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ =>
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z _ => hfab y z))
      _ ≤ ∑ y, ∑ z ∈ Xv, a y * b z :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun y _ _ =>
            Finset.sum_nonneg fun z _ => mul_nonneg (ha0 y) (hb0 z)
      _ = (∑ y, a y) * ∑ z ∈ Xv, b z := by rw [Finset.sum_mul_sum]
      _ ≤ (sa * Fintype.card F) * (m * Bmax) := by
          refine mul_le_mul hsa ?_ (Finset.sum_nonneg fun z _ => hb0 z)
            ((Finset.sum_nonneg fun y _ => ha0 y).trans hsa)
          calc ∑ z ∈ Xv, b z ≤ ∑ z ∈ Xv, Bmax := Finset.sum_le_sum fun z _ => hbM z
            _ = Xv.card * Bmax := by rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ m * Bmax := mul_le_mul_of_nonneg_right (by exact_mod_cast hXv) hBmax
  calc |∑ y ∈ Xu, ∑ z, f y z + ∑ y ∈ Xuᶜ, ∑ z ∈ Xv, f y z|
      ≤ |∑ y ∈ Xu, ∑ z, f y z| + |∑ y ∈ Xuᶜ, ∑ z ∈ Xv, f y z| := abs_add_le _ _
    _ ≤ m * Amax * (sb * Fintype.card F) + (sa * Fintype.card F) * (m * Bmax) :=
        add_le_add h1 h2
    _ = m * (Amax * sb + Bmax * sa) * Fintype.card F := by ring

/-- **`lem:push:localvariance` (b)(ii), the edge `uv` on the restricted domain.** With the
optional centres `O_u`, `O_v` (signs `±1`), forced centres `F_u`, `F_v` disjoint from them,
`∑_y ρ̃_u ≤ s_u p`, `∑_z ρ̃_v ≤ s_v p`, and excluded sets `X_u`, `X_v` of at most `m` labels:
the sum over `y_u ∉ X_u`, `y_v ∉ X_v` of `ρ̃_u ρ̃_v χ(f_{F_u}(y_u)) χ(f_{F_v}(y_v)) χ(y_v - y_u)`
is at most
`p ∑_{i,j} binom(d_u,i) binom(d_v,j) 𝐜(i + f_u, j + f_v) + m (2^{d_u} s_v + 2^{d_v} s_u) p`
in modulus. Divided by `p²` (and with `m = 2n`) this is the paper's
`r²(C₀ + rC₁ + r²C₂) + 2n r²(2^{d_u} s_v + 2^{d_v} s_u)`. -/
theorem two_variable_restricted (hTV : Target.TwoVariable) (hp2 : p ≠ 2)
    (Ou Ov Fu Fv : Finset (ZMod p)) (hu : Disjoint Ou Fu) (hv : Disjoint Ov Fv)
    (su sv : ZMod p → ℤ) (hsu : ∀ β ∈ Ou, su β = 1 ∨ su β = -1)
    (hsv : ∀ γ ∈ Ov, sv γ = 1 ∨ sv γ = -1) (hsu1 : ∀ β, |su β| ≤ 1) (hsv1 : ∀ γ, |sv γ| ≤ 1)
    {Su Sv : ℝ} {m : ℕ} (Xu Xv : Finset (ZMod p))
    (hSu : ((∑ y, ∏ β ∈ Ou, (1 + su β * quadraticChar (ZMod p) (y - β)) : ℤ) : ℝ) ≤ Su * p)
    (hSv : ((∑ z, ∏ γ ∈ Ov, (1 + sv γ * quadraticChar (ZMod p) (z - γ)) : ℤ) : ℝ) ≤ Sv * p)
    (hXu : Xu.card ≤ m) (hXv : Xv.card ≤ m) :
    |∑ y ∈ Xuᶜ, ∑ z ∈ Xvᶜ,
        ((∏ β ∈ Ou, (1 + su β * quadraticChar (ZMod p) (y - β)) : ℤ) : ℝ) *
        ((∏ γ ∈ Ov, (1 + sv γ * quadraticChar (ZMod p) (z - γ)) : ℤ) : ℝ) *
        ((quadraticChar (ZMod p) (∏ β ∈ Fu, (y - β)) *
          quadraticChar (ZMod p) (∏ γ ∈ Fv, (z - γ)) * quadraticChar (ZMod p) (z - y) : ℤ) : ℝ)| ≤
      p * ∑ i ∈ range (Ou.card + 1), ∑ j ∈ range (Ov.card + 1),
        (Ou.card.choose i : ℝ) * (Ov.card.choose j : ℝ) *
          twoVarCoeff p (i + Fu.card) (j + Fv.card) +
      m * ((2 : ℝ) ^ Ou.card * Sv + (2 : ℝ) ^ Ov.card * Su) * p := by
  set a : ZMod p → ℝ := fun y =>
    ((∏ β ∈ Ou, (1 + su β * quadraticChar (ZMod p) (y - β)) : ℤ) : ℝ) with ha
  set b : ZMod p → ℝ := fun z =>
    ((∏ γ ∈ Ov, (1 + sv γ * quadraticChar (ZMod p) (z - γ)) : ℤ) : ℝ) with hb
  set k : ZMod p → ZMod p → ℝ := fun y z =>
    ((quadraticChar (ZMod p) (∏ β ∈ Fu, (y - β)) * quadraticChar (ZMod p) (∏ γ ∈ Fv, (z - γ)) *
      quadraticChar (ZMod p) (z - y) : ℤ) : ℝ) with hk
  have hk1 : ∀ y z, |k y z| ≤ 1 := fun y z => by
    rw [hk]
    push_cast
    rw [abs_mul, abs_mul]
    have h1 := abs_quadraticChar_le_one (∏ β ∈ Fu, (y - β))
    have h2 := abs_quadraticChar_le_one (∏ γ ∈ Fv, (z - γ))
    have h3 := abs_quadraticChar_le_one (z - y)
    calc _ ≤ 1 * 1 * 1 := mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) zero_le_one) h3
          (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have ha0 : ∀ y, 0 ≤ a y := fun y => by
    simp only [ha]; exact_mod_cast (soft_product_bounds Ou su hsu y).1
  have hb0 : ∀ z, 0 ≤ b z := fun z => by
    simp only [hb]; exact_mod_cast (soft_product_bounds Ov sv hsv z).1
  have haM : ∀ y, a y ≤ (2 : ℝ) ^ Ou.card := fun y => by
    simp only [ha]; exact_mod_cast (soft_product_bounds Ou su hsu y).2.1
  have hbM : ∀ z, b z ≤ (2 : ℝ) ^ Ov.card := fun z => by
    simp only [hb]; exact_mod_cast (soft_product_bounds Ov sv hsv z).2.1
  have hcard : (Fintype.card (ZMod p) : ℝ) = p := by rw [ZMod.card]
  have hsa : ∑ y, a y ≤ Su * Fintype.card (ZMod p) := by
    rw [hcard]; simp only [ha]; exact_mod_cast hSu
  have hsb : ∑ z, b z ≤ Sv * Fintype.card (ZMod p) := by
    rw [hcard]; simp only [hb]; exact_mod_cast hSv
  have hres := restoration_bound a b k Xu Xv ha0 hb0 haM hbM hsa hsb hk1 hXu hXv
  rw [hcard] at hres
  have hfull := two_variable_bound hTV hp2 Ou Ov Fu Fv hu hv su sv hsu1 hsv1
  have e : ((∑ y, ∑ z, (∏ β ∈ Ou, (1 + su β * quadraticChar (ZMod p) (y - β))) *
      (∏ γ ∈ Ov, (1 + sv γ * quadraticChar (ZMod p) (z - γ))) *
      quadraticChar (ZMod p) (∏ β ∈ Fu, (y - β)) *
      quadraticChar (ZMod p) (∏ γ ∈ Fv, (z - γ)) * quadraticChar (ZMod p) (z - y) : ℤ) : ℝ) =
      ∑ y, ∑ z, a y * b z * k y z := by
    rw [ha, hb, hk]
    push_cast
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
    ring
  rw [e] at hfull
  have htri : |∑ y ∈ Xuᶜ, ∑ z ∈ Xvᶜ, a y * b z * k y z| ≤
      |∑ y, ∑ z, a y * b z * k y z| +
        |∑ y, ∑ z, a y * b z * k y z - ∑ y ∈ Xuᶜ, ∑ z ∈ Xvᶜ, a y * b z * k y z| := by
    have := abs_sub (∑ y, ∑ z, a y * b z * k y z)
      (∑ y, ∑ z, a y * b z * k y z - ∑ y ∈ Xuᶜ, ∑ z ∈ Xvᶜ, a y * b z * k y z)
    rwa [sub_sub_cancel] at this
  calc |∑ y ∈ Xuᶜ, ∑ z ∈ Xvᶜ, a y * b z * k y z| ≤ _ := htri
    _ ≤ _ := add_le_add hfull hres
    _ = _ := by ring

end Sarkozy.Spectral
