module

public import Sarkozy.ExtractionK.PinnedCollision

@[expose] public section

/-!
# Pinned coincidences at a threshold `Q ≤ p` (`prop:pinned-collision`, last sentence)

`paper/sections/16_extraction.tex`, `prop:pinned-collision`: "for fixed data, `D_X/r²`, `D_Y/r²`
… are admissible (`lem:majorant`) as functions of `r` on the range where `e^pin_ϖ < 1`". The use
of admissibility is that a bound evaluated at a threshold `Q` holds at every prime `p ≥ Q`, after
the factor `r² = 1/p`; this file proves that consequence directly, by monotonicity in `q`:

* `pin_exp_le_chord` (convexity of `exp`), `pin_mul_expm1_anti` (`q(e^{s/q} − 1)` is nonincreasing),
  `ePin_anti`, and **`pinD_mul_anti`**: `q D(q) = (D/r²)(q)` is nonincreasing in `q ≥ Q` when
  `e^pin_ϖ(Q) < 1`, for every family of neighbourhoods (so for `D_X` and `D_Y`);
* **`pinned_collision_opBound_at`**: `‖T^pin_coll‖ ≤ (Q/q)(D_X(Q) D_Y(Q))^{1/2}` at `q = |F| ≥ Q`.

The statement for `N^pin/r²` (`prop:pinned-extraction`) and the admissibility in the sense of
`lem:majorant` are not stated here.
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

/-- Convexity of `exp`: `e^x ≤ 1 + (x/y)(e^y - 1)` for `0 ≤ x ≤ y`, `y > 0`. -/
theorem pin_exp_le_chord {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : 0 < y) :
    Real.exp x ≤ 1 + x / y * (Real.exp y - 1) := by
  have hb0 : 0 ≤ x / y := div_nonneg hx hy.le
  have hb1 : x / y ≤ 1 := (div_le_one hy).mpr hxy
  have h := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ y) (by linarith : 0 ≤ 1 - x / y) hb0
    (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  have e : x / y * y = x := by field_simp
  rw [e] at h
  linarith

/-- `q (e^{s/q} - 1)` is nonincreasing in `q > 0` for `s ≥ 0`. -/
theorem pin_mul_expm1_anti {s Q q : ℝ} (hs : 0 ≤ s) (hQ : 0 < Q) (hQq : Q ≤ q) :
    q * (Real.exp (s / q) - 1) ≤ Q * (Real.exp (s / Q) - 1) := by
  have hq : 0 < q := lt_of_lt_of_le hQ hQq
  rcases eq_or_lt_of_le hs with h0 | hpos
  · rw [← h0]
    simp
  · have hy : 0 < s / Q := div_pos hpos hQ
    have hx : 0 ≤ s / q := div_nonneg hs hq.le
    have hxy : s / q ≤ s / Q := div_le_div_of_nonneg_left hs hQ hQq
    have h := pin_exp_le_chord hx hxy hy
    have e : s / q / (s / Q) = Q / q := by field_simp
    rw [e] at h
    have : q * (Real.exp (s / q) - 1) ≤ q * (Q / q * (Real.exp (s / Q) - 1)) :=
      mul_le_mul_of_nonneg_left (by linarith) hq.le
    calc q * (Real.exp (s / q) - 1) ≤ q * (Q / q * (Real.exp (s / Q) - 1)) := this
      _ = Q * (Real.exp (s / Q) - 1) := by field_simp

theorem pin_rinv_sq {q : ℝ} (hq : 0 < q) : (Real.sqrt q)⁻¹ ^ 2 = 1 / q := by
  rw [inv_pow, Real.sq_sqrt hq.le, one_div]

theorem ePin_anti (n z d : ℕ) {Q q : ℝ} (hQ : 0 < Q) (hQq : Q ≤ q) :
    ePin q n z d ≤ ePin Q n z d := by
  unfold ePin
  have h1 : (Real.sqrt q)⁻¹ ≤ (Real.sqrt Q)⁻¹ :=
    inv_anti₀ (Real.sqrt_pos.mpr hQ) (Real.sqrt_le_sqrt hQq)
  have h0 : 0 ≤ (Real.sqrt q)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have h2 : (Real.sqrt q)⁻¹ ^ 2 ≤ (Real.sqrt Q)⁻¹ ^ 2 := pow_le_pow_left₀ h0 h1 2
  have ha : (0 : ℝ) ≤ 2 * n + z := by positivity
  have hb : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have := mul_le_mul_of_nonneg_left h2 ha
  have := mul_le_mul_of_nonneg_left h1 hb
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- **`prop:pinned-collision`, the threshold form of the admissibility sentence**: `D/r² =
q D(q)` is nonincreasing in `q ≥ Q` when `e^pin_ϖ(Q) < 1`. -/
theorem pinD_mul_anti {n : ℕ} (z ϖ : ℕ) (N : Fin n → Finset (Fin n)) {Q q : ℝ} (hQ : 0 < Q)
    (hQq : Q ≤ q) (he : ePin Q n z ϖ < 1) : q * pinD q z ϖ N ≤ Q * pinD Q z ϖ N := by
  have hq : 0 < q := lt_of_lt_of_le hQ hQq
  unfold pinD pinU
  rw [pin_rinv_sq hq, pin_rinv_sq hQ]
  set s0 := ∑ j, ∑ i, (2 : ℝ) ^ (ϖ + ((N j).card - if i ∈ N j then 1 else 0))
  have hs0 : 0 ≤ s0 := by positivity
  have hE := pin_mul_expm1_anti hs0 hQ hQq
  rw [one_div_mul_eq_div, one_div_mul_eq_div]
  have heq : ePin q n z ϖ ≤ ePin Q n z ϖ := ePin_anti n z ϖ hQ hQq
  have hUps : pinUps q z ϖ N ≤ pinUps Q z ϖ N := by
    unfold pinUps
    exact prod_le_prod₀ (fun j _ => by linarith [ePin_nonneg q n z (ϖ + (N j).card)])
      (fun j _ => by linarith [ePin_anti n z (ϖ + (N j).card) hQ hQq])
  have hU0 : 0 ≤ pinUps q z ϖ N := prod_nonneg fun j _ => by
    linarith [ePin_nonneg q n z (ϖ + (N j).card)]
  have hden : (1 - ePin Q n z ϖ) ^ n ≤ (1 - ePin q n z ϖ) ^ n :=
    pow_le_pow_left₀ (by linarith) (by linarith) n
  have hdQ : 0 < (1 - ePin Q n z ϖ) ^ n := pow_pos (by linarith) n
  have hfrac : pinUps q z ϖ N / (1 - ePin q n z ϖ) ^ n ≤
      pinUps Q z ϖ N / (1 - ePin Q n z ϖ) ^ n := div_le_div₀ (by
        linarith [prod_nonneg fun j (_ : j ∈ univ) => (by
          linarith [ePin_nonneg Q n z (ϖ + (N j).card)] : (0 : ℝ) ≤ 1 + ePin Q n z (ϖ + (N j).card))])
      hUps hdQ hden
  have hexp0 : 0 ≤ q * (Real.exp (s0 / q) - 1) := by
    have : 1 ≤ Real.exp (s0 / q) := Real.one_le_exp (div_nonneg hs0 hq.le)
    exact mul_nonneg hq.le (by linarith)
  have hfrac0 : 0 ≤ pinUps q z ϖ N / (1 - ePin q n z ϖ) ^ n :=
    div_nonneg hU0 (pow_pos (by linarith) n).le
  calc q * (pinUps q z ϖ N / (1 - ePin q n z ϖ) ^ n * (Real.exp (s0 / q) - 1))
      = pinUps q z ϖ N / (1 - ePin q n z ϖ) ^ n * (q * (Real.exp (s0 / q) - 1)) := by ring
    _ ≤ pinUps Q z ϖ N / (1 - ePin Q n z ϖ) ^ n * (Q * (Real.exp (s0 / Q) - 1)) :=
        mul_le_mul hfrac hE hexp0 (le_trans hfrac0 hfrac)
    _ = Q * (pinUps Q z ϖ N / (1 - ePin Q n z ϖ) ^ n * (Real.exp (s0 / Q) - 1)) := by ring

section At

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **`prop:pinned-collision` at a threshold `Q ≤ q = |F|`**: the bound evaluated at `Q`,
`‖T^pin_coll‖ ≤ (Q/q) (D_X(Q) D_Y(Q))^{1/2}` (i.e. `r² · (D/r²)(Q)`, the use of the
admissibility of `D_X/r²`, `D_Y/r²`; `lem:majorant` is replaced by `pinD_mul_anti`). -/
theorem pinned_collision_opBound_at (hW : WeilBound F) {n : ℕ} (M : Finset F)
    (pin : Fin n → F → ℤ) (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ϖ : ℕ) (hϖ : ∀ j, pinCount pin j ≤ ϖ) {Q : ℝ}
    (hQ : 0 < Q) (hQq : Q ≤ Fintype.card F) (he : ePin Q n M.card ϖ < 1)
    (ς : Fin n → Fin n → ℤ) (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1) :
    Sarkozy.Influence.OpBound (pinLab M pin) (pinLab M pin)
      (fun x y => pinKer ς x y / (pinLab M pin).card)
      (Q / Fintype.card F * Real.sqrt (pinD Q M.card ϖ (pinNX ς) * pinD Q M.card ϖ (pinNY ς))) := by
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  have hq : 0 < q := lt_of_lt_of_le hQ hQq
  have heq : ePin q n M.card ϖ < 1 := lt_of_le_of_lt (ePin_anti n M.card ϖ hQ hQq) he
  have h := pinned_collision_opBound hW M pin hpin hpinM ϖ hϖ heq ς hς
  refine h.mono (Real.sqrt_nonneg _) ?_
  have hX := pinD_mul_anti M.card ϖ (pinNX ς) hQ hQq he
  have hY := pinD_mul_anti M.card ϖ (pinNY ς) hQ hQq he
  have hX0 := pinD_nonneg q M.card ϖ (pinNX ς) heq
  have hY0 := pinD_nonneg q M.card ϖ (pinNY ς) heq
  have hX0' := pinD_nonneg Q M.card ϖ (pinNX ς) he
  have hY0' := pinD_nonneg Q M.card ϖ (pinNY ς) he
  have hXq : pinD q M.card ϖ (pinNX ς) ≤ Q / q * pinD Q M.card ϖ (pinNX ς) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hq]
    linarith
  have hYq : pinD q M.card ϖ (pinNY ς) ≤ Q / q * pinD Q M.card ϖ (pinNY ς) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hq]
    linarith
  have hQq0 : 0 ≤ Q / q := div_nonneg hQ.le hq.le
  calc Real.sqrt (pinD q M.card ϖ (pinNX ς) * pinD q M.card ϖ (pinNY ς))
      ≤ Real.sqrt ((Q / q * pinD Q M.card ϖ (pinNX ς)) * (Q / q * pinD Q M.card ϖ (pinNY ς))) :=
        Real.sqrt_le_sqrt (mul_le_mul hXq hYq hY0 (mul_nonneg hQq0 hX0'))
    _ = Real.sqrt ((Q / q) ^ 2 * (pinD Q M.card ϖ (pinNX ς) * pinD Q M.card ϖ (pinNY ς))) := by
        ring_nf
    _ = Q / q * Real.sqrt (pinD Q M.card ϖ (pinNX ς) * pinD Q M.card ϖ (pinNY ς)) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hQq0]

end At

end Sarkozy.ExtractionK
