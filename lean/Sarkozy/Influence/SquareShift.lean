module

public import Sarkozy.Influence.PinPairBound
public import Sarkozy.Labellings.Extension

/-!
# Pinned influence, XIV: the square-shift bound (`lem:square-shift` (a), matrix part)

`SquareShiftBound p`: for an odd prime `p` and `σ = ±1`, the `𝔽_p × 𝔽_p` matrices
`(A_p(σ(x' - x)) - 1/2)_{x,x'}` have norm at most `(√p + 1)/2` (`squareShiftBound`). This
removes the explicit hypothesis of `lem:mid:pinpair` for odd primes (`pinpair_odd`).

The proof avoids the eigenvalue computation of `lem:square-shift` (a). It uses the Paley
matrix `C(x, x') = χ(x' - x)` (`lem:square-shift` (c)):
* `A_p(σt) - 1/2 = (χ(σ)χ(t) - [t = 0])/2`, so the matrix is `(χ(σ)C - I)/2`;
* `CᵀC = pI - J`, by the two-root identity `∑_x χ((x-a)(x-b)) = -1` for `a ≠ b`
  (`Sarkozy.Labellings.two_root`, unconditional). Hence `‖C u‖² = p‖u‖² - (∑u)² ≤ p‖u‖²`;
* the triangle inequality: `‖(χ(σ)C - I)/2‖ ≤ (√p + 1)/2`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Influence

open Sarkozy

variable {p : ℕ} [Fact p.Prime]

/-- The quadratic character `χ` as a real number. -/
noncomputable def chiR (t : ZMod p) : ℝ := (quadraticChar (ZMod p) t : ℝ)

theorem chiR_mul (s t : ZMod p) : chiR (s * t) = chiR s * chiR t := by
  unfold chiR
  rw [map_mul]
  push_cast
  ring

theorem chiR_sign {σ : ZMod p} (hσ : σ = 1 ∨ σ = -1) : chiR σ = 1 ∨ chiR σ = -1 := by
  have hσ0 : σ ≠ 0 := by
    rcases hσ with h | h <;> rw [h]
    · exact one_ne_zero
    · exact neg_ne_zero.mpr one_ne_zero
  unfold chiR
  rcases quadraticChar_dichotomy hσ0 with h | h <;> rw [h] <;> norm_num

/-- `A_p(σ t) - 1/2 = (χ(σ) χ(t) - [t = 0]) / 2`. -/
theorem sqInd_sub_half {σ : ZMod p} (hσ : σ = 1 ∨ σ = -1) (t : ZMod p) :
    sqInd (σ * t) - 1 / 2 = (chiR σ * chiR t - (if t = 0 then 1 else 0)) / 2 := by
  classical
  have hσ0 : σ ≠ 0 := by
    rcases hσ with h | h <;> rw [h]
    · exact one_ne_zero
    · exact neg_ne_zero.mpr one_ne_zero
  by_cases ht : t = 0
  · subst ht
    have h0 : ¬ IsNzSq (0 : ZMod p) := fun h => h.1 rfl
    rw [mul_zero]
    unfold sqInd chiR
    rw [ite_eq_right h0, quadraticChar_zero, ite_eq_left rfl]
    push_cast
    ring
  · have hst : σ * t ≠ 0 := mul_ne_zero hσ0 ht
    have hiff : IsNzSq (σ * t) ↔ quadraticChar (ZMod p) (σ * t) = 1 := by
      unfold IsNzSq
      rw [and_iff_right hst, quadraticChar_one_iff_isSquare hst]
    have hc : chiR σ * chiR t = chiR (σ * t) := (chiR_mul σ t).symm
    rw [hc, ite_eq_right ht, sub_zero]
    unfold sqInd chiR
    rcases quadraticChar_dichotomy hst with h | h
    · rw [ite_eq_left (hiff.mpr h), h]
      norm_num
    · have hn : ¬ IsNzSq (σ * t) := fun hh => by
        have := hiff.mp hh
        rw [h] at this
        norm_num at this
      rw [ite_eq_right hn, h]
      norm_num

/-- `∑_x χ(y - x) χ(z - x) = p - 1` if `y = z` and `-1` otherwise (`CᵀC = pI - J`). -/
theorem sum_chiR_mul (hp2 : p ≠ 2) (y z : ZMod p) :
    ∑ x, chiR (y - x) * chiR (z - x) = if y = z then (p : ℝ) - 1 else -1 := by
  classical
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  by_cases hyz : y = z
  · subst hyz
    rw [ite_eq_left rfl]
    have e : ∀ x, chiR (y - x) * chiR (y - x) = if x = y then 0 else 1 := by
      intro x
      rw [← chiR_mul]
      by_cases hx : x = y
      · subst hx
        simp [chiR]
      · rw [ite_eq_right hx]
        have hd : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
        unfold chiR
        rw [← sq, quadraticChar_sq_one' hd]
        norm_num
    rw [Finset.sum_congr rfl (fun x _ => e x), Finset.sum_ite, Finset.sum_const_zero, zero_add,
      Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard : (Finset.univ.filter (fun x : ZMod p => ¬ x = y)).card = p - 1 := by
      rw [Finset.filter_ne' Finset.univ y, Finset.card_erase_of_mem (Finset.mem_univ y),
        Finset.card_univ, ZMod.card]
    rw [hcard]
    have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
    push_cast [hp1]
    ring
  · rw [ite_eq_right hyz]
    have h := Labellings.two_root hF hyz
    unfold Labellings.rootSum at h
    simp only [Finset.prod_pair hyz] at h
    have e : ∀ x, chiR (y - x) * chiR (z - x) =
        ((quadraticChar (ZMod p) ((x - y) * (x - z)) : ℤ) : ℝ) := by
      intro x
      rw [← chiR_mul]
      unfold chiR
      congr 2
      ring
    rw [Finset.sum_congr rfl (fun x _ => e x)]
    exact_mod_cast h

/-- The Paley matrix `C(x, x') = χ(x' - x)` has norm at most `√p` (`lem:square-shift` (c)). -/
theorem opBound_paley (hp2 : p ≠ 2) :
    OpBound (Finset.univ : Finset (ZMod p)) Finset.univ (fun x x' => chiR (x' - x)) (√(p : ℝ)) := by
  classical
  intro u
  rw [Real.sq_sqrt (Nat.cast_nonneg p)]
  have e1 : ∑ x, (∑ x', chiR (x' - x) * u x') ^ 2 =
      ∑ x', ∑ x'', u x' * u x'' * ∑ x, chiR (x' - x) * chiR (x'' - x) := by
    have h1 : ∀ x, (∑ x', chiR (x' - x) * u x') ^ 2 =
        ∑ x', ∑ x'', u x' * u x'' * (chiR (x' - x) * chiR (x'' - x)) := by
      intro x
      rw [sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl (fun x' _ => Finset.sum_congr rfl (fun x'' _ => by ring))
    rw [Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x' _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x'' _ => ?_)
    rw [Finset.mul_sum]
  rw [e1]
  simp only [sum_chiR_mul hp2]
  have e2 : ∑ x', ∑ x'', u x' * u x'' * (if x' = x'' then (p : ℝ) - 1 else -1) =
      p * ∑ x, u x ^ 2 - (∑ x, u x) ^ 2 := by
    have : ∀ x', ∑ x'', u x' * u x'' * (if x' = x'' then (p : ℝ) - 1 else -1) =
        p * u x' ^ 2 - u x' * ∑ x'', u x'' := by
      intro x'
      have h1 : ∀ x'', u x' * u x'' * (if x' = x'' then (p : ℝ) - 1 else -1) =
          (if x' = x'' then p * u x' * u x'' else 0) - u x' * u x'' := by
        intro x''
        split_ifs <;> ring
      rw [Finset.sum_congr rfl (fun x'' _ => h1 x''), Finset.sum_sub_distrib,
        Finset.sum_ite_eq Finset.univ x', ite_eq_left (Finset.mem_univ _), Finset.mul_sum]
      ring
    rw [Finset.sum_congr rfl (fun x' _ => this x'), Finset.sum_sub_distrib, ← Finset.mul_sum,
      sq, Finset.sum_mul]
  rw [e2]
  nlinarith [sq_nonneg (∑ x, u x)]

theorem OpBound.smul {α β : Type*} {R : Finset α} {C : Finset β} {A : α → β → ℝ} {Λ : ℝ}
    (h : OpBound R C A Λ) (c : ℝ) : OpBound R C (fun i j => c * A i j) (|c| * Λ) := by
  intro x
  have e : ∀ i, ∑ j ∈ C, c * A i j * x j = c * ∑ j ∈ C, A i j * x j := by
    intro i
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  simp_rw [e]
  have h1 := h x
  calc ∑ i ∈ R, (c * ∑ j ∈ C, A i j * x j) ^ 2 = c ^ 2 * ∑ i ∈ R, (∑ j ∈ C, A i j * x j) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
    _ ≤ c ^ 2 * (Λ ^ 2 * ∑ j ∈ C, x j ^ 2) := mul_le_mul_of_nonneg_left h1 (sq_nonneg c)
    _ = (|c| * Λ) ^ 2 * ∑ j ∈ C, x j ^ 2 := by rw [mul_pow, sq_abs]; ring

/-- **`lem:square-shift` (a), matrix bound**: for an odd prime `p`, `SquareShiftBound p`. -/
theorem squareShiftBound (hp2 : p ≠ 2) : SquareShiftBound p := by
  classical
  intro σ hσ
  have hC := (opBound_paley hp2).smul (chiR σ)
  have habs : |chiR σ| = 1 := by
    rcases chiR_sign hσ with h | h <;> rw [h] <;> norm_num
  rw [habs, one_mul] at hC
  have hI := opBound_neg_diag (p := p) Finset.univ Finset.univ
  have hsum := hC.add hI (Real.sqrt_nonneg _) zero_le_one
  have hhalf := hsum.smul (1 / 2)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hhalf
  have e : 1 / 2 * (√(p : ℝ) + 1) = (√(p : ℝ) + 1) / 2 := by ring
  rw [e] at hhalf
  refine hhalf.congr (fun x _ x' _ => ?_)
  rw [sqInd_sub_half hσ (x' - x)]
  have hxx : (x' - x = 0) ↔ x = x' := by
    rw [sub_eq_zero]
    exact eq_comm
  by_cases h : x = x'
  · rw [ite_eq_left h, ite_eq_left (hxx.mpr h)]
    ring
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hxx.mp h'))]
    ring

/-- **`lem:mid:pinpair` for odd primes**, with no square-shift hypothesis. -/
theorem pinpair_odd {U : Type*} [Fintype U] [DecidableEq U] (hp2 : p ≠ 2)
    (G : OrientedGraph U) (hInj : (injLabellings G p).Nonempty) (F : Finset U) {w : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w < 1) (hw : StandingBound p (maxDeg G F) (Fintype.card U) w)
    {i j : U} (hi : i ∈ F) (hj : j ∈ F) (hij : i ≠ j) (z : U → ZMod p)
    (h : 0 < Sarkozy.Peyre.prob (graphLaw G p hInj) (pinEvent (offPair i j) z)) :
    Sarkozy.Peyre.maxCorr (Sarkozy.Peyre.condLaw (graphLaw G p hInj) (pinEvent (offPair i j) z) h)
      (fun ω => ω i) (fun ω => ω j) ≤ influence G p w i j :=
  pinpair G hInj (squareShiftBound hp2) F hw0 hw1 hw hi hj hij z h

end Sarkozy.Influence
