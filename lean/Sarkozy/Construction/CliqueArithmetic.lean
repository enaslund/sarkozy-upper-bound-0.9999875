module

public import Sarkozy.Construction.CliqueLaw
public import Sarkozy.Construction.HenselSquares
public import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Arithmetic of the square clique (`lem:frontier:iidlocal`(iii))

`paper/sections/19_prefix.tex`. For digit pairs `(A_j, B_j)` with `B_j - A_j` a nonzero square
modulo `p` and `-1` a square modulo `p` (`p ≡ 1 (mod 4)`), the base-`p²` numbers
`N(x) = ∑_j p^{2j} x_j`, `x_j ∈ {A_j, B_j}`, satisfy:

* `digits_sub`: for choices `x ≠ x'`, `N(x) - N(x') = p^{2j} u` with `j < ℓ`, `p ∤ u` and `u` a
  square modulo `p`, hence (Hensel) modulo every power of `p`;
* `clique_card`: the square clique has exactly `2^ℓ` elements;
* `clique_sub`: two distinct clique elements differ in `ℤ/p^{2ℓ}ℤ` by `p^{2j} u` with `j < ℓ`,
  `p ∤ u` and `u` a square modulo every power of `p` (so a unit square modulo `p^{2ℓ - 2j}`).
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy

variable {p : ℕ} [hp : Fact p.Prime]

/-- `N(x) = ∑_j p^{2j} · (if x_j then B_j else A_j)` over the integers. -/
def digitNumber {ℓ : ℕ} (A B : Fin ℓ → ℤ) (x : Fin ℓ → Bool) : ℤ :=
  ∑ j, (p : ℤ) ^ (2 * j.val) * (if x j then B j else A j)

omit hp in
theorem digitNumber_succ {ℓ : ℕ} (A B : Fin (ℓ + 1) → ℤ) (x : Fin (ℓ + 1) → Bool) :
    digitNumber (p := p) A B x = (if x 0 then B 0 else A 0) +
      (p : ℤ) ^ 2 * digitNumber (p := p) (fun j => A j.succ) (fun j => B j.succ)
        (fun j => x j.succ) := by
  unfold digitNumber
  rw [Fin.sum_univ_succ, mul_sum]
  simp only [Fin.val_zero, mul_zero, pow_zero, one_mul, Fin.val_succ]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  rw [show 2 * (j.val + 1) = 2 + 2 * j.val by ring, pow_add]
  ring

/-- **Differences of base-`p²` numbers with square digit gaps.** -/
theorem digits_sub (hsqm1 : IsSquare (-1 : ZMod p)) :
    ∀ {ℓ : ℕ} (A B : Fin ℓ → ℤ), (∀ j, ¬ (p : ℤ) ∣ B j - A j) →
      (∀ j, IsSquare (((B j - A j : ℤ)) : ZMod p)) → ∀ x x' : Fin ℓ → Bool, x ≠ x' →
      ∃ j : ℕ, j < ℓ ∧ ∃ u : ℤ, digitNumber (p := p) A B x - digitNumber (p := p) A B x' =
        (p : ℤ) ^ (2 * j) * u ∧ ¬ (p : ℤ) ∣ u ∧ IsSquare ((u : ℤ) : ZMod p)
  | 0, A, B, _, _, x, x', hxx => absurd (funext fun j => j.elim0) hxx
  | ℓ + 1, A, B, hnd, hsq, x, x', hxx => by
    rw [digitNumber_succ, digitNumber_succ]
    set N := digitNumber (p := p) (fun j => A j.succ) (fun j => B j.succ) (fun j => x j.succ)
    set N' := digitNumber (p := p) (fun j => A j.succ) (fun j => B j.succ) (fun j => x' j.succ)
    by_cases h0 : x 0 = x' 0
    · -- the first digits agree: induct on the tail
      have htail : (fun j : Fin ℓ => x j.succ) ≠ (fun j => x' j.succ) := by
        intro h
        apply hxx
        funext j
        refine Fin.cases h0 (fun i => ?_) j
        exact congrFun h i
      obtain ⟨j, hj, u, hu, hpu, hsqu⟩ := digits_sub hsqm1 (fun j => A j.succ) (fun j => B j.succ)
        (fun j => hnd j.succ) (fun j => hsq j.succ) _ _ htail
      refine ⟨j + 1, by omega, u, ?_, hpu, hsqu⟩
      rw [h0, show (if x' 0 then B 0 else A 0) + (p : ℤ) ^ 2 * N -
          ((if x' 0 then B 0 else A 0) + (p : ℤ) ^ 2 * N') = (p : ℤ) ^ 2 * (N - N') by ring, hu,
        show 2 * (j + 1) = 2 + 2 * j by ring, pow_add]
      ring
    · -- the first digits differ: `j = 0`
      have hcase : (x 0 = true ∧ x' 0 = false) ∨ (x 0 = false ∧ x' 0 = true) := by
        rcases Bool.eq_false_or_eq_true (x 0) with h1 | h1 <;>
          rcases Bool.eq_false_or_eq_true (x' 0) with h2 | h2
        · exact absurd (h1.trans h2.symm) h0
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨h1, h2⟩
        · exact absurd (h1.trans h2.symm) h0
      have hd : (if x 0 then B 0 else A 0) - (if x' 0 then B 0 else A 0) = B 0 - A 0 ∨
          (if x 0 then B 0 else A 0) - (if x' 0 then B 0 else A 0) = -(B 0 - A 0) := by
        rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; simp [h1, h2]
        · right; simp [h1, h2]
      refine ⟨0, by omega,
        ((if x 0 then B 0 else A 0) - (if x' 0 then B 0 else A 0)) + (p : ℤ) ^ 2 * (N - N'),
        by rw [mul_zero, pow_zero, one_mul]; ring, ?_, ?_⟩
      · intro hdiv
        have h2 : (p : ℤ) ∣ (p : ℤ) ^ 2 * (N - N') :=
          dvd_mul_of_dvd_left (dvd_pow_self _ two_ne_zero) _
        have hdd : (p : ℤ) ∣ (if x 0 then B 0 else A 0) - (if x' 0 then B 0 else A 0) := by
          have := dvd_sub hdiv h2
          simpa using this
        rcases hd with h | h
        · rw [h] at hdd; exact hnd 0 hdd
        · rw [h] at hdd; exact hnd 0 (dvd_neg.mp hdd)
      · have hcast : ((((if x 0 then B 0 else A 0) - (if x' 0 then B 0 else A 0)) +
            (p : ℤ) ^ 2 * (N - N') : ℤ) : ZMod p) =
            (((if x 0 then B 0 else A 0) - (if x' 0 then B 0 else A 0) : ℤ) : ZMod p) := by
          push_cast
          rw [ZMod.natCast_self]
          ring
        rw [hcast]
        obtain ⟨s, hs⟩ := hsq 0
        obtain ⟨m, hm⟩ := hsqm1
        rcases hd with h | h
        · rw [h]; exact ⟨s, hs⟩
        · refine ⟨m * s, ?_⟩
          have : ((-(B 0 - A 0) : ℤ) : ZMod p) = (-1) * ((B 0 - A 0 : ℤ) : ZMod p) := by
            push_cast; ring
          rw [h, this, hs, hm]
          ring


section Clique

variable (ℓ : ℕ)

/-- The clique element of a choice of digits. -/
noncomputable def cliqueElt (d : CliqueData p ℓ) (x : Fin ℓ → Bool) : ZMod (p ^ (2 * ℓ)) :=
  ∑ j : Fin ℓ, ((p : ZMod (p ^ (2 * ℓ))) ^ (2 * j.val)) * cliqueDigit p ℓ d j (x j)

/-- The integer digits `A_j = a_j + p k_j`, `B_j = b_j + p k'_j`. -/
def digitA (d : CliqueData p ℓ) (j : Fin ℓ) : ℤ := ((d j).1.1.1.val + p * (d j).2.1.val : ℕ)
def digitB (d : CliqueData p ℓ) (j : Fin ℓ) : ℤ := ((d j).1.1.2.val + p * (d j).2.2.val : ℕ)

theorem cliqueElt_eq_cast (d : CliqueData p ℓ) (x : Fin ℓ → Bool) :
    cliqueElt ℓ d x = ((digitNumber (p := p) (digitA ℓ d) (digitB ℓ d) x : ℤ) : ZMod (p ^ (2 * ℓ))) := by
  unfold cliqueElt digitNumber
  push_cast
  refine sum_congr rfl fun j _ => ?_
  unfold cliqueDigit digitA digitB
  split_ifs <;> push_cast <;> ring

theorem digit_gap_cast (d : CliqueData p ℓ) (j : Fin ℓ) :
    ((digitB ℓ d j - digitA ℓ d j : ℤ) : ZMod p) = (d j).1.1.2 - (d j).1.1.1 := by
  unfold digitA digitB
  push_cast
  rw [ZMod.natCast_self, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  ring

theorem digit_gap_ne (d : CliqueData p ℓ) (j : Fin ℓ) : ¬ (p : ℤ) ∣ digitB ℓ d j - digitA ℓ d j := by
  intro h
  have h0 : ((digitB ℓ d j - digitA ℓ d j : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
  rw [digit_gap_cast] at h0
  have hχ := (d j).1.2
  rw [h0, quadraticChar_zero] at hχ
  exact zero_ne_one hχ

theorem digit_gap_sq (d : CliqueData p ℓ) (j : Fin ℓ) :
    IsSquare ((digitB ℓ d j - digitA ℓ d j : ℤ) : ZMod p) := by
  rw [digit_gap_cast]
  have hχ := (d j).1.2
  have hne : (d j).1.1.2 - (d j).1.1.1 ≠ 0 := by
    intro h; rw [h, quadraticChar_zero] at hχ; exact zero_ne_one hχ
  exact (quadraticChar_one_iff_isSquare hne).mp hχ

/-- **`lem:frontier:iidlocal`(iii), differences.** For `p ≡ 1 (mod 4)`, two distinct clique
elements differ by `p^{2j} w` with `j < ℓ` and `w` a unit square of `ℤ/p^{2ℓ}ℤ` (in particular a
unit square modulo `p^{2ℓ-2j}`). -/
theorem cliqueElt_sub (hp2 : p ≠ 2) (hp4 : p % 4 ≠ 3) (d : CliqueData p ℓ) {x x' : Fin ℓ → Bool}
    (hxx : x ≠ x') :
    ∃ j : ℕ, j < ℓ ∧ ∃ w : ZMod (p ^ (2 * ℓ)), cliqueElt ℓ d x - cliqueElt ℓ d x' =
      (p : ZMod (p ^ (2 * ℓ))) ^ (2 * j) * w ∧ IsUnit w ∧ IsSquare w ∧
      ∃ u : ℤ, w = (u : ZMod (p ^ (2 * ℓ))) ∧ ¬ (p : ℤ) ∣ u := by
  have hsqm1 : IsSquare (-1 : ZMod p) := ZMod.exists_sq_eq_neg_one_iff.mpr hp4
  obtain ⟨j, hj, u, hu, hpu, hsqu⟩ := digits_sub hsqm1 (digitA ℓ d) (digitB ℓ d)
    (digit_gap_ne ℓ d) (digit_gap_sq ℓ d) x x' hxx
  refine ⟨j, hj, (u : ZMod (p ^ (2 * ℓ))), ?_, ?_, ?_, u, rfl, hpu⟩
  · rw [cliqueElt_eq_cast, cliqueElt_eq_cast, ← Int.cast_sub, hu]
    push_cast
    ring
  · -- `u` is prime to `p`, hence a unit modulo `p^{2ℓ}`
    rw [ZMod.coe_int_isUnit_iff_isCoprime]
    have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
    push_cast
    exact IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hpr).mpr hpu)
  · exact Hensel.isSquare_zmod_pow hp2 hpu hsqu (2 * ℓ)

theorem pow_mul_unit_ne_zero {j : ℕ} (hj : j < ℓ) {w : ZMod (p ^ (2 * ℓ))} (hw : IsUnit w) :
    (p : ZMod (p ^ (2 * ℓ))) ^ (2 * j) * w ≠ 0 := by
  intro h
  have h0 : (p : ZMod (p ^ (2 * ℓ))) ^ (2 * j) = 0 := by
    have h' := congrArg (fun y => y * ((hw.unit⁻¹ : (ZMod (p ^ (2 * ℓ)))ˣ) : ZMod _)) h
    simp only [zero_mul, mul_assoc, IsUnit.mul_val_inv, mul_one] at h'
    exact h'
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff] at h0
  have := (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).mp h0
  omega

/-- The clique has exactly `2^ℓ` elements (`lem:frontier:iidlocal`(iii)), for `p ≡ 1 (mod 4)`. -/
theorem clique_card (hp2 : p ≠ 2) (hp4 : p % 4 ≠ 3) (d : CliqueData p ℓ) :
    (clique p ℓ d).card = 2 ^ ℓ := by
  have hinj : Function.Injective (cliqueElt ℓ d) := by
    intro x x' hxx
    by_contra hne
    obtain ⟨j, hj, w, hw, hwu, _, _⟩ := cliqueElt_sub ℓ hp2 hp4 d hne
    exact pow_mul_unit_ne_zero ℓ hj hwu (by rw [← hw, hxx, sub_self])
  have hcl : clique p ℓ d = (univ : Finset (Fin ℓ → Bool)).image (cliqueElt ℓ d) := rfl
  rw [hcl, card_image_of_injective _ hinj, card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]

/-- **Differences in the support of the clique law** (`lem:frontier:iidlocal`(iii)): after a
square-affine map `y ↦ s y + c` with `s` a unit square, two labels coming from distinct clique
elements differ by `p^{2j} w` with `j < ℓ` and `w` a unit square of `ℤ/p^{2ℓ}ℤ`. -/
theorem affine_cliqueElt_sub (hp2 : p ≠ 2) (hp4 : p % 4 ≠ 3) (d : CliqueData p ℓ)
    {s : ZMod (p ^ (2 * ℓ))} (hs : s ∈ unitSquares p ℓ) (c : ZMod (p ^ (2 * ℓ)))
    {x x' : Fin ℓ → Bool} (hxx : x ≠ x') :
    ∃ j : ℕ, j < ℓ ∧ ∃ w : ZMod (p ^ (2 * ℓ)),
      (s * cliqueElt ℓ d x + c) - (s * cliqueElt ℓ d x' + c) =
        (p : ZMod (p ^ (2 * ℓ))) ^ (2 * j) * w ∧ IsUnit w ∧ IsSquare w := by
  obtain ⟨j, hj, w, hw, hwu, hws, _⟩ := cliqueElt_sub ℓ hp2 hp4 d hxx
  obtain ⟨t, _, rfl⟩ := mem_image.mp hs
  refine ⟨j, hj, ((t ^ 2 : (ZMod (p ^ (2 * ℓ)))ˣ) : ZMod _) * w, ?_, ?_, ?_⟩
  · rw [show (((t ^ 2 : (ZMod (p ^ (2 * ℓ)))ˣ) : ZMod _) * cliqueElt ℓ d x + c) -
        (((t ^ 2 : (ZMod (p ^ (2 * ℓ)))ˣ) : ZMod _) * cliqueElt ℓ d x' + c) =
        ((t ^ 2 : (ZMod (p ^ (2 * ℓ)))ˣ) : ZMod _) * (cliqueElt ℓ d x - cliqueElt ℓ d x') by ring, hw]
    ring
  · exact (Units.isUnit _).mul hwu
  · obtain ⟨r, hr⟩ := hws
    refine ⟨(t : ZMod _) * r, ?_⟩
    rw [hr]
    push_cast
    ring

end Clique

end Sarkozy
