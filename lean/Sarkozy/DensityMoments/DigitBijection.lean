module

public import Sarkozy.DensityMoments.Clique36
public import Sarkozy.Construction.CliqueArithmetic

/-!
# Base-`p²` digits: `(ℤ/p²ℤ)^ℓ ≅ ℤ/p^{2ℓ}ℤ` in digit coordinates

`thm:density:iid-prefix`(b) and `lem:density:clique-copies`
(`paper/sections/30_density_moment_upgrade.tex`) identify the label group `ℤ/p^{2ℓ}ℤ` of the prefix
with `ℓ` independent digit pairs. With the digit alphabet `Digit p = ZMod p × Fin p`
(`(x, y) ↦ x + p y`) of `Sarkozy/DensityMoments/Clique36.lean`:

* `digitEquiv p ℓ : (Fin ℓ → Digit p) ≃ ZMod (p^{2ℓ})`, `w ↦ ∑_j p^{2j} (x_j + p y_j)`;
* `digitEquiv_label`: the clique element `cliqueElt ℓ d x` of `Construction/CliqueArithmetic.lean`
  is the image of the per-digit labels `label (pairB p) (pairA p) (d j) (x j)`;
* `cliqueElt_injective`: hence `x ↦ cliqueElt ℓ d x` is injective for every odd prime (only
  `a_j ≠ b_j` is used, not `p ≡ 1 (mod 4)`).
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.DensityMoments

open CliqueCopies

variable {p : ℕ} [hp : Fact p.Prime]

/-- The value `x + p y < p²` of a digit-pair label. -/
def digitVal (x : Digit p) : ℕ := x.1.val + p * x.2.val

theorem digitVal_lt (x : Digit p) : digitVal x < p ^ 2 := by
  unfold digitVal
  have h1 : x.1.val < p := ZMod.val_lt x.1
  have h2 : x.2.val + 1 ≤ p := x.2.isLt
  calc x.1.val + p * x.2.val < p + p * x.2.val := by omega
    _ = p * (x.2.val + 1) := by ring
    _ ≤ p * p := Nat.mul_le_mul_left _ h2
    _ = p ^ 2 := (sq p).symm

theorem digitVal_injective : Function.Injective (digitVal (p := p)) := by
  intro x y hxy
  have hp0 : 0 < p := hp.out.pos
  have h1 : ∀ z : Digit p, digitVal z % p = z.1.val := by
    intro z
    unfold digitVal
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ZMod.val_lt z.1)]
  have h2 : ∀ z : Digit p, digitVal z / p = z.2.val := by
    intro z
    unfold digitVal
    rw [Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt (ZMod.val_lt z.1), zero_add]
  have e1 : x.1 = y.1 := ZMod.val_injective p (by rw [← h1 x, ← h1 y, hxy])
  have e2 : x.2 = y.2 := Fin.ext (by rw [← h2 x, ← h2 y, hxy])
  exact Prod.ext e1 e2

/-- The base-`p²` number of a digit vector. -/
def digitNat : ∀ {ℓ : ℕ}, (Fin ℓ → Digit p) → ℕ
  | 0, _ => 0
  | _ + 1, w => digitVal (w 0) + p ^ 2 * digitNat (fun j => w j.succ)

omit hp in
theorem digitNat_eq_sum : ∀ {ℓ : ℕ} (w : Fin ℓ → Digit p),
    digitNat w = ∑ j : Fin ℓ, p ^ (2 * j.val) * digitVal (w j)
  | 0, _ => by simp [digitNat]
  | ℓ + 1, w => by
    rw [digitNat, digitNat_eq_sum (fun j => w j.succ), Fin.sum_univ_succ, mul_sum]
    simp only [Fin.val_zero, mul_zero, pow_zero, one_mul, Fin.val_succ]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [show 2 * (j.val + 1) = 2 + 2 * j.val by ring, pow_add]
    ring

theorem digitNat_lt : ∀ {ℓ : ℕ} (w : Fin ℓ → Digit p), digitNat w < p ^ (2 * ℓ)
  | 0, _ => by simp [digitNat]
  | ℓ + 1, w => by
    rw [digitNat]
    have h1 := digitVal_lt (w 0)
    have h2 := digitNat_lt (fun j => w j.succ)
    calc digitVal (w 0) + p ^ 2 * digitNat (fun j => w j.succ)
        < p ^ 2 + p ^ 2 * digitNat (fun j => w j.succ) := by omega
      _ = p ^ 2 * (digitNat (fun j => w j.succ) + 1) := by ring
      _ ≤ p ^ 2 * p ^ (2 * ℓ) := Nat.mul_le_mul_left _ h2
      _ = p ^ (2 * (ℓ + 1)) := by ring

theorem digitNat_injective : ∀ {ℓ : ℕ}, Function.Injective (digitNat (p := p) (ℓ := ℓ))
  | 0, w, w', _ => funext fun j => j.elim0
  | ℓ + 1, w, w', h => by
    have hp2 : 0 < p ^ 2 := pow_pos hp.out.pos 2
    rw [digitNat, digitNat] at h
    have hmod := congrArg (· % p ^ 2) h
    have hdiv := congrArg (· / p ^ 2) h
    rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (digitVal_lt _), Nat.mod_eq_of_lt (digitVal_lt _)] at hmod
    rw [Nat.add_mul_div_left _ _ hp2, Nat.add_mul_div_left _ _ hp2,
      Nat.div_eq_of_lt (digitVal_lt _), Nat.div_eq_of_lt (digitVal_lt _), zero_add,
      zero_add] at hdiv
    have h0 : w 0 = w' 0 := digitVal_injective hmod
    have htail := digitNat_injective hdiv
    funext j
    refine Fin.cases h0 (fun i => ?_) j
    exact congrFun htail i

variable (p) in
/-- **The digit bijection** `(Fin ℓ → Digit p) ≃ ℤ/p^{2ℓ}ℤ`, `w ↦ ∑_j p^{2j} (x_j + p y_j)`. -/
noncomputable def digitEquiv (ℓ : ℕ) : (Fin ℓ → Digit p) ≃ ZMod (p ^ (2 * ℓ)) :=
  Equiv.ofBijective (fun w => (digitNat w : ZMod (p ^ (2 * ℓ)))) <| by
    rw [Fintype.bijective_iff_injective_and_card]
    constructor
    · intro w w' h
      have hv := congrArg ZMod.val h
      simp only [ZMod.val_natCast] at hv
      rw [Nat.mod_eq_of_lt (digitNat_lt w), Nat.mod_eq_of_lt (digitNat_lt w')] at hv
      exact digitNat_injective hv
    · rw [Fintype.card_fun, Fintype.card_prod, ZMod.card, ZMod.card, Fintype.card_fin,
        Fintype.card_fin, pow_mul, sq]

theorem digitEquiv_apply (ℓ : ℕ) (w : Fin ℓ → Digit p) :
    digitEquiv p ℓ w = ((∑ j : Fin ℓ, p ^ (2 * j.val) * digitVal (w j) : ℕ) :
      ZMod (p ^ (2 * ℓ))) := by
  rw [← digitNat_eq_sum]
  rfl

/-- **The clique element in digit coordinates**: `cliqueElt ℓ d x` is the digit bijection applied
to the per-digit labels `label (pairB p) (pairA p) (d j) (x j)`. -/
theorem digitEquiv_label (ℓ : ℕ) (d : CliqueData p ℓ) (x : Fin ℓ → Bool) :
    digitEquiv p ℓ (fun j => label (pairB p) (pairA p) (d j) (x j)) = cliqueElt ℓ d x := by
  rw [digitEquiv_apply]
  unfold cliqueElt
  push_cast
  refine sum_congr rfl fun j _ => ?_
  congr 1
  unfold cliqueDigit
  cases x j <;> simp [label, pairA, pairB, digitVal]

/-- The two labels of a digit pair differ. -/
theorem pairB_ne_pairA (ω : DigitData p) : pairB p ω ≠ pairA p ω := by
  intro h
  have h1 : ω.1.1.2 = ω.1.1.1 := congrArg Prod.fst h
  have hχ := ω.1.2
  rw [h1, sub_self, quadraticChar_zero] at hχ
  exact zero_ne_one hχ

/-- **The clique has `2^ℓ` distinct elements** at every prime: `x ↦ cliqueElt ℓ d x` is
injective. -/
theorem cliqueElt_injective (ℓ : ℕ) (d : CliqueData p ℓ) : Function.Injective (cliqueElt ℓ d) := by
  intro x x' h
  rw [← digitEquiv_label, ← digitEquiv_label] at h
  have h' := (digitEquiv p ℓ).injective h
  funext j
  have hj := congrFun h' j
  have hne := pairB_ne_pairA (d j)
  cases hx : x j <;> cases hx' : x' j
  · rfl
  · rw [hx, hx'] at hj
    exact absurd hj.symm hne
  · rw [hx, hx'] at hj
    exact absurd hj hne
  · rfl

variable (p) in
/-- **One digit pair**: `Digit p ≃ ℤ/p²ℤ`, `(x, y) ↦ x + p y`. -/
noncomputable def digitEquivOne : Digit p ≃ ZMod (p ^ 2) :=
  Equiv.ofBijective (fun x => (digitVal x : ZMod (p ^ 2))) <| by
    rw [Fintype.bijective_iff_injective_and_card]
    constructor
    · intro x x' h
      have hv := congrArg ZMod.val h
      simp only [ZMod.val_natCast] at hv
      rw [Nat.mod_eq_of_lt (digitVal_lt x), Nat.mod_eq_of_lt (digitVal_lt x')] at hv
      exact digitVal_injective hv
    · rw [Fintype.card_prod, ZMod.card, ZMod.card, Fintype.card_fin, sq]

/-- The labels of `lem:density:clique36` in `ℤ/p²ℤ`: `A = a + p k` and `B = b + p k'`. -/
theorem digitEquivOne_pairA (ω : DigitData p) :
    digitEquivOne p (pairA p ω) = ((ω.1.1.1.val + p * ω.2.1.val : ℕ) : ZMod (p ^ 2)) := rfl

theorem digitEquivOne_pairB (ω : DigitData p) :
    digitEquivOne p (pairB p ω) = ((ω.1.1.2.val + p * ω.2.2.val : ℕ) : ZMod (p ^ 2)) := rfl

/-- **`lem:density:clique36` on `ℤ/p²ℤ`**, the paper's alphabet: 36 conditionally independent
uniform draws from `{A, B}`, `A = a + p k`, `B = b + p k'` in `ℤ/p²ℤ`, have unit mixed
`L^{600/17}`. -/
theorem clique36_zmod (hp2 : p ≠ 2) (h16 : 2 ^ 16 ≤ p) (h512 : p < 2 ^ 512)
    (hinterp : ∀ i : Fin 31, 2 ^ Certificates.clique36Band i ≤ p →
      p < 2 ^ (Certificates.clique36Band i + 16) →
      SquarePairInterpolation p hp2 (Certificates.clique36J i)) :
    MixedLpBound (drawLaw (digitPairLaw p) (fun ω => digitEquivOne p (pairB p ω))
      (fun ω => digitEquivOne p (pairA p ω)) (Fin 36)) (600 / 17) 1 := by
  have h := (clique36 hp2 h16 h512 hinterp).map_equiv (digitEquivOne p)
  apply mixedLpBound_of_expect_eq _ h
  intro F
  rw [FiniteLaw.expect_map, expect_drawLaw, expect_drawLaw]
  refine FiniteLaw.expect_congr _ fun ω => FiniteLaw.expect_congr _ fun c => ?_
  congr 1
  funext t
  show label _ _ ω (c t) = digitEquivOne p (label (pairB p) (pairA p) ω (c t))
  cases c t <;> rfl

end Sarkozy.DensityMoments
