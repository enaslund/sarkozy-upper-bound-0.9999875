module

public import Sarkozy.DensityMoments.Clique36Assembly
public import Sarkozy.Certificates.SquarePairMoment
public import Sarkozy.Moments.Product

/-!
# Thirty-six digit-clique draws (`lem:density:clique36`)

`paper/sections/30_density_moment_upgrade.tex`. The digit-pair law of `def:clique-law`: a digit
pair is `(A, B)` with `A = a + p k`, `B = b + p k'`, where `(a, b)` is a uniform strict square pair
of `𝔽_p` (`χ(b - a) = 1`) and `k, k'` are independent uniform digits. We keep the two base-`p`
digits of a label as coordinates: the alphabet is `Digit p = ZMod p × Fin p`, the label
`x + p y` being `(x, y)`. This is the data `StrictSquarePair p × Fin p × Fin p` of one digit pair
of `Sarkozy.CliqueData`, and `pairB`, `pairA` are the two labels `cliqueDigit … true` and
`cliqueDigit … false` of `Construction/CliqueLaw.lean` in these coordinates. The identification
with `ℤ/p²ℤ` is a bijection of alphabets, under which mixed bounds transfer
(`MixedLpBound.map_equiv`); it is made in `Sarkozy/DensityMoments/IidPrefix.lean`.

* `digitPair_pairLpBound`: the last sentence of `lem:density:edge-moment`. If the uniform strict
  square pair law of `𝔽_p` has unit mixed `L^r`, so does the digit pair `(B, A)`: average each
  input over its high digit, an `L^r` contraction (`lpNorm_digitAvg_le`).
* `pairA_uniform`, `pairB_uniform`: both labels are uniform on the alphabet.
* `clique36`: **`lem:density:clique36`**. At every odd prime `2^16 ≤ p < 2^512`, the law of 36
  conditionally independent uniform draws from `{B, A}` has unit mixed `L^{600/17}`. Here the
  interpolated centred bound of `lem:density:edge-moment` (`SquarePairInterpolation`, for the
  band's integer `j`) is a hypothesis; `Unconditional.lean` discharges it with I1's
  `Interpolation.square_pair_interp` (`clique36_proved`).

The paper states `lem:density:clique36` for `p ≡ 1 (mod 4)`; the proof does not use it, and
neither does this formalization. (Our orientation `(B, A)` of the pair is the clique's; the pair
moment is applied to `(A, B)`, which is the paper's uniform strict square pair, so `χ(-1)` is never
needed.)
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.DensityMoments

open Certificates CliqueCopies InvariantPair

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable (p : ℕ) [hp : Fact p.Prime]

/-- The data of one digit pair: a strict square pair `(a, b)` and two high digits `k, k'`. -/
abbrev DigitData := StrictSquarePair p × Fin p × Fin p

/-- The alphabet of one digit pair, `x + p y ↦ (x, y)`. -/
abbrev Digit := ZMod p × Fin p

/-- The label `A = a + p k`. -/
def pairA (ω : DigitData p) : Digit p := (ω.1.1.1, ω.2.1)

/-- The label `B = b + p k'`. -/
def pairB (ω : DigitData p) : Digit p := (ω.1.1.2, ω.2.2)

/-- The digit-pair law of `def:clique-law`. -/
noncomputable abbrev digitPairLaw : FiniteLaw (DigitData p) := FiniteLaw.uniform (DigitData p)

variable {p}

/-- Expectations under the uniform law on a triple product, coordinate by coordinate. -/
theorem expect_uniform_triple {A B C : Type*} [Fintype A] [Fintype B] [Fintype C] [Nonempty A]
    [Nonempty B] [Nonempty C] (F : A × B × C → ℝ) :
    (FiniteLaw.uniform (A × B × C)).expect F = (FiniteLaw.uniform A).expect (fun x =>
      (FiniteLaw.uniform B).expect (fun y => (FiniteLaw.uniform C).expect (fun z =>
        F (x, y, z)))) := by
  rw [← FiniteLaw.uniform_product (X := A) (Y := B × C), FiniteLaw.expect_product]
  refine FiniteLaw.expect_congr _ fun x => ?_
  rw [← FiniteLaw.uniform_product (X := B) (Y := C), FiniteLaw.expect_product]

/-- Sums over strict square pairs are sums over the class set `χ(z₁ - z₀) = 1`. -/
theorem sum_strictSquarePair (h : ZMod p → ZMod p → ℝ) :
    ∑ e : StrictSquarePair p, h e.1.1 e.1.2 = ∑ x ∈ classSet (p := p) 1, h (x 0) (x 1) := by
  refine Finset.sum_bij' (fun e _ => ![e.1.1, e.1.2])
    (fun x hx => ⟨(x 0, x 1), (mem_filter.mp hx).2⟩) ?_ ?_ ?_ ?_ ?_
  · intro e _
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    simpa using e.2
  · intro x _
    exact mem_univ _
  · intro e _
    rfl
  · intro x _
    funext k
    fin_cases k <;> rfl
  · intro e _
    rfl

/-- **The strict square pairs as the class law**: uniform expectations over strict square pairs
are expectations under `uniformOn (classSet 1)`. -/
theorem expect_strictSquarePair (hp2 : p ≠ 2) (h : ZMod p → ZMod p → ℝ) :
    (FiniteLaw.uniform (StrictSquarePair p)).expect (fun e => h e.1.1 e.1.2) =
      (uniformOn (classSet (p := p) 1) (classSet_nonempty hp2 (Or.inl rfl))).expect
        (fun x => h (x 0) (x 1)) := by
  rw [FiniteLaw.expect_uniform, expect_uniformOn, sum_strictSquarePair]
  congr 1
  have hc := sum_strictSquarePair (p := p) (fun _ _ => (1 : ℝ))
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one] at hc
  exact hc

/-- The average of a digit-pair input over its high digit. -/
noncomputable def digitAvg (f : Digit p → ℝ) (z : ZMod p) : ℝ :=
  (FiniteLaw.uniform (Fin p)).expect (fun k => f (z, k))

/-- **Averaging over the high digit is an `L^r` contraction**, `r ≥ 1`. -/
theorem lpNorm_digitAvg_le {r : ℝ} (hr : 1 ≤ r) (f : Digit p → ℝ) :
    (FiniteLaw.uniform (ZMod p)).lpNorm r (digitAvg f) ≤
      (FiniteLaw.uniform (Digit p)).lpNorm r f := by
  have hr0 : 0 < r := by linarith
  have hmom : (FiniteLaw.uniform (ZMod p)).moment r (digitAvg f) ≤
      (FiniteLaw.uniform (Digit p)).moment r f := by
    unfold FiniteLaw.moment
    rw [← FiniteLaw.uniform_product, FiniteLaw.expect_product]
    apply FiniteLaw.expect_mono
    intro z
    unfold digitAvg
    set ν := FiniteLaw.uniform (Fin p)
    calc |ν.expect (fun k => f (z, k))| ^ r ≤ (ν.expect (fun k => |f (z, k)|)) ^ r :=
          Real.rpow_le_rpow (abs_nonneg _) (ν.abs_expect_le _) hr0.le
      _ ≤ ν.expect (fun k => |f (z, k)| ^ r) := ν.expect_rpow_le hr (fun _ => abs_nonneg _)
  unfold FiniteLaw.lpNorm
  exact Real.rpow_le_rpow (FiniteLaw.moment_nonneg _ _ _) hmom (by positivity)

/-- The uniform expectation on the alphabet, digit by digit. -/
theorem expect_digit (g : Digit p → ℝ) :
    (FiniteLaw.uniform (Digit p)).expect g = (FiniteLaw.uniform (ZMod p)).expect (digitAvg g) := by
  rw [← FiniteLaw.uniform_product, FiniteLaw.expect_product]
  rfl

/-- Products of functions of the two labels, digit-averaged. -/
theorem expect_pairB_pairA (f g : Digit p → ℝ) :
    (digitPairLaw p).expect (fun ω => f (pairB p ω) * g (pairA p ω)) =
      (FiniteLaw.uniform (StrictSquarePair p)).expect
        (fun e => digitAvg g e.1.1 * digitAvg f e.1.2) := by
  rw [expect_uniform_triple]
  refine FiniteLaw.expect_congr _ fun e => ?_
  unfold digitAvg pairA pairB
  simp only
  rw [← FiniteLaw.expect_mul_const]
  refine FiniteLaw.expect_congr _ fun k => ?_
  rw [← FiniteLaw.expect_const_mul]
  refine FiniteLaw.expect_congr _ fun k' => ?_
  ring

/-- **The digit-pair moment** (last sentence of `lem:density:edge-moment`): if the uniform strict
square pair law of `𝔽_p` has unit mixed `L^r`, `r ≥ 1`, so does the digit pair `(B, A)` on
`ℤ/p²ℤ`, in its digit coordinates. -/
theorem digitPair_pairLpBound (hp2 : p ≠ 2) {r : ℝ} (hr : 1 ≤ r)
    (hclass : MixedLpBound (uniformOn (classSet (p := p) 1) (classSet_nonempty hp2 (Or.inl rfl)))
      r 1) :
    PairLpBound (digitPairLaw p) (pairB p) (pairA p) r := by
  intro f g
  rw [expect_pairB_pairA,
    expect_strictSquarePair hp2 (fun x y => digitAvg g x * digitAvg f y)]
  have h := hclass (![digitAvg g, digitAvg f])
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul] at h
  refine h.trans ?_
  rw [mul_comm]
  exact mul_le_mul (lpNorm_digitAvg_le hr f) (lpNorm_digitAvg_le hr g)
    (FiniteLaw.lpNorm_nonneg _ _ _) (FiniteLaw.lpNorm_nonneg _ _ _)

/-- Coordinates of the class law are uniform. -/
theorem classSet_coord_expect (hp2 : p ≠ 2) (v : Fin 2) (g : ZMod p → ℝ) :
    (uniformOn (classSet (p := p) 1) (classSet_nonempty hp2 (Or.inl rfl))).expect
      (fun x => g (x v)) = (FiniteLaw.uniform (ZMod p)).expect g := by
  have h := DensityUpgrade.conditioning_marginal_sum _
    (EdgeGate.classSet_uniformCoords hp2 (Or.inl rfl)) v g
  rw [FiniteLaw.expect_uniform]
  unfold FiniteLaw.expect
  rw [h, div_eq_mul_inv]

/-- **The label `A` is uniform.** -/
theorem pairA_uniform (hp2 : p ≠ 2) (g : Digit p → ℝ) :
    (digitPairLaw p).expect (fun ω => g (pairA p ω)) = (FiniteLaw.uniform (Digit p)).expect g := by
  have h := expect_pairB_pairA (p := p) (fun _ => 1) g
  simp only [one_mul] at h
  rw [h]
  have hA : ∀ e : StrictSquarePair p, digitAvg g e.1.1 * digitAvg (fun _ : Digit p => (1 : ℝ)) e.1.2 =
      digitAvg g e.1.1 := by
    intro e
    simp [digitAvg]
  simp only [hA]
  rw [expect_strictSquarePair hp2 (fun x _ => digitAvg g x), expect_digit]
  exact classSet_coord_expect hp2 0 _

/-- **The label `B` is uniform.** -/
theorem pairB_uniform (hp2 : p ≠ 2) (g : Digit p → ℝ) :
    (digitPairLaw p).expect (fun ω => g (pairB p ω)) = (FiniteLaw.uniform (Digit p)).expect g := by
  have h := expect_pairB_pairA (p := p) g (fun _ => 1)
  simp only [mul_one] at h
  rw [h]
  have hB : ∀ e : StrictSquarePair p, digitAvg (fun _ : Digit p => (1 : ℝ)) e.1.1 * digitAvg g e.1.2 =
      digitAvg g e.1.2 := by
    intro e
    simp [digitAvg]
  simp only [hB]
  rw [expect_strictSquarePair hp2 (fun _ y => digitAvg g y), expect_digit]
  exact classSet_coord_expect hp2 1 _

/-- **The analytic input** of `lem:density:edge-moment`: the interpolated centred bound
`β = L^{(j-1)/(j+1)} ρ^{2/(j+1)}`, `L = (p+1)/(p-1)`, `ρ = 1/(√p - 1)`, for the uniform strict square
pair law at `r = 1 + 1/j` (bilinear Riesz–Thorin between the `L¹` and `L²` bounds). A hypothesis
in this file; proved by I1 (`Interpolation.square_pair_interp`), see
`squarePairInterpolation_proved` in `Unconditional.lean`. -/
def SquarePairInterpolation (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (j : ℕ) : Prop :=
  ∀ f g : ZMod p → ℝ, ∑ a, f a = 0 → ∑ a, g a = 0 →
    |∑ x, (uniformOn (classSet (p := p) 1) (classSet_nonempty hp2 (Or.inl rfl))).weight x *
        (f (x 0) * g (x 1))| ≤
      (((p : ℝ) + 1) / ((p : ℝ) - 1)) ^ (((j : ℝ) - 1) / ((j : ℝ) + 1)) *
        (1 / (Real.sqrt p - 1)) ^ ((2 : ℝ) / ((j : ℝ) + 1)) *
        DensityUpgrade.conditioningNorm (1 + 1 / (j : ℝ)) f *
        DensityUpgrade.conditioningNorm (1 + 1 / (j : ℝ)) g

/-! ## The bands -/

theorem bandJ_eq (i : Fin 31) : EdgeGate.bandJ i = clique36J i := by
  fin_cases i <;> rfl

theorem two_le_clique36J : ∀ i : Fin 31, 2 ≤ clique36J i := by decide

theorem band_index {L : ℕ} (h1 : 16 ≤ L) (h2 : L < 512) :
    L / 16 - 1 < 31 ∧ 16 * (L / 16 - 1 + 1) ≤ L ∧ L + 1 ≤ 16 * (L / 16 - 1 + 1) + 16 := by
  omega

theorem exists_band_aux {n E : ℕ} (hE : E = 512) (h16 : 2 ^ 16 ≤ n) (hn : n < 2 ^ E) :
    ∃ i : Fin 31, 2 ^ clique36Band i ≤ n ∧ n < 2 ^ (clique36Band i + 16) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact absurd h16 (by norm_num)
  have hL16 : 16 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) h16
  have hLE : Nat.log 2 n < E := Nat.log_lt_of_lt_pow hn0 hn
  obtain ⟨hi, hb1, hb2⟩ := band_index hL16 (by rw [← hE]; exact hLE)
  refine ⟨⟨Nat.log 2 n / 16 - 1, hi⟩, ?_, ?_⟩
  · show 2 ^ (16 * (Nat.log 2 n / 16 - 1 + 1)) ≤ n
    exact le_trans (Nat.pow_le_pow_right (by norm_num) hb1) (Nat.pow_log_le_self 2 hn0)
  · show n < 2 ^ (16 * (Nat.log 2 n / 16 - 1 + 1) + 16)
    exact lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by norm_num) n)
      (Nat.pow_le_pow_right (by norm_num) hb2)

/-- Every `2^16 ≤ p < 2^512` lies in a band `2^b ≤ p < 2^{b+16}`, `b = 16 (i + 1)`. -/
theorem exists_band {n : ℕ} (h16 : 2 ^ 16 ≤ n) (h512 : n < 2 ^ 512) :
    ∃ i : Fin 31, 2 ^ clique36Band i ≤ n ∧ n < 2 ^ (clique36Band i + 16) :=
  exists_band_aux rfl h16 h512

/-- `lem:density:clique36` from the two gates at an integer `j ≥ 2` and a band exponent `e`
with `p < 2^{e+16}`. -/
theorem clique36_of_gates (hp2 : p ≠ 2) {j e : ℕ} (hj : 2 ≤ j)
    (hedge : (j : ℝ) ^ (j + 1) * (((p : ℝ) + 1) / ((p : ℝ) - 1)) ^ (j - 1) *
      (1 / (Real.sqrt p - 1)) ^ 2 ≤ 1)
    (hbin : clique36BinomialCharge e j ≤ 95659840 / 13884957009) (hhi : p < 2 ^ (e + 16))
    (hinterp : SquarePairInterpolation p hp2 j) :
    MixedLpBound (drawLaw (digitPairLaw p) (pairB p) (pairA p) (Fin 36)) (600 / 17) 1 := by
  have hj1 : 1 ≤ j := le_trans (by norm_num) hj
  have hclass := EdgeGate.square_pair_moment hp2 (Or.inl rfl) hj1 hedge hinterp
  have hr : (1 : ℝ) ≤ 1 + 1 / (j : ℝ) := by
    have : (0 : ℝ) ≤ 1 / (j : ℝ) := div_nonneg zero_le_one (Nat.cast_nonneg _)
    linarith
  have hpair := digitPair_pairLpBound hp2 hr hclass
  have hQ : (Fintype.card (Digit p) : ℝ) ≤ 2 ^ (2 * (e + 16)) := by
    have hcard : Fintype.card (Digit p) = p * p := by
      rw [Fintype.card_prod, ZMod.card, Fintype.card_fin]
    have hle : p * p ≤ 2 ^ (2 * (e + 16)) := by
      rw [two_mul, pow_add]
      exact Nat.mul_le_mul hhi.le hhi.le
    rw [hcard]
    exact_mod_cast hle
  exact drawLaw36_of_pair (digitPairLaw p) (pairB p) (pairA p) hj hbin hQ
    hpair (pairB_uniform hp2) (pairA_uniform hp2)

/-- `lem:density:clique36` on one band `2^b ≤ p < 2^{b+16}`. -/
theorem clique36_band (hp2 : p ≠ 2) (i : Fin 31) (hlo : 2 ^ clique36Band i ≤ p)
    (hhi : p < 2 ^ (clique36Band i + 16))
    (hinterp : SquarePairInterpolation p hp2 (clique36J i)) :
    MixedLpBound (drawLaw (digitPairLaw p) (pairB p) (pairA p) (Fin 36)) (600 / 17) 1 := by
  have hlo' : (2 : ℝ) ^ EdgeGate.bandB i ≤ (p : ℝ) := by
    have : (2 : ℕ) ^ clique36Band i ≤ p := hlo
    exact_mod_cast this
  have hgate := EdgeGate.edge_gate_band i hlo'
  rw [bandJ_eq, ← one_div_pow] at hgate
  exact clique36_of_gates hp2 (two_le_clique36J i) hgate (clique36_binomial_gate i) hhi hinterp

/-- **`lem:density:clique36`.** Let `p` be an odd prime with `2^16 ≤ p < 2^512`, and `j` the
integer of its band `[2^b, 2^{b+16})`. Assume the interpolated centred bound of
`lem:density:edge-moment` at `j` (`SquarePairInterpolation`; for instance, assume it for every
`j ≥ 1`). Then `36` conditionally independent uniform draws from the digit pair `{B, A}` have
unit mixed `L^{600/17}` norm, i.e. density endpoint `51/50`.

Proved from: the band gates `EdgeGate.edge_gate_band` and `Certificates.clique36_binomial_gate`,
the pair moment `EdgeGate.square_pair_moment`, the high-digit averaging, the class bounds and the
typed-mixture lemma (`drawLaw36_of_pair`). -/
theorem clique36 (hp2 : p ≠ 2) (h16 : 2 ^ 16 ≤ p) (h512 : p < 2 ^ 512)
    (hinterp : ∀ i : Fin 31, 2 ^ clique36Band i ≤ p → p < 2 ^ (clique36Band i + 16) →
      SquarePairInterpolation p hp2 (clique36J i)) :
    MixedLpBound (drawLaw (digitPairLaw p) (pairB p) (pairA p) (Fin 36)) (600 / 17) 1 := by
  obtain ⟨i, hlo, hhi⟩ := exists_band h16 h512
  exact clique36_band hp2 i hlo hhi (hinterp i hlo hhi)

end Sarkozy.DensityMoments
