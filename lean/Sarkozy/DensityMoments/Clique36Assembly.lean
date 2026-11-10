module

public import Sarkozy.DensityMoments.ChoiceClasses
public import Sarkozy.Certificates.Clique36Gates

/-!
# Thirty-six draws from a two-element clique: the assembly (`lem:density:clique36`)

`paper/sections/30_density_moment_upgrade.tex`, proof of `lem:density:clique36`. Here the pair
`(a ω, b ω)` is arbitrary, on any finite alphabet `X` of size `Q`; the digit-pair law is the
instance of `Sarkozy/DensityMoments/Clique36.lean`.

`drawLaw36_of_pair`: fix a band exponent `e` and an integer `j ≥ 2`, put `r = 1 + 1/j`,
`s = 18 r`, `R = 600/17`, `κ = s/R`. Assume

* the pair `(a, b)` has unit mixed `L^r` (`PairLpBound`), and `a`, `b` are uniform on `X`;
* `Q ≤ 2^{2(e+16)}`;
* the binomial test `eq:density:clique-binomial-gate` holds at `(e, j)` (the rational
  `Certificates.clique36BinomialCharge e j ≤ 95659840/13884957009`).

Then 36 conditionally independent draws from `{a ω, b ω}` have unit mixed `L^{600/17}`.

The proof is the paper's: expand into choice vectors (`expect_drawLaw_eq_mixture`); the class of
minority count `k` has unit mixed `L^{v_k}` with `v_k = Certificates.clique36V j k`
(`classLaw_mixed_pair`, `classLaw_uniformMarginals`); the balanced class (`k = 18`) has
`v_{18} = s`; then the typed-mixture lemma with coarse charges
(`Sarkozy.mixedLpBound_typed_mixture_coarse`), whose charge `typedCost` is bounded on the band by
the summand of the binomial test (`typedCost_le_band`).

The denominator test `eq:density:clique-denominator`, and the lower end `Q ≥ 2^{2e}` of the band
that it uses, are not needed: the paper uses them only to justify the coarse form
`C_v(Q) ≤ (2d/(κv)) Q^{d/R-d/v}`, which `Moments/CoarseDeficit.lean` proves for every `Q` with a
constant `coarseGapConstant`, equal to `2/κ` here (`coarseGapConstant_le`).
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.DensityMoments

open Certificates CliqueCopies

theorem clique36R_real : ((clique36R : ℚ) : ℝ) = 600 / 17 := by
  norm_num [clique36R]

theorem clique36s_real (j : ℕ) : ((clique36s j : ℚ) : ℝ) = 18 * (1 + 1 / (j : ℝ)) := by
  simp [clique36s, clique36r]

theorem inv_le_half {j : ℕ} (hj : 2 ≤ j) : 1 / (j : ℚ) ≤ 1 / 2 := by
  have : (2 : ℚ) ≤ j := by exact_mod_cast hj
  exact one_div_le_one_div_of_le (by norm_num) this

theorem clique36V_pos {j : ℕ} (hj : 2 ≤ j) {k : ℕ} (hk : k ≤ 18) : 0 < clique36V j k := by
  have hj0 : (0 : ℚ) < 1 / (j : ℚ) := by
    have : (0 : ℚ) < j := by exact_mod_cast (show 0 < j by omega)
    positivity
  have hk' : (k : ℚ) ≤ 18 := by exact_mod_cast hk
  unfold clique36V clique36r
  split_ifs
  · norm_num
  · exact lt_min (by norm_num) (mul_pos (by linarith) (by linarith))

theorem clique36V_le {j k : ℕ} : clique36V j k ≤ 36 := by
  unfold clique36V
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem clique36V_eighteen {j : ℕ} (hj : 2 ≤ j) : clique36V j 18 = clique36s j := by
  have h := inv_le_half hj
  unfold clique36V clique36s clique36r
  simp only [show (18 : ℕ) ≠ 0 by norm_num, ↓reduceIte]
  rw [min_eq_right (by push_cast; linarith)]
  push_cast
  ring

theorem clique36s_lt_R {j : ℕ} (hj : 2 ≤ j) : clique36s j < clique36R := by
  have h := inv_le_half hj
  unfold clique36s clique36r clique36R
  linarith

theorem clique36s_pos (j : ℕ) : 0 < clique36s j := by
  unfold clique36s clique36r
  have : (0 : ℚ) ≤ 1 / (j : ℚ) := by positivity
  linarith

/-- **The coarse charge on a band**: for `v ∈ (R, 36]` and `Q ≤ 2^{2(e+16)}`, the charge
`typedCost s R v 36 Q` of the typed-mixture lemma is at most the summand
`72/(κ v) · 2^⌈2(e+16)(θ - 36/v)⌉` of `eq:density:clique-binomial-gate`. -/
theorem typedCost_le_band {j : ℕ} (hj : 2 ≤ j) {e Q : ℕ} (hQ : (Q : ℝ) ≤ 2 ^ (2 * (e + 16)))
    {v : ℚ} (hRv : clique36R < v) (hv : v ≤ 36) :
    typedCost (clique36s j) (clique36R) v 36 Q ≤
      ((72 / (clique36Kappa j * v) *
        (2 : ℚ) ^ ⌈2 * ((e : ℚ) + 16) * (clique36Theta - 36 / v)⌉ : ℚ) : ℝ) := by
  have hR := clique36R_real
  have hs := clique36s_real j
  have hjr : (2 : ℝ) ≤ j := by exact_mod_cast hj
  set u : ℝ := 1 / (j : ℝ) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu1 : u ≤ 1 / 2 := by
    rw [hu]
    exact one_div_le_one_div_of_le (by norm_num) hjr
  have hvR : (600 / 17 : ℝ) < v := by rw [← hR]; exact_mod_cast hRv
  have hv36 : (v : ℝ) ≤ 36 := by exact_mod_cast hv
  have hv0 : (0 : ℝ) < v := by linarith
  set κ : ℝ := ((clique36s j : ℚ) : ℝ) / ((clique36R : ℚ) : ℝ) with hκdef
  have hκ : κ = 51 / 100 * (1 + u) := by rw [hκdef, hs, hR]; ring
  set ℓ : ℝ := (v : ℝ) / ((clique36R : ℚ) : ℝ) with hℓdef
  have hℓ1 : 1 < ℓ := by rw [hℓdef, hR, one_lt_div (by norm_num)]; exact hvR
  have hℓ2 : ℓ ≤ 51 / 50 := by rw [hℓdef, hR, div_le_iff₀ (by norm_num)]; linarith
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  have hκ1 : κ < 1 := by rw [hκ]; linarith
  have hcoarse : coarseGapConstant κ ℓ ≤ 2 / κ := by
    apply coarseGapConstant_le hκ0 hκ1 hℓ1 (by rw [hκ]; linarith)
    have hL : 2 * ℓ * (ℓ - 1) ≤ 2 * (51 / 50) * (1 / 50) := by nlinarith
    have h1 : 51 / 100 ≤ κ := by rw [hκ]; nlinarith
    have h2 : 47 / 200 ≤ 1 - κ := by rw [hκ]; linarith
    have h3 : (51 / 100 : ℝ) ^ 2 ≤ κ ^ 2 := by nlinarith
    have h4 : (51 / 100 : ℝ) ^ 2 * (47 / 200) ≤ κ ^ 2 * (1 - κ) :=
      mul_le_mul h3 h2 (by norm_num) (by positivity)
    nlinarith
  -- the power of `Q`
  set x : ℝ := ((36 : ℕ) : ℝ) / ((clique36R : ℚ) : ℝ) - ((36 : ℕ) : ℝ) / (v : ℝ) with hxdef
  have hx0 : 0 ≤ x := by
    rw [hxdef, sub_nonneg]
    apply div_le_div_of_nonneg_left (by norm_num) (by rw [hR]; norm_num)
    rw [hR]
    exact hvR.le
  set y : ℚ := 2 * ((e : ℚ) + 16) * (clique36Theta - 36 / v) with hydef
  have hxy : ((2 * (e + 16) : ℕ) : ℝ) * x = (y : ℝ) := by
    rw [hxdef, hydef, hR]
    push_cast
    unfold clique36Theta
    push_cast
    ring
  have hpow : (Q : ℝ) ^ x ≤ (2 : ℝ) ^ ⌈y⌉ := by
    calc (Q : ℝ) ^ x ≤ ((2 : ℝ) ^ (2 * (e + 16))) ^ x :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hQ hx0
      _ = (2 : ℝ) ^ (((2 * (e + 16) : ℕ) : ℝ) * x) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      _ ≤ (2 : ℝ) ^ (((⌈y⌉ : ℤ) : ℝ)) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          rw [hxy]
          exact_mod_cast Int.le_ceil y
      _ = (2 : ℝ) ^ ⌈y⌉ := Real.rpow_intCast 2 _
  have hcast : ((72 / (clique36Kappa j * v) * (2 : ℚ) ^ ⌈y⌉ : ℚ) : ℝ) =
      72 / (κ * (v : ℝ)) * (2 : ℝ) ^ ⌈y⌉ := by
    rw [hκdef]
    unfold clique36Kappa
    push_cast
    ring
  rw [hcast]
  unfold typedCost
  rw [← hκdef, ← hℓdef, ← hxdef]
  calc ((36 : ℕ) : ℝ) / (v : ℝ) * coarseGapConstant κ ℓ * (Q : ℝ) ^ x
      ≤ ((36 : ℕ) : ℝ) / (v : ℝ) * (2 / κ) * (2 : ℝ) ^ ⌈y⌉ := by
        apply mul_le_mul _ hpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity)
        exact mul_le_mul_of_nonneg_left hcoarse (by positivity)
    _ = 72 / (κ * (v : ℝ)) * (2 : ℝ) ^ ⌈y⌉ := by
        push_cast
        field_simp
        ring

section Assembly

variable {Ω X : Type*} [Fintype Ω] [Fintype X] [DecidableEq X] (μ : FiniteLaw Ω) (a b : Ω → X)

/-- The minority count of a choice vector of `36` coins. -/
def minorityCount (c : Fin 36 → Bool) : ℕ := min (trueCount c) (36 - trueCount c)

theorem minorityCount_le (c : Fin 36 → Bool) : minorityCount c ≤ 18 := by
  unfold minorityCount
  omega

/-- **The class bounds**: the class of minority count `k` has unit mixed `L^{v_k}`. -/
theorem classLaw_mixed_v [Nonempty X] {j : ℕ} (hj : 2 ≤ j)
    (hpair : PairLpBound μ a b (1 + 1 / (j : ℝ)))
    (ha : ∀ g : X → ℝ, μ.expect (fun ω => g (a ω)) = (FiniteLaw.uniform X).expect g)
    (hb : ∀ g : X → ℝ, μ.expect (fun ω => g (b ω)) = (FiniteLaw.uniform X).expect g)
    (c : Fin 36 → Bool) :
    MixedLpBound (classLaw μ a b c) ((clique36V j (minorityCount c) : ℚ) : ℝ) 1 := by
  have h36 : MixedLpBound (classLaw μ a b c) 36 1 := by
    have h := mixedLpBound_of_uniform_marginals (classLaw μ a b c)
      (classLaw_uniformMarginals μ a b c ha hb)
    simpa using h
  have hr : (0 : ℝ) < 1 + 1 / (j : ℝ) := by positivity
  set m := trueCount c with hm
  have hm36 : m ≤ 36 := trueCount_le c
  set k := minorityCount c with hk
  have hkm : k ≤ m := by rw [hk]; unfold minorityCount; omega
  have hkm' : m ≤ 36 - k := by rw [hk]; unfold minorityCount; omega
  have hk18 : k ≤ 18 := minorityCount_le c
  unfold clique36V
  by_cases hk0 : k = 0
  · simp only [hk0, ↓reduceIte, Rat.cast_ofNat]
    exact h36
  · simp only [hk0, ↓reduceIte]
    rcases le_total (36 : ℚ) ((36 - (k : ℚ)) * clique36r j) with h | h
    · rw [min_eq_left h]
      simpa using h36
    · rw [min_eq_right h]
      apply classLaw_mixed_pair μ a b c hr hpair
      · have : (m : ℝ) ≤ 36 - (k : ℝ) := by
          have := (Nat.cast_le (α := ℝ)).mpr hkm'
          push_cast [Nat.cast_sub (show k ≤ 36 by omega)] at this
          linarith
        unfold clique36r
        push_cast
        exact mul_le_mul_of_nonneg_right this hr.le
      · rw [falseCount_eq]
        have : ((36 - m : ℕ) : ℝ) ≤ 36 - (k : ℝ) := by
          rw [Nat.cast_sub hm36]
          have := (Nat.cast_le (α := ℝ)).mpr hkm
          push_cast
          linarith
        unfold clique36r
        push_cast
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) hr.le

/-- The weight of a coin vector. -/
theorem coins_weight (c : Fin 36 → Bool) : (coins (Fin 36)).weight c = ((2 : ℝ) ^ 36)⁻¹ := by
  simp [coins, coin, FiniteLaw.pi, FiniteLaw.uniform]

/-- The exponent assigned to a choice vector: `v_k` at its minority count `k`. -/
noncomputable def classExponent (j : ℕ) (c : Fin 36 → Bool) : ℝ :=
  ((clique36V j (minorityCount c) : ℚ) : ℝ)

/-- The balanced classes (eighteen of each label) carry the anchor weight `C(36,18)/2^36` and
have exponent `s`. -/
theorem balance_right {j : ℕ} (hj : 2 ≤ j) :
    ((clique36AnchorWeight : ℚ) : ℝ) ≤
      ∑ c ∈ univ.filter (fun c => classExponent j c ≤ ((clique36s j : ℚ) : ℝ)),
        (coins (Fin 36)).weight c := by
  calc ((clique36AnchorWeight : ℚ) : ℝ) =
        ∑ _c ∈ univ.filter (fun c : Fin 36 → Bool => trueCount c = 18), ((2 : ℝ) ^ 36)⁻¹ := by
        rw [sum_const, card_choice_count, nsmul_eq_mul, clique36AnchorWeight, Rat.cast_div,
          Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat, div_eq_mul_inv]
    _ ≤ ∑ c ∈ univ.filter (fun c => classExponent j c ≤ ((clique36s j : ℚ) : ℝ)),
          ((2 : ℝ) ^ 36)⁻¹ := by
        refine sum_le_sum_of_subset_of_nonneg (Finset.monotone_filter_right _ ?_)
          (fun _ _ _ => by positivity)
        intro c _ hc
        have hk : minorityCount c = 18 := by
          unfold minorityCount
          rw [show trueCount c = 18 from hc]
          rfl
        show classExponent j c ≤ _
        rw [classExponent, hk, clique36V_eighteen hj]
    _ = _ := sum_congr rfl fun c _ => (coins_weight c).symm

/-- The charge of minority count `k` in the typed-mixture balance. -/
noncomputable def classCharge (j Q : ℕ) (k : ℕ) : ℝ :=
  if ((clique36R : ℚ) : ℝ) < ((clique36V j k : ℚ) : ℝ) then
    typedCost (clique36s j) (clique36R) (clique36V j k) 36 Q else 0

/-- The summand of the binomial test at minority count `k`. -/
noncomputable def gateSummand (j e : ℕ) (k : ℕ) : ℝ :=
  if clique36R < clique36V j k then
    ((72 / (clique36Kappa j * clique36V j k) *
      (2 : ℚ) ^ ⌈2 * ((e : ℚ) + 16) * (clique36Theta - 36 / clique36V j k)⌉ : ℚ) : ℝ)
  else 0

theorem classCharge_le {j e Q : ℕ} (hj : 2 ≤ j) (hQ : (Q : ℝ) ≤ 2 ^ (2 * (e + 16))) (k : ℕ) :
    classCharge j Q k ≤ gateSummand j e k := by
  unfold classCharge gateSummand
  by_cases hk : clique36R < clique36V j k
  · have hk' : ((clique36R : ℚ) : ℝ) < ((clique36V j k : ℚ) : ℝ) := by exact_mod_cast hk
    simp only [hk, hk', ↓reduceIte]
    exact typedCost_le_band hj hQ hk clique36V_le
  · have hk' : ¬ ((clique36R : ℚ) : ℝ) < ((clique36V j k : ℚ) : ℝ) := by exact_mod_cast hk
    simp only [hk, hk', ↓reduceIte, le_refl]

theorem classCharge_eighteen {j Q : ℕ} (hj : 2 ≤ j) : classCharge j Q 18 = 0 := by
  unfold classCharge
  rw [clique36V_eighteen hj]
  have hsR : ((clique36s j : ℚ) : ℝ) < ((clique36R : ℚ) : ℝ) := by
    exact_mod_cast clique36s_lt_R hj
  have : ¬ ((clique36R : ℚ) : ℝ) < ((clique36s j : ℚ) : ℝ) := not_lt.mpr hsR.le
  simp only [this, ↓reduceIte]

/-- The left side of the balance, grouped by minority count. -/
theorem balance_left_eq {j Q : ℕ} (hj : 2 ≤ j) :
    ∑ c ∈ univ.filter (fun c => ((clique36R : ℚ) : ℝ) < classExponent j c),
        (coins (Fin 36)).weight c *
          typedCost (clique36s j) (clique36R) (classExponent j c) 36 Q =
      ((2 : ℝ) ^ 36)⁻¹ * ∑ k ∈ range 18, 2 * ((Nat.choose 36 k : ℕ) : ℝ) * classCharge j Q k := by
  rw [sum_filter]
  have h1 : ∀ c : Fin 36 → Bool, (if ((clique36R : ℚ) : ℝ) < classExponent j c then
      (coins (Fin 36)).weight c * typedCost (clique36s j) (clique36R) (classExponent j c) 36 Q
        else 0) =
      ((2 : ℝ) ^ 36)⁻¹ * classCharge j Q (min (trueCount c) (36 - trueCount c)) := by
    intro c
    simp only [classExponent, classCharge, coins_weight, minorityCount, mul_ite, mul_zero]
  rw [sum_congr rfl fun c _ => h1 c, ← mul_sum,
    sum_choice_count 36 (fun m => classCharge j Q (min m (36 - m))), sum_range_fold,
    classCharge_eighteen hj, mul_zero, add_zero]

theorem anchor_pos : (0 : ℚ) < clique36AnchorWeight := by
  unfold clique36AnchorWeight
  have := Nat.choose_pos (show 18 ≤ 36 by norm_num)
  positivity

/-- The binomial test in real form. -/
theorem gate_sum_eq (j e : ℕ) :
    ((2 : ℝ) ^ 36)⁻¹ * ∑ k ∈ range 18, 2 * ((Nat.choose 36 k : ℕ) : ℝ) * gateSummand j e k =
      ((clique36AnchorWeight * clique36BinomialCharge e j : ℚ) : ℝ) := by
  have hcharge : clique36AnchorWeight * clique36BinomialCharge e j =
      ∑ k ∈ (range 18).filter (fun k => clique36R < clique36V j k),
        clique36W k * (72 / (clique36Kappa j * clique36V j k)) *
          (2 : ℚ) ^ ⌈2 * ((e : ℚ) + 16) * (clique36Theta - 36 / clique36V j k)⌉ := by
    unfold clique36BinomialCharge
    rw [← mul_assoc, mul_one_div_cancel anchor_pos.ne', one_mul]
  rw [hcharge, Rat.cast_sum, sum_filter, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  unfold gateSummand
  split_ifs
  · unfold clique36W
    push_cast
    ring
  · ring

theorem gate_final {j e : ℕ}
    (hgate : clique36BinomialCharge e j ≤ 95659840 / 13884957009) :
    ((clique36AnchorWeight * clique36BinomialCharge e j : ℚ) : ℝ) ≤
      ((clique36AnchorWeight : ℚ) : ℝ) := by
  have h1 : clique36AnchorWeight * clique36BinomialCharge e j ≤ clique36AnchorWeight := by
    have h2 := mul_le_mul_of_nonneg_left hgate anchor_pos.le
    have h3 : clique36AnchorWeight * (95659840 / 13884957009) ≤ clique36AnchorWeight := by
      have := clique36_binomial_gate_lt_one
      have := anchor_pos
      nlinarith
    linarith
  exact_mod_cast h1

/-- **The typed-mixture balance on a band**: the charges of the classes above `R` are paid by
the balanced classes. -/
theorem clique36_balance {j e Q : ℕ} (hj : 2 ≤ j)
    (hgate : clique36BinomialCharge e j ≤ 95659840 / 13884957009)
    (hQ : (Q : ℝ) ≤ 2 ^ (2 * (e + 16))) :
    ∑ c ∈ univ.filter (fun c => ((clique36R : ℚ) : ℝ) < classExponent j c),
        (coins (Fin 36)).weight c *
          typedCost (clique36s j) (clique36R) (classExponent j c) 36 Q ≤
      ∑ c ∈ univ.filter (fun c => classExponent j c ≤ ((clique36s j : ℚ) : ℝ)),
        (coins (Fin 36)).weight c := by
  rw [balance_left_eq hj]
  calc ((2 : ℝ) ^ 36)⁻¹ * ∑ k ∈ range 18, 2 * ((Nat.choose 36 k : ℕ) : ℝ) * classCharge j Q k
      ≤ ((2 : ℝ) ^ 36)⁻¹ * ∑ k ∈ range 18, 2 * ((Nat.choose 36 k : ℕ) : ℝ) *
          gateSummand j e k := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (classCharge_le hj hQ k)
          (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    _ = ((clique36AnchorWeight * clique36BinomialCharge e j : ℚ) : ℝ) := gate_sum_eq j e
    _ ≤ ((clique36AnchorWeight : ℚ) : ℝ) := gate_final hgate
    _ ≤ _ := balance_right hj

/-- **`lem:density:clique36` for an arbitrary random pair**, on one band: if the pair has unit
mixed `L^{1+1/j}` and uniform coordinates, the alphabet has at most `2^{2(e+16)}` letters and the
binomial test holds at `(e, j)`, then `36` draws have unit mixed `L^{600/17}`. -/
theorem drawLaw36_of_pair [Nonempty X] {j e : ℕ} (hj : 2 ≤ j)
    (hgate : clique36BinomialCharge e j ≤ 95659840 / 13884957009)
    (hQ : (Fintype.card X : ℝ) ≤ 2 ^ (2 * (e + 16)))
    (hpair : PairLpBound μ a b (1 + 1 / (j : ℝ)))
    (ha : ∀ g : X → ℝ, μ.expect (fun ω => g (a ω)) = (FiniteLaw.uniform X).expect g)
    (hb : ∀ g : X → ℝ, μ.expect (fun ω => g (b ω)) = (FiniteLaw.uniform X).expect g) :
    MixedLpBound (drawLaw μ a b (Fin 36)) (600 / 17) 1 := by
  apply mixedLpBound_of_expect_eq (expect_drawLaw_eq_mixture μ a b (Fin 36))
  rw [← clique36R_real]
  have hsR : ((clique36s j : ℚ) : ℝ) < ((clique36R : ℚ) : ℝ) := by
    exact_mod_cast clique36s_lt_R hj
  have hs0 : (0 : ℝ) < ((clique36s j : ℚ) : ℝ) := by exact_mod_cast clique36s_pos j
  apply mixedLpBound_typed_mixture_coarse (coins (Fin 36)) (classLaw μ a b) (classExponent j)
    hs0 hsR
  · intro c
    unfold classExponent
    exact_mod_cast clique36V_pos hj (minorityCount_le c)
  · intro c
    rw [Fintype.card_fin]
    unfold classExponent
    exact_mod_cast clique36V_le
  · exact classLaw_mixed_v μ a b hj hpair ha hb
  · rw [Fintype.card_fin]
    exact clique36_balance hj hgate hQ

end Assembly

end Sarkozy.DensityMoments
