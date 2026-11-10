module

public import Sarkozy.Cancellation.SquareShift
public import Sarkozy.Functional.PrefixModel
public import Sarkozy.Functional.Conductor
public import Sarkozy.Kernel.IndicatorCorollary

@[expose] public section

/-!
# The characters of `X_{𝒮'}` as the frequencies `Ξ_{H,D}`

Step 3 of `lem:record:density-can` (`paper/sections/08_scale_comparison.tex`): "the characters
of `X_{𝒮'}` with `q(ξ) ≤ H` are exactly the elements of `Ξ_{H,D}` (`def:kernel-notation`),
since a squarefree `q ≤ H ≤ N^β` coprime to `D` has all its primes in `𝒮'`", and the pair
multiplier of `lem:square-shift`(d) is the unit quadratic average `g(ξ)` of
`def:kernel-notation`.

For a family of distinct odd primes `p_j`, the character `a` of `X = ∏_j 𝔽_{p_j}` has the
frequency `ξ_a = {∑_j a_j/p_j} ∈ [0, 1)` (`charFreq`; WP-FI's `Sarkozy.Functional.frequency`
before the fractional part). We prove:

* `charFreq_den`: the reduced denominator of `ξ_a` is the conductor `q(a) = ∏_{a_j ≠ 0} p_j`;
* `prodChar_integerResidue_charFreq`: `χ_a(n) = e(n ξ_a)` for `n ∈ ℤ`;
* `pairMultiplier_eq_unitQuadraticAverage`: `λ(a) = g(ξ_a)`;
* `sum_low_eq_sum_frequencySet`: `∑_{q(a) ≤ H} F(ξ_a) = ∑_{ξ ∈ Ξ_{H,D}} F(ξ)` when the `p_j` are
  coprime to `D` and every prime `ℓ ≤ H` with `ℓ ∤ D` is one of the `p_j`.

New material for this paper, on WP-FI's `frequency`, `conductor_eq_den`,
`conductor_eq_supportDenominator`, `prodChar_integerResidue_eq_expPhase` and the CRT means
`periodicMean_prod_coprime` of `Sarkozy.Kernel.CoefficientIdentity`.
-/

namespace Sarkozy.Cancellation

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Finset Complex
open scoped BigOperators ComplexConjugate
open Sarkozy.FourierArithmetic Sarkozy.Functional

variable {K : Type*} [Fintype K] [DecidableEq K] (p : K → ℕ) [∀ j, NeZero (p j)]
  [∀ j, Fact (p j).Prime]

/-- The frequency `ξ_a ∈ [0, 1)` of the character `a`: the fractional part of `∑_j a_j/p_j`. -/
noncomputable def charFreq (a : ResidueSpace p) : ℚ := Int.fract (frequency p a)

omit [Fintype K] [DecidableEq K] [∀ j, NeZero (p j)] in
lemma pairwise_coprime_of_injective (hinj : Function.Injective p) :
    Pairwise fun i j => (p i).Coprime (p j) := fun i j hij =>
  (Nat.coprime_primes (Fact.out : (p i).Prime) (Fact.out : (p j).Prime)).mpr
    (fun h => hij (hinj h))

omit [DecidableEq K] in
/-- `q(ξ_a) = ∏_{a_j ≠ 0} p_j`. -/
lemma charFreq_den (hinj : Function.Injective p) (a : ResidueSpace p) :
    (charFreq p a).den = supportDenominator p a := by
  rw [charFreq, Rat.den_intFract, ← conductor_eq_den p (pairwise_coprime_of_injective p hinj) a,
    conductor_eq_supportDenominator p (fun j => Fact.out) a]

omit [DecidableEq K] [∀ j, NeZero (p j)] [∀ j, Fact (p j).Prime] in
lemma frequency_cast (a : ResidueSpace p) : ((frequency p a : ℚ) : ℝ) = frequencyAngle p a := by
  unfold frequency frequencyAngle
  push_cast
  rfl

omit [DecidableEq K] [∀ j, NeZero (p j)] [∀ j, Fact (p j).Prime] in
lemma expPhase_int_mul_charFreq (a : ResidueSpace p) (n : ℤ) :
    expPhase (n * (charFreq p a : ℝ)) = expPhase (n * frequencyAngle p a) := by
  have h : (n : ℝ) * (charFreq p a : ℝ) =
      n * frequencyAngle p a + ((-(n * ⌊frequency p a⌋) : ℤ) : ℝ) := by
    rw [charFreq, Int.fract, ← frequency_cast]
    push_cast
    ring
  rw [h, expPhase_add, expPhase_int, mul_one]

omit [DecidableEq K] [∀ j, Fact (p j).Prime] in
/-- `χ_a(n) = e(n ξ_a)` for `n ∈ ℤ`. -/
lemma prodChar_integerResidue_charFreq (a : ResidueSpace p) (n : ℤ) :
    prodChar p a (integerResidue p n) = expPhase (n * (charFreq p a : ℝ)) := by
  rw [expPhase_int_mul_charFreq, prodChar_integerResidue_eq_expPhase]

omit [DecidableEq K] [∀ j, Fact (p j).Prime] in
lemma conj_prodChar_integerResidue (a : ResidueSpace p) (n : ℤ) :
    conj (prodChar p a (integerResidue p n)) = expPhase (-(n : ℝ) * (charFreq p a : ℝ)) := by
  rw [prodChar_integerResidue_charFreq, neg_mul, expPhase_neg]

lemma kernel_expPhase_eq (t : ℝ) : Kernel.expPhase t = expPhase t := rfl

/-! ## The multiplier is the unit quadratic average -/

omit [DecidableEq K] in
/-- `e(ξ_a m²) = ∏_{a_j ≠ 0} e(a_j m²/p_j)`. -/
lemma expPhase_charFreq_sq (a : ResidueSpace p) (m : ℕ) :
    Kernel.expPhase ((charFreq p a : ℝ) * (m : ℝ) ^ 2) =
      ∏ j ∈ primeSupport p a, (ZMod.stdAddChar (a j * (m : ZMod (p j)) ^ 2) : ℂ) := by
  classical
  rw [kernel_expPhase_eq]
  have h1 : (charFreq p a : ℝ) * (m : ℝ) ^ 2 = (((m ^ 2 : ℕ) : ℤ) : ℝ) * (charFreq p a : ℝ) := by
    push_cast; ring
  rw [h1, ← prodChar_integerResidue_charFreq]
  have hres : ∀ j, integerResidue p ((m ^ 2 : ℕ) : ℤ) j = (m : ZMod (p j)) ^ 2 := by
    intro j
    simp [integerResidue]
  unfold prodChar
  simp_rw [hres]
  unfold primeSupport
  rw [← prod_filter_mul_prod_filter_not univ (fun j => a j ≠ 0)]
  have hrest : ∏ j ∈ univ.filter (fun j => ¬ a j ≠ 0),
      (ZMod.stdAddChar (a j * (m : ZMod (p j)) ^ 2) : ℂ) = 1 := by
    apply prod_eq_one
    intro j hj
    rw [mem_filter, not_not] at hj
    rw [hj.2, zero_mul, AddChar.map_zero_eq_one]
  rw [hrest, mul_one]

omit [Fintype K] [DecidableEq K] in
lemma sum_ite_ne_zero (q : ℕ) [Fact q.Prime] (f : ZMod q → ℂ) :
    ∑ x : ZMod q, (if x ≠ 0 then f x else 0) = ∑ x : ZMod q, f x - f 0 := by
  rw [← sum_filter, filter_ne', sum_erase_eq_sub (mem_univ _)]

omit [DecidableEq K] in
/-- **The multiplier is the unit quadratic average**: `λ(a) = g(ξ_a)`, the identification used in
Step 3 of `lem:record:density-can` ("with `g(ξ)` the unit quadratic average"). -/
theorem pairMultiplier_eq_unitQuadraticAverage (hinj : Function.Injective p)
    (hodd : ∀ j, p j ≠ 2) (a : ResidueSpace p) :
    pairMultiplier p a = Kernel.unitQuadraticAverage (charFreq p a) := by
  classical
  set S := primeSupport p a with hS
  have hq : (charFreq p a).den = ∏ j ∈ S, p j := charFreq_den p hinj a
  set T : K → ℕ → ℂ := fun j m => if (m : ZMod (p j)) ≠ 0 then
      (ZMod.stdAddChar (a j * (m : ZMod (p j)) ^ 2) : ℂ) else 0 with hT
  set U : K → ℕ → ℂ := fun j m => if (m : ZMod (p j)) ≠ 0 then (1 : ℂ) else 0 with hU
  have hcopiff : ∀ m : ℕ, Nat.Coprime m (∏ j ∈ S, p j) ↔ ∀ j ∈ S, (m : ZMod (p j)) ≠ 0 := by
    intro m
    rw [Nat.coprime_prod_right_iff]
    apply forall₂_congr
    intro j _
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (Fact.out), Ne, ZMod.natCast_eq_zero_iff]
  have hTprod : ∀ m : ℕ, (if Nat.Coprime m (∏ j ∈ S, p j) then
      Kernel.expPhase ((charFreq p a : ℝ) * (m : ℝ) ^ 2) else 0) = ∏ j ∈ S, T j m := by
    intro m
    simp only [hT]
    rw [prod_ite_zero]
    by_cases h : ∀ j ∈ S, (m : ZMod (p j)) ≠ 0
    · rw [ite_eq_left ((hcopiff m).mpr h), ite_eq_left h, expPhase_charFreq_sq]
    · rw [ite_eq_right (fun h' => h ((hcopiff m).mp h')), ite_eq_right h]
  have hUprod : ∀ m : ℕ, (if Nat.Coprime (∏ j ∈ S, p j) m then (1 : ℂ) else 0) =
      ∏ j ∈ S, U j m := by
    intro m
    simp only [hU]
    rw [prod_ite_zero, prod_const_one]
    by_cases h : ∀ j ∈ S, (m : ZMod (p j)) ≠ 0
    · rw [ite_eq_left ((hcopiff m).mpr h).symm, ite_eq_left h]
    · rw [ite_eq_right (fun h' => h ((hcopiff m).mp h'.symm)), ite_eq_right h]
  have hpos : ∀ j ∈ S, 0 < p j := fun j _ => (Fact.out : (p j).Prime).pos
  have hpw : (S : Set K).Pairwise (fun i j => (p i).Coprime (p j)) :=
    fun i _ j _ hij => pairwise_coprime_of_injective p hinj hij
  have hperT : ∀ j ∈ S, Function.Periodic (T j) (p j) := by
    intro j _ m
    simp only [hT, Nat.cast_add, ZMod.natCast_self, add_zero]
  have hperU : ∀ j ∈ S, Function.Periodic (U j) (p j) := by
    intro j _ m
    simp only [hU, Nat.cast_add, ZMod.natCast_self, add_zero]
  have hmT := Kernel.periodicMean_prod_coprime S p hpos hpw T hperT
  have hmU := Kernel.periodicMean_prod_coprime S p hpos hpw U hperU
  have hlocT : ∀ j, Kernel.periodicMean (T j) (p j) =
      ((p j : ℂ))⁻¹ * (quadGauss (q := p j) (a j) - 1) := by
    intro j
    have h := Kernel.expect_zmod_range (q := p j)
      (fun x : ZMod (p j) => if x ≠ 0 then (ZMod.stdAddChar (a j * x ^ 2) : ℂ) else 0)
    rw [← show (fun m : ℕ => (fun x : ZMod (p j) => if x ≠ 0 then
        (ZMod.stdAddChar (a j * x ^ 2) : ℂ) else 0) (m : ZMod (p j))) = T j from rfl, ← h,
      expect_eq_sum_div_card, card_univ, ZMod.card, sum_ite_ne_zero (p j)]
    unfold quadGauss
    rw [zero_pow two_ne_zero, mul_zero, AddChar.map_zero_eq_one, div_eq_inv_mul]
  have hlocU : ∀ j, Kernel.periodicMean (U j) (p j) = ((p j : ℂ))⁻¹ * ((p j : ℂ) - 1) := by
    intro j
    have h := Kernel.expect_zmod_range (q := p j)
      (fun x : ZMod (p j) => if x ≠ 0 then (1 : ℂ) else 0)
    rw [← show (fun m : ℕ => (fun x : ZMod (p j) => if x ≠ 0 then (1 : ℂ) else 0)
        (m : ZMod (p j))) = U j from rfl, ← h,
      expect_eq_sum_div_card, card_univ, ZMod.card, sum_ite_ne_zero (p j)]
    simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_one]
    rw [div_eq_inv_mul]
  -- the unit quadratic average as a ratio of periodic means
  have hQ0 : (∏ j ∈ S, p j) ≠ 0 := prod_ne_zero_iff.mpr (fun j hj => (hpos j hj).ne')
  have hQC : ((∏ j ∈ S, p j : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hQ0
  have hnum : ∑ m ∈ (range (∏ j ∈ S, p j)).filter (fun m => Nat.Coprime m (∏ j ∈ S, p j)),
      Kernel.expPhase ((charFreq p a : ℝ) * (m : ℝ) ^ 2) =
      ((∏ j ∈ S, p j : ℕ) : ℂ) * Kernel.periodicMean (fun n => ∏ j ∈ S, T j n) (∏ j ∈ S, p j) := by
    rw [sum_filter]
    simp_rw [hTprod]
    unfold Kernel.periodicMean
    rw [← mul_assoc, mul_inv_cancel₀ hQC, one_mul]
  have hden : ((Nat.totient (∏ j ∈ S, p j) : ℕ) : ℂ) =
      ((∏ j ∈ S, p j : ℕ) : ℂ) * Kernel.periodicMean (fun n => ∏ j ∈ S, U j n) (∏ j ∈ S, p j) := by
    rw [Nat.totient_eq_card_coprime, natCast_card_filter]
    simp_rw [hUprod]
    unfold Kernel.periodicMean
    rw [← mul_assoc, mul_inv_cancel₀ hQC, one_mul]
  have hp1 : ∀ j, ((p j : ℂ) - 1) ≠ 0 := by
    intro j h0
    have h2 : (2 : ℝ) ≤ p j := by exact_mod_cast (Fact.out : (p j).Prime).two_le
    have h1 : ((p j : ℂ) - 1).re = 0 := by rw [h0]; simp
    simp at h1
    linarith
  have hpC : ∀ j, (p j : ℂ) ≠ 0 := fun j => by exact_mod_cast (Fact.out : (p j).Prime).ne_zero
  unfold Kernel.unitQuadraticAverage
  rw [hq, hnum, hden, hmT, hmU]
  simp_rw [hlocT, hlocU]
  -- the left side
  unfold pairMultiplier
  rw [← prod_filter_mul_prod_filter_not univ (fun j => a j ≠ 0)]
  have hrest : ∏ j ∈ univ.filter (fun j => ¬ a j ≠ 0), shiftEigen p j (a j) = 1 := by
    apply prod_eq_one
    intro j hj
    rw [mem_filter, not_not] at hj
    rw [hj.2, shiftEigen_zero]
  rw [hrest, mul_one]
  have hSdef : univ.filter (fun j => a j ≠ 0) = S := rfl
  rw [hSdef]
  have hloc : ∀ j ∈ S, shiftEigen p j (a j) =
      (((p j : ℂ))⁻¹ * ((p j : ℂ) - 1))⁻¹ * (((p j : ℂ))⁻¹ * (quadGauss (q := p j) (a j) - 1)) := by
    intro j _
    have h := sqAvg_eq (q := p j) (hodd j) (a j)
    change ((sqSetZ (p j)).card : ℂ)⁻¹ * ∑ u ∈ sqSetZ (p j), (ZMod.stdAddChar (a j * u) : ℂ) = _
    rw [h]
    field_simp [hpC j, hp1 j]
  rw [prod_congr rfl hloc, prod_mul_distrib, prod_inv_distrib, mul_inv]
  have key : ∀ (q X Y : ℂ), q ≠ 0 → X⁻¹ * Y = q⁻¹ * X⁻¹ * (q * Y) := by
    intro q X Y hq0
    rw [show q⁻¹ * X⁻¹ * (q * Y) = (q⁻¹ * q) * (X⁻¹ * Y) by ring, inv_mul_cancel₀ hq0, one_mul]
  exact key _ _ _ hQC

/-! ## The low characters are the frequencies `Ξ_{H,D}` -/

omit [DecidableEq K] in
lemma charFreq_injective (hinj : Function.Injective p) : Function.Injective (charFreq p) := by
  intro a b h
  apply frequencyAngle_separates p (pairwise_coprime_of_injective p hinj) a b
  unfold charFreq Int.fract at h
  have h3 : frequency p a - frequency p b = ((⌊frequency p a⌋ - ⌊frequency p b⌋ : ℤ) : ℚ) := by
    push_cast; linarith
  have h1 : frequencyAngle p a - frequencyAngle p b =
      ((⌊frequency p a⌋ - ⌊frequency p b⌋ : ℤ) : ℝ) := by
    rw [← frequency_cast, ← frequency_cast]
    exact_mod_cast h3
  rw [h1, expPhase_int]

omit [DecidableEq K] in
lemma charFreq_mem_frequencySet (hinj : Function.Injective p) {H : ℝ} (hH : 0 ≤ H) (D : ℕ)
    (hcopD : ∀ j, Nat.Coprime (p j) D) (a : ResidueSpace p)
    (ha : (supportDenominator p a : ℝ) ≤ H) :
    charFreq p a ∈ Kernel.frequencySet H D := by
  classical
  rw [Kernel.mem_frequencySet hH, charFreq_den p hinj]
  refine ⟨Int.fract_nonneg _, Int.fract_lt_one _, ha, ?_, ?_⟩
  · exact Kernel.squarefree_prod_primes p hinj (primeSupport p a)
  · exact Nat.Coprime.prod_left (fun j _ => hcopD j)

/-- A rational `x ∈ [0, 1)` whose denominator divides `q` is some `k/q`, `0 ≤ k < q`. -/
lemma mem_image_range_div (q : ℕ) (hq : 0 < q) (x : ℚ) (h0 : 0 ≤ x) (h1 : x < 1)
    (hd : x.den ∣ q) : x ∈ (range q).image (fun k : ℕ => (k : ℚ) / q) := by
  obtain ⟨t, ht⟩ := hd
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  set k : ℤ := x.num * t with hk
  have hxq : x * q = k := by
    rw [hk, ht]
    push_cast
    rw [← mul_assoc, Rat.mul_den_eq_num]
  have hk0 : 0 ≤ k := by
    have : (0 : ℚ) ≤ k := by rw [← hxq]; positivity
    exact_mod_cast this
  have hkq : k < q := by
    have : (k : ℚ) < q := by rw [← hxq]; nlinarith
    exact_mod_cast this
  rw [mem_image]
  refine ⟨k.toNat, mem_range.mpr (by omega), ?_⟩
  have hcast : ((k.toNat : ℕ) : ℚ) = (k : ℚ) := by
    rw [show ((k.toNat : ℕ) : ℚ) = ((k.toNat : ℤ) : ℚ) by push_cast; rfl, Int.toNat_of_nonneg hk0]
  rw [hcast, ← hxq]
  field_simp

omit [DecidableEq K] in
lemma exists_charFreq_eq (hinj : Function.Injective p) {H : ℝ} (hH : 0 ≤ H) (D : ℕ)
    (hcover : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℝ) ≤ H → ¬ ℓ ∣ D → ∃ j, p j = ℓ)
    (ξ : ℚ) (hξ : ξ ∈ Kernel.frequencySet H D) :
    ∃ a : ResidueSpace p, (supportDenominator p a : ℝ) ≤ H ∧ charFreq p a = ξ := by
  classical
  rw [Kernel.mem_frequencySet hH] at hξ
  obtain ⟨h0, h1, hden, hsq, hcop⟩ := hξ
  set q := ξ.den with hqdef
  have hq0 : 0 < q := ξ.pos
  set B := univ.filter (fun j => p j ∣ q) with hB
  have hqB : ∏ j ∈ B, p j = q := by
    rw [← Nat.prod_primeFactors_of_squarefree hsq]
    apply Finset.prod_nbij p
    · intro j hj
      rw [mem_filter] at hj
      exact Nat.mem_primeFactors.mpr ⟨Fact.out, hj.2, hq0.ne'⟩
    · intro i _ j _ h
      exact hinj h
    · intro ℓ hℓ
      obtain ⟨hℓp, hℓq, _⟩ := Nat.mem_primeFactors.mp hℓ
      have hℓH : (ℓ : ℝ) ≤ H := le_trans (by exact_mod_cast Nat.le_of_dvd hq0 hℓq) hden
      have hℓD : ¬ ℓ ∣ D := by
        intro h
        have h2 := Nat.dvd_gcd hℓq h
        rw [hcop.gcd_eq_one] at h2
        exact hℓp.one_lt.ne' (Nat.dvd_one.mp h2)
      obtain ⟨j, rfl⟩ := hcover ℓ hℓp hℓH hℓD
      exact ⟨j, by simp [hB, hℓq], rfl⟩
    · intro j _
      rfl
  set A := Fintype.piFinset (fun j => if j ∈ B then (univ : Finset (ZMod (p j))) else {0})
    with hA
  have hcardA : A.card = q := by
    rw [hA, Fintype.card_piFinset]
    have h : ∀ j, (if j ∈ B then (univ : Finset (ZMod (p j))) else {0}).card =
        if j ∈ B then p j else 1 := by
      intro j
      split_ifs <;> simp
    simp_rw [h]
    rw [← prod_filter]
    have hfB : univ.filter (fun j => j ∈ B) = B := by ext j; simp
    rw [hfB, hqB]
  set R := (range q).image (fun k : ℕ => (k : ℚ) / q) with hR
  have hcardR : R.card = q := by
    rw [hR, card_image_of_injective, card_range]
    intro k₁ k₂ h
    have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq0.ne'
    have h' : (k₁ : ℚ) = k₂ := by
      have := congrArg (fun x : ℚ => x * q) h
      simpa [div_mul_cancel₀ _ hqQ] using this
    exact_mod_cast h'
  have hmaps : ∀ a ∈ A, charFreq p a ∈ R := by
    intro a ha
    rw [hA, Fintype.mem_piFinset] at ha
    apply mem_image_range_div q hq0 _ (Int.fract_nonneg _) (Int.fract_lt_one _)
    show (charFreq p a).den ∣ q
    rw [charFreq_den p hinj, ← hqB]
    apply prod_dvd_prod_of_subset
    intro j hj
    by_contra hjB
    have := ha j
    rw [ite_eq_right hjB, mem_singleton] at this
    exact (mem_filter.mp hj).2 this
  have hξR : ξ ∈ R := mem_image_range_div q hq0 ξ h0 h1 dvd_rfl
  obtain ⟨a, _, hξa⟩ := surj_on_of_inj_on_of_card_le (fun a _ => charFreq p a)
    (fun a ha => hmaps a ha) (fun a₁ a₂ _ _ h => charFreq_injective p hinj h)
    (by rw [hcardA, hcardR]) ξ hξR
  refine ⟨a, ?_, hξa.symm⟩
  rw [← charFreq_den p hinj, ← hξa]
  exact hden

/-- **The low characters are `Ξ_{H,D}`** (Step 3 of `lem:record:density-can`): when the `p_j`
are coprime to `D` and every prime `ℓ ≤ H` with `ℓ ∤ D` is one of them,
`a ↦ ξ_a` is a bijection from `{q(a) ≤ H}` onto `Ξ_{H,D}`. -/
theorem sum_low_eq_sum_frequencySet (hinj : Function.Injective p) {H : ℝ} (hH : 0 ≤ H) (D : ℕ)
    (hcopD : ∀ j, Nat.Coprime (p j) D)
    (hcover : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℝ) ≤ H → ¬ ℓ ∣ D → ∃ j, p j = ℓ) (F : ℚ → ℂ) :
    ∑ a ∈ univ.filter (fun a : ResidueSpace p => (supportDenominator p a : ℝ) ≤ H),
        F (charFreq p a) = ∑ ξ ∈ Kernel.frequencySet H D, F ξ := by
  classical
  apply Finset.sum_nbij (charFreq p)
  · intro a ha
    exact charFreq_mem_frequencySet p hinj hH D hcopD a (mem_filter.mp ha).2
  · intro a _ b _ h
    exact charFreq_injective p hinj h
  · intro ξ hξ
    obtain ⟨a, ha, rfl⟩ := exists_charFreq_eq p hinj hH D hcover ξ hξ
    exact ⟨a, by simp [ha], rfl⟩
  · intro a _
    rfl

end Sarkozy.Cancellation
