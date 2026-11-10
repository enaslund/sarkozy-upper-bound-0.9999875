module

public import Sarkozy.Kernel.FiniteKernel

@[expose] public section

/-!
# The arithmetic coefficient of the model kernel

This module identifies the major-arc coefficient of the upstream model kernel
(`kernelModelCoefficient`, built from the complete root/unit weight) with the
coefficient of the paper's model kernel. In the notation of the paper
(`def:kernel-notation`, `lem:record:K20-centres`, `lem:record:kernel-coefficient`):
the model kernel has centres `j/D + ξ` with `j mod D` and `ξ ∈ Ξ_{H,D}`, and
coefficient `e(j r/D) g(ξ)`, where `g` is the unit quadratic average.

Main results:

* `unitQuadraticAverage`: the paper's `g(ξ) = φ(q)⁻¹ ∑_{m ∈ (ℤ/q)ˣ} e(ξ m²)`,
  `q = q(ξ)`, with the units represented by `0 ≤ m < q`, `gcd(m,q) = 1`.
* `frequencySet`: the paper's `Ξ_{H,D}`, represented by its elements in `[0,1)`.
* `completeRationalCoefficient_centre`: the complete coefficient at `j/D + ξ`
  equals `e(j r/D) g(ξ)` (the case `q₁ ≤ H` of `lem:record:kernel-coefficient`).
* `kernelModelCoefficient_centre`, `kernelModelCoefficient_eq_zero_of_not_centre`,
  `model_sum_reindex`: the upstream model coefficient is supported on the paper's
  centres and equals the paper's coefficient there.

New material for this paper; it uses the upstream definitions of
`FiniteKernel.lean`, `CircleDistance.lean`, `CompleteWeights.lean`
(OpenAI, Apache-2.0) and the lemma `primaryModelCoefficient_denominator`.
-/

namespace Sarkozy

section
open Finset
open scoped ComplexConjugate BigOperators
namespace Kernel

/-! ## Means of periodic functions under the Chinese remainder theorem -/

lemma periodic_eq_val_cast (f : ℕ → ℂ) (A : ℕ) [NeZero A] (hf : Function.Periodic f A)
    (n : ℕ) : f n = f ((n : ZMod A).val) := by
  rw [ZMod.val_natCast]
  exact (periodic_nat_mod f A hf n).symm

lemma periodicMean_eq_expect_val (f : ℕ → ℂ) (A : ℕ) [NeZero A] (hf : Function.Periodic f A) :
    periodicMean f A = 𝔼 x : ZMod A, f x.val := by
  rw [expect_zmod_range]
  congr 1
  funext n
  exact periodic_eq_val_cast f A hf n

lemma periodic_mul_of_dvd {f : ℕ → ℂ} {A t : ℕ} (hf : Function.Periodic f A) (h : A ∣ t) :
    Function.Periodic f t := by
  obtain ⟨k, rfl⟩ := h
  intro n
  simpa [nsmul_eq_mul, Nat.cast_id, Nat.mul_comm] using (hf.nsmul k) n

lemma periodicMean_mul_coprime {A B : ℕ} [NeZero A] [NeZero B] (hAB : A.Coprime B)
    (f g : ℕ → ℂ) (hf : Function.Periodic f A) (hg : Function.Periodic g B) :
    periodicMean (fun n => f n * g n) (A * B) = periodicMean f A * periodicMean g B := by
  have : NeZero (A * B) := ⟨Nat.mul_ne_zero (NeZero.ne A) (NeZero.ne B)⟩
  have hfg : Function.Periodic (fun n => f n * g n) (A * B) :=
    (periodic_mul_of_dvd hf (dvd_mul_right A B)).mul (periodic_mul_of_dvd hg (dvd_mul_left B A))
  rw [periodicMean_eq_expect_val _ _ hfg, periodicMean_eq_expect_val f A hf,
    periodicMean_eq_expect_val g B hg]
  have hx (x : ZMod (A * B)) : f x.val * g x.val =
      (fun y : ZMod A × ZMod B => f y.1.val * g y.2.val) (ZMod.chineseRemainder hAB x) := by
    have h1 : (ZMod.chineseRemainder hAB x).1 = ((x.val : ℕ) : ZMod A) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val x]
      simp [ZMod.chineseRemainder]
    have h2 : (ZMod.chineseRemainder hAB x).2 = ((x.val : ℕ) : ZMod B) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val x]
      simp [ZMod.chineseRemainder]
    simp only [h1, h2]
    rw [← periodic_eq_val_cast f A hf, ← periodic_eq_val_cast g B hg]
  simp_rw [hx]
  rw [Fintype.expect_equiv (ZMod.chineseRemainder hAB).toEquiv
    (fun x => (fun y : ZMod A × ZMod B => f y.1.val * g y.2.val) (ZMod.chineseRemainder hAB x))
    (fun y : ZMod A × ZMod B => f y.1.val * g y.2.val) (fun _ => rfl)]
  rw [Fintype.expect_mul_expect, ← Finset.univ_product_univ, Finset.expect_product]

lemma periodic_finset_prod {ι : Type*} (S : Finset ι) (m : ι → ℕ) (f : ι → ℕ → ℂ)
    (hf : ∀ i ∈ S, Function.Periodic (f i) (m i)) :
    Function.Periodic (fun n => ∏ i ∈ S, f i n) (∏ i ∈ S, m i) := by
  intro n
  apply prod_congr rfl
  intro i hi
  exact periodic_mul_of_dvd (hf i hi) (dvd_prod_of_mem m hi) n

lemma periodicMean_prod_coprime {ι : Type*} [DecidableEq ι] (S : Finset ι) (m : ι → ℕ)
    (hm : ∀ i ∈ S, 0 < m i)
    (hcop : (S : Set ι).Pairwise (fun i j => (m i).Coprime (m j)))
    (f : ι → ℕ → ℂ) (hf : ∀ i ∈ S, Function.Periodic (f i) (m i)) :
    periodicMean (fun n => ∏ i ∈ S, f i n) (∏ i ∈ S, m i) = ∏ i ∈ S, periodicMean (f i) (m i) := by
  induction S using Finset.induction_on with
  | empty => simp [periodicMean]
  | @insert a S ha ih =>
    have hma : 0 < m a := hm a (mem_insert_self a S)
    have hmS : 0 < ∏ i ∈ S, m i := prod_pos (fun i hi => hm i (mem_insert_of_mem hi))
    have : NeZero (m a) := ⟨hma.ne'⟩
    have : NeZero (∏ i ∈ S, m i) := ⟨hmS.ne'⟩
    have hc : (m a).Coprime (∏ i ∈ S, m i) := by
      apply Nat.Coprime.prod_right
      intro i hi
      exact hcop (mem_insert_self a S) (mem_insert_of_mem hi) (ne_of_mem_of_not_mem hi ha).symm
    simp only [prod_insert ha]
    rw [periodicMean_mul_coprime hc (f a) (fun n => ∏ i ∈ S, f i n)
      (hf a (mem_insert_self a S))
      (periodic_finset_prod S m f (fun i hi => hf i (mem_insert_of_mem hi)))]
    rw [ih (fun i hi => hm i (mem_insert_of_mem hi))
      (hcop.mono (by intro i hi; exact mem_insert_of_mem hi))
      (fun i hi => hf i (mem_insert_of_mem hi))]

/-! ## Local factors -/

lemma periodicMean_root_indicator (p : ℕ) [Fact p.Prime] (c : ZMod p) :
    periodicMean (fun n : ℕ => if (n : ZMod p) = c then (p : ℂ) else 0) p = 1 := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [← expect_zmod_range (fun x : ZMod p => if x = c then (p : ℂ) else 0)]
  rw [expect_eq_sum_div_card]
  simp only [sum_ite_eq', mem_univ, ite_true, card_univ, ZMod.card]
  exact div_self (by exact_mod_cast (Fact.out : p.Prime).ne_zero)

lemma periodicMean_unit_indicator (p : ℕ) [Fact p.Prime] :
    periodicMean (fun n : ℕ => 1 - (primeSieveWeight p (n : ZMod p) : ℂ)) p = 1 := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [← expect_zmod_range (fun x : ZMod p => 1 - (primeSieveWeight p x : ℂ))]
  rw [expect_sub_distrib, Fintype.expect_const]
  have h := primeSieveWeight_mean_zero (p := p)
  have h' : (𝔼 x : ZMod p, (primeSieveWeight p x : ℂ)) = 0 := by
    rw [← Complex.ofReal_expect, h, Complex.ofReal_zero]
  rw [h', sub_zero]

lemma unit_indicator_eq (p : ℕ) [Fact p.Prime] (n : ℕ) :
    1 - (primeSieveWeight p (n : ZMod p) : ℂ) =
      if p ∣ n then 0 else (p : ℂ) / ((p : ℂ) - 1) := by
  have h := primeSieveWeight_unit_density (p := p) (n : ZMod p)
  have h' : (1 - (primeSieveWeight p (n : ZMod p) : ℂ)) =
      (((p : ℝ) / (p - 1) * (if (n : ZMod p) ≠ 0 then 1 else 0) : ℝ) : ℂ) := by
    rw [← h]; push_cast; ring
  rw [h']
  by_cases hpn : p ∣ n
  · have hz : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).mpr hpn
    simp [hz, hpn]
  · have hz : (n : ZMod p) ≠ 0 := fun h => hpn ((ZMod.natCast_eq_zero_iff n p).mp h)
    simp [hz, hpn]

/-! ## The unit quadratic average and the frequency set -/

/-- The paper's unit quadratic average (`def:kernel-notation`):
`g(ξ) = φ(q)⁻¹ ∑_{m ∈ (ℤ/qℤ)ˣ} e(ξ m²)` with `q = q(ξ)` the reduced denominator.
The units modulo `q` are represented by `0 ≤ m < q` with `gcd(m, q) = 1`; for
`q = 1` this is the single class `m = 0`, so `g(0) = 1`. -/
noncomputable def unitQuadraticAverage (ξ : ℚ) : ℂ :=
  ((Nat.totient ξ.den : ℕ) : ℂ)⁻¹ *
    ∑ m ∈ (range ξ.den).filter (fun m => Nat.Coprime m ξ.den), expPhase ((ξ : ℝ) * (m : ℝ)^2)

/-- The paper's frequency set `Ξ_{H,D}` (`def:kernel-notation`): the points of `ℚ/ℤ`
whose reduced denominator is at most `H`, squarefree and coprime to `D`, represented
by their representatives in `[0,1)`. -/
noncomputable def frequencySet (H : ℝ) (D : ℕ) : Finset ℚ :=
  (boundedRationals ⌊H⌋₊).filter (fun ξ => Squarefree ξ.den ∧ Nat.Coprime ξ.den D)

lemma mem_frequencySet {H : ℝ} (hH : 0 ≤ H) (D : ℕ) (ξ : ℚ) :
    ξ ∈ frequencySet H D ↔
      0 ≤ ξ ∧ ξ < 1 ∧ (ξ.den : ℝ) ≤ H ∧ Squarefree ξ.den ∧ Nat.Coprime ξ.den D := by
  unfold frequencySet
  rw [mem_filter, mem_boundedRationals, Nat.le_floor_iff hH]
  tauto

lemma expPhase_rat_sq_periodic (ξ : ℚ) :
    Function.Periodic (fun m : ℕ => expPhase ((ξ : ℝ) * (m : ℝ)^2)) ξ.den := by
  intro m
  dsimp only
  have hq : (ξ : ℝ) * (ξ.den : ℝ) = (ξ.num : ℝ) := by
    have h := Rat.mul_den_eq_num ξ
    exact_mod_cast h
  have he : (ξ : ℝ) * (((m + ξ.den : ℕ) : ℝ))^2 =
      (ξ : ℝ) * (m : ℝ)^2 + ((ξ.num * (2 * (m : ℤ) + ξ.den) : ℤ) : ℝ) := by
    push_cast
    linear_combination (2 * (m : ℝ) + (ξ.den : ℝ)) * hq
  rw [he, expPhase_add, expPhase_int, mul_one]

section CentreCoefficient

variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀ i, Fact (p i).Prime] (R : Finset I) (c : ∀ i, ZMod (p i))

/-- The prime factors of a squarefree denominator, read through the prime family. -/
lemma prod_family_eq_of_squarefree (hinj : Function.Injective p) (q : ℕ) (hsq : Squarefree q) (hq : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ q → ∃ i ∉ R, p i = ℓ)
    (g : ℕ → ℂ) :
    ∏ i ∈ Rᶜ.filter (fun i => p i ∣ q), g (p i) = ∏ ℓ ∈ q.primeFactors, g ℓ := by
  have hq0 : q ≠ 0 := Squarefree.ne_zero hsq
  apply Finset.prod_nbij p
  · intro i hi
    rw [mem_filter] at hi
    exact Nat.mem_primeFactors.mpr ⟨(Fact.out : (p i).Prime), hi.2, hq0⟩
  · intro i _ j _ h
    exact hinj h
  · intro ℓ hℓ
    obtain ⟨hℓp, hℓq, _⟩ := Nat.mem_primeFactors.mp hℓ
    obtain ⟨i, hiR, rfl⟩ := hq ℓ hℓp hℓq
    exact ⟨i, by simp [hiR, hℓq], rfl⟩
  · intro i _
    rfl

lemma totient_eq_prod_of_squarefree (q : ℕ) (hsq : Squarefree q) :
    Nat.totient q = ∏ ℓ ∈ q.primeFactors, (ℓ - 1) := by
  have h := Nat.totient_mul_prod_primeFactors q
  rw [Nat.prod_primeFactors_of_squarefree hsq] at h
  have hq0 : 0 < q := Nat.pos_of_ne_zero (Squarefree.ne_zero hsq)
  rw [mul_comm] at h
  exact Nat.eq_of_mul_eq_mul_left hq0 h

/-- The product of the local unit densities over the primes of a squarefree `q`. -/
lemma unit_density_product (hinj : Function.Injective p) (q : ℕ) (hsq : Squarefree q)
    (hq : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ q → ∃ i ∉ R, p i = ℓ) (m : ℕ) :
    ∏ i ∈ Rᶜ.filter (fun i => p i ∣ q), (1 - (primeSieveWeight (p i) (m : ZMod (p i)) : ℂ)) =
      if Nat.Coprime m q then (q : ℂ) / (Nat.totient q : ℂ) else 0 := by
  simp_rw [unit_indicator_eq]
  have hswap : ∀ i, (if p i ∣ m then (0 : ℂ) else (p i : ℂ) / ((p i : ℂ) - 1)) =
      if ¬ p i ∣ m then (p i : ℂ) / ((p i : ℂ) - 1) else 0 := by
    intro i; split_ifs <;> rfl
  simp_rw [hswap]
  rw [prod_ite_zero]
  have hiff : (∀ i ∈ Rᶜ.filter (fun i => p i ∣ q), ¬ p i ∣ m) ↔ Nat.Coprime m q := by
    constructor
    · intro h
      apply Nat.coprime_of_dvd
      intro ℓ hℓ hℓm hℓq
      obtain ⟨i, hiR, rfl⟩ := hq ℓ hℓ hℓq
      exact h i (by simp [hiR, hℓq]) hℓm
    · intro h i hi hpm
      rw [mem_filter] at hi
      have h1 := Nat.dvd_gcd hpm hi.2
      rw [h.gcd_eq_one] at h1
      exact (Fact.out : (p i).Prime).one_lt.ne' (Nat.dvd_one.mp h1)
  by_cases hc : Nat.Coprime m q
  · rw [ite_eq_left (hiff.mpr hc), ite_eq_left hc, prod_div_distrib]
    have h1 : ∏ i ∈ Rᶜ.filter (fun i => p i ∣ q), (p i : ℂ) = (q : ℂ) := by
      rw [prod_family_eq_of_squarefree p R hinj q hsq hq (fun ℓ => (ℓ : ℂ)), ← Nat.cast_prod,
        Nat.prod_primeFactors_of_squarefree hsq]
    have h2 : ∏ i ∈ Rᶜ.filter (fun i => p i ∣ q), ((p i : ℂ) - 1) = (Nat.totient q : ℂ) := by
      rw [prod_family_eq_of_squarefree p R hinj q hsq hq (fun ℓ => (ℓ : ℂ) - 1),
        totient_eq_prod_of_squarefree q hsq, Nat.cast_prod]
      apply prod_congr rfl
      intro ℓ hℓ
      rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hℓ).one_le, Nat.cast_one]
    rw [h1, h2]
  · rw [ite_eq_right (fun h => hc (hiff.mp h)), ite_eq_right hc]

/-- Pointwise factorization of the complete weight against a centre `j/D + ξ`. -/
lemma complete_weight_centre_factor (D : ℕ) (hD : 0 < D) (r : ℤ)
    (hroot : ∀ n : ℕ, actualRootWeight p R c n ≠ 0 → (D : ℤ) ∣ (n : ℤ)^2 - r)
    (j : ℤ) (ξ : ℚ) (q : ℕ) (m : ℕ) :
    actualCompleteWeight p R c m * expPhase ((((j : ℚ) / D + ξ : ℚ) : ℝ) * (m : ℝ)^2) =
      (expPhase ((j : ℝ) * r / D) * actualRootWeight p R c m) *
        ((∏ i ∈ Rᶜ.filter (fun i => p i ∣ q),
            (1 - (primeSieveWeight (p i) (m : ZMod (p i)) : ℂ))) *
          expPhase ((ξ : ℝ) * (m : ℝ)^2) *
          ∏ i ∈ Rᶜ.filter (fun i => ¬ p i ∣ q),
            (1 - (primeSieveWeight (p i) (m : ZMod (p i)) : ℂ))) := by
  have hprod : (∏ i, (1 - if i ∈ R then 0 else
      (primeSieveWeight (p i) (m : ZMod (p i)) : ℂ))) =
      (∏ i ∈ Rᶜ.filter (fun i => p i ∣ q),
          (1 - (primeSieveWeight (p i) (m : ZMod (p i)) : ℂ))) *
        ∏ i ∈ Rᶜ.filter (fun i => ¬ p i ∣ q),
          (1 - (primeSieveWeight (p i) (m : ZMod (p i)) : ℂ)) := by
    rw [prod_filter_mul_prod_filter_not, ← prod_mul_prod_compl R]
    have hR : ∏ i ∈ R, (1 - if i ∈ R then 0 else
        (primeSieveWeight (p i) (m : ZMod (p i)) : ℂ)) = 1 := by
      apply prod_eq_one
      intro i hi
      simp [hi]
    rw [hR, one_mul]
    apply prod_congr rfl
    intro i hi
    rw [ite_eq_right (mem_compl.mp hi)]
  unfold actualCompleteWeight
  rw [hprod]
  by_cases h0 : actualRootWeight p R c m = 0
  · rw [h0]; ring
  · obtain ⟨k, hk⟩ := hroot m h0
    have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    have he : (((j : ℚ) / D + ξ : ℚ) : ℝ) * (m : ℝ)^2 =
        ((j : ℝ) * r / D + (ξ : ℝ) * (m : ℝ)^2) + ((j * k : ℤ) : ℝ) := by
      have hk' : ((m : ℝ))^2 = (r : ℝ) + (D : ℝ) * (k : ℝ) := by
        have := congrArg (fun z : ℤ => (z : ℝ)) hk
        push_cast at this
        linarith
      push_cast
      rw [hk']
      field_simp
      ring
    rw [he, expPhase_add, expPhase_int, mul_one, expPhase_add]
    ring

/-- The complete major-arc coefficient at a centre `j/D + ξ` (`lem:record:kernel-coefficient`,
case `q₁ ≤ H`, before truncation): it equals `e(j r/D) g(ξ)`. -/
lemma completeRationalCoefficient_centre (hinj : Function.Injective p)
    (D : ℕ) (hD : 0 < D) (hRD : ∀ i ∈ R, p i ∣ D) (hcopD : ∀ i ∉ R, Nat.Coprime (p i) D)
    (r : ℤ) (hroot : ∀ n : ℕ, actualRootWeight p R c n ≠ 0 → (D : ℤ) ∣ (n : ℤ)^2 - r)
    (j : ℤ) (ξ : ℚ) (hsq : Squarefree ξ.den)
    (hq : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ ξ.den → ∃ i ∉ R, p i = ℓ) :
    completeRationalCoefficient p R c ((j : ℚ) / D + ξ) =
      expPhase ((j : ℝ) * r / D) * unitQuadraticAverage ξ := by
  classical
  set q := ξ.den with hqdef
  set S₁ := Rᶜ.filter (fun i => p i ∣ q) with hS₁
  set S₂ := Rᶜ.filter (fun i => ¬ p i ∣ q) with hS₂
  have hpos : ∀ i, 0 < p i := fun i => (Fact.out : (p i).Prime).pos
  have hP₁ : ∏ i ∈ S₁, p i = q := by
    have h := prod_family_eq_of_squarefree p R hinj q hsq hq (fun ℓ => (ℓ : ℂ))
    have h' : ((∏ i ∈ S₁, p i : ℕ) : ℂ) = ((q : ℕ) : ℂ) := by
      rw [Nat.cast_prod, h, ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
    exact_mod_cast h'
  set P₂ := ∏ i ∈ S₂, p i with hP₂def
  have hq0 : 0 < q := ξ.pos
  have hP₂ : 0 < P₂ := prod_pos (fun i _ => hpos i)
  have : NeZero D := ⟨hD.ne'⟩
  have : NeZero q := ⟨hq0.ne'⟩
  have : NeZero P₂ := ⟨hP₂.ne'⟩
  have : NeZero (q * P₂) := ⟨(Nat.mul_pos hq0 hP₂).ne'⟩
  -- pairwise coprimality of distinct family primes
  have hpp : ∀ i k, i ≠ k → (p i).Coprime (p k) := fun i k hik =>
    (Nat.coprime_primes (Fact.out : (p i).Prime) (Fact.out : (p k).Prime)).mpr
      (fun h => hik (hinj h))
  have hcopQ : Nat.Coprime q P₂ := by
    rw [← hP₁]
    apply Nat.Coprime.prod_left
    intro i hi
    apply Nat.Coprime.prod_right
    intro k hk
    apply hpp
    rintro rfl
    exact (mem_filter.mp hk).2 (mem_filter.mp hi).2
  have hcopDQ : Nat.Coprime D (q * P₂) := by
    rw [← hP₁, ← prod_union (disjoint_filter_filter_not _ _ _), filter_union_filter_not_eq]
    apply Nat.Coprime.symm
    apply Nat.Coprime.prod_left
    intro i hi
    exact hcopD i (mem_compl.mp hi)
  set t := D * (q * P₂) with htdef
  have ht : 0 < t := Nat.mul_pos hD (Nat.mul_pos hq0 hP₂)
  have hpt : ∀ i, p i ∣ t := by
    intro i
    by_cases hiR : i ∈ R
    · exact dvd_mul_of_dvd_left (hRD i hiR) _
    · by_cases hiq : p i ∣ q
      · exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hiq _) _
      · apply dvd_mul_of_dvd_right (dvd_mul_of_dvd_right _ _)
        exact dvd_prod_of_mem p (by simp [hS₂, hiR, hiq])
  have hbt : ((j : ℚ) / D + ξ).den ∣ t := by
    have h1 : ((j : ℚ) / D).den ∣ D := by
      have h := Rat.den_dvd j (D : ℤ)
      rw [Rat.divInt_eq_div] at h
      push_cast at h
      exact_mod_cast h
    apply (Rat.add_den_dvd _ _).trans
    exact Nat.mul_dvd_mul h1 (dvd_mul_right q P₂)
  rw [completeRationalCoefficient_eq p R c _ t ht hpt hbt]
  have hpt' : ∀ n : ℕ, actualCompleteWeight p R c (n+1) *
      expPhase ((((j : ℚ) / D + ξ : ℚ) : ℝ) * ((n : ℝ) + 1)^2) =
      (fun n => expPhase ((j : ℝ) * r / D) * actualRootWeight p R c (n+1)) n *
      (fun n => ((∏ i ∈ S₁, (1 - (primeSieveWeight (p i) ((n+1 : ℕ) : ZMod (p i)) : ℂ))) *
          expPhase ((ξ : ℝ) * ((n+1 : ℕ) : ℝ)^2)) *
          ∏ i ∈ S₂, (1 - (primeSieveWeight (p i) ((n+1 : ℕ) : ZMod (p i)) : ℂ))) n := by
    intro n
    have h := complete_weight_centre_factor p R c D hD r hroot j ξ q (n+1)
    push_cast at h ⊢
    rw [h]
  simp_rw [hpt']
  have hper_u : ∀ i, Function.Periodic
      (fun n : ℕ => 1 - (primeSieveWeight (p i) ((n+1 : ℕ) : ZMod (p i)) : ℂ)) (p i) := by
    intro i n
    simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self, add_zero]
  have hperA : Function.Periodic
      (fun n => expPhase ((j : ℝ) * r / D) * actualRootWeight p R c (n+1)) D := by
    intro n
    simp only
    rw [show n + D + 1 = (n + 1) + D by ring,
      actualRootWeight_periodic p R c D hRD (n+1)]
  have hperG₁ : Function.Periodic
      (fun n => (∏ i ∈ S₁, (1 - (primeSieveWeight (p i) ((n+1 : ℕ) : ZMod (p i)) : ℂ))) *
          expPhase ((ξ : ℝ) * ((n+1 : ℕ) : ℝ)^2)) q := by
    apply Function.Periodic.mul
    · rw [← hP₁]
      exact periodic_finset_prod S₁ p _ (fun i _ => hper_u i)
    · intro n
      have h := expPhase_rat_sq_periodic ξ (n+1)
      simpa [Nat.add_right_comm] using h
  have hperG₂ : Function.Periodic
      (fun n => ∏ i ∈ S₂, (1 - (primeSieveWeight (p i) ((n+1 : ℕ) : ZMod (p i)) : ℂ))) P₂ :=
    periodic_finset_prod S₂ p _ (fun i _ => hper_u i)
  have hper12 : Function.Periodic
      (fun n => (∏ i ∈ S₁, (1 - (primeSieveWeight (p i) ((n+1 : ℕ) : ZMod (p i)) : ℂ))) *
          expPhase ((ξ : ℝ) * ((n+1 : ℕ) : ℝ)^2) *
          ∏ i ∈ S₂, (1 - (primeSieveWeight (p i) ((n+1 : ℕ) : ZMod (p i)) : ℂ))) (q * P₂) :=
    (periodic_mul_of_dvd hperG₁ (dvd_mul_right q P₂)).mul
      (periodic_mul_of_dvd hperG₂ (dvd_mul_left P₂ q))
  rw [periodicMean_mul_coprime hcopDQ _ _ hperA hper12]
  rw [periodicMean_mul_coprime hcopQ _ _ hperG₁ hperG₂]
  -- the root factor
  have hA : periodicMean (fun n => expPhase ((j : ℝ) * r / D) * actualRootWeight p R c (n+1)) D =
      expPhase ((j : ℝ) * r / D) := by
    rw [periodicMean_mul_left]
    rw [periodicMean_shift_one _ D (actualRootWeight_periodic p R c D hRD)]
    have hdvd : (∏ i ∈ R, p i) ∣ D := by
      apply nat_pairwise_coprime_prod_dvd
      · intro i _ k _ hik; exact hpp i k hik
      · exact hRD
    have hperR : Function.Periodic (actualRootWeight p R c) (∏ i ∈ R, p i) :=
      actualRootWeight_periodic p R c _ (fun i hi => dvd_prod_of_mem p hi)
    rw [periodicMean_of_dvd _ _ D hD.ne' hdvd hperR]
    unfold actualRootWeight
    rw [periodicMean_prod_coprime R p (fun i _ => hpos i)
      (fun i _ k _ hik => hpp i k hik) _ (fun i _ n => by
        simp only [Nat.cast_add, ZMod.natCast_self, add_zero])]
    rw [prod_eq_one (fun i _ => periodicMean_root_indicator (p i) (c i)), mul_one]
  -- the unit factor away from q
  have hG₂ : periodicMean
      (fun n => ∏ i ∈ S₂, (1 - (primeSieveWeight (p i) ((n+1 : ℕ) : ZMod (p i)) : ℂ))) P₂ = 1 := by
    have hper : Function.Periodic
        (fun n : ℕ => ∏ i ∈ S₂, (1 - (primeSieveWeight (p i) (n : ZMod (p i)) : ℂ))) P₂ :=
      periodic_finset_prod S₂ p _ (fun i _ n => by
        simp only [Nat.cast_add, ZMod.natCast_self, add_zero])
    rw [periodicMean_shift_one _ P₂ hper]
    rw [periodicMean_prod_coprime S₂ p (fun i _ => hpos i)
      (fun i _ k _ hik => hpp i k hik) _ (fun i _ n => by
        simp only [Nat.cast_add, ZMod.natCast_self, add_zero])]
    exact prod_eq_one (fun i _ => periodicMean_unit_indicator (p i))
  -- the unit factor at q
  have hG₁ : periodicMean
      (fun n => (∏ i ∈ S₁, (1 - (primeSieveWeight (p i) ((n+1 : ℕ) : ZMod (p i)) : ℂ))) *
          expPhase ((ξ : ℝ) * ((n+1 : ℕ) : ℝ)^2)) q = unitQuadraticAverage ξ := by
    have hper : Function.Periodic
        (fun n : ℕ => (∏ i ∈ S₁, (1 - (primeSieveWeight (p i) (n : ZMod (p i)) : ℂ))) *
          expPhase ((ξ : ℝ) * (n : ℝ)^2)) q := by
      apply Function.Periodic.mul
      · rw [← hP₁]
        exact periodic_finset_prod S₁ p _ (fun i _ n => by
          simp only [Nat.cast_add, ZMod.natCast_self, add_zero])
      · exact expPhase_rat_sq_periodic ξ
    rw [periodicMean_shift_one _ q hper]
    simp_rw [hS₁, unit_density_product p R hinj q hsq hq]
    unfold periodicMean unitQuadraticAverage
    rw [sum_filter]
    have htot : (Nat.totient q : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr hq0).ne'
    have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
    rw [mul_sum, mul_sum]
    apply sum_congr rfl
    intro m _
    split_ifs
    · field_simp
      rw [← hqdef]
      ring
    · simp
  rw [hA, hG₁, hG₂, mul_one]

end CentreCoefficient

/-! ## Centres of the model kernel -/

section Centres

variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀ i, Fact (p i).Prime] (R : Finset I) (c : ∀ i, ZMod (p i))

omit [Fintype I] [DecidableEq I] [∀ i, Fact (p i).Prime] in
lemma dvd_rootSquareModulus {i : I} (hi : i ∈ R) : p i ∣ rootSquareModulus p R := by
  unfold rootSquareModulus
  have h1 : p i ∣ (if p i = 2 then 8 else p i) := by
    split_ifs with h
    · rw [h]; norm_num
    · exact dvd_rfl
  exact h1.trans (dvd_prod_of_mem (fun i => if p i = 2 then 8 else p i) hi)

omit [Fintype I] [DecidableEq I] in
lemma coprime_rootSquareModulus (hinj : Function.Injective p) (htwo : ∀ i, p i = 2 → i ∈ R)
    {i : I} (hi : i ∉ R) : Nat.Coprime (p i) (rootSquareModulus p R) := by
  unfold rootSquareModulus
  apply Nat.Coprime.prod_right
  intro k hk
  have hik : i ≠ k := by rintro rfl; exact hi hk
  have hpi : (p i).Prime := Fact.out
  have hpk : (p k).Prime := Fact.out
  split_ifs with h
  · have h2 : p i ≠ 2 := fun h' => hi (htwo i h')
    have hc : Nat.Coprime (p i) 2 := (Nat.coprime_primes hpi Nat.prime_two).mpr h2
    simpa using hc.pow_right 3
  · exact (Nat.coprime_primes hpi hpk).mpr (fun h' => hik (hinj h'))

lemma rat_div_den_dvd (j : ℤ) (D : ℕ) : ((j : ℚ) / D).den ∣ D := by
  have h := Rat.den_dvd j (D : ℤ)
  rw [Rat.divInt_eq_div] at h
  push_cast at h
  exact_mod_cast h

/-- The upstream model coefficient at a centre `j/D + ξ`, `D = rootSquareModulus`. -/
lemma kernelModelCoefficient_centre (hinj : Function.Injective p)
    (htwo : ∀ i, p i = 2 → i ∈ R)
    (r : ℤ) (hroot : ∀ n : ℕ, actualRootWeight p R c n ≠ 0 →
      (rootSquareModulus p R : ℤ) ∣ (n : ℤ)^2 - r)
    (H : ℝ) (j : ℤ) (ξ : ℚ) (hsq : Squarefree ξ.den)
    (hcop : Nat.Coprime ξ.den (rootSquareModulus p R))
    (hq : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ ξ.den → ∃ i, p i = ℓ) :
    kernelModelCoefficient p R c H ((j : ℚ) / (rootSquareModulus p R) + ξ) =
      if (ξ.den : ℝ) ≤ H then
        expPhase ((j : ℝ) * r / (rootSquareModulus p R)) * unitQuadraticAverage ξ
      else 0 := by
  classical
  set D := rootSquareModulus p R with hDdef
  have hD : 0 < D := rootSquareModulus_pos p R
  have hq' : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ ξ.den → ∃ i ∉ R, p i = ℓ := by
    intro ℓ hℓ hℓq
    obtain ⟨i, rfl⟩ := hq ℓ hℓ hℓq
    refine ⟨i, ?_, rfl⟩
    intro hiR
    have h1 : p i ∣ Nat.gcd ξ.den D := Nat.dvd_gcd hℓq (dvd_rootSquareModulus p R hiR)
    rw [hcop.gcd_eq_one] at h1
    exact hℓ.one_lt.ne' (Nat.dvd_one.mp h1)
  set b : ℚ := (j : ℚ) / D + ξ with hb
  have hb1 : b.den ∣ D * ξ.den :=
    (Rat.add_den_dvd _ _).trans (Nat.mul_dvd_mul (rat_div_den_dvd j D) dvd_rfl)
  have hb2 : ξ.den ∣ b.den * D := by
    have he : ξ = b - (j : ℚ) / D := by rw [hb]; ring
    rw [he]
    exact (Rat.sub_den_dvd _ _).trans (Nat.mul_dvd_mul dvd_rfl (rat_div_den_dvd j D))
  have hact : primaryActive p b.den \ R = Rᶜ.filter (fun i => p i ∣ ξ.den) := by
    ext i
    simp only [mem_sdiff, mem_primaryActive, mem_filter, mem_compl]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h2, ?_⟩
      have hc := coprime_rootSquareModulus p R hinj htwo h2
      exact hc.dvd_of_dvd_mul_left (h1.trans hb1)
    · rintro ⟨h2, h1⟩
      refine ⟨?_, h2⟩
      have hc := coprime_rootSquareModulus p R hinj htwo h2
      exact hc.dvd_of_dvd_mul_right (h1.trans hb2)
  have hprod : ((∏ i ∈ primaryActive p b.den \ R, p i : ℕ) : ℝ) = (ξ.den : ℝ) := by
    rw [hact]
    have h := prod_family_eq_of_squarefree p R hinj ξ.den hsq hq' (fun ℓ => (ℓ : ℂ))
    have h' : ((∏ i ∈ Rᶜ.filter (fun i => p i ∣ ξ.den), p i : ℕ) : ℂ) = ((ξ.den : ℕ) : ℂ) := by
      rw [Nat.cast_prod, h, ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
    have h'' : (∏ i ∈ Rᶜ.filter (fun i => p i ∣ ξ.den), p i : ℕ) = ξ.den := by exact_mod_cast h'
    rw [h'']
  unfold kernelModelCoefficient
  rw [hprod, completeRationalCoefficient_centre p R c hinj D hD
    (fun i hi => dvd_rootSquareModulus p R hi)
    (fun i hi => coprime_rootSquareModulus p R hinj htwo hi) r hroot j ξ hsq hq']

/-- Distinct centres: `(j, ξ) ↦ fract(j/D + ξ)` is injective on `[0,D) × Ξ_{H,D}`. -/
lemma centre_injective (D : ℕ) (hD : 0 < D) (H : ℝ) (hH : 0 ≤ H)
    (j j' : ℕ) (hj : j < D) (hj' : j' < D) (ξ ξ' : ℚ)
    (hξ : ξ ∈ frequencySet H D) (hξ' : ξ' ∈ frequencySet H D)
    (he : Int.fract ((j : ℚ) / D + ξ) = Int.fract ((j' : ℚ) / D + ξ')) :
    j = j' ∧ ξ = ξ' := by
  rw [mem_frequencySet hH] at hξ hξ'
  obtain ⟨k, hk⟩ := Int.fract_eq_fract.mp he
  set δ := ξ - ξ' with hδ
  have hδ1 : δ.den ∣ ξ.den * ξ'.den := Rat.sub_den_dvd _ _
  have hδ2 : δ.den ∣ D := by
    have he2 : δ = (((k : ℤ) * D - ((j : ℤ) - j') : ℤ) : ℚ) / D := by
      have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
      rw [hδ, show ξ - ξ' = (k : ℚ) - ((j : ℚ) / D - (j' : ℚ) / D) by linarith]
      push_cast
      field_simp
    rw [he2]
    exact rat_div_den_dvd _ D
  have hcop : Nat.Coprime (ξ.den * ξ'.den) D :=
    Nat.coprime_mul_iff_left.mpr ⟨hξ.2.2.2.2, hξ'.2.2.2.2⟩
  have hδ3 : δ.den = 1 := by
    have h := Nat.dvd_gcd hδ1 hδ2
    rw [hcop.gcd_eq_one] at h
    exact Nat.dvd_one.mp h
  have hδint : (δ.num : ℚ) = δ := (Rat.den_eq_one_iff δ).mp hδ3
  have hlo : -1 < δ := by rw [hδ]; linarith [hξ.1, hξ'.2.1]
  have hhi : δ < 1 := by rw [hδ]; linarith [hξ.2.1, hξ'.1]
  have hnum : δ.num = 0 := by
    have h1 : (-1 : ℚ) < (δ.num : ℚ) := by rw [hδint]; exact hlo
    have h2 : (δ.num : ℚ) < 1 := by rw [hδint]; exact hhi
    have h1' : -1 < δ.num := by exact_mod_cast h1
    have h2' : δ.num < 1 := by exact_mod_cast h2
    omega
  have hδ0 : δ = 0 := by rw [← hδint, hnum]; simp
  have hξeq : ξ = ξ' := by rw [hδ] at hδ0; linarith
  refine ⟨?_, hξeq⟩
  have hk' : ((j : ℚ) - j') = (k : ℚ) * D := by
    have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    rw [hξeq] at hk
    field_simp at hk
    linarith
  have hk'' : ((j : ℤ) - j') = k * D := by exact_mod_cast hk'
  have hjD : (j : ℤ) < D := by exact_mod_cast hj
  have hj'D : (j' : ℤ) < D := by exact_mod_cast hj'
  have hk0 : k = 0 := by
    rcases lt_trichotomy k 0 with hneg | h0 | hpos
    · have : k * (D : ℤ) ≤ -(D : ℤ) := by nlinarith
      omega
    · exact h0
    · have : (D : ℤ) ≤ k * (D : ℤ) := by nlinarith
      omega
  rw [hk0] at hk''
  omega

/-- Every centre `fract(j/D + ξ)` is one of the bounded rationals of the model sum. -/
lemma centre_mem_boundedRationals (D : ℕ) (hD : 0 < D) (H : ℝ) (hH : 0 ≤ H) (j : ℕ) (ξ : ℚ)
    (hξ : ξ ∈ frequencySet H D) :
    Int.fract ((j : ℚ) / D + ξ) ∈ boundedRationals ⌈(D : ℝ) * H⌉₊ := by
  rw [mem_frequencySet hH] at hξ
  apply boundedRationals_fract
  have hjD : ((j : ℚ) / D).den ∣ D := by
    have h := rat_div_den_dvd (j : ℤ) D
    rwa [Int.cast_natCast] at h
  have h1 : ((j : ℚ) / D + ξ).den ∣ D * ξ.den :=
    (Rat.add_den_dvd _ _).trans (Nat.mul_dvd_mul hjD dvd_rfl)
  have hle : ((j : ℚ) / D + ξ).den ≤ D * ξ.den := Nat.le_of_dvd (Nat.mul_pos hD ξ.pos) h1
  have hle' : ((D * ξ.den : ℕ) : ℝ) ≤ (D : ℝ) * H := by
    push_cast
    exact mul_le_mul_of_nonneg_left hξ.2.2.1 (Nat.cast_nonneg _)
  have hle'' : (((j : ℚ) / D + ξ).den : ℝ) ≤ ⌈(D : ℝ) * H⌉₊ :=
    ((Nat.cast_le.mpr hle).trans hle').trans (Nat.le_ceil _)
  exact_mod_cast hle''

omit [Fintype I] [DecidableEq I] in
lemma squarefree_prod_primes (hinj : Function.Injective p) (S : Finset I) :
    Squarefree (∏ i ∈ S, p i) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i _ k _ hik
    have hc : Nat.Coprime (p i) (p k) :=
      (Nat.coprime_primes (Fact.out : (p i).Prime) (Fact.out : (p k).Prime)).mpr
        (fun h => hik (hinj h))
    exact Nat.coprime_iff_isRelPrime.mp hc
  · intro i _
    exact (Fact.out : (p i).Prime).prime.squarefree

/-- The upstream model coefficient vanishes off the paper's centres (`lem:record:K20-centres`):
a bounded rational with nonzero coefficient is `fract(j/D + ξ)` with `0 ≤ j < D`, `ξ ∈ Ξ_{H,D}`. -/
lemma exists_centre_of_ne_zero (hinj : Function.Injective p)
    (htwo : ∀ i, p i = 2 → i ∈ R) (hc : ∀ i ∈ R, if p i = 2 then c i = 1 else c i ≠ 0)
    (H : ℝ) (hH : 0 ≤ H) (b : ℚ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hbcov : b.den ∣ ∏ i, primaryModulus b.den (p i))
    (hne : kernelModelCoefficient p R c H b ≠ 0) :
    ∃ j < rootSquareModulus p R, ∃ ξ ∈ frequencySet H (rootSquareModulus p R),
      Int.fract ((j : ℚ) / (rootSquareModulus p R) + ξ) = b := by
  classical
  set D := rootSquareModulus p R with hDdef
  have hD : 0 < D := rootSquareModulus_pos p R
  set u := ∏ i ∈ primaryActive p b.den \ R, p i with hudef
  have hu : (u : ℝ) ≤ H := by
    by_contra hcon
    apply hne
    unfold kernelModelCoefficient
    rw [ite_eq_right hcon]
  have hne' : primaryModelCoefficient p hinj b hbcov R c H ≠ 0 := by
    rw [primaryModelCoefficient_eq_kernelModel p R c hinj b hbcov H htwo]
    exact hne
  have hdvd : b.den ∣ D * u :=
    primaryModelCoefficient_denominator p hinj b hbcov R c H htwo hc hne'
  have hu0 : 0 < u := prod_pos (fun i _ => (Fact.out : (p i).Prime).pos)
  have hcopuD : Nat.Coprime u D := by
    apply Nat.Coprime.prod_left
    intro i hi
    exact coprime_rootSquareModulus p R hinj htwo (mem_sdiff.mp hi).2
  have husq : Squarefree u := squarefree_prod_primes p hinj _
  obtain ⟨k, hk⟩ := hdvd
  set x : ℤ := b.num * (k : ℤ) with hxdef
  have hbx : b = (x : ℚ) / ((D : ℚ) * u) := by
    have hk' : ((D : ℚ) * u) = (b.den : ℚ) * k := by exact_mod_cast hk
    have hk0 : (k : ℚ) ≠ 0 := by
      intro h0
      have : ((D : ℚ) * u) = 0 := by rw [hk', h0, mul_zero]
      have hDu : (0 : ℚ) < (D : ℚ) * u := by positivity
      linarith
    have hden : (b.den : ℚ) ≠ 0 := by exact_mod_cast b.pos.ne'
    rw [hk', hxdef]
    push_cast
    rw [mul_div_mul_right _ _ hk0]
    exact (Rat.num_div_den b).symm
  obtain ⟨s, t, hst⟩ := Nat.isCoprime_iff_coprime.mpr hcopuD.symm
  -- hst : s * D + t * u = 1
  set ξ : ℚ := Int.fract (((x * s : ℤ) : ℚ) / u) with hξdef
  set jz : ℤ := (x * t) % (D : ℤ) with hjz
  have hjz0 : 0 ≤ jz := Int.emod_nonneg _ (by exact_mod_cast hD.ne')
  have hjzD : jz < D := Int.emod_lt_of_pos _ (by exact_mod_cast hD)
  refine ⟨jz.toNat, by omega, ξ, ?_, ?_⟩
  · rw [mem_frequencySet hH]
    have hξden : ξ.den ∣ u := by
      rw [hξdef, Rat.den_intFract]
      exact rat_div_den_dvd _ u
    refine ⟨Int.fract_nonneg _, Int.fract_lt_one _, ?_, husq.squarefree_of_dvd hξden,
      hcopuD.coprime_dvd_left hξden⟩
    exact (Nat.cast_le.mpr (Nat.le_of_dvd hu0 hξden)).trans hu
  · have hj : ((jz.toNat : ℕ) : ℚ) = (jz : ℚ) := by
      have h := Int.toNat_of_nonneg hjz0
      exact_mod_cast h
    rw [hj]
    have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    have hu' : (u : ℚ) ≠ 0 := by exact_mod_cast hu0.ne'
    have hsum : (jz : ℚ) / D + ξ =
        b - ((((x * t) / (D : ℤ) : ℤ) : ℚ) + (⌊(((x * s : ℤ) : ℚ) / u)⌋ : ℚ)) := by
      have hjz' : (jz : ℚ) = ((x * t : ℤ) : ℚ) - (D : ℚ) * (((x * t) / (D : ℤ) : ℤ) : ℚ) := by
        rw [hjz, Int.emod_def]
        push_cast
        ring
      have hst' : (s : ℚ) * D + (t : ℚ) * u = 1 := by exact_mod_cast hst
      have key : (x : ℚ) * t / D + (x : ℚ) * s / u = x / (D * u) := by
        rw [div_add_div _ _ hD' hu', div_eq_div_iff (mul_ne_zero hD' hu') (mul_ne_zero hD' hu')]
        linear_combination ((x : ℚ) * D * u) * hst'
      rw [hξdef, Int.fract, hjz', hbx, ← key]
      push_cast
      field_simp
      ring
    rw [hsum]
    rw [show b - ((((x * t) / (D : ℤ) : ℤ) : ℚ) + (⌊(((x * s : ℤ) : ℚ) / u)⌋ : ℚ)) =
      b - ((((x * t) / (D : ℤ) + ⌊(((x * s : ℤ) : ℚ) / u)⌋ : ℤ)) : ℚ) by push_cast; ring]
    rw [Int.fract_sub_intCast]
    exact Int.fract_eq_self.mpr ⟨hb0, hb1⟩

/-- Reindexing the upstream model sum over the paper's centres (`lem:record:K20-centres`). -/
lemma model_sum_reindex (hinj : Function.Injective p)
    (htwo : ∀ i, p i = 2 → i ∈ R) (hc : ∀ i ∈ R, if p i = 2 then c i = 1 else c i ≠ 0)
    (r : ℤ) (hroot : ∀ n : ℕ, actualRootWeight p R c n ≠ 0 →
      (rootSquareModulus p R : ℤ) ∣ (n : ℤ)^2 - r)
    (H : ℝ) (hH : 0 ≤ H)
    (hcover : ∀ b : ℚ, b.den ≤ ⌈(rootSquareModulus p R : ℝ) * H⌉₊ →
      b.den ∣ ∏ i, primaryModulus b.den (p i))
    (hfam : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℝ) ≤ H → ∃ i, p i = ℓ)
    (X : ℚ → ℂ) (hX : ∀ (b : ℚ) (k : ℤ), X (b + k) = X b) :
    ∑ b ∈ boundedRationals ⌈(rootSquareModulus p R : ℝ) * H⌉₊,
        kernelModelCoefficient p R c H b * X b =
      ∑ j ∈ range (rootSquareModulus p R), ∑ ξ ∈ frequencySet H (rootSquareModulus p R),
        expPhase ((j : ℝ) * r / (rootSquareModulus p R)) * unitQuadraticAverage ξ *
          X ((j : ℚ) / (rootSquareModulus p R) + ξ) := by
  classical
  set D := rootSquareModulus p R with hDdef
  have hD : 0 < D := rootSquareModulus_pos p R
  have hXf : ∀ b : ℚ, X (Int.fract b) = X b := by
    intro b
    have h := hX b (-⌊b⌋)
    rw [Int.fract]
    simpa [sub_eq_add_neg] using h
  rw [← Finset.sum_product']
  symm
  apply Finset.sum_of_injOn (fun x : ℕ × ℚ => Int.fract ((x.1 : ℚ) / D + x.2))
  · intro x hx y hy hxy
    rw [mem_coe, mem_product, mem_range] at hx hy
    have h := centre_injective D hD H hH x.1 y.1 hx.1 hy.1 x.2 y.2 hx.2 hy.2 hxy
    exact Prod.ext h.1 h.2
  · intro x hx
    rw [mem_coe, mem_product] at hx
    exact centre_mem_boundedRationals D hD H hH x.1 x.2 hx.2
  · intro b hb hnot
    by_contra hne
    have hne' : kernelModelCoefficient p R c H b ≠ 0 := left_ne_zero_of_mul hne
    rw [mem_boundedRationals] at hb
    obtain ⟨j, hj, ξ, hξ, he⟩ := exists_centre_of_ne_zero p R c hinj htwo hc H hH b hb.1 hb.2.1
      (hcover b hb.2.2) hne'
    exact hnot ⟨(j, ξ), mem_coe.mpr (mem_product.mpr ⟨mem_range.mpr hj, hξ⟩), he⟩
  · intro x hx
    rw [mem_product, mem_range] at hx
    have hξ := (mem_frequencySet hH D x.2).mp hx.2
    rw [kernelModelCoefficient_fract, hXf]
    have hq : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ x.2.den → ∃ i, p i = ℓ := by
      intro ℓ hℓ hℓq
      apply hfam ℓ hℓ
      exact (Nat.cast_le.mpr (Nat.le_of_dvd x.2.pos hℓq)).trans hξ.2.2.1
    have hcen := kernelModelCoefficient_centre p R c hinj htwo r hroot H (x.1 : ℤ) x.2
      hξ.2.2.2.1 hξ.2.2.2.2 hq
    rw [Int.cast_natCast] at hcen
    rw [hcen, ite_eq_left hξ.2.2.1]
    push_cast
    ring

end Centres

end Kernel
end
end Sarkozy
