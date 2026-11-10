module

public import Sarkozy.Kernel.Pairing

@[expose] public section

/-!
# The actual-square kernel for general moduli

This module proves the kernel estimate `eq:record:K20` of the paper's
`prop:record:kernel20` at the triple of `cor:kernel20` for an arbitrary even modulus `D`
equipped with a root class (`RootClassDatum D (b - a)`, the content of
`lem:kernel-depth-classes`). Combined with the constructions of root classes for strict
square classes (`D = 8d`, any odd `d`) and for nonvanishing square classes, it gives parts
(i) and (iii) of the proposition.

The construction is the one of Appendix C: the actual kernel is supported on the squares,
weighted by the root class weight `classWeight D' m₀` and the truncated unit sieve over the
odd primes `≤ N` not dividing `D` (`OddFamily`); the model kernel has centres `j/D + ξ`,
`0 ≤ j < D`, `ξ ∈ Ξ_{H,D}`, with coefficients `e(j r/D) g(ξ)`. The major-arc coefficients
are compared by splitting a rational into its `D`-part and its part coprime to `D`
(Chinese remainder theorem), using the root class for the `D`-part and the upstream
coefficient bound (`finiteRationalCoefficient_actual_uniform`, OpenAI) with an empty root
set for the coprime part. The analytic estimate is upstream `finite_kernel_uniform`
(`FiniteKernel.lean`) with the rate bookkeeping of `RatesTwentieth.lean`.

Upstream (OpenAI, Apache-2.0) proofs adapted here: `rootWeight_fourier` follows
`actualDivisorWeight_fourier` (`FiniteKernel.lean`, with the residue-class density
`residueDensity_fourier_dvd` of `SievedFourier.lean`), `termCoefficient_eq_mean` follows
`finiteRationalCoefficient_actual`, `termCost` follows `sieveTermCost`, `general_kernel_rate`
follows `actual_kernel_uniform`/`actual_kernel_power_error` (`UniformRates.lean`) and
`kernel_pairing_rootDatum` follows `actual_kernel_ordered_bilinear` (`DualCoordinates.lean`).
The partial-fraction split, the coefficient comparison and the treatment of non-squarefree
moduli through `RootClassDatum` are new.
-/

namespace Sarkozy

section
open Finset
open scoped ComplexConjugate BigOperators
namespace Kernel

/-! ## The odd prime family away from `D` -/

/-- The odd primes up to `N` not dividing `D` (all primes up to `N` not dividing `D` when
`D` is even). -/
abbrev OddFamily (N D : ℕ) := {ℓ : ℕ // ℓ ∈ (range (N+1)).filter (fun ℓ => ℓ.Prime ∧ ¬ ℓ ∣ D)}

instance oddFamily_fact (N D : ℕ) (i : OddFamily N D) : Fact (Nat.Prime (i : ℕ)) :=
  ⟨(mem_filter.mp i.2).2.1⟩

lemma oddFamily_injective (N D : ℕ) : Function.Injective (fun i : OddFamily N D => (i : ℕ)) :=
  Subtype.val_injective

lemma oddFamily_not_dvd (N D : ℕ) (i : OddFamily N D) : ¬ (i : ℕ) ∣ D :=
  (mem_filter.mp i.2).2.2

lemma oddFamily_exists (N D ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ≤ N) (hℓD : ¬ ℓ ∣ D) :
    ∃ i : OddFamily N D, (i : ℕ) = ℓ :=
  ⟨⟨ℓ, mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hℓN), hℓ, hℓD⟩⟩, rfl⟩

lemma oddFamily_two (N D : ℕ) (hD : 2 ∣ D) : ∀ i : OddFamily N D, (i : ℕ) = 2 → i ∈ (∅ : Finset _) := by
  intro i hi
  exact absurd (hi ▸ hD) (oddFamily_not_dvd N D i)

lemma oddFamily_cover (N D : ℕ) (b : ℚ) (hb : b.den ≤ N) (hcop : Nat.Coprime b.den D) :
    b.den ∣ ∏ i : OddFamily N D, primaryModulus b.den (i : ℕ) := by
  apply primary_cover_of_prime_support (fun i : OddFamily N D => (i : ℕ)) (oddFamily_injective N D)
    b.den b.den_nz
  intro ℓ hℓ hdvd
  refine oddFamily_exists N D ℓ hℓ ((Nat.le_of_dvd b.pos hdvd).trans hb) ?_
  intro hℓD
  have h := Nat.dvd_gcd hdvd hℓD
  rw [hcop.gcd_eq_one] at h
  exact hℓ.one_lt.ne' (Nat.dvd_one.mp h)

/-! ## The actual weight -/

section Weight

variable (N D D' m₀ : ℕ)

/-- The coprime-part weight: the truncated unit sieve over `OddFamily N D`, with no root
primes. -/
noncomputable def sieveWeight (H : ℝ) (m : ℕ) : ℂ :=
  actualDivisorWeight (fun i : OddFamily N D => (i : ℕ)) ∅ (fun _ => 0) H m

/-- The terms of the actual weight: root class weight times one sieve term. -/
noncomputable def rootTermWeight (T : Finset (OddFamily N D)) (m : ℕ) : ℂ :=
  classWeight D' m₀ m * sieveTermWeight (fun i : OddFamily N D => (i : ℕ)) ∅ (fun _ => 0) T m

lemma classWeight_periodic : Function.Periodic (classWeight D' m₀) D' := by
  intro m
  unfold classWeight
  have h : (m + D') ≡ m [MOD D'] := by
    simp [Nat.ModEq, Nat.add_mod_right]
  by_cases hm : m ≡ m₀ [MOD D']
  · rw [ite_eq_left (h.trans hm), ite_eq_left hm]
  · rw [ite_eq_right (fun h' => hm (h.symm.trans h')), ite_eq_right hm]

lemma norm_classWeight (m : ℕ) : ‖classWeight D' m₀ m‖ ≤ D' := by
  unfold classWeight
  split_ifs <;> simp

lemma rootTermWeight_periodic (T : Finset (OddFamily N D)) :
    Function.Periodic (rootTermWeight N D D' m₀ T)
      (D' * sieveTermPeriod (fun i : OddFamily N D => (i : ℕ)) ∅ T) := by
  apply Function.Periodic.mul
  · exact periodic_mul_of_dvd (classWeight_periodic D' m₀) (dvd_mul_right _ _)
  · exact periodic_mul_of_dvd (sieveTermWeight_periodic _ ∅ _ T) (dvd_mul_left _ _)

lemma norm_rootTermWeight (T : Finset (OddFamily N D)) (m : ℕ) :
    ‖rootTermWeight N D D' m₀ T m‖ ≤ D' := by
  unfold rootTermWeight
  rw [norm_mul]
  have h1 := norm_classWeight D' m₀ m
  have h2 := sieveTermWeight_norm (fun i : OddFamily N D => (i : ℕ)) ∅ (fun _ => 0) T m
  simp only [prod_empty, Nat.cast_one] at h2
  calc ‖classWeight D' m₀ m‖ * ‖sieveTermWeight _ ∅ _ T m‖ ≤ D' * 1 :=
        mul_le_mul h1 h2 (norm_nonneg _) (Nat.cast_nonneg _)
    _ = D' := mul_one _

lemma rootTerm_sum (H : ℝ) (m : ℕ) :
    (∑ T : boundedSieveSets (fun i : OddFamily N D => (i : ℕ)) H,
      sieveTermSign T.val * rootTermWeight N D D' m₀ T.val m) =
      classWeight D' m₀ m * sieveWeight N D H m := by
  unfold sieveWeight
  rw [actualDivisorWeight_eq_terms, mul_sum]
  apply sum_congr rfl
  intro T _
  unfold rootTermWeight
  ring

lemma classWeight_ring (Q : ℕ) [NeZero Q] (hQ : D' ∣ Q) (n : ℕ) :
    (residueDensity hQ (m₀ : ZMod D') (n : ZMod Q) : ℂ) = classWeight D' m₀ n := by
  unfold residueDensity classWeight
  rw [map_natCast]
  by_cases h : n ≡ m₀ [MOD D']
  · rw [ite_eq_left ((ZMod.natCast_eq_natCast_iff n m₀ D').mpr h), ite_eq_left h]
    simp
  · rw [ite_eq_right (fun h' => h ((ZMod.natCast_eq_natCast_iff n m₀ D').mp h')), ite_eq_right h]
    simp

/-- Fourier expansion of the actual weight, with coefficients of total size `≤ D' H`
(`def:record:K20-kernels`(c)). -/
lemma rootWeight_fourier (hD' : 0 < D') (H : ℝ) (hH : 0 ≤ H) :
    ∃ (q : ℕ) (_ : NeZero q) (w : ZMod q → ℂ),
      (∀ n : ℕ, classWeight D' m₀ n * sieveWeight N D H n =
        ∑ a : ZMod q, w a * expPhase (((a.val : ℝ) / q) * n)) ∧
      (∑ a : ZMod q, ‖w a‖) ≤ D' * H := by
  classical
  let p : OddFamily N D → ℕ := fun i => (i : ℕ)
  let q : ℕ := D' * ∏ i, p i
  have hq : 0 < q := Nat.mul_pos hD' (prod_pos (fun i _ => (Fact.out : (p i).Prime).pos))
  let hq' : NeZero q := ⟨hq.ne'⟩
  have : NeZero D' := ⟨hD'.ne'⟩
  have hpq (i : OddFamily N D) : p i ∣ q := dvd_mul_of_dvd_right (dvd_prod_of_mem p (mem_univ i)) _
  have hDq : D' ∣ q := dvd_mul_right _ _
  have h1 := residueDensity_fourier_dvd hDq (ZMod.stdAddChar (N := q))
    (ZMod.isPrimitive_stdAddChar q) (m₀ : ZMod D')
  have h2 := ringDivisorWeight_fourier p ∅ (fun _ => 0) q hpq (oddFamily_injective N D) H hH
  have h3 := h1.mul h2
  obtain ⟨w, hw, hbound⟩ := h3
  refine ⟨q, hq', w, ?_, ?_⟩
  · intro n
    have hn := hw (n : ZMod q)
    dsimp only at hn
    rw [classWeight_ring D' m₀ q hDq n, ringDivisorWeight_natCast] at hn
    unfold sieveWeight
    rw [hn]
    apply sum_congr rfl
    intro a _
    congr 1
    have he := AddChar.map_nsmul_eq_pow (ZMod.stdAddChar (N := q)) n a
    simp only [nsmul_eq_mul] at he
    rw [mul_comm a _, he, stdAddChar_eq_expPhase, ← expPhase_nat_mul, mul_comm]
  · simp only [prod_empty, Nat.cast_one, one_mul] at hbound
    exact hbound

end Weight

/-! ## Rational numbers: the `D`-part and the part coprime to `D` -/

/-- Every prime of `x` divides `D`. -/
def SupportedOn (D x : ℕ) : Prop := ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ x → ℓ ∣ D

lemma supportedOn_coprime (D x y : ℕ) (hx : SupportedOn D x) (hy : Nat.Coprime y D) :
    Nat.Coprime x y := by
  apply Nat.coprime_of_dvd
  intro ℓ hℓ hℓx hℓy
  have h := Nat.dvd_gcd hℓy (hx ℓ hℓ hℓx)
  rw [hy.gcd_eq_one] at h
  exact hℓ.one_lt.ne' (Nat.dvd_one.mp h)

lemma den_eq_one_of_supported_coprime (D : ℕ) (γ : ℚ) (h1 : SupportedOn D γ.den)
    (h2 : Nat.Coprime γ.den D) : γ.den = 1 := by
  have h := supportedOn_coprime D γ.den γ.den h1 h2
  exact (Nat.coprime_self γ.den).mp h

lemma supportedOn_of_dvd {D x y : ℕ} (h : SupportedOn D y) (hxy : x ∣ y) : SupportedOn D x :=
  fun ℓ hℓ hℓx => h ℓ hℓ (hℓx.trans hxy)

lemma supportedOn_mul {D x y : ℕ} (hx : SupportedOn D x) (hy : SupportedOn D y) :
    SupportedOn D (x * y) := by
  intro ℓ hℓ hℓxy
  rcases (Nat.Prime.dvd_mul hℓ).mp hℓxy with h | h
  · exact hx ℓ hℓ h
  · exact hy ℓ hℓ h

lemma supportedOn_of_dvd_D {D x : ℕ} (h : x ∣ D) : SupportedOn D x :=
  fun _ _ hℓx => hℓx.trans h

/-- Partial fractions: `b = α + β` with the denominator of `α` built from primes of `D` and
the denominator of `β` coprime to `D`, both dividing that of `b`. -/
lemma rat_split (D : ℕ) (b : ℚ) :
    ∃ α β : ℚ, b = α + β ∧ SupportedOn D α.den ∧ Nat.Coprime β.den D ∧
      α.den ∣ b.den ∧ β.den ∣ b.den := by
  classical
  set n := b.den with hn
  have hn0 : n ≠ 0 := b.den_nz
  set A := ∏ ℓ ∈ n.primeFactors.filter (· ∣ D), ℓ ^ (n.factorization ℓ) with hA
  set B := ∏ ℓ ∈ n.primeFactors.filter (fun ℓ => ¬ ℓ ∣ D), ℓ ^ (n.factorization ℓ) with hB
  have hAB : A * B = n := by
    rw [hA, hB, prod_filter_mul_prod_filter_not]
    exact Nat.prod_factorization_pow_eq_self hn0
  have hAsupp : SupportedOn D A := by
    intro ℓ hℓ hℓA
    obtain ⟨q, hq, hℓq⟩ := (Prime.dvd_finsetProd_iff hℓ.prime _).mp hℓA
    rw [mem_filter] at hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq.1
    have : ℓ = q := (Nat.prime_dvd_prime_iff_eq hℓ hqp).mp (hℓ.dvd_of_dvd_pow hℓq)
    rw [this]
    exact hq.2
  have hBcop : Nat.Coprime B D := by
    apply Nat.Coprime.prod_left
    intro ℓ hℓ
    rw [mem_filter] at hℓ
    apply Nat.Coprime.pow_left
    exact (Nat.Prime.coprime_iff_not_dvd (Nat.prime_of_mem_primeFactors hℓ.1)).mpr hℓ.2
  have hcop : Nat.Coprime A B := supportedOn_coprime D A B hAsupp hBcop
  obtain ⟨s, t, hst⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  -- s * A + t * B = 1
  have hA0 : (A : ℚ) ≠ 0 := by
    have : A ≠ 0 := by intro h; rw [h, zero_mul] at hAB; exact hn0 hAB.symm
    exact_mod_cast this
  have hB0 : (B : ℚ) ≠ 0 := by
    have : B ≠ 0 := by intro h; rw [h, mul_zero] at hAB; exact hn0 hAB.symm
    exact_mod_cast this
  refine ⟨((b.num * t : ℤ) : ℚ) / A, ((b.num * s : ℤ) : ℚ) / B, ?_, ?_, ?_, ?_, ?_⟩
  · have hb : b = (b.num : ℚ) / ((A : ℚ) * B) := by
      rw [← Nat.cast_mul, hAB, hn]
      exact (Rat.num_div_den b).symm
    have hst' : (s : ℚ) * A + (t : ℚ) * B = 1 := by exact_mod_cast hst
    conv_lhs => rw [hb]
    rw [div_add_div _ _ hA0 hB0]
    congr 1
    push_cast
    linear_combination (-(b.num : ℚ)) * hst'
  · exact supportedOn_of_dvd hAsupp (rat_div_den_dvd _ A)
  · exact Nat.Coprime.coprime_dvd_left (rat_div_den_dvd _ B) hBcop
  · exact (rat_div_den_dvd _ A).trans (hAB ▸ dvd_mul_right A B)
  · exact (rat_div_den_dvd _ B).trans (hAB ▸ dvd_mul_left B A)

/-- Matching a point `α + β` with a centre `j/D + ξ`. -/
lemma match_centre (D : ℕ) (α β ξ : ℚ) (j : ℤ) (hα : SupportedOn D α.den)
    (hβ : Nat.Coprime β.den D) (hξ : Nat.Coprime ξ.den D)
    (h : ∃ k : ℤ, α + β - ((j : ℚ) / D + ξ) = k) :
    (∃ k : ℤ, α - (j : ℚ) / D = k) ∧ (∃ k : ℤ, β - ξ = k) := by
  obtain ⟨k, hk⟩ := h
  set γ := α - (j : ℚ) / D with hγ
  have hγ1 : SupportedOn D γ.den :=
    supportedOn_of_dvd (supportedOn_mul hα (supportedOn_of_dvd_D (rat_div_den_dvd j D)))
      (Rat.sub_den_dvd _ _)
  have hγ' : γ = (ξ - β) + k := by rw [hγ]; linarith
  have hγ2 : Nat.Coprime γ.den D := by
    rw [hγ', Rat.add_intCast_den]
    exact Nat.Coprime.coprime_dvd_left (Rat.sub_den_dvd _ _)
      (Nat.coprime_mul_iff_left.mpr ⟨hξ, hβ⟩)
  have hγint := den_eq_one_of_supported_coprime D γ hγ1 hγ2
  have hγz : (γ.num : ℚ) = γ := (Rat.den_eq_one_iff γ).mp hγint
  refine ⟨⟨γ.num, hγz.symm⟩, ⟨k - γ.num, ?_⟩⟩
  push_cast
  rw [hγz, hγ']
  ring

/-! ## The major-arc coefficient of the actual kernel -/

section Coefficient

variable (N D : ℕ) (r : ℤ) (ρ : RootClassDatum D r) (H : ℝ)

/-- The sign of a kernel term. -/
noncomputable def termSign (T : boundedSieveSets (fun i : OddFamily N D => (i : ℕ)) H) : ℂ :=
  sieveTermSign T.val

/-- The kernel terms: root class weight times one sieve term. -/
noncomputable def termWeight (T : boundedSieveSets (fun i : OddFamily N D => (i : ℕ)) H) :
    ℕ → ℂ :=
  rootTermWeight N D ρ.period ρ.base T.val

/-- The period of a kernel term. -/
noncomputable def termPeriod (T : boundedSieveSets (fun i : OddFamily N D => (i : ℕ)) H) : ℕ :=
  ρ.period * sieveTermPeriod (fun i : OddFamily N D => (i : ℕ)) ∅ T.val

lemma shift_periodic (f : ℕ → ℂ) (t : ℕ) (hf : Function.Periodic f t) :
    Function.Periodic (fun n => f (n+1)) t := by
  intro n
  simp only
  rw [show n + t + 1 = (n + 1) + t by ring]
  exact hf (n+1)

lemma termCoefficient_eq_mean (b : ℚ) (t : ℕ) (ht : 0 < t) (hDt : ρ.period ∣ t)
    (hpt : ∀ i : OddFamily N D, (i : ℕ) ∣ t) (hbt : b.den ∣ t) :
    finiteRationalCoefficient (termSign N D H) (termWeight N D r ρ H) (termPeriod N D r ρ H) b =
      periodicMean (fun n => classWeight ρ.period ρ.base (n+1) * sieveWeight N D H (n+1) *
        expPhase ((b : ℝ) * ((n : ℝ) + 1)^2)) t := by
  unfold finiteRationalCoefficient
  have hterm : ∀ T : boundedSieveSets (fun i : OddFamily N D => (i : ℕ)) H,
      periodicMean (fun m => termWeight N D r ρ H T (m+1) * expPhase ((b : ℝ) * ((m : ℝ) + 1)^2))
        (b.den * termPeriod N D r ρ H T) =
      periodicMean (fun m => termWeight N D r ρ H T (m+1) * expPhase ((b : ℝ) * ((m : ℝ) + 1)^2)) t := by
    intro T
    apply periodicMean_independent
    · exact (Nat.mul_pos b.pos (Nat.mul_pos ρ.period_pos (sieveTermPeriod_pos _ ∅ T.val))).ne'
    · exact ht.ne'
    · exact periodic_rational_quadratic _ _ (rootTermWeight_periodic N D ρ.period ρ.base T.val) b
    · have h1 : Function.Periodic (fun n => classWeight ρ.period ρ.base (n+1)) t :=
        shift_periodic _ t (periodic_mul_of_dvd (classWeight_periodic ρ.period ρ.base) hDt)
      have h2 := sieveTermQuadratic_periodic (fun i : OddFamily N D => (i : ℕ)) ∅ (fun _ => 0)
        T.val b t hpt hbt
      have h3 := h1.mul h2
      intro n
      have := h3 n
      simp only [Pi.mul_apply] at this
      unfold termWeight rootTermWeight
      push_cast at this ⊢
      linear_combination this
  have hsum : ∀ n : ℕ, (∑ T : boundedSieveSets (fun i : OddFamily N D => (i : ℕ)) H,
      termSign N D H T * (termWeight N D r ρ H T (n+1) * expPhase ((b : ℝ) * ((n : ℝ) + 1)^2))) =
      classWeight ρ.period ρ.base (n+1) * sieveWeight N D H (n+1) *
        expPhase ((b : ℝ) * ((n : ℝ) + 1)^2) := by
    intro n
    rw [← rootTerm_sum N D ρ.period ρ.base H (n+1), sum_mul]
    apply sum_congr rfl
    intro T _
    unfold termSign termWeight
    ring
  simp_rw [hterm, ← periodicMean_mul_left]
  rw [← periodicMean_sum]
  congr 1
  funext n
  exact hsum n

lemma sieveWeight_periodic :
    Function.Periodic (sieveWeight N D H) (∏ i : OddFamily N D, (i : ℕ)) := by
  intro n
  unfold sieveWeight actualDivisorWeight
  have hp : ∀ i : OddFamily N D, (i : ℕ) ∣ ∏ i : OddFamily N D, (i : ℕ) :=
    fun i => dvd_prod_of_mem (fun i : OddFamily N D => (i : ℕ)) (mem_univ i)
  rw [actualRootWeight_periodic (fun i : OddFamily N D => (i : ℕ)) ∅ (fun _ => 0) _
    (fun i _ => hp i) n]
  congr 1
  apply sum_congr rfl
  intro T _
  rw [actualSieveWeight_periodic (fun i : OddFamily N D => (i : ℕ)) ∅ T _ (fun i _ => hp i) n]

lemma familyProduct_coprime : Nat.Coprime (∏ i : OddFamily N D, (i : ℕ)) D := by
  apply Nat.Coprime.prod_left
  intro i _
  exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : (i : ℕ).Prime)).mpr (oddFamily_not_dvd N D i)

lemma familyProduct_pos : 0 < ∏ i : OddFamily N D, (i : ℕ) :=
  prod_pos (fun i _ => (Fact.out : (i : ℕ).Prime).pos)

/-- The `D`-part and the coprime part of the major-arc coefficient separate
(the factorization `A_u = A^{(D)} A^{(1)}_u` of `lem:record:kernel-coefficient`). -/
lemma termCoefficient_split (b α β : ℚ) (hb : b = α + β) (hα : SupportedOn D α.den)
    (hβ : Nat.Coprime β.den D) :
    finiteRationalCoefficient (termSign N D H) (termWeight N D r ρ H) (termPeriod N D r ρ H) b =
      periodicMean (fun n => classWeight ρ.period ρ.base (n+1) *
          expPhase ((α : ℝ) * ((n : ℝ) + 1)^2)) (α.den * ρ.period) *
      periodicMean (fun n => sieveWeight N D H (n+1) *
          expPhase ((β : ℝ) * ((n : ℝ) + 1)^2)) (β.den * ∏ i : OddFamily N D, (i : ℕ)) := by
  set Q := ∏ i : OddFamily N D, (i : ℕ) with hQ
  have hQ0 : 0 < Q := familyProduct_pos N D
  have hPA : 0 < α.den * ρ.period := Nat.mul_pos α.pos ρ.period_pos
  have hPB : 0 < β.den * Q := Nat.mul_pos β.pos hQ0
  have : NeZero (α.den * ρ.period) := ⟨hPA.ne'⟩
  have : NeZero (β.den * Q) := ⟨hPB.ne'⟩
  have hcop : Nat.Coprime (α.den * ρ.period) (β.den * Q) := by
    apply supportedOn_coprime D
    · exact supportedOn_mul hα (supportedOn_of_dvd_D ρ.period_dvd)
    · exact Nat.coprime_mul_iff_left.mpr ⟨hβ, familyProduct_coprime N D⟩
  have hbden : b.den ∣ (α.den * ρ.period) * (β.den * Q) := by
    rw [hb]
    apply (Rat.add_den_dvd α β).trans
    exact Nat.mul_dvd_mul (dvd_mul_right _ _) (dvd_mul_right _ _)
  rw [termCoefficient_eq_mean N D r ρ H b _ (Nat.mul_pos hPA hPB)
    ((dvd_mul_left _ _).trans (dvd_mul_right _ _))
    (fun i => (dvd_prod_of_mem (fun i : OddFamily N D => (i : ℕ)) (mem_univ i)).trans
      ((dvd_mul_left _ _).trans (dvd_mul_left _ _))) hbden]
  have hpt : ∀ n : ℕ, classWeight ρ.period ρ.base (n+1) * sieveWeight N D H (n+1) *
      expPhase ((b : ℝ) * ((n : ℝ) + 1)^2) =
      (classWeight ρ.period ρ.base (n+1) * expPhase ((α : ℝ) * ((n : ℝ) + 1)^2)) *
      (sieveWeight N D H (n+1) * expPhase ((β : ℝ) * ((n : ℝ) + 1)^2)) := by
    intro n
    rw [hb]
    push_cast
    rw [add_mul, expPhase_add]
    ring
  simp_rw [hpt]
  apply periodicMean_mul_coprime hcop
  · apply Function.Periodic.mul
    · exact shift_periodic _ _ (periodic_mul_of_dvd (classWeight_periodic ρ.period ρ.base)
        (dvd_mul_left _ _))
    · have h := expPhase_rat_square_periodic α (α.den * ρ.period) (dvd_mul_right _ _)
      intro n
      have := h n
      push_cast at this ⊢
      exact this
  · apply Function.Periodic.mul
    · exact shift_periodic _ _ (periodic_mul_of_dvd (sieveWeight_periodic N D H)
        (dvd_mul_left _ _))
    · have h := expPhase_rat_square_periodic β (β.den * Q) (dvd_mul_right _ _)
      intro n
      have := h n
      push_cast at this ⊢
      exact this

lemma periodicMean_classWeight (D' m₀ : ℕ) (hD' : 0 < D') :
    periodicMean (classWeight D' m₀) D' = 1 := by
  have : NeZero D' := ⟨hD'.ne'⟩
  have hfun : classWeight D' m₀ =
      fun m : ℕ => if ((m : ℕ) : ZMod D') = (m₀ : ZMod D') then (D' : ℂ) else 0 := by
    funext m
    unfold classWeight
    by_cases hm : m ≡ m₀ [MOD D']
    · rw [ite_eq_left hm, ite_eq_left ((ZMod.natCast_eq_natCast_iff m m₀ D').mpr hm)]
    · rw [ite_eq_right hm,
        ite_eq_right (fun h' => hm ((ZMod.natCast_eq_natCast_iff m m₀ D').mp h'))]
  rw [hfun]
  have h := expect_zmod_range (fun x : ZMod D' => if x = (m₀ : ZMod D') then (D' : ℂ) else 0)
  rw [← h, expect_eq_sum_div_card]
  simp only [sum_ite_eq', mem_univ, ite_true, card_univ, ZMod.card]
  exact div_self (by exact_mod_cast hD'.ne')

/-- The root factor at a `D`-part dividing `D` is `e(α r)` (`lem:kernel-depth-classes`). -/
lemma rootMean_of_dvd (α : ℚ) (hα : α.den ∣ D) :
    periodicMean (fun n => classWeight ρ.period ρ.base (n+1) *
      expPhase ((α : ℝ) * ((n : ℝ) + 1)^2)) (α.den * ρ.period) = expPhase ((α : ℝ) * r) := by
  have hpt : ∀ n : ℕ, classWeight ρ.period ρ.base (n+1) * expPhase ((α : ℝ) * ((n : ℝ) + 1)^2) =
      expPhase ((α : ℝ) * r) * classWeight ρ.period ρ.base (n+1) := by
    intro n
    by_cases hn : (n+1) ≡ ρ.base [MOD ρ.period]
    · obtain ⟨k, hk⟩ := ρ.root (n+1) hn
      obtain ⟨e, he⟩ := hα
      have hαD : (α : ℝ) * D = (α.num * e : ℤ) := by
        have h1 : (α : ℝ) = (α.num : ℝ) / α.den := by exact_mod_cast (Rat.num_div_den α).symm
        have h2 : (D : ℝ) = (α.den : ℝ) * e := by exact_mod_cast he
        rw [h1, h2]
        push_cast
        field_simp [(Nat.cast_ne_zero.mpr α.den_nz : (α.den : ℝ) ≠ 0)]
      have hsq : ((n : ℝ) + 1)^2 = (r : ℝ) + (D : ℝ) * k := by
        have := congrArg (fun z : ℤ => (z : ℝ)) hk
        push_cast at this
        linarith
      have he2 : (α : ℝ) * ((n : ℝ) + 1)^2 = (α : ℝ) * r + ((α.num * e * k : ℤ) : ℝ) := by
        rw [hsq]
        push_cast at hαD ⊢
        linear_combination (k : ℝ) * hαD
      rw [he2, expPhase_add, expPhase_int, mul_one, mul_comm]
    · unfold classWeight
      rw [ite_eq_right hn]
      ring
  simp_rw [hpt]
  rw [periodicMean_mul_left]
  have hper := classWeight_periodic ρ.period ρ.base
  rw [periodicMean_shift_one _ _ (periodic_mul_of_dvd hper (dvd_mul_left _ _))]
  rw [periodicMean_of_dvd _ _ _ (Nat.mul_pos α.pos ρ.period_pos).ne' (dvd_mul_left _ _) hper]
  rw [periodicMean_classWeight _ _ ρ.period_pos, mul_one]

/-- The root factor vanishes when the `D`-part does not divide `D`. -/
lemma rootMean_vanish (α : ℚ) (hsupp : SupportedOn D α.den) (hnd : ¬ α.den ∣ D) :
    periodicMean (fun n => classWeight ρ.period ρ.base (n+1) *
      expPhase ((α : ℝ) * ((n : ℝ) + 1)^2)) (α.den * ρ.period) = 0 := by
  have hper : Function.Periodic
      (fun m => classWeight ρ.period ρ.base m * expPhase ((α : ℝ) * (m : ℝ) ^ 2))
      (α.den * ρ.period) := by
    apply Function.Periodic.mul
    · exact periodic_mul_of_dvd (classWeight_periodic ρ.period ρ.base) (dvd_mul_left _ _)
    · exact periodic_mul_of_dvd (expPhase_rat_sq_periodic α) (dvd_mul_right _ _)
  have h := periodicMean_shift_one _ _ hper
  have h' : (fun n => classWeight ρ.period ρ.base (n+1) * expPhase ((α : ℝ) * ((n : ℝ) + 1)^2)) =
      (fun n => classWeight ρ.period ρ.base (n+1) * expPhase ((α : ℝ) * (((n+1 : ℕ)) : ℝ) ^ 2)) := by
    funext n; push_cast; rfl
  rw [h', h]
  exact ρ.vanish α hsupp hnd

/-- The coprime part of the coefficient is the upstream coefficient with no root primes. -/
lemma sieveMean_bound (h2 : 2 ∣ D) (hH : 0 < H) (β : ℚ) (hβ : Nat.Coprime β.den D)
    (hβN : β.den ≤ N) :
    ‖periodicMean (fun n => sieveWeight N D H (n+1) *
        expPhase ((β : ℝ) * ((n : ℝ) + 1)^2)) (β.den * ∏ i : OddFamily N D, (i : ℕ)) -
      kernelModelCoefficient (fun i : OddFamily N D => (i : ℕ)) ∅ (fun _ => 0) H β‖ ≤
      2^64 * H^(-(1 : ℝ)/3) := by
  have hQ0 := familyProduct_pos N D
  have h := finiteRationalCoefficient_actual (fun i : OddFamily N D => (i : ℕ)) ∅ (fun _ => 0) H β
    (β.den * ∏ i : OddFamily N D, (i : ℕ)) (Nat.mul_pos β.pos hQ0)
    (fun i => (dvd_prod_of_mem (fun i : OddFamily N D => (i : ℕ)) (mem_univ i)).trans
      (dvd_mul_left _ _)) (dvd_mul_right _ _)
  unfold sieveWeight
  have h' : periodicMean (fun n => actualDivisorWeight (fun i : OddFamily N D => (i : ℕ)) ∅
      (fun _ => 0) H (n+1) * expPhase ((β : ℝ) * ((n : ℝ) + 1)^2))
        (β.den * ∏ i : OddFamily N D, (i : ℕ)) =
      finiteRationalCoefficient (fun T : boundedSieveSets (fun i : OddFamily N D => (i : ℕ)) H =>
        sieveTermSign T.val) (fun T => sieveTermWeight (fun i : OddFamily N D => (i : ℕ)) ∅
          (fun _ => 0) T.val) (fun T => sieveTermPeriod (fun i : OddFamily N D => (i : ℕ)) ∅ T.val) β := by
    rw [h]
  rw [h']
  exact finiteRationalCoefficient_actual_uniform (fun i : OddFamily N D => (i : ℕ)) ∅ (fun _ => 0)
    (oddFamily_injective N D) H hH (oddFamily_two N D h2) β (oddFamily_cover N D β hβN hβ)

lemma primaryModulus_ne_self {q ℓ : ℕ} (hq : q ≠ 0) (hℓ : ℓ.Prime) (h : ℓ * ℓ ∣ q) :
    primaryModulus q ℓ ≠ ℓ := by
  rw [primaryModulus_of_dvd hq hℓ ((dvd_mul_right ℓ ℓ).trans h)]
  have h2 : 2 ≤ q.factorization ℓ := by
    rw [← hℓ.pow_dvd_iff_le_factorization hq, pow_two]
    exact h
  intro he
  have : ℓ ^ 2 ≤ ℓ ^ (q.factorization ℓ) := Nat.pow_le_pow_right hℓ.pos h2
  rw [he, pow_two] at this
  have := hℓ.two_le
  nlinarith

/-- The upstream model coefficient with no root primes is `g` on `Ξ_{H,D}` and `0` off it. -/
lemma kappa_formula (h2 : 2 ∣ D) (hH : 0 ≤ H) (β : ℚ) (hβ : Nat.Coprime β.den D)
    (hβN : β.den ≤ N) :
    kernelModelCoefficient (fun i : OddFamily N D => (i : ℕ)) ∅ (fun _ => 0) H β =
      if Int.fract β ∈ frequencySet H D then unitQuadraticAverage (Int.fract β) else 0 := by
  classical
  rw [← kernelModelCoefficient_fract]
  set ξ := Int.fract β with hξdef
  have hξden : ξ.den = β.den := Rat.den_intFract β
  have hinj := oddFamily_injective N D
  have htwo := oddFamily_two N D h2
  have hcov : ξ.den ∣ ∏ i : OddFamily N D, primaryModulus ξ.den (i : ℕ) :=
    oddFamily_cover N D ξ (hξden ▸ hβN) (hξden ▸ hβ)
  by_cases hsq : Squarefree ξ.den
  · have hrsm : rootSquareModulus (fun i : OddFamily N D => (i : ℕ)) ∅ = 1 := by
      simp [rootSquareModulus]
    have hc := kernelModelCoefficient_centre (fun i : OddFamily N D => (i : ℕ)) ∅ (fun _ => 0)
      hinj htwo 0 (fun n _ => by rw [hrsm]; exact one_dvd _) H 0 ξ hsq
      (by rw [hrsm]; exact Nat.coprime_one_right _)
      (fun ℓ hℓ hℓξ => oddFamily_exists N D ℓ hℓ ((Nat.le_of_dvd ξ.pos hℓξ).trans (hξden ▸ hβN))
        (fun hℓD => by
          have h := Nat.dvd_gcd hℓξ hℓD
          rw [(hξden ▸ hβ : Nat.Coprime ξ.den D).gcd_eq_one] at h
          exact hℓ.one_lt.ne' (Nat.dvd_one.mp h)))
    rw [hrsm] at hc
    simp only [Int.cast_zero, zero_div, zero_add, zero_mul, expPhase_zero, one_mul] at hc
    rw [hc]
    have hmem : ξ ∈ frequencySet H D ↔ (ξ.den : ℝ) ≤ H := by
      rw [mem_frequencySet hH]
      constructor
      · intro h; exact h.2.2.1
      · intro h
        exact ⟨Int.fract_nonneg β, Int.fract_lt_one β, h, hsq, hξden ▸ hβ⟩
    by_cases hle : (ξ.den : ℝ) ≤ H
    · rw [ite_eq_left hle, ite_eq_left (hmem.mpr hle)]
    · rw [ite_eq_right hle, ite_eq_right (fun h => hle (hmem.mp h))]
  · have hnot : ξ ∉ frequencySet H D := fun h => hsq ((mem_frequencySet hH D ξ).mp h).2.2.2.1
    rw [ite_eq_right hnot]
    rw [← primaryModelCoefficient_eq_kernelModel (fun i : OddFamily N D => (i : ℕ)) ∅ (fun _ => 0)
      hinj ξ hcov H htwo]
    unfold primaryModelCoefficient
    rw [ite_eq_right]
    rintro ⟨_, hsqf⟩
    apply hsq
    rw [Nat.squarefree_iff_prime_squarefree]
    intro ℓ hℓ hℓℓ
    have hℓξ : ℓ ∣ ξ.den := (dvd_mul_right ℓ ℓ).trans hℓℓ
    obtain ⟨i, hi⟩ := oddFamily_exists N D ℓ hℓ ((Nat.le_of_dvd ξ.pos hℓξ).trans (hξden ▸ hβN))
      (fun hℓD => by
        have h := Nat.dvd_gcd hℓξ hℓD
        rw [(hξden ▸ hβ : Nat.Coprime ξ.den D).gcd_eq_one] at h
        exact hℓ.one_lt.ne' (Nat.dvd_one.mp h))
    have hiact : i ∈ primaryActive (fun i : OddFamily N D => (i : ℕ)) ξ.den \ ∅ := by
      simp [hi, hℓξ]
    have := hsqf i hiact
    simp only at this
    rw [hi] at this
    exact primaryModulus_ne_self ξ.den_nz hℓ hℓℓ this

end Coefficient

/-! ## The model kernel: centres `j/D + ξ` with coefficients `e(j r/D) g(ξ)` -/

/-- The index set of the centres: `0 ≤ j < D`, `ξ ∈ Ξ_{H,D}`. -/
abbrev CentreIndex (H : ℝ) (D : ℕ) := {x : ℕ × ℚ // x ∈ range D ×ˢ frequencySet H D}

/-- The centre `j/D + ξ` (`lem:record:K20-centres`). -/
noncomputable def centre (H : ℝ) (D : ℕ) (x : CentreIndex H D) : ℚ := (x.1.1 : ℚ) / D + x.1.2

/-- The coefficient `e(j r/D) g(ξ)` of the centre `j/D + ξ` (`lem:record:K20-centres`). -/
noncomputable def centreCoeff (H : ℝ) (D : ℕ) (r : ℤ) (x : CentreIndex H D) : ℂ :=
  expPhase ((x.1.1 : ℝ) * r / D) * unitQuadraticAverage x.1.2

lemma norm_unitQuadraticAverage (ξ : ℚ) : ‖unitQuadraticAverage ξ‖ ≤ 1 := by
  unfold unitQuadraticAverage
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have hcard : ((range ξ.den).filter (fun m => Nat.Coprime m ξ.den)).card = Nat.totient ξ.den := by
    rw [Nat.totient]
    congr 1
    apply filter_congr
    intro m _
    exact Nat.coprime_comm
  have hsum : ‖∑ m ∈ (range ξ.den).filter (fun m => Nat.Coprime m ξ.den),
      expPhase ((ξ : ℝ) * (m : ℝ)^2)‖ ≤ Nat.totient ξ.den := by
    apply (norm_sum_le _ _).trans
    simp only [norm_expPhase, sum_const, nsmul_eq_mul, mul_one]
    rw [hcard]
  have htot : (0 : ℝ) < Nat.totient ξ.den := by exact_mod_cast Nat.totient_pos.mpr ξ.pos
  calc ((Nat.totient ξ.den : ℕ) : ℝ)⁻¹ * ‖∑ m ∈ (range ξ.den).filter (fun m => Nat.Coprime m ξ.den),
      expPhase ((ξ : ℝ) * (m : ℝ)^2)‖ ≤ ((Nat.totient ξ.den : ℕ) : ℝ)⁻¹ * Nat.totient ξ.den :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 := inv_mul_cancel₀ htot.ne'

lemma norm_centreCoeff (H : ℝ) (D : ℕ) (r : ℤ) (x : CentreIndex H D) : ‖centreCoeff H D r x‖ ≤ 1 := by
  unfold centreCoeff
  rw [norm_mul, norm_expPhase, one_mul]
  exact norm_unitQuadraticAverage _

section ModelCoefficient

variable (N D : ℕ) (r : ℤ) (ρ : RootClassDatum D r) (H : ℝ)

/-- The coefficient comparison on the major arcs (`lem:record:kernel-coefficient`). -/
lemma termCoefficient_model_bound (h2 : 2 ∣ D) (hD : 0 < D) (hH : 0 < H) (b : ℚ)
    (hbN : b.den ≤ N) :
    ‖finiteRationalCoefficient (termSign N D H) (termWeight N D r ρ H) (termPeriod N D r ρ H) b -
      modelCenterCoefficient (centre H D) (centreCoeff H D r) b‖ ≤ 2^64 * H^(-(1 : ℝ)/3) := by
  classical
  obtain ⟨α, β, hb, hα, hβ, _, hβb⟩ := rat_split D b
  have hβN : β.den ≤ N := (Nat.le_of_dvd b.pos hβb).trans hbN
  rw [termCoefficient_split N D r ρ H b α β hb hα hβ]
  have hC := sieveMean_bound N D H h2 hH β hβ hβN
  rw [kappa_formula N D H h2 hH.le β hβ hβN] at hC
  have hE : (0 : ℝ) ≤ 2^64 * H^(-(1 : ℝ)/3) := by positivity
  -- the matching criterion
  have hmatch : ∀ x : CentreIndex H D, (∃ k : ℤ, b - centre H D x = k) →
      (∃ k : ℤ, α - ((x.1.1 : ℤ) : ℚ) / D = k) ∧ (∃ k : ℤ, β - x.1.2 = k) := by
    intro x hx
    have hxξ : x.1.2 ∈ frequencySet H D := (mem_product.mp x.2).2
    have hξcop := ((mem_frequencySet hH.le D x.1.2).mp hxξ).2.2.2.2
    apply match_centre D α β x.1.2 (x.1.1 : ℤ) hα hβ hξcop
    rw [← hb]
    unfold centre at hx
    push_cast at hx ⊢
    exact hx
  by_cases hαD : α.den ∣ D
  · rw [rootMean_of_dvd D r ρ α hαD]
    -- the residue `j₀` with `α ≡ j₀ / D`
    obtain ⟨e, he⟩ := hαD
    have hαD' : (α : ℚ) * D = (α.num * e : ℤ) := by
      have hD' : (D : ℚ) = (α.den : ℚ) * e := by exact_mod_cast he
      rw [hD', ← mul_assoc, Rat.mul_den_eq_num]
      push_cast
      ring
    set n₀ : ℤ := α.num * e with hn₀
    set j₀ : ℕ := (n₀ % (D : ℤ)).toNat with hj₀
    have hj₀z : (j₀ : ℤ) = n₀ % (D : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hD.ne'))
    have hj₀D : j₀ < D := by
      have := Int.emod_lt_of_pos n₀ (show (0 : ℤ) < D by exact_mod_cast hD)
      omega
    have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    have hαj : α = (j₀ : ℚ) / D + ((n₀ / (D : ℤ) : ℤ) : ℚ) := by
      have h1 : (j₀ : ℚ) = (n₀ : ℚ) - (D : ℚ) * ((n₀ / (D : ℤ) : ℤ) : ℚ) := by
        have := hj₀z
        rw [Int.emod_def] at this
        exact_mod_cast this
      rw [h1]
      field_simp
      rw [← hαD']
      ring
    have hphase : expPhase ((α : ℝ) * r) = expPhase ((j₀ : ℝ) * r / D) := by
      have : (α : ℝ) * r = (j₀ : ℝ) * r / D + (((n₀ / (D : ℤ)) * r : ℤ) : ℝ) := by
        rw [hαj]
        push_cast
        ring
      rw [this, expPhase_add, expPhase_int, mul_one]
    rw [hphase]
    by_cases hξ : Int.fract β ∈ frequencySet H D
    · rw [ite_eq_left hξ] at hC
      set x₀ : CentreIndex H D := ⟨(j₀, Int.fract β), mem_product.mpr ⟨mem_range.mpr hj₀D, hξ⟩⟩
      have hmcc : modelCenterCoefficient (centre H D) (centreCoeff H D r) b = centreCoeff H D r x₀ := by
        unfold modelCenterCoefficient
        rw [Fintype.sum_eq_single x₀]
        · rw [ite_eq_left]
          refine ⟨(n₀ / (D : ℤ)) + ⌊β⌋, ?_⟩
          unfold centre
          rw [hb, hαj]
          simp only [x₀, Int.fract]
          push_cast
          ring
        · intro x hx
          rw [ite_eq_right]
          intro hxm
          apply hx
          obtain ⟨⟨k₁, hk₁⟩, ⟨k₂, hk₂⟩⟩ := hmatch x hxm
          have hxξ : x.1.2 ∈ frequencySet H D := (mem_product.mp x.2).2
          have hx01 := (mem_frequencySet hH.le D x.1.2).mp hxξ
          have hxj : x.1.1 < D := mem_range.mp (mem_product.mp x.2).1
          -- second coordinate
          have h2' : x.1.2 = Int.fract β := by
            have : Int.fract β = Int.fract x.1.2 := by
              rw [show β = x.1.2 + k₂ by linarith, Int.fract_add_intCast]
            rw [this, Int.fract_eq_self.mpr ⟨hx01.1, hx01.2.1⟩]
          -- first coordinate
          have h1' : x.1.1 = j₀ := by
            set m : ℤ := k₁ - n₀ / (D : ℤ) with hm
            have e1 : (j₀ : ℚ) / D - (x.1.1 : ℚ) / D = (m : ℚ) := by
              have := hk₁
              rw [hαj] at this
              rw [hm]
              push_cast at this ⊢
              linarith
            have e2 : (j₀ : ℚ) - (x.1.1 : ℚ) = (D : ℚ) * ((j₀ : ℚ) / D - (x.1.1 : ℚ) / D) := by
              field_simp
            rw [e1] at e2
            have e3 : (((j₀ : ℤ) - (x.1.1 : ℤ) : ℤ) : ℚ) = (((D : ℤ) * m : ℤ) : ℚ) := by
              push_cast
              linarith
            have hk' : (j₀ : ℤ) - (x.1.1 : ℤ) = (D : ℤ) * m := Int.cast_injective e3
            have hxjz : (x.1.1 : ℤ) < D := by exact_mod_cast hxj
            have hj₀z' : (j₀ : ℤ) < D := by exact_mod_cast hj₀D
            have hDz : (0 : ℤ) < D := by exact_mod_cast hD
            rcases lt_trichotomy m 0 with hneg | h0 | hpos
            · have : (D : ℤ) * m ≤ -(D : ℤ) := by nlinarith
              omega
            · rw [h0, mul_zero] at hk'
              omega
            · have : (D : ℤ) ≤ (D : ℤ) * m := by nlinarith
              omega
          exact Subtype.ext (Prod.ext h1' h2')
      rw [hmcc]
      unfold centreCoeff
      simp only [x₀]
      rw [← mul_sub, norm_mul, norm_expPhase, one_mul]
      exact hC
    · rw [ite_eq_right hξ, sub_zero] at hC
      have hmcc : modelCenterCoefficient (centre H D) (centreCoeff H D r) b = 0 := by
        unfold modelCenterCoefficient
        apply sum_eq_zero
        intro x _
        rw [ite_eq_right]
        intro hxm
        obtain ⟨_, ⟨k₂, hk₂⟩⟩ := hmatch x hxm
        have hxξ : x.1.2 ∈ frequencySet H D := (mem_product.mp x.2).2
        have hx01 := (mem_frequencySet hH.le D x.1.2).mp hxξ
        apply hξ
        have : Int.fract β = x.1.2 := by
          rw [show β = x.1.2 + k₂ by linarith, Int.fract_add_intCast,
            Int.fract_eq_self.mpr ⟨hx01.1, hx01.2.1⟩]
        rw [this]
        exact hxξ
      rw [hmcc, sub_zero, norm_mul, norm_expPhase, one_mul]
      exact hC
  · rw [rootMean_vanish D r ρ α hα hαD, zero_mul]
    have hmcc : modelCenterCoefficient (centre H D) (centreCoeff H D r) b = 0 := by
      unfold modelCenterCoefficient
      apply sum_eq_zero
      intro x _
      rw [ite_eq_right]
      intro hxm
      obtain ⟨⟨k₁, hk₁⟩, _⟩ := hmatch x hxm
      apply hαD
      have : α = ((x.1.1 : ℤ) : ℚ) / D + k₁ := by linarith
      rw [this, Rat.add_intCast_den]
      exact rat_div_den_dvd _ D
    rw [hmcc, sub_zero, norm_zero]
    exact hE

end ModelCoefficient

/-! ## The uniform approximation for general moduli -/

section Uniform

variable (N D : ℕ) (r : ℤ) (ρ : RootClassDatum D r) (H : ℝ)

lemma termCost (hH : 0 ≤ H) :
    (∑ T : boundedSieveSets (fun i : OddFamily N D => (i : ℕ)) H,
      ‖termSign N D H T‖ * (2 * (termPeriod N D r ρ H T : ℝ) + 1) * (ρ.period : ℝ)) ≤
      H * (2 * (ρ.period : ℝ) * H + 1) * ρ.period := by
  calc _ ≤ ∑ _T : boundedSieveSets (fun i : OddFamily N D => (i : ℕ)) H,
        (2 * (ρ.period : ℝ) * H + 1) * ρ.period := by
        apply sum_le_sum
        intro T _
        unfold termSign termPeriod
        rw [sieveTermSign_norm, one_mul]
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        apply add_le_add _ le_rfl
        have ht := (mem_filter.mp T.property).2
        unfold sieveTermPeriod
        simp only [prod_empty, one_mul, Nat.cast_mul]
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left ht (by positivity)
    _ = (Fintype.card (boundedSieveSets (fun i : OddFamily N D => (i : ℕ)) H) : ℝ) *
        ((2 * (ρ.period : ℝ) * H + 1) * ρ.period) := by simp
    _ ≤ _ := by
      have hc := boundedSieveSets_card (fun i : OddFamily N D => (i : ℕ)) (oddFamily_injective N D) H hH
      nlinarith [show 0 ≤ (2 * (ρ.period : ℝ) * H + 1) * ρ.period by positivity]

lemma centreCoeff_sum (hH : 0 ≤ H) (L : ℕ) (hL : (D : ℝ) * H ≤ L) (hD : 1 ≤ D) :
    (∑ x : CentreIndex H D, ‖centreCoeff H D r x‖) ≤ (L : ℝ)^2 := by
  calc _ ≤ ∑ _x : CentreIndex H D, (1 : ℝ) := sum_le_sum (fun x _ => norm_centreCoeff H D r x)
    _ = ((range D ×ˢ frequencySet H D).card : ℝ) := by simp
    _ ≤ (D : ℝ) * H^2 := by
        rw [card_product, card_range, Nat.cast_mul]
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        have h1 : (frequencySet H D).card ≤ (boundedRationals ⌊H⌋₊).card := card_filter_le _ _
        have h2 := boundedRationals_card ⌊H⌋₊
        have h3 : ((⌊H⌋₊ : ℕ) : ℝ) ≤ H := Nat.floor_le hH
        calc ((frequencySet H D).card : ℝ) ≤ ((⌊H⌋₊ ^ 2 : ℕ) : ℝ) := by exact_mod_cast h1.trans h2
          _ = ((⌊H⌋₊ : ℕ) : ℝ)^2 := by push_cast; ring
          _ ≤ H^2 := by gcongr
    _ ≤ ((D : ℝ) * H)^2 := by
        have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
        nlinarith [sq_nonneg H, sq_nonneg ((D : ℝ) * H)]
    _ ≤ (L : ℝ)^2 := by
        have h0 : 0 ≤ (D : ℝ) * H := by positivity
        gcongr

lemma centre_den_le (hH : 0 ≤ H) (hD : 0 < D) (x : CentreIndex H D) :
    (centre H D x).den ≤ ⌈(D : ℝ) * H⌉₊ := by
  have hm := centre_mem_boundedRationals D hD H hH x.1.1 x.1.2 (mem_product.mp x.2).2
  rw [mem_boundedRationals, Rat.den_intFract] at hm
  exact hm.2.2

end Uniform

/-- **Uniform kernel approximation for general moduli at `β = κ = 1/20`**
(`lem:record:K20-approx` at the exponents of `cor:kernel20`, for any even modulus with a
root class): `‖S(α) - S₀(α)‖ ≤ C H^(-1/3)`, where `S` is the actual-square transform with
the root class and unit sieve weights, and `S₀` the model transform with centres
`j/D + ξ` and coefficients `e(j r/D) g(ξ)`. -/
theorem general_kernel_rate (CD CH : ℝ) (hCD : 1 ≤ CD) (hCH : 1 ≤ CH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ D : ℕ, 2 ∣ D → 0 < D → (D : ℝ) ≤ CD * (N : ℝ) ^ ((1 : ℝ) / 20) →
      ∀ (r : ℤ) (ρ : RootClassDatum D r),
      ∀ H : ℝ, CH⁻¹ * (N : ℝ) ^ ((1 : ℝ) / 40) ≤ H → H ≤ CH * (N : ℝ) ^ ((1 : ℝ) / 40) →
      ∀ α : ℝ, ‖finiteSquareKernel (termSign N D H) (termWeight N D r ρ H) N.sqrt N α -
        ∑ x : CentreIndex H D, centreCoeff H D r x * normalizedLinearSum N (α - centre H D x)‖ ≤
          C * H ^ (-(1 : ℝ) / 3) := by
  refine ⟨twentiethRateConstant CD CH, twentiethRateConstant_pos CD CH hCD hCH,
    twentiethThreshold CD CH, ?_⟩
  intro N hN D h2 hDpos hD r ρ H hHlo hHhi α
  have hCD0 : 0 ≤ CD := by linarith
  have hCH0 : 0 < CH := by linarith
  have hK8 : (8 : ℝ) ≤ max 8 (4 * CD * CH) := le_max_left _ _
  have hK4 : 4 * CD * CH ≤ max 8 (4 * CD * CH) := le_max_right _ _
  have hK0 : 0 < max 8 (4 * CD * CH) := by linarith
  have hnK : (max 8 (4 * CD * CH)) ^ 40 ≤ (N : ℝ) := by
    have h : ((twentiethThreshold CD CH : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    exact (Nat.le_ceil _).trans h
  have hn1 : (1 : ℝ) ≤ N := by
    have : (1 : ℝ) ≤ (max 8 (4 * CD * CH)) ^ 40 := one_le_pow₀ (by linarith)
    linarith
  have hn0 : (0 : ℝ) < N := by linarith
  have hN1 : 1 ≤ N := by exact_mod_cast hn1
  have hroot : max 8 (4 * CD * CH) ≤ (N : ℝ) ^ ((1 : ℝ) / 40) := by
    have h := Real.rpow_le_rpow (by positivity) hnK (by norm_num : (0 : ℝ) ≤ 1 / 40)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le] at h
    norm_num at h
    exact max_le h.1 h.2
  have hpow : ∀ e : ℝ, (1 : ℝ) / 40 ≤ e → max 8 (4 * CD * CH) ≤ (N : ℝ) ^ e :=
    fun e he => hroot.trans (rpow_mono_one hn1 he)
  have hH1 : 1 ≤ H := by
    have h1 : CH⁻¹ * (4 * CD * CH) ≤ CH⁻¹ * (N : ℝ) ^ ((1 : ℝ) / 40) :=
      mul_le_mul_of_nonneg_left (hK4.trans hroot) (inv_nonneg.mpr hCH0.le)
    have h2 : CH⁻¹ * (4 * CD * CH) = 4 * CD := by field_simp
    linarith
  have hH0 : 0 < H := by linarith
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hDpos
  have hP0 : (0 : ℝ) ≤ (ρ.period : ℝ) := Nat.cast_nonneg _
  have hPD : (ρ.period : ℝ) ≤ (D : ℝ) := by
    exact_mod_cast Nat.le_of_dvd hDpos ρ.period_dvd
  have hDH : 1 ≤ (D : ℝ) * H := by nlinarith
  have hDHn : (D : ℝ) * H ≤ CD * CH * (N : ℝ) ^ ((3 : ℝ) / 40) := by
    calc (D : ℝ) * H ≤ (CD * (N : ℝ) ^ ((1 : ℝ) / 20)) * (CH * (N : ℝ) ^ ((1 : ℝ) / 40)) := by
          gcongr
      _ = CD * CH * ((N : ℝ) ^ ((1 : ℝ) / 20) * (N : ℝ) ^ ((1 : ℝ) / 40)) := by ring
      _ = CD * CH * (N : ℝ) ^ ((3 : ℝ) / 40) := by rw [← Real.rpow_add hn0]; norm_num
  have hLD : (⌈(D : ℝ) * H⌉₊ : ℝ) ≤ 2 * (D : ℝ) * H := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ (D : ℝ) * H by linarith)
    linarith
  have hmodel : (D : ℝ) * H ≤ (⌈(D : ℝ) * H⌉₊ : ℝ) := Nat.le_ceil _
  have hp7 : 0 < (N : ℝ) ^ ((7 : ℝ) / 10) := Real.rpow_pos_of_pos hn0 _
  have hT : 0 < ⌈(N : ℝ) ^ ((7 : ℝ) / 10)⌉₊ := Nat.ceil_pos.mpr hp7
  have hTlo : (N : ℝ) ^ ((7 : ℝ) / 10) ≤ (⌈(N : ℝ) ^ ((7 : ℝ) / 10)⌉₊ : ℝ) := Nat.le_ceil _
  have hThi : (⌈(N : ℝ) ^ ((7 : ℝ) / 10)⌉₊ : ℝ) ≤ 2 * (N : ℝ) ^ ((7 : ℝ) / 10) := by
    have h := Nat.ceil_lt_add_one hp7.le
    have h1 : 1 ≤ (N : ℝ) ^ ((7 : ℝ) / 10) := Real.one_le_rpow hn1 (by norm_num)
    linarith
  have hLT : 2 * ⌈(D : ℝ) * H⌉₊ ≤ ⌈(N : ℝ) ^ ((7 : ℝ) / 10)⌉₊ + 1 := by
    have h1 : 2 * (⌈(D : ℝ) * H⌉₊ : ℝ) ≤ (N : ℝ) ^ ((7 : ℝ) / 10) := by
      calc 2 * (⌈(D : ℝ) * H⌉₊ : ℝ) ≤ 4 * ((D : ℝ) * H) := by linarith
        _ ≤ 4 * (CD * CH * (N : ℝ) ^ ((3 : ℝ) / 40)) := by gcongr
        _ = (4 * CD * CH) * (N : ℝ) ^ ((3 : ℝ) / 40) := by ring
        _ ≤ (N : ℝ) ^ ((5 : ℝ) / 8) * (N : ℝ) ^ ((3 : ℝ) / 40) := by
          gcongr
          exact hK4.trans (hpow _ (by norm_num))
        _ = (N : ℝ) ^ ((7 : ℝ) / 10) := by rw [← Real.rpow_add hn0]; norm_num
    have h2 : ((2 * ⌈(D : ℝ) * H⌉₊ : ℕ) : ℝ) ≤ (⌈(N : ℝ) ^ ((7 : ℝ) / 10)⌉₊ : ℝ) := by
      push_cast
      linarith
    have h3 : 2 * ⌈(D : ℝ) * H⌉₊ ≤ ⌈(N : ℝ) ^ ((7 : ℝ) / 10)⌉₊ := by exact_mod_cast h2
    omega
  have hX : (8 : ℝ) ≤ (N : ℝ) ^ ((3 : ℝ) / 10) := hK8.trans (hpow _ (by norm_num))
  have hLX : (⌈(D : ℝ) * H⌉₊ : ℝ) ≤ (N : ℝ) ^ ((3 : ℝ) / 10) := by
    have h9 := hpow ((9 : ℝ) / 40) (by norm_num)
    have hK2 : 2 * CD * CH ≤ (N : ℝ) ^ ((9 : ℝ) / 40) := by nlinarith
    calc (⌈(D : ℝ) * H⌉₊ : ℝ) ≤ 2 * ((D : ℝ) * H) := by linarith
      _ ≤ 2 * (CD * CH * (N : ℝ) ^ ((3 : ℝ) / 40)) := by gcongr
      _ = (2 * CD * CH) * (N : ℝ) ^ ((3 : ℝ) / 40) := by ring
      _ ≤ (N : ℝ) ^ ((9 : ℝ) / 40) * (N : ℝ) ^ ((3 : ℝ) / 40) := by gcongr
      _ = (N : ℝ) ^ ((3 : ℝ) / 10) := by rw [← Real.rpow_add hn0]; norm_num
  have hXN : (N : ℝ) ^ ((3 : ℝ) / 10) ≤ N := Real.rpow_le_self_of_one_le hn1 (by norm_num)
  obtain ⟨hM, hlo, hhi, hMn⟩ := natural_sqrt_bounds N hN1
  obtain ⟨q, hq, w, hw, hwn⟩ := rootWeight_fourier N D ρ.period ρ.base ρ.period_pos H hH0.le
  have hf := finite_kernel_uniform (termSign N D H) (termWeight N D r ρ H) (termPeriod N D r ρ H)
    (fun T => Nat.mul_pos ρ.period_pos (sieveTermPeriod_pos _ ∅ T.val))
    (fun T => rootTermWeight_periodic N D ρ.period ρ.base T.val)
    (fun _ => (ρ.period : ℝ)) (fun _ => Nat.cast_nonneg _)
    (fun T m => norm_rootTermWeight N D ρ.period ρ.base T.val m)
    (centre H D) (centreCoeff H D r) ⌈(D : ℝ) * H⌉₊ ⌈(N : ℝ) ^ ((7 : ℝ) / 10)⌉₊
    ((N : ℝ) ^ ((3 : ℝ) / 10)) (2^64 * H^(-(1 : ℝ)/3)) hT hLT
    (fun x => centre_den_le D H hH0.le hDpos x) hX hLX (by positivity)
    (fun b hb => termCoefficient_model_bound N D r ρ H h2 hDpos hH0 b
      (by exact_mod_cast hb.trans hXN))
    w (fun a : ZMod q => (a.val : ℝ) / q)
    (fun m => by
      unfold termSign termWeight
      rw [rootTerm_sum, hw m]) N.sqrt N hM hlo hhi α
  refine hf.trans ?_
  have hcost := termCost N D r ρ H hH0.le
  have hwz := centreCoeff_sum D r H hH0.le ⌈(D : ℝ) * H⌉₊ hmodel hDpos
  have hX0 : 0 ≤ (N : ℝ) ^ ((3 : ℝ) / 10) := by positivity
  calc _ ≤ 2^64 * H^(-(1 : ℝ)/3) +
        (H * (2 * (ρ.period : ℝ) * H + 1) * ρ.period) *
          (4 * (N : ℝ) ^ ((3 : ℝ) / 10) + 8 * Real.pi * N / ((⌈(N : ℝ) ^ ((7 : ℝ) / 10)⌉₊ : ℝ) + 1)) *
            N.sqrt / N +
        ((ρ.period : ℝ) * H) * (4 * (N.sqrt : ℝ) / N) * Real.sqrt
          (5 * N.sqrt + 32 * (N.sqrt : ℝ)^2 / (N : ℝ) ^ ((3 : ℝ) / 10) +
            (64 * N.sqrt + 8 * ⌈(N : ℝ) ^ ((7 : ℝ) / 10)⌉₊) * (1 + Real.log ⌈(N : ℝ) ^ ((7 : ℝ) / 10)⌉₊)) +
        (⌈(D : ℝ) * H⌉₊ : ℝ)^2 * ((⌈(N : ℝ) ^ ((7 : ℝ) / 10)⌉₊ : ℝ) * ⌈(D : ℝ) * H⌉₊ / N) := by
        gcongr
    _ ≤ _ := twentieth_all (N : ℝ) (ρ.period : ℝ) (D : ℝ) H
        (⌈(N : ℝ) ^ ((7 : ℝ) / 10)⌉₊ : ℝ) (N.sqrt : ℝ) (⌈(D : ℝ) * H⌉₊ : ℝ)
        CD CH hn1 hP0 hPD hD1 hD hH1 hHhi hCD hCH (by exact_mod_cast hT)
        (by linarith) hThi (Nat.cast_nonneg _) hLD (Nat.cast_nonneg _) hMn

lemma finiteSquareKernel_root (N D : ℕ) (r : ℤ) (ρ : RootClassDatum D r) (H : ℝ) (M : ℕ) (α : ℝ) :
    finiteSquareKernel (termSign N D H) (termWeight N D r ρ H) M N α =
      ∑ m ∈ range M, squareWeight N α m *
        (classWeight ρ.period ρ.base (m+1) * sieveWeight N D H (m+1)) := by
  unfold finiteSquareKernel
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro m _
  rw [← rootTerm_sum N D ρ.period ρ.base H (m+1), mul_sum]
  apply sum_congr rfl
  intro T _
  unfold termSign termWeight
  ring

/-- **The actual-square kernel for an even modulus with a root class**
(`prop:record:kernel20` at the triple of `cor:kernel20`, from the root-class construction of
`lem:kernel-depth-classes`): for `N ≥ N₀`, an even `D ≤ C_D N^(1/20)`, a cutoff
`C_H⁻¹ N^(1/40) ≤ H ≤ C_H N^(1/40)`, integers `a, b` for which `b - a` admits a root class
modulo `D`, and `F, J` supported in `[1,N]` and in the classes `a, b mod D`, with every point
of `supp F` below every point of `supp J` and no difference a positive square,
`|D ∑_{ξ ∈ Ξ_{H,D}} g(ξ) F̂(-ξ) Ĵ(ξ)| ≤ C N^(-1/120) ‖F‖₂ ‖J‖₂ / N`, with `C, N₀` depending
only on `C_D, C_H`. -/
theorem kernel_pairing_rootDatum (CD CH : ℝ) (hCD : 1 ≤ CD) (hCH : 1 ≤ CH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ D : ℕ, 2 ∣ D → 0 < D → (D : ℝ) ≤ CD * (N : ℝ) ^ ((1 : ℝ) / 20) →
      ∀ H : ℝ, CH⁻¹ * (N : ℝ) ^ ((1 : ℝ) / 40) ≤ H → H ≤ CH * (N : ℝ) ^ ((1 : ℝ) / 40) →
      ∀ a b : ℤ, RootClassDatum D (b - a) →
      ∀ F J : ℤ →₀ ℂ,
        (∀ x ∈ F.support, 1 ≤ x ∧ x ≤ N ∧ x ≡ a [ZMOD (D : ℤ)]) →
        (∀ y ∈ J.support, 1 ≤ y ∧ y ≤ N ∧ y ≡ b [ZMOD (D : ℤ)]) →
        (∀ x ∈ F.support, ∀ y ∈ J.support, x < y) →
        (∀ x ∈ F.support, ∀ y ∈ J.support, ∀ m : ℕ, 1 ≤ m → y - x ≠ (m : ℤ) ^ 2) →
        ‖(D : ℂ) * ∑ ξ ∈ frequencySet H D,
            unitQuadraticAverage ξ * kernelTransform N F (-(ξ : ℝ)) *
              kernelTransform N J (ξ : ℝ)‖ ≤
          C * (N : ℝ) ^ (-(1 : ℝ) / 120) * (l2norm F * l2norm J) / N := by
  obtain ⟨C₁, hC₁, N₁, hrate⟩ := general_kernel_rate CD CH hCD hCH
  refine ⟨C₁ * CH ^ ((1 : ℝ) / 3), by positivity, max N₁ 1, ?_⟩
  intro N hN D h2 hDpos hD H hH1 hH2 a b ρ F J hF hJ hord hnosq
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans hN
  have hNpos : 0 < N := (le_max_right _ _).trans hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hCH0 : 0 < CH := by linarith
  have hk := hrate N hN₁ D h2 hDpos hD (b - a) ρ H hH1 hH2
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) hH1
  have hδ : 0 ≤ C₁ * H ^ (-(1 : ℝ) / 3) :=
    mul_nonneg hC₁.le (Real.rpow_nonneg hH0.le _)
  have hFs : ∀ x ∈ F.support, 1 ≤ x ∧ x ≤ N := fun x hx => ⟨(hF x hx).1, (hF x hx).2.1⟩
  have hJs : ∀ y ∈ J.support, 1 ≤ y ∧ y ≤ N := fun y hy => ⟨(hJ y hy).1, (hJ y hy).2.1⟩
  have hordc : ∀ x y : ZMod (N+1), liftCyclic N F x * liftCyclic N J y ≠ 0 →
      x.val < y.val ∧ y.val ≤ N := by
    intro x y hxy
    have hx : (x.val : ℤ) ∈ F.support :=
      Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul hxy)
    have hy : (y.val : ℤ) ∈ J.support :=
      Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hxy)
    have h1 := hord _ hx _ hy
    have h2' := (hJ _ hy).2.1
    constructor
    · exact_mod_cast h1
    · exact_mod_cast h2'
  have hsquarec : ∀ (x y : ZMod (N+1)) (m : ℕ), m ∈ range N.sqrt →
      (((m+1)^2 : ℕ) : ZMod (N+1)) = y - x → liftCyclic N F x * liftCyclic N J y = 0 := by
    intro x y m hm hxy
    by_contra hne
    obtain ⟨hlt, hyN⟩ := hordc x y hne
    have hx : (x.val : ℤ) ∈ F.support :=
      Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul hne)
    have hy : (y.val : ℤ) ∈ J.support :=
      Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hne)
    have hm' : m + 1 ≤ N.sqrt := mem_range.mp hm
    have hsqN : (m+1)^2 ≤ N := by
      have := Nat.sqrt_le' N
      calc (m+1)^2 ≤ N.sqrt^2 := Nat.pow_le_pow_left hm' 2
        _ ≤ N := this
    have hval := congrArg ZMod.val hxy
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), ZMod.val_sub hlt.le] at hval
    apply hnosq _ hx _ hy (m+1) (by omega)
    have : ((y.val - x.val : ℕ) : ℤ) = (y.val : ℤ) - (x.val : ℤ) := by
      rw [Nat.cast_sub hlt.le]
    rw [← this, ← hval]
    push_cast
    ring
  have hbil := ordered_square_kernel_bilinear_l2 (q := N+1) N.sqrt N hNpos (by omega)
    (fun m => classWeight ρ.period ρ.base m * sieveWeight N D H m)
    (fun x : CentreIndex H D => ((centre H D x : ℚ) : ℝ))
    (centreCoeff H D (b - a)) (C₁ * H ^ (-(1 : ℝ) / 3)) hδ
    (fun α => by
      have := hk α
      rw [finiteSquareKernel_root] at this
      exact this) (liftCyclic N F) (liftCyclic N J) hordc hsquarec
  rw [sum_norm_sq_liftCyclic N F hFs, sum_norm_sq_liftCyclic N J hJs] at hbil
  have hmodel : (∑ x : CentreIndex H D, centreCoeff H D (b - a) x *
      intervalFourier N (liftCyclic N F) (-((centre H D x : ℚ) : ℝ)) *
      intervalFourier N (liftCyclic N J) ((centre H D x : ℚ) : ℝ)) =
      (D : ℂ) * ∑ ξ ∈ frequencySet H D,
        unitQuadraticAverage ξ * kernelTransform N F (-(ξ : ℝ)) * kernelTransform N J (ξ : ℝ) := by
    simp_rw [intervalFourier_liftCyclic N F hFs, intervalFourier_liftCyclic N J hJs]
    unfold centreCoeff centre
    rw [Finset.sum_coe_sort (range D ×ˢ frequencySet H D)
      (fun y : ℕ × ℚ => expPhase ((y.1 : ℝ) * ((b - a : ℤ) : ℝ) / D) * unitQuadraticAverage y.2 *
        kernelTransform N F (-((((y.1 : ℚ) / D + y.2 : ℚ)) : ℝ)) *
        kernelTransform N J ((((y.1 : ℚ) / D + y.2 : ℚ)) : ℝ))]
    rw [Finset.sum_product]
    have hph := pairing_phase N D hDpos F J a b (fun x hx => (hF x hx).2.2)
      (fun y hy => (hJ y hy).2.2) (frequencySet H D) unitQuadraticAverage
    simp_rw [mul_assoc] at hph ⊢
    exact hph
  rw [hmodel] at hbil
  have hsave := cutoff_saving N H CH hn1 hCH0 hH1
  calc _ ≤ C₁ * H ^ (-(1 : ℝ) / 3) * Real.sqrt (∑ n ∈ F.support, ‖F n‖^2) *
        Real.sqrt (∑ n ∈ J.support, ‖J n‖^2) / N := hbil
    _ ≤ C₁ * (CH ^ ((1 : ℝ) / 3) * (N : ℝ) ^ (-(1 : ℝ) / 120)) *
        Real.sqrt (∑ n ∈ F.support, ‖F n‖^2) * Real.sqrt (∑ n ∈ J.support, ‖J n‖^2) / N := by
        gcongr
    _ = _ := by unfold l2norm; ring

end Kernel
end
end Sarkozy
