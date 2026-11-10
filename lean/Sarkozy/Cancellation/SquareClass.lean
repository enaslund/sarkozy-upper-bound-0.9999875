module

public import Sarkozy.Kernel.RootDatum

@[expose] public section

/-!
# The square class of `𝔞₂ − 𝔞₁` in Step 3 of `lem:record:density-can`

Step 3: "The difference `𝔞₂ − 𝔞₁` is `r` modulo `M₀`, a nonzero square at the primes of `U` and at
the primes below `P₅` with `e_p = 1`, and at the clique primes nonzero of even valuation below
`e_p` with square unit part, by (b)." — so `𝔞₂ − 𝔞₁` is a nonvanishing square class modulo
`D = M₀ D_pre q_U` (`def:nonvanishing-square-class`, `Sarkozy.Kernel.IsNonvanishingSquareClass`).

* `isNonvanishingSquareClass_congr`: the condition depends only on the class modulo `D`;
* `isNonvanishingSquareClass_mul`: a nonvanishing square class modulo `D₁` that satisfies the
  odd local condition at every prime of a coprime `D₂` is one modulo `D₁ D₂`;
* `localSquare_of_primePowers`: the local conditions at the primes of `∏_i p_i^{e_i}` from the
  conditions modulo each `p_i^{e_i}`;
* `squareClass_difference`: the combination used in Step 3.

New material for this paper.
-/

namespace Sarkozy.Cancellation

open Finset

/-- The odd local condition of `def:nonvanishing-square-class` at `p` with exponent `e`:
`d ≡ p^{2j} u (mod p^e)`, `p ∤ u`, `2j < e`, `u` a square modulo `p`. -/
def OddLocalSquare (p e : ℕ) (d : ℤ) : Prop :=
  ∃ j : ℕ, ∃ u : ℤ, ¬ (p : ℤ) ∣ u ∧ d ≡ (p : ℤ) ^ (2 * j) * u [ZMOD (p : ℤ) ^ e] ∧
    2 * j < e ∧ IsSquare (u : ZMod p)

/-- At a prime of exponent `1` the local condition is: a nonzero square modulo `p`. -/
lemma oddLocalSquare_one {p : ℕ} {d : ℤ} (hd : ¬ (p : ℤ) ∣ d) (hsq : IsSquare (d : ZMod p)) :
    OddLocalSquare p 1 d :=
  ⟨0, d, hd, by simp, by norm_num, hsq⟩

lemma oddLocalSquare_congr {p e : ℕ} {d d' : ℤ} (h : d ≡ d' [ZMOD (p : ℤ) ^ e])
    (hd : OddLocalSquare p e d) : OddLocalSquare p e d' := by
  obtain ⟨j, u, hu, hc, hj, hs⟩ := hd
  exact ⟨j, u, hu, h.symm.trans hc, hj, hs⟩

/-- `def:nonvanishing-square-class` depends only on the class modulo `D`. -/
theorem isNonvanishingSquareClass_congr {D : ℕ} {d d' : ℤ} (h : d ≡ d' [ZMOD (D : ℤ)])
    (hd : Kernel.IsNonvanishingSquareClass D d) : Kernel.IsNonvanishingSquareClass D d' := by
  obtain ⟨h2, hp⟩ := hd
  refine ⟨h2, fun p hpp hpD => ?_⟩
  obtain ⟨j, u, hu, hc, hrest⟩ := hp p hpp hpD
  have hdvd : ((p : ℤ) ^ (D.factorization p)) ∣ (D : ℤ) := by
    exact_mod_cast Nat.ordProj_dvd D p
  exact ⟨j, u, hu, (h.of_dvd hdvd).symm.trans hc, hrest⟩

/-- **Local to global**: a nonvanishing square class modulo `D₁` with the odd local condition at
every prime of a coprime `D₂` is a nonvanishing square class modulo `D₁ D₂`. -/
theorem isNonvanishingSquareClass_mul {D₁ D₂ : ℕ} (hD₁ : D₁ ≠ 0) (hD₂ : D₂ ≠ 0)
    (hcop : Nat.Coprime D₁ D₂) {d : ℤ} (h₁ : Kernel.IsNonvanishingSquareClass D₁ d)
    (h₂ : ∀ p : ℕ, p.Prime → p ∣ D₂ → OddLocalSquare p (D₂.factorization p) d) :
    Kernel.IsNonvanishingSquareClass (D₁ * D₂) d := by
  obtain ⟨h2, hp₁⟩ := h₁
  have hfac : (D₁ * D₂).factorization = D₁.factorization + D₂.factorization :=
    Nat.factorization_mul hD₁ hD₂
  have h2D₁ : 2 ∣ D₁ := by
    by_contra h
    rw [Nat.factorization_eq_zero_of_not_dvd h] at h2
    omega
  have h2D₂ : ¬ 2 ∣ D₂ := by
    intro h
    have := Nat.dvd_gcd h2D₁ h
    rw [hcop.gcd_eq_one] at this
    omega
  have hv1 : ∀ p, p ∣ D₁ → p.Prime → D₂.factorization p = 0 := by
    intro p hp hpp
    apply Nat.factorization_eq_zero_of_not_dvd
    intro h
    have := Nat.dvd_gcd hp h
    rw [hcop.gcd_eq_one] at this
    exact hpp.one_lt.ne' (Nat.dvd_one.mp this)
  have hv2 : ∀ p, p ∣ D₂ → p.Prime → D₁.factorization p = 0 := by
    intro p hp hpp
    apply Nat.factorization_eq_zero_of_not_dvd
    intro h
    have := Nat.dvd_gcd h hp
    rw [hcop.gcd_eq_one] at this
    exact hpp.one_lt.ne' (Nat.dvd_one.mp this)
  have h2' : (D₁ * D₂).factorization 2 = D₁.factorization 2 := by
    rw [hfac, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd h2D₂, add_zero]
  refine ⟨by rw [h2']; exact h2, fun p hpp hpD => ?_⟩
  rcases (Nat.Prime.dvd_mul hpp).mp hpD with hp | hp
  · have he : (D₁ * D₂).factorization p = D₁.factorization p := by
      rw [hfac, Finsupp.add_apply, hv1 p hp hpp, add_zero]
    rw [he, h2']
    exact hp₁ p hpp hp
  · have he : (D₁ * D₂).factorization p = D₂.factorization p := by
      rw [hfac, Finsupp.add_apply, hv2 p hp hpp, zero_add]
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact h2D₂ hp
    obtain ⟨j, u, hu, hc, hj, hs⟩ := h₂ p hpp hp
    refine ⟨j, u, hu, by rw [he]; exact hc, ?_⟩
    rw [ite_eq_right hp2, he]
    exact ⟨hj, hs⟩

/-- **The local conditions at the primes of `∏_i p_i^{e_i}`**, from the conditions modulo each
`p_i^{e_i}` (distinct primes `p_i`). -/
theorem localSquare_of_primePowers {ι : Type*} (S : Finset ι) (P e : ι → ℕ)
    (hP : ∀ i ∈ S, (P i).Prime) (hinj : Set.InjOn P S) {d : ℤ}
    (hloc : ∀ i ∈ S, OddLocalSquare (P i) (e i) d) :
    ∀ p : ℕ, p.Prime → p ∣ ∏ i ∈ S, P i ^ e i →
      OddLocalSquare p ((∏ i ∈ S, P i ^ e i).factorization p) d := by
  intro p hp hdvd
  obtain ⟨i, hi, hpi⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hdvd
  have hpP : p = P i := (Nat.prime_dvd_prime_iff_eq hp (hP i hi)).mp (hp.dvd_of_dvd_pow hpi)
  subst hpP
  have hfac : (∏ k ∈ S, P k ^ e k).factorization (P i) = e i := by
    rw [Nat.factorization_prod (fun k hk => pow_ne_zero _ (hP k hk).ne_zero)]
    rw [Finset.sum_apply']
    rw [Finset.sum_eq_single i]
    · rw [(hP i hi).factorization_pow, Finsupp.single_eq_same]
    · intro k hk hki
      rw [(hP k hk).factorization_pow, Finsupp.single_eq_of_ne]
      intro h
      exact hki (hinj hk hi h.symm)
    · intro h
      exact absurd hi h
  rw [hfac]
  exact hloc i hi

/-- **The square class of Step 3.** If `r` is a nonvanishing square class modulo `M₀`,
`𝔞₂ − 𝔞₁ ≡ r (mod M₀)`, and `𝔞₂ − 𝔞₁` satisfies the odd local condition modulo every frozen
modulus `p_i^{e_i}` (distinct primes coprime to `M₀`), then `𝔞₂ − 𝔞₁` is a nonvanishing square
class modulo `D = M₀ ∏_i p_i^{e_i}`. -/
theorem squareClass_difference {ι : Type*} (S : Finset ι) (P e : ι → ℕ)
    (hP : ∀ i ∈ S, (P i).Prime) (hinj : Set.InjOn P S) {M₀ : ℕ} (hM₀ : M₀ ≠ 0)
    (hcop : ∀ i ∈ S, Nat.Coprime M₀ (P i)) {r 𝔞₁ 𝔞₂ : ℤ}
    (hr : Kernel.IsNonvanishingSquareClass M₀ r) (hcong : 𝔞₂ - 𝔞₁ ≡ r [ZMOD (M₀ : ℤ)])
    (hloc : ∀ i ∈ S, OddLocalSquare (P i) (e i) (𝔞₂ - 𝔞₁)) :
    Kernel.IsNonvanishingSquareClass (M₀ * ∏ i ∈ S, P i ^ e i) (𝔞₂ - 𝔞₁) := by
  apply isNonvanishingSquareClass_mul hM₀
    (prod_ne_zero_iff.mpr (fun i hi => pow_ne_zero _ (hP i hi).ne_zero))
  · exact Nat.Coprime.prod_right (fun i hi => Nat.Coprime.pow_right _ (hcop i hi))
  · exact isNonvanishingSquareClass_congr hcong.symm hr
  · exact localSquare_of_primePowers S P e hP hinj hloc

end Sarkozy.Cancellation
