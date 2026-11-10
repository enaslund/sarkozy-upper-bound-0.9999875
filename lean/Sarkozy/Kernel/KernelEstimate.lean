module

public import Sarkozy.Kernel.GeneralKernel
public import Sarkozy.Kernel.RootClasses

@[expose] public section

/-!
# The actual-square kernel estimate (`prop:record:kernel20` at the triple of `cor:kernel20`)

This module states the paper's `prop:record:kernel20`, parts (i), (ii) and (iii), at the
admissible triple `(β, κ, η) = (1/20, 1/20, 17/100)` of `cor:kernel20`: moduli
`D ≤ C_D N^(1/20)`, cutoffs `C_H⁻¹ N^(1/40) ≤ H ≤ C_H N^(1/40)`, saving `N^(-β/6) = N^(-1/120)`,
with one pair of constants `C, N₀` depending only on `C_D, C_H` for all three parts.

* (i) `D = 8d`, `d` odd, `b - a` a strict square class;
* (ii) `D = 8d`, `d` odd, with the divided classes of (ii) (`IsDividedSquareClass`), as a
  special case of (iii) (`dividedSquareClass_nonvanishing`); the rescaling identity of (ii)
  (`lem:record:nonunit-rescale`) is not formalized here;
* (iii) `v₂(D) ≥ 3`, `b - a` a nonvanishing square class.

The proof combines `kernel_pairing_rootDatum` (`GeneralKernel.lean`) with the root-class
constructions `rootClassDatum_of_strict` and `rootClassDatum_of_nonvanishing`
(`RootClasses.lean`). The arc exponent `η` is internal to the proof and does not appear in
the statement; the proof uses its own circle-method parameters (`RatesTwentieth.lean`).
-/

namespace Sarkozy

namespace Kernel

lemma factorization_eight_mul_two (d : ℕ) (hd : Odd d) : (8 * d).factorization 2 = 3 := by
  have hd0 : d ≠ 0 := by rintro rfl; exact Nat.not_odd_zero hd
  rw [Nat.factorization_mul (by norm_num) hd0, Finsupp.add_apply]
  have h8 : (8 : ℕ).factorization 2 = 3 := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, Nat.Prime.factorization_pow Nat.prime_two]
    simp
  have hd2 : d.factorization 2 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    exact fun h => (Nat.not_even_iff_odd.mpr hd) (even_iff_two_dvd.mpr h)
  rw [h8, hd2]

/-- The hypotheses of `prop:record:kernel20`(ii) on `b - a` modulo `D = 8d`. -/
def IsDividedSquareClass (d : ℕ) (P₀ : Finset ℕ) (m : ℕ → ℕ) (r : ℤ) : Prop :=
  (∀ p ∈ P₀, p.Prime ∧ p ≠ 2 ∧ 1 ≤ m p ∧ (8 * d).factorization p = 2 * m p) ∧
  r ≡ 1 [ZMOD 8] ∧
  (∀ p : ℕ, p.Prime → p ∣ d → p ∉ P₀ → (r : ZMod p) ≠ 0 ∧ IsSquare (r : ZMod p)) ∧
  (∀ p ∈ P₀, ((r : ZMod p) ≠ 0 ∧ IsSquare (r : ZMod p)) ∨
    ∃ j : ℕ, 1 ≤ j ∧ j < m p ∧ ∃ u : ℤ, ¬ (p : ℤ) ∣ u ∧
      r ≡ (p : ℤ) ^ (2 * j) * u [ZMOD (p : ℤ) ^ (2 * m p)] ∧ IsSquare (u : ZMod p))

lemma strict_to_nonvanishing_local (D p : ℕ) (hp : p.Prime) (hpD : p ∣ D) (hD : 0 < D) (r : ℤ)
    (hr0 : (r : ZMod p) ≠ 0) (hrsq : IsSquare (r : ZMod p)) (hp2 : p ≠ 2) :
    ∃ j : ℕ, ∃ u : ℤ, ¬ (p : ℤ) ∣ u ∧
      r ≡ (p : ℤ) ^ (2 * j) * u [ZMOD (p : ℤ) ^ (D.factorization p)] ∧
      (if p = 2 then 2 * j + 3 ≤ D.factorization 2 ∧ u ≡ 1 [ZMOD 8]
        else 2 * j < D.factorization p ∧ IsSquare (u : ZMod p)) := by
  refine ⟨0, r, ?_, ?_, ?_⟩
  · intro h
    exact hr0 ((ZMod.intCast_zmod_eq_zero_iff_dvd r p).mpr h)
  · simp
  · rw [ite_eq_right hp2]
    refine ⟨?_, hrsq⟩
    have := (hp.dvd_iff_one_le_factorization hD.ne').mp hpD
    omega

/-- Part (ii) of `prop:record:kernel20` is a special case of part (iii): the classes of (ii)
are nonvanishing square classes. -/
lemma dividedSquareClass_nonvanishing (d : ℕ) (hd : Odd d) (P₀ : Finset ℕ) (m : ℕ → ℕ) (r : ℤ)
    (hr : IsDividedSquareClass d P₀ m r) : IsNonvanishingSquareClass (8 * d) r := by
  obtain ⟨hP₀, h8, hout, hin⟩ := hr
  have hd0 : d ≠ 0 := by rintro rfl; exact Nat.not_odd_zero hd
  have hD : 0 < 8 * d := by positivity
  have hf2 := factorization_eight_mul_two d hd
  refine ⟨by rw [hf2], ?_⟩
  intro p hp hpD
  by_cases hp2 : p = 2
  · subst hp2
    refine ⟨0, r, ?_, ?_, ?_⟩
    · intro h
      have h1 : (2 : ℤ) ∣ r - 1 := (show (2 : ℤ) ∣ 8 by norm_num).trans (Int.ModEq.dvd h8.symm)
      have h3 := dvd_sub h h1
      simp at h3
    · simp
    · rw [ite_eq_left rfl, hf2]
      exact ⟨by norm_num, h8⟩
  · have hpd : p ∣ d := by
      have hc : Nat.Coprime p 8 := by
        have : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
        simpa using this.pow_right 3
      exact hc.dvd_of_dvd_mul_left hpD
    by_cases hpP : p ∈ P₀
    · rcases hin p hpP with ⟨hr0, hrsq⟩ | ⟨j, hj1, hjm, u, hu, hru, husq⟩
      · exact strict_to_nonvanishing_local (8 * d) p hp hpD hD r hr0 hrsq hp2
      · obtain ⟨_, _, _, hfac⟩ := hP₀ p hpP
        refine ⟨j, u, hu, ?_, ?_⟩
        · rw [hfac]; exact hru
        · rw [ite_eq_right hp2, hfac]
          exact ⟨by omega, husq⟩
    · obtain ⟨hr0, hrsq⟩ := hout p hp hpd hpP
      exact strict_to_nonvanishing_local (8 * d) p hp hpD hD r hr0 hrsq hp2

/-- **The actual-square kernel at `β = 1/20`** (`prop:record:kernel20`, parts (i), (ii), (iii),
at the triple `(1/20, 1/20, 17/100)` of `cor:kernel20`).

Fix `C_D, C_H ≥ 1`. There are `C > 0` and `N₀`, depending only on `C_D, C_H`, such that for
all `N ≥ N₀` and `C_H⁻¹ N^(1/40) ≤ H ≤ C_H N^(1/40)` the following hold, where for a modulus
`D` and integers `a, b` the *pairing bound* means: for all finitely supported `F, J : ℤ → ℂ`
supported in `[1,N]` and in the residue classes `a`, resp. `b`, modulo `D`, with `x < y` and
`y - x` not the square of a positive integer for all `x ∈ supp F`, `y ∈ supp J`,
`|D ∑_{ξ ∈ Ξ_{H,D}} g(ξ) F̂(-ξ) Ĵ(ξ)| ≤ C N^(-1/120) ‖F‖₂ ‖J‖₂ / N` (`eq:record:K20`).

(i) For `D = 8d ≤ C_D N^(1/20)`, `d` odd, and `b - a` a strict square class modulo `D`.
(ii) For `D = 8d ≤ C_D N^(1/20)`, `d` odd, and `b - a` satisfying the hypotheses of (ii)
  (`IsDividedSquareClass d P₀ m (b - a)`).
(iii) For `D ≤ C_D N^(1/20)` and `b - a` a nonvanishing square class modulo `D`
  (`IsNonvanishingSquareClass D (b - a)`, which includes `v₂(D) ≥ 3`). -/
theorem prop_kernel20_twentieth (CD CH : ℝ) (hCD : 1 ≤ CD) (hCH : 1 ≤ CH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ H : ℝ, CH⁻¹ * (N : ℝ) ^ ((1 : ℝ) / 40) ≤ H → H ≤ CH * (N : ℝ) ^ ((1 : ℝ) / 40) →
      -- (i)
      (∀ d : ℕ, Odd d → ((8 * d : ℕ) : ℝ) ≤ CD * (N : ℝ) ^ ((1 : ℝ) / 20) →
        ∀ a b : ℤ, IsStrictSquareClass d (b - a) →
        ∀ F J : ℤ →₀ ℂ,
          (∀ x ∈ F.support, 1 ≤ x ∧ x ≤ N ∧ x ≡ a [ZMOD ((8 * d : ℕ) : ℤ)]) →
          (∀ y ∈ J.support, 1 ≤ y ∧ y ≤ N ∧ y ≡ b [ZMOD ((8 * d : ℕ) : ℤ)]) →
          (∀ x ∈ F.support, ∀ y ∈ J.support, x < y) →
          (∀ x ∈ F.support, ∀ y ∈ J.support, ∀ m : ℕ, 1 ≤ m → y - x ≠ (m : ℤ) ^ 2) →
          ‖((8 * d : ℕ) : ℂ) * ∑ ξ ∈ frequencySet H (8 * d),
              unitQuadraticAverage ξ * kernelTransform N F (-(ξ : ℝ)) *
                kernelTransform N J (ξ : ℝ)‖ ≤
            C * (N : ℝ) ^ (-(1 : ℝ) / 120) * (l2norm F * l2norm J) / N) ∧
      -- (ii)
      (∀ d : ℕ, Odd d → ((8 * d : ℕ) : ℝ) ≤ CD * (N : ℝ) ^ ((1 : ℝ) / 20) →
        ∀ (P₀ : Finset ℕ) (m : ℕ → ℕ) (a b : ℤ), IsDividedSquareClass d P₀ m (b - a) →
        ∀ F J : ℤ →₀ ℂ,
          (∀ x ∈ F.support, 1 ≤ x ∧ x ≤ N ∧ x ≡ a [ZMOD ((8 * d : ℕ) : ℤ)]) →
          (∀ y ∈ J.support, 1 ≤ y ∧ y ≤ N ∧ y ≡ b [ZMOD ((8 * d : ℕ) : ℤ)]) →
          (∀ x ∈ F.support, ∀ y ∈ J.support, x < y) →
          (∀ x ∈ F.support, ∀ y ∈ J.support, ∀ m : ℕ, 1 ≤ m → y - x ≠ (m : ℤ) ^ 2) →
          ‖((8 * d : ℕ) : ℂ) * ∑ ξ ∈ frequencySet H (8 * d),
              unitQuadraticAverage ξ * kernelTransform N F (-(ξ : ℝ)) *
                kernelTransform N J (ξ : ℝ)‖ ≤
            C * (N : ℝ) ^ (-(1 : ℝ) / 120) * (l2norm F * l2norm J) / N) ∧
      -- (iii)
      (∀ D : ℕ, (D : ℝ) ≤ CD * (N : ℝ) ^ ((1 : ℝ) / 20) →
        ∀ a b : ℤ, IsNonvanishingSquareClass D (b - a) →
        ∀ F J : ℤ →₀ ℂ,
          (∀ x ∈ F.support, 1 ≤ x ∧ x ≤ N ∧ x ≡ a [ZMOD (D : ℤ)]) →
          (∀ y ∈ J.support, 1 ≤ y ∧ y ≤ N ∧ y ≡ b [ZMOD (D : ℤ)]) →
          (∀ x ∈ F.support, ∀ y ∈ J.support, x < y) →
          (∀ x ∈ F.support, ∀ y ∈ J.support, ∀ m : ℕ, 1 ≤ m → y - x ≠ (m : ℤ) ^ 2) →
          ‖(D : ℂ) * ∑ ξ ∈ frequencySet H D,
              unitQuadraticAverage ξ * kernelTransform N F (-(ξ : ℝ)) *
                kernelTransform N J (ξ : ℝ)‖ ≤
            C * (N : ℝ) ^ (-(1 : ℝ) / 120) * (l2norm F * l2norm J) / N) := by
  obtain ⟨C, hC, N₀, hmain⟩ := kernel_pairing_rootDatum CD CH hCD hCH
  refine ⟨C, hC, N₀, ?_⟩
  intro N hN H hH1 hH2
  -- part (iii), from which (i) and (ii) follow
  have hiii : ∀ D : ℕ, (D : ℝ) ≤ CD * (N : ℝ) ^ ((1 : ℝ) / 20) →
      ∀ a b : ℤ, IsNonvanishingSquareClass D (b - a) →
      ∀ F J : ℤ →₀ ℂ,
        (∀ x ∈ F.support, 1 ≤ x ∧ x ≤ N ∧ x ≡ a [ZMOD (D : ℤ)]) →
        (∀ y ∈ J.support, 1 ≤ y ∧ y ≤ N ∧ y ≡ b [ZMOD (D : ℤ)]) →
        (∀ x ∈ F.support, ∀ y ∈ J.support, x < y) →
        (∀ x ∈ F.support, ∀ y ∈ J.support, ∀ m : ℕ, 1 ≤ m → y - x ≠ (m : ℤ) ^ 2) →
        ‖(D : ℂ) * ∑ ξ ∈ frequencySet H D,
            unitQuadraticAverage ξ * kernelTransform N F (-(ξ : ℝ)) *
              kernelTransform N J (ξ : ℝ)‖ ≤
          C * (N : ℝ) ^ (-(1 : ℝ) / 120) * (l2norm F * l2norm J) / N := by
    intro D hD a b hab F J hF hJ hord hsq
    have hD0 : 0 < D := by
      rcases Nat.eq_zero_or_pos D with h | h
      · exfalso
        have := hab.1
        rw [h] at this
        simp at this
      · exact h
    have h2 : 2 ∣ D := by
      have h3 := hab.1
      exact (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hD0.ne').mpr (by omega)
    obtain ⟨ρ⟩ := rootClassDatum_of_nonvanishing D hD0 (b - a) hab
    exact hmain N hN D h2 hD0 hD H hH1 hH2 a b ρ F J hF hJ hord hsq
  refine ⟨?_, ?_, hiii⟩
  · intro d hd hD a b hab F J hF hJ hord hsq
    exact hiii (8 * d) hD a b (isNonvanishing_of_strict d hd (b - a) hab) F J hF hJ hord hsq
  · intro d hd hD P₀ m a b hab F J hF hJ hord hsq
    exact hiii (8 * d) hD a b (dividedSquareClass_nonvanishing d hd P₀ m (b - a) hab)
      F J hF hJ hord hsq

end Kernel

end Sarkozy
