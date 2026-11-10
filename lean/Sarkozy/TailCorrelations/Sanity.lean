module

public import Sarkozy.TailCorrelations.Ledger

@[expose] public section

/-!
# Sanity checks for `TailCorrelations` (non-vacuity)

The only hypothesis of the package is `Target.Weil` (H1, `thm:weil`(a)), a theorem of the
literature. These checks make sure the conclusions are neither vacuous nor trivial:

* `exists_tail_prime`: there are primes `q ≥ P₄`, so the quantifier `∀ q ≥ P₄` of `tailCorr2`
  and `tailRp` ranges over a nonempty set;
* `tailCorr_small`: the two correlation numbers are at most `2⁻¹⁷⁵`, far below the trivial
  Cauchy–Schwarz value `1`, so `CentredBound` and `old_corr` are strong statements;
* `tailRp_C_small`: every repair constant of `tailRp` is at most `2⁻¹⁷³`, against `3` for FR's
  unconditional replacement `crudeRepair`.
-/

namespace Sarkozy.TailCorrelations

open Sarkozy.PartV Sarkozy.TailPrices Sarkozy.F7Repair Sarkozy.UpperComparison
  Sarkozy.RecordExpansion Sarkozy.TheoremC

/-- **There are tail primes** (Euclid). -/
theorem exists_tail_prime : ∃ q : ℕ, q.Prime ∧ P4 ≤ q := by
  obtain ⟨q, hq, hp⟩ := Nat.exists_infinite_primes P4
  exact ⟨q, hp, hq⟩

theorem rhoHat_r_le {q : ℕ} (h4 : P4 ≤ q) : rhoHat * tailR q ≤ 1 / 2 ^ 175 := by
  unfold rhoHat
  calc (2 : ℝ) ^ 81 * tailR q ≤ 2 ^ 81 * (1 / 2 ^ 256) :=
        mul_le_mul_of_nonneg_left (tailR_le h4) (by positivity)
    _ = 1 / 2 ^ 175 := by norm_num

/-- **The correlation bounds are far from trivial**: `ρ_new, ρ_old ≤ 2⁻¹⁷⁵`. -/
theorem tailCorr_small (hW : Target.Weil) {q : ℕ} [Fact q.Prime] (h4 : P4 ≤ q)
    (hne : TailNonempty q) (t : PType × PType) (φ : t.1.Pat × t.2.Pat) :
    (tailCorr hW h4 hne t φ).ρ ≤ 1 / 2 ^ 175 ∧ (tailCorr hW h4 hne t φ).ρold ≤ 1 / 2 ^ 175 :=
  ⟨rhoHat_r_le h4, rhoHat_r_le h4⟩

/-- **The repair constants of `tailRp` are tiny**: `C^ε_ρ ≤ 2⁸³ q^{-1/2} ≤ 2⁻¹⁷³`. -/
theorem tailRp_C_small (hW : Target.Weil) (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q)
    (t : PType × PType) (φ : t.1.Pat × t.2.Pat) (h : upperFate (true, ⟨t, φ⟩) = .changed)
    (e : ChangeType) : (tailRp hW q h4 t φ h).C e ≤ 1 / 2 ^ 173 := by
  refine (tailRp_C_le' hW q h4 t φ h e).trans ?_
  calc (2 : ℝ) ^ 83 * tailR q ≤ 2 ^ 83 * (1 / 2 ^ 256) :=
        mul_le_mul_of_nonneg_left (tailR_le h4) (by positivity)
    _ = 1 / 2 ^ 173 := by norm_num

end Sarkozy.TailCorrelations
