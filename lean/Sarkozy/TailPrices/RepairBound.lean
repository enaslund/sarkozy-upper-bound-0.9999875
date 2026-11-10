module

public import Sarkozy.TailPrices.Repairs

@[expose] public section

/-!
# A repair from one bound on its change (`lem:tr:repair`(f))

`paper/sections/17_completion_repair.tex`, `lem:tr:repair`(f): "`ν' − π` has zero marginals and,
as an operator from `L²(μ_Y)` to `L²(μ_X)`, norm at most `ρ' + ρ(π)`". In the form of
`TailRepair`, one bound `|𝒞_{K'}(φ, ψ) − 𝒞_O(φ, ψ)| ≤ C ‖φ‖ ‖ψ‖` (relative to the old half
marginal) gives both fields `sym_bound` and `skew_bound` with `C^s = C^a = C`, the paper's
charging (each repair bound included in full in both totals).

* **`TailRepair.ofChangeBound`**.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.TailPrices

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.Mixing Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.Labellings Sarkozy.UpperComparison Sarkozy.Recentering Sarkozy.Structured

variable {p : ℕ} [Fact p.Prime] {hne : TailNonempty p}

omit [Fact p.Prime] in
/-- Both parts of a bilinear quantity are bounded by a bound on it. -/
theorem half_bounds {a b C m n : ℝ} (ha : |a| ≤ C * m * n) (hb : |b| ≤ C * n * m) :
    |(a + b) / 2| ≤ C * m * n ∧ |(a - b) / 2| ≤ C * m * n := by
  have hb' : |b| ≤ C * m * n := by linarith [show C * n * m = C * m * n by ring]
  constructor
  · rw [abs_div, abs_two, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_add_le a b]
  · rw [abs_div, abs_two, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_sub a b]

/-- **A repair from one bound on its change** (`lem:tr:repair`(f)). *The fields are hypotheses*:
the repaired law with support, acceptance and invariance, and one bound `C` on the change of
centred pair forms relative to the old half marginal. -/
def TailRepair.ofChangeBound {t : PType × PType} {φ : t.1.Pat × t.2.Pat}
    (lam : FiniteLaw (t.1.field.Obj × t.2.field.Obj × Fin 2 → ZMod p))
    (supp : LayersSupported lam (tailHalf p hne t.1.field t.2.field))
    (accepts : ∀ z, (emit lam (upEmission (t.1.pat φ.1) (t.2.pat φ.2))).weight z ≠ 0 →
      ∀ j : Chamber, quadraticChar (ZMod p) (z (queryTarget j) - z (querySource j)) = 1)
    (inv : AffineInvariant p (emit lam (upEmission (t.1.pat φ.1) (t.2.pat φ.2))).weight)
    (C : ℝ) (hC : 0 ≤ C)
    (hB : ∀ φ' ψ', |tailChangeForm p hne t lam φ' ψ'| ≤
      C * mnrm (tailHalf p hne t.1.field t.2.field) (tailU p hne t) φ' *
        mnrm (tailHalf p hne t.1.field t.2.field) (tailU p hne t) ψ') :
    TailRepair p hne t φ where
  lam := lam
  supp := supp
  accepts := accepts
  inv := inv
  Cs := C
  Ca := C
  Cs_nonneg := hC
  Ca_nonneg := hC
  sym_bound φ' ψ' := (half_bounds (hB φ' ψ') (hB ψ' φ')).1
  skew_bound φ' ψ' := (half_bounds (hB φ' ψ') (hB ψ' φ')).2

end Sarkozy.TailPrices
