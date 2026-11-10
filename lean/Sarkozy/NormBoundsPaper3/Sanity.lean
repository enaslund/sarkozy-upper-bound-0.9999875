module

public import Sarkozy.NormBoundsPaper3.Final

@[expose] public section

/-!
# Sanity checks of NB3

* `sanity_P3_mass`, `sanity_C0_mass`: `K₁` and `K^E_0`, read at the two layers, are probability
  laws on pairs of halves (so the identifications `P3_eq`, `C0_eq` and the couplings are not
  degenerate);
* `sanity_m3_mass`: `ν_E` is a probability law;
* **`aEp_le_paper`**: the prime skew constant `aEp p = √p (p + 2)/(p² − 3p + 4)` proved here is
  at most the paper's `a^E_p = r(1 + 2q)/((1 − q)(1 − 2q)) = √p (p + 2)/((p − 1)(p − 2))`;
* `sanity_eOrth`: the one-prime input `EOrthPrime` is satisfiable (crude constant,
  `eOrthPrime_crude`), at `p = 7`;
* `sanity_kappa`: at the first piece, `fX X ≤ a_E` and `2 ≤ s_E² X` (the two numerical facts used
  at `paperKappa`).
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.NormBoundsPaper3

open Sarkozy.PartV Sarkozy.Labellings Sarkozy.MiddleComparison
open Sarkozy.HsumProof (paperKappa)

variable {p : ℕ} [Fact p.Prime]

theorem sanity_m3_mass (hp : 3 ≤ p) : ∑ x, m3 p x = 1 := sum_m3 hp

theorem sanity_P3_mass (hE : (eSet (F := ZMod p)).Nonempty) (hp : 7 ≤ p) (h3 : p % 4 = 3) :
    ∑ x, ∑ y, P3 hE x y = 1 := by
  simp only [P3_row hE hp h3]
  exact sum_m3 (by omega)

theorem sanity_C0_mass (hne : (injLabellings (ZMod p) (matchGraph (Fin 2))).Nonempty)
    (hp : 3 ≤ p) : ∑ x, ∑ y, C0 hne x y = 1 := by
  simp only [C0_row hne hp]
  exact sum_m3 hp

omit [Fact p.Prime] in
/-- **The prime skew constant is below the paper's `a^E_p`.** -/
theorem aEp_le_paper (hp : 3 ≤ p) :
    aEp p ≤ Real.sqrt p * ((p : ℝ) + 2) / (((p : ℝ) - 1) * ((p : ℝ) - 2)) := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  unfold aEp
  have h12 : 0 < ((p : ℝ) - 1) * ((p : ℝ) - 2) := by nlinarith
  exact div_le_div_of_nonneg_left (by positivity) h12 (by nlinarith)

/-- The one-prime input is satisfiable (crude constant) at `p = 7`. -/
theorem sanity_eOrth :
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    EOrthPrime 7 (rhoE 7 + 18 * ((7 : ℕ) : ℝ) / ((((7 : ℕ) : ℝ) - 1) * (((7 : ℕ) : ℝ) - 2))) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact eOrthPrime_crude le_rfl (by norm_num)

/-- The numerical facts at the first piece. -/
theorem sanity_kappa :
    fX (pieceStart 0) ≤ (paperKappa 0).aE ∧
      2 ≤ (paperKappa 0).sE ^ 2 * (pieceStart 0 : ℝ) :=
  ⟨fX_le_paperKappa 0, (sE_facts 0).2⟩

end Sarkozy.NormBoundsPaper3
