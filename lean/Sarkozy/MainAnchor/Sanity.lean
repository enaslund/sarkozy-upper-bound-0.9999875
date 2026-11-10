module

public import Sarkozy.MainAnchor.Main

@[expose] public section




namespace Sarkozy.MainAnchor

open Sarkozy.Comparison (PrimitiveLedger)
open Sarkozy.LedgerAnchor (AnchorBounds anchorLedger)

/-- The ledger fields are consistent. -/
theorem ledger_fields_consistent : ∃ l : PrimitiveLedger, AnchorBounds l :=
  ⟨anchorLedger, LedgerAnchor.anchorLedger_bounds⟩

/-- The shape field is satisfiable: six queries. -/
theorem shape_fields_consistent : Fintype.card (Fin 6) = 6 := by simp

/-- The comparison fields are consistent with the ledger fields: the ledger's own totals
satisfy them (with `𝓔 = E` and the mean credit at its bound). -/
theorem comparison_fields_consistent :
    ∃ B L₀ T R S A 𝓔 m : ℝ, B ≤ anchorLedger.B ∧ L₀ ≤ anchorLedger.L₀ ∧ T ≤ anchorLedger.T ∧
      R ≤ anchorLedger.R_I ∧ S + A ≤ anchorLedger.S + anchorLedger.A ∧ 𝓔 ≤ anchorLedger.E ∧
      anchorLedger.m₁ + 64 * ((anchorLedger.deltaAlpha + anchorLedger.deltaMatching +
        anchorLedger.deltaOdd + anchorLedger.deltaEven) + anchorLedger.deltaUpper -
        anchorLedger.upperError) ≤ m :=
  ⟨_, _, _, _, _, _, _, _, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩

end Sarkozy.MainAnchor
