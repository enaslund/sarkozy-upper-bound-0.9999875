module

public import Sarkozy.LedgerAnchor.PaperVariant

@[expose] public section

/-!
# Non-vacuity of the `a₀` ledger bounds

The ledgers whose entries are the rounded bounds themselves satisfy `AnchorBounds` and
`AnchorBoundsPaper`. So the bounds are consistent, and `theta_lt_cap` applies to them: these
are the closing numbers `Θ ≤ 0.958358781949…` and `Θ ≤ 0.941975757620…` of the two variants.
-/

namespace Sarkozy.LedgerAnchor

open Sarkozy.Comparison (PrimitiveLedger)

/-- The formalization-friendly ledger at `a₀`, entries at their rounded bounds. -/
noncomputable def anchorLedger : PrimitiveLedger :=
  ⟨2.336116464034, 0.00047996208, 0.011140349411, 0.968315055203, 0.602949465952, 0.469121104481,
      1.529229285152, 1.248422835484, 0.007609899014, 0.012646953992, 0.006568610064,
      0.000741210604, 0.000900869447, 0.000000087723⟩

/-- The paper-certificate ledger at `a₀`, entries at their rounded bounds. -/
noncomputable def anchorLedgerPaper : PrimitiveLedger :=
  ⟨2.333773146847, 0.000476049892, 0.008805926773, 0.965864162302, 0.598583337443, 0.467569676434,
      1.529599479214, 1.247518781991, 0.00758997189, 0.012609201077, 0.006547928062,
      0.000738471869, 0.000681478634, 0.000000065513⟩

theorem anchorLedger_bounds : AnchorBounds anchorLedger := by
  constructor <;> norm_num [anchorLedger]

theorem anchorLedgerPaper_bounds : AnchorBoundsPaper anchorLedgerPaper := by
  constructor <;> norm_num [anchorLedgerPaper]

/-- The closing number of the rounded formalization-friendly ledger is below `0.95836`. -/
theorem anchorLedger_theta_lt : anchorLedger.theta < closingCapAnchor :=
  anchorLedger_bounds.theta_lt_cap

/-- The closing number of the rounded paper-certificate ledger is below `0.94198`. -/
theorem anchorLedgerPaper_theta_lt : anchorLedgerPaper.theta < closingCapPaper :=
  anchorLedgerPaper_bounds.theta_lt_cap

end Sarkozy.LedgerAnchor
