module

public import Sarkozy.MainFinal3.Comparison
public import Sarkozy.MainFinal3.Main

@[expose] public section

/-!
# The combined main statement, third round (C10)

* `Comparison` — `ComparisonParts3` (K2's `ComparisonParts2` without the square-clique field,
  proved by C10, and without the middle-block estimates, proved by E1) and `SAParts3` (E2's
  `SAPartsE3` with the clique bound `12/2^{534}` entered).
* `Main` — `FinalBlockData3` (with E2's `EnvelopePartsE2`), `MainFinalObligations3`,
  **`main_target_paper_final3`**: C10's, E1's and E2's reductions of K2's obligations combined.
-/
