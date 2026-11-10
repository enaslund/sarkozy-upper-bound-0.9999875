module

public import Sarkozy.ClassSlack.NoMean
public import Sarkozy.ClassSlack.Main
public import Sarkozy.ClassSlack.Sanity
public import Sarkozy.ClassSlack.MeanZero
public import Sarkozy.ClassSlack.MeanZeroFinal

@[expose] public section

/-!
# CG: the class group without the middle mean credit (umbrella)

* `NoMean`: `zeroDiag`, `diagW_zeroDiag_le`, `noMean_room`, `seriesBound_noMean`,
  `mdInputsNoMean`, `classPartsNoMean`;
* `Main`: `CompanionObligationsCG`, **`main_goal_rebased_cg`**;
* `Sanity`: `CompanionObligationsCG.ofND`, `main_goal_of_nd`, `numerics_satisfiable_cg`;
* `MeanZero`: `SelMeanAt`, `selMeanAt_zero` (the one-block credit at `m₁ = 0` is a theorem);
* `MeanZeroFinal`: at the ledger's `m₁ = 0`, `hm₁_proved`, `CompanionObligationsCG0`,
  **`main_goal_rebased_cg0`** (no mean input).
-/
