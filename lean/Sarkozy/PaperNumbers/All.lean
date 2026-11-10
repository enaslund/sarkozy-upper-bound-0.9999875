module

public import Sarkozy.PaperNumbers.BinData
public import Sarkozy.PaperNumbers.Cell
public import Sarkozy.PaperNumbers.Checks
public import Sarkozy.PaperNumbers.Budget
public import Sarkozy.PaperNumbers.Charge
public import Sarkozy.PaperNumbers.Main
public import Sarkozy.PaperNumbers.FirstStage
public import Sarkozy.PaperNumbers.ChargeData
public import Sarkozy.PaperNumbers.Costs
public import Sarkozy.PaperNumbers.HistData
public import Sarkozy.PaperNumbers.Histogram

/-!
# N1: the paper's partition data (umbrella)

* `BinData` — generated: the 5669 bin endpoints and the 36 threshold points
  (`def:record:exact-blocks`(b), (c)).
* `Cell` — the paper's within-site rule `paperCell` (`paperCellWith U` for recorded band cells).
* `Checks` — kernel checks of the data against the paper (threshold formula, piece endpoints, cell
  counts `𝗇 = 236, 256, 512, 640, 306`).
* `Budget` — `paperCell_budget : PaperBudget paperCell` (`lem:record:local-domain`(ii)).
* `Charge` — `blockCharge_le_pieceCharge`, `blockCharge_le_bmor` (`lem:record:block-charge` at the
  paper's partition).
* `Main` — `main_target_paper_joint_N1` and its `_charges`, `_bmor`, `_prices`, `_with` forms.
* `FirstStage` — the first-stage sums by piece (`sum_pvar_le`, `sum_dTag_le`, `sum_vTag_le`) and
  **`main_target_paper_joint_N1_numbers`** (`hB`, `hL₀` from 66 per-piece numbers).
* `ChargeData` — generated: the 66 numbers `c_d(i)`, decimal totals, exponential witnesses.
* `Costs` — `costB_le`, `costL_le` (the two cost inequalities, kernel-checked) and
  **`main_target_paper_joint_N1_final`**.
* `HistData` — generated: the exact-block histogram of the 35 parts (10737 buckets), the cell
  bounds, the exponential witness of a bucket.
* `Histogram` — `exactBound_le_hist`, `pieceBound_le_charge` (the 66 bounds from `HistogramClaim`
  and `CellClaim`) and **`main_target_paper_joint_N1_hist`**.
-/
