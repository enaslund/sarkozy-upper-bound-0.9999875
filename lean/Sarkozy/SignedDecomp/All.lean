module

public import Sarkozy.SignedDecomp.Poly
public import Sarkozy.SignedDecomp.Paper
public import Sarkozy.SignedDecomp.Numbers
public import Sarkozy.SignedDecomp.Block
public import Sarkozy.SignedDecomp.Main
public import Sarkozy.SignedDecomp.Sanity
public import Sarkozy.SignedDecomp.CompTools
public import Sarkozy.SignedDecomp.CompForm
public import Sarkozy.SignedDecomp.Comp
public import Sarkozy.SignedDecomp.Main2
public import Sarkozy.SignedDecomp.Theta1

/-!
# SD2: PG's `SD` with the numerical gates proved (umbrella)

* `Poly`: the constants of `eq:signed-constants` as polynomials in nonnegative atoms; monotonicity
  (`lem:majorant`).
* `Paper`: the paper's `c_col`, `e_sg`, `c_+` at a prime (`ccolP`, `esgP`, `cpP`), their
  identification with the polynomials, and the decrease of the atoms along the primes.
* `Numbers`: the tables at the 33 piece starts; `gate_check`, `table_check`, `crude_check`,
  `gate_tight` (kernel).
* `Block`: `AnalyticAt`, `AnalyticAt80`; `gateAt_gen`, `gateAt_paper`; `Hblock_le`,
  `card_le_of_budget`; `decompGateAtC_of_analytic(80)`.
* `Main`: **`SignedDecompAnalytic.toSD : SignedDecompInputsC C`**; `FrontKA.toFrontK`.
* `Sanity`: `cert_Q3` (the printed values of `cert:signed-local` reproduced).
* `CompTools`: `separable_bound` (a separable cross character, `√p p²`), `schur_bound`,
  `paley_form`, `sum_update`.
* `CompForm`: `Vk_form` (B8's `U_{uv}` against `(∑ g)(∑ f)`), `Jker_form` (`J_C`).
* `Comp`: **`comp_form`**, **`comp_centred`**: `prop:signed-bounds`(c), Step 1, with the crude
  constant `80` (any repair constant with the defect bound, `p ≥ 2²⁴`).
* `Main2`: `comp80_paper`; **`SignedDecompAnalytic2.toSD`** (two analytic inputs);
  `FrontKB.toFrontK`.
* `Theta1`: **`main_goal_theta1k_sd2`** (`main_goal_theta1k` with the front `FrontKB`).
-/
