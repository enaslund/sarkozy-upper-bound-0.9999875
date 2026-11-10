# What the Lean companion proves and assumes

The main entry point is
[`Sarkozy.BudgetLinks.main_goal_rebased_bl`](Sarkozy/BudgetLinks/Main.lean).
It concludes `Target.SarkozyBound TargetGoal.epsGoal`, with
`TargetGoal.epsGoal = 1/100000`. Thus its conclusion is
`s(N) ≤ C N^0.99999` for an absolute positive constant `C`.

The result is conditional on five named analytic inputs, an upper-record
coefficient table, and a value of `CompanionObligationsBL`. The latter has 31
fields, including data and side conditions as well as unproved mathematical
obligations. Counting fields is not a measure of proof completion. The Lean
definitions are authoritative; this document is a reading aid.

## Named analytic inputs

| Hypothesis | Meaning |
| --- | --- |
| `Target.Weil` | The character-sum bound used throughout the construction |
| `Target.BMOR` | The explicit Chebyshev estimate of Bennett, Martin, O'Bryant and Rechnitzer |
| `Target.ThetaSmallRR` | The small-range estimate from Ramaré–Rumely |
| `Target.MovingRoot` | The moving-root moment statement proved in the paper |
| `Target.FourCycle` | The paper's four-cycle bound, formulated in `TargetDLK.lean` |

The last two are results of the paper whose proofs are assumed in this Lean
route. Their use should not be mistaken for a formalization of the paper's
cohomological or representation-theoretic arguments. `Target.TwoVariable` and
`Target.AhlgrenOno` occur elsewhere in the library but are not hypotheses of
this principal theorem.

## Remaining obligations

The following table summarizes the mathematical content of the structures.
Follow `CompanionObligationsBL` and its `F` field for the exact types and
quantifiers.

| Fields | Content still supplied as hypotheses |
| --- | --- |
| `UpT`, `hC`, `hCv` | Upper-record coefficients, closing-series data and the required closing inequality |
| `F.hs`, `F.ha` | Upper-block constants fit the table |
| `F.PCu` | Seven per-prime certificate families: `rootB`, `rootA`, `nonroot`, `h20lo`, `h20hi`, `h10`, `h21` |
| `F.BA` | Three block obligations concerning reference rows and layer caps |
| `F.rep` | Upper replacing laws |
| `ops` | Class savings from the envelope argument and variance steps |
| `hcomp`, `hX` | Comparison coefficients and letter totals |

In particular, `ops` contains substantial unfinished mathematics from Part V.
The presence of a Lean structure bundling these fields is not a construction
of a value satisfying them. Numerical experiments supporting an obligation
are not themselves Lean proofs of that obligation.

`CompanionObligationsBL` and `E1Closure.CompanionObligationsEC` are related by
proved maps `toEC`, `ofEC` and `nonempty_iff`. The budget formulation absorbs
the residual and energy links into `ops`; it does not remove their mathematical
content. Other theorem variants in the library can request stronger inputs
and should be read with their own signatures.

## Checked material

The library includes proofs for the square-difference predicate and its
preservation, Fourier and reflection arguments, the kernel and comparison
frameworks, local graph estimates, extraction, density induction, and many
finite numerical certificates. The conclusion is connected to the explicit
remaining obligations by Lean proofs.

The formal route uses some cruder estimates and different parameters than the
paper. Its target exponent 0.99999 leaves additional room for those estimates.
It should be evaluated as a conditional companion, rather than as a
line-for-line formalization of the paper's stronger numerical theorem.

## Trust and verification

[Audit.lean](Audit.lean) checks all declarations in the `Sarkozy` namespace
against the allowed axioms `propext`, `Classical.choice` and `Quot.sound` and
prints the dependencies of the headline theorems. Explicit theorem parameters
are hypotheses, not additional Lean axioms; an axiom audit does not prove them.

[verification.json](verification.json) records the source comparison and
validation for this release. Earlier independent checks covered all 840
headline roots, including the principal theorem, on 10 November 2026.
They are reported as earlier checks, not as new independent replays of this
publication package. The NanoDa run reported no typechecker errors and one
pretty-printer error; the con-ron verified run accepted its exported
declarations. Earlier runs with a smaller root list are not used as evidence
for the final theorem.
