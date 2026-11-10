# Partial Lean companion

**This development does not prove the paper's theorem outright.** The
principal theorem, `Sarkozy.BudgetLinks.main_goal_rebased_bl`, proves a bound
with exponent **0.99999**, conditional on the explicit hypotheses described in
[TRUST_MAP.md](TRUST_MAP.md). The paper's stated exponent is 0.9999873.

Start with these files:

| File | Purpose |
| --- | --- |
| [Target.lean](Sarkozy/Target.lean) and [TargetDLK.lean](Sarkozy/TargetDLK.lean) | Definition of the conclusion and named analytic inputs |
| [TargetGoal/Main.lean](Sarkozy/TargetGoal/Main.lean) | The formal target saving `ε = 1/100000` |
| [BudgetLinks/Main.lean](Sarkozy/BudgetLinks/Main.lean) | Principal conditional theorem and its obligation structure |
| [E1Closure/Main.lean](Sarkozy/E1Closure/Main.lean) | Equivalent earlier formulation of the obligations |
| [Sarkozy.lean](Sarkozy.lean) | Aggregate library imports |
| [Audit.lean](Audit.lean) | Axiom audit for every declaration in the `Sarkozy` namespace |

## Build

Use the Lean version selected by [lean-toolchain](lean-toolchain),
`leanprover/lean4:v4.35.0-rc3`. Lake pins mathlib to
`c55e6e786f49471c72fbddbec5415808896aec1e`; the complete dependency revisions are
in [lake-manifest.json](lake-manifest.json).

With Lean's `elan` toolchain manager installed, run from this directory:

```sh
lake exe cache get
lake build Sarkozy
lake env lean -DautoImplicit=false -DwarningAsError=true Audit.lean
```

The first command obtains the mathlib build cache. A full build of the local
proofs still requires substantial time and memory because the project contains
large embedded finite certificates. No private data, generators or research
repository is needed to check the included Lean sources.

The audit rejects `sorryAx`, custom axioms and compiler-trust axioms. It allows
only `propext`, `Classical.choice` and `Quot.sound`. Passing it establishes the
axiom dependencies of the conditional theorems; it does not discharge their
explicit hypotheses.

## Verification and attribution

[verification.json](verification.json) describes the validation performed for
this publication copy and the earlier independent checker results. It
distinguishes those earlier runs from checks performed during packaging.

Some development comments were removed for publication. Definitions, theorem
statements and proof code are unchanged, checked by comparing the source with
all comments masked. The included `.lean` files contain the numerical
certificates required by their proofs. Auxiliary search and generation
programs are outside this release.

See [NOTICES.md](NOTICES.md) for the OpenAI proof material adapted here and
[LICENSE.openai](LICENSE.openai) for its upstream license. Original work in this
repository is also distributed under the root Apache-2.0 [LICENSE](../LICENSE).
