module

public import Sarkozy.SignedComponents.Paper

@[expose] public section

/-!
# Non-vacuity of the new inputs of `Sarkozy.SignedComponents`

Every structure introduced in this directory has an instance built from proved facts only:

* `RepairInput`: `repairInput` (at every prime `p ≡ 3 (4)`, `p ≥ 19` with `Inj_p(G_{F,2}) ≠ ∅`);
* `RepairInput.DefectBound`: satisfiable by `Mmax` (`defectBound_Mmax`);
* `FoldPrimeComponents`: `primeComponentsMax` (`sanity_prime`);
* `FoldComponents`: `blockComponentsMax` (`sanity_block`);
* `DefectConstants`: `DefectConstants.max`;
* B7's `ReplacementData` on the paper's frame of any middle block, any root: `ofFold` with
  `blockComponentsMax` (`sanity_replacementData`).

`FormBound` is a predicate; `formBound_zero` checks it on the zero measure and
`optNorm_zero` that the optimal norm of the zero measure is `0`. The paper's norm bounds in
`ofFold_price_sum_le` are hypotheses about the concrete changes; they are the statements of
`prop:signed-bounds`, `lem:record:exact-marginal-e`(ii), `lem:merge-repair` and
`lem:record:accepting-c2`, and are not checked here.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.SignedComponents

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.Labellings
open Sarkozy.MiddleComparison

/-- `FoldPrimeComponents` has an instance at every admissible prime. -/
noncomputable def sanity_prime {p : ℕ} [Fact p.Prime] (h3 : p % 4 = 3) (h19 : 19 ≤ p)
    (hF : (injLabellings (ZMod p) (foldGraph (Fin 2))).Nonempty) : FoldPrimeComponents p hF :=
  primeComponentsMax h3 h19 hF (t := 127 / 500) (by norm_num) (by norm_num)

/-- `FoldComponents` has an instance on every middle block of primes `≡ 3 (4)`, `≥ 19`. -/
noncomputable def sanity_block {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ}
    [∀ i, Fact (pr i).Prime] (h3 : ∀ i, pr i % 4 = 3) (h19 : ∀ i, 19 ≤ pr i)
    (hne : MiddleNonempty pr) : FoldComponents pr hne :=
  blockComponentsMax h3 h19 hne (t := 127 / 500) (by norm_num) (by norm_num)

/-- **B7's `ReplacementData` is inhabited on the paper's frame** of every middle block of primes
`≡ 3 (4)`, `≥ 19`, for any root, weights and inputs. -/
noncomputable def sanity_replacementData {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ}
    [∀ i, Fact (pr i).Prime] (h : ClassThreeBlock pr) (h19 : ∀ i, 19 ≤ pr i)
    (hne : MiddleNonempty pr) (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr))
    (W : MiddleWeights) (I : MiddleInputs) {r : ℝ} (hr : 0 ≤ r) (b : ℝ) :
    ReplacementData pr h (middleFrame pr hne root W I hr b h) :=
  ofFold pr h hne root W I hr b (blockComponentsMax h.mod4 h19 hne (t := 127 / 500)
    (by norm_num) (by norm_num)) (127 / 500) (by norm_num) (by norm_num)

theorem formBound_zero {W Y : Type} [Fintype W] [DecidableEq W] [Fintype Y]
    (c : ReflectionCut W) (m : (c.Half → Y) → ℝ) :
    FormBound c m (0 : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) 0 :=
  ⟨le_rfl, fun F G => by rw [form_zero]; simp⟩

theorem optNorm_zero {W Y : Type} [Fintype W] [DecidableEq W] [Fintype Y]
    (c : ReflectionCut W) (m : (c.Half → Y) → ℝ) :
    optNorm c m (0 : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) = 0 :=
  le_antisymm (optNorm_le (formBound_zero c m)) (optNorm_nonneg m 0)

end Sarkozy.SignedComponents
