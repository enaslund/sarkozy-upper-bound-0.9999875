module

public import Sarkozy.TailUnit.Main
public import Sarkozy.TheoremCParam.Main

/-!
# `hunit` in the form of `MainAnchor.PartVObligations`

`paper/sections/31_density_induction_upgrade.tex`, `lem:density:global-moment` (tail part).

* `tailLaw_unit`: under `Target.Weil`, V1's tail law `PartV.tailLaw q hne` has unit mixed `L³⁶`
  at every prime `q` above a threshold, for every proof `hne` of nonemptiness.
* `hunit_of_tailLaws`: the field `hunit` of `MainAnchor.PartVObligations`,
  `∃ p₀, ∀ q [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (D.R.μp q) 36 1`, for comparison data
  `D` whose tail reference laws are V1's (`D.R.μp q = PartV.tailLawFamily q`).
-/

@[expose] public section

namespace Sarkozy.TailUnit

open Sarkozy.PartV

/-- **The tail law has unit mixed `L³⁶` at every large prime** (`lem:density:global-moment`,
tail part), for every proof of the nonemptiness of its labelling sets. -/
theorem tailLaw_unit (hW : Target.Weil) :
    ∃ p₀ : ℕ, ∀ (q : ℕ) [Fact q.Prime], p₀ ≤ q → ∀ hne : TailNonempty q,
      MixedLpBound (tailLaw q hne) 36 1 := by
  obtain ⟨p₀, hp₀⟩ := tailLawFamily_unit hW
  refine ⟨p₀, fun q hq hle hne => ?_⟩
  have h := hp₀ q hq.out hle
  rwa [tailLawFamily_eq q hne] at h

/-- **`hunit` of `MainAnchor.PartVObligations`** (hypothesis 6 of the main theorem) for comparison
data whose tail reference laws are V1's tail laws, from `Target.Weil`. -/
theorem hunit_of_tailLaws {a : ℝ}
    {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
    {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
    [∀ L j, NeZero (p L j)]
    {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
    {E : Type} [Fintype E] [DecidableEq E] (D : TheoremCParam.ComparisonData a m₀ p pr h E)
    (hW : Target.Weil) (hμ : ∀ (q : ℕ) [NeZero q], D.R.μp q = tailLawFamily q) :
    ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (D.R.μp q) 36 1 := by
  obtain ⟨p₀, hp₀⟩ := tailLawFamily_unit hW
  exact ⟨p₀, fun q _ hq hle => by rw [hμ q]; exact hp₀ q hq hle⟩

end Sarkozy.TailUnit
