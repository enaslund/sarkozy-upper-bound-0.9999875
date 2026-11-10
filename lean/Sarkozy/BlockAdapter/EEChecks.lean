module

public import Sarkozy.UpperRecords.CompletionData

@[expose] public section

/-!
# The rational gate of the upper `E × E` layer caps

`ee_gate`: on each of the 310 upper bands, for the nine `E × E` type pairs `(t₀, t₁)`
(`t₀, t₁ ∈ {S, R, C}`), the recorded layer cap `g = cap(t₀, t₁)` satisfies `g ≤ 1` and
`(81 + g)² ≤ g² X` at the band start `X`, and `81² ≤ X`. Checked by `decide +kernel`.
(`UpperEE.lean` turns it into `81/(p - 81) ≤ g p^{-1/2}` for every prime `p ≥ X`, the condition of
the edgeless cut bound with `|U⁺| = 9`.)
-/

namespace Sarkozy.BlockAdapter

open Sarkozy.UpperRecords Sarkozy.PartV

/-- The gate of one `E × E` cap: `g ≤ 1` and `(81 + g)² ≤ g² X`. -/
def EEOK (R : CompletionRecord) (t₀ t₁ : PType) : Prop :=
  R.cap t₀ t₁ ≤ 1 ∧
    (81 + R.cap t₀ t₁) * (81 + R.cap t₀ t₁) ≤ R.cap t₀ t₁ * R.cap t₀ t₁ * (R.start : ℚ)

instance (R : CompletionRecord) (t₀ t₁ : PType) : Decidable (EEOK R t₀ t₁) := by
  unfold EEOK
  infer_instance

/-- The gate of the nine `E × E` caps of a band. -/
def EEGate (R : CompletionRecord) : Prop :=
  6561 ≤ R.start ∧ EEOK R .S .S ∧ EEOK R .S .R ∧ EEOK R .S .C ∧ EEOK R .R .S ∧ EEOK R .R .R ∧
    EEOK R .R .C ∧ EEOK R .C .S ∧ EEOK R .C .R ∧ EEOK R .C .C

instance (R : CompletionRecord) : Decidable (EEGate R) := by
  unfold EEGate
  infer_instance

/-- **The `E × E` gate on all 310 upper bands.** -/
theorem ee_gate : ∀ i : Fin 310, EEGate (CompletionData.record i) := by
  decide +kernel

end Sarkozy.BlockAdapter
