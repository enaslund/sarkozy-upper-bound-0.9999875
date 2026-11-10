module

public import Sarkozy.PartV.UpperReference

/-!
# Exact completion certificates for the 310 upper bands

The reserved caps are indexed by states, including the special observed caps
for `LR`, `RL`, `LC`, and `CL`. The 105 rational inequalities are separate from
the analytic validity of the recorded inputs and caps.
-/

@[expose] public section

namespace Sarkozy.UpperRecords

open Sarkozy.PartV Sarkozy.Labellings

/-- The exact data of `def:record:upper-bands`(a), (c), (d). -/
structure CompletionRecord where
  start : ℕ
  stop : ℕ
  budget : ℕ
  w : PType → PType → ℚ
  v : PType → PType → ℚ
  ord : FType → CompletionInput
  res : FType → CompletionInput
  ordT : FType → ℚ
  resT : FType → ℚ
  cap : PType → PType → ℚ

namespace CompletionRecord

def InputPositive (I : CompletionInput) (t : ℚ) : Prop :=
  0 < I.d ∧ 0 < I.f ∧ 1 ≤ I.h ∧ 1 ≤ I.M ∧ 0 < t

instance (I : CompletionInput) (t : ℚ) : Decidable (InputPositive I t) := by
  unfold InputPositive
  infer_instance

def Positive (R : CompletionRecord) : Prop :=
  R.w .L .L = 1 ∧ (∀ t₀ t₁, 0 < R.w t₀ t₁) ∧
    (∀ t₀ t₁, 0 < R.v t₀ t₁) ∧ (∀ t₀ t₁, 0 < R.cap t₀ t₁) ∧
    (∀ f, InputPositive (R.ord f) (R.ordT f)) ∧
    ∀ f, InputPositive (R.res f) (R.resT f)

instance (R : CompletionRecord) : Decidable R.Positive := by
  unfold Positive
  infer_instance

/-- Forty ordinary slice inequalities, forty reserved slice inequalities,
and twenty-five statewise domination inequalities. -/
def Completes (R : CompletionRecord) : Prop :=
  (∀ c t, SliceOK (R.ord t.field) (slice R.w c t)) ∧
    (∀ c t, SliceOK (R.res t.field) (slice R.v c t)) ∧
    ∀ t₀ t₁, R.cap t₀ t₁ * R.w t₀ t₁ ≤ R.v t₀ t₁

instance (R : CompletionRecord) : Decidable R.Completes := by
  unfold Completes SliceOK
  infer_instance

def RangeOK (R : CompletionRecord) : Prop :=
  P3 ≤ R.start ∧ R.start < R.stop ∧ R.stop ≤ P4 ∧
    550 ≤ R.budget ∧ R.budget ≤ 886

instance (R : CompletionRecord) : Decidable R.RangeOK := by
  unfold RangeOK
  infer_instance

noncomputable def weights (R : CompletionRecord) (h : R.Positive) : UpperWeights where
  w t₀ t₁ := R.w t₀ t₁
  v t₀ t₁ := R.v t₀ t₁
  w_LL := by exact_mod_cast h.1
  w_nonneg t₀ t₁ := by exact_mod_cast (h.2.1 t₀ t₁).le
  v_nonneg t₀ t₁ := by exact_mod_cast (h.2.2.1 t₀ t₁).le

noncomputable def realCap (R : CompletionRecord) (t₀ t₁ : PType) : ℝ := R.cap t₀ t₁

theorem weights_pos (R : CompletionRecord) (h : R.Positive) :
    (∀ t₀ t₁, 0 < (R.weights h).w t₀ t₁) ∧
      ∀ t₀ t₁, 0 < (R.weights h).v t₀ t₁ := by
  dsimp only [weights]
  constructor <;> intro t₀ t₁
  · exact_mod_cast h.2.1 t₀ t₁
  · exact_mod_cast h.2.2.1 t₀ t₁

theorem cap_pos (R : CompletionRecord) (h : R.Positive) (t₀ t₁ : PType) :
    0 < R.realCap t₀ t₁ := by
  dsimp only [realCap]
  exact_mod_cast h.2.2.2.1 t₀ t₁

theorem domination (R : CompletionRecord) (hp : R.Positive) (h : R.Completes)
    (t₀ t₁ : PType) :
    R.realCap t₀ t₁ * (R.weights hp).w t₀ t₁ ≤ (R.weights hp).v t₀ t₁ := by
  dsimp only [realCap, weights]
  exact_mod_cast h.2.2 t₀ t₁

end CompletionRecord

end Sarkozy.UpperRecords
