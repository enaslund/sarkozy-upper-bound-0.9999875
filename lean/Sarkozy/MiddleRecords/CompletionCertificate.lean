module

public import Sarkozy.PartV.MiddleReference

/-!
# Rational certificates for the middle completion weights

The certificate checks the thirteen completion inequalities and protection,
including the stronger matching-type reserved-cut gate used in the paper.
Its inputs are rational caps. Establishing the analytic estimates at those
caps is a separate obligation.
-/

@[expose] public section

namespace Sarkozy.MiddleRecords

open Sarkozy.PartV Sarkozy.Labellings

/-- Exact data for one middle piece, with the paper's equalities `wS = wD`, `vS = vD`. -/
structure CompletionRecord where
  start : ℕ
  stop : ℕ
  wD : ℚ
  wR : ℚ
  wC : ℚ
  vL : ℚ
  vD : ℚ
  vR : ℚ
  vC : ℚ
  d : ℚ
  d₁ : ℚ
  f₁ : ℚ
  f₂ : ℚ
  h₁ : ℚ
  h₂ : ℚ
  kL : ℚ
  kD : ℚ
  kE : ℚ

namespace CompletionRecord

def w (R : CompletionRecord) : PType → ℚ
  | .L => 1
  | .D | .S => R.wD
  | .R => R.wR
  | .C => R.wC

def v (R : CompletionRecord) : PType → ℚ
  | .L => R.vL
  | .D | .S => R.vD
  | .R => R.vR
  | .C => R.vC

def k (R : CompletionRecord) : PType → ℚ
  | .L => R.kL
  | .D => R.kD
  | .S | .R | .C => R.kE

def Nonneg (R : CompletionRecord) : Prop :=
  (∀ t, 0 ≤ R.w t) ∧ (∀ t, 0 ≤ R.v t) ∧
    0 ≤ R.d ∧ 0 ≤ R.d₁ ∧ 0 ≤ R.f₁ ∧ 0 ≤ R.f₂ ∧
    0 ≤ R.h₁ ∧ 0 ≤ R.h₂ ∧ ∀ t, 0 ≤ R.k t

instance (R : CompletionRecord) : Decidable R.Nonneg := by
  unfold Nonneg
  infer_instance

def Completes (R : CompletionRecord) : Prop :=
  R.d ≤ R.w .D ∧ R.w .D ≤ R.w .S ∧
    R.f₂ * R.w .D + R.h₂ * R.w .S ≤ R.w .R ∧
    R.w .R ^ 2 ≤ R.w .C * R.w .S ∧
    R.d₁ * R.v .L ≤ R.v .D ∧ R.v .D ≤ R.v .S ∧
    R.f₁ * R.v .D + R.h₁ * R.v .S ≤ R.v .R ∧
    R.v .R ^ 2 ≤ R.v .C * R.v .S ∧ ∀ t, R.k t * R.w t ≤ R.v t

instance (R : CompletionRecord) : Decidable R.Completes := by
  unfold Completes
  infer_instance

def Protects (R : CompletionRecord) : Prop := 2 * R.k .D * R.w .D ≤ R.v .D

instance (R : CompletionRecord) : Decidable R.Protects := by
  unfold Protects
  infer_instance

noncomputable def weights (R : CompletionRecord) (h : R.Nonneg) : MiddleWeights where
  w t := R.w t
  v t := R.v t
  w_L := by norm_num [w]
  w_nonneg t := by exact_mod_cast h.1 t
  v_nonneg t := by exact_mod_cast h.2.1 t

noncomputable def inputs (R : CompletionRecord) : MiddleInputs where
  d := R.d
  d₁ := R.d₁
  f₁ := R.f₁
  f₂ := R.f₂
  h₁ := R.h₁
  h₂ := R.h₂
  k t := R.k t

theorem completes_sound (R : CompletionRecord) (hn : R.Nonneg) (h : R.Completes) :
    (R.weights hn).Completes R.inputs := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  dsimp only [MiddleWeights.Completes, weights, inputs]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun t => ?_⟩
  · exact_mod_cast h1
  · exact_mod_cast h2
  · exact_mod_cast h3
  · exact_mod_cast h4
  · exact_mod_cast h5
  · exact_mod_cast h6
  · exact_mod_cast h7
  · exact_mod_cast h8
  · exact_mod_cast h9 t

theorem protects_sound (R : CompletionRecord) (hn : R.Nonneg) (h : R.Protects) :
    (R.weights hn).Protects R.inputs := by
  dsimp only [MiddleWeights.Protects, weights, inputs]
  change 2 * R.k .D * R.w .D ≤ R.v .D at h
  exact_mod_cast h

theorem inputs_nonneg (R : CompletionRecord) (hn : R.Nonneg) :
    0 ≤ R.inputs.d ∧ 0 ≤ R.inputs.d₁ ∧ 0 ≤ R.inputs.f₁ ∧ 0 ≤ R.inputs.f₂ ∧
      0 ≤ R.inputs.h₁ ∧ 0 ≤ R.inputs.h₂ ∧ ∀ t, 0 ≤ R.inputs.k t := by
  rcases hn.2.2 with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  dsimp only [inputs]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun t => ?_⟩
  · exact_mod_cast h1
  · exact_mod_cast h2
  · exact_mod_cast h3
  · exact_mod_cast h4
  · exact_mod_cast h5
  · exact_mod_cast h6
  · exact_mod_cast h7 t

end CompletionRecord

end Sarkozy.MiddleRecords
