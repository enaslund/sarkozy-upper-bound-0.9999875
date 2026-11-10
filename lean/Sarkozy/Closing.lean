module

public import Sarkozy.Parameters

@[expose] public section

/-!
# Joint closing from the outward ledger

Formalizes `eq:final-joint-closing` and the arithmetic consequence of
`paper/four_routes_ledger.tex`. The bounds on the *actual* construction remain
explicit hypotheses. This file does not certify the analytic construction or
the Python computations that produced the ledger.
-/

namespace Sarkozy

structure ClosingLedger where
  L₀ : ℝ
  E : ℝ
  J : ℝ
  W : ℝ
  m₁ : ℝ
  deltaAlpha : ℝ
  deltaMatching : ℝ
  deltaOdd : ℝ
  deltaEven : ℝ
  deltaUpper : ℝ
  upperError : ℝ

noncomputable def ClosingLedger.theta (l : ClosingLedger) : ℝ :=
  (63 / 64 : ℝ) * (l.L₀ + l.E) + l.J + l.W + (1 - l.m₁) / 64 -
    (l.deltaAlpha + l.deltaMatching + l.deltaOdd + l.deltaEven) -
    l.deltaUpper + l.upperError

/-- Weak inequalities suffice; the paper supplies strict outward bounds. -/
structure ClosingLedger.Bounds (l : ClosingLedger) : Prop where
  L₀_le : l.L₀ ≤ 0.000507024733
  E_le : l.E ≤ 0.785417906625
  J_le : l.J ≤ 0.264252164235
  W_le : l.W ≤ 0.000041043577
  m₁_ge : 1.529526120248 ≤ l.m₁
  deltaAlpha_ge : 0.007949257298 ≤ l.deltaAlpha
  deltaMatching_ge : 0.013289595166 ≤ l.deltaMatching
  deltaOdd_ge : 0.006920381923 ≤ l.deltaOdd
  deltaEven_ge : 0.000788314597 ≤ l.deltaEven
  deltaUpper_ge : 0.000716967431 ≤ l.deltaUpper
  upperError_le : l.upperError ≤ 0.000000070807

/-- Exact rational assembly of the displayed outward ledger. -/
theorem ClosingLedger.theta_le_rounded {l : ClosingLedger} (h : l.Bounds) :
    l.theta ≤ (31999992668181 : ℝ) / 32000000000000 := by
  obtain ⟨hL, hE, hJ, hW, hm, hα, hM, hO, hK, hu, hR⟩ := h
  unfold ClosingLedger.theta
  linarith

theorem ClosingLedger.theta_lt_cap {l : ClosingLedger} (h : l.Bounds) :
    l.theta < closingCap := by
  have hround : (31999992668181 : ℝ) / 32000000000000 < closingCap := by
    norm_num [closingCap]
  exact (theta_le_rounded h).trans_lt hround

theorem ClosingLedger.theta_lt_one {l : ClosingLedger} (h : l.Bounds) :
    l.theta < 1 := (theta_lt_cap h).trans closingCap_lt_one

theorem ClosingLedger.margin_gt {l : ClosingLedger} (h : l.Bounds) :
    closingMargin < 1 - l.theta := by
  have ht := theta_lt_cap h
  have hm := closingCap_add_margin
  linarith

/-- A relative error below the certified margin still leaves a strict contraction. -/
theorem ClosingLedger.perturbed_lt_one {l : ClosingLedger} (h : l.Bounds)
    {error : ℝ} (he : error ≤ closingMargin) : l.theta + error < 1 := by
  have hm := margin_gt h
  linarith

end Sarkozy
