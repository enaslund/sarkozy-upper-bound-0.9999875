module

public import Sarkozy.PartVLaws.RowCovariance
public import Sarkozy.JointRows.ScaledKernel

/-! Exact comparison of raw pinned weights with the graph law on three rows. -/

@[expose] public section

namespace Sarkozy.PartVLaws.FieldGraphs.RowCase

open Finset Sarkozy.Labellings Sarkozy.JointRows Sarkozy.FiveType

variable {p : ℕ} [Fact p.Prime]

theorem strictSet_nonempty (c : RowCase) (hp : 2 ^ 512 ≤ p) (hW : WeilBound (ZMod p))
    (b : c.Index → ZMod p) (hb : Function.Injective b) :
    (Coll.strictSet (c.allowed b)).Nonempty := by
  by_contra h
  have hs := not_nonempty_iff_eq_empty.mp h
  have ht := (c.strictLaw hp hW b hb).total
  simp [c.strictLaw_weight hp hW b hb, hs] at ht

noncomputable def jointScale (c : RowCase) (b : c.Index → ZMod p) : ℝ :=
  (2 : ℝ) ^ (Coll.pairSet c.finSigns).card *
    ((Coll.strictSet (c.allowed b)).card : ℝ)⁻¹ ^ 2 *
      (injLabellings (ZMod p) c.rowGraph).card

theorem jointScale_pos (c : RowCase) (hp : 2 ^ 512 ≤ p) (hW : WeilBound (ZMod p))
    (b : c.Index → ZMod p) (hb : Function.Injective b)
    (hne : (injLabellings (ZMod p) c.rowGraph).Nonempty) : 0 < c.jointScale b := by
  have hs : (0 : ℝ) < (Coll.strictSet (c.allowed b)).card :=
    Nat.cast_pos.mpr (card_pos.mpr (c.strictSet_nonempty hp hW b hb))
  have hg : (0 : ℝ) < (injLabellings (ZMod p) c.rowGraph).card :=
    Nat.cast_pos.mpr (card_pos.mpr hne)
  unfold jointScale
  positivity

theorem row_joint_weight (c : RowCase) (hp : 2 ^ 512 ≤ p) (hW : WeilBound (ZMod p))
    (b : c.Index → ZMod p) (hb : Function.Injective b)
    (hne : (injLabellings (ZMod p) c.rowGraph).Nonempty) (x y : c.Index → ZMod p) :
    (c.strictLaw hp hW b hb).weight x * (c.strictLaw hp hW b hb).weight y *
      c.rowKernel x y = c.jointScale b * (graphLaw c.rowGraph hne).weight (c.pack b x y) := by
  classical
  have hn : ((injLabellings (ZMod p) c.rowGraph).card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (card_ne_zero.mpr hne)
  rw [c.strictLaw_weight, c.strictLaw_weight, c.rowKernel_indicator]
  simp only [graphLaw, c.pack_mem_iff b x y hb]
  by_cases hx : x ∈ Coll.strictSet (c.allowed b) <;>
    by_cases hy : y ∈ Coll.strictSet (c.allowed b) <;>
    by_cases hc : Coll.Compatible c.finSigns (c.labelEquiv x) (c.labelEquiv y)
  all_goals simp only [hx, hy, hc, and_self, and_false, false_and, ↓reduceIte,
    zero_mul, mul_zero]
  unfold jointScale
  field_simp

end Sarkozy.PartVLaws.FieldGraphs.RowCase
