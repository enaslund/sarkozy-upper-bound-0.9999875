module

public import Sarkozy.PartVLaws.RowPinData

/-! Exact identification of the strict row reference law with uniform pinned labellings. -/

@[expose] public section

namespace Sarkozy.PartVLaws.FieldGraphs.RowCase

open Finset Sarkozy.Labellings Sarkozy.JointRows Sarkozy.ExtractionK

variable {p : ℕ} [Fact p.Prime]

theorem labelEquiv_mem (c : RowCase) (b : c.Index → ZMod p) (hb : Function.Injective b)
    (x : c.Index → ZMod p) :
    c.labelEquiv x ∈ pinLab (c.fixedLabels b) (c.pinData b) ↔
      x ∈ Coll.strictSet (c.allowed b) := by
  rw [mem_pinLab]
  simp only [Coll.strictSet, mem_filter, mem_univ, true_and, c.pinData_allowed b hb]
  change (Function.Injective (fun i => x (c.indexEquiv.symm i)) ∧
      ∀ i, x (c.indexEquiv.symm i) ∈ c.allowed b (c.indexEquiv.symm i)) ↔
    Function.Injective x ∧ ∀ i, x i ∈ c.allowed b i
  constructor
  · rintro ⟨hi, ha⟩
    refine ⟨?_, fun i => by simpa using ha (c.indexEquiv i)⟩
    intro i j hij
    apply c.indexEquiv.injective
    apply hi
    simpa using hij
  · rintro ⟨hi, ha⟩
    exact ⟨hi.comp c.indexEquiv.symm.injective, fun i => ha _⟩

theorem strict_card (c : RowCase) (b : c.Index → ZMod p) (hb : Function.Injective b) :
    (Coll.strictSet (c.allowed b)).card = (pinLab (c.fixedLabels b) (c.pinData b)).card := by
  apply card_bij (fun x _ => c.labelEquiv x)
  · intro x hx
    exact (c.labelEquiv_mem b hb x).mpr hx
  · intro x _ y _ h
    exact c.labelEquiv.injective h
  · intro y hy
    refine ⟨c.labelEquiv.symm y, ?_, c.labelEquiv.apply_symm_apply y⟩
    apply (c.labelEquiv_mem b hb _).mp
    simpa using hy

noncomputable def finLaw (c : RowCase) (hp : 2 ^ 512 ≤ p) (hW : WeilBound (ZMod p))
    (b : c.Index → ZMod p) (hb : Function.Injective b) :
    FiniteLaw (Fin (Fintype.card c.Index) → ZMod p) :=
  lawEquiv (c.strictLaw hp hW b hb) c.labelEquiv

theorem finLaw_weight (c : RowCase) (hp : 2 ^ 512 ≤ p) (hW : WeilBound (ZMod p))
    (b : c.Index → ZMod p) (hb : Function.Injective b)
    (x : Fin (Fintype.card c.Index) → ZMod p) :
    (c.finLaw hp hW b hb).weight x =
      if x ∈ pinLab (c.fixedLabels b) (c.pinData b) then
        (((pinLab (c.fixedLabels b) (c.pinData b)).card : ℝ))⁻¹ else 0 := by
  change (c.strictLaw hp hW b hb).weight (c.labelEquiv.symm x) = _
  rw [show (c.strictLaw hp hW b hb).weight (c.labelEquiv.symm x) = _ from
    Coll.strict_product_weight (c.allowed b) (c.allowed_nonempty hp hW b hb)
      (c.prob_injective_pos hp hW b hb) (c.labelEquiv.symm x)]
  simp only [c.strict_card b hb, ← c.labelEquiv_mem b hb, Equiv.apply_symm_apply]

end Sarkozy.PartVLaws.FieldGraphs.RowCase
