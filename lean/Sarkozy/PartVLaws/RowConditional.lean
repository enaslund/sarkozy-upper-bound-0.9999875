module

public import Sarkozy.PartVLaws.RowJointWeight
public import Sarkozy.PartVLaws.GraphRowRead

/-! The ten row estimates for the actual conditional graph laws, in arbitrary row coordinates. -/

@[expose] public section

namespace Sarkozy.PartVLaws.FieldGraphs.RowCase

open Finset Sarkozy.Labellings Sarkozy.JointRows Sarkozy.FiveType Sarkozy.PartV
  Sarkozy.Extraction

variable {p : ℕ} [Fact p.Prime] {Q : Type} [Fintype Q] [DecidableEq Q]

theorem conditional_row_weight (c : RowCase) (hp : 2 ^ 512 ≤ p)
    (hW : WeilBound (ZMod p)) (e : Q ≃ c.Index)
    (hne : (injLabellings (ZMod p) c.rowGraph).Nonempty)
    (π : FiniteLaw (Fin 3 → Q → ZMod p))
    (hπ : π = (graphLaw c.rowGraph hne).map (rowRead (Equiv.refl _) e))
    (b : Q → ZMod p) (hb : Function.Injective b) (x y : c.Index → ZMod p) :
    (c.strictLaw hp hW ((rowReindex e).symm b) (hb.comp e.symm.injective)).weight x *
      (c.strictLaw hp hW ((rowReindex e).symm b) (hb.comp e.symm.injective)).weight y *
        c.rowKernel x y = c.jointScale ((rowReindex e).symm b) *
          π.weight ![rowReindex e x, b, rowReindex e y] := by
  calc
    _ = c.jointScale ((rowReindex e).symm b) * (graphLaw c.rowGraph hne).weight
        (c.pack ((rowReindex e).symm b) x y) :=
      c.row_joint_weight hp hW _ (hb.comp e.symm.injective) hne x y
    _ = _ := ?_
  rw [hπ, graph_row_weight]
  congr 2
  funext ⟨a, i⟩
  fin_cases a <;> simp [pack, rowReadEquiv, rowReindex]

theorem conditional_row_correlation (c : RowCase) (hp : 2 ^ 512 ≤ p)
    (hW : WeilBound (ZMod p)) (h4 : FourCycleBound p) (e : Q ≃ c.Index)
    (hne : (injLabellings (ZMod p) c.rowGraph).Nonempty)
    (πE π : FiniteLaw (Fin 3 → Q → ZMod p))
    (hπ : π = (graphLaw c.rowGraph hne).map (rowRead (Equiv.refl _) e))
    (hS : GamSupported πE π) (b : Q → ZMod p) (hb : Function.Injective b)
    (hbE : (nuOf πE).weight b ≠ 0) :
    KernelCorr (nubOf πE b) (kernelOf πE π b)
      (((c.cap : ℝ) - 1 / 2 ^ 90) * (Real.sqrt p)⁻¹) := by
  let bI := (rowReindex e).symm b
  have hbI : Function.Injective bI := hb.comp e.symm.injective
  let μ := c.strictLaw hp hW bI hbI
  have hc : KernelCorr μ c.rowKernel (((c.cap : ℝ) - 1 / 2 ^ 90) * (Real.sqrt p)⁻¹) :=
    c.row_covariance_bound hp hW h4 bI hbI
  apply hc.transport (rowReindex e)
  have ha : c.jointScale bI * (nuOf πE).weight b ≠ 0 :=
    mul_ne_zero (c.jointScale_pos hp hW bI hbI hne).ne' hbE
  apply normalized_form_of_scaled μ (nubOf πE b) c.rowKernel (kernelOf πE π b)
    (rowReindex e) ha
  intro x y
  rw [fold_term πE π hS hbE]
  rw [show μ.weight x * μ.weight y * c.rowKernel x y = _ from
    c.conditional_row_weight hp hW e hne π hπ b hb x y]
  dsimp only [bI]
  field_simp

theorem conditional_row_norm (c : RowCase) (hp : 2 ^ 512 ≤ p)
    (hW : WeilBound (ZMod p)) (h4 : FourCycleBound p) (e : Q ≃ c.Index)
    (hne : (injLabellings (ZMod p) c.rowGraph).Nonempty)
    (π : FiniteLaw (Fin 3 → Q → ZMod p))
    (hπ : π = (graphLaw c.rowGraph hne).map (rowRead (Equiv.refl _) e))
    (hexch : ∀ (σ : Equiv.Perm (Fin 3)) (ω : Fin 3 → Q → ZMod p),
      π.weight (ω ∘ σ) = π.weight ω)
    (b : Q → ZMod p) (hb : Function.Injective b)
    (hbE : (nuOf π).weight b ≠ 0) :
    NormBound (nubOf π b) (kernelOf π π b) ((c.cap : ℝ) * (Real.sqrt p)⁻¹) := by
  have hc := c.conditional_row_correlation hp hW h4 e hne π π hπ
    (gamSupported_self π (hexch (Equiv.swap 0 2))) b hb hbE
  have hle : ((c.cap : ℝ) - 1 / 2 ^ 90) * (Real.sqrt p)⁻¹ ≤
      (c.cap : ℝ) * (Real.sqrt p)⁻¹ :=
    mul_le_mul_of_nonneg_right (sub_le_self _ (by positivity)) (by positivity)
  exact (hc.mono hle).normBound (by positivity) (kernelOf_exactE π hexch hbE)

end Sarkozy.PartVLaws.FieldGraphs.RowCase
