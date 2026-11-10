module

public import Sarkozy.L20Cap.RectangleCertificate.PartitionBound
public import Sarkozy.L20Cap.PrimeCapsX1
public import Sarkozy.DLK.Basic
public import Sarkozy.JointRows.PaleyGauss

/-! The actual rectangle nonstar operator is bounded by 282/p for p ≥ 2^40. -/

@[expose] public section

namespace Sarkozy.L20Cap

open Finset Sarkozy.Labellings Sarkozy.Extraction Sarkozy.ExtractionK
open Sarkozy.Cuts Sarkozy.Recentering

variable {p : ℕ} [Fact p.Prime]

theorem rectangle_nonstar_graph_bound (hW : WeilBound (ZMod p)) (h4 : FourCycleBound p)
    (hp40 : 2 ^ 40 ≤ p) (hne : (injLabellings (ZMod p) G6).Nonempty)
    (f g : (Fin 6 → ZMod p) → ℝ) :
    |(graphLaw G6 hne).expect (fun x => f x *
      (graphLaw G6 hne).expect (fun y => K6 x y * g y))| ≤
      (282 * (p : ℝ)⁻¹) * nrm (graphLaw G6 hne) f * nrm (graphLaw G6 hne) g := by
  have hς : ∀ j k, D20Z j k = 0 ∨ D20Z j k = 1 ∨ D20Z j k = -1 := by decide
  have hEx : ∀ e ∈ Ex8, D20Z e.1 e.2 ≠ 0 := by decide
  have hQp : RectangleCertificate.anchor ≤ (p : ℝ) := by
    unfold RectangleCertificate.anchor
    exact_mod_cast hp40
  have hb := sk_soft_extraction_leaf_partition_g hW (by omega : p ≠ 2) h4 G6 D20Z hς
    D20Z_antisymm hne (by simp : Fintype.card (Fin 6) ≤ 6) Ex8 hEx
    RectangleCertificate.partition RectangleCertificate.partition_exact RectangleCertificate.recordOf
    RectangleCertificate.recordOf_valid RectangleCertificate.anchor_pos hQp
    RectangleCertificate.ehat_lt_one (fun _ => 1) (fun _ => by simp) f g
  have hn (v : (Fin 6 → ZMod p) → ℝ) :
      Real.sqrt ((graphLaw G6 hne).expect (fun x => v x ^ 2)) = nrm (graphLaw G6 hne) v := by
    simp only [nrm, Recentering.ip, pow_two]
  rw [hn f, hn g] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (RectangleCertificate.partition_bound p) (nrm_nonneg _ _))
    (nrm_nonneg _ _))

variable [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))]

theorem rectangle_nonstar_norm_282 (hW : WeilBound (ZMod p)) (h4 : FourCycleBound p)
    (hp3 : p % 4 = 3) (hp40 : 2 ^ 40 ≤ p) (g : PairT (ZMod p) → ℝ) :
    nrm coreLaw (fun C => pairLaw.expect (fun b => Nrect C b * g b)) ≤
      (282 * (p : ℝ)⁻¹) * nrm pairLaw g := by
  have h6 : 6 ≤ Fintype.card (ZMod p) := by rw [ZMod.card]; omega
  have hne := injLabellings_G6_nonempty (F := ZMod p) h6
  apply hN_of_X1 (JointRows.PaleyGauss.chi_neg_one hp3) h6 hne (by positivity) _ g
  intro φ h
  simpa only [nrm, Recentering.ip, pow_two] using
    rectangle_nonstar_graph_bound hW h4 hp40 hne φ h

theorem rectangle_nonstar_norm_282_target (hW : WeilBound (ZMod p))
    (hDLK : Target.FourCycle) (hp3 : p % 4 = 3) (hp40 : 2 ^ 40 ≤ p)
    (g : PairT (ZMod p) → ℝ) :
    nrm coreLaw (fun C => pairLaw.expect (fun b => Nrect C b * g b)) ≤
      (282 * (p : ℝ)⁻¹) * nrm pairLaw g :=
  rectangle_nonstar_norm_282 hW (DLK.fourCycleBound hDLK (by omega)) hp3 hp40 g

end Sarkozy.L20Cap
