module

public import Sarkozy.MiddleCertificates.L20Bridge
public import Sarkozy.L20Cap.RectangleCertificate.PartitionBound






@[expose] public section

namespace Sarkozy.MiddlePrimeInputs

open Finset Sarkozy.Labellings Sarkozy.Cuts Sarkozy.Recentering Sarkozy.BlockAdapter
  Sarkozy.BlockSpecPaper
  Sarkozy.BlockSpecPaper.AllpData Sarkozy.PartV Sarkozy.MiddleCertificates
open scoped BigOperators InnerProductSpace

open L20Cap Sarkozy.Extraction Sarkozy.ExtractionK in
theorem l20W3Bounds_of_rectangle (i : Fin 33) {p : ℕ} [Fact p.Prime] [Nonempty (CoreT (ZMod p))]
    [Nonempty (PairT (ZMod p))] (hm1 : quadraticChar (ZMod p) (-1) = -1) (hWeil : Target.Weil)
    (hFour : Target.FourCycle) (h6 : 6 ≤ Fintype.card (ZMod p))
    (h40 : (2 : ℝ) ^ 40 ≤ p) {m NA mstar Nns χp : ℝ} (hNA : 282 * (p : ℝ)⁻¹ ≤ NA)
    (hm : (coreLaw (F := ZMod p)).expect (fun C => Kbar C.1 - 1) ≤ m) (hm0 : 0 ≤ m)
    (hΔ : 0 < 30 * (Fintype.card (ZMod p) : ℝ)⁻¹ -
      (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) ^ 2)
    (hgate : cGap (Fintype.card (ZMod p) : ℝ)⁻¹ (tauG (ZMod p) m)
      (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) (xPaper (ZMod p) m NA) ≤ sP (ZMod p) m)
    (hNns0 : 0 ≤ Nns)
    (hXns : ∀ φ h : (Fin 6 → ZMod p) → ℝ,
      |(graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z => φ z *
          (graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z' => Kns z z' * h z'))| ≤
        Nns * Real.sqrt ((graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z => φ z ^ 2)) *
          Real.sqrt ((graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z => h z ^ 2)))
    (hstar : |kernelForm (halfLaw h6) (halfLaw h6)
      (fun x x' => starPart6 (labels x) (labels x')) (fun _ => 1) (fun _ => 1)| ≤ mstar)
    (hεZ : Nns + Dbal (Real.sqrt (Fintype.card (ZMod p)))⁻¹ (Fintype.card (ZMod p) : ℝ)⁻¹ +
      mstar < 1)
    (hχ0 : 0 ≤ χp)
    (hchi : nrm (halfLaw h6) (fun x => recOp (halfLaw h6) (cutT h6) (fun _ => 1) x - 1) ^ 2 ≤ χp)
    (hC1 : (sP (ZMod p) m * cGap (Fintype.card (ZMod p) : ℝ)⁻¹ (tauG (ZMod p) m)
        (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) (xPaper (ZMod p) m NA) /
      prob ((coreLaw (F := ZMod p)).product (pairLaw (F := ZMod p))) Avoid +
        Dbal (Real.sqrt (Fintype.card (ZMod p)))⁻¹ (Fintype.card (ZMod p) : ℝ)⁻¹) /
        (1 - (Nns + Dbal (Real.sqrt (Fintype.card (ZMod p)))⁻¹ (Fintype.card (ZMod p) : ℝ)⁻¹ +
          mstar)) < 1)
    (hH1 : (Nns + Dbal (Real.sqrt (Fintype.card (ZMod p)))⁻¹ (Fintype.card (ZMod p) : ℝ)⁻¹) /
      (1 - (Nns + Dbal (Real.sqrt (Fintype.card (ZMod p)))⁻¹ (Fintype.card (ZMod p) : ℝ)⁻¹ +
        mstar)) < 1)
    (hgateC : (sP (ZMod p) m * cGap (Fintype.card (ZMod p) : ℝ)⁻¹ (tauG (ZMod p) m)
        (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) (xPaper (ZMod p) m NA) /
        prob ((coreLaw (F := ZMod p)).product (pairLaw (F := ZMod p))) Avoid +
          Dbal (Real.sqrt (Fintype.card (ZMod p)))⁻¹ (Fintype.card (ZMod p) : ℝ)⁻¹) /
          (1 - (Nns + Dbal (Real.sqrt (Fintype.card (ZMod p)))⁻¹ (Fintype.card (ZMod p) : ℝ)⁻¹ +
            mstar)) ≤
        (allpG i 0 : ℝ) * (√(p : ℝ))⁻¹)
    (hgateB : χp / (1 - (Nns + Dbal (Real.sqrt (Fintype.card (ZMod p)))⁻¹
        (Fintype.card (ZMod p) : ℝ)⁻¹) /
        (1 - (Nns + Dbal (Real.sqrt (Fintype.card (ZMod p)))⁻¹ (Fintype.card (ZMod p) : ℝ)⁻¹ +
          mstar))) ≤ (allpB i 0 : ℝ) / p) :
    L20W3Bounds i p := by
  have h20 : (2 : ℝ) ^ 20 ≤ Fintype.card (ZMod p) := by
    rw [ZMod.card]
    exact le_trans (by norm_num) h40
  have hQp : RectangleCertificate.anchor ≤ (p : ℝ) := by
    rw [RectangleCertificate.anchor]
    exact h40
  have hQ : (64 : ℝ) ≤ RectangleCertificate.anchor := by
    rw [RectangleCertificate.anchor]
    norm_num
  exact l20W3Bounds_of_balanced i hm1 hWeil hFour h6 h20 RectangleCertificate.partition
    RectangleCertificate.partition_exact RectangleCertificate.recordOf
    RectangleCertificate.recordOf_valid hQ hQp
    ((RectangleCertificate.partition_bound p).trans hNA) hm hm0 hΔ hgate hNns0 hXns hstar hεZ
    hχ0 hchi hC1 hH1 hgateC hgateB

/-- **The middle pieces at or above the certificate's threshold `2⁴⁰`**: `2⁴⁰ ≤ X_i` exactly
for the last two pieces (`i = 31`, start `2⁴⁰`; `i = 32`, start `2⁴⁵`). -/
theorem pieceStart_ge_two_pow_40 (i : Fin 33) : 2 ^ 40 ≤ pieceStart i ↔ 31 ≤ i.val := by
  revert i
  unfold pieceStart pieceEnds
  decide +kernel

/-- Under ALLp the only uniform piece at or above `2⁴⁰` is the last one (`2⁴⁵`). -/
theorem uniform_ge_two_pow_40 (i : Fin 33) (hi : allpIndividual i = none)
    (h40 : 2 ^ 40 ≤ pieceStart i) : i.val = 32 := by
  have h := (pieceStart_ge_two_pow_40 i).mp h40
  have hne : i.val ≠ 31 := by
    intro h31
    simp [allpIndividual, h31] at hi
  omega

end Sarkozy.MiddlePrimeInputs
