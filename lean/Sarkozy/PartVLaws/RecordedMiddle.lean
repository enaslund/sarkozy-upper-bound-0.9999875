module

public import Sarkozy.PartVLaws.FinalBridge
public import Sarkozy.MiddleRecords.PieceCompletion
public import Sarkozy.PartV.CoherentDictionary

/-!
# Middle block specifications with the recorded weights

All finite completion and sign gates are supplied from the 33 checked records.
The remaining arguments are the analytic row, root, and layer estimates.
-/

@[expose] public section

namespace Sarkozy.PartVLaws

open Sarkozy.CancellationSteps Sarkozy.PartV Sarkozy.FiveType Sarkozy.MiddleRecords

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B} {b : B}

noncomputable def MiddleUniformInputs.ofPiece (i : Fin 33)
    (hne : MiddleNonempty (blockPrimes blockOf b)) {r : ℝ} (hr : 0 ≤ r)
    (hrows₂ : RowBounds (fieldDatum (middleBlock_datumHyp₂ (blockPrimes blockOf b) hne))
      (pieceInputs i).f₂ (pieceInputs i).h₂ r)
    (hrows₁ : RowBounds (fieldDatum (middleBlock_datumHyp₁ (blockPrimes blockOf b) hne))
      (pieceInputs i).f₁ (pieceInputs i).h₁ r)
    (hroot₂ : RootEnvelope (fieldDatum (middleBlock_datumHyp₂ (blockPrimes blockOf b) hne))
      (pieceInputs i).d r)
    (hroot₁ : RootEnvelope (fieldDatum (middleBlock_datumHyp₁ (blockPrimes blockOf b) hne))
      (pieceInputs i).d₁ r)
    (hcap : MiddleLayerCaps (middleBlockFieldLaws (blockPrimes blockOf b) hne
      (uniformRoot (blockPrimes blockOf b) hne)) (pieceInputs i).k r) :
    MiddleUniformInputs blockOf b where
  hne := hne
  W := pieceWeights i
  I := pieceInputs i
  r := r
  hr := hr
  hW := pieceWeights_completes i
  hf₂ := (pieceInputs_nonneg i).2.2.2.1
  hf₁ := (pieceInputs_nonneg i).2.2.1
  hrows₂ := hrows₂
  hrows₁ := hrows₁
  hroot₂ := hroot₂
  hroot₁ := hroot₁
  hcap := hcap

noncomputable def MiddleIndividualInputs.ofPiece (i : Fin 33)
    (hne : MiddleNonempty (blockPrimes blockOf b)) (u : ℚ) {r : ℝ} (hr : 0 ≤ r)
    (hrows₂ : RowBounds
      (fieldDatum (middleBlock_datumHyp₂_individual (blockPrimes blockOf b) hne u))
      (pieceInputs i).f₂ (pieceInputs i).h₂ r)
    (hrows₁ : RowBounds (fieldDatum (middleBlock_datumHyp₁ (blockPrimes blockOf b) hne))
      (pieceInputs i).f₁ (pieceInputs i).h₁ r)
    (hroot₂ : RootEnvelope
      (fieldDatum (middleBlock_datumHyp₂_individual (blockPrimes blockOf b) hne u))
      (pieceInputs i).d r)
    (hroot₁ : RootEnvelope (fieldDatum (middleBlock_datumHyp₁ (blockPrimes blockOf b) hne))
      (pieceInputs i).d₁ r)
    (hcap : MiddleLayerCaps (middleBlockFieldLaws (blockPrimes blockOf b) hne
      (individualBlockRoot (blockPrimes blockOf b) u hne.L2)) (pieceInputs i).k r) :
    MiddleIndividualInputs blockOf b where
  hne := hne
  u := u
  W := pieceWeights i
  I := pieceInputs i
  r := r
  hr := hr
  hW := pieceWeights_completes i
  hf₂ := (pieceInputs_nonneg i).2.2.2.1
  hf₁ := (pieceInputs_nonneg i).2.2.1
  hrows₂ := hrows₂
  hrows₁ := hrows₁
  hroot₂ := hroot₂
  hroot₁ := hroot₁
  hcap := hcap

noncomputable def MiddleCoherentInputs.ofPiece (i : Fin 33)
    (hne : MiddleNonempty (blockPrimes blockOf b)) (D : Dictionary) (hD : D.Invariant)
    (u η : ℚ) (hη : 0 < η) {r : ℝ} (hr : 0 ≤ r)
    (hrows₂ : RowBounds
      (fieldDatum (middleBlock_datumHyp₂_coherent (blockPrimes blockOf b) hne D hD u hη))
      (pieceInputs i).f₂ (pieceInputs i).h₂ r)
    (hrows₁ : RowBounds (fieldDatum (middleBlock_datumHyp₁ (blockPrimes blockOf b) hne))
      (pieceInputs i).f₁ (pieceInputs i).h₁ r)
    (hroot₂ : RootEnvelope
      (fieldDatum (middleBlock_datumHyp₂_coherent (blockPrimes blockOf b) hne D hD u hη))
      (pieceInputs i).d r)
    (hroot₁ : RootEnvelope (fieldDatum (middleBlock_datumHyp₁ (blockPrimes blockOf b) hne))
      (pieceInputs i).d₁ r)
    (hcap : MiddleLayerCaps (middleBlockFieldLaws (blockPrimes blockOf b) hne
      (coherentBlockRoot (blockPrimes blockOf b) D u hη hne.L2)) (pieceInputs i).k r) :
    MiddleCoherentInputs blockOf b where
  hne := hne
  D := D
  hD := hD
  u := u
  η := η
  hη := hη
  W := pieceWeights i
  I := pieceInputs i
  r := r
  hr := hr
  hW := pieceWeights_completes i
  hf₂ := (pieceInputs_nonneg i).2.2.2.1
  hf₁ := (pieceInputs_nonneg i).2.2.1
  hrows₂ := hrows₂
  hrows₁ := hrows₁
  hroot₂ := hroot₂
  hroot₁ := hroot₁
  hcap := hcap

/-! The final piece uses the exact checked dictionary and the selected rational parameters. -/

noncomputable def MiddleCoherentInputs.ofFinalPiece
    (hne : MiddleNonempty (blockPrimes blockOf b)) {r : ℝ} (hr : 0 ≤ r)
    (hrows₂ : RowBounds
      (fieldDatum (middleBlock_datumHyp₂_coherent (blockPrimes blockOf b) hne
        CoherentDictionary.dictionary39 CoherentDictionary.dictionary39_invariant
        (67 / 40) (by norm_num : (0 : ℚ) < 1 / 100)))
      (pieceInputs 32).f₂ (pieceInputs 32).h₂ r)
    (hrows₁ : RowBounds (fieldDatum (middleBlock_datumHyp₁ (blockPrimes blockOf b) hne))
      (pieceInputs 32).f₁ (pieceInputs 32).h₁ r)
    (hroot₂ : RootEnvelope
      (fieldDatum (middleBlock_datumHyp₂_coherent (blockPrimes blockOf b) hne
        CoherentDictionary.dictionary39 CoherentDictionary.dictionary39_invariant
        (67 / 40) (by norm_num : (0 : ℚ) < 1 / 100)))
      (pieceInputs 32).d r)
    (hroot₁ : RootEnvelope (fieldDatum (middleBlock_datumHyp₁ (blockPrimes blockOf b) hne))
      (pieceInputs 32).d₁ r)
    (hcap : MiddleLayerCaps (middleBlockFieldLaws (blockPrimes blockOf b) hne
      (coherentBlockRoot (blockPrimes blockOf b) CoherentDictionary.dictionary39
        (67 / 40) (by norm_num : (0 : ℚ) < 1 / 100) hne.L2)) (pieceInputs 32).k r) :
    MiddleCoherentInputs blockOf b :=
  MiddleCoherentInputs.ofPiece 32 hne CoherentDictionary.dictionary39
    CoherentDictionary.dictionary39_invariant (67 / 40) (1 / 100) (by norm_num)
    hr hrows₂ hrows₁ hroot₂ hroot₁ hcap

end Sarkozy.PartVLaws
