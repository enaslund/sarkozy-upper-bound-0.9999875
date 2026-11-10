module

public import Sarkozy.UpperRecords.CompletionCertificate
public import Sarkozy.PartVLaws.TailRP

/-!
# Rational upper-band certificates imply the real completion gates

The statewise caps retain the observed merge and constant improvements.
This bridge supplies `WeightsOK`; analytic `ValidInputs` remains separate.
-/

@[expose] public section

namespace Sarkozy.UpperRecords.CompletionRecord

open Sarkozy.PartV Sarkozy.Labellings Sarkozy.PartVLaws
open Sarkozy.FiveType Sarkozy.FiveType.TwoCoord

def ordinary (R : CompletionRecord) (f : FieldTy) : CompletionInput := R.ord (toFType f)

def reserved (R : CompletionRecord) (f : FieldTy) : CompletionInput := R.res (toFType f)

/-- The 105 rational inequalities give exactly the gates used in the
two-coordinate reflection-positivity proof. -/
theorem weightsOK (R : CompletionRecord) (hp : R.Positive) (h : R.Completes) :
    WeightsOK (R.weights hp) R.ordinary R.reserved R.realCap where
  g20 t := by
    have hs := sliceGates_of_sliceOK _ _ (h.1 0 (ofTy t))
    rw [field_ofTy] at hs
    exact hs
  g21 t := by
    have hs := sliceGates_of_sliceOK _ _ (h.1 1 (ofTy t))
    rw [field_ofTy] at hs
    exact hs
  g10 t := by
    have hs := sliceGates_of_sliceOK _ _ (h.2.1 0 (ofTy t))
    rw [field_ofTy] at hs
    exact hs
  g11 t := by
    have hs := sliceGates_of_sliceOK _ _ (h.2.1 1 (ofTy t))
    rw [field_ofTy] at hs
    exact hs
  dom := R.domination hp h
  posW := (R.weights_pos hp).1
  posV := (R.weights_pos hp).2

end Sarkozy.UpperRecords.CompletionRecord
