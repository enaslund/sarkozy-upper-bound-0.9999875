module

public import Sarkozy.SpectralD.SmallMatrixData
public import Sarkozy.SpectralD.BooleanModels
public import Sarkozy.SpectralD.GaussianCertificate

/-!
# Exact checks for the smaller-cut matrix candidates

The geometry checks identify the integer models with the actual graph.
The test checks clear the finite-test denominators. The residual checks
prove positivity after subtracting an explicit integer Gram matrix.
-/

@[expose] public section

namespace Sarkozy.SpectralD.SmallMatrices

open Finset Sarkozy.PartVLaws.FieldGraphs Sarkozy.SpectralC

def atTable (c : SmallCut) (T : List (List ℤ)) (i j : c.data.cut.Half) : ℤ :=
  entry T (code c i.1) (code c j.1)

def char (e : Fin 3) : ℤ := (e.val : ℤ) - 1

def modelD (c : SmallCut) (a : Fin 2) : c.data.cut.Half → c.data.cut.Half → ℤ :=
  atTable c (if a = 0 then crossTable c else signTable c)

def modelH (c : SmallCut) (a : Fin 2) : c.data.cut.Half → c.data.cut.Half → ℤ :=
  atTable c (if a = 0 then plusOneTable c else gramThreeTable c)

def testReal (c : SmallCut) (a : Fin 2) (e : Fin 3) := atTable c (testRealTable c a e)
def testImag (c : SmallCut) (a : Fin 2) (e : Fin 3) := atTable c (testImagTable c a e)
def factorReal (c : SmallCut) (a : Fin 2) (e : Fin 3) := atTable c (factorRealTable c a e)
def factorImag (c : SmallCut) (a : Fin 2) (e : Fin 3) := atTable c (factorImagTable c a e)

noncomputable def residualReal (c : SmallCut) (a : Fin 2) (e : Fin 3)
    (i j : c.data.cut.Half) : ℤ :=
  1000000000000 * testReal c a e i j - gramReal (factorReal c a e) (factorImag c a e) i j

noncomputable def residualImag (c : SmallCut) (a : Fin 2) (e : Fin 3)
    (i j : c.data.cut.Half) : ℤ :=
  1000000000000 * testImag c a e i j - gramImag (factorReal c a e) (factorImag c a e) i j

def ModelChecks (c : SmallCut) : Prop := ∀ i j : c.data.cut.Half,
  edgeSign c.edge c.data.cut.flip i.1 j.1 = atTable c (signTable c) i j ∧
  FiniteModel.crossOne c.edge c.data.cut i j = atTable c (crossTable c) i j ∧
  FiniteModel.gramOne c.edge c.data.cut i j = atTable c (gramOneTable c) i j ∧
  FiniteModel.plusOne c.edge c.data.cut i j = atTable c (plusOneTable c) i j ∧
  FiniteModel.gramThree c.edge c.data.cut i j = atTable c (gramThreeTable c) i j

def TestChecks (c : SmallCut) : Prop := ∀ (a : Fin 2) (e : Fin 3) (i j : c.data.cut.Half),
  testReal c a e i j = (if i = j then base c else 0) +
    (if a = 0 then char e * linear c * modelD c a i j else 0) +
    100000000 * char e ^ 2 * (∑ k, modelD c a k i * modelD c a k j) -
    100000000 * modelH c a i j ∧
  testImag c a e i j = (if a = 0 then 0 else char e * linear c * modelD c a i j)

def ResidualChecks (c : SmallCut) : Prop := ∀ (a : Fin 2) (e : Fin 3),
  (∀ i j, residualReal c a e i j = residualReal c a e j i) ∧
  (∀ i j, residualImag c a e i j = -residualImag c a e j i) ∧
  ∀ i, ∑ j, (|(if i = j then shift c a e else 0) - residualReal c a e i j| +
    |residualImag c a e i j|) ≤ shift c a e

def RowChecks (c : SmallCut) : Prop :=
  (∀ i j, atTable c (gramOneTable c) i j = atTable c (gramOneTable c) j i) ∧
  (∀ i j, atTable c (gramThreeTable c) i j = atTable c (gramThreeTable c) j i) ∧
  (∀ i j, atTable c (plusOneTable c) i j = atTable c (plusOneTable c) j i) ∧
  ∀ i, (∑ j, |atTable c (gramOneTable c) i j| ≤ 8928) ∧
    (∑ j, |atTable c (gramThreeTable c) i j| ≤ 8928) ∧
    (∑ j, |atTable c (plusOneTable c) i j| ≤ 12384)

theorem test_nonneg (c : SmallCut) (hc : ResidualChecks c) (a : Fin 2) (e : Fin 3)
    (x : c.data.cut.Half → ℂ) :
    0 ≤ (qform (fun i j => gaussian (testReal c a e i j) (testImag c a e i j)) x).re :=
  qform_nonneg_of_gaussian_factor (testReal c a e) (testImag c a e)
    (factorReal c a e) (factorImag c a e) 1000000000000 (shift c a e)
    (by norm_num) (hc a e).1 (hc a e).2.1 (hc a e).2.2 x

end Sarkozy.SpectralD.SmallMatrices
