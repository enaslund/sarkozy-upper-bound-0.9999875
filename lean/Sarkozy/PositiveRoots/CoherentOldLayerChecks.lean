module

public import Sarkozy.PositiveRoots.CoherentOldLayerData

/-! Kernel checks for the untilted layer matrix and its factor residual. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentOldLayer

open Finset Sarkozy.SpectralD Sarkozy.SpectralC CoherentEndpoint

def modelR (i j : Fin 27) : ℤ :=
  100 * starReal .layer (index .layer i) (index .layer j) + if i = j then 219 else 0

def modelI (i j : Fin 27) : ℤ :=
  100 * starImag .layer (index .layer i) (index .layer j)

theorem model_00 : ∀ j, R 0 j = modelR 0 j ∧ I 0 j = modelI 0 j := by
  decide +kernel

theorem model_01 : ∀ j, R 1 j = modelR 1 j ∧ I 1 j = modelI 1 j := by
  decide +kernel

theorem model_02 : ∀ j, R 2 j = modelR 2 j ∧ I 2 j = modelI 2 j := by
  decide +kernel

theorem model_03 : ∀ j, R 3 j = modelR 3 j ∧ I 3 j = modelI 3 j := by
  decide +kernel

theorem model_04 : ∀ j, R 4 j = modelR 4 j ∧ I 4 j = modelI 4 j := by
  decide +kernel

theorem model_05 : ∀ j, R 5 j = modelR 5 j ∧ I 5 j = modelI 5 j := by
  decide +kernel

theorem model_06 : ∀ j, R 6 j = modelR 6 j ∧ I 6 j = modelI 6 j := by
  decide +kernel

theorem model_07 : ∀ j, R 7 j = modelR 7 j ∧ I 7 j = modelI 7 j := by
  decide +kernel

theorem model_08 : ∀ j, R 8 j = modelR 8 j ∧ I 8 j = modelI 8 j := by
  decide +kernel

theorem model_09 : ∀ j, R 9 j = modelR 9 j ∧ I 9 j = modelI 9 j := by
  decide +kernel

theorem model_10 : ∀ j, R 10 j = modelR 10 j ∧ I 10 j = modelI 10 j := by
  decide +kernel

theorem model_11 : ∀ j, R 11 j = modelR 11 j ∧ I 11 j = modelI 11 j := by
  decide +kernel

theorem model_12 : ∀ j, R 12 j = modelR 12 j ∧ I 12 j = modelI 12 j := by
  decide +kernel

theorem model_13 : ∀ j, R 13 j = modelR 13 j ∧ I 13 j = modelI 13 j := by
  decide +kernel

theorem model_14 : ∀ j, R 14 j = modelR 14 j ∧ I 14 j = modelI 14 j := by
  decide +kernel

theorem model_15 : ∀ j, R 15 j = modelR 15 j ∧ I 15 j = modelI 15 j := by
  decide +kernel

theorem model_16 : ∀ j, R 16 j = modelR 16 j ∧ I 16 j = modelI 16 j := by
  decide +kernel

theorem model_17 : ∀ j, R 17 j = modelR 17 j ∧ I 17 j = modelI 17 j := by
  decide +kernel

theorem model_18 : ∀ j, R 18 j = modelR 18 j ∧ I 18 j = modelI 18 j := by
  decide +kernel

theorem model_19 : ∀ j, R 19 j = modelR 19 j ∧ I 19 j = modelI 19 j := by
  decide +kernel

theorem model_20 : ∀ j, R 20 j = modelR 20 j ∧ I 20 j = modelI 20 j := by
  decide +kernel

theorem model_21 : ∀ j, R 21 j = modelR 21 j ∧ I 21 j = modelI 21 j := by
  decide +kernel

theorem model_22 : ∀ j, R 22 j = modelR 22 j ∧ I 22 j = modelI 22 j := by
  decide +kernel

theorem model_23 : ∀ j, R 23 j = modelR 23 j ∧ I 23 j = modelI 23 j := by
  decide +kernel

theorem model_24 : ∀ j, R 24 j = modelR 24 j ∧ I 24 j = modelI 24 j := by
  decide +kernel

theorem model_25 : ∀ j, R 25 j = modelR 25 j ∧ I 25 j = modelI 25 j := by
  decide +kernel

theorem model_26 : ∀ j, R 26 j = modelR 26 j ∧ I 26 j = modelI 26 j := by
  decide +kernel

theorem model_checks (i j : Fin 27) : R i j = modelR i j ∧ I i j = modelI i j := by
  fin_cases i
  · exact model_00 j
  · exact model_01 j
  · exact model_02 j
  · exact model_03 j
  · exact model_04 j
  · exact model_05 j
  · exact model_06 j
  · exact model_07 j
  · exact model_08 j
  · exact model_09 j
  · exact model_10 j
  · exact model_11 j
  · exact model_12 j
  · exact model_13 j
  · exact model_14 j
  · exact model_15 j
  · exact model_16 j
  · exact model_17 j
  · exact model_18 j
  · exact model_19 j
  · exact model_20 j
  · exact model_21 j
  · exact model_22 j
  · exact model_23 j
  · exact model_24 j
  · exact model_25 j
  · exact model_26 j

def scale : ℤ := 1000000000000
def shift : ℤ := 20000000000

theorem residual_symm : ∀ i j, scale * R i j - gramReal BR BI i j =
    scale * R j i - gramReal BR BI j i := by decide +kernel

theorem residual_skew : ∀ i j, scale * I i j - gramImag BR BI i j =
    -(scale * I j i - gramImag BR BI j i) := by decide +kernel

theorem row_00 : ∑ j,
    (|(if (0 : Fin 27) = j then shift else 0) - (scale * R 0 j - gramReal BR BI 0 j)| +
      |scale * I 0 j - gramImag BR BI 0 j|) ≤ shift := by decide +kernel

theorem row_01 : ∑ j,
    (|(if (1 : Fin 27) = j then shift else 0) - (scale * R 1 j - gramReal BR BI 1 j)| +
      |scale * I 1 j - gramImag BR BI 1 j|) ≤ shift := by decide +kernel

theorem row_02 : ∑ j,
    (|(if (2 : Fin 27) = j then shift else 0) - (scale * R 2 j - gramReal BR BI 2 j)| +
      |scale * I 2 j - gramImag BR BI 2 j|) ≤ shift := by decide +kernel

theorem row_03 : ∑ j,
    (|(if (3 : Fin 27) = j then shift else 0) - (scale * R 3 j - gramReal BR BI 3 j)| +
      |scale * I 3 j - gramImag BR BI 3 j|) ≤ shift := by decide +kernel

theorem row_04 : ∑ j,
    (|(if (4 : Fin 27) = j then shift else 0) - (scale * R 4 j - gramReal BR BI 4 j)| +
      |scale * I 4 j - gramImag BR BI 4 j|) ≤ shift := by decide +kernel

theorem row_05 : ∑ j,
    (|(if (5 : Fin 27) = j then shift else 0) - (scale * R 5 j - gramReal BR BI 5 j)| +
      |scale * I 5 j - gramImag BR BI 5 j|) ≤ shift := by decide +kernel

theorem row_06 : ∑ j,
    (|(if (6 : Fin 27) = j then shift else 0) - (scale * R 6 j - gramReal BR BI 6 j)| +
      |scale * I 6 j - gramImag BR BI 6 j|) ≤ shift := by decide +kernel

theorem row_07 : ∑ j,
    (|(if (7 : Fin 27) = j then shift else 0) - (scale * R 7 j - gramReal BR BI 7 j)| +
      |scale * I 7 j - gramImag BR BI 7 j|) ≤ shift := by decide +kernel

theorem row_08 : ∑ j,
    (|(if (8 : Fin 27) = j then shift else 0) - (scale * R 8 j - gramReal BR BI 8 j)| +
      |scale * I 8 j - gramImag BR BI 8 j|) ≤ shift := by decide +kernel

theorem row_09 : ∑ j,
    (|(if (9 : Fin 27) = j then shift else 0) - (scale * R 9 j - gramReal BR BI 9 j)| +
      |scale * I 9 j - gramImag BR BI 9 j|) ≤ shift := by decide +kernel

theorem row_10 : ∑ j,
    (|(if (10 : Fin 27) = j then shift else 0) - (scale * R 10 j - gramReal BR BI 10 j)| +
      |scale * I 10 j - gramImag BR BI 10 j|) ≤ shift := by decide +kernel

theorem row_11 : ∑ j,
    (|(if (11 : Fin 27) = j then shift else 0) - (scale * R 11 j - gramReal BR BI 11 j)| +
      |scale * I 11 j - gramImag BR BI 11 j|) ≤ shift := by decide +kernel

theorem row_12 : ∑ j,
    (|(if (12 : Fin 27) = j then shift else 0) - (scale * R 12 j - gramReal BR BI 12 j)| +
      |scale * I 12 j - gramImag BR BI 12 j|) ≤ shift := by decide +kernel

theorem row_13 : ∑ j,
    (|(if (13 : Fin 27) = j then shift else 0) - (scale * R 13 j - gramReal BR BI 13 j)| +
      |scale * I 13 j - gramImag BR BI 13 j|) ≤ shift := by decide +kernel

theorem row_14 : ∑ j,
    (|(if (14 : Fin 27) = j then shift else 0) - (scale * R 14 j - gramReal BR BI 14 j)| +
      |scale * I 14 j - gramImag BR BI 14 j|) ≤ shift := by decide +kernel

theorem row_15 : ∑ j,
    (|(if (15 : Fin 27) = j then shift else 0) - (scale * R 15 j - gramReal BR BI 15 j)| +
      |scale * I 15 j - gramImag BR BI 15 j|) ≤ shift := by decide +kernel

theorem row_16 : ∑ j,
    (|(if (16 : Fin 27) = j then shift else 0) - (scale * R 16 j - gramReal BR BI 16 j)| +
      |scale * I 16 j - gramImag BR BI 16 j|) ≤ shift := by decide +kernel

theorem row_17 : ∑ j,
    (|(if (17 : Fin 27) = j then shift else 0) - (scale * R 17 j - gramReal BR BI 17 j)| +
      |scale * I 17 j - gramImag BR BI 17 j|) ≤ shift := by decide +kernel

theorem row_18 : ∑ j,
    (|(if (18 : Fin 27) = j then shift else 0) - (scale * R 18 j - gramReal BR BI 18 j)| +
      |scale * I 18 j - gramImag BR BI 18 j|) ≤ shift := by decide +kernel

theorem row_19 : ∑ j,
    (|(if (19 : Fin 27) = j then shift else 0) - (scale * R 19 j - gramReal BR BI 19 j)| +
      |scale * I 19 j - gramImag BR BI 19 j|) ≤ shift := by decide +kernel

theorem row_20 : ∑ j,
    (|(if (20 : Fin 27) = j then shift else 0) - (scale * R 20 j - gramReal BR BI 20 j)| +
      |scale * I 20 j - gramImag BR BI 20 j|) ≤ shift := by decide +kernel

theorem row_21 : ∑ j,
    (|(if (21 : Fin 27) = j then shift else 0) - (scale * R 21 j - gramReal BR BI 21 j)| +
      |scale * I 21 j - gramImag BR BI 21 j|) ≤ shift := by decide +kernel

theorem row_22 : ∑ j,
    (|(if (22 : Fin 27) = j then shift else 0) - (scale * R 22 j - gramReal BR BI 22 j)| +
      |scale * I 22 j - gramImag BR BI 22 j|) ≤ shift := by decide +kernel

theorem row_23 : ∑ j,
    (|(if (23 : Fin 27) = j then shift else 0) - (scale * R 23 j - gramReal BR BI 23 j)| +
      |scale * I 23 j - gramImag BR BI 23 j|) ≤ shift := by decide +kernel

theorem row_24 : ∑ j,
    (|(if (24 : Fin 27) = j then shift else 0) - (scale * R 24 j - gramReal BR BI 24 j)| +
      |scale * I 24 j - gramImag BR BI 24 j|) ≤ shift := by decide +kernel

theorem row_25 : ∑ j,
    (|(if (25 : Fin 27) = j then shift else 0) - (scale * R 25 j - gramReal BR BI 25 j)| +
      |scale * I 25 j - gramImag BR BI 25 j|) ≤ shift := by decide +kernel

theorem row_26 : ∑ j,
    (|(if (26 : Fin 27) = j then shift else 0) - (scale * R 26 j - gramReal BR BI 26 j)| +
      |scale * I 26 j - gramImag BR BI 26 j|) ≤ shift := by decide +kernel

theorem residual_rows (i : Fin 27) : ∑ j,
    (|(if i = j then shift else 0) - (scale * R i j - gramReal BR BI i j)| +
      |scale * I i j - gramImag BR BI i j|) ≤ shift := by
  fin_cases i
  · exact row_00
  · exact row_01
  · exact row_02
  · exact row_03
  · exact row_04
  · exact row_05
  · exact row_06
  · exact row_07
  · exact row_08
  · exact row_09
  · exact row_10
  · exact row_11
  · exact row_12
  · exact row_13
  · exact row_14
  · exact row_15
  · exact row_16
  · exact row_17
  · exact row_18
  · exact row_19
  · exact row_20
  · exact row_21
  · exact row_22
  · exact row_23
  · exact row_24
  · exact row_25
  · exact row_26

theorem checked_matrix_nonneg (x : Fin 27 → ℂ) :
    0 ≤ (qform (fun i j => gaussian (modelR i j) (modelI i j)) x).re := by
  have h := qform_nonneg_of_gaussian_factor R I BR BI scale shift (by decide)
    residual_symm residual_skew residual_rows x
  simpa only [(model_checks _ _).1, (model_checks _ _).2] using h

end Sarkozy.PositiveRoots.CoherentOldLayer
