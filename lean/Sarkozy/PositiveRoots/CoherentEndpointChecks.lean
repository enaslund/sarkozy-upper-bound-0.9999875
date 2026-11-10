module

public import Sarkozy.PositiveRoots.CoherentEndpointData


@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentEndpoint

open Finset Sarkozy.SpectralD Sarkozy.SpectralC

def entry (c : Cut) (T : List (List ℤ)) (i j : Fin (size c)) : ℤ :=
  (T.getD i.val []).getD j.val 0

def R (c : Cut) := entry c (realTable c)
def I (c : Cut) := entry c (imagTable c)
def BR (c : Cut) := entry c (factorRealTable c)
def BI (c : Cut) := entry c (factorImagTable c)

theorem chamber_model_00 : ∀ j,
    R .chamber 0 j = modelReal .chamber 0 j ∧
      I .chamber 0 j = modelImag .chamber 0 j := by decide +kernel

theorem chamber_model_01 : ∀ j,
    R .chamber 1 j = modelReal .chamber 1 j ∧
      I .chamber 1 j = modelImag .chamber 1 j := by decide +kernel

theorem chamber_model_02 : ∀ j,
    R .chamber 2 j = modelReal .chamber 2 j ∧
      I .chamber 2 j = modelImag .chamber 2 j := by decide +kernel

theorem chamber_model_03 : ∀ j,
    R .chamber 3 j = modelReal .chamber 3 j ∧
      I .chamber 3 j = modelImag .chamber 3 j := by decide +kernel

theorem chamber_model_04 : ∀ j,
    R .chamber 4 j = modelReal .chamber 4 j ∧
      I .chamber 4 j = modelImag .chamber 4 j := by decide +kernel

theorem chamber_model_05 : ∀ j,
    R .chamber 5 j = modelReal .chamber 5 j ∧
      I .chamber 5 j = modelImag .chamber 5 j := by decide +kernel

theorem chamber_model_06 : ∀ j,
    R .chamber 6 j = modelReal .chamber 6 j ∧
      I .chamber 6 j = modelImag .chamber 6 j := by decide +kernel

theorem chamber_model_07 : ∀ j,
    R .chamber 7 j = modelReal .chamber 7 j ∧
      I .chamber 7 j = modelImag .chamber 7 j := by decide +kernel

theorem chamber_model_08 : ∀ j,
    R .chamber 8 j = modelReal .chamber 8 j ∧
      I .chamber 8 j = modelImag .chamber 8 j := by decide +kernel

theorem chamber_model_09 : ∀ j,
    R .chamber 9 j = modelReal .chamber 9 j ∧
      I .chamber 9 j = modelImag .chamber 9 j := by decide +kernel

theorem chamber_model_10 : ∀ j,
    R .chamber 10 j = modelReal .chamber 10 j ∧
      I .chamber 10 j = modelImag .chamber 10 j := by decide +kernel

theorem chamber_model_11 : ∀ j,
    R .chamber 11 j = modelReal .chamber 11 j ∧
      I .chamber 11 j = modelImag .chamber 11 j := by decide +kernel

theorem chamber_model_12 : ∀ j,
    R .chamber 12 j = modelReal .chamber 12 j ∧
      I .chamber 12 j = modelImag .chamber 12 j := by decide +kernel

theorem chamber_model_13 : ∀ j,
    R .chamber 13 j = modelReal .chamber 13 j ∧
      I .chamber 13 j = modelImag .chamber 13 j := by decide +kernel

theorem chamber_model_14 : ∀ j,
    R .chamber 14 j = modelReal .chamber 14 j ∧
      I .chamber 14 j = modelImag .chamber 14 j := by decide +kernel

theorem chamber_model_15 : ∀ j,
    R .chamber 15 j = modelReal .chamber 15 j ∧
      I .chamber 15 j = modelImag .chamber 15 j := by decide +kernel

theorem chamber_model_16 : ∀ j,
    R .chamber 16 j = modelReal .chamber 16 j ∧
      I .chamber 16 j = modelImag .chamber 16 j := by decide +kernel

theorem chamber_model_17 : ∀ j,
    R .chamber 17 j = modelReal .chamber 17 j ∧
      I .chamber 17 j = modelImag .chamber 17 j := by decide +kernel

theorem chamber_model_18 : ∀ j,
    R .chamber 18 j = modelReal .chamber 18 j ∧
      I .chamber 18 j = modelImag .chamber 18 j := by decide +kernel

theorem chamber_model_19 : ∀ j,
    R .chamber 19 j = modelReal .chamber 19 j ∧
      I .chamber 19 j = modelImag .chamber 19 j := by decide +kernel

theorem chamber_model_20 : ∀ j,
    R .chamber 20 j = modelReal .chamber 20 j ∧
      I .chamber 20 j = modelImag .chamber 20 j := by decide +kernel

theorem chamber_model_21 : ∀ j,
    R .chamber 21 j = modelReal .chamber 21 j ∧
      I .chamber 21 j = modelImag .chamber 21 j := by decide +kernel

theorem chamber_model_22 : ∀ j,
    R .chamber 22 j = modelReal .chamber 22 j ∧
      I .chamber 22 j = modelImag .chamber 22 j := by decide +kernel

theorem chamber_model_23 : ∀ j,
    R .chamber 23 j = modelReal .chamber 23 j ∧
      I .chamber 23 j = modelImag .chamber 23 j := by decide +kernel

theorem chamber_model_24 : ∀ j,
    R .chamber 24 j = modelReal .chamber 24 j ∧
      I .chamber 24 j = modelImag .chamber 24 j := by decide +kernel

theorem chamber_model_25 : ∀ j,
    R .chamber 25 j = modelReal .chamber 25 j ∧
      I .chamber 25 j = modelImag .chamber 25 j := by decide +kernel

theorem chamber_model_26 : ∀ j,
    R .chamber 26 j = modelReal .chamber 26 j ∧
      I .chamber 26 j = modelImag .chamber 26 j := by decide +kernel

theorem chamber_model_27 : ∀ j,
    R .chamber 27 j = modelReal .chamber 27 j ∧
      I .chamber 27 j = modelImag .chamber 27 j := by decide +kernel

theorem layer_model_00 : ∀ j,
    R .layer 0 j = modelReal .layer 0 j ∧
      I .layer 0 j = modelImag .layer 0 j := by decide +kernel

theorem layer_model_01 : ∀ j,
    R .layer 1 j = modelReal .layer 1 j ∧
      I .layer 1 j = modelImag .layer 1 j := by decide +kernel

theorem layer_model_02 : ∀ j,
    R .layer 2 j = modelReal .layer 2 j ∧
      I .layer 2 j = modelImag .layer 2 j := by decide +kernel

theorem layer_model_03 : ∀ j,
    R .layer 3 j = modelReal .layer 3 j ∧
      I .layer 3 j = modelImag .layer 3 j := by decide +kernel

theorem layer_model_04 : ∀ j,
    R .layer 4 j = modelReal .layer 4 j ∧
      I .layer 4 j = modelImag .layer 4 j := by decide +kernel

theorem layer_model_05 : ∀ j,
    R .layer 5 j = modelReal .layer 5 j ∧
      I .layer 5 j = modelImag .layer 5 j := by decide +kernel

theorem layer_model_06 : ∀ j,
    R .layer 6 j = modelReal .layer 6 j ∧
      I .layer 6 j = modelImag .layer 6 j := by decide +kernel

theorem layer_model_07 : ∀ j,
    R .layer 7 j = modelReal .layer 7 j ∧
      I .layer 7 j = modelImag .layer 7 j := by decide +kernel

theorem layer_model_08 : ∀ j,
    R .layer 8 j = modelReal .layer 8 j ∧
      I .layer 8 j = modelImag .layer 8 j := by decide +kernel

theorem layer_model_09 : ∀ j,
    R .layer 9 j = modelReal .layer 9 j ∧
      I .layer 9 j = modelImag .layer 9 j := by decide +kernel

theorem layer_model_10 : ∀ j,
    R .layer 10 j = modelReal .layer 10 j ∧
      I .layer 10 j = modelImag .layer 10 j := by decide +kernel

theorem layer_model_11 : ∀ j,
    R .layer 11 j = modelReal .layer 11 j ∧
      I .layer 11 j = modelImag .layer 11 j := by decide +kernel

theorem layer_model_12 : ∀ j,
    R .layer 12 j = modelReal .layer 12 j ∧
      I .layer 12 j = modelImag .layer 12 j := by decide +kernel

theorem layer_model_13 : ∀ j,
    R .layer 13 j = modelReal .layer 13 j ∧
      I .layer 13 j = modelImag .layer 13 j := by decide +kernel

theorem layer_model_14 : ∀ j,
    R .layer 14 j = modelReal .layer 14 j ∧
      I .layer 14 j = modelImag .layer 14 j := by decide +kernel

theorem layer_model_15 : ∀ j,
    R .layer 15 j = modelReal .layer 15 j ∧
      I .layer 15 j = modelImag .layer 15 j := by decide +kernel

theorem layer_model_16 : ∀ j,
    R .layer 16 j = modelReal .layer 16 j ∧
      I .layer 16 j = modelImag .layer 16 j := by decide +kernel

theorem layer_model_17 : ∀ j,
    R .layer 17 j = modelReal .layer 17 j ∧
      I .layer 17 j = modelImag .layer 17 j := by decide +kernel

theorem layer_model_18 : ∀ j,
    R .layer 18 j = modelReal .layer 18 j ∧
      I .layer 18 j = modelImag .layer 18 j := by decide +kernel

theorem layer_model_19 : ∀ j,
    R .layer 19 j = modelReal .layer 19 j ∧
      I .layer 19 j = modelImag .layer 19 j := by decide +kernel

theorem layer_model_20 : ∀ j,
    R .layer 20 j = modelReal .layer 20 j ∧
      I .layer 20 j = modelImag .layer 20 j := by decide +kernel

theorem layer_model_21 : ∀ j,
    R .layer 21 j = modelReal .layer 21 j ∧
      I .layer 21 j = modelImag .layer 21 j := by decide +kernel

theorem layer_model_22 : ∀ j,
    R .layer 22 j = modelReal .layer 22 j ∧
      I .layer 22 j = modelImag .layer 22 j := by decide +kernel

theorem layer_model_23 : ∀ j,
    R .layer 23 j = modelReal .layer 23 j ∧
      I .layer 23 j = modelImag .layer 23 j := by decide +kernel

theorem layer_model_24 : ∀ j,
    R .layer 24 j = modelReal .layer 24 j ∧
      I .layer 24 j = modelImag .layer 24 j := by decide +kernel

theorem layer_model_25 : ∀ j,
    R .layer 25 j = modelReal .layer 25 j ∧
      I .layer 25 j = modelImag .layer 25 j := by decide +kernel

theorem layer_model_26 : ∀ j,
    R .layer 26 j = modelReal .layer 26 j ∧
      I .layer 26 j = modelImag .layer 26 j := by decide +kernel

theorem model_checks (c : Cut) (i j : Fin (size c)) :
    R c i j = modelReal c i j ∧ I c i j = modelImag c i j := by
  cases c with
  | chamber =>
    fin_cases i
    · exact chamber_model_00 j
    · exact chamber_model_01 j
    · exact chamber_model_02 j
    · exact chamber_model_03 j
    · exact chamber_model_04 j
    · exact chamber_model_05 j
    · exact chamber_model_06 j
    · exact chamber_model_07 j
    · exact chamber_model_08 j
    · exact chamber_model_09 j
    · exact chamber_model_10 j
    · exact chamber_model_11 j
    · exact chamber_model_12 j
    · exact chamber_model_13 j
    · exact chamber_model_14 j
    · exact chamber_model_15 j
    · exact chamber_model_16 j
    · exact chamber_model_17 j
    · exact chamber_model_18 j
    · exact chamber_model_19 j
    · exact chamber_model_20 j
    · exact chamber_model_21 j
    · exact chamber_model_22 j
    · exact chamber_model_23 j
    · exact chamber_model_24 j
    · exact chamber_model_25 j
    · exact chamber_model_26 j
    · exact chamber_model_27 j
  | layer =>
    fin_cases i
    · exact layer_model_00 j
    · exact layer_model_01 j
    · exact layer_model_02 j
    · exact layer_model_03 j
    · exact layer_model_04 j
    · exact layer_model_05 j
    · exact layer_model_06 j
    · exact layer_model_07 j
    · exact layer_model_08 j
    · exact layer_model_09 j
    · exact layer_model_10 j
    · exact layer_model_11 j
    · exact layer_model_12 j
    · exact layer_model_13 j
    · exact layer_model_14 j
    · exact layer_model_15 j
    · exact layer_model_16 j
    · exact layer_model_17 j
    · exact layer_model_18 j
    · exact layer_model_19 j
    · exact layer_model_20 j
    · exact layer_model_21 j
    · exact layer_model_22 j
    · exact layer_model_23 j
    · exact layer_model_24 j
    · exact layer_model_25 j
    · exact layer_model_26 j

theorem real_symm (c : Cut) : ∀ i j, R c i j = R c j i := by
  cases c <;> decide +kernel

theorem imag_skew (c : Cut) : ∀ i j, I c i j = -I c j i := by
  cases c <;> decide +kernel

def residualR (c : Cut) (i j : Fin (size c)) : ℤ :=
  scale * R c i j - gramReal (BR c) (BI c) i j

def residualI (c : Cut) (i j : Fin (size c)) : ℤ :=
  scale * I c i j - gramImag (BR c) (BI c) i j

theorem residualR_symm (c : Cut) (i j : Fin (size c)) :
    residualR c i j = residualR c j i := by
  unfold residualR
  rw [real_symm c i j]
  congr 1
  unfold gramReal
  apply sum_congr rfl
  intro k _
  ring

theorem residualI_skew (c : Cut) (i j : Fin (size c)) :
    residualI c i j = -residualI c j i := by
  have hg : gramImag (BR c) (BI c) i j = -gramImag (BR c) (BI c) j i := by
    unfold gramImag
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro k _
    ring
  unfold residualI
  rw [imag_skew c i j, hg]
  ring

theorem chamber_residual_00 :
    (∑ j, (|(if (0 : Fin (size .chamber)) = j then shift else 0) -
      residualR .chamber 0 j| + |residualI .chamber 0 j|)) ≤ shift := by
  decide +kernel

theorem chamber_residual_01 :
    (∑ j, (|(if (1 : Fin (size .chamber)) = j then shift else 0) -
      residualR .chamber 1 j| + |residualI .chamber 1 j|)) ≤ shift := by
  decide +kernel

theorem chamber_residual_02 :
    (∑ j, (|(if (2 : Fin (size .chamber)) = j then shift else 0) -
      residualR .chamber 2 j| + |residualI .chamber 2 j|)) ≤ shift := by
  decide +kernel

theorem chamber_residual_03 :
    (∑ j, (|(if (3 : Fin (size .chamber)) = j then shift else 0) -
      residualR .chamber 3 j| + |residualI .chamber 3 j|)) ≤ shift := by
  decide +kernel

theorem chamber_residual_04 :
    (∑ j, (|(if (4 : Fin (size .chamber)) = j then shift else 0) -
      residualR .chamber 4 j| + |residualI .chamber 4 j|)) ≤ shift := by
  decide +kernel

theorem chamber_residual_05 :
    (∑ j, (|(if (5 : Fin (size .chamber)) = j then shift else 0) -
      residualR .chamber 5 j| + |residualI .chamber 5 j|)) ≤ shift := by
  decide +kernel

theorem chamber_residual_06 :
    (∑ j, (|(if (6 : Fin (size .chamber)) = j then shift else 0) -
      residualR .chamber 6 j| + |residualI .chamber 6 j|)) ≤ shift := by
  decide +kernel

theorem chamber_residual_07 :
    (∑ j, (|(if (7 : Fin (size .chamber)) = j then shift else 0) -
      residualR .chamber 7 j| + |residualI .chamber 7 j|)) ≤ shift := by
  decide +kernel

theorem chamber_residual_08 :
    (∑ j, (|(if (8 : Fin (size .chamber)) = j then shift else 0) -
      residualR .chamber 8 j| + |residualI .chamber 8 j|)) ≤ shift := by
  decide +kernel

theorem chamber_residual_09 :
    (∑ j, (|(if (9 : Fin (size .chamber)) = j then shift else 0) -
      residualR .chamber 9 j| + |residualI .chamber 9 j|)) ≤ shift := by
  decide +kernel

theorem chamber_residual_10 :
    (∑ j, (|(if (10 : Fin (size .chamber)) = j then shift else 0) -
      residualR .chamber 10 j| + |residualI .chamber 10 j|)) ≤ shift := by
  decide +kernel

theorem chamber_residual_11 :
    (∑ j, (|(if (11 : Fin (size .chamber)) = j then shift else 0) -
      residualR .chamber 11 j| + |residualI .chamber 11 j|)) ≤ shift := by
  decide +kernel

theorem chamber_residual_12 :
    (∑ j, (|(if (12 : Fin (size .chamber)) = j then shift else 0) -
      residualR .chamber 12 j| + |residualI .chamber 12 j|)) ≤ shift := by
  decide +kernel

theorem chamber_residual_13 :
    (∑ j, (|(if (13 : Fin (size .chamber)) = j then shift else 0) -
      residualR .chamber 13 j| + |residualI .chamber 13 j|)) ≤ shift := by
  decide +kernel

theorem chamber_residual_14 :
    (∑ j, (|(if (14 : Fin (size .chamber)) = j then shift else 0) -
      residualR .chamber 14 j| + |residualI .chamber 14 j|)) ≤ shift := by
  decide +kernel

theorem chamber_residual_15 :
    (∑ j, (|(if (15 : Fin (size .chamber)) = j then shift else 0) -
      residualR .chamber 15 j| + |residualI .chamber 15 j|)) ≤ shift := by
  decide +kernel

theorem chamber_residual_16 :
    (∑ j, (|(if (16 : Fin (size .chamber)) = j then shift else 0) -
      residualR .chamber 16 j| + |residualI .chamber 16 j|)) ≤ shift := by
  decide +kernel

theorem chamber_residual_17 :
    (∑ j, (|(if (17 : Fin (size .chamber)) = j then shift else 0) -
      residualR .chamber 17 j| + |residualI .chamber 17 j|)) ≤ shift := by
  decide +kernel

theorem chamber_residual_18 :
    (∑ j, (|(if (18 : Fin (size .chamber)) = j then shift else 0) -
      residualR .chamber 18 j| + |residualI .chamber 18 j|)) ≤ shift := by
  decide +kernel

theorem chamber_residual_19 :
    (∑ j, (|(if (19 : Fin (size .chamber)) = j then shift else 0) -
      residualR .chamber 19 j| + |residualI .chamber 19 j|)) ≤ shift := by
  decide +kernel

theorem chamber_residual_20 :
    (∑ j, (|(if (20 : Fin (size .chamber)) = j then shift else 0) -
      residualR .chamber 20 j| + |residualI .chamber 20 j|)) ≤ shift := by
  decide +kernel

theorem chamber_residual_21 :
    (∑ j, (|(if (21 : Fin (size .chamber)) = j then shift else 0) -
      residualR .chamber 21 j| + |residualI .chamber 21 j|)) ≤ shift := by
  decide +kernel

theorem chamber_residual_22 :
    (∑ j, (|(if (22 : Fin (size .chamber)) = j then shift else 0) -
      residualR .chamber 22 j| + |residualI .chamber 22 j|)) ≤ shift := by
  decide +kernel

theorem chamber_residual_23 :
    (∑ j, (|(if (23 : Fin (size .chamber)) = j then shift else 0) -
      residualR .chamber 23 j| + |residualI .chamber 23 j|)) ≤ shift := by
  decide +kernel

theorem chamber_residual_24 :
    (∑ j, (|(if (24 : Fin (size .chamber)) = j then shift else 0) -
      residualR .chamber 24 j| + |residualI .chamber 24 j|)) ≤ shift := by
  decide +kernel

theorem chamber_residual_25 :
    (∑ j, (|(if (25 : Fin (size .chamber)) = j then shift else 0) -
      residualR .chamber 25 j| + |residualI .chamber 25 j|)) ≤ shift := by
  decide +kernel

theorem chamber_residual_26 :
    (∑ j, (|(if (26 : Fin (size .chamber)) = j then shift else 0) -
      residualR .chamber 26 j| + |residualI .chamber 26 j|)) ≤ shift := by
  decide +kernel

theorem chamber_residual_27 :
    (∑ j, (|(if (27 : Fin (size .chamber)) = j then shift else 0) -
      residualR .chamber 27 j| + |residualI .chamber 27 j|)) ≤ shift := by
  decide +kernel

theorem layer_residual_00 :
    (∑ j, (|(if (0 : Fin (size .layer)) = j then shift else 0) -
      residualR .layer 0 j| + |residualI .layer 0 j|)) ≤ shift := by
  decide +kernel

theorem layer_residual_01 :
    (∑ j, (|(if (1 : Fin (size .layer)) = j then shift else 0) -
      residualR .layer 1 j| + |residualI .layer 1 j|)) ≤ shift := by
  decide +kernel

theorem layer_residual_02 :
    (∑ j, (|(if (2 : Fin (size .layer)) = j then shift else 0) -
      residualR .layer 2 j| + |residualI .layer 2 j|)) ≤ shift := by
  decide +kernel

theorem layer_residual_03 :
    (∑ j, (|(if (3 : Fin (size .layer)) = j then shift else 0) -
      residualR .layer 3 j| + |residualI .layer 3 j|)) ≤ shift := by
  decide +kernel

theorem layer_residual_04 :
    (∑ j, (|(if (4 : Fin (size .layer)) = j then shift else 0) -
      residualR .layer 4 j| + |residualI .layer 4 j|)) ≤ shift := by
  decide +kernel

theorem layer_residual_05 :
    (∑ j, (|(if (5 : Fin (size .layer)) = j then shift else 0) -
      residualR .layer 5 j| + |residualI .layer 5 j|)) ≤ shift := by
  decide +kernel

theorem layer_residual_06 :
    (∑ j, (|(if (6 : Fin (size .layer)) = j then shift else 0) -
      residualR .layer 6 j| + |residualI .layer 6 j|)) ≤ shift := by
  decide +kernel

theorem layer_residual_07 :
    (∑ j, (|(if (7 : Fin (size .layer)) = j then shift else 0) -
      residualR .layer 7 j| + |residualI .layer 7 j|)) ≤ shift := by
  decide +kernel

theorem layer_residual_08 :
    (∑ j, (|(if (8 : Fin (size .layer)) = j then shift else 0) -
      residualR .layer 8 j| + |residualI .layer 8 j|)) ≤ shift := by
  decide +kernel

theorem layer_residual_09 :
    (∑ j, (|(if (9 : Fin (size .layer)) = j then shift else 0) -
      residualR .layer 9 j| + |residualI .layer 9 j|)) ≤ shift := by
  decide +kernel

theorem layer_residual_10 :
    (∑ j, (|(if (10 : Fin (size .layer)) = j then shift else 0) -
      residualR .layer 10 j| + |residualI .layer 10 j|)) ≤ shift := by
  decide +kernel

theorem layer_residual_11 :
    (∑ j, (|(if (11 : Fin (size .layer)) = j then shift else 0) -
      residualR .layer 11 j| + |residualI .layer 11 j|)) ≤ shift := by
  decide +kernel

theorem layer_residual_12 :
    (∑ j, (|(if (12 : Fin (size .layer)) = j then shift else 0) -
      residualR .layer 12 j| + |residualI .layer 12 j|)) ≤ shift := by
  decide +kernel

theorem layer_residual_13 :
    (∑ j, (|(if (13 : Fin (size .layer)) = j then shift else 0) -
      residualR .layer 13 j| + |residualI .layer 13 j|)) ≤ shift := by
  decide +kernel

theorem layer_residual_14 :
    (∑ j, (|(if (14 : Fin (size .layer)) = j then shift else 0) -
      residualR .layer 14 j| + |residualI .layer 14 j|)) ≤ shift := by
  decide +kernel

theorem layer_residual_15 :
    (∑ j, (|(if (15 : Fin (size .layer)) = j then shift else 0) -
      residualR .layer 15 j| + |residualI .layer 15 j|)) ≤ shift := by
  decide +kernel

theorem layer_residual_16 :
    (∑ j, (|(if (16 : Fin (size .layer)) = j then shift else 0) -
      residualR .layer 16 j| + |residualI .layer 16 j|)) ≤ shift := by
  decide +kernel

theorem layer_residual_17 :
    (∑ j, (|(if (17 : Fin (size .layer)) = j then shift else 0) -
      residualR .layer 17 j| + |residualI .layer 17 j|)) ≤ shift := by
  decide +kernel

theorem layer_residual_18 :
    (∑ j, (|(if (18 : Fin (size .layer)) = j then shift else 0) -
      residualR .layer 18 j| + |residualI .layer 18 j|)) ≤ shift := by
  decide +kernel

theorem layer_residual_19 :
    (∑ j, (|(if (19 : Fin (size .layer)) = j then shift else 0) -
      residualR .layer 19 j| + |residualI .layer 19 j|)) ≤ shift := by
  decide +kernel

theorem layer_residual_20 :
    (∑ j, (|(if (20 : Fin (size .layer)) = j then shift else 0) -
      residualR .layer 20 j| + |residualI .layer 20 j|)) ≤ shift := by
  decide +kernel

theorem layer_residual_21 :
    (∑ j, (|(if (21 : Fin (size .layer)) = j then shift else 0) -
      residualR .layer 21 j| + |residualI .layer 21 j|)) ≤ shift := by
  decide +kernel

theorem layer_residual_22 :
    (∑ j, (|(if (22 : Fin (size .layer)) = j then shift else 0) -
      residualR .layer 22 j| + |residualI .layer 22 j|)) ≤ shift := by
  decide +kernel

theorem layer_residual_23 :
    (∑ j, (|(if (23 : Fin (size .layer)) = j then shift else 0) -
      residualR .layer 23 j| + |residualI .layer 23 j|)) ≤ shift := by
  decide +kernel

theorem layer_residual_24 :
    (∑ j, (|(if (24 : Fin (size .layer)) = j then shift else 0) -
      residualR .layer 24 j| + |residualI .layer 24 j|)) ≤ shift := by
  decide +kernel

theorem layer_residual_25 :
    (∑ j, (|(if (25 : Fin (size .layer)) = j then shift else 0) -
      residualR .layer 25 j| + |residualI .layer 25 j|)) ≤ shift := by
  decide +kernel

theorem layer_residual_26 :
    (∑ j, (|(if (26 : Fin (size .layer)) = j then shift else 0) -
      residualR .layer 26 j| + |residualI .layer 26 j|)) ≤ shift := by
  decide +kernel

theorem residual_rows (c : Cut) (i : Fin (size c)) :
    (∑ j, (|(if i = j then shift else 0) - residualR c i j| +
      |residualI c i j|)) ≤ shift := by
  cases c with
  | chamber =>
    fin_cases i
    · exact chamber_residual_00
    · exact chamber_residual_01
    · exact chamber_residual_02
    · exact chamber_residual_03
    · exact chamber_residual_04
    · exact chamber_residual_05
    · exact chamber_residual_06
    · exact chamber_residual_07
    · exact chamber_residual_08
    · exact chamber_residual_09
    · exact chamber_residual_10
    · exact chamber_residual_11
    · exact chamber_residual_12
    · exact chamber_residual_13
    · exact chamber_residual_14
    · exact chamber_residual_15
    · exact chamber_residual_16
    · exact chamber_residual_17
    · exact chamber_residual_18
    · exact chamber_residual_19
    · exact chamber_residual_20
    · exact chamber_residual_21
    · exact chamber_residual_22
    · exact chamber_residual_23
    · exact chamber_residual_24
    · exact chamber_residual_25
    · exact chamber_residual_26
    · exact chamber_residual_27
  | layer =>
    fin_cases i
    · exact layer_residual_00
    · exact layer_residual_01
    · exact layer_residual_02
    · exact layer_residual_03
    · exact layer_residual_04
    · exact layer_residual_05
    · exact layer_residual_06
    · exact layer_residual_07
    · exact layer_residual_08
    · exact layer_residual_09
    · exact layer_residual_10
    · exact layer_residual_11
    · exact layer_residual_12
    · exact layer_residual_13
    · exact layer_residual_14
    · exact layer_residual_15
    · exact layer_residual_16
    · exact layer_residual_17
    · exact layer_residual_18
    · exact layer_residual_19
    · exact layer_residual_20
    · exact layer_residual_21
    · exact layer_residual_22
    · exact layer_residual_23
    · exact layer_residual_24
    · exact layer_residual_25
    · exact layer_residual_26

theorem checked_matrix_nonneg (c : Cut) (x : Fin (size c) → ℂ) :
    0 ≤ (qform (fun i j => gaussian (modelReal c i j) (modelImag c i j)) x).re := by
  have h := qform_nonneg_of_gaussian_factor (R c) (I c) (BR c) (BI c)
    scale shift (by norm_num [scale]) (residualR_symm c) (residualI_skew c)
    (residual_rows c) x
  simpa only [(model_checks _ _ _).1, (model_checks _ _ _).2] using h

end Sarkozy.PositiveRoots.CoherentEndpoint
