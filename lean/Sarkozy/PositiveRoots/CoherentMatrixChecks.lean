module

public import Sarkozy.PositiveRoots.CoherentMatrixData
public import Sarkozy.SpectralD.SmallFast.Residuals

/-!
# Integer checks for the selected coherent chamber matrix

The table is identified with the actual graph and dictionary before checking
the Gram factor and its diagonally dominant residual.
-/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentMatrix

open Finset Sarkozy.SpectralD Sarkozy.SpectralC

def entry (T : List (List ℤ)) (i j : Fin 64) : ℤ := (T.getD i.val []).getD j.val 0

def R := entry realTable
def I := entry imagTable
def BR := entry factorRealTable
def BI := entry factorImagTable

theorem model_row_00 : ∀ j, R 0 j = modelReal 0 j ∧ I 0 j = modelImag 0 j := by
  decide +kernel

theorem model_row_01 : ∀ j, R 1 j = modelReal 1 j ∧ I 1 j = modelImag 1 j := by
  decide +kernel

theorem model_row_02 : ∀ j, R 2 j = modelReal 2 j ∧ I 2 j = modelImag 2 j := by
  decide +kernel

theorem model_row_03 : ∀ j, R 3 j = modelReal 3 j ∧ I 3 j = modelImag 3 j := by
  decide +kernel

theorem model_row_04 : ∀ j, R 4 j = modelReal 4 j ∧ I 4 j = modelImag 4 j := by
  decide +kernel

theorem model_row_05 : ∀ j, R 5 j = modelReal 5 j ∧ I 5 j = modelImag 5 j := by
  decide +kernel

theorem model_row_06 : ∀ j, R 6 j = modelReal 6 j ∧ I 6 j = modelImag 6 j := by
  decide +kernel

theorem model_row_07 : ∀ j, R 7 j = modelReal 7 j ∧ I 7 j = modelImag 7 j := by
  decide +kernel

theorem model_row_08 : ∀ j, R 8 j = modelReal 8 j ∧ I 8 j = modelImag 8 j := by
  decide +kernel

theorem model_row_09 : ∀ j, R 9 j = modelReal 9 j ∧ I 9 j = modelImag 9 j := by
  decide +kernel

theorem model_row_10 : ∀ j, R 10 j = modelReal 10 j ∧ I 10 j = modelImag 10 j := by
  decide +kernel

theorem model_row_11 : ∀ j, R 11 j = modelReal 11 j ∧ I 11 j = modelImag 11 j := by
  decide +kernel

theorem model_row_12 : ∀ j, R 12 j = modelReal 12 j ∧ I 12 j = modelImag 12 j := by
  decide +kernel

theorem model_row_13 : ∀ j, R 13 j = modelReal 13 j ∧ I 13 j = modelImag 13 j := by
  decide +kernel

theorem model_row_14 : ∀ j, R 14 j = modelReal 14 j ∧ I 14 j = modelImag 14 j := by
  decide +kernel

theorem model_row_15 : ∀ j, R 15 j = modelReal 15 j ∧ I 15 j = modelImag 15 j := by
  decide +kernel

theorem model_row_16 : ∀ j, R 16 j = modelReal 16 j ∧ I 16 j = modelImag 16 j := by
  decide +kernel

theorem model_row_17 : ∀ j, R 17 j = modelReal 17 j ∧ I 17 j = modelImag 17 j := by
  decide +kernel

theorem model_row_18 : ∀ j, R 18 j = modelReal 18 j ∧ I 18 j = modelImag 18 j := by
  decide +kernel

theorem model_row_19 : ∀ j, R 19 j = modelReal 19 j ∧ I 19 j = modelImag 19 j := by
  decide +kernel

theorem model_row_20 : ∀ j, R 20 j = modelReal 20 j ∧ I 20 j = modelImag 20 j := by
  decide +kernel

theorem model_row_21 : ∀ j, R 21 j = modelReal 21 j ∧ I 21 j = modelImag 21 j := by
  decide +kernel

theorem model_row_22 : ∀ j, R 22 j = modelReal 22 j ∧ I 22 j = modelImag 22 j := by
  decide +kernel

theorem model_row_23 : ∀ j, R 23 j = modelReal 23 j ∧ I 23 j = modelImag 23 j := by
  decide +kernel

theorem model_row_24 : ∀ j, R 24 j = modelReal 24 j ∧ I 24 j = modelImag 24 j := by
  decide +kernel

theorem model_row_25 : ∀ j, R 25 j = modelReal 25 j ∧ I 25 j = modelImag 25 j := by
  decide +kernel

theorem model_row_26 : ∀ j, R 26 j = modelReal 26 j ∧ I 26 j = modelImag 26 j := by
  decide +kernel

theorem model_row_27 : ∀ j, R 27 j = modelReal 27 j ∧ I 27 j = modelImag 27 j := by
  decide +kernel

theorem model_row_28 : ∀ j, R 28 j = modelReal 28 j ∧ I 28 j = modelImag 28 j := by
  decide +kernel

theorem model_row_29 : ∀ j, R 29 j = modelReal 29 j ∧ I 29 j = modelImag 29 j := by
  decide +kernel

theorem model_row_30 : ∀ j, R 30 j = modelReal 30 j ∧ I 30 j = modelImag 30 j := by
  decide +kernel

theorem model_row_31 : ∀ j, R 31 j = modelReal 31 j ∧ I 31 j = modelImag 31 j := by
  decide +kernel

theorem model_row_32 : ∀ j, R 32 j = modelReal 32 j ∧ I 32 j = modelImag 32 j := by
  decide +kernel

theorem model_row_33 : ∀ j, R 33 j = modelReal 33 j ∧ I 33 j = modelImag 33 j := by
  decide +kernel

theorem model_row_34 : ∀ j, R 34 j = modelReal 34 j ∧ I 34 j = modelImag 34 j := by
  decide +kernel

theorem model_row_35 : ∀ j, R 35 j = modelReal 35 j ∧ I 35 j = modelImag 35 j := by
  decide +kernel

theorem model_row_36 : ∀ j, R 36 j = modelReal 36 j ∧ I 36 j = modelImag 36 j := by
  decide +kernel

theorem model_row_37 : ∀ j, R 37 j = modelReal 37 j ∧ I 37 j = modelImag 37 j := by
  decide +kernel

theorem model_row_38 : ∀ j, R 38 j = modelReal 38 j ∧ I 38 j = modelImag 38 j := by
  decide +kernel

theorem model_row_39 : ∀ j, R 39 j = modelReal 39 j ∧ I 39 j = modelImag 39 j := by
  decide +kernel

theorem model_row_40 : ∀ j, R 40 j = modelReal 40 j ∧ I 40 j = modelImag 40 j := by
  decide +kernel

theorem model_row_41 : ∀ j, R 41 j = modelReal 41 j ∧ I 41 j = modelImag 41 j := by
  decide +kernel

theorem model_row_42 : ∀ j, R 42 j = modelReal 42 j ∧ I 42 j = modelImag 42 j := by
  decide +kernel

theorem model_row_43 : ∀ j, R 43 j = modelReal 43 j ∧ I 43 j = modelImag 43 j := by
  decide +kernel

theorem model_row_44 : ∀ j, R 44 j = modelReal 44 j ∧ I 44 j = modelImag 44 j := by
  decide +kernel

theorem model_row_45 : ∀ j, R 45 j = modelReal 45 j ∧ I 45 j = modelImag 45 j := by
  decide +kernel

theorem model_row_46 : ∀ j, R 46 j = modelReal 46 j ∧ I 46 j = modelImag 46 j := by
  decide +kernel

theorem model_row_47 : ∀ j, R 47 j = modelReal 47 j ∧ I 47 j = modelImag 47 j := by
  decide +kernel

theorem model_row_48 : ∀ j, R 48 j = modelReal 48 j ∧ I 48 j = modelImag 48 j := by
  decide +kernel

theorem model_row_49 : ∀ j, R 49 j = modelReal 49 j ∧ I 49 j = modelImag 49 j := by
  decide +kernel

theorem model_row_50 : ∀ j, R 50 j = modelReal 50 j ∧ I 50 j = modelImag 50 j := by
  decide +kernel

theorem model_row_51 : ∀ j, R 51 j = modelReal 51 j ∧ I 51 j = modelImag 51 j := by
  decide +kernel

theorem model_row_52 : ∀ j, R 52 j = modelReal 52 j ∧ I 52 j = modelImag 52 j := by
  decide +kernel

theorem model_row_53 : ∀ j, R 53 j = modelReal 53 j ∧ I 53 j = modelImag 53 j := by
  decide +kernel

theorem model_row_54 : ∀ j, R 54 j = modelReal 54 j ∧ I 54 j = modelImag 54 j := by
  decide +kernel

theorem model_row_55 : ∀ j, R 55 j = modelReal 55 j ∧ I 55 j = modelImag 55 j := by
  decide +kernel

theorem model_row_56 : ∀ j, R 56 j = modelReal 56 j ∧ I 56 j = modelImag 56 j := by
  decide +kernel

theorem model_row_57 : ∀ j, R 57 j = modelReal 57 j ∧ I 57 j = modelImag 57 j := by
  decide +kernel

theorem model_row_58 : ∀ j, R 58 j = modelReal 58 j ∧ I 58 j = modelImag 58 j := by
  decide +kernel

theorem model_row_59 : ∀ j, R 59 j = modelReal 59 j ∧ I 59 j = modelImag 59 j := by
  decide +kernel

theorem model_row_60 : ∀ j, R 60 j = modelReal 60 j ∧ I 60 j = modelImag 60 j := by
  decide +kernel

theorem model_row_61 : ∀ j, R 61 j = modelReal 61 j ∧ I 61 j = modelImag 61 j := by
  decide +kernel

theorem model_row_62 : ∀ j, R 62 j = modelReal 62 j ∧ I 62 j = modelImag 62 j := by
  decide +kernel

theorem model_row_63 : ∀ j, R 63 j = modelReal 63 j ∧ I 63 j = modelImag 63 j := by
  decide +kernel

theorem model_checks (i j : Fin 64) : R i j = modelReal i j ∧ I i j = modelImag i j := by
  fin_cases i
  · exact model_row_00 j
  · exact model_row_01 j
  · exact model_row_02 j
  · exact model_row_03 j
  · exact model_row_04 j
  · exact model_row_05 j
  · exact model_row_06 j
  · exact model_row_07 j
  · exact model_row_08 j
  · exact model_row_09 j
  · exact model_row_10 j
  · exact model_row_11 j
  · exact model_row_12 j
  · exact model_row_13 j
  · exact model_row_14 j
  · exact model_row_15 j
  · exact model_row_16 j
  · exact model_row_17 j
  · exact model_row_18 j
  · exact model_row_19 j
  · exact model_row_20 j
  · exact model_row_21 j
  · exact model_row_22 j
  · exact model_row_23 j
  · exact model_row_24 j
  · exact model_row_25 j
  · exact model_row_26 j
  · exact model_row_27 j
  · exact model_row_28 j
  · exact model_row_29 j
  · exact model_row_30 j
  · exact model_row_31 j
  · exact model_row_32 j
  · exact model_row_33 j
  · exact model_row_34 j
  · exact model_row_35 j
  · exact model_row_36 j
  · exact model_row_37 j
  · exact model_row_38 j
  · exact model_row_39 j
  · exact model_row_40 j
  · exact model_row_41 j
  · exact model_row_42 j
  · exact model_row_43 j
  · exact model_row_44 j
  · exact model_row_45 j
  · exact model_row_46 j
  · exact model_row_47 j
  · exact model_row_48 j
  · exact model_row_49 j
  · exact model_row_50 j
  · exact model_row_51 j
  · exact model_row_52 j
  · exact model_row_53 j
  · exact model_row_54 j
  · exact model_row_55 j
  · exact model_row_56 j
  · exact model_row_57 j
  · exact model_row_58 j
  · exact model_row_59 j
  · exact model_row_60 j
  · exact model_row_61 j
  · exact model_row_62 j
  · exact model_row_63 j

theorem real_symm : ∀ i j, R i j = R j i := by decide +kernel

theorem imag_skew : ∀ i j, I i j = -I j i := by decide +kernel

def residualR (i j : Fin 64) : ℤ := scale * R i j - gramReal BR BI i j
def residualI (i j : Fin 64) : ℤ := scale * I i j - gramImag BR BI i j

theorem residualR_symm (i j : Fin 64) : residualR i j = residualR j i := by
  unfold residualR
  rw [real_symm i j]
  congr 1
  unfold gramReal
  apply sum_congr rfl
  intro k _
  ring

theorem residualI_skew (i j : Fin 64) : residualI i j = -residualI j i := by
  have hg : gramImag BR BI i j = -gramImag BR BI j i := by
    unfold gramImag
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro k _
    ring
  unfold residualI
  rw [imag_skew i j, hg]
  ring

/-! ### The residual rows on codes

Each residual entry recomputes a Gram sum over `Fin 64`. The row checks below use the
column dot products of `SpectralD.SmallFast.Residuals` instead (`residualR_code`,
`residualI_code`, `residual_row_of`). -/

theorem factor_lengths : factorRealTable.length = 64 ∧ factorImagTable.length = 64 := by
  decide +kernel

theorem factor_tri : ∀ k, k < 64 → ∀ x, x < k →
    SmallMatrices.entry factorRealTable k x = 0 ∧ SmallMatrices.entry factorImagTable k x = 0 := by
  decide +kernel

theorem gram_fin_dot (T₁ T₂ : List (List ℤ)) (h₁ : T₁.length = 64)
    (hz₁ : ∀ k, k < 64 → ∀ x, x < k → SmallMatrices.entry T₁ k x = 0)
    (hz₂ : ∀ k, k < 64 → ∀ x, x < k → SmallMatrices.entry T₂ k x = 0) (i j : Fin 64) :
    ∑ k : Fin 64, entry T₁ k i * entry T₂ k j =
      SmallMatrices.dotZ (SmallMatrices.colUpTo T₁ i.val) (SmallMatrices.colUpTo T₂ j.val) := by
  have hl : (SmallMatrices.colUpTo T₁ i.val).length ≤ 64 := by
    rw [SmallMatrices.colUpTo, SmallMatrices.length_colOf, List.length_take, h₁]
    exact Nat.min_le_right _ _
  rw [SmallMatrices.dotZ_eq_sum _ _ 64 hl]
  have ht : ∀ (T : List (List ℤ)) z k, k < 64 →
      (∀ k, k < 64 → ∀ x, x < k → SmallMatrices.entry T k x = 0) →
      (SmallMatrices.colUpTo T z).getD k 0 = SmallMatrices.entry T k z := by
    intro T z k hk hz
    rw [SmallMatrices.colUpTo, SmallMatrices.getD_colOf, SmallMatrices.entry_take]
    split_ifs with hkz
    · rfl
    · exact (hz k hk z (by omega)).symm
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [ht T₁ i.val k.val k.isLt hz₁, ht T₂ j.val k.val k.isLt hz₂]
  rfl

/-- The real residual entry at the codes `x`, `y`. -/
def resRCode (x y : ℕ) : ℤ :=
  scale * SmallMatrices.entry realTable x y -
    (SmallMatrices.dotZ (SmallMatrices.colUpTo factorRealTable x)
        (SmallMatrices.colUpTo factorRealTable y) +
      SmallMatrices.dotZ (SmallMatrices.colUpTo factorImagTable x)
        (SmallMatrices.colUpTo factorImagTable y))

/-- The imaginary residual entry at the codes `x`, `y`. -/
def resICode (x y : ℕ) : ℤ :=
  scale * SmallMatrices.entry imagTable x y -
    (SmallMatrices.dotZ (SmallMatrices.colUpTo factorRealTable x)
        (SmallMatrices.colUpTo factorImagTable y) -
      SmallMatrices.dotZ (SmallMatrices.colUpTo factorImagTable x)
        (SmallMatrices.colUpTo factorRealTable y))

/-- The term of a residual row sum at the codes `x`, `y`. -/
def rowTermCode (x y : ℕ) : ℤ :=
  ((((if x = y then shift else 0) - resRCode x y).natAbs : ℕ) : ℤ) +
    ((resICode x y).natAbs : ℤ)

theorem residualR_code (i j : Fin 64) : residualR i j = resRCode i.val j.val := by
  unfold residualR gramReal resRCode BR BI
  rw [Finset.sum_add_distrib,
    gram_fin_dot _ _ factor_lengths.1 (fun k hk x hx => (factor_tri k hk x hx).1)
      (fun k hk x hx => (factor_tri k hk x hx).1),
    gram_fin_dot _ _ factor_lengths.2 (fun k hk x hx => (factor_tri k hk x hx).2)
      (fun k hk x hx => (factor_tri k hk x hx).2)]
  rfl

theorem residualI_code (i j : Fin 64) : residualI i j = resICode i.val j.val := by
  unfold residualI gramImag resICode BR BI
  rw [Finset.sum_sub_distrib,
    gram_fin_dot _ _ factor_lengths.1 (fun k hk x hx => (factor_tri k hk x hx).1)
      (fun k hk x hx => (factor_tri k hk x hx).2),
    gram_fin_dot _ _ factor_lengths.2 (fun k hk x hx => (factor_tri k hk x hx).2)
      (fun k hk x hx => (factor_tri k hk x hx).1)]
  rfl

theorem residual_row_of (i : Fin 64) (h : ∑ y ∈ range 64, rowTermCode i.val y ≤ shift) :
    (∑ j, (|(if i = j then shift else 0) - residualR i j| + |residualI i j|)) ≤ shift := by
  have hterm : ∀ j : Fin 64, |(if i = j then shift else 0) - residualR i j| +
      |residualI i j| = rowTermCode i.val j.val := by
    intro j
    rw [residualR_code, residualI_code, rowTermCode, Int.abs_eq_natAbs, Int.abs_eq_natAbs]
    by_cases hij : i = j
    · subst hij
      simp
    · have h2 : i.val ≠ j.val := fun h' => hij (Fin.ext h')
      simp only [hij, h2, ite_false]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  rw [Fin.sum_univ_eq_sum_range (fun y => rowTermCode i.val y) 64]
  exact h

theorem residual_row_00 :
    (∑ j, (|(if (0 : Fin 64) = j then shift else 0) - residualR 0 j| +
      |residualI 0 j|)) ≤ shift :=
  residual_row_of 0 (by decide +kernel)

theorem residual_row_01 :
    (∑ j, (|(if (1 : Fin 64) = j then shift else 0) - residualR 1 j| +
      |residualI 1 j|)) ≤ shift :=
  residual_row_of 1 (by decide +kernel)

theorem residual_row_02 :
    (∑ j, (|(if (2 : Fin 64) = j then shift else 0) - residualR 2 j| +
      |residualI 2 j|)) ≤ shift :=
  residual_row_of 2 (by decide +kernel)

theorem residual_row_03 :
    (∑ j, (|(if (3 : Fin 64) = j then shift else 0) - residualR 3 j| +
      |residualI 3 j|)) ≤ shift :=
  residual_row_of 3 (by decide +kernel)

theorem residual_row_04 :
    (∑ j, (|(if (4 : Fin 64) = j then shift else 0) - residualR 4 j| +
      |residualI 4 j|)) ≤ shift :=
  residual_row_of 4 (by decide +kernel)

theorem residual_row_05 :
    (∑ j, (|(if (5 : Fin 64) = j then shift else 0) - residualR 5 j| +
      |residualI 5 j|)) ≤ shift :=
  residual_row_of 5 (by decide +kernel)

theorem residual_row_06 :
    (∑ j, (|(if (6 : Fin 64) = j then shift else 0) - residualR 6 j| +
      |residualI 6 j|)) ≤ shift :=
  residual_row_of 6 (by decide +kernel)

theorem residual_row_07 :
    (∑ j, (|(if (7 : Fin 64) = j then shift else 0) - residualR 7 j| +
      |residualI 7 j|)) ≤ shift :=
  residual_row_of 7 (by decide +kernel)

theorem residual_row_08 :
    (∑ j, (|(if (8 : Fin 64) = j then shift else 0) - residualR 8 j| +
      |residualI 8 j|)) ≤ shift :=
  residual_row_of 8 (by decide +kernel)

theorem residual_row_09 :
    (∑ j, (|(if (9 : Fin 64) = j then shift else 0) - residualR 9 j| +
      |residualI 9 j|)) ≤ shift :=
  residual_row_of 9 (by decide +kernel)

theorem residual_row_10 :
    (∑ j, (|(if (10 : Fin 64) = j then shift else 0) - residualR 10 j| +
      |residualI 10 j|)) ≤ shift :=
  residual_row_of 10 (by decide +kernel)

theorem residual_row_11 :
    (∑ j, (|(if (11 : Fin 64) = j then shift else 0) - residualR 11 j| +
      |residualI 11 j|)) ≤ shift :=
  residual_row_of 11 (by decide +kernel)

theorem residual_row_12 :
    (∑ j, (|(if (12 : Fin 64) = j then shift else 0) - residualR 12 j| +
      |residualI 12 j|)) ≤ shift :=
  residual_row_of 12 (by decide +kernel)

theorem residual_row_13 :
    (∑ j, (|(if (13 : Fin 64) = j then shift else 0) - residualR 13 j| +
      |residualI 13 j|)) ≤ shift :=
  residual_row_of 13 (by decide +kernel)

theorem residual_row_14 :
    (∑ j, (|(if (14 : Fin 64) = j then shift else 0) - residualR 14 j| +
      |residualI 14 j|)) ≤ shift :=
  residual_row_of 14 (by decide +kernel)

theorem residual_row_15 :
    (∑ j, (|(if (15 : Fin 64) = j then shift else 0) - residualR 15 j| +
      |residualI 15 j|)) ≤ shift :=
  residual_row_of 15 (by decide +kernel)

theorem residual_row_16 :
    (∑ j, (|(if (16 : Fin 64) = j then shift else 0) - residualR 16 j| +
      |residualI 16 j|)) ≤ shift :=
  residual_row_of 16 (by decide +kernel)

theorem residual_row_17 :
    (∑ j, (|(if (17 : Fin 64) = j then shift else 0) - residualR 17 j| +
      |residualI 17 j|)) ≤ shift :=
  residual_row_of 17 (by decide +kernel)

theorem residual_row_18 :
    (∑ j, (|(if (18 : Fin 64) = j then shift else 0) - residualR 18 j| +
      |residualI 18 j|)) ≤ shift :=
  residual_row_of 18 (by decide +kernel)

theorem residual_row_19 :
    (∑ j, (|(if (19 : Fin 64) = j then shift else 0) - residualR 19 j| +
      |residualI 19 j|)) ≤ shift :=
  residual_row_of 19 (by decide +kernel)

theorem residual_row_20 :
    (∑ j, (|(if (20 : Fin 64) = j then shift else 0) - residualR 20 j| +
      |residualI 20 j|)) ≤ shift :=
  residual_row_of 20 (by decide +kernel)

theorem residual_row_21 :
    (∑ j, (|(if (21 : Fin 64) = j then shift else 0) - residualR 21 j| +
      |residualI 21 j|)) ≤ shift :=
  residual_row_of 21 (by decide +kernel)

theorem residual_row_22 :
    (∑ j, (|(if (22 : Fin 64) = j then shift else 0) - residualR 22 j| +
      |residualI 22 j|)) ≤ shift :=
  residual_row_of 22 (by decide +kernel)

theorem residual_row_23 :
    (∑ j, (|(if (23 : Fin 64) = j then shift else 0) - residualR 23 j| +
      |residualI 23 j|)) ≤ shift :=
  residual_row_of 23 (by decide +kernel)

theorem residual_row_24 :
    (∑ j, (|(if (24 : Fin 64) = j then shift else 0) - residualR 24 j| +
      |residualI 24 j|)) ≤ shift :=
  residual_row_of 24 (by decide +kernel)

theorem residual_row_25 :
    (∑ j, (|(if (25 : Fin 64) = j then shift else 0) - residualR 25 j| +
      |residualI 25 j|)) ≤ shift :=
  residual_row_of 25 (by decide +kernel)

theorem residual_row_26 :
    (∑ j, (|(if (26 : Fin 64) = j then shift else 0) - residualR 26 j| +
      |residualI 26 j|)) ≤ shift :=
  residual_row_of 26 (by decide +kernel)

theorem residual_row_27 :
    (∑ j, (|(if (27 : Fin 64) = j then shift else 0) - residualR 27 j| +
      |residualI 27 j|)) ≤ shift :=
  residual_row_of 27 (by decide +kernel)

theorem residual_row_28 :
    (∑ j, (|(if (28 : Fin 64) = j then shift else 0) - residualR 28 j| +
      |residualI 28 j|)) ≤ shift :=
  residual_row_of 28 (by decide +kernel)

theorem residual_row_29 :
    (∑ j, (|(if (29 : Fin 64) = j then shift else 0) - residualR 29 j| +
      |residualI 29 j|)) ≤ shift :=
  residual_row_of 29 (by decide +kernel)

theorem residual_row_30 :
    (∑ j, (|(if (30 : Fin 64) = j then shift else 0) - residualR 30 j| +
      |residualI 30 j|)) ≤ shift :=
  residual_row_of 30 (by decide +kernel)

theorem residual_row_31 :
    (∑ j, (|(if (31 : Fin 64) = j then shift else 0) - residualR 31 j| +
      |residualI 31 j|)) ≤ shift :=
  residual_row_of 31 (by decide +kernel)

theorem residual_row_32 :
    (∑ j, (|(if (32 : Fin 64) = j then shift else 0) - residualR 32 j| +
      |residualI 32 j|)) ≤ shift :=
  residual_row_of 32 (by decide +kernel)

theorem residual_row_33 :
    (∑ j, (|(if (33 : Fin 64) = j then shift else 0) - residualR 33 j| +
      |residualI 33 j|)) ≤ shift :=
  residual_row_of 33 (by decide +kernel)

theorem residual_row_34 :
    (∑ j, (|(if (34 : Fin 64) = j then shift else 0) - residualR 34 j| +
      |residualI 34 j|)) ≤ shift :=
  residual_row_of 34 (by decide +kernel)

theorem residual_row_35 :
    (∑ j, (|(if (35 : Fin 64) = j then shift else 0) - residualR 35 j| +
      |residualI 35 j|)) ≤ shift :=
  residual_row_of 35 (by decide +kernel)

theorem residual_row_36 :
    (∑ j, (|(if (36 : Fin 64) = j then shift else 0) - residualR 36 j| +
      |residualI 36 j|)) ≤ shift :=
  residual_row_of 36 (by decide +kernel)

theorem residual_row_37 :
    (∑ j, (|(if (37 : Fin 64) = j then shift else 0) - residualR 37 j| +
      |residualI 37 j|)) ≤ shift :=
  residual_row_of 37 (by decide +kernel)

theorem residual_row_38 :
    (∑ j, (|(if (38 : Fin 64) = j then shift else 0) - residualR 38 j| +
      |residualI 38 j|)) ≤ shift :=
  residual_row_of 38 (by decide +kernel)

theorem residual_row_39 :
    (∑ j, (|(if (39 : Fin 64) = j then shift else 0) - residualR 39 j| +
      |residualI 39 j|)) ≤ shift :=
  residual_row_of 39 (by decide +kernel)

theorem residual_row_40 :
    (∑ j, (|(if (40 : Fin 64) = j then shift else 0) - residualR 40 j| +
      |residualI 40 j|)) ≤ shift :=
  residual_row_of 40 (by decide +kernel)

theorem residual_row_41 :
    (∑ j, (|(if (41 : Fin 64) = j then shift else 0) - residualR 41 j| +
      |residualI 41 j|)) ≤ shift :=
  residual_row_of 41 (by decide +kernel)

theorem residual_row_42 :
    (∑ j, (|(if (42 : Fin 64) = j then shift else 0) - residualR 42 j| +
      |residualI 42 j|)) ≤ shift :=
  residual_row_of 42 (by decide +kernel)

theorem residual_row_43 :
    (∑ j, (|(if (43 : Fin 64) = j then shift else 0) - residualR 43 j| +
      |residualI 43 j|)) ≤ shift :=
  residual_row_of 43 (by decide +kernel)

theorem residual_row_44 :
    (∑ j, (|(if (44 : Fin 64) = j then shift else 0) - residualR 44 j| +
      |residualI 44 j|)) ≤ shift :=
  residual_row_of 44 (by decide +kernel)

theorem residual_row_45 :
    (∑ j, (|(if (45 : Fin 64) = j then shift else 0) - residualR 45 j| +
      |residualI 45 j|)) ≤ shift :=
  residual_row_of 45 (by decide +kernel)

theorem residual_row_46 :
    (∑ j, (|(if (46 : Fin 64) = j then shift else 0) - residualR 46 j| +
      |residualI 46 j|)) ≤ shift :=
  residual_row_of 46 (by decide +kernel)

theorem residual_row_47 :
    (∑ j, (|(if (47 : Fin 64) = j then shift else 0) - residualR 47 j| +
      |residualI 47 j|)) ≤ shift :=
  residual_row_of 47 (by decide +kernel)

theorem residual_row_48 :
    (∑ j, (|(if (48 : Fin 64) = j then shift else 0) - residualR 48 j| +
      |residualI 48 j|)) ≤ shift :=
  residual_row_of 48 (by decide +kernel)

theorem residual_row_49 :
    (∑ j, (|(if (49 : Fin 64) = j then shift else 0) - residualR 49 j| +
      |residualI 49 j|)) ≤ shift :=
  residual_row_of 49 (by decide +kernel)

theorem residual_row_50 :
    (∑ j, (|(if (50 : Fin 64) = j then shift else 0) - residualR 50 j| +
      |residualI 50 j|)) ≤ shift :=
  residual_row_of 50 (by decide +kernel)

theorem residual_row_51 :
    (∑ j, (|(if (51 : Fin 64) = j then shift else 0) - residualR 51 j| +
      |residualI 51 j|)) ≤ shift :=
  residual_row_of 51 (by decide +kernel)

theorem residual_row_52 :
    (∑ j, (|(if (52 : Fin 64) = j then shift else 0) - residualR 52 j| +
      |residualI 52 j|)) ≤ shift :=
  residual_row_of 52 (by decide +kernel)

theorem residual_row_53 :
    (∑ j, (|(if (53 : Fin 64) = j then shift else 0) - residualR 53 j| +
      |residualI 53 j|)) ≤ shift :=
  residual_row_of 53 (by decide +kernel)

theorem residual_row_54 :
    (∑ j, (|(if (54 : Fin 64) = j then shift else 0) - residualR 54 j| +
      |residualI 54 j|)) ≤ shift :=
  residual_row_of 54 (by decide +kernel)

theorem residual_row_55 :
    (∑ j, (|(if (55 : Fin 64) = j then shift else 0) - residualR 55 j| +
      |residualI 55 j|)) ≤ shift :=
  residual_row_of 55 (by decide +kernel)

theorem residual_row_56 :
    (∑ j, (|(if (56 : Fin 64) = j then shift else 0) - residualR 56 j| +
      |residualI 56 j|)) ≤ shift :=
  residual_row_of 56 (by decide +kernel)

theorem residual_row_57 :
    (∑ j, (|(if (57 : Fin 64) = j then shift else 0) - residualR 57 j| +
      |residualI 57 j|)) ≤ shift :=
  residual_row_of 57 (by decide +kernel)

theorem residual_row_58 :
    (∑ j, (|(if (58 : Fin 64) = j then shift else 0) - residualR 58 j| +
      |residualI 58 j|)) ≤ shift :=
  residual_row_of 58 (by decide +kernel)

theorem residual_row_59 :
    (∑ j, (|(if (59 : Fin 64) = j then shift else 0) - residualR 59 j| +
      |residualI 59 j|)) ≤ shift :=
  residual_row_of 59 (by decide +kernel)

theorem residual_row_60 :
    (∑ j, (|(if (60 : Fin 64) = j then shift else 0) - residualR 60 j| +
      |residualI 60 j|)) ≤ shift :=
  residual_row_of 60 (by decide +kernel)

theorem residual_row_61 :
    (∑ j, (|(if (61 : Fin 64) = j then shift else 0) - residualR 61 j| +
      |residualI 61 j|)) ≤ shift :=
  residual_row_of 61 (by decide +kernel)

theorem residual_row_62 :
    (∑ j, (|(if (62 : Fin 64) = j then shift else 0) - residualR 62 j| +
      |residualI 62 j|)) ≤ shift :=
  residual_row_of 62 (by decide +kernel)

theorem residual_row_63 :
    (∑ j, (|(if (63 : Fin 64) = j then shift else 0) - residualR 63 j| +
      |residualI 63 j|)) ≤ shift :=
  residual_row_of 63 (by decide +kernel)

theorem residual_rows (i : Fin 64) :
    (∑ j, (|(if i = j then shift else 0) - residualR i j| + |residualI i j|)) ≤ shift := by
  fin_cases i
  · exact residual_row_00
  · exact residual_row_01
  · exact residual_row_02
  · exact residual_row_03
  · exact residual_row_04
  · exact residual_row_05
  · exact residual_row_06
  · exact residual_row_07
  · exact residual_row_08
  · exact residual_row_09
  · exact residual_row_10
  · exact residual_row_11
  · exact residual_row_12
  · exact residual_row_13
  · exact residual_row_14
  · exact residual_row_15
  · exact residual_row_16
  · exact residual_row_17
  · exact residual_row_18
  · exact residual_row_19
  · exact residual_row_20
  · exact residual_row_21
  · exact residual_row_22
  · exact residual_row_23
  · exact residual_row_24
  · exact residual_row_25
  · exact residual_row_26
  · exact residual_row_27
  · exact residual_row_28
  · exact residual_row_29
  · exact residual_row_30
  · exact residual_row_31
  · exact residual_row_32
  · exact residual_row_33
  · exact residual_row_34
  · exact residual_row_35
  · exact residual_row_36
  · exact residual_row_37
  · exact residual_row_38
  · exact residual_row_39
  · exact residual_row_40
  · exact residual_row_41
  · exact residual_row_42
  · exact residual_row_43
  · exact residual_row_44
  · exact residual_row_45
  · exact residual_row_46
  · exact residual_row_47
  · exact residual_row_48
  · exact residual_row_49
  · exact residual_row_50
  · exact residual_row_51
  · exact residual_row_52
  · exact residual_row_53
  · exact residual_row_54
  · exact residual_row_55
  · exact residual_row_56
  · exact residual_row_57
  · exact residual_row_58
  · exact residual_row_59
  · exact residual_row_60
  · exact residual_row_61
  · exact residual_row_62
  · exact residual_row_63

theorem checked_matrix_nonneg (x : Fin 64 → ℂ) :
    0 ≤ (qform (fun i j => gaussian (modelReal i j) (modelImag i j)) x).re := by
  have h := qform_nonneg_of_gaussian_factor R I BR BI scale shift
    (by norm_num [scale]) residualR_symm residualI_skew residual_rows x
  simpa only [(model_checks _ _).1, (model_checks _ _).2] using h

end Sarkozy.PositiveRoots.CoherentMatrix
