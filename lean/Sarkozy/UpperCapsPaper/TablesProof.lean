module

public import Sarkozy.UpperCapsPaper.Tables
public import Sarkozy.UpperCapsPaper.LogBands
public import Sarkozy.UpperReference.Certificates





@[expose] public section

namespace Sarkozy.UpperCapsPaper

open Sarkozy Sarkozy.PartV Sarkozy.BlockAdapter

/-- The lower bound `λ_k = E_k · 0.6931471803 / J` for `log X_k`. -/
def lamQ (k : Fin 310) : ℚ := (logE.getD k.val 0 : ℚ) * (6931471803 / 10 ^ 10) / logJ

/-- **`log X_k ≥ λ_k`**. -/
theorem log_band_ge (k : Fin 310) : (lamQ k : ℝ) ≤ Real.log ((bandOf k).1 : ℝ) := by
  have hq : (lamQ k : ℝ) = (logE.getD k.val 0 : ℝ) * 0.6931471803 / logJ := by
    unfold lamQ
    push_cast
    norm_num
  rw [hq]
  exact log_band_ge_logE k

/-- `y₀ = B L/(X λ_k)` of the row. -/
def yQ (k : Fin 310) (c : Cap) : ℚ :=
  (capRow k c).B * (UpperRecords.CompletionData.record k).budget / ((bandOf k).1 * lamQ k)

/-- The rational check of a row: `λ_k > 0`, `y₀ ≤ 1` and `g(1 + y₀ + y₀²/2 + (2/9)y₀³) ≤ d`. -/
def RowArith (k : Fin 310) (c : Cap) : Prop :=
  0 < lamQ k ∧ yQ k c ≤ 1 ∧
    (capRow k c).g * (1 + yQ k c + yQ k c ^ 2 / 2 + 2 / 9 * yQ k c ^ 3) ≤ capD k c

instance (k : Fin 310) (c : Cap) : Decidable (RowArith k c) := by
  unfold RowArith
  infer_instance

/-- **The rational checks of all 1860 rows** (kernel). -/
theorem rowArith_all : ∀ (k : Fin 310) (c : Cap), RowArith k c := by
  decide +kernel

/-- **The finite hypothesis `UpperCapTables` holds**: the paper's 1860 block caps
`g exp(B_top L_k/(X_k log X_k)) ≤ d` (`cert:upper-root-caps`, `cert:upper-completed-root`,
`cert:upper-band-inputs`(a)). -/
theorem upperCapTables_holds : UpperCapTables := by
  intro k c
  obtain ⟨hlam, hy1, hd⟩ := rowArith_all k c
  obtain ⟨hg, hB, -, -, hX⟩ := capRow_side k c
  have hX0 : (0 : ℝ) < (bandOf k).1 := by
    have : (1 : ℝ) < (bandOf k).1 := by exact_mod_cast hX
    linarith
  have hy1' : ((capRow k c).B : ℝ) * ((UpperRecords.CompletionData.record k).budget : ℝ) /
      (((bandOf k).1 : ℝ) * (lamQ k : ℝ)) ≤ 1 := by
    have : ((yQ k c : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hy1
    unfold yQ at this
    push_cast at this
    exact this
  have hd' : ((capRow k c).g : ℝ) * (1 + (capRow k c).B *
      ((UpperRecords.CompletionData.record k).budget : ℝ) / (((bandOf k).1 : ℝ) * (lamQ k : ℝ)) +
      ((capRow k c).B * ((UpperRecords.CompletionData.record k).budget : ℝ) /
        (((bandOf k).1 : ℝ) * (lamQ k : ℝ))) ^ 2 / 2 +
      2 / 9 * ((capRow k c).B * ((UpperRecords.CompletionData.record k).budget : ℝ) /
        (((bandOf k).1 : ℝ) * (lamQ k : ℝ))) ^ 3) ≤ (capD k c : ℝ) := by
    have : (((capRow k c).g * (1 + yQ k c + yQ k c ^ 2 / 2 + 2 / 9 * yQ k c ^ 3) : ℚ) : ℝ) ≤
        (capD k c : ℝ) := by exact_mod_cast hd
    unfold yQ at this
    push_cast at this
    exact this
  exact UpperReference.Cert.inflation_le (by exact_mod_cast hg) (by exact_mod_cast hB)
    (Nat.cast_nonneg _) hX0 (by exact_mod_cast hlam) (log_band_ge k) hy1' hd'

/-- **`PC.hUC` from the anchor certificates alone**: the band arithmetic is proved. -/
theorem upperRootCaps_of_anchors (hB : RootAnchorsB) (hA : RootAnchorsA) (hN : NonrootAnchors) :
    ∀ k, UpperRootCaps k :=
  upperRootCaps_of_tables upperCapTables_holds hB hA hN

end Sarkozy.UpperCapsPaper
