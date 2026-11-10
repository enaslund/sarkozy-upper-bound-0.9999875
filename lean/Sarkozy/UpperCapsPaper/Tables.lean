module

public import Sarkozy.UpperCapsPaper.TableData





@[expose] public section

namespace Sarkozy.UpperCapsPaper

open Sarkozy Sarkozy.PartV Sarkozy.BlockAdapter

/-- **The paper's row of the cut `c` on band `k`**: the LL20 row of the band, or the nonroot row
at `2⁴⁷` (bands below `2⁴⁸`) or `2⁴⁸`. -/
def capRow (k : Fin 310) : Cap → CapRow
  | .LL20 => rootRows.getD k.val ⟨0, 0, 0⟩
  | c => if (bandOf k).1 < 2 ^ 48 then nonroot47 c else nonroot48 c

def UpperCapTables : Prop :=
  ∀ (k : Fin 310) (c : Cap), ((capRow k c).g : ℝ) *
      Real.exp (((capRow k c).B : ℝ) * (UpperRecords.CompletionData.record k).budget /
        (((bandOf k).1 : ℝ) * Real.log ((bandOf k).1 : ℝ))) ≤ (capD k c : ℝ)

/-- The rational side conditions of a row on band `k`. -/
def RowSide (k : Fin 310) (R : CapRow) : Prop :=
  0 ≤ R.g ∧ 0 ≤ R.B ∧ R.anchor ≤ (bandOf k).1 ∧ R.g ^ 2 < (bandOf k).1 ∧ 1 < (bandOf k).1

instance (k : Fin 310) (R : CapRow) : Decidable (RowSide k R) := by
  unfold RowSide
  infer_instance

/-- **The rational side conditions of all 1860 rows** (kernel): `0 ≤ g`, `0 ≤ B_top`, `p₀ ≤ X_k`,
`g² < X_k` and `1 < X_k`. -/
theorem capRow_side : ∀ (k : Fin 310) (c : Cap), RowSide k (capRow k c) := by
  decide +kernel

/-- The rows of band `k` with `X_k < 2⁴⁸` are the anchor rows at `2⁴⁷`, the others those at
`2⁴⁸`. -/
theorem capRow_nonroot (k : Fin 310) (c : Cap) (hc : c ≠ .LL20) :
    capRow k c = if (bandOf k).1 < 2 ^ 48 then nonroot47 c else nonroot48 c := by
  cases c
  · exact absurd rfl hc
  all_goals rfl

/-- The nonroot anchors are at `2⁴⁷` and `2⁴⁸`. -/
theorem nonroot_anchor (c : Cap) (hc : c ≠ .LL20) :
    (nonroot47 c).anchor = 2 ^ 47 ∧ (nonroot48 c).anchor = 2 ^ 48 := by
  cases c
  · exact absurd rfl hc
  all_goals constructor <;> rfl

/-- The 301 bands below `2⁵²` are the bands `k < 301`. -/
theorem band_lt_2_52 : ∀ k : Fin 310, k.val < 301 ↔ (bandOf k).1 < 2 ^ 52 := by
  decide +kernel

/-! ## The anchor certificates (analytic, uniform in the prime) -/

/-- **The LL20 anchor certificates below `2⁵²`** (`lem:record:monotone-endpoint`, general form, at
`X = X_k` with the frame witness of the band's anchor `2⁴⁷, …, 2⁵¹`; `thm:record:direct-star`;
the inputs of `lem:record:direct-star-inputs` at `X_k`, with the nonstar coefficients of the
tables at the 19 anchors interpolated by `lem:logconvex-coefficients`; `cert:upper-root-caps`):
for each of the 301 bands, at every class-three prime `p ≥ X_k`,
`-g p^{-1/2} ⪯ A_p ⪯ 1 + B_top/p` for the LL20 chamber cut, with the band's row.
*Hypothesis* (analytic; 301 statements, each uniform in the prime). -/
def RootAnchorsB : Prop :=
  ∀ k : Fin 310, k.val < 301 →
    AnchorCap .LL20 (capRow k .LL20).anchor (capRow k .LL20).g (capRow k .LL20).B

/-- **The LL20 anchor certificates from `2⁵²`: the completed root** (`lem:upper-completed-root`,
`thm:spectral-criterion`, the coupling inputs with H4 `thm:dl:H2`; `cert:upper-completed-root`):
for each of the 9 bands from `2⁵²`, at every class-three prime `p ≥ X_k`, the LL20 bound with the
band's row. *Hypothesis* (analytic; 9 statements, each uniform in the prime). -/
def RootAnchorsA : Prop :=
  ∀ k : Fin 310, 301 ≤ k.val →
    AnchorCap .LL20 (capRow k .LL20).anchor (capRow k .LL20).g (capRow k .LL20).B

/-- **The nonroot anchor certificates** (`lem:record:domain`(i) with (F6): `thm:spectral-criterion`
with the standard inputs of `subsec:upper-nonroot`; `cert:upper-band-inputs`(a), the 20 exact PSD
tests at each of `2⁴⁷` and `2⁴⁸`): for the five nonroot cuts, at every class-three prime
`p ≥ 2⁴⁷` (resp. `2⁴⁸`), the bound with the row at `2⁴⁷` (resp. `2⁴⁸`). *Hypothesis* (analytic;
10 statements, each uniform in the prime). -/
def NonrootAnchors : Prop :=
  ∀ c : Cap, c ≠ .LL20 →
    AnchorCap c (nonroot47 c).anchor (nonroot47 c).g (nonroot47 c).B ∧
      AnchorCap c (nonroot48 c).anchor (nonroot48 c).g (nonroot48 c).B

/-- **All anchor certificates of the table** from the three families. -/
theorem anchorCap_capRow (hB : RootAnchorsB) (hA : RootAnchorsA) (hN : NonrootAnchors)
    (k : Fin 310) (c : Cap) :
    AnchorCap c (capRow k c).anchor (capRow k c).g (capRow k c).B := by
  by_cases hc : c = .LL20
  · subst hc
    rcases lt_or_ge k.val 301 with h | h
    · exact hB k h
    · exact hA k h
  · rw [capRow_nonroot k c hc]
    split_ifs
    · exact (hN c hc).1
    · exact (hN c hc).2

/-- **`PC.hUC` from the paper's tables** (`cert:upper-root-caps`, `cert:upper-completed-root`,
`cert:upper-band-inputs`(a), with `lem:record:monotone-endpoint`, `lem:upper-completed-root`,
`lem:record:domain`): the finite hypothesis `UpperCapTables` and the anchor certificates give
B6's root caps on all 310 bands. -/
theorem upperRootCaps_of_tables (hT : UpperCapTables) (hB : RootAnchorsB) (hA : RootAnchorsA)
    (hN : NonrootAnchors) : ∀ k, UpperRootCaps k := by
  intro k
  refine upperRootCaps_of_capBands fun c => ?_
  obtain ⟨hg, hBt, hp₀, hgX, hX⟩ := capRow_side k c
  have hp₀' : ((capRow k c).anchor : ℝ) ≤ (bandOf k).1 := by exact_mod_cast hp₀
  have hgX' : ((capRow k c).g : ℝ) ^ 2 < (bandOf k).1 := by exact_mod_cast hgX
  have hX' : (1 : ℝ) < (bandOf k).1 := by exact_mod_cast hX
  exact capBand_of_anchor (anchorCap_capRow hB hA hN k c) hp₀' (by exact_mod_cast hg)
    (by exact_mod_cast hBt) hX' hgX' (hT k c)

end Sarkozy.UpperCapsPaper
