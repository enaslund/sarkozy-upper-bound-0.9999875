module

public import Sarkozy.FoldSymSkew.Constructor

@[expose] public section





namespace Sarkozy.FoldSymSkew

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.SignedDecomp Sarkozy.CompSharp
open Sarkozy.NormBoundsPaper4 (eo73)
open Sarkozy.MainFinal (MiddleConsts)
open Sarkozy.MainFinalF1 Sarkozy.BlockSpecPaper Sarkozy.GramBracketPaper
open Sarkozy.AnalyticCells (f1Cell)
open Sarkozy.NormBoundsPaper3 (SpecNormBoundsRest4)
open Sarkozy.MainFinalF1c (ComparisonPartsTC)

/-- RB's candidate rebased piece constants `(s_F, a_F, ℓ_t, s_E, a_E)` × 10⁹ (package R, `c₊ = 38`).
Data, for the satisfiability check only. -/
def rbKappaTab : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [(1811810326590, 1810776000000, 1285929760, 546127, 1010000254),
    (1811808857470, 1810776000000, 1285929741, 522936, 1010000233),
    (1811807456771, 1810776000000, 1285929723, 500811, 1010000214),
    (1811806375589, 1810776000000, 1285929710, 483723, 1010000199),
    (1811806110841, 1810776000000, 1285929707, 479536, 1010000196),
    (1811804826073, 1810776000000, 1285929692, 459217, 1010000180),
    (1811802416489, 1810776000000, 1285929665, 421074, 1010000152),
    (1811800211680, 1810776000000, 1285929643, 386133, 1010000128),
    (1811798189965, 1810776000000, 1285929625, 354062, 1010000108),
    (1811796337370, 1810776000000, 1285929609, 324647, 1010000090),
    (1811794641363, 1810776000000, 1285929596, 297695, 1010000076),
    (1811793088452, 1810776000000, 1285929585, 272997, 1010000064),
    (1811791665447, 1810776000000, 1285929575, 250350, 1010000054),
    (1811790360119, 1810776000000, 1285929567, 229561, 1010000046),
    (1811789163753, 1810776000000, 1285929561, 210498, 1010000039),
    (1811788068426, 1810776000000, 1285929555, 193034, 1010000033),
    (1811787063525, 1810776000000, 1285929550, 177003, 1010000028),
    (1811786142914, 1810776000000, 1285929547, 162312, 1010000024),
    (1811785299012, 1810776000000, 1285929543, 148837, 1010000020),
    (1811784526002, 1810776000000, 1285929541, 136490, 1010000017),
    (1811783816996, 1810776000000, 1285929538, 125162, 1010000015),
    (1811783166836, 1810776000000, 1285929536, 114770, 1010000013),
    (1811782571042, 1810776000000, 1285929535, 105244, 1010000011),
    (1811782024863, 1810776000000, 1285929533, 96509, 1010000009),
    (1811781524102, 1810776000000, 1285929532, 88499, 1010000008),
    (1811781065015, 1810776000000, 1285929531, 81153, 1010000007),
    (1811780644089, 1810776000000, 1285929530, 74416, 1010000006),
    (1811779282813, 1810776000000, 1285929528, 52621, 1010000004),
    (1811778320691, 1810776000000, 1285929527, 37208, 1010000003),
    (1811777160007, 1810776000000, 1285929526, 18605, 1010000002),
    (1811776579919, 1810776000000, 1285929526, 9303, 1010000002),
    (1811776144964, 1810776000000, 1285929526, 2327, 1010000002),
    (1811776025626, 1810776000000, 1285929526, 413, 1010000002)]

/-- The row of piece `k`. -/
def rbRow (k : Fin 33) : ℕ × ℕ × ℕ × ℕ × ℕ := rbKappaTab.getD k.val (0, 0, 0, 0, 0)

/-- `s_F′(k)`. -/
def rbSF (k : Fin 33) : ℚ := ((rbRow k).1 : ℚ) / 10 ^ 9
/-- `a_F′(k)`. -/
def rbAF (k : Fin 33) : ℚ := ((rbRow k).2.1 : ℚ) / 10 ^ 9
/-- `ℓ′(k)`. -/
def rbL (k : Fin 33) : ℚ := ((rbRow k).2.2.1 : ℚ) / 10 ^ 9
/-- `s_E′(k)`. -/
def rbSE (k : Fin 33) : ℚ := ((rbRow k).2.2.2.1 : ℚ) / 10 ^ 9
/-- `a_E′(k)`. -/
def rbAE (k : Fin 33) : ℚ := ((rbRow k).2.2.2.2 : ℚ) / 10 ^ 9

/-- RB's candidate table as `MiddleConsts`. -/
noncomputable def rbKappa (k : Fin 33) : MiddleConsts where
  sF := (rbSF k : ℝ)
  aF := (rbAF k : ℝ)
  ℓ := (rbL k : ℝ)
  sE := (rbSE k : ℝ)
  aE := (rbAE k : ℝ)

/-- **The side conditions at RB's table** (kernel, exact rationals): FS's `SymSkewSides` with
`E = esgX` and C38's `FoldSides` at `c_B = 38`, `R = 0`. -/
theorem rb_check : ∀ k : Fin 33,
    eo73 k + esgX k ≤ rbSF k ∧ esgX k ≤ rbAF k ∧ aNU * gamX k ≤ rbL k ∧ 0 ≤ rbL k ∧
      (gamX k + eo73 k * rX k) ^ 2 + 627 / 500 * (38 + 0 * rX k) ^ 2 ≤ rbSF k ∧
      627 / 500 * (38 + 0 * rX k) ^ 2 ≤ rbAF k ∧ (38 + 0 * rX k) * rX k ≤ 1 := by
  decide +kernel

theorem rb_sides (k : Fin 33) : SymSkewSides rbKappa esgX k ∧ FoldSides rbKappa 38 0 k := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := rb_check k
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · change (((eo73 k + esgX k : ℚ)) : ℝ) ≤ (rbSF k : ℝ); exact_mod_cast h1
  · change ((esgX k : ℚ) : ℝ) ≤ (rbAF k : ℝ); exact_mod_cast h2
  · change ((aNU * gamX k : ℚ) : ℝ) ≤ (rbL k : ℝ); exact_mod_cast h3
  · change (0 : ℝ) ≤ (rbL k : ℝ); exact_mod_cast h4
  · change (((gamX k + eo73 k * rX k) ^ 2 : ℚ) : ℝ) +
        627 / 500 * ((38 : ℝ) + 0 * ((rX k : ℚ) : ℝ)) ^ 2 ≤ (rbSF k : ℝ)
    have := (Rat.cast_le (K := ℝ)).mpr h5
    push_cast at this ⊢
    linarith
  · change 627 / 500 * ((38 : ℝ) + 0 * ((rX k : ℚ) : ℝ)) ^ 2 ≤ (rbAF k : ℝ)
    have := (Rat.cast_le (K := ℝ)).mpr h6
    push_cast at this ⊢
    linarith
  · exact_mod_cast h7

/-- **All four fold bounds at RB's table from SD2's `SDB`** (`prop:signed-bounds`(a),(b),(e)):
NB3's `hNr4` at `rbKappa`, with no further input. -/
theorem hNr4_rb {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
    {A : PaperAnalyticInputs f1Cell} {C : ComparisonPartsTC hW hMR hFour A}
    (H : SignedDecompAnalytic2 C) :
    ∀ b i, blockSite b = .inl i →
      SpecNormBoundsRest4 hW (paperIn f1Cell) (rbKappa i) (blockLeast b) (specF hW A b) (C.blk b) :=
  hNr4_of_SDB38 H rbKappa (fun k => (rb_sides k).2) (fun k => (rb_sides k).1)

end Sarkozy.FoldSymSkew
