module

public import Sarkozy.SignedDecompCrude.Uniform

@[expose] public section

/-!
# The gates at `e_sg′ = 21`, `c_col = 73`, `c_+ = 38` at the rebased sides; PG's `SD` (ND)

`paper/sections/24_matching_mean.tex`, `prop:signed-sides`(i);
`paper/sections/21_middle_records.tex`, `cert:signed-local`, `prop:signed-bounds`(c).

* **`gate21_check`** (kernel, exact rationals): at the 33 piece starts, with MRG's sides after
  RB's package R (`sideQ`, `+ 0.02`), FD's `e_o(X) = eoPoly (AX k) 73` and `c_B = 38`:
  `(s_t Γ_X + (e_o(X) + 21) r_X) H̄_X ≤ d_k`, `((Γ_X + e_o(X) r_X)² + (1 + t) 38²) r_X H̄_X ≤ d_k`,
  `(Γ_X + e_o(X) r_X) r_X ≤ 1`, `38 r_X ≤ 1`. This is RG's `gate73_80_check` with `esgX k`
  replaced by `21` and `80` by `38`.
* **`gateAt21`**: PG's `GateAt` on a middle block of piece `k` at these constants (RG's
  `gateAt73`, proof copied); **`pieceGate21`**: `PieceGate (fun _ => 21) 38 k`.
* **`pieceGate_esgCrude`**: `PieceGate (esgCrude κRec nT) 38 k`, since `e_sg′(p) ≤ 21`
  (`esgCrude_le`, `pieceGate_mono`).
* **`signedDecompInputs_proved`**: **PG's `SignedDecompInputsC C` for every `C`, with no
  hypothesis** beyond those inside `C` (H1 through E1's `paperMiddleEstimates`).
-/

open Finset

namespace Sarkozy.SignedDecompCrude

open Sarkozy.PrimeGram Sarkozy.MiddleRecords Sarkozy.SignedGram Sarkozy.SignedComponents
  Sarkozy.Labellings
open Sarkozy.SignedDecomp
open Sarkozy.PartV (MiddleNonempty)
open Sarkozy.MainFinal2 (tPaper tPaper_nonneg tPaper_le_one)
open Sarkozy.MiddleRefinement (sideQ paperSide)
open Sarkozy.MainFinalF1c (ComparisonPartsTC)
open Sarkozy.AnalyticCells (f1Cell)
open Sarkozy.BlockSpecPaper

/-- **The gates at `e_sg = 21`, `c_col = 73`, `c_B = 38`** at the rebased sides (kernel, exact
rationals). -/
theorem gate21_check : ∀ k : Fin 33,
    (stU * gamX k + (eoPoly (AX k) 73 + 21) * rX k) * hX k ≤ sideQ k ∧
    ((gamX k + eoPoly (AX k) 73 * rX k) ^ 2 + 627 / 500 * 38 ^ 2) * rX k * hX k ≤ sideQ k ∧
    (gamX k + eoPoly (AX k) 73 * rX k) * rX k ≤ 1 ∧ 38 * rX k ≤ 1 ∧ 0 ≤ eoPoly (AX k) 73 := by
  decide +kernel

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ} [∀ i, Fact (pr i).Prime]

/-- **The gates on a middle block of piece `k`** at `e_o = eoP pr 73`, `e_sg = 21`, `c_+ = 38`
(RG's `gateAt73` with these constants, from `gate21_check`). -/
theorem gateAt21 (k : Fin 33) (hXp : ∀ i, XQ k ≤ pr i) (hcard : Fintype.card ι ≤ nX k)
    {r : ℝ} (hr0 : 0 ≤ r) (hrp : ∀ i, rP pr i ≤ r) (hrX : r ≤ (rX k : ℝ)) :
    GateAt pr (eoP pr (fun _ => (73 : ℝ))) (fun _ => (21 : ℝ)) (fun _ => (38 : ℝ))
        (r * paperSide k / Hblock pr) := by
  obtain ⟨hX24, hs1, hs2, -⟩ := table_check k
  obtain ⟨g1, g2, g3, g4, g5⟩ := gate21_check k
  have hX' : (2 : ℝ) ^ 24 ≤ (XQ k : ℝ) := by exact_mod_cast hX24
  have hX5 : (5 : ℕ) ≤ XQ k := le_trans (by norm_num) hX24
  have hXp' : ∀ i, (XQ k : ℝ) ≤ (pr i : ℝ) := fun i => by exact_mod_cast hXp i
  have h19 : ∀ i, 19 ≤ pr i := fun i => le_trans (by norm_num) (hX24.trans (hXp i))
  have hp0 : ∀ i, (0 : ℝ) < pr i := fun i => lt_of_lt_of_le (by norm_num) (hX'.trans (hXp' i))
  have hrP0 : ∀ i, 0 ≤ rP pr i := fun i => inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hγ0 : ∀ i, 0 ≤ gammaP pr i := gammaP_nonneg h19
  have hγA : ∀ i, gammaP pr i ≤ GammaAP pr i := gammaP_le_GammaAP h19
  have hΓA : ∀ i, GammaAP pr i ≤ ((gamX k : ℚ) : ℝ) := fun i => GammaA_le hX24 (hXp' i) hs2 hs1
  have hLeG : ∀ i, (atomsAt (pr i) (gammaP pr i)).Le (AX k).cast := fun i =>
    atomsAt_le hX24 (hXp' i) hs2 hs1 (hγ0 i) ((hγA i).trans (hΓA i))
  -- the constants
  have heo : ∀ i, eoP pr (fun _ => (73 : ℝ)) i = eoPoly (atomsAt (pr i) (gammaP pr i)) 73 :=
    fun i => eoC_eq _ _ _
  have heoX : ∀ i, eoP pr (fun _ => (73 : ℝ)) i ≤ ((eoPoly (AX k) 73 : ℚ) : ℝ) := fun i => by
    rw [heo, eoPoly_cast]
    exact eoPoly_mono (hLeG i) (by norm_num) (by norm_num)
  have heo0 : ∀ i, 0 ≤ eoP pr (fun _ => (73 : ℝ)) i := fun i => by
    rw [heo]; exact eoPoly_nonneg (hLeG i) (by norm_num)
  -- the density bound
  have hH : Hblock pr ≤ ((hX k : ℚ) : ℝ) := by
    rw [hX_cast hX5]; exact Hblock_le (by exact_mod_cast hX5) hXp' hcard
  have hH0 : 0 < Hblock pr := Hblock_pos pr h19
  -- the rational gates in `ℝ`
  obtain ⟨p1, -, -, -, p5, p6⟩ := pos_check k
  have pG : (0 : ℝ) ≤ ((gamX k : ℚ) : ℝ) := by exact_mod_cast p1
  have pE : (0 : ℝ) ≤ ((eoPoly (AX k) 73 : ℚ) : ℝ) := by exact_mod_cast g5
  have pS : (0 : ℝ) ≤ ((21 : ℚ) : ℝ) := by norm_num
  have pC : (0 : ℝ) ≤ ((38 : ℚ) : ℝ) := by norm_num
  have pR : (0 : ℝ) ≤ ((rX k : ℚ) : ℝ) := by exact_mod_cast p5
  have pT : (0 : ℝ) ≤ ((stU : ℚ) : ℝ) := by exact_mod_cast p6
  have h1 : (((stU * gamX k + (eoPoly (AX k) 73 + 21) * rX k) * hX k : ℚ) : ℝ) ≤
      ((sideQ k : ℚ) : ℝ) := by
    exact_mod_cast g1
  have h2 : ((((gamX k + eoPoly (AX k) 73 * rX k) ^ 2 + 627 / 500 * 38 ^ 2) * rX k * hX k : ℚ) :
      ℝ) ≤ ((sideQ k : ℚ) : ℝ) := by
    exact_mod_cast g2
  have h3 : (((gamX k + eoPoly (AX k) 73 * rX k) * rX k : ℚ) : ℝ) ≤ 1 := by exact_mod_cast g3
  have h4 : ((((38 : ℚ) * rX k : ℚ) : ℝ)) ≤ 1 := by exact_mod_cast g4
  push_cast at h1 h2 h3 h4
  have hd : paperSide k = ((sideQ k : ℚ) : ℝ) := rfl
  set G := ((gamX k : ℚ) : ℝ)
  set E := ((eoPoly (AX k) 73 : ℚ) : ℝ)
  set S := ((21 : ℚ) : ℝ) with hSdef
  set R := ((rX k : ℚ) : ℝ)
  set T := ((stU : ℚ) : ℝ)
  set H := ((hX k : ℚ) : ℝ)
  set d := ((sideQ k : ℚ) : ℝ)
  have hrR : ∀ i, rP pr i ≤ R := fun i => (hrp i).trans hrX
  have hσ : ∀ x : ℝ, 0 ≤ x → x * H ≤ d → r * x ≤ r * paperSide k / Hblock pr := by
    intro x hx hxd
    rw [hd, le_div_iff₀ hH0]
    have : x * Hblock pr ≤ d := (mul_le_mul_of_nonneg_left hH hx).trans hxd
    nlinarith
  refine ⟨fun i => ?_, (G + E * R) * r, 38 * r, by positivity, ?_, by positivity, ?_,
    fun i => ?_, fun i => ?_, ?_⟩
  · -- the prime Gram gate
    have hA : Sarkozy.Envelopes.sT tPaper * gammaP pr i +
        (eoP pr (fun _ => (73 : ℝ)) i + 21) * rP pr i ≤ T * G + (E + S) * R := by
      have := mul_le_mul sT_le ((hγA i).trans (hΓA i)) (hγ0 i) pT
      have hS21 : (21 : ℝ) ≤ S := by rw [hSdef]; norm_num
      have := mul_le_mul (add_le_add (heoX i) hS21) (hrR i) (hrP0 i) (add_nonneg pE pS)
      linarith
    have hA0 : 0 ≤ Sarkozy.Envelopes.sT tPaper * gammaP pr i +
        (eoP pr (fun _ => (73 : ℝ)) i + 21) * rP pr i := by
      have : 0 ≤ Sarkozy.Envelopes.sT tPaper := Real.sqrt_nonneg _
      have := hγ0 i
      have := heo0 i
      have := hrP0 i
      positivity
    have := hσ (T * G + (E + S) * R) (by positivity) h1
    calc _ ≤ (T * G + (E + S) * R) * r := mul_le_mul hA (hrp i) (hrP0 i) (by positivity)
      _ = r * (T * G + (E + S) * R) := by ring
      _ ≤ _ := this
  · have : (G + E * R) * r ≤ (G + E * R) * R := mul_le_mul_of_nonneg_left hrX (by positivity)
    linarith
  · have : 38 * r ≤ 38 * R := mul_le_mul_of_nonneg_left hrX (by norm_num)
    linarith
  · refine min_le_of_right_le ?_
    have : gammaP pr i + eoP pr (fun _ => (73 : ℝ)) i * rP pr i ≤ G + E * R := by
      have := mul_le_mul (heoX i) (hrR i) (hrP0 i) pE
      linarith [(hγA i).trans (hΓA i)]
    exact mul_le_mul this (hrp i) (hrP0 i) (by positivity)
  · exact min_le_of_right_le (mul_le_mul_of_nonneg_left (hrp i) (by norm_num))
  · have ht : (1 : ℝ) + tPaper = 627 / 500 := by norm_num [tPaper]
    rw [ht]
    have := hσ (((G + E * R) ^ 2 + 627 / 500 * 38 ^ 2) * R) (by positivity) (by linarith)
    have hW : 0 ≤ (G + E * R) ^ 2 + 627 / 500 * 38 ^ 2 := by positivity
    calc ((G + E * R) * r) ^ 2 + 627 / 500 * (38 * r) ^ 2
        = r * (((G + E * R) ^ 2 + 627 / 500 * 38 ^ 2) * r) := by ring
      _ ≤ r * (((G + E * R) ^ 2 + 627 / 500 * 38 ^ 2) * R) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrX hW) hr0
      _ ≤ _ := this

end Block

/-- **`PieceGate (fun _ => 21) 38 k`** at every piece. -/
theorem pieceGate21 (k : Fin 33) : PieceGate (fun _ => 21) 38 k := by
  intro ι _ _ pr _ hXp hcard r hr0 hrp hrX
  exact gateAt21 k hXp hcard hr0 hrp hrX

/-- **The gate of ND's crude constant**: `PieceGate (esgCrude κRec nT) 38 k` at every piece. -/
theorem pieceGate_esgCrude (k : Fin 33) : PieceGate (esgCrude κRec nT) 38 k :=
  pieceGate_mono (pieceGate21 k) fun _ hp => esgCrude_le hp

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {A : PaperAnalyticInputs f1Cell}

/-- **PG's `SD` proved**: for every `C : ComparisonPartsTC`, `SignedDecompInputsC C` holds, with
`lem:record:conditional-collision`(d) at `c_col = 73`, `prop:signed-bounds`(c) for the components
at `c_+ = 38` and for the signed record at `e_sg′ = esgCrude κRec nT ≤ 21`, and all gates at
the rebased sides. -/
theorem signedDecompInputs_proved (C : ComparisonPartsTC hW hMR hFour A) : SignedDecompInputsC C :=
  signedDecompInputs_of_gates C pieceGate_esgCrude

end Sarkozy.SignedDecompCrude
