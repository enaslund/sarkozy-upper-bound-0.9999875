module

public import Sarkozy.SignedDecomp.Main2
public import Sarkozy.NormBoundsPaper4.FoldCol

@[expose] public section

/-!
# SD2's `SDB` without the collision bound: `c_col = 73` at the loosened sides (RG)

`paper/sections/21_middle_records.tex`, `lem:record:conditional-collision`(d), `cert:signed-local`,
`prop:signed-bounds`(c),(d); `paper/sections/24_matching_mean.tex`, `prop:signed-sides`(i).

SD2's `SignedDecompAnalytic2` asks, at every prime of every middle block, for two analytic
statements at the paper's constants: the collision bound `lem:record:conditional-collision`(d)
with `c_col ≈ 5.62` (`col`) and the signed decomposition of `prop:signed-bounds`(c) with `e_sg`
(`new`). The first gate of `prop:signed-sides`(i) was tight at the paper's sides (`gate_tight`),
so the paper's `c_col` was needed.

**RG's rebase (7 November 2026).** RB's package R loosens every side by `0.02`
(`MiddleRefinement.sideTab`). At these sides the gates hold with `e_o` evaluated at the crude
collision constant `c_col = 73`, which FD proved for every prime `p ≥ 2²⁴`
(`NormBoundsPaper4.collisionBound_73`), and with SD2's proved component constant `80`
(`comp80_paper`):

* **`gate73_80_check`** (kernel, exact rationals): the two gates and the side conditions at the 33
  piece starts with `e_o(X) = eoPoly (AX k) 73` and `c_B = 80`;
* **`gateAt73`**: PG's `GateAt` on a middle block of piece `k` at `e_o = eoP pr 73`, `e_sg = esgP`,
  `c_+ = 80` (as SD2's `gateAt_gen`, with the constant collision constant);
* **`decompGateAtC_of_new73`**: PG's `DecompGateAtC` from `new` alone (`col` proved by
  `collisionBound_73`, `comp` given);
* **`SpecNew`**, **`SignedDecompNew`** (*hypothesis*, 1 field, `prop:signed-bounds`(c) for the
  signed record at the paper's `e_sg`, every prime of every middle block), with
  **`SignedDecompNew.toSD : SignedDecompInputsC C`** and **`SignedDecompAnalytic2.toNew`** (SD2's
  hypothesis implies it: the new one is the `new` half).

So the collision half of `SDB` is closed: only `new` (`e_sg`) remains.
-/

open Finset

namespace Sarkozy.Rebase

open Sarkozy.PrimeGram Sarkozy.MiddleRecords Sarkozy.SignedGram Sarkozy.SignedComponents
  Sarkozy.Labellings
open Sarkozy.SignedDecomp
open Sarkozy.MiddleComparison (signedCoef)
open Sarkozy.PartV (MiddleNonempty)
open Sarkozy.MainFinal2 (tPaper tPaper_nonneg tPaper_le_one)
open Sarkozy.MiddleRefinement (sideQ paperSide)
open Sarkozy.NormBoundsPaper4 (collisionBound_73)

/-- **The gates at `c_col = 73` and `c_B = 80`** at RB's loosened sides (kernel, exact
rationals; `prop:signed-sides`(i), `cert:signed-local`). -/
theorem gate73_80_check : ∀ k : Fin 33,
    (stU * gamX k + (eoPoly (AX k) 73 + esgX k) * rX k) * hX k ≤ sideQ k ∧
    ((gamX k + eoPoly (AX k) 73 * rX k) ^ 2 + 627 / 500 * 80 ^ 2) * rX k * hX k ≤ sideQ k ∧
    (gamX k + eoPoly (AX k) 73 * rX k) * rX k ≤ 1 ∧ 80 * rX k ≤ 1 ∧ 0 ≤ eoPoly (AX k) 73 := by
  decide +kernel

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ} [∀ i, Fact (pr i).Prime]

/-- **The gates on a middle block of piece `k`** at `e_o = eoP pr 73` (the crude collision
constant), `e_sg = esgP` and `c_+ = 80`, for any scale `r ≥ 0` with `p^{-1/2} ≤ r ≤ r_X` at every
prime (SD2's `gateAt_gen` with `c_col = 73`, from `gate73_80_check`). -/
theorem gateAt73 (k : Fin 33) (hXp : ∀ i, XQ k ≤ pr i) (hcard : Fintype.card ι ≤ nX k)
    {r : ℝ} (hr0 : 0 ≤ r) (hrp : ∀ i, rP pr i ≤ r) (hrX : r ≤ (rX k : ℝ)) :
    GateAt pr (eoP pr (fun _ => (73 : ℝ))) (esgP pr) (fun _ => (80 : ℝ))
        (r * paperSide k / Hblock pr) ∧ (∀ i, 0 ≤ esgP pr i) := by
  obtain ⟨hX24, hs1, hs2, -⟩ := table_check k
  obtain ⟨g1, g2, g3, g4, g5⟩ := gate73_80_check k
  have hX' : (2 : ℝ) ^ 24 ≤ (XQ k : ℝ) := by exact_mod_cast hX24
  have hX5 : (5 : ℕ) ≤ XQ k := le_trans (by norm_num) hX24
  have hXp' : ∀ i, (XQ k : ℝ) ≤ (pr i : ℝ) := fun i => by exact_mod_cast hXp i
  have h19 : ∀ i, 19 ≤ pr i := fun i => le_trans (by norm_num) (hX24.trans (hXp i))
  have hp0 : ∀ i, (0 : ℝ) < pr i := fun i => lt_of_lt_of_le (by norm_num) (hX'.trans (hXp' i))
  have hrP0 : ∀ i, 0 ≤ rP pr i := fun i => inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hγ0 : ∀ i, 0 ≤ gammaP pr i := gammaP_nonneg h19
  have hγA : ∀ i, gammaP pr i ≤ GammaAP pr i := gammaP_le_GammaAP h19
  have hΓA : ∀ i, GammaAP pr i ≤ ((gamX k : ℚ) : ℝ) := fun i => GammaA_le hX24 (hXp' i) hs2 hs1
  have hLeA : ∀ i, (atomsAt (pr i) (GammaAP pr i)).Le (AX k).cast := fun i =>
    atomsAt_le hX24 (hXp' i) hs2 hs1 ((hγ0 i).trans (hγA i)) (hΓA i)
  have hLeG : ∀ i, (atomsAt (pr i) (gammaP pr i)).Le (AX k).cast := fun i =>
    atomsAt_le hX24 (hXp' i) hs2 hs1 (hγ0 i) ((hγA i).trans (hΓA i))
  -- the constants
  have hesg : ∀ i, esgP pr i = esgPoly (atomsAt (pr i) (GammaAP pr i)) := fun i =>
    esgL_eq (hp0 i) _
  have hesgX : ∀ i, esgP pr i ≤ ((esgX k : ℚ) : ℝ) := fun i => by
    rw [hesg, esgX, esgPoly_cast]; exact esgPoly_mono (hLeA i)
  have hesg0 : ∀ i, 0 ≤ esgP pr i := fun i => by rw [hesg]; exact esgPoly_nonneg (hLeA i)
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
  obtain ⟨p1, -, p3, -, p5, p6⟩ := pos_check k
  have pG : (0 : ℝ) ≤ ((gamX k : ℚ) : ℝ) := by exact_mod_cast p1
  have pE : (0 : ℝ) ≤ ((eoPoly (AX k) 73 : ℚ) : ℝ) := by exact_mod_cast g5
  have pS : (0 : ℝ) ≤ ((esgX k : ℚ) : ℝ) := by exact_mod_cast p3
  have pC : (0 : ℝ) ≤ ((80 : ℚ) : ℝ) := by norm_num
  have pR : (0 : ℝ) ≤ ((rX k : ℚ) : ℝ) := by exact_mod_cast p5
  have pT : (0 : ℝ) ≤ ((stU : ℚ) : ℝ) := by exact_mod_cast p6
  have h1 : (((stU * gamX k + (eoPoly (AX k) 73 + esgX k) * rX k) * hX k : ℚ) : ℝ) ≤
      ((sideQ k : ℚ) : ℝ) := by
    exact_mod_cast g1
  have h2 : ((((gamX k + eoPoly (AX k) 73 * rX k) ^ 2 + 627 / 500 * 80 ^ 2) * rX k * hX k : ℚ) :
      ℝ) ≤ ((sideQ k : ℚ) : ℝ) := by
    exact_mod_cast g2
  have h3 : (((gamX k + eoPoly (AX k) 73 * rX k) * rX k : ℚ) : ℝ) ≤ 1 := by exact_mod_cast g3
  have h4 : ((((80 : ℚ) * rX k : ℚ) : ℝ)) ≤ 1 := by exact_mod_cast g4
  push_cast at h1 h2 h3 h4
  have hd : paperSide k = ((sideQ k : ℚ) : ℝ) := rfl
  set G := ((gamX k : ℚ) : ℝ)
  set E := ((eoPoly (AX k) 73 : ℚ) : ℝ)
  set S := ((esgX k : ℚ) : ℝ)
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
  refine ⟨⟨fun i => ?_, (G + E * R) * r, 80 * r, by positivity, ?_, by positivity, ?_,
    fun i => ?_, fun i => ?_, ?_⟩, hesg0⟩
  · -- the prime Gram gate
    have hA : Sarkozy.Envelopes.sT tPaper * gammaP pr i +
        (eoP pr (fun _ => (73 : ℝ)) i + esgP pr i) * rP pr i ≤ T * G + (E + S) * R := by
      have := mul_le_mul sT_le ((hγA i).trans (hΓA i)) (hγ0 i) pT
      have := mul_le_mul (add_le_add (heoX i) (hesgX i)) (hrR i) (hrP0 i) (add_nonneg pE pS)
      linarith
    have hA0 : 0 ≤ Sarkozy.Envelopes.sT tPaper * gammaP pr i +
        (eoP pr (fun _ => (73 : ℝ)) i + esgP pr i) * rP pr i := by
      have : 0 ≤ Sarkozy.Envelopes.sT tPaper := Real.sqrt_nonneg _
      have := hγ0 i
      have := heo0 i
      have := hesg0 i
      have := hrP0 i
      positivity
    have := hσ (T * G + (E + S) * R) (by positivity) h1
    calc _ ≤ (T * G + (E + S) * R) * r := mul_le_mul hA (hrp i) (hrP0 i) (by positivity)
      _ = r * (T * G + (E + S) * R) := by ring
      _ ≤ _ := this
  · have : (G + E * R) * r ≤ (G + E * R) * R := mul_le_mul_of_nonneg_left hrX (by positivity)
    linarith
  · have : 80 * r ≤ 80 * R := mul_le_mul_of_nonneg_left hrX (by norm_num)
    linarith
  · refine min_le_of_right_le ?_
    have : gammaP pr i + eoP pr (fun _ => (73 : ℝ)) i * rP pr i ≤ G + E * R := by
      have := mul_le_mul (heoX i) (hrR i) (hrP0 i) pE
      linarith [(hγA i).trans (hΓA i)]
    exact mul_le_mul this (hrp i) (hrP0 i) (by positivity)
  · exact min_le_of_right_le (mul_le_mul_of_nonneg_left (hrp i) (by norm_num))
  · have ht : (1 : ℝ) + tPaper = 627 / 500 := by norm_num [tPaper]
    rw [ht]
    have := hσ (((G + E * R) ^ 2 + 627 / 500 * 80 ^ 2) * R) (by positivity) (by linarith)
    have hW : 0 ≤ (G + E * R) ^ 2 + 627 / 500 * 80 ^ 2 := by positivity
    calc ((G + E * R) * r) ^ 2 + 627 / 500 * (80 * r) ^ 2
        = r * (((G + E * R) ^ 2 + 627 / 500 * 80 ^ 2) * r) := by ring
      _ ≤ r * (((G + E * R) ^ 2 + 627 / 500 * 80 ^ 2) * R) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrX hW) hr0
      _ ≤ _ := this

variable (pr) in
/-- **PG's `DecompGateAtC` on a middle block of piece `k` from the signed decomposition alone**:
the collision bound at `c_col = 73` is proved (`collisionBound_73`, primes `≥ 2²⁴`), the
component norms at `80` are given, the gates are proved (`gateAt73`). -/
theorem decompGateAtC_of_new73 (hne : MiddleNonempty pr) (C : FoldComponents pr hne)
    (k : Fin 33) (h3 : ∀ i, pr i % 4 = 3) (hXp : ∀ i, XQ k ≤ pr i)
    (hcard : Fintype.card ι ≤ nX k) {r : ℝ} (hr0 : 0 ≤ r) (hrp : ∀ i, rP pr i ≤ r)
    (hrX : r ≤ (rX k : ℝ))
    (new : ∀ i, NewDecomp (mP hne i) (∑ c, signedCoef tPaper c • compP hne C c i) tPaper
      (esgP pr i))
    (comp : ∀ c i, CentredNorm (mP hne i) (compP hne C c i) (80 * rP pr i)) :
    DecompGateAtC pr hne C r (paperSide k) := by
  obtain ⟨G, h1⟩ := gateAt73 k hXp hcard hr0 hrp hrX
  obtain ⟨hX24, -, -, -⟩ := table_check k
  have h19 : ∀ i, 19 ≤ pr i := fun i => le_trans (by norm_num) (hX24.trans (hXp i))
  have col : ∀ i, CollisionBound (hne.F2 i) ((fun _ => (73 : ℝ)) i) := fun i => by
    obtain ⟨hR, h3', -⟩ := primeHyps h3 h19 i
    have h24 : 2 ^ 24 ≤ Fintype.card (ZMod (pr i)) := by
      rw [ZMod.card]; exact hX24.trans (hXp i)
    exact collisionBound_73 (hne.F2 i) hR h3' h24
  exact ⟨fun _ => 73, esgP pr, fun _ => 80,
    ⟨col, new, comp, fun _ => by norm_num, h1, fun _ => by norm_num⟩, G⟩

end Block

section Paper

open Sarkozy.MainFinalF1 (bOf Blk SignedSpec specF analyticInputs)
open Sarkozy.MainFinalF1c (ComparisonPartsTC)
open Sarkozy.BlockSpecPaper
open Sarkozy.PartVLaws (PaperBlockSpec blockPrimes)
open Sarkozy.AnalyticCells (f1Cell f1Cell_budget)
open Sarkozy.GramBracketPaper (specScale)

/-- **`DecompGateAtC` at a middle block of piece `k`** of the F1 data, for any scale `r ≥ 0` with
`r² b_𝔅 = 1`, from the signed decomposition at the paper's `e_sg` alone (SD2's `blockDecomp`
with `c_col = 73` and the component norms `comp80_paper`). -/
theorem blockDecomp73 {b : Blk} {k : Fin 33} (hb : blockSite b = .inl k)
    (hne : MiddleNonempty (blockPrimes bOf b))
    (Dc : DefectConstants b hne tPaper_nonneg tPaper_le_one)
    {r : ℝ} (hr : 0 ≤ r) (hs : r ^ 2 * (paperIn f1Cell).bmin b = 1)
    (new : ∀ i, NewDecomp (mP hne i)
      (∑ c, signedCoef tPaper c • compP hne (paperComponents Dc) c i) tPaper
      (esgP (blockPrimes bOf b) i)) :
    DecompGateAtC (blockPrimes bOf b) hne (paperComponents Dc) r (paperSide k) := by
  have hXp : ∀ j, XQ k ≤ blockPrimes bOf b j := fun j => (blockPrimes_mem_piece hb j).1
  have hbud : ∑ j, Real.log (blockPrimes bOf b j) ≤ 570 := by
    have h := (f1Cell_budget b).1 k hb
    have e : ((PartV.middleBudget : ℕ) : ℝ) = 570 := by norm_num [PartV.middleBudget]
    rw [e] at h
    exact h
  obtain ⟨hX24, -, -, hE⟩ := table_check k
  have hcard := card_le_of_budget (le_trans (by norm_num) hX24) hXp hbud hE
  have hbm : (paperIn f1Cell).bmin b = (blockLeast b : ℝ) := rfl
  have hXb : (XQ k : ℝ) ≤ (paperIn f1Cell).bmin b := by
    have h := siteStart_le_blockLeast b
    rw [hb] at h
    have h' : XQ k ≤ blockLeast b := h
    rw [hbm]
    exact Nat.cast_le.mpr h'
  have hbp : ∀ j, (paperIn f1Cell).bmin b ≤ (blockPrimes bOf b j : ℝ) := fun j => by
    rw [hbm]
    exact Nat.cast_le.mpr (blockLeast_le b j)
  obtain ⟨hrp, hrX⟩ := scale_bounds k hr hs hbp hXb
  exact decompGateAtC_of_new73 _ hne _ k
    (fun j => (Sarkozy.FirstStagePaper.blockPrimes_mod_ge b j).1) hXp hcard hr hrp hrX new
    (comp80_paper hne Dc)

variable (hW : Target.Weil)

/-- **The signed decomposition at a class-three block of the F1 data**, by specification
(`prop:signed-bounds`(c) for the centred signed record at the paper's `e_sg`, every prime).
`True` on an upper block. -/
def SpecNew {b : Blk} : (S : PaperBlockSpec bOf b) → SignedSpec hW S → Prop
  | .upper _, _ => True
  | .middleUniform M, E => ∀ i, NewDecomp (mP M.hne i)
      (∑ c, signedCoef tPaper c • compP M.hne (paperComponents E.down.toDC) c i) tPaper
      (esgP (blockPrimes bOf b) i)
  | .middleIndividual M, E => ∀ i, NewDecomp (mP M.hne i)
      (∑ c, signedCoef tPaper c • compP M.hne (paperComponents E.down.toDC) c i) tPaper
      (esgP (blockPrimes bOf b) i)
  | .middleCoherent M, E => ∀ i, NewDecomp (mP M.hne i)
      (∑ c, signedCoef tPaper c • compP M.hne (paperComponents E.down.toDC) c i) tPaper
      (esgP (blockPrimes bOf b) i)

/-- **PG's `SpecDecompC` from `SpecNew`** at a middle block of piece `k`: collision bound, component
norms and gates proved. -/
theorem specDecompC_of_new {b : Blk} {k : Fin 33} (hb : blockSite b = .inl k) :
    (S : PaperBlockSpec bOf b) → (E : SignedSpec hW S) → specScale (paperIn f1Cell) S →
      SpecNew hW S E → SpecDecompC hW (paperIn f1Cell) (paperSide k) S E
  | .upper _, _, _, _ => trivial
  | .middleUniform M, E, hs, H => blockDecomp73 hb M.hne E.down.toDC M.hr hs H
  | .middleIndividual M, E, hs, H => blockDecomp73 hb M.hne E.down.toDC M.hr hs H
  | .middleCoherent M, E, hs, H => blockDecomp73 hb M.hne E.down.toDC M.hr hs H

/-- SD2's `SpecAnalytic2` gives `SpecNew` (its `new` half). -/
theorem specNew_of_2 {b : Blk} :
    (S : PaperBlockSpec bOf b) → (E : SignedSpec hW S) → SpecAnalytic2 hW S E → SpecNew hW S E
  | .upper _, _, _ => trivial
  | .middleUniform _, _, H => H.new
  | .middleIndividual _, _, H => H.new
  | .middleCoherent _, _, H => H.new

variable {hW} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {A : PaperAnalyticInputs f1Cell}

/-- **The analytic content of PG's `SD` after RG's rebase** (*hypothesis*, 1 field): at every
prime of every middle block of the F1 data, `prop:signed-bounds`(c) for the centred signed record
with the paper's `e_sg` (`esgP`). The collision bound `lem:record:conditional-collision`(d) is
not an input any more (`c_col = 73` suffices at the loosened sides). -/
structure SignedDecompNew (C : ComparisonPartsTC hW hMR hFour A) : Prop where
  an : ∀ b i, blockSite b = .inl i → SpecNew hW (specF hW A b) (C.blk b)

/-- **A constructor of PG's `SignedDecompInputsC`** from the signed decomposition alone: the
collision bound (`collisionBound_73`), the component norms (`comp80_paper`) and all the gates
(`gate73_80_check`) are proved. -/
theorem SignedDecompNew.toSD {C : ComparisonPartsTC hW hMR hFour A}
    (H : SignedDecompNew C) : SignedDecompInputsC C :=
  ⟨fun b i hb => specDecompC_of_new hW hb (specF hW A b) (C.blk b) (paperSpec_scale hW A b)
    (H.an b i hb)⟩

/-- SD2's two-statement hypothesis implies the new one-statement hypothesis. -/
theorem SignedDecompAnalytic2.toNew {C : ComparisonPartsTC hW hMR hFour A}
    (H : SignedDecompAnalytic2 C) : SignedDecompNew C :=
  ⟨fun b i hb => specNew_of_2 hW (specF hW A b) (C.blk b) (H.an b i hb)⟩

end Paper

end Sarkozy.Rebase
