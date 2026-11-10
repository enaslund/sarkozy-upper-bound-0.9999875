module

public import Sarkozy.PrimeGram.Block
public import Sarkozy.PrimeGram.OldDecomp
public import Sarkozy.PrimeGram.OldAB

@[expose] public section

/-!
# `SGp` with the reference decomposition proved up to `lem:record:conditional-collision`(d) (PG)

The field `old` of `DecompAt` (`lem:old-f-law`(f)) is now a theorem
(`oldDecomp_of_inputs` with `abBound`), given only the collision bound
`lem:record:conditional-collision`(d) at every prime of the block:

* `eoP pr ccol i`: the paper's `e_o = r_o + n_o` (`eq:signed-constants`) at `(1/p_i, p_i^{-1/2})`,
  with W6's `Γ ≤ Γ_A` and the collision constant `c_col(i)`;
* **`oldDecomp_block`**: `OldDecomp (mP hne i) (oldP hne i) (eoP pr ccol i)` from
  `CollisionBound`;
* **`DecompAtC`** (hypotheses: `CollisionBound`, `NewDecomp`, the component norms);
  **`DecompAtC.toDecompAt`**;
* **`SpecDecompC`**, **`SignedDecompInputsC`**, **`SignedDecompInputsC.toPrime`**: a constructor of
  SGA's `SignedPrimeInputs` (the field `SGp` of `main_goal_f1i`).
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.PrimeGram

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.MiddleComparison Sarkozy.SignedComponents Sarkozy.MiddleRefinement
open Sarkozy.Labellings Sarkozy.FirstStagePaper Sarkozy.IndexSupport Sarkozy.SignedEstimates
open Sarkozy.SignedGram Sarkozy.Envelopes
open Sarkozy.PartVLaws (PaperBlockSpec blockPrimes paperAtomMap)
open Sarkozy.MainFinal2 (tPaper tPaper_nonneg tPaper_le_one)
open Sarkozy.MainFinalF1 (bOf Blk SignedSpec)

theorem eoC_nonneg {q r e Γ ccol : ℝ} (hq : 0 < q) (hq19 : q ≤ 1 / 19) (hr : 0 ≤ r)
    (he0 : 0 ≤ e) (he1 : e < 1) (hΓ : 0 ≤ Γ) (hc : 0 ≤ ccol) : 0 ≤ eoC q r e Γ ccol := by
  have h1 : 0 < 1 - q := by linarith
  have h2 : 0 < 1 - 2 * q := by linarith
  have h14 : 0 < 1 - 14 * q := by linarith
  have h1e : 0 < 1 - e := by linarith
  have hcg : 0 ≤ cgC e := sq_nonneg _
  have hDg : 0 ≤ DgC e := by unfold DgC; positivity
  have hro : 0 ≤ roC q r e Γ ccol := by unfold roC; positivity
  unfold eoC noC
  positivity

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ} [∀ i, Fact (pr i).Prime]

variable (pr) in
/-- **The paper's `e_o`** (`eq:signed-constants`) at `(1/p_i, p_i^{-1/2})`, with W6's `Γ ≤ Γ_A`
and the collision constant `c_col(i)`. -/
noncomputable def eoP (ccol : ι → ℝ) (i : ι) : ℝ :=
  eoC (pr i : ℝ)⁻¹ (rP pr i) (e0 (pr i : ℝ)) (gammaP pr i) (ccol i)

omit [Fintype ι] [DecidableEq ι] in
/-- **`lem:old-f-law`(f) at every prime of a middle block**, from
`lem:record:conditional-collision`(d) (`CollisionBound`; `lem:old-f-law`(b)(ii) is `abBound`). -/
theorem oldDecomp_block (hne : MiddleNonempty pr) (h3 : ∀ i, pr i % 4 = 3)
    (h19 : ∀ i, 19 ≤ pr i) {ccol : ι → ℝ} (i : ι) (hcol : CollisionBound (hne.F2 i) (ccol i)) :
    OldDecomp (mP hne i) (oldP hne i) (eoP pr ccol i) := by
  obtain ⟨hR, h3', h19'⟩ := primeHyps h3 h19 i
  have h := oldDecomp_of_inputs (hne.F2 i) hR h3' h19' (abBound hR h3' h19') hcol
  rw [card_zmod] at h
  exact h

variable (pr) in
/-- **The prime inputs of a middle block, with the reference decomposition proved** (hypotheses,
constants per prime):
* `col`: `lem:record:conditional-collision`(d), the operator of `𝖢_rem` on the `m₀`-centred
  functions of `L²(m₀)` has norm at most `c_col q`;
* `new`: `prop:signed-bounds`(c), `Π_⊥ T' Π_⊥ = O₀ + L^m_t + R^new` with `‖R^new‖ ≤ e_sg q`;
* `comp`: `prop:signed-bounds`(c), `‖Π_⊥ T[P_{c,p}] Π_⊥‖ ≤ c_+ r`;
* the constants are nonnegative. -/
structure DecompAtC (hne : MiddleNonempty pr) (C : FoldComponents pr hne) (ccol esg cp : ι → ℝ) :
    Prop where
  col : ∀ i, CollisionBound (hne.F2 i) (ccol i)
  new : ∀ i, NewDecomp (mP hne i) (∑ c, signedCoef tPaper c • compP hne C c i) tPaper (esg i)
  comp : ∀ c i, CentredNorm (mP hne i) (compP hne C c i) (cp i * rP pr i)
  ccol_nonneg : ∀ i, 0 ≤ ccol i
  esg_nonneg : ∀ i, 0 ≤ esg i
  cp_nonneg : ∀ i, 0 ≤ cp i

omit [Fintype ι] [DecidableEq ι] in
theorem eoP_nonneg (h19 : ∀ i, 19 ≤ pr i) {ccol : ι → ℝ} (hc : ∀ i, 0 ≤ ccol i) (i : ι) :
    0 ≤ eoP pr ccol i := by
  have h19' : (19 : ℝ) ≤ pr i := by exact_mod_cast h19 i
  have hq : (0 : ℝ) < (pr i : ℝ)⁻¹ := inv_pos.mpr (by linarith)
  have hq19 : (pr i : ℝ)⁻¹ ≤ 1 / 19 := by
    rw [← one_div]; exact one_div_le_one_div_of_le (by norm_num) h19'
  have h19z : 19 ≤ Fintype.card (ZMod (pr i)) := by rw [ZMod.card]; exact h19 i
  have he1 := e0_lt_one (F := ZMod (pr i)) h19z
  have he0 := e0_nonneg (F := ZMod (pr i)) h19z
  rw [ZMod.card] at he1 he0
  exact eoC_nonneg hq hq19 (inv_nonneg.mpr (Real.sqrt_nonneg _)) he0 he1 (gammaP_nonneg h19 i)
    (hc i)

omit [Fintype ι] [DecidableEq ι] in
/-- **`DecompAt` from `DecompAtC`**, with `e_o = eoP` (`oldDecomp_block`). -/
theorem DecompAtC.toDecompAt {hne : MiddleNonempty pr} {C : FoldComponents pr hne}
    {ccol esg cp : ι → ℝ} (h3 : ∀ i, pr i % 4 = 3) (h19 : ∀ i, 19 ≤ pr i)
    (D : DecompAtC pr hne C ccol esg cp) : DecompAt pr hne C (eoP pr ccol) esg cp where
  old i := oldDecomp_block hne h3 h19 i (D.col i)
  new := D.new
  comp := D.comp
  eo_nonneg := eoP_nonneg h19 D.ccol_nonneg
  esg_nonneg := D.esg_nonneg
  cp_nonneg := D.cp_nonneg

end Block

section Paper

variable (hW : Target.Weil) (In : FirstStageInputs bOf)

/-- **The collision bound, the signed decomposition, the component norms and the gates of a
middle block** at the shift `σ = r d / H_𝔅` (`e_o` the paper's, `eoP`). -/
def DecompGateAtC {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
    (hne : MiddleNonempty pr) (C : FoldComponents pr hne) (r d : ℝ) : Prop :=
  ∃ ccol esg cp : ι → ℝ, DecompAtC pr hne C ccol esg cp ∧
    GateAt pr (eoP pr ccol) esg cp (r * d / Hblock pr)

theorem decompGateAt_of_C {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ}
    [∀ i, Fact (pr i).Prime] {hne : MiddleNonempty pr} {C : FoldComponents pr hne} {r d : ℝ}
    (h3 : ∀ i, pr i % 4 = 3) (h19 : ∀ i, 19 ≤ pr i) (h : DecompGateAtC pr hne C r d) :
    DecompGateAt pr hne C r d := by
  obtain ⟨ccol, esg, cp, D, G⟩ := h
  exact ⟨eoP pr ccol, esg, cp, D.toDecompAt h3 h19, G⟩

/-- **`DecompGateAtC` at a class-three block of the F1 data**, by specification. `True` on an upper
block. -/
def SpecDecompC {b : Blk} (d : ℝ) : (S : PaperBlockSpec bOf b) → SignedSpec hW S → Prop
  | .upper _, _ => True
  | .middleUniform M, E =>
      DecompGateAtC (blockPrimes bOf b) M.hne (paperComponents E.down.toDC) (frameU In M).r d
  | .middleIndividual M, E =>
      DecompGateAtC (blockPrimes bOf b) M.hne (paperComponents E.down.toDC) (frameI In M).r d
  | .middleCoherent M, E =>
      DecompGateAtC (blockPrimes bOf b) M.hne (paperComponents E.down.toDC) (frameC In M).r d

theorem specDecomp_of_C {b : Blk} {d : ℝ} :
    (S : PaperBlockSpec bOf b) → (E : SignedSpec hW S) → SpecDecompC hW In d S E →
      SpecDecomp hW In d S E
  | .upper _, _, _ => trivial
  | .middleUniform _, _, h => decompGateAt_of_C (fun i => (blockPrimes_mod_ge b i).1)
      (blockPrimes_ge19 b) h
  | .middleIndividual _, _, h => decompGateAt_of_C (fun i => (blockPrimes_mod_ge b i).1)
      (blockPrimes_ge19 b) h
  | .middleCoherent _, _, h => decompGateAt_of_C (fun i => (blockPrimes_mod_ge b i).1)
      (blockPrimes_ge19 b) h

end Paper

section Main

open Sarkozy.BlockSpecPaper
open Sarkozy.AnalyticCells (f1Cell)
open Sarkozy.MainFinalF1 (specF analyticInputs)
open Sarkozy.MainFinalF1c (ComparisonPartsTC)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {A : PaperAnalyticInputs f1Cell}

/-- **The remaining prime inputs at every middle block** of the F1 data, at the paper's side
`paperSide i`: `lem:record:conditional-collision`(d), `prop:signed-bounds`(c) (signed record and
components) and the gates. 1 field. *Hypothesis*. -/
structure SignedDecompInputsC (C : ComparisonPartsTC hW hMR hFour A) : Prop where
  decomp : ∀ b i, blockSite b = .inl i →
    SpecDecompC hW (paperIn f1Cell) (paperSide i) (specF hW A b) (C.blk b)

theorem SignedDecompInputsC.toDecomp {C : ComparisonPartsTC hW hMR hFour A}
    (G : SignedDecompInputsC C) : SignedDecompInputs C where
  decomp b i hb := specDecomp_of_C hW (paperIn f1Cell) (specF hW A b) (C.blk b) (G.decomp b i hb)

/-- **A constructor of SGA's `SignedPrimeInputs`** (the field `SGp` of `main_goal_f1i`) from the
collision bound, the signed decomposition, the component norms and the gates. -/
theorem SignedDecompInputsC.toPrime {C : ComparisonPartsTC hW hMR hFour A}
    (G : SignedDecompInputsC C) : SignedPrimeInputs C :=
  G.toDecomp.toPrime

end Main

end Sarkozy.PrimeGram
