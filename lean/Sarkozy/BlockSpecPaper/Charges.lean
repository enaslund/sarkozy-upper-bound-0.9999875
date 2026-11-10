module

public import Sarkozy.BlockSpecPaper.Main

@[expose] public section

/-!
# `hB` from the per-piece block charges (`lem:record:middle-prices`, `lem:record:block-charge`)

`paper/sections/20_middle_reference.tex`, `lem:record:block-charge` (closing sentence) and
`subsec:middle-frame-prices`; `lem:record:middle-prices`.

For the constructed specification, the price bound of a middle block of piece `i` is
`(U₂(i) r² + U₃(i) r³) q_𝔅^{2a}` with `r = b_𝔅^{-1/2}` and the ALLp constants
`U₂(i) = 2 v_D`, `U₃(i) = 2 v_D (f₁ + h₁) + 12 w_S/(1 - 3/X_i)` (`chargeU2`, `chargeU3`); it is `0`
on an upper block (`paperSpec_ubound`). Summed over the blocks and grouped by piece
(`sum_paperSpec_ubound`):
`∑_𝔅 specUbound = ∑_i (U₂(i) b₂(i) + U₃(i) b₃(i))`, with the block charges
`b_d(i) = ∑_{𝔅 ⊆ piece i} b_𝔅^{-d/2} q_𝔅^{2a}` (`blockCharge`), the paper's `b_d(X,Y)`.

**`hB_of_blockCharges`**: if `b_d(i) ≤ c_d(i)` for `d = 2, 3` on every piece, the first-stage tag
sums are at most `d'`, `v'`, and `e^{∑_i (U₂(i) c₂(i) + U₃(i) c₃(i))} (1 + 𝔗(d', v')) ≤ B^{ledger}`,
then `hB` holds. This is the form of the ledger's `U₀ = ∑_i (U0_2 I₂ + U0_3 I₃)` (the native
`charges` of the pieces); the charges `b_d(i)` are bounded by M2's `piece_charge_le` for the paper's
partition.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.BlockSpecPaper

open Sarkozy.PartV Sarkozy.CancellationSteps Sarkozy.PartVLaws Sarkozy.FirstStagePaper
  Sarkozy.GramBracketPaper Sarkozy.MainTarget Sarkozy.RecordExpansion
open Sarkozy.TargetLedger (targetDecay targetLedger)

/-- `U₂(i) = 2 v_D` (the coefficient `U0_2` of the piece, `β = 1`). -/
noncomputable def chargeU2 (i : Fin 33) : ℝ := 2 * (allpWeights i).v .D

/-- `U₃(i) = 2 v_D (f₁ + h₁) + 12 w_S/(1 - 3/X_i)` (the coefficient `U0_3` of the piece, with the
polarization coefficient `f₁ + h₁`). -/
noncomputable def chargeU3 (i : Fin 33) : ℝ :=
  2 * (allpWeights i).v .D * ((allpInputs i).f₁ + (allpInputs i).h₁) +
    12 * (allpWeights i).w .S / (1 - 3 / (pieceStart i : ℝ))

theorem chargeU2_nonneg (i : Fin 33) : 0 ≤ chargeU2 i :=
  mul_nonneg (by norm_num) ((allpWeights i).v_nonneg _)

theorem chargeU3_nonneg (i : Fin 33) : 0 ≤ chargeU3 i := by
  have hX : (3 : ℝ) < pieceStart i := by
    have h := pieceStart_ge_Q3 i
    have h' : (3 : ℕ) < pieceStart i := lt_of_lt_of_le (by norm_num [Q3]) h
    exact_mod_cast h'
  have h1 : 0 < 1 - 3 / (pieceStart i : ℝ) := by
    rw [sub_pos, div_lt_one (by linarith)]
    exact hX
  have hn := allpInputs_nonneg i
  have hv := (allpWeights i).v_nonneg .D
  have hw := (allpWeights i).w_nonneg .S
  have hf := add_nonneg hn.2.2.1 hn.2.2.2.2.1
  unfold chargeU3
  exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hv) hf)
    (div_nonneg (mul_nonneg (by norm_num) hw) h1.le)

variable {cell : ℕ → ℕ}

/-- The price bound at a site: `(U₂ r² + U₃ r³) x` at piece `i`, `0` at a band. -/
noncomputable def siteUbound (b : PaperBlock cell) (x : ℝ) : Site → ℝ
  | .inl i => (chargeU2 i * blockScale b ^ 2 + chargeU3 i * blockScale b ^ 3) * x
  | .inr _ => 0

/-- The price bound of a block of the constructed specification: `(U₂ r² + U₃ r³) x` on a block
of piece `i`, `0` on an upper block. -/
noncomputable def blockUbound (b : PaperBlock cell) (x : ℝ) : ℝ := siteUbound b x (blockSite b)

theorem middleSpec_ubound (hW : Target.Weil) (A : PaperAnalyticInputs cell) (b : PaperBlock cell)
    (i : Fin 33) (hs : blockSite b = .inl i) (x : ℝ) :
    ∀ o hu, specUbound (paperIn cell) (middleSpec hW A b i hs o hu) x =
      (chargeU2 i * blockScale b ^ 2 + chargeU3 i * blockScale b ^ 3) * x := by
  have hX : (paperIn cell).X b = pieceStart i := by
    change ((siteStart (blockSite b) : ℕ) : ℝ) = _
    rw [hs]
    rfl
  intro o hu
  cases o with
  | none =>
    change (2 * (allpWeights i).v .D * blockScale b ^ 2 + (2 * (allpWeights i).v .D *
      ((allpInputs i).f₁ + (allpInputs i).h₁) + 12 * (allpWeights i).w .S /
        (1 - 3 / (paperIn cell).X b)) * blockScale b ^ 3) * x = _
    rw [hX]
    unfold chargeU2 chargeU3
    ring
  | some u =>
    change (2 * (allpWeights i).v .D * blockScale b ^ 2 + (2 * (allpWeights i).v .D *
      ((allpInputs i).f₁ + (allpInputs i).h₁) + 12 * (allpWeights i).w .S /
        (1 - 3 / (paperIn cell).X b)) * blockScale b ^ 3) * x = _
    rw [hX]
    unfold chargeU2 chargeU3
    ring

theorem siteSpec_ubound (hW : Target.Weil) (A : PaperAnalyticInputs cell) (b : PaperBlock cell)
    (x : ℝ) : ∀ s (hs : blockSite b = s),
      specUbound (paperIn cell) (siteSpec hW A b s hs) x = siteUbound b x s
  | .inl i, hs => middleSpec_ubound hW A b i hs x _ rfl
  | .inr _, _ => rfl

/-- **The price bound of a block of the constructed specification** (`lem:record:middle-prices`). -/
theorem paperSpec_ubound (hW : Target.Weil) (A : PaperAnalyticInputs cell) (b : PaperBlock cell)
    (x : ℝ) : specUbound (paperIn cell) (paperSpec hW A b) x = blockUbound b x :=
  siteSpec_ubound hW A b x _ rfl

/-- **The block charge** `b_d(i) = ∑_{𝔅 ⊆ piece i} r_𝔅^d f(𝔅)` (`r_𝔅 = b_𝔅^{-1/2}`; with
`f(𝔅) = q_𝔅^{2a}` this is the paper's `b_d(X_i, X_{i+1})`, `lem:record:block-charge`). -/
noncomputable def blockCharge (f : PaperBlock cell → ℝ) (d : ℕ) (i : Fin 33) : ℝ :=
  ∑ b ∈ univ.filter (fun b : PaperBlock cell => blockSite b = .inl i), blockScale b ^ d * f b

/-- **Grouping by piece**: `∑_𝔅 specUbound = ∑_i (U₂(i) b₂(i) + U₃(i) b₃(i))`. -/
theorem sum_paperSpec_ubound (hW : Target.Weil) (A : PaperAnalyticInputs cell)
    (f : PaperBlock cell → ℝ) :
    ∑ b, specUbound (paperIn cell) (paperSpec hW A b) (f b) =
      ∑ i : Fin 33, (chargeU2 i * blockCharge f 2 i + chargeU3 i * blockCharge f 3 i) := by
  have hb : ∀ b : PaperBlock cell, blockUbound b (f b) = ∑ i : Fin 33,
      if blockSite b = .inl i then
        (chargeU2 i * blockScale b ^ 2 + chargeU3 i * blockScale b ^ 3) * f b else 0 := by
    intro b
    unfold blockUbound
    rcases h : blockSite b with i | k
    · simp only [siteUbound, Sum.inl.injEq]
      rw [Finset.sum_ite_eq]
      simp
    · simp [siteUbound]
  simp_rw [paperSpec_ubound, hb]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_filter]
  unfold blockCharge
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- `r_𝔅² = b_𝔅⁻¹`. -/
theorem blockScale_sq (b : PaperBlock cell) : blockScale b ^ 2 = (blockLeast b : ℝ)⁻¹ := by
  have h := blockScale_sq_mul b
  have hb := blockLeast_pos b
  field_simp
  linarith

/-- `r_𝔅³ = b_𝔅^{-3/2}`. -/
theorem blockScale_cube (b : PaperBlock cell) :
    blockScale b ^ 3 = (blockLeast b : ℝ) ^ (-(3 / 2 : ℝ)) := by
  unfold blockScale
  rw [← Real.rpow_natCast, ← Real.rpow_mul (blockLeast_pos b).le]
  have h : (-(1 / 2 : ℝ)) * ((3 : ℕ) : ℝ) = -(3 / 2) := by norm_num
  rw [h]

/-- **`hB` from the per-piece block charges** (`lem:record:middle-prices`,
`lem:record:block-charge`, `def:closing-quantities`): A2's `hB_of_charges` with the sum over the
blocks grouped into the piece charges `b₂(i)`, `b₃(i)` (with `f(𝔅) = q_𝔅^{2a}` at `a_T`). -/
theorem hB_of_blockCharges {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
    {A : PaperAnalyticInputs cell} (D : B1BlockDataTarget cell hW hMR hFour A)
    {c₂ c₃ : Fin 33 → ℝ} {d' v' : Fin 2 → ℝ}
    (h₂ : ∀ i, blockCharge
      (fun b => paperSelAt (paperAtomMap (paperBlockOf cell)) targetDecay (.inr b)) 2 i ≤ c₂ i)
    (h₃ : ∀ i, blockCharge
      (fun b => paperSelAt (paperAtomMap (paperBlockOf cell)) targetDecay (.inr b)) 3 i ≤ c₃ i)
    (hd : ∀ j, ∑ β, (paperStage (paperBlockOf cell) hW (paperSpec hW A)
      (TailCorrCore.tailInputsCorr hW hMR hFour) (paperIn cell) β).dTag
      (paperSelAt (paperAtomMap (paperBlockOf cell)) targetDecay β) j ≤ d' j)
    (hv : ∀ j, ∑ β, (paperStage (paperBlockOf cell) hW (paperSpec hW A)
      (TailCorrCore.tailInputsCorr hW hMR hFour) (paperIn cell) β).vTag
      (paperSelAt (paperAtomMap (paperBlockOf cell)) targetDecay β) j ≤ v' j)
    (hcost : Real.exp (∑ i : Fin 33, (chargeU2 i * c₂ i + chargeU3 i * c₃ i)) *
      (1 + tagSeries d' v') ≤ targetLedger.B) :
    D.toA2.toA1.toV2.toCertData.toData.B ≤ targetLedger.B := by
  refine hB_of_charges_B1 D ?_ hd hv hcost
  rw [sum_paperSpec_ubound hW A (fun b =>
    paperSelAt (paperAtomMap (paperBlockOf cell)) targetDecay (.inr b))]
  exact Finset.sum_le_sum fun i _ => add_le_add
    (mul_le_mul_of_nonneg_left (h₂ i) (chargeU2_nonneg i))
    (mul_le_mul_of_nonneg_left (h₃ i) (chargeU3_nonneg i))

end Sarkozy.BlockSpecPaper
