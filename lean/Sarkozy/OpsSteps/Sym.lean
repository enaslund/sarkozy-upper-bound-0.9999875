module

public import Sarkozy.OpsSteps.SymSplit
public import Sarkozy.OpsSteps.QMain

@[expose] public section

/-!
# The improved bound `hsym` of Step 3, reduced to the category `e_s` (OPS-S)

`paper/sections/23_envelopes.tex`, `lem:orbit-coupon`(i) and its proof.

The input `hsym` of `Step3.step3_orbit` is the bound
`|Y^Ñ[κ̄] − Y^{Ñ₀}[κ̄]| ≤ (R_err − e^{tU} tδ + z') C_X Y + r` at the `R_h`-invariant orbit averages
`κ̄ = ½([C] + [hC])`. The paper proves it by changing one category of the sharp-first expansion, the
count vector `e_s` (exactly one record difference, of tag `s`); "the other categories keep their
bounds". This file formalizes that structure:

* `Eσ`: the sharp term `σ` with the tensor `Q` on `S` (B9's `sharpPiece`);
* **`diff_tensor_eq_sum`**, **`diff_avg_eq_sum`**: `Y^Ñ[⊗Q] − Y^{Ñ₀}[⊗Q] = ∑_{σ≠∅} E_σ(Q)`, and the
  same for the average of two tensors;
* **`hsym_of_category`**: the bound of `hsym` from **one** input, the improved bound of the category
  `e_s`, `|∑_{σ ∈ e_s} Ē_σ| ≤ K (d_s e^{U₀} − e^{tU} tδ) + r_sym`. The other categories are bounded
  by the canonical remainders `rCan` (`hterm_rCan`, already summed by `QMain.rCan_class_sum`),
  `e^P (𝔗 − d_s) ≤ e^{U₀} (𝔗(d_T, v_T) − d_{T,s})` (`tagSeries_sub_mono`, `tagMin_single`), and
  `R_err = e^{U₀} 𝔗(d_T, v_T)`;
* **`jointEnergy_slotPush_both`**, **`sym_swap`**: the first step of the paper's proof of the
  improvement: for an `R_h`-invariant law on `S` and outside factors that are `R_h`-invariant except
  at the atom `𝔅'` of the difference, `Y_{κ̄ ⊗ δ ⊗ O} = Y_{κ̄ ⊗ R_{h*}δ ⊗ O}`, so `δ` may be
  replaced by its symmetric part `½(δ + R_{h*}δ)` (`rem:cut-symmetries`(a) in the paper; here the
  invariance of the energy under a slot permutation, `lem:reflection-averaging`(c)).

What remains of `hsym` is the category bound itself: the symmetric part has the sharp bound
`s_fold(X) b^{-1}` (`lem:record:one-stage-folded-e`(e)), which charges the `G`-free terms with the
symmetric price; the terms with `G` keep the sharp price; and the polynomial evaluation with the
chosen prices of `lem:oct24:invariant-background`(v).
-/

namespace Sarkozy.OpsSteps

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeSteps Sarkozy.Envelopes
  Sarkozy.BlockFrame Sarkozy.TheoremC Sarkozy.Comparison Sarkozy.RecordExpansion
  Sarkozy.RecordExpansion.Choice

/-! ## Energies of a joint law under a slot permutation -/

section Swap

variable {V : Type*} [Fintype V] [DecidableEq V]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- **The energy of a joint law is invariant under a slot permutation of both factors.** -/
theorem jointEnergy_slotPush_both (α : V ≃ V) (κ : ((V → A) → ℝ) →ₗ[ℝ] ℝ)
    (Ob : ((V → B) → ℝ) →ₗ[ℝ] ℝ) (F : (∀ b, pairFam A B b) → ℝ) :
    jointEnergy (slotPush α κ) (slotPush α Ob) F = jointEnergy κ Ob F := by
  unfold jointEnergy
  have e : pairLaws (slotPush α κ) (slotPush α Ob) = fun b => slotPush α (pairLaws κ Ob b) := by
    funext b
    cases b <;> rfl
  rw [e, ← slotPush_tensorLaw, diagonalIntegral_slotPush]

/-- **The difference may be reflected** (the first step of the improvement in
`lem:orbit-coupon`(i)): if the law `κ` on the selected blocks is `α`-invariant and the outside
factors `O_𝔟` are `α`-invariant except at `𝔅'`, then `Y_{κ ⊗ O} = Y_{κ ⊗ O'}`, where `O'` has
`α_* O_{𝔅'}` at `𝔅'`. -/
theorem sym_swap {Jo : Type} [Fintype Jo] [DecidableEq Jo] {Xo : Jo → Type}
    [∀ b, Fintype (Xo b)] [∀ b, DecidableEq (Xo b)] (α : V ≃ V) (κ : ((V → A) → ℝ) →ₗ[ℝ] ℝ)
    (hκ : slotPush α κ = κ) (Lo : ∀ b, ((V → Xo b) → ℝ) →ₗ[ℝ] ℝ) (b' : Jo)
    (hO : ∀ b, b ≠ b' → slotPush α (Lo b) = Lo b)
    (F : (∀ t, pairFam A (∀ b, Xo b) t) → ℝ) :
    jointEnergy κ (tensorLaw Lo) F =
      jointEnergy κ (tensorLaw fun b => if b = b' then slotPush α (Lo b) else Lo b) F := by
  have h := slotPush_tensor_invariant α Lo {b'} (fun b hb => hO b (by simpa using hb))
  simp only [mem_singleton] at h
  rw [← h, ← jointEnergy_slotPush_both α κ, hκ]

end Swap

/-! ## The sharp-first expansion of a tensor at the paper's data -/

section Paper

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ) (A : Finset ℤ)
  (S : Finset (BlockAtom Bk J L))

/-- The sharp term `σ` with the tensor `Q` on `S`. -/
noncomputable def Eσ (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (σ : ∀ b, Option (D.FS.Ib L b)) : ℝ :=
  diagonalIntegral (tensorLaw (sharpPiece D L Qb (fun b => decide (b ∈ S)) σ))
    (blockLift m₀ blk p L A)

omit [DecidableEq P] in
/-- **The sharp-first expansion of `Y^Ñ − Y^{Ñ₀}` at a tensor on `S`**. -/
theorem diff_tensor_eq_sum (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) :
    paperEN D L A S (tensorLaw fun b : {b // b ∈ S} => Qb b.1) -
        paperEN0 D L A S (tensorLaw fun b : {b // b ∈ S} => Qb b.1) =
      ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        Eσ D L A S Qb σ := by
  rw [paperEN_tensor, paperEN0_tensor]
  set Ab : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b :=
    fun b => if decide (b ∈ S) then Qb b else D.GB.N₀ L b
  set Db : ∀ b, D.FS.Ib L b → TheoremCBlock.AtomMeasure m₀ blk p L b :=
    fun b i => if decide (b ∈ S) then 0 else D.FS.κ' L b i - D.FS.κ L b i
  have hN : (fun b => if decide (b ∈ S) then Qb b else D.GB.N L b) =
      fun b => Ab b + ∑ i, Db b i := by
    funext b
    by_cases hb : b ∈ S
    · simp [Ab, Db, hb]
    · simp only [Ab, Db, hb, decide_false, Bool.false_eq_true, ↓reduceIte]
      rfl
  rw [hN, ← diagonalIntegral_sub, tensorLaw_add_sum_sub_eq, diagonalIntegral_sum]
  rfl

omit [DecidableEq P] in
/-- **The same for the average of two tensors** (an orbit average `½([C] + [hC])`). -/
theorem diff_avg_eq_sum (Q₁ Q₂ : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) :
    paperEN D L A S ((1 / 2 : ℝ) • (tensorLaw (fun b : {b // b ∈ S} => Q₁ b.1) +
        tensorLaw (fun b : {b // b ∈ S} => Q₂ b.1))) -
      paperEN0 D L A S ((1 / 2 : ℝ) • (tensorLaw (fun b : {b // b ∈ S} => Q₁ b.1) +
        tensorLaw (fun b : {b // b ∈ S} => Q₂ b.1))) =
      ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        (1 / 2 : ℝ) * (Eσ D L A S Q₁ σ + Eσ D L A S Q₂ σ) := by
  have h1 := diff_tensor_eq_sum D L A S Q₁
  have h2 := diff_tensor_eq_sum D L A S Q₂
  simp only [map_smul, map_add, smul_eq_mul]
  rw [← mul_sum, sum_add_distrib, ← h1, ← h2]
  ring

omit [DecidableEq P] in
/-- **`hsym` from the improved bound of the category `e_s`** (`lem:orbit-coupon`(i)). For the
orbit average of two tensors `Q₁`, `Q₂` on `S` (probability laws with uniform one-slot marginals at
the selected blocks of `ω`, `S = supp ω`), with `K = (1 + ε) C_X Y`:

* the categories other than `e_s` are bounded by the canonical remainders `rCan` (no input);
* `hcat`: the category `e_s` (one difference, of tag `s`) of the average satisfies
  `|∑_{σ ∈ e_s} Ē_σ| ≤ K (d_{T,s} e^{U₀} − e^{tU} tδ) + r_sym` (**the remaining input**, C).

Then `|Y^Ñ[κ̄] − Y^{Ñ₀}[κ̄]| ≤ (R_err − e^{tU} tδ) K + ∑_σ ½(rCan₁ + rCan₂) + r_sym`. -/
theorem hsym_of_category (εE : ℕ → ℝ) (hε0 : ∀ L, 0 ≤ εE L) (hY : 0 ≤ D.Y L A)
    (ω : Choice (D.CL.T L)) (Q₁ Q₂ : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (s : D.FS.Tag) {tU tδ rsym : ℝ}
    (hcat : |∑ σ ∈ (univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)).filter
        (fun σ => countVec (D.FS.tag L) σ = Pi.single s 1),
        (1 / 2 : ℝ) * (Eσ D L A (Choice.support ω) Q₁ σ + Eσ D L A (Choice.support ω) Q₂ σ)| ≤
      ((1 + εE L) * (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
          D.Y L A) * (D.FS.dT s * Real.exp D.GB.U₀ - Real.exp tU * tδ) + rsym) :
    |paperEN D L A (Choice.support ω) ((1 / 2 : ℝ) •
        (tensorLaw (fun b : {b // b ∈ Choice.support ω} => Q₁ b.1) +
          tensorLaw (fun b : {b // b ∈ Choice.support ω} => Q₂ b.1))) -
      paperEN0 D L A (Choice.support ω) ((1 / 2 : ℝ) •
        (tensorLaw (fun b : {b // b ∈ Choice.support ω} => Q₁ b.1) +
          tensorLaw (fun b : {b // b ∈ Choice.support ω} => Q₂ b.1)))| ≤
      (D.GB.Rerr - Real.exp tU * tδ) *
          ((1 + εE L) * (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
            D.Y L A) +
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          (1 / 2 : ℝ) * (rCan D L A (Choice.support ω) Q₁
              ((1 + εE L) *
                (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
                D.Y L A) σ +
            rCan D L A (Choice.support ω) Q₂
              ((1 + εE L) *
                (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
                D.Y L A) σ) + rsym := by
  set S := Choice.support ω with hSdef
  set K := (1 + εE L) * (∏ b ∈ S, TheoremCBlock.selectionFactor a p D.S.selPre L b) * D.Y L A
    with hKdef
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (by linarith [hε0 L])
    (prod_nonneg fun b _ => D.selectionFactor_nonneg L b)) hY
  set ne := univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)
  set r : (∀ b, Option (D.FS.Ib L b)) → ℝ := fun σ =>
    (1 / 2 : ℝ) * (rCan D L A S Q₁ K σ + rCan D L A S Q₂ K σ) with hr
  have hr0 : ∀ σ, 0 ≤ r σ := fun σ => mul_nonneg (by norm_num)
    (add_nonneg (rCan_nonneg D L A S Q₁ K σ) (rCan_nonneg D L A S Q₂ K σ))
  set pp : BlockAtom Bk J L → ℝ := fun b => if decide (b ∈ S) then 0 else D.GB.uprice L b
  have hpp : ∀ b, 0 ≤ pp b := fun b => by
    show 0 ≤ if decide (b ∈ S) then 0 else D.GB.uprice L b
    split_ifs
    · exact le_rfl
    · exact uprice_nonneg D L b
  rw [diff_avg_eq_sum]
  have hsplit := abs_sum_le_tagSeries_split (D.FS.tag L) (fun b i => D.dprice_nonneg L b i)
    (fun b i => D.vprice_nonneg L b i) hpp hK
    (fun σ => (1 / 2 : ℝ) * (Eσ D L A S Q₁ σ + Eσ D L A S Q₂ σ)) r (Pi.single s 1)
    (fun σ hσ _ j hj => by
      have h1 := hterm_rCan D L A S Q₁ K σ hσ j hj
      have h2 := hterm_rCan D L A S Q₂ K σ hσ j hj
      change |(1 / 2 : ℝ) * (Eσ D L A S Q₁ σ + Eσ D L A S Q₂ σ)| ≤ _
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      have h3 := abs_add_le (Eσ D L A S Q₁ σ) (Eσ D L A S Q₂ σ)
      change |Eσ D L A S Q₁ σ| ≤ _ at h1
      change |Eσ D L A S Q₂ σ| ≤ _ at h2
      simp only [hr]
      linarith)
  -- the series: `e^P (𝔗 − 𝔗_{e_s}) ≤ e^{U₀} (𝔗(d_T, v_T) − d_{T,s})`
  have hd' : ∀ j, 0 ≤ tagTotal (D.FS.tag L) (D.FS.dprice L) j :=
    fun j => sum_nonneg fun b _ => sum_nonneg fun i _ => by
      split_ifs
      · exact D.dprice_nonneg L b i
      · exact le_rfl
  have hv' : ∀ j, 0 ≤ tagTotal (D.FS.tag L) (D.FS.vprice L) j :=
    fun j => sum_nonneg fun b _ => sum_nonneg fun i _ => by
      split_ifs
      · exact D.vprice_nonneg L b i
      · exact le_rfl
  have hdT : ∀ j, tagTotal (D.FS.tag L) (D.FS.dprice L) j ≤ D.FS.dT j :=
    fun j => D.FS.dT_total L j
  have hvT : ∀ j, tagTotal (D.FS.tag L) (D.FS.vprice L) j ≤ D.FS.vT j :=
    fun j => D.FS.vT_total L j
  have hmono := tagSeries_sub_mono hd' hv' hdT hvT (Pi.single s 1)
  rw [tagMin_single D.FS.dT D.FS.vT s] at hmono
  have hrest0 : 0 ≤ tagSeries (tagTotal (D.FS.tag L) (D.FS.dprice L))
      (tagTotal (D.FS.tag L) (D.FS.vprice L)) -
      tagMin (tagTotal (D.FS.tag L) (D.FS.dprice L)) (tagTotal (D.FS.tag L) (D.FS.vprice L))
        (Pi.single s 1) := by
    have := sum_tagMin_le_tagSeries hd' hv' {Pi.single s 1}
    rw [sum_singleton] at this
    linarith
  have hP : ∑ b, pp b ≤ D.GB.U₀ := by
    refine le_trans (sum_le_sum fun b _ => ?_) (sum_uprice_le D L)
    show (if decide (b ∈ S) then 0 else D.GB.uprice L b) ≤ D.GB.uprice L b
    split_ifs
    · exact uprice_nonneg D L b
    · exact le_rfl
  have hexp := Real.exp_le_exp.mpr hP
  have hser : Real.exp (∑ b, pp b) * (tagSeries (tagTotal (D.FS.tag L) (D.FS.dprice L))
      (tagTotal (D.FS.tag L) (D.FS.vprice L)) -
      tagMin (tagTotal (D.FS.tag L) (D.FS.dprice L)) (tagTotal (D.FS.tag L) (D.FS.vprice L))
        (Pi.single s 1)) ≤
      Real.exp D.GB.U₀ * (tagSeries D.FS.dT D.FS.vT - D.FS.dT s) :=
    mul_le_mul hexp hmono hrest0 (Real.exp_pos _).le
  have hKser := mul_le_mul_of_nonneg_left hser hK
  have hrestr : ∑ σ ∈ ne.filter (fun σ => countVec (D.FS.tag L) σ ≠ Pi.single s 1), r σ ≤
      ∑ σ ∈ ne, r σ :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun σ _ _ => hr0 σ
  have hRerr : D.GB.Rerr = Real.exp D.GB.U₀ * tagSeries D.FS.dT D.FS.vT := rfl
  rw [hRerr]
  have e1 : K * (Real.exp (∑ b, pp b) * (tagSeries (tagTotal (D.FS.tag L) (D.FS.dprice L))
      (tagTotal (D.FS.tag L) (D.FS.vprice L)) -
      tagMin (tagTotal (D.FS.tag L) (D.FS.dprice L)) (tagTotal (D.FS.tag L) (D.FS.vprice L))
        (Pi.single s 1))) = K * Real.exp (∑ b, pp b) *
      (tagSeries (tagTotal (D.FS.tag L) (D.FS.dprice L))
        (tagTotal (D.FS.tag L) (D.FS.vprice L)) -
      tagMin (tagTotal (D.FS.tag L) (D.FS.dprice L)) (tagTotal (D.FS.tag L) (D.FS.vprice L))
        (Pi.single s 1)) := by ring
  rw [e1] at hKser
  have hgoal : (Real.exp D.GB.U₀ * tagSeries D.FS.dT D.FS.vT - Real.exp tU * tδ) * K =
      K * (D.FS.dT s * Real.exp D.GB.U₀ - Real.exp tU * tδ) +
        K * (Real.exp D.GB.U₀ * (tagSeries D.FS.dT D.FS.vT - D.FS.dT s)) := by ring
  rw [hgoal]
  linarith

end Paper

end Sarkozy.OpsSteps
