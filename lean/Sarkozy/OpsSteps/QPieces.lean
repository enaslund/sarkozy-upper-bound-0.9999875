module

public import Sarkozy.OpsSteps.QSum
public import Sarkozy.OpsSteps.Coupled

@[expose] public section

/-!
# The coupled pieces with an arbitrary probability law on the support (OPS-S)

`paper/sections/10_comparison_lemmas.tex`, proofs of `lem:bracket-energy` and `lem:sharp-first`;
`paper/sections/23_envelopes.tex`, proof of `lem:orbit-coupon`(i) ("Every `C_k` is an admissible
probability measure. Its difference is bounded as in the proof of `lem:bracket-energy`").

G1's coupled pieces (`ecpieceK`) carry the norm envelope `D^ε_{𝔟,t}` at the selected atoms. Here
they carry an arbitrary family `Q_{𝔟,t,ε}` of probability laws with uniform one-slot marginals (for
Step 3: the placed per-block couplings `[C_𝔟]_{ω(𝔟)}`); the coefficients `ecpieceCoef` and the
prices `ecpieceG` are G1's (they do not involve the law):

* `qK`, `qTerm`, **`qSum_eq`**: the pieces add up to the factor of the sharp term (G1's
  `ecpieceSum_eq` with `Q`);
* `qInt`, `qX`: the energy of a piece and its canonical remainder (EC's `coupInt`, `rX`);
* **`abs_qTerm_le`**: `|E_σ| ≤ (1 + ε)(∏_X q^{2a}) Y wt_j(σ) + ∑_f ∏|c| qX_f` (G1's
  `envelopeBound_terms_of_coupled`, second family, with `Q`);
* `qDom`, `isPositiveRecord_qDom`, `qK_dom`, `mass_qDom`: the dominating positive records;
  **`abs_qInt_le_large`**: the Hölder bound (`lem:record:density-lp`), with the masses of EC's
  `cDom` (the law on the support has mass `1` either way);
* **`qX_le_pieceBnd_large`**: on a large union, `qX_f ≤ pieceBnd` (`QSum.lean`).
-/

namespace Sarkozy.OpsSteps

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.E1Closure Sarkozy.EnvelopeInputsBlock
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame
open Sarkozy.TheoremC Sarkozy.Comparison Sarkozy.PaperFrame Sarkozy.RecordExpansion
  Sarkozy.RecordExpansion.Choice

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
  (Qf : ∀ b : BlockAtom Bk J L, D.CL.T L b → ChangeType → TheoremCBlock.AtomMeasure m₀ blk p L b)

/-- **The coupled pieces with the law `Q` on the support** (G1's `ecpieceK` with `Q` for `D`). -/
noncomputable def qK (ω : Choice (D.CL.T L)) (b : BlockAtom Bk J L) :
    CEPiece D L b → TheoremCBlock.AtomMeasure m₀ blk p L b
  | Sum.inl none => entryFactor (D.R.law p L b) (Qf b) (ω b)
  | Sum.inl (some i) => D.GB.κu L b i
  | Sum.inr (i, none) => D.FS.κ' L b i - D.FS.κ L b i
  | Sum.inr (i, some t) => if t then D.FS.κ' L b i else D.FS.κ L b i

/-- The factor of the sharp term `σ` with `Q` on the support (`Ñ₀ = μ + ∑ κu` off it). -/
noncomputable def qTerm (ω : Choice (D.CL.T L)) (σ : ∀ b, Option (D.FS.Ib L b))
    (b : BlockAtom Bk J L) : TheoremCBlock.AtomMeasure m₀ blk p L b :=
  (σ b).elim (entryFactor (D.R.law p L b) (Qf b) (ω b) +
      (if (ω b).isSome then 0 else ∑ i, D.GB.κu L b i))
    (fun i => if (ω b).isSome then 0 else (D.FS.κ' L b i - D.FS.κ L b i))

omit [DecidableEq P] in
/-- **The pieces add up to the factor of the term** (G1's `ecpieceSum_eq` with `Q`). -/
theorem qSum_eq (ω : Choice (D.CL.T L)) (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag)
    (b : BlockAtom Bk J L) :
    ∑ x, ecpieceCoef D L ω σ j b x • qK D L Qf ω b x = qTerm D L Qf ω σ b := by
  unfold qTerm
  rw [Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_prod_type]
  rcases hσ : σ b with _ | i₀
  · have hinr : ∀ i y, ecpieceCoef D L ω σ j b (Sum.inr (i, y)) = 0 := by
      intro i y
      rcases y with _ | t <;> simp [ecpieceCoef, hσ]
    simp only [hinr, zero_smul, Finset.sum_const_zero, add_zero]
    rcases hω : ω b with _ | te
    · simp [ecpieceCoef, qK, hσ, hω]
    · simp [ecpieceCoef, qK, hσ, hω]
  · have hinl : ∀ o, ecpieceCoef D L ω σ j b (Sum.inl o) = 0 := by
      intro o
      rcases o with _ | i <;> simp [ecpieceCoef, hσ]
    simp only [hinl, zero_smul, Finset.sum_const_zero, zero_add]
    rcases hω : ω b with _ | te
    · have hinr : ∀ i, i ≠ i₀ → ∀ y, ecpieceCoef D L ω σ j b (Sum.inr (i, y)) = 0 := by
        intro i hi y
        rcases y with _ | t <;> simp [ecpieceCoef, hσ, Ne.symm hi]
      rw [Finset.sum_eq_single i₀ (fun i _ hi => by simp [hinr i hi]) (by simp)]
      simp only [Option.elim, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      rw [Fintype.sum_option, Fintype.sum_bool]
      by_cases ht : D.FS.tag L b i₀ = j
      · have hb : ∀ t : Bool, ecpieceCoef D L ω σ j b (Sum.inr (i₀, some t)) = 0 := by
          intro t
          simp [ecpieceCoef, hσ, ht]
        have h1 : ecpieceCoef D L ω σ j b (Sum.inr (i₀, none)) = 1 := by
          simp [ecpieceCoef, hσ, ht, hω]
        rw [hb, hb, h1]
        simp only [zero_smul, add_zero, one_smul]
        rfl
      · have h0 : ecpieceCoef D L ω σ j b (Sum.inr (i₀, none)) = 0 := by
          simp [ecpieceCoef, hσ, ht]
        have ht1 : ecpieceCoef D L ω σ j b (Sum.inr (i₀, some true)) = 1 := by
          simp [ecpieceCoef, hσ, ht, hω]
        have ht2 : ecpieceCoef D L ω σ j b (Sum.inr (i₀, some false)) = -1 := by
          simp [ecpieceCoef, hσ, ht, hω]
        have hk1 : qK D L Qf ω b (Sum.inr (i₀, some true)) = D.FS.κ' L b i₀ := rfl
        have hk2 : qK D L Qf ω b (Sum.inr (i₀, some false)) = D.FS.κ L b i₀ := rfl
        rw [h0, ht1, ht2, hk1, hk2, zero_smul, zero_add, one_smul]
        apply LinearMap.ext
        intro F
        simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul]
        ring
    · have hinr : ∀ i y, ecpieceCoef D L ω σ j b (Sum.inr (i, y)) = 0 := by
        intro i y
        rcases y with _ | t <;> simp [ecpieceCoef, hω]
      simp [hinr]

/-- The energy of a piece with `Q` on the support (EC's `coupInt`). -/
noncomputable def qInt (A : Finset ℤ) (ω : Choice (D.CL.T L)) (f : ∀ b, CEPiece D L b) : ℝ :=
  diagonalIntegral (tensorLaw fun b => qK D L Qf ω b (f b)) (blockLift m₀ blk p L A)

/-- **The canonical remainder of a piece with `Q` on the support** (EC's `rX`): its excess over
the main term `(∏ g)(1 + ε) Y`, when the tag `j` occurs in `σ`. -/
noncomputable def qX (εE : ℕ → ℝ) (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) (f : ∀ b, CEPiece D L b) : ℝ :=
  if 1 ≤ countVec (D.FS.tag L) σ j then max 0 (|qInt D L Qf A ω f| - coupMain D εE L A ω f)
  else 0

omit [DecidableEq P] in
theorem qX_nonneg (εE : ℕ → ℝ) (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) (f : ∀ b, CEPiece D L b) :
    0 ≤ qX D L Qf εE A ω σ j f := by
  unfold qX
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

omit [DecidableEq P] in
/-- **The sharp term with `Q` on the support, from its pieces** (G1's
`envelopeBound_terms_of_coupled`, second family, with the canonical remainders): for a tag `j`
present in `σ`,
`|E_σ| ≤ (1 + ε)(∏_X q^{2a}) Y wt_j(σ) + ∑_f ∏_𝔟 |c_𝔟| qX_f`. -/
theorem abs_qTerm_le (εE : ℕ → ℝ) (hε0 : ∀ L, 0 ≤ εE L) (A : Finset ℤ) (hY : 0 ≤ D.Y L A)
    (ω : Choice (D.CL.T L)) (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag)
    (hj : 1 ≤ countVec (D.FS.tag L) σ j) :
    |diagonalIntegral (tensorLaw (qTerm D L Qf ω σ)) (blockLift m₀ blk p L A)| ≤
      ((1 + εE L) * (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
          D.Y L A) * tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
            (fun b => if (ω b).isSome then 0 else D.GB.uprice L b) j σ +
        ∑ f, (∏ b, |ecpieceCoef D L ω σ j b (f b)|) * qX D L Qf εE A ω σ j f := by
  have hK : 0 ≤ (1 + εE L) * D.Y L A := mul_nonneg (by linarith [hε0 L]) hY
  have hT : qTerm D L Qf ω σ = fun b => ∑ x, ecpieceCoef D L ω σ j b x • qK D L Qf ω b x :=
    funext fun b => (qSum_eq D L Qf ω σ j b).symm
  rw [hT, EnvelopeInputs.diagonalIntegral_tensorLaw_sum']
  have hw := EnvelopeInputs.weighted_abs_le (ecpieceCoef D L ω σ j) (ecpieceG D L ω)
    (fun f => diagonalIntegral (tensorLaw fun b => qK D L Qf ω b (f b)) (blockLift m₀ blk p L A))
    (qX D L Qf εE A ω σ j) ((1 + εE L) * D.Y L A) (fun f _ => by
      change |qInt D L Qf A ω f| ≤ _
      unfold qX
      simp only [hj, ↓reduceIte]
      have := le_max_right 0 (|qInt D L Qf A ω f| - coupMain D εE L A ω f)
      have hcm : coupMain D εE L A ω f =
          (∏ b, ecpieceG D L ω b (f b)) * ((1 + εE L) * D.Y L A) := rfl
      linarith)
  refine hw.trans ?_
  have hprod : ∏ b, ∑ x, |ecpieceCoef D L ω σ j b x| * ecpieceG D L ω b x ≤
      (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
        tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
          (fun b => if (ω b).isSome then 0 else D.GB.uprice L b) j σ := by
    have h1 : ∏ b, ∑ x, |ecpieceCoef D L ω σ j b x| * ecpieceG D L ω b x ≤
        ∏ b, ((if (ω b).isSome then TheoremCBlock.selectionFactor a p D.S.selPre L b else 1) *
          (σ b).elim (1 + selPriceU ω b)
            (fun i => if D.FS.tag L b i = j then D.FS.dprice L b i else D.FS.vprice L b i)) :=
      Finset.prod_le_prod₀ (fun b _ => Finset.sum_nonneg fun x _ => mul_nonneg
        (abs_nonneg _) (ecpieceG_nonneg D L ω b x))
        (fun b _ => esum_cpieceWeight_le D L ω σ j b)
    refine h1.trans (le_of_eq ?_)
    rw [Finset.prod_mul_distrib, prod_selFactor_eq D L ω]
    rfl
  have hKP := mul_le_mul_of_nonneg_left hprod hK
  have hre : (1 + εE L) * D.Y L A *
      ((∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
      tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
        (fun b => if (ω b).isSome then 0 else D.GB.uprice L b) j σ) =
      ((1 + εE L) *
          (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) * D.Y L A) *
        tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
          (fun b => if (ω b).isSome then 0 else D.GB.uprice L b) j σ := by ring
  linarith

/-! ## The large unions: Hölder -/

/-- The dominating positive record of a piece with `Q` on the support (EC's `cDom`). -/
noncomputable def qDom (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType)) :
    CEPiece D L b → TheoremCBlock.AtomMeasure m₀ blk p L b
  | Sum.inl none => entryFactor (D.R.law p L b) (Qf b) o
  | Sum.inl (some i) => D.GB.κu L b i
  | Sum.inr (i, none) => D.FS.κ' L b i + D.FS.κ L b i
  | Sum.inr (i, some t) => if t then D.FS.κ' L b i else D.FS.κ L b i

variable {D L Qf}

omit [DecidableEq P] in
theorem isPositiveRecord_entryQ (hp : ∀ j, (p L j).Prime)
    (hQp : ∀ b t e, IsProbability (Qf b t e)) (hQu : ∀ b t e, HasUniformSlotMarginals (Qf b t e))
    (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType)) :
    IsPositiveRecord (entryFactor (D.R.law p L b) (Qf b) o) := by
  rcases o with _ | ⟨t, e⟩
  · exact Sarkozy.DensityChain.isPositiveRecord_muLaw D L hp b
  · exact ⟨(hQp b t e).1, hQu b t e⟩

omit [DecidableEq P] in
theorem mass_entryQ (hQp : ∀ b t e, IsProbability (Qf b t e)) (b : BlockAtom Bk J L)
    (o : Option (D.CL.T L b × ChangeType)) :
    mass (entryFactor (D.R.law p L b) (Qf b) o) = 1 := by
  rcases o with _ | ⟨t, e⟩
  · exact Sarkozy.LargeSums.mass_refLaw D L b
  · exact (hQp b t e).2

omit [DecidableEq P] in
theorem isPositiveRecord_qDom (hp : ∀ j, (p L j).Prime)
    (hQp : ∀ b t e, IsProbability (Qf b t e)) (hQu : ∀ b t e, HasUniformSlotMarginals (Qf b t e))
    (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType)) (x : CEPiece D L b) :
    IsPositiveRecord (qDom D L Qf b o x) := by
  rcases x with (_ | i) | ⟨i, _ | t⟩
  · exact isPositiveRecord_entryQ hp hQp hQu b o
  · exact isPositiveRecord_cDom D L hp b o (Sum.inl (some i))
  · exact isPositiveRecord_cDom D L hp b o (Sum.inr (i, none))
  · exact isPositiveRecord_cDom D L hp b o (Sum.inr (i, some t))

omit [DecidableEq P] in
theorem mass_qDom (hQp : ∀ b t e, IsProbability (Qf b t e)) (b : BlockAtom Bk J L)
    (o : Option (D.CL.T L b × ChangeType)) (x : CEPiece D L b) :
    mass (qDom D L Qf b o x) = mass (cDom D L b o x) := by
  rcases x with (_ | i) | ⟨i, _ | t⟩
  · change mass (entryFactor (D.R.law p L b) (Qf b) o) =
      mass (entryFactor (D.R.law p L b) (D.CL.D L b) o)
    rw [mass_entryQ hQp b o, mass_entryFactor D L b o]
  · rfl
  · rfl
  · rfl

omit [DecidableEq P] in
theorem qK_dom (hp : ∀ j, (p L j).Prime)
    (hQp : ∀ b t e, IsProbability (Qf b t e)) (hQu : ∀ b t e, HasUniformSlotMarginals (Qf b t e))
    (ω : Choice (D.CL.T L)) (b : BlockAtom Bk J L) (x : CEPiece D L b)
    (z : Slot → BlockLabel m₀ blk p L b) :
    |lawDensity (qK D L Qf ω b x) z| ≤ lawDensity (qDom D L Qf b (ω b) x) z := by
  rcases x with (_ | i) | ⟨i, _ | t⟩
  · exact le_of_eq (abs_of_nonneg (lawDensity_nonneg
      (isPositiveRecord_entryQ hp hQp hQu b (ω b)).1 z))
  · exact cK_dom D L hp b (ω b) (Sum.inl (some i)) z
  · exact cK_dom D L hp b (ω b) (Sum.inr (i, none)) z
  · exact cK_dom D L hp b (ω b) (Sum.inr (i, some t)) z

omit [DecidableEq P] in
/-- **The Hölder bound of a piece with `Q` on the support** (`lem:record:density-lp`; EC's
`abs_diag_le_dom`), with EC's masses. -/
theorem abs_qInt_le_large (hp : ∀ j, (p L j).Prime)
    (hQp : ∀ b t e, IsProbability (Qf b t e)) (hQu : ∀ b t e, HasUniformSlotMarginals (Qf b t e))
    (A : Finset ℤ) {B : ℝ}
    (hB : (FiniteLaw.uniform (∀ b : BlockAtom Bk J L, BlockLabel m₀ blk p L b)).moment 72
      (blockLift m₀ blk p L A) ≤ B) (ω : Choice (D.CL.T L)) (f : ∀ b, CEPiece D L b) :
    |qInt D L Qf A ω f| ≤ (∏ b, mass (cDom D L b (ω b) (f b))) * B := by
  unfold qInt
  have h := abs_diag_le_dom (fun b => qK D L Qf ω b (f b)) (fun b => qDom D L Qf b (ω b) (f b))
    (fun b => isPositiveRecord_qDom hp hQp hQu b (ω b) (f b))
    (fun b z => qK_dom hp hQp hQu ω b (f b) z) _ hB
  simp only [mass_qDom hQp] at h
  exact h

omit [DecidableEq P] in
/-- **On a large union, the canonical remainder is at most the law-independent bound.** -/
theorem qX_le_pieceBnd_large (hp : ∀ j, (p L j).Prime)
    (hQp : ∀ b t e, IsProbability (Qf b t e)) (hQu : ∀ b t e, HasUniformSlotMarginals (Qf b t e))
    {εE : ℕ → ℝ} (hε0 : ∀ L, 0 ≤ εE L) (A : Finset ℤ) (hY : 0 ≤ D.Y L A) {rem B : ℝ}
    (hB : (FiniteLaw.uniform (∀ b : BlockAtom Bk J L, BlockLabel m₀ blk p L b)).moment 72
      (blockLift m₀ blk p L A) ≤ B) (ω : Choice (D.CL.T L)) (σ : ∀ b, Option (D.FS.Ib L b))
    (j : D.FS.Tag) (f : ∀ b, CEPiece D L b) (hs : ¬ CoupSmall D L ω f) :
    qX D L Qf εE A ω σ j f ≤ pieceBnd D L rem B ω f := by
  unfold pieceBnd
  simp only [hs, ↓reduceIte]
  have h1 := abs_qInt_le_large hp hQp hQu A hB ω f
  have hm := coupMain_nonneg D hε0 hY ω f
  unfold qX
  split_ifs
  · exact max_le ((abs_nonneg _).trans h1) (by linarith)
  · exact (abs_nonneg _).trans h1

end Sarkozy.OpsSteps
