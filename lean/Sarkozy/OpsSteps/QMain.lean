module

public import Sarkozy.OpsSteps.QSmall
public import Sarkozy.OpsSteps.Step3

@[expose] public section

/-!
# The summed per-coupling remainders of Step 3, proved (OPS-S)

`paper/sections/23_envelopes.tex`, proof of `thm:envelopes`, Step 3, and proof of
`lem:orbit-coupon`(i) ("Every `C_k` is an admissible probability measure. Its difference is bounded
as in the proof of `lem:bracket-energy`"); `paper/sections/10_comparison_lemmas.tex`,
`lem:bracket-energy`, `lem:sharp-first`, `lem:density:coupled`, `lem:record:density-lp`,
"Fixed selections and summed remainders" (ll. 126–140).

`Coupled.herr_canonical` proves the per-coupling bound of Step 3 with the canonical remainders
`rCan` of the sharp terms; its content was the sum of these remainders over the couplings and the
class selections. This file proves that sum:

* `qfOf`, `sharpPiece_eq_qTerm`: the sharp term of `Coupled.lean` (B9's `sharpPiece`, the tensor
  `Q` on `S = supp ω`) is the term `qTerm` of `QPieces.lean`;
* **`rCan_le_qX`**: `rCan_σ ≤ ∑_j ∑_f ∏|c| qX_f` (the pieces, G1's coefficients);
* **`sum_rCan_le_pieceBnd`**: at a least counterexample, `∑_{σ≠∅} rCan_σ` is at most the
  law-independent `∑_{σ,j,f} ∏|c| pieceBnd` (per term: `qCoupSmallPT_proved` on a small union,
  Hölder on a large one);
* **`rCan_class_sum`**: on the paper's tails there is `c ≥ 0` such that at every least
  counterexample, for every set `𝒞` of selections with weights `0 ≤ w_ω ≤ K₁ π̃_ω` (e.g.
  `π̃^arm_ω`, `E1Diag.wt_le_of_hπ`), coupling families of mass `≤ M` and probability laws with
  uniform one-slot marginals on the support (the placed couplings),
  `∑_{ω ∈ 𝒞} w_ω ∑_C |c_ω(C)| ∑_{σ≠∅} rCan_{ω,C,σ} ≤ M K₁ c L^{-σ} α`.

So the remainders `r₃ = ∑_C |c(C)| r_C` of `Step3.step3_orbit` with `r_C = ∑_σ rCan` (from
`herr_canonical`) sum to a remainder: the per-coupling bound `herr` of Step 3 is proved, with its
summed remainders.
-/

namespace Sarkozy.OpsSteps

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.CancellationSteps Sarkozy.BlockAnchor Sarkozy.DensityChain2
  Sarkozy.DensityFibre Sarkozy.EnvelopeInputsBlock Sarkozy.RecordExpansion
  Sarkozy.RecordExpansion.Choice Sarkozy.E1Closure Sarkozy.Envelopes
open Sarkozy.Param (Params)
open Sarkozy.SharpFirst (sfEps sfEps_nonneg)

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

section Generic

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)

/-- The support-law family of a tensor `Q` on `S`: `Q_𝔟` on `S`, the norm envelope elsewhere (only
the selected atoms are used). -/
noncomputable def qfOf (S : Finset (BlockAtom Bk J L))
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) :
    ∀ b : BlockAtom Bk J L, D.CL.T L b → ChangeType → TheoremCBlock.AtomMeasure m₀ blk p L b :=
  fun b t e => if b ∈ S then Qb b else D.CL.D L b t e

omit [DecidableEq P] in
theorem qfOf_prob (S : Finset (BlockAtom Bk J L)) (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (hQ : ∀ b ∈ S, IsProbability (Qb b)) (b : BlockAtom Bk J L) (t : D.CL.T L b)
    (e : ChangeType) : IsProbability (qfOf D L S Qb b t e) := by
  unfold qfOf
  split_ifs with hb
  · exact hQ b hb
  · exact D.CL.D_prob L b t e

omit [DecidableEq P] in
theorem qfOf_unif (S : Finset (BlockAtom Bk J L)) (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (hQ : ∀ b ∈ S, HasUniformSlotMarginals (Qb b)) (b : BlockAtom Bk J L) (t : D.CL.T L b)
    (e : ChangeType) : HasUniformSlotMarginals (qfOf D L S Qb b t e) := by
  unfold qfOf
  split_ifs with hb
  · exact hQ b hb
  · exact D.CL.D_unif L b t e

omit [DecidableEq P] in
theorem mem_support_iff' (ω : Choice (D.CL.T L)) (b : BlockAtom Bk J L) :
    b ∈ Choice.support ω ↔ (ω b).isSome = true := by
  simp [Choice.support]

omit [DecidableEq P] in
/-- **The sharp term of `Coupled.lean` is `qTerm`** when `S = supp ω`. -/
theorem sharpPiece_eq_qTerm (ω : Choice (D.CL.T L))
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (σ : ∀ b, Option (D.FS.Ib L b)) :
    sharpPiece D L Qb (fun b => decide (b ∈ Choice.support ω)) σ =
      qTerm D L (qfOf D L (Choice.support ω) Qb) ω σ := by
  funext b
  unfold sharpPiece qTerm
  rcases hω : ω b with _ | ⟨t, e⟩
  · have hb : b ∉ Choice.support ω := by rw [mem_support_iff', hω]; simp
    simp only [hb, decide_false, Bool.false_eq_true, ↓reduceIte, Option.isSome_none]
    rcases σ b with _ | i
    · simp only [Option.elim]
      change D.GB.N₀ L b = D.R.law p L b + ∑ i, D.GB.κu L b i
      rw [← D.GB.N₀_sub L b]
      abel
    · rfl
  · have hb : b ∈ Choice.support ω := by rw [mem_support_iff', hω]; simp
    simp only [hb, decide_true, ↓reduceIte, Option.isSome_some]
    rcases σ b with _ | i
    · simp only [Option.elim, add_zero]
      change Qb b = qfOf D L (Choice.support ω) Qb b t e
      simp only [qfOf, hb, ↓reduceIte]
    · rfl

omit [DecidableEq P] in
theorem tagP_eq (ω : Choice (D.CL.T L)) (u : BlockAtom Bk J L → ℝ) :
    (fun b => if decide (b ∈ Choice.support ω) then (0 : ℝ) else u b) =
      fun b => if (ω b).isSome then 0 else u b := by
  funext b
  by_cases hb : b ∈ Choice.support ω
  · have := (mem_support_iff' D L ω b).1 hb
    simp [hb, this]
  · have : (ω b).isSome = false := by
      cases h' : (ω b).isSome
      · rfl
      · exact absurd ((mem_support_iff' D L ω b).2 h') hb
    simp [hb, this]

omit [DecidableEq P] in
/-- **The canonical remainder of a sharp term is at most the remainders of its pieces.** -/
theorem rCan_le_qX (εE : ℕ → ℝ) (hε0 : ∀ L, 0 ≤ εE L) (A : Finset ℤ) (hY : 0 ≤ D.Y L A)
    (ω : Choice (D.CL.T L)) (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (σ : ∀ b, Option (D.FS.Ib L b)) :
    rCan D L A (Choice.support ω) Qb
        ((1 + εE L) * (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
          D.Y L A) σ ≤
      ∑ j, ∑ f, (∏ b, |ecpieceCoef D L ω σ j b (f b)|) *
        qX D L (qfOf D L (Choice.support ω) Qb) εE A ω σ j f := by
  unfold rCan
  refine sum_le_sum fun j _ => ?_
  have hs0 : 0 ≤ ∑ f, (∏ b, |ecpieceCoef D L ω σ j b (f b)|) *
      qX D L (qfOf D L (Choice.support ω) Qb) εE A ω σ j f :=
    sum_nonneg fun f _ => mul_nonneg (prod_nonneg fun b _ => abs_nonneg _)
      (qX_nonneg D L _ _ _ _ _ _ _)
  split_ifs with hj
  · refine max_le hs0 ?_
    have h := abs_qTerm_le D L (qfOf D L (Choice.support ω) Qb) εE hε0 A hY ω σ j hj
    rw [← sharpPiece_eq_qTerm D L ω Qb σ] at h
    rw [tagP_eq D L ω]
    linarith
  · exact hs0

end Generic

section Paper

variable (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)

omit [DecidableEq P] in
/-- **The sum of the canonical remainders of the sharp terms is at most the law-independent
bound**, given the per-term small bound (`qCoupSmallPT_proved`) and the moment bound. -/
theorem sum_rCan_le_pieceBnd {L : ℕ} {A : Finset ℤ} (hY : 0 ≤ D.Y L A) {rem B : ℝ}
    (hrem : 0 ≤ rem)
    (hB : (FiniteLaw.uniform (∀ b : BlockAtom Bk PaperJt L, BlockLabel m₀ blk paperTail L b)).moment
      72 (blockLift m₀ blk paperTail L A) ≤ B)
    (ω : Choice (D.CL.T L)) (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk paperTail L b)
    (hQp : ∀ b ∈ Choice.support ω, IsProbability (Qb b))
    (hQu : ∀ b ∈ Choice.support ω, HasUniformSlotMarginals (Qb b))
    (hpt : ∀ σ : (∀ b, Option (D.FS.Ib L b)), ∀ j, ∀ f : (∀ b, CEPiece D L b),
      (∀ b, ecpieceCoef D L ω σ j b (f b) ≠ 0) → CoupSmall D L ω f →
      |qInt D L (qfOf D L (Choice.support ω) Qb) A ω f| ≤ coupMain D (sfEps D) L A ω f +
        (∏ b, cM D L b (f b)) * rem) :
    ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        rCan D L A (Choice.support ω) Qb
          ((1 + sfEps D L) *
            (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a paperTail D.S.selPre L b) *
            D.Y L A) σ ≤
      ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        ∑ j, ∑ f, (∏ b, |ecpieceCoef D L ω σ j b (f b)|) * pieceBnd D L rem B ω f := by
  refine sum_le_sum fun σ _ => (rCan_le_qX D L (sfEps D) (sfEps_nonneg D) A hY ω Qb σ).trans ?_
  refine sum_le_sum fun j _ => sum_le_sum fun f _ => ?_
  by_cases hs : CoupSmall D L ω f
  · exact qX_le_pieceBnd_small D hrem ω σ j f hs (fun hcf => hpt σ j f hcf hs)
  · exact mul_le_mul_of_nonneg_left
      (qX_le_pieceBnd_large (D.S.p_prime L) (qfOf_prob D L _ Qb hQp) (qfOf_unif D L _ Qb hQu)
        (sfEps_nonneg D) A hY hB ω σ j f hs)
      (prod_nonneg fun b _ => abs_nonneg _)

omit [DecidableEq P] in
/-- **The per-coupling remainders of Step 3 sum to a remainder** (see the module docstring). -/
theorem rCan_class_sum
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (ha : 0 ≤ a) (hpar : ParityCondition D.S.ep)
    (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β) (hne : ∀ β, ∃ i, blk i = β) :
    ∃ c : ℝ, 0 ≤ c ∧ Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∀ (𝒞 : Finset (Choice (D.CL.T L))), (∀ ω ∈ 𝒞, IsSelection ω) →
      ∀ (wt : Choice (D.CL.T L) → ℝ) (K₁ M : ℝ), 0 ≤ K₁ → 0 ≤ M →
      (∀ ω ∈ 𝒞, 0 ≤ wt ω) → (∀ ω ∈ 𝒞, wt ω ≤ K₁ * monomial (D.CL.πt L) ω) →
      ∀ (ι : Choice (D.CL.T L) → Type) [∀ ω, Fintype (ι ω)] (coef : ∀ ω, ι ω → ℝ),
      (∀ ω ∈ 𝒞, couplingMass (coef ω) ≤ M) →
      ∀ (Qb : ∀ ω, ι ω → ∀ b, TheoremCBlock.AtomMeasure m₀ blk paperTail L b),
      (∀ ω ∈ 𝒞, ∀ i, ∀ b ∈ Choice.support ω, IsProbability (Qb ω i b)) →
      (∀ ω ∈ 𝒞, ∀ i, ∀ b ∈ Choice.support ω, HasUniformSlotMarginals (Qb ω i b)) →
      ∑ ω ∈ 𝒞, wt ω * ∑ i, |coef ω i| *
          ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
            rCan D L A (Choice.support ω) (Qb ω i)
              ((1 + sfEps D L) *
                (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a paperTail D.S.selPre L b) *
                D.Y L A) σ ≤
        remainder (M * K₁ * c) L A) := by
  obtain ⟨c₁, hc₁, hPT⟩ := qCoupSmallPT_proved D hpair ha hpar hsel hne
  obtain ⟨Cm, -, c, hc, hsum⟩ := pieceBnd_summable D ha hc₁
  refine ⟨c, hc, ?_⟩
  filter_upwards [hPT, hsum] with L hPTL hsumL
  intro C hC hk A hA hYc 𝒞 h𝒞 wt K₁ M hK₁ hM0 hwt0 hwt ι _ coef hM Qb hQp hQu
  have hY : 0 ≤ D.Y L A := (Param.counterexample_pos (Params.ofDecay a) hC hYc).le
  obtain ⟨hB0, hB, _, hS⟩ := hsumL A
  set rem := remainder c₁ L A with hremdef
  have hrem0 : 0 ≤ rem := E1Closure.remainder_nonneg' hc₁ L A
  set SS := univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)
  set Bnd : Choice (D.CL.T L) → ℝ := fun ω => ∑ σ ∈ SS, ∑ j, ∑ f,
    (∏ b, |ecpieceCoef D L ω σ j b (f b)|) * pieceBnd D L rem (momB (m₀ := m₀) Cm L A) ω f
    with hBnd
  have hBnd0 : ∀ ω, 0 ≤ Bnd ω := fun ω => sum_nonneg fun σ _ => sum_nonneg fun j _ =>
    sum_nonneg fun f _ => mul_nonneg (prod_nonneg fun b _ => abs_nonneg _)
      (pieceBnd_nonneg D L (D.S.p_prime L) hrem0 hB0 ω f)
  have hper : ∀ ω ∈ 𝒞, ∀ i, ∑ σ ∈ SS, rCan D L A (Choice.support ω) (Qb ω i)
      ((1 + sfEps D L) *
        (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a paperTail D.S.selPre L b) *
        D.Y L A) σ ≤ Bnd ω := by
    intro ω hω i
    exact sum_rCan_le_pieceBnd D hY hrem0 hB ω (Qb ω i) (hQp ω hω i) (hQu ω hω i)
      (fun σ j f hcf hs => hPTL C hC hk A hA hYc (qfOf D L (Choice.support ω) (Qb ω i))
        (qfOf_prob D L _ _ (hQp ω hω i)) (qfOf_unif D L _ _ (hQu ω hω i)) ω (h𝒞 ω hω) σ j f
        hcf hs)
  have hstep : ∀ ω ∈ 𝒞, wt ω * ∑ i, |coef ω i| * ∑ σ ∈ SS, rCan D L A (Choice.support ω)
      (Qb ω i) ((1 + sfEps D L) *
        (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a paperTail D.S.selPre L b) *
        D.Y L A) σ ≤ (M * K₁) * (monomial (D.CL.πt L) ω * Bnd ω) := by
    intro ω hω
    have h1 : ∑ i, |coef ω i| * ∑ σ ∈ SS, rCan D L A (Choice.support ω) (Qb ω i)
        ((1 + sfEps D L) *
          (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a paperTail D.S.selPre L b) *
          D.Y L A) σ ≤ M * Bnd ω := by
      calc _ ≤ ∑ i, |coef ω i| * Bnd ω :=
            sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hper ω hω i) (abs_nonneg _)
        _ = couplingMass (coef ω) * Bnd ω := by rw [couplingMass, sum_mul]
        _ ≤ M * Bnd ω := mul_le_mul_of_nonneg_right (hM ω hω) (hBnd0 ω)
    have hm0 : 0 ≤ monomial (D.CL.πt L) ω := monomial_nonneg (D.CL.πt_nonneg L) ω
    calc _ ≤ wt ω * (M * Bnd ω) := mul_le_mul_of_nonneg_left h1 (hwt0 ω hω)
      _ ≤ (K₁ * monomial (D.CL.πt L) ω) * (M * Bnd ω) :=
          mul_le_mul_of_nonneg_right (hwt ω hω) (mul_nonneg hM0 (hBnd0 ω))
      _ = (M * K₁) * (monomial (D.CL.πt L) ω * Bnd ω) := by ring
  have hsub : 𝒞 ⊆ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω) :=
    fun ω hω => mem_filter.mpr ⟨mem_univ _, h𝒞 ω hω⟩
  calc _ ≤ ∑ ω ∈ 𝒞, (M * K₁) * (monomial (D.CL.πt L) ω * Bnd ω) := sum_le_sum hstep
    _ ≤ ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
          (M * K₁) * (monomial (D.CL.πt L) ω * Bnd ω) :=
        sum_le_sum_of_subset_of_nonneg hsub fun ω _ _ =>
          mul_nonneg (mul_nonneg hM0 hK₁) (mul_nonneg (monomial_nonneg (D.CL.πt_nonneg L) ω)
            (hBnd0 ω))
    _ = (M * K₁) * ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
          monomial (D.CL.πt L) ω * Bnd ω := by rw [mul_sum]
    _ ≤ (M * K₁) * remainder c L A := mul_le_mul_of_nonneg_left hS (mul_nonneg hM0 hK₁)
    _ = remainder (M * K₁ * c) L A := by unfold remainder; ring

end Paper

section Field

open Sarkozy.EnvelopeSteps

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)

omit [DecidableEq P] in
/-- **The input `herr` of `step3_orbit` / `paperDegreeOpsS` for a tensor coupling, in its exact
form**: with product objects and a coupling whose kernel is the product of per-block kernels,
`|Y^Ñ[[C]] − Y^{Ñ₀}[[C]]| ≤ (R_err + z') C_X Y + r_C` with `z' = ε R_err` and
`r_C = ∑_{σ≠∅} rCan_σ` (`herr_canonical` at `z = 0`, `K = (1 + ε) C_X Y`). The sum of the `r_C`
over the couplings and the class selections is `rCan_class_sum`. -/
theorem herr_of_tensor (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j)) (L : ℕ) (A : Finset ℤ)
    (ω : Choice (D.CL.T L)) {εE : ℝ} (hε : 0 ≤ εE) (hY : 0 ≤ D.Y L A)
    (O : {b // b ∈ Choice.support ω} → Type) [∀ b, Fintype (O b)] [∀ b, DecidableEq (O b)]
    (m : ∀ b, O b → ℝ) (φ : ∀ b, O b → (reservedCut.Half → BlockLabel m₀ blk p L b.1))
    (Cb : ∀ b, (O b → ℝ) →ₗ[ℝ] (O b → ℝ)) (Cop : ((∀ b, O b) → ℝ) →ₗ[ℝ] ((∀ b, O b) → ℝ))
    (hC : ∀ x y, kern (prodWeight m) Cop x y = ∏ b, kern (m b) (Cb b) (x b) (y b))
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (hQ : ∀ b : {b // b ∈ Choice.support ω}, Qb b.1 = place reservedCut (m b) (φ b) (Cb b)) :
    |paperEN D L A (Choice.support ω)
        (place reservedCut (prodWeight m) (prodPlace reservedCut φ) Cop) -
      paperEN0 D L A (Choice.support ω)
        (place reservedCut (prodWeight m) (prodPlace reservedCut φ) Cop)| ≤
      (D.GB.Rerr + εE * D.GB.Rerr) *
          (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) * D.Y L A +
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          rCan D L A (Choice.support ω) Qb
            ((1 + εE) * (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
              D.Y L A) σ := by
  have hCX : 0 ≤ (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) :=
    prod_nonneg fun b _ => D.selectionFactor_nonneg L b
  have hK : 0 ≤ (1 + εE) * (∏ b ∈ Choice.support ω,
      TheoremCBlock.selectionFactor a p D.S.selPre L b) * D.Y L A :=
    mul_nonneg (mul_nonneg (by linarith) hCX) hY
  have h := herr_canonical D h0 L A (Choice.support ω) O m φ Cb Cop hC Qb hQ hK le_rfl
  refine h.trans (le_of_eq ?_)
  ring

end Field

end Sarkozy.OpsSteps
