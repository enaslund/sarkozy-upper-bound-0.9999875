module

public import Sarkozy.OpsSteps.SymFineSum
public import Sarkozy.OpsSteps.Plug
public import Sarkozy.OpsSteps.Coupling

@[expose] public section

/-!
# Step 3 at tensor couplings: `herr` and `hsym` of `paperDegreeOpsS` together (OPS-S)

`paper/sections/23_envelopes.tex`, proof of `thm:envelopes`(i), Step 3; `lem:orbit-coupon`(i).

`paperDegreeOpsS` takes the per-coupling bound `herr` and the improved bound `hsym` at the orbit
averages with **one** remainder `r_C` per coupling. For tensor couplings (the per-block kernels of
`lem:oct24:pure-pair-substitute`):

* `r3`: `r_C = ∑_σ rCan(C) + ∑_σ rCan(hC) + ∑_{σ ∈ e_s} (r^sym_σ + ∑_Z rQ_{σ,Z})`;
* **`herr_hsym_of_tensor`**: both fields hold with `z' = ε R_err` (`herr_of_tensor`, `hsym_fine`);
  the only analytic input is the `G`-free symmetric bound `hsymT` (C,
  `lem:record:one-stage-folded-e`(e));
* **`r3_class_sum`**: `∑_ω w_ω ∑_C |c(C)| r_C ≤ M K₁ c L^{-σ} α + ∑_ω w_ω ∑_C |c(C)| ∑ r^sym`
  (`rCan_class_sum` twice, the second time along the involution `C ↦ hC`, and `rQ_class_sum`).
-/

namespace Sarkozy.OpsSteps

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.E1Closure Sarkozy.EnvelopeInputsBlock
open Sarkozy.Param (Params)
open Sarkozy.SharpFirst (sfEps sfEps_nonneg)
open Sarkozy.BlockFrame Sarkozy.BracketEnergy Sarkozy.EnvelopeSteps Sarkozy.Envelopes
open Sarkozy.TheoremC Sarkozy.Comparison Sarkozy.PaperFrame Sarkozy.RecordExpansion
  Sarkozy.RecordExpansion.Choice Sarkozy.CancellationSteps Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.IndexSupport
  Sarkozy.DensityChain Sarkozy.BlockAnchor Sarkozy.DensityChain2 Sarkozy.DensityFibre

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)

/-- **The common per-coupling remainder of Step 3** (see the module docstring). -/
noncomputable def r3 (L : ℕ) (A : Finset ℤ)
    (isG : ∀ b : BlockAtom Bk PaperJt L, D.GB.Iu L b → Bool) (ω : Choice (D.CL.T L)) {ι : Type*}
    (Q : ι → ∀ b, TheoremCBlock.AtomMeasure m₀ blk paperTail L b)
    (hC : ι → ι) (s : D.FS.Tag) (rSym : ι → (∀ b, Option (D.FS.Ib L b)) → ℝ) (i : ι) : ℝ :=
  ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      rCan D L A (Choice.support ω) (Q i) ((1 + sfEps D L) * cX D L ω * D.Y L A) σ +
    ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      rCan D L A (Choice.support ω) (Q (hC i)) ((1 + sfEps D L) * cX D L ω * D.Y L A) σ +
    ∑ σ ∈ (univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)).filter
        (fun σ => countVec (D.FS.tag L) σ = Pi.single s 1),
      (rSym i σ + ∑ f, rQ D L isG (sfEps D) A ω (Q i) (Q (hC i)) s σ f)

omit [DecidableEq P] in
/-- **`herr` and `hsym` of `paperDegreeOpsS` at tensor couplings** (see the module docstring). -/
theorem herr_hsym_of_tensor (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j)) (L : ℕ)
    (A : Finset ℤ) (hY : 0 ≤ D.Y L A) (isG : ∀ b : BlockAtom Bk PaperJt L, D.GB.Iu L b → Bool)
    (ω : Choice (D.CL.T L))
    (Ob : {b // b ∈ Choice.support ω} → Type) [∀ b, Fintype (Ob b)] [∀ b, DecidableEq (Ob b)]
    (mb : ∀ b, Ob b → ℝ)
    (φb : ∀ b, Ob b → (reservedCut.Half → BlockLabel m₀ blk paperTail L b.1))
    {ι : Type*} (Cop : ι → ((∀ b, Ob b) → ℝ) →ₗ[ℝ] ((∀ b, Ob b) → ℝ))
    (Cb : ι → ∀ b, (Ob b → ℝ) →ₗ[ℝ] (Ob b → ℝ))
    (hCk : ∀ i x y, kern (prodWeight mb) (Cop i) x y = ∏ b, kern (mb b) (Cb i b) (x b) (y b))
    (Q : ι → ∀ b, TheoremCBlock.AtomMeasure m₀ blk paperTail L b)
    (hQ : ∀ i, ∀ b : {b // b ∈ Choice.support ω},
      Q i b.1 = place reservedCut (mb b) (φb b) (Cb i b))
    (hC : ι → ι) (s : D.FS.Tag) {tU tδ : ℝ} (htδ : 0 ≤ tδ)
    (sym : ∀ b, D.FS.Ib L b → ℝ) (hsym0 : ∀ b i, 0 ≤ sym b i)
    (hsymd : ∀ b i, sym b i ≤ D.FS.dprice L b i)
    (htot : tagTotal (D.FS.tag L) sym s + tδ ≤ D.FS.dT s)
    (htW : tU + ∑ c, wP D L isG ω c ≤ D.GB.U₀)
    (rSym : ι → (∀ b, Option (D.FS.Ib L b)) → ℝ) (hrSym0 : ∀ i σ, 0 ≤ rSym i σ)
    (hsymT : ∀ i, ∀ σ ∈ (univ.filter
        (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)).filter
        (fun σ => countVec (D.FS.tag L) σ = Pi.single s 1),
      |catT D L A isG (Choice.support ω) (Q i) (Q (hC i)) σ (fun _ => false)| ≤
        ((1 + sfEps D L) * cX D L ω * D.Y L A) *
          (tagWeight (D.FS.tag L) sym (D.FS.vprice L) (fun _ => 0) s σ *
            ∏ c, (1 + vP D L isG ω c)) + rSym i σ) :
    (∀ i, |paperEN D L A (Choice.support ω)
          (place reservedCut (prodWeight mb) (prodPlace reservedCut φb) (Cop i)) -
        paperEN0 D L A (Choice.support ω)
          (place reservedCut (prodWeight mb) (prodPlace reservedCut φb) (Cop i))| ≤
        (D.GB.Rerr + sfEps D L * D.GB.Rerr) * cX D L ω * D.Y L A + r3 D L A isG ω Q hC s rSym i) ∧
    (∀ κ, ∀ i, κ = (1 / 2 : ℝ) •
      (place reservedCut (prodWeight mb) (prodPlace reservedCut φb) (Cop i) +
        place reservedCut (prodWeight mb) (prodPlace reservedCut φb) (Cop (hC i))) →
      |paperEN D L A (Choice.support ω) κ - paperEN0 D L A (Choice.support ω) κ| ≤
        (D.GB.Rerr - Real.exp tU * tδ + sfEps D L * D.GB.Rerr) * cX D L ω * D.Y L A +
          r3 D L A isG ω Q hC s rSym i) := by
  have hε := sfEps_nonneg D L
  have hcX : 0 ≤ cX D L ω := prod_nonneg fun b _ => D.selectionFactor_nonneg L b
  set K := (1 + sfEps D L) * cX D L ω * D.Y L A with hK
  have hcan : ∀ Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk paperTail L b,
      0 ≤ ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        rCan D L A (Choice.support ω) Qb K σ :=
    fun Qb => sum_nonneg fun σ _ => rCan_nonneg D L A _ Qb K σ
  have hes : ∀ i, 0 ≤ ∑ σ ∈ (univ.filter
      (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)).filter
      (fun σ => countVec (D.FS.tag L) σ = Pi.single s 1),
      (rSym i σ + ∑ f, rQ D L isG (sfEps D) A ω (Q i) (Q (hC i)) s σ f) :=
    fun i => sum_nonneg fun σ _ => add_nonneg (hrSym0 i σ)
      (sum_nonneg fun f _ => rQ_nonneg D L isG (sfEps D) A ω (Q i) (Q (hC i)) s σ f)
  refine ⟨fun i => ?_, fun κ i hκ => ?_⟩
  · have h1 := herr_of_tensor D h0 L A ω hε hY Ob mb φb (Cb i) (Cop i) (hCk i) (Q i) (hQ i)
    have h2 := hcan (Q (hC i))
    have h3 := hes i
    unfold r3
    have e : (D.GB.Rerr + sfEps D L * D.GB.Rerr) * cX D L ω * D.Y L A =
        (D.GB.Rerr + sfEps D L * D.GB.Rerr) *
          (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a paperTail D.S.selPre L b) *
          D.Y L A := rfl
    linarith
  · have ht : ∀ j, place reservedCut (prodWeight mb) (prodPlace reservedCut φb) (Cop j) =
        tensorLaw fun b : {b // b ∈ Choice.support ω} => Q j b.1 := by
      intro j
      rw [place_tensor reservedCut mb φb (Cb j) (Cop j) (hCk j)]
      congr 1
      funext b
      exact (hQ j b).symm
    rw [hκ, ht i, ht (hC i)]
    have h1 := hsym_fine D L A isG hY ω (Q i) (Q (hC i)) s sym hsym0 hsymd htot htW (rSym i)
      (hsymT i)
    have h2 : ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        (1 / 2 : ℝ) * (rCan D L A (Choice.support ω) (Q i) K σ +
          rCan D L A (Choice.support ω) (Q (hC i)) K σ) ≤
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          rCan D L A (Choice.support ω) (Q i) K σ +
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          rCan D L A (Choice.support ω) (Q (hC i)) K σ := by
      rw [← sum_add_distrib]
      refine sum_le_sum fun σ _ => ?_
      have := rCan_nonneg D L A (Choice.support ω) (Q i) K σ
      have := rCan_nonneg D L A (Choice.support ω) (Q (hC i)) K σ
      linarith
    have h3 : (D.GB.Rerr - Real.exp tU * tδ) * K ≤
        (D.GB.Rerr - Real.exp tU * tδ + sfEps D L * D.GB.Rerr) * cX D L ω * D.Y L A := by
      have h4 : 0 ≤ sfEps D L * (Real.exp tU * tδ) * (cX D L ω * D.Y L A) :=
        mul_nonneg (mul_nonneg hε (mul_nonneg (Real.exp_pos _).le htδ)) (mul_nonneg hcX hY)
      have e : (D.GB.Rerr - Real.exp tU * tδ) * K =
          (D.GB.Rerr - Real.exp tU * tδ + sfEps D L * D.GB.Rerr) * cX D L ω * D.Y L A -
            sfEps D L * (Real.exp tU * tδ) * (cX D L ω * D.Y L A) := by
        rw [hK]
        ring
      linarith
    unfold r3
    have e : ((1 + sfEps D L) *
        (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a paperTail D.S.selPre L b) *
        D.Y L A) = K := rfl
    rw [e] at h1
    linarith

omit [DecidableEq P] in
/-- **The common Step 3 remainders sum to a remainder, up to the symmetric remainders** (see the
module docstring): on the paper's tails there is `c ≥ 0` such that at every least counterexample,
for every split, tag, class, weights `0 ≤ w ≤ K₁ π̃`, coupling families with mass `≤ M`, an
involution `C ↦ hC` and tensor laws with uniform one-slot marginals on the support,
`∑_ω w_ω ∑_C |c(C)| r_C ≤ M K₁ c L^{-σ} α + ∑_ω w_ω ∑_C |c(C)| ∑_{σ ∈ e_s} r^sym_{C,σ}`. -/
theorem r3_class_sum
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (ha : 0 ≤ a) (hpar : ParityCondition D.S.ep)
    (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β) (hne : ∀ β, ∃ i, blk i = β) :
    ∃ c : ℝ, 0 ≤ c ∧ Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∀ (isG : ∀ b : BlockAtom Bk PaperJt L, D.GB.Iu L b → Bool) (s : D.FS.Tag)
        (𝒞 : Finset (Choice (D.CL.T L))), (∀ ω ∈ 𝒞, IsSelection ω) →
      ∀ (wt : Choice (D.CL.T L) → ℝ) (K₁ M : ℝ), 0 ≤ K₁ → 0 ≤ M →
      (∀ ω ∈ 𝒞, 0 ≤ wt ω) → (∀ ω ∈ 𝒞, wt ω ≤ K₁ * monomial (D.CL.πt L) ω) →
      ∀ (ι : Choice (D.CL.T L) → Type) [∀ ω, Fintype (ι ω)] (coef : ∀ ω, ι ω → ℝ),
      (∀ ω ∈ 𝒞, couplingMass (coef ω) ≤ M) →
      ∀ (hC : ∀ ω, ι ω → ι ω), (∀ ω ∈ 𝒞, ∀ i, hC ω (hC ω i) = i) →
      ∀ (Q : ∀ ω, ι ω → ∀ b, TheoremCBlock.AtomMeasure m₀ blk paperTail L b),
      (∀ ω ∈ 𝒞, ∀ i, ∀ b ∈ Choice.support ω, IsProbability (Q ω i b)) →
      (∀ ω ∈ 𝒞, ∀ i, ∀ b ∈ Choice.support ω, HasUniformSlotMarginals (Q ω i b)) →
      ∀ (rSym : ∀ ω, ι ω → (∀ b, Option (D.FS.Ib L b)) → ℝ),
      ∑ ω ∈ 𝒞, wt ω * ∑ i, |coef ω i| * r3 D L A isG ω (Q ω) (hC ω) s (rSym ω) i ≤
        remainder (M * K₁ * c) L A +
          ∑ ω ∈ 𝒞, wt ω * ∑ i, |coef ω i| *
            ∑ σ ∈ (univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)).filter
              (fun σ => countVec (D.FS.tag L) σ = Pi.single s 1), rSym ω i σ) := by
  obtain ⟨c₁, hc₁, h1⟩ := rCan_class_sum D hpair ha hpar hsel hne
  obtain ⟨c₂, hc₂, h2⟩ := rQ_class_sum D hpair ha hpar hsel hne
  refine ⟨c₁ + c₁ + c₂, by positivity, ?_⟩
  filter_upwards [h1, h2] with L h1L h2L
  intro C hCc hk A hA hYc isG s 𝒞 h𝒞 wt K₁ M hK₁ hM0 hwt0 hwt ι _ coef hM hC hh Q hQp hQu rSym
  -- the three summed parts and the symmetric part
  have hr3 : ∀ ω i, r3 D L A isG ω (Q ω) (hC ω) s (rSym ω) i =
      (∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        rCan D L A (Choice.support ω) (Q ω i) ((1 + sfEps D L) *
          (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a paperTail D.S.selPre L b) *
          D.Y L A) σ) +
      (∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        rCan D L A (Choice.support ω) (Q ω (hC ω i)) ((1 + sfEps D L) *
          (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a paperTail D.S.selPre L b) *
          D.Y L A) σ) +
      (∑ σ ∈ (univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)).filter
          (fun σ => countVec (D.FS.tag L) σ = Pi.single s 1),
        ∑ f, rQ D L isG (sfEps D) A ω (Q ω i) (Q ω (hC ω i)) s σ f) +
      (∑ σ ∈ (univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)).filter
          (fun σ => countVec (D.FS.tag L) σ = Pi.single s 1), rSym ω i σ) := by
    intro ω i
    unfold r3
    rw [sum_add_distrib]
    ring
  have hM' : ∀ ω ∈ 𝒞, couplingMass (fun i => coef ω (hC ω i)) ≤ M := by
    intro ω hω
    have e := couplingMass_comp_equiv (coef ω) (Function.Involutive.toPerm (hC ω) (hh ω hω))
    have e' : (fun i => coef ω (hC ω i)) =
        coef ω ∘ (Function.Involutive.toPerm (hC ω) (hh ω hω)) := rfl
    rw [e', e]
    exact hM ω hω
  have p1 := h1L C hCc hk A hA hYc 𝒞 h𝒞 wt K₁ M hK₁ hM0 hwt0 hwt ι coef hM Q hQp hQu
  have p2 := h1L C hCc hk A hA hYc 𝒞 h𝒞 wt K₁ M hK₁ hM0 hwt0 hwt ι
    (fun ω i => coef ω (hC ω i)) hM' Q hQp hQu
  have p3 := h2L C hCc hk A hA hYc isG s 𝒞 h𝒞 wt K₁ M hK₁ hM0 hwt0 hwt ι coef hM Q
    (fun ω i => Q ω (hC ω i)) hQp hQu (fun ω hω i => hQp ω hω (hC ω i))
    (fun ω hω i => hQu ω hω (hC ω i))
  beta_reduce at p2 p3
  have hre : ∀ ω ∈ 𝒞, ∑ i, |coef ω i| *
      (∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        rCan D L A (Choice.support ω) (Q ω (hC ω i)) ((1 + sfEps D L) *
          (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a paperTail D.S.selPre L b) *
          D.Y L A) σ) =
      ∑ i, |coef ω (hC ω i)| *
      (∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        rCan D L A (Choice.support ω) (Q ω i) ((1 + sfEps D L) *
          (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a paperTail D.S.selPre L b) *
          D.Y L A) σ) := by
    intro ω hω
    have e := Equiv.sum_comp (Function.Involutive.toPerm (hC ω) (hh ω hω))
      (fun i => |coef ω (hC ω i)| *
        (∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          rCan D L A (Choice.support ω) (Q ω i) ((1 + sfEps D L) *
            (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a paperTail D.S.selPre L b) *
            D.Y L A) σ))
    rw [← e]
    refine sum_congr rfl fun i _ => ?_
    change _ = |coef ω (hC ω (hC ω i))| * _
    rw [hh ω hω i]
    rfl
  have hsplit : ∀ ω ∈ 𝒞, wt ω * ∑ i, |coef ω i| * r3 D L A isG ω (Q ω) (hC ω) s (rSym ω) i =
      wt ω * ∑ i, |coef ω i| *
        (∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          rCan D L A (Choice.support ω) (Q ω i) ((1 + sfEps D L) *
            (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a paperTail D.S.selPre L b) *
            D.Y L A) σ) +
      wt ω * ∑ i, |coef ω (hC ω i)| *
        (∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          rCan D L A (Choice.support ω) (Q ω i) ((1 + sfEps D L) *
            (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a paperTail D.S.selPre L b) *
            D.Y L A) σ) +
      wt ω * ∑ i, |coef ω i| *
        (∑ σ ∈ (univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)).filter
            (fun σ => countVec (D.FS.tag L) σ = Pi.single s 1),
          ∑ f, rQ D L isG (sfEps D) A ω (Q ω i) (Q ω (hC ω i)) s σ f) +
      wt ω * ∑ i, |coef ω i| *
        (∑ σ ∈ (univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)).filter
            (fun σ => countVec (D.FS.tag L) σ = Pi.single s 1), rSym ω i σ) := by
    intro ω hω
    rw [← hre ω hω]
    simp only [hr3, mul_add, sum_add_distrib]
  rw [sum_congr rfl hsplit, sum_add_distrib, sum_add_distrib, sum_add_distrib]
  have e1 : remainder (M * K₁ * (c₁ + c₁ + c₂)) L A =
      remainder (M * K₁ * c₁) L A + remainder (M * K₁ * c₁) L A + remainder (M * K₁ * c₂) L A := by
    unfold remainder
    ring
  linarith [p1, p2, p3, e1]

omit [DecidableEq P] in
/-- **Non-vacuity of `hsymT`**: at the sharp price (`s = d`, `tδ = 0`, no improvement) the input
`hsymT` of `herr_hsym_of_tensor` holds, by `abs_catT_le` at `Z = ∅`, with `r^sym_σ = rQ_{σ,∅}`. -/
theorem hsymT_sharp (L : ℕ) (A : Finset ℤ) (isG : ∀ b : BlockAtom Bk PaperJt L, D.GB.Iu L b → Bool)
    (hY : 0 ≤ D.Y L A) (ω : Choice (D.CL.T L))
    (Q₁ Q₂ : ∀ b, TheoremCBlock.AtomMeasure m₀ blk paperTail L b) (s : D.FS.Tag) :
    ∀ σ ∈ (univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)).filter
        (fun σ => countVec (D.FS.tag L) σ = Pi.single s 1),
      |catT D L A isG (Choice.support ω) Q₁ Q₂ σ (fun _ => false)| ≤
        ((1 + sfEps D L) * cX D L ω * D.Y L A) *
          (tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (fun _ => 0) s σ *
            ∏ c, (1 + vP D L isG ω c)) +
          rQ D L isG (sfEps D) A ω Q₁ Q₂ s σ (fun _ => false) := by
  intro σ hσ
  have hcount : 1 ≤ countVec (D.FS.tag L) σ s := by
    rw [(mem_filter.mp hσ).2]
    simp
  have h := abs_catT_le D L isG (sfEps D) (sfEps_nonneg D) A hY ω Q₁ Q₂ s σ hcount
    (fun _ => false)
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  exact h

omit [DecidableEq P] in
/-- **The fields `herr` and `hsym` of `paperDegreeOpsS`, verbatim**, for a class of selections
with tensor couplings: `herr_hsym_of_tensor` at every `ω ∈ 𝒞`, with `Rerr = R_err`,
`z' = ε R_err` and `r = r3`. -/
theorem herr_hsym_class (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j)) (L : ℕ)
    (A : Finset ℤ) (hY : 0 ≤ D.Y L A) (isG : ∀ b : BlockAtom Bk PaperJt L, D.GB.Iu L b → Bool)
    (𝒞 : Finset (Choice (D.CL.T L)))
    (Ob : ∀ ω : Choice (D.CL.T L), {b // b ∈ Choice.support ω} → Type)
    [∀ ω b, Fintype (Ob ω b)] [∀ ω b, DecidableEq (Ob ω b)]
    (mb : ∀ ω b, Ob ω b → ℝ)
    (φb : ∀ ω b, Ob ω b → (reservedCut.Half → BlockLabel m₀ blk paperTail L b.1))
    (ι : Choice (D.CL.T L) → Type)
    (Cop : ∀ ω, ι ω → ((∀ b, Ob ω b) → ℝ) →ₗ[ℝ] ((∀ b, Ob ω b) → ℝ))
    (Cb : ∀ ω, ι ω → ∀ b, (Ob ω b → ℝ) →ₗ[ℝ] (Ob ω b → ℝ))
    (hCk : ∀ ω ∈ 𝒞, ∀ i x y, kern (prodWeight (mb ω)) (Cop ω i) x y =
      ∏ b, kern (mb ω b) (Cb ω i b) (x b) (y b))
    (Q : ∀ ω, ι ω → ∀ b, TheoremCBlock.AtomMeasure m₀ blk paperTail L b)
    (hQ : ∀ ω ∈ 𝒞, ∀ i, ∀ b : {b // b ∈ Choice.support ω},
      Q ω i b.1 = place reservedCut (mb ω b) (φb ω b) (Cb ω i b))
    (hR : ZMod 6) (hC : ∀ ω, ι ω → ι ω) (s : D.FS.Tag) {tU tδ : ℝ} (htδ : 0 ≤ tδ)
    (sym : ∀ b, D.FS.Ib L b → ℝ) (hsym0 : ∀ b i, 0 ≤ sym b i)
    (hsymd : ∀ b i, sym b i ≤ D.FS.dprice L b i)
    (htot : tagTotal (D.FS.tag L) sym s + tδ ≤ D.FS.dT s)
    (htW : ∀ ω ∈ 𝒞, tU + ∑ c, wP D L isG ω c ≤ D.GB.U₀)
    (rSym : ∀ ω, ι ω → (∀ b, Option (D.FS.Ib L b)) → ℝ) (hrSym0 : ∀ ω i σ, 0 ≤ rSym ω i σ)
    (hsymT : ∀ ω ∈ 𝒞, ∀ i, ∀ σ ∈ (univ.filter
        (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)).filter
        (fun σ => countVec (D.FS.tag L) σ = Pi.single s 1),
      |catT D L A isG (Choice.support ω) (Q ω i) (Q ω (hC ω i)) σ (fun _ => false)| ≤
        ((1 + sfEps D L) * cX D L ω * D.Y L A) *
          (tagWeight (D.FS.tag L) sym (D.FS.vprice L) (fun _ => 0) s σ *
            ∏ c, (1 + vP D L isG ω c)) + rSym ω i σ) :
    (∀ ω ∈ 𝒞, ∀ i,
      |paperEN D L A (Choice.support ω)
          (place reservedCut (prodWeight (mb ω)) (prodPlace reservedCut (φb ω)) (Cop ω i)) -
        paperEN0 D L A (Choice.support ω)
          (place reservedCut (prodWeight (mb ω)) (prodPlace reservedCut (φb ω)) (Cop ω i))| ≤
        (D.GB.Rerr + sfEps D L * D.GB.Rerr) * cX D L ω * D.Y L A +
          r3 D L A isG ω (Q ω) (hC ω) s (rSym ω) i) ∧
    (∀ ω ∈ 𝒞, ∀ κ, slotPush (slotREquiv hR) κ = κ → ∀ i, κ = (1 / 2 : ℝ) •
      (place reservedCut (prodWeight (mb ω)) (prodPlace reservedCut (φb ω)) (Cop ω i) +
        place reservedCut (prodWeight (mb ω)) (prodPlace reservedCut (φb ω)) (Cop ω (hC ω i))) →
      |paperEN D L A (Choice.support ω) κ - paperEN0 D L A (Choice.support ω) κ| ≤
        (D.GB.Rerr - Real.exp tU * tδ + sfEps D L * D.GB.Rerr) * cX D L ω * D.Y L A +
          r3 D L A isG ω (Q ω) (hC ω) s (rSym ω) i) :=
  ⟨fun ω hω => (herr_hsym_of_tensor D h0 L A hY isG ω (Ob ω) (mb ω) (φb ω) (Cop ω) (Cb ω)
      (hCk ω hω) (Q ω) (hQ ω hω) (hC ω) s htδ sym hsym0 hsymd htot (htW ω hω) (rSym ω)
      (hrSym0 ω) (hsymT ω hω)).1,
    fun ω hω κ _ i hκ => (herr_hsym_of_tensor D h0 L A hY isG ω (Ob ω) (mb ω) (φb ω) (Cop ω)
      (Cb ω) (hCk ω hω) (Q ω) (hQ ω hω) (hC ω) s htδ sym hsym0 hsymd htot (htW ω hω) (rSym ω)
      (hrSym0 ω) (hsymT ω hω)).2 κ i hκ⟩

omit [DecidableEq P] in
/-- **The input `hκ` of `hsymT_of_sym` from `hpush`**: at tensor couplings, the orbit average
`κ̄ = ½(⊗Q_C + ⊗Q_{hC})` is `R_h`-invariant when `R_{h*}[C] = [hC]` for the involution `C ↦ hC`
(`orbitAvg_invariant`). -/
theorem orbitBar_invariant (L : ℕ) (ω : Choice (D.CL.T L))
    (Ob : {b // b ∈ Choice.support ω} → Type) [∀ b, Fintype (Ob b)] [∀ b, DecidableEq (Ob b)]
    (mb : ∀ b, Ob b → ℝ)
    (φb : ∀ b, Ob b → (reservedCut.Half → BlockLabel m₀ blk paperTail L b.1))
    {ι : Type*} (Cop : ι → ((∀ b, Ob b) → ℝ) →ₗ[ℝ] ((∀ b, Ob b) → ℝ))
    (Cb : ι → ∀ b, (Ob b → ℝ) →ₗ[ℝ] (Ob b → ℝ))
    (hCk : ∀ i x y, kern (prodWeight mb) (Cop i) x y = ∏ b, kern (mb b) (Cb i b) (x b) (y b))
    (Q : ι → ∀ b, TheoremCBlock.AtomMeasure m₀ blk paperTail L b)
    (hQ : ∀ i, ∀ b : {b // b ∈ Choice.support ω},
      Q i b.1 = place reservedCut (mb b) (φb b) (Cb i b))
    (hR : ZMod 6) (hC : ι → ι) (hh : ∀ i, hC (hC i) = i)
    (hpush : ∀ i, slotPush (slotREquiv hR)
      (place reservedCut (prodWeight mb) (prodPlace reservedCut φb) (Cop i)) =
        place reservedCut (prodWeight mb) (prodPlace reservedCut φb) (Cop (hC i))) (i : ι) :
    slotPush (slotREquiv hR) (orbitBar L (Choice.support ω) (Q i) (Q (hC i))) =
      orbitBar L (Choice.support ω) (Q i) (Q (hC i)) := by
  have ht : ∀ j, place reservedCut (prodWeight mb) (prodPlace reservedCut φb) (Cop j) =
      tensorLaw fun b : {b // b ∈ Choice.support ω} => Q j b.1 := by
    intro j
    rw [place_tensor reservedCut mb φb (Cb j) (Cop j) (hCk j)]
    congr 1
    funext b
    exact (hQ j b).symm
  have h := orbitAvg_invariant hh
    (fun j => place reservedCut (prodWeight mb) (prodPlace reservedCut φb) (Cop j)) hpush i
  simp only [ht] at h
  exact h

omit [DecidableEq P] in
/-- **B11's `paperDegreeOps` with `hE1` and Step 3 discharged at tensor couplings**:
`paperDegreeOpsS` with `herr` and `hsym` from `herr_hsym_class` (`Rerr = R_err`, `z' = ε R_err`,
`r = r3`). Step 3's only analytic input left is `hsymT` (the `G`-free term at the symmetric price,
`hsymT_of_sym` states it on the symmetric part); `r3_class_sum` bounds the `hrr` sum. -/
noncomputable def paperDegreeOpsT (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j)) (L : ℕ)
    (A : Finset ℤ) (𝒞 : Finset (Choice (D.CL.T L)))
    (hsel : ∀ ω ∈ 𝒞, IsSelection ω) (π ρ rr : Choice (D.CL.T L) → ℝ) (WZ z K : ℝ)
    (hY : 0 ≤ D.Y L A)
    -- the product objects
    (Ob : ∀ ω : Choice (D.CL.T L), {b // b ∈ Choice.support ω} → Type)
    [∀ ω b, Fintype (Ob ω b)] [∀ ω b, DecidableEq (Ob ω b)]
    (mb : ∀ ω b, Ob ω b → ℝ)
    (φb : ∀ ω b, Ob ω b → (reservedCut.Half → BlockLabel m₀ blk paperTail L b.1))
    -- the operators and B11's Steps 1–2 inputs
    (Lop Υop Dop : ∀ ω, ((∀ b, Ob ω b) → ℝ) →ₗ[ℝ] ((∀ b, Ob ω b) → ℝ))
    (hdom : ∀ ω ∈ 𝒞, OpLE (prodWeight (mb ω)) (Lop ω) (Dop ω) ∧
      OpLE (prodWeight (mb ω)) (-Lop ω) (Dop ω))
    (υ : Choice (D.CL.T L) → ℝ) (hυ : ∀ ω ∈ 𝒞, 0 ≤ υ ω)
    (hΥsym : ∀ ω ∈ 𝒞, ∀ f g,
      ip (prodWeight (mb ω)) f (Υop ω g) = ip (prodWeight (mb ω)) g (Υop ω f))
    (hΥ : ∀ ω ∈ 𝒞, ∀ f, |ip (prodWeight (mb ω)) f (Υop ω f)| ≤ υ ω * ip (prodWeight (mb ω)) f f)
    -- (E1): the envelope bound and the identification of the norm envelopes
    (hD : ∀ ω ∈ 𝒞, ∀ b (hb : b ∈ Choice.support ω), ∀ t e, ω b = some (t, e) →
      reservedCut.diagonalLaw (push (mb ω ⟨b, hb⟩) (φb ω ⟨b, hb⟩)) = D.CL.D L b t e)
    {εE : ℝ} (rE : Choice (D.CL.T L) → ℝ) (hz : εE ≤ z)
    (hEB : ∀ ω : Choice (D.CL.T L), IsSelection ω →
      diagonalIntegral (envelopeLaw (D.GB.N L) (D.CL.D L) ω) (blockLift m₀ blk paperTail L A) ≤
        (D.B + εE) * cX D L ω * D.Y L A + rE ω)
    -- (N4)
    (wt : Choice (D.CL.T L) → ℝ) (hwt : ∀ ω ∈ 𝒞, 0 ≤ wt ω)
    (hN4 : ∀ ω ∈ 𝒞, selTensor D L ω = wt ω •
      (place reservedCut (prodWeight (mb ω)) (prodPlace reservedCut (φb ω)) (Lop ω) +
        place reservedCut (prodWeight (mb ω)) (prodPlace reservedCut (φb ω)) (Υop ω)))
    -- Step 3: the coupling expansion and the orbit coupon
    (ι : Choice (D.CL.T L) → Type) [∀ ω, Fintype (ι ω)] (coef : ∀ ω, ι ω → ℝ)
    (Cop : ∀ ω, ι ω → ((∀ b, Ob ω b) → ℝ) →ₗ[ℝ] ((∀ b, Ob ω b) → ℝ))
    (hDk : ∀ ω ∈ 𝒞, ∀ x y, kern (prodWeight (mb ω)) (Dop ω) x y =
      ∑ i, coef ω i * kern (prodWeight (mb ω)) (Cop ω i) x y)
    (hR : ZMod 6) (hC : ∀ ω, ι ω → ι ω) (hh : ∀ ω ∈ 𝒞, ∀ i, hC ω (hC ω i) = i)
    (hpush : ∀ ω ∈ 𝒞, ∀ i, slotPush (slotREquiv hR)
      (place reservedCut (prodWeight (mb ω)) (prodPlace reservedCut (φb ω)) (Cop ω i)) =
        place reservedCut (prodWeight (mb ω)) (prodPlace reservedCut (φb ω)) (Cop ω (hC ω i)))
    -- Step 3 at tensor couplings (`herr_hsym_class`)
    (Cb : ∀ ω, ι ω → ∀ b, (Ob ω b → ℝ) →ₗ[ℝ] (Ob ω b → ℝ))
    (hCk : ∀ ω ∈ 𝒞, ∀ i x y, kern (prodWeight (mb ω)) (Cop ω i) x y =
      ∏ b, kern (mb ω b) (Cb ω i b) (x b) (y b))
    (Q : ∀ ω, ι ω → ∀ b, TheoremCBlock.AtomMeasure m₀ blk paperTail L b)
    (hQ : ∀ ω ∈ 𝒞, ∀ i, ∀ b : {b // b ∈ Choice.support ω},
      Q ω i b.1 = place reservedCut (mb ω b) (φb ω b) (Cb ω i b))
    (isG : ∀ b : BlockAtom Bk PaperJt L, D.GB.Iu L b → Bool) (s : D.FS.Tag)
    (tU tδ : ℝ) (hRerr : 0 ≤ D.GB.Rerr) (htδ : 0 ≤ tδ)
    (sym : ∀ b, D.FS.Ib L b → ℝ) (hsym0 : ∀ b i, 0 ≤ sym b i)
    (hsymd : ∀ b i, sym b i ≤ D.FS.dprice L b i)
    (htot : tagTotal (D.FS.tag L) sym s + tδ ≤ D.FS.dT s)
    (htW : ∀ ω ∈ 𝒞, tU + ∑ c, wP D L isG ω c ≤ D.GB.U₀)
    (rSym : ∀ ω, ι ω → (∀ b, Option (D.FS.Ib L b)) → ℝ) (hrSym0 : ∀ ω i σ, 0 ≤ rSym ω i σ)
    (hsymT : ∀ ω ∈ 𝒞, ∀ i, ∀ σ ∈ (univ.filter
        (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)).filter
        (fun σ => countVec (D.FS.tag L) σ = Pi.single s 1),
      |catT D L A isG (Choice.support ω) (Q ω i) (Q ω (hC ω i)) σ (fun _ => false)| ≤
        ((1 + sfEps D L) * cX D L ω * D.Y L A) *
          (tagWeight (D.FS.tag L) sym (D.FS.vprice L) (fun _ => 0) s σ *
            ∏ c, (1 + vP D L isG ω c)) + rSym ω i σ)
    (hzc : ∀ ω ∈ 𝒞, couplingMass (coef ω) * (sfEps D L * D.GB.Rerr) ≤ z)
    -- Step 4 and the evaluations
    (r₄ M Minv : ℝ)
    (step4 : ∑ ω ∈ 𝒞, wt ω * paperEN0 D L A (Choice.support ω)
        (place reservedCut (prodWeight (mb ω)) (prodPlace reservedCut (φb ω)) (Dop ω)) ≤
      WZ + z * (∑ ω ∈ 𝒞, wt ω * cX D L ω) * D.Y L A + r₄)
    (hM : ∑ ω ∈ 𝒞, wt ω * cX D L ω * couplingMass (coef ω) ≤ M * ∑ ω ∈ 𝒞, wt ω * cX D L ω)
    (hMinv : Minv * ∑ ω ∈ 𝒞, wt ω * cX D L ω ≤
      ∑ ω ∈ 𝒞, wt ω * cX D L ω * orbitMass (hC ω) (coef ω))
    (hρ : (M * D.GB.Rerr - Minv * Real.exp tU * tδ) * (∑ ω ∈ 𝒞, wt ω * cX D L ω) +
      D.B * (∑ ω ∈ 𝒞, wt ω * υ ω * cX D L ω) ≤ ∑ ω ∈ 𝒞, ρ ω)
    (hπ : ∀ ω ∈ 𝒞, wt ω * (2 + υ ω) * cX D L ω ≤ K * π ω)
    (hrr : ∑ ω ∈ 𝒞, wt ω * (υ ω * rE ω +
        ∑ i, |coef ω i| * r3 D L A isG ω (Q ω) (hC ω) s (rSym ω) i) + r₄ ≤ ∑ ω ∈ 𝒞, rr ω) :
    DegreeOps reservedCut 𝒞
      (fun ω => term (D.FS.lam L) (D.CL.ζ L) (blockLift m₀ blk paperTail L A) ω)
      π ρ rr WZ (D.Y L A) z K :=
    paperDegreeOpsS D L A 𝒞 hsel π ρ rr WZ z K hY Ob mb φb Lop Υop Dop hdom υ hυ hΥsym hΥ hD rE hz
      hEB wt hwt hN4 ι coef Cop hDk hR hC hh hpush D.GB.Rerr (sfEps D L * D.GB.Rerr) tU tδ hRerr htδ
      (fun ω i => r3 D L A isG ω (Q ω) (hC ω) s (rSym ω) i)
      (herr_hsym_class D h0 L A hY isG 𝒞 Ob mb φb ι Cop Cb hCk Q hQ hR hC s htδ sym hsym0 hsymd
        htot htW rSym hrSym0 hsymT).1
      (herr_hsym_class D h0 L A hY isG 𝒞 Ob mb φb ι Cop Cb hCk Q hQ hR hC s htδ sym hsym0 hsymd
        htot htW rSym hrSym0 hsymT).2
      hzc r₄ M Minv step4 hM hMinv hρ hπ hrr

end Sarkozy.OpsSteps
