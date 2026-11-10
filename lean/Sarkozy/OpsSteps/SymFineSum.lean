module

public import Sarkozy.OpsSteps.SymFine
public import Sarkozy.OpsSteps.Prices

@[expose] public section

/-!
# `hsym` with the terms with `G` proved (OPS-S)

`paper/sections/23_envelopes.tex`, proof of `lem:orbit-coupon`(i).

* `cat_poly_le_total`, `hcat_of_terms_total`: `SymCat`'s evaluation with the two price totals
  `∑(v + w) ≤ U₀` and `tU + ∑ w ≤ U₀` of `Prices` (no upper prices);
* `hVW_P`: the first total at the piece prices `vP`, `wP` (`U₀_total`);
* **`sum_rQ_le_pieceBnd`**, **`rQ_class_sum`**: the remainders `rQ` of the terms with `G` (and all
  other expanded terms) sum, over couplings and class selections, to `M K₁ c L^{-σ} α`
  (`QMain`'s argument: `qCoupSmallPT_proved` on the small unions, Hölder on the large ones,
  `pieceBnd_summable`);
* **`hsym_fine`**: `hsym` for an orbit average, with **one** remaining per-term input: the `G`-free
  term at the symmetric price, `|T_{σ,∅}| ≤ K s_σ ∏(1 + v) + r_σ`
  (`lem:record:one-stage-folded-e`(e), in the form of `SymSwap.catT_zero_sym`); the terms with `G`
  are `SymFine.abs_catT_le`.
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

section Generic

/-- **`cat_poly_le` with the two price totals** (`Prices.background_le_total`): if every term
`T_Z` is at most `K · price(Z) ∏_{Z} w ∏_{Zᶜ}(1 + v) + r_Z`, the price being `s` at `Z = ∅` and
`d` otherwise, then `|∑_Z T_Z| ≤ K (d e^{U₀} − (d − s) e^{tU}) + ∑_Z r_Z`. -/
theorem cat_poly_le_total {ι : Type*} [Fintype ι] [DecidableEq ι] (T r : (ι → Bool) → ℝ)
    {K dd ss U₀ tU : ℝ} {v w : ι → ℝ} (hK : 0 ≤ K) (hs : 0 ≤ ss) (hsd : ss ≤ dd)
    (hv : ∀ b, 0 ≤ v b) (hw : ∀ b, 0 ≤ w b)
    (hVW : ∑ b, (v b + w b) ≤ U₀) (htW : tU + ∑ b, w b ≤ U₀)
    (hT : ∀ f, |T f| ≤ K * ((if f = (fun _ => false) then ss else dd) *
      ∏ c, (if f c then w c else 1 + v c)) + r f) :
    |∑ f, T f| ≤ K * (dd * Real.exp U₀ - (dd - ss) * Real.exp tU) + ∑ f, r f := by
  have h1 : |∑ f, T f| ≤ ∑ f, (K * ((if f = (fun _ => false) then ss else dd) *
      ∏ c, (if f c then w c else 1 + v c)) + r f) :=
    (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun f _ => hT f)
  rw [sum_add_distrib, ← mul_sum, background_poly_eq v w dd ss] at h1
  have h2 := mul_le_mul_of_nonneg_left (background_le_total univ hs hsd hv hw hVW htW) hK
  linarith

end Generic

section Gen

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ) (A : Finset ℤ)
  (isG : ∀ b : BlockAtom Bk J L, D.GB.Iu L b → Bool) (S : Finset (BlockAtom Bk J L))

omit [DecidableEq P] in
/-- **`hcat_of_terms` with the two price totals**: `∑(v + w) ≤ U₀` and `tU + ∑ w ≤ U₀`
(`Prices`).

**`hcat` from the per-term bounds** (`lem:orbit-coupon`(i), see the module docstring). With
`d_σ`, `s_σ` the sharp and symmetric prices of the single difference of `σ`, every expanded term
`T_{σ,Z}` of a choice `σ ∈ e_s` is assumed at most `K · (Z = ∅ ? s_σ : d_σ) ∏_Z w ∏_{Zᶜ}(1 + v) + r`
(`hterm`, C). Then the category satisfies the input `hcat` of `hsym_of_category`. -/
theorem hcat_of_terms_total (Q₁ Q₂ : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (s : D.FS.Tag)
    {K tU tδ : ℝ} (hK : 0 ≤ K)
    (sym : ∀ b, D.FS.Ib L b → ℝ) (hsym0 : ∀ b i, 0 ≤ sym b i)
    (hsymd : ∀ b i, sym b i ≤ D.FS.dprice L b i)
    (htot : tagTotal (D.FS.tag L) sym s + tδ ≤ D.FS.dT s)
    {v w : BlockAtom Bk J L → ℝ} (hv : ∀ b, 0 ≤ v b) (hw : ∀ b, 0 ≤ w b)
    (hVW : ∑ b, (v b + w b) ≤ D.GB.U₀) (htW : tU + ∑ b, w b ≤ D.GB.U₀)
    (r : (∀ b, Option (D.FS.Ib L b)) → (BlockAtom Bk J L → Bool) → ℝ)
    (hterm : ∀ σ ∈ (univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)).filter
        (fun σ => countVec (D.FS.tag L) σ = Pi.single s 1), ∀ f,
      |catT D L A isG S Q₁ Q₂ σ f| ≤
        K * ((if f = (fun _ => false) then
            tagWeight (D.FS.tag L) sym (D.FS.vprice L) (fun _ => 0) s σ
          else tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (fun _ => 0) s σ) *
          ∏ c, (if f c then w c else 1 + v c)) + r σ f) :
    |∑ σ ∈ (univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)).filter
        (fun σ => countVec (D.FS.tag L) σ = Pi.single s 1),
        (1 / 2 : ℝ) * (Eσ D L A S Q₁ σ + Eσ D L A S Q₂ σ)| ≤
      K * (D.FS.dT s * Real.exp D.GB.U₀ - Real.exp tU * tδ) +
        ∑ σ ∈ (univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)).filter
          (fun σ => countVec (D.FS.tag L) σ = Pi.single s 1), ∑ f, r σ f := by
  set 𝒮 := (univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)).filter
    (fun σ => countVec (D.FS.tag L) σ = Pi.single s 1) with h𝒮def
  have h𝒮 : ∀ σ ∈ 𝒮, countVec (D.FS.tag L) σ = Pi.single s 1 :=
    fun σ hσ => (mem_filter.mp hσ).2
  have hd0 : ∀ b i, 0 ≤ D.FS.dprice L b i := fun b i => D.dprice_nonneg L b i
  have hv0 : ∀ b i, 0 ≤ D.FS.vprice L b i := fun b i => D.vprice_nonneg L b i
  have h0 : ∀ b : BlockAtom Bk J L, 0 ≤ (fun _ => (0 : ℝ)) b := fun _ => le_rfl
  have hper : ∀ σ ∈ 𝒮, |(1 / 2 : ℝ) * (Eσ D L A S Q₁ σ + Eσ D L A S Q₂ σ)| ≤
      K * (tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (fun _ => 0) s σ *
          Real.exp D.GB.U₀ -
        (tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (fun _ => 0) s σ -
          tagWeight (D.FS.tag L) sym (D.FS.vprice L) (fun _ => 0) s σ) * Real.exp tU) +
        ∑ f, r σ f := by
    intro σ hσ
    rw [avg_eq_sum_catT D L A isG S Q₁ Q₂ σ]
    exact cat_poly_le_total _ (r σ) hK (tagWeight_nonneg _ hsym0 hv0 h0 s σ)
      (tagWeight_mono _ hsym0 hsymd hv0 h0 s σ) hv hw hVW htW (hterm σ hσ)
  have hD : ∑ σ ∈ 𝒮, tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (fun _ => 0) s σ ≤
      D.FS.dT s :=
    (sum_single_tagWeight_le _ hd0 hv0 s 𝒮 h𝒮).trans (D.FS.dT_total L s)
  have hS : ∑ σ ∈ 𝒮, tagWeight (D.FS.tag L) sym (D.FS.vprice L) (fun _ => 0) s σ ≤
      tagTotal (D.FS.tag L) sym s := sum_single_tagWeight_le _ hsym0 hv0 s 𝒮 h𝒮
  have htU : tU ≤ D.GB.U₀ := by
    have hn : 0 ≤ ∑ b, w b := sum_nonneg fun b _ => hw b
    linarith
  have hexp : Real.exp tU ≤ Real.exp D.GB.U₀ := Real.exp_le_exp.mpr htU
  set dS := ∑ σ ∈ 𝒮, tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (fun _ => 0) s σ
    with hdS
  set sS := ∑ σ ∈ 𝒮, tagWeight (D.FS.tag L) sym (D.FS.vprice L) (fun _ => 0) s σ with hsS
  have hdist : ∑ σ ∈ 𝒮, K *
      (tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (fun _ => 0) s σ *
          Real.exp D.GB.U₀ -
        (tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (fun _ => 0) s σ -
          tagWeight (D.FS.tag L) sym (D.FS.vprice L) (fun _ => 0) s σ) * Real.exp tU) =
      K * ((Real.exp D.GB.U₀ - Real.exp tU) * dS + Real.exp tU * sS) := by
    simp only [hdS, hsS, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun σ _ => by ring
  have h1 : (Real.exp D.GB.U₀ - Real.exp tU) * dS ≤ (Real.exp D.GB.U₀ - Real.exp tU) * D.FS.dT s :=
    mul_le_mul_of_nonneg_left hD (by linarith)
  have h2 : Real.exp tU * sS ≤ Real.exp tU * (D.FS.dT s - tδ) :=
    mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  have h3 := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hK
  have h4 : K * ((Real.exp D.GB.U₀ - Real.exp tU) * D.FS.dT s + Real.exp tU * (D.FS.dT s - tδ)) =
      K * (D.FS.dT s * Real.exp D.GB.U₀ - Real.exp tU * tδ) := by ring
  calc _ ≤ ∑ σ ∈ 𝒮, |(1 / 2 : ℝ) * (Eσ D L A S Q₁ σ + Eσ D L A S Q₂ σ)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ σ ∈ 𝒮, (K *
          (tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (fun _ => 0) s σ *
              Real.exp D.GB.U₀ -
            (tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (fun _ => 0) s σ -
              tagWeight (D.FS.tag L) sym (D.FS.vprice L) (fun _ => 0) s σ) * Real.exp tU) +
          ∑ f, r σ f) := sum_le_sum hper
    _ = K * ((Real.exp D.GB.U₀ - Real.exp tU) * dS + Real.exp tU * sS) +
          ∑ σ ∈ 𝒮, ∑ f, r σ f := by rw [sum_add_distrib, hdist]
    _ ≤ _ := by linarith

end Gen

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)

omit [DecidableEq P] in
/-- **The piece prices of the outside atoms add up to at most `U₀`** (`U₀_total`). -/
theorem hVW_P (L : ℕ) (isG : ∀ b : BlockAtom Bk PaperJt L, D.GB.Iu L b → Bool)
    (ω : Choice (D.CL.T L)) : ∑ c, (vP D L isG ω c + wP D L isG ω c) ≤ D.GB.U₀ := by
  refine le_trans (sum_le_sum fun c _ => ?_) (D.GB.U₀_total L)
  unfold vP wP
  split_ifs
  · rw [add_zero]
    exact sum_nonneg fun i _ => mul_nonneg
      (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.GB.κu_pos L c i).1)
      (D.selectionFactor_nonneg L c)
  · have e := sum_filter_add_sum_filter_not univ (fun i => isG c i = false)
      (fun i => mass (D.GB.κu L c i) * TheoremCBlock.selectionFactor a paperTail D.S.selPre L c)
    simp only [Bool.not_eq_false] at e
    rw [e]

omit [DecidableEq P] in
theorem rQ_nonneg (L : ℕ) (isG : ∀ b : BlockAtom Bk PaperJt L, D.GB.Iu L b → Bool) (εE : ℕ → ℝ)
    (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (Q₁ Q₂ : ∀ b, TheoremCBlock.AtomMeasure m₀ blk paperTail L b) (s : D.FS.Tag)
    (σ : ∀ b, Option (D.FS.Ib L b)) (f : BlockAtom Bk PaperJt L → Bool) :
    0 ≤ rQ D L isG εE A ω Q₁ Q₂ s σ f := by
  unfold rQ
  split_ifs
  · exact mul_nonneg (by norm_num) (sum_nonneg fun g _ => mul_nonneg
      (prod_nonneg fun b _ => abs_nonneg _)
      (add_nonneg (qX_nonneg D L _ εE A ω σ s g) (qX_nonneg D L _ εE A ω σ s g)))
  · exact le_rfl

omit [DecidableEq P] in
/-- **The expanded remainders of the category `e_s` are at most the law-independent piece
bound.** -/
theorem sum_rQ_le_pieceBnd {L : ℕ} {A : Finset ℤ}
    (isG : ∀ b : BlockAtom Bk PaperJt L, D.GB.Iu L b → Bool) (hY : 0 ≤ D.Y L A) {rem B : ℝ}
    (hrem : 0 ≤ rem)
    (hB : (FiniteLaw.uniform (∀ b : BlockAtom Bk PaperJt L, BlockLabel m₀ blk paperTail L b)).moment
      72 (blockLift m₀ blk paperTail L A) ≤ B)
    (ω : Choice (D.CL.T L)) (Q₁ Q₂ : ∀ b, TheoremCBlock.AtomMeasure m₀ blk paperTail L b)
    (hQp₁ : ∀ b ∈ Choice.support ω, IsProbability (Q₁ b))
    (hQu₁ : ∀ b ∈ Choice.support ω, HasUniformSlotMarginals (Q₁ b))
    (hQp₂ : ∀ b ∈ Choice.support ω, IsProbability (Q₂ b))
    (hQu₂ : ∀ b ∈ Choice.support ω, HasUniformSlotMarginals (Q₂ b)) (s : D.FS.Tag)
    (hpt : ∀ Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk paperTail L b,
      (∀ b ∈ Choice.support ω, IsProbability (Qb b)) →
      (∀ b ∈ Choice.support ω, HasUniformSlotMarginals (Qb b)) →
      ∀ σ : (∀ b, Option (D.FS.Ib L b)), ∀ j, ∀ f : (∀ b, CEPiece D L b),
      (∀ b, ecpieceCoef D L ω σ j b (f b) ≠ 0) → CoupSmall D L ω f →
      |qInt D L (qfOf D L (Choice.support ω) Qb) A ω f| ≤ coupMain D (sfEps D) L A ω f +
        (∏ b, cM D L b (f b)) * rem) :
    ∑ σ ∈ (univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)).filter
        (fun σ => countVec (D.FS.tag L) σ = Pi.single s 1),
        ∑ f, rQ D L isG (sfEps D) A ω Q₁ Q₂ s σ f ≤
      ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        ∑ j, ∑ g, (∏ b, |ecpieceCoef D L ω σ j b (g b)|) * pieceBnd D L rem B ω g := by
  have hpiece : ∀ Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk paperTail L b,
      (∀ b ∈ Choice.support ω, IsProbability (Qb b)) →
      (∀ b ∈ Choice.support ω, HasUniformSlotMarginals (Qb b)) →
      ∀ σ j g, (∏ b, |ecpieceCoef D L ω σ j b (g b)|) *
        qX D L (qfOf D L (Choice.support ω) Qb) (sfEps D) A ω σ j g ≤
        (∏ b, |ecpieceCoef D L ω σ j b (g b)|) * pieceBnd D L rem B ω g := by
    intro Qb hQp hQu σ j g
    by_cases hs : CoupSmall D L ω g
    · exact qX_le_pieceBnd_small D hrem ω σ j g hs (fun hcf => hpt Qb hQp hQu σ j g hcf hs)
    · exact mul_le_mul_of_nonneg_left
        (qX_le_pieceBnd_large (D.S.p_prime L) (qfOf_prob D L _ Qb hQp) (qfOf_unif D L _ Qb hQu)
          (sfEps_nonneg D) A hY hB ω σ j g hs)
        (prod_nonneg fun b _ => abs_nonneg _)
  have hB0 : ∀ σ j g, 0 ≤ (∏ b, |ecpieceCoef D L ω σ j b (g b)|) * pieceBnd D L rem B ω g :=
    fun σ j g => (mul_nonneg (prod_nonneg fun b _ => abs_nonneg _)
      (qX_nonneg D L _ (sfEps D) A ω σ j g)).trans
        (hpiece Q₁ hQp₁ hQu₁ σ j g)
  have hσ : ∀ σ, ∑ f, rQ D L isG (sfEps D) A ω Q₁ Q₂ s σ f ≤
      ∑ g, (∏ b, |ecpieceCoef D L ω σ s b (g b)|) * pieceBnd D L rem B ω g := by
    intro σ
    refine (sum_rQ_le D L isG (sfEps D) A ω Q₁ Q₂ s σ).trans ?_
    rw [mul_sum]
    refine sum_le_sum fun g _ => ?_
    have h1 := hpiece Q₁ hQp₁ hQu₁ σ s g
    have h2 := hpiece Q₂ hQp₂ hQu₂ σ s g
    nlinarith
  calc _ ≤ ∑ σ ∈ (univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)).filter
          (fun σ => countVec (D.FS.tag L) σ = Pi.single s 1),
          ∑ g, (∏ b, |ecpieceCoef D L ω σ s b (g b)|) * pieceBnd D L rem B ω g :=
        sum_le_sum fun σ _ => hσ σ
    _ ≤ ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          ∑ g, (∏ b, |ecpieceCoef D L ω σ s b (g b)|) * pieceBnd D L rem B ω g :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun σ _ _ =>
          sum_nonneg fun g _ => hB0 σ s g
    _ ≤ _ := sum_le_sum fun σ _ =>
        single_le_sum (f := fun j => ∑ g, (∏ b, |ecpieceCoef D L ω σ j b (g b)|) *
          pieceBnd D L rem B ω g) (fun j _ => sum_nonneg fun g _ => hB0 σ j g) (mem_univ s)

omit [DecidableEq P] in
/-- **The remainders of the expanded category `e_s` sum to a remainder**: on the paper's tails
there is `c ≥ 0` such that at every least counterexample, for every split `isG`, tag `s`, set `𝒞`
of selections, weights `0 ≤ w ≤ K₁ π̃` and families of orbit pairs `(Q₁, Q₂)` with coefficient
mass `≤ M` (probability laws with uniform one-slot marginals on the support),
`∑_ω w_ω ∑_i |c_i| ∑_{σ ∈ e_s} ∑_Z rQ_{σ,Z} ≤ M K₁ c L^{-σ} α`. -/
theorem rQ_class_sum
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
      ∀ (Q₁ Q₂ : ∀ ω, ι ω → ∀ b, TheoremCBlock.AtomMeasure m₀ blk paperTail L b),
      (∀ ω ∈ 𝒞, ∀ i, ∀ b ∈ Choice.support ω, IsProbability (Q₁ ω i b)) →
      (∀ ω ∈ 𝒞, ∀ i, ∀ b ∈ Choice.support ω, HasUniformSlotMarginals (Q₁ ω i b)) →
      (∀ ω ∈ 𝒞, ∀ i, ∀ b ∈ Choice.support ω, IsProbability (Q₂ ω i b)) →
      (∀ ω ∈ 𝒞, ∀ i, ∀ b ∈ Choice.support ω, HasUniformSlotMarginals (Q₂ ω i b)) →
      ∑ ω ∈ 𝒞, wt ω * ∑ i, |coef ω i| *
          ∑ σ ∈ (univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)).filter
            (fun σ => countVec (D.FS.tag L) σ = Pi.single s 1),
            ∑ f, rQ D L isG (sfEps D) A ω (Q₁ ω i) (Q₂ ω i) s σ f ≤
        remainder (M * K₁ * c) L A) := by
  obtain ⟨c₁, hc₁, hPT⟩ := qCoupSmallPT_proved D hpair ha hpar hsel hne
  obtain ⟨Cm, -, c, hc, hsum⟩ := pieceBnd_summable D ha hc₁
  refine ⟨c, hc, ?_⟩
  filter_upwards [hPT, hsum] with L hPTL hsumL
  intro C hC hk A hA hYc isG s 𝒞 h𝒞 wt K₁ M hK₁ hM0 hwt0 hwt ι _ coef hM Q₁ Q₂ hQp₁ hQu₁ hQp₂
    hQu₂
  have hY : 0 ≤ D.Y L A := (Param.counterexample_pos (Params.ofDecay a) hC hYc).le
  obtain ⟨hB0, hB, _, hS⟩ := hsumL A
  set rem := remainder c₁ L A with hremdef
  have hrem0 : 0 ≤ rem := E1Closure.remainder_nonneg' hc₁ L A
  set SS := univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)
  set ES := SS.filter (fun σ => countVec (D.FS.tag L) σ = Pi.single s 1)
  set Bnd : Choice (D.CL.T L) → ℝ := fun ω => ∑ σ ∈ SS, ∑ j, ∑ f,
    (∏ b, |ecpieceCoef D L ω σ j b (f b)|) * pieceBnd D L rem (momB (m₀ := m₀) Cm L A) ω f
    with hBnd
  have hBnd0 : ∀ ω, 0 ≤ Bnd ω := fun ω => sum_nonneg fun σ _ => sum_nonneg fun j _ =>
    sum_nonneg fun f _ => mul_nonneg (prod_nonneg fun b _ => abs_nonneg _)
      (pieceBnd_nonneg D L (D.S.p_prime L) hrem0 hB0 ω f)
  have hper : ∀ ω ∈ 𝒞, ∀ i, ∑ σ ∈ ES, ∑ f, rQ D L isG (sfEps D) A ω (Q₁ ω i) (Q₂ ω i) s σ f ≤
      Bnd ω := by
    intro ω hω i
    exact sum_rQ_le_pieceBnd D isG hY hrem0 hB ω (Q₁ ω i) (Q₂ ω i) (hQp₁ ω hω i) (hQu₁ ω hω i)
      (hQp₂ ω hω i) (hQu₂ ω hω i) s
      (fun Qb hQp hQu σ j f hcf hs => hPTL C hC hk A hA hYc (qfOf D L (Choice.support ω) Qb)
        (qfOf_prob D L _ _ hQp) (qfOf_unif D L _ _ hQu) ω (h𝒞 ω hω) σ j f hcf hs)
  have hstep : ∀ ω ∈ 𝒞, wt ω * ∑ i, |coef ω i| *
      ∑ σ ∈ ES, ∑ f, rQ D L isG (sfEps D) A ω (Q₁ ω i) (Q₂ ω i) s σ f ≤
      (M * K₁) * (monomial (D.CL.πt L) ω * Bnd ω) := by
    intro ω hω
    have h1 : ∑ i, |coef ω i| *
        ∑ σ ∈ ES, ∑ f, rQ D L isG (sfEps D) A ω (Q₁ ω i) (Q₂ ω i) s σ f ≤ M * Bnd ω := by
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

omit [DecidableEq P] in
/-- **`hsym` for an orbit average, with the terms with `G` proved** (see the module docstring).
With `K = (1 + ε) C_X Y`, the symmetric prices `0 ≤ s ≤ d` with `∑_{tag s} s + tδ ≤ d_{T,s}`, the
generic-price condition `tU + ∑ w ≤ U₀`, and the `G`-free bound `hsymT` (C), the difference of the
energies of `κ̄ = ½(⊗Q₁ + ⊗Q₂)` is at most `(R_err − e^{tU} tδ) K` plus the canonical remainders
`rCan` (other categories), `r_σ` (the `G`-free terms) and `rQ` (the terms with `G`). -/
theorem hsym_fine (L : ℕ) (A : Finset ℤ) (isG : ∀ b : BlockAtom Bk PaperJt L, D.GB.Iu L b → Bool)
    (hY : 0 ≤ D.Y L A) (ω : Choice (D.CL.T L))
    (Q₁ Q₂ : ∀ b, TheoremCBlock.AtomMeasure m₀ blk paperTail L b) (s : D.FS.Tag) {tU tδ : ℝ}
    (sym : ∀ b, D.FS.Ib L b → ℝ) (hsym0 : ∀ b i, 0 ≤ sym b i)
    (hsymd : ∀ b i, sym b i ≤ D.FS.dprice L b i)
    (htot : tagTotal (D.FS.tag L) sym s + tδ ≤ D.FS.dT s)
    (htW : tU + ∑ c, wP D L isG ω c ≤ D.GB.U₀)
    (rSym : (∀ b, Option (D.FS.Ib L b)) → ℝ)
    (hsymT : ∀ σ ∈ (univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)).filter
        (fun σ => countVec (D.FS.tag L) σ = Pi.single s 1),
      |catT D L A isG (Choice.support ω) Q₁ Q₂ σ (fun _ => false)| ≤
        ((1 + sfEps D L) *
            (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a paperTail D.S.selPre L b) *
            D.Y L A) *
          (tagWeight (D.FS.tag L) sym (D.FS.vprice L) (fun _ => 0) s σ *
            ∏ c, (1 + vP D L isG ω c)) + rSym σ) :
    |paperEN D L A (Choice.support ω) ((1 / 2 : ℝ) •
        (tensorLaw (fun b : {b // b ∈ Choice.support ω} => Q₁ b.1) +
          tensorLaw (fun b : {b // b ∈ Choice.support ω} => Q₂ b.1))) -
      paperEN0 D L A (Choice.support ω) ((1 / 2 : ℝ) •
        (tensorLaw (fun b : {b // b ∈ Choice.support ω} => Q₁ b.1) +
          tensorLaw (fun b : {b // b ∈ Choice.support ω} => Q₂ b.1)))| ≤
      (D.GB.Rerr - Real.exp tU * tδ) *
          ((1 + sfEps D L) *
            (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a paperTail D.S.selPre L b) *
            D.Y L A) +
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          (1 / 2 : ℝ) * (rCan D L A (Choice.support ω) Q₁
              ((1 + sfEps D L) *
                (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a paperTail D.S.selPre L b) *
                D.Y L A) σ +
            rCan D L A (Choice.support ω) Q₂
              ((1 + sfEps D L) *
                (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a paperTail D.S.selPre L b) *
                D.Y L A) σ) +
        ∑ σ ∈ (univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)).filter
          (fun σ => countVec (D.FS.tag L) σ = Pi.single s 1),
          (rSym σ + ∑ f, rQ D L isG (sfEps D) A ω Q₁ Q₂ s σ f) := by
  set K := (1 + sfEps D L) *
    (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a paperTail D.S.selPre L b) * D.Y L A
    with hKdef
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (by linarith [sfEps_nonneg D L])
    (prod_nonneg fun b _ => D.selectionFactor_nonneg L b)) hY
  set r : (∀ b, Option (D.FS.Ib L b)) → (BlockAtom Bk PaperJt L → Bool) → ℝ := fun σ f =>
    if f = (fun _ => false) then rSym σ else rQ D L isG (sfEps D) A ω Q₁ Q₂ s σ f with hr
  have hterm : ∀ σ ∈ (univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)).filter
      (fun σ => countVec (D.FS.tag L) σ = Pi.single s 1), ∀ f,
      |catT D L A isG (Choice.support ω) Q₁ Q₂ σ f| ≤
        K * ((if f = (fun _ => false) then
            tagWeight (D.FS.tag L) sym (D.FS.vprice L) (fun _ => 0) s σ
          else tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (fun _ => 0) s σ) *
          ∏ c, (if f c then wP D L isG ω c else 1 + vP D L isG ω c)) + r σ f := by
    intro σ hσ f
    by_cases hf : f = fun _ => false
    · subst hf
      simp only [↓reduceIte, Bool.false_eq_true, r]
      exact hsymT σ hσ
    · have hcount : 1 ≤ countVec (D.FS.tag L) σ s := by
        rw [(mem_filter.mp hσ).2]
        simp
      simp only [hf, ↓reduceIte, r]
      exact abs_catT_le D L isG (sfEps D) (sfEps_nonneg D) A hY ω Q₁ Q₂ s σ hcount f
  have h := hsym_of_category D L A (sfEps D) (sfEps_nonneg D) hY ω Q₁ Q₂ s
    (hcat_of_terms_total D L A isG (Choice.support ω) Q₁ Q₂ s hK sym hsym0 hsymd htot
      (vP_nonneg D L isG ω) (wP_nonneg D L isG ω) (hVW_P D L isG ω) htW r hterm)
  refine h.trans ?_
  gcongr with σ hσ
  have hpt : ∀ f, r σ f ≤ (if f = (fun _ => false) then rSym σ else 0) +
      rQ D L isG (sfEps D) A ω Q₁ Q₂ s σ f := by
    intro f
    simp only [r]
    split_ifs
    · linarith [rQ_nonneg D L isG (sfEps D) A ω Q₁ Q₂ s σ f]
    · linarith
  refine (sum_le_sum fun f _ => hpt f).trans (le_of_eq ?_)
  rw [sum_add_distrib, sum_ite_eq' univ (fun _ => false) (fun _ => rSym σ)]
  simp

end Sarkozy.OpsSteps
