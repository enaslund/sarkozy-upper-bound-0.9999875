module

public import Sarkozy.OpsSteps.QSmall
public import Sarkozy.OpsSteps.Uniform

@[expose] public section

/-!
# The finer (E1) of Step 4 (i): the tags of `E_add + H` and of `G` priced separately (OPS-S)

`paper/sections/23_envelopes.tex`, proof of `thm:envelopes`, "(iii) and (i)" ("Expanding
`Ñ^inv_𝔅 = μ_𝔅 + (E_add + H)_𝔅` in every `O_Z`, each term of `Y^{O_Z}[Diag_ω]` is the energy of an
admissible positive measure with `μ` outside, at most `(1 + o(1)) C_X` times the product of the tag
prices times `Y` (E1), as in the proof of `lem:bracket-energy`");
`paper/sections/10_comparison_lemmas.tex`, `lem:bracket-energy`, `prop:record:density-structured`,
`lem:record:density-lp`.

EC's subset terms put the whole bracket record `∑_i κu_{𝔟,i} = Ñ_{0,𝔟} − μ_𝔟` at an atom. Step 4 (i)
needs them split into the invariant tags (`E_add + H`) and the generic tag (`G`), priced separately.
Given a split `isG` of the bracket records (`G_𝔟 = ∑_{isG} κu`, `(E_add + H)_𝔟 = ∑_{¬isG} κu`), the
finer terms choose at every atom `μ` (`none`), `G` (`some true`) or `E_add + H` (`some false`):

* `fineLaw`, `fineInt`, `finePr`, `fineMain`, `fX`: the finer terms, their main terms
  (`(1 + ε) C_X Y ∏ (tag prices)`) and their canonical remainders;
* **`envN0_eq_sum_fine`**: `Y[env_ω ⊗ Ñ₀] = ∑_g 𝔈_{ω,g}` (the finer expansion);
* **`collapse_sum`**: the finer masses add up to EC's (`mass G + mass(E_add + H) = mass ∑ κu`), so
  every law-independent weight summed over the finer terms is EC's sum over its subset terms;
* **`fineSmallPT_proved`**: a finer term with a small union is at most its main term plus
  `(∏ masses) c L^{-σ} α` (`whole_chain`, as EC's `e1SubSmallPT_proved`);
* **`fX_summable`**: `∑_ω π̃_ω ∑_g fX_{ω,g} ≤ c L^{-σ} α` at every least counterexample (small
  unions by the per-term bound and G1's summations; large unions by Hölder and Rankin).

So the finer (E1) of Step 4 (i) holds with summable remainders. What is left of `hfine`
(`Background.heval_of_finer`) is bookkeeping: grouping the finer terms by their set `Z` of `G`
atoms, and the identification of `isG` with the frame's `G` at the middle blocks (OPS-L's data).
-/

namespace Sarkozy.OpsSteps

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.CancellationSteps Sarkozy.BlockAnchor Sarkozy.DensityChain2
  Sarkozy.DensityFibre Sarkozy.EnvelopeInputsBlock Sarkozy.RecordExpansion
  Sarkozy.RecordExpansion.Choice Sarkozy.E1Closure
open Sarkozy.Param (Params)
open Sarkozy.SharpFirst (sfEps sfEps_nonneg whole_chain)
open Sarkozy.LargeSums (atomQR atomQR_nonneg atomPr)

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E) (L : ℕ)
  (isG : ∀ b : BlockAtom Bk PaperJt L, D.GB.Iu L b → Bool)

/-- **The laws of the finer terms**: `μ_𝔟` or the selected envelope (`none`), the generic tag
`G_𝔟 = ∑_{isG} κu` (`some true`), the invariant tags `∑_{¬isG} κu` (`some false`); `0` at a selected
atom for the tags. -/
noncomputable def fineLaw (b : BlockAtom Bk PaperJt L) (o : Option (D.CL.T L b × ChangeType)) :
    Option Bool → TheoremCBlock.AtomMeasure m₀ blk paperTail L b
  | none => entryFactor (D.R.law paperTail L b) (D.CL.D L b) o
  | some g => if o.isSome then 0 else ∑ i ∈ univ.filter (fun i => isG b i = g), D.GB.κu L b i

/-- The atoms that carry a tag. -/
def collapse (g : BlockAtom Bk PaperJt L → Option Bool) : BlockAtom Bk PaperJt L → Bool :=
  fun b => (g b).isSome

/-- The energy of a finer term. -/
noncomputable def fineInt (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (g : BlockAtom Bk PaperJt L → Option Bool) : ℝ :=
  diagonalIntegral (tensorLaw fun b => fineLaw D L isG b (ω b) (g b))
    (blockLift m₀ blk paperTail L A)

/-- The tag price of an atom in a finer term (`v_𝔟` or `w_𝔟`; `1` at `μ`). -/
noncomputable def finePr (b : BlockAtom Bk PaperJt L) (o : Option (D.CL.T L b × ChangeType)) :
    Option Bool → ℝ
  | none => 1
  | some g => if o.isSome then 0 else
      mass (∑ i ∈ univ.filter (fun i => isG b i = g), D.GB.κu L b i) *
        TheoremCBlock.selectionFactor a paperTail D.S.selPre L b

/-- The main term of a finer term: `(1 + ε) C_X Y ∏_𝔟 (tag price)`. -/
noncomputable def fineMain (εE : ℕ → ℝ) (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (g : BlockAtom Bk PaperJt L → Option Bool) : ℝ :=
  ((1 + εE L) * (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a paperTail D.S.selPre L b) *
    D.Y L A) * ∏ b, finePr D L isG b (ω b) (g b)

/-- The canonical remainder of a finer term. -/
noncomputable def fX (εE : ℕ → ℝ) (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (g : BlockAtom Bk PaperJt L → Option Bool) : ℝ :=
  max 0 (|fineInt D L isG A ω g| - fineMain D L isG εE A ω g)

/-! ## Masses and positivity -/

omit [DecidableEq P] in
theorem mass_filter_add (b : BlockAtom Bk PaperJt L) :
    mass (∑ i ∈ univ.filter (fun i => isG b i = true), D.GB.κu L b i) +
      mass (∑ i ∈ univ.filter (fun i => isG b i = false), D.GB.κu L b i) =
      mass (∑ i, D.GB.κu L b i) := by
  have e : (∑ i ∈ univ.filter (fun i => isG b i = true), D.GB.κu L b i) +
      (∑ i ∈ univ.filter (fun i => isG b i = false), D.GB.κu L b i) = ∑ i, D.GB.κu L b i := by
    have := sum_filter_add_sum_filter_not univ (fun i => isG b i = true) (fun i => D.GB.κu L b i)
    simpa using this
  rw [← e]
  rfl

omit [DecidableEq P] in
theorem isPositiveRecord_fineLaw (hp : ∀ j, (paperTail L j).Prime) (b : BlockAtom Bk PaperJt L)
    (o : Option (D.CL.T L b × ChangeType)) (y : Option Bool) :
    IsPositiveRecord (fineLaw D L isG b o y) := by
  rcases y with _ | g
  · exact isPositiveRecord_entryFactor D L hp b o
  · unfold fineLaw
    split_ifs
    · exact isPositiveRecord_zero
    · exact isPositiveRecord_sum _ _ fun i _ => D.GB.κu_pos L b i

omit [DecidableEq P] in
/-- **The finer masses collapse to EC's**: per atom, the fibre sums of the finer masses are the
masses of EC's subset laws. -/
theorem fiber_mass (b : BlockAtom Bk PaperJt L) (o : Option (D.CL.T L b × ChangeType)) (y : Bool) :
    ∑ z ∈ univ.filter (fun z : Option Bool => z.isSome = y), mass (fineLaw D L isG b o z) =
      mass (subLaw D L b o y) := by
  cases y
  · have : univ.filter (fun z : Option Bool => z.isSome = false) = {none} := by
      ext z; rcases z with _ | g <;> simp
    rw [this, sum_singleton]
    rfl
  · have : univ.filter (fun z : Option Bool => z.isSome = true) = {some true, some false} := by
      ext z; rcases z with _ | g
      · simp
      · cases g <;> simp
    rw [this, sum_pair (by simp)]
    unfold fineLaw subLaw
    by_cases ho : o.isSome
    · simp only [ho, ↓reduceIte, mass_zero_measure, add_zero]
    · simp only [ho, Bool.false_eq_true, ↓reduceIte]
      exact mass_filter_add D L isG b

omit [DecidableEq P] in
/-- **Every weight of the collapsed term, summed over the finer terms, is EC's sum.** -/
theorem collapse_sum (ω : Choice (D.CL.T L)) (F : (BlockAtom Bk PaperJt L → Bool) → ℝ) :
    ∑ g : (BlockAtom Bk PaperJt L → Option Bool),
        F (collapse L g) * ∏ b, mass (fineLaw D L isG b (ω b) (g b)) =
      ∑ f : BlockAtom Bk PaperJt L → Bool, F f * ∏ b, mass (subLaw D L b (ω b) (f b)) := by
  rw [← sum_fiberwise univ (collapse L)
    (fun g => F (collapse L g) * ∏ b, mass (fineLaw D L isG b (ω b) (g b)))]
  refine sum_congr rfl fun f _ => ?_
  have hfib : univ.filter (fun g : (BlockAtom Bk PaperJt L → Option Bool) =>
      collapse L g = f) = Fintype.piFinset fun b => univ.filter (fun z : Option Bool =>
        z.isSome = f b) := by
    ext g
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    exact funext_iff
  rw [hfib]
  have hc : ∀ g ∈ Fintype.piFinset (fun b => univ.filter (fun z : Option Bool =>
      z.isSome = f b)), F (collapse L g) * ∏ b, mass (fineLaw D L isG b (ω b) (g b)) =
      F f * ∏ b, mass (fineLaw D L isG b (ω b) (g b)) := by
    intro g hg
    have : collapse L g = f := by
      funext b
      exact (mem_filter.mp ((Fintype.mem_piFinset.mp hg) b)).2
    rw [this]
  rw [sum_congr rfl hc, ← mul_sum]
  congr 1
  rw [← Finset.prod_univ_sum (fun b => univ.filter (fun z : Option Bool => z.isSome = f b))
    (fun b z => mass (fineLaw D L isG b (ω b) z))]
  exact prod_congr rfl fun b _ => fiber_mass D L isG b (ω b) (f b)

/-! ## The finer expansion -/

omit [DecidableEq P] in
/-- **The finer expansion of the envelope energy against `Ñ₀`.** -/
theorem envN0_eq_sum_fine (A : Finset ℤ) (ω : Choice (D.CL.T L)) :
    diagonalIntegral (envelopeLaw (D.GB.N₀ L) (D.CL.D L) ω) (blockLift m₀ blk paperTail L A) =
      ∑ g : (BlockAtom Bk PaperJt L → Option Bool), fineInt D L isG A ω g := by
  unfold fineInt envelopeLaw
  have hsplit : (fun b => entryFactor (D.GB.N₀ L b) (D.CL.D L b) (ω b)) =
      fun b => ∑ z : Option Bool, fineLaw D L isG b (ω b) z := by
    funext b
    rw [Fintype.sum_option, Fintype.sum_bool]
    rcases hω : ω b with _ | ⟨t, e⟩
    · simp only [fineLaw, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      change D.GB.N₀ L b = _
      have e1 := sum_filter_add_sum_filter_not univ (fun i => isG b i = true)
        (fun i => D.GB.κu L b i)
      simp only [Bool.not_eq_true] at e1
      rw [e1]
      change D.GB.N₀ L b = D.R.law paperTail L b + ∑ i, D.GB.κu L b i
      rw [← D.GB.N₀_sub L b]
      abel
    · simp only [fineLaw, Option.isSome_some, ↓reduceIte, add_zero]
      rfl
  rw [hsplit, tensorLaw_sum, diagonalIntegral_sum]

/-! ## Per term: the small unions -/

omit [DecidableEq P] in
theorem fineLaw_of_not_mem (ω : Choice (D.CL.T L)) (g : BlockAtom Bk PaperJt L → Option Bool)
    (b : BlockAtom Bk PaperJt L) (hb : b ∉ subAtoms D L ω (collapse L g)) :
    fineLaw D L isG b (ω b) (g b) = D.R.law paperTail L b := by
  rcases hg : g b with _ | gg
  · rcases hω : ω b with _ | te
    · rfl
    · exfalso
      apply hb
      unfold subAtoms
      exact mem_filter.mpr ⟨mem_univ _, Or.inr (by simp [hω])⟩
  · exfalso
    apply hb
    unfold subAtoms collapse
    exact mem_filter.mpr ⟨mem_univ _, Or.inl (by simp [hg])⟩

omit [DecidableEq P] in
theorem prod_mass_fine (ω : Choice (D.CL.T L)) (g : BlockAtom Bk PaperJt L → Option Bool) :
    ∏ b ∈ subAtoms D L ω (collapse L g), mass (fineLaw D L isG b (ω b) (g b)) =
      ∏ b, mass (fineLaw D L isG b (ω b) (g b)) := by
  refine prod_subset (subset_univ _) fun b _ hb => ?_
  rw [fineLaw_of_not_mem D L isG ω g b hb]
  exact Sarkozy.LargeSums.mass_refLaw D L b

omit [DecidableEq P] in
/-- **The price bookkeeping of a finer term**: `(∏ masses) sq(D_E)^a ≤ C_X ∏ (tag prices)`. -/
theorem finePrice_le
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (ω : Choice (D.CL.T L)) (g : BlockAtom Bk PaperJt L → Option Bool) :
    (∏ b, mass (fineLaw D L isG b (ω b) (g b))) *
        ((leastSquare (∏ b ∈ subAtoms D L ω (collapse L g), crtModuli m₀ blk paperTail L b) :
          ℕ) : ℝ) ^ a ≤
      (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a paperTail D.S.selPre L b) *
        ∏ b, finePr D L isG b (ω b) (g b) := by
  have hsq : ((leastSquare (∏ b ∈ subAtoms D L ω (collapse L g), crtModuli m₀ blk paperTail L b) :
      ℕ) : ℝ) ^ a = ∏ b ∈ subAtoms D L ω (collapse L g),
        ((leastSquare (crtModuli m₀ blk paperTail L b) : ℕ) : ℝ) ^ a := by
    rw [leastSquare_prod_coprime (crtModuli m₀ blk paperTail L) (crtModuli_pairwise blk (hpair L)),
      Nat.cast_prod, ← Real.finsetProd_rpow _ _ (fun _ _ => Nat.cast_nonneg _)]
  rw [hsq]
  unfold subAtoms Choice.support
  rw [prod_filter, prod_filter, ← prod_mul_distrib, ← prod_mul_distrib]
  refine prod_le_prod₀ (fun b _ => mul_nonneg (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg
    (isPositiveRecord_fineLaw D L isG (D.S.p_prime L) b (ω b) (g b)).1) ?_) fun b _ => ?_
  · split_ifs
    · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · exact zero_le_one
  · have hs := hselF_of_parity D (prefix_pairwise (hpair L)) hpar hsel L b
    have hcol : collapse L g b = (g b).isSome := rfl
    rw [hcol]
    rcases hg : g b with _ | gg <;> rcases hω : ω b with _ | te
    · simp only [Option.isSome_none, Bool.false_eq_true, or_self, ↓reduceIte, mul_one, finePr]
      exact le_of_eq (Sarkozy.LargeSums.mass_refLaw D L b)
    · simp only [Option.isSome_none, Bool.false_eq_true, Option.isSome_some, or_true, ↓reduceIte,
        finePr, mul_one]
      change mass (D.CL.D L b te.1 te.2) * _ ≤ _
      rw [(D.CL.D_prob L b te.1 te.2).2, one_mul]
      exact hs
    · simp only [Option.isSome_some, Option.isSome_none, true_or, ↓reduceIte, Bool.false_eq_true,
        finePr, one_mul]
      have hm : 0 ≤ mass (∑ i ∈ univ.filter (fun i => isG b i = gg), D.GB.κu L b i) :=
        TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg
          (isPositiveRecord_sum _ _ fun i _ => D.GB.κu_pos L b i).1
      change mass (∑ i ∈ univ.filter (fun i => isG b i = gg), D.GB.κu L b i) * _ ≤ _
      exact mul_le_mul_of_nonneg_left hs hm
    · simp only [Option.isSome_some, true_or, ↓reduceIte, finePr, mul_zero]
      change mass (0 : TheoremCBlock.AtomMeasure m₀ blk paperTail L b) * _ ≤ 0
      rw [mass_zero_measure, zero_mul]

omit [DecidableEq P] in
/-- **The finer terms with a small union, per term** (`prop:record:density-structured`, as EC's
`e1SubSmallPT_proved`). -/
theorem fineSmallPT_proved
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (ha : 0 ≤ a) (hpar : ParityCondition D.S.ep)
    (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β) (hne : ∀ β, ∃ i, blk i = β) :
    ∃ c : ℝ, 0 ≤ c ∧ Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∀ (isG : ∀ b : BlockAtom Bk PaperJt L, D.GB.Iu L b → Bool) (ω : Choice (D.CL.T L)),
      IsSelection ω → ∀ g : (BlockAtom Bk PaperJt L → Option Bool),
      SubSmall D L ω (collapse L g) →
      |fineInt D L isG A ω g| ≤ fineMain D L isG (sfEps D) A ω g +
        (∏ b, mass (fineLaw D L isG b (ω b) (g b))) * remainder c L A) := by
  classical
  obtain ⟨C1, C71, hC1, hC71, hdcb⟩ := density_dc_block' (1 / 10 : ℝ) (by norm_num)
  have hM0 : 1 ≤ modulus pr h := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hQ1 : 1 ≤ cliqueConstant m₀ D.S.ep :=
    Nat.one_le_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun i _ => NeZero.ne _)
  set Cdc := dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ
    (modulus pr h) (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 with hCdc
  have hCdc0 : 0 ≤ Cdc := dcConstant_nonneg (by exact_mod_cast (prefixConductor_pos blk _).le)
    (Nat.cast_nonneg _) hC1.le hC71.le
  refine ⟨Cdc, hCdc0, ?_⟩
  filter_upwards [eventually_scaleConditions blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep)
    1 0 0 (by norm_num [blockScale]) hM0 hQ1, eventually_ge_atTop 2] with L hsc hL
  intro C hC hk A hA hY isG ω hω g hs
  have hcex : IsLeastCounterexample D.Y a densityExponent C L A :=
    ⟨hA, hY, fun ℓ h1 h2 => hk ℓ h1 h2⟩
  have hC0 : (0 : ℝ) ≤ C := zero_le_one.trans hC
  have hcd : (0 : ℝ) ≤ Sarkozy.cancellationDecay := by
    unfold Sarkozy.cancellationDecay; norm_num
  have hY0 : 0 ≤ D.Y L A := (Param.counterexample_pos (Params.ofDecay a) hC hY).le
  obtain ⟨qE, cE, hDE, hqE, hcE, hcE0, hcQ, hcopE, hqN⟩ : ∃ qE cE : ℕ,
      ∏ b ∈ subAtoms D L ω (collapse L g), crtModuli m₀ blk paperTail L b = qE * cE ∧
      Squarefree qE ∧ IsSquare cE ∧ cE ≠ 0 ∧ cE ≤ cliqueConstant m₀ D.S.ep ∧ qE.Coprime cE ∧
      (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau := by
    rcases moduli_paper D hpair hpar le_rfl L (((blockScale * L : ℕ) : ℝ) ^ stageTau)
      (subAtoms D L ω (collapse L g)) with h1 | h1
    · exact h1
    · exfalso
      rw [← prod_subQ_eq] at h1
      exact absurd hs (not_le.mpr h1)
  have hch := whole_chain hdcb D hpair hcex ha hC0 hL hsc hM0
    (fun b => fineLaw D L isG b (ω b) (g b)) (subAtoms D L ω (collapse L g))
    (fun b hb => fineLaw_of_not_mem D L isG ω g b hb)
    (fun b _ => isPositiveRecord_fineLaw D L isG (D.S.p_prime L) b (ω b) (g b))
    (prod_crtModuli_ne_one D hne (subAtoms_nonempty D hω _)) hDE hqE hcE hcE0 hcQ hcopE hqN hcd
    S1_at_cancellationDecay
  rw [prod_mass_fine D L isG ω g] at hch
  have hpr := finePrice_le D L isG hpair hpar hsel ω g
  set m := ∏ b, mass (fineLaw D L isG b (ω b) (g b)) with hm
  set G := (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a paperTail D.S.selPre L b) *
    ∏ b, finePr D L isG b (ω b) (g b) with hG
  set s := ((leastSquare (∏ b ∈ subAtoms D L ω (collapse L g), crtModuli m₀ blk paperTail L b) :
    ℕ) : ℝ) ^ a with hsdef
  have hu0 := sfEps_nonneg D L
  have hmain : fineMain D L isG (sfEps D) A ω g = G * ((1 + sfEps D L) * D.Y L A) := by
    unfold fineMain
    rw [hG]
    ring
  rw [hmain]
  have hcY : 0 ≤ (1 + sfEps D L) * D.Y L A := mul_nonneg (by linarith) hY0
  have h4 : m * ((1 + sfEps D L) * s * D.Y L A) ≤ G * ((1 + sfEps D L) * D.Y L A) := by
    calc m * ((1 + sfEps D L) * s * D.Y L A) = (m * s) * ((1 + sfEps D L) * D.Y L A) := by ring
      _ ≤ G * ((1 + sfEps D L) * D.Y L A) := mul_le_mul_of_nonneg_right hpr hcY
  have hrem : m * (Cdc * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A) =
      m * remainder Cdc L A := by
    unfold remainder
    rfl
  have hsub : fineInt D L isG A ω g = multilinearIntegral
      (tensorLaw fun b => fineLaw D L isG b (ω b) (g b))
      (fun _ => blockLift m₀ blk paperTail L A) := rfl
  rw [hsub]
  change _ ≤ m * ((1 + sfEps D L) * s * D.Y L A + Cdc * (L : ℝ) ^ (-Sarkozy.cancellationDecay) *
    density (blockScale * L) A) at hch
  rw [mul_add, hrem] at hch
  linarith

end Sarkozy.OpsSteps
