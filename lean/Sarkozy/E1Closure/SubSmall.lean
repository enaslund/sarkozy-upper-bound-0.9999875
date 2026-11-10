module

public import Sarkozy.E1Closure.Paper
public import Sarkozy.SharpFirst.Rem

@[expose] public section

/-!
# The subset terms with a small union, proved (`prop:record:density-structured`) (EC)

EC, 8 November 2026. **`e1SubSmallPT_proved`**: on the paper's tails, with `a ≥ 0`, the parity
condition, `blockSel ≤ selPre` and nonempty blocks, there is `c ≥ 0` with
`E1SubSmallPT D u c`, where `u = sfEps D` is SR's `u_L` (the scale term of
`lem:scale-conditions`). That is, at every least counterexample, every subset term with a small
union satisfies

`|𝔈_{ω,f}| ≤ (1 + u_L)(∏_{supp ω} sel_𝔟) Y ∏_{f ∖ supp ω} u_𝔟 + (∏_𝔟 m_𝔟) C_dc L^{-σ} α`.

This is `prop:record:density-structured` (first display) for the subset term, "applied once
with the union `E` of the selected moduli", through SR's `whole_chain` (DC2's
`block_energy_le_structured_data` with DC1's `lem:record:density-dc` and DC3's restoration):

* the atoms not at `μ_𝔟` (`subAtoms`) are nonempty, since a selection is nonempty;
* `q_E ≤ N^τ` gives the modulus conditions of `def:record:structured-energy`(a) (DC3's
  `moduli_paper`, the large alternative being excluded by `SubSmall`);
* the price bookkeeping `m sq(D_E)^a ≤ (∏_{supp ω} sel) ∏_{f ∖ supp ω} u` (`subPrice_le`), from
  `sq(D_𝔟)^a ≤ sel_𝔟` (DC3's `hselF_of_parity`) and `‖∑_i κu_{𝔟,i}‖ sel_𝔟 = u_𝔟`.

With `e1SubSmall_of_perTerm` this gives **`e1SubSmall_proved`**, and with the monotonicity in
`ε_E` (`e1SubSmall_mono`), `E1SubSmall` at every `ε_E ≥ u_L`.
-/

namespace Sarkozy.E1Closure

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.CancellationSteps Sarkozy.BlockAnchor Sarkozy.DensityChain2
  Sarkozy.DensityFibre Sarkozy.ThetaOne Sarkozy.EnvelopeInputsBlock Sarkozy.RecordExpansion
  Sarkozy.RecordExpansion.Choice
open Sarkozy.Param (Params)
open Sarkozy.SharpFirst (sfEps sfEps_nonneg tendsto_sfEps whole_chain)

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

section Mono

variable {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)

omit [DecidableEq P] in
/-- A larger relative error gives a smaller excess (at `Y ≥ 0`). -/
theorem r0X_anti {εE εE' : ℕ → ℝ} (hle : ∀ L, εE L ≤ εE' L) {L : ℕ} {A : Finset ℤ}
    (hY : 0 ≤ D.Y L A) (ω : Choice (D.CL.T L)) (f : BlockAtom Bk J L → Bool) :
    r0X D εE' L A ω f ≤ r0X D εE L A ω f := by
  unfold r0X subMain
  have h2 : 0 ≤ ∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b :=
    prod_nonneg fun b _ => D.selectionFactor_nonneg L b
  have h3 : 0 ≤ ∏ b, (if f b then (if (ω b).isSome then 0 else D.GB.uprice L b) else 1) :=
    prod_nonneg fun b _ => by
      split_ifs
      · exact le_rfl
      · exact TheoremCBlock.Structured.uprice_nonneg D L b
      · exact zero_le_one
  have : (1 + εE L) * (∏ b ∈ Choice.support ω,
      TheoremCBlock.selectionFactor a p D.S.selPre L b) * D.Y L A *
        ∏ b, (if f b then (if (ω b).isSome then 0 else D.GB.uprice L b) else 1) ≤
      (1 + εE' L) * (∏ b ∈ Choice.support ω,
        TheoremCBlock.selectionFactor a p D.S.selPre L b) * D.Y L A *
        ∏ b, (if f b then (if (ω b).isSome then 0 else D.GB.uprice L b) else 1) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (by linarith [hle L]) h2) hY) h3
  exact max_le_max le_rfl (by linarith)

omit [DecidableEq P] in
theorem rX_anti {εE εE' : ℕ → ℝ} (hle : ∀ L, εE L ≤ εE' L) {L : ℕ} {A : Finset ℤ}
    (hY : 0 ≤ D.Y L A) (ω : Choice (D.CL.T L)) (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag)
    (f : ∀ b, CEPiece D L b) : rX D εE' L A ω σ j f ≤ rX D εE L A ω σ j f := by
  unfold rX coupMain
  have hG : 0 ≤ ∏ b, ecpieceG D L ω b (f b) := prod_nonneg fun b _ => ecpieceG_nonneg D L ω b (f b)
  have : (∏ b, ecpieceG D L ω b (f b)) * ((1 + εE L) * D.Y L A) ≤
      (∏ b, ecpieceG D L ω b (f b)) * ((1 + εE' L) * D.Y L A) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith [hle L]) hY) hG
  split_ifs
  · exact max_le_max le_rfl (by linarith)
  · exact le_rfl

omit [DecidableEq P] in
/-- **`E1SubSmall` is monotone in `ε_E`.** -/
theorem e1SubSmall_mono {εE εE' : ℕ → ℝ} (hle : ∀ L, εE L ≤ εE' L) {c : ℝ}
    (h : E1SubSmall D εE c) : E1SubSmall D εE' c := by
  unfold E1SubSmall at h ⊢
  filter_upwards [h] with L hL
  intro C hC hk A hA hY
  have hY0 : 0 ≤ D.Y L A := (Param.counterexample_pos (Params.ofDecay a) hC hY).le
  refine le_trans (sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (sum_le_sum fun f _ => ?_)
    (monomial_nonneg (D.CL.πt_nonneg L) ω)) (hL C hC hk A hA hY)
  split_ifs
  · exact r0X_anti D hle hY0 ω f
  · exact le_rfl

omit [DecidableEq P] in
/-- **`E1CoupSmall` is monotone in `ε_E`.** -/
theorem e1CoupSmall_mono {εE εE' : ℕ → ℝ} (hle : ∀ L, εE L ≤ εE' L) {c : ℝ}
    (h : E1CoupSmall D εE c) : E1CoupSmall D εE' c := by
  unfold E1CoupSmall at h ⊢
  filter_upwards [h] with L hL
  intro C hC hk A hA hY
  have hY0 : 0 ≤ D.Y L A := (Param.counterexample_pos (Params.ofDecay a) hC hY).le
  refine le_trans (sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (sum_le_sum fun σ _ =>
    sum_le_sum fun j _ => sum_le_sum fun f _ => mul_le_mul_of_nonneg_left ?_
      (prod_nonneg fun b _ => abs_nonneg _)) (monomial_nonneg (D.CL.πt_nonneg L) ω))
    (hL C hC hk A hA hY)
  split_ifs
  · exact rX_anti D hle hY0 ω σ j f
  · exact le_rfl

end Mono

section Paper

variable (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)

/-- The atoms of a subset term that do not carry `μ_𝔟`: the selected atoms and the atoms where
`f` chooses the bracket records. -/
noncomputable def subAtoms (L : ℕ) (ω : Choice (D.CL.T L)) (f : BlockAtom Bk PaperJt L → Bool) :
    Finset (BlockAtom Bk PaperJt L) :=
  univ.filter fun b => f b = true ∨ (ω b).isSome = true

omit [DecidableEq P] in
theorem subAtoms_nonempty {L : ℕ} {ω : Choice (D.CL.T L)} (hω : IsSelection ω)
    (f : BlockAtom Bk PaperJt L → Bool) : (subAtoms D L ω f).Nonempty := by
  obtain ⟨b, hb⟩ := (Choice.support_nonempty_iff ω).mpr hω.1
  refine ⟨b, ?_⟩
  simp only [Choice.support, mem_filter, mem_univ, true_and] at hb
  simp [subAtoms, hb]

omit [DecidableEq P] in
theorem subLaw_of_not_mem {L : ℕ} (ω : Choice (D.CL.T L)) (f : BlockAtom Bk PaperJt L → Bool)
    (b : BlockAtom Bk PaperJt L) (hb : b ∉ subAtoms D L ω f) :
    subLaw D L b (ω b) (f b) = D.R.law paperTail L b := by
  simp only [subAtoms, mem_filter, mem_univ, true_and, not_or, Bool.not_eq_true,
    Option.isSome_eq_false_iff] at hb
  obtain ⟨hf, hω⟩ := hb
  simp [subLaw, hf, Option.isNone_iff_eq_none.mp hω, entryFactor]

omit [DecidableEq P] in
theorem prod_subQ_eq (L : ℕ) (ω : Choice (D.CL.T L)) (f : BlockAtom Bk PaperJt L → Bool) :
    ∏ b, subQ D L b (ω b) (f b) =
      ∏ b, ((if b ∈ subAtoms D L ω f then atomQ blk paperTail D.S.pp D.S.ep L b else 1 : ℕ) :
        ℝ) := by
  refine prod_congr rfl fun b _ => ?_
  unfold subQ subAtoms Sarkozy.LargeSums.atomQR
  by_cases hb : f b = true ∨ (ω b).isSome = true
  · simp [hb]
  · simp only [hb, ↓reduceIte, mem_filter, mem_univ, true_and, Nat.cast_one]

omit [DecidableEq P] in
/-- The masses of the selected atom laws of a subset term are its subset masses. -/
theorem prod_mass_subAtoms (L : ℕ) (ω : Choice (D.CL.T L)) (f : BlockAtom Bk PaperJt L → Bool) :
    ∏ b ∈ subAtoms D L ω f, mass (subLaw D L b (ω b) (f b)) =
      ∏ b, (if f b then (if (ω b).isSome then 0 else mass (∑ i, D.GB.κu L b i)) else 1) := by
  unfold subAtoms
  rw [prod_filter]
  refine prod_congr rfl fun b _ => ?_
  rcases hf : f b <;> rcases hω : ω b with _ | te
  · simp
  · simp only [Bool.false_eq_true, Option.isSome_some, or_true, ↓reduceIte, subLaw]
    exact mass_entryFactor D L b _
  · simp [subLaw]
  · simp [subLaw, mass_zero_measure]

omit [DecidableEq P] in
/-- **The price bookkeeping of a subset term**:
`m sq(D_E)^a ≤ (∏_{supp ω} sel_𝔟) ∏_𝔟 (u_𝔟 on f ∖ supp ω, 0 on f ∩ supp ω, 1 off f)`. -/
theorem subPrice_le
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (L : ℕ) (ω : Choice (D.CL.T L)) (f : BlockAtom Bk PaperJt L → Bool) :
    (∏ b, (if f b then (if (ω b).isSome then 0 else mass (∑ i, D.GB.κu L b i)) else 1)) *
        ((leastSquare (∏ b ∈ subAtoms D L ω f, crtModuli m₀ blk paperTail L b) : ℕ) : ℝ) ^ a ≤
      (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a paperTail D.S.selPre L b) *
        ∏ b, (if f b then (if (ω b).isSome then 0 else D.GB.uprice L b) else 1) := by
  have hsq : ((leastSquare (∏ b ∈ subAtoms D L ω f, crtModuli m₀ blk paperTail L b) : ℕ) : ℝ) ^ a =
      ∏ b ∈ subAtoms D L ω f, ((leastSquare (crtModuli m₀ blk paperTail L b) : ℕ) : ℝ) ^ a := by
    rw [leastSquare_prod_coprime (crtModuli m₀ blk paperTail L) (crtModuli_pairwise blk (hpair L)),
      Nat.cast_prod, ← Real.finsetProd_rpow _ _ (fun _ _ => Nat.cast_nonneg _)]
  rw [hsq]
  unfold subAtoms Choice.support
  rw [prod_filter, prod_filter, ← prod_mul_distrib, ← prod_mul_distrib]
  refine prod_le_prod₀ (fun b _ => mul_nonneg (subsetMass_nonneg D L ω f b) ?_) fun b _ => ?_
  · split_ifs
    · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · exact zero_le_one
  · have hs := hselF_of_parity D (prefix_pairwise (hpair L)) hpar hsel L b
    have hsq0 : 0 ≤ ((leastSquare (crtModuli m₀ blk paperTail L b) : ℕ) : ℝ) ^ a :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hm : 0 ≤ mass (∑ i, D.GB.κu L b i) := by
      rw [mass_sum_measure]
      exact sum_nonneg fun i _ =>
        TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.GB.κu_pos L b i).1
    have hu : mass (∑ i, D.GB.κu L b i) * TheoremCBlock.selectionFactor a paperTail D.S.selPre L b =
        D.GB.uprice L b := by
      rw [mass_sum_measure, sum_mul]
      rfl
    rcases hf : f b <;> rcases hω : ω b with _ | te
    · simp
    · simp only [Bool.false_eq_true, Option.isSome_some, or_true, ↓reduceIte, one_mul, mul_one]
      exact hs
    · simp only [↓reduceIte, Option.isSome_none, Bool.false_eq_true, true_or, one_mul]
      rw [← hu]
      exact mul_le_mul_of_nonneg_left hs hm
    · simp

omit [DecidableEq P] in
/-- **`E1SubSmallPT`, proved** (`prop:record:density-structured` at the subset terms with a
small union; see the module docstring). -/
theorem e1SubSmallPT_proved
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (ha : 0 ≤ a) (hpar : ParityCondition D.S.ep)
    (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β) (hne : ∀ β, ∃ i, blk i = β) :
    ∃ c : ℝ, 0 ≤ c ∧ E1SubSmallPT D (sfEps D) c := by
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
  unfold E1SubSmallPT
  filter_upwards [eventually_scaleConditions blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep)
    1 0 0 (by norm_num [blockScale]) hM0 hQ1, eventually_ge_atTop 2] with L hsc hL
  intro C hC hk A hA hY ω hω f hs
  have hcex : IsLeastCounterexample D.Y a densityExponent C L A :=
    ⟨hA, hY, fun ℓ h1 h2 => hk ℓ h1 h2⟩
  have hC0 : (0 : ℝ) ≤ C := zero_le_one.trans hC
  have hcd : (0 : ℝ) ≤ Sarkozy.cancellationDecay := by
    unfold Sarkozy.cancellationDecay; norm_num
  have hY0 : 0 ≤ D.Y L A := (Param.counterexample_pos (Params.ofDecay a) hC hY).le
  obtain ⟨qE, cE, hDE, hqE, hcE, hcE0, hcQ, hcopE, hqN⟩ : ∃ qE cE : ℕ,
      ∏ b ∈ subAtoms D L ω f, crtModuli m₀ blk paperTail L b = qE * cE ∧ Squarefree qE ∧
      IsSquare cE ∧ cE ≠ 0 ∧ cE ≤ cliqueConstant m₀ D.S.ep ∧ qE.Coprime cE ∧
      (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau := by
    rcases moduli_paper D hpair hpar le_rfl L (((blockScale * L : ℕ) : ℝ) ^ stageTau)
      (subAtoms D L ω f) with h1 | h1
    · exact h1
    · exfalso
      rw [← prod_subQ_eq] at h1
      exact absurd hs (not_le.mpr h1)
  have hch := whole_chain hdcb D hpair hcex ha hC0 hL hsc hM0
    (fun b => subLaw D L b (ω b) (f b)) (subAtoms D L ω f)
    (fun b hb => subLaw_of_not_mem D ω f b hb)
    (fun b _ => isPositiveRecord_subLaw D L (D.S.p_prime L) b (ω b) (f b))
    (prod_crtModuli_ne_one D hne (subAtoms_nonempty D hω f)) hDE hqE hcE hcE0 hcQ hcopE hqN hcd
    S1_at_cancellationDecay
  rw [prod_mass_subAtoms D L ω f] at hch
  have hpr := subPrice_le D hpair hpar hsel L ω f
  set m := ∏ b, (if f b then (if (ω b).isSome then 0 else mass (∑ i, D.GB.κu L b i)) else 1)
    with hm
  set G := (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a paperTail D.S.selPre L b) *
    ∏ b, (if f b then (if (ω b).isSome then 0 else D.GB.uprice L b) else 1) with hG
  set s := ((leastSquare (∏ b ∈ subAtoms D L ω f, crtModuli m₀ blk paperTail L b) : ℕ) : ℝ) ^ a
    with hsdef
  have hu0 := sfEps_nonneg D L
  have hmain : subMain D (sfEps D) L A ω f = G * ((1 + sfEps D L) * D.Y L A) := by
    unfold subMain
    rw [hG]
    ring
  change |subInt D L A ω f| ≤ subMain D (sfEps D) L A ω f + m * remainder Cdc L A
  rw [hmain]
  have hcY : 0 ≤ (1 + sfEps D L) * D.Y L A := mul_nonneg (by linarith) hY0
  have h4 : m * ((1 + sfEps D L) * s * D.Y L A) ≤ G * ((1 + sfEps D L) * D.Y L A) := by
    calc m * ((1 + sfEps D L) * s * D.Y L A) = (m * s) * ((1 + sfEps D L) * D.Y L A) := by ring
      _ ≤ G * ((1 + sfEps D L) * D.Y L A) := mul_le_mul_of_nonneg_right hpr hcY
  have hrem : m * (Cdc * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A) =
      m * remainder Cdc L A := by
    unfold remainder
    rfl
  have hsub : subInt D L A ω f = multilinearIntegral (tensorLaw fun b => subLaw D L b (ω b) (f b))
      (fun _ => blockLift m₀ blk paperTail L A) := rfl
  rw [hsub]
  change _ ≤ m * ((1 + sfEps D L) * s * D.Y L A + Cdc * (L : ℝ) ^ (-Sarkozy.cancellationDecay) *
    density (blockScale * L) A) at hch
  rw [mul_add, hrem] at hch
  linarith

omit [DecidableEq P] in
/-- **`E1SubSmall`, proved** at `ε_E = u_L` (`e1SubSmallPT_proved`, `e1SubSmall_of_perTerm`). -/
theorem e1SubSmall_proved
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (ha : 0 ≤ a) (hpar : ParityCondition D.S.ep)
    (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β) (hne : ∀ β, ∃ i, blk i = β) :
    ∃ c : ℝ, 0 ≤ c ∧ E1SubSmall D (sfEps D) c := by
  obtain ⟨c₁, hc₁, h⟩ := e1SubSmallPT_proved D hpair ha hpar hsel hne
  exact ⟨_, mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le)
    (mul_nonneg (Real.exp_pos _).le hc₁), e1SubSmall_of_perTerm D ha hc₁ h⟩

end Paper

end Sarkozy.E1Closure
