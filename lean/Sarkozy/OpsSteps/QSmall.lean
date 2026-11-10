module

public import Sarkozy.OpsSteps.QPieces
public import Sarkozy.E1Closure.CoupSmall

@[expose] public section

/-!
# The coupled pieces with a small union, with an arbitrary law on the support (OPS-S)

`paper/sections/10_comparison_lemmas.tex`, `lem:sharp-first` (term `T′`), `lem:density:coupled`,
`lem:record:folded-energy`(a), `prop:record:density-structured`.

EC's `e1CoupSmallPT_proved` bounds a coupled piece with a small union by folding it at the cut
`c_j` of its tag (`lem:record:folded-energy`(a)): `|T′| ≤ (∏ d) √(𝔈₊ 𝔈₋)`, where the folded laws are
`Diag_{c_j}` of the half marginals of each factor; then `whole_chain`
(`prop:record:density-structured`) bounds each folded energy. At the selected atoms only three
facts about the law are used: it is nonnegative (the bracket of `lem:record:folded-energy`(a)), it
has uniform one-slot marginals (its folded laws are positive records), and its mass is `1`. So the
proof goes through for any probability law `Q` with uniform one-slot marginals on the support:

* `qeK`, `qeLp`, `qeLm`: EC's local laws `eK`, `eLp`, `eLm` with `Q`; `qe_bracket`,
  `isPositiveRecord_qeLp/m`, `mass_qeLp/m`, `qeLp_of_mu`, `qeLm_of_mu`, `qK_eq_qeK`,
  `prod_mass_coupAtomsQ`;
* **`qCoupSmallPT_proved`**: on the paper's tails, there is `c ≥ 0` (independent of `Q`) such
  that at every least counterexample every coupled piece with `Q` on the support and a small
  union has `|qInt| ≤ coupMain + (∏ cM) c L^{-σ} α`;
* **`qX_le_pieceBnd_small`**: hence its canonical remainder is at most `pieceBnd`.
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

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

section Local

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
  (Qf : ∀ b : BlockAtom Bk J L, D.CL.T L b → ChangeType → TheoremCBlock.AtomMeasure m₀ blk p L b)
  (dec : DecFamily D L) (j : D.FS.Tag)

/-- EC's local coupled law `eK` with `Q` on the support. -/
noncomputable def qeK (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType)) :
    CEPiece D L b → TheoremCBlock.AtomMeasure m₀ blk p L b
  | Sum.inl none => entryFactor (D.R.law p L b) (Qf b) o
  | Sum.inl (some i) => D.GB.κu L b i
  | Sum.inr (i, y) => ThetaOne.wpieceK (D := D) (L := L) j b (Sum.inr ⟨i, y⟩)

/-- EC's plus folded law `eLp` with `Q` on the support. -/
noncomputable def qeLp (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType)) :
    CEPiece D L b → TheoremCBlock.AtomMeasure m₀ blk p L b
  | Sum.inl none => o.elim (D.R.law p L b) fun te =>
      (D.FS.cut j).diagonalLaw (halfMarginalPlus (D.FS.cut j) (Qf b te.1 te.2))
  | Sum.inl (some i) => (D.FS.cut j).diagonalLaw (halfMarginalPlus (D.FS.cut j) (D.GB.κu L b i))
  | Sum.inr (i, y) => ThetaOne.wpieceLp dec j b (Sum.inr ⟨i, y⟩)

/-- EC's minus folded law `eLm` with `Q` on the support. -/
noncomputable def qeLm (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType)) :
    CEPiece D L b → TheoremCBlock.AtomMeasure m₀ blk p L b
  | Sum.inl none => o.elim (D.R.law p L b) fun te =>
      (D.FS.cut j).diagonalLaw (halfMarginalMinus (D.FS.cut j) (Qf b te.1 te.2))
  | Sum.inl (some i) => (D.FS.cut j).diagonalLaw (halfMarginalMinus (D.FS.cut j) (D.GB.κu L b i))
  | Sum.inr (i, y) => ThetaOne.wpieceLm dec j b (Sum.inr ⟨i, y⟩)

variable {D L Qf}

omit [DecidableEq P] in
theorem qeLp_positive (hQp : ∀ b t e, IsProbability (Qf b t e)) (b : BlockAtom Bk J L)
    (o : Option (D.CL.T L b × ChangeType)) (x : CEPiece D L b) :
    (D.FS.cut j).Positive (qeLp D L Qf dec j b o x) := by
  rcases x with (_ | i) | ⟨i, y⟩
  · rcases o with _ | ⟨t, e⟩
    · exact eLp_positive D L dec j b none (Sum.inl none)
    · exact (D.FS.cut j).diagonalLaw_positive (halfMarginalPlus_nonneg _ (hQp b t e).1)
  · exact eLp_positive D L dec j b o (Sum.inl (some i))
  · exact eLp_positive D L dec j b o (Sum.inr (i, y))

omit [DecidableEq P] in
theorem qeLm_positive (hQp : ∀ b t e, IsProbability (Qf b t e)) (b : BlockAtom Bk J L)
    (o : Option (D.CL.T L b × ChangeType)) (x : CEPiece D L b) :
    (D.FS.cut j).Positive (qeLm D L Qf dec j b o x) := by
  rcases x with (_ | i) | ⟨i, y⟩
  · rcases o with _ | ⟨t, e⟩
    · exact eLm_positive D L dec j b none (Sum.inl none)
    · exact (D.FS.cut j).diagonalLaw_positive (halfMarginalMinus_nonneg _ (hQp b t e).1)
  · exact eLm_positive D L dec j b o (Sum.inl (some i))
  · exact eLm_positive D L dec j b o (Sum.inr (i, y))

omit [DecidableEq P] in
/-- **Every piece is bracketed at `c_j` by its folded laws** (`lem:record:folded-energy`(a)). -/
theorem qe_bracket (hQp : ∀ b t e, IsProbability (Qf b t e)) (b : BlockAtom Bk J L)
    (o : Option (D.CL.T L b × ChangeType)) (x : CEPiece D L b) :
    (D.FS.cut j).Bracket (eD D L b x • qeLp D L Qf dec j b o x) (qeK D L Qf j b o x)
      (eD D L b x • qeLm D L Qf dec j b o x) := by
  rcases x with (_ | i) | ⟨i, y⟩
  · rcases o with _ | ⟨t, e⟩
    · exact e_bracket D L dec j b none (Sum.inl none)
    · exact bracket_of_nonneg _ _ (hQp b t e).1
  · exact e_bracket D L dec j b o (Sum.inl (some i))
  · exact e_bracket D L dec j b o (Sum.inr (i, y))

omit [DecidableEq P] in
theorem isPositiveRecord_qeLp (hQp : ∀ b t e, IsProbability (Qf b t e))
    (hQu : ∀ b t e, HasUniformSlotMarginals (Qf b t e)) (hp : ∀ j, (p L j).Prime)
    (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType)) (x : CEPiece D L b) :
    IsPositiveRecord (qeLp D L Qf dec j b o x) := by
  rcases x with (_ | i) | ⟨i, y⟩
  · rcases o with _ | ⟨t, e⟩
    · exact isPositiveRecord_eLp D L dec j hp b none (Sum.inl none)
    · exact isPositiveRecord_diag_plus _ ⟨(hQp b t e).1, hQu b t e⟩
  · exact isPositiveRecord_eLp D L dec j hp b o (Sum.inl (some i))
  · exact isPositiveRecord_eLp D L dec j hp b o (Sum.inr (i, y))

omit [DecidableEq P] in
theorem isPositiveRecord_qeLm (hQp : ∀ b t e, IsProbability (Qf b t e))
    (hQu : ∀ b t e, HasUniformSlotMarginals (Qf b t e)) (hp : ∀ j, (p L j).Prime)
    (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType)) (x : CEPiece D L b) :
    IsPositiveRecord (qeLm D L Qf dec j b o x) := by
  rcases x with (_ | i) | ⟨i, y⟩
  · rcases o with _ | ⟨t, e⟩
    · exact isPositiveRecord_eLm D L dec j hp b none (Sum.inl none)
    · exact isPositiveRecord_diag_minus _ ⟨(hQp b t e).1, hQu b t e⟩
  · exact isPositiveRecord_eLm D L dec j hp b o (Sum.inl (some i))
  · exact isPositiveRecord_eLm D L dec j hp b o (Sum.inr (i, y))

omit [DecidableEq P] in
theorem mass_qeLp (hQp : ∀ b t e, IsProbability (Qf b t e)) (b : BlockAtom Bk J L)
    (o : Option (D.CL.T L b × ChangeType)) (x : CEPiece D L b) :
    mass (qeLp D L Qf dec j b o x) = eMass D L b x := by
  rcases x with (_ | i) | ⟨i, y⟩
  · rcases o with _ | ⟨t, e⟩
    · exact mass_eLp D L dec j b none (Sum.inl none)
    · exact (Sarkozy.LargeSums.mass_diag_plus _ _).trans (hQp b t e).2
  · exact mass_eLp D L dec j b o (Sum.inl (some i))
  · exact mass_eLp D L dec j b o (Sum.inr (i, y))

omit [DecidableEq P] in
theorem mass_qeLm (hQp : ∀ b t e, IsProbability (Qf b t e)) (b : BlockAtom Bk J L)
    (o : Option (D.CL.T L b × ChangeType)) (x : CEPiece D L b) :
    mass (qeLm D L Qf dec j b o x) = eMass D L b x := by
  rcases x with (_ | i) | ⟨i, y⟩
  · rcases o with _ | ⟨t, e⟩
    · exact mass_eLm D L dec j b none (Sum.inl none)
    · exact (Sarkozy.LargeSums.mass_diag_minus _ _).trans (hQp b t e).2
  · exact mass_eLm D L dec j b o (Sum.inl (some i))
  · exact mass_eLm D L dec j b o (Sum.inr (i, y))

omit [DecidableEq P] in
theorem qeLp_of_mu (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType))
    (x : CEPiece D L b) (hx : eIsMu D L b o x = true) :
    qeLp D L Qf dec j b o x = D.R.law p L b := by
  rcases x with (_ | i) | ⟨i, y⟩
  · rcases o with _ | te
    · rfl
    · simp [eIsMu] at hx
  · simp [eIsMu] at hx
  · simp [eIsMu] at hx

omit [DecidableEq P] in
theorem qeLm_of_mu (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType))
    (x : CEPiece D L b) (hx : eIsMu D L b o x = true) :
    qeLm D L Qf dec j b o x = D.R.law p L b := by
  rcases x with (_ | i) | ⟨i, y⟩
  · rcases o with _ | te
    · rfl
    · simp [eIsMu] at hx
  · simp [eIsMu] at hx
  · simp [eIsMu] at hx

omit [DecidableEq P] in
/-- **At a piece with nonzero coefficient, the piece is the local law `qeK`.** -/
theorem qK_eq_qeK (ω : Choice (D.CL.T L)) (σ : ∀ b, Option (D.FS.Ib L b))
    (b : BlockAtom Bk J L) (x : CEPiece D L b)
    (hc : EnvelopeInputsBlock.ecpieceCoef D L ω σ j b x ≠ 0) :
    qK D L Qf ω b x = qeK D L Qf j b (ω b) x := by
  rcases x with (_ | i) | ⟨i, _ | t⟩
  · rfl
  · rfl
  · have ht : D.FS.tag L b i = j := by
      by_contra hne
      exact hc (by simp [EnvelopeInputsBlock.ecpieceCoef, hne])
    simp [qK, qeK, ThetaOne.wpieceK, ht]
  · cases t <;> simp [qK, qeK, ThetaOne.wpieceK]

end Local

section Paper

variable (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)

omit [DecidableEq P] in
theorem prod_mass_coupAtomsQ (L : ℕ)
    {Qf : ∀ b : BlockAtom Bk PaperJt L, D.CL.T L b → ChangeType →
      TheoremCBlock.AtomMeasure m₀ blk paperTail L b}
    (hQp : ∀ b t e, IsProbability (Qf b t e)) (dec : DecFamily D L) (j : D.FS.Tag)
    (ω : Choice (D.CL.T L)) (f : ∀ b, CEPiece D L b) :
    (∏ b ∈ coupAtoms D L ω f, mass (qeLp D L Qf dec j b (ω b) (f b)) = ∏ b, eMass D L b (f b)) ∧
    (∏ b ∈ coupAtoms D L ω f, mass (qeLm D L Qf dec j b (ω b) (f b)) = ∏ b, eMass D L b (f b)) := by
  unfold coupAtoms
  rw [prod_filter, prod_filter]
  refine ⟨prod_congr rfl fun b _ => ?_, prod_congr rfl fun b _ => ?_⟩
  · cases hm : eIsMu D L b (ω b) (f b)
    · simp only [↓reduceIte]
      exact mass_qeLp dec j hQp b (ω b) (f b)
    · simp only [Bool.true_eq_false, ↓reduceIte]
      exact (eMass_of_mu D L b (ω b) (f b) hm).symm
  · cases hm : eIsMu D L b (ω b) (f b)
    · simp only [↓reduceIte]
      exact mass_qeLm dec j hQp b (ω b) (f b)
    · simp only [Bool.true_eq_false, ↓reduceIte]
      exact (eMass_of_mu D L b (ω b) (f b) hm).symm

omit [DecidableEq P] in
/-- **The coupled pieces with `Q` on the support and a small union, per term** (EC's
`e1CoupSmallPT_proved` with `Q`; `lem:sharp-first` term `T′`, `lem:density:coupled`): the constant
`c` does not depend on `Q`. -/
theorem qCoupSmallPT_proved
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (ha : 0 ≤ a) (hpar : ParityCondition D.S.ep)
    (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β) (hne : ∀ β, ∃ i, blk i = β) :
    ∃ c : ℝ, 0 ≤ c ∧ Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∀ (Qf : ∀ b : BlockAtom Bk PaperJt L, D.CL.T L b → ChangeType →
          TheoremCBlock.AtomMeasure m₀ blk paperTail L b),
      (∀ b t e, IsProbability (Qf b t e)) → (∀ b t e, HasUniformSlotMarginals (Qf b t e)) →
      ∀ ω : Choice (D.CL.T L), IsSelection ω →
      ∀ σ : (∀ b, Option (D.FS.Ib L b)), ∀ j, ∀ f : (∀ b, CEPiece D L b),
      (∀ b, EnvelopeInputsBlock.ecpieceCoef D L ω σ j b (f b) ≠ 0) → CoupSmall D L ω f →
      |qInt D L Qf A ω f| ≤ coupMain D (sfEps D) L A ω f +
        (∏ b, cM D L b (f b)) * remainder c L A) := by
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
  intro C hC hk A hA hY Qf hQp hQu ω hω σ j f hcf hs
  have hcex : IsLeastCounterexample D.Y a densityExponent C L A :=
    ⟨hA, hY, fun ℓ h1 h2 => hk ℓ h1 h2⟩
  have hC0 : (0 : ℝ) ≤ C := zero_le_one.trans hC
  have hcd : (0 : ℝ) ≤ Sarkozy.cancellationDecay := by
    unfold Sarkozy.cancellationDecay; norm_num
  have hY0 : 0 ≤ D.Y L A := (Param.counterexample_pos (Params.ofDecay a) hC hY).le
  set dec : DecFamily D L := Classical.choice (nonempty_decFamily D L) with hdec
  set g := blockLift m₀ blk paperTail L A with hgdef
  have hfe := folded_energy_tensor (D.FS.cut j) (fun b => qeK D L Qf j b (ω b) (f b))
    (fun b => qeLp D L Qf dec j b (ω b) (f b)) (fun b => qeLm D L Qf dec j b (ω b) (f b))
    (fun b => eD D L b (f b)) (fun b => eD_nonneg D L b (f b))
    (fun b => qeLp_positive dec j hQp b (ω b) (f b))
    (fun b => qeLm_positive dec j hQp b (ω b) (f b))
    (fun b => qe_bracket dec j hQp b (ω b) (f b)) (fun _ => g)
  obtain ⟨hFp0, hFm0, hfold⟩ := hfe
  set Fp := multilinearIntegral (tensorLaw fun b => qeLp D L Qf dec j b (ω b) (f b))
    ((fun _ => g) ∘ (D.FS.cut j).foldPlus) with hFp
  set Fm := multilinearIntegral (tensorLaw fun b => qeLm D L Qf dec j b (ω b) (f b))
    ((fun _ => g) ∘ (D.FS.cut j).foldMinus) with hFm
  have hK : qInt D L Qf A ω f =
      multilinearIntegral (tensorLaw fun b => qeK D L Qf j b (ω b) (f b)) (fun _ => g) := by
    unfold qInt diagonalIntegral
    congr 2
    funext b
    exact qK_eq_qeK j ω σ b (f b) (hcf b)
  obtain ⟨qE, cE, hDE, hqE, hcE, hcE0, hcQ, hcopE, hqN⟩ : ∃ qE cE : ℕ,
      ∏ b ∈ coupAtoms D L ω f, crtModuli m₀ blk paperTail L b = qE * cE ∧ Squarefree qE ∧
      IsSquare cE ∧ cE ≠ 0 ∧ cE ≤ cliqueConstant m₀ D.S.ep ∧ qE.Coprime cE ∧
      (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau := by
    rcases moduli_paper D hpair hpar le_rfl L (((blockScale * L : ℕ) : ℝ) ^ stageTau)
      (coupAtoms D L ω f) with h1 | h1
    · exact h1
    · exfalso
      rw [← prod_coupQ_eq] at h1
      exact absurd hs (not_le.mpr h1)
  have hEne := prod_crtModuli_ne_one D hne (coupAtoms_nonempty D hω f)
  have hEp : ∀ b ∉ coupAtoms D L ω f, qeLp D L Qf dec j b (ω b) (f b) = D.R.law paperTail L b :=
    fun b hb => qeLp_of_mu dec j b (ω b) (f b) (by
      simpa [coupAtoms] using hb)
  have hEm : ∀ b ∉ coupAtoms D L ω f, qeLm D L Qf dec j b (ω b) (f b) = D.R.law paperTail L b :=
    fun b hb => qeLm_of_mu dec j b (ω b) (f b) (by
      simpa [coupAtoms] using hb)
  have hchp := whole_chain hdcb D hpair hcex ha hC0 hL hsc hM0
    (fun b => qeLp D L Qf dec j b (ω b) (f b)) (coupAtoms D L ω f) hEp
    (fun b _ => isPositiveRecord_qeLp dec j hQp hQu (D.S.p_prime L) b (ω b) (f b)) hEne hDE hqE
    hcE hcE0 hcQ hcopE hqN hcd S1_at_cancellationDecay
  have hchm := whole_chain hdcb D hpair hcex ha hC0 hL hsc hM0
    (fun b => qeLm D L Qf dec j b (ω b) (f b)) (coupAtoms D L ω f) hEm
    (fun b _ => isPositiveRecord_qeLm dec j hQp hQu (D.S.p_prime L) b (ω b) (f b)) hEne hDE hqE
    hcE hcE0 hcQ hcopE hqN hcd S1_at_cancellationDecay
  obtain ⟨hmp, hmm⟩ := prod_mass_coupAtomsQ D L hQp dec j ω f
  rw [hmp] at hchp
  rw [hmm] at hchm
  set m := ∏ b, eMass D L b (f b) with hmdef
  set dd := ∏ b, eD D L b (f b) with hdd
  set s := ((leastSquare (∏ b ∈ coupAtoms D L ω f, crtModuli m₀ blk paperTail L b) : ℕ) : ℝ) ^ a
    with hsdef
  set u := sfEps D L with hudef
  set K := Cdc * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A with hKdef
  set M := m * ((1 + u) * s * D.Y L A + K) with hMdef
  have hFpM : Fp ≤ M := (le_abs_self _).trans hchp
  have hFmM : Fm ≤ M := (le_abs_self _).trans hchm
  have hdd0 : 0 ≤ dd := prod_nonneg fun b _ => eD_nonneg D L b (f b)
  have hgeo : Real.sqrt Fp * Real.sqrt Fm ≤ M := by
    refine (Sarkozy.LargeSums.sqrt_mul_sqrt_le_abs Fp Fm).trans ?_
    rw [abs_of_nonneg hFp0, abs_of_nonneg hFm0]
    linarith
  have h1 : |qInt D L Qf A ω f| ≤ dd * M := by
    rw [hK]
    refine hfold.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hgeo hdd0
  have hpr := coupPrice_le D hpair hpar hsel L ω f
  have hrm := coupRem_le D L f
  have hu0 := sfEps_nonneg D L
  have hK0 : 0 ≤ K := mul_nonneg (mul_nonneg hCdc0 (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (density_nonneg _ _)
  have hcY : 0 ≤ (1 + u) * D.Y L A := mul_nonneg (by linarith) hY0
  have h2 : dd * M ≤ (∏ b, ecpieceG D L ω b (f b)) * ((1 + u) * D.Y L A) +
      (∏ b, cM D L b (f b)) * K := by
    have e : dd * M = (dd * m * s) * ((1 + u) * D.Y L A) + (dd * m) * K := by
      rw [hMdef]
      ring
    rw [e]
    exact add_le_add (mul_le_mul_of_nonneg_right hpr hcY) (mul_le_mul_of_nonneg_right hrm hK0)
  have hrem : remainder Cdc L A = K := rfl
  change |qInt D L Qf A ω f| ≤ coupMain D (sfEps D) L A ω f + (∏ b, cM D L b (f b)) *
    remainder Cdc L A
  rw [hrem]
  exact h1.trans h2

omit [DecidableEq P] in
/-- **On a small union, the canonical remainder is at most the law-independent bound**, given the
per-term bound of `qCoupSmallPT_proved`. -/
theorem qX_le_pieceBnd_small {L : ℕ} {A : Finset ℤ}
    {Qf : ∀ b : BlockAtom Bk PaperJt L, D.CL.T L b → ChangeType →
      TheoremCBlock.AtomMeasure m₀ blk paperTail L b}
    {rem B : ℝ} (hrem : 0 ≤ rem) (ω : Choice (D.CL.T L)) (σ : ∀ b, Option (D.FS.Ib L b))
    (j : D.FS.Tag) (f : ∀ b, CEPiece D L b) (hs : CoupSmall D L ω f)
    (hpt : (∀ b, EnvelopeInputsBlock.ecpieceCoef D L ω σ j b (f b) ≠ 0) →
      |qInt D L Qf A ω f| ≤ coupMain D (sfEps D) L A ω f + (∏ b, cM D L b (f b)) * rem) :
    (∏ b, |EnvelopeInputsBlock.ecpieceCoef D L ω σ j b (f b)|) * qX D L Qf (sfEps D) A ω σ j f ≤
      (∏ b, |EnvelopeInputsBlock.ecpieceCoef D L ω σ j b (f b)|) * pieceBnd D L rem B ω f := by
  have hc0 : 0 ≤ ∏ b, |EnvelopeInputsBlock.ecpieceCoef D L ω σ j b (f b)| :=
    prod_nonneg fun b _ => abs_nonneg _
  have hM0 : 0 ≤ (∏ b, cM D L b (f b)) * rem :=
    mul_nonneg (prod_nonneg fun b _ => cM_nonneg D L b (f b)) hrem
  unfold pieceBnd
  simp only [hs, ↓reduceIte]
  by_cases hcf : ∀ b, EnvelopeInputsBlock.ecpieceCoef D L ω σ j b (f b) ≠ 0
  · refine mul_le_mul_of_nonneg_left ?_ hc0
    have := hpt hcf
    unfold qX
    split_ifs
    · exact max_le hM0 (by linarith)
    · exact hM0
  · obtain ⟨b, hb⟩ := not_forall.mp hcf
    have h0 : ∏ b, |EnvelopeInputsBlock.ecpieceCoef D L ω σ j b (f b)| = 0 :=
      prod_eq_zero (mem_univ b) (by rw [not_not.mp hb, abs_zero])
    rw [h0, zero_mul, zero_mul]

end Paper

end Sarkozy.OpsSteps
