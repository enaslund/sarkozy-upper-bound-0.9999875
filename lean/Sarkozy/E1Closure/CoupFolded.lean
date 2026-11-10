module

public import Sarkozy.E1Closure.SubSmall

@[expose] public section

/-!
# The folded laws of the coupled pieces of (E1) (`lem:record:folded-energy`) (EC)

EC, 8 November 2026. The proof of `lem:sharp-first` bounds a term `T′` by
`lem:record:folded-energy` at the cut `c_j` of its tag: `|T′| ≤ ∏ d · √𝔈₊ √𝔈₋`. Here this is set
up for (E1)'s coupled pieces `ecpiece` under a selection `ω`, at the tag `j`:

* the local laws `eK` (the coupled law, with a whole difference of another tag set to `0`, as in
  TH's `wpieceK`; such pieces have coefficient `0`), the folded laws `eLp`, `eLm` and the bracket
  constants `eD`:
  - `μ_𝔟` (unselected entry factor): itself ((R2));
  - a selected envelope `D^ε_{𝔟,t}` and a bracket record `κu_{𝔟,i}`: the diagonal laws of their
    half marginals (positive measures);
  - the first-stage pieces: TH's `wpieceLp`, `wpieceLm` (the full folded law
    `κ(1) ∑_s π_s Diag(m_±(κ_s))` of a whole difference, with `d = d̃`);
* **`e_bracket`** (`lem:record:folded-energy`(a)), positivity at the cut, positive records, masses
  (`eMass`);
* **`ecpieceK_eq_eK`**: at a piece with nonzero coefficient the two laws agree.
-/

namespace Sarkozy.E1Closure

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.CancellationSteps Sarkozy.BlockAnchor Sarkozy.DensityChain2
  Sarkozy.DensityFibre Sarkozy.EnvelopeInputsBlock Sarkozy.RecordExpansion
  Sarkozy.RecordExpansion.Choice
open Sarkozy.Param (Params)

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ) (dec : DecFamily D L)
  (j : D.FS.Tag)

/-- The local coupled law at the tag `j` (a whole difference of another tag is `0`). -/
noncomputable def eK (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType)) :
    CEPiece D L b → TheoremCBlock.AtomMeasure m₀ blk p L b
  | Sum.inl none => entryFactor (D.R.law p L b) (D.CL.D L b) o
  | Sum.inl (some i) => D.GB.κu L b i
  | Sum.inr (i, y) => ThetaOne.wpieceK (D := D) (L := L) j b (Sum.inr ⟨i, y⟩)

/-- The plus folded law at the cut `c_j`. -/
noncomputable def eLp (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType)) :
    CEPiece D L b → TheoremCBlock.AtomMeasure m₀ blk p L b
  | Sum.inl none => o.elim (D.R.law p L b) fun te =>
      (D.FS.cut j).diagonalLaw (halfMarginalPlus (D.FS.cut j) (D.CL.D L b te.1 te.2))
  | Sum.inl (some i) => (D.FS.cut j).diagonalLaw (halfMarginalPlus (D.FS.cut j) (D.GB.κu L b i))
  | Sum.inr (i, y) => ThetaOne.wpieceLp dec j b (Sum.inr ⟨i, y⟩)

/-- The minus folded law at the cut `c_j`. -/
noncomputable def eLm (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType)) :
    CEPiece D L b → TheoremCBlock.AtomMeasure m₀ blk p L b
  | Sum.inl none => o.elim (D.R.law p L b) fun te =>
      (D.FS.cut j).diagonalLaw (halfMarginalMinus (D.FS.cut j) (D.CL.D L b te.1 te.2))
  | Sum.inl (some i) => (D.FS.cut j).diagonalLaw (halfMarginalMinus (D.FS.cut j) (D.GB.κu L b i))
  | Sum.inr (i, y) => ThetaOne.wpieceLm dec j b (Sum.inr ⟨i, y⟩)

/-- The bracket constants: the sharp constant `d̃` at a whole difference, `1` otherwise. -/
noncomputable def eD (b : BlockAtom Bk J L) : CEPiece D L b → ℝ
  | Sum.inl _ => 1
  | Sum.inr (i, none) => D.FS.dconst L b i
  | Sum.inr (_, some _) => 1

/-- The masses of the folded laws. -/
noncomputable def eMass (b : BlockAtom Bk J L) : CEPiece D L b → ℝ
  | Sum.inl none => 1
  | Sum.inl (some i) => mass (D.GB.κu L b i)
  | Sum.inr (i, none) => mass (D.FS.κ L b i)
  | Sum.inr (i, some t) => if t then mass (D.FS.κ' L b i) else mass (D.FS.κ L b i)

/-- Whether the piece carries `μ_𝔟` (unselected entry factor). -/
def eIsMu (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType)) : CEPiece D L b → Bool
  | Sum.inl none => o.isNone
  | _ => false

omit [DecidableEq P] in
theorem eD_nonneg (b : BlockAtom Bk J L) (x : CEPiece D L b) : 0 ≤ eD D L b x := by
  rcases x with (_ | i) | ⟨i, _ | t⟩
  · exact zero_le_one
  · exact zero_le_one
  · exact D.FS.dconst_nonneg L b i
  · exact zero_le_one

omit [DecidableEq P] in
theorem eMass_nonneg (b : BlockAtom Bk J L) (x : CEPiece D L b) : 0 ≤ eMass D L b x := by
  rcases x with (_ | i) | ⟨i, _ | t⟩
  · exact zero_le_one
  · exact TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.GB.κu_pos L b i).1
  · exact TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1
  · cases t
    · exact TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1
    · exact TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ'_pos L b i).1

omit [DecidableEq P] in
theorem eLp_positive (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType))
    (x : CEPiece D L b) : (D.FS.cut j).Positive (eLp D L dec j b o x) := by
  rcases x with (_ | i) | ⟨i, y⟩
  · rcases o with _ | ⟨t, e⟩
    · exact ThetaOne.wpieceLp_positive dec j b (Sum.inl none)
    · exact (D.FS.cut j).diagonalLaw_positive
        (halfMarginalPlus_nonneg _ (D.CL.D_prob L b t e).1)
  · exact (D.FS.cut j).diagonalLaw_positive (halfMarginalPlus_nonneg _ (D.GB.κu_pos L b i).1)
  · exact ThetaOne.wpieceLp_positive dec j b (Sum.inr ⟨i, y⟩)

omit [DecidableEq P] in
theorem eLm_positive (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType))
    (x : CEPiece D L b) : (D.FS.cut j).Positive (eLm D L dec j b o x) := by
  rcases x with (_ | i) | ⟨i, y⟩
  · rcases o with _ | ⟨t, e⟩
    · exact ThetaOne.wpieceLm_positive dec j b (Sum.inl none)
    · exact (D.FS.cut j).diagonalLaw_positive
        (halfMarginalMinus_nonneg _ (D.CL.D_prob L b t e).1)
  · exact (D.FS.cut j).diagonalLaw_positive (halfMarginalMinus_nonneg _ (D.GB.κu_pos L b i).1)
  · exact ThetaOne.wpieceLm_positive dec j b (Sum.inr ⟨i, y⟩)

omit [DecidableEq P] in
/-- **Every coupled piece is bracketed at `c_j` by its folded laws**
(`lem:record:folded-energy`(a); TH's `wpiece_bracket` at the first-stage pieces and `μ`). -/
theorem e_bracket (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType))
    (x : CEPiece D L b) :
    (D.FS.cut j).Bracket (eD D L b x • eLp D L dec j b o x) (eK D L j b o x)
      (eD D L b x • eLm D L dec j b o x) := by
  rcases x with (_ | i) | ⟨i, y⟩
  · rcases o with _ | ⟨t, e⟩
    · exact ThetaOne.wpiece_bracket dec j b (Sum.inl none)
    · exact bracket_of_nonneg _ _ (D.CL.D_prob L b t e).1
  · exact bracket_of_nonneg _ _ (D.GB.κu_pos L b i).1
  · rcases y with _ | t
    · exact ThetaOne.wpiece_bracket dec j b (Sum.inr ⟨i, none⟩)
    · exact ThetaOne.wpiece_bracket dec j b (Sum.inr ⟨i, some t⟩)

omit [DecidableEq P] in
theorem isPositiveRecord_eLp (hp : ∀ j, (p L j).Prime) (b : BlockAtom Bk J L)
    (o : Option (D.CL.T L b × ChangeType)) (x : CEPiece D L b) :
    IsPositiveRecord (eLp D L dec j b o x) := by
  rcases x with (_ | i) | ⟨i, y⟩
  · rcases o with _ | ⟨t, e⟩
    · exact isPositiveRecord_muLaw D L hp b
    · exact isPositiveRecord_diag_plus _ ⟨(D.CL.D_prob L b t e).1, D.CL.D_unif L b t e⟩
  · exact isPositiveRecord_diag_plus _ (D.GB.κu_pos L b i)
  · exact SharpFirst.isPositiveRecord_wpieceLp dec hp j b (Sum.inr ⟨i, y⟩)

omit [DecidableEq P] in
theorem isPositiveRecord_eLm (hp : ∀ j, (p L j).Prime) (b : BlockAtom Bk J L)
    (o : Option (D.CL.T L b × ChangeType)) (x : CEPiece D L b) :
    IsPositiveRecord (eLm D L dec j b o x) := by
  rcases x with (_ | i) | ⟨i, y⟩
  · rcases o with _ | ⟨t, e⟩
    · exact isPositiveRecord_muLaw D L hp b
    · exact isPositiveRecord_diag_minus _ ⟨(D.CL.D_prob L b t e).1, D.CL.D_unif L b t e⟩
  · exact isPositiveRecord_diag_minus _ (D.GB.κu_pos L b i)
  · exact SharpFirst.isPositiveRecord_wpieceLm dec hp j b (Sum.inr ⟨i, y⟩)

omit [DecidableEq P] in
theorem mass_eLp (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType))
    (x : CEPiece D L b) : mass (eLp D L dec j b o x) = eMass D L b x := by
  rcases x with (_ | i) | ⟨i, _ | t⟩
  · rcases o with _ | ⟨t, e⟩
    · exact Sarkozy.LargeSums.mass_refLaw D L b
    · exact (Sarkozy.LargeSums.mass_diag_plus _ _).trans (D.CL.D_prob L b t e).2
  · exact Sarkozy.LargeSums.mass_diag_plus _ _
  · exact SharpFirst.mass_wpieceLp dec j b (Sum.inr ⟨i, none⟩)
  · exact SharpFirst.mass_wpieceLp dec j b (Sum.inr ⟨i, some t⟩)

omit [DecidableEq P] in
theorem mass_eLm (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType))
    (x : CEPiece D L b) : mass (eLm D L dec j b o x) = eMass D L b x := by
  rcases x with (_ | i) | ⟨i, _ | t⟩
  · rcases o with _ | ⟨t, e⟩
    · exact Sarkozy.LargeSums.mass_refLaw D L b
    · exact (Sarkozy.LargeSums.mass_diag_minus _ _).trans (D.CL.D_prob L b t e).2
  · exact Sarkozy.LargeSums.mass_diag_minus _ _
  · exact SharpFirst.mass_wpieceLm dec j b (Sum.inr ⟨i, none⟩)
  · exact SharpFirst.mass_wpieceLm dec j b (Sum.inr ⟨i, some t⟩)

omit [DecidableEq P] in
theorem eLp_of_mu (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType))
    (x : CEPiece D L b) (hx : eIsMu D L b o x = true) : eLp D L dec j b o x = D.R.law p L b := by
  rcases x with (_ | i) | ⟨i, y⟩
  · rcases o with _ | te
    · rfl
    · simp [eIsMu] at hx
  · simp [eIsMu] at hx
  · simp [eIsMu] at hx

omit [DecidableEq P] in
theorem eLm_of_mu (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType))
    (x : CEPiece D L b) (hx : eIsMu D L b o x = true) : eLm D L dec j b o x = D.R.law p L b := by
  rcases x with (_ | i) | ⟨i, y⟩
  · rcases o with _ | te
    · rfl
    · simp [eIsMu] at hx
  · simp [eIsMu] at hx
  · simp [eIsMu] at hx

omit [DecidableEq P] in
theorem eMass_of_mu (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType))
    (x : CEPiece D L b) (hx : eIsMu D L b o x = true) : eMass D L b x = 1 := by
  rcases x with (_ | i) | ⟨i, y⟩
  · rfl
  · simp [eIsMu] at hx
  · simp [eIsMu] at hx

omit [DecidableEq P] in
/-- **At a piece with nonzero coefficient, the coupled law is the local law `eK`.** -/
theorem ecpieceK_eq_eK (ω : Choice (D.CL.T L)) (σ : ∀ b, Option (D.FS.Ib L b))
    (b : BlockAtom Bk J L) (x : CEPiece D L b) (hc : ecpieceCoef D L ω σ j b x ≠ 0) :
    ecpieceK D L ω b x = eK D L j b (ω b) x := by
  rcases x with (_ | i) | ⟨i, _ | t⟩
  · rfl
  · rfl
  · have ht : D.FS.tag L b i = j := by
      by_contra hne
      exact hc (by simp [EnvelopeInputsBlock.ecpieceCoef, hne])
    simp [EnvelopeInputsBlock.ecpieceK, eK, ThetaOne.wpieceK, ht]
  · cases t <;> simp [EnvelopeInputsBlock.ecpieceK, eK, ThetaOne.wpieceK]

section Paper

variable (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)

/-- The atoms of a coupled piece that do not carry `μ_𝔟`. -/
noncomputable def coupAtoms (L : ℕ) (ω : Choice (D.CL.T L)) (f : ∀ b, CEPiece D L b) :
    Finset (BlockAtom Bk PaperJt L) :=
  univ.filter fun b => eIsMu D L b (ω b) (f b) = false

omit [DecidableEq P] in
theorem coupAtoms_nonempty {L : ℕ} {ω : Choice (D.CL.T L)} (hω : IsSelection ω)
    (f : ∀ b, CEPiece D L b) : (coupAtoms D L ω f).Nonempty := by
  obtain ⟨b, hb⟩ := (Choice.support_nonempty_iff ω).mpr hω.1
  refine ⟨b, ?_⟩
  simp only [Choice.support, mem_filter, mem_univ, true_and] at hb
  simp only [coupAtoms, mem_filter, mem_univ, true_and]
  rcases hf : f b with (_ | i) | ⟨i, y⟩
  · simp only [eIsMu]
    rcases hω : ω b with _ | te
    · rw [hω] at hb; simp at hb
    · rfl
  · rfl
  · rfl

omit [DecidableEq P] in
theorem prod_coupQ_eq (L : ℕ) (ω : Choice (D.CL.T L)) (f : ∀ b, CEPiece D L b) :
    ∏ b, coupQ D L b (ω b) (f b) =
      ∏ b, ((if b ∈ coupAtoms D L ω f then atomQ blk paperTail D.S.pp D.S.ep L b else 1 : ℕ) :
        ℝ) := by
  refine prod_congr rfl fun b _ => ?_
  simp only [coupAtoms, mem_filter, mem_univ, true_and]
  rcases f b with (_ | i) | ⟨i, y⟩
  · rcases ω b with _ | te
    · simp [coupQ, eIsMu]
    · simp [coupQ, eIsMu, Sarkozy.LargeSums.atomQR]
  · simp [coupQ, eIsMu, Sarkozy.LargeSums.atomQR]
  · simp [coupQ, eIsMu, Sarkozy.LargeSums.atomQR]

omit [DecidableEq P] in
theorem prod_mass_coupAtoms (L : ℕ) (dec : DecFamily D L) (j : D.FS.Tag) (ω : Choice (D.CL.T L))
    (f : ∀ b, CEPiece D L b) :
    (∏ b ∈ coupAtoms D L ω f, mass (eLp D L dec j b (ω b) (f b)) = ∏ b, eMass D L b (f b)) ∧
    (∏ b ∈ coupAtoms D L ω f, mass (eLm D L dec j b (ω b) (f b)) = ∏ b, eMass D L b (f b)) := by
  unfold coupAtoms
  rw [prod_filter, prod_filter]
  refine ⟨prod_congr rfl fun b _ => ?_, prod_congr rfl fun b _ => ?_⟩
  · cases hm : eIsMu D L b (ω b) (f b)
    · simp only [↓reduceIte]
      exact mass_eLp D L dec j b (ω b) (f b)
    · simp only [Bool.true_eq_false, ↓reduceIte]
      exact (eMass_of_mu D L b (ω b) (f b) hm).symm
  · cases hm : eIsMu D L b (ω b) (f b)
    · simp only [↓reduceIte]
      exact mass_eLm D L dec j b (ω b) (f b)
    · simp only [Bool.true_eq_false, ↓reduceIte]
      exact (eMass_of_mu D L b (ω b) (f b) hm).symm

omit [DecidableEq P] in
/-- **The price bookkeeping of a coupled piece** (`lem:sharp-first`: "the geometric mean retains
`Π(T′)`"): `(∏ d)(∏ m) sq(D_E)^a ≤ ∏_𝔟 g_𝔟`. -/
theorem coupPrice_le
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (L : ℕ) (ω : Choice (D.CL.T L)) (f : ∀ b, CEPiece D L b) :
    (∏ b, eD D L b (f b)) * (∏ b, eMass D L b (f b)) *
        ((leastSquare (∏ b ∈ coupAtoms D L ω f, crtModuli m₀ blk paperTail L b) : ℕ) : ℝ) ^ a ≤
      ∏ b, ecpieceG D L ω b (f b) := by
  have hsq : ((leastSquare (∏ b ∈ coupAtoms D L ω f, crtModuli m₀ blk paperTail L b) : ℕ) :
      ℝ) ^ a = ∏ b ∈ coupAtoms D L ω f,
        ((leastSquare (crtModuli m₀ blk paperTail L b) : ℕ) : ℝ) ^ a := by
    rw [leastSquare_prod_coprime (crtModuli m₀ blk paperTail L) (crtModuli_pairwise blk (hpair L)),
      Nat.cast_prod, ← Real.finsetProd_rpow _ _ (fun _ _ => Nat.cast_nonneg _)]
  rw [hsq]
  unfold coupAtoms
  rw [prod_filter, ← prod_mul_distrib, ← prod_mul_distrib]
  refine prod_le_prod₀ (fun b _ => mul_nonneg (mul_nonneg (eD_nonneg D L b (f b))
    (eMass_nonneg D L b (f b))) ?_) fun b _ => ?_
  · split_ifs
    · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · exact zero_le_one
  · have hs := hselF_of_parity D (prefix_pairwise (hpair L)) hpar hsel L b
    rcases hf : f b with (_ | i) | ⟨i, _ | t⟩
    · rcases hω : ω b with _ | te
      · simp [eIsMu, eD, eMass, EnvelopeInputsBlock.ecpieceG, hω]
      · simp only [eIsMu, hω, Option.isNone_some, ↓reduceIte, eD, eMass, one_mul,
          EnvelopeInputsBlock.ecpieceG, Option.elim]
        exact hs
    · simp only [eIsMu, ↓reduceIte, eD, eMass, one_mul,
        EnvelopeInputsBlock.ecpieceG]
      exact mul_le_mul_of_nonneg_left hs
        (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.GB.κu_pos L b i).1)
    · simp only [eIsMu, ↓reduceIte, eD, eMass,
        EnvelopeInputsBlock.ecpieceG, TheoremCBlock.FirstStage.dprice, sharpPrice]
      have hm := TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1
      have hd := D.FS.dconst_nonneg L b i
      calc D.FS.dconst L b i * mass (D.FS.κ L b i) *
            ((leastSquare (crtModuli m₀ blk paperTail L b) : ℕ) : ℝ) ^ a
          ≤ D.FS.dconst L b i * mass (D.FS.κ L b i) *
            TheoremCBlock.selectionFactor a paperTail D.S.selPre L b :=
            mul_le_mul_of_nonneg_left hs (mul_nonneg hd hm)
        _ = _ := by ring
    · cases t
      · simp only [eIsMu, Bool.false_eq_true, ↓reduceIte, eD, eMass, one_mul,
          EnvelopeInputsBlock.ecpieceG]
        exact mul_le_mul_of_nonneg_left hs
          (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1)
      · simp only [eIsMu, ↓reduceIte, eD, eMass, one_mul,
          EnvelopeInputsBlock.ecpieceG]
        exact mul_le_mul_of_nonneg_left hs
          (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ'_pos L b i).1)

omit [DecidableEq P] in
/-- The remainder coefficient: `(∏ d)(∏ m) ≤ ∏ cM`. -/
theorem coupRem_le (L : ℕ) (f : ∀ b, CEPiece D L b) :
    (∏ b, eD D L b (f b)) * (∏ b, eMass D L b (f b)) ≤ ∏ b, cM D L b (f b) := by
  rw [← prod_mul_distrib]
  refine prod_le_prod₀ (fun b _ => mul_nonneg (eD_nonneg D L b (f b))
    (eMass_nonneg D L b (f b))) fun b _ => ?_
  rcases f b with (_ | i) | ⟨i, _ | t⟩
  · simp [eD, eMass, cM]
  · simp [eD, eMass, cM]
  · simp only [eD, eMass, cM]
    have := TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1
    linarith
  · cases t <;> simp [eD, eMass, cM]

end Paper

end Sarkozy.E1Closure
