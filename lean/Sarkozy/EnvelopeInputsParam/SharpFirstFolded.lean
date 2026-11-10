module

public import Sarkozy.EnvelopeInputs.SharpFirstFolded
public import Sarkozy.TheoremCParam.StructuredSharpFirstGlue

@[expose] public section



open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.EnvelopeInputsParam

open Sarkozy.EnvelopeInputs
open Sarkozy.Param (Params)

variable {a : ℝ}

open Sarkozy.TheoremC Sarkozy.Comparison Sarkozy.PaperFrame Sarkozy.RecordExpansion
  Sarkozy.Structured ReflectionCut

section Pieces

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (D : TheoremCParam.ComparisonData a m₀ p pr h E) (L : ℕ)

/-- Sharp decompositions of all the differences of the first stage at the scale `L`. -/
abbrev DecFamily : Type 1 :=
  ∀ b i, SharpDecomp (D.FS.cut (D.FS.tag L b i)) (D.FS.κ L b i) (D.FS.κ' L b i - D.FS.κ L b i)
    (D.FS.dconst L b i)

omit [DecidableEq P] in
theorem nonempty_decFamily : Nonempty (DecFamily D L) := by
  classical
  exact ⟨fun b i => Classical.choice (nonempty_sharpDecomp (D.FS.sharp L b i))⟩

variable {D L} (dec : DecFamily D L)

/-- The pieces of an atom: `μ_𝔟` and the records `κa_h` of `ρ_𝔟` (`inl`), and for every
difference `i` the components `s` of its sharp decomposition (`inr ⟨i, inl s⟩`) and its two
positive parts (`inr ⟨i, inr t⟩`, `t = true` for `κ'`). -/
abbrev Piece (b : PaperAtom J L) : Type :=
  Option (D.FS.Ia L b) ⊕ (Σ i : D.FS.Ib L b, (dec b i).S ⊕ Bool)

/-- The coefficients of the pieces for the choice `σ` and the tag `j`. -/
noncomputable def pieceCoef (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) (b : PaperAtom J L) :
    Piece dec b → ℝ
  | Sum.inl o => if σ b = none then o.elim 1 (D.FS.ca L b) else 0
  | Sum.inr ⟨i, Sum.inl s⟩ =>
      if σ b = some i ∧ D.FS.tag L b i = j then mass (D.FS.κ L b i) * (dec b i).π.weight s
      else 0
  | Sum.inr ⟨i, Sum.inr t⟩ =>
      if σ b = some i ∧ D.FS.tag L b i ≠ j then (if t then 1 else -1) else 0

/-- The pieces. -/
noncomputable def pieceK (j : D.FS.Tag) (b : PaperAtom J L) : Piece dec b → AtomMeasure m₀ p L b
  | Sum.inl none => D.R.law p L b
  | Sum.inl (some h) => D.FS.κa L b h
  | Sum.inr ⟨i, Sum.inl s⟩ => if D.FS.tag L b i = j then (dec b i).Ks s else 0
  | Sum.inr ⟨i, Sum.inr t⟩ => if t then D.FS.κ' L b i else D.FS.κ L b i

/-- The plus folded factors of the pieces at the cut `c_j`. -/
noncomputable def pieceLp (j : D.FS.Tag) (b : PaperAtom J L) : Piece dec b → AtomMeasure m₀ p L b
  | Sum.inl none => D.R.law p L b
  | Sum.inl (some h) => (D.FS.cut j).diagonalLaw (halfMarginalPlus (D.FS.cut j) (D.FS.κa L b h))
  | Sum.inr ⟨i, Sum.inl s⟩ =>
      (D.FS.cut j).diagonalLaw (halfMarginalPlus (D.FS.cut j) ((dec b i).κs s))
  | Sum.inr ⟨i, Sum.inr t⟩ => (D.FS.cut j).diagonalLaw
      (halfMarginalPlus (D.FS.cut j) (if t then D.FS.κ' L b i else D.FS.κ L b i))

/-- The minus folded factors of the pieces at the cut `c_j`. -/
noncomputable def pieceLm (j : D.FS.Tag) (b : PaperAtom J L) : Piece dec b → AtomMeasure m₀ p L b
  | Sum.inl none => D.R.law p L b
  | Sum.inl (some h) => (D.FS.cut j).diagonalLaw (halfMarginalMinus (D.FS.cut j) (D.FS.κa L b h))
  | Sum.inr ⟨i, Sum.inl s⟩ =>
      (D.FS.cut j).diagonalLaw (halfMarginalMinus (D.FS.cut j) ((dec b i).κs s))
  | Sum.inr ⟨i, Sum.inr t⟩ => (D.FS.cut j).diagonalLaw
      (halfMarginalMinus (D.FS.cut j) (if t then D.FS.κ' L b i else D.FS.κ L b i))

/-- The bracket constants of the pieces: the sharp constant for the components, one otherwise. -/
noncomputable def pieceD (b : PaperAtom J L) : Piece dec b → ℝ
  | Sum.inl _ => 1
  | Sum.inr ⟨i, Sum.inl _⟩ => D.FS.dconst L b i
  | Sum.inr ⟨_, Sum.inr _⟩ => 1

/-- The prices of the folded pieces: mass times selection factor (one for `μ_𝔟`). -/
noncomputable def pieceG (b : PaperAtom J L) : Piece dec b → ℝ
  | Sum.inl none => 1
  | Sum.inl (some h) => mass (D.FS.κa L b h) * TheoremCParam.selectionFactor a p D.S.selPre L b
  | Sum.inr ⟨_, Sum.inl _⟩ => TheoremCParam.selectionFactor a p D.S.selPre L b
  | Sum.inr ⟨i, Sum.inr t⟩ =>
      (if t then mass (D.FS.κ' L b i) else mass
          (D.FS.κ L b i)) * TheoremCParam.selectionFactor a p D.S.selPre L b

omit [DecidableEq P] in
/-- **The pieces add up to the factor of the term**: `∑_x c_x K_x = σ_𝔟 ? δ_{𝔟,σ_𝔟} : ρ_𝔟`. -/
theorem pieceSum_eq (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) (b : PaperAtom J L) :
    ∑ x, pieceCoef dec σ j b x • pieceK dec j b x =
      (σ b).elim (D.FS.ρ L b) (fun i => D.FS.κ' L b i - D.FS.κ L b i) := by
  rw [Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_sigma]
  rcases hσ : σ b with _ | i₀
  · have hinr : ∀ i y, pieceCoef dec σ j b (Sum.inr ⟨i, y⟩) = 0 := by
      intro i y
      rcases y with s | t <;> simp [pieceCoef, hσ]
    simp only [hinr, zero_smul, Finset.sum_const_zero, add_zero]
    simp only [pieceCoef, pieceK, hσ, ↓reduceIte, Option.elim, one_smul]
    have h := D.FS.ρ_sub L b
    rw [sub_eq_iff_eq_add'] at h
    exact h.symm
  · have hinl : ∀ o, pieceCoef dec σ j b (Sum.inl o) = 0 := by
      intro o
      simp [pieceCoef, hσ]
    have hinr : ∀ i, i ≠ i₀ → ∀ y, pieceCoef dec σ j b (Sum.inr ⟨i, y⟩) = 0 := by
      intro i hi y
      rcases y with s | t <;> simp [pieceCoef, hσ, Ne.symm hi]
    simp only [hinl, zero_smul, Finset.sum_const_zero, zero_add]
    rw [Finset.sum_eq_single i₀ (fun i _ hi => by simp [hinr i hi]) (by simp)]
    simp only [Option.elim]
    rw [Fintype.sum_sum_type, Fintype.sum_bool]
    by_cases ht : D.FS.tag L b i₀ = j
    · have hb : ∀ t : Bool, pieceCoef dec σ j b (Sum.inr ⟨i₀, Sum.inr t⟩) = 0 := by
        intro t
        simp [pieceCoef, hσ, ht]
      simp only [hb, zero_smul, add_zero]
      simp only [pieceCoef, pieceK, hσ, ht, and_self, ↓reduceIte]
      refine Eq.trans ?_ (dec b i₀).hζ.symm
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [smul_smul]
    · have hs : ∀ s, pieceCoef dec σ j b (Sum.inr ⟨i₀, Sum.inl s⟩) = 0 := by
        intro s
        simp [pieceCoef, hσ, ht]
      simp only [hs, zero_smul, Finset.sum_const_zero, zero_add]
      have ht1 : pieceCoef dec σ j b (Sum.inr ⟨i₀, Sum.inr true⟩) = 1 := by
        simp [pieceCoef, hσ, ht]
      have ht2 : pieceCoef dec σ j b (Sum.inr ⟨i₀, Sum.inr false⟩) = -1 := by
        simp [pieceCoef, hσ, ht]
      have hk1 : pieceK dec j b (Sum.inr ⟨i₀, Sum.inr true⟩) = D.FS.κ' L b i₀ := rfl
      have hk2 : pieceK dec j b (Sum.inr ⟨i₀, Sum.inr false⟩) = D.FS.κ L b i₀ := rfl
      rw [ht1, ht2, hk1, hk2, one_smul]
      apply LinearMap.ext
      intro F
      simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul]
      ring

omit [DecidableEq P] in
theorem pieceD_nonneg (b : PaperAtom J L) (x : Piece dec b) : 0 ≤ pieceD dec b x := by
  rcases x with _ | ⟨i, s | t⟩
  · exact zero_le_one
  · exact D.FS.dconst_nonneg L b i
  · exact zero_le_one

omit [DecidableEq P] in
theorem pieceLp_positive (j : D.FS.Tag) (b : PaperAtom J L) (x : Piece dec b) :
    (D.FS.cut j).Positive (pieceLp dec j b x) := by
  rcases x with (_ | hh) | ⟨i, s | t⟩
  · exact D.law_positive (D.FS.cut_family j) L b
  · exact (D.FS.cut j).diagonalLaw_positive
      (halfMarginalPlus_nonneg _ (D.FS.κa_pos L b hh).1)
  · exact (D.FS.cut j).diagonalLaw_positive (halfMarginalPlus_nonneg _ ((dec b i).prob s).1)
  · cases t
    · exact (D.FS.cut j).diagonalLaw_positive (halfMarginalPlus_nonneg _ (D.FS.κ_pos L b i).1)
    · exact (D.FS.cut j).diagonalLaw_positive (halfMarginalPlus_nonneg _ (D.FS.κ'_pos L b i).1)

omit [DecidableEq P] in
theorem pieceLm_positive (j : D.FS.Tag) (b : PaperAtom J L) (x : Piece dec b) :
    (D.FS.cut j).Positive (pieceLm dec j b x) := by
  rcases x with (_ | hh) | ⟨i, s | t⟩
  · exact D.law_positive (D.FS.cut_family j) L b
  · exact (D.FS.cut j).diagonalLaw_positive
      (halfMarginalMinus_nonneg _ (D.FS.κa_pos L b hh).1)
  · exact (D.FS.cut j).diagonalLaw_positive (halfMarginalMinus_nonneg _ ((dec b i).prob s).1)
  · cases t
    · exact (D.FS.cut j).diagonalLaw_positive (halfMarginalMinus_nonneg _ (D.FS.κ_pos L b i).1)
    · exact (D.FS.cut j).diagonalLaw_positive (halfMarginalMinus_nonneg _ (D.FS.κ'_pos L b i).1)

omit [DecidableEq P] in
/-- Every piece is bracketed at the cut `c_j` by its folded factors. -/
theorem piece_bracket (j : D.FS.Tag) (b : PaperAtom J L) (x : Piece dec b) :
    (D.FS.cut j).Bracket (pieceD dec b x • pieceLp dec j b x) (pieceK dec j b x)
      (pieceD dec b x • pieceLm dec j b x) := by
  rcases x with (_ | hh) | ⟨i, s | t⟩
  · exact bracket_of_positive _ (D.law_positive (D.FS.cut_family j) L b)
  · exact bracket_of_nonneg _ _ (D.FS.κa_pos L b hh).1
  · by_cases ht : D.FS.tag L b i = j
    · simp only [pieceD, pieceLp, pieceLm, pieceK, ht, ↓reduceIte]
      have hsh := (dec b i).sharp s
      subst ht
      exact (sharp_iff_bracket _ _ (halfMarginalPlus_nonneg _ ((dec b i).prob s).1)
        (halfMarginalMinus_nonneg _ ((dec b i).prob s).1) (D.FS.dconst_nonneg L b i)).mp hsh
    · simp only [pieceD, pieceLp, pieceLm, pieceK, ht, ↓reduceIte]
      have hp := ((D.FS.cut j).diagonalLaw_positive
        (halfMarginalPlus_nonneg (D.FS.cut j) ((dec b i).prob s).1)).smul
          (D.FS.dconst_nonneg L b i)
      have hm := ((D.FS.cut j).diagonalLaw_positive
        (halfMarginalMinus_nonneg (D.FS.cut j) ((dec b i).prob s).1)).smul
          (D.FS.dconst_nonneg L b i)
      refine ⟨hp, hm, fun F G => ?_⟩
      have h1 := hp.nonneg F
      have h2 := hm.nonneg G
      have h0 : (D.FS.cut j).form (0 : AtomMeasure m₀ p L b) F G = 0 := rfl
      rw [h0]
      linarith
  · cases t
    · exact bracket_of_nonneg _ _ (D.FS.κ_pos L b i).1
    · exact bracket_of_nonneg _ _ (D.FS.κ'_pos L b i).1

omit [DecidableEq P] in
/-- **The folded factorization of a sharp-first term** (`lem:sharp-first` with
`lem:record:folded-energy` at the cut `c_j`): `|Y_σ| ≤ √𝔈₊ √𝔈₋` with the weighted folded energies
of the choices of pieces, which are nonnegative. -/
theorem sharp_term_le_folded (A : Finset ℤ) (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) :
    (∀ f, 0 ≤ foldedPlus (D.FS.cut j) (pieceLp dec j) (fun _ => atomLift m₀ p L A) f) ∧
    (∀ f, 0 ≤ foldedMinus (D.FS.cut j) (pieceLm dec j) (fun _ => atomLift m₀ p L A) f) ∧
    |diagonalIntegral (tensorLaw (fun b => (σ b).elim (D.FS.ρ L b)
        (fun i => D.FS.κ' L b i - D.FS.κ L b i))) (atomLift m₀ p L A)| ≤
      Real.sqrt (∑ f, choiceWeight (pieceCoef dec σ j) (pieceD dec) f *
          foldedPlus (D.FS.cut j) (pieceLp dec j) (fun _ => atomLift m₀ p L A) f) *
        Real.sqrt (∑ f, choiceWeight (pieceCoef dec σ j) (pieceD dec) f *
          foldedMinus (D.FS.cut j) (pieceLm dec j) (fun _ => atomLift m₀ p L A) f) := by
  have hlaw : (fun b => (σ b).elim (D.FS.ρ L b) (fun i => D.FS.κ' L b i - D.FS.κ L b i)) =
      fun b => ∑ x, pieceCoef dec σ j b x • pieceK dec j b x :=
    funext fun b => (pieceSum_eq dec σ j b).symm
  rw [hlaw]
  exact abs_tensor_sum_le_folded (D.FS.cut j) (pieceCoef dec σ j) (pieceD dec) (pieceK dec j)
    (pieceLp dec j) (pieceLm dec j) (pieceD_nonneg dec) (pieceLp_positive dec j)
    (pieceLm_positive dec j) (piece_bracket dec j) (fun _ => atomLift m₀ p L A)

omit [DecidableEq P] in
/-- **The price bookkeeping of `lem:sharp-first`**: at every atom the weighted prices
`∑_x |c_x| d_x g_x` of the pieces are the factor of `tagWeight`: `d_{𝔟,i}` for a difference of
tag `j`, `v_{𝔟,i}` for a difference of another tag, `1 + p_𝔟` at an unchosen atom. -/
theorem sum_pieceWeight (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) (b : PaperAtom J L) :
    ∑ x, |pieceCoef dec σ j b x| * pieceD dec b x * pieceG dec b x =
      (σ b).elim (1 + D.FS.pvar L b)
        (fun i => if D.FS.tag L b i = j then D.FS.dprice L b i else D.FS.vprice L b i) := by
  rw [Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_sigma]
  rcases hσ : σ b with _ | i₀
  · have hinr : ∀ i y, pieceCoef dec σ j b (Sum.inr ⟨i, y⟩) = 0 := by
      intro i y
      rcases y with s | t <;> simp [pieceCoef, hσ]
    simp only [hinr, abs_zero, zero_mul, Finset.sum_const_zero, add_zero]
    simp only [pieceCoef, pieceD, pieceG, hσ, ↓reduceIte, Option.elim, abs_one, mul_one]
    unfold TheoremCParam.FirstStage.pvar
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · have hinl : ∀ o, pieceCoef dec σ j b (Sum.inl o) = 0 := by
      intro o
      simp [pieceCoef, hσ]
    have hinr : ∀ i, i ≠ i₀ → ∀ y, pieceCoef dec σ j b (Sum.inr ⟨i, y⟩) = 0 := by
      intro i hi y
      rcases y with s | t <;> simp [pieceCoef, hσ, Ne.symm hi]
    simp only [hinl, abs_zero, zero_mul, Finset.sum_const_zero, zero_add]
    rw [Finset.sum_eq_single i₀ (fun i _ hi => by simp [hinr i hi]) (by simp)]
    simp only [Option.elim]
    rw [Fintype.sum_sum_type, Fintype.sum_bool]
    by_cases ht : D.FS.tag L b i₀ = j
    · have hb : ∀ t : Bool, pieceCoef dec σ j b (Sum.inr ⟨i₀, Sum.inr t⟩) = 0 := by
        intro t
        simp [pieceCoef, hσ, ht]
      simp only [hb, abs_zero, zero_mul, add_zero]
      simp only [pieceCoef, pieceD, pieceG, hσ, ht, and_self, ↓reduceIte]
      have hm := TheoremCParam.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i₀).1
      have hterm : ∀ s, |mass (D.FS.κ L b i₀) * (dec b i₀).π.weight s| * D.FS.dconst L b i₀ *
          TheoremCParam.selectionFactor a p D.S.selPre L b =
            (dec b i₀).π.weight s * (mass (D.FS.κ L b i₀) * D.FS.dconst L b i₀ *
              TheoremCParam.selectionFactor a p D.S.selPre L b) := by
        intro s
        rw [abs_of_nonneg (mul_nonneg hm ((dec b i₀).π.nonneg s))]
        ring
      rw [Finset.sum_congr rfl fun s _ => hterm s, ← Finset.sum_mul, (dec b i₀).π.total,
        one_mul]
      rfl
    · have hs : ∀ s, pieceCoef dec σ j b (Sum.inr ⟨i₀, Sum.inl s⟩) = 0 := by
        intro s
        simp [pieceCoef, hσ, ht]
      simp only [hs, abs_zero, zero_mul, Finset.sum_const_zero, zero_add]
      have ht1 : pieceCoef dec σ j b (Sum.inr ⟨i₀, Sum.inr true⟩) = 1 := by
        simp [pieceCoef, hσ, ht]
      have ht2 : pieceCoef dec σ j b (Sum.inr ⟨i₀, Sum.inr false⟩) = -1 := by
        simp [pieceCoef, hσ, ht]
      rw [ht1, ht2]
      simp only [pieceD, pieceG, ht, ↓reduceIte, abs_one, abs_neg, one_mul, Bool.false_eq_true]
      unfold TheoremCParam.FirstStage.vprice
      ring

end Pieces

section Final

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

omit [DecidableEq P] in
/-- **`SharpFirstTerms` from the folded-energy bounds of the pieces** (`lem:sharp-first`,
`lem:record:folded-energy`). Fix sharp decompositions `dec` of the differences
(`nonempty_decFamily`). Suppose that at every least counterexample, for every nonempty choice
`σ`, every tag `j` present and every choice `f` of pieces, the two folded energies satisfy
`𝔈_±(f) ≤ (∏_𝔟 g_𝔟(f_𝔟)) (1 + ε_L) Y + r_±(f)` (`prop:record:density-structured` for the folded
laws, which are tensor products of the `μ_𝔟` and of diagonal laws of half marginals of positive
measures), with nonnegative remainders whose weighted sums are density-linear. Then
`D.SharpFirstTerms` holds. The multilinear expansion over the mixture components, the variation of
the other tags and the price bookkeeping are proved here. -/
theorem sharpFirstTerms_of_foldedPieces (D : TheoremCParam.ComparisonData a m₀ p pr h E)
    (dec : ∀ L, DecFamily D L)
    (ε : ℕ → ℝ) (hε0 : ∀ L, 0 ≤ ε L) (hεt : Tendsto ε atTop (𝓝 0)) {c : ℝ} (hc : 0 ≤ c)
    (rp rm : ∀ L, Finset ℤ → (∀ b, Option (D.FS.Ib L b)) → D.FS.Tag →
      (∀ b, Piece (dec L) b) → ℝ)
    (hr0 : ∀ L A σ j f, 0 ≤ rp L A σ j f ∧ 0 ≤ rm L A σ j f)
    (hfold : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => ∀ σ : (∀ b, Option (D.FS.Ib L b)),
      σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec (D.FS.tag L) σ j → ∀ f,
      foldedPlus (D.FS.cut j) (pieceLp (dec L) j) (fun _ => atomLift m₀ p L A) f ≤
          (∏ b, pieceG (dec L) b (f b)) * ((1 + ε L) * D.Y L A) + rp L A σ j f ∧
        foldedMinus (D.FS.cut j) (pieceLm (dec L) j) (fun _ => atomLift m₀ p L A) f ≤
          (∏ b, pieceG (dec L) b (f b)) * ((1 + ε L) * D.Y L A) + rm L A σ j f))
    (hrem : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        ∑ j, ∑ f, choiceWeight (pieceCoef (dec L) σ j) (pieceD (dec L)) f *
          ((rp L A σ j f + rm L A σ j f) / 2) ≤ remainder c L A)) :
    D.SharpFirstTerms := by
  refine ⟨ε, hε0, hεt, c, hc, fun L A σ => ∑ j, ∑ f,
    choiceWeight (pieceCoef (dec L) σ j) (pieceD (dec L)) f *
      ((rp L A σ j f + rm L A σ j f) / 2), ?_, hrem⟩
  filter_upwards [hfold] with L hL
  intro C hC hk A hA hY σ hσ j hj
  obtain ⟨hFp0, hFm0, hY1⟩ := sharp_term_le_folded (dec L) A σ j
  have hw : ∀ f, 0 ≤ choiceWeight (pieceCoef (dec L) σ j) (pieceD (dec L)) f := fun f =>
    Finset.prod_nonneg fun b _ => mul_nonneg (abs_nonneg _) (pieceD_nonneg (dec L) b (f b))
  have htw : ∏ b, ∑ x, |pieceCoef (dec L) σ j b x| * pieceD (dec L) b x * pieceG (dec L) b x =
      tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (D.FS.pvar L) j σ := by
    unfold tagWeight
    exact Finset.prod_congr rfl fun b _ => sum_pieceWeight (dec L) σ j b
  have hFp := weighted_folded_le (pieceCoef (dec L) σ j) (pieceD (dec L)) (pieceG (dec L))
    (pieceD_nonneg (dec L)) _ (rp L A σ j) ((1 + ε L) * D.Y L A)
    (fun f => (hL C hC hk A hA hY σ hσ j hj f).1)
  have hFm := weighted_folded_le (pieceCoef (dec L) σ j) (pieceD (dec L)) (pieceG (dec L))
    (pieceD_nonneg (dec L)) _ (rm L A σ j) ((1 + ε L) * D.Y L A)
    (fun f => (hL C hC hk A hA hY σ hσ j hj f).2)
  rw [htw] at hFp hFm
  set w := choiceWeight (pieceCoef (dec L) σ j) (pieceD (dec L))
  set Fp := ∑ f, w f * foldedPlus (D.FS.cut j) (pieceLp (dec L) j) (fun _ => atomLift m₀ p L A) f
  set Fm := ∑ f, w f * foldedMinus (D.FS.cut j) (pieceLm (dec L) j) (fun _ => atomLift m₀ p L A) f
  set T := tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (D.FS.pvar L) j σ
  have hFp0' : 0 ≤ Fp := Finset.sum_nonneg fun f _ => mul_nonneg (hw f) (hFp0 f)
  have hFm0' : 0 ≤ Fm := Finset.sum_nonneg fun f _ => mul_nonneg (hw f) (hFm0 f)
  have hgm := sqrt_mul_sqrt_le_add_div_two hFp0' hFm0'
  have hsplit : ∑ f, w f * ((rp L A σ j f + rm L A σ j f) / 2) =
      ((∑ f, w f * rp L A σ j f) + ∑ f, w f * rm L A σ j f) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun f _ => ?_
    ring
  have hsingle : ∑ f, w f * ((rp L A σ j f + rm L A σ j f) / 2) ≤
      ∑ j', ∑ f, choiceWeight (pieceCoef (dec L) σ j') (pieceD (dec L)) f *
        ((rp L A σ j' f + rm L A σ j' f) / 2) := by
    refine Finset.single_le_sum (f := fun j' => ∑ f, choiceWeight (pieceCoef (dec L) σ j')
      (pieceD (dec L)) f * ((rp L A σ j' f + rm L A σ j' f) / 2)) (fun j' _ => ?_)
      (Finset.mem_univ j)
    refine Finset.sum_nonneg fun f _ => mul_nonneg ?_ ?_
    · exact Finset.prod_nonneg fun b _ => mul_nonneg (abs_nonneg _) (pieceD_nonneg (dec L) b (f b))
    · have := hr0 L A σ j' f
      linarith [this.1, this.2]
  calc |diagonalIntegral (tensorLaw (fun b => (σ b).elim (D.FS.ρ L b)
          (fun i => D.FS.κ' L b i - D.FS.κ L b i))) (atomLift m₀ p L A)|
      ≤ Real.sqrt Fp * Real.sqrt Fm := hY1
    _ ≤ (Fp + Fm) / 2 := hgm
    _ ≤ (1 + ε L) * D.Y L A * T + ∑ f, w f * ((rp L A σ j f + rm L A σ j f) / 2) := by
        rw [hsplit]
        linarith
    _ ≤ (1 + ε L) * D.Y L A * T + ∑ j', ∑ f,
          choiceWeight (pieceCoef (dec L) σ j') (pieceD (dec L)) f *
            ((rp L A σ j' f + rm L A σ j' f) / 2) := by linarith

end Final

end Sarkozy.EnvelopeInputsParam
