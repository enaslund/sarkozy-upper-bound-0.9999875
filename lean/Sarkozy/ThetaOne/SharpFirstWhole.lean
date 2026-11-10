module

public import Sarkozy.EnvelopeInputsBlock.SharpFirstFolded
public import Sarkozy.DensityFibre.FoldedChoice

@[expose] public section






open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.ThetaOne

open Sarkozy.EnvelopeInputs Sarkozy.EnvelopeInputsBlock
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame
open Sarkozy.TheoremC Sarkozy.Comparison Sarkozy.PaperFrame Sarkozy.RecordExpansion
  Sarkozy.Structured ReflectionCut

variable {a : ℝ}

section Pieces

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)

/-- The pieces of an atom: `μ_𝔟` and the records `κa_h` of `ρ_𝔟` (`inl`); for every difference
`i`, the whole difference (`inr ⟨i, none⟩`) and its two positive parts (`inr ⟨i, some t⟩`,
`t = true` for `κ'`). -/
abbrev WPiece (b : BlockAtom Bk J L) : Type :=
  Option (D.FS.Ia L b) ⊕ (Σ _i : D.FS.Ib L b, Option Bool)

variable {D L}

/-- The coefficients of the pieces for the choice `σ` and the tag `j`. -/
noncomputable def wpieceCoef (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag)
    (b : BlockAtom Bk J L) : WPiece D L b → ℝ
  | Sum.inl o => if σ b = none then o.elim 1 (D.FS.ca L b) else 0
  | Sum.inr ⟨i, none⟩ => if σ b = some i ∧ D.FS.tag L b i = j then 1 else 0
  | Sum.inr ⟨i, some t⟩ =>
      if σ b = some i ∧ D.FS.tag L b i ≠ j then (if t then 1 else -1) else 0

/-- The laws of the pieces at the tag `j` (a whole difference of another tag is `0`; its
coefficient is `0`). -/
noncomputable def wpieceK (j : D.FS.Tag) (b : BlockAtom Bk J L) : WPiece D L b →
    TheoremCBlock.AtomMeasure m₀ blk p L b
  | Sum.inl none => D.R.law p L b
  | Sum.inl (some h) => D.FS.κa L b h
  | Sum.inr ⟨i, none⟩ => if D.FS.tag L b i = j then D.FS.κ' L b i - D.FS.κ L b i else 0
  | Sum.inr ⟨i, some t⟩ => if t then D.FS.κ' L b i else D.FS.κ L b i

variable (dec : DecFamily D L)

/-- The plus folded factors at the cut `c_j`. A whole difference carries the **full folded law**
`κ(1) ∑_s π_s Diag(m₊(κ_s))` of its sharp decomposition (`lem:record:folded-energy`). -/
noncomputable def wpieceLp (j : D.FS.Tag) (b : BlockAtom Bk J L) : WPiece D L b →
    TheoremCBlock.AtomMeasure m₀ blk p L b
  | Sum.inl none => D.R.law p L b
  | Sum.inl (some h) => (D.FS.cut j).diagonalLaw (halfMarginalPlus (D.FS.cut j) (D.FS.κa L b h))
  | Sum.inr ⟨i, none⟩ => mass (D.FS.κ L b i) • ∑ s, (dec b i).π.weight s •
      (D.FS.cut j).diagonalLaw (halfMarginalPlus (D.FS.cut j) ((dec b i).κs s))
  | Sum.inr ⟨i, some t⟩ => (D.FS.cut j).diagonalLaw
      (halfMarginalPlus (D.FS.cut j) (if t then D.FS.κ' L b i else D.FS.κ L b i))

/-- The minus folded factors at the cut `c_j`. -/
noncomputable def wpieceLm (j : D.FS.Tag) (b : BlockAtom Bk J L) : WPiece D L b →
    TheoremCBlock.AtomMeasure m₀ blk p L b
  | Sum.inl none => D.R.law p L b
  | Sum.inl (some h) => (D.FS.cut j).diagonalLaw (halfMarginalMinus (D.FS.cut j) (D.FS.κa L b h))
  | Sum.inr ⟨i, none⟩ => mass (D.FS.κ L b i) • ∑ s, (dec b i).π.weight s •
      (D.FS.cut j).diagonalLaw (halfMarginalMinus (D.FS.cut j) ((dec b i).κs s))
  | Sum.inr ⟨i, some t⟩ => (D.FS.cut j).diagonalLaw
      (halfMarginalMinus (D.FS.cut j) (if t then D.FS.κ' L b i else D.FS.κ L b i))

variable (D L) in
/-- The bracket constants: the sharp constant for a whole difference, one otherwise. -/
noncomputable def wpieceD (b : BlockAtom Bk J L) : WPiece D L b → ℝ
  | Sum.inl _ => 1
  | Sum.inr ⟨i, none⟩ => D.FS.dconst L b i
  | Sum.inr ⟨_, some _⟩ => 1

variable (D L) in
/-- The prices of the folded pieces: mass times selection factor (one for `μ_𝔟`). -/
noncomputable def wpieceG (b : BlockAtom Bk J L) : WPiece D L b → ℝ
  | Sum.inl none => 1
  | Sum.inl (some h) => mass (D.FS.κa L b h) * TheoremCBlock.selectionFactor a p D.S.selPre L b
  | Sum.inr ⟨i, none⟩ => mass (D.FS.κ L b i) * TheoremCBlock.selectionFactor a p D.S.selPre L b
  | Sum.inr ⟨i, some t⟩ =>
      (if t then mass (D.FS.κ' L b i) else mass (D.FS.κ L b i)) *
        TheoremCBlock.selectionFactor a p D.S.selPre L b

omit [DecidableEq P] in
/-- **The pieces add up to the factor of the term**: `∑_x c_x K_x = σ_𝔟 ? (κ' − κ) : ρ_𝔟`. -/
theorem wpieceSum_eq (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) (b : BlockAtom Bk J L) :
    ∑ x, wpieceCoef σ j b x • wpieceK j b x =
      (σ b).elim (D.FS.ρ L b) (fun i => D.FS.κ' L b i - D.FS.κ L b i) := by
  rw [Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_sigma]
  rcases hσ : σ b with _ | i₀
  · have hinr : ∀ i y, wpieceCoef σ j b (Sum.inr ⟨i, y⟩) = 0 := by
      intro i y
      rcases y with _ | t <;> simp [wpieceCoef, hσ]
    simp only [hinr, zero_smul, Finset.sum_const_zero, add_zero]
    simp only [wpieceCoef, wpieceK, hσ, ↓reduceIte, Option.elim, one_smul]
    have h := D.FS.ρ_sub L b
    rw [sub_eq_iff_eq_add'] at h
    exact h.symm
  · have hinl : ∀ o, wpieceCoef σ j b (Sum.inl o) = 0 := by
      intro o
      simp [wpieceCoef, hσ]
    have hinr : ∀ i, i ≠ i₀ → ∀ y, wpieceCoef σ j b (Sum.inr ⟨i, y⟩) = 0 := by
      intro i hi y
      rcases y with _ | t <;> simp [wpieceCoef, hσ, Ne.symm hi]
    simp only [hinl, zero_smul, Finset.sum_const_zero, zero_add]
    rw [Finset.sum_eq_single i₀ (fun i _ hi => by simp [hinr i hi]) (by simp)]
    simp only [Option.elim]
    rw [Fintype.sum_option, Fintype.sum_bool]
    by_cases ht : D.FS.tag L b i₀ = j
    · have hb : ∀ t : Bool, wpieceCoef σ j b (Sum.inr ⟨i₀, some t⟩) = 0 := by
        intro t
        simp [wpieceCoef, hσ, ht]
      simp only [hb, zero_smul, add_zero]
      simp only [wpieceCoef, wpieceK, hσ, ht, and_self, ↓reduceIte, one_smul]
    · have hn : wpieceCoef σ j b (Sum.inr ⟨i₀, none⟩) = 0 := by
        simp [wpieceCoef, hσ, ht]
      have ht1 : wpieceCoef σ j b (Sum.inr ⟨i₀, some true⟩) = 1 := by
        simp [wpieceCoef, hσ, ht]
      have ht2 : wpieceCoef σ j b (Sum.inr ⟨i₀, some false⟩) = -1 := by
        simp [wpieceCoef, hσ, ht]
      have hk1 : wpieceK j b (Sum.inr ⟨i₀, some true⟩) = D.FS.κ' L b i₀ := rfl
      have hk2 : wpieceK j b (Sum.inr ⟨i₀, some false⟩) = D.FS.κ L b i₀ := rfl
      rw [hn, ht1, ht2, hk1, hk2, zero_smul, zero_add, one_smul]
      apply LinearMap.ext
      intro F
      simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul]
      ring

omit [DecidableEq P] in
theorem wpieceD_nonneg (b : BlockAtom Bk J L) (x : WPiece D L b) : 0 ≤ wpieceD D L b x := by
  rcases x with _ | ⟨i, _ | t⟩
  · exact zero_le_one
  · exact D.FS.dconst_nonneg L b i
  · exact zero_le_one

omit [DecidableEq P] in
theorem wpieceLp_positive (j : D.FS.Tag) (b : BlockAtom Bk J L) (x : WPiece D L b) :
    (D.FS.cut j).Positive (wpieceLp dec j b x) := by
  rcases x with (_ | hh) | ⟨i, _ | t⟩
  · exact D.law_positive (D.FS.cut_family j) L b
  · exact (D.FS.cut j).diagonalLaw_positive
      (halfMarginalPlus_nonneg _ (D.FS.κa_pos L b hh).1)
  · exact Positive.smul (Positive.sum _ fun s _ => Positive.smul
      ((D.FS.cut j).diagonalLaw_positive (halfMarginalPlus_nonneg _ ((dec b i).prob s).1))
      ((dec b i).π.nonneg s))
      (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1)
  · cases t
    · exact (D.FS.cut j).diagonalLaw_positive (halfMarginalPlus_nonneg _ (D.FS.κ_pos L b i).1)
    · exact (D.FS.cut j).diagonalLaw_positive (halfMarginalPlus_nonneg _ (D.FS.κ'_pos L b i).1)

omit [DecidableEq P] in
theorem wpieceLm_positive (j : D.FS.Tag) (b : BlockAtom Bk J L) (x : WPiece D L b) :
    (D.FS.cut j).Positive (wpieceLm dec j b x) := by
  rcases x with (_ | hh) | ⟨i, _ | t⟩
  · exact D.law_positive (D.FS.cut_family j) L b
  · exact (D.FS.cut j).diagonalLaw_positive
      (halfMarginalMinus_nonneg _ (D.FS.κa_pos L b hh).1)
  · exact Positive.smul (Positive.sum _ fun s _ => Positive.smul
      ((D.FS.cut j).diagonalLaw_positive (halfMarginalMinus_nonneg _ ((dec b i).prob s).1))
      ((dec b i).π.nonneg s))
      (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1)
  · cases t
    · exact (D.FS.cut j).diagonalLaw_positive (halfMarginalMinus_nonneg _ (D.FS.κ_pos L b i).1)
    · exact (D.FS.cut j).diagonalLaw_positive (halfMarginalMinus_nonneg _ (D.FS.κ'_pos L b i).1)

omit [DecidableEq P] in
/-- **Every piece is bracketed at the cut `c_j` by its folded factors**
(`lem:record:folded-energy`(a)). A whole difference of tag `j` is bracketed by its full folded
laws: the sharp bound of each component (`def:price`(b)), weighted by `κ(1) π_s` and summed
(brackets are a convex cone; DC2's `bpiece_bracket`). Positive pieces are bracketed by their
half-marginal diagonal laws, and `μ` by itself ((R2)). -/
theorem wpiece_bracket (j : D.FS.Tag) (b : BlockAtom Bk J L) (x : WPiece D L b) :
    (D.FS.cut j).Bracket (wpieceD D L b x • wpieceLp dec j b x) (wpieceK j b x)
      (wpieceD D L b x • wpieceLm dec j b x) := by
  rcases x with (_ | hh) | ⟨i, _ | t⟩
  · exact bracket_of_positive _ (D.law_positive (D.FS.cut_family j) L b)
  · exact bracket_of_nonneg _ _ (D.FS.κa_pos L b hh).1
  · by_cases ht : D.FS.tag L b i = j
    · subst ht
      simp only [wpieceD, wpieceLp, wpieceLm, wpieceK, ↓reduceIte]
      have hm := TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1
      have hs : ∀ s ∈ (univ : Finset (dec b i).S), (D.FS.cut (D.FS.tag L b i)).Bracket
          ((mass (D.FS.κ L b i) * (dec b i).π.weight s) • (D.FS.dconst L b i •
            (D.FS.cut (D.FS.tag L b i)).diagonalLaw
              (halfMarginalPlus (D.FS.cut (D.FS.tag L b i)) ((dec b i).κs s))))
          ((mass (D.FS.κ L b i) * (dec b i).π.weight s) • (dec b i).Ks s)
          ((mass (D.FS.κ L b i) * (dec b i).π.weight s) • (D.FS.dconst L b i •
            (D.FS.cut (D.FS.tag L b i)).diagonalLaw
              (halfMarginalMinus (D.FS.cut (D.FS.tag L b i)) ((dec b i).κs s)))) := by
        intro s _
        have hsh := (dec b i).sharp s
        have hbr := (sharp_iff_bracket _ _ (halfMarginalPlus_nonneg _ ((dec b i).prob s).1)
          (halfMarginalMinus_nonneg _ ((dec b i).prob s).1) (D.FS.dconst_nonneg L b i)).mp hsh
        exact DensityFibre.bracket_smul hbr (mul_nonneg hm ((dec b i).π.nonneg s))
      have hsum := bracket_sum _ hs
      have e1 : ∀ (M : (dec b i).S → TheoremCBlock.AtomMeasure m₀ blk p L b),
          ∑ s, (mass (D.FS.κ L b i) * (dec b i).π.weight s) • (D.FS.dconst L b i • M s) =
            D.FS.dconst L b i • (mass (D.FS.κ L b i) • ∑ s, (dec b i).π.weight s • M s) := by
        intro M
        rw [Finset.smul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [smul_smul]
        congr 1
        ring
      have e2 : ∑ s, (mass (D.FS.κ L b i) * (dec b i).π.weight s) • (dec b i).Ks s =
          D.FS.κ' L b i - D.FS.κ L b i := by
        refine Eq.trans ?_ (dec b i).hζ.symm
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [smul_smul]
      rw [e1, e1, e2] at hsum
      exact hsum
    · simp only [wpieceD, wpieceLp, wpieceLm, wpieceK, ht, ↓reduceIte]
      have hm := TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1
      have hpos : ∀ (mh : (dec b i).S → ((D.FS.cut j).Half → BlockLabel m₀ blk p L b) → ℝ),
          (∀ s x, 0 ≤ mh s x) → (D.FS.cut j).Positive (D.FS.dconst L b i •
            (mass (D.FS.κ L b i) • ∑ s, (dec b i).π.weight s • (D.FS.cut j).diagonalLaw (mh s))) :=
        fun mh hmh => Positive.smul (Positive.smul (Positive.sum _ fun s _ => Positive.smul
          ((D.FS.cut j).diagonalLaw_positive (hmh s)) ((dec b i).π.nonneg s)) hm)
          (D.FS.dconst_nonneg L b i)
      have hp := hpos _ fun s => halfMarginalPlus_nonneg (D.FS.cut j) ((dec b i).prob s).1
      have hmn := hpos _ fun s => halfMarginalMinus_nonneg (D.FS.cut j) ((dec b i).prob s).1
      refine ⟨hp, hmn, fun F G => ?_⟩
      have h1 := hp.nonneg F
      have h2 := hmn.nonneg G
      have h0 : (D.FS.cut j).form (0 : TheoremCBlock.AtomMeasure m₀ blk p L b) F G = 0 := rfl
      rw [h0]
      linarith
  · cases t
    · exact bracket_of_nonneg _ _ (D.FS.κ_pos L b i).1
    · exact bracket_of_nonneg _ _ (D.FS.κ'_pos L b i).1

omit [DecidableEq P] in
/-- **The folded factorization of a sharp-first term** (`lem:sharp-first` with
`lem:record:folded-energy` at the cut `c_j`), with whole differences: `|Y_σ| ≤ √𝔈₊ √𝔈₋` with
the weighted folded energies of the choices of pieces, which are nonnegative. -/
theorem sharp_term_le_wfolded (A : Finset ℤ) (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) :
    (∀ f, 0 ≤ foldedPlus (D.FS.cut j) (wpieceLp dec j) (fun _ => blockLift m₀ blk p L A) f) ∧
    (∀ f, 0 ≤ foldedMinus (D.FS.cut j) (wpieceLm dec j) (fun _ => blockLift m₀ blk p L A) f) ∧
    |diagonalIntegral (tensorLaw (fun b => (σ b).elim (D.FS.ρ L b)
        (fun i => D.FS.κ' L b i - D.FS.κ L b i))) (blockLift m₀ blk p L A)| ≤
      Real.sqrt (∑ f, choiceWeight (wpieceCoef σ j) (wpieceD D L) f *
          foldedPlus (D.FS.cut j) (wpieceLp dec j) (fun _ => blockLift m₀ blk p L A) f) *
        Real.sqrt (∑ f, choiceWeight (wpieceCoef σ j) (wpieceD D L) f *
          foldedMinus (D.FS.cut j) (wpieceLm dec j) (fun _ => blockLift m₀ blk p L A) f) := by
  have hlaw : (fun b => (σ b).elim (D.FS.ρ L b) (fun i => D.FS.κ' L b i - D.FS.κ L b i)) =
      fun b => ∑ x, wpieceCoef σ j b x • wpieceK j b x :=
    funext fun b => (wpieceSum_eq σ j b).symm
  rw [hlaw]
  exact abs_tensor_sum_le_folded (D.FS.cut j) (wpieceCoef σ j) (wpieceD D L) (wpieceK j)
    (wpieceLp dec j) (wpieceLm dec j) wpieceD_nonneg (wpieceLp_positive dec j)
    (wpieceLm_positive dec j) (wpiece_bracket dec j) (fun _ => blockLift m₀ blk p L A)

omit [DecidableEq P] in
/-- **The price bookkeeping of `lem:sharp-first`**: at every atom the weighted prices
`∑_x |c_x| d_x g_x` of the pieces are the factor of `tagWeight`: `d_{𝔟,i}` for a difference of
tag `j`, `v_{𝔟,i}` for a difference of another tag, `1 + p_𝔟` at an unchosen atom. -/
theorem sum_wpieceWeight (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) (b : BlockAtom Bk J L) :
    ∑ x, |wpieceCoef σ j b x| * wpieceD D L b x * wpieceG D L b x =
      (σ b).elim (1 + D.FS.pvar L b)
        (fun i => if D.FS.tag L b i = j then D.FS.dprice L b i else D.FS.vprice L b i) := by
  rw [Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_sigma]
  rcases hσ : σ b with _ | i₀
  · have hinr : ∀ i y, wpieceCoef σ j b (Sum.inr ⟨i, y⟩) = 0 := by
      intro i y
      rcases y with _ | t <;> simp [wpieceCoef, hσ]
    simp only [hinr, abs_zero, zero_mul, Finset.sum_const_zero, add_zero]
    simp only [wpieceCoef, wpieceD, wpieceG, hσ, ↓reduceIte, Option.elim, abs_one, mul_one]
    unfold TheoremCBlock.FirstStage.pvar
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · have hinl : ∀ o, wpieceCoef σ j b (Sum.inl o) = 0 := by
      intro o
      simp [wpieceCoef, hσ]
    have hinr : ∀ i, i ≠ i₀ → ∀ y, wpieceCoef σ j b (Sum.inr ⟨i, y⟩) = 0 := by
      intro i hi y
      rcases y with _ | t <;> simp [wpieceCoef, hσ, Ne.symm hi]
    simp only [hinl, abs_zero, zero_mul, Finset.sum_const_zero, zero_add]
    rw [Finset.sum_eq_single i₀ (fun i _ hi => by simp [hinr i hi]) (by simp)]
    simp only [Option.elim]
    rw [Fintype.sum_option, Fintype.sum_bool]
    by_cases ht : D.FS.tag L b i₀ = j
    · have hb : ∀ t : Bool, wpieceCoef σ j b (Sum.inr ⟨i₀, some t⟩) = 0 := by
        intro t
        simp [wpieceCoef, hσ, ht]
      simp only [hb, abs_zero, zero_mul, add_zero]
      simp only [wpieceCoef, wpieceD, wpieceG, hσ, ht, and_self, ↓reduceIte, abs_one, one_mul]
      unfold TheoremCBlock.FirstStage.dprice sharpPrice
      ring
    · have hn : wpieceCoef σ j b (Sum.inr ⟨i₀, none⟩) = 0 := by
        simp [wpieceCoef, hσ, ht]
      have ht1 : wpieceCoef σ j b (Sum.inr ⟨i₀, some true⟩) = 1 := by
        simp [wpieceCoef, hσ, ht]
      have ht2 : wpieceCoef σ j b (Sum.inr ⟨i₀, some false⟩) = -1 := by
        simp [wpieceCoef, hσ, ht]
      rw [hn, ht1, ht2]
      simp only [wpieceD, wpieceG, ht, ↓reduceIte, abs_zero, abs_one, abs_neg, zero_mul,
        zero_add, one_mul, Bool.false_eq_true]
      unfold TheoremCBlock.FirstStage.vprice
      ring

end Pieces

section Final

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

omit [DecidableEq P] in
/-- **`SharpFirstTerms` from the folded-energy bounds of the whole pieces** (`lem:sharp-first`,
`lem:record:folded-energy`; the baseline route at `ϑ = 1`). Fix sharp decompositions `dec` of
the differences (`EnvelopeInputsBlock.nonempty_decFamily`). Suppose that at every least
counterexample, for every nonempty choice `σ`, every tag `j` present and every choice `f` of
pieces, the two folded energies satisfy `𝔈_±(f) ≤ (∏_𝔟 g_𝔟(f_𝔟)) (1 + ε_L) Y + r_±(f)`
(`hfold`: `prop:record:density-structured` for the folded laws, which are tensor products of the
`μ_𝔟`, of the diagonal laws of half marginals of the positive records `κa_h`, `κ`, `κ'`, and of the
full folded laws `κ(1) ∑_s π_s Diag(m_±(κ_s))` of whole differences), with nonnegative remainders
whose weighted sum is density-linear (`hrem`). Then `D.SharpFirstTerms` holds. The expansion,
the brackets, the geometric mean and the price bookkeeping are proved here. -/
theorem sharpFirstTerms_of_wholeFolded (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (dec : ∀ L, DecFamily D L)
    (ε : ℕ → ℝ) (hε0 : ∀ L, 0 ≤ ε L) (hεt : Tendsto ε atTop (𝓝 0)) {c : ℝ} (hc : 0 ≤ c)
    (rp rm : ∀ L, Finset ℤ → (∀ b, Option (D.FS.Ib L b)) → D.FS.Tag →
      (∀ b, WPiece D L b) → ℝ)
    (hr0 : ∀ L A σ j f, 0 ≤ rp L A σ j f ∧ 0 ≤ rm L A σ j f)
    (hfold : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => ∀ σ : (∀ b, Option (D.FS.Ib L b)),
      σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec (D.FS.tag L) σ j → ∀ f,
      foldedPlus (D.FS.cut j) (wpieceLp (dec L) j) (fun _ => blockLift m₀ blk p L A) f ≤
          (∏ b, wpieceG D L b (f b)) * ((1 + ε L) * D.Y L A) + rp L A σ j f ∧
        foldedMinus (D.FS.cut j) (wpieceLm (dec L) j) (fun _ => blockLift m₀ blk p L A) f ≤
          (∏ b, wpieceG D L b (f b)) * ((1 + ε L) * D.Y L A) + rm L A σ j f))
    (hrem : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        ∑ j, ∑ f, choiceWeight (wpieceCoef σ j) (wpieceD D L) f *
          ((rp L A σ j f + rm L A σ j f) / 2) ≤ remainder c L A)) :
    D.SharpFirstTerms := by
  refine ⟨ε, hε0, hεt, c, hc, fun L A σ => ∑ j, ∑ f,
    choiceWeight (wpieceCoef σ j) (wpieceD D L) f *
      ((rp L A σ j f + rm L A σ j f) / 2), ?_, hrem⟩
  filter_upwards [hfold] with L hL
  intro C hC hk A hA hY σ hσ j hj
  obtain ⟨hFp0, hFm0, hY1⟩ := sharp_term_le_wfolded (dec L) A σ j
  have hw : ∀ f, 0 ≤ choiceWeight (wpieceCoef σ j) (wpieceD D L) f := fun f =>
    Finset.prod_nonneg fun b _ => mul_nonneg (abs_nonneg _) (wpieceD_nonneg b (f b))
  have htw : ∏ b, ∑ x, |wpieceCoef σ j b x| * wpieceD D L b x * wpieceG D L b x =
      tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (D.FS.pvar L) j σ := by
    unfold tagWeight
    exact Finset.prod_congr rfl fun b _ => sum_wpieceWeight σ j b
  have hFp := weighted_folded_le (wpieceCoef σ j) (wpieceD D L) (wpieceG D L)
    wpieceD_nonneg _ (rp L A σ j) ((1 + ε L) * D.Y L A)
    (fun f => (hL C hC hk A hA hY σ hσ j hj f).1)
  have hFm := weighted_folded_le (wpieceCoef σ j) (wpieceD D L) (wpieceG D L)
    wpieceD_nonneg _ (rm L A σ j) ((1 + ε L) * D.Y L A)
    (fun f => (hL C hC hk A hA hY σ hσ j hj f).2)
  rw [htw] at hFp hFm
  set w := choiceWeight (wpieceCoef σ j) (wpieceD D L)
  set Fp := ∑ f, w f * foldedPlus (D.FS.cut j) (wpieceLp (dec L) j)
      (fun _ => blockLift m₀ blk p L A) f
  set Fm := ∑ f, w f * foldedMinus (D.FS.cut j) (wpieceLm (dec L) j)
      (fun _ => blockLift m₀ blk p L A) f
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
      ∑ j', ∑ f, choiceWeight (wpieceCoef σ j') (wpieceD D L) f *
        ((rp L A σ j' f + rm L A σ j' f) / 2) := by
    refine Finset.single_le_sum (f := fun j' => ∑ f, choiceWeight (wpieceCoef σ j')
      (wpieceD D L) f * ((rp L A σ j' f + rm L A σ j' f) / 2)) (fun j' _ => ?_)
      (Finset.mem_univ j)
    refine Finset.sum_nonneg fun f _ => mul_nonneg ?_ ?_
    · exact Finset.prod_nonneg fun b _ => mul_nonneg (abs_nonneg _) (wpieceD_nonneg b (f b))
    · have := hr0 L A σ j' f
      linarith [this.1, this.2]
  calc |diagonalIntegral (tensorLaw (fun b => (σ b).elim (D.FS.ρ L b)
          (fun i => D.FS.κ' L b i - D.FS.κ L b i))) (blockLift m₀ blk p L A)|
      ≤ Real.sqrt Fp * Real.sqrt Fm := hY1
    _ ≤ (Fp + Fm) / 2 := hgm
    _ ≤ (1 + ε L) * D.Y L A * T + ∑ f, w f * ((rp L A σ j f + rm L A σ j f) / 2) := by
        rw [hsplit]
        linarith
    _ ≤ (1 + ε L) * D.Y L A * T + ∑ j', ∑ f,
          choiceWeight (wpieceCoef σ j') (wpieceD D L) f *
            ((rp L A σ j' f + rm L A σ j' f) / 2) := by linarith

end Final

end Sarkozy.ThetaOne
