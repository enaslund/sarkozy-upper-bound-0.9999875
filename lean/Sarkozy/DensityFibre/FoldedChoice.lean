module

public import Sarkozy.DensityFibre.SharpDiff
public import Sarkozy.EnvelopeInputsBlock.SharpFirstFolded
public import Sarkozy.DensityFibre.ChoiceExpansion
public import Sarkozy.TheoremC.WrapTerms

@[expose] public section

/-!
# The baseline per-choice bound of a sharp-first difference: folded energies (`ϑ = 1` route)

This is the paper's own proof of `lem:sharp-first` (`paper/sections/10_comparison_lemmas.tex`),
for the per-choice terms of the bracket difference `Ñ − Ñ₀`. It covers K2's fields 26–27 and
30–31. The terms carry `Q` on `f`, `Ñ₀ = μ + ∑ κu` elsewhere, and slot-dependent (revealed)
inputs. The route is the **baseline** one: `lem:record:folded-energy` at the cut `c_j`, then
`prop:record:density-structured` on each folded energy. No mixed `L^{72/θ}` moment and no
`lem:density:coupled` is used.

The pieces are those of the coupled expansion (`HPiece`, `hpieceCoef`):
* `μ`;
* a reserved record `κu_k`;
* a whole difference `κ' − κ` of tag `j`;
* the positive parts `κ'`, `κ` of a difference of another tag, with signs `±1`;
* `Q`.

The folded factors of a whole difference are its **full folded laws**
`κ(1) ∑_s π_s Diag(m_±(κ_s))`, with the shared labels `s` of its sharp decomposition integrated,
as in `lem:record:folded-energy` (`𝔈_± = ∫ π(ds) …`). This matters: by part (b) of that lemma, a
folded selected measure has uniform one-slot marginals when `κ = ∫ π(ds) κ_s` has them. A single
component `κ_s` need not, so a per-component folded energy need not be a structured energy, and
`prop:record:density-structured` would not apply to it.

Every piece is bracketed at `c_j` by its folded factors (`bpiece_bracket`):
* a whole difference by its full folded laws: the sharp bound of each component, weighted and
  summed (brackets form a convex cone);
* the positive pieces by their half-marginal diagonal laws;
* `μ` by itself ((R2)).

G1/I1's `abs_tensor_sum_le_folded` (generic in the slot inputs) then gives
`|E_σ| ≤ √(∑ w 𝔈₊) √(∑ w 𝔈₋)`.

* `bpieceSum_eq`: the pieces add up to `sharpPiece`;
* `sum_bpieceWeight_le`: `∑_x |c_x| d_x g_x ≤` the factor of `wt_j(σ)`;
* **`choice_bound_of_folded`**: assume per-choice bounds on the folded energies
  `𝔈_±(φ) ≤ (∏ g) M_± + r_±(φ)` (`prop:record:density-structured` for the folded laws, used as
  hypothesis), with `M₊ M₋ ≤ M²`. Then `|E_σ| ≤ M wt_j(σ) + r_σ`, with `r_σ` explicit (AM–GM
  with the ratio `t = √(M₋/M₊)`).

At a fixed index `ω` the main prices `M_±` carry the local density factors of the revealed inputs
(B9's finding 1). Their product is at most `M²` only after the average over `ω`. The relative
factor is therefore left in `M` and passed to the fields through `diff_bound_of_coupled_loc`.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.DensityFibre

open Sarkozy.BracketEnergy
open Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper Sarkozy.EnvelopeInputsBlock
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame Sarkozy.RecordExpansion
open Sarkozy.IndexSupport Sarkozy.Functional Sarkozy.TheoremC Sarkozy.Structured
  Sarkozy.PaperFrame Sarkozy.Comparison Sarkozy.FourierArithmetic ReflectionCut

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

section Pieces

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
  (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)

/-- The laws of the pieces at the tag `j`: as `hpieceK`, except that a whole difference of another
tag is replaced by `0` (its coefficient is `0`). -/
noncomputable def bpieceK (j : D.FS.Tag) (b : BlockAtom Bk J L) :
    HPiece D L b → TheoremCBlock.AtomMeasure m₀ blk p L b
  | .inl none => D.R.law p L b
  | .inl (some k) => D.GB.κu L b k
  | .inr (.inl (i, none)) => if D.FS.tag L b i = j then D.FS.κ' L b i - D.FS.κ L b i else 0
  | .inr (.inl (i, some t)) => if t then D.FS.κ' L b i else D.FS.κ L b i
  | .inr (.inr _) => Qb b

/-- The plus folded factors at the cut `c_j`. A whole difference carries the **full folded law**
of its sharp decomposition, `κ(1) ∑_s π_s Diag(m₊(κ_s))`, with the shared labels `s` integrated
(`lem:record:folded-energy`: `π(ds) m₊^s(dz₊)`). -/
noncomputable def bpieceLp (dec : DecFamily D L) (j : D.FS.Tag) (b : BlockAtom Bk J L) :
    HPiece D L b → TheoremCBlock.AtomMeasure m₀ blk p L b
  | .inl none => D.R.law p L b
  | .inl (some k) => (D.FS.cut j).diagonalLaw (halfMarginalPlus (D.FS.cut j) (D.GB.κu L b k))
  | .inr (.inl (i, none)) => mass (D.FS.κ L b i) • ∑ s, (dec b i).π.weight s •
      (D.FS.cut j).diagonalLaw (halfMarginalPlus (D.FS.cut j) ((dec b i).κs s))
  | .inr (.inl (i, some t)) => (D.FS.cut j).diagonalLaw
      (halfMarginalPlus (D.FS.cut j) (if t then D.FS.κ' L b i else D.FS.κ L b i))
  | .inr (.inr _) => (D.FS.cut j).diagonalLaw (halfMarginalPlus (D.FS.cut j) (Qb b))

/-- The minus folded factors at the cut `c_j`. -/
noncomputable def bpieceLm (dec : DecFamily D L) (j : D.FS.Tag) (b : BlockAtom Bk J L) :
    HPiece D L b → TheoremCBlock.AtomMeasure m₀ blk p L b
  | .inl none => D.R.law p L b
  | .inl (some k) => (D.FS.cut j).diagonalLaw (halfMarginalMinus (D.FS.cut j) (D.GB.κu L b k))
  | .inr (.inl (i, none)) => mass (D.FS.κ L b i) • ∑ s, (dec b i).π.weight s •
      (D.FS.cut j).diagonalLaw (halfMarginalMinus (D.FS.cut j) ((dec b i).κs s))
  | .inr (.inl (i, some t)) => (D.FS.cut j).diagonalLaw
      (halfMarginalMinus (D.FS.cut j) (if t then D.FS.κ' L b i else D.FS.κ L b i))
  | .inr (.inr _) => (D.FS.cut j).diagonalLaw (halfMarginalMinus (D.FS.cut j) (Qb b))

/-- The bracket constants: `dconst` for a whole difference, one otherwise. -/
noncomputable def bpieceD (b : BlockAtom Bk J L) : HPiece D L b → ℝ
  | .inr (.inl (i, none)) => D.FS.dconst L b i
  | _ => 1

/-- The prices of the folded pieces: mass times selection factor; one for `μ` and `Q` (the price
of `Q` is in the outer price `K`). -/
noncomputable def bpieceG (b : BlockAtom Bk J L) : HPiece D L b → ℝ
  | .inl none => 1
  | .inl (some k) => mass (D.GB.κu L b k) * TheoremCBlock.selectionFactor a p D.S.selPre L b
  | .inr (.inl (i, none)) => mass (D.FS.κ L b i) * TheoremCBlock.selectionFactor a p D.S.selPre L b
  | .inr (.inl (i, some t)) =>
      (if t then mass (D.FS.κ' L b i) else mass (D.FS.κ L b i)) *
        TheoremCBlock.selectionFactor a p D.S.selPre L b
  | .inr (.inr _) => 1

omit [DecidableEq P] in
theorem bpieceD_nonneg (b : BlockAtom Bk J L) (x : HPiece D L b) : 0 ≤ bpieceD D L b x := by
  rcases x with (_ | k) | (⟨i, _ | t⟩ | _)
  · exact zero_le_one
  · exact zero_le_one
  · exact D.FS.dconst_nonneg L b i
  · exact zero_le_one
  · exact zero_le_one

omit [DecidableEq P] in
theorem bpieceG_nonneg (b : BlockAtom Bk J L) (x : HPiece D L b) : 0 ≤ bpieceG D L b x := by
  rcases x with (_ | k) | (⟨i, _ | t⟩ | _)
  · exact zero_le_one
  · exact mul_nonneg (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.GB.κu_pos L b k).1)
      (D.selectionFactor_nonneg L b)
  · exact mul_nonneg (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1)
      (D.selectionFactor_nonneg L b)
  · cases t
    · exact mul_nonneg (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1)
        (D.selectionFactor_nonneg L b)
    · exact mul_nonneg (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ'_pos L b i).1)
        (D.selectionFactor_nonneg L b)
  · exact zero_le_one

omit [DecidableEq P] in
/-- `d g` of a piece is its price `g` of the coupled expansion (`d_i = κ(1) dconst sel` for a
whole difference). -/
theorem bpieceD_mul_G (b : BlockAtom Bk J L) (x : HPiece D L b) :
    bpieceD D L b x * bpieceG D L b x = hpieceG D L b x := by
  rcases x with (_ | k) | (⟨i, _ | t⟩ | _)
  · exact one_mul _
  · exact one_mul _
  · show D.FS.dconst L b i * (mass (D.FS.κ L b i) *
      TheoremCBlock.selectionFactor a p D.S.selPre L b) = D.FS.dprice L b i
    unfold TheoremCBlock.FirstStage.dprice sharpPrice
    ring
  · exact one_mul _
  · exact one_mul _

omit [DecidableEq P] in
/-- **The pieces add up to the atom law of the choice**: `∑_x c_x K_x = sharpPiece_𝔟`. -/
theorem bpieceSum_eq (f : BlockAtom Bk J L → Bool) (σ : ∀ b, Option (D.FS.Ib L b))
    (j : D.FS.Tag) (b : BlockAtom Bk J L) :
    ∑ x, hpieceCoef D L f σ j b x • bpieceK D L Qb j b x = sharpPiece D L Qb f σ b := by
  rw [← hpieceSum_eq D L Qb f σ j b]
  refine Finset.sum_congr rfl fun x _ => ?_
  rcases x with (_ | k) | (⟨i, _ | t⟩ | _)
  · rfl
  · rfl
  · by_cases ht : D.FS.tag L b i = j
    · simp only [bpieceK, ht, ↓reduceIte, hpieceK]
    · have h0 : hpieceCoef D L f σ j b (.inr (.inl (i, none))) = 0 := by
        simp [hpieceCoef, ht]
      rw [h0, zero_smul, zero_smul]
  · rfl
  · rfl

omit [DecidableEq P] in
/-- **The weights of the pieces**: `∑_x |c_x| d_x g_x` is at most the factor of `wt_j(σ)`. -/
theorem sum_bpieceWeight_le (f : BlockAtom Bk J L → Bool) (σ : ∀ b, Option (D.FS.Ib L b))
    (j : D.FS.Tag) (b : BlockAtom Bk J L) :
    ∑ x, |hpieceCoef D L f σ j b x| * bpieceD D L b x * bpieceG D L b x ≤
      (σ b).elim (1 + (if f b then 0 else D.GB.uprice L b))
        (fun i => if D.FS.tag L b i = j then D.FS.dprice L b i else D.FS.vprice L b i) := by
  have e : ∀ x, |hpieceCoef D L f σ j b x| * bpieceD D L b x * bpieceG D L b x =
      |hpieceCoef D L f σ j b x| * hpieceG D L b x := fun x => by
    rw [mul_assoc, bpieceD_mul_G]
  rw [Finset.sum_congr rfl fun x _ => e x]
  exact hpiece_weight_le D L f σ j b

theorem bracket_smul {c : ReflectionCut Slot} {X : Type} {Lw K R : ((Slot → X) → ℝ) →ₗ[ℝ] ℝ}
    (hb : c.Bracket Lw K R) {w : ℝ} (hw : 0 ≤ w) : c.Bracket (w • Lw) (w • K) (w • R) where
  left_positive := hb.left_positive.smul hw
  right_positive := hb.right_positive.smul hw
  nonneg F G := by
    have h1 := hb.nonneg F G
    change 0 ≤ w * c.form Lw F F + 2 * (w * c.form K F G) + w * c.form R G G
    nlinarith

variable (dec : DecFamily D L)

omit [DecidableEq P] in
theorem bpieceLp_positive (hQ0 : ∀ b, IsNonneg (Qb b)) (j : D.FS.Tag) (b : BlockAtom Bk J L)
    (x : HPiece D L b) : (D.FS.cut j).Positive (bpieceLp D L Qb dec j b x) := by
  rcases x with (_ | k) | (⟨i, _ | t⟩ | _)
  · exact D.law_positive (D.FS.cut_family j) L b
  · exact (D.FS.cut j).diagonalLaw_positive (halfMarginalPlus_nonneg _ (D.GB.κu_pos L b k).1)
  · refine Positive.smul (Positive.sum _ fun s _ => Positive.smul
      ((D.FS.cut j).diagonalLaw_positive (halfMarginalPlus_nonneg _ ((dec b i).prob s).1))
      ((dec b i).π.nonneg s))
      (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1)
  · cases t
    · exact (D.FS.cut j).diagonalLaw_positive (halfMarginalPlus_nonneg _ (D.FS.κ_pos L b i).1)
    · exact (D.FS.cut j).diagonalLaw_positive (halfMarginalPlus_nonneg _ (D.FS.κ'_pos L b i).1)
  · exact (D.FS.cut j).diagonalLaw_positive (halfMarginalPlus_nonneg _ (hQ0 b))

omit [DecidableEq P] in
theorem bpieceLm_positive (hQ0 : ∀ b, IsNonneg (Qb b)) (j : D.FS.Tag) (b : BlockAtom Bk J L)
    (x : HPiece D L b) : (D.FS.cut j).Positive (bpieceLm D L Qb dec j b x) := by
  rcases x with (_ | k) | (⟨i, _ | t⟩ | _)
  · exact D.law_positive (D.FS.cut_family j) L b
  · exact (D.FS.cut j).diagonalLaw_positive (halfMarginalMinus_nonneg _ (D.GB.κu_pos L b k).1)
  · refine Positive.smul (Positive.sum _ fun s _ => Positive.smul
      ((D.FS.cut j).diagonalLaw_positive (halfMarginalMinus_nonneg _ ((dec b i).prob s).1))
      ((dec b i).π.nonneg s))
      (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1)
  · cases t
    · exact (D.FS.cut j).diagonalLaw_positive (halfMarginalMinus_nonneg _ (D.FS.κ_pos L b i).1)
    · exact (D.FS.cut j).diagonalLaw_positive (halfMarginalMinus_nonneg _ (D.FS.κ'_pos L b i).1)
  · exact (D.FS.cut j).diagonalLaw_positive (halfMarginalMinus_nonneg _ (hQ0 b))

omit [DecidableEq P] in
/-- **Every piece is bracketed at the cut `c_j` by its folded factors**
(`lem:record:folded-energy`(a)). A whole difference of tag `j` is bracketed by its full folded
laws: the sharp bound of each component (`def:price`(b)), weighted by `κ(1) π_s` and summed
(brackets are a convex cone). Positive pieces are bracketed by their half-marginal diagonal laws,
and `μ` by itself ((R2)). -/
theorem bpiece_bracket (hQ0 : ∀ b, IsNonneg (Qb b)) (j : D.FS.Tag) (b : BlockAtom Bk J L)
    (x : HPiece D L b) :
    (D.FS.cut j).Bracket (bpieceD D L b x • bpieceLp D L Qb dec j b x) (bpieceK D L Qb j b x)
      (bpieceD D L b x • bpieceLm D L Qb dec j b x) := by
  rcases x with (_ | k) | (⟨i, _ | t⟩ | _)
  · exact bracket_of_positive _ (D.law_positive (D.FS.cut_family j) L b)
  · exact bracket_of_nonneg _ _ (D.GB.κu_pos L b k).1
  · by_cases ht : D.FS.tag L b i = j
    · subst ht
      simp only [bpieceD, bpieceLp, bpieceLm, bpieceK, ↓reduceIte]
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
        exact bracket_smul hbr (mul_nonneg hm ((dec b i).π.nonneg s))
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
    · simp only [bpieceD, bpieceLp, bpieceLm, bpieceK, ht, ↓reduceIte]
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
  · exact bracket_of_nonneg _ _ (hQ0 b)

end Pieces

section Choice

variable {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} {L : ℕ} (dec : DecFamily D L)
  (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
variable (blk)

omit [DecidableEq P] in
/-- **The folded factorization of a per-choice term** (`lem:record:folded-energy` at `c_j`, the
baseline proof of `lem:sharp-first`), on the cyclic coordinates with any slot inputs `G`:
`|E_σ| ≤ √(∑_φ w_φ 𝔈₊(φ)) √(∑_φ w_φ 𝔈₋(φ))`, `w = ∏ |c| d`, with nonnegative folded energies.
The folded energies are taken on the block labels, with the inputs `G ∘ crt⁻¹`. -/
theorem choice_le_folded (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j))
    (hQ0 : ∀ b, IsNonneg (Qb b)) (f : BlockAtom Bk J L → Bool) (σ : ∀ b, Option (D.FS.Ib L b))
    (j : D.FS.Tag) (G : Slot → ResidueSpace (crtModuli m₀ blk p L) → ℝ) :
    (∀ φ, 0 ≤ foldedPlus (D.FS.cut j) (bpieceLp D L Qb dec j)
      (fun v x => G v ((crtLabelEquiv blk h0 L).symm x)) φ) ∧
    (∀ φ, 0 ≤ foldedMinus (D.FS.cut j) (bpieceLm D L Qb dec j)
      (fun v x => G v ((crtLabelEquiv blk h0 L).symm x)) φ) ∧
    |multilinearIntegral (tensorLaw (crtLaws blk h0 L (sharpPiece D L Qb f σ))) G| ≤
      Real.sqrt (∑ φ, choiceWeight (hpieceCoef D L f σ j) (bpieceD D L) φ *
          foldedPlus (D.FS.cut j) (bpieceLp D L Qb dec j)
            (fun v x => G v ((crtLabelEquiv blk h0 L).symm x)) φ) *
        Real.sqrt (∑ φ, choiceWeight (hpieceCoef D L f σ j) (bpieceD D L) φ *
          foldedMinus (D.FS.cut j) (bpieceLm D L Qb dec j)
            (fun v x => G v ((crtLabelEquiv blk h0 L).symm x)) φ) := by
  have hcrt := multilinearIntegral_crt blk h0 L (sharpPiece D L Qb f σ)
    (fun v x => G v ((crtLabelEquiv blk h0 L).symm x))
  simp only [Equiv.symm_apply_apply] at hcrt
  rw [← hcrt]
  have hlaw : sharpPiece D L Qb f σ = fun b => ∑ x, hpieceCoef D L f σ j b x • bpieceK D L Qb j b
      x :=
    funext fun b => (bpieceSum_eq D L Qb f σ j b).symm
  rw [hlaw]
  exact abs_tensor_sum_le_folded (D.FS.cut j) (hpieceCoef D L f σ j) (bpieceD D L)
    (bpieceK D L Qb j) (bpieceLp D L Qb dec j) (bpieceLm D L Qb dec j) (bpieceD_nonneg D L)
    (bpieceLp_positive D L Qb dec hQ0 j) (bpieceLm_positive D L Qb dec hQ0 j)
    (bpiece_bracket D L Qb dec hQ0 j)
    (fun v x => G v ((crtLabelEquiv blk h0 L).symm x))

/-- AM–GM with a ratio: `√x √y ≤ (t x + y/t)/2` for `x, y ≥ 0`, `t > 0`. -/
theorem sqrt_mul_sqrt_le_ratio {x y t : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (ht : 0 < t) :
    Real.sqrt x * Real.sqrt y ≤ (t * x + y / t) / 2 := by
  have h1 : Real.sqrt x * Real.sqrt y = Real.sqrt (t * x) * Real.sqrt (y / t) := by
    rw [← Real.sqrt_mul hx, ← Real.sqrt_mul (mul_nonneg ht.le hx)]
    congr 1
    field_simp
  rw [h1]
  have hA := Real.sq_sqrt (mul_nonneg ht.le hx)
  have hB := Real.sq_sqrt (div_nonneg hy ht.le)
  nlinarith [sq_nonneg (Real.sqrt (t * x) - Real.sqrt (y / t))]

omit [DecidableEq P] in
/-- **The per-choice bound from the folded-energy bounds** (baseline `lem:sharp-first`): if the
folded energies of the pieces satisfy `𝔈_±(φ) ≤ (∏ g) M_± + r_±(φ)` at the choices with nonzero
coefficients (`prop:record:density-structured` for the folded laws), `t > 0` and
`t M₊ + M₋/t ≤ 2M`, `M ≥ 0`, then `|E_σ| ≤ M wt_j(σ) + (t R₊ + R₋/t)/2` with
`R_± = ∑_φ w_φ r_±(φ)`. For equal prices take `t = 1`. -/
theorem choice_bound_of_folded (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j))
    (hQ0 : ∀ b, IsNonneg (Qb b)) (f : BlockAtom Bk J L → Bool) (σ : ∀ b, Option (D.FS.Ib L b))
    (j : D.FS.Tag) (G : Slot → ResidueSpace (crtModuli m₀ blk p L) → ℝ)
    {t Mp Mm M : ℝ} (ht : 0 < t) (hM0 : 0 ≤ M) (hM : t * Mp + Mm / t ≤ 2 * M)
    (rp rm : (∀ b, HPiece D L b) → ℝ)
    (hp : ∀ φ, (∀ b, hpieceCoef D L f σ j b (φ b) ≠ 0) →
      foldedPlus (D.FS.cut j) (bpieceLp D L Qb dec j)
        (fun v x => G v ((crtLabelEquiv blk h0 L).symm x)) φ ≤
        (∏ b, bpieceG D L b (φ b)) * Mp + rp φ)
    (hm : ∀ φ, (∀ b, hpieceCoef D L f σ j b (φ b) ≠ 0) →
      foldedMinus (D.FS.cut j) (bpieceLm D L Qb dec j)
        (fun v x => G v ((crtLabelEquiv blk h0 L).symm x)) φ ≤
        (∏ b, bpieceG D L b (φ b)) * Mm + rm φ) :
    |multilinearIntegral (tensorLaw (crtLaws blk h0 L (sharpPiece D L Qb f σ))) G| ≤
      M * tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
          (fun b => if f b then 0 else D.GB.uprice L b) j σ +
        (t * ∑ φ, choiceWeight (hpieceCoef D L f σ j) (bpieceD D L) φ * rp φ +
          (∑ φ, choiceWeight (hpieceCoef D L f σ j) (bpieceD D L) φ * rm φ) / t) / 2 := by
  obtain ⟨hp0, hm0, hfold⟩ := choice_le_folded blk dec Qb h0 hQ0 f σ j G
  set a' := fun v x => G v ((crtLabelEquiv blk h0 L).symm x)
  set w := choiceWeight (hpieceCoef D L f σ j) (bpieceD D L)
  have hw : ∀ φ, 0 ≤ w φ := fun φ =>
    Finset.prod_nonneg fun b _ => mul_nonneg (abs_nonneg _) (bpieceD_nonneg D L b (φ b))
  set T := ∑ φ : (∀ b, HPiece D L b), w φ * ∏ b, bpieceG D L b (φ b)
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun φ _ =>
    mul_nonneg (hw φ) (Finset.prod_nonneg fun b _ => bpieceG_nonneg D L b (φ b))
  have hTw : T ≤ tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
      (fun b => if f b then 0 else D.GB.uprice L b) j σ := by
    have hprod : ∏ b, ∑ x, |hpieceCoef D L f σ j b x| * bpieceD D L b x * bpieceG D L b x = T := by
      rw [Fintype.prod_sum (fun b x => |hpieceCoef D L f σ j b x| * bpieceD D L b x *
        bpieceG D L b x)]
      refine Finset.sum_congr rfl fun φ _ => ?_
      simp only [w, choiceWeight]
      rw [← Finset.prod_mul_distrib]
    rw [← hprod]
    unfold tagWeight
    exact Finset.prod_le_prod₀ (fun b _ => Finset.sum_nonneg fun x _ =>
      mul_nonneg (mul_nonneg (abs_nonneg _) (bpieceD_nonneg D L b x)) (bpieceG_nonneg D L b x))
      fun b _ => sum_bpieceWeight_le D L f σ j b
  -- the weighted sums of the folded energies
  have hsum : ∀ (E' : (∀ b, HPiece D L b) → ℝ) (Mx : ℝ) (rx : (∀ b, HPiece D L b) → ℝ),
      (∀ φ, (∀ b, hpieceCoef D L f σ j b (φ b) ≠ 0) → E' φ ≤ (∏ b, bpieceG D L b (φ b)) * Mx + rx
          φ) →
      ∑ φ, w φ * E' φ ≤ T * Mx + ∑ φ, w φ * rx φ := by
    intro E' Mx rx hE
    have hpt : ∀ φ, w φ * E' φ ≤ w φ * ((∏ b, bpieceG D L b (φ b)) * Mx + rx φ) := by
      intro φ
      by_cases hφ : ∀ b, hpieceCoef D L f σ j b (φ b) ≠ 0
      · exact mul_le_mul_of_nonneg_left (hE φ hφ) (hw φ)
      · simp only [not_forall, not_not] at hφ
        obtain ⟨b₀, hb₀⟩ := hφ
        have : w φ = 0 := Finset.prod_eq_zero (Finset.mem_univ b₀) (by rw [hb₀, abs_zero, zero_mul])
        rw [this, zero_mul, zero_mul]
    calc ∑ φ, w φ * E' φ ≤ ∑ φ, w φ * ((∏ b, bpieceG D L b (φ b)) * Mx + rx φ) :=
          Finset.sum_le_sum fun φ _ => hpt φ
      _ = T * Mx + ∑ φ, w φ * rx φ := by
          simp only [T, mul_add, Finset.sum_add_distrib, Finset.sum_mul]
          congr 1
          refine Finset.sum_congr rfl fun φ _ => ?_
          ring
  have hXp := hsum _ Mp rp hp
  have hXm := hsum _ Mm rm hm
  have hXp0 : 0 ≤ ∑ φ, w φ * foldedPlus (D.FS.cut j) (bpieceLp D L Qb dec j) a' φ :=
    Finset.sum_nonneg fun φ _ => mul_nonneg (hw φ) (hp0 φ)
  have hXm0 : 0 ≤ ∑ φ, w φ * foldedMinus (D.FS.cut j) (bpieceLm D L Qb dec j) a' φ :=
    Finset.sum_nonneg fun φ _ => mul_nonneg (hw φ) (hm0 φ)
  have hgm := sqrt_mul_sqrt_le_ratio hXp0 hXm0 ht
  have hstep : (t * ∑ φ, w φ * foldedPlus (D.FS.cut j) (bpieceLp D L Qb dec j) a' φ +
        (∑ φ, w φ * foldedMinus (D.FS.cut j) (bpieceLm D L Qb dec j) a' φ) / t) / 2 ≤
      (t * (T * Mp + ∑ φ, w φ * rp φ) + (T * Mm + ∑ φ, w φ * rm φ) / t) / 2 := by
    have h1 := mul_le_mul_of_nonneg_left hXp ht.le
    have h2 := div_le_div_of_nonneg_right hXm ht.le
    linarith
  have hmain : (t * (T * Mp + ∑ φ, w φ * rp φ) + (T * Mm + ∑ φ, w φ * rm φ) / t) / 2 =
      T * ((t * Mp + Mm / t) / 2) +
        (t * ∑ φ, w φ * rp φ + (∑ φ, w φ * rm φ) / t) / 2 := by
    field_simp
    ring
  have hTM : T * ((t * Mp + Mm / t) / 2) ≤ M * tagWeight (D.FS.tag L) (D.FS.dprice L)
      (D.FS.vprice L) (fun b => if f b then 0 else D.GB.uprice L b) j σ := by
    have h1 : T * ((t * Mp + Mm / t) / 2) ≤ T * M :=
      mul_le_mul_of_nonneg_left (by linarith) hT0
    have h2 : T * M ≤ M * tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
        (fun b => if f b then 0 else D.GB.uprice L b) j σ := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left hTw hM0
    linarith
  calc _ ≤ _ := hfold
    _ ≤ _ := hgm
    _ ≤ _ := hstep
    _ = _ := hmain
    _ ≤ _ := by linarith

end Choice

end Sarkozy.DensityFibre
