module

public import Sarkozy.BracketEnergy.SharpDiff
public import Sarkozy.BracketEnergy.Bundles

@[expose] public section

/-!
# The coupled expansion of a per-choice term of `lem:sharp-first` (revealed inputs)

B9's `diff_bound_of_coupled` (and `DensityFibre.envHdiffL_of_choices` etc.) asks, for every
nonempty choice `σ` and every tag `j` present in it, `|E_σ| ≤ K wt_j(σ) + r_σ`. Here `E_σ` is the
energy of the law `sharpPiece`, with any slot inputs `G` (for `envC`, `fixC` the revealed inputs).
The atom laws of `sharpPiece` are:
* at the atoms where `σ` picks `i` (outside `f`): the difference `κ'_i − κ_i`;
* on `f`: the selected increment `Q`;
* elsewhere: `Ñ₀ = μ + ∑_k κu_k`.

This file is G1/B5's coupled expansion redone for these laws (`lem:sharp-first`, proof; the
expansion before `lem:density:coupled` is applied). Each atom law is written as a combination of
**pieces** `HPiece`:
* `μ`;
* a reserved record `κu_k`;
* a whole difference `κ'_i − κ_i` of tag `j` (the sharp atom of `lem:density:coupled`);
* the positive records `κ'_i`, `κ_i` with signs `±1` for a difference of another tag;
* `Q`.

The weights are `1`, `|κu_k| sel`, `d_i`, `|κ'_i| sel`, `|κ_i| sel` and `1`; the price of `Q`
is in `K`.

* `hpieceSum_eq`: `∑_x c_x K_x = sharpPiece_𝔟` (using `Ñ₀ − μ = ∑_k κu_k`, (CP3));
* `hpiece_weight_le`: `∑_x |c_x| g_x ≤ σ_𝔟 ? (tag = j ? d : v) : 1 + (f_𝔟 ? 0 : u'_𝔟)`, the
  factor of `wt_j(σ)`;
* `multilinear_sharpPiece_expand`: the energy of `σ` is `∑_φ (∏ c) E_φ`;
* **`choice_bound_of_terms`**: from per-term bounds `|E_φ| ≤ (∏ g) K + r_φ` at the terms with
  nonzero coefficients, `|E_σ| ≤ K wt_j(σ) + ∑_φ ∏|c| r_φ`;
* **`envHdiffL_of_terms`** (and `R`, and `fixHdiffL/R_of_terms`): K2's fields 26–27 and 30–31
  from these **per-term** bounds, i.e. `lem:density:coupled` for one term with revealed inputs
  (used as hypothesis), with nonnegative remainders `r_φ`. The field's remainder is
  `r₂ = ∑_{σ ≠ ∅} ∑_j ∑_φ ∏|c| r_φ`.

Each per-term energy is that of
`(⊗ sharp differences of tag j) ⊗ (⊗ positive spectators: Q, κu, κ', κ) ⊗ μ`, the setting of
`lem:density:coupled`. B9's `abs_multilinearIntegral_coupled_le_laws` (`CoupledMulti`) bounds it
from a slot-dependent fibre input.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.DensityFibre

open Sarkozy.BracketEnergy
open Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame Sarkozy.RecordExpansion
open Sarkozy.IndexSupport Sarkozy.Functional Sarkozy.TheoremC Sarkozy.Structured
  Sarkozy.PaperFrame Sarkozy.Comparison Sarkozy.FourierArithmetic

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

section Pieces

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)

/-- The pieces of a per-choice term at an atom: `μ` (`inl none`), a reserved record `κu_k`
(`inl (some k)`), a whole difference `κ'_i − κ_i` (`inr (inl (i, none))`), a positive record
`κ'_i` or `κ_i` (`inr (inl (i, some t))`), or the selected increment `Q` (`inr (inr ())`). -/
abbrev HPiece (b : BlockAtom Bk J L) : Type :=
  Option (D.GB.Iu L b) ⊕ ((D.FS.Ib L b × Option Bool) ⊕ Unit)

/-- The law of a piece. -/
noncomputable def hpieceK (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (b : BlockAtom Bk J L) : HPiece D L b → TheoremCBlock.AtomMeasure m₀ blk p L b
  | .inl none => D.R.law p L b
  | .inl (some k) => D.GB.κu L b k
  | .inr (.inl (i, none)) => D.FS.κ' L b i - D.FS.κ L b i
  | .inr (.inl (i, some t)) => if t then D.FS.κ' L b i else D.FS.κ L b i
  | .inr (.inr _) => Qb b

/-- The coefficient of a piece in the choice `σ` at the tag `j`, with `Q` on `f`. -/
noncomputable def hpieceCoef (f : BlockAtom Bk J L → Bool) (σ : ∀ b, Option (D.FS.Ib L b))
    (j : D.FS.Tag) (b : BlockAtom Bk J L) : HPiece D L b → ℝ
  | .inl _ => if σ b = none ∧ f b = false then 1 else 0
  | .inr (.inl (i, none)) =>
      if σ b = some i ∧ D.FS.tag L b i = j ∧ f b = false then 1 else 0
  | .inr (.inl (i, some t)) =>
      if σ b = some i ∧ D.FS.tag L b i ≠ j ∧ f b = false then (if t then 1 else -1) else 0
  | .inr (.inr _) => if σ b = none ∧ f b = true then 1 else 0

/-- The price weight of a piece. -/
noncomputable def hpieceG (b : BlockAtom Bk J L) : HPiece D L b → ℝ
  | .inl none => 1
  | .inl (some k) => mass (D.GB.κu L b k) * TheoremCBlock.selectionFactor a p D.S.selPre L b
  | .inr (.inl (i, none)) => D.FS.dprice L b i
  | .inr (.inl (i, some t)) =>
      (if t then mass (D.FS.κ' L b i) else mass (D.FS.κ L b i)) *
        TheoremCBlock.selectionFactor a p D.S.selPre L b
  | .inr (.inr _) => 1

omit [DecidableEq P] in
theorem hpieceG_nonneg (b : BlockAtom Bk J L) (x : HPiece D L b) : 0 ≤ hpieceG D L b x := by
  rcases x with (_ | k) | (⟨i, _ | t⟩ | _)
  · exact zero_le_one
  · exact mul_nonneg (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.GB.κu_pos L b k).1)
      (D.selectionFactor_nonneg L b)
  · exact D.dprice_nonneg L b i
  · cases t
    · exact mul_nonneg (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1)
        (D.selectionFactor_nonneg L b)
    · exact mul_nonneg (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ'_pos L b i).1)
        (D.selectionFactor_nonneg L b)
  · exact zero_le_one

omit [DecidableEq P] in
/-- The sum over the pieces, unfolded. -/
theorem sum_hpiece {M : Type*} [AddCommMonoid M] (b : BlockAtom Bk J L) (F : HPiece D L b → M) :
    ∑ x, F x = F (.inl none) + ∑ k, F (.inl (some k)) +
      (∑ i, (F (.inr (.inl (i, none))) + (F (.inr (.inl (i, some true))) +
        F (.inr (.inl (i, some false))))) + F (.inr (.inr ()))) := by
  rw [Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [Fintype.sum_option, Fintype.sum_bool, Fintype.univ_punit, Finset.sum_singleton]

omit [DecidableEq P] in
/-- **The pieces add up to the atom law of the choice**: `∑_x c_x K_x = sharpPiece_𝔟`. -/
theorem hpieceSum_eq (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (f : BlockAtom Bk J L → Bool) (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag)
    (b : BlockAtom Bk J L) :
    ∑ x, hpieceCoef D L f σ j b x • hpieceK D L Qb b x = sharpPiece D L Qb f σ b := by
  rw [sum_hpiece]
  rcases hσ : σ b with _ | i <;> cases hf : f b
  · -- `Ñ₀ = μ + ∑ κu`
    simp only [hpieceCoef, hσ, hf, and_self, ↓reduceIte, hpieceK, one_smul, reduceCtorEq,
      and_true, false_and, zero_smul, ne_eq, Bool.false_eq_true, add_zero, sum_const_zero,
      and_false, sharpPiece, Option.elim_none]
    rw [← D.GB.N₀_sub L b]
    abel
  · simp only [hpieceCoef, hσ, hf, Bool.true_eq_false, and_false, ↓reduceIte, hpieceK, zero_smul,
      sum_const_zero, add_zero, reduceCtorEq, and_self, ne_eq, Bool.false_eq_true, one_smul,
      zero_add, sharpPiece, Option.elim_none]
  · simp only [hpieceCoef, hσ, reduceCtorEq, hf, and_true, ↓reduceIte, hpieceK, zero_smul,
      sum_const_zero, add_zero, Option.some.injEq, ite_and, ite_smul, one_smul, ne_eq, ite_not,
      Bool.false_eq_true, and_self, zero_add, sharpPiece, Option.elim_some]
    rw [Finset.sum_eq_single i (fun x _ hx => by simp [Ne.symm hx])
      (fun hi => absurd (mem_univ i) hi)]
    by_cases ht : D.FS.tag L b i = j
    · simp [ht]
    · simp [ht, sub_eq_add_neg]
      exact neg_one_smul ℝ (D.FS.κ L b i)
  · simp only [hpieceCoef, hσ, reduceCtorEq, hf, Bool.true_eq_false, and_self, ↓reduceIte,
      hpieceK, zero_smul, sum_const_zero, add_zero, Option.some.injEq, and_false, ne_eq,
      Bool.false_eq_true, and_true, sharpPiece, Option.elim_some]

omit [DecidableEq P] in
/-- **The weights of the pieces**: `∑_x |c_x| g_x` is at most the factor of `wt_j(σ)` at the atom,
`σ_𝔟 ? (tag = j ? d : v) : 1 + (f_𝔟 ? 0 : u'_𝔟)`. -/
theorem hpiece_weight_le (f : BlockAtom Bk J L → Bool) (σ : ∀ b, Option (D.FS.Ib L b))
    (j : D.FS.Tag) (b : BlockAtom Bk J L) :
    ∑ x, |hpieceCoef D L f σ j b x| * hpieceG D L b x ≤
      (σ b).elim (1 + (if f b then 0 else D.GB.uprice L b))
        (fun i => if D.FS.tag L b i = j then D.FS.dprice L b i else D.FS.vprice L b i) := by
  rw [sum_hpiece]
  rcases hσ : σ b with _ | i <;> cases hf : f b
  · simp only [hpieceCoef, hσ, hf, and_self, ↓reduceIte, abs_one, hpieceG, mul_one, one_mul,
      reduceCtorEq, and_true, false_and, abs_zero, zero_mul, ne_eq, Bool.false_eq_true, add_zero,
      sum_const_zero, and_false, Option.elim_none, add_le_add_iff_left]
    exact le_of_eq rfl
  · simp only [hpieceCoef, hσ, hf, Bool.true_eq_false, and_false, ↓reduceIte, abs_zero, hpieceG,
      mul_one, zero_mul, sum_const_zero, add_zero, reduceCtorEq, and_self, ne_eq,
      Bool.false_eq_true, abs_one, zero_add, Option.elim_none, Std.le_refl]
  · simp only [hpieceCoef, hσ, reduceCtorEq, hf, and_true, ↓reduceIte, abs_zero, hpieceG, mul_one,
      zero_mul, sum_const_zero, add_zero, Option.some.injEq, ite_and, ne_eq, ite_not,
      Bool.false_eq_true, and_self, zero_add, Option.elim_some]
    rw [Finset.sum_eq_single i (fun x _ hx => by simp [Ne.symm hx])
      (fun hi => absurd (mem_univ i) hi)]
    by_cases ht : D.FS.tag L b i = j
    · simp [ht]
    · simp [ht, TheoremCBlock.FirstStage.vprice, add_mul]
      exact le_of_eq (add_comm _ _)
  · simp only [hpieceCoef, hσ, reduceCtorEq, hf, Bool.true_eq_false, and_self, ↓reduceIte,
      abs_zero, hpieceG, mul_one, zero_mul, sum_const_zero, add_zero, Option.some.injEq, and_false,
      ne_eq, Bool.false_eq_true, and_true, Option.elim_some]
    split_ifs
    · exact D.dprice_nonneg L b i
    · exact D.vprice_nonneg L b i

end Pieces

section Expansion

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
variable (blk)

omit [DecidableEq P] in
/-- **The coupled expansion of a per-choice term**: on the cyclic coordinates, with any slot inputs,
`E_σ = ∑_φ (∏_𝔟 c_{φ_𝔟}) E_φ`, `E_φ` the energy of `⊗_𝔟 K_{φ_𝔟}`. -/
theorem multilinear_sharpPiece_expand (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j))
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (f : BlockAtom Bk J L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag)
    (G : Slot → ResidueSpace (crtModuli m₀ blk p L) → ℝ) :
    multilinearIntegral (tensorLaw (crtLaws blk h0 L (sharpPiece D L Qb f σ))) G =
      ∑ φ : (∀ b, HPiece D L b), (∏ b, hpieceCoef D L f σ j b (φ b)) *
        multilinearIntegral (tensorLaw (crtLaws blk h0 L fun b => hpieceK D L Qb b (φ b))) G := by
  have hT : crtLaws blk h0 L (sharpPiece D L Qb f σ) = fun b => ∑ x,
      hpieceCoef D L f σ j b x • pullLaw (crtAtomEquiv blk h0 L b) (hpieceK D L Qb b x) := by
    funext b
    unfold crtLaws
    rw [← hpieceSum_eq D L Qb f σ j b]
    apply LinearMap.ext
    intro F
    rw [pullLaw_apply, LinearMap.sum_apply, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, pullLaw_apply]
  rw [hT, tensorLaw_sum, multilinearIntegral_sum]
  refine Finset.sum_congr rfl fun φ _ => ?_
  rw [tensorLaw_smul]
  unfold multilinearIntegral
  rw [LinearMap.smul_apply, smul_eq_mul]
  rfl

omit [DecidableEq P] in
/-- **The per-choice bound from the per-term bounds** (`lem:sharp-first`: the summation of the
coupled expansion). If every term `φ` with nonzero coefficients satisfies
`|E_φ| ≤ (∏_𝔟 g_{φ_𝔟}) K + r_φ` (`lem:density:coupled` for one term), then
`|E_σ| ≤ K wt_j(σ) + ∑_φ ∏|c| r_φ`, with `p_𝔟 = (f_𝔟 ? 0 : u'_𝔟)` in `wt_j`. -/
theorem choice_bound_of_terms (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j))
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (f : BlockAtom Bk J L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag)
    (G : Slot → ResidueSpace (crtModuli m₀ blk p L) → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (r : (∀ b, HPiece D L b) → ℝ)
    (hterm : ∀ φ : (∀ b, HPiece D L b), (∀ b, hpieceCoef D L f σ j b (φ b) ≠ 0) →
      |multilinearIntegral (tensorLaw (crtLaws blk h0 L fun b => hpieceK D L Qb b (φ b))) G| ≤
        (∏ b, hpieceG D L b (φ b)) * K + r φ) :
    |multilinearIntegral (tensorLaw (crtLaws blk h0 L (sharpPiece D L Qb f σ))) G| ≤
      K * tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
          (fun b => if f b then 0 else D.GB.uprice L b) j σ +
        ∑ φ : (∀ b, HPiece D L b), (∏ b, |hpieceCoef D L f σ j b (φ b)|) * r φ := by
  rw [multilinear_sharpPiece_expand blk D L h0 Qb f σ j G]
  set Ef := fun φ : (∀ b, HPiece D L b) =>
    multilinearIntegral (tensorLaw (crtLaws blk h0 L fun b => hpieceK D L Qb b (φ b))) G
  have hterm' : ∀ φ : (∀ b, HPiece D L b), |(∏ b, hpieceCoef D L f σ j b (φ b)) * Ef φ| ≤
      (∏ b, |hpieceCoef D L f σ j b (φ b)|) * ((∏ b, hpieceG D L b (φ b)) * K + r φ) := by
    intro φ
    rw [abs_mul, Finset.abs_prod]
    by_cases hφ : ∀ b, hpieceCoef D L f σ j b (φ b) ≠ 0
    · exact mul_le_mul_of_nonneg_left (hterm φ hφ) (Finset.prod_nonneg fun b _ => abs_nonneg _)
    · simp only [not_forall, not_not] at hφ
      obtain ⟨b₀, hb₀⟩ := hφ
      have h0' : ∏ b, |hpieceCoef D L f σ j b (φ b)| = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ b₀) (by rw [hb₀, abs_zero])
      rw [h0', zero_mul, zero_mul]
  have hprod : ∏ b, ∑ x, |hpieceCoef D L f σ j b x| * hpieceG D L b x =
      ∑ φ : (∀ b, HPiece D L b), (∏ b, |hpieceCoef D L f σ j b (φ b)|) *
        ∏ b, hpieceG D L b (φ b) := by
    rw [Fintype.prod_sum (fun b x => |hpieceCoef D L f σ j b x| * hpieceG D L b x)]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [← Finset.prod_mul_distrib]
  have hwt : ∏ b, ∑ x, |hpieceCoef D L f σ j b x| * hpieceG D L b x ≤
      tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
        (fun b => if f b then 0 else D.GB.uprice L b) j σ := by
    unfold tagWeight
    exact Finset.prod_le_prod₀ (fun b _ => Finset.sum_nonneg fun x _ =>
      mul_nonneg (abs_nonneg _) (hpieceG_nonneg D L b x)) fun b _ => hpiece_weight_le D L f σ j b
  calc |∑ φ, (∏ b, hpieceCoef D L f σ j b (φ b)) * Ef φ|
      ≤ ∑ φ, |(∏ b, hpieceCoef D L f σ j b (φ b)) * Ef φ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ φ, (∏ b, |hpieceCoef D L f σ j b (φ b)|) * ((∏ b, hpieceG D L b (φ b)) * K + r φ) :=
        Finset.sum_le_sum fun φ _ => hterm' φ
    _ = K * ∏ b, ∑ x, |hpieceCoef D L f σ j b x| * hpieceG D L b x +
          ∑ φ, (∏ b, |hpieceCoef D L f σ j b (φ b)|) * r φ := by
        rw [hprod, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun φ _ => ?_
        ring
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left hwt hK
        linarith

omit [DecidableEq P] in
/-- The per-choice bound at every tag, with the remainder `r_σ = ∑_j ∑_φ ∏|c| r_{j,φ}` (independent
of the tag, as `diff_bound_of_coupled` needs), from nonnegative per-term remainders. -/
theorem choice_bound_all_tags (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j))
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (f : BlockAtom Bk J L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b))
    (G : Slot → ResidueSpace (crtModuli m₀ blk p L) → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (r : D.FS.Tag → (∀ b, HPiece D L b) → ℝ) (hr0 : ∀ j φ, 0 ≤ r j φ) (j : D.FS.Tag)
    (hterm : ∀ φ : (∀ b, HPiece D L b), (∀ b, hpieceCoef D L f σ j b (φ b) ≠ 0) →
      |multilinearIntegral (tensorLaw (crtLaws blk h0 L fun b => hpieceK D L Qb b (φ b))) G| ≤
        (∏ b, hpieceG D L b (φ b)) * K + r j φ) :
    |multilinearIntegral (tensorLaw (crtLaws blk h0 L (sharpPiece D L Qb f σ))) G| ≤
      K * tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
          (fun b => if f b then 0 else D.GB.uprice L b) j σ +
        ∑ j', ∑ φ : (∀ b, HPiece D L b), (∏ b, |hpieceCoef D L f σ j' b (φ b)|) * r j' φ := by
  have h1 := choice_bound_of_terms blk D L h0 Qb f σ j G hK (r j) hterm
  have h2 : ∑ φ : (∀ b, HPiece D L b), (∏ b, |hpieceCoef D L f σ j b (φ b)|) * r j φ ≤
      ∑ j', ∑ φ : (∀ b, HPiece D L b), (∏ b, |hpieceCoef D L f σ j' b (φ b)|) * r j' φ :=
    Finset.single_le_sum (f := fun j' => ∑ φ : (∀ b, HPiece D L b),
        (∏ b, |hpieceCoef D L f σ j' b (φ b)|) * r j' φ)
      (fun j' _ => Finset.sum_nonneg fun φ _ =>
        mul_nonneg (Finset.prod_nonneg fun b _ => abs_nonneg _) (hr0 j' φ)) (Finset.mem_univ j)
  linarith

end Expansion

end Sarkozy.DensityFibre
