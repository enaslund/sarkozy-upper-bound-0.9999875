module

public import Sarkozy.EnvelopeInputs.SharpFirstCoupled
public import Sarkozy.EnvelopeInputsBlock.SharpFirstUniform

@[expose] public section




open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.EnvelopeInputsBlock

open Sarkozy.EnvelopeInputs
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame

variable {a : ℝ}

open Sarkozy.TheoremC Sarkozy.Comparison Sarkozy.PaperFrame Sarkozy.RecordExpansion
  Sarkozy.Structured ReflectionCut

section Pieces

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)

/-- The coupled pieces of an atom: `μ_𝔟` and the records `κa_h` of `ρ_𝔟` (`inl`); for every
difference `i`, the whole difference `κ' − κ` (`inr (i, none)`) and its two positive parts
(`inr (i, some t)`, `t = true` for `κ'`). -/
abbrev CPiece (b : BlockAtom Bk J L) : Type :=
  Option (D.FS.Ia L b) ⊕ (D.FS.Ib L b × Option Bool)

/-- The coefficients of the coupled pieces for the choice `σ` and the tag `j`: the whole
difference at a chosen difference of tag `j`, its two parts at one of another tag. -/
noncomputable def cpieceCoef (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) (b : BlockAtom Bk J L) :
    CPiece D L b → ℝ
  | Sum.inl o => if σ b = none then o.elim 1 (D.FS.ca L b) else 0
  | Sum.inr (i, none) => if σ b = some i ∧ D.FS.tag L b i = j then 1 else 0
  | Sum.inr (i, some t) =>
      if σ b = some i ∧ D.FS.tag L b i ≠ j then (if t then 1 else -1) else 0

/-- The coupled pieces. -/
noncomputable def cpieceK (b : BlockAtom Bk J L) : CPiece D L b →
    TheoremCBlock.AtomMeasure m₀ blk p L b
  | Sum.inl none => D.R.law p L b
  | Sum.inl (some h) => D.FS.κa L b h
  | Sum.inr (i, none) => D.FS.κ' L b i - D.FS.κ L b i
  | Sum.inr (i, some t) => if t then D.FS.κ' L b i else D.FS.κ L b i

/-- The prices of the coupled pieces: one for `μ_𝔟`, the sharp price `d_{𝔟,i}` for the whole
difference, mass times selection factor for a positive spectator. -/
noncomputable def cpieceG (b : BlockAtom Bk J L) : CPiece D L b → ℝ
  | Sum.inl none => 1
  | Sum.inl (some h) => mass (D.FS.κa L b h) * TheoremCBlock.selectionFactor a p D.S.selPre L b
  | Sum.inr (i, none) => D.FS.dprice L b i
  | Sum.inr (i, some t) =>
      (if t then mass (D.FS.κ' L b i) else mass
          (D.FS.κ L b i)) * TheoremCBlock.selectionFactor a p D.S.selPre L b

omit [DecidableEq P] in
/-- **The coupled pieces add up to the factor of the term**:
`∑_x c_x K_x = σ_𝔟 ? δ_{𝔟,σ_𝔟} : ρ_𝔟`. -/
theorem cpieceSum_eq (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) (b : BlockAtom Bk J L) :
    ∑ x, cpieceCoef D L σ j b x • cpieceK D L b x =
      (σ b).elim (D.FS.ρ L b) (fun i => D.FS.κ' L b i - D.FS.κ L b i) := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  rcases hσ : σ b with _ | i₀
  · have hinr : ∀ i y, cpieceCoef D L σ j b (Sum.inr (i, y)) = 0 := by
      intro i y
      rcases y with _ | t <;> simp [cpieceCoef, hσ]
    simp only [hinr, zero_smul, Finset.sum_const_zero, add_zero]
    rw [Fintype.sum_option]
    simp only [cpieceCoef, cpieceK, hσ, ↓reduceIte, Option.elim, one_smul]
    have h := D.FS.ρ_sub L b
    rw [sub_eq_iff_eq_add'] at h
    exact h.symm
  · have hinl : ∀ o, cpieceCoef D L σ j b (Sum.inl o) = 0 := by
      intro o
      simp [cpieceCoef, hσ]
    have hinr : ∀ i, i ≠ i₀ → ∀ y, cpieceCoef D L σ j b (Sum.inr (i, y)) = 0 := by
      intro i hi y
      rcases y with _ | t <;> simp [cpieceCoef, hσ, Ne.symm hi]
    simp only [hinl, zero_smul, Finset.sum_const_zero, zero_add]
    rw [Finset.sum_eq_single i₀ (fun i _ hi => by simp [hinr i hi]) (by simp)]
    simp only [Option.elim]
    rw [Fintype.sum_option, Fintype.sum_bool]
    by_cases ht : D.FS.tag L b i₀ = j
    · have hb : ∀ t : Bool, cpieceCoef D L σ j b (Sum.inr (i₀, some t)) = 0 := by
        intro t
        simp [cpieceCoef, hσ, ht]
      have h1 : cpieceCoef D L σ j b (Sum.inr (i₀, none)) = 1 := by
        simp [cpieceCoef, hσ, ht]
      rw [hb, hb, h1]
      simp only [zero_smul, add_zero, one_smul]
      rfl
    · have h0 : cpieceCoef D L σ j b (Sum.inr (i₀, none)) = 0 := by
        simp [cpieceCoef, hσ, ht]
      have ht1 : cpieceCoef D L σ j b (Sum.inr (i₀, some true)) = 1 := by
        simp [cpieceCoef, hσ, ht]
      have ht2 : cpieceCoef D L σ j b (Sum.inr (i₀, some false)) = -1 := by
        simp [cpieceCoef, hσ, ht]
      have hk1 : cpieceK D L b (Sum.inr (i₀, some true)) = D.FS.κ' L b i₀ := rfl
      have hk2 : cpieceK D L b (Sum.inr (i₀, some false)) = D.FS.κ L b i₀ := rfl
      rw [h0, ht1, ht2, hk1, hk2, zero_smul, zero_add, one_smul]
      apply LinearMap.ext
      intro F
      simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul]
      ring

omit [DecidableEq P] in
/-- **The price bookkeeping of the coupled expansion**: at every atom `∑_x |c_x| g_x` is the
factor of `tagWeight`: `d_{𝔟,i}` for a difference of tag `j`, `v_{𝔟,i}` for a difference of
another tag, `1 + p_𝔟` at an unchosen atom. -/
theorem csum_pieceWeight (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) (b : BlockAtom Bk J L) :
    ∑ x, |cpieceCoef D L σ j b x| * cpieceG D L b x =
      (σ b).elim (1 + D.FS.pvar L b)
        (fun i => if D.FS.tag L b i = j then D.FS.dprice L b i else D.FS.vprice L b i) := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  rcases hσ : σ b with _ | i₀
  · have hinr : ∀ i y, cpieceCoef D L σ j b (Sum.inr (i, y)) = 0 := by
      intro i y
      rcases y with _ | t <;> simp [cpieceCoef, hσ]
    simp only [hinr, abs_zero, zero_mul, Finset.sum_const_zero, add_zero]
    rw [Fintype.sum_option]
    simp only [cpieceCoef, cpieceG, hσ, ↓reduceIte, Option.elim, abs_one, one_mul]
    unfold TheoremCBlock.FirstStage.pvar
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · have hinl : ∀ o, cpieceCoef D L σ j b (Sum.inl o) = 0 := by
      intro o
      simp [cpieceCoef, hσ]
    have hinr : ∀ i, i ≠ i₀ → ∀ y, cpieceCoef D L σ j b (Sum.inr (i, y)) = 0 := by
      intro i hi y
      rcases y with _ | t <;> simp [cpieceCoef, hσ, Ne.symm hi]
    simp only [hinl, abs_zero, zero_mul, Finset.sum_const_zero, zero_add]
    rw [Finset.sum_eq_single i₀ (fun i _ hi => by simp [hinr i hi]) (by simp)]
    simp only [Option.elim]
    rw [Fintype.sum_option, Fintype.sum_bool]
    by_cases ht : D.FS.tag L b i₀ = j
    · have hb : ∀ t : Bool, cpieceCoef D L σ j b (Sum.inr (i₀, some t)) = 0 := by
        intro t
        simp [cpieceCoef, hσ, ht]
      have h1 : cpieceCoef D L σ j b (Sum.inr (i₀, none)) = 1 := by
        simp [cpieceCoef, hσ, ht]
      rw [hb, hb, h1]
      simp only [abs_zero, zero_mul, add_zero, abs_one, one_mul, ht, ↓reduceIte]
      rfl
    · have h0 : cpieceCoef D L σ j b (Sum.inr (i₀, none)) = 0 := by
        simp [cpieceCoef, hσ, ht]
      have ht1 : cpieceCoef D L σ j b (Sum.inr (i₀, some true)) = 1 := by
        simp [cpieceCoef, hσ, ht]
      have ht2 : cpieceCoef D L σ j b (Sum.inr (i₀, some false)) = -1 := by
        simp [cpieceCoef, hσ, ht]
      rw [h0, ht1, ht2]
      simp only [cpieceG, ht, ↓reduceIte, abs_zero, zero_mul, zero_add, abs_one, abs_neg,
        one_mul, Bool.false_eq_true]
      unfold TheoremCBlock.FirstStage.vprice
      ring

/-- The variations of the coupled pieces: `2 κ(1)` for the whole difference (`‖κ' − κ‖ ≤ κ'(1) +
κ(1) = 2 κ(1)`), the mass otherwise. They weight the remainders of the per-term bounds. -/
noncomputable def cpieceM (b : BlockAtom Bk J L) : CPiece D L b → ℝ
  | Sum.inl none => 1
  | Sum.inl (some h) => mass (D.FS.κa L b h)
  | Sum.inr (i, none) => 2 * mass (D.FS.κ L b i)
  | Sum.inr (i, some t) => if t then mass (D.FS.κ' L b i) else mass (D.FS.κ L b i)

omit [DecidableEq P] in
theorem cpieceM_nonneg (b : BlockAtom Bk J L) (x : CPiece D L b) : 0 ≤ cpieceM D L b x := by
  rcases x with (_ | hh) | ⟨i, _ | t⟩
  · exact zero_le_one
  · exact TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κa_pos L b hh).1
  · exact mul_nonneg zero_le_two
      (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1)
  · cases t
    · exact TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1
    · exact TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ'_pos L b i).1

omit [DecidableEq P] in
/-- The weighted variations of the coupled pieces of an atom are at most `v_{𝔟,i}` at a chosen
difference (of either tag) and `1 + p_𝔟` at an unchosen atom. -/
theorem csum_pieceMass_le (ha : 0 ≤ a) (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag)
    (b : BlockAtom Bk J L) :
    ∑ x, |cpieceCoef D L σ j b x| * cpieceM D L b x ≤
      (σ b).elim (1 + D.FS.pvar L b) (fun i => D.FS.vprice L b i) := by
  have hs := D.one_le_selectionFactor ha L b
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  rcases hσ : σ b with _ | i₀
  · have hinr : ∀ i y, cpieceCoef D L σ j b (Sum.inr (i, y)) = 0 := by
      intro i y
      rcases y with _ | t <;> simp [cpieceCoef, hσ]
    simp only [hinr, abs_zero, zero_mul, Finset.sum_const_zero, add_zero]
    rw [Fintype.sum_option]
    simp only [cpieceCoef, cpieceM, hσ, ↓reduceIte, Option.elim, abs_one, one_mul]
    unfold TheoremCBlock.FirstStage.pvar
    refine add_le_add le_rfl (Finset.sum_le_sum fun i _ => ?_)
    exact le_mul_of_one_le_right (mul_nonneg (abs_nonneg _)
      (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κa_pos L b i).1)) hs
  · have hinl : ∀ o, cpieceCoef D L σ j b (Sum.inl o) = 0 := by
      intro o
      simp [cpieceCoef, hσ]
    have hinr : ∀ i, i ≠ i₀ → ∀ y, cpieceCoef D L σ j b (Sum.inr (i, y)) = 0 := by
      intro i hi y
      rcases y with _ | t <;> simp [cpieceCoef, hσ, Ne.symm hi]
    simp only [hinl, abs_zero, zero_mul, Finset.sum_const_zero, zero_add]
    rw [Finset.sum_eq_single i₀ (fun i _ hi => by simp [hinr i hi]) (by simp)]
    simp only [Option.elim]
    rw [Fintype.sum_option, Fintype.sum_bool]
    have hm := TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i₀).1
    have hm' := D.FS.mass_eq L b i₀
    unfold TheoremCBlock.FirstStage.vprice
    by_cases ht : D.FS.tag L b i₀ = j
    · have hb : ∀ t : Bool, cpieceCoef D L σ j b (Sum.inr (i₀, some t)) = 0 := by
        intro t
        simp [cpieceCoef, hσ, ht]
      have h1 : cpieceCoef D L σ j b (Sum.inr (i₀, none)) = 1 := by
        simp [cpieceCoef, hσ, ht]
      rw [hb, hb, h1]
      simp only [cpieceM, abs_zero, zero_mul, add_zero, abs_one, one_mul]
      rw [hm']
      nlinarith
    · have h0 : cpieceCoef D L σ j b (Sum.inr (i₀, none)) = 0 := by
        simp [cpieceCoef, hσ, ht]
      have ht1 : cpieceCoef D L σ j b (Sum.inr (i₀, some true)) = 1 := by
        simp [cpieceCoef, hσ, ht]
      have ht2 : cpieceCoef D L σ j b (Sum.inr (i₀, some false)) = -1 := by
        simp [cpieceCoef, hσ, ht]
      rw [h0, ht1, ht2]
      simp only [cpieceM, ↓reduceIte, abs_zero, zero_mul, zero_add, abs_one, abs_neg, one_mul,
        Bool.false_eq_true]
      rw [hm']
      nlinarith

end Pieces

section Final

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

omit [DecidableEq P] in
/-- **The coupled expansion of a sharp-first term**: the energy of
`⊗_𝔟 (σ_𝔟 ? δ_{𝔟,σ_𝔟} : ρ_𝔟)` is `∑_f (∏_𝔟 c_{f_𝔟}) Y[⊗_𝔟 K_{f_𝔟}]`. -/
theorem coupled_expansion (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) (g : (∀ b, BlockLabel m₀ blk p L b) → ℝ) :
    diagonalIntegral (tensorLaw (fun b => (σ b).elim (D.FS.ρ L b)
        (fun i => D.FS.κ' L b i - D.FS.κ L b i))) g =
      ∑ f : (∀ b, CPiece D L b), (∏ b, cpieceCoef D L σ j b (f b)) *
        diagonalIntegral (tensorLaw fun b => cpieceK D L b (f b)) g := by
  have hT : (fun b => (σ b).elim (D.FS.ρ L b) (fun i => D.FS.κ' L b i - D.FS.κ L b i)) =
      fun b => ∑ x, cpieceCoef D L σ j b x • cpieceK D L b x :=
    funext fun b => (cpieceSum_eq D L σ j b).symm
  have hexp : tensorLaw (fun b => ∑ x, cpieceCoef D L σ j b x • cpieceK D L b x) =
      ∑ f : (∀ b, CPiece D L b), (∏ b, cpieceCoef D L σ j b (f b)) •
        tensorLaw (fun b => cpieceK D L b (f b)) := by
    rw [tensorLaw_sum (fun b x => cpieceCoef D L σ j b x • cpieceK D L b x)]
    refine Finset.sum_congr rfl fun f _ => ?_
    exact tensorLaw_smul (fun b => cpieceCoef D L σ j b (f b)) (fun b => cpieceK D L b (f b))
  rw [hT, hexp]
  unfold diagonalIntegral multilinearIntegral
  rw [LinearMap.sum_apply]
  rfl

omit [DecidableEq P] in
/-- **The weighted per-term bounds**: if every term with nonzero coefficients satisfies
`|Y_f| ≤ (∏_𝔟 g_𝔟(f_𝔟)) K + r_f`, then `|∑_f w_f Y_f| ≤ K ∏_𝔟 ∑_x |c_x| g_x + ∑_f |w_f| r_f`. -/
theorem coupled_weighted_le (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) (Yf r : (∀ b, CPiece D L b) → ℝ) (K : ℝ)
    (hY : ∀ f, (∀ b, cpieceCoef D L σ j b (f b) ≠ 0) →
      |Yf f| ≤ (∏ b, cpieceG D L b (f b)) * K + r f) :
    |∑ f, (∏ b, cpieceCoef D L σ j b (f b)) * Yf f| ≤
      K * ∏ b, ∑ x, |cpieceCoef D L σ j b x| * cpieceG D L b x +
        ∑ f, (∏ b, |cpieceCoef D L σ j b (f b)|) * r f := by
  have hterm : ∀ f, |(∏ b, cpieceCoef D L σ j b (f b)) * Yf f| ≤
      (∏ b, |cpieceCoef D L σ j b (f b)|) * ((∏ b, cpieceG D L b (f b)) * K + r f) := by
    intro f
    rw [abs_mul, Finset.abs_prod]
    by_cases hf : ∀ b, cpieceCoef D L σ j b (f b) ≠ 0
    · exact mul_le_mul_of_nonneg_left (hY f hf) (Finset.prod_nonneg fun b _ => abs_nonneg _)
    · simp only [not_forall, not_not] at hf
      obtain ⟨b₀, hb₀⟩ := hf
      have h0 : ∏ b, |cpieceCoef D L σ j b (f b)| = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ b₀) (by rw [hb₀, abs_zero])
      rw [h0, zero_mul, zero_mul]
  have hprod : ∏ b, ∑ x, |cpieceCoef D L σ j b x| * cpieceG D L b x =
      ∑ f : (∀ b, CPiece D L b), (∏ b, |cpieceCoef D L σ j b (f b)|) *
        ∏ b, cpieceG D L b (f b) := by
    rw [Fintype.prod_sum (fun b x => |cpieceCoef D L σ j b x| * cpieceG D L b x)]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [← Finset.prod_mul_distrib]
  calc |∑ f, (∏ b, cpieceCoef D L σ j b (f b)) * Yf f|
      ≤ ∑ f, |(∏ b, cpieceCoef D L σ j b (f b)) * Yf f| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ f, (∏ b, |cpieceCoef D L σ j b (f b)|) * ((∏ b, cpieceG D L b (f b)) * K + r f) :=
        Finset.sum_le_sum fun f _ => hterm f
    _ = K * ∏ b, ∑ x, |cpieceCoef D L σ j b x| * cpieceG D L b x +
          ∑ f, (∏ b, |cpieceCoef D L σ j b (f b)|) * r f := by
        rw [hprod, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun f _ => ?_
        ring

omit [DecidableEq P] in
/-- **`SharpFirstTerms` from the coupled per-term bounds** (`lem:sharp-first` with
`lem:density:coupled`). Suppose that at every least counterexample, for every nonempty choice
`σ`, every tag `j` present and every choice `f` of coupled pieces with nonzero coefficients,
`|Y[⊗_𝔟 K_𝔟(f_𝔟)]| ≤ (∏_𝔟 g_𝔟(f_𝔟)) (1 + ε_L) Y + r_f`, with nonnegative remainders whose weighted
sums are density-linear. Then `D.SharpFirstTerms` holds.

Each such term is the energy of `(⊗ δ_𝔟 over the sharp atoms of tag j) ⊗ (⊗ positive spectators)
⊗ μ`, the setting of `lem:density:coupled`. Nothing is folded here. -/
theorem sharpFirstTerms_of_coupledPieces (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (ε : ℕ → ℝ) (hε0 : ∀ L, 0 ≤ ε L) (hεt : Tendsto ε atTop (𝓝 0)) {c : ℝ} (hc : 0 ≤ c)
    (r : ∀ L, Finset ℤ → (∀ b, Option (D.FS.Ib L b)) → D.FS.Tag → (∀ b, CPiece D L b) → ℝ)
    (hcoup : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => ∀ σ : (∀ b, Option (D.FS.Ib L b)),
      σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec (D.FS.tag L) σ j → ∀ f : (∀ b, CPiece D L b),
      (∀ b, cpieceCoef D L σ j b (f b) ≠ 0) →
      |diagonalIntegral (tensorLaw fun b => cpieceK D L b (f b)) (blockLift m₀ blk p L A)| ≤
        (∏ b, cpieceG D L b (f b)) * ((1 + ε L) * D.Y L A) + r L A σ j f))
    (hr0 : ∀ L A σ j f, 0 ≤ r L A σ j f)
    (hrem : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        ∑ j, ∑ f, (∏ b, |cpieceCoef D L σ j b (f b)|) * r L A σ j f ≤ remainder c L A)) :
    D.SharpFirstTerms := by
  refine ⟨ε, hε0, hεt, c, hc, fun L A σ => ∑ j, ∑ f,
    (∏ b, |cpieceCoef D L σ j b (f b)|) * r L A σ j f, ?_, hrem⟩
  filter_upwards [hcoup] with L hL
  intro C hC hk A hA hY σ hσ j hj
  have htw : ∏ b, ∑ x, |cpieceCoef D L σ j b x| * cpieceG D L b x =
      tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (D.FS.pvar L) j σ := by
    unfold tagWeight
    exact Finset.prod_congr rfl fun b _ => csum_pieceWeight D L σ j b
  have hw := coupled_weighted_le D L σ j
    (fun f => diagonalIntegral (tensorLaw fun b => cpieceK D L b (f b)) (blockLift m₀ blk p L A))
    (r L A σ j) ((1 + ε L) * D.Y L A) (hL C hC hk A hA hY σ hσ j hj)
  rw [htw] at hw
  have hsingle : ∑ f, (∏ b, |cpieceCoef D L σ j b (f b)|) * r L A σ j f ≤
      ∑ j', ∑ f, (∏ b, |cpieceCoef D L σ j' b (f b)|) * r L A σ j' f := by
    refine Finset.single_le_sum (f := fun j' => ∑ f, (∏ b, |cpieceCoef D L σ j' b (f b)|) *
      r L A σ j' f) (fun j' _ => ?_) (Finset.mem_univ j)
    exact Finset.sum_nonneg fun f _ =>
      mul_nonneg (Finset.prod_nonneg fun b _ => abs_nonneg _) (hr0 L A σ j' f)
  rw [coupled_expansion D L σ j]
  refine hw.trans ?_
  linarith

omit [DecidableEq P] in
/-- **The weighted variations of one choice** are at most `maxWeight(σ) e^{P}`. -/
theorem coupled_weighted_mass_le (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (ha : 0 ≤ a)
    (L : ℕ)
    (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) :
    ∑ f : (∀ b, CPiece D L b), (∏ b, |cpieceCoef D L σ j b (f b)|) *
        ∏ b, cpieceM D L b (f b) ≤
      maxWeight (D.FS.dprice L) (D.FS.vprice L) σ * Real.exp D.FS.P := by
  have hprod : ∏ b, ∑ x, |cpieceCoef D L σ j b x| * cpieceM D L b x =
      ∑ f : (∀ b, CPiece D L b), (∏ b, |cpieceCoef D L σ j b (f b)|) *
        ∏ b, cpieceM D L b (f b) := by
    rw [Fintype.prod_sum (fun b x => |cpieceCoef D L σ j b x| * cpieceM D L b x)]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [← Finset.prod_mul_distrib]
  rw [← hprod]
  have h1 : ∏ b, ∑ x, |cpieceCoef D L σ j b x| * cpieceM D L b x ≤
      ∏ b, (σ b).elim (1 + D.FS.pvar L b) (fun i => D.FS.vprice L b i) :=
    Finset.prod_le_prod₀ (fun b _ => Finset.sum_nonneg fun x _ =>
      mul_nonneg (abs_nonneg _) (cpieceM_nonneg D L b x))
          (fun b _ => csum_pieceMass_le D L ha σ j b)
  have h2 : ∏ b, (σ b).elim (1 + D.FS.pvar L b) (fun i => D.FS.vprice L b i) ≤
      maxWeight (D.FS.dprice L) (D.FS.vprice L) σ * restWeight (D.FS.pvar L) σ := by
    unfold maxWeight restWeight
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun b _ => ?_) (fun b _ => ?_)
    · rcases σ b with _ | i
      · simp only [Option.elim_none]
        linarith [TheoremCBlock.Structured.pvar_nonneg D L b]
      · exact TheoremCBlock.Structured.vprice_nonneg D L b i
    · rcases σ b with _ | i
      · simp only [Option.elim_none, one_mul]
        exact le_rfl
      · simp only [Option.elim_some, mul_one]
        linarith [TheoremCBlock.Structured.dprice_nonneg D L b i]
  have hR : restWeight (D.FS.pvar L) σ ≤ Real.exp D.FS.P := by
    have h3 : restWeight (D.FS.pvar L) σ ≤ ∏ b, (1 + D.FS.pvar L b) := by
      unfold restWeight
      refine Finset.prod_le_prod₀ (fun b _ => ?_) (fun b _ => ?_)
      · rcases σ b with _ | i
        · simp only [Option.elim_none]
          linarith [TheoremCBlock.Structured.pvar_nonneg D L b]
        · exact zero_le_one
      · rcases σ b with _ | i
        · exact le_rfl
        · simp only [Option.elim_some]
          linarith [TheoremCBlock.Structured.pvar_nonneg D L b]
    have h4 := prod_one_add_le_exp (D.FS.pvar L) (TheoremCBlock.Structured.pvar_nonneg D L)
    have h5 : Real.exp (∑ b, D.FS.pvar L b) ≤ Real.exp D.FS.P :=
      Real.exp_le_exp.mpr (by unfold TheoremCBlock.FirstStage.pvar; exact D.FS.P_total L)
    linarith
  have hM0 : 0 ≤ maxWeight (D.FS.dprice L) (D.FS.vprice L) σ := by
    unfold maxWeight
    refine prod_nonneg fun b _ => ?_
    rcases σ b with _ | i
    · exact zero_le_one
    · exact add_nonneg (TheoremCBlock.Structured.dprice_nonneg D L b i)
        (TheoremCBlock.Structured.vprice_nonneg D L b i)
  exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left hR hM0))

omit [DecidableEq P] in
/-- **`SharpFirstTerms` from the coupled per-term bounds alone** (`lem:sharp-first`,
`lem:density:coupled`): for every nonempty `σ`, tag `j` present and choice `f` of coupled pieces
with nonzero coefficients,
`|Y[⊗_𝔟 K_𝔟(f_𝔟)]| ≤ (∏_𝔟 g_𝔟(f_𝔟)) (1 + ε_L) Y + (∏_𝔟 m_𝔟(f_𝔟)) c₁ L^{-σ} α`. The remainder
summation is proved, with the constant `|𝔗| e^{P} e^{∑_j (d_j + v_j)} c₁`. -/
theorem sharpFirstTerms_of_coupledPieces_uniform
    (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (ha : 0 ≤ a) (ε : ℕ → ℝ) (hε0 : ∀ L, 0 ≤ ε L) (hεt : Tendsto ε atTop (𝓝 0)) {c₁ : ℝ}
        (hc₁ : 0 ≤ c₁)
    (hcoup : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => ∀ σ : (∀ b, Option (D.FS.Ib L b)),
      σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec (D.FS.tag L) σ j → ∀ f : (∀ b, CPiece D L b),
      (∀ b, cpieceCoef D L σ j b (f b) ≠ 0) →
      |diagonalIntegral (tensorLaw fun b => cpieceK D L b (f b)) (blockLift m₀ blk p L A)| ≤
        (∏ b, cpieceG D L b (f b)) * ((1 + ε L) * D.Y L A) +
          (∏ b, cpieceM D L b (f b)) * remainder c₁ L A)) :
    D.SharpFirstTerms := by
  have hrem0 : ∀ L A, 0 ≤ remainder c₁ L A := fun L A => by
    unfold remainder
    exact mul_nonneg (mul_nonneg hc₁ (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (density_nonneg _ _)
  refine sharpFirstTerms_of_coupledPieces D ε hε0 hεt
    (c := (Fintype.card D.FS.Tag : ℝ) * Real.exp D.FS.P *
      Real.exp (∑ j, (D.FS.dT j + D.FS.vT j)) * c₁)
    (by positivity)
    (fun L A _ _ f => (∏ b, cpieceM D L b (f b)) * remainder c₁ L A) hcoup
    (fun L A _ _ f => mul_nonneg (prod_nonneg fun b _ => cpieceM_nonneg D L b (f b))
      (hrem0 L A)) ?_
  refine Filter.Eventually.of_forall fun L => ?_
  intro C _ _ A _ _
  set rem := remainder c₁ L A
  have hr := hrem0 L A
  have hterm : ∀ σ : (∀ b, Option (D.FS.Ib L b)), ∀ j,
      ∑ f : (∀ b, CPiece D L b), (∏ b, |cpieceCoef D L σ j b (f b)|) *
          ((∏ b, cpieceM D L b (f b)) * rem) ≤
        maxWeight (D.FS.dprice L) (D.FS.vprice L) σ * Real.exp D.FS.P * rem := by
    intro σ j
    have h1 : ∑ f : (∀ b, CPiece D L b), (∏ b, |cpieceCoef D L σ j b (f b)|) *
          ((∏ b, cpieceM D L b (f b)) * rem) =
        (∑ f : (∀ b, CPiece D L b), (∏ b, |cpieceCoef D L σ j b (f b)|) *
          ∏ b, cpieceM D L b (f b)) * rem := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun f _ => ?_
      ring
    rw [h1]
    exact mul_le_mul_of_nonneg_right (coupled_weighted_mass_le D ha L σ j) hr
  have hsum := sum_maxWeight_le (TheoremCBlock.Structured.dprice_nonneg D L)
      (TheoremCBlock.Structured.vprice_nonneg D L)
  have hexp := Real.exp_le_exp.mpr (TheoremCBlock.Structured.sum_prices_le_totals D L)
  have hstep1 := Finset.sum_le_sum (s := univ.filter
      (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none))
    fun σ _ => Finset.sum_le_sum (s := (univ : Finset D.FS.Tag)) fun j _ => hterm σ j
  refine hstep1.trans ?_
  have hstep2 : ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      ∑ _j : D.FS.Tag, maxWeight (D.FS.dprice L) (D.FS.vprice L) σ * Real.exp D.FS.P * rem =
      (Fintype.card D.FS.Tag : ℝ) * Real.exp D.FS.P * rem *
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          maxWeight (D.FS.dprice L) (D.FS.vprice L) σ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [hstep2]
  have hfin : remainder ((Fintype.card D.FS.Tag : ℝ) * Real.exp D.FS.P *
      Real.exp (∑ j, (D.FS.dT j + D.FS.vT j)) * c₁) L A =
      (Fintype.card D.FS.Tag : ℝ) * Real.exp D.FS.P * rem *
        Real.exp (∑ j, (D.FS.dT j + D.FS.vT j)) := by
    unfold rem remainder
    ring
  rw [hfin]
  exact mul_le_mul_of_nonneg_left (hsum.trans hexp) (by positivity)

end Final

end Sarkozy.EnvelopeInputsBlock
