module

public import Sarkozy.EnvelopeInputs.EnvelopeUniform
public import Sarkozy.EnvelopeInputsBlock.EnvelopeSharpFolded
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
  Sarkozy.RecordExpansion.Choice Sarkozy.Structured ReflectionCut

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

section Masses

variable {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} {L : ℕ} (dec : DecFamily D L)
    (ω : Choice (D.CL.T L))

/-- The masses of the pieces under a selection (one for the entry factor: `μ_𝔟` or a selected
envelope, both probability measures). -/
noncomputable def epieceM (b : BlockAtom Bk J L) : EPiece dec b → ℝ
  | Sum.inl none => 1
  | Sum.inl (some i) => mass (D.GB.κu L b i)
  | Sum.inr ⟨_, Sum.inl _⟩ => 1
  | Sum.inr ⟨i, Sum.inr t⟩ => if t then mass (D.FS.κ' L b i) else mass (D.FS.κ L b i)

omit [DecidableEq P] in
theorem epieceM_nonneg (b : BlockAtom Bk J L) (x : EPiece dec b) : 0 ≤ epieceM dec b x := by
  rcases x with (_ | i) | ⟨i, s | t⟩
  · exact zero_le_one
  · exact TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.GB.κu_pos L b i).1
  · exact zero_le_one
  · cases t
    · exact TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1
    · exact TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ'_pos L b i).1

omit [DecidableEq P] in
theorem epieceM_le_epieceG (ha : 0 ≤ a) (b : BlockAtom Bk J L) (x : EPiece dec b) :
    epieceM dec b x ≤ epieceG dec ω b x := by
  have hs := D.one_le_selectionFactor ha L b
  rcases x with (_ | i) | ⟨i, s | t⟩
  · rcases hω : ω b with _ | te
    · simp only [epieceM, epieceG, hω, Option.elim, le_refl]
    · simp only [epieceM, epieceG, hω, Option.elim]
      exact hs
  · exact le_mul_of_one_le_right
      (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.GB.κu_pos L b i).1) hs
  · exact hs
  · cases t
    · exact le_mul_of_one_le_right
        (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1) hs
    · exact le_mul_of_one_le_right
        (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ'_pos L b i).1)
        hs

omit [DecidableEq P] in
/-- **The weighted masses of the pieces of an atom** are at most the factor of
`tagWeight(d, v, u')` (no selection factor). -/
theorem sum_epieceMass_le (ha : 0 ≤ a) (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag)
    (b : BlockAtom Bk J L) :
    ∑ x, |epieceCoef dec ω σ j b x| * epieceD dec b x * epieceM dec b x ≤
      (σ b).elim (1 + selPriceU ω b)
        (fun i => if D.FS.tag L b i = j then D.FS.dprice L b i else D.FS.vprice L b i) := by
  rcases hω : ω b with _ | te
  · have h1 := sum_epieceWeight_le dec ω σ j b
    simp only [hω, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, one_mul] at h1
    refine le_trans (Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
      (epieceM_le_epieceG dec ω ha b x) (mul_nonneg (abs_nonneg _) (epieceD_nonneg dec b x))) h1
  · have hc : ∀ x, x ≠ Sum.inl none → epieceCoef dec ω σ j b x = 0 := by
      intro x hx
      rcases x with (_ | i) | ⟨i, s | t⟩
      · exact absurd rfl hx
      · simp [epieceCoef, hω]
      · simp [epieceCoef, hω]
      · simp [epieceCoef, hω]
    rw [Finset.sum_eq_single (Sum.inl none) (fun x _ hx => by rw [hc x hx, abs_zero, zero_mul,
      zero_mul]) (by simp)]
    simp only [epieceD, epieceM, mul_one]
    rcases hσ : σ b with _ | i₀
    · simp [epieceCoef, hσ, selPriceU, hω]
    · simp only [epieceCoef, hσ, reduceCtorEq, ↓reduceIte, abs_zero, Option.elim]
      split_ifs
      · exact TheoremCBlock.Structured.dprice_nonneg D L b i₀
      · exact TheoremCBlock.Structured.vprice_nonneg D L b i₀

end Masses

omit [DecidableEq P] in
/-- The weighted remainders of one `(σ, j)` under a selection are at most `tagWeight_j(σ)` times
the remainder. -/
theorem weighted_emass_le (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (ha : 0 ≤ a) (L : ℕ)
    (dec : DecFamily D L)
    (ω : Choice (D.CL.T L)) (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) :
    ∑ f, choiceWeight (epieceCoef dec ω σ j) (epieceD dec) f * ∏ b, epieceM dec b (f b) ≤
      tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (selPriceU ω) j σ := by
  have hprod : ∏ b, ∑ x, |epieceCoef dec ω σ j b x| * epieceD dec b x * epieceM dec b x =
      ∑ f : (∀ b, EPiece dec b), choiceWeight (epieceCoef dec ω σ j) (epieceD dec) f *
        ∏ b, epieceM dec b (f b) := by
    rw [Fintype.prod_sum (fun b x => |epieceCoef dec ω σ j b x| * epieceD dec b x *
      epieceM dec b x)]
    refine Finset.sum_congr rfl fun f _ => ?_
    unfold choiceWeight
    rw [← Finset.prod_mul_distrib]
  rw [← hprod]
  unfold tagWeight
  exact Finset.prod_le_prod₀ (fun b _ => Finset.sum_nonneg fun x _ => mul_nonneg
    (mul_nonneg (abs_nonneg _) (epieceD_nonneg dec b x)) (epieceM_nonneg dec b x))
    (fun b _ => sum_epieceMass_le dec ω ha σ j b)

omit [DecidableEq P] in
/-- `tagWeight(d, v, u')_j(σ) ≤ maxWeight(σ) e^{U₀}`. -/
theorem tagWeight_selPrice_le (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (ω : Choice (D.CL.T L))
    (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) :
    tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (selPriceU ω) j σ ≤
      maxWeight (D.FS.dprice L) (D.FS.vprice L) σ * Real.exp D.GB.U₀ := by
  have hu0 : ∀ b, 0 ≤ selPriceU ω b := by
    intro b
    unfold selPriceU
    split_ifs
    · exact le_rfl
    · exact TheoremCBlock.Structured.uprice_nonneg D L b
  rw [tagWeight_eq_mul]
  have hW := sharpVarWeight_le_maxWeight (D.FS.tag L) (TheoremCBlock.Structured.dprice_nonneg D L)
    (TheoremCBlock.Structured.vprice_nonneg D L) j σ
  have hR0 := restWeight_nonneg hu0 σ
  have hW0 := sharpVarWeight_nonneg (D.FS.tag L) (TheoremCBlock.Structured.dprice_nonneg D L)
    (TheoremCBlock.Structured.vprice_nonneg D L) j σ
  have hR : restWeight (selPriceU ω) σ ≤ Real.exp D.GB.U₀ := by
    have h1 : restWeight (selPriceU ω) σ ≤ ∏ b, (1 + selPriceU ω b) := by
      unfold restWeight
      refine Finset.prod_le_prod₀ (fun b _ => ?_) (fun b _ => ?_)
      · rcases σ b with _ | i
        · simp only [Option.elim_none]
          linarith [hu0 b]
        · exact zero_le_one
      · rcases σ b with _ | i
        · exact le_rfl
        · simp only [Option.elim_some]
          linarith [hu0 b]
    have h2 := prod_one_add_le_exp (selPriceU ω) hu0
    have h3 : ∑ b, selPriceU ω b ≤ D.GB.U₀ := by
      refine le_trans (Finset.sum_le_sum fun b _ => ?_) (D.GB.U₀_total L)
      unfold selPriceU
      split_ifs
      · exact Finset.sum_nonneg fun i _ => mul_nonneg
          (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.GB.κu_pos L b i).1)
          (D.selectionFactor_nonneg L b)
      · exact le_rfl
    have h4 := Real.exp_le_exp.mpr h3
    linarith
  calc sharpVarWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) j σ *
        restWeight (selPriceU ω) σ
      ≤ maxWeight (D.FS.dprice L) (D.FS.vprice L) σ * restWeight (selPriceU ω) σ :=
        mul_le_mul_of_nonneg_right hW hR0
    _ ≤ maxWeight (D.FS.dprice L) (D.FS.vprice L) σ * Real.exp D.GB.U₀ :=
        mul_le_mul_of_nonneg_left hR (hW0.trans hW)

omit [DecidableEq P] in
/-- **`EnvelopeBound` from density-structured bounds alone** (`lem:bracket-energy`,
`lem:sharp-first`, `lem:record:folded-energy`, `prop:record:density-structured`): the subset
terms with the remainders `∏_f mass(∑κu) c₁ L^{-σ} α`, and the folded energies of every choice of
pieces with the remainders `(∏_𝔟 m_𝔟(f_𝔟)) c₁ L^{-σ} α`. The remainder summation is proved, with
the per-selection constant `e^{U₀} (1 + |𝔗| e^{∑_j(d_j+v_j)}) c₁`. -/
theorem envelopeBound_of_foldedPieces_uniform (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (ha : 0 ≤ a) (dec : ∀ L, DecFamily D L)
    (εE : ℕ → ℝ) (hε0 : ∀ L, 0 ≤ εE L) (hεt : Tendsto εE atTop (𝓝 0)) {c₁ : ℝ} (hc₁ : 0 ≤ c₁)
    (hsub : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
      ∀ f : BlockAtom Bk J L → Bool,
        |diagonalIntegral (tensorLaw fun b => if f b then
            (if (ω b).isSome then 0 else ∑ i, D.GB.κu L b i)
          else entryFactor (D.R.law p L b) (D.CL.D L b) (ω b)) (blockLift m₀ blk p L A)| ≤
          ((1 + εE L) * (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
            D.Y L A) * ∏ b, (if f b then (if (ω b).isSome then 0 else D.GB.uprice L b) else 1) +
          (∏ b, (if f b then (if (ω b).isSome then 0 else mass (∑ i, D.GB.κu L b i)) else 1)) *
            remainder c₁ L A))
    (hfold : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
      ∀ j f,
      foldedPlus (D.FS.cut j) (epieceLp (dec L) ω j) (fun _ => blockLift m₀ blk p L A) f ≤
          (∏ b, epieceG (dec L) ω b (f b)) * ((1 + εE L) * D.Y L A) +
            (∏ b, epieceM (dec L) b (f b)) * remainder c₁ L A ∧
        foldedMinus (D.FS.cut j) (epieceLm (dec L) ω j) (fun _ => blockLift m₀ blk p L A) f ≤
          (∏ b, epieceG (dec L) ω b (f b)) * ((1 + εE L) * D.Y L A) +
            (∏ b, epieceM (dec L) b (f b)) * remainder c₁ L A)) :
    D.EnvelopeBound := by
  have hrem0 : ∀ L A, 0 ≤ remainder c₁ L A := fun L A => by
    unfold remainder
    exact mul_nonneg (mul_nonneg hc₁ (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (density_nonneg _ _)
  set K := Real.exp D.GB.U₀ * (1 + (Fintype.card D.FS.Tag : ℝ) *
    Real.exp (∑ j, (D.FS.dT j + D.FS.vT j))) * c₁ with hK
  have hK0 : 0 ≤ K := by positivity
  refine TheoremCBlock.Structured.envelopeBound_of_terms_uniform D ha εE hε0 hεt hK0
    (fun L A ω f =>
      (∏ b, (if f b then (if (ω b).isSome then 0 else mass (∑ i, D.GB.κu L b i)) else 1)) *
        remainder c₁ L A)
    (fun L A ω σ => ∑ j, ∑ f, choiceWeight (epieceCoef (dec L) ω σ j) (epieceD (dec L)) f *
      (((∏ b, epieceM (dec L) b (f b)) * remainder c₁ L A +
        (∏ b, epieceM (dec L) b (f b)) * remainder c₁ L A) / 2)) ?_ ?_
  · -- the two families of term bounds
    have hgen := (envelopeBound_terms_of_folded D dec εE hε0
      (fun L A ω f =>
        (∏ b, (if f b then (if (ω b).isSome then 0 else mass (∑ i, D.GB.κu L b i)) else 1)) *
          remainder c₁ L A)
      (fun L A ω _ _ f => (∏ b, epieceM (dec L) b (f b)) * remainder c₁ L A)
      (fun L A ω _ _ f => (∏ b, epieceM (dec L) b (f b)) * remainder c₁ L A)
      (fun L A ω σ j f => ⟨mul_nonneg (prod_nonneg fun b _ => epieceM_nonneg (dec L) b (f b))
        (hrem0 L A), mul_nonneg (prod_nonneg fun b _ => epieceM_nonneg (dec L) b (f b))
        (hrem0 L A)⟩) hsub (by
        filter_upwards [hfold] with L hL
        intro C hC hk A hA hY ω hω _ _ j _ f
        exact hL C hC hk A hA hY ω hω j f))
    exact hgen
  · refine Filter.Eventually.of_forall fun L => ?_
    intro C _ _ A _ _ ω _
    set rem := remainder c₁ L A
    have hr := hrem0 L A
    have hsub_rem := TheoremCBlock.Structured.sum_subset_remainder_le D ha L A ω hc₁
    have hterm : ∀ σ : (∀ b, Option (D.FS.Ib L b)), ∀ j,
        ∑ f, choiceWeight (epieceCoef (dec L) ω σ j) (epieceD (dec L)) f *
          (((∏ b, epieceM (dec L) b (f b)) * rem + (∏ b, epieceM (dec L) b (f b)) * rem) / 2) ≤
          maxWeight (D.FS.dprice L) (D.FS.vprice L) σ * Real.exp D.GB.U₀ * rem := by
      intro σ j
      have h1 : ∑ f, choiceWeight (epieceCoef (dec L) ω σ j) (epieceD (dec L)) f *
          (((∏ b, epieceM (dec L) b (f b)) * rem + (∏ b, epieceM (dec L) b (f b)) * rem) / 2) =
          (∑ f, choiceWeight (epieceCoef (dec L) ω σ j) (epieceD (dec L)) f *
            ∏ b, epieceM (dec L) b (f b)) * rem := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun f _ => ?_
        ring
      rw [h1]
      exact (mul_le_mul_of_nonneg_right (weighted_emass_le D ha L (dec L) ω σ j) hr).trans
        (mul_le_mul_of_nonneg_right (tagWeight_selPrice_le D L ω σ j) hr)
    have hsum := sum_maxWeight_le (TheoremCBlock.Structured.dprice_nonneg D L)
        (TheoremCBlock.Structured.vprice_nonneg D L)
    have hexp := Real.exp_le_exp.mpr (TheoremCBlock.Structured.sum_prices_le_totals D L)
    have hsharp : ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        ∑ j, ∑ f, choiceWeight (epieceCoef (dec L) ω σ j) (epieceD (dec L)) f *
          (((∏ b, epieceM (dec L) b (f b)) * rem + (∏ b, epieceM (dec L) b (f b)) * rem) / 2) ≤
        (Fintype.card D.FS.Tag : ℝ) * Real.exp D.GB.U₀ * rem *
          Real.exp (∑ j, (D.FS.dT j + D.FS.vT j)) := by
      calc ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
            ∑ j, ∑ f, choiceWeight (epieceCoef (dec L) ω σ j) (epieceD (dec L)) f *
              (((∏ b, epieceM (dec L) b (f b)) * rem +
                (∏ b, epieceM (dec L) b (f b)) * rem) / 2)
          ≤ ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
              ∑ _j : D.FS.Tag, maxWeight (D.FS.dprice L) (D.FS.vprice L) σ *
                Real.exp D.GB.U₀ * rem :=
            Finset.sum_le_sum fun σ _ => Finset.sum_le_sum fun j _ => hterm σ j
        _ = (Fintype.card D.FS.Tag : ℝ) * Real.exp D.GB.U₀ * rem *
              ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
                maxWeight (D.FS.dprice L) (D.FS.vprice L) σ := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun σ _ => ?_
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            ring
        _ ≤ (Fintype.card D.FS.Tag : ℝ) * Real.exp D.GB.U₀ * rem *
              Real.exp (∑ j, (D.FS.dT j + D.FS.vT j)) :=
            mul_le_mul_of_nonneg_left (hsum.trans hexp) (by positivity)
    calc ∑ f : BlockAtom Bk J L → Bool,
          (∏ b, (if f b then (if (ω b).isSome then 0 else mass (∑ i, D.GB.κu L b i)) else 1)) *
            rem +
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          ∑ j, ∑ f, choiceWeight (epieceCoef (dec L) ω σ j) (epieceD (dec L)) f *
            (((∏ b, epieceM (dec L) b (f b)) * rem +
              (∏ b, epieceM (dec L) b (f b)) * rem) / 2)
        ≤ remainder (Real.exp D.GB.U₀ * c₁) L A + (Fintype.card D.FS.Tag : ℝ) *
            Real.exp D.GB.U₀ * rem * Real.exp (∑ j, (D.FS.dT j + D.FS.vT j)) :=
          add_le_add hsub_rem hsharp
      _ = remainder K L A := by
          unfold rem remainder
          rw [hK]
          ring

end Sarkozy.EnvelopeInputsBlock
