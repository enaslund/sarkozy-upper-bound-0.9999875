module

public import Sarkozy.DensityChain2.PiecePrice
public import Sarkozy.SharpSums.Split

@[expose] public section

/-!
# The chain² and cross weight sums of `lem:sharp-first`

SUM (7 November 2026). The weight sums shared by the four summations `RchSumPT*`
(`SharpBase2.Fields`), in the paper's form (proof of `lem:sharp-first`: "summing over the
energies `T'` of one term …, summing then over the terms of the category"):

* `sum_tagWeight_eq`: `∑_σ wt_j(σ) = ∏_𝔟 (1 + p_𝔟 + ∑_i [tag = j ? d : v])` (all choices);
* `sum_tagWeight_le`: over the nonempty choices, at most `∏_𝔟 (1 + p_𝔟 + s_𝔟)`,
  `s_𝔟 = ∑_i (d_{𝔟,i} + v_{𝔟,i})`;
* `sum_bool_prod_eq`: `∑_f ∏_𝔟 (f 𝔟 ? c_𝔟 : 1)(1 + (f 𝔟 ? 0 : u_𝔟) + s_𝔟) =
  ∏_𝔟 (c_𝔟 (1 + s_𝔟) + 1 + u_𝔟 + s_𝔟)` (the selections `f`, `Fintype.prod_sum`);
* `sum_weight_bpieceG_le`: `∑_φ w_φ BG(φ) ≤ wt_j(σ)` (as in SH2's `choice_bound_perterm`);
* `piecePrice_plus_le_one`, `piecePrice_minus_le_one`: DC3's `piecePrice_plus/minus_le` with
  `sq(D_E)^a ≥ 1`: `G_±(φ) ≤ BG(φ) ∏_𝔟 (f 𝔟 ? uQ_𝔟 : 1)`;
* **`chain2_total_le`**: the chain² weight sum of all four summations,
  `∑_f ∑_{σ≠∅} ∑_j chainPart ≤ |𝔗| ∏_𝔟 (uQ_𝔟 (1 + s_𝔟) + 1 + u_𝔟 + s_𝔟)`;
* **`cross_weight_total_le`**: the weight sum of the cross terms,
  `∑_f ∑_{σ≠∅} c_f ∑_φ w_φ BG(φ) ≤ ∏_𝔟 (c_𝔟 (1 + s_𝔟) + 1 + u_𝔟 + s_𝔟)` per tag, with
  `c_f = ∏_𝔟 (f 𝔟 ? c_𝔟 : 1)`.
-/

namespace Sarkozy.SharpSums

open Finset
open scoped BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.BlockFrame Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.EnvelopeInputsBlock Sarkozy.RecordExpansion

section TagSums

variable {ι : Type} [Fintype ι] [DecidableEq ι] {I : ι → Type} [∀ b, Fintype (I b)]
  [∀ b, DecidableEq (I b)] {Tag : Type} [DecidableEq Tag]

omit [∀ b, DecidableEq (I b)] in
/-- **The tag weights summed over all choices** (`lem:sharp-first`, the sum over the terms of a
category, before the distinct-atom restriction is dropped): `∑_σ wt_j(σ) =
∏_𝔟 (1 + p_𝔟 + ∑_i [tag(𝔟,i) = j ? d_{𝔟,i} : v_{𝔟,i}])`. -/
theorem sum_tagWeight_eq (tag : ∀ b, I b → Tag) (d v : ∀ b, I b → ℝ) (p : ι → ℝ) (j : Tag) :
    ∑ σ : (∀ b, Option (I b)), tagWeight tag d v p j σ =
      ∏ b, (1 + p b + ∑ i, if tag b i = j then d b i else v b i) := by
  unfold tagWeight
  rw [← Fintype.prod_sum (fun b (o : Option (I b)) =>
    o.elim (1 + p b) (fun i => if tag b i = j then d b i else v b i))]
  refine prod_congr rfl fun b _ => ?_
  rw [Fintype.sum_option]
  rfl

omit [DecidableEq ι] [∀ b, Fintype (I b)] [∀ b, DecidableEq (I b)] in
theorem tagWeight_nonneg (tag : ∀ b, I b → Tag) {d v : ∀ b, I b → ℝ} {p : ι → ℝ}
    (hd : ∀ b i, 0 ≤ d b i) (hv : ∀ b i, 0 ≤ v b i) (hp : ∀ b, 0 ≤ p b) (j : Tag)
    (σ : ∀ b, Option (I b)) : 0 ≤ tagWeight tag d v p j σ := by
  unfold tagWeight
  refine prod_nonneg fun b _ => ?_
  cases σ b with
  | none => simp only [Option.elim_none]; linarith [hp b]
  | some i =>
    simp only [Option.elim_some]
    split_ifs
    · exact hd b i
    · exact hv b i

/-- **The tag weights over the nonempty choices**: `∑_{σ≠∅} wt_j(σ) ≤ ∏_𝔟 (1 + p_𝔟 + s_𝔟)`
with `s_𝔟 = ∑_i (d_{𝔟,i} + v_{𝔟,i})`, for nonnegative prices. -/
theorem sum_tagWeight_le (tag : ∀ b, I b → Tag) {d v : ∀ b, I b → ℝ} {p : ι → ℝ}
    (hd : ∀ b i, 0 ≤ d b i) (hv : ∀ b i, 0 ≤ v b i) (hp : ∀ b, 0 ≤ p b) (j : Tag) :
    ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (I b)) => σ ≠ fun _ => none),
        tagWeight tag d v p j σ ≤
      ∏ b, (1 + p b + ∑ i, (d b i + v b i)) := by
  refine (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun σ _ _ =>
    tagWeight_nonneg tag hd hv hp j σ).trans ?_
  rw [sum_tagWeight_eq]
  refine prod_le_prod₀ (fun b _ => ?_) fun b _ => ?_
  · have : 0 ≤ ∑ i, (if tag b i = j then d b i else v b i) := sum_nonneg fun i _ => by
      split_ifs
      · exact hd b i
      · exact hv b i
    linarith [hp b]
  · have : ∑ i, (if tag b i = j then d b i else v b i) ≤ ∑ i, (d b i + v b i) :=
      sum_le_sum fun i _ => by
        split_ifs
        · linarith [hv b i]
        · linarith [hd b i]
    linarith

/-- **The selections `f`, summed** (`Fintype.prod_sum` over `ι → Bool`):
`∑_f ∏_𝔟 (f 𝔟 ? c_𝔟 : 1) (1 + (f 𝔟 ? 0 : u_𝔟) + s_𝔟) = ∏_𝔟 (c_𝔟 (1 + s_𝔟) + (1 + u_𝔟 + s_𝔟))`. -/
theorem sum_bool_prod_eq (c u s : ι → ℝ) :
    ∑ f : ι → Bool, (∏ b, (if f b then c b else 1)) *
        ∏ b, (1 + (if f b then 0 else u b) + s b) =
      ∏ b, (c b * (1 + s b) + (1 + u b + s b)) := by
  have e : ∀ b, c b * (1 + s b) + (1 + u b + s b) = ∑ x : Bool,
      (if x then c b else 1) * (1 + (if x then 0 else u b) + s b) := by
    intro b
    rw [Fintype.sum_bool]
    simp only [↓reduceIte, Bool.false_eq_true]
    ring
  simp_rw [e]
  rw [Fintype.prod_sum (fun b (x : Bool) => (if x then c b else 1) *
    (1 + (if x then 0 else u b) + s b))]
  refine sum_congr rfl fun f _ => ?_
  rw [prod_mul_distrib]

end TagSums

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

section Concrete

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)

omit [DecidableEq P] in
/-- **The weights of the pieces against their prices** (`lem:sharp-first`: "at an atom of
`S \ S_j` the two positive parts have total price `v`, at an atom of `F \ S` the factor is `μ` or a
positive record of total weight `p`"): `∑_φ w_φ ∏_𝔟 BG_𝔟(φ_𝔟) ≤ wt_j(σ)`. -/
theorem sum_weight_bpieceG_le (f : BlockAtom Bk J L → Bool) (σ : ∀ b, Option (D.FS.Ib L b))
    (j : D.FS.Tag) :
    ∑ φ : (∀ b, DensityFibre.HPiece D L b),
        choiceWeight (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ *
          ∏ b, DensityFibre.bpieceG D L b (φ b) ≤
      tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
        (fun b => if f b then 0 else D.GB.uprice L b) j σ := by
  have hprod' : ∏ b, ∑ x, |DensityFibre.hpieceCoef D L f σ j b x| *
      DensityFibre.bpieceD D L b x * DensityFibre.bpieceG D L b x =
      ∑ φ : (∀ b, DensityFibre.HPiece D L b),
        choiceWeight (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ *
          ∏ b, DensityFibre.bpieceG D L b (φ b) := by
    rw [Fintype.prod_sum (fun b x => |DensityFibre.hpieceCoef D L f σ j b x| *
      DensityFibre.bpieceD D L b x * DensityFibre.bpieceG D L b x)]
    refine Finset.sum_congr rfl fun φ _ => ?_
    simp only [choiceWeight]
    rw [← Finset.prod_mul_distrib]
  rw [← hprod']
  unfold tagWeight
  exact Finset.prod_le_prod₀ (fun b _ => Finset.sum_nonneg fun x _ =>
    mul_nonneg (mul_nonneg (abs_nonneg _) (DensityFibre.bpieceD_nonneg D L b x))
      (DensityFibre.bpieceG_nonneg D L b x))
    fun b _ => DensityFibre.sum_bpieceWeight_le D L f σ j b

omit [DecidableEq P] in
theorem choiceWeight_nonneg' (f : BlockAtom Bk J L → Bool) (σ : ∀ b, Option (D.FS.Ib L b))
    (j : D.FS.Tag) (φ : ∀ b, DensityFibre.HPiece D L b) :
    0 ≤ choiceWeight (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ :=
  prod_nonneg fun b _ => mul_nonneg (abs_nonneg _) (DensityFibre.bpieceD_nonneg D L b (φ b))

omit [DecidableEq P] in
/-- A piece of nonzero weight has nonzero coefficients at every atom. -/
theorem coef_ne_zero_of_weight_ne_zero (f : BlockAtom Bk J L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) (φ : ∀ b, DensityFibre.HPiece D L b)
    (hw : choiceWeight (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ ≠ 0) :
    ∀ b, DensityFibre.hpieceCoef D L f σ j b (φ b) ≠ 0 := by
  intro b hb
  apply hw
  exact prod_eq_zero (mem_univ b) (by rw [hb, abs_zero, zero_mul])

omit [DecidableEq P] in
/-- **The weight sum over the choices and selections** (`lem:sharp-first`, the sum over the
categories, with the distinct-atom restriction dropped): for `c ≥ 0`,
`∑_f ∑_{σ≠∅} (∏_𝔟 (f 𝔟 ? c_𝔟 : 1)) ∑_φ w_φ BG(φ) ≤ ∏_𝔟 (c_𝔟 (1 + s_𝔟) + 1 + u_𝔟 + s_𝔟)`
at every tag `j`, `s_𝔟 = ∑_i (d_{𝔟,i} + v_{𝔟,i})`. -/
theorem weight_total_le (j : D.FS.Tag) (c : BlockAtom Bk J L → ℝ) (hc : ∀ b, 0 ≤ c b) :
    ∑ f : BlockAtom Bk J L → Bool,
      ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        (∏ b, (if f b then c b else 1)) *
          ∑ φ : (∀ b, DensityFibre.HPiece D L b),
            choiceWeight (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ *
              ∏ b, DensityFibre.bpieceG D L b (φ b) ≤
      ∏ b, (c b * (1 + ∑ i, (D.FS.dprice L b i + D.FS.vprice L b i)) +
        (1 + D.GB.uprice L b + ∑ i, (D.FS.dprice L b i + D.FS.vprice L b i))) := by
  refine le_trans ?_ (le_of_eq (sum_bool_prod_eq c (D.GB.uprice L)
    (fun b => ∑ i, (D.FS.dprice L b i + D.FS.vprice L b i))))
  refine sum_le_sum fun f _ => ?_
  have hcf : 0 ≤ ∏ b, (if f b then c b else 1) := prod_nonneg fun b _ => by
    split_ifs
    · exact hc b
    · exact zero_le_one
  rw [← mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hcf
  refine (sum_le_sum fun σ _ => sum_weight_bpieceG_le D L f σ j).trans ?_
  have hp : ∀ b, 0 ≤ (if f b then 0 else D.GB.uprice L b) := fun b => by
    split_ifs
    · exact le_rfl
    · exact TheoremCBlock.Structured.uprice_nonneg D L b
  refine (sum_tagWeight_le (D.FS.tag L) (TheoremCBlock.Structured.dprice_nonneg D L)
    (TheoremCBlock.Structured.vprice_nonneg D L) hp j).trans (le_of_eq ?_)
  refine prod_congr rfl fun b _ => ?_
  split_ifs <;> ring

variable (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
  (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (hQ : ∀ b, IsPositiveRecord (Qb b))
  (dec : DecFamily D L)

include hpair hQ

omit [DecidableEq P] in
/-- **DC3's piece price with `sq(D_E)^a ≥ 1`** (`a ≥ 0`): the plus chain price of a piece of
nonzero coefficients is at most `BG(φ) ∏_𝔟 (f 𝔟 ? uQ_𝔟 : 1)`. -/
theorem piecePrice_plus_le_one (ha : 0 ≤ a) (j : D.FS.Tag) (f : BlockAtom Bk J L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) (φ : ∀ b, DensityFibre.HPiece D L b)
    (hφ : ∀ b, DensityFibre.hpieceCoef D L f σ j b (φ b) ≠ 0)
    (hsel : ∀ b, ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a ≤
      TheoremCBlock.selectionFactor a p D.S.selPre L b)
    (uQ : BlockAtom Bk J L → ℝ)
    (hQp : ∀ b, (∑ z, |lawDensity (Qb b) z|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a ≤ uQ b) :
    (∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
        ∑ z, |lawDensity (DensityFibre.bpieceLp D L Qb dec j b.1 (φ b.1)) z|) ≤
      (∏ b, DensityFibre.bpieceG D L b (φ b)) * ∏ b, (if f b then uQ b else 1) := by
  have h := DensityChain2.piecePrice_plus_le D L hpair Qb hQ dec j f σ φ hφ hsel uQ hQp
  have h1 : (1 : ℝ) ≤ ((leastSquare (∏ b ∈ DensityFibre.hTermAtoms D L φ,
      crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a :=
    Real.one_le_rpow (by exact_mod_cast leastSquare_pos _) ha
  have h0 : 0 ≤ ∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
      ∑ z, |lawDensity (DensityFibre.bpieceLp D L Qb dec j b.1 (φ b.1)) z| :=
    prod_nonneg fun b _ => sum_nonneg fun z _ => abs_nonneg _
  nlinarith

omit [DecidableEq P] in
/-- The minus chain price, as `piecePrice_plus_le_one`. -/
theorem piecePrice_minus_le_one (ha : 0 ≤ a) (j : D.FS.Tag) (f : BlockAtom Bk J L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) (φ : ∀ b, DensityFibre.HPiece D L b)
    (hφ : ∀ b, DensityFibre.hpieceCoef D L f σ j b (φ b) ≠ 0)
    (hsel : ∀ b, ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a ≤
      TheoremCBlock.selectionFactor a p D.S.selPre L b)
    (uQ : BlockAtom Bk J L → ℝ)
    (hQp : ∀ b, (∑ z, |lawDensity (Qb b) z|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a ≤ uQ b) :
    (∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
        ∑ z, |lawDensity (DensityFibre.bpieceLm D L Qb dec j b.1 (φ b.1)) z|) ≤
      (∏ b, DensityFibre.bpieceG D L b (φ b)) * ∏ b, (if f b then uQ b else 1) := by
  have h := DensityChain2.piecePrice_minus_le D L hpair Qb hQ dec j f σ φ hφ hsel uQ hQp
  have h1 : (1 : ℝ) ≤ ((leastSquare (∏ b ∈ DensityFibre.hTermAtoms D L φ,
      crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a :=
    Real.one_le_rpow (by exact_mod_cast leastSquare_pos _) ha
  have h0 : 0 ≤ ∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
      ∑ z, |lawDensity (DensityFibre.bpieceLm D L Qb dec j b.1 (φ b.1)) z| :=
    prod_nonneg fun b _ => sum_nonneg fun z _ => abs_nonneg _
  nlinarith

omit [DecidableEq P] in
/-- **The chain² weight sum of the four summations** (`lem:sharp-first`, the products of the two
chain remainders of `prop:record:density-structured`): with DC3's piece prices
(`piecePrice_plus/minus_le`, `sq(D_E)^a ≥ 1`), the chain² part of SH2's `rchPT`, summed over the
tags, the nonempty choices and the selections, is at most
`|𝔗| ∏_𝔟 (uQ_𝔟 (1 + s_𝔟) + 1 + u_𝔟 + s_𝔟)`. It does not depend on `ω`, `𝒥` or the
small-piece predicate. -/
theorem chain2_total_le (ha : 0 ≤ a)
    (hsel : ∀ b, ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a ≤
      TheoremCBlock.selectionFactor a p D.S.selPre L b)
    (uQ : BlockAtom Bk J L → ℝ) (huQ : ∀ b, 0 ≤ uQ b)
    (hQp : ∀ b, (∑ z, |lawDensity (Qb b) z|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a ≤ uQ b)
    (small : D.FS.Tag → (∀ b, DensityFibre.HPiece D L b) → Prop) :
    ∑ f : BlockAtom Bk J L → Bool,
      ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        ∑ j : D.FS.Tag, chainPart (small j)
          (fun φ => choiceWeight (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ)
          (fun φ => ∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
            ∑ z, |lawDensity (DensityFibre.bpieceLp D L Qb dec j b.1 (φ b.1)) z|)
          (fun φ => ∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
            ∑ z, |lawDensity (DensityFibre.bpieceLm D L Qb dec j b.1 (φ b.1)) z|) ≤
      (Fintype.card D.FS.Tag : ℝ) *
        ∏ b, (uQ b * (1 + ∑ i, (D.FS.dprice L b i + D.FS.vprice L b i)) +
          (1 + D.GB.uprice L b + ∑ i, (D.FS.dprice L b i + D.FS.vprice L b i))) := by
  have hpt : ∀ (f : BlockAtom Bk J L → Bool) (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag),
      chainPart (small j)
          (fun φ => choiceWeight (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ)
          (fun φ => ∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
            ∑ z, |lawDensity (DensityFibre.bpieceLp D L Qb dec j b.1 (φ b.1)) z|)
          (fun φ => ∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
            ∑ z, |lawDensity (DensityFibre.bpieceLm D L Qb dec j b.1 (φ b.1)) z|) ≤
        (∏ b, (if f b then uQ b else 1)) *
          ∑ φ : (∀ b, DensityFibre.HPiece D L b),
            choiceWeight (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ *
              ∏ b, DensityFibre.bpieceG D L b (φ b) := by
    intro f σ j
    have hU0 : 0 ≤ ∏ b, (if f b then uQ b else 1) := prod_nonneg fun b _ => by
      split_ifs
      · exact huQ b
      · exact zero_le_one
    refine (chainPart_le (small j) _ _ _
      (fun φ => (∏ b, DensityFibre.bpieceG D L b (φ b)) * ∏ b, (if f b then uQ b else 1))
      (fun φ => choiceWeight_nonneg' D L f σ j φ)
      (fun φ => mul_nonneg (prod_nonneg fun b _ => DensityFibre.bpieceG_nonneg D L b (φ b)) hU0)
      (fun φ => prod_nonneg fun b _ => sum_nonneg fun z _ => abs_nonneg _)
      (fun φ hw => piecePrice_plus_le_one D L hpair Qb hQ dec ha j f σ φ
        (coef_ne_zero_of_weight_ne_zero D L f σ j φ hw) hsel uQ hQp)
      (fun φ hw => piecePrice_minus_le_one D L hpair Qb hQ dec ha j f σ φ
        (coef_ne_zero_of_weight_ne_zero D L f σ j φ hw) hsel uQ hQp)).trans (le_of_eq ?_)
    rw [mul_sum]
    exact sum_congr rfl fun φ _ => by ring
  calc _ ≤ ∑ f : BlockAtom Bk J L → Bool,
      ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        ∑ j : D.FS.Tag, (∏ b, (if f b then uQ b else 1)) *
          ∑ φ : (∀ b, DensityFibre.HPiece D L b),
            choiceWeight (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ *
              ∏ b, DensityFibre.bpieceG D L b (φ b) :=
        sum_le_sum fun f _ => sum_le_sum fun σ _ => sum_le_sum fun j _ => hpt f σ j
    _ = ∑ j : D.FS.Tag, ∑ f : BlockAtom Bk J L → Bool,
      ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        (∏ b, (if f b then uQ b else 1)) *
          ∑ φ : (∀ b, DensityFibre.HPiece D L b),
            choiceWeight (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ *
              ∏ b, DensityFibre.bpieceG D L b (φ b) := by
        refine (sum_congr rfl fun f _ => Finset.sum_comm).trans ?_
        exact Finset.sum_comm
    _ ≤ ∑ _j : D.FS.Tag, ∏ b, (uQ b * (1 + ∑ i, (D.FS.dprice L b i + D.FS.vprice L b i)) +
          (1 + D.GB.uprice L b + ∑ i, (D.FS.dprice L b i + D.FS.vprice L b i))) :=
        sum_le_sum fun j _ => weight_total_le D L j uQ huQ
    _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]

end Concrete

end Sarkozy.SharpSums
