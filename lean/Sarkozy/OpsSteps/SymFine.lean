module

public import Sarkozy.OpsSteps.SymSwap
public import Sarkozy.OpsSteps.QMain

@[expose] public section

/-!
# The terms with `G` of the category `e_s`, from G1's coupled pieces (OPS-S)

`paper/sections/23_envelopes.tex`, proof of `lem:orbit-coupon`(i): "The terms with `G` keep the
sharp price"; `lem:sharp-first`.

G1's coupled pieces list the bracket records `κu_{𝔟,i}` one by one at the atoms outside the
support, so the split `Ñ₀ = (μ + ∑_{¬isG} κu) + ∑_{isG} κu` is a partition of the pieces:

* `gPiece`, `pset`, **`catLaw_eq_pieces`**: the law of an atom in the expanded term `T_{σ,Z}` is
  the sum of the pieces of its class (`G` pieces at `Z`, the others off `Z`);
* **`catInt_eq`**: so `T_{σ,Z}(Q)` is the sum of the piece energies `qInt` over the product set;
* **`abs_catT_le`**: hence `|T_{σ,Z}| ≤ K d_σ ∏_Z w ∏_{Zᶜ}(1 + v) + rQ_{σ,Z}`, with `rQ` the sum of
  the canonical remainders `qX` of the pieces of class `Z` (EC's main terms add up to the prices);
* **`sum_rQ_le`**: the classes are disjoint, so `∑_Z rQ_{σ,Z} ≤ ∑_g |c_g| qX_g`, the remainder that
  `QMain.rCan_class_sum` already sums.
-/

namespace Sarkozy.OpsSteps

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.E1Closure Sarkozy.EnvelopeInputsBlock
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame Sarkozy.BracketEnergy Sarkozy.EnvelopeSteps Sarkozy.Envelopes
open Sarkozy.TheoremC Sarkozy.Comparison Sarkozy.PaperFrame Sarkozy.RecordExpansion
  Sarkozy.RecordExpansion.Choice

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
  (isG : ∀ b : BlockAtom Bk J L, D.GB.Iu L b → Bool)

/-- The `G` pieces: the bracket records `κu_{𝔟,i}` with `isG`. -/
def gPiece (b : BlockAtom Bk J L) : CEPiece D L b → Bool
  | Sum.inl (some i) => isG b i
  | _ => false

/-- The pieces of an atom in the class `y` (`G` for `y = true`); all pieces at the support and at
the differences. -/
noncomputable def pset (ω : Choice (D.CL.T L)) (σ : ∀ b, Option (D.FS.Ib L b))
    (b : BlockAtom Bk J L) (y : Bool) : Finset (CEPiece D L b) :=
  if (σ b).isSome || (ω b).isSome then univ else univ.filter (fun x => gPiece D L isG b x = y)

omit [DecidableEq P] in
/-- **The law of an atom of `T_{σ,Z}` is the sum of the pieces of its class.** -/
theorem catLaw_eq_pieces (ω : Choice (D.CL.T L)) (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (σ : ∀ b, Option (D.FS.Ib L b)) (s : D.FS.Tag) (b : BlockAtom Bk J L) (y : Bool)
    (hy : y ∈ catSet D L (Choice.support ω) σ b) :
    catLaw D L isG (Choice.support ω) Qb σ b y =
      ∑ x ∈ pset D L isG ω σ b y,
        ecpieceCoef D L ω σ s b x • qK D L (qfOf D L (Choice.support ω) Qb) ω b x := by
  have hsupp : b ∈ Choice.support ω ↔ (ω b).isSome = true := mem_support_iff' D L ω b
  unfold pset
  by_cases hc : ((σ b).isSome || (ω b).isSome) = true
  · have hcs : catSet D L (Choice.support ω) σ b = {false} := by
      unfold catSet
      have : ((σ b).isSome || decide (b ∈ Choice.support ω)) = true := by
        rcases Bool.or_eq_true_iff.mp hc with h1 | h1
        · simp [h1]
        · simp [hsupp.mpr h1]
      simp [this]
    rw [hcs, mem_singleton] at hy
    subst hy
    rw [ite_eq_left hc, qSum_eq D L _ ω σ s b, ← sharpPiece_eq_qTerm D L ω Qb σ,
      sharpPiece_eq_sum D L isG (Choice.support ω) Qb σ b, hcs, sum_singleton]
  · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, Option.isSome_eq_false_iff,
      Option.isNone_iff_eq_none] at hc
    obtain ⟨hσ, hω⟩ := hc
    have hb : b ∉ Choice.support ω := by rw [hsupp, hω]; simp
    rw [ite_eq_right (by simp [hσ, hω]), sum_filter, Fintype.sum_sum_type, Fintype.sum_option,
      Fintype.sum_prod_type]
    have hinr : ∀ i z, ecpieceCoef D L ω σ s b (Sum.inr (i, z)) = 0 := by
      intro i z
      rcases z with _ | t <;> simp [ecpieceCoef, hσ]
    simp only [hinr, zero_smul, ite_self, sum_const_zero, add_zero]
    have h0 : ecpieceCoef D L ω σ s b (Sum.inl none) = 1 := by simp [ecpieceCoef, hσ]
    have h1 : ∀ i, ecpieceCoef D L ω σ s b (Sum.inl (some i)) = 1 := by
      intro i; simp [ecpieceCoef, hσ, hω]
    have hq0 : qK D L (qfOf D L (Choice.support ω) Qb) ω b (Sum.inl none) = D.R.law p L b := by
      simp [qK, hω, entryFactor]
    simp only [h0, h1, one_smul, hq0]
    unfold catLaw
    rw [hσ]
    simp only [Option.elim_none, hb, decide_false, Bool.false_eq_true, ↓reduceIte]
    cases y
    · simp only [gPiece, ↓reduceIte, Bool.false_eq_true]
      rw [sum_filter]
      simp only [qK]
      congr 1
    · simp only [gPiece, Bool.false_eq_true, ↓reduceIte, zero_add]
      rw [sum_filter]
      simp only [qK]
      refine sum_congr rfl fun i _ => ?_
      by_cases hi : isG b i = true
      · simp [hi]
      · simp only [Bool.not_eq_true] at hi
        simp [hi]

omit [DecidableEq P] in
/-- **`T_{σ,Z}(Q)` is the sum of its piece energies.** -/
theorem catInt_eq (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (σ : ∀ b, Option (D.FS.Ib L b))
    (s : D.FS.Tag) (f : BlockAtom Bk J L → Bool)
    (hf : f ∈ Fintype.piFinset (catSet D L (Choice.support ω) σ)) :
    diagonalIntegral (tensorLaw fun b => catLaw D L isG (Choice.support ω) Qb σ b (f b))
        (blockLift m₀ blk p L A) =
      ∑ g ∈ Fintype.piFinset (fun b => pset D L isG ω σ b (f b)),
        (∏ b, ecpieceCoef D L ω σ s b (g b)) *
          qInt D L (qfOf D L (Choice.support ω) Qb) A ω g := by
  classical
  have hL : (fun b => catLaw D L isG (Choice.support ω) Qb σ b (f b)) =
      fun b => ∑ x ∈ pset D L isG ω σ b (f b),
        ecpieceCoef D L ω σ s b x • qK D L (qfOf D L (Choice.support ω) Qb) ω b x :=
    funext fun b => catLaw_eq_pieces D L isG ω Qb σ s b (f b) (Fintype.mem_piFinset.mp hf b)
  rw [hL, tensorLaw_sum_finset, diagonalIntegral_sum]
  refine sum_congr rfl fun g _ => ?_
  rw [tensorLaw_smul (fun b => ecpieceCoef D L ω σ s b (g b))
    (fun b => qK D L (qfOf D L (Choice.support ω) Qb) ω b (g b))]
  rfl

/-- The invariant price `v_𝔟 = ∑_{¬isG} ‖κu‖ q^{2a}` of an atom off the support. -/
noncomputable def vP (ω : Choice (D.CL.T L)) (b : BlockAtom Bk J L) : ℝ :=
  if (ω b).isSome then 0 else ∑ i ∈ univ.filter (fun i => isG b i = false),
    mass (D.GB.κu L b i) * TheoremCBlock.selectionFactor a p D.S.selPre L b

/-- The generic price `w_𝔟 = ∑_{isG} ‖κu‖ q^{2a}` of an atom off the support. -/
noncomputable def wP (ω : Choice (D.CL.T L)) (b : BlockAtom Bk J L) : ℝ :=
  if (ω b).isSome then 0 else ∑ i ∈ univ.filter (fun i => isG b i = true),
    mass (D.GB.κu L b i) * TheoremCBlock.selectionFactor a p D.S.selPre L b

omit [DecidableEq P] in
theorem vP_nonneg (ω : Choice (D.CL.T L)) (b : BlockAtom Bk J L) : 0 ≤ vP D L isG ω b := by
  unfold vP
  split_ifs
  · exact le_rfl
  · exact sum_nonneg fun i _ => mul_nonneg
      (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.GB.κu_pos L b i).1)
      (D.selectionFactor_nonneg L b)

omit [DecidableEq P] in
theorem wP_nonneg (ω : Choice (D.CL.T L)) (b : BlockAtom Bk J L) : 0 ≤ wP D L isG ω b := by
  unfold wP
  split_ifs
  · exact le_rfl
  · exact sum_nonneg fun i _ => mul_nonneg
      (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.GB.κu_pos L b i).1)
      (D.selectionFactor_nonneg L b)

omit [DecidableEq P] in
/-- **The prices of the pieces of one atom of `T_{σ,Z}`.** -/
theorem atom_pset_le (ω : Choice (D.CL.T L)) (σ : ∀ b, Option (D.FS.Ib L b)) (s : D.FS.Tag)
    (b : BlockAtom Bk J L) (y : Bool) (hy : y ∈ catSet D L (Choice.support ω) σ b) :
    ∑ x ∈ pset D L isG ω σ b y, |ecpieceCoef D L ω σ s b x| * ecpieceG D L ω b x ≤
      (if (ω b).isSome then TheoremCBlock.selectionFactor a p D.S.selPre L b else 1) *
        ((σ b).elim 1
            (fun i => if D.FS.tag L b i = s then D.FS.dprice L b i else D.FS.vprice L b i) *
          (if y then wP D L isG ω b else 1 + vP D L isG ω b)) := by
  have hsupp : b ∈ Choice.support ω ↔ (ω b).isSome = true := mem_support_iff' D L ω b
  have hA0 : 0 ≤ (if (ω b).isSome then TheoremCBlock.selectionFactor a p D.S.selPre L b
      else 1) := by
    split_ifs
    · exact D.selectionFactor_nonneg L b
    · exact zero_le_one
  unfold pset
  by_cases hc : ((σ b).isSome || (ω b).isSome) = true
  · have hcs : catSet D L (Choice.support ω) σ b = {false} := by
      unfold catSet
      have : ((σ b).isSome || decide (b ∈ Choice.support ω)) = true := by
        rcases Bool.or_eq_true_iff.mp hc with h1 | h1
        · simp [h1]
        · simp [hsupp.mpr h1]
      simp [this]
    rw [hcs, mem_singleton] at hy
    subst hy
    rw [ite_eq_left hc]
    refine (esum_cpieceWeight_le D L ω σ s b).trans (mul_le_mul_of_nonneg_left ?_ hA0)
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hv0 := vP_nonneg D L isG ω b
    rcases hσ : σ b with _ | i
    · have hω : (ω b).isSome = true := by simpa [hσ] using hc
      simp only [Option.elim_none, selPriceU, hω, ↓reduceIte, add_zero, one_mul, vP]
      exact le_rfl
    · simp only [Option.elim_some]
      have hF : 0 ≤ (if D.FS.tag L b i = s then D.FS.dprice L b i else D.FS.vprice L b i) := by
        split_ifs
        · exact D.dprice_nonneg L b i
        · exact D.vprice_nonneg L b i
      nlinarith
  · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, Option.isSome_eq_false_iff,
      Option.isNone_iff_eq_none] at hc
    obtain ⟨hσ, hω⟩ := hc
    rw [ite_eq_right (by simp [hσ, hω]), sum_filter, Fintype.sum_sum_type, Fintype.sum_option,
      Fintype.sum_prod_type]
    have hinr : ∀ i z, ecpieceCoef D L ω σ s b (Sum.inr (i, z)) = 0 := by
      intro i z
      rcases z with _ | t <;> simp [ecpieceCoef, hσ]
    simp only [hinr, abs_zero, zero_mul, ite_self, sum_const_zero, add_zero]
    have h0 : ecpieceCoef D L ω σ s b (Sum.inl none) = 1 := by simp [ecpieceCoef, hσ]
    have h1 : ∀ i, ecpieceCoef D L ω σ s b (Sum.inl (some i)) = 1 := by
      intro i; simp [ecpieceCoef, hσ, hω]
    have hg0 : ecpieceG D L ω b (Sum.inl none) = 1 := by simp [ecpieceG, hω]
    simp only [h0, h1, abs_one, one_mul, hg0, hσ, hω, Option.elim_none, Option.isSome_none,
      Bool.false_eq_true, ↓reduceIte, mul_one, vP, wP]
    cases y
    · simp only [gPiece, ↓reduceIte, Bool.false_eq_true]
      rw [sum_filter]
      simp only [ecpieceG]
      exact le_rfl
    · simp only [gPiece, Bool.false_eq_true, ↓reduceIte, zero_add]
      rw [sum_filter]
      simp only [ecpieceG]
      exact le_rfl

/-- **The remainder of `T_{σ,Z}`**: the canonical remainders `qX` of its pieces, for the two
tensors of the orbit average. -/
noncomputable def rQ (εE : ℕ → ℝ) (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (Q₁ Q₂ : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (s : D.FS.Tag)
    (σ : ∀ b, Option (D.FS.Ib L b)) (f : BlockAtom Bk J L → Bool) : ℝ :=
  if f ∈ Fintype.piFinset (catSet D L (Choice.support ω) σ) then
    (1 / 2 : ℝ) * ∑ g ∈ Fintype.piFinset (fun b => pset D L isG ω σ b (f b)),
      (∏ b, |ecpieceCoef D L ω σ s b (g b)|) *
        (qX D L (qfOf D L (Choice.support ω) Q₁) εE A ω σ s g +
          qX D L (qfOf D L (Choice.support ω) Q₂) εE A ω σ s g)
  else 0

omit [DecidableEq P] in
/-- **One tensor of a term `T_{σ,Z}`, from its pieces.** -/
theorem abs_catInt_le (εE : ℕ → ℝ) (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (s : D.FS.Tag)
    (σ : ∀ b, Option (D.FS.Ib L b)) (hs : 1 ≤ countVec (D.FS.tag L) σ s)
    (f : BlockAtom Bk J L → Bool) (hf : f ∈ Fintype.piFinset (catSet D L (Choice.support ω) σ)) :
    |diagonalIntegral (tensorLaw fun b => catLaw D L isG (Choice.support ω) Qb σ b (f b))
        (blockLift m₀ blk p L A)| ≤
      ((1 + εE L) * D.Y L A) *
          ∏ b, ∑ x ∈ pset D L isG ω σ b (f b), |ecpieceCoef D L ω σ s b x| * ecpieceG D L ω b x +
        ∑ g ∈ Fintype.piFinset (fun b => pset D L isG ω σ b (f b)),
          (∏ b, |ecpieceCoef D L ω σ s b (g b)|) *
            qX D L (qfOf D L (Choice.support ω) Qb) εE A ω σ s g := by
  rw [catInt_eq D L isG A ω Qb σ s f hf, prod_univ_sum, mul_sum, ← sum_add_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun g _ => ?_)
  rw [abs_mul, abs_prod]
  have hX : |qInt D L (qfOf D L (Choice.support ω) Qb) A ω g| ≤
      coupMain D εE L A ω g + qX D L (qfOf D L (Choice.support ω) Qb) εE A ω σ s g := by
    unfold qX
    simp only [hs, ↓reduceIte]
    linarith [le_max_right 0 (|qInt D L (qfOf D L (Choice.support ω) Qb) A ω g| -
      coupMain D εE L A ω g)]
  have hc0 : 0 ≤ ∏ b, |ecpieceCoef D L ω σ s b (g b)| := prod_nonneg fun b _ => abs_nonneg _
  have hcm : coupMain D εE L A ω g = (∏ b, ecpieceG D L ω b (g b)) * ((1 + εE L) * D.Y L A) :=
    rfl
  calc (∏ b, |ecpieceCoef D L ω σ s b (g b)|) * |qInt D L (qfOf D L (Choice.support ω) Qb) A ω g|
      ≤ (∏ b, |ecpieceCoef D L ω σ s b (g b)|) *
          (coupMain D εE L A ω g + qX D L (qfOf D L (Choice.support ω) Qb) εE A ω σ s g) :=
        mul_le_mul_of_nonneg_left hX hc0
    _ = _ := by
        rw [hcm, prod_mul_distrib]
        ring

omit [DecidableEq P] in
/-- **The terms of the category `e_s` with the sharp price** (`lem:sharp-first` with the `G` atoms
priced apart): for `σ` with a difference of tag `s`,
`|T_{σ,Z}| ≤ (1 + ε) C_X Y · d_σ ∏_c (Z ∋ c ? w_c : 1 + v_c) + rQ_{σ,Z}`. -/
theorem abs_catT_le (εE : ℕ → ℝ) (hε0 : ∀ L, 0 ≤ εE L) (A : Finset ℤ) (hY : 0 ≤ D.Y L A)
    (ω : Choice (D.CL.T L)) (Q₁ Q₂ : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (s : D.FS.Tag) (σ : ∀ b, Option (D.FS.Ib L b)) (hs : 1 ≤ countVec (D.FS.tag L) σ s)
    (f : BlockAtom Bk J L → Bool) :
    |catT D L A isG (Choice.support ω) Q₁ Q₂ σ f| ≤
      ((1 + εE L) * (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
          D.Y L A) *
        (tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (fun _ => 0) s σ *
          ∏ c, (if f c then wP D L isG ω c else 1 + vP D L isG ω c)) +
        rQ D L isG εE A ω Q₁ Q₂ s σ f := by
  have hK : 0 ≤ (1 + εE L) * D.Y L A := mul_nonneg (by linarith [hε0 L]) hY
  have hsf0 : 0 ≤ ∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b :=
    prod_nonneg fun b _ => D.selectionFactor_nonneg L b
  have hd0 : ∀ b i, 0 ≤ D.FS.dprice L b i := fun b i => D.dprice_nonneg L b i
  have hv0 : ∀ b i, 0 ≤ D.FS.vprice L b i := fun b i => D.vprice_nonneg L b i
  have htw0 := tagWeight_nonneg (D.FS.tag L) hd0 hv0 (fun _ => le_rfl) s σ
  have hC0 : 0 ≤ ∏ c, (if f c then wP D L isG ω c else 1 + vP D L isG ω c) :=
    prod_nonneg fun c _ => by
      split_ifs
      · exact wP_nonneg D L isG ω c
      · linarith [vP_nonneg D L isG ω c]
  unfold catT rQ
  split_ifs with hf
  · -- the per-atom prices
    have hprod : ∏ b, ∑ x ∈ pset D L isG ω σ b (f b),
        |ecpieceCoef D L ω σ s b x| * ecpieceG D L ω b x ≤
        (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
          (tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (fun _ => 0) s σ *
            ∏ c, (if f c then wP D L isG ω c else 1 + vP D L isG ω c)) := by
      refine (prod_le_prod₀ (fun b _ => sum_nonneg fun x _ => mul_nonneg (abs_nonneg _)
        (ecpieceG_nonneg D L ω b x)) fun b _ =>
          atom_pset_le D L isG ω σ s b (f b) (Fintype.mem_piFinset.mp hf b)).trans (le_of_eq ?_)
      rw [prod_mul_distrib, prod_mul_distrib, prod_selFactor_eq D L ω]
      congr 2
      unfold tagWeight
      refine prod_congr rfl fun b _ => ?_
      rcases σ b with _ | i
      · simp
      · rfl
    have h1 := abs_catInt_le D L isG εE A ω Q₁ s σ hs f hf
    have h2 := abs_catInt_le D L isG εE A ω Q₂ s σ hs f hf
    have hP := mul_le_mul_of_nonneg_left hprod hK
    set T₁ := diagonalIntegral (tensorLaw fun b => catLaw D L isG (Choice.support ω) Q₁ σ b (f b))
      (blockLift m₀ blk p L A)
    set T₂ := diagonalIntegral (tensorLaw fun b => catLaw D L isG (Choice.support ω) Q₂ σ b (f b))
      (blockLift m₀ blk p L A)
    have habs : |(1 / 2 : ℝ) * (T₁ + T₂)| ≤ (1 / 2 : ℝ) * (|T₁| + |T₂|) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
    have hsplit : (1 / 2 : ℝ) * ∑ g ∈ Fintype.piFinset (fun b => pset D L isG ω σ b (f b)),
        (∏ b, |ecpieceCoef D L ω σ s b (g b)|) *
          (qX D L (qfOf D L (Choice.support ω) Q₁) εE A ω σ s g +
            qX D L (qfOf D L (Choice.support ω) Q₂) εE A ω σ s g) =
        (1 / 2 : ℝ) * (∑ g ∈ Fintype.piFinset (fun b => pset D L isG ω σ b (f b)),
          (∏ b, |ecpieceCoef D L ω σ s b (g b)|) *
            qX D L (qfOf D L (Choice.support ω) Q₁) εE A ω σ s g +
          ∑ g ∈ Fintype.piFinset (fun b => pset D L isG ω σ b (f b)),
          (∏ b, |ecpieceCoef D L ω σ s b (g b)|) *
            qX D L (qfOf D L (Choice.support ω) Q₂) εE A ω σ s g) := by
      rw [← sum_add_distrib]
      congr 1
      exact sum_congr rfl fun g _ => by ring
    rw [hsplit]
    have hre : (1 + εE L) * D.Y L A *
        ((∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
          (tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (fun _ => 0) s σ *
            ∏ c, (if f c then wP D L isG ω c else 1 + vP D L isG ω c))) =
        ((1 + εE L) * (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
          D.Y L A) *
        (tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (fun _ => 0) s σ *
          ∏ c, (if f c then wP D L isG ω c else 1 + vP D L isG ω c)) := by ring
    linarith
  · rw [abs_zero, add_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith [hε0 L]) hsf0) hY)
      (mul_nonneg htw0 hC0)

omit [DecidableEq P] in
/-- **The remainders of the terms `T_{σ,Z}` add up to at most the piece remainders of `σ`** (the
classes `Z` are disjoint sets of pieces). -/
theorem sum_rQ_le (εE : ℕ → ℝ) (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (Q₁ Q₂ : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (s : D.FS.Tag)
    (σ : ∀ b, Option (D.FS.Ib L b)) :
    ∑ f, rQ D L isG εE A ω Q₁ Q₂ s σ f ≤
      (1 / 2 : ℝ) * ∑ g : (∀ b, CEPiece D L b), (∏ b, |ecpieceCoef D L ω σ s b (g b)|) *
        (qX D L (qfOf D L (Choice.support ω) Q₁) εE A ω σ s g +
          qX D L (qfOf D L (Choice.support ω) Q₂) εE A ω σ s g) := by
  classical
  have hsupp : ∀ b, b ∈ Choice.support ω ↔ (ω b).isSome = true := mem_support_iff' D L ω
  have hX0 : ∀ g : (∀ b, CEPiece D L b), 0 ≤ (∏ b, |ecpieceCoef D L ω σ s b (g b)|) *
      (qX D L (qfOf D L (Choice.support ω) Q₁) εE A ω σ s g +
        qX D L (qfOf D L (Choice.support ω) Q₂) εE A ω σ s g) := fun g =>
    mul_nonneg (prod_nonneg fun b _ => abs_nonneg _)
      (add_nonneg (qX_nonneg D L _ εE A ω σ s g) (qX_nonneg D L _ εE A ω σ s g))
  unfold rQ
  rw [sum_ite_mem univ, univ_inter, ← mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  rw [← sum_biUnion]
  · exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun g _ _ => hX0 g
  · intro f₁ hf₁ f₂ hf₂ hne
    rw [Function.onFun, disjoint_left]
    intro g hg₁ hg₂
    apply hne
    funext b
    have hc₁ := Fintype.mem_piFinset.mp (mem_coe.mp hf₁) b
    have hc₂ := Fintype.mem_piFinset.mp (mem_coe.mp hf₂) b
    have hg₁b := Fintype.mem_piFinset.mp hg₁ b
    have hg₂b := Fintype.mem_piFinset.mp hg₂ b
    unfold pset at hg₁b hg₂b
    unfold catSet at hc₁ hc₂
    by_cases hc : ((σ b).isSome || (ω b).isSome) = true
    · have hcs : ((σ b).isSome || decide (b ∈ Choice.support ω)) = true := by
        rcases Bool.or_eq_true_iff.mp hc with h1 | h1
        · simp [h1]
        · simp [(hsupp b).mpr h1]
      simp only [hcs, ↓reduceIte, mem_singleton] at hc₁ hc₂
      rw [hc₁, hc₂]
    · simp only [Bool.not_eq_true] at hc
      simp only [hc, Bool.false_eq_true, ↓reduceIte, mem_filter, mem_univ, true_and]
        at hg₁b hg₂b
      rw [← hg₁b, ← hg₂b]

end Sarkozy.OpsSteps
