module

public import Sarkozy.E1Closure.AtomSums

@[expose] public section

/-!
# `lem:record:density-lp` at the (E1) terms with a large union, proved (EC)

EC, 8 November 2026. **`e1Large_proved`**: for every comparison datum with `a ≥ 0` there is
`c ≥ 0` with `E1Large D c`: at every large `L` and every `A`,

`∑_ω π̃_ω (∑_{f, q_E > N^τ} |𝔈_{ω,f}| + ∑_{σ ≠ ∅} ∑_j ∑_{f, q_E > N^τ} ∏_𝔟 |c_𝔟| |𝔈_{ω,f}|)
  ≤ c L^{-σ} α`.

This is the paper's proof of `lem:record:density-lp`, with `η_𝔟` the prices of the selected laws
(the post-reduction prices `π̃`, the masses of the bracket records and of the first-stage pieces):

* **`blockLift_moment_le`** (`lem:record:lift-moments`(c), DC1's `input_moment_le_density` at
  `r = 36`, `ε = 1/2000`, `D₀ = 1`): `‖F_A‖_{72}^{72} ≤ |X₀|^{72} C Q^{1/2000} K α` for the lift
  `F_A` read on the block labels;
* Hölder per term (`abs_diag_le_dom`), with the whole differences dominated by `κ' + κ`;
* Rankin per term (`rankin_term`) and the factorization over the atoms (`sum_sum_prod`); for the
  coupled pieces, first the sum over `σ` (`sum_abs_ccoef_le`);
* the per-atom sums (`subAtom_le`, `coupAtom_le`) and `Π_H ≤ e^{2 D.SM.bound}` (LP's
  `prod_atomPr_le_exp`, `def:cp8`(c));
* (S4) through LP's `final_le` (`Q^{1/2000} N^{-τ/4} ≤ L^{-1/825}`).

The bound holds at every large `L` and every `A`; no counterexample hypothesis is used. The
constant is `c = (1 + |𝔗|) |X₀|^{72} C K e^{2 D.SM.bound}`.
-/

namespace Sarkozy.E1Closure

open Filter Finset Function
open scoped BigOperators
open Sarkozy.EnvelopeInputsBlock Sarkozy.EnvelopeInputs
open Sarkozy.BlockFrame
open Sarkozy.TheoremC Sarkozy.Comparison Sarkozy.PaperFrame Sarkozy.RecordExpansion
  Sarkozy.RecordExpansion.Choice Sarkozy.Structured ReflectionCut
open Sarkozy.Functional (paperCutoff one_le_paperCutoff stageTau)
open Sarkozy.LargeSums (atomQR atomQR_nonneg atomPr)
open Sarkozy.FourierArithmetic (ResidueSpace)

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

omit [DecidableEq P] in
/-- **The `72`-th moment of the lift `F_A` on the block labels** (`lem:record:lift-moments`(c)). -/
theorem blockLift_moment_le :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℕ, 2 ^ 20 * blockScale ≤ L → (∀ j, (p L j).Prime) →
      Injective (p L) → ∀ A : Finset ℤ,
      (FiniteLaw.uniform (∀ b : BlockAtom Bk J L, BlockLabel m₀ blk p L b)).moment 72
          (blockLift m₀ blk p L A) ≤
        1 ^ 72 * ((Fintype.card (ResidueSpace m₀) : ℝ) ^ 72 * C *
          paperCutoff (blockScale * L) ^ ((1 : ℝ) / 2000) *
          ((blockScale : ℝ) * density (blockScale * L) A)) := by
  obtain ⟨C, hC, hc⟩ := Sarkozy.DensityDC.input_moment_le_density 36 (by norm_num)
    ((1 : ℝ) / 2000) (by norm_num)
  refine ⟨C, hC, fun L hL hp hinj A => ?_⟩
  have hK : 1 ≤ blockScale := by norm_num [blockScale]
  have hL1 : 1 ≤ L := le_trans (by norm_num [blockScale]) hL
  have hKL : 1 ≤ blockScale * L := Nat.mul_pos (by omega) (by omega)
  have hLM : L ≤ blockScale * L := Nat.le_mul_of_pos_left L (by omega)
  obtain ⟨hf1, hf2⟩ := Sarkozy.CancellationSteps.floor_cutoff_bounds hK hL
  have key := hc m₀ (p L) hp hinj (paperCutoff (blockScale * L)) (one_le_paperCutoff hKL) 0
    (M := blockScale * L) (L := L) (M0 := 1) hL1 hLM (by omega) (by omega) (D0 := 1) le_rfl
    (0 : ZMod 1) A
  simp only [show (2 * 36 : ℕ) = 72 from rfl, Nat.cast_ofNat, Nat.cast_one] at key
  refine le_of_eq_of_le ?_ key
  rw [← Sarkozy.LargeSums.moment_uniform_equiv (blockGroupEquiv m₀ blk p L)]
  congr 1
  funext x
  rw [blockLift_eq, Equiv.apply_symm_apply, Sarkozy.EnvelopeInputs.wholeLift_eq_input_one,
    zero_add, zero_add]

section Sums

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)

omit [DecidableEq P] in
theorem subQ_nonneg (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType)) (y : Bool) :
    0 ≤ subQ D L b o y := by
  unfold subQ
  split_ifs
  · exact atomQR_nonneg D L b
  · exact zero_le_one

omit [DecidableEq P] in
theorem coupQ_nonneg (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType))
    (x : CEPiece D L b) : 0 ≤ coupQ D L b o x := by
  rcases x with (_ | i) | ⟨i, _ | t⟩ <;> unfold coupQ <;> try split_ifs
  all_goals first | exact atomQR_nonneg D L b | exact zero_le_one

/-- The per-atom bound `1 + 2 q_𝔟^{1/4} Pr_𝔟`. -/
noncomputable def atomW (b : BlockAtom Bk J L) : ℝ :=
  1 + 2 * (atomQR D L b ^ ((1 : ℝ) / 4) * atomPr D L (TheoremCBlock.Structured.wrapInc D L) b)

omit [DecidableEq P] in
/-- **The subset terms with a large union** (`lem:record:density-lp`): at fixed `L`, `A`, with
the moment bound `B` of the lift. -/
theorem sub_large_le (A : Finset ℤ) (hp : ∀ j, (p L j).Prime) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : (FiniteLaw.uniform (∀ b : BlockAtom Bk J L, BlockLabel m₀ blk p L b)).moment 72
      (blockLift m₀ blk p L A) ≤ B) (hT : 0 < stageT L) :
    ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω), monomial (D.CL.πt L) ω *
        ∑ f, (if SubSmall D L ω f then 0 else |subInt D L A ω f|) ≤
      B * (stageT L ^ (-((1 : ℝ) / 4)) * ∏ b, atomW D L b) := by
  set T := stageT L with hTdef
  set g : ∀ b : BlockAtom Bk J L, Option (D.CL.T L b × ChangeType) → Bool → ℝ := fun b o y =>
    entryPrice (D.CL.πt L b) o * mass (subLaw D L b o y) * subQ D L b o y ^ ((1 : ℝ) / 4)
    with hg
  have hw0 : ∀ b o y, 0 ≤ entryPrice (D.CL.πt L b) o * mass (subLaw D L b o y) := fun b o y =>
    mul_nonneg (entryPrice_nonneg (D.CL.πt_nonneg L b) o)
      (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (isPositiveRecord_subLaw D L hp b o y).1)
  have hg0 : ∀ b o y, 0 ≤ g b o y := fun b o y =>
    mul_nonneg (hw0 b o y) (Real.rpow_nonneg (subQ_nonneg D L b o y) _)
  have hT4 : 0 ≤ T ^ (-((1 : ℝ) / 4)) := Real.rpow_nonneg hT.le _
  have hterm : ∀ (ω : Choice (D.CL.T L)) (f : BlockAtom Bk J L → Bool),
      monomial (D.CL.πt L) ω * (if SubSmall D L ω f then 0 else |subInt D L A ω f|) ≤
        B * (T ^ (-((1 : ℝ) / 4)) * ∏ b, g b (ω b) (f b)) := by
    intro ω f
    split_ifs with hs
    · rw [mul_zero]
      exact mul_nonneg hB0 (mul_nonneg hT4 (prod_nonneg fun b _ => hg0 b (ω b) (f b)))
    · have h1 : |subInt D L A ω f| ≤ (∏ b, mass (subLaw D L b (ω b) (f b))) * B :=
        abs_diag_le_dom _ _ (fun b => isPositiveRecord_subLaw D L hp b (ω b) (f b))
          (fun b z => subLaw_dom D L hp b (ω b) (f b) z) _ hB
      have h2 := rankin_term univ
        (fun b => entryPrice (D.CL.πt L b) (ω b) * mass (subLaw D L b (ω b) (f b)))
        (fun b => subQ D L b (ω b) (f b)) (fun b _ => hw0 b (ω b) (f b))
        (fun b _ => subQ_nonneg D L b (ω b) (f b)) hT (lt_of_not_ge hs)
      have hm : monomial (D.CL.πt L) ω = ∏ b, entryPrice (D.CL.πt L b) (ω b) := rfl
      calc monomial (D.CL.πt L) ω * |subInt D L A ω f|
          ≤ monomial (D.CL.πt L) ω * ((∏ b, mass (subLaw D L b (ω b) (f b))) * B) :=
            mul_le_mul_of_nonneg_left h1 (monomial_nonneg (D.CL.πt_nonneg L) ω)
        _ = B * ∏ b, (entryPrice (D.CL.πt L b) (ω b) * mass (subLaw D L b (ω b) (f b))) := by
            rw [hm, prod_mul_distrib]
            ring
        _ ≤ B * (T ^ (-((1 : ℝ) / 4)) * ∏ b, g b (ω b) (f b)) :=
            mul_le_mul_of_nonneg_left h2 hB0
  calc ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω), monomial (D.CL.πt L) ω *
        ∑ f, (if SubSmall D L ω f then 0 else |subInt D L A ω f|)
      ≤ ∑ ω : Choice (D.CL.T L), monomial (D.CL.πt L) ω *
        ∑ f, (if SubSmall D L ω f then 0 else |subInt D L A ω f|) := by
        refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun ω _ _ =>
          mul_nonneg (monomial_nonneg (D.CL.πt_nonneg L) ω) (sum_nonneg fun f _ => ?_)
        split_ifs
        · exact le_rfl
        · exact abs_nonneg _
    _ = ∑ ω : Choice (D.CL.T L), ∑ f : BlockAtom Bk J L → Bool, monomial (D.CL.πt L) ω *
        (if SubSmall D L ω f then 0 else |subInt D L A ω f|) := by
        simp only [mul_sum]
    _ ≤ ∑ ω : Choice (D.CL.T L), ∑ f : BlockAtom Bk J L → Bool,
        B * (T ^ (-((1 : ℝ) / 4)) * ∏ b, g b (ω b) (f b)) :=
        sum_le_sum fun ω _ => sum_le_sum fun f _ => hterm ω f
    _ = B * (T ^ (-((1 : ℝ) / 4)) * ∏ b, ∑ o, ∑ y, g b o y) := by
        rw [← sum_sum_prod g]
        simp only [mul_sum]
    _ ≤ B * (T ^ (-((1 : ℝ) / 4)) * ∏ b, atomW D L b) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hT4) hB0
        exact prod_le_prod₀ (fun b _ => sum_nonneg fun o _ => sum_nonneg fun y _ => hg0 b o y)
          fun b _ => subAtom_le D L b

omit [DecidableEq P] in
/-- The sum over the first-stage choices of a piece's coefficients is at most its
compatibility with the selection. -/
theorem sum_prod_abs_coef_le (ω : Choice (D.CL.T L)) (j : D.FS.Tag) (f : ∀ b, CEPiece D L b) :
    ∑ σ : (∀ b, Option (D.FS.Ib L b)), ∏ b, |ecpieceCoef D L ω σ j b (f b)| ≤
      ∏ b, compat D L b (ω b) (f b) := by
  simp only [ecpieceCoef_eq]
  rw [← Fintype.prod_sum (fun b s => |ccoef D L b (ω b) s j (f b)|)]
  exact prod_le_prod₀ (fun b _ => sum_nonneg fun s _ => abs_nonneg _)
    fun b _ => sum_abs_ccoef_le D L b (ω b) j (f b)

omit [DecidableEq P] in
/-- **The coupled pieces with a large union** (`lem:record:density-lp`): at fixed `L`, `A`, with
the moment bound `B` of the lift. -/
theorem coup_large_le (A : Finset ℤ) (hp : ∀ j, (p L j).Prime) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : (FiniteLaw.uniform (∀ b : BlockAtom Bk J L, BlockLabel m₀ blk p L b)).moment 72
      (blockLift m₀ blk p L A) ≤ B) (hT : 0 < stageT L) :
    ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω), monomial (D.CL.πt L) ω *
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          ∑ j, ∑ f, (∏ b, |ecpieceCoef D L ω σ j b (f b)|) *
            (if CoupSmall D L ω f then 0 else |coupInt D L A ω f|) ≤
      (Fintype.card D.FS.Tag : ℝ) * (B * (stageT L ^ (-((1 : ℝ) / 4)) * ∏ b, atomW D L b)) := by
  set T := stageT L with hTdef
  set G : Choice (D.CL.T L) → (∀ b, CEPiece D L b) → ℝ := fun ω f =>
    if CoupSmall D L ω f then 0 else |coupInt D L A ω f| with hG
  have hG0 : ∀ ω f, 0 ≤ G ω f := fun ω f => by
    simp only [hG]
    split_ifs
    · exact le_rfl
    · exact abs_nonneg _
  set g : ∀ b : BlockAtom Bk J L, Option (D.CL.T L b × ChangeType) → CEPiece D L b → ℝ :=
    fun b o x => entryPrice (D.CL.πt L b) o * compat D L b o x * mass (cDom D L b o x) *
      coupQ D L b o x ^ ((1 : ℝ) / 4) with hg
  have hw0 : ∀ b o x, 0 ≤ entryPrice (D.CL.πt L b) o * compat D L b o x * mass (cDom D L b o x) :=
    fun b o x => mul_nonneg (mul_nonneg (entryPrice_nonneg (D.CL.πt_nonneg L b) o)
      (compat_nonneg D L b o x))
      (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (isPositiveRecord_cDom D L hp b o x).1)
  have hg0 : ∀ b o x, 0 ≤ g b o x := fun b o x =>
    mul_nonneg (hw0 b o x) (Real.rpow_nonneg (coupQ_nonneg D L b o x) _)
  have hT4 : 0 ≤ T ^ (-((1 : ℝ) / 4)) := Real.rpow_nonneg hT.le _
  -- the sum over `σ` first
  have hσ : ∀ ω : Choice (D.CL.T L),
      ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        ∑ j, ∑ f, (∏ b, |ecpieceCoef D L ω σ j b (f b)|) * G ω f ≤
      ∑ j : D.FS.Tag, ∑ f : (∀ b, CEPiece D L b), (∏ b, compat D L b (ω b) (f b)) * G ω f := by
    intro ω
    calc _ ≤ ∑ σ : (∀ b, Option (D.FS.Ib L b)),
          ∑ j, ∑ f, (∏ b, |ecpieceCoef D L ω σ j b (f b)|) * G ω f :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun σ _ _ =>
            sum_nonneg fun j _ => sum_nonneg fun f _ =>
              mul_nonneg (prod_nonneg fun b _ => abs_nonneg _) (hG0 ω f)
      _ = ∑ j : D.FS.Tag, ∑ f : (∀ b, CEPiece D L b),
          (∑ σ : (∀ b, Option (D.FS.Ib L b)), ∏ b, |ecpieceCoef D L ω σ j b (f b)|) * G ω f := by
          rw [sum_comm]
          refine sum_congr rfl fun j _ => ?_
          rw [sum_comm]
          simp only [sum_mul]
      _ ≤ _ := sum_le_sum fun j _ => sum_le_sum fun f _ =>
          mul_le_mul_of_nonneg_right (sum_prod_abs_coef_le D L ω j f) (hG0 ω f)
  have hterm : ∀ (ω : Choice (D.CL.T L)) (f : ∀ b, CEPiece D L b),
      monomial (D.CL.πt L) ω * ((∏ b, compat D L b (ω b) (f b)) * G ω f) ≤
        B * (T ^ (-((1 : ℝ) / 4)) * ∏ b, g b (ω b) (f b)) := by
    intro ω f
    simp only [hG]
    split_ifs with hs
    · rw [mul_zero, mul_zero]
      exact mul_nonneg hB0 (mul_nonneg hT4 (prod_nonneg fun b _ => hg0 b (ω b) (f b)))
    · have hK : (fun b => ecpieceK D L ω b (f b)) = fun b => cK D L b (ω b) (f b) :=
        funext fun b => ecpieceK_eq D L ω b (f b)
      have h1 : |coupInt D L A ω f| ≤ (∏ b, mass (cDom D L b (ω b) (f b))) * B := by
        unfold coupInt
        rw [hK]
        exact abs_diag_le_dom _ _ (fun b => isPositiveRecord_cDom D L hp b (ω b) (f b))
          (fun b z => cK_dom D L hp b (ω b) (f b) z) _ hB
      have h2 := rankin_term univ
        (fun b => entryPrice (D.CL.πt L b) (ω b) * compat D L b (ω b) (f b) *
          mass (cDom D L b (ω b) (f b)))
        (fun b => coupQ D L b (ω b) (f b)) (fun b _ => hw0 b (ω b) (f b))
        (fun b _ => coupQ_nonneg D L b (ω b) (f b)) hT (lt_of_not_ge hs)
      have hm : monomial (D.CL.πt L) ω = ∏ b, entryPrice (D.CL.πt L b) (ω b) := rfl
      have hc0 : 0 ≤ ∏ b, compat D L b (ω b) (f b) :=
        prod_nonneg fun b _ => compat_nonneg D L b (ω b) (f b)
      calc monomial (D.CL.πt L) ω * ((∏ b, compat D L b (ω b) (f b)) * |coupInt D L A ω f|)
          ≤ monomial (D.CL.πt L) ω * ((∏ b, compat D L b (ω b) (f b)) *
              ((∏ b, mass (cDom D L b (ω b) (f b))) * B)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hc0)
              (monomial_nonneg (D.CL.πt_nonneg L) ω)
        _ = B * ∏ b, (entryPrice (D.CL.πt L b) (ω b) * compat D L b (ω b) (f b) *
              mass (cDom D L b (ω b) (f b))) := by
            rw [hm, prod_mul_distrib, prod_mul_distrib]
            ring
        _ ≤ B * (T ^ (-((1 : ℝ) / 4)) * ∏ b, g b (ω b) (f b)) :=
            mul_le_mul_of_nonneg_left h2 hB0
  have hper : ∀ j : D.FS.Tag, ∑ ω : Choice (D.CL.T L), ∑ f : (∀ b, CEPiece D L b),
      monomial (D.CL.πt L) ω * ((∏ b, compat D L b (ω b) (f b)) * G ω f) ≤
      B * (T ^ (-((1 : ℝ) / 4)) * ∏ b, atomW D L b) := by
    intro j
    calc _ ≤ ∑ ω : Choice (D.CL.T L), ∑ f : (∀ b, CEPiece D L b),
          B * (T ^ (-((1 : ℝ) / 4)) * ∏ b, g b (ω b) (f b)) :=
          sum_le_sum fun ω _ => sum_le_sum fun f _ => hterm ω f
      _ = B * (T ^ (-((1 : ℝ) / 4)) * ∏ b, ∑ o, ∑ x, g b o x) := by
          rw [← sum_sum_prod g]
          simp only [mul_sum]
      _ ≤ B * (T ^ (-((1 : ℝ) / 4)) * ∏ b, atomW D L b) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hT4) hB0
          exact prod_le_prod₀ (fun b _ => sum_nonneg fun o _ => sum_nonneg fun x _ => hg0 b o x)
            fun b _ => coupAtom_le D L b
  calc _ ≤ ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
        monomial (D.CL.πt L) ω *
          ∑ j : D.FS.Tag, ∑ f : (∀ b, CEPiece D L b), (∏ b, compat D L b (ω b) (f b)) * G ω f :=
        sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hσ ω)
          (monomial_nonneg (D.CL.πt_nonneg L) ω)
    _ ≤ ∑ ω : Choice (D.CL.T L), monomial (D.CL.πt L) ω *
          ∑ j : D.FS.Tag, ∑ f : (∀ b, CEPiece D L b), (∏ b, compat D L b (ω b) (f b)) * G ω f :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun ω _ _ =>
          mul_nonneg (monomial_nonneg (D.CL.πt_nonneg L) ω) (sum_nonneg fun j _ =>
            sum_nonneg fun f _ =>
              mul_nonneg (prod_nonneg fun b _ => compat_nonneg D L b (ω b) (f b)) (hG0 ω f))
    _ = ∑ j : D.FS.Tag, ∑ ω : Choice (D.CL.T L), ∑ f : (∀ b, CEPiece D L b),
          monomial (D.CL.πt L) ω * ((∏ b, compat D L b (ω b) (f b)) * G ω f) := by
        simp only [mul_sum]
        rw [sum_comm]
    _ ≤ ∑ _j : D.FS.Tag, B * (T ^ (-((1 : ℝ) / 4)) * ∏ b, atomW D L b) :=
        sum_le_sum fun j _ => hper j
    _ = _ := by
        rw [sum_const, card_univ, nsmul_eq_mul]

omit [DecidableEq P] in
/-- **`Π_H ≤ e^{2 D.SM.bound}`** for the per-atom bounds (`def:cp8`(c), LP's
`prod_atomPr_le_exp` at the wrapping increment). -/
theorem prod_atomW_le (ha : 0 ≤ a) :
    ∏ b, atomW D L b ≤ Real.exp (2 * D.SM.bound) := by
  have hx : ∀ b, 0 ≤ atomQR D L b ^ ((1 : ℝ) / 4) *
      atomPr D L (TheoremCBlock.Structured.wrapInc D L) b := fun b =>
    mul_nonneg (Real.rpow_nonneg (atomQR_nonneg D L b) _) (atomPr_nonneg D L b)
  have hP := Sarkozy.LargeSums.prod_atomPr_le_exp D L ha (TheoremCBlock.Structured.wrapInc D L)
    (fun b => TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg
      (Sarkozy.DensityChain.isPositiveRecord_wrapInc D L b).1)
    (fun b => Sarkozy.LargeSums.mass_wrapInc_le D L ha b)
  calc ∏ b, atomW D L b ≤ ∏ b, (1 + atomQR D L b ^ ((1 : ℝ) / 4) *
        atomPr D L (TheoremCBlock.Structured.wrapInc D L) b) ^ 2 := by
        refine prod_le_prod₀ (fun b _ => ?_) fun b _ => ?_
        · unfold atomW
          linarith [hx b]
        · unfold atomW
          nlinarith [hx b]
    _ = (∏ b, (1 + atomQR D L b ^ ((1 : ℝ) / 4) *
        atomPr D L (TheoremCBlock.Structured.wrapInc D L) b)) ^ 2 := prod_pow _ _ _
    _ ≤ Real.exp D.SM.bound ^ 2 :=
        pow_le_pow_left₀ (prod_nonneg fun b _ => by linarith [hx b]) hP 2
    _ = Real.exp (2 * D.SM.bound) := by
        rw [sq, ← Real.exp_add]
        ring_nf

end Sums

omit [DecidableEq P] in
/-- **`E1Large`, proved** (`lem:record:density-lp` at the (E1) terms with a large union; see the
module docstring). -/
theorem e1Large_proved (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (ha : 0 ≤ a) :
    ∃ c : ℝ, 0 ≤ c ∧ E1Large D c := by
  obtain ⟨C, hC, hmom⟩ := blockLift_moment_le (m₀ := m₀) (blk := blk) (p := p)
  set X : ℝ := (Fintype.card (ResidueSpace m₀) : ℝ) with hX
  set nT : ℝ := 1 + (Fintype.card D.FS.Tag : ℝ) with hnT
  have hnT0 : 0 ≤ nT := by positivity
  refine ⟨nT * ((1 : ℝ) ^ 72 * (X ^ 72 * C * blockScale)) * Real.exp (2 * D.SM.bound),
    by positivity, ?_⟩
  unfold E1Large
  filter_upwards [eventually_ge_atTop (2 ^ 20 * blockScale)] with L hL
  intro A
  have hL1 : 1 ≤ L := le_trans (by norm_num [blockScale]) hL
  have hB := hmom L hL (D.S.p_prime L) (D.S.p_inj L) A
  have hB0 := Sarkozy.LargeSums.lpB_nonneg (M0 := 1) (X := X) hL1 A hC.le
  have hT : 0 < stageT L := Sarkozy.LargeSums.stageT_pos L hL1
  have h1 := sub_large_le D L A (D.S.p_prime L) hB0 hB hT
  have h2 := coup_large_le D L A (D.S.p_prime L) hB0 hB hT
  have hPi := prod_atomW_le D L ha
  rw [← sum_add_distrib.symm.trans (sum_congr rfl fun ω _ => (mul_add _ _ _).symm)]
  refine (add_le_add h1 h2).trans ?_
  have key := Sarkozy.LargeSums.final_le hL1 hnT0 hC.le (density_nonneg (blockScale * L) A) hPi
    (M0 := 1) (X := X)
  unfold stageT
  unfold remainder
  refine le_of_eq_of_le (by ring) (key.trans_eq (by ring))

end Sarkozy.E1Closure
