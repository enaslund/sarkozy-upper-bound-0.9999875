module

public import Sarkozy.LargeSums.Data

@[expose] public section

/-!
# `lem:record:density-lp` at the large pieces of one per-choice remainder

LP (8 November 2026). At fixed `L`, `A` and depth vector, for any positive-record increments `Q`,
any inputs `a^ω_v` whose averaged `72`-th moments are at most `B`, and any notion `small` of the
pieces such that every other piece has `T < ∏_𝔟 qf_𝔟(φ_𝔟)`:

**`large_core`**:
`E_ω ∑_f ∑_{σ ∈ S} ∑_j ∑_{¬small φ} w_φ √𝔈₊(φ) √𝔈₋(φ) ≤ |𝔗| B T^{-1/4} ∏_𝔟 (1 + q_𝔟^{1/4} Pr_𝔟)`.

The steps are the paper's (proof of `lem:record:density-lp`):
* `√𝔈₊ √𝔈₋ ≤ (|𝔈₊| + |𝔈₋|)/2` (`sqrt_mul_sqrt_le_abs`);
* `E_ω |𝔈_±(φ)| ≤ m(φ) B` (Hölder in `L^{72}` with the uniform marginals of the folded positive
  records, then over the index law: `expect_abs_tensor_le`, `mass_bpieceLp/Lm`);
* Rankin over the large pieces and the sums over the choices (`sum_choices_rankin_le`).
-/

namespace Sarkozy.LargeSums

open Finset Function
open scoped BigOperators
open Sarkozy.TheoremC Sarkozy.Structured Sarkozy.DensityChain Sarkozy.DensityFibre
  Sarkozy.EnvelopeInputs Sarkozy.EnvelopeInputsBlock Sarkozy.BlockFrame
  Sarkozy.EnvelopeEnergiesPaper Sarkozy.Comparison ReflectionCut

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

omit [DecidableEq P] in
theorem choiceWeight_nonneg (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (f : BlockAtom Bk J L → Bool) (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag)
    (φ : ∀ b, HPiece D L b) : 0 ≤ choiceWeight (hpieceCoef D L f σ j) (bpieceD D L) φ :=
  prod_nonneg fun b _ => mul_nonneg (abs_nonneg _) (bpieceD_nonneg D L b (φ b))

omit [DecidableEq P] in
/-- **`lem:record:density-lp` at the large pieces of one per-choice remainder** (see the module
docstring). -/
theorem large_core {Ω : Type*} [Fintype Ω] (Pω : FiniteLaw Ω)
    (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ) (hp : ∀ j, (p L j).Prime)
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (hQ : ∀ b, IsPositiveRecord (Qb b))
    (dec : DecFamily D L) {Y : Type} [Fintype Y] [Nonempty Y]
    (e : Y ≃ (∀ b, BlockLabel m₀ blk p L b)) (Ain : Ω → Slot → Y → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ v, Pω.expect (fun ω => (FiniteLaw.uniform Y).moment 72 (Ain ω v)) ≤ B)
    (q : BlockAtom Bk J L → ℝ) (hq : ∀ b, 0 ≤ q b) {T : ℝ} (hT : 0 < T)
    (small : (∀ b, HPiece D L b) → Prop)
    (hlarge : ∀ φ, ¬ small φ → T < ∏ b, qf D L q b (φ b))
    (S : Finset (∀ b, Option (D.FS.Ib L b))) :
    Pω.expect (fun ω => ∑ f : BlockAtom Bk J L → Bool, ∑ σ ∈ S, ∑ j : D.FS.Tag,
      Sarkozy.SharpSums.largePart small
        (fun φ => choiceWeight (hpieceCoef D L f σ j) (bpieceD D L) φ)
        (fun φ => foldedPlus (D.FS.cut j) (bpieceLp D L Qb dec j)
          (fun v x => Ain ω v (e.symm x)) φ)
        (fun φ => foldedMinus (D.FS.cut j) (bpieceLm D L Qb dec j)
          (fun v x => Ain ω v (e.symm x)) φ)) ≤
      (Fintype.card D.FS.Tag : ℝ) *
        (B * (T ^ (-((1 : ℝ) / 4)) * ∏ b, (1 + q b ^ ((1 : ℝ) / 4) * atomPr D L Qb b))) := by
  classical
  set Fp : D.FS.Tag → Ω → (∀ b, HPiece D L b) → ℝ := fun j ω φ =>
    foldedPlus (D.FS.cut j) (bpieceLp D L Qb dec j) (fun v x => Ain ω v (e.symm x)) φ with hFp
  set Fm : D.FS.Tag → Ω → (∀ b, HPiece D L b) → ℝ := fun j ω φ =>
    foldedMinus (D.FS.cut j) (bpieceLm D L Qb dec j) (fun v x => Ain ω v (e.symm x)) φ with hFm
  set w : (BlockAtom Bk J L → Bool) → (∀ b, Option (D.FS.Ib L b)) → D.FS.Tag →
      (∀ b, HPiece D L b) → ℝ := fun f σ j φ =>
    choiceWeight (hpieceCoef D L f σ j) (bpieceD D L) φ with hw
  set m : (∀ b, HPiece D L b) → ℝ := fun φ => ∏ b, pieceMass D L Qb b (φ b) with hm
  -- the Hölder bounds, one fold at a time
  have hEp : ∀ j φ, Pω.expect (fun ω => |Fp j ω φ|) ≤ m φ * B := by
    intro j φ
    have h := expect_abs_tensor_le Pω (fun b => bpieceLp D L Qb dec j b (φ b))
      (fun b => isPositiveRecord_bpieceLp D L Qb dec hp hQ j b (φ b)) e (D.FS.cut j).foldPlus
      Ain hB
    simp only [mass_bpieceLp] at h
    exact h
  have hEm : ∀ j φ, Pω.expect (fun ω => |Fm j ω φ|) ≤ m φ * B := by
    intro j φ
    have h := expect_abs_tensor_le Pω (fun b => bpieceLm D L Qb dec j b (φ b))
      (fun b => isPositiveRecord_bpieceLm D L Qb dec hp hQ j b (φ b)) e (D.FS.cut j).foldMinus
      Ain hB
    simp only [mass_bpieceLm] at h
    exact h
  -- pointwise: the large part by one fold at a time
  have hpt : ∀ ω, (∑ f : BlockAtom Bk J L → Bool, ∑ σ ∈ S, ∑ j : D.FS.Tag,
      Sarkozy.SharpSums.largePart small (w f σ j) (Fp j ω) (Fm j ω)) ≤
      ∑ f : BlockAtom Bk J L → Bool, ∑ σ ∈ S, ∑ j : D.FS.Tag, ∑ φ : (∀ b, HPiece D L b),
        w f σ j φ * (if small φ then 0 else (|Fp j ω φ| + |Fm j ω φ|) / 2) := by
    intro ω
    refine sum_le_sum fun f _ => sum_le_sum fun σ _ => sum_le_sum fun j _ => ?_
    unfold Sarkozy.SharpSums.largePart
    refine sum_le_sum fun φ _ => mul_le_mul_of_nonneg_left ?_ (choiceWeight_nonneg D L f σ j φ)
    split_ifs
    · exact le_rfl
    · exact sqrt_mul_sqrt_le_abs _ _
  refine (Pω.expect_mono hpt).trans ?_
  simp only [FiniteLaw.expect_sum, FiniteLaw.expect_const_mul]
  have hφ : ∀ j φ, Pω.expect (fun ω => if small φ then 0 else (|Fp j ω φ| + |Fm j ω φ|) / 2) ≤
      (if small φ then 0 else m φ) * B := by
    intro j φ
    by_cases hs : small φ
    · simp [hs]
    · simp only [hs, ↓reduceIte]
      have e1 : (fun ω => (|Fp j ω φ| + |Fm j ω φ|) / 2) =
          fun ω => (1 / 2 : ℝ) * |Fp j ω φ| + (1 / 2 : ℝ) * |Fm j ω φ| := by
        funext ω; ring
      rw [e1, FiniteLaw.expect_add, FiniteLaw.expect_const_mul, FiniteLaw.expect_const_mul]
      linarith [hEp j φ, hEm j φ]
  calc _ ≤ ∑ f : BlockAtom Bk J L → Bool, ∑ σ ∈ S, ∑ j : D.FS.Tag, ∑ φ : (∀ b, HPiece D L b),
        w f σ j φ * ((if small φ then 0 else m φ) * B) :=
        sum_le_sum fun f _ => sum_le_sum fun σ _ => sum_le_sum fun j _ => sum_le_sum fun φ _ =>
          mul_le_mul_of_nonneg_left (hφ j φ) (choiceWeight_nonneg D L f σ j φ)
    _ = ∑ f : BlockAtom Bk J L → Bool, ∑ j : D.FS.Tag, ∑ σ ∈ S,
          B * ∑ φ : (∀ b, HPiece D L b), w f σ j φ * (if small φ then 0 else m φ) := by
        refine sum_congr rfl fun f _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun j _ => sum_congr rfl fun σ _ => ?_
        rw [mul_sum]
        exact sum_congr rfl fun φ _ => by ring
    _ = B * ∑ j : D.FS.Tag, ∑ f : BlockAtom Bk J L → Bool, ∑ σ ∈ S,
          ∑ φ : (∀ b, HPiece D L b), w f σ j φ * (if small φ then 0 else m φ) := by
        rw [sum_comm]
        simp only [mul_sum]
    _ ≤ B * ∑ _j : D.FS.Tag,
          T ^ (-((1 : ℝ) / 4)) * ∏ b, (1 + q b ^ ((1 : ℝ) / 4) * atomPr D L Qb b) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun j _ =>
          sum_choices_rankin_le D L Qb hQ j q hq hT small hlarge S) hB0
    _ = _ := by
        rw [sum_const, card_univ, nsmul_eq_mul]
        ring

end Sarkozy.LargeSums
