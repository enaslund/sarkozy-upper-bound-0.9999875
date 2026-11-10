module

public import Sarkozy.E1Closure.Large

@[expose] public section

/-!
# The two small-union sums from the paper's per-term bounds (EC)

EC, 8 November 2026. On a small union (`q_E ≤ N^τ`) the paper proves a bound **per term**, with
a remainder that is uniform in `E` and its labels (`10_comparison_lemmas.tex` l. 130: "On
`q_E ≤ N^τ` the structured-energy error is uniform in `E` and its labels"):

* `prop:record:density-structured`: `|𝔈| ≤ ‖ρ‖[(1 + u_L) Π_main Y + C_dc L^{-σ} α]`, so a subset
  term with a small union is at most its main term plus `(∏_𝔟 m_𝔟) c₁ L^{-σ} α`
  (**`E1SubSmallPT`**, kind R);
* `lem:sharp-first` (term `T′`), `lem:density:coupled`: a coupled piece with a small union is at
  most its main term plus `(∏_𝔟 cM_𝔟) c₁ L^{-σ} α` (**`E1CoupSmallPT`**, kind C), where `cM` is
  the mass of the piece except at a whole difference, where it is `d̃ w + 2w` (the proof of
  `lem:sharp-first` bounds `|T′|` by `∏ d̃ w` times the masses times the geometric mean of two
  folded energies). G1's `ecpieceM` (`2w` at a whole difference) is smaller (`ecpieceM_le_cM`);
  with it the per-term form would need `d̃ ≤ 2` at every whole difference of the piece.

The subset form is the per-term field of K2's `E1Inputs` restricted to the small unions, where
FA2 (P1) judged it faithful; the coupled form has the larger coefficient `cM`. Then:

* **`e1SubSmall_of_perTerm`**: `E1SubSmallPT D εE c₁ → E1SubSmall D εE (e^S cosh A e^{U₀} c₁)`
  (G1's `sum_subset_remainder_le`, `sum_selection_remainder_le`);
* **`e1CoupSmall_of_perTerm`**: `E1CoupSmallPT D εE c₁ → E1CoupSmall D εE (|𝔗| e^{3 D.SM.bound} c₁)`
  (the sum over `σ` first, `sum_prod_abs_coef_le`; the factorization over the atoms,
  `coupAtomM_le`: `≤ 1 + 3 Pr_𝔟`; `prod_three_atomPr_le`, with `q_𝔟 ≥ 1`).

Both per-term forms are proved at `ε_E = u_L` on the paper's tails (`e1SubSmallPT_proved` in
`SubSmall.lean`, `e1CoupSmallPT_proved` in `CoupSmall.lean`).
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.E1Closure

open Sarkozy.EnvelopeInputsBlock Sarkozy.EnvelopeInputs
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame
open Sarkozy.TheoremC Sarkozy.Comparison Sarkozy.PaperFrame Sarkozy.RecordExpansion
  Sarkozy.RecordExpansion.Choice Sarkozy.Structured ReflectionCut

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)

/-- **(R) The subset terms with a small union, per term** (`prop:record:density-structured`):
the remainder is the product of the masses times `c₁ L^{-σ} α`. -/
def E1SubSmallPT (εE : ℕ → ℝ) (c₁ : ℝ) : Prop :=
  Param.AtCounterexamples (Params.ofDecay a) D.Y
    (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
    ∀ f : BlockAtom Bk J L → Bool, SubSmall D L ω f →
    |subInt D L A ω f| ≤ subMain D εE L A ω f +
      (∏ b, (if f b then (if (ω b).isSome then 0 else mass (∑ i, D.GB.κu L b i)) else 1)) *
        remainder c₁ L A)

/-- **The paper's remainder coefficient of a coupled piece** (`lem:sharp-first`, proof: "`|T′|` is
at most `∏_{𝔟 ∈ S_j} d̃_{𝔟,i} w_{𝔟,i}` times the masses of the positive factors times the geometric
mean of two folded energies"): `d̃ w + 2 w` at a whole difference (the sharp constant times the
mass, plus G1's variation `2 κ(1)`), the mass elsewhere. It dominates G1's `ecpieceM`
(`ecpieceM_le_cM`). -/
noncomputable def cM (L : ℕ) (b : BlockAtom Bk J L) : CEPiece D L b → ℝ
  | Sum.inl none => 1
  | Sum.inl (some i) => mass (D.GB.κu L b i)
  | Sum.inr (i, none) => D.FS.dconst L b i * mass (D.FS.κ L b i) + 2 * mass (D.FS.κ L b i)
  | Sum.inr (i, some t) => if t then mass (D.FS.κ' L b i) else mass (D.FS.κ L b i)

omit [DecidableEq P] in
theorem ecpieceM_le_cM (L : ℕ) (b : BlockAtom Bk J L) (x : CEPiece D L b) :
    ecpieceM D L b x ≤ cM D L b x := by
  rcases x with (_ | i) | ⟨i, _ | t⟩
  · exact le_rfl
  · exact le_rfl
  · change 2 * mass (D.FS.κ L b i) ≤ D.FS.dconst L b i * mass (D.FS.κ L b i) +
      2 * mass (D.FS.κ L b i)
    have := mul_nonneg (D.FS.dconst_nonneg L b i)
      (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1)
    linarith
  · exact le_rfl

omit [DecidableEq P] in
theorem cM_nonneg (L : ℕ) (b : BlockAtom Bk J L) (x : CEPiece D L b) : 0 ≤ cM D L b x :=
  (ecpieceM_nonneg D L b x).trans (ecpieceM_le_cM D L b x)

/-- **(C) The coupled pieces with a small union, per term** (`lem:sharp-first`, term `T′`;
`lem:density:coupled`): the remainder is `(∏_𝔟 cM_𝔟) c₁ L^{-σ} α`, with the paper's coefficient
`d̃ w` (plus `2w`) at the whole differences. -/
def E1CoupSmallPT (εE : ℕ → ℝ) (c₁ : ℝ) : Prop :=
  Param.AtCounterexamples (Params.ofDecay a) D.Y
    (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
    ∀ σ : (∀ b, Option (D.FS.Ib L b)), σ ≠ (fun _ => none) → ∀ j,
    1 ≤ countVec (D.FS.tag L) σ j → ∀ f : (∀ b, CEPiece D L b),
    (∀ b, ecpieceCoef D L ω σ j b (f b) ≠ 0) → CoupSmall D L ω f →
    |coupInt D L A ω f| ≤ coupMain D εE L A ω f + (∏ b, cM D L b (f b)) * remainder c₁ L A)

omit [DecidableEq P] in
/-- `q_𝔟 ≥ 1`: a product of primes. -/
theorem one_le_atomQR (L : ℕ) (b : BlockAtom Bk J L) : 1 ≤ Sarkozy.LargeSums.atomQR D L b := by
  unfold Sarkozy.LargeSums.atomQR
  have : 1 ≤ Sarkozy.DensityChain2.atomQ blk p D.S.pp D.S.ep L b := by
    rcases b with β | j
    · exact Finset.one_le_prod fun i _ => (D.S.pp_prime i.1).one_lt.le
    · change 1 ≤ p L j
      exact Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  exact_mod_cast this

omit [DecidableEq P] in
/-- The per-atom sum of the paper's coefficients: at most `1 + 3 Pr_𝔟`. -/
theorem coupAtomM_le (L : ℕ) (b : BlockAtom Bk J L) :
    ∑ o, ∑ x : CEPiece D L b, entryPrice (D.CL.πt L b) o * compat D L b o x * cM D L b x ≤
      1 + 3 * Sarkozy.LargeSums.atomPr D L (TheoremCBlock.Structured.wrapInc D L) b := by
  have hnone : ∑ x : CEPiece D L b, entryPrice (D.CL.πt L b) none * compat D L b none x *
      cM D L b x = 1 + (∑ k, mass (D.GB.κu L b k) +
        ∑ i, (D.FS.dconst L b i * mass (D.FS.κ L b i) + 3 * mass (D.FS.κ L b i) +
          mass (D.FS.κ' L b i))) := by
    rw [Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_prod_type]
    simp only [Fintype.sum_option, Fintype.sum_bool]
    simp only [entryPrice, compat, cM, ↓reduceIte, one_mul, mul_one, Bool.false_eq_true]
    have e : ∀ i, D.FS.dconst L b i * mass (D.FS.κ L b i) + 2 * mass (D.FS.κ L b i) +
        (mass (D.FS.κ' L b i) + mass (D.FS.κ L b i)) =
        D.FS.dconst L b i * mass (D.FS.κ L b i) + 3 * mass (D.FS.κ L b i) +
          mass (D.FS.κ' L b i) := fun i => by ring
    simp only [e]
    ring
  have hsome : ∀ te : D.CL.T L b × ChangeType, ∑ x : CEPiece D L b,
      entryPrice (D.CL.πt L b) (some te) * compat D L b (some te) x * cM D L b x =
      D.CL.πt L b te.1 te.2 := by
    intro te
    rw [Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_prod_type]
    simp only [Fintype.sum_option, Fintype.sum_bool]
    simp only [entryPrice, compat, cM, reduceCtorEq, ↓reduceIte, mul_zero, zero_mul,
      sum_const_zero, add_zero, mul_one]
  rw [Fintype.sum_option, hnone, sum_congr rfl fun te _ => hsome te, ← mass_wrapInc]
  have := atomPr_ge D L b
  have hd : ∀ i, 0 ≤ D.FS.dconst L b i * mass (D.FS.κ L b i) := fun i =>
    mul_nonneg (D.FS.dconst_nonneg L b i)
      (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1)
  have hk : ∀ i, 0 ≤ mass (D.FS.κ L b i) := fun i =>
    TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1
  have hk' : ∀ i, 0 ≤ mass (D.FS.κ' L b i) := fun i =>
    TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ'_pos L b i).1
  have h3 : ∑ i, (D.FS.dconst L b i * mass (D.FS.κ L b i) + 3 * mass (D.FS.κ L b i) +
      mass (D.FS.κ' L b i)) ≤ 3 * ∑ i, (D.FS.dconst L b i * mass (D.FS.κ L b i) +
        (mass (D.FS.κ' L b i) + mass (D.FS.κ L b i))) := by
    rw [mul_sum]
    exact sum_le_sum fun i _ => by linarith [hd i, hk i, hk' i]
  unfold Sarkozy.LargeSums.atomPr at this ⊢
  have h1 : 0 ≤ ∑ k, mass (D.GB.κu L b k) := sum_nonneg fun k _ =>
    TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.GB.κu_pos L b k).1
  have h2 : 0 ≤ mass (TheoremCBlock.Structured.wrapInc D L b) :=
    TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg
      (Sarkozy.DensityChain.isPositiveRecord_wrapInc D L b).1
  linarith

omit [DecidableEq P] in
/-- `∏_𝔟 (1 + 3 Pr_𝔟) ≤ e^{3 D.SM.bound}` (`def:cp8`(c), with `q_𝔟 ≥ 1`). -/
theorem prod_three_atomPr_le (ha : 0 ≤ a) (L : ℕ) :
    ∏ b, (1 + 3 * Sarkozy.LargeSums.atomPr D L (TheoremCBlock.Structured.wrapInc D L) b) ≤
      Real.exp (3 * D.SM.bound) := by
  have hx : ∀ b, 0 ≤ Sarkozy.LargeSums.atomPr D L (TheoremCBlock.Structured.wrapInc D L) b :=
    atomPr_nonneg D L
  have hq : ∀ b, 1 ≤ Sarkozy.LargeSums.atomQR D L b ^ ((1 : ℝ) / 4) := fun b =>
    Real.one_le_rpow (one_le_atomQR D L b) (by norm_num)
  have hP := Sarkozy.LargeSums.prod_atomPr_le_exp D L ha (TheoremCBlock.Structured.wrapInc D L)
    (fun b => TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg
      (Sarkozy.DensityChain.isPositiveRecord_wrapInc D L b).1)
    (fun b => Sarkozy.LargeSums.mass_wrapInc_le D L ha b)
  set y : BlockAtom Bk J L → ℝ := fun b => Sarkozy.LargeSums.atomQR D L b ^ ((1 : ℝ) / 4) *
    Sarkozy.LargeSums.atomPr D L (TheoremCBlock.Structured.wrapInc D L) b with hy
  have hy0 : ∀ b, 0 ≤ y b := fun b => mul_nonneg (zero_le_one.trans (hq b)) (hx b)
  calc ∏ b, (1 + 3 * Sarkozy.LargeSums.atomPr D L (TheoremCBlock.Structured.wrapInc D L) b)
      ≤ ∏ b, (1 + y b) ^ 3 := by
        refine prod_le_prod₀ (fun b _ => by linarith [hx b]) fun b _ => ?_
        have hxy : Sarkozy.LargeSums.atomPr D L (TheoremCBlock.Structured.wrapInc D L) b ≤ y b :=
          le_mul_of_one_le_left (hx b) (hq b)
        nlinarith [hy0 b, sq_nonneg (y b)]
    _ = (∏ b, (1 + y b)) ^ 3 := prod_pow _ _ _
    _ ≤ Real.exp D.SM.bound ^ 3 :=
        pow_le_pow_left₀ (prod_nonneg fun b _ => by linarith [hy0 b]) hP 3
    _ = Real.exp (3 * D.SM.bound) := by
        rw [← Real.exp_nat_mul]
        norm_num

theorem remainder_nonneg' {c : ℝ} (hc : 0 ≤ c) (L : ℕ) (A : Finset ℤ) : 0 ≤ remainder c L A := by
  unfold remainder
  exact mul_nonneg (mul_nonneg hc (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (density_nonneg _ _)

omit [DecidableEq P] in
/-- **`E1SubSmall` from the per-term structured bound** (G1's summations). -/
theorem e1SubSmall_of_perTerm (ha : 0 ≤ a) {εE : ℕ → ℝ} {c₁ : ℝ} (hc₁ : 0 ≤ c₁)
    (h : E1SubSmallPT D εE c₁) :
    E1SubSmall D εE (Real.exp D.CL.S * Real.cosh D.CL.A * (Real.exp D.GB.U₀ * c₁)) := by
  unfold E1SubSmallPT at h
  unfold E1SubSmall
  filter_upwards [h] with L hL
  intro C hC hk A hA hY
  have hrem0 := remainder_nonneg' hc₁ L A
  refine TheoremCBlock.Structured.sum_selection_remainder_le D ha L A _
    (mul_nonneg (Real.exp_pos _).le hc₁) fun ω hω => ?_
  refine le_trans (sum_le_sum fun f _ => ?_)
    (TheoremCBlock.Structured.sum_subset_remainder_le D ha L A ω hc₁)
  have hm0 : 0 ≤ (∏ b, (if f b then (if (ω b).isSome then 0 else mass (∑ i, D.GB.κu L b i))
      else 1)) * remainder c₁ L A :=
    mul_nonneg (prod_nonneg fun b _ => subsetMass_nonneg D L ω f b) hrem0
  split_ifs with hs
  · have := hL C hC hk A hA hY ω hω f hs
    exact max_le hm0 (by linarith)
  · exact hm0

omit [DecidableEq P] in
/-- **`E1CoupSmall` from the per-term coupled bound** (with the paper's coefficients `cM`; the
sums over `σ`, the selections and the pieces factor over the atoms, `coupAtomM_le`,
`prod_three_atomPr_le`). -/
theorem e1CoupSmall_of_perTerm (ha : 0 ≤ a) {εE : ℕ → ℝ} {c₁ : ℝ} (hc₁ : 0 ≤ c₁)
    (h : E1CoupSmallPT D εE c₁) :
    E1CoupSmall D εE ((Fintype.card D.FS.Tag : ℝ) * Real.exp (3 * D.SM.bound) * c₁) := by
  unfold E1CoupSmallPT at h
  unfold E1CoupSmall
  filter_upwards [h] with L hL
  intro C hC hk A hA hY
  set rem := remainder c₁ L A with hremdef
  have hrem0 : 0 ≤ rem := remainder_nonneg' hc₁ L A
  set SS := univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)
  set g : ∀ b : BlockAtom Bk J L, Option (D.CL.T L b × ChangeType) → CEPiece D L b → ℝ :=
    fun b o x => entryPrice (D.CL.πt L b) o * compat D L b o x * cM D L b x with hg
  have hg0 : ∀ b o x, 0 ≤ g b o x := fun b o x =>
    mul_nonneg (mul_nonneg (entryPrice_nonneg (D.CL.πt_nonneg L b) o) (compat_nonneg D L b o x))
      (cM_nonneg D L b x)
  -- per term: the small remainder is at most the paper's one
  have hpt : ∀ ω : Choice (D.CL.T L), IsSelection ω → ∀ σ ∈ SS, ∀ (j : D.FS.Tag)
      (f : ∀ b, CEPiece D L b), (∏ b, |ecpieceCoef D L ω σ j b (f b)|) *
      (if CoupSmall D L ω f then rX D εE L A ω σ j f else 0) ≤
      (∏ b, |ecpieceCoef D L ω σ j b (f b)|) * ((∏ b, cM D L b (f b)) * rem) := by
    intro ω hω σ hσ j f
    have hc0 : 0 ≤ ∏ b, |ecpieceCoef D L ω σ j b (f b)| := prod_nonneg fun b _ => abs_nonneg _
    have hM0 : 0 ≤ (∏ b, cM D L b (f b)) * rem :=
      mul_nonneg (prod_nonneg fun b _ => cM_nonneg D L b (f b)) hrem0
    by_cases hcf : ∀ b, ecpieceCoef D L ω σ j b (f b) ≠ 0
    · refine mul_le_mul_of_nonneg_left ?_ hc0
      split_ifs with hs
      · unfold rX
        split_ifs with hj
        · have := hL C hC hk A hA hY ω hω σ (mem_filter.mp hσ).2 j hj f hcf hs
          exact max_le hM0 (by linarith)
        · exact hM0
      · exact hM0
    · obtain ⟨b, hb⟩ := not_forall.mp hcf
      have h0 : ∏ b, |ecpieceCoef D L ω σ j b (f b)| = 0 :=
        prod_eq_zero (mem_univ b) (by rw [not_not.mp hb, abs_zero])
      rw [h0, zero_mul, zero_mul]
  -- the sum over `σ` first
  have hσ : ∀ ω : Choice (D.CL.T L), ∑ σ ∈ SS, ∑ j : D.FS.Tag, ∑ f : (∀ b, CEPiece D L b),
      (∏ b, |ecpieceCoef D L ω σ j b (f b)|) * ((∏ b, cM D L b (f b)) * rem) ≤
      ∑ j : D.FS.Tag, ∑ f : (∀ b, CEPiece D L b),
        (∏ b, compat D L b (ω b) (f b)) * ((∏ b, cM D L b (f b)) * rem) := by
    intro ω
    have hG0 : ∀ f : (∀ b, CEPiece D L b), 0 ≤ (∏ b, cM D L b (f b)) * rem := fun f =>
      mul_nonneg (prod_nonneg fun b _ => cM_nonneg D L b (f b)) hrem0
    calc _ ≤ ∑ σ : (∀ b, Option (D.FS.Ib L b)), ∑ j : D.FS.Tag, ∑ f : (∀ b, CEPiece D L b),
          (∏ b, |ecpieceCoef D L ω σ j b (f b)|) * ((∏ b, cM D L b (f b)) * rem) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun σ _ _ =>
            sum_nonneg fun j _ => sum_nonneg fun f _ =>
              mul_nonneg (prod_nonneg fun b _ => abs_nonneg _) (hG0 f)
      _ = ∑ j : D.FS.Tag, ∑ f : (∀ b, CEPiece D L b),
          (∑ σ : (∀ b, Option (D.FS.Ib L b)), ∏ b, |ecpieceCoef D L ω σ j b (f b)|) *
            ((∏ b, cM D L b (f b)) * rem) := by
          rw [sum_comm]
          refine sum_congr rfl fun j _ => ?_
          rw [sum_comm]
          simp only [sum_mul]
      _ ≤ _ := sum_le_sum fun j _ => sum_le_sum fun f _ =>
          mul_le_mul_of_nonneg_right (sum_prod_abs_coef_le D L ω j f) (hG0 f)
  have hper : ∀ j : D.FS.Tag, ∑ ω : Choice (D.CL.T L), ∑ f : (∀ b, CEPiece D L b),
      monomial (D.CL.πt L) ω * ((∏ b, compat D L b (ω b) (f b)) * ((∏ b, cM D L b (f b)) * rem)) ≤
      Real.exp (3 * D.SM.bound) * rem := by
    intro j
    have e : ∀ (ω : Choice (D.CL.T L)) (f : ∀ b, CEPiece D L b),
        monomial (D.CL.πt L) ω * ((∏ b, compat D L b (ω b) (f b)) *
          ((∏ b, cM D L b (f b)) * rem)) = rem * ∏ b, g b (ω b) (f b) := by
      intro ω f
      have hm : monomial (D.CL.πt L) ω = ∏ b, entryPrice (D.CL.πt L b) (ω b) := rfl
      rw [hm]
      simp only [hg, prod_mul_distrib]
      ring
    simp only [e, ← mul_sum]
    rw [sum_sum_prod g, mul_comm]
    refine mul_le_mul_of_nonneg_right ((prod_le_prod₀ (fun b _ => sum_nonneg fun o _ =>
      sum_nonneg fun x _ => hg0 b o x) fun b _ => coupAtomM_le D L b).trans
        (prod_three_atomPr_le D ha L)) hrem0
  calc ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
        monomial (D.CL.πt L) ω * ∑ σ ∈ SS, ∑ j, ∑ f, (∏ b, |ecpieceCoef D L ω σ j b (f b)|) *
          (if CoupSmall D L ω f then rX D εE L A ω σ j f else 0)
      ≤ ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
        monomial (D.CL.πt L) ω * ∑ j : D.FS.Tag, ∑ f : (∀ b, CEPiece D L b),
          (∏ b, compat D L b (ω b) (f b)) * ((∏ b, cM D L b (f b)) * rem) := by
        refine sum_le_sum fun ω hω => mul_le_mul_of_nonneg_left ?_
          (monomial_nonneg (D.CL.πt_nonneg L) ω)
        exact (sum_le_sum fun σ hσ => sum_le_sum fun j _ => sum_le_sum fun f _ =>
          hpt ω (mem_filter.mp hω).2 σ hσ j f).trans (hσ ω)
    _ ≤ ∑ ω : Choice (D.CL.T L), monomial (D.CL.πt L) ω * ∑ j : D.FS.Tag,
          ∑ f : (∀ b, CEPiece D L b),
            (∏ b, compat D L b (ω b) (f b)) * ((∏ b, cM D L b (f b)) * rem) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun ω _ _ =>
          mul_nonneg (monomial_nonneg (D.CL.πt_nonneg L) ω) (sum_nonneg fun j _ =>
            sum_nonneg fun f _ => mul_nonneg (prod_nonneg fun b _ =>
              compat_nonneg D L b (ω b) (f b))
              (mul_nonneg (prod_nonneg fun b _ => cM_nonneg D L b (f b)) hrem0))
    _ = ∑ j : D.FS.Tag, ∑ ω : Choice (D.CL.T L), ∑ f : (∀ b, CEPiece D L b),
          monomial (D.CL.πt L) ω * ((∏ b, compat D L b (ω b) (f b)) *
            ((∏ b, cM D L b (f b)) * rem)) := by
        simp only [mul_sum]
        rw [sum_comm]
    _ ≤ ∑ _j : D.FS.Tag, Real.exp (3 * D.SM.bound) * rem := sum_le_sum fun j _ => hper j
    _ = remainder ((Fintype.card D.FS.Tag : ℝ) * Real.exp (3 * D.SM.bound) * c₁) L A := by
        rw [sum_const, card_univ, nsmul_eq_mul, hremdef]
        unfold remainder
        ring

end Sarkozy.E1Closure
