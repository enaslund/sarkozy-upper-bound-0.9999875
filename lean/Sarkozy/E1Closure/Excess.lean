module

public import Sarkozy.Companion.Kinds

@[expose] public section

/-!
# (E1) off the classes: the canonical remainders (EC)

EC, 8 November 2026. The three fields `E1Sub` (R), `E1Coup` (C) and `E1Rem` (C) of
`Sarkozy.Companion` (F1P's `E1InputsAgg` after FA2's P1) have free per-term remainders `r0`, `r`.
Alone, each of `E1Sub`, `E1Coup` is trivially satisfiable; the content is joint, in `E1Rem`.
This file makes that precise, with **canonical remainders**: the excess of a term over its main
term,

`r0X_{ω,f} = (|𝔈_{ω,f}| − M_{ω,f})⁺`, `rX_{ω,σ,j,f} = (|𝔈_{ω,f}| − M_{ω,f})⁺` (if `k_j(σ) ≥ 1`).

* `subLaw`, `subInt`, `subMain`, `coupInt`, `coupMain`: the integrals and the main terms of the
  two per-term fields, verbatim;
* `r0X`, `rX`: the canonical remainders; **`e1Sub_r0X`**, **`e1Coup_rX`**: `E1Sub` and `E1Coup`
  hold for them, for every `εE`;
* **`E1RemX D εE cE`** `:= E1Rem D cE (r0X D εE) (rX D εE)`: the joint content;
* **`e1RemX_of_fields`** (exactness): any nonnegative `r0`, `r` with `E1Sub`, `E1Coup` and
  `E1Rem` give `E1RemX`. So the triple (with free remainders) is equivalent to the single
  statement `E1RemX`, and the remainders are no longer data.

The weights of `E1Rem` are nonnegative (`monomial_nonneg`, `|c|`), so a smaller remainder can only
decrease its left side; the canonical remainders are the smallest admissible ones, except at the
pairs `(σ, j)` with `k_j(σ) = 0`, where `E1Coup` says nothing and `rX = 0`.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.E1Closure

open Sarkozy.EnvelopeInputsBlock Sarkozy.EnvelopeInputs
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame
open Sarkozy.TheoremC Sarkozy.Comparison Sarkozy.PaperFrame Sarkozy.RecordExpansion
  Sarkozy.RecordExpansion.Choice Sarkozy.Structured ReflectionCut
open Sarkozy.Companion (E1R0 E1R E1Sub E1Coup E1Rem)

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

section Defs

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)

/-- The atom law of a subset term (`E1Sub`): the bracket records `∑_i κu_{𝔟,i}` where `f`
chooses them (`0` on the selected set), the entry factor (`μ_𝔟` or the selected `D^ε_{𝔟,t}`)
elsewhere. It depends on the atom only through `o = ω 𝔟` and `y = f 𝔟`. -/
noncomputable def subLaw (L : ℕ) (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType))
    (y : Bool) : TheoremCBlock.AtomMeasure m₀ blk p L b :=
  if y then (if o.isSome then 0 else ∑ i, D.GB.κu L b i)
  else entryFactor (D.R.law p L b) (D.CL.D L b) o

/-- The integral of a subset term (`E1Sub`, left side inside `|·|`). -/
noncomputable def subInt (L : ℕ) (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (f : BlockAtom Bk J L → Bool) : ℝ :=
  diagonalIntegral (tensorLaw fun b => subLaw D L b (ω b) (f b)) (blockLift m₀ blk p L A)

/-- The main term of a subset term (`E1Sub`, right side without `r0`). -/
noncomputable def subMain (εE : ℕ → ℝ) (L : ℕ) (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (f : BlockAtom Bk J L → Bool) : ℝ :=
  ((1 + εE L) * (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
    D.Y L A) * ∏ b, (if f b then (if (ω b).isSome then 0 else D.GB.uprice L b) else 1)

/-- The integral of a coupled piece (`E1Coup`, left side inside `|·|`). -/
noncomputable def coupInt (L : ℕ) (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (f : ∀ b, CEPiece D L b) : ℝ :=
  diagonalIntegral (tensorLaw fun b => ecpieceK D L ω b (f b)) (blockLift m₀ blk p L A)

/-- The main term of a coupled piece (`E1Coup`, right side without `r`). -/
noncomputable def coupMain (εE : ℕ → ℝ) (L : ℕ) (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (f : ∀ b, CEPiece D L b) : ℝ :=
  (∏ b, ecpieceG D L ω b (f b)) * ((1 + εE L) * D.Y L A)

/-- **The canonical remainder of a subset term**: its excess `(|𝔈| − M)⁺`. -/
noncomputable def r0X (εE : ℕ → ℝ) : E1R0 D := fun L A ω f =>
  max 0 (|subInt D L A ω f| - subMain D εE L A ω f)

/-- **The canonical remainder of a coupled piece**: its excess `(|𝔈| − M)⁺` when the tag `j`
occurs in `σ`, and `0` otherwise (where `E1Coup` asks nothing). -/
noncomputable def rX (εE : ℕ → ℝ) : E1R D := fun L A ω σ j f =>
  if 1 ≤ countVec (D.FS.tag L) σ j then max 0 (|coupInt D L A ω f| - coupMain D εE L A ω f)
  else 0

omit [DecidableEq P] in
theorem r0X_nonneg (εE : ℕ → ℝ) (L : ℕ) (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (f : BlockAtom Bk J L → Bool) : 0 ≤ r0X D εE L A ω f :=
  le_max_left _ _

omit [DecidableEq P] in
theorem rX_nonneg (εE : ℕ → ℝ) (L : ℕ) (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) (f : ∀ b, CEPiece D L b) :
    0 ≤ rX D εE L A ω σ j f := by
  unfold rX
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

omit [DecidableEq P] in
/-- **`E1Sub` holds for the canonical remainders** (for every `εE`). -/
theorem e1Sub_r0X (εE : ℕ → ℝ) : E1Sub D εE (r0X D εE) := by
  unfold E1Sub
  refine Filter.Eventually.of_forall fun L C _ _ A _ _ ω _ f => ?_
  change |subInt D L A ω f| ≤ subMain D εE L A ω f + max 0 (|subInt D L A ω f| -
    subMain D εE L A ω f)
  linarith [le_max_right 0 (|subInt D L A ω f| - subMain D εE L A ω f)]

omit [DecidableEq P] in
/-- **`E1Coup` holds for the canonical remainders** (for every `εE`). -/
theorem e1Coup_rX (εE : ℕ → ℝ) : E1Coup D εE (rX D εE) := by
  unfold E1Coup
  refine Filter.Eventually.of_forall fun L C _ _ A _ _ ω _ σ _ j hj f _ => ?_
  change |coupInt D L A ω f| ≤ coupMain D εE L A ω f + rX D εE L A ω σ j f
  simp only [rX, hj, ↓reduceIte]
  linarith [le_max_right 0 (|coupInt D L A ω f| - coupMain D εE L A ω f)]

/-- **The joint content of (E1) off the classes** (`lem:record:density-lp`, `def:robust`,
`10_comparison_lemmas.tex` ll. 126–140): `E1Rem` at the canonical remainders. The summed excess
of the subset terms and of the coupled pieces over their main terms, weighted by the selection
monomials and the coefficients, is at most `c_E L^{-σ} α`. -/
def E1RemX (εE : ℕ → ℝ) (cE : ℝ) : Prop := E1Rem D cE (r0X D εE) (rX D εE)

omit [DecidableEq P] in
/-- **Exactness**: nonnegative remainders `r0`, `r` with `E1Sub`, `E1Coup` and `E1Rem` give
`E1RemX` (the canonical remainders are at most `r0`, `r` wherever the weights of `E1Rem` are
nonzero). -/
theorem e1RemX_of_fields {εE : ℕ → ℝ} {cE : ℝ} {r0 : E1R0 D} {r : E1R D}
    (hr0 : ∀ L A ω σ j f, 0 ≤ r L A ω σ j f) (hs0 : ∀ L A ω f, 0 ≤ r0 L A ω f)
    (hsub : E1Sub D εE r0) (hcoup : E1Coup D εE r) (hrem : E1Rem D cE r0 r) :
    E1RemX D εE cE := by
  unfold E1RemX E1Rem
  unfold E1Sub at hsub
  unfold E1Coup at hcoup
  unfold E1Rem at hrem
  filter_upwards [hsub, hcoup, hrem] with L h1 h2 h3
  intro C hC hk A hA hY
  refine le_trans ?_ (h3 C hC hk A hA hY)
  refine sum_le_sum fun ω hω => ?_
  have hsel : IsSelection ω := (mem_filter.mp hω).2
  refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_)
    (monomial_nonneg (D.CL.πt_nonneg L) ω)
  · refine sum_le_sum fun f _ => ?_
    have := h1 C hC hk A hA hY ω hsel f
    change |subInt D L A ω f| ≤ subMain D εE L A ω f + r0 L A ω f at this
    exact max_le (hs0 L A ω f) (by linarith)
  · refine sum_le_sum fun σ hσ => sum_le_sum fun j _ => sum_le_sum fun f _ => ?_
    have hσ' : σ ≠ fun _ => none := (mem_filter.mp hσ).2
    have hc0 : 0 ≤ ∏ b, |ecpieceCoef D L ω σ j b (f b)| := prod_nonneg fun b _ => abs_nonneg _
    by_cases hj : 1 ≤ countVec (D.FS.tag L) σ j
    · by_cases hcf : ∀ b, ecpieceCoef D L ω σ j b (f b) ≠ 0
      · refine mul_le_mul_of_nonneg_left ?_ hc0
        have := h2 C hC hk A hA hY ω hsel σ hσ' j hj f hcf
        change |coupInt D L A ω f| ≤ coupMain D εE L A ω f + r L A ω σ j f at this
        simp only [rX, hj, ↓reduceIte]
        exact max_le (hr0 L A ω σ j f) (by linarith)
      · obtain ⟨b, hb⟩ := not_forall.mp hcf
        have h0 : ∏ b, |ecpieceCoef D L ω σ j b (f b)| = 0 :=
          prod_eq_zero (mem_univ b) (by rw [not_not.mp hb, abs_zero])
        rw [h0, zero_mul, zero_mul]
    · simp only [rX, hj, ↓reduceIte, mul_zero]
      exact mul_nonneg hc0 (hr0 L A ω σ j f)

end Defs

end Sarkozy.E1Closure
