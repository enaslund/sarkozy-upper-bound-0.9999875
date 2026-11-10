module

public import Sarkozy.E1Closure.Excess
public import Sarkozy.LargeSums.All

@[expose] public section

/-!
# (E1) off the classes: the split by the full union `q_E ≤ N^τ` (EC)

EC, 8 November 2026. `10_comparison_lemmas.tex` ll. 126–140 ("Fixed selections and summed
remainders"): "In a sum over selections we first expand the outside laws and split by the *full*
union `E` of selected atoms. On `q_E ≤ N^τ` the structured-energy error is uniform in `E` and its
labels. All terms with `q_E > N^τ` are instead summed by `lem:record:density-lp`, with their
post-reduction coefficients."

Here the summed excess `E1RemX` (`Excess.lean`) is split in the same way.

* `subQ`, `coupQ`: the conductor `q_𝔟` of an atom that carries a law other than `μ_𝔟` (a
  selected envelope, a bracket record, a first-stage piece), `1` at `μ_𝔟`; `q_𝔟` is the product
  of the primes of `𝔟` with `e_p = 1` (LP's `atomQR`, `oneWeight` of `def:cp8`(c));
* `SubSmall`, `CoupSmall`: the full union is small, `∏_𝔟 q_𝔟 ≤ N^τ` (`N = KL`, `τ = 1/201`;
  `def:record:structured-energy`(a));
* **`E1SubSmall D εE c`** (R): the summed excess of the subset terms with a small union (proved
  at `ε_E = u_L`: `e1SubSmall_proved`, `SubSmall.lean`);
* **`E1CoupSmall D εE c`** (C): the summed excess of the coupled pieces with a small union
  (proved at `ε_E = u_L`: `e1CoupSmall_proved`, `CoupSmall.lean`);
* **`E1Large D c`**: the summed absolute values of all terms with a large union
  (`lem:record:density-lp`), *proved* in `Large.lean`;
* **`e1RemX_of_split`**: `E1SubSmall`, `E1CoupSmall` and `E1Large` give `E1RemX` with
  `c_E = c₁ + c₂ + c₃` (on a large union the excess is at most `|𝔈|`, since the main terms are
  nonnegative at a counterexample);
* **`e1SubSmall_of_remX`**, **`e1CoupSmall_of_remX`**: conversely `E1RemX` gives both small
  parts, with the same constant (the weights are nonnegative). So nothing is asked beyond the
  joint statement.
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
open Sarkozy.LargeSums (atomQR atomQR_nonneg)
open Sarkozy.Functional (stageTau)

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- The threshold `N^τ`, `N = KL`, `τ = 1/201`. -/
noncomputable def stageT (L : ℕ) : ℝ := ((blockScale * L : ℕ) : ℝ) ^ stageTau

section Defs

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)

/-- The conductor of an atom in a subset term: `q_𝔟` if the atom is selected or carries the
bracket records, `1` at `μ_𝔟`. -/
noncomputable def subQ (L : ℕ) (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType))
    (y : Bool) : ℝ :=
  if y = true ∨ o.isSome = true then atomQR D L b else 1

/-- The conductor of an atom in a coupled piece: `1` at `μ_𝔟` (the entry factor of an
unselected atom), `q_𝔟` otherwise. -/
noncomputable def coupQ (L : ℕ) (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType)) :
    CEPiece D L b → ℝ
  | Sum.inl none => if o.isSome = true then atomQR D L b else 1
  | _ => atomQR D L b

/-- **A subset term has a small full union**: `∏_𝔟 q_𝔟 ≤ N^τ` over the atoms where it does not
carry `μ_𝔟`. -/
abbrev SubSmall (L : ℕ) (ω : Choice (D.CL.T L)) (f : BlockAtom Bk J L → Bool) : Prop :=
  ∏ b, subQ D L b (ω b) (f b) ≤ stageT L

/-- **A coupled piece has a small full union.** -/
abbrev CoupSmall (L : ℕ) (ω : Choice (D.CL.T L)) (f : ∀ b, CEPiece D L b) : Prop :=
  ∏ b, coupQ D L b (ω b) (f b) ≤ stageT L

/-- **(R) The subset terms with a small union, summed** (`lem:bracket-energy`,
`prop:record:density-structured` on `q_E ≤ N^τ`, "the structured-energy error is uniform in `E`
and its labels"): the excess `(|𝔈| − M)⁺` of the subset terms with `q_E ≤ N^τ`, weighted by the
selection monomials, is at most `c L^{-σ} α`. -/
def E1SubSmall (εE : ℕ → ℝ) (c : ℝ) : Prop :=
  Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
    ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
      monomial (D.CL.πt L) ω *
        ∑ f, (if SubSmall D L ω f then r0X D εE L A ω f else 0) ≤ remainder c L A)

/-- **(C) The coupled pieces with a small union, summed** (`lem:sharp-first`,
`lem:density:coupled`, `prop:density:production` on `q_E ≤ N^τ`): the excess of the coupled
pieces with `q_E ≤ N^τ`, weighted by the selection monomials and the coefficients, is at most
`c L^{-σ} α`. -/
def E1CoupSmall (εE : ℕ → ℝ) (c : ℝ) : Prop :=
  Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
    ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
      monomial (D.CL.πt L) ω *
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          ∑ j, ∑ f, (∏ b, |ecpieceCoef D L ω σ j b (f b)|) *
            (if CoupSmall D L ω f then rX D εE L A ω σ j f else 0) ≤ remainder c L A)

/-- **The terms with a large union, summed** (`lem:record:density-lp` with the post-reduction
prices): the absolute values of the subset terms and of the coupled pieces with `q_E > N^τ`,
weighted as in `E1Rem`, are at most `c L^{-σ} α`, at every large `L` and every `A`. Proved in
`Large.lean`. -/
def E1Large (c : ℝ) : Prop :=
  ∀ᶠ L : ℕ in atTop, ∀ A : Finset ℤ,
    ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
      monomial (D.CL.πt L) ω *
        (∑ f, (if SubSmall D L ω f then 0 else |subInt D L A ω f|) +
          ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
            ∑ j, ∑ f, (∏ b, |ecpieceCoef D L ω σ j b (f b)|) *
              (if CoupSmall D L ω f then 0 else |coupInt D L A ω f|)) ≤ remainder c L A

omit [DecidableEq P] in
theorem subMain_nonneg {εE : ℕ → ℝ} (hε0 : ∀ L, 0 ≤ εE L) {L : ℕ} {A : Finset ℤ}
    (hY : 0 ≤ D.Y L A) (ω : Choice (D.CL.T L)) (f : BlockAtom Bk J L → Bool) :
    0 ≤ subMain D εE L A ω f := by
  unfold subMain
  have h1 : 0 ≤ 1 + εE L := by linarith [hε0 L]
  have h2 : 0 ≤ ∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b :=
    prod_nonneg fun b _ => D.selectionFactor_nonneg L b
  have h3 : 0 ≤ ∏ b, (if f b then (if (ω b).isSome then 0 else D.GB.uprice L b) else 1) :=
    prod_nonneg fun b _ => by
      split_ifs
      · exact le_rfl
      · exact TheoremCBlock.Structured.uprice_nonneg D L b
      · exact zero_le_one
  exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) hY) h3

omit [DecidableEq P] in
theorem coupMain_nonneg {εE : ℕ → ℝ} (hε0 : ∀ L, 0 ≤ εE L) {L : ℕ} {A : Finset ℤ}
    (hY : 0 ≤ D.Y L A) (ω : Choice (D.CL.T L)) (f : ∀ b, CEPiece D L b) :
    0 ≤ coupMain D εE L A ω f := by
  unfold coupMain
  have h1 : 0 ≤ 1 + εE L := by linarith [hε0 L]
  exact mul_nonneg (prod_nonneg fun b _ => ecpieceG_nonneg D L ω b (f b)) (mul_nonneg h1 hY)

omit [DecidableEq P] in
/-- On any term, the canonical remainder is at most `|𝔈|` when the main term is nonnegative. -/
theorem r0X_le_abs {εE : ℕ → ℝ} (hε0 : ∀ L, 0 ≤ εE L) {L : ℕ} {A : Finset ℤ}
    (hY : 0 ≤ D.Y L A) (ω : Choice (D.CL.T L)) (f : BlockAtom Bk J L → Bool) :
    r0X D εE L A ω f ≤ |subInt D L A ω f| :=
  max_le (abs_nonneg _) (by linarith [subMain_nonneg D hε0 hY ω f])

omit [DecidableEq P] in
theorem rX_le_abs {εE : ℕ → ℝ} (hε0 : ∀ L, 0 ≤ εE L) {L : ℕ} {A : Finset ℤ}
    (hY : 0 ≤ D.Y L A) (ω : Choice (D.CL.T L)) (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag)
    (f : ∀ b, CEPiece D L b) : rX D εE L A ω σ j f ≤ |coupInt D L A ω f| := by
  unfold rX
  split_ifs
  · exact max_le (abs_nonneg _) (by linarith [coupMain_nonneg D hε0 hY ω f])
  · exact abs_nonneg _

theorem remainder_add (c₁ c₂ : ℝ) (L : ℕ) (A : Finset ℤ) :
    remainder (c₁ + c₂) L A = remainder c₁ L A + remainder c₂ L A := by
  unfold remainder
  ring

omit [DecidableEq P] in
/-- **(E1) off the classes from the split** (`10_comparison_lemmas.tex` ll. 126–140): the small
parts `E1SubSmall`, `E1CoupSmall` and the large part `E1Large` give `E1RemX` with
`c_E = c₁ + c₂ + c₃`. -/
theorem e1RemX_of_split {εE : ℕ → ℝ} (hε0 : ∀ L, 0 ≤ εE L) {c₁ c₂ c₃ : ℝ}
    (hsub : E1SubSmall D εE c₁) (hcoup : E1CoupSmall D εE c₂) (hlarge : E1Large D c₃) :
    E1RemX D εE (c₁ + c₂ + c₃) := by
  unfold E1RemX E1Rem
  unfold E1SubSmall at hsub
  unfold E1CoupSmall at hcoup
  unfold E1Large at hlarge
  filter_upwards [hsub, hcoup, hlarge] with L h1 h2 h3
  intro C hC hk A hA hY
  have hY0 : 0 ≤ D.Y L A := (Param.counterexample_pos (Params.ofDecay a) hC hY).le
  set SF := univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω)
  set SS := univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)
  calc ∑ ω ∈ SF, monomial (D.CL.πt L) ω * (∑ f, r0X D εE L A ω f +
        ∑ σ ∈ SS, ∑ j, ∑ f, (∏ b, |ecpieceCoef D L ω σ j b (f b)|) * rX D εE L A ω σ j f)
      ≤ ∑ ω ∈ SF, monomial (D.CL.πt L) ω *
        (∑ f, ((if SubSmall D L ω f then r0X D εE L A ω f else 0) +
            (if SubSmall D L ω f then 0 else |subInt D L A ω f|)) +
          ∑ σ ∈ SS, ∑ j, ∑ f, (∏ b, |ecpieceCoef D L ω σ j b (f b)|) *
            ((if CoupSmall D L ω f then rX D εE L A ω σ j f else 0) +
              (if CoupSmall D L ω f then 0 else |coupInt D L A ω f|))) := by
        refine sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (add_le_add ?_ ?_)
          (monomial_nonneg (D.CL.πt_nonneg L) ω)
        · refine sum_le_sum fun f _ => ?_
          split_ifs
          · simp
          · simpa using r0X_le_abs D hε0 hY0 ω f
        · refine sum_le_sum fun σ _ => sum_le_sum fun j _ => sum_le_sum fun f _ =>
            mul_le_mul_of_nonneg_left ?_ (prod_nonneg fun b _ => abs_nonneg _)
          split_ifs
          · simp
          · simpa using rX_le_abs D hε0 hY0 ω σ j f
    _ = ∑ ω ∈ SF, monomial (D.CL.πt L) ω *
          ∑ f, (if SubSmall D L ω f then r0X D εE L A ω f else 0) +
        ∑ ω ∈ SF, monomial (D.CL.πt L) ω *
          ∑ σ ∈ SS, ∑ j, ∑ f, (∏ b, |ecpieceCoef D L ω σ j b (f b)|) *
            (if CoupSmall D L ω f then rX D εE L A ω σ j f else 0) +
        ∑ ω ∈ SF, monomial (D.CL.πt L) ω *
          (∑ f, (if SubSmall D L ω f then 0 else |subInt D L A ω f|) +
            ∑ σ ∈ SS, ∑ j, ∑ f, (∏ b, |ecpieceCoef D L ω σ j b (f b)|) *
              (if CoupSmall D L ω f then 0 else |coupInt D L A ω f|)) := by
        simp only [mul_add, sum_add_distrib]
        ring
    _ ≤ remainder c₁ L A + remainder c₂ L A + remainder c₃ L A :=
        add_le_add (add_le_add (h1 C hC hk A hA hY) (h2 C hC hk A hA hY)) (h3 A)
    _ = remainder (c₁ + c₂ + c₃) L A := by rw [remainder_add, remainder_add]

omit [DecidableEq P] in
/-- **Conversely, `E1RemX` gives the small subset part** with the same constant. -/
theorem e1SubSmall_of_remX {εE : ℕ → ℝ} {cE : ℝ} (h : E1RemX D εE cE) :
    E1SubSmall D εE cE := by
  unfold E1RemX E1Rem at h
  unfold E1SubSmall
  filter_upwards [h] with L hL
  intro C hC hk A hA hY
  refine le_trans (sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_
    (monomial_nonneg (D.CL.πt_nonneg L) ω)) (hL C hC hk A hA hY)
  refine le_add_of_le_of_nonneg (sum_le_sum fun f _ => ?_) (sum_nonneg fun σ _ =>
    sum_nonneg fun j _ => sum_nonneg fun f _ =>
      mul_nonneg (prod_nonneg fun b _ => abs_nonneg _) (rX_nonneg D εE L A ω σ j f))
  split_ifs
  · exact le_rfl
  · exact r0X_nonneg D εE L A ω f

omit [DecidableEq P] in
/-- **Conversely, `E1RemX` gives the small coupled part** with the same constant. -/
theorem e1CoupSmall_of_remX {εE : ℕ → ℝ} {cE : ℝ} (h : E1RemX D εE cE) :
    E1CoupSmall D εE cE := by
  unfold E1RemX E1Rem at h
  unfold E1CoupSmall
  filter_upwards [h] with L hL
  intro C hC hk A hA hY
  refine le_trans (sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_
    (monomial_nonneg (D.CL.πt_nonneg L) ω)) (hL C hC hk A hA hY)
  refine le_add_of_nonneg_of_le (sum_nonneg fun f _ => r0X_nonneg D εE L A ω f)
    (sum_le_sum fun σ _ => sum_le_sum fun j _ => sum_le_sum fun f _ =>
      mul_le_mul_of_nonneg_left ?_ (prod_nonneg fun b _ => abs_nonneg _))
  split_ifs
  · exact le_rfl
  · exact rX_nonneg D εE L A ω σ j f

end Defs

end Sarkozy.E1Closure
