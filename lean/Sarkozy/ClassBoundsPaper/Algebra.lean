module

public import Sarkozy.RecordExpansion.Replacement
public import Sarkozy.TheoremC.RecordComparison
public import Sarkozy.Comparison.ClosingNumerics

@[expose] public section

/-!
# The class algebra of the closing (`prop:closing-data`(d), certificate family F15)

`paper/sections/28_closing.tex`, `prop:closing-data`(d) and `def:closing-quantities`(7)–(9);
`paper/sections/10_comparison_lemmas.tex`, `lem:record:record-expansion` (ii)–(v);
`paper/sections/09_comparison_theorem.tex`, `def:cp5`, `rem:cp:monotone`.

The obligation `hΨ` of the main statement asks, at every scale, that the sum over the selections `ω`
of `b_ω` (`B π_ω` for a selection in no class, its class bound `φ_ω` for a selection of a class) be
at most the ledger's `𝓔 = B(e^S cosh A − 1) − D`. This file reduces that inequality, for any class
bounds, to the class algebra of the paper:

* `classTerm`: the summand `b_ω` of `hΨ`.
* `classTerm_le_replacedBound`: the pointwise comparison of `b_ω` with WP-R's `replacedBound` (the
  class bound `C_n π^arm_ω + B'(π^tot_ω − π^lead_ω)` of `thm:envelopes`(i) on the replaced degree
  classes, a class cost `c_ω π_ω` elsewhere), from three named properties of the classes:
  - a selection in no class is in no replaced degree class, and `B ≤ c_ω` there;
  - a selection of a class outside the replaced degree classes (a variance class of
    `cor:variance:final`(i), (iii)) has `φ_ω ≤ c_ω π_ω`;
  - a selection of a replaced degree class `𝒞_n` is in a class and has `φ_ω ≤ C_n π^arm_ω +
    B'(π^tot_ω − π^lead_ω)` (`cor:envelope-costs`, `thm:envelopes`(i)).
* **`sum_classTerm_le_upper`**: `∑_ω b_ω ≤ B'(e^Ŝ cosh Â − 1) − 𝒟(π̂) − ∑_n saving_n(π̂, ŷ)` at
  upper prices `π̂ ≥ π` and upper auxiliary prices `ŷ ≥ y`, from `replacement_le_upper`
  (`lem:record:record-expansion` (iii)–(v)); `𝒟` is the completion polynomial `𝒟_sym` of the
  variance classes.
* **`sum_classTerm_le_E`**: the same is at most `l.E` for a ledger `l` with `B' ≤ l.B`, `Ŝ ≤ l.S`,
  `Â ≤ l.A` and `l.D ≤ 𝒟(π̂) + ∑_n saving_n(π̂, ŷ)` (`prop:closing-data`(d), conclusion).
* `replacementSaving_eq_totals`: the saving of a degree class depends on the prices only through the
  kind totals (`savingOfTotals`, the formula (8) of `def:closing-quantities`), which is what makes
  the numerical certificate of `Sarkozy.ClassBoundsPaper.Savings` possible.

Everything here is proved; the hypotheses are the named properties above.
-/

open Finset
open scoped BigOperators Nat

namespace Sarkozy.ClassBoundsPaper

open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice Sarkozy.Comparison

section Generic

variable {J : Type*} [Fintype J] [DecidableEq J] {T : J → Type*} [∀ b, Fintype (T b)]
  [∀ b, DecidableEq (T b)] {L : Type*} [Fintype L] [DecidableEq L] {ι : Type*}

/-- The summand `b_ω` of `hΨ` (`lem:record:record-expansion` (ii)): `B π_ω` for a selection in no
class, the class bound `φ_ω` for a selection of a class. -/
noncomputable def classTerm (cls : Choice T → Option ι) (phi : Choice T → ℝ) (B : ℝ)
    (π : ∀ b, T b → ChangeType → ℝ) (ω : Choice T) : ℝ :=
  if cls ω = none then B * monomial π ω else phi ω

/-- **The summand of `hΨ` against the replaced bound** (`prop:closing-data`(d), the variance and
envelope classes). Let `B ≤ c_ω` and `ω` be in no replaced degree class whenever `ω` is in no class;
let `φ_ω ≤ c_ω π_ω` for the selections of a class outside the replaced degree classes (the variance
classes, class costs `B' − g`); and let every selection of a replaced degree class `𝒞_n` be in a
class with `φ_ω ≤ C_n π^arm_ω + B'(π^tot_ω − π^lead_ω)` (`thm:envelopes`(i), `cor:envelope-costs`).
Then `b_ω ≤ replacedBound(ω)` for every selection. -/
theorem classTerm_le_replacedBound {π : ∀ b, T b → ChangeType → ℝ} (hπ : ∀ b t e, 0 ≤ π b t e)
    (cls : Choice T → Option ι) (phi : Choice T → ℝ) (B : ℝ)
    (kind : PriceVar T → Option L) (N : Finset (L → ℕ)) (C : (L → ℕ) → ℝ) (B' : ℝ)
    (yarm ylead yrem : PriceVar T → ℝ) (cost : Choice T → ℝ)
    (hnone : ∀ ω, IsSelection ω → cls ω = none →
      (∀ n ∈ N, selMono ω ∉ kindMonos kind n) ∧ B ≤ cost ω)
    (hvar : ∀ ω, IsSelection ω → cls ω ≠ none → (∀ n ∈ N, selMono ω ∉ kindMonos kind n) →
      phi ω ≤ cost ω * monomial π ω)
    (hrep : ∀ ω, IsSelection ω → ∀ n ∈ N, selMono ω ∈ kindMonos kind n →
      cls ω ≠ none ∧ phi ω ≤ replacementBound (C n) B' yarm ylead yrem ω)
    (ω : Choice T) (hω : IsSelection ω) :
    classTerm cls phi B π ω ≤ replacedBound kind N C B' yarm ylead yrem cost π ω := by
  classical
  unfold classTerm replacedBound
  by_cases hU : selMono ω ∈ N.biUnion (kindMonos kind)
  · obtain ⟨n, hn, hmn⟩ := mem_biUnion.mp hU
    obtain ⟨hcls, hphi⟩ := hrep ω hω n hn hmn
    rw [ite_eq_right hcls, ite_eq_left hU, degreeOf_of_mem hmn]
    exact hphi
  · rw [ite_eq_right hU]
    have hout : ∀ n ∈ N, selMono ω ∉ kindMonos kind n := fun n hn hmn =>
      hU (mem_biUnion.mpr ⟨n, hn, hmn⟩)
    by_cases hc : cls ω = none
    · rw [ite_eq_left hc]
      exact mul_le_mul_of_nonneg_right (hnone ω hω hc).2 (monomial_nonneg hπ ω)
    · rw [ite_eq_right hc]
      exact hvar ω hω hc hout

/-- **The class algebra at upper prices** (`prop:closing-data`(d); `lem:record:record-expansion`
(ii)–(v), `rem:cp:monotone`). Under the pointwise comparison of `classTerm_le_replacedBound` and the
hypotheses of WP-R's `replacement_le_upper` (the completion polynomial `𝒟` of the variance classes
with `0 ≤ d_m`, `d_m ≤ B' − c_ω` on the selections outside the replaced classes, `d_m ≤ B' c_m`
elsewhere and `d_m = 0` on the replaced classes; nonnegative costs `C_n`, auxiliary prices and costs
outside the classes), the sum of `hΨ` is at most `B'(e^Ŝ cosh Â − 1) − 𝒟(π̂) − ∑_n saving_n(π̂, ŷ)`.
-/
theorem sum_classTerm_le_upper {π πu : ∀ b, T b → ChangeType → ℝ} (hπ : ∀ b t e, 0 ≤ π b t e)
    (hle : ∀ b t e, π b t e ≤ πu b t e)
    (cls : Choice T → Option ι) (phi : Choice T → ℝ) (B : ℝ)
    (kind : PriceVar T → Option L) (hkind : ∀ v l, kind v = some l → v.2.2 = .skew)
    (N : Finset (L → ℕ)) (hN : ∀ n ∈ N, n ≠ 0 ∧ Even (∑ l, n l))
    (C : (L → ℕ) → ℝ) (hC : ∀ n ∈ N, 0 ≤ C n)
    {yarm ylead yrem yarmu yleadu yremu : PriceVar T → ℝ}
    (harm : ∀ v, 0 ≤ yarm v) (hlead : ∀ v, 0 ≤ ylead v) (hrem : ∀ v, 0 ≤ yrem v)
    (harmu : ∀ v, yarm v ≤ yarmu v) (hleadu : ∀ v, ylead v ≤ yleadu v)
    (hremu : ∀ v, yrem v ≤ yremu v)
    (cost : Choice T → ℝ)
    (hcost : ∀ ω, IsSelection ω → (∀ n ∈ N, selMono ω ∉ kindMonos kind n) → 0 ≤ cost ω)
    {B' : ℝ} (hB' : 0 ≤ B')
    (supp : Finset (PriceVar T → ℕ)) (d : (PriceVar T → ℕ) → ℝ) (hd : ∀ m, 0 ≤ d m)
    (hd0 : ∀ n ∈ N, ∀ m ∈ kindMonos kind n, d m = 0)
    (hsel : ∀ ω, IsSelection ω → (∀ n ∈ N, selMono ω ∉ kindMonos kind n) →
      d (selMono ω) ≤ B' - cost ω)
    (hoth : ∀ m, (∀ ω, IsSelection ω → selMono ω ≠ m) → d m ≤ B' * expCoeff m)
    (hnone : ∀ ω, IsSelection ω → cls ω = none →
      (∀ n ∈ N, selMono ω ∉ kindMonos kind n) ∧ B ≤ cost ω)
    (hvar : ∀ ω, IsSelection ω → cls ω ≠ none → (∀ n ∈ N, selMono ω ∉ kindMonos kind n) →
      phi ω ≤ cost ω * monomial π ω)
    (hrep : ∀ ω, IsSelection ω → ∀ n ∈ N, selMono ω ∈ kindMonos kind n →
      cls ω ≠ none ∧ phi ω ≤ replacementBound (C n) B' yarm ylead yrem ω) :
    ∑ ω ∈ univ.filter (fun ω : Choice T => IsSelection ω), classTerm cls phi B π ω ≤
      B' * (Real.exp (∑ b, symTotal πu b) * Real.cosh (∑ b, skewTotal πu b) - 1) -
        ∑ m ∈ supp, d m * mono (priceVec πu) m -
        ∑ n ∈ N, replacementSaving kind n (C n) B' (priceVec πu) yarmu yleadu yremu := by
  have h1 : ∑ ω ∈ univ.filter (fun ω : Choice T => IsSelection ω), classTerm cls phi B π ω ≤
      ∑ ω ∈ univ.filter (fun ω : Choice T => IsSelection ω),
        replacedBound kind N C B' yarm ylead yrem cost π ω :=
    sum_le_sum fun ω hω => classTerm_le_replacedBound hπ cls phi B kind N C B' yarm ylead yrem
      cost hnone hvar hrep ω (mem_filter.mp hω).2
  rw [sum_replacedBound] at h1
  exact h1.trans (replacement_le_upper hπ hle kind hkind N hN C hC harm hlead hrem harmu hleadu
    hremu cost hcost hB' supp d hd hd0 hsel hoth)

omit [DecidableEq J] [∀ b, DecidableEq (T b)] in
/-- The totals of upper prices are nonnegative. -/
theorem sum_skewTotal_nonneg {πu : ∀ b, T b → ChangeType → ℝ} (h : ∀ b t e, 0 ≤ πu b t e) :
    0 ≤ ∑ b, skewTotal πu b :=
  sum_nonneg fun b _ => sum_nonneg fun t _ => h b t _

/-- **The evaluation against the ledger** (`prop:closing-data`(d), conclusion: `Ψ(π̂, ŷ) ≤ B(e^S
cosh A − 1) − D = 𝓔`): if `B' ≤ l.B`, the totals of the upper prices are at most `l.S` and `l.A`
(and nonnegative), and `𝒟(π̂) + ∑_n saving_n(π̂, ŷ) ≥ l.D`, then `B'(e^Ŝ cosh Â − 1) − 𝒟(π̂) − ∑_n
saving_n ≤ l.E`. -/
theorem completed_le_E (l : PrimitiveLedger) {B' Ŝ Â X : ℝ} (hB' : 0 ≤ B') (hBl : B' ≤ l.B)
    (hS0 : 0 ≤ Ŝ) (hS : Ŝ ≤ l.S) (hA0 : 0 ≤ Â) (hA : Â ≤ l.A) (hX : l.D ≤ X) :
    B' * (Real.exp Ŝ * Real.cosh Â - 1) - X ≤ l.E := by
  unfold PrimitiveLedger.E
  have hle := TheoremC.exp_mul_cosh_le_of_le hS hA0 hA
  have h1 : 1 ≤ Real.exp Ŝ * Real.cosh Â :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_exp hS0) (Real.one_le_cosh _)
  have hBB : B' * (Real.exp Ŝ * Real.cosh Â - 1) ≤ l.B * (Real.exp l.S * Real.cosh l.A - 1) :=
    mul_le_mul hBl (by linarith) (by linarith) (hB'.trans hBl)
  linarith

end Generic

/-! ### The saving of a degree class depends only on the kind totals -/

section Totals

variable {L : Type*} [Fintype L]

/-- **The saving of a degree class from the kind totals** (`def:closing-quantities`(8)): `D_n =
(1/n!)[B' ∏ A_l^{n_l} − C_n ∏ (A^arm_l)^{n_l} − B'(∏ (A^lead_l + A^rem_l)^{n_l} − ∏
(A^lead_l)^{n_l})]`, with `n! = ∏_l n_l!`. -/
noncomputable def savingOfTotals (n : L → ℕ) (Cn B' : ℝ) (Atot Aarm Alead Arem : L → ℝ) : ℝ :=
  (B' * ∏ l, Atot l ^ n l - Cn * ∏ l, Aarm l ^ n l -
    B' * (∏ l, (Alead l + Arem l) ^ n l - ∏ l, Alead l ^ n l)) / (degFact n : ℝ)

/-- **The saving is monotone in the totals** (`lem:record:record-expansion`(iii)): it increases
with the full totals `A_l` and decreases with the raw-arm, leading and remainder totals, for
`C_n, B' ≥ 0` and nonnegative totals (`prod_add_pow_sub_mono`). -/
theorem savingOfTotals_mono [DecidableEq L] (n : L → ℕ) {Cn B' : ℝ} (hC : 0 ≤ Cn) (hB : 0 ≤ B')
    {A₀ a₀ l₀ r₀ A a l r : L → ℝ} (hA₀ : ∀ i, 0 ≤ A₀ i) (hA : ∀ i, A₀ i ≤ A i)
    (ha : ∀ i, 0 ≤ a i) (ha₀ : ∀ i, a i ≤ a₀ i) (hl : ∀ i, 0 ≤ l i) (hl₀ : ∀ i, l i ≤ l₀ i)
    (hr : ∀ i, 0 ≤ r i) (hr₀ : ∀ i, r i ≤ r₀ i) :
    savingOfTotals n Cn B' A₀ a₀ l₀ r₀ ≤ savingOfTotals n Cn B' A a l r := by
  unfold savingOfTotals
  have hd : (0 : ℝ) < (degFact n : ℝ) := by
    have : 0 < degFact n := Finset.prod_pos fun i _ => Nat.factorial_pos _
    exact_mod_cast this
  apply div_le_div_of_nonneg_right _ hd.le
  have h1 : ∏ i, A₀ i ^ n i ≤ ∏ i, A i ^ n i :=
    Finset.prod_le_prod₀ (fun i _ => pow_nonneg (hA₀ i) _)
      (fun i _ => pow_le_pow_left₀ (hA₀ i) (hA i) _)
  have h2 : ∏ i, a i ^ n i ≤ ∏ i, a₀ i ^ n i :=
    Finset.prod_le_prod₀ (fun i _ => pow_nonneg (ha i) _)
      (fun i _ => pow_le_pow_left₀ (ha i) (ha₀ i) _)
  have h3 := (prod_add_pow_sub_mono univ n hl hr hl₀ hr₀).2
  have e1 := mul_le_mul_of_nonneg_left h1 hB
  have e2 := mul_le_mul_of_nonneg_left h2 hC
  have e3 := mul_le_mul_of_nonneg_left h3 hB
  linarith

variable {J : Type*} [Fintype J] {T : J → Type*} [∀ b, Fintype (T b)] [DecidableEq L]

/-- `replacementSaving` is `savingOfTotals` at the kind totals. -/
theorem replacementSaving_eq_totals (kind : PriceVar T → Option L) (n : L → ℕ) (Cn B' : ℝ)
    (x yarm ylead yrem : PriceVar T → ℝ) :
    replacementSaving kind n Cn B' x yarm ylead yrem =
      savingOfTotals n Cn B' (kindTotal kind x) (kindTotal kind yarm) (kindTotal kind ylead)
        (kindTotal kind yrem) := rfl

end Totals

end Sarkozy.ClassBoundsPaper
