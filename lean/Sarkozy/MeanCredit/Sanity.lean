module

public import Sarkozy.MeanCredit.Evaluation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

@[expose] public section

/-!
# Sanity: the completion and a closed-form evaluation recover the record-expansion bound

`paper/sections/10_comparison_lemmas.tex`, `lem:record:record-expansion`(ii);
`paper/sections/24a_joint_mean.tex`, `prop:joint-middle-mean` (the completion).

With the letters given by the change type (`sym`, `skew`) and the coefficient `1` on every nonzero
letter degree of even skew degree, the completed series is `e^{X_sym} cosh X_skew − 1`
(**`hasSum_selections`**, via the exponential and `cosh` series). Combined with `completion_le`
this gives **`selections_le_of_completion`**: `∑ c π_ω ≤ c (e^{X_sym} cosh X_skew − 1)` over the
choices of nonzero even-skew degree. This is the bound of
`RecordExpansion.sum_monomial_selections_le`: those choices are its selections, and
`X_sym = ∑ s_b`, `X_skew = ∑ a_b` (this identification is not formalized here). So the
completion step with a closed-form evaluation loses nothing on the comparison side without classes,
and `SeriesBound` is satisfiable in closed form (`seriesBound_of_hasSum`). This is a consistency
check of the framework, not a new paper result.
-/

open Finset

namespace Sarkozy.MeanCredit

open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice

theorem prod_changeType {M : Type*} [CommMonoid M] (f : ChangeType → M) :
    ∏ e, f e = f .sym * f .skew := by
  change ∏ e ∈ {ChangeType.sym, ChangeType.skew}, f e = _
  rw [Finset.prod_pair (by decide)]

/-- The even part of the exponential series is `cosh`. -/
theorem hasSum_even_exp (A : ℝ) :
    HasSum (fun b : ℕ => (if Even b then A ^ b / b.factorial else 0)) (Real.cosh A) := by
  have h := Real.hasSum_cosh A
  have hinj : Function.Injective (fun n : ℕ => 2 * n) := fun m n hmn => by
    simpa using hmn
  rw [← hinj.hasSum_iff]
  · convert h using 1
    funext n
    simp
  · intro b hb
    have hodd : ¬ Even b := by
      rintro ⟨k, rfl⟩
      exact hb ⟨k, by ring⟩
    simp [hodd]

/-- The letter degree of a choice entry by its change type. -/
def ctDeg (d : ChangeType → ℕ) : ℕ × ℕ := (d .sym, d .skew)

/-- The inverse of `ctDeg`. -/
def ctOf (x : ℕ × ℕ) : ChangeType → ℕ := fun e => match e with
  | .sym => x.1
  | .skew => x.2

/-- Degrees in the change types are pairs. -/
def ctEquiv : (ChangeType → ℕ) ≃ ℕ × ℕ where
  toFun := ctDeg
  invFun := ctOf
  left_inv d := funext fun e => by cases e <;> rfl
  right_inv x := rfl

/-- The letter totals `S` (symmetric) and `A` (skew). -/
def ctTot (S A : ℝ) : ChangeType → ℝ := fun e => match e with
  | .sym => S
  | .skew => A

theorem ctOf_ne_zero (a b : ℕ) : ctOf (a, b) ≠ 0 ↔ ¬ (a = 0 ∧ b = 0) := by
  constructor
  · rintro h ⟨rfl, rfl⟩
    exact h (funext fun e => by cases e <;> rfl)
  · intro h h0
    exact h ⟨congrFun h0 .sym, congrFun h0 .skew⟩

/-- **The completed comparison series without classes** (`lem:record:record-expansion`(ii)): with
the letters `sym`, `skew` (totals `S`, `A`) and coefficient `1` on every nonzero degree of even skew
degree, the completed series is `e^S cosh A − 1`. -/
theorem hasSum_selections (S A : ℝ) (hS : 0 ≤ S) (hA : 0 ≤ A) :
    HasSum (fun d : ChangeType → ℕ =>
        (if d ≠ 0 ∧ Even (d .skew) then (1 : ℝ) else 0) *
          ∏ l, ctTot S A l ^ d l / (d l).factorial)
      (Real.exp S * Real.cosh A - 1) := by
  set g : ℕ → ℝ := fun a => S ^ a / a.factorial with hg
  set k : ℕ → ℝ := fun b => if Even b then A ^ b / b.factorial else 0 with hk
  have hgs : HasSum g (Real.exp S) := by
    have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) S
    rwa [← Real.exp_eq_exp_ℝ] at h
  have hks : HasSum k (Real.cosh A) := hasSum_even_exp A
  have hg0 : ∀ a, 0 ≤ g a := fun a => by positivity
  have hk0 : ∀ b, 0 ≤ k b := fun b => by
    simp only [hk]; split_ifs <;> positivity
  have hsum : Summable fun x : ℕ × ℕ => g x.1 * k x.2 :=
    summable_mul_of_summable_norm (by simpa [Real.norm_eq_abs, abs_of_nonneg (hg0 _)] using
      hgs.summable) (by simpa [Real.norm_eq_abs, abs_of_nonneg (hk0 _)] using hks.summable)
  have hprod := hgs.mul hks hsum
  have h1 : HasSum (fun x : ℕ × ℕ => if x = (0, 0) then (1 : ℝ) else 0) 1 := hasSum_ite_eq _ _
  have h2 := hprod.sub h1
  rw [← ctEquiv.symm.hasSum_iff]
  convert h2 using 1
  funext x
  obtain ⟨a, b⟩ := x
  have e1 : (ctEquiv.symm (a, b)) = ctOf (a, b) := rfl
  simp only [Function.comp, e1, prod_changeType]
  have es : ctOf (a, b) .sym = a := rfl
  have ek : ctOf (a, b) .skew = b := rfl
  have ts : ctTot S A .sym = S := rfl
  have tk : ctTot S A .skew = A := rfl
  rw [es, ek, ts, tk]
  by_cases h0 : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := h0
    have hz : ¬ (ctOf (0, 0) ≠ 0) := fun h => ((ctOf_ne_zero 0 0).mp h) ⟨rfl, rfl⟩
    simp [hz, hg, hk]
  · have hz : ctOf (a, b) ≠ 0 := (ctOf_ne_zero a b).mpr h0
    have hne : (a, b) ≠ ((0 : ℕ), (0 : ℕ)) := fun h => h0 ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    by_cases hb : Even b
    · simp [hz, hb, hne, hg, hk]
    · simp [hb, hne, hg, hk]

/-- **Sanity: the completion and the closed form recover the record-expansion bound**
(`lem:record:record-expansion`(ii) without classes): for the letters given by the change type,
the choices of nonzero letter degree with even skew degree (the selections) have
`∑ c π_ω ≤ c (e^{X_sym} cosh X_skew − 1)`. -/
theorem selections_le_of_completion {J : Type*} [Fintype J] [DecidableEq J] {T : J → Type*}
    [∀ b, Fintype (T b)] [∀ b, DecidableEq (T b)] {π : ∀ b, T b → ChangeType → ℝ}
    (hπ : ∀ b t e, 0 ≤ π b t e) (c : ℝ) (hc : 0 ≤ c) :
    ∑ ω ∈ univ.filter (fun ω : Choice T => deg (fun e : Entry T => e.2.2) ω ≠ 0 ∧
        Even (deg (fun e : Entry T => e.2.2) ω .skew)), c * monomial π ω ≤
      c * (Real.exp (letterTotal (fun e : Entry T => e.2.2) π .sym) *
        Real.cosh (letterTotal (fun e : Entry T => e.2.2) π .skew) - 1) := by
  set ℓ : Entry T → ChangeType := fun e => e.2.2
  set S := univ.filter (fun ω : Choice T => deg ℓ ω ≠ 0 ∧ Even (deg ℓ ω .skew))
  set R : (ChangeType → ℕ) → ℝ := fun d => c * (if d ≠ 0 ∧ Even (d .skew) then 1 else 0)
  have hX0 : ∀ l, 0 ≤ letterTotal ℓ π l := fun l => sum_nonneg fun _ _ => hπ _ _ _
  have hp : ∀ d : ChangeType → ℕ, ∏ l, letterTotal ℓ π l ^ d l / ((d l).factorial : ℝ) =
      ∏ l, ctTot (letterTotal ℓ π .sym) (letterTotal ℓ π .skew) l ^ d l / ((d l).factorial : ℝ) :=
    fun d => prod_congr rfl fun l _ => by cases l <;> rfl
  have h1 := completion_le ℓ hπ S (S.image (deg ℓ)) (fun ω hω => mem_image_of_mem _ hω) R
    (fun d _ => mul_nonneg hc (by split_ifs <;> norm_num))
  have e1 : ∑ ω ∈ S, R (deg ℓ ω) * monomial π ω = ∑ ω ∈ S, c * monomial π ω :=
    sum_congr rfl fun ω hω => by
      have h := (mem_filter.mp hω).2
      have e : R (deg ℓ ω) = c := by
        change c * (if deg ℓ ω ≠ 0 ∧ Even (deg ℓ ω .skew) then 1 else 0) = c
        simp only [h, ne_eq, not_false_eq_true, and_self, ↓reduceIte, mul_one]
      rw [e]
  have hs := ((hasSum_selections _ _ (hX0 .sym) (hX0 .skew)).mul_left c)
  have hs' : HasSum (fun d => R d * completedMono ℓ π d)
      (c * (Real.exp (letterTotal ℓ π .sym) * Real.cosh (letterTotal ℓ π .skew) - 1)) := by
    convert hs using 1
    funext d
    simp only [R, completedMono]
    rw [hp d]
    ring
  have h2 := sum_le_hasSum (S.image (deg ℓ)) (fun d _ =>
    mul_nonneg (mul_nonneg hc (by split_ifs <;> norm_num)) (completedMono_nonneg ℓ hπ d)) hs'
  rw [e1] at h1
  exact h1.trans h2

end Sarkozy.MeanCredit
