module

public import Sarkozy.FiniteProbability
public import Mathlib.Algebra.BigOperators.Field

/-!
# Peyre's tensorization in finite form, I: conditional expectations

This file formalizes the conventions `sec:peyre:conv` of the paper's Appendix B
(`app:peyre`, file `paper/sections/B_peyre_finite.tex`): spaces of functions
of random variables, conditional expectations as level-set averages, the
facts (P1)–(P3), and conditioning on an event of positive probability.

## Representation choices

* The probability space is a finite type `Ω` with a `Sarkozy.FiniteLaw`, i.e.
  nonnegative weights summing to one.  Zero weights are **allowed**: instead of
  the paper's reduction to full support, statements that hold only on the
  support are stated "almost everywhere", i.e. at every `ω` with
  `μ.weight ω ≠ 0`.  Conditioning on an event `E` of positive probability is
  the law `condLaw μ E h` on the *same* type `Ω` (weights `1_E μ / μ(E)`), so no
  subtypes are needed.
* A random variable is a function `Z : Ω → γ` into an arbitrary type.  The
  space `L²(Z)` is represented by the predicate `IsFunOf Z h` ("`h` is constant
  on the level sets of `Z`").  `L²(Z) ⊆ L²(W)` is `Coarser Z W`.
* `condExp μ Z f ω` is the average of `f` over the level set of `Z` through
  `ω` (and `0` on a level set of mass zero, by Lean's convention `x / 0 = 0`).
  This is the paper's explicit formula for `E[f | Z]`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Peyre

open Sarkozy

variable {Ω : Type*}

/-! ### Functions of random variables -/

/-- `IsFunOf Z h`: the real function `h` on `Ω` is a function of `Z`, i.e. it is
constant on every level set of `Z`.  This is membership in `L²(Z)`. -/
def IsFunOf {γ : Type*} (Z : Ω → γ) (h : Ω → ℝ) : Prop :=
  ∀ ω ω', Z ω = Z ω' → h ω = h ω'

/-- `Coarser Z W`: `Z` is a function of `W`; equivalently `L²(Z) ⊆ L²(W)`. -/
def Coarser {γ δ : Type*} (Z : Ω → γ) (W : Ω → δ) : Prop :=
  ∀ ω ω', W ω = W ω' → Z ω = Z ω'

section IsFunOf

variable {γ δ ε : Type*}

theorem IsFunOf.mono {Z : Ω → γ} {W : Ω → δ} {h : Ω → ℝ} (hh : IsFunOf Z h)
    (hZW : Coarser Z W) : IsFunOf W h :=
  fun ω ω' hw => hh ω ω' (hZW ω ω' hw)

theorem IsFunOf.sub {Z : Ω → γ} {f g : Ω → ℝ} (hf : IsFunOf Z f) (hg : IsFunOf Z g) :
    IsFunOf Z (fun ω => f ω - g ω) :=
  fun ω ω' h => by simp only [hf ω ω' h, hg ω ω' h]

theorem IsFunOf.mul {Z : Ω → γ} {f g : Ω → ℝ} (hf : IsFunOf Z f) (hg : IsFunOf Z g) :
    IsFunOf Z (fun ω => f ω * g ω) :=
  fun ω ω' h => by simp only [hf ω ω' h, hg ω ω' h]

theorem isFunOf_const (Z : Ω → γ) (c : ℝ) : IsFunOf Z (fun _ => c) :=
  fun _ _ _ => rfl

theorem isFunOf_comp (Z : Ω → γ) (φ : γ → ℝ) : IsFunOf Z (fun ω => φ (Z ω)) :=
  fun _ _ h => congrArg φ h

theorem Coarser.refl (Z : Ω → γ) : Coarser Z Z := fun _ _ h => h

theorem Coarser.trans {Z : Ω → γ} {W : Ω → δ} {V : Ω → ε} (h₁ : Coarser Z W)
    (h₂ : Coarser W V) : Coarser Z V :=
  fun ω ω' h => h₁ ω ω' (h₂ ω ω' h)

theorem coarser_fst (Z : Ω → γ) (W : Ω → δ) : Coarser Z (fun ω => (Z ω, W ω)) :=
  fun _ _ h => (Prod.ext_iff.mp h).1

theorem coarser_snd (Z : Ω → γ) (W : Ω → δ) : Coarser W (fun ω => (Z ω, W ω)) :=
  fun _ _ h => (Prod.ext_iff.mp h).2

/-- A function constant on the level sets of `X` inside an event `E` agrees on `E`
with a function of the values of `X` (uses choice). -/
theorem exists_fun_on {α : Type*} (X : Ω → α) (E : Ω → Prop) (F : Ω → ℝ)
    (hF : ∀ ω ω', E ω → E ω' → X ω = X ω' → F ω = F ω') :
    ∃ φ : α → ℝ, ∀ ω, E ω → F ω = φ (X ω) := by
  classical
  refine ⟨fun a => if h : ∃ ω, E ω ∧ X ω = a then F (Classical.choose h) else 0, ?_⟩
  intro ω hω
  have hex : ∃ ω', E ω' ∧ X ω' = X ω := ⟨ω, hω, rfl⟩
  simp only [hex, dite_true]
  have hs := Classical.choose_spec hex
  exact (hF _ _ hs.1 hω hs.2).symm

theorem exists_fun_of_isFunOf {α : Type*} (X : Ω → α) (F : Ω → ℝ) (hF : IsFunOf X F) :
    ∃ φ : α → ℝ, ∀ ω, F ω = φ (X ω) := by
  obtain ⟨φ, hφ⟩ := exists_fun_on X (fun _ => True) F (fun ω ω' _ _ h => hF ω ω' h)
  exact ⟨φ, fun ω => hφ ω trivial⟩

end IsFunOf

/-! ### Indicators, probabilities, almost-everywhere statements -/

open Classical in
/-- The indicator function of an event (a predicate on `Ω`). -/
noncomputable def ind (E : Ω → Prop) (ω : Ω) : ℝ := if E ω then 1 else 0

theorem ind_of_pos {E : Ω → Prop} {ω : Ω} (h : E ω) : ind E ω = 1 := by
  classical
  simp [ind, h]

theorem ind_of_neg {E : Ω → Prop} {ω : Ω} (h : ¬ E ω) : ind E ω = 0 := by
  classical
  simp [ind, h]

theorem ind_nonneg (E : Ω → Prop) (ω : Ω) : 0 ≤ ind E ω := by
  by_cases h : E ω
  · rw [ind_of_pos h]; exact zero_le_one
  · rw [ind_of_neg h]

theorem ind_le_one (E : Ω → Prop) (ω : Ω) : ind E ω ≤ 1 := by
  by_cases h : E ω
  · rw [ind_of_pos h]
  · rw [ind_of_neg h]; exact zero_le_one

theorem ind_and (E F : Ω → Prop) (ω : Ω) :
    ind (fun ω => E ω ∧ F ω) ω = ind E ω * ind F ω := by
  by_cases hE : E ω <;> by_cases hF : F ω <;>
    simp [ind_of_pos, ind_of_neg, hE, hF]

theorem ind_congr {E F : Ω → Prop} (h : ∀ ω, E ω ↔ F ω) : ind E = ind F := by
  have : E = F := funext fun ω => propext (h ω)
  rw [this]

variable [Fintype Ω]

/-- The probability of an event. -/
noncomputable def prob (μ : FiniteLaw Ω) (E : Ω → Prop) : ℝ := μ.expect (ind E)

theorem prob_nonneg (μ : FiniteLaw Ω) (E : Ω → Prop) : 0 ≤ prob μ E :=
  μ.expect_nonneg (ind_nonneg E)

theorem weight_le_prob (μ : FiniteLaw Ω) {E : Ω → Prop} {ω : Ω} (h : E ω) :
    μ.weight ω ≤ prob μ E := by
  unfold prob FiniteLaw.expect
  have hle : μ.weight ω * ind E ω ≤ ∑ ω', μ.weight ω' * ind E ω' :=
    Finset.single_le_sum (f := fun ω' => μ.weight ω' * ind E ω')
      (fun ω' _ => mul_nonneg (μ.nonneg ω') (ind_nonneg E ω')) (Finset.mem_univ ω)
  rwa [ind_of_pos h, mul_one] at hle

theorem prob_pos_of_weight {μ : FiniteLaw Ω} {E : Ω → Prop} {ω : Ω} (h : E ω)
    (hw : μ.weight ω ≠ 0) : 0 < prob μ E :=
  lt_of_lt_of_le (lt_of_le_of_ne (μ.nonneg ω) (Ne.symm hw)) (weight_le_prob μ h)

theorem exists_of_prob_pos {μ : FiniteLaw Ω} {E : Ω → Prop} (h : 0 < prob μ E) :
    ∃ ω, E ω ∧ μ.weight ω ≠ 0 := by
  by_contra hne'
  have hne : ∀ ω, E ω → μ.weight ω = 0 := fun ω hω => by
    by_contra hw
    exact hne' ⟨ω, hω, hw⟩
  have : prob μ E = 0 := by
    unfold prob FiniteLaw.expect
    refine Finset.sum_eq_zero (fun ω _ => ?_)
    by_cases hE : E ω
    · rw [hne ω hE, zero_mul]
    · rw [ind_of_neg hE, mul_zero]
  linarith

theorem expect_congr_ae (μ : FiniteLaw Ω) {f g : Ω → ℝ}
    (h : ∀ ω, μ.weight ω ≠ 0 → f ω = g ω) : μ.expect f = μ.expect g := by
  unfold FiniteLaw.expect
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  by_cases hw : μ.weight ω = 0
  · rw [hw, zero_mul, zero_mul]
  · rw [h ω hw]

theorem expect_mono_ae (μ : FiniteLaw Ω) {f g : Ω → ℝ}
    (h : ∀ ω, μ.weight ω ≠ 0 → f ω ≤ g ω) : μ.expect f ≤ μ.expect g := by
  unfold FiniteLaw.expect
  refine Finset.sum_le_sum (fun ω _ => ?_)
  by_cases hw : μ.weight ω = 0
  · rw [hw, zero_mul, zero_mul]
  · exact mul_le_mul_of_nonneg_left (h ω hw) (μ.nonneg ω)

theorem expect_eq_zero_ae (μ : FiniteLaw Ω) {f : Ω → ℝ}
    (h : ∀ ω, μ.weight ω ≠ 0 → f ω = 0) : μ.expect f = 0 := by
  rw [expect_congr_ae μ h, FiniteLaw.expect_const]

theorem expect_sum (μ : FiniteLaw Ω) {ι : Type*} (s : Finset ι) (F : ι → Ω → ℝ) :
    μ.expect (fun ω => ∑ i ∈ s, F i ω) = ∑ i ∈ s, μ.expect (F i) := by
  unfold FiniteLaw.expect
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

theorem expect_sq_nonneg (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    0 ≤ μ.expect (fun ω => f ω ^ 2) := μ.second_moment_nonneg f

/-! ### Conditional expectation given a random variable -/

section CondExp

variable {γ δ : Type*}

/-- The level set of `Z` through `ω`, as an event. -/
def lv (Z : Ω → γ) (ω : Ω) : Ω → Prop := fun ω' => Z ω' = Z ω

/-- `E[f | Z]`: at `ω`, the `μ`-average of `f` over the level set of `Z` through `ω`
(paper, `sec:peyre:conv`: `E[f | Z](ω) = E[f 1_{Z = Z(ω)}] / P(Z = Z(ω))`). -/
noncomputable def condExp (μ : FiniteLaw Ω) (Z : Ω → γ) (f : Ω → ℝ) (ω : Ω) : ℝ :=
  μ.expect (fun ω' => ind (lv Z ω) ω' * f ω') / prob μ (lv Z ω)

omit [Fintype Ω] in
theorem lv_eq_of_eq {Z : Ω → γ} {ω ω' : Ω} (h : Z ω = Z ω') : lv Z ω = lv Z ω' := by
  funext x
  simp only [lv, h]

omit [Fintype Ω] in
theorem ind_lv_symm (Z : Ω → γ) (ω ω' : Ω) : ind (lv Z ω) ω' = ind (lv Z ω') ω := by
  by_cases h : Z ω' = Z ω
  · rw [ind_of_pos (show lv Z ω ω' from h), ind_of_pos (show lv Z ω' ω from h.symm)]
  · rw [ind_of_neg (show ¬ lv Z ω ω' from h),
      ind_of_neg (show ¬ lv Z ω' ω from fun h' => h h'.symm)]

theorem condExp_isFunOf (μ : FiniteLaw Ω) (Z : Ω → γ) (f : Ω → ℝ) :
    IsFunOf Z (condExp μ Z f) := by
  intro ω ω' h
  simp only [condExp, lv_eq_of_eq h]

/-- The defining property of `E[f | Z]` (orthogonality, (P2)): for `h ∈ L²(Z)`,
`E[E[f|Z] h] = E[f h]`. -/
theorem expect_condExp_mul (μ : FiniteLaw Ω) (Z : Ω → γ) (f h : Ω → ℝ)
    (hh : IsFunOf Z h) :
    μ.expect (fun ω => condExp μ Z f ω * h ω) = μ.expect (fun ω => f ω * h ω) := by
  -- pointwise identity for the inner sum
  have key : ∀ ω', μ.weight ω' *
      (∑ ω, μ.weight ω * ind (lv Z ω) ω' * h ω / prob μ (lv Z ω)) = μ.weight ω' * h ω' := by
    intro ω'
    have hin : ∀ ω, μ.weight ω * ind (lv Z ω) ω' * h ω / prob μ (lv Z ω) =
        μ.weight ω * ind (lv Z ω') ω * (h ω' / prob μ (lv Z ω')) := by
      intro ω
      by_cases hz : Z ω' = Z ω
      · rw [hh ω ω' hz.symm, lv_eq_of_eq hz.symm, ind_of_pos (show lv Z ω' ω' from rfl),
          ind_of_pos (show lv Z ω' ω from hz.symm)]
        ring
      · rw [ind_of_neg (show ¬ lv Z ω ω' from hz),
          ind_of_neg (show ¬ lv Z ω' ω from fun h' => hz h'.symm)]
        ring
    simp_rw [hin]
    rw [← Finset.sum_mul]
    have hP : (∑ ω, μ.weight ω * ind (lv Z ω') ω) = prob μ (lv Z ω') := rfl
    rw [hP]
    by_cases hp : prob μ (lv Z ω') = 0
    · have hw : μ.weight ω' = 0 :=
        le_antisymm (hp ▸ weight_le_prob μ (show lv Z ω' ω' from rfl)) (μ.nonneg ω')
      rw [hw, zero_mul, zero_mul]
    · field_simp
  unfold condExp FiniteLaw.expect
  calc
    ∑ ω, μ.weight ω * ((∑ ω', μ.weight ω' * (ind (lv Z ω) ω' * f ω')) /
        prob μ (lv Z ω) * h ω)
        = ∑ ω, ∑ ω', μ.weight ω' * f ω' *
            (μ.weight ω * ind (lv Z ω) ω' * h ω / prob μ (lv Z ω)) := by
          refine Finset.sum_congr rfl (fun ω _ => ?_)
          rw [Finset.sum_div, Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun ω' _ => ?_)
          ring
    _ = ∑ ω', ∑ ω, μ.weight ω' * f ω' *
            (μ.weight ω * ind (lv Z ω) ω' * h ω / prob μ (lv Z ω)) := Finset.sum_comm
    _ = ∑ ω', f ω' * (μ.weight ω' *
            ∑ ω, μ.weight ω * ind (lv Z ω) ω' * h ω / prob μ (lv Z ω)) := by
          refine Finset.sum_congr rfl (fun ω' _ => ?_)
          rw [← Finset.mul_sum]
          ring
    _ = ∑ ω', μ.weight ω' * (f ω' * h ω') := by
          refine Finset.sum_congr rfl (fun ω' _ => ?_)
          rw [key ω']
          ring

theorem expect_mul_condExp (μ : FiniteLaw Ω) (Z : Ω → γ) (f h : Ω → ℝ)
    (hh : IsFunOf Z h) :
    μ.expect (fun ω => h ω * condExp μ Z f ω) = μ.expect (fun ω => h ω * f ω) := by
  have := expect_condExp_mul μ Z f h hh
  simpa only [mul_comm] using this

/-- `E[E[f|Z]] = E[f]`. -/
theorem expect_condExp (μ : FiniteLaw Ω) (Z : Ω → γ) (f : Ω → ℝ) :
    μ.expect (condExp μ Z f) = μ.expect f := by
  have := expect_condExp_mul μ Z f (fun _ => 1) (isFunOf_const Z 1)
  simpa only [mul_one] using this

theorem condExp_sub (μ : FiniteLaw Ω) (Z : Ω → γ) (f g : Ω → ℝ) (ω : Ω) :
    condExp μ Z (fun ω => f ω - g ω) ω = condExp μ Z f ω - condExp μ Z g ω := by
  unfold condExp
  rw [← sub_div, ← FiniteLaw.expect_sub]
  congr 1
  exact μ.expect_congr (fun ω' => by ring)

theorem condExp_nonneg (μ : FiniteLaw Ω) (Z : Ω → γ) {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω)
    (ω : Ω) : 0 ≤ condExp μ Z f ω :=
  div_nonneg (μ.expect_nonneg (fun ω' => mul_nonneg (ind_nonneg _ _) (hf ω')))
    (prob_nonneg μ _)

theorem condExp_congr_ae (μ : FiniteLaw Ω) (Z : Ω → γ) {f g : Ω → ℝ}
    (h : ∀ ω, μ.weight ω ≠ 0 → f ω = g ω) : condExp μ Z f = condExp μ Z g := by
  funext ω
  unfold condExp
  congr 1
  exact expect_congr_ae μ (fun ω' hw => by rw [h ω' hw])

/-- `E[f|Z]` depends only on the level sets of `Z`. -/
theorem condExp_congr_level (μ : FiniteLaw Ω) {Z : Ω → γ} {Z' : Ω → δ}
    (h : ∀ ω ω', Z ω = Z ω' ↔ Z' ω = Z' ω') (f : Ω → ℝ) : condExp μ Z f = condExp μ Z' f := by
  funext ω
  have : lv Z ω = lv Z' ω := funext fun ω' => propext (h ω' ω)
  simp only [condExp, this]

/-- (P1), last clause: `E[h | Z] = h` for `h ∈ L²(Z)`, at every point of positive mass. -/
theorem condExp_eq_self (μ : FiniteLaw Ω) (Z : Ω → γ) {h : Ω → ℝ} (hh : IsFunOf Z h)
    {ω : Ω} (hw : μ.weight ω ≠ 0) : condExp μ Z h ω = h ω := by
  unfold condExp
  have hp : 0 < prob μ (lv Z ω) := prob_pos_of_weight (show lv Z ω ω from rfl) hw
  have hnum : μ.expect (fun ω' => ind (lv Z ω) ω' * h ω') =
      μ.expect (fun ω' => ind (lv Z ω) ω' * h ω) := by
    refine μ.expect_congr (fun ω' => ?_)
    by_cases hz : Z ω' = Z ω
    · rw [hh ω' ω hz]
    · rw [ind_of_neg (show ¬ lv Z ω ω' from hz), zero_mul, zero_mul]
  rw [hnum, FiniteLaw.expect_mul_const]
  change prob μ (lv Z ω) * h ω / prob μ (lv Z ω) = h ω
  field_simp

/-- (P1), tower property: if `L²(Z) ⊆ L²(W)` then `E[E[f|W] | Z] = E[f|Z]` (everywhere). -/
theorem condExp_condExp_of_coarser (μ : FiniteLaw Ω) {Z : Ω → γ} {W : Ω → δ}
    (hZW : Coarser Z W) (f : Ω → ℝ) : condExp μ Z (condExp μ W f) = condExp μ Z f := by
  funext ω
  unfold condExp
  congr 1
  have hind : IsFunOf W (ind (lv Z ω)) := by
    intro ω₁ ω₂ h
    have h' := hZW ω₁ ω₂ h
    by_cases h1 : Z ω₁ = Z ω
    · rw [ind_of_pos (show lv Z ω ω₁ from h1), ind_of_pos (show lv Z ω ω₂ from h'.symm.trans h1)]
    · rw [ind_of_neg (show ¬ lv Z ω ω₁ from h1),
        ind_of_neg (show ¬ lv Z ω ω₂ from fun h2 => h1 (h'.trans h2))]
  exact expect_mul_condExp μ W f _ hind

/-- (P1): if `L²(Z) ⊆ L²(W)` then `E[E[f|Z] | W] = E[f|Z]` at every point of positive mass. -/
theorem condExp_of_coarser_eq (μ : FiniteLaw Ω) {Z : Ω → γ} {W : Ω → δ}
    (hZW : Coarser Z W) (f : Ω → ℝ) {ω : Ω} (hw : μ.weight ω ≠ 0) :
    condExp μ W (condExp μ Z f) ω = condExp μ Z f ω :=
  condExp_eq_self μ W ((condExp_isFunOf μ Z f).mono hZW) hw

/-- Conditioning on a constant random variable is taking the expectation. -/
theorem condExp_of_const (μ : FiniteLaw Ω) {Z : Ω → γ} (hZ : ∀ ω ω', Z ω = Z ω')
    (f : Ω → ℝ) (ω : Ω) : condExp μ Z f ω = μ.expect f := by
  unfold condExp
  have hind : ind (lv Z ω) = fun _ => 1 := funext fun ω' => ind_of_pos (hZ ω' ω)
  rw [prob, hind, FiniteLaw.expect_const, div_one]
  exact μ.expect_congr (fun ω' => one_mul _)

/-! ### Orthogonality and Pythagoras (P2) -/

/-- (P2): `f - E[f|Z] ⊥ L²(Z)`. -/
theorem expect_sub_condExp_mul (μ : FiniteLaw Ω) (Z : Ω → γ) (f g : Ω → ℝ)
    (hg : IsFunOf Z g) :
    μ.expect (fun ω => (f ω - condExp μ Z f ω) * g ω) = 0 := by
  have h1 := expect_condExp_mul μ Z f g hg
  have : μ.expect (fun ω => (f ω - condExp μ Z f ω) * g ω) =
      μ.expect (fun ω => f ω * g ω) - μ.expect (fun ω => condExp μ Z f ω * g ω) := by
    rw [← FiniteLaw.expect_sub]
    exact μ.expect_congr (fun ω => by ring)
  rw [this, h1, sub_self]

/-- Orthogonal sum: if `E[u r] = 0` then `‖u + r‖² = ‖u‖² + ‖r‖²`. -/
theorem expect_sq_add_of_orth (μ : FiniteLaw Ω) (u r : Ω → ℝ)
    (h : μ.expect (fun ω => u ω * r ω) = 0) :
    μ.expect (fun ω => (u ω + r ω) ^ 2) =
      μ.expect (fun ω => u ω ^ 2) + μ.expect (fun ω => r ω ^ 2) := by
  have : μ.expect (fun ω => (u ω + r ω) ^ 2) = μ.expect (fun ω => u ω ^ 2 + r ω ^ 2 +
      2 * (u ω * r ω)) := μ.expect_congr (fun ω => by ring)
  rw [this, FiniteLaw.expect_add, FiniteLaw.expect_add, FiniteLaw.expect_const_mul, h]
  ring

/-- Pythagoras (P2): `‖f‖² = ‖E[f|Z]‖² + ‖f - E[f|Z]‖²`. -/
theorem expect_sq_eq_condExp_add (μ : FiniteLaw Ω) (Z : Ω → γ) (f : Ω → ℝ) :
    μ.expect (fun ω => f ω ^ 2) = μ.expect (fun ω => condExp μ Z f ω ^ 2) +
      μ.expect (fun ω => (f ω - condExp μ Z f ω) ^ 2) := by
  have horth : μ.expect (fun ω => condExp μ Z f ω * (f ω - condExp μ Z f ω)) = 0 := by
    have := expect_sub_condExp_mul μ Z f (condExp μ Z f) (condExp_isFunOf μ Z f)
    simpa only [mul_comm] using this
  have h := expect_sq_add_of_orth μ (condExp μ Z f) (fun ω => f ω - condExp μ Z f ω) horth
  simpa only [add_sub_cancel] using h

theorem expect_sq_sub_condExp_le (μ : FiniteLaw Ω) (Z : Ω → γ) (f : Ω → ℝ) :
    μ.expect (fun ω => (f ω - condExp μ Z f ω) ^ 2) ≤ μ.expect (fun ω => f ω ^ 2) := by
  rw [expect_sq_eq_condExp_add μ Z f]
  linarith [expect_sq_nonneg μ (condExp μ Z f)]

theorem expect_sq_condExp_le (μ : FiniteLaw Ω) (Z : Ω → γ) (f : Ω → ℝ) :
    μ.expect (fun ω => condExp μ Z f ω ^ 2) ≤ μ.expect (fun ω => f ω ^ 2) := by
  rw [expect_sq_eq_condExp_add μ Z f]
  linarith [expect_sq_nonneg μ (fun ω => f ω - condExp μ Z f ω)]

/-- (P2), best approximation: `‖f - E[f|Z]‖ ≤ ‖f - h‖` for every `h ∈ L²(Z)`
(squared form). -/
theorem expect_sq_sub_condExp_le_of_isFunOf (μ : FiniteLaw Ω) (Z : Ω → γ) (f : Ω → ℝ)
    {h : Ω → ℝ} (hh : IsFunOf Z h) :
    μ.expect (fun ω => (f ω - condExp μ Z f ω) ^ 2) ≤ μ.expect (fun ω => (f ω - h ω) ^ 2) := by
  have hu : IsFunOf Z (fun ω => condExp μ Z f ω - h ω) := (condExp_isFunOf μ Z f).sub hh
  have horth : μ.expect (fun ω => (f ω - condExp μ Z f ω) * (condExp μ Z f ω - h ω)) = 0 :=
    expect_sub_condExp_mul μ Z f _ hu
  have e := expect_sq_add_of_orth μ (fun ω => f ω - condExp μ Z f ω)
    (fun ω => condExp μ Z f ω - h ω) horth
  have e' : μ.expect (fun ω => (f ω - h ω) ^ 2) =
      μ.expect (fun ω => (f ω - condExp μ Z f ω + (condExp μ Z f ω - h ω)) ^ 2) :=
    μ.expect_congr (fun ω => by ring)
  rw [e', e]
  linarith [expect_sq_nonneg μ (fun ω => condExp μ Z f ω - h ω)]

/-- One step of a martingale decomposition: if `L²(Z) ⊆ L²(W)` then
`‖f - E[f|Z]‖² = ‖E[f|W] - E[f|Z]‖² + ‖f - E[f|W]‖²`. -/
theorem expect_sq_sub_condExp_step (μ : FiniteLaw Ω) {Z : Ω → γ} {W : Ω → δ}
    (hZW : Coarser Z W) (f : Ω → ℝ) :
    μ.expect (fun ω => (f ω - condExp μ Z f ω) ^ 2) =
      μ.expect (fun ω => (condExp μ W f ω - condExp μ Z f ω) ^ 2) +
      μ.expect (fun ω => (f ω - condExp μ W f ω) ^ 2) := by
  have hu : IsFunOf W (fun ω => condExp μ W f ω - condExp μ Z f ω) :=
    (condExp_isFunOf μ W f).sub ((condExp_isFunOf μ Z f).mono hZW)
  have horth : μ.expect (fun ω => (condExp μ W f ω - condExp μ Z f ω) *
      (f ω - condExp μ W f ω)) = 0 := by
    have := expect_sub_condExp_mul μ W f _ hu
    simpa only [mul_comm] using this
  have h := expect_sq_add_of_orth μ _ _ horth
  rw [← h]
  exact μ.expect_congr (fun ω => by ring)

/-- If `f ∈ L²(Z)` then `‖f - E[f|Z]‖ = 0`. -/
theorem expect_sq_sub_condExp_eq_zero (μ : FiniteLaw Ω) (Z : Ω → γ) {f : Ω → ℝ}
    (hf : IsFunOf Z f) : μ.expect (fun ω => (f ω - condExp μ Z f ω) ^ 2) = 0 :=
  expect_eq_zero_ae μ (fun ω hw => by rw [condExp_eq_self μ Z hf hw, sub_self]; ring)

end CondExp

/-! ### Conditioning on an event -/

section Cond

/-- The conditional law `μ(· | E)` on the same finite type, for `μ(E) > 0`. -/
noncomputable def condLaw (μ : FiniteLaw Ω) (E : Ω → Prop) (hE : 0 < prob μ E) : FiniteLaw Ω where
  weight ω := ind E ω * μ.weight ω / prob μ E
  nonneg ω := div_nonneg (mul_nonneg (ind_nonneg E ω) (μ.nonneg ω)) hE.le
  total := by
    rw [← Finset.sum_div]
    have : (∑ ω, ind E ω * μ.weight ω) = prob μ E := by
      unfold prob FiniteLaw.expect
      exact Finset.sum_congr rfl (fun ω _ => mul_comm _ _)
    rw [this, div_self hE.ne']

theorem cond_weight (μ : FiniteLaw Ω) (E : Ω → Prop) (hE : 0 < prob μ E) (ω : Ω) :
    (condLaw μ E hE).weight ω = ind E ω * μ.weight ω / prob μ E := rfl

theorem cond_expect (μ : FiniteLaw Ω) (E : Ω → Prop) (hE : 0 < prob μ E) (u : Ω → ℝ) :
    (condLaw μ E hE).expect u = μ.expect (fun ω => ind E ω * u ω) / prob μ E := by
  unfold FiniteLaw.expect
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [cond_weight]
  ring

theorem cond_congr (μ : FiniteLaw Ω) {E F : Ω → Prop} (h : E = F) (hE : 0 < prob μ E)
    (hF : 0 < prob μ F) : condLaw μ E hE = condLaw μ F hF := by
  subst h
  rfl

theorem cond_weight_ne_zero {μ : FiniteLaw Ω} {E : Ω → Prop} {hE : 0 < prob μ E} {ω : Ω}
    (h : (condLaw μ E hE).weight ω ≠ 0) : E ω ∧ μ.weight ω ≠ 0 := by
  rw [cond_weight] at h
  by_cases hω : E ω
  · refine ⟨hω, fun hw => h ?_⟩
    rw [hw, mul_zero, zero_div]
  · exact absurd (by rw [ind_of_neg hω, zero_mul, zero_div]) h

/-- Expectations under `μ(·|E)` see only the values on `E`. -/
theorem cond_expect_congr (μ : FiniteLaw Ω) {E : Ω → Prop} (hE : 0 < prob μ E)
    {u v : Ω → ℝ} (h : ∀ ω, E ω → u ω = v ω) :
    (condLaw μ E hE).expect u = (condLaw μ E hE).expect v :=
  expect_congr_ae _ (fun ω hw => h ω (cond_weight_ne_zero hw).1)

/-- The expectation under `μ(· | Z = Z ω₀)` is the conditional expectation at `ω₀`. -/
theorem cond_expect_level (μ : FiniteLaw Ω) {γ : Type*} (Z : Ω → γ) (ω₀ : Ω)
    (h : 0 < prob μ (fun ω => Z ω = Z ω₀)) (u : Ω → ℝ) :
    (condLaw μ (fun ω => Z ω = Z ω₀) h).expect u = condExp μ Z u ω₀ := by
  rw [cond_expect]
  rfl

theorem prob_cond (μ : FiniteLaw Ω) (E : Ω → Prop) (hE : 0 < prob μ E) (F : Ω → Prop) :
    prob (condLaw μ E hE) F = prob μ (fun ω => F ω ∧ E ω) / prob μ E := by
  unfold prob
  rw [cond_expect]
  congr 1
  exact μ.expect_congr (fun ω => by rw [ind_and]; ring)

theorem prob_and_pos_of_cond (μ : FiniteLaw Ω) (E : Ω → Prop) (hE : 0 < prob μ E)
    (F : Ω → Prop) (hF : 0 < prob (condLaw μ E hE) F) : 0 < prob μ (fun ω => F ω ∧ E ω) := by
  rw [prob_cond] at hF
  exact (div_pos_iff_of_pos_right hE).mp hF

theorem law_ext {μ ν : FiniteLaw Ω} (h : ∀ ω, μ.weight ω = ν.weight ω) : μ = ν := by
  cases μ
  cases ν
  simp only [FiniteLaw.mk.injEq]
  exact funext h

/-- Conditioning twice is conditioning on the intersection. -/
theorem cond_cond (μ : FiniteLaw Ω) (E : Ω → Prop) (hE : 0 < prob μ E) (F : Ω → Prop)
    (hF : 0 < prob (condLaw μ E hE) F) (hFE : 0 < prob μ (fun ω => F ω ∧ E ω)) :
    condLaw (condLaw μ E hE) F hF = condLaw μ (fun ω => F ω ∧ E ω) hFE := by
  apply law_ext
  intro ω
  rw [cond_weight, cond_weight, cond_weight, prob_cond, ind_and]
  field_simp

/-- (P3): conditional expectations under `μ(·|E)` are conditional expectations under
`μ` given the finer variable `Z'` whose level sets are those of `Z` intersected
with `E`. -/
theorem condExp_cond (μ : FiniteLaw Ω) {γ δ : Type*} (E : Ω → Prop) (hE : 0 < prob μ E)
    (Z : Ω → γ) (Z' : Ω → δ) (ω : Ω) (hZ : ∀ ω', Z' ω' = Z' ω ↔ Z ω' = Z ω ∧ E ω')
    (f : Ω → ℝ) : condExp (condLaw μ E hE) Z f ω = condExp μ Z' f ω := by
  have hind : ∀ ω', ind (lv Z' ω) ω' = ind (lv Z ω) ω' * ind E ω' := by
    intro ω'
    rw [← ind_and]
    exact congrFun (ind_congr (fun ω' => hZ ω')) ω'
  unfold condExp
  rw [cond_expect, prob_cond]
  have h1 : μ.expect (fun ω' => ind E ω' * (ind (lv Z ω) ω' * f ω')) =
      μ.expect (fun ω' => ind (lv Z' ω) ω' * f ω') :=
    μ.expect_congr (fun ω' => by rw [hind]; ring)
  have h2 : prob μ (fun ω' => lv Z ω ω' ∧ E ω') = prob μ (lv Z' ω) := by
    unfold prob
    exact μ.expect_congr (fun ω' => by rw [hind, ind_and])
  rw [h1, h2, div_div_div_cancel_right₀ hE.ne']

end Cond

end Sarkozy.Peyre
