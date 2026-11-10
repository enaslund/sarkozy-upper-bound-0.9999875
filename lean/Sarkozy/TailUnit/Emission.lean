module

public import Sarkozy.PartV.Components
public import Sarkozy.PartV.UpperReference
public import Sarkozy.Moments.Mixed
public import Sarkozy.Moments.Grouping
public import Sarkozy.Moments.Normalization

/-!
# Unit mixed norms of the upper-reference components, I: emissions

`paper/sections/31_density_induction_upgrade.tex`, proof of `lem:density:global-moment`, second
paragraph: "A component with maximum multiplicity `m` therefore has unit mixed `L^{11m/10}`".

A component of V1's upper reference (`Sarkozy.PartV.upComponent`) is the image `emit λ π` of a
field law `λ` (a graph law on the objects) under an emission `π : Slot → objects`. Several slots
may read the same object; the *multiplicity* of an object is the number of slots reading it.
* `mixedLpBound_emit`: if `λ` has unit mixed `Lʳ` and every object has multiplicity at most `m`,
  then `emit λ π` has unit mixed `L^{rm}` (Hölder inside each fibre).
* `maxFib`: the largest fibre of a pattern map of each type, `1, 2, 2, 4, 6` for `L, D, S, R, C`
  (`pat_fiber_le`, checked by `decide`). These are the paper's "physical maximum multiplicities".
* `upEmission_fiber_le`, `upDiagEmission_fiber_le`: the two-layer emission has multiplicities at
  most `maxFib t₀ · maxFib t₁`, the one-layer diagonal copy at most twice that.
* `upComponent_mixedLpBound`: every component has unit mixed `L^{r · compFib j}` when the field
  laws have unit mixed `Lʳ`, with `compFib j = fibOf b t₀ t₁` the product above.

New material for this paper (the paper states the multiplicity rule without proof).
-/

@[expose] public section

namespace Sarkozy.TailUnit

open Finset Sarkozy.PartV

section Emission

variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X] [Nonempty X]

omit [DecidableEq X] in
/-- `‖1‖_r = 1` under the uniform law. -/
theorem uniform_lpNorm_one (r : ℝ) :
    (FiniteLaw.uniform X).lpNorm r (fun _ => (1 : ℝ)) = 1 := by
  unfold FiniteLaw.lpNorm FiniteLaw.moment
  simp only [abs_one, Real.one_rpow, FiniteLaw.expect_const]

omit [DecidableEq X] in
/-- A function with `‖f‖_R ≤ 1` has `𝔼|f|^q ≤ 1` for `0 < q ≤ R`. -/
theorem uniform_moment_le_one_of_lpNorm {q R : ℝ} (hq : 0 < q) (hqR : q ≤ R) {f : X → ℝ}
    (hf : (FiniteLaw.uniform X).lpNorm R f ≤ 1) : (FiniteLaw.uniform X).moment q f ≤ 1 := by
  rw [← (FiniteLaw.uniform X).lpNorm_rpow hq.ne' f]
  exact Real.rpow_le_one ((FiniteLaw.uniform X).lpNorm_nonneg _ _)
    (((FiniteLaw.uniform X).lpNorm_mono hq hqR f).trans hf) hq.le

/-- **Emission Hölder.** If `λ` has unit mixed `Lʳ` and every object is read by at most `m` slots,
the image `emit λ π` has unit mixed `L^{rm}`. -/
theorem mixedLpBound_emit (lam : FiniteLaw (I → X)) (π : Slot → I) {r : ℝ} (hr : 0 < r)
    {m : ℕ} (hm1 : 1 ≤ m) (hm : ∀ i, Fintype.card {v // π v = i} ≤ m)
    (hlam : MixedLpBound lam r 1) : MixedLpBound (emit lam π) (r * m) 1 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hrm : 0 < r * m := mul_pos hr hm0
  apply mixedLpBound_of_normalized _ hrm
  intro f hf hn
  have hprod : ∀ y : I → X,
      ∏ v, f v (y (π v)) = ∏ i, (fun x => ∏ v : {v // π v = i}, f v.1 x) (y i) := by
    intro y
    rw [← Fintype.prod_fiberwise π (fun v => f v (y (π v)))]
    refine prod_congr rfl fun i _ => prod_congr rfl fun v _ => ?_
    rw [v.2]
  have hgi : ∀ i, (FiniteLaw.uniform X).lpNorm r (fun x => ∏ v : {v // π v = i}, f v.1 x) ≤ 1 := by
    intro i
    rcases isEmpty_or_nonempty {v // π v = i} with hne | hne
    · have hgeq : (fun x : X => ∏ v : {v // π v = i}, f v.1 x) = fun _ => 1 := by
        funext x
        exact Fintype.prod_empty _
      rw [hgeq, uniform_lpNorm_one]
    · have hk : (Fintype.card {v // π v = i} : ℝ) ≤ m := by exact_mod_cast hm i
      have hk0 : (0 : ℝ) < Fintype.card {v // π v = i} := by exact_mod_cast Fintype.card_pos
      exact (FiniteLaw.uniform X).lpNorm_prod_le_one_of_moments (I := {v // π v = i}) hr
        (fun v x => f v.1 x) (fun v x => hf v.1 x)
        (fun v => uniform_moment_le_one_of_lpNorm (mul_pos hr hk0)
          (mul_le_mul_of_nonneg_left hk hr.le) (hn v.1).le)
  simp only [expect_emit, Function.comp_apply]
  rw [lam.expect_congr hprod]
  calc lam.expect (fun y => ∏ i, (fun x => ∏ v : {v // π v = i}, f v.1 x) (y i))
      ≤ |lam.expect (fun y => ∏ i, (fun x => ∏ v : {v // π v = i}, f v.1 x) (y i))| :=
        le_abs_self _
    _ ≤ 1 * ∏ i, (FiniteLaw.uniform X).lpNorm r (fun x => ∏ v : {v // π v = i}, f v.1 x) :=
        hlam (fun i x => ∏ v : {v // π v = i}, f v.1 x)
    _ ≤ 1 := by
        rw [one_mul]
        exact prod_le_one₀ (fun i _ => (FiniteLaw.uniform X).lpNorm_nonneg _ _) (fun i _ => hgi i)

end Emission

/-! ## Multiplicities of the patterns and emissions -/

/-- **The largest fibre of a pattern map** of each type: `1, 2, 2, 4, 6` for `L, D, S, R, C`
(the identity, the folds, the matchings, the merges, the constant). -/
def maxFib : PType → ℕ
  | .L => 1
  | .D => 2
  | .S => 2
  | .R => 4
  | .C => 6

theorem one_le_maxFib (t : PType) : 1 ≤ maxFib t := by
  cases t <;> decide

/-- Every fibre of a pattern map of type `t` has at most `maxFib t` elements. -/
theorem pat_fiber_le (t : PType) (φ : t.Pat) (o : t.field.Obj) :
    Fintype.card {u : ZMod 6 // t.pat φ u = o} ≤ maxFib t := by
  rw [Fintype.card_subtype]
  revert φ o
  cases t <;> decide

/-- The layer map is injective: each layer label is read by at most one layer. -/
theorem layerFin_fiber_le :
    ∀ ℓ : Fin 2, (univ.filter fun l : Layer => layerFin l = ℓ).card ≤ 1 := by
  decide

/-- The two-layer emission `(u₀, u₁, ℓ) ↦ (φ₀ u₀, φ₁ u₁, ℓ)` has multiplicities at most
`maxFib t₀ · maxFib t₁`. -/
theorem upEmission_fiber_le (t₀ t₁ : PType) (φ₀ : t₀.Pat) (φ₁ : t₁.Pat)
    (i : t₀.field.Obj × t₁.field.Obj × Fin 2) :
    Fintype.card {v : Slot // upEmission (t₀.pat φ₀) (t₁.pat φ₁) v = i} ≤
      maxFib t₀ * maxFib t₁ := by
  obtain ⟨o₀, o₁, ℓ⟩ := i
  rw [Fintype.card_subtype]
  have hsub : (univ.filter fun v : Slot => upEmission (t₀.pat φ₀) (t₁.pat φ₁) v = (o₀, o₁, ℓ)) ⊆
      (univ.filter fun u => t₀.pat φ₀ u = o₀) ×ˢ ((univ.filter fun u => t₁.pat φ₁ u = o₁) ×ˢ
        (univ.filter fun l : Layer => layerFin l = ℓ)) := by
    intro v hv
    simp only [mem_filter, mem_univ, true_and, upEmission, Prod.mk.injEq] at hv
    simp only [mem_product, mem_filter, mem_univ, true_and]
    exact ⟨hv.1, hv.2.1, hv.2.2⟩
  have hl : (univ.filter fun l : Layer => layerFin l = ℓ).card ≤ 1 := layerFin_fiber_le ℓ
  have h0 := pat_fiber_le t₀ φ₀ o₀
  have h1 := pat_fiber_le t₁ φ₁ o₁
  rw [Fintype.card_subtype] at h0 h1
  calc _ ≤ _ := card_le_card hsub
    _ = _ := by rw [card_product, card_product]
    _ ≤ maxFib t₀ * (maxFib t₁ * 1) := Nat.mul_le_mul h0 (Nat.mul_le_mul h1 hl)
    _ = maxFib t₀ * maxFib t₁ := by rw [mul_one]

/-- The one-layer diagonal copy `(u₀, u₁, ℓ) ↦ (φ₀ u₀, φ₁ u₁, 0)` has multiplicities at most
`2 maxFib t₀ · maxFib t₁`. -/
theorem upDiagEmission_fiber_le (t₀ t₁ : PType) (φ₀ : t₀.Pat) (φ₁ : t₁.Pat)
    (i : t₀.field.Obj × t₁.field.Obj × Fin 1) :
    Fintype.card {v : Slot // upDiagEmission (t₀.pat φ₀) (t₁.pat φ₁) v = i} ≤
      2 * (maxFib t₀ * maxFib t₁) := by
  obtain ⟨o₀, o₁, ℓ⟩ := i
  rw [Fintype.card_subtype]
  have hsub : (univ.filter fun v : Slot => upDiagEmission (t₀.pat φ₀) (t₁.pat φ₁) v = (o₀, o₁, ℓ))
      ⊆ (univ.filter fun u => t₀.pat φ₀ u = o₀) ×ˢ ((univ.filter fun u => t₁.pat φ₁ u = o₁) ×ˢ
        (univ : Finset Layer)) := by
    intro v hv
    simp only [mem_filter, mem_univ, true_and, upDiagEmission, Prod.mk.injEq] at hv
    simp only [mem_product, mem_filter, mem_univ, true_and, and_true]
    exact ⟨hv.1, hv.2.1⟩
  have hl : (univ : Finset Layer).card = 2 := rfl
  have h0 := pat_fiber_le t₀ φ₀ o₀
  have h1 := pat_fiber_le t₁ φ₁ o₁
  rw [Fintype.card_subtype] at h0 h1
  calc _ ≤ _ := card_le_card hsub
    _ = _ := by rw [card_product, card_product]
    _ ≤ maxFib t₀ * (maxFib t₁ * 2) := Nat.mul_le_mul h0 (Nat.mul_le_mul h1 hl.le)
    _ = 2 * (maxFib t₀ * maxFib t₁) := by ring

/-- The multiplicity bound of a component: `maxFib t₀ · maxFib t₁` for a two-layer copy, twice
that for a one-layer diagonal copy ("a folded component doubles its multiplicity"). -/
def fibOf (b : Bool) (t₀ t₁ : PType) : ℕ := (if b then 1 else 2) * (maxFib t₀ * maxFib t₁)

/-- The formal degree of a component: `deg t₀ + deg t₁`, plus one for a diagonal copy. -/
def degOf (b : Bool) (t₀ t₁ : PType) : ℕ := t₀.deg + t₁.deg + (if b then 0 else 1)

/-- **A component of multiplicity above `32` has formal degree at least `6`** ("Any component
whose exponent exceeds 36 has formal degree at least six"; the multiplicities above `32` are
`36, 48, 72`, from the two-layer `CC` and the diagonal `RC, CR, CC`). -/
theorem degOf_ge_of_fibOf : ∀ b t₀ t₁, 32 < fibOf b t₀ t₁ → 6 ≤ degOf b t₀ t₁ := by
  decide

/-- The multiplicity bound of the component `j`. -/
def compFib (j : UpIdx) : ℕ := fibOf j.1 j.2.1.1 j.2.1.2

/-- The formal degree of the component `j`. -/
def compDeg (j : UpIdx) : ℕ := degOf j.1 j.2.1.1 j.2.1.2

theorem one_le_compFib (j : UpIdx) : 1 ≤ compFib j := by
  rcases j with ⟨b, ⟨t₀, t₁⟩, φ⟩
  unfold compFib fibOf
  have h0 := one_le_maxFib t₀
  have h1 := one_le_maxFib t₁
  have h01 : 1 ≤ maxFib t₀ * maxFib t₁ := Nat.one_le_iff_ne_zero.mpr (by positivity)
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- **Every component of the upper reference has unit mixed `L^{r · compFib j}`** when the field
laws have unit mixed `Lʳ`. -/
theorem upComponent_mixedLpBound {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (F : UpperFieldLaws X) {r : ℝ} (hr : 0 < r)
    (h2 : ∀ f₀ f₁, MixedLpBound (F.two f₀ f₁) r 1) (h1 : ∀ f₀ f₁, MixedLpBound (F.one f₀ f₁) r 1)
    (j : UpIdx) : MixedLpBound (upComponent F j) (r * compFib j) 1 := by
  rcases j with ⟨b, ⟨t₀, t₁⟩, φ₀, φ₁⟩
  cases b
  · have h := mixedLpBound_emit (F.one t₀.field t₁.field)
      (upDiagEmission (t₀.pat φ₀) (t₁.pat φ₁)) hr (one_le_compFib (false, ⟨(t₀, t₁), φ₀, φ₁⟩))
      (fun i => by
        have := upDiagEmission_fiber_le t₀ t₁ φ₀ φ₁ i
        unfold compFib fibOf
        simpa only [Bool.false_eq_true, ↓reduceIte] using this)
      (h1 _ _)
    exact h
  · have h := mixedLpBound_emit (F.two t₀.field t₁.field)
      (upEmission (t₀.pat φ₀) (t₁.pat φ₁)) hr (one_le_compFib (true, ⟨(t₀, t₁), φ₀, φ₁⟩))
      (fun i => by
        have := upEmission_fiber_le t₀ t₁ φ₀ φ₁ i
        unfold compFib fibOf
        simpa only [↓reduceIte, one_mul] using this)
      (h2 _ _)
    exact h

end Sarkozy.TailUnit
