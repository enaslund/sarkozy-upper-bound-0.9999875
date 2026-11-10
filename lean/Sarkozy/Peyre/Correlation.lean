module

public import Sarkozy.Peyre.Basic

/-!
# Peyre's tensorization in finite form, II: maximal correlation

* `maxCorr μ X Y` is the maximal correlation `ρ(X;Y)` of `def:prelim:maxcorr`
  (paper `04_notation.tex`): the supremum of `|E f(X) g(Y)|` over real functions
  `f` of the values of `X` and `g` of the values of `Y` with
  `E f(X) = E g(Y) = 0`, `E f(X)² = E g(Y)² = 1`, and `0` if there are none
  (Lean's `sSup ∅ = 0` on `ℝ`).  The conditional maximal correlation
  `ρ(X;Y | E)` is `maxCorr (condLaw μ E h) X Y`.
* `CorrLe μ X Y ε` is the inequality form `|E f(X) g(Y)| ≤ ε ‖f(X)‖ ‖g(Y)‖` for
  centred `f(X), g(Y)`; for `ε ≥ 0` it is equivalent to `maxCorr μ X Y ≤ ε`
  (`maxCorr_le_iff`).
* `lem:peyre:basic` (a), (b), (c) of Appendix B; (b) is also
  `cor:condLaw-decorrelation` of Section 4.6.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Peyre

open Sarkozy

variable {Ω : Type*} [Fintype Ω] {α β γ : Type*}

/-- The values `|E f(X) g(Y)|` over standardized `f(X)`, `g(Y)` (def:prelim:maxcorr). -/
def corrSet (μ : FiniteLaw Ω) (X : Ω → α) (Y : Ω → β) : Set ℝ :=
  {c | ∃ f : α → ℝ, ∃ g : β → ℝ, μ.expect (fun ω => f (X ω)) = 0 ∧
    μ.expect (fun ω => g (Y ω)) = 0 ∧ μ.expect (fun ω => f (X ω) ^ 2) = 1 ∧
    μ.expect (fun ω => g (Y ω) ^ 2) = 1 ∧ c = |μ.expect (fun ω => f (X ω) * g (Y ω))|}

/-- The maximal correlation `ρ(X;Y)` (def:prelim:maxcorr). -/
noncomputable def maxCorr (μ : FiniteLaw Ω) (X : Ω → α) (Y : Ω → β) : ℝ :=
  sSup (corrSet μ X Y)

/-- Inequality form of `ρ(X;Y) ≤ ε`: `|E f(X) g(Y)| ≤ ε ‖f(X)‖ ‖g(Y)‖` whenever
`E f(X) = E g(Y) = 0`. -/
def CorrLe (μ : FiniteLaw Ω) (X : Ω → α) (Y : Ω → β) (ε : ℝ) : Prop :=
  ∀ f : α → ℝ, ∀ g : β → ℝ, μ.expect (fun ω => f (X ω)) = 0 →
    μ.expect (fun ω => g (Y ω)) = 0 →
    |μ.expect (fun ω => f (X ω) * g (Y ω))| ≤
      ε * √(μ.expect (fun ω => f (X ω) ^ 2)) * √(μ.expect (fun ω => g (Y ω) ^ 2))

theorem expect_div_const (μ : FiniteLaw Ω) (f : Ω → ℝ) (c : ℝ) :
    μ.expect (fun ω => f ω / c) = μ.expect f / c := by
  simp only [div_eq_mul_inv]
  exact μ.expect_mul_const f c⁻¹

theorem corrSet_le_one (μ : FiniteLaw Ω) (X : Ω → α) (Y : Ω → β) :
    ∀ c ∈ corrSet μ X Y, c ≤ 1 := by
  rintro c ⟨f, g, -, -, hf2, hg2, rfl⟩
  have h := μ.abs_expect_mul_le (fun ω => f (X ω)) (fun ω => g (Y ω))
  simp only [hf2, hg2, Real.sqrt_one, mul_one] at h
  exact h

theorem corrSet_bddAbove (μ : FiniteLaw Ω) (X : Ω → α) (Y : Ω → β) :
    BddAbove (corrSet μ X Y) := ⟨1, corrSet_le_one μ X Y⟩

theorem maxCorr_nonneg (μ : FiniteLaw Ω) (X : Ω → α) (Y : Ω → β) : 0 ≤ maxCorr μ X Y := by
  apply Real.sSup_nonneg
  rintro c ⟨f, g, -, -, -, -, rfl⟩
  exact abs_nonneg _

/-- `ρ(X;Y) ≤ 1` (Cauchy–Schwarz). -/
theorem maxCorr_le_one (μ : FiniteLaw Ω) (X : Ω → α) (Y : Ω → β) : maxCorr μ X Y ≤ 1 :=
  Real.sSup_le (corrSet_le_one μ X Y) zero_le_one

theorem maxCorr_le_of_corrLe {μ : FiniteLaw Ω} {X : Ω → α} {Y : Ω → β} {ε : ℝ}
    (hε : 0 ≤ ε) (h : CorrLe μ X Y ε) : maxCorr μ X Y ≤ ε := by
  apply Real.sSup_le _ hε
  rintro c ⟨f, g, hf, hg, hf2, hg2, rfl⟩
  have := h f g hf hg
  rwa [hf2, hg2, Real.sqrt_one, mul_one, mul_one] at this

theorem corrLe_of_maxCorr_le {μ : FiniteLaw Ω} {X : Ω → α} {Y : Ω → β} {ε : ℝ}
    (h : maxCorr μ X Y ≤ ε) : CorrLe μ X Y ε := by
  intro f g hf hg
  have ha : 0 ≤ μ.expect (fun ω => f (X ω) ^ 2) := μ.second_moment_nonneg _
  have hb : 0 ≤ μ.expect (fun ω => g (Y ω) ^ 2) := μ.second_moment_nonneg _
  have hcs := μ.abs_expect_mul_le (fun ω => f (X ω)) (fun ω => g (Y ω))
  rcases ha.eq_or_lt with ha0 | ha0
  · rw [← ha0, Real.sqrt_zero, zero_mul] at hcs
    rw [← ha0, Real.sqrt_zero, mul_zero, zero_mul]
    exact hcs
  rcases hb.eq_or_lt with hb0 | hb0
  · rw [← hb0, Real.sqrt_zero, mul_zero] at hcs
    rw [← hb0, Real.sqrt_zero, mul_zero]
    exact hcs
  set a := μ.expect (fun ω => f (X ω) ^ 2) with ha_def
  set b := μ.expect (fun ω => g (Y ω) ^ 2) with hb_def
  have hsa : 0 < √a := Real.sqrt_pos.mpr ha0
  have hsb : 0 < √b := Real.sqrt_pos.mpr hb0
  have hmem : |μ.expect (fun ω => f (X ω) * g (Y ω))| / (√a * √b) ∈ corrSet μ X Y := by
    refine ⟨fun x => f x / √a, fun y => g y / √b, ?_, ?_, ?_, ?_, ?_⟩
    · rw [expect_div_const μ (fun ω => f (X ω)), hf, zero_div]
    · rw [expect_div_const μ (fun ω => g (Y ω)), hg, zero_div]
    · have e : (fun ω => (f (X ω) / √a) ^ 2) = fun ω => f (X ω) ^ 2 / a := by
        funext ω
        rw [div_pow, Real.sq_sqrt ha0.le]
      simp only [e]
      rw [expect_div_const μ (fun ω => f (X ω) ^ 2), ← ha_def, div_self ha0.ne']
    · have e : (fun ω => (g (Y ω) / √b) ^ 2) = fun ω => g (Y ω) ^ 2 / b := by
        funext ω
        rw [div_pow, Real.sq_sqrt hb0.le]
      simp only [e]
      rw [expect_div_const μ (fun ω => g (Y ω) ^ 2), ← hb_def, div_self hb0.ne']
    · have e : (fun ω => f (X ω) / √a * (g (Y ω) / √b)) =
          fun ω => f (X ω) * g (Y ω) / (√a * √b) := by
        funext ω
        ring
      simp only [e]
      rw [expect_div_const μ (fun ω => f (X ω) * g (Y ω)), abs_div,
        abs_of_pos (mul_pos hsa hsb)]
  have hle := (le_csSup (corrSet_bddAbove μ X Y) hmem).trans h
  rw [div_le_iff₀ (mul_pos hsa hsb)] at hle
  linarith

/-- For `ε ≥ 0`, `ρ(X;Y) ≤ ε` is equivalent to its inequality form. -/
theorem maxCorr_le_iff {μ : FiniteLaw Ω} {X : Ω → α} {Y : Ω → β} {ε : ℝ} (hε : 0 ≤ ε) :
    maxCorr μ X Y ≤ ε ↔ CorrLe μ X Y ε :=
  ⟨corrLe_of_maxCorr_le, maxCorr_le_of_corrLe hε⟩

/-- `ρ(X;Y)` can only grow when `X` and `Y` are refined. -/
theorem corrSet_subset_of_coarser (μ : FiniteLaw Ω) {α' β' : Type*} {X : Ω → α}
    {X' : Ω → α'} {Y : Ω → β} {Y' : Ω → β'} (hX : Coarser X X') (hY : Coarser Y Y') :
    corrSet μ X Y ⊆ corrSet μ X' Y' := by
  rintro c ⟨f, g, hf, hg, hf2, hg2, rfl⟩
  obtain ⟨f', hf'⟩ := exists_fun_of_isFunOf X' (fun ω => f (X ω))
    (fun ω ω' h => by simp only [hX ω ω' h])
  obtain ⟨g', hg'⟩ := exists_fun_of_isFunOf Y' (fun ω => g (Y ω))
    (fun ω ω' h => by simp only [hY ω ω' h])
  have e1 : (fun ω => f' (X' ω)) = fun ω => f (X ω) := funext fun ω => (hf' ω).symm
  have e2 : (fun ω => g' (Y' ω)) = fun ω => g (Y ω) := funext fun ω => (hg' ω).symm
  refine ⟨f', g', ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1]; exact hf
  · rw [e2]; exact hg
  · simp only [← hf']; exact hf2
  · simp only [← hg']; exact hg2
  · simp only [← hf', ← hg']

theorem maxCorr_mono (μ : FiniteLaw Ω) {α' β' : Type*} {X : Ω → α} {X' : Ω → α'}
    {Y : Ω → β} {Y' : Ω → β'} (hX : Coarser X X') (hY : Coarser Y Y') :
    maxCorr μ X Y ≤ maxCorr μ X' Y' := by
  rcases (corrSet μ X Y).eq_empty_or_nonempty with he | hne
  · rw [maxCorr, he, Real.sSup_empty]
    exact maxCorr_nonneg μ X' Y'
  · exact csSup_le_csSup (corrSet_bddAbove μ X' Y') hne (corrSet_subset_of_coarser μ hX hY)

/-- `ρ(X;Y)` depends only on the level sets of `X` and of `Y`. -/
theorem maxCorr_congr (μ : FiniteLaw Ω) {α' β' : Type*} {X : Ω → α} {X' : Ω → α'}
    {Y : Ω → β} {Y' : Ω → β'} (hX : ∀ ω ω', X ω = X ω' ↔ X' ω = X' ω')
    (hY : ∀ ω ω', Y ω = Y ω' ↔ Y' ω = Y' ω') :
    maxCorr μ X Y = maxCorr μ X' Y' :=
  le_antisymm (maxCorr_mono μ (fun ω ω' h => (hX ω ω').mpr h) (fun ω ω' h => (hY ω ω').mpr h))
    (maxCorr_mono μ (fun ω ω' h => (hX ω ω').mp h) (fun ω ω' h => (hY ω ω').mp h))

/-! ### `lem:peyre:basic` -/

/-- `lem:peyre:basic` (a), first claim, for functions of the values: if `E f(X) = 0`
then `|E f(X) g(Y)| ≤ ρ ‖f(X)‖ ‖g(Y) - E g(Y)‖`. -/
theorem corrLe_centered {μ : FiniteLaw Ω} {X : Ω → α} {Y : Ω → β} {ε : ℝ}
    (h : CorrLe μ X Y ε) (f : α → ℝ) (g : β → ℝ) (hf : μ.expect (fun ω => f (X ω)) = 0) :
    |μ.expect (fun ω => f (X ω) * g (Y ω))| ≤ ε * √(μ.expect (fun ω => f (X ω) ^ 2)) *
      √(μ.expect (fun ω => (g (Y ω) - μ.expect (fun ω => g (Y ω))) ^ 2)) := by
  set c := μ.expect (fun ω => g (Y ω))
  have hg0 : μ.expect (fun ω => (fun y => g y - c) (Y ω)) = 0 := by
    show μ.expect (fun ω => g (Y ω) - c) = 0
    rw [FiniteLaw.expect_sub, FiniteLaw.expect_const, sub_self]
  have e : μ.expect (fun ω => f (X ω) * g (Y ω)) =
      μ.expect (fun ω => f (X ω) * (fun y => g y - c) (Y ω)) := by
    have : μ.expect (fun ω => f (X ω) * g (Y ω)) =
        μ.expect (fun ω => f (X ω) * (g (Y ω) - c)) + μ.expect (fun ω => f (X ω)) * c := by
      rw [← FiniteLaw.expect_mul_const, ← FiniteLaw.expect_add]
      exact μ.expect_congr (fun ω => by ring)
    rw [this, hf, zero_mul, add_zero]
  rw [e]
  exact h f (fun y => g y - c) hf hg0

/-- `lem:peyre:basic` (a), first claim, for `F ∈ L²₀(X)` and `G ∈ L²(Y)`. -/
theorem corrLe_isFunOf {μ : FiniteLaw Ω} {X : Ω → α} {Y : Ω → β} {ε : ℝ}
    (h : CorrLe μ X Y ε) {F G : Ω → ℝ} (hF : IsFunOf X F) (hG : IsFunOf Y G)
    (hF0 : μ.expect F = 0) :
    |μ.expect (fun ω => F ω * G ω)| ≤ ε * √(μ.expect (fun ω => F ω ^ 2)) *
      √(μ.expect (fun ω => (G ω - μ.expect G) ^ 2)) := by
  obtain ⟨φ, hφ⟩ := exists_fun_of_isFunOf X F hF
  obtain ⟨ψ, hψ⟩ := exists_fun_of_isFunOf Y G hG
  have eF : F = fun ω => φ (X ω) := funext hφ
  have eG : G = fun ω => ψ (Y ω) := funext hψ
  subst eF eG
  exact corrLe_centered h φ ψ hF0

/-- `lem:peyre:basic` (a), second claim: `‖E[f|Y]‖ ≤ ρ ‖f‖` for `f ∈ L²₀(X)`. -/
theorem sqrt_condExp_sq_le {μ : FiniteLaw Ω} {X : Ω → α} {Y : Ω → β} {ε : ℝ}
    (h : CorrLe μ X Y ε) (hε : 0 ≤ ε) {F : Ω → ℝ} (hF : IsFunOf X F) (hF0 : μ.expect F = 0) :
    √(μ.expect (fun ω => condExp μ Y F ω ^ 2)) ≤ ε * √(μ.expect (fun ω => F ω ^ 2)) := by
  set H := condExp μ Y F with hH
  have hHf : IsFunOf Y H := condExp_isFunOf μ Y F
  have hH0 : μ.expect H = 0 := by rw [hH, expect_condExp, hF0]
  have e : μ.expect (fun ω => H ω ^ 2) = μ.expect (fun ω => F ω * H ω) := by
    have := expect_mul_condExp μ Y F H hHf
    rw [← hH] at this
    rw [show (fun ω => H ω ^ 2) = fun ω => H ω * H ω from funext fun ω => sq (H ω), this]
    exact μ.expect_congr (fun ω => mul_comm _ _)
  have ha := corrLe_isFunOf h hF hHf hF0
  rw [hH0] at ha
  simp only [sub_zero] at ha
  rw [← e] at ha
  have hn : 0 ≤ μ.expect (fun ω => H ω ^ 2) := μ.second_moment_nonneg _
  set s := √(μ.expect (fun ω => H ω ^ 2))
  have hs : s ^ 2 = μ.expect (fun ω => H ω ^ 2) := Real.sq_sqrt hn
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  rw [abs_of_nonneg hn, ← hs] at ha
  rcases hs0.eq_or_lt with h0 | h0
  · rw [← h0]
    exact mul_nonneg hε (Real.sqrt_nonneg _)
  · nlinarith

/-- `lem:peyre:basic` (b) (`cor:condLaw-decorrelation`): if `ρ(X;Y | Z = z) ≤ ε` for every
value `z` of positive probability, `f ∈ L²(X,Z)` has `E[f|Z] = 0` and `g ∈ L²(Y,Z)`, then
`|E fg| ≤ ε ‖f‖ ‖g - E[g|Z]‖`.  Here `E[f|Z] = 0` is only required at points of
positive mass. -/
theorem cond_decorrelation (μ : FiniteLaw Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hyp : ∀ z, ∀ hz : 0 < prob μ (fun ω => Z ω = z),
      CorrLe (condLaw μ (fun ω => Z ω = z) hz) X Y ε)
    {f g : Ω → ℝ} (hf : ∀ ω ω', X ω = X ω' → Z ω = Z ω' → f ω = f ω')
    (hf0 : ∀ ω, μ.weight ω ≠ 0 → condExp μ Z f ω = 0)
    (hg : ∀ ω ω', Y ω = Y ω' → Z ω = Z ω' → g ω = g ω') :
    |μ.expect (fun ω => f ω * g ω)| ≤ ε * √(μ.expect (fun ω => f ω ^ 2)) *
      √(μ.expect (fun ω => (g ω - condExp μ Z g ω) ^ 2)) := by
  set A : Ω → ℝ := condExp μ Z (fun ω => f ω ^ 2) with hA_def
  set B : Ω → ℝ := condExp μ Z (fun ω => (g ω - condExp μ Z g ω) ^ 2) with hB_def
  have hpt : ∀ ω₀, μ.weight ω₀ ≠ 0 →
      |condExp μ Z (fun ω => f ω * g ω) ω₀| ≤ ε * (√(A ω₀) * √(B ω₀)) := by
    intro ω₀ hw₀
    have hpos : 0 < prob μ (fun ω => Z ω = Z ω₀) :=
      prob_pos_of_weight (E := fun ω => Z ω = Z ω₀) rfl hw₀
    have hνe : ∀ u, (condLaw μ (fun ω => Z ω = Z ω₀) hpos).expect u = condExp μ Z u ω₀ :=
      fun u => cond_expect_level μ Z ω₀ hpos u
    obtain ⟨φ, hφ⟩ := exists_fun_on X (fun ω => Z ω = Z ω₀) f
      (fun ω ω' h1 h2 hx => hf ω ω' hx (h1.trans h2.symm))
    obtain ⟨ψ, hψ⟩ := exists_fun_on Y (fun ω => Z ω = Z ω₀) g
      (fun ω ω' h1 h2 hy => hg ω ω' hy (h1.trans h2.symm))
    have h1 : (condLaw μ (fun ω => Z ω = Z ω₀) hpos).expect (fun ω => φ (X ω)) = 0 := by
      rw [cond_expect_congr μ hpos (v := f) (fun ω hω => (hφ ω hω).symm), hνe]
      exact hf0 ω₀ hw₀
    have ha := corrLe_centered (hyp (Z ω₀) hpos) φ ψ h1
    have e1 : (condLaw μ (fun ω => Z ω = Z ω₀) hpos).expect (fun ω => φ (X ω) * ψ (Y ω)) =
        condExp μ Z (fun ω => f ω * g ω) ω₀ := by
      rw [← hνe]
      exact cond_expect_congr μ hpos (fun ω hω => by rw [hφ ω hω, hψ ω hω])
    have e2 : (condLaw μ (fun ω => Z ω = Z ω₀) hpos).expect (fun ω => φ (X ω) ^ 2) = A ω₀ := by
      rw [hA_def, ← hνe]
      exact cond_expect_congr μ hpos (fun ω hω => by rw [hφ ω hω])
    have e3 : (condLaw μ (fun ω => Z ω = Z ω₀) hpos).expect (fun ω => ψ (Y ω)) =
        condExp μ Z g ω₀ := by
      rw [← hνe]
      exact cond_expect_congr μ hpos (fun ω hω => by rw [hψ ω hω])
    have e4 : (condLaw μ (fun ω => Z ω = Z ω₀) hpos).expect (fun ω => (ψ (Y ω) -
        (condLaw μ (fun ω => Z ω = Z ω₀) hpos).expect (fun ω => ψ (Y ω))) ^ 2) = B ω₀ := by
      rw [e3, hB_def, ← hνe (fun ω => (g ω - condExp μ Z g ω) ^ 2)]
      exact cond_expect_congr μ hpos (fun ω hω => by
        rw [hψ ω hω, condExp_isFunOf μ Z g ω ω₀ hω])
    rw [e1, e2, e4, mul_assoc] at ha
    exact ha
  have hA : ∀ ω, 0 ≤ A ω := fun ω => condExp_nonneg μ Z (fun ω => sq_nonneg (f ω)) ω
  have hB : ∀ ω, 0 ≤ B ω := fun ω => condExp_nonneg μ Z (fun ω => sq_nonneg _) ω
  have eA : μ.expect (fun ω => √(A ω) ^ 2) = μ.expect (fun ω => f ω ^ 2) := by
    rw [show (fun ω => √(A ω) ^ 2) = A from funext fun ω => Real.sq_sqrt (hA ω), hA_def,
      expect_condExp]
  have eB : μ.expect (fun ω => √(B ω) ^ 2) =
      μ.expect (fun ω => (g ω - condExp μ Z g ω) ^ 2) := by
    rw [show (fun ω => √(B ω) ^ 2) = B from funext fun ω => Real.sq_sqrt (hB ω), hB_def,
      expect_condExp]
  calc |μ.expect (fun ω => f ω * g ω)|
      = |μ.expect (condExp μ Z (fun ω => f ω * g ω))| := by rw [expect_condExp]
    _ ≤ μ.expect (fun ω => |condExp μ Z (fun ω => f ω * g ω) ω|) := μ.abs_expect_le _
    _ ≤ μ.expect (fun ω => ε * (√(A ω) * √(B ω))) := expect_mono_ae μ hpt
    _ = ε * μ.expect (fun ω => √(A ω) * √(B ω)) := μ.expect_const_mul _ _
    _ ≤ ε * (√(μ.expect (fun ω => √(A ω) ^ 2)) * √(μ.expect (fun ω => √(B ω) ^ 2))) :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans (μ.abs_expect_mul_le _ _)) hε
    _ = _ := by rw [eA, eB, mul_assoc]

/-- `lem:peyre:basic` (b), weaker right side `ε ‖f‖ ‖g‖`. -/
theorem cond_decorrelation' (μ : FiniteLaw Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hyp : ∀ z, ∀ hz : 0 < prob μ (fun ω => Z ω = z),
      CorrLe (condLaw μ (fun ω => Z ω = z) hz) X Y ε)
    {f g : Ω → ℝ} (hf : ∀ ω ω', X ω = X ω' → Z ω = Z ω' → f ω = f ω')
    (hf0 : ∀ ω, μ.weight ω ≠ 0 → condExp μ Z f ω = 0)
    (hg : ∀ ω ω', Y ω = Y ω' → Z ω = Z ω' → g ω = g ω') :
    |μ.expect (fun ω => f ω * g ω)| ≤ ε * √(μ.expect (fun ω => f ω ^ 2)) *
      √(μ.expect (fun ω => g ω ^ 2)) := by
  refine (cond_decorrelation μ X Y Z hε hyp hf hf0 hg).trans ?_
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (expect_sq_sub_condExp_le μ Z g))
    (mul_nonneg hε (Real.sqrt_nonneg _))

/-- `cor:condLaw-decorrelation` (Section 4.6) with the hypothesis stated with conditional maximal
correlations: if `ρ(X;Y | Z = z) ≤ ε` for every `z` with `P(Z = z) > 0`, `f ∈ L²(X,Z)`
with `E[f|Z] = 0` and `g ∈ L²(Y,Z)`, then `|E fg| ≤ ε ‖f‖ ‖g - E[g|Z]‖ ≤ ε ‖f‖ ‖g‖`. -/
theorem cond_decorrelation_maxCorr (μ : FiniteLaw Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hyp : ∀ z, ∀ hz : 0 < prob μ (fun ω => Z ω = z),
      maxCorr (condLaw μ (fun ω => Z ω = z) hz) X Y ≤ ε)
    {f g : Ω → ℝ} (hf : ∀ ω ω', X ω = X ω' → Z ω = Z ω' → f ω = f ω')
    (hf0 : ∀ ω, μ.weight ω ≠ 0 → condExp μ Z f ω = 0)
    (hg : ∀ ω ω', Y ω = Y ω' → Z ω = Z ω' → g ω = g ω') :
    |μ.expect (fun ω => f ω * g ω)| ≤ ε * √(μ.expect (fun ω => f ω ^ 2)) *
        √(μ.expect (fun ω => (g ω - condExp μ Z g ω) ^ 2)) ∧
      ε * √(μ.expect (fun ω => f ω ^ 2)) *
        √(μ.expect (fun ω => (g ω - condExp μ Z g ω) ^ 2)) ≤
      ε * √(μ.expect (fun ω => f ω ^ 2)) * √(μ.expect (fun ω => g ω ^ 2)) := by
  have hyp' := fun z hz => corrLe_of_maxCorr_le (hyp z hz)
  refine ⟨cond_decorrelation μ X Y Z hε hyp' hf hf0 hg, ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (expect_sq_sub_condExp_le μ Z g))
    (mul_nonneg hε (Real.sqrt_nonneg _))

/-- `lem:peyre:basic` (c), inequality form: if `‖E[f|Y]‖² ≤ λ ‖f‖²` for all `f ∈ L²₀(X)`,
then `|E f(X) g(Y)| ≤ √λ ‖f(X)‖ ‖g(Y)‖`. -/
theorem corrLe_of_condExp_sq_le (μ : FiniteLaw Ω) (X : Ω → α) (Y : Ω → β) {lam : ℝ}
    (hlam : 0 ≤ lam)
    (h : ∀ F : Ω → ℝ, IsFunOf X F → μ.expect F = 0 →
      μ.expect (fun ω => condExp μ Y F ω ^ 2) ≤ lam * μ.expect (fun ω => F ω ^ 2)) :
    CorrLe μ X Y (√lam) := by
  intro φ ψ hφ _
  have e : μ.expect (fun ω => φ (X ω) * ψ (Y ω)) =
      μ.expect (fun ω => condExp μ Y (fun ω => φ (X ω)) ω * ψ (Y ω)) :=
    (expect_condExp_mul μ Y (fun ω => φ (X ω)) _ (isFunOf_comp Y ψ)).symm
  rw [e]
  calc _ ≤ √(μ.expect (fun ω => condExp μ Y (fun ω => φ (X ω)) ω ^ 2)) *
        √(μ.expect (fun ω => ψ (Y ω) ^ 2)) := μ.abs_expect_mul_le _ _
    _ ≤ √(lam * μ.expect (fun ω => φ (X ω) ^ 2)) * √(μ.expect (fun ω => ψ (Y ω) ^ 2)) :=
        mul_le_mul_of_nonneg_right
          (Real.sqrt_le_sqrt (h _ (isFunOf_comp X φ) hφ)) (Real.sqrt_nonneg _)
    _ = _ := by rw [Real.sqrt_mul hlam]

/-- `lem:peyre:basic` (c): if `‖E[f|Y]‖² ≤ λ ‖f‖²` for all `f ∈ L²₀(X)`, then
`ρ(X;Y) ≤ √λ`. -/
theorem maxCorr_le_of_condExp_sq_le (μ : FiniteLaw Ω) (X : Ω → α) (Y : Ω → β) {lam : ℝ}
    (hlam : 0 ≤ lam)
    (h : ∀ F : Ω → ℝ, IsFunOf X F → μ.expect F = 0 →
      μ.expect (fun ω => condExp μ Y F ω ^ 2) ≤ lam * μ.expect (fun ω => F ω ^ 2)) :
    maxCorr μ X Y ≤ √lam :=
  maxCorr_le_of_corrLe (Real.sqrt_nonneg _) (corrLe_of_condExp_sq_le μ X Y hlam h)

/-- `def:prelim:maxcorr`: `ρ(X;Y)` is the norm of the conditional expectation operator
`L²₀(X) → L²(Y)`, `f ↦ E[f|Y]`: for `c ≥ 0`, `ρ(X;Y) ≤ c` iff `‖E[f|Y]‖ ≤ c ‖f‖` for every
`f ∈ L²₀(X)`. -/
theorem maxCorr_le_iff_condExp (μ : FiniteLaw Ω) (X : Ω → α) (Y : Ω → β) {c : ℝ}
    (hc : 0 ≤ c) :
    maxCorr μ X Y ≤ c ↔ ∀ F : Ω → ℝ, IsFunOf X F → μ.expect F = 0 →
      √(μ.expect (fun ω => condExp μ Y F ω ^ 2)) ≤ c * √(μ.expect (fun ω => F ω ^ 2)) := by
  constructor
  · intro h F hF hF0
    exact sqrt_condExp_sq_le (corrLe_of_maxCorr_le h) hc hF hF0
  · intro h
    have h2 : ∀ F : Ω → ℝ, IsFunOf X F → μ.expect F = 0 →
        μ.expect (fun ω => condExp μ Y F ω ^ 2) ≤ c ^ 2 * μ.expect (fun ω => F ω ^ 2) := by
      intro F hF hF0
      have h1 := h F hF hF0
      have hA : 0 ≤ μ.expect (fun ω => condExp μ Y F ω ^ 2) := μ.second_moment_nonneg _
      have hB : 0 ≤ μ.expect (fun ω => F ω ^ 2) := μ.second_moment_nonneg _
      have h3 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
      rw [Real.sq_sqrt hA, mul_pow, Real.sq_sqrt hB] at h3
      exact h3
    have := maxCorr_le_of_condExp_sq_le μ X Y (sq_nonneg c) h2
    rwa [Real.sqrt_sq hc] at this

/-- `def:prelim:maxcorr`: if `L²(X) ∩ L²(Y)` contains a function that is not a.s. constant,
then `ρ(X;Y) = 1`. -/
theorem maxCorr_eq_one_of_common (μ : FiniteLaw Ω) (X : Ω → α) (Y : Ω → β) {h : Ω → ℝ}
    (hX : IsFunOf X h) (hY : IsFunOf Y h)
    (hvar : 0 < μ.expect (fun ω => (h ω - μ.expect h) ^ 2)) : maxCorr μ X Y = 1 := by
  apply le_antisymm (maxCorr_le_one μ X Y)
  obtain ⟨φ, hφ⟩ := exists_fun_of_isFunOf X h hX
  obtain ⟨ψ, hψ⟩ := exists_fun_of_isFunOf Y h hY
  set m := μ.expect h with hm
  set V := μ.expect (fun ω => (h ω - m) ^ 2) with hV
  have hσ : 0 < √V := Real.sqrt_pos.mpr hvar
  have hσ2 : √V ^ 2 = V := Real.sq_sqrt hvar.le
  have hmean : μ.expect (fun ω => (h ω - m) / √V) = 0 := by
    rw [expect_div_const μ (fun ω => h ω - m), FiniteLaw.expect_sub, FiniteLaw.expect_const,
      ← hm, sub_self, zero_div]
  have hsq : μ.expect (fun ω => ((h ω - m) / √V) ^ 2) = 1 := by
    have e : (fun ω => ((h ω - m) / √V) ^ 2) = fun ω => (h ω - m) ^ 2 / V := by
      funext ω
      rw [div_pow, hσ2]
    rw [e, expect_div_const μ (fun ω => (h ω - m) ^ 2), ← hV, div_self hvar.ne']
  have hmem : (1 : ℝ) ∈ corrSet μ X Y := by
    refine ⟨fun a => (φ a - m) / √V, fun b => (ψ b - m) / √V, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [← hφ]
      exact hmean
    · simp only [← hψ]
      exact hmean
    · simp only [← hφ]
      exact hsq
    · simp only [← hψ]
      exact hsq
    · simp only [← hφ, ← hψ]
      have e : (fun ω => (h ω - m) / √V * ((h ω - m) / √V)) =
          fun ω => ((h ω - m) / √V) ^ 2 := funext fun ω => (sq _).symm
      rw [e, hsq, abs_one]
  exact le_csSup (corrSet_bddAbove μ X Y) hmem

end Sarkozy.Peyre
