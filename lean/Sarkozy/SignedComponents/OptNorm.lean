module

public import Sarkozy.MiddleComparison.Atom

@[expose] public section

/-!
# Optimal norms of changes at a cut (`rem:cp:charging`(ii))

`paper/sections/09_comparison_theorem.tex`, `rem:cp:charging`(ii);
`paper/sections/21_middle_records.tex`, `lem:middle-comparison-prices`.

The charging rule prices a change `ζ` at the reserved cut by a norm `N` with
`|Q_ζ(F, G)| ≤ N ‖F‖_m ‖G‖_m`, where `m` is the actual half marginal of the record. B7's
`ReplacementData` asks for such an `N` for each of the twelve changes of a middle block. This
file gives the generic tools to supply it:

* `hsq c m G = ∑ₓ m(x) G(x)²`, the squared `L²(m)` norm (B7's `halfSq` is `hsq` at the record's
  plus marginal);
* `FormBound c m L C`: `C ≥ 0` and `|Q_L(F, G)| ≤ C ‖F‖_m ‖G‖_m` for all `F, G`;
  `FormBounded c m L`: some `C` works;
* closure: `FormBound.add`, `.smul`, `.neg`, `.sub`, `FormBounded.sum`, and the symmetric and
  skew parts (`FormBound.symPart`, `FormBound.skewPart`, `FormBound.changePart`);
* **`formBound_signedIntegral`**: the elementary bound. If every configuration `z` charged by
  `w` has both halves in the support of `m`, then `Q_w` is bounded, with
  `C = ∑_z |w(z)| / (√m(z₊) √m(z₋))`. This is not the paper's bound; it only shows that the
  optimal constant is finite;
* **`optNorm c m L`**, the optimal constant `inf {C : FormBound c m L C}`: `optNorm_nonneg`,
  `optNorm_spec` (it is itself a bound, when some bound exists) and `optNorm_le` (it is below
  every bound, in particular below the paper's).

So a norm field can be discharged by `optNorm`, and the paper's norm bounds become statements
`FormBound c m ζ K` about the concrete changes, from which `optNorm_le` gives `N ≤ K`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.SignedComponents

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.UpperComparison

variable {W Y : Type*} [Fintype W] [DecidableEq W] (c : ReflectionCut W)

section Form

variable {c}

theorem form_add (L₁ L₂ : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) (F G : (c.Half → Y) → ℝ) :
    c.form (L₁ + L₂) F G = c.form L₁ F G + c.form L₂ F G := rfl

theorem form_smul (a : ℝ) (L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) (F G : (c.Half → Y) → ℝ) :
    c.form (a • L) F G = a * c.form L F G := rfl

theorem form_neg (L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) (F G : (c.Half → Y) → ℝ) :
    c.form (-L) F G = -c.form L F G := rfl

theorem form_zero (F G : (c.Half → Y) → ℝ) : c.form (0 : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) F G = 0 := rfl

end Form

variable [Fintype Y]

/-- The squared norm `‖G‖²_m = ∑ₓ m(x) G(x)²` of a function of a half. -/
noncomputable def hsq (m : (c.Half → Y) → ℝ) (G : (c.Half → Y) → ℝ) : ℝ :=
  ∑ x, m x * (G x * G x)

/-- `C` bounds the cut form of `L` relative to `m`: `C ≥ 0` and
`|Q_L(F, G)| ≤ C ‖F‖_m ‖G‖_m` (`rem:cp:charging`(ii)). -/
def FormBound (m : (c.Half → Y) → ℝ) (L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ F G : (c.Half → Y) → ℝ,
    |c.form L F G| ≤ C * Real.sqrt (hsq c m F) * Real.sqrt (hsq c m G)

/-- The cut form of `L` is bounded relative to `m`. -/
def FormBounded (m : (c.Half → Y) → ℝ) (L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) : Prop :=
  ∃ C, FormBound c m L C

variable {c}

theorem hsq_nonneg {m : (c.Half → Y) → ℝ} (hm : ∀ x, 0 ≤ m x) (G : (c.Half → Y) → ℝ) :
    0 ≤ hsq c m G :=
  sum_nonneg fun x _ => mul_nonneg (hm x) (mul_self_nonneg _)

namespace FormBound

variable {m : (c.Half → Y) → ℝ} {L L₁ L₂ : ((W → Y) → ℝ) →ₗ[ℝ] ℝ} {C C₁ C₂ : ℝ}

theorem nonneg (h : FormBound c m L C) : 0 ≤ C := h.1

theorem add (h₁ : FormBound c m L₁ C₁) (h₂ : FormBound c m L₂ C₂) :
    FormBound c m (L₁ + L₂) (C₁ + C₂) := by
  refine ⟨add_nonneg h₁.1 h₂.1, fun F G => ?_⟩
  rw [form_add]
  calc |c.form L₁ F G + c.form L₂ F G| ≤ |c.form L₁ F G| + |c.form L₂ F G| := abs_add_le _ _
    _ ≤ C₁ * Real.sqrt (hsq c m F) * Real.sqrt (hsq c m G) +
        C₂ * Real.sqrt (hsq c m F) * Real.sqrt (hsq c m G) := add_le_add (h₁.2 F G) (h₂.2 F G)
    _ = _ := by ring

theorem smul (h : FormBound c m L C) (a : ℝ) : FormBound c m (a • L) (|a| * C) := by
  refine ⟨mul_nonneg (abs_nonneg a) h.1, fun F G => ?_⟩
  rw [form_smul, abs_mul]
  calc |a| * |c.form L F G| ≤ |a| * (C * Real.sqrt (hsq c m F) * Real.sqrt (hsq c m G)) :=
        mul_le_mul_of_nonneg_left (h.2 F G) (abs_nonneg a)
    _ = _ := by ring

theorem neg (h : FormBound c m L C) : FormBound c m (-L) C := by
  refine ⟨h.1, fun F G => ?_⟩
  rw [form_neg, abs_neg]
  exact h.2 F G

theorem sub (h₁ : FormBound c m L₁ C₁) (h₂ : FormBound c m L₂ C₂) :
    FormBound c m (L₁ - L₂) (C₁ + C₂) := by
  rw [sub_eq_add_neg]
  exact h₁.add h₂.neg

theorem mono (h : FormBound c m L C) {C' : ℝ} (hC : C ≤ C') : FormBound c m L C' := by
  refine ⟨h.1.trans hC, fun F G => (h.2 F G).trans ?_⟩
  have h1 := Real.sqrt_nonneg (hsq c m F)
  have h2 := Real.sqrt_nonneg (hsq c m G)
  have := mul_le_mul_of_nonneg_right hC h1
  exact mul_le_mul_of_nonneg_right this h2

/-- The symmetric part at the cut obeys the same bound (`form_symPart`). -/
theorem symPart (h : FormBound c m L C) :
    FormBound c m (Sarkozy.RecordExpansion.symPart c L) C := by
  refine ⟨h.1, fun F G => ?_⟩
  rw [form_symPart]
  have h1 := h.2 F G
  have h2 := h.2 G F
  rw [abs_le] at h1 h2 ⊢
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- The skew part at the cut obeys the same bound (`form_skewPart`). -/
theorem skewPart (h : FormBound c m L C) :
    FormBound c m (Sarkozy.RecordExpansion.skewPart c L) C := by
  refine ⟨h.1, fun F G => ?_⟩
  rw [form_skewPart]
  have h1 := h.2 F G
  have h2 := h.2 G F
  rw [abs_le] at h1 h2 ⊢
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

end FormBound

theorem FormBounded.zero (m : (c.Half → Y) → ℝ) :
    FormBounded c m (0 : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) :=
  ⟨0, le_rfl, fun F G => by rw [form_zero]; simp⟩

theorem FormBounded.add {m : (c.Half → Y) → ℝ} {L₁ L₂ : ((W → Y) → ℝ) →ₗ[ℝ] ℝ}
    (h₁ : FormBounded c m L₁) (h₂ : FormBounded c m L₂) : FormBounded c m (L₁ + L₂) :=
  let ⟨_, hC₁⟩ := h₁
  let ⟨_, hC₂⟩ := h₂
  ⟨_, hC₁.add hC₂⟩

theorem FormBounded.smul {m : (c.Half → Y) → ℝ} {L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ}
    (h : FormBounded c m L) (a : ℝ) : FormBounded c m (a • L) :=
  let ⟨_, hC⟩ := h
  ⟨_, hC.smul a⟩

theorem FormBounded.sub {m : (c.Half → Y) → ℝ} {L₁ L₂ : ((W → Y) → ℝ) →ₗ[ℝ] ℝ}
    (h₁ : FormBounded c m L₁) (h₂ : FormBounded c m L₂) : FormBounded c m (L₁ - L₂) :=
  let ⟨_, hC₁⟩ := h₁
  let ⟨_, hC₂⟩ := h₂
  ⟨_, hC₁.sub hC₂⟩

theorem FormBounded.sum {m : (c.Half → Y) → ℝ} {K : Type*} (s : Finset K)
    (L : K → ((W → Y) → ℝ) →ₗ[ℝ] ℝ) (h : ∀ k ∈ s, FormBounded c m (L k)) :
    FormBounded c m (∑ k ∈ s, L k) :=
  Finset.sum_induction L (FormBounded c m) (fun _ _ h₁ h₂ => h₁.add h₂) (FormBounded.zero m) h

/-! ## The elementary bound from the supports -/

/-- A single value is controlled by the norm: `|G(x)| ≤ ‖G‖_m / √m(x)` when `m(x) > 0`. -/
theorem abs_le_of_hsq {m : (c.Half → Y) → ℝ} (hm : ∀ x, 0 ≤ m x) (G : (c.Half → Y) → ℝ)
    {x : c.Half → Y} (hx : 0 < m x) : |G x| ≤ Real.sqrt (hsq c m G) / Real.sqrt (m x) := by
  have h1 : m x * (G x * G x) ≤ hsq c m G :=
    single_le_sum (f := fun y => m y * (G y * G y))
      (fun y _ => mul_nonneg (hm y) (mul_self_nonneg _)) (mem_univ x)
  have hs : 0 < Real.sqrt (m x) := Real.sqrt_pos.mpr hx
  rw [le_div_iff₀ hs]
  have e : Real.sqrt (m x * (G x * G x)) = |G x| * Real.sqrt (m x) := by
    rw [Real.sqrt_mul hx.le, Real.sqrt_mul_self_eq_abs, mul_comm]
  rw [← e]
  exact Real.sqrt_le_sqrt h1

/-- The plus half `z₊` of a configuration. -/
def plusHalf (z : W → Y) : c.Half → Y := fun v => z v.1

/-- The minus half `z₋` of a configuration, read on the plus half through the reflection. -/
def minusHalf (z : W → Y) : c.Half → Y := fun v => z (c.flip v.1)

/-- Both halves of `z` lie in the support of `m`. -/
def HalvesIn (m : (c.Half → Y) → ℝ) (z : W → Y) : Prop :=
  0 < m (plusHalf (c := c) z) ∧ 0 < m (minusHalf (c := c) z)

/-- **The elementary bound** (finiteness of the optimal norm): if every configuration charged by
`w` has both halves in the support of `m`, the cut form of `w` is bounded relative to `m`, with
`C = ∑_z |w(z)| / (√m(z₊) √m(z₋))`. -/
theorem formBound_signedIntegral {m : (c.Half → Y) → ℝ} (hm : ∀ x, 0 ≤ m x)
    {w : (W → Y) → ℝ} (hsupp : ∀ z, w z ≠ 0 → HalvesIn (c := c) m z) :
    FormBound c m (signedIntegral w)
      (∑ z, |w z| / (Real.sqrt (m (plusHalf (c := c) z)) *
        Real.sqrt (m (minusHalf (c := c) z)))) := by
  refine ⟨sum_nonneg fun z _ => div_nonneg (abs_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)), fun F G => ?_⟩
  change |∑ z, w z * (F (plusHalf (c := c) z) * G (minusHalf (c := c) z))| ≤ _
  rw [sum_mul, sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun z _ => ?_)
  by_cases hz : w z = 0
  · rw [hz]
    simp
  · obtain ⟨h1, h2⟩ := hsupp z hz
    have hF := abs_le_of_hsq hm F h1
    have hG := abs_le_of_hsq hm G h2
    have ha := Real.sqrt_pos.mpr h1
    have hb := Real.sqrt_pos.mpr h2
    rw [abs_mul, abs_mul]
    have hFn := abs_nonneg (F (plusHalf (c := c) z))
    have hGn := abs_nonneg (G (minusHalf (c := c) z))
    calc |w z| * (|F (plusHalf (c := c) z)| * |G (minusHalf (c := c) z)|) ≤
        |w z| * ((Real.sqrt (hsq c m F) / Real.sqrt (m (plusHalf (c := c) z))) *
          (Real.sqrt (hsq c m G) / Real.sqrt (m (minusHalf (c := c) z)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hF hG hGn (le_trans hFn hF)) (abs_nonneg _)
      _ = _ := by field_simp

theorem formBounded_signedIntegral {m : (c.Half → Y) → ℝ} (hm : ∀ x, 0 ≤ m x)
    {w : (W → Y) → ℝ} (hsupp : ∀ z, w z ≠ 0 → HalvesIn (c := c) m z) :
    FormBounded c m (signedIntegral w) :=
  ⟨_, formBound_signedIntegral hm hsupp⟩

/-! ## The optimal norm -/

variable (c) in
/-- **The optimal norm** `inf {C : |Q_L(F, G)| ≤ C ‖F‖_m ‖G‖_m}` of the cut form of `L` relative to
`m`. -/
noncomputable def optNorm (m : (c.Half → Y) → ℝ) (L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) : ℝ :=
  sInf {C | FormBound c m L C}

theorem optNorm_nonneg (m : (c.Half → Y) → ℝ) (L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) :
    0 ≤ optNorm c m L :=
  Real.sInf_nonneg fun _ hC => hC.1

/-- The optimal norm is below every bound (`N ≤ K` from the paper's bound `K`). -/
theorem optNorm_le {m : (c.Half → Y) → ℝ} {L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ} {C : ℝ}
    (h : FormBound c m L C) : optNorm c m L ≤ C :=
  csInf_le ⟨0, fun _ hC => hC.1⟩ h

/-- **The optimal norm is a bound**, when some bound exists. -/
theorem optNorm_spec {m : (c.Half → Y) → ℝ} {L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ}
    (h : FormBounded c m L) : FormBound c m L (optNorm c m L) := by
  obtain ⟨C₀, hC₀⟩ := h
  refine ⟨optNorm_nonneg m L, fun F G => ?_⟩
  set A := Real.sqrt (hsq c m F) * Real.sqrt (hsq c m G) with hA
  have hA0 : 0 ≤ A := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [mul_assoc]
  rcases hA0.lt_or_eq with hpos | hzero
  · have key : |c.form L F G| / A ≤ optNorm c m L := by
      refine le_csInf ⟨C₀, hC₀⟩ fun C hC => ?_
      rw [div_le_iff₀ hpos]
      have := hC.2 F G
      rw [mul_assoc] at this
      exact this
    rw [div_le_iff₀ hpos] at key
    exact key
  · have e : Real.sqrt (hsq c m F) * Real.sqrt (hsq c m G) = 0 := by rw [← hA, ← hzero]
    rw [e, mul_zero]
    have := hC₀.2 F G
    rw [mul_assoc, e, mul_zero] at this
    exact this

end Sarkozy.SignedComponents
