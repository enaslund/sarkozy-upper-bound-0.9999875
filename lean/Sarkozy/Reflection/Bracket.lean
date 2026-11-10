module

public import Sarkozy.Reflection.CommonCut
public import Sarkozy.Reflection.Holder

/-!
# Block domination at one cut

A bracket is the positivity of the two-by-two block quadratic form, with its
two diagonal forms explicitly reflection positive. The off-diagonal form may
come from a signed law. The mixed bound follows directly from the quadratic
discriminant and does not require an inverse or an invertibility assumption.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.ReflectionCut

variable {V X : Type*} [Fintype V] [DecidableEq V]

theorem form_smul_left (c : ReflectionCut V) (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (a : ℝ) (F G : (c.Half → X) → ℝ) : c.form L (a • F) G = a * c.form L F G := by
  unfold form
  have he : (fun z : V → X => (a • F) (fun v => z v.1) * G (fun v => z (c.flip v.1))) =
      a • (fun z => F (fun v => z v.1) * G (fun v => z (c.flip v.1))) := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [he, map_smul, smul_eq_mul]

theorem form_smul_right (c : ReflectionCut V) (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (a : ℝ) (F G : (c.Half → X) → ℝ) : c.form L F (a • G) = a * c.form L F G := by
  unfold form
  have he : (fun z : V → X => F (fun v => z v.1) * (a • G) (fun v => z (c.flip v.1))) =
      a • (fun z => F (fun v => z v.1) * G (fun v => z (c.flip v.1))) := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm]
  rw [he, map_smul, smul_eq_mul]

theorem form_add_left (c : ReflectionCut V) (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (F G H : (c.Half → X) → ℝ) : c.form L (F + G) H = c.form L F H + c.form L G H := by
  unfold form
  have he : (fun z : V → X => (F + G) (fun v => z v.1) * H (fun v => z (c.flip v.1))) =
      (fun z => F (fun v => z v.1) * H (fun v => z (c.flip v.1))) +
      (fun z => G (fun v => z v.1) * H (fun v => z (c.flip v.1))) := by
    funext z
    simp only [Pi.add_apply, add_mul]
  rw [he, map_add]

theorem form_add_right (c : ReflectionCut V) (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (F G H : (c.Half → X) → ℝ) : c.form L F (G + H) = c.form L F G + c.form L F H := by
  unfold form
  have he : (fun z : V → X => F (fun v => z v.1) * (G + H) (fun v => z (c.flip v.1))) =
      (fun z => F (fun v => z v.1) * G (fun v => z (c.flip v.1))) +
      (fun z => F (fun v => z v.1) * H (fun v => z (c.flip v.1))) := by
    funext z
    simp only [Pi.add_apply, mul_add]
  rw [he, map_add]

theorem form_sub_left (c : ReflectionCut V) (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (F G H : (c.Half → X) → ℝ) : c.form L (F - G) H = c.form L F H - c.form L G H := by
  rw [show F - G = F + (-1 : ℝ) • G by ext x; simp [sub_eq_add_neg]]
  rw [c.form_add_left, c.form_smul_left]
  ring

theorem form_sub_right (c : ReflectionCut V) (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (F G H : (c.Half → X) → ℝ) : c.form L F (G - H) = c.form L F G - c.form L F H := by
  rw [show G - H = G + (-1 : ℝ) • H by ext x; simp [sub_eq_add_neg]]
  rw [c.form_add_right, c.form_smul_right]
  ring

structure Bracket (c : ReflectionCut V) (L K R : ((V → X) → ℝ) →ₗ[ℝ] ℝ) : Prop where
  left_positive : c.Positive L
  right_positive : c.Positive R
  nonneg : ∀ F G : (c.Half → X) → ℝ,
    0 ≤ c.form L F F + 2 * c.form K F G + c.form R G G

theorem Bracket.cauchy_schwarz_sq {c : ReflectionCut V}
    {L K R : ((V → X) → ℝ) →ₗ[ℝ] ℝ} (h : c.Bracket L K R)
    (F G : (c.Half → X) → ℝ) :
    |c.form K F G| ^ 2 ≤ c.form L F F * c.form R G G := by
  have hquad (t : ℝ) := h.nonneg (t • F) G
  simp only [c.form_smul_left, c.form_smul_right] at hquad
  have hd := discrim_le_zero (fun t => show 0 ≤
    c.form L F F * (t * t) + (2 * c.form K F G) * t + c.form R G G by
      nlinarith [hquad t])
  rw [discrim] at hd
  rw [sq_abs]
  nlinarith

theorem Bracket.abs_form_le {c : ReflectionCut V}
    {L K R : ((V → X) → ℝ) →ₗ[ℝ] ℝ} (h : c.Bracket L K R)
    (F G : (c.Half → X) → ℝ) :
    |c.form K F G| ≤ Real.sqrt (c.form L F F) * Real.sqrt (c.form R G G) := by
  have hs := Real.abs_le_sqrt (h.cauchy_schwarz_sq F G)
  rw [abs_abs, Real.sqrt_mul (h.left_positive.nonneg F)] at hs
  exact hs

theorem Bracket.folding {c : ReflectionCut V}
    {L K R : ((V → X) → ℝ) →ₗ[ℝ] ℝ} (h : c.Bracket L K R) (a : V → X → ℝ) :
    |multilinearIntegral K a| ^ 2 ≤
      multilinearIntegral L (a ∘ c.foldPlus) * multilinearIntegral R (a ∘ c.foldMinus) := by
  rw [c.multilinear_eq_form, c.folded_plus_eq_form, c.folded_minus_eq_form]
  exact h.cauchy_schwarz_sq _ _

theorem Positive.bracket_self {c : ReflectionCut V}
    {L : ((V → X) → ℝ) →ₗ[ℝ] ℝ} (h : c.Positive L) : c.Bracket L L L := by
  refine ⟨h, h, ?_⟩
  intro F G
  have hh := h.nonneg (F + G)
  rw [c.form_add_left, c.form_add_right, c.form_add_right, h.symmetric G F] at hh
  linarith

/-- The two symmetric cut inequalities imply a bracket; no spectral calculus
is needed for this implication. -/
theorem bracket_of_add_sub_positive {c : ReflectionCut V}
    {L K : ((V → X) → ℝ) →ₗ[ℝ] ℝ}
    (hp : c.Positive (L + K)) (hm : c.Positive (L - K)) : c.Bracket L K L := by
  have hL : c.Positive L := by
    have h := (hp.add hm).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have he : (1 / 2 : ℝ) • ((L + K) + (L - K)) = L := by
      ext f
      change (1 / 2 : ℝ) * ((L f + K f) + (L f - K f)) = L f
      ring
    rwa [he] at h
  have hKsym (F G : (c.Half → X) → ℝ) : c.form K F G = c.form K G F := by
    have hs := hp.symmetric F G
    change c.form L F G + c.form K F G = c.form L G F + c.form K G F at hs
    rw [hL.symmetric F G] at hs
    linarith
  refine ⟨hL, hL, ?_⟩
  intro F G
  have h₁ := hp.nonneg (F + G)
  have h₂ := hm.nonneg (F - G)
  change 0 ≤ c.form L (F + G) (F + G) + c.form K (F + G) (F + G) at h₁
  change 0 ≤ c.form L (F - G) (F - G) - c.form K (F - G) (F - G) at h₂
  simp only [c.form_add_left, c.form_add_right, c.form_sub_left, c.form_sub_right] at h₁ h₂
  rw [hKsym G F] at h₁ h₂
  linarith

theorem prod_folds (c : ReflectionCut V) (b : V → ℝ) :
    (∏ v, b (c.foldPlus v)) * (∏ v, b (c.foldMinus v)) = (∏ v, b v) ^ 2 := by
  rw [c.prod_split (fun v => b (c.foldPlus v)), c.prod_split (fun v => b (c.foldMinus v)),
    c.prod_split b]
  simp only [foldPlus_half, foldPlus_flip_half, foldMinus_half, foldMinus_flip_half]
  ring

/-- A bracket at one cut transfers a common mixed Hölder bound to the
off-diagonal signed law. -/
theorem Bracket.mixed_bound {c : ReflectionCut V}
    {L K R : ((V → X) → ℝ) →ₗ[ℝ] ℝ} (h : c.Bracket L K R)
    (B : (X → ℝ) → ℝ) (hB : ∀ f, 0 ≤ B f)
    (hL : ∀ a : V → X → ℝ, |multilinearIntegral L a| ≤ ∏ v, B (a v))
    (hR : ∀ a : V → X → ℝ, |multilinearIntegral R a| ≤ ∏ v, B (a v))
    (a : V → X → ℝ) : |multilinearIntegral K a| ≤ ∏ v, B (a v) := by
  have h₁ := hL (a ∘ c.foldPlus)
  have h₂ := hR (a ∘ c.foldMinus)
  rw [abs_of_nonneg (h.left_positive.foldPlus_nonneg a)] at h₁
  rw [abs_of_nonneg (h.right_positive.foldMinus_nonneg a)] at h₂
  have hh := (h.folding a).trans (mul_le_mul h₁ h₂
    (h.right_positive.foldMinus_nonneg a) (Finset.prod_nonneg (fun _ _ => hB _)))
  change |multilinearIntegral K a| ^ 2 ≤
    (∏ v, B (a (c.foldPlus v))) * (∏ v, B (a (c.foldMinus v))) at hh
  rw [c.prod_folds (fun v => B (a v))] at hh
  exact (sq_le_sq₀ (abs_nonneg _) (Finset.prod_nonneg (fun _ _ => hB _))).mp hh

end Sarkozy.ReflectionCut
