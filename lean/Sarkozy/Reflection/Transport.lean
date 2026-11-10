module

public import Sarkozy.Reflection.Coordinates
public import Sarkozy.ProbabilityConstructions

/-!
# Applying the same Markov kernel to both halves

A kernel is an explicit finite probability law for each input half-labeling.
Applying it independently to the two halves transports cut forms by the same
linear map on both arguments. Positivity, cut order, and brackets therefore
survive. Jensen's inequality also bounds the transported diagonal law by the
diagonal law of the transported marginal.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.ReflectionCut

variable {V W X Y : Type*} [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W] [Fintype Y] [DecidableEq Y]

noncomputable def kernelLaw (c : ReflectionCut V) (d : ReflectionCut W)
    (P : (c.Half → X) → FiniteLaw (d.Half → Y)) (z : V → X) : FiniteLaw (W → Y) :=
  ((P (fun v => z v.1)).product (P (fun v => z (c.flip v.1)))).map
    (fun p => d.join p.1 p.2)

noncomputable def transport (c : ReflectionCut V) (d : ReflectionCut W)
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (P : (c.Half → X) → FiniteLaw (d.Half → Y)) :
    ((W → Y) → ℝ) →ₗ[ℝ] ℝ where
  toFun f := L (fun z => (c.kernelLaw d P z).expect f)
  map_add' f g := by
    change L (fun z => (c.kernelLaw d P z).expect (fun w => f w + g w)) = _
    simp only [FiniteLaw.expect_add]
    exact L.map_add _ _
  map_smul' a f := by
    change L (fun z => (c.kernelLaw d P z).expect (fun w => a * f w)) =
      a * L (fun z => (c.kernelLaw d P z).expect f)
    simp only [FiniteLaw.expect_const_mul]
    exact L.map_smul a _

theorem form_transport (c : ReflectionCut V) (d : ReflectionCut W)
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (P : (c.Half → X) → FiniteLaw (d.Half → Y))
    (F G : (d.Half → Y) → ℝ) :
    d.form (c.transport d L P) F G =
      c.form L (fun x => (P x).expect F) (fun x => (P x).expect G) := by
  apply congrArg L
  funext z
  rw [kernelLaw, FiniteLaw.expect_map]
  change ((P (fun v => z v.1)).product (P (fun v => z (c.flip v.1)))).expect
    (fun p => F (fun v => d.join p.1 p.2 v.1) * G (fun v => d.join p.1 p.2 (d.flip v.1))) = _
  simp only [join_plus, join_minus]
  exact FiniteLaw.expect_product_mul _ _ F G

theorem transport_const (c : ReflectionCut V) (d : ReflectionCut W)
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (P : (c.Half → X) → FiniteLaw (d.Half → Y)) (a : ℝ) :
    c.transport d L P (fun _ => a) = L (fun _ => a) := by
  change L (fun z => (c.kernelLaw d P z).expect (fun _ => a)) = _
  simp only [FiniteLaw.expect_const]

theorem transport_nonneg (c : ReflectionCut V) (d : ReflectionCut W)
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (P : (c.Half → X) → FiniteLaw (d.Half → Y))
    (hL : ∀ f, (∀ z, 0 ≤ f z) → 0 ≤ L f) {f : (W → Y) → ℝ} (hf : ∀ z, 0 ≤ f z) :
    0 ≤ c.transport d L P f := hL _ (fun z => (c.kernelLaw d P z).expect_nonneg hf)

theorem Positive.transport {c : ReflectionCut V} (d : ReflectionCut W)
    {L : ((V → X) → ℝ) →ₗ[ℝ] ℝ} (h : c.Positive L)
    (P : (c.Half → X) → FiniteLaw (d.Half → Y)) : d.Positive (c.transport d L P) := by
  constructor
  · intro F G
    rw [c.form_transport, c.form_transport]
    exact h.symmetric _ _
  · intro F
    rw [c.form_transport]
    exact h.nonneg _

theorem Below.transport {c : ReflectionCut V} (d : ReflectionCut W)
    {L M : ((V → X) → ℝ) →ₗ[ℝ] ℝ} (h : c.Below L M)
    (P : (c.Half → X) → FiniteLaw (d.Half → Y)) :
    d.Below (c.transport d L P) (c.transport d M P) := Positive.transport d h P

theorem Bracket.transport {c : ReflectionCut V} (d : ReflectionCut W)
    {L K R : ((V → X) → ℝ) →ₗ[ℝ] ℝ} (h : c.Bracket L K R)
    (P : (c.Half → X) → FiniteLaw (d.Half → Y)) :
    d.Bracket (c.transport d L P) (c.transport d K P) (c.transport d R P) := by
  refine ⟨h.left_positive.transport d P, h.right_positive.transport d P, ?_⟩
  intro F G
  simp only [c.form_transport]
  exact h.nonneg _ _

section Diagonal

variable [Fintype X]

noncomputable def diagonalLaw (c : ReflectionCut V) (m : (c.Half → X) → ℝ) :
    ((V → X) → ℝ) →ₗ[ℝ] ℝ := sampleIntegral m (fun x => c.join x x)

theorem form_diagonalLaw (c : ReflectionCut V) (m : (c.Half → X) → ℝ)
    (F G : (c.Half → X) → ℝ) :
    c.form (c.diagonalLaw m) F G = ∑ x, m x * (F x * G x) := by
  change (∑ x, m x * (F (fun v => c.join x x v.1) *
    G (fun v => c.join x x (c.flip v.1)))) = _
  simp only [join_plus, join_minus]

theorem diagonalLaw_positive (c : ReflectionCut V) {m : (c.Half → X) → ℝ}
    (hm : ∀ x, 0 ≤ m x) : c.Positive (c.diagonalLaw m) := by
  constructor
  · intro F G
    simp only [c.form_diagonalLaw]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  · intro F
    rw [c.form_diagonalLaw]
    exact Finset.sum_nonneg (fun x _ => mul_nonneg (hm x) (mul_self_nonneg _))

noncomputable def kernelMarginal (c : ReflectionCut V) (d : ReflectionCut W)
    (m : (c.Half → X) → ℝ) (P : (c.Half → X) → FiniteLaw (d.Half → Y))
    (y : d.Half → Y) : ℝ := ∑ x, m x * (P x).weight y

omit [DecidableEq Y] in
theorem kernelMarginal_nonneg (c : ReflectionCut V) (d : ReflectionCut W)
    {m : (c.Half → X) → ℝ} (hm : ∀ x, 0 ≤ m x)
    (P : (c.Half → X) → FiniteLaw (d.Half → Y)) (y : d.Half → Y) :
    0 ≤ c.kernelMarginal d m P y :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (hm x) ((P x).nonneg y))

omit [DecidableEq Y] in
theorem form_diagonal_kernelMarginal (c : ReflectionCut V) (d : ReflectionCut W)
    (m : (c.Half → X) → ℝ) (P : (c.Half → X) → FiniteLaw (d.Half → Y))
    (F G : (d.Half → Y) → ℝ) :
    d.form (d.diagonalLaw (c.kernelMarginal d m P)) F G =
      ∑ x, m x * (P x).expect (fun y => F y * G y) := by
  rw [d.form_diagonalLaw]
  simp only [kernelMarginal, Finset.sum_mul, FiniteLaw.expect, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- Jensen's inequality places the transported diagonal below the diagonal
of the transported marginal in cut order. -/
theorem transported_diagonal_below (c : ReflectionCut V) (d : ReflectionCut W)
    {m : (c.Half → X) → ℝ} (hm : ∀ x, 0 ≤ m x)
    (P : (c.Half → X) → FiniteLaw (d.Half → Y)) :
    d.Below (c.transport d (c.diagonalLaw m) P)
      (d.diagonalLaw (c.kernelMarginal d m P)) := by
  have hleft := (c.diagonalLaw_positive hm).transport d P
  have hright := d.diagonalLaw_positive (c.kernelMarginal_nonneg d hm P)
  constructor
  · intro F G
    change d.form _ F G - d.form _ F G = d.form _ G F - d.form _ G F
    rw [hleft.symmetric, hright.symmetric]
  · intro F
    change 0 ≤ d.form (d.diagonalLaw (c.kernelMarginal d m P)) F F -
      d.form (c.transport d (c.diagonalLaw m) P) F F
    rw [c.form_diagonal_kernelMarginal, c.form_transport, c.form_diagonalLaw,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_nonneg
    intro x _
    have hh := (P x).mean_sq_le_second_moment F
    have h := mul_nonneg (hm x) (sub_nonneg.mpr hh)
    simpa only [pow_two, mul_sub] using h

/-- A diagonal correction remains sufficient after applying the same kernel
on both halves; its coefficient need not increase. -/
theorem transport_diagonal_correction (c : ReflectionCut V) (d : ReflectionCut W)
    {L : ((V → X) → ℝ) →ₗ[ℝ] ℝ} {m : (c.Half → X) → ℝ}
    (hm : ∀ x, 0 ≤ m x) {k : ℝ} (hk : 0 ≤ k)
    (h : c.Positive (L + k • c.diagonalLaw m))
    (P : (c.Half → X) → FiniteLaw (d.Half → Y)) :
    d.Positive (c.transport d L P + k • d.diagonalLaw (c.kernelMarginal d m P)) := by
  have hp := h.transport d P
  have hc := (c.transported_diagonal_below d hm P).smul hk
  have hall := hp.add hc
  convert hall using 1
  apply LinearMap.ext
  intro f
  change c.transport d L P f + k * d.diagonalLaw (c.kernelMarginal d m P) f =
    (c.transport d L P f + k * c.transport d (c.diagonalLaw m) P f) +
      k * (d.diagonalLaw (c.kernelMarginal d m P) f - c.transport d (c.diagonalLaw m) P f)
  ring

end Diagonal
end Sarkozy.ReflectionCut
