module

public import Sarkozy.Reflection.Tensor

/-!
# Common-cut order and latent restrictions

A nonnegative measure supported on configurations fixed by a cut is positive
at that cut. Consequently, pointwise domination of such measures gives an
inequality of diagonal energies, even for signed input functions. This is the
common-cut union-bound mechanism of Section 5, before adjoining tensor factors.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy

/-- Push a finite signed weight forward by a deterministic sample map. -/
noncomputable def sampleIntegral {Ω Ξ : Type*} [Fintype Ω] (w : Ω → ℝ) (Z : Ω → Ξ) :
    (Ξ → ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∑ ω, w ω * f (Z ω)
  map_add' f g := by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a f := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
    mul_left_comm, Finset.mul_sum]

theorem sampleIntegral_sub {Ω Ξ : Type*} [Fintype Ω] (w w' : Ω → ℝ) (Z : Ω → Ξ) :
    sampleIntegral (fun ω => w ω - w' ω) Z = sampleIntegral w Z - sampleIntegral w' Z := by
  ext f
  simp only [sampleIntegral, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem sampleIntegral_sum {Ω Ξ I : Type*} [Fintype Ω] (s : Finset I)
    (w : I → Ω → ℝ) (Z : Ω → Ξ) :
    sampleIntegral (fun ω => ∑ i ∈ s, w i ω) Z = ∑ i ∈ s, sampleIntegral (w i) Z := by
  ext f
  simp only [sampleIntegral, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

namespace ReflectionCut

variable {V X : Type*} [Fintype V] [DecidableEq V]

/-- Loewner order at a specified cut, expressed through its quadratic form. -/
def Below (c : ReflectionCut V) (L M : ((V → X) → ℝ) →ₗ[ℝ] ℝ) : Prop :=
  c.Positive (M - L)

theorem Positive.add {c : ReflectionCut V} {L M : ((V → X) → ℝ) →ₗ[ℝ] ℝ}
    (hL : c.Positive L) (hM : c.Positive M) : c.Positive (L + M) := by
  constructor
  · intro F G
    change c.form L F G + c.form M F G = c.form L G F + c.form M G F
    rw [hL.symmetric, hM.symmetric]
  · intro F
    exact add_nonneg (hL.nonneg F) (hM.nonneg F)

theorem Positive.smul {c : ReflectionCut V} {L : ((V → X) → ℝ) →ₗ[ℝ] ℝ}
    (hL : c.Positive L) {a : ℝ} (ha : 0 ≤ a) : c.Positive (a • L) := by
  constructor
  · intro F G
    change a * c.form L F G = a * c.form L G F
    rw [hL.symmetric]
  · intro F
    exact mul_nonneg ha (hL.nonneg F)

theorem Positive.sum {I : Type*} (s : Finset I) {c : ReflectionCut V}
    {L : I → ((V → X) → ℝ) →ₗ[ℝ] ℝ} (h : ∀ i ∈ s, c.Positive (L i)) :
    c.Positive (∑ i ∈ s, L i) := by
  constructor
  · intro F G
    simp only [form, LinearMap.sum_apply]
    exact Finset.sum_congr rfl (fun i hi => (h i hi).symmetric F G)
  · intro F
    simp only [form, LinearMap.sum_apply]
    exact Finset.sum_nonneg (fun i hi => (h i hi).nonneg F)

theorem Below.form_le {c : ReflectionCut V} {L M : ((V → X) → ℝ) →ₗ[ℝ] ℝ}
    (h : c.Below L M) (F : (c.Half → X) → ℝ) : c.form L F F ≤ c.form M F F := by
  exact sub_nonneg.mp (h.nonneg F)

theorem Below.diagonal_le {c : ReflectionCut V} {L M : ((V → X) → ℝ) →ₗ[ℝ] ℝ}
    (h : c.Below L M) (f : X → ℝ) : diagonalIntegral L f ≤ diagonalIntegral M f := by
  exact sub_nonneg.mp (h.diagonal_nonneg f)

theorem Below.trans {c : ReflectionCut V} {L M N : ((V → X) → ℝ) →ₗ[ℝ] ℝ}
    (hLM : c.Below L M) (hMN : c.Below M N) : c.Below L N := by
  have h := hMN.add hLM
  change c.Positive (N - L)
  simpa only [sub_add_sub_cancel] using h

/-- A latent representation is fixed samplewise wherever its weight is nonzero. -/
def SamplewiseFixed {Ω : Type*} (c : ReflectionCut V) (w : Ω → ℝ) (Z : Ω → V → X) : Prop :=
  ∀ ω, w ω ≠ 0 → ∀ v, Z ω (c.flip v) = Z ω v

theorem form_of_samplewiseFixed {Ω : Type*} [Fintype Ω] (c : ReflectionCut V)
    {w : Ω → ℝ} {Z : Ω → V → X} (hfix : c.SamplewiseFixed w Z)
    (F G : (c.Half → X) → ℝ) :
    c.form (sampleIntegral w Z) F G =
      ∑ ω, w ω * (F (fun v => Z ω v.1) * G (fun v => Z ω v.1)) := by
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hw : w ω = 0
  · simp only [hw, zero_mul]
  · have he : (fun v : c.Half => Z ω (c.flip v.1)) = (fun v : c.Half => Z ω v.1) :=
      funext (fun v => hfix ω hw v.1)
    change w ω * (F (fun v => Z ω v.1) * G (fun v => Z ω (c.flip v.1))) = _
    rw [he]

/-- Restriction to a latent event preserves positivity at a samplewise fixed cut. -/
theorem positive_of_samplewiseFixed {Ω : Type*} [Fintype Ω] (c : ReflectionCut V)
    {w : Ω → ℝ} {Z : Ω → V → X} (hw : ∀ ω, 0 ≤ w ω)
    (hfix : c.SamplewiseFixed w Z) : c.Positive (sampleIntegral w Z) := by
  constructor
  · intro F G
    rw [c.form_of_samplewiseFixed hfix, c.form_of_samplewiseFixed hfix]
    apply Finset.sum_congr rfl
    intro ω _
    ring
  · intro F
    rw [c.form_of_samplewiseFixed hfix]
    exact Finset.sum_nonneg (fun ω _ => mul_nonneg (hw ω) (mul_self_nonneg _))

theorem SamplewiseFixed.reweight {Ω : Type*} {c : ReflectionCut V}
    {w : Ω → ℝ} {Z : Ω → V → X} (hfix : c.SamplewiseFixed w Z) (a : Ω → ℝ) :
    c.SamplewiseFixed (fun ω => w ω * a ω) Z := by
  intro ω hw v
  exact hfix ω (left_ne_zero_of_mul hw) v

/-- Pointwise order of weights becomes cut order, provided the relevant samples
are fixed by this particular reflection. -/
theorem below_of_weights_le {Ω : Type*} [Fintype Ω] (c : ReflectionCut V)
    {w w' : Ω → ℝ} {Z : Ω → V → X} (hle : ∀ ω, w ω ≤ w' ω)
    (hfix : c.SamplewiseFixed w Z) (hfix' : c.SamplewiseFixed w' Z) :
    c.Below (sampleIntegral w Z) (sampleIntegral w' Z) := by
  have hdiff : c.SamplewiseFixed (fun ω => w' ω - w ω) Z := by
    intro ω hω v
    by_cases hw : w ω = 0
    · exact hfix' ω (by simpa only [hw, sub_zero] using hω) v
    · exact hfix ω hw v
  have hp := c.positive_of_samplewiseFixed (fun ω => sub_nonneg.mpr (hle ω)) hdiff
  rwa [sampleIntegral_sub] at hp

/-- An event cover gives a union bound for diagonal energies of signed input
functions, because the underlying samples are fixed at the common cut. -/
theorem diagonal_union_bound {Ω I : Type*} [Fintype Ω] (c : ReflectionCut V)
    (s : Finset I) {w : Ω → ℝ} {ws : I → Ω → ℝ} {Z : Ω → V → X}
    (hcover : ∀ ω, w ω ≤ ∑ i ∈ s, ws i ω)
    (hfix : c.SamplewiseFixed w Z)
    (hfixs : ∀ i ∈ s, c.SamplewiseFixed (ws i) Z) (f : X → ℝ) :
    diagonalIntegral (sampleIntegral w Z) f ≤
      ∑ i ∈ s, diagonalIntegral (sampleIntegral (ws i) Z) f := by
  have hsum : c.SamplewiseFixed (fun ω => ∑ i ∈ s, ws i ω) Z := by
    intro ω hω v
    obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hω
    exact hfixs i hi ω hne v
  have h := (c.below_of_weights_le hcover hfix hsum).diagonal_le f
  rw [sampleIntegral_sum] at h
  simpa only [diagonalIntegral, multilinearIntegral, LinearMap.sum_apply] using h

end ReflectionCut
end Sarkozy
