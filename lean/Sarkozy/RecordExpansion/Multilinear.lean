module

public import Sarkozy.Reflection.Coordinates

/-!
# Multilinearity and reflection of tensor laws

Finite signed measures on a finite configuration space `Ω` are represented,
as everywhere in this project, by linear functionals `(Ω → ℝ) →ₗ[ℝ] ℝ`
(`Sarkozy/Reflection/Basic.lean`). For a finite family of atoms `J` with label
types `X j`, the product measure `⊗_j κ_j` on `(∏_j X j)^V` is
`Sarkozy.tensorLaw` (`Sarkozy/Reflection/Tensor.lean`), whose labels are
`V → ∀ j, X j`. This file supplies the algebra of `tensorLaw` used by the record
expansion of the paper (Section 10, `lem:record:record-expansion`):

* `tensorLaw_sum`: the product of finite sums is the sum, over all choices of
  one summand at every atom, of the products. This is the expansion of
  `⊗_B (λ_B + Σ_t (ζ^s_{B,t} + ζ^a_{B,t}))` in the proof of
  `lem:record:record-expansion` (i).
* `tensorLaw_smul`: scalars factor out of every atom.
* `reflect`: the image `c_* κ` of a measure under the reflection
  `(z_v)_v ↦ (z_{c v})_v` of a cut `c`. `tensorLaw_reflect`: the image of a
  product is the product of the images.
* `diagonalIntegral_reflect`: the diagonal evaluation
  `Y_κ = ∫ ∏_{v ∈ V} F(z_v) dκ` (Section 9, "Energies") is invariant under
  the reflection.
* `IsSymmetricAt`, `IsSkewAt`, `symPart`, `skewPart`: symmetric and skew
  measures and the symmetric and skew parts `½(ζ ± ι_* ζ)` of
  `def:cp:records`; `isSymmetricAt_iff_matrix_transpose` and
  `isSkewAt_iff_matrix_transpose` are `rem:cut-symmetries` (a).
* `diagonalIntegral_eq_zero_of_isSkewAt`, `IsSkewAt.form_self`: the diagonal
  energy and the diagonal cut form of a skew measure vanish.

The reflection of configurations is the pullback `z ↦ z ∘ c.flip`; since it
is an involution this is also the pushforward. The existing lemmas
`ReflectionCut.matrix_reflection` and `ReflectionCut.matrix_injective`
(`Sarkozy/Reflection/Coordinates.lean`) are reused for the cut-matrix
characterizations.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.RecordExpansion

/-! ### Point masses -/

theorem lawDensity_add {Ω : Type*} [DecidableEq Ω] (L M : (Ω → ℝ) →ₗ[ℝ] ℝ) (x : Ω) :
    lawDensity (L + M) x = lawDensity L x + lawDensity M x := rfl

theorem lawDensity_smul {Ω : Type*} [DecidableEq Ω] (a : ℝ) (L : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (x : Ω) : lawDensity (a • L) x = a * lawDensity L x := rfl

theorem lawDensity_sum {Ω ι : Type*} [DecidableEq Ω] (s : Finset ι)
    (L : ι → (Ω → ℝ) →ₗ[ℝ] ℝ) (x : Ω) :
    lawDensity (∑ i ∈ s, L i) x = ∑ i ∈ s, lawDensity (L i) x := by
  unfold lawDensity
  exact LinearMap.sum_apply s L _

/-! ### Multilinearity of the tensor product -/

section Tensor

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]

theorem tensorLaw_apply (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (F : (V → ∀ j, X j) → ℝ) :
    tensorLaw L F =
      ∑ z : ∀ j, V → X j, (∏ j, lawDensity (L j) (z j)) * F (fun v j => z j v) :=
  rfl

/-- **Expansion of a product of sums.** If the law of every atom `j` is a finite
sum `∑_i L j i`, the product law is the sum over all choices `f` of one index
`f j` at every atom of the product laws `⊗_j L j (f j)`. -/
theorem tensorLaw_sum {I : J → Type*} [∀ j, Fintype (I j)]
    (L : ∀ j, I j → ((V → X j) → ℝ) →ₗ[ℝ] ℝ) :
    tensorLaw (fun j => ∑ i, L j i) = ∑ f : (∀ j, I j), tensorLaw (fun j => L j (f j)) := by
  apply LinearMap.ext
  intro F
  rw [LinearMap.sum_apply]
  simp only [tensorLaw_apply, lawDensity_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [← Finset.sum_mul, Fintype.prod_sum]

/-- Scalars factor out of a tensor product, one from every atom. -/
theorem tensorLaw_smul (a : J → ℝ) (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) :
    tensorLaw (fun j => a j • L j) = (∏ j, a j) • tensorLaw L := by
  apply LinearMap.ext
  intro F
  rw [LinearMap.smul_apply, smul_eq_mul]
  simp only [tensorLaw_apply, lawDensity_smul, Finset.prod_mul_distrib, Finset.mul_sum,
    mul_assoc]

/-- A product law is linear in each single factor. -/
theorem tensorLaw_update_add (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (j₀ : J)
    (M N : ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ) :
    tensorLaw (Function.update L j₀ (M + N)) =
      tensorLaw (Function.update L j₀ M) + tensorLaw (Function.update L j₀ N) := by
  apply LinearMap.ext
  intro F
  rw [LinearMap.add_apply]
  simp only [tensorLaw_apply, ← Finset.sum_add_distrib, ← add_mul]
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  rw [← Finset.mul_prod_erase univ _ (mem_univ j₀), ← Finset.mul_prod_erase univ _ (mem_univ j₀),
    ← Finset.mul_prod_erase univ _ (mem_univ j₀)]
  have hrest : ∀ M' : ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ,
      ∏ j ∈ univ.erase j₀, lawDensity (Function.update L j₀ M' j) (z j) =
        ∏ j ∈ univ.erase j₀, lawDensity (L j) (z j) := by
    intro M'
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hrest, hrest, hrest]
  simp only [Function.update_self, lawDensity_add]
  ring

end Tensor

/-! ### Reflection of measures -/

section Reflection

variable {W Y : Type*} [Fintype W] [DecidableEq W]

/-- The image `c_* κ` of a finite signed measure `κ` on `W → Y` under the
reflection `(z_v)_v ↦ (z_{c v})_v` of the cut `c`. -/
noncomputable def reflect (c : ReflectionCut W) (L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) :
    ((W → Y) → ℝ) →ₗ[ℝ] ℝ :=
  pushFunctional L (fun z : W → Y => z ∘ c.flip)

theorem reflect_apply (c : ReflectionCut W) (L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) (f : (W → Y) → ℝ) :
    reflect c L f = L (fun z => f (z ∘ c.flip)) := rfl

theorem comp_flip_flip (c : ReflectionCut W) (z : W → Y) : (z ∘ c.flip) ∘ c.flip = z := by
  funext v
  exact congrArg z (c.flip_flip v)

theorem reflect_reflect (c : ReflectionCut W) (L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) :
    reflect c (reflect c L) = L := by
  apply LinearMap.ext
  intro f
  simp only [reflect_apply, comp_flip_flip]

theorem reflect_add (c : ReflectionCut W) (L M : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) :
    reflect c (L + M) = reflect c L + reflect c M :=
  LinearMap.ext fun _ => rfl

theorem reflect_sub (c : ReflectionCut W) (L M : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) :
    reflect c (L - M) = reflect c L - reflect c M :=
  LinearMap.ext fun _ => rfl

theorem reflect_neg (c : ReflectionCut W) (L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) :
    reflect c (-L) = -reflect c L :=
  LinearMap.ext fun _ => rfl

theorem reflect_smul (c : ReflectionCut W) (a : ℝ) (L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) :
    reflect c (a • L) = a • reflect c L :=
  LinearMap.ext fun _ => rfl

theorem reflect_sum {ι : Type*} (c : ReflectionCut W) (s : Finset ι)
    (L : ι → ((W → Y) → ℝ) →ₗ[ℝ] ℝ) :
    reflect c (∑ i ∈ s, L i) = ∑ i ∈ s, reflect c (L i) := by
  apply LinearMap.ext
  intro f
  rw [reflect_apply, LinearMap.sum_apply, LinearMap.sum_apply]
  rfl

theorem lawDensity_reflect [DecidableEq Y] (c : ReflectionCut W)
    (L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) (x : W → Y) :
    lawDensity (reflect c L) x = lawDensity L (x ∘ c.flip) := by
  unfold lawDensity
  rw [reflect_apply]
  congr 1
  funext z
  have hiff : z ∘ c.flip = x ↔ z = x ∘ c.flip := by
    constructor
    · rintro rfl
      exact (comp_flip_flip c z).symm
    · rintro rfl
      exact comp_flip_flip c x
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact absurd (hiff.mp h₁) h₂
  · exact absurd (hiff.mpr h₂) h₁
  · rfl

/-- **The diagonal evaluation is reflection invariant.** Every slot carries the
same input, so `∫ ∏_v f(z_v) d(c_* κ) = ∫ ∏_v f(z_v) dκ`. -/
theorem diagonalIntegral_reflect (c : ReflectionCut W) (L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ)
    (f : Y → ℝ) : diagonalIntegral (reflect c L) f = diagonalIntegral L f := by
  unfold diagonalIntegral multilinearIntegral
  rw [reflect_apply]
  congr 1
  funext z
  exact Equiv.prod_comp c.flip (fun v => f (z v))

/-- The cut form of the reflected measure is the transposed cut form. -/
theorem form_reflect (c : ReflectionCut W) (L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ)
    (F G : (c.Half → Y) → ℝ) : c.form (reflect c L) F G = c.form L G F := by
  unfold ReflectionCut.form
  rw [reflect_apply]
  congr 1
  funext z
  simp only [Function.comp_apply, c.flip_flip]
  ring

/-! ### Symmetric and skew measures (`def:cp:records`) -/

/-- `κ` is symmetric at the cut `c`: `c_* κ = κ`. -/
def IsSymmetricAt (c : ReflectionCut W) (L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) : Prop :=
  reflect c L = L

/-- `κ` is skew at the cut `c`: `c_* κ = -κ`. -/
def IsSkewAt (c : ReflectionCut W) (L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) : Prop :=
  reflect c L = -L

/-- The symmetric part `½(ζ + c_* ζ)` of `ζ` at `c` (`def:cp:records`). -/
noncomputable def symPart (c : ReflectionCut W) (L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) :
    ((W → Y) → ℝ) →ₗ[ℝ] ℝ :=
  (1 / 2 : ℝ) • (L + reflect c L)

/-- The skew part `½(ζ - c_* ζ)` of `ζ` at `c` (`def:cp:records`). -/
noncomputable def skewPart (c : ReflectionCut W) (L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) :
    ((W → Y) → ℝ) →ₗ[ℝ] ℝ :=
  (1 / 2 : ℝ) • (L - reflect c L)

theorem symPart_add_skewPart (c : ReflectionCut W) (L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) :
    symPart c L + skewPart c L = L := by
  apply LinearMap.ext
  intro f
  simp only [symPart, skewPart, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, smul_eq_mul]
  ring

theorem isSymmetricAt_symPart (c : ReflectionCut W) (L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) :
    IsSymmetricAt c (symPart c L) := by
  unfold IsSymmetricAt symPart
  rw [reflect_smul, reflect_add, reflect_reflect, add_comm]

theorem isSkewAt_skewPart (c : ReflectionCut W) (L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) :
    IsSkewAt c (skewPart c L) := by
  unfold IsSkewAt skewPart
  rw [reflect_smul, reflect_sub, reflect_reflect]
  apply LinearMap.ext
  intro f
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.neg_apply, smul_eq_mul]
  ring

theorem IsSymmetricAt.add {c : ReflectionCut W} {L M : ((W → Y) → ℝ) →ₗ[ℝ] ℝ}
    (hL : IsSymmetricAt c L) (hM : IsSymmetricAt c M) : IsSymmetricAt c (L + M) := by
  unfold IsSymmetricAt at *
  rw [reflect_add, hL, hM]

theorem IsSkewAt.add {c : ReflectionCut W} {L M : ((W → Y) → ℝ) →ₗ[ℝ] ℝ}
    (hL : IsSkewAt c L) (hM : IsSkewAt c M) : IsSkewAt c (L + M) := by
  unfold IsSkewAt at *
  rw [reflect_add, hL, hM, neg_add]

theorem IsSymmetricAt.smul {c : ReflectionCut W} {L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ}
    (hL : IsSymmetricAt c L) (a : ℝ) : IsSymmetricAt c (a • L) := by
  unfold IsSymmetricAt at *
  rw [reflect_smul, hL]

theorem IsSkewAt.smul {c : ReflectionCut W} {L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ}
    (hL : IsSkewAt c L) (a : ℝ) : IsSkewAt c (a • L) := by
  unfold IsSkewAt at *
  rw [reflect_smul, hL, smul_neg]

/-- The cut form of a symmetric measure is symmetric. -/
theorem IsSymmetricAt.form_comm {c : ReflectionCut W} {L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ}
    (h : IsSymmetricAt c L) (F G : (c.Half → Y) → ℝ) : c.form L F G = c.form L G F := by
  rw [← form_reflect c L F G, h]

/-- The cut form of a skew measure is antisymmetric. -/
theorem IsSkewAt.form_anticomm {c : ReflectionCut W} {L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ}
    (h : IsSkewAt c L) (F G : (c.Half → Y) → ℝ) : c.form L F G = -c.form L G F := by
  have h' := form_reflect c L G F
  rw [h] at h'
  change -c.form L G F = c.form L F G at h'
  linarith

/-- The diagonal cut form of a skew measure vanishes (`rem:cut-symmetries` (a)). -/
theorem IsSkewAt.form_self {c : ReflectionCut W} {L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ}
    (h : IsSkewAt c L) (F : (c.Half → Y) → ℝ) : c.form L F F = 0 := by
  have h' := h.form_anticomm F F
  linarith

/-- **The diagonal energy of a skew measure vanishes.** -/
theorem diagonalIntegral_eq_zero_of_isSkewAt {c : ReflectionCut W}
    {L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ} (h : IsSkewAt c L) (f : Y → ℝ) :
    diagonalIntegral L f = 0 := by
  have h1 := diagonalIntegral_reflect c L f
  rw [h] at h1
  change -diagonalIntegral L f = diagonalIntegral L f at h1
  linarith

/-! ### Cut matrices of symmetric and skew measures (`rem:cut-symmetries` (a)) -/

section Matrix

variable [DecidableEq Y]

theorem matrix_add (c : ReflectionCut W) (L M : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) :
    c.matrix (L + M) = c.matrix L + c.matrix M := by
  ext x y
  rfl

theorem matrix_neg (c : ReflectionCut W) (L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) :
    c.matrix (-L) = -c.matrix L := by
  ext x y
  rfl

theorem matrix_smul (c : ReflectionCut W) (a : ℝ) (L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) :
    c.matrix (a • L) = a • c.matrix L := by
  ext x y
  rfl

/-- A measure is symmetric at `c` iff its cut matrix at `c` is symmetric. -/
theorem isSymmetricAt_iff_matrix_transpose [Fintype Y] (c : ReflectionCut W)
    (L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) :
    IsSymmetricAt c L ↔ (c.matrix L).transpose = c.matrix L := by
  unfold IsSymmetricAt reflect
  rw [← c.matrix_reflection]
  exact c.matrix_injective.eq_iff.symm

/-- A measure is skew at `c` iff its cut matrix at `c` is antisymmetric. -/
theorem isSkewAt_iff_matrix_transpose [Fintype Y] (c : ReflectionCut W)
    (L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) :
    IsSkewAt c L ↔ (c.matrix L).transpose = -c.matrix L := by
  unfold IsSkewAt reflect
  rw [← c.matrix_reflection, ← matrix_neg]
  exact c.matrix_injective.eq_iff.symm

/-- The cut matrix of the symmetric part is the symmetric part of the cut matrix. -/
theorem matrix_symPart [Fintype Y] (c : ReflectionCut W) (L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) :
    c.matrix (symPart c L) = (1 / 2 : ℝ) • (c.matrix L + (c.matrix L).transpose) := by
  unfold symPart reflect
  rw [matrix_smul, matrix_add, c.matrix_reflection]

/-- The cut matrix of the skew part is the antisymmetric part of the cut matrix. -/
theorem matrix_skewPart [Fintype Y] (c : ReflectionCut W) (L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) :
    c.matrix (skewPart c L) = (1 / 2 : ℝ) • (c.matrix L - (c.matrix L).transpose) := by
  unfold skewPart reflect
  rw [matrix_smul, sub_eq_add_neg, matrix_add, matrix_neg, c.matrix_reflection,
    ← sub_eq_add_neg]

end Matrix

end Reflection

/-! ### Reflection of product laws -/

section TensorReflection

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]

/-- Reflect the configuration of every atom. -/
def flipEquiv (c : ReflectionCut V) : (∀ j, V → X j) ≃ (∀ j, V → X j) where
  toFun z j := z j ∘ c.flip
  invFun z j := z j ∘ c.flip
  left_inv z := by
    funext j
    exact comp_flip_flip c (z j)
  right_inv z := by
    funext j
    exact comp_flip_flip c (z j)

/-- **The reflection of a product is the product of the reflections.** -/
theorem tensorLaw_reflect (c : ReflectionCut V) (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) :
    reflect c (tensorLaw L) = tensorLaw (fun j => reflect c (L j)) := by
  apply LinearMap.ext
  intro F
  rw [reflect_apply, tensorLaw_apply, tensorLaw_apply]
  simp only [lawDensity_reflect]
  apply Fintype.sum_equiv (flipEquiv c)
  intro z
  change (∏ j, lawDensity (L j) (z j)) * F (fun v j => z j (c.flip v)) =
    (∏ j, lawDensity (L j) ((z j ∘ c.flip) ∘ c.flip)) * F (fun v j => z j (c.flip v))
  simp only [comp_flip_flip]

/-- If every factor is an eigenmeasure of the reflection, `c_* κ_j = σ_j κ_j`,
the product is an eigenmeasure with eigenvalue `∏_j σ_j`. -/
theorem tensorLaw_reflect_of_eigen (c : ReflectionCut V) (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (σ : J → ℝ) (h : ∀ j, reflect c (L j) = σ j • L j) :
    reflect c (tensorLaw L) = (∏ j, σ j) • tensorLaw L := by
  rw [tensorLaw_reflect, show (fun j => reflect c (L j)) = fun j => σ j • L j from funext h]
  exact tensorLaw_smul σ L

/-- Products of measures symmetric at `c` are symmetric at `c`. -/
theorem isSymmetricAt_tensorLaw (c : ReflectionCut V) (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (h : ∀ j, IsSymmetricAt c (L j)) : IsSymmetricAt c (tensorLaw L) := by
  unfold IsSymmetricAt
  rw [tensorLaw_reflect]
  exact congrArg tensorLaw (funext h)

/-- **Odd products of skew factors.** If every factor is symmetric or skew at
`c` and the product of the signs is `-1`, the product law is skew at `c` and its
diagonal energy vanishes. -/
theorem diagonalIntegral_tensorLaw_eq_zero (c : ReflectionCut V)
    (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (σ : J → ℝ) (h : ∀ j, reflect c (L j) = σ j • L j)
    (hσ : ∏ j, σ j = -1) (f : (∀ j, X j) → ℝ) : diagonalIntegral (tensorLaw L) f = 0 := by
  apply diagonalIntegral_eq_zero_of_isSkewAt (c := c)
  unfold IsSkewAt
  rw [tensorLaw_reflect_of_eigen c L σ h, hσ]
  apply LinearMap.ext
  intro F
  simp only [LinearMap.smul_apply, LinearMap.neg_apply, smul_eq_mul, neg_one_mul]

end TensorReflection

end Sarkozy.RecordExpansion
