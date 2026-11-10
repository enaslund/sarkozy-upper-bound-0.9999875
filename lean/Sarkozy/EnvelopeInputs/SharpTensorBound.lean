module

public import Sarkozy.EnvelopeInputs.SharpTensor
public import Sarkozy.TheoremC.Defs
public import Sarkozy.ProbabilityProducts

/-!
# The sharp bound of a product of sharp atoms (`HasSharpBound` tensorizes)

`lem:density:coupled`, "products of sharp atoms ... obey the same proof", for the sharp bound of
`def:price`(b) (`TheoremC.HasSharpBound`). Given sharp decompositions
`ζ_j = w_j ∑_s π_j(s) K_{j,s}`, `κ_j = w_j ∑_s π_j(s) κ_{j,s}` of the atoms, the product has
the decomposition indexed by tuples `s = (s_j)`, with `π = ⊗ π_j` (`FiniteLaw.pi`),
`κ_s = ⊗ κ_{j,s_j}`, `K_s = ⊗ K_{j,s_j}` and the
constant `∏_j d_j`:

* `apply_eq_sum_lawDensity`: a functional is the sum against its point weights;
* `tensorLaw_one`, `halfMarginalPlus_tensorLaw`, `halfMarginalMinus_tensorLaw`: the mass and the
  half marginals of a product law are the products;
* **`hasSharpBound_tensor`**: `HasSharpBound c (⊗κ_j) (⊗ζ_j) (∏_j d_j)`.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.EnvelopeInputs

open Sarkozy.Comparison Sarkozy.ReflectionCut Sarkozy.RecordExpansion Sarkozy.TheoremC

/-- A linear functional on a finite function space is the sum against its point weights. -/
theorem apply_eq_sum_lawDensity {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (f : Ω → ℝ) : L f = ∑ w, lawDensity L w * f w := by
  have hf : f = ∑ w, f w • (fun y => if y = w then (1 : ℝ) else 0) := by
    funext y
    simp [Finset.sum_apply]
  conv_lhs => rw [hf]
  rw [map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]
  rfl

variable {V : Type*} [Fintype V] [DecidableEq V] {J : Type*} [Fintype J] [DecidableEq J]
  {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]

/-- The mass of a product law is the product of the masses. -/
theorem tensorLaw_one (K : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) :
    tensorLaw K (fun _ => 1) = ∏ j, K j (fun _ => 1) := by
  rw [tensorLaw_apply]
  simp only [mul_one]
  rw [← Fintype.prod_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [apply_eq_sum_lawDensity (K j) (fun _ => 1)]
  simp

/-- The plus half marginal of a product law is the product of the plus half marginals. -/
theorem halfMarginalPlus_tensorLaw (c : ReflectionCut V) (K : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (x : c.Half → ∀ j, X j) :
    halfMarginalPlus c (tensorLaw K) x = ∏ j, halfMarginalPlus c (K j) (fun u => x u j) := by
  unfold halfMarginalPlus
  rw [tensorLaw_apply]
  have hind : ∀ z : ∀ j, V → X j,
      (if (fun v : c.Half => (fun v j => z j v) v.1) = x then (1 : ℝ) else 0) =
        ∏ j, (if (fun u : c.Half => z j u.1) = (fun u => x u j) then (1 : ℝ) else 0) := by
    intro z
    by_cases hz : (fun v : c.Half => (fun v j => z j v) v.1) = x
    · simp only [hz, ↓reduceIte]
      refine (Finset.prod_eq_one fun j _ => ?_).symm
      have hj : (fun u : c.Half => z j u.1) = (fun u => x u j) :=
        funext fun u => congrFun (congrFun hz u) j
      simp [hj]
    · simp only [hz, ↓reduceIte]
      have h1 : ∃ j, (fun u : c.Half => z j u.1) ≠ (fun u => x u j) := by
        by_contra hc
        push Not at hc
        exact hz (funext fun u => funext fun j => congrFun (hc j) u)
      obtain ⟨j₀, hj₀⟩ := h1
      exact (Finset.prod_eq_zero (Finset.mem_univ j₀) (by simp [hj₀])).symm
  simp only [hind, ← Finset.prod_mul_distrib]
  have hR : ∀ j, (K j) (fun w => if (fun v : c.Half => w v.1) = (fun u => x u j) then (1 : ℝ)
      else 0) = ∑ w, lawDensity (K j) w *
        (if (fun v : c.Half => w v.1) = (fun u => x u j) then (1 : ℝ) else 0) :=
    fun j => apply_eq_sum_lawDensity (K j) _
  simp only [hR]
  rw [Fintype.prod_sum]

/-- The minus half marginal of a product law is the product of the minus half marginals. -/
theorem halfMarginalMinus_tensorLaw (c : ReflectionCut V) (K : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (x : c.Half → ∀ j, X j) :
    halfMarginalMinus c (tensorLaw K) x = ∏ j, halfMarginalMinus c (K j) (fun u => x u j) := by
  unfold halfMarginalMinus
  rw [tensorLaw_apply]
  have hind : ∀ z : ∀ j, V → X j,
      (if (fun v : c.Half => (fun v j => z j v) (c.flip v.1)) = x then (1 : ℝ) else 0) =
        ∏ j, (if (fun u : c.Half => z j (c.flip u.1)) = (fun u => x u j) then (1 : ℝ) else 0) := by
    intro z
    by_cases hz : (fun v : c.Half => (fun v j => z j v) (c.flip v.1)) = x
    · simp only [hz, ↓reduceIte]
      refine (Finset.prod_eq_one fun j _ => ?_).symm
      have hj : (fun u : c.Half => z j (c.flip u.1)) = (fun u => x u j) :=
        funext fun u => congrFun (congrFun hz u) j
      simp [hj]
    · simp only [hz, ↓reduceIte]
      have h1 : ∃ j, (fun u : c.Half => z j (c.flip u.1)) ≠ (fun u => x u j) := by
        by_contra hc
        push Not at hc
        exact hz (funext fun u => funext fun j => congrFun (hc j) u)
      obtain ⟨j₀, hj₀⟩ := h1
      exact (Finset.prod_eq_zero (Finset.mem_univ j₀) (by simp [hj₀])).symm
  simp only [hind, ← Finset.prod_mul_distrib]
  have hR : ∀ j, (K j) (fun w => if (fun v : c.Half => w (c.flip v.1)) = (fun u => x u j)
      then (1 : ℝ) else 0) = ∑ w, lawDensity (K j) w *
        (if (fun v : c.Half => w (c.flip v.1)) = (fun u => x u j) then (1 : ℝ) else 0) :=
    fun j => apply_eq_sum_lawDensity (K j) _
  simp only [hR]
  rw [Fintype.prod_sum]

section Bound

variable {J' : Type} [Fintype J'] [DecidableEq J'] {Y : J' → Type} [∀ j, Fintype (Y j)]
  [∀ j, DecidableEq (Y j)]

/-- A product of probability measures on the slots is a probability measure. -/
theorem isProbability_tensorLaw (κ : ∀ j, SlotMeasure (Y j)) (h : ∀ j, IsProbability (κ j)) :
    IsProbability (tensorLaw κ : SlotMeasure (∀ j, Y j)) :=
  ⟨tensorLaw_nonneg κ (fun j F hF => (h j).1 F hF), tensorLaw_probability κ (fun j => (h j).2)⟩

/-- **The sharp bound tensorizes** (`def:price`(b) for a product of sharp atoms,
`lem:density:coupled`): if every `ζ_j` has a sharp bound at `c` relative to `κ_j` with constant
`d_j ≥ 0`, then `⊗_j ζ_j` has a sharp bound at `c` relative to `⊗_j κ_j` with constant
`∏_j d_j`. The decomposition is indexed by the tuples of components, with `π = ⊗_j π_j`. -/
theorem hasSharpBound_tensor (c : ReflectionCut Slot) (κ ζ : ∀ j, SlotMeasure (Y j))
    (d : J' → ℝ) (hd : ∀ j, 0 ≤ d j) (h : ∀ j, HasSharpBound c (κ j) (ζ j) (d j)) :
    HasSharpBound c (tensorLaw κ : SlotMeasure (∀ j, Y j)) (tensorLaw ζ) (∏ j, d j) := by
  unfold HasSharpBound at h
  choose S hS π κs Ks hprob hκ hζ hsharp using h
  have hmass : mass (tensorLaw κ : SlotMeasure (∀ j, Y j)) = ∏ j, mass (κ j) := tensorLaw_one κ
  refine ⟨∀ j, S j, inferInstance, FiniteLaw.pi π, fun s => tensorLaw (fun j => κs j (s j)),
    fun s => tensorLaw (fun j => Ks j (s j)),
    fun s => isProbability_tensorLaw _ (fun j => hprob j (s j)), ?_, ?_, ?_⟩
  · have e : (tensorLaw κ : SlotMeasure (∀ j, Y j)) =
        tensorLaw (fun j => mass (κ j) • ∑ t, (π j).weight t • κs j t) := by
      congr 1
      exact funext hκ
    rw [hmass, e, tensorLaw_smul (fun j => mass (κ j)), tensorLaw_sum
      (fun j t => (π j).weight t • κs j t)]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [tensorLaw_smul (fun j => (π j).weight (s j)) (fun j => κs j (s j))]
    rfl
  · have e : (tensorLaw ζ : SlotMeasure (∀ j, Y j)) =
        tensorLaw (fun j => mass (κ j) • ∑ t, (π j).weight t • Ks j t) := by
      congr 1
      exact funext hζ
    rw [e, hmass, tensorLaw_smul (fun j => mass (κ j)), tensorLaw_sum
      (fun j t => (π j).weight t • Ks j t)]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [tensorLaw_smul (fun j => (π j).weight (s j)) (fun j => Ks j (s j))]
    rfl
  · intro s
    have hs := sharp_tensor c (fun j => Ks j (s j)) (fun j => halfMarginalPlus c (κs j (s j)))
      (fun j => halfMarginalMinus c (κs j (s j))) d
      (fun j x => (hprob j (s j)).1 _ (fun _ => by split_ifs <;> norm_num))
      (fun j x => (hprob j (s j)).1 _ (fun _ => by split_ifs <;> norm_num)) hd
      (fun j => hsharp j (s j))
    have hp : halfMarginalPlus c (tensorLaw fun j => κs j (s j) : SlotMeasure (∀ j, Y j)) =
        fun x => ∏ j, halfMarginalPlus c (κs j (s j)) (fun u => x u j) :=
      funext fun x => halfMarginalPlus_tensorLaw c _ x
    have hm : halfMarginalMinus c (tensorLaw fun j => κs j (s j) : SlotMeasure (∀ j, Y j)) =
        fun x => ∏ j, halfMarginalMinus c (κs j (s j)) (fun u => x u j) :=
      funext fun x => halfMarginalMinus_tensorLaw c _ x
    rw [hp, hm]
    exact hs

end Bound

end Sarkozy.EnvelopeInputs
