module

public import Sarkozy.TheoremC.Main

/-!
# (R2) and (R3) per prefix coordinate for a product prefix law (gap 4)

`paper/sections/09_comparison_theorem.tex`, (CP1) and `hyp:record:reference` (R2), (R3). WP-FI's
`TheoremC.Reference` states (R2) and (R3) for the prefix law `μ₀` on the whole prefix
`ResidueSpace m₀ = ∏_i ℤ/m₀_iℤ`: reflection positivity at every cut of the family (`rp₀`), and
invariance under the coordinatewise square-affine maps `piAffineEquiv` (`inv₀`). WP-R's
density-dc theorems take them per prefix coordinate, for a product prefix law `μ₀ = ⊗_i μ0_i`
(`_hp0`, `_hR30`). This was gap 4 of WP-R's list. Here the per-coordinate statements are derived
by taking coordinate marginals:

* `expect_tensor_eq_pi`, `expect_pi_coordinate'`, `expect_tensor_coordinate`: the coordinate
  marginal of `FiniteLaw.tensor μ` is `μ i`;
* `prefix_R3_coordinate`: `(μ0 i).expect (F ∘ (r · + t)) = (μ0 i).expect F` for square units `r`
  (`_hR30`), from `inv₀`;
* `prefix_R2_coordinate`: `SlotReflectionPositive (signedIntegral (μ0 i).weight)` (`_hp0`), from
  `rp₀`.
-/

@[expose] public section

open Finset Function
open scoped BigOperators

namespace Sarkozy.EnvelopeInputs

open Sarkozy.TheoremC Sarkozy.PaperFrame Sarkozy.RecordExpansion Sarkozy.FourierArithmetic

section Marginals

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]

/-- The tensor law as the independent product over the coordinates. -/
theorem expect_tensor_eq_pi (μ : ∀ j, FiniteLaw (V → X j)) (F : (V → ∀ j, X j) → ℝ) :
    (FiniteLaw.tensor μ).expect F =
      (FiniteLaw.pi μ).expect (fun z => F (fun v j => z j v)) := by
  rw [FiniteLaw.expect_eq_signedIntegral, FiniteLaw.signedIntegral_tensor]
  unfold tensorLaw
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  refine Finset.sum_congr rfl fun z _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  simp [lawDensity, signedIntegral]

omit [Fintype V] [DecidableEq V] [∀ j, DecidableEq (X j)] in
/-- The coordinate marginal of an independent product, for dependent coordinate types. -/
theorem expect_pi_coordinate' {Ω : J → Type*} [∀ j, Fintype (Ω j)] (μ : ∀ j, FiniteLaw (Ω j))
    (i₀ : J) (G : Ω i₀ → ℝ) :
    (FiniteLaw.pi μ).expect (fun z => G (z i₀)) = (μ i₀).expect G := by
  have h := FiniteLaw.expect_pi_product μ (Function.update (fun _ _ => (1 : ℝ)) i₀ G)
  have h1 : ∀ z : ∀ j, Ω j,
      ∏ j, Function.update (fun _ _ => (1 : ℝ)) i₀ G j (z j) = G (z i₀) := by
    intro z
    rw [Finset.prod_eq_single i₀ (fun j _ hj => by rw [Function.update_of_ne hj])
      (by simp), Function.update_self]
  have h2 : ∏ j, (μ j).expect (Function.update (fun _ _ => (1 : ℝ)) i₀ G j) =
      (μ i₀).expect G := by
    rw [Finset.prod_eq_single i₀ (fun j _ hj => by
      rw [Function.update_of_ne hj, FiniteLaw.expect_const]) (by simp), Function.update_self]
  simp only [h1] at h
  rw [h, h2]

/-- **The coordinate marginal of a tensor law**: `E_{⊗μ} G(z_{·, i₀}) = E_{μ_{i₀}} G`. -/
theorem expect_tensor_coordinate (μ : ∀ j, FiniteLaw (V → X j)) (i₀ : J)
    (G : (V → X i₀) → ℝ) :
    (FiniteLaw.tensor μ).expect (fun w => G (fun v => w v i₀)) = (μ i₀).expect G := by
  rw [expect_tensor_eq_pi]
  exact expect_pi_coordinate' μ i₀ G

end Marginals

section Prefix

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]

/-- **(R3) per prefix coordinate** (`_hR30` of the density-dc theorems): if the prefix law is
the product `⊗_i μ0_i`, every `μ0_i` is invariant under `w ↦ r w + t` for square units `r`.
From WP-FI's `Reference.inv₀`. -/
theorem prefix_R3_coordinate (R : Reference m₀) (μ0 : ∀ i, FiniteLaw (Slot → ZMod (m₀ i)))
    (hμ : R.μ₀ = FiniteLaw.tensor μ0) (i₀ : J₀) (r t : ZMod (m₀ i₀)) (hr : IsUnit r)
    (hsq : IsSquare r) (F : (Slot → ZMod (m₀ i₀)) → ℝ) :
    (μ0 i₀).expect (fun w => F (fun v => r * w v + t)) = (μ0 i₀).expect F := by
  set a : ∀ i, (ZMod (m₀ i))ˣ := Function.update (fun _ => 1) i₀ hr.unit with ha
  set b : ResidueSpace m₀ := Function.update (fun _ => 0) i₀ t with hb
  have hsqa : ∀ i, IsSquare ((a i : ZMod (m₀ i))) := by
    intro i
    by_cases hi : i = i₀
    · subst hi
      simp only [ha, Function.update_self, IsUnit.unit_spec]
      exact hsq
    · simp only [ha, Function.update_of_ne hi, Units.val_one]
      exact ⟨1, by ring⟩
  have hinv := R.inv₀ a b hsqa (fun z => F (fun v => z v i₀))
  rw [hμ] at hinv
  have hcoord : ∀ x : ResidueSpace m₀, piAffineEquiv m₀ a b x i₀ = r * x i₀ + t := by
    intro x
    change (a i₀ : ZMod (m₀ i₀)) * x i₀ + b i₀ = r * x i₀ + t
    simp only [ha, hb, Function.update_self, IsUnit.unit_spec]
  simp only [hcoord] at hinv
  rw [expect_tensor_coordinate μ0 i₀ (fun w => F (fun v => r * w v + t)),
    expect_tensor_coordinate μ0 i₀ F] at hinv
  exact hinv

/-- **(R2) per prefix coordinate** (`_hp0` of the density-dc theorems): if the prefix law is the
product `⊗_i μ0_i`, every `μ0_i` is reflection positive at the sorting cuts. From WP-FI's
`Reference.rp₀`. -/
theorem prefix_R2_coordinate (R : Reference m₀) (μ0 : ∀ i, FiniteLaw (Slot → ZMod (m₀ i)))
    (hμ : R.μ₀ = FiniteLaw.tensor μ0) (i₀ : J₀) :
    SlotReflectionPositive (signedIntegral (μ0 i₀).weight) := by
  intro c hc
  have hpos := R.rp₀.slot c hc
  rw [hμ] at hpos
  -- the cut form of `μ0 i₀` is the cut form of the product at lifted half-functions
  have hform : ∀ F G : (c.Half → ZMod (m₀ i₀)) → ℝ,
      c.form (signedIntegral (μ0 i₀).weight) F G =
        c.form (signedIntegral (FiniteLaw.tensor μ0).weight)
          (fun x => F (fun v => x v i₀)) (fun x => G (fun v => x v i₀)) := by
    intro F G
    unfold ReflectionCut.form
    rw [← FiniteLaw.expect_eq_signedIntegral, ← FiniteLaw.expect_eq_signedIntegral]
    exact (expect_tensor_coordinate μ0 i₀ _).symm
  refine ⟨fun F G => ?_, fun F => ?_⟩
  · rw [hform, hform]
    exact hpos.symmetric _ _
  · rw [hform]
    exact hpos.nonneg _

end Prefix

end Sarkozy.EnvelopeInputs
