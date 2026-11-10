module

public import Sarkozy.OpsVariance.TensorCen
public import Sarkozy.OpsVariance.ZeroMarginal

@[expose] public section

/-!
# The record laws of a middle block: half marginals, symmetry, and the block (Cen)

`paper/sections/22_variance.tex`, `lem:var-gain` (Cen): "for every `φ ∈ 𝓡`, `Π_φ` is symmetric at
`ι`, and its Markov operator `T_φ` on `L²(m_φ)` satisfies `‖T_φ − 𝒥‖ ≤ κ`";
`lem:record:paired-e-bridge`(b), `lem:record:old-f-marginal`(d) ("`T_X` is the tensor product of the
prime operators"); `def:cp4`(b) (the norm envelopes are `Diag_ι` of the actual half marginals).

A record of a middle block is `emit λ (midEmission φ)` with `λ = ⊗_p λ_p` a tensor over the primes
of the block. Proved here, for any such record:

* `signedIntegral_emit_tensor`: the emission of a tensor is the tensor of the emissions;
* `plusMarginal_emit_tensor`: its half marginal is the product of the prime half marginals;
* **`centredNormLe_emit_tensor`**: the block (Cen) from the prime (Cen), with
  `κ = max_p κ_p ≤ 1` (`centredNormLe_tensor`);
* `minusMarginal_eq_plus_of_swap`, `form_symm_of_swap`: a record whose two-layer law is invariant
  under the layer swap has equal half marginals and is symmetric at `ι`;
* `halfMarginalPlus_diagonalLaw`: the half marginal of `Diag_c(m)` is `m` (so the half marginal of
  a norm envelope `env = Diag_ι(m_+)` of B7 is the record's `m_+`).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.OpsVariance

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.RecordExpansion Sarkozy.Variance
open Sarkozy.SignedComponents (plusHalf_mid minusHalf_mid halfRead)
open Sarkozy.Labellings (layerSwapMap)

section Diag

variable {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X]

/-- The plus-half marginal of `Diag_c(m)` is `m`. -/
theorem halfMarginalPlus_diagonalLaw (c : ReflectionCut V) (m : (c.Half → X) → ℝ) :
    Comparison.halfMarginalPlus c (c.diagonalLaw m) = m := by
  funext x
  unfold Comparison.halfMarginalPlus
  change ∑ y, m y * (if (fun v : c.Half => c.join y y v.1) = x then 1 else 0) = m x
  have hj : ∀ y : c.Half → X, (fun v : c.Half => c.join y y v.1) = y := fun y =>
    funext fun v => c.join_plus y y v
  simp_rw [hj]
  rw [sum_eq_single x]
  · simp
  · intro y _ hy
    simp [hy]
  · intro h
    exact absurd (mem_univ _) h

end Diag

section Tensor

variable {J : Type} [Fintype J] [DecidableEq J] {X : J → Type} [∀ j, Fintype (X j)]
  [∀ j, DecidableEq (X j)] {I : Type} [Fintype I] [DecidableEq I]

/-- **The emission of a tensor is the tensor of the emissions.** -/
theorem signedIntegral_emit_tensor (μ : ∀ j, FiniteLaw (I → X j)) (π : Slot → I) :
    signedIntegral (emit (FiniteLaw.tensor μ) π).weight =
      tensorLaw (fun j => signedIntegral (emit (μ j) π).weight) := by
  classical
  apply LinearMap.ext
  intro f
  rw [linearFunctional_density (signedIntegral (emit (FiniteLaw.tensor μ) π).weight) f,
    linearFunctional_density (tensorLaw (fun j => signedIntegral (emit (μ j) π).weight)) f]
  refine sum_congr rfl fun z _ => ?_
  congr 1
  -- both sides are `∏_j E_{μ_j}[y_j ∘ π = z_j]`
  have hind : ∀ x : Slot → ∀ j, X j, (if x = z then (1 : ℝ) else 0) =
      ∏ j, (if (fun v => x v j) = (fun v => z v j) then 1 else 0) := by
    intro x
    rw [prod_indicator_forall (fun j => (fun v => x v j) = (fun v => z v j))]
    congr 1
    apply propext
    constructor
    · rintro rfl j
      rfl
    · intro h
      funext v j
      exact congrFun (h j) v
  have hL : signedIntegral (emit (FiniteLaw.tensor μ) π).weight (fun y => if y = z then 1 else 0) =
      ∏ j, signedIntegral (μ j).weight
        (fun yj => if (fun v => yj (π v)) = (fun v => z v j) then 1 else 0) := by
    rw [signedIntegral_emit]
    change signedIntegral (FiniteLaw.tensor μ).weight (fun y => if y ∘ π = z then 1 else 0) = _
    rw [FiniteLaw.signedIntegral_tensor]
    have e : (fun y : I → ∀ j, X j => if y ∘ π = z then (1 : ℝ) else 0) =
        fun y => ∏ j, (fun yj : I → X j =>
          if (fun v => yj (π v)) = (fun v => z v j) then (1 : ℝ) else 0) (fun w => y w j) := by
      funext y
      rw [hind (y ∘ π)]
      rfl
    rw [e]
    exact tensorLaw_fubini (fun j => signedIntegral (μ j).weight)
      (fun j (yj : I → X j) => if (fun v => yj (π v)) = (fun v => z v j) then (1 : ℝ) else 0)
  have hR : tensorLaw (fun j => signedIntegral (emit (μ j) π).weight)
      (fun y => if y = z then 1 else 0) =
      ∏ j, signedIntegral (μ j).weight
        (fun yj => if (fun v => yj (π v)) = (fun v => z v j) then 1 else 0) := by
    have e : (fun y : Slot → ∀ j, X j => if y = z then (1 : ℝ) else 0) =
        fun y => ∏ j, (fun yj : Slot → X j =>
          if yj = (fun v => z v j) then (1 : ℝ) else 0) (fun v => y v j) := by
      funext y
      rw [hind y]
    rw [e]
    refine (tensorLaw_fubini _ (fun j (yj : Slot → X j) =>
      if yj = (fun v => z v j) then (1 : ℝ) else 0)).trans (prod_congr rfl fun j _ => ?_)
    rw [signedIntegral_emit]
    rfl
  change signedIntegral (emit (FiniteLaw.tensor μ) π).weight (fun y => if y = z then 1 else 0) =
    tensorLaw (fun j => signedIntegral (emit (μ j) π).weight) (fun y => if y = z then 1 else 0)
  rw [hL, hR]

/-- The plus-half marginal of a weight, as a cut form against an indicator. -/
theorem plusMarginal_eq_form {Y : Type} [Fintype Y] [DecidableEq Y] (c : ReflectionCut Slot)
    (w : (Slot → Y) → ℝ) (x : c.Half → Y) :
    plusMarginal c w x = c.form (signedIntegral w) (fun x' => if x' = x then 1 else 0) 1 := by
  rw [form_signedIntegral_one_right]
  rw [sum_eq_single x]
  · simp
  · intro y _ hy
    simp [hy]
  · intro h
    exact absurd (mem_univ _) h

/-- **The half marginal of the emission of a tensor is the product of the prime half marginals.** -/
theorem plusMarginal_emit_tensor (c : ReflectionCut Slot) (μ : ∀ j, FiniteLaw (I → X j))
    (π : Slot → I) (x : c.Half → ∀ j, X j) :
    plusMarginal c (emit (FiniteLaw.tensor μ) π).weight x =
      ∏ j, plusMarginal c (emit (μ j) π).weight (fun u => x u j) := by
  classical
  rw [plusMarginal_eq_form, signedIntegral_emit_tensor]
  simp_rw [plusMarginal_eq_form]
  unfold ReflectionCut.form
  have e : (fun z : Slot → ∀ j, X j =>
      (fun x' : c.Half → ∀ j, X j => if x' = x then (1 : ℝ) else 0) (fun v => z v.1) *
        (1 : (c.Half → ∀ j, X j) → ℝ) (fun v => z (c.flip v.1))) =
      fun z => ∏ j, (fun zj : Slot → X j =>
        (fun x' : c.Half → X j => if x' = (fun u => x u j) then (1 : ℝ) else 0) (fun v => zj v.1) *
          (1 : (c.Half → X j) → ℝ) (fun v => zj (c.flip v.1))) (fun v => z v j) := by
    funext z
    simp only [Pi.one_apply, mul_one]
    rw [prod_indicator_forall (fun j => (fun v : c.Half => z v.1 j) = (fun u => x u j))]
    congr 1
    apply propext
    constructor
    · rintro rfl j
      rfl
    · intro h
      funext v j
      exact congrFun (h j) v
  rw [e]
  exact tensorLaw_fubini (fun j => signedIntegral (emit (μ j) π).weight)
    (fun j (zj : Slot → X j) =>
      (fun x' : c.Half → X j => if x' = (fun u => x u j) then (1 : ℝ) else 0) (fun v => zj v.1) *
        (1 : (c.Half → X j) → ℝ) (fun v => zj (c.flip v.1)))

/-- **The block (Cen) from the prime (Cen)**: if every prime record `emit μ_j π` is symmetric at
`c`, with half marginal of positive mass and centred norm `κ_j ≤ κ ≤ 1`, then the block record
`emit (⊗μ_j) π` has centred norm `≤ κ` relative to its half marginal. -/
theorem centredNormLe_emit_tensor (c : ReflectionCut Slot) (μ : ∀ j, FiniteLaw (I → X j))
    (π : Slot → I)
    (hsymm : ∀ j (F G : (c.Half → X j) → ℝ),
      c.form (signedIntegral (emit (μ j) π).weight) F G =
        c.form (signedIntegral (emit (μ j) π).weight) G F)
    (hmpos : ∀ j, 0 < ∑ x, plusMarginal c (emit (μ j) π).weight x)
    (κj : J → ℝ) (hκj0 : ∀ j, 0 ≤ κj j)
    (hcen : ∀ j, CentredNormLe c (signedIntegral (emit (μ j) π).weight)
      (plusMarginal c (emit (μ j) π).weight) (κj j))
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hκ : ∀ j, κj j ≤ κ) :
    CentredNormLe c (signedIntegral (emit (FiniteLaw.tensor μ) π).weight)
      (plusMarginal c (emit (FiniteLaw.tensor μ) π).weight) κ := by
  have hM : plusMarginal c (emit (FiniteLaw.tensor μ) π).weight =
      fun x => ∏ j, plusMarginal c (emit (μ j) π).weight (fun u => x u j) := by
    funext x
    exact plusMarginal_emit_tensor c μ π x
  rw [hM, signedIntegral_emit_tensor]
  exact centredNormLe_tensor c _ _ (fun j x => plusMarginal_nonneg c (emit (μ j) π).nonneg x)
    hmpos hsymm (fun j F => form_signedIntegral_one_right c _ F) κj hκj0 hcen hκ0 hκ1 hκ

end Tensor

section Swap

variable {X : Type} [Fintype X] [DecidableEq X] {O : Type} [Fintype O] [DecidableEq O]

omit [DecidableEq X] in
/-- A two-layer law invariant under the layer swap has the same expectations after the swap. -/
theorem expect_swap (lam : FiniteLaw (O × Fin 2 → X))
    (hsw : ∀ y, lam.weight (y ∘ layerSwapMap O) = lam.weight y) (f : (O × Fin 2 → X) → ℝ) :
    lam.expect (fun y => f (y ∘ layerSwapMap O)) = lam.expect f := by
  unfold FiniteLaw.expect
  let e : (O × Fin 2 → X) ≃ (O × Fin 2 → X) :=
    { toFun := fun y => y ∘ layerSwapMap O
      invFun := fun y => y ∘ layerSwapMap O
      left_inv := fun y => by
        funext w
        rcases w with ⟨o, ℓ⟩
        simp [layerSwapMap, Equiv.swap_apply_self]
      right_inv := fun y => by
        funext w
        rcases w with ⟨o, ℓ⟩
        simp [layerSwapMap, Equiv.swap_apply_self] }
  rw [← Equiv.sum_comp e]
  refine sum_congr rfl fun y _ => ?_
  change lam.weight (y ∘ layerSwapMap O) * f ((y ∘ layerSwapMap O) ∘ layerSwapMap O) = _
  rw [hsw]
  congr 2
  funext w
  rcases w with ⟨o, ℓ⟩
  simp [layerSwapMap, Equiv.swap_apply_self]

/-- **A swap-invariant record is symmetric at `ι`.** -/
theorem form_symm_of_swap (lam : FiniteLaw (O × Fin 2 → X)) (φ : ZMod 6 → O)
    (hsw : ∀ y, lam.weight (y ∘ layerSwapMap O) = lam.weight y)
    (F G : (reservedCut.Half → X) → ℝ) :
    reservedCut.form (signedIntegral (emit lam (midEmission φ)).weight) F G =
      reservedCut.form (signedIntegral (emit lam (midEmission φ)).weight) G F := by
  have hf : ∀ H K : (reservedCut.Half → X) → ℝ,
      reservedCut.form (signedIntegral (emit lam (midEmission φ)).weight) H K =
        lam.expect (fun y => H (halfRead φ y 0) * K (halfRead φ y 1)) := by
    intro H K
    unfold ReflectionCut.form
    change (emit lam (midEmission φ)).expect _ = _
    rw [expect_emit]
    refine FiniteLaw.expect_congr _ fun y => ?_
    have h1 : (fun v : reservedCut.Half => (y ∘ midEmission φ) v.1) = halfRead φ y 0 :=
      plusHalf_mid (X := X) φ y
    have h2 : (fun v : reservedCut.Half => (y ∘ midEmission φ) (reservedCut.flip v.1)) =
        halfRead φ y 1 := minusHalf_mid (X := X) φ y
    rw [h1, h2]
  rw [hf, hf, ← expect_swap lam hsw]
  refine FiniteLaw.expect_congr _ fun y => ?_
  rw [mul_comm]
  congr 2

/-- **A swap-invariant record has equal half marginals.** -/
theorem minusMarginal_eq_plus_of_swap (lam : FiniteLaw (O × Fin 2 → X)) (φ : ZMod 6 → O)
    (hsw : ∀ y, lam.weight (y ∘ layerSwapMap O) = lam.weight y) :
    minusMarginal reservedCut (emit lam (midEmission φ)).weight =
      plusMarginal reservedCut (emit lam (midEmission φ)).weight := by
  funext x
  have h1 := form_signedIntegral_one_left reservedCut (emit lam (midEmission φ)).weight
    (fun x' => if x' = x then 1 else 0)
  rw [← form_symm_of_swap lam φ hsw, form_signedIntegral_one_right] at h1
  have e : ∀ m : (reservedCut.Half → X) → ℝ,
      ∑ y, m y * (if y = x then (1 : ℝ) else 0) = m x := by
    intro m
    rw [sum_eq_single x]
    · simp
    · intro y _ hy
      simp [hy]
    · intro h
      exact absurd (mem_univ _) h
  rw [e, e] at h1
  exact h1.symm

end Swap

end Sarkozy.OpsVariance
