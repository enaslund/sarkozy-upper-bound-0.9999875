module

public import Sarkozy.BlockRows.Middle
public import Sarkozy.TraceMixing.Paley

@[expose] public section

/-!
# Block rows, III′: the middle object has the same law under the `F` and `E` laws

`paper/sections/20c_middle_frame.tex`, `lem:front12:reference`(i), proof, "One prime": "For one
layer the middle law is uniform for both laws, by translation invariance; for two layers it is
uniform on the distinct pairs for the `E` law by symmetry and for the `F` law by
`lem:record:class-three`(ii)".

Here this is proved for the one-prime laws `λ_p(G_F)`, `λ_p(G_E)` without counting: the middle
law of either law is invariant under the square-affine maps `z ↦ αz + β` (`χ(α) = 1`) and, for two
layers, under the layer swap (an automorphism of both graphs); it vanishes on the diagonal
(injectivity). For `p ≡ 3 (mod 4)` (`χ(-1) = -1`) these maps act transitively on the ordered
distinct pairs, so both middle laws are uniform there, hence equal.

* `midLaw_affine`, `midLaw_swap`, `midLaw_diag`: the invariances and the vanishing;
* `eq_of_const_on`: two laws constant on the same set and zero off it are equal;
* **`primeMid_one`**, **`primeMid_two`**: `ν_F = ν_E` at one prime, one and two layers.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.BlockRows

open Sarkozy Sarkozy.Labellings Sarkozy.FiveType Sarkozy.PartV

section Generic

variable {p : ℕ} [Fact p.Prime] {Λ : Type} [Fintype Λ] [DecidableEq Λ]

/-- The weight of a one-prime law is invariant under the square-affine maps. -/
theorem graphLaw_weight_affine {W : Type} [Fintype W] [DecidableEq W] (G : OrientedGraph W)
    (hne : (injLabellings (ZMod p) G).Nonempty) {α : ZMod p}
    (hα : quadraticChar (ZMod p) α = 1) (β : ZMod p) (z : W → ZMod p) :
    (graphLaw G hne).weight (fun w => α * z w + β) = (graphLaw G hne).weight z := by
  have hmem : (fun w => α * z w + β) ∈ injLabellings (ZMod p) G ↔
      z ∈ injLabellings (ZMod p) G := by
    rw [mem_injLabellings_iff_feasible, mem_injLabellings_iff_feasible]
    exact feasible_affine_iff G hα β z
  simp only [graphLaw, hmem]

/-- **A middle law is invariant under a weight-preserving relabelling of the configurations that
acts on the middle object by an injective map.** -/
theorem nuOf_comp {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛] (π : FiniteLaw (Fin 3 → 𝔛))
    (A : (Fin 3 → 𝔛) ≃ (Fin 3 → 𝔛)) (hA : ∀ ω, π.weight (A ω) = π.weight ω) (a : 𝔛 → 𝔛)
    (ha : Function.Injective a) (hAa : ∀ ω, A ω 1 = a (ω 1)) (ξ : 𝔛) :
    (nuOf π).weight (a ξ) = (nuOf π).weight ξ := by
  rw [nuOf, map_weight_eq, map_weight_eq, sum_filter, sum_filter]
  rw [← Fintype.sum_equiv A (fun ω => if A ω 1 = a ξ then π.weight (A ω) else 0) _
    (fun _ => rfl)]
  refine sum_congr rfl fun ω _ => ?_
  rw [hAa, hA]
  simp only [ha.eq_iff]

/-- **Square-affine invariance of the middle law** of `λ_p(G)`. -/
theorem midLaw_affine (G : OrientedGraph (Fin 3 × Λ))
    (hne : (injLabellings (ZMod p) G).Nonempty) {α : ZMod p}
    (hα : quadraticChar (ZMod p) α = 1) (β : ZMod p) (ξ : Λ → ZMod p) :
    (nuOf (primeLaw p G hne)).weight (fun l => α * ξ l + β) =
      (nuOf (primeLaw p G hne)).weight ξ := by
  have hα0 : α ≠ 0 := ne_zero_of_quadraticChar_eq_one hα
  let A : (Fin 3 → Λ → ZMod p) ≃ (Fin 3 → Λ → ZMod p) :=
    { toFun := fun ω o l => α * ω o l + β
      invFun := fun ω o l => α⁻¹ * (ω o l - β)
      left_inv := fun ω => by funext o l; field_simp; ring
      right_inv := fun ω => by funext o l; field_simp; ring }
  refine nuOf_comp _ A (fun ω => ?_) (fun ξ l => α * ξ l + β) (fun x y h => ?_) (fun _ => rfl) ξ
  · rw [objLaw_weight, objLaw_weight]
    exact graphLaw_weight_affine G hne hα β (fun q => ω q.1 q.2)
  · funext l
    have := congrFun h l
    simpa [hα0] using this

/-- **Layer-swap invariance of the middle law** of `λ_p(G)` (two layers), when the layer swap is
an automorphism of `G`. -/
theorem midLaw_swap (G : OrientedGraph (Fin 3 × Fin 2))
    (hne : (injLabellings (ZMod p) G).Nonempty)
    (hG : IsAutomorphism G ((Equiv.refl (Fin 3)).prodCongr (Equiv.swap (0 : Fin 2) 1)))
    (ξ : Fin 2 → ZMod p) :
    (nuOf (primeLaw p G hne)).weight (ξ ∘ Equiv.swap (0 : Fin 2) 1) =
      (nuOf (primeLaw p G hne)).weight ξ := by
  let A : (Fin 3 → Fin 2 → ZMod p) ≃ (Fin 3 → Fin 2 → ZMod p) :=
    { toFun := fun ω o => ω o ∘ Equiv.swap (0 : Fin 2) 1
      invFun := fun ω o => ω o ∘ Equiv.swap (0 : Fin 2) 1
      left_inv := fun ω => by funext o l; simp
      right_inv := fun ω => by funext o l; simp }
  refine nuOf_comp _ A (fun ω => ?_) (fun ξ => ξ ∘ Equiv.swap (0 : Fin 2) 1) (fun x y h => ?_)
    (fun _ => rfl) ξ
  · rw [objLaw_weight, objLaw_weight]
    have h := weight_comp_of_expect (graphLaw G hne)
      (relabelEquiv ((Equiv.refl (Fin 3)).prodCongr (Equiv.swap (0 : Fin 2) 1)))
      (fun f => graphLaw_expect_comp G hne _ hG f) (fun q => ω q.1 q.2)
    exact h
  · funext l
    have := congrFun h (Equiv.swap (0 : Fin 2) 1 l)
    simpa using this

/-- **The middle law vanishes on the diagonal** (two layers): a middle object with equal labels
on its two layers is not injective. -/
theorem midLaw_diag (G : OrientedGraph (Fin 3 × Fin 2))
    (hne : (injLabellings (ZMod p) G).Nonempty) {ξ : Fin 2 → ZMod p} (hξ : ξ 0 = ξ 1) :
    (nuOf (primeLaw p G hne)).weight ξ = 0 := by
  rw [nuOf, map_weight_eq]
  refine sum_eq_zero fun ω hω => ?_
  have h1 : ω 1 = ξ := (mem_filter.mp hω).2
  rw [objLaw_weight]
  simp only [graphLaw]
  split_ifs with hmem
  · exfalso
    rw [mem_injLabellings_iff_feasible] at hmem
    have := hmem.1 ((1 : Fin 3), (0 : Fin 2)) (mem_univ _) ((1 : Fin 3), (1 : Fin 2)) (mem_univ _)
      (by simp only; rw [h1]; exact hξ)
    simp at this
  · rfl

/-- **Two laws constant on the same set and zero off it are equal.** -/
theorem eq_of_const_on {X : Type*} [Fintype X] (μ μ' : FiniteLaw X) (S : X → Prop)
    [DecidablePred S] (h0 : ∀ x, ¬ S x → μ.weight x = 0) (h0' : ∀ x, ¬ S x → μ'.weight x = 0)
    (hc : ∀ x y, S x → S y → μ.weight x = μ.weight y)
    (hc' : ∀ x y, S x → S y → μ'.weight x = μ'.weight y) (x : X) :
    μ.weight x = μ'.weight x := by
  by_cases hx : S x
  · have ht : ∀ ν : FiniteLaw X, (∀ y, ¬ S y → ν.weight y = 0) →
        (∀ y, S y → ν.weight y = ν.weight x) →
        ν.weight x * ((univ.filter S).card : ℝ) = 1 := by
      intro ν hν0 hνc
      rw [← ν.total, ← sum_filter_add_sum_filter_not univ S]
      rw [sum_congr rfl fun y hy => hνc y (mem_filter.mp hy).2,
        sum_congr rfl fun y hy => hν0 y (mem_filter.mp hy).2]
      rw [sum_const, sum_const_zero, add_zero, nsmul_eq_mul]
      ring
    have h1 := ht μ h0 fun y hy => hc y x hy hx
    have h2 := ht μ' h0' fun y hy => hc' y x hy hx
    have hN : ((univ.filter S).card : ℝ) ≠ 0 := by
      intro h
      rw [h, mul_zero] at h1
      exact zero_ne_one h1
    exact mul_right_cancel₀ hN (h1.trans h2.symm)
  · rw [h0 x hx, h0' x hx]

end Generic

/-! ## The two middle laws agree -/

section Equal

variable (p : ℕ) [Fact p.Prime]

/-- **One layer**: the middle laws of `λ_p(G_F)` and `λ_p(G_E)` agree (both are uniform). -/
theorem primeMid_one (hE : (injLabellings (ZMod p) (matchGraph (Fin 1))).Nonempty)
    (hF : (injLabellings (ZMod p) (foldGraph (Fin 1))).Nonempty) (ξ : Fin 1 → ZMod p) :
    (nuOf (primeLaw p (foldGraph (Fin 1)) hF)).weight ξ =
      (nuOf (primeLaw p (matchGraph (Fin 1)) hE)).weight ξ := by
  have hconst : ∀ (G : OrientedGraph (Fin 3 × Fin 1)) (hne : (injLabellings (ZMod p) G).Nonempty)
      (x y : Fin 1 → ZMod p), (nuOf (primeLaw p G hne)).weight x =
        (nuOf (primeLaw p G hne)).weight y := by
    intro G hne x y
    have h := midLaw_affine G hne (α := 1) (by simp) (y 0 - x 0) x
    have e : (fun l => (1 : ZMod p) * x l + (y 0 - x 0)) = y := by
      funext l
      fin_cases l
      simp only [one_mul, Fin.zero_eta, Fin.isValue]
      ring
    rw [e] at h
    exact h.symm
  exact eq_of_const_on _ _ (fun _ => True) (fun _ h => absurd trivial h)
    (fun _ h => absurd trivial h) (fun x y _ _ => hconst _ _ x y) (fun x y _ _ => hconst _ _ x y) ξ

/-- The layer swap is an automorphism of `G_{F,2}` (its edges do not read the layers). -/
theorem foldGraph_two_swap :
    IsAutomorphism (foldGraph (Fin 2))
      ((Equiv.refl (Fin 3)).prodCongr (Equiv.swap (0 : Fin 2) 1)) := by
  intro u v
  simp [mem_foldGraph]

/-- **Two layers**, `p ≡ 3 (mod 4)`: the middle laws of `λ_p(G_F)` and `λ_p(G_E)` agree (both are
uniform on the ordered distinct pairs). -/
theorem primeMid_two (h3 : p % 4 = 3) (hE : (injLabellings (ZMod p) (matchGraph (Fin 2))).Nonempty)
    (hF : (injLabellings (ZMod p) (foldGraph (Fin 2))).Nonempty) (ξ : Fin 2 → ZMod p) :
    (nuOf (primeLaw p (foldGraph (Fin 2)) hF)).weight ξ =
      (nuOf (primeLaw p (matchGraph (Fin 2)) hE)).weight ξ := by
  have hχ : quadraticChar (ZMod p) (-1) = -1 :=
    TraceMixing.chi_neg_one_of_three (by rw [ZMod.card]; exact h3)
  have hconst : ∀ (G : OrientedGraph (Fin 3 × Fin 2)) (hne : (injLabellings (ZMod p) G).Nonempty),
      IsAutomorphism G ((Equiv.refl (Fin 3)).prodCongr (Equiv.swap (0 : Fin 2) 1)) →
      ∀ x y : Fin 2 → ZMod p, x 0 ≠ x 1 → y 0 ≠ y 1 →
        (nuOf (primeLaw p G hne)).weight x = (nuOf (primeLaw p G hne)).weight y := by
    intro G hne hG x y hx hy
    -- the affine step, when `χ(x₁ - x₀) = χ(y₁ - y₀)`
    have step : ∀ x : Fin 2 → ZMod p, x 0 ≠ x 1 →
        quadraticChar (ZMod p) (x 1 - x 0) = quadraticChar (ZMod p) (y 1 - y 0) →
        (nuOf (primeLaw p G hne)).weight x = (nuOf (primeLaw p G hne)).weight y := by
      intro x hx hc
      have hdx : x 1 - x 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
      have hdy : y 1 - y 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
      set α : ZMod p := (y 1 - y 0) / (x 1 - x 0) with hαd
      have hα : quadraticChar (ZMod p) α = 1 := by
        have hm := map_mul (quadraticChar (ZMod p)) α (x 1 - x 0)
        have hαx : α * (x 1 - x 0) = y 1 - y 0 := by rw [hαd]; field_simp
        rw [hαx, ← hc] at hm
        have hne0 : quadraticChar (ZMod p) (x 1 - x 0) ≠ 0 :=
          fun h0 => hdx (quadraticChar_eq_zero_iff.mp h0)
        have : quadraticChar (ZMod p) α * quadraticChar (ZMod p) (x 1 - x 0) =
            1 * quadraticChar (ZMod p) (x 1 - x 0) := by rw [one_mul]; exact hm.symm
        exact mul_right_cancel₀ hne0 this
      have h := midLaw_affine G hne hα (y 0 - α * x 0) x
      have e : (fun l => α * x l + (y 0 - α * x 0)) = y := by
        funext l
        fin_cases l
        · simp only [Fin.zero_eta, Fin.isValue]
          ring
        · simp only [Fin.mk_one, Fin.isValue]
          rw [hαd]
          field_simp
          ring
      rw [e] at h
      exact h.symm
    by_cases hc : quadraticChar (ZMod p) (x 1 - x 0) = quadraticChar (ZMod p) (y 1 - y 0)
    · exact step x hx hc
    · rw [← midLaw_swap G hne hG x]
      refine step _ (by simpa using Ne.symm hx) ?_
      have hdx : x 1 - x 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
      have hdy : y 1 - y 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
      have e1 : (x ∘ Equiv.swap (0 : Fin 2) 1) 1 = x 0 := by simp
      have e0 : (x ∘ Equiv.swap (0 : Fin 2) 1) 0 = x 1 := by simp
      have key : quadraticChar (ZMod p) (x 1 - x 0) = -quadraticChar (ZMod p) (y 1 - y 0) := by
        rcases quadraticChar_dichotomy hdx with h | h <;>
          rcases quadraticChar_dichotomy hdy with h' | h' <;> rw [h, h'] at hc ⊢ <;> simp_all
      rw [e1, e0, TraceMixing.chi_swap (by rw [ZMod.card]; exact h3) (x 0) (x 1), key, neg_neg]
  exact eq_of_const_on _ _ (fun x : Fin 2 → ZMod p => x 0 ≠ x 1)
    (fun x h => midLaw_diag _ hF (not_not.mp h)) (fun x h => midLaw_diag _ hE (not_not.mp h))
    (fun x y hx hy => hconst _ hF (foldGraph_two_swap) x y hx hy)
    (fun x y hx hy => hconst _ hE (matchGraph_auto _ _) x y hx hy) ξ

end Equal

end Sarkozy.BlockRows
