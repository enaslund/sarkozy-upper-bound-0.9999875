module

public import Sarkozy.ExtractionK.SoftCollision2

@[expose] public section

/-!
# Soft coincidences: the full collision operator (`cor:soft-kernels`(b), `lem:oct24-collision`)

`paper/sections/16_extraction.tex`, `cor:soft-kernels`(b) for the full soft collision operator
`T^D_coll` with kernel `1{x(U⁺) ∩ x'(U⁺) ≠ ∅} ∏_{e ∈ E_×}(1 + D_e χ_e)` (`skCollKerColl`,
`= skCollKer1 + skCollKer2`, `sk_collKerColl_eq`): the bounds of `lem:oct24-collision`(d), (e) of
`Extraction/CollisionStrata.lean` hold with the same constants, from the soft parts
`sk_soft_collision_opBound` (`D_1`) and `sk_soft_collision_opBound2` (`D_{≥2}`):

* `sk_soft_collision_opBound_sum` (`D_1 + D_{≥2}`), `sk_soft_collision_opBound_natural`
  (`eq:collision-natural`, `D_nat`), `sk_soft_collision_opBound_ord` (`D_ord`),
  `sk_soft_collision_opBound_tailForm` (the tail form).

Hypotheses as in `Extraction/CollisionStrata.lean` (antisymmetric signs), plus `|D_e| ≤ 1` and
`χ(-1) = -1` if some `D_e < 0`.
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

section SkColl3

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The soft collision kernel `1{x(U⁺) ∩ x'(U⁺) ≠ ∅} ∏_{e ∈ E_×}(1 + D_e χ_e)` (`T^D_coll`). -/
noncomputable def skCollKerColl (ς : U → U → ℤ) (D : U × U → ℝ) (x x' : U → F) : ℝ :=
  if 1 ≤ collisionCommon x x' then
    ∏ e ∈ collisionCross ς, (1 + D e * (quadraticChar F ((ς e.1 e.2 : F) * (x' e.2 - x e.1)) : ℝ))
  else 0

omit [DecidableEq U] in
theorem sk_collKerColl_eq (ς : U → U → ℤ) (D : U × U → ℝ) (x x' : U → F) :
    skCollKerColl ς D x x' = skCollKer1 ς D x x' + skCollKer2 ς D x x' := by
  unfold skCollKerColl skCollKer1 skCollKer2
  by_cases h0 : collisionCommon x x' = 0
  · simp [h0]
  · by_cases h1 : collisionCommon x x' = 1
    · simp [h1]
    · have h2 : 2 ≤ collisionCommon x x' := by omega
      have h1' : 1 ≤ collisionCommon x x' := by omega
      simp [h1, h2, h1']

/-- **`cor:soft-kernels`(b) for `collision_opBound_sum`** (`lem:oct24-collision`): the same bound for the soft
collision operator `T^D_coll` (`|D_e| ≤ 1`; `χ(-1) = -1` if some `D_e < 0`). -/
theorem sk_soft_collision_opBound_sum (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (ord : U → U → U → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (π : ℕ → U → ℕ) (hπ : ∀ k, Function.Injective (π k))
    (D : U × U → ℝ) (hD : ∀ e, |D e| ≤ 1) (hneg : ∀ e, D e < 0 → quadraticChar F (-1) = -1) :
    Sarkozy.Influence.OpBound (injLabellings F G) (injLabellings F G)
      (fun x x' => skCollKerColl ς D x x' / (injLabellings F G).card)
      (collisionD1 G ς ord (Fintype.card F) n + collisionD2 G ς π (Fintype.card F) n) := by
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have h1 := sk_soft_collision_opBound hW G ς hς hanti hne hn hS1 ord hord D hD hneg
  have h2 := sk_soft_collision_opBound2 hW G ς hς hanti hne hn hS1 π hπ D hD hneg
  have hsum := Sarkozy.Influence.OpBound.add h1 h2 (collisionD1_nonneg G ς ord hq0 hS1)
    (collisionD2_nonneg G ς π hq0 hS1)
  have heq : (fun (x x' : U → F) => skCollKerColl ς D x x' / (injLabellings F G).card) =
      (fun (x x' : U → F) => skCollKer1 ς D x x' / (injLabellings F G).card +
        skCollKer2 ς D x x' / (injLabellings F G).card) := by
    funext x x'
    rw [sk_collKerColl_eq, add_div]
  rw [heq]
  exact hsum

/-- **`cor:soft-kernels`(b) for `collision_opBound_natural`** (`lem:oct24-collision`): the same bound for the soft
collision operator `T^D_coll` (`|D_e| ≤ 1`; `χ(-1) = -1` if some `D_e < 0`). -/
theorem sk_soft_collision_opBound_natural (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (ord : U → U → U → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (π : ℕ → U → ℕ) (hπ : ∀ k, Function.Injective (π k))
    (D : U × U → ℝ) (hD : ∀ e, |D e| ≤ 1) (hneg : ∀ e, D e < 0 → quadraticChar F (-1) = -1) :
    Sarkozy.Influence.OpBound (injLabellings F G) (injLabellings F G)
      (fun x x' => skCollKerColl ς D x x' / (injLabellings F G).card)
      (collisionDnat G ς (Fintype.card F) n) := by
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have h1 := sk_soft_collision_opBound hW G ς hς hanti hne hn hS1 ord hord D hD hneg
  have h2 := sk_soft_collision_opBound2 hW G ς hς hanti hne hn hS1 π hπ D hD hneg
  have hD1 := collisionD1_nonneg G ς ord hq0 hS1
  have hD2 := collisionD2_nonneg G ς π hq0 hS1
  have hsum := Sarkozy.Influence.OpBound.add h1 h2 hD1 hD2
  have heq : (fun (x x' : U → F) => skCollKerColl ς D x x' / (injLabellings F G).card) =
      (fun (x x' : U → F) => skCollKer1 ς D x x' / (injLabellings F G).card +
        skCollKer2 ς D x x' / (injLabellings F G).card) := by
    funext x x'
    rw [sk_collKerColl_eq, add_div]
  rw [heq]
  refine hsum.mono (add_nonneg hD1 hD2) ?_
  have hc1 := collisionD1_le G ς ord hq0 hS1
  have hc2 := collisionD2_le G ς π hq0 hS1
  have hL : 0 < collisionLint G (Fintype.card F) n := prod_pos fun v _ => by linarith [hS1 v]
  unfold collisionDnat
  have hrw : collisionUps G ς (Fintype.card F) n * ((Fintype.card F : ℝ) *
      collisionLint G (Fintype.card F) n)⁻¹ * ∑ i, ∑ j, collisionA G ς i j =
      collisionUps G ς (Fintype.card F) n / collisionLint G (Fintype.card F) n *
        ((Fintype.card F : ℝ)⁻¹ * ∑ i, ∑ j, collisionA G ς i j) := by
    field_simp
  rw [hrw] at hc1
  nlinarith [hc1, hc2]

/-- **`cor:soft-kernels`(b) for `collision_opBound_ord`** (`lem:oct24-collision`): the same bound for the soft
collision operator `T^D_coll` (`|D_e| ≤ 1`; `χ(-1) = -1` if some `D_e < 0`). -/
theorem sk_soft_collision_opBound_ord (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (ord : U → U → U → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (π : ℕ → U → ℕ) (hπ : ∀ k, Function.Injective (π k))
    (D : U × U → ℝ) (hD : ∀ e, |D e| ≤ 1) (hneg : ∀ e, D e < 0 → quadraticChar F (-1) = -1) :
    Sarkozy.Influence.OpBound (injLabellings F G) (injLabellings F G)
      (fun x x' => skCollKerColl ς D x x' / (injLabellings F G).card)
      (collisionDord G ς ord (Fintype.card F) n) := by
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  refine (sk_soft_collision_opBound_sum hW G ς hς hanti hne hn hS1 ord hord π hπ D hD hneg).mono
    (add_nonneg (collisionD1_nonneg G ς ord hq0 hS1) (collisionD2_nonneg G ς π hq0 hS1)) ?_
  unfold collisionDord
  linarith [collisionD2_le G ς π hq0 hS1]

/-- **`cor:soft-kernels`(b) for `collision_opBound_tailForm`** (`lem:oct24-collision`): the same bound for the soft
collision operator `T^D_coll` (`|D_e| ≤ 1`; `χ(-1) = -1` if some `D_e < 0`). -/
theorem sk_soft_collision_opBound_tailForm (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (ord : U → U → U → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (π : ℕ → U → ℕ) (hπ : ∀ k, Function.Injective (π k))
    (D : U × U → ℝ) (hD : ∀ e, |D e| ≤ 1) (hneg : ∀ e, D e < 0 → quadraticChar F (-1) = -1) {k₀ : ℕ} (h2 : 2 ≤ k₀)
    (hk₀ : collisionDeltaPlus G ≤ k₀) (hΞ : collisionXi G ς (Fintype.card F) < k₀ + 1) :
    Sarkozy.Influence.OpBound (injLabellings F G) (injLabellings F G)
      (fun x x' => skCollKerColl ς D x x' / (injLabellings F G).card)
      (collisionD1 G ς ord (Fintype.card F) n +
        ((collisionLint G (Fintype.card F) n)⁻¹ * ∑ k ∈ Ico 2 k₀,
          collisionUpsK G ς π (Fintype.card F) n k *
            (collisionXi G ς (Fintype.card F) ^ k / (k.factorial : ℝ)) +
        collisionUps G ς (Fintype.card F) n / collisionLint G (Fintype.card F) n *
          (collisionXi G ς (Fintype.card F) ^ k₀ / (k₀.factorial : ℝ)) *
            (1 - collisionXi G ς (Fintype.card F) / (k₀ + 1))⁻¹)) := by
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  refine (sk_soft_collision_opBound_sum hW G ς hς hanti hne hn hS1 ord hord π hπ D hD hneg).mono
    (add_nonneg (collisionD1_nonneg G ς ord hq0 hS1) (collisionD2_nonneg G ς π hq0 hS1)) ?_
  linarith [collisionD2_le_tail G ς π hq0 hS1 h2 hk₀ hΞ]

end SkColl3

end Sarkozy.ExtractionK
