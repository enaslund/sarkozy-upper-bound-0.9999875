module

public import Sarkozy.SpectralD.StarMatrix

@[expose] public section

/-!
# The complete star part inside the expansion of the soft kernel (`cor:star-matrix`)

`paper/sections/14_spectral.tex`, `cor:star-matrix`. The soft cross kernel
`K_D(x, y) = ∏_{i,j ∈ U} (1 + D_ij χ(y_j − x_i))` (`softKer`) expands as
`∑_{E ⊆ U × U} ∏_{(i,j) ∈ E} D_ij χ(y_j − x_i)` (`softKer_expand`). The *complete star part* is
the sum of the terms of the sets `E` that are single pairs `{(i, j)}`, left stars `{i} × S` and
right stars `S × {j}` with `|S| ≥ 2` (`starSets`). These three families are pairwise disjoint and
each is parametrized injectively, so this sub-sum is `softStarPart D`, the kernel treated in
`Sarkozy.SpectralD.StarMatrix` (`softStarPart_eq_sum_starSets`).

New material for this paper.
-/

namespace Sarkozy.SpectralD.StarMatrix

open Finset Sarkozy.SpectralC
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

/-- The soft cross kernel `K_D(x, y) = ∏_{i,j ∈ U} (1 + D_ij χ(y_j − x_i))`. -/
noncomputable def softKer (D : U → U → ℝ) (x y : U → ZMod p) : ℝ :=
  ∏ e : U × U, (1 + D e.1 e.2 * chiRe (y e.2 - x e.1))

/-- The term of a set `E` of cross pairs in the expansion: `∏_{(i,j) ∈ E} D_ij χ(y_j − x_i)`. -/
noncomputable def expTerm (D : U → U → ℝ) (E : Finset (U × U)) (x y : U → ZMod p) : ℝ :=
  ∏ e ∈ E, D e.1 e.2 * chiRe (y e.2 - x e.1)

omit [DecidableEq U] in
/-- The expansion `K_D(x, y) = ∑_{E ⊆ U × U} ∏_{(i,j) ∈ E} D_ij χ(y_j − x_i)`. -/
theorem softKer_expand (D : U → U → ℝ) (x y : U → ZMod p) :
    softKer D x y = ∑ E ∈ (univ : Finset (U × U)).powerset, expTerm D E x y :=
  prod_one_add univ

/-- The left star `{i} × S`. -/
def leftStar (i : U) (S : Finset U) : Finset (U × U) := S.image (fun j => (i, j))

/-- The right star `S × {j}`. -/
def rightStar (S : Finset U) (j : U) : Finset (U × U) := S.image (fun i => (i, j))

/-- The single pairs `{(i, j)}`. -/
def pairSets (U : Type*) [Fintype U] [DecidableEq U] : Finset (Finset (U × U)) :=
  univ.image (fun e : U × U => {e})

/-- The left stars `{i} × S`, `|S| ≥ 2`. -/
def leftSets (U : Type*) [Fintype U] [DecidableEq U] : Finset (Finset (U × U)) :=
  (univ ×ˢ supports U).image (fun q => leftStar q.1 q.2)

/-- The right stars `S × {j}`, `|S| ≥ 2`. -/
def rightSets (U : Type*) [Fintype U] [DecidableEq U] : Finset (Finset (U × U)) :=
  (supports U ×ˢ univ).image (fun q => rightStar q.1 q.2)

/-- **The sets of cross pairs of the complete star part** (`cor:star-matrix`). -/
def starSets (U : Type*) [Fintype U] [DecidableEq U] : Finset (Finset (U × U)) :=
  pairSets U ∪ leftSets U ∪ rightSets U

lemma mem_supports {S : Finset U} : S ∈ supports U ↔ 2 ≤ S.card := by
  unfold supports
  simp

omit [Fintype U] in
lemma card_leftStar (i : U) (S : Finset U) : (leftStar i S).card = S.card :=
  card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)

omit [Fintype U] in
lemma card_rightStar (S : Finset U) (j : U) : (rightStar S j).card = S.card :=
  card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)

lemma leftStar_injOn :
    Set.InjOn (fun q : U × Finset U => leftStar q.1 q.2)
      ((univ ×ˢ supports U : Finset (U × Finset U)) : Set (U × Finset U)) := by
  rintro ⟨i, S⟩ hq ⟨i', S'⟩ hq' h
  simp only [coe_product, coe_univ, Set.mem_prod, Set.mem_univ, mem_coe, mem_supports,
    true_and] at hq hq'
  dsimp only at h
  obtain ⟨j, hj⟩ : S.Nonempty := card_pos.mp (by omega)
  have hmem : (i, j) ∈ leftStar i' S' := by
    rw [← h]; exact mem_image.mpr ⟨j, hj, rfl⟩
  obtain ⟨j', _, hj'⟩ := mem_image.mp hmem
  have hii : i = i' := (Prod.mk.inj hj').1.symm
  subst hii
  have hS : S = S' := by
    ext k
    constructor
    · intro hk
      have : (i, k) ∈ leftStar i S' := by rw [← h]; exact mem_image.mpr ⟨k, hk, rfl⟩
      obtain ⟨k', hk', e⟩ := mem_image.mp this
      rw [← (Prod.mk.inj e).2]; exact hk'
    · intro hk
      have : (i, k) ∈ leftStar i S := by rw [h]; exact mem_image.mpr ⟨k, hk, rfl⟩
      obtain ⟨k', hk', e⟩ := mem_image.mp this
      rw [← (Prod.mk.inj e).2]; exact hk'
  rw [hS]

lemma rightStar_injOn :
    Set.InjOn (fun q : Finset U × U => rightStar q.1 q.2)
      ((supports U ×ˢ univ : Finset (Finset U × U)) : Set (Finset U × U)) := by
  rintro ⟨S, j⟩ hq ⟨S', j'⟩ hq' h
  simp only [coe_product, coe_univ, Set.mem_prod, Set.mem_univ, mem_coe, mem_supports,
    and_true] at hq hq'
  dsimp only at h
  obtain ⟨i, hi⟩ : S.Nonempty := card_pos.mp (by omega)
  have hmem : (i, j) ∈ rightStar S' j' := by
    rw [← h]; exact mem_image.mpr ⟨i, hi, rfl⟩
  obtain ⟨i', _, hi'⟩ := mem_image.mp hmem
  have hjj : j = j' := (Prod.mk.inj hi').2.symm
  subst hjj
  have hS : S = S' := by
    ext k
    constructor
    · intro hk
      have : (k, j) ∈ rightStar S' j := by rw [← h]; exact mem_image.mpr ⟨k, hk, rfl⟩
      obtain ⟨k', hk', e⟩ := mem_image.mp this
      rw [← (Prod.mk.inj e).1]; exact hk'
    · intro hk
      have : (k, j) ∈ rightStar S j := by rw [h]; exact mem_image.mpr ⟨k, hk, rfl⟩
      obtain ⟨k', hk', e⟩ := mem_image.mp this
      rw [← (Prod.mk.inj e).1]; exact hk'
  rw [hS]

lemma disjoint_pair_left : Disjoint (pairSets U) (leftSets U) := by
  rw [disjoint_left]
  intro E hE hE'
  obtain ⟨e, _, rfl⟩ := mem_image.mp hE
  obtain ⟨⟨i, S⟩, hq, h⟩ := mem_image.mp hE'
  simp only [mem_product, mem_univ, mem_supports, true_and] at hq
  dsimp only at h
  have := congrArg card h
  rw [card_leftStar, card_singleton] at this
  omega

lemma disjoint_pairLeft_right : Disjoint (pairSets U ∪ leftSets U) (rightSets U) := by
  rw [disjoint_left]
  intro E hE hE'
  obtain ⟨⟨S, j⟩, hq, h⟩ := mem_image.mp hE'
  simp only [mem_product, mem_univ, mem_supports, and_true] at hq
  rcases mem_union.mp hE with hE1 | hE1
  · obtain ⟨e, _, rfl⟩ := mem_image.mp hE1
    dsimp only at h
    have := congrArg card h
    rw [card_rightStar, card_singleton] at this
    omega
  · obtain ⟨⟨i, T⟩, hq', h'⟩ := mem_image.mp hE1
    simp only [mem_product, mem_univ, mem_supports, true_and] at hq'
    dsimp only at h h'
    -- `{i} × T = S × {j}` with `|T| ≥ 2`: two distinct second coordinates, a contradiction
    obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (by omega : 1 < T.card)
    have hma : (i, a) ∈ rightStar S j := by
      rw [h, ← h']; exact mem_image.mpr ⟨a, ha, rfl⟩
    have hmb : (i, b) ∈ rightStar S j := by
      rw [h, ← h']; exact mem_image.mpr ⟨b, hb, rfl⟩
    obtain ⟨_, _, ea⟩ := mem_image.mp hma
    obtain ⟨_, _, eb⟩ := mem_image.mp hmb
    exact hab ((Prod.mk.inj ea).2.symm.trans (Prod.mk.inj eb).2)

omit [Fintype U] in
lemma expTerm_leftStar (D : U → U → ℝ) (i : U) (S : Finset U) (x y : U → ZMod p) :
    expTerm D (leftStar i S) x y = (∏ j ∈ S, D i j) * ∏ j ∈ S, chiRe (y j - x i) := by
  unfold expTerm leftStar
  rw [prod_image (fun a _ b _ h => (Prod.mk.inj h).2), ← prod_mul_distrib]

omit [Fintype U] in
lemma expTerm_rightStar (D : U → U → ℝ) (S : Finset U) (j : U) (x y : U → ZMod p) :
    expTerm D (rightStar S j) x y = (∏ i ∈ S, D i j) * ∏ i ∈ S, chiRe (y j - x i) := by
  unfold expTerm rightStar
  rw [prod_image (fun a _ b _ h => (Prod.mk.inj h).1), ← prod_mul_distrib]

/-- **The complete star part is the sub-sum of the expansion of `K_D` over the single pairs, the
left stars and the right stars** (`cor:star-matrix`): `softStarPart D = ∑_{E ∈ starSets} ∏_E`,
each term once. -/
theorem softStarPart_eq_sum_starSets (D : U → U → ℝ) (x y : U → ZMod p) :
    softStarPart D x y = ∑ E ∈ starSets U, expTerm D E x y := by
  unfold starSets
  rw [sum_union disjoint_pairLeft_right, sum_union disjoint_pair_left]
  unfold pairSets leftSets rightSets
  rw [sum_image (fun e _ e' _ h => singleton_injective h), sum_image leftStar_injOn,
    sum_image rightStar_injOn, sum_product, sum_product]
  unfold softStarPart starPart
  congr 1
  congr 1
  · rw [← univ_product_univ, sum_product]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    unfold expTerm
    rw [prod_singleton]
  · exact sum_congr rfl fun i _ => sum_congr rfl fun S _ => (expTerm_leftStar D i S x y).symm
  · exact sum_congr rfl fun S _ => sum_congr rfl fun j _ => (expTerm_rightStar D S j x y).symm

/-- The star sets are sets of cross pairs, so `∑_{E ∈ starSets}` is a sub-sum of the expansion
`softKer_expand`. -/
lemma starSets_subset_powerset : starSets U ⊆ (univ : Finset (U × U)).powerset :=
  fun E _ => mem_powerset.mpr (subset_univ E)

end Sarkozy.SpectralD.StarMatrix
