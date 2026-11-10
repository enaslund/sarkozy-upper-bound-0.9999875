module

public import Sarkozy.JointRows.StarBridge
public import Sarkozy.JointRows.StarScalarBound

/-!
# Star expansion at both prime classes

The real edge coefficient is chi(sign). This equals the oriented sign
in class three and the unsigned adjacency in class one. Keeping this
coefficient explicit makes the star dictionary valid in both classes.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows.StarOps

open Sarkozy.JointRows.PaleyGauss

variable {p : ℕ} [Fact p.Prime] {nv : ℕ}

noncomputable def characterSigns (ς : Fin nv → Fin nv → ℤ) (i j : Fin nv) : ℝ :=
  chiR p (ς i j : ZMod p)

theorem starKer_eq_characterStar (ς : Fin nv → Fin nv → ℤ) (x y : Fin nv → ZMod p) :
    Coll.starKer ς x y = starKernel (characterSigns (p := p) ς) (sets2 (Fin nv)) x y := by
  set c : Fin nv × Fin nv → ℝ :=
    fun e => characterSigns (p := p) ς e.1 e.2 * chiR p (y e.2 - x e.1) with hc
  -- the star subsets of `E_×`, with `χ_e = c e`
  have hA : Coll.starKer ς x y = ∑ S ∈ Coll.starSets ς, ∏ e ∈ S, c e := by
    unfold Coll.starKer
    exact Finset.sum_congr rfl fun S _ => Finset.prod_congr rfl fun e _ =>
      (by
        dsimp only [c]
        unfold ExtractionK.chiPair characterSigns chiR
        rw [map_mul]
        push_cast
        rfl)
  -- extend to all star sets: a set leaving `E_×` has a factor `c e = 0`
  have hB : ∑ S ∈ Coll.starSets ς, ∏ e ∈ S, c e =
      ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin nv × Fin nv) => Extraction.IsStar S),
        ∏ e ∈ S, c e := by
    apply Finset.sum_subset
    · intro S hS
      simp only [Coll.starSets, Finset.mem_filter, Finset.mem_powerset] at hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hS.2
    · intro S hS hS'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
      simp only [Coll.starSets, Finset.mem_filter, Finset.mem_powerset, not_and] at hS'
      have hsub : ¬ S ⊆ Coll.pairSet ς := fun h => hS' h hS
      obtain ⟨e, he, he'⟩ := Finset.not_subset.mp hsub
      apply Finset.prod_eq_zero he
      simp only [Coll.pairSet, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at he'
      simp only [hc, he', characterSigns, Int.cast_zero, chiR_zero, zero_mul]
  -- split the stars
  have hC : ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin nv × Fin nv) => Extraction.IsStar S),
      ∏ e ∈ S, c e =
      (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin nv × Fin nv) => S.card = 1), ∏ e ∈ S, c e) +
      (∑ S ∈ Finset.univ.filter
        (fun S : Finset (Fin nv × Fin nv) => Extraction.IsRowStar S ∧ 2 ≤ S.card), ∏ e ∈ S, c e) +
      ∑ S ∈ Finset.univ.filter
        (fun S : Finset (Fin nv × Fin nv) => Extraction.IsColStar S ∧ 2 ≤ S.card),
          ∏ e ∈ S, c e := by
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun S _ => star_indicator S _
  -- the three classes
  have h1 : ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin nv × Fin nv) => S.card = 1),
      ∏ e ∈ S, c e = ∑ i, ∑ j, characterSigns (p := p) ς i j * chiR p (y j - x i) := by
    rw [show Finset.univ.filter (fun S : Finset (Fin nv × Fin nv) => S.card = 1) =
        Finset.powersetCard 1 Finset.univ by
      rw [Finset.powersetCard_eq_filter, Finset.powerset_univ], Finset.powersetCard_one,
      Finset.sum_map]
    simp only [Function.Embedding.coeFn_mk, Finset.prod_singleton]
    rw [← Finset.univ_product_univ, Finset.sum_product]
  have h2 : ∑ S ∈ Finset.univ.filter
      (fun S : Finset (Fin nv × Fin nv) => Extraction.IsRowStar S ∧ 2 ≤ S.card), ∏ e ∈ S, c e =
      ∑ i, ∑ T ∈ sets2 (Fin nv), ∏ j ∈ T, (characterSigns (p := p) ς i j * chiR p (y j - x i)) := by
    rw [rowStar_filter_eq, Finset.sum_image rowMap_injOn, Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun T _ => ?_
    unfold rowMap
    rw [Finset.prod_image fun j _ j' _ h => (Prod.mk.inj h).2]
  have h3 : ∑ S ∈ Finset.univ.filter
      (fun S : Finset (Fin nv × Fin nv) => Extraction.IsColStar S ∧ 2 ≤ S.card), ∏ e ∈ S, c e =
      ∑ j, ∑ S ∈ sets2 (Fin nv), ∏ i ∈ S, (characterSigns (p := p) ς i j * chiR p (y j - x i)) := by
    rw [colStar_filter_eq, Finset.sum_image colMap_injOn, Finset.sum_product]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun S _ => ?_
    unfold colMap
    rw [Finset.prod_image fun i _ i' _ h => (Prod.mk.inj h).1]
  rw [hA, hB, hC, h1, h2, h3]
  rfl

end Sarkozy.JointRows.StarOps
