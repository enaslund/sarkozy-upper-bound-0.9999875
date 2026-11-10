module

public import Sarkozy.F3Kernel.ConcreteNonstarBound
public import Sarkozy.Cuts.CutTransport

/-!
# Transporting nonstar kernels through vertex equivalences
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Labellings Sarkozy.Extraction Sarkozy.ExtractionK

variable {U V : Type*} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]

omit [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V] in
theorem pairDisj_equiv (e : U ≃ V) (a b : U × U) :
    PairDisj ((e.prodCongr e) a) ((e.prodCongr e) b) ↔ PairDisj a b := by
  change (e a.1 ≠ e b.1 ∧ e a.2 ≠ e b.2) ↔ (a.1 ≠ b.1 ∧ a.2 ≠ b.2)
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun h => h1 (congrArg e h), fun h => h2 (congrArg e h)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun h => h1 (e.injective h), fun h => h2 (e.injective h)⟩

omit [Fintype U] [Fintype V] in
theorem isNonstar_map_equiv (e : U ≃ V) (S : Finset (U × U)) :
    IsNonstar (S.map (e.prodCongr e).toEmbedding) ↔ IsNonstar S := by
  rw [isNonstar_iff, isNonstar_iff]
  constructor
  · rintro ⟨a, ha, b, hb, hd⟩
    obtain ⟨a, ha', rfl⟩ := mem_map.mp ha
    obtain ⟨b, hb', rfl⟩ := mem_map.mp hb
    exact ⟨a, ha', b, hb', (pairDisj_equiv e a b).mp hd⟩
  · rintro ⟨a, ha, b, hb, hd⟩
    exact ⟨_, mem_map.mpr ⟨a, ha, rfl⟩, _, mem_map.mpr ⟨b, hb, rfl⟩,
      (pairDisj_equiv e a b).mpr hd⟩

omit [Fintype U] [Fintype V] in
theorem nonstars_map_equiv (e : U ≃ V) (Ex : Finset (U × U)) :
    nonstars (Ex.map (e.prodCongr e).toEmbedding) =
      (nonstars Ex).map (e.prodCongr e).finsetCongr.toEmbedding := by
  apply Finset.ext
  intro S
  obtain ⟨S, rfl⟩ := (e.prodCongr e).finsetCongr.surjective S
  rw [mem_map, mem_nonstars, Equiv.finsetCongr_apply, map_subset_map,
    isNonstar_map_equiv]
  constructor
  · intro h
    exact ⟨S, mem_nonstars.mpr h, rfl⟩
  · rintro ⟨T, hT, he⟩
    have he' : T = S := (e.prodCongr e).finsetCongr.injective he
    subst T
    exact mem_nonstars.mp hT

omit [Fintype U] [Fintype V] in
theorem nonstar_kernel_equiv {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (e : U ≃ V) (Ex : Finset (U × U)) (sgn : U → U → ℤ) (sgn' : V → V → ℤ)
    (hs : ∀ i j, sgn' (e i) (e j) = sgn i j) (x y : V → F) :
    (∑ S ∈ nonstars (Ex.map (e.prodCongr e).toEmbedding),
      ∏ a ∈ S, chiPair sgn' a x y) =
    ∑ S ∈ nonstars Ex, ∏ a ∈ S, chiPair sgn a (x ∘ e) (y ∘ e) := by
  rw [nonstars_map_equiv, sum_map]
  apply sum_congr rfl
  intro S _
  rw [Equiv.coe_toEmbedding, Equiv.finsetCongr_apply, prod_map]
  apply prod_congr rfl
  intro a _
  simp only [chiPair, Equiv.coe_toEmbedding, Equiv.prodCongr_apply, Prod.map, hs,
    Function.comp_apply]

theorem nonstar_form_equiv {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (H : OrientedGraph U) (H' : OrientedGraph V) (e : U ≃ V)
    (he : ∀ u v, (u, v) ∈ H.E ↔ (e u, e v) ∈ H'.E)
    (hne : (injLabellings F H).Nonempty) (hne' : (injLabellings F H').Nonempty)
    (Ex : Finset (U × U)) (sgn : U → U → ℤ) (sgn' : V → V → ℤ)
    (hs : ∀ i j, sgn' (e i) (e j) = sgn i j) (f h : (V → F) → ℝ) :
    (graphLaw H' hne').expect (fun x => f x * (graphLaw H' hne').expect (fun y =>
      (∑ S ∈ nonstars (Ex.map (e.prodCongr e).toEmbedding),
        ∏ a ∈ S, chiPair sgn' a x y) * h y)) =
    (graphLaw H hne).expect (fun x => f (x ∘ e.symm) *
      (graphLaw H hne).expect (fun y =>
        (∑ S ∈ nonstars Ex, ∏ a ∈ S, chiPair sgn a x y) * h (y ∘ e.symm))) := by
  rw [Cuts.graphLaw_iso H H' e he hne hne']
  apply FiniteLaw.expect_congr
  intro x
  congr 1
  rw [Cuts.graphLaw_iso H H' e he hne hne']
  apply FiniteLaw.expect_congr
  intro y
  rw [nonstar_kernel_equiv e Ex sgn sgn' hs]
  simp only [Function.comp_def, Equiv.symm_apply_apply]

theorem nonstar_bound_equiv {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (H : OrientedGraph U) (H' : OrientedGraph V) (e : U ≃ V)
    (he : ∀ u v, (u, v) ∈ H.E ↔ (e u, e v) ∈ H'.E)
    (hne : (injLabellings F H).Nonempty) (hne' : (injLabellings F H').Nonempty)
    (Ex : Finset (U × U)) (sgn : U → U → ℤ) (sgn' : V → V → ℤ)
    (hs : ∀ i j, sgn' (e i) (e j) = sgn i j) {B : ℝ}
    (hB : ∀ f h : (U → F) → ℝ,
      |(graphLaw H hne).expect (fun x => f x * (graphLaw H hne).expect (fun y =>
        (∑ S ∈ nonstars Ex, ∏ a ∈ S, chiPair sgn a x y) * h y))| ≤
      B * Real.sqrt ((graphLaw H hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw H hne).expect (fun x => h x ^ 2))) (f h : (V → F) → ℝ) :
    |(graphLaw H' hne').expect (fun x => f x * (graphLaw H' hne').expect (fun y =>
      (∑ S ∈ nonstars (Ex.map (e.prodCongr e).toEmbedding),
        ∏ a ∈ S, chiPair sgn' a x y) * h y))| ≤
      B * Real.sqrt ((graphLaw H' hne').expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw H' hne').expect (fun x => h x ^ 2)) := by
  rw [nonstar_form_equiv H H' e he hne hne' Ex sgn sgn' hs]
  have hb := hB (fun x => f (x ∘ e.symm)) (fun x => h (x ∘ e.symm))
  rw [Cuts.graphLaw_iso H H' e he hne hne' (fun x => f x ^ 2),
    Cuts.graphLaw_iso H H' e he hne hne' (fun x => h x ^ 2)]
  exact hb

end Sarkozy.F3Kernel
