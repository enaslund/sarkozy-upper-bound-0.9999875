module

public import Sarkozy.F3Kernel.CountProducts
public import Sarkozy.F3Kernel.NeighbourCounts

/-!
# Scan products as products over vertex sets

For a scan without repetitions, the state at a vertex is the initial prefix followed by
exactly the vertices earlier in the scan. This identifies recursive products with finite
products over the decoded vertex set.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset

theorem prod_map_listVertices (f : ℕ → ℝ) {s : List ℕ} (hn : s.Nodup)
    (hs : ∀ u ∈ s, u < 36) : (s.map f).prod = ∏ v ∈ listVertices s, f v := by
  induction s with
  | nil => simp
  | cons u s ih =>
      obtain ⟨hu, hn⟩ := List.nodup_cons.mp hn
      let v : Fin 36 := ⟨u, hs u List.mem_cons_self⟩
      have hv : v ∉ listVertices s := by simpa using hu
      rw [show u = v.val from rfl, listVertices_cons, prod_insert hv,
        List.map_cons, List.prod_cons, ih hn (fun a ha => hs a (List.mem_cons_of_mem _ ha))]

variable (E : Fin 36 → Fin 36 → Prop) [DecidableRel E]

theorem countProd_eq_map (f : ℕ → ℝ) (h : Fin 36 → ℕ)
    (p : List ℕ) {s : List ℕ} (hn : s.Nodup) :
    countProd E f h p s =
      (s.map (fun u => f (vertexValue (countState E h (p ++ s.take (s.idxOf u))) u))).prod := by
  induction s generalizing p with
  | nil => rfl
  | cons u s ih =>
      obtain ⟨hu, hn⟩ := List.nodup_cons.mp hn
      rw [countProd, ih _ hn, List.map_cons, List.prod_cons, List.idxOf_cons_self,
        List.take_zero, List.append_nil]
      congr 1
      apply congrArg List.prod
      apply List.map_congr_left
      intro v hv
      have huv : u ≠ v := fun he => hu (he ▸ hv)
      rw [List.idxOf_cons_ne s huv, List.take_succ_cons]
      simp only [List.append_assoc, List.singleton_append]

theorem countProd_eq_finset (f : ℕ → ℝ) (h : Fin 36 → ℕ)
    (p : List ℕ) {s : List ℕ} (hn : s.Nodup) (hs : ∀ u ∈ s, u < 36) :
    countProd E f h p s = ∏ v ∈ listVertices s,
      f (h v + neighbourSum E (p ++ s.take (s.idxOf v.val)) v) := by
  rw [countProd_eq_map E f h p hn, prod_map_listVertices _ hn hs]
  apply prod_congr rfl
  intro v _
  rw [vertexValue_fin]
  rfl

end Sarkozy.F3Kernel
