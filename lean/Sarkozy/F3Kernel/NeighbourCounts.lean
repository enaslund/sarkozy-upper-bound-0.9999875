module

public import Sarkozy.F3Kernel.WitnessExponent
public import Sarkozy.F3Kernel.OrderAgreement

/-!
# Count lanes as cardinalities of graph neighbourhoods

The list sums in the accumulator are graph-theoretic neighbour counts. A prefix of a
distinct scan is exactly the set of vertices earlier in that scan.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset

def listVertices (s : List ℕ) : Finset (Fin 36) := univ.filter fun v => v.val ∈ s

@[simp] theorem mem_listVertices (s : List ℕ) (v : Fin 36) :
    v ∈ listVertices s ↔ v.val ∈ s := by simp [listVertices]

@[simp] theorem listVertices_nil : listVertices [] = ∅ := by ext v; simp

theorem listVertices_cons (u : Fin 36) (s : List ℕ) :
    listVertices (u.val :: s) = insert u (listVertices s) := by
  ext v
  simp [Fin.ext_iff]

theorem sumVertices_eq_sum (f : Fin 36 → ℕ) {s : List ℕ} (hn : s.Nodup)
    (hs : ∀ u ∈ s, u < 36) : sumVertices f s = ∑ v ∈ listVertices s, f v := by
  induction s with
  | nil => simp [sumVertices]
  | cons u s ih =>
      obtain ⟨hu, hn⟩ := List.nodup_cons.mp hn
      let v : Fin 36 := ⟨u, hs u List.mem_cons_self⟩
      have hv : v ∉ listVertices s := by simpa using hu
      rw [show u = v.val from rfl, listVertices_cons, sum_insert hv]
      change vertexValue f v.val + sumVertices f s = _
      rw [vertexValue_fin, ih hn (fun a ha => hs a (List.mem_cons_of_mem _ ha))]

theorem listVertices_take_idxOf {s : List ℕ} (a : Fin 36) :
    listVertices (s.take (s.idxOf a.val)) =
      (listVertices s).filter (fun v => s.idxOf v.val < s.idxOf a.val) := by
  ext v
  simp only [mem_listVertices, mem_filter]
  constructor
  · intro h
    have hv := List.mem_of_mem_take h
    exact ⟨hv, (List.mem_take_iff_idxOf_lt hv).mp h⟩
  · rintro ⟨hv, hlt⟩
    exact (List.mem_take_iff_idxOf_lt hv).mpr hlt

variable (E : Fin 36 → Fin 36 → Prop) [DecidableRel E]

theorem neighbourSum_eq_card {s : List ℕ} (hn : s.Nodup)
    (hs : ∀ u ∈ s, u < 36) (v : Fin 36) :
    neighbourSum E s v = ((listVertices s).filter (fun u => E u v)).card := by
  change sumVertices (fun u => if E u v then 1 else 0) s = _
  rw [sumVertices_eq_sum _ hn hs]
  simp

theorem signature_countState_eq_card {h : Fin 36 → ℕ} (hh : ∀ v, h v ≤ 36)
    {s : List ℕ} (hlen : s.length ≤ 36) (hn : s.Nodup)
    (hs : ∀ u ∈ s, u < 36) (v : Fin 36) :
    signature (packCounts (countState E h s)) v =
      h v + ((listVertices s).filter (fun u => E u v)).card := by
  rw [signature_countState E hh hlen, neighbourSum_eq_card E hn hs]

theorem neighbourSum_take_idxOf {s : List ℕ} (hn : s.Nodup)
    (hs : ∀ u ∈ s, u < 36) (a v : Fin 36) :
    neighbourSum E (s.take (s.idxOf a.val)) v =
      ((listVertices s).filter (fun u => s.idxOf u.val < s.idxOf a.val ∧ E u v)).card := by
  rw [neighbourSum_eq_card E hn.take (fun u hu => hs u (List.mem_of_mem_take hu)),
    listVertices_take_idxOf, filter_filter]

end Sarkozy.F3Kernel
