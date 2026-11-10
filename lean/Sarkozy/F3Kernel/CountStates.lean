module

public import Sarkozy.F3Kernel.LaneCounts

/-!
# The graph meaning of count accumulators

The initial free-degree vector plus the neighbourhoods of already labelled vertices is
exactly the integer accumulator read by the checker. At most 36 initial free partners and
36 labelled vertices give a uniform bound of 72, so seven-bit extraction cannot overflow.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

variable (E : Fin 36 → Fin 36 → Prop) [DecidableRel E]

def neighbourSum (s : List ℕ) (v : Fin 36) : ℕ :=
  (s.map (fun u => neighbourCount E u v)).sum

def countState (h : Fin 36 → ℕ) (s : List ℕ) (v : Fin 36) : ℕ :=
  h v + neighbourSum E s v

theorem neighbourSum_nil (v : Fin 36) : neighbourSum E [] v = 0 := rfl

theorem neighbourSum_cons (u : ℕ) (s : List ℕ) (v : Fin 36) :
    neighbourSum E (u :: s) v = neighbourCount E u v + neighbourSum E s v := rfl

theorem neighbourSum_append (s t : List ℕ) (v : Fin 36) :
    neighbourSum E (s ++ t) v = neighbourSum E s v + neighbourSum E t v := by
  simp only [neighbourSum, List.map_append, List.sum_append]

theorem neighbourSum_le_length (s : List ℕ) (v : Fin 36) :
    neighbourSum E s v ≤ s.length := by
  induction s with
  | nil => rfl
  | cons u s ih =>
      rw [neighbourSum_cons, List.length_cons]
      have := neighbourCount_le_one E u v
      omega

theorem countState_nil (h : Fin 36 → ℕ) : countState E h [] = h := by
  funext v
  exact Nat.add_zero _

theorem countState_append (h : Fin 36 → ℕ) (s t : List ℕ) :
    countState E h (s ++ t) = countState E (countState E h s) t := by
  funext v
  simp only [countState, neighbourSum_append, Nat.add_assoc]

theorem countState_snoc (h : Fin 36 → ℕ) (s : List ℕ) (u : ℕ) :
    countState E h (s ++ [u]) = fun v => countState E h s v + neighbourCount E u v := by
  funext v
  simp only [countState, neighbourSum_append, neighbourSum_cons, neighbourSum_nil,
    Nat.add_zero, Nat.add_assoc]

theorem countState_le (h : Fin 36 → ℕ) (s : List ℕ) (v : Fin 36) :
    countState E h s v ≤ h v + s.length :=
  Nat.add_le_add_left (neighbourSum_le_length E s v) _

theorem countState_lt_128 {h : Fin 36 → ℕ} (hh : ∀ v, h v ≤ 36)
    {s : List ℕ} (hs : s.length ≤ 36) (v : Fin 36) : countState E h s v < 128 := by
  have := countState_le E h s v
  have := hh v
  omega

theorem signature_countState {h : Fin 36 → ℕ} (hh : ∀ v, h v ≤ 36)
    {s : List ℕ} (hs : s.length ≤ 36) (v : Fin 36) :
    signature (packCounts (countState E h s)) v = h v + neighbourSum E s v :=
  signature_packCounts _ (countState_lt_128 E hh hs) v

theorem packCounts_countState (h : Fin 36 → ℕ) (s : List ℕ) :
    packCounts (countState E h s) =
      packCounts h + (s.map (fun u => packCounts (neighbourCount E u))).sum := by
  unfold countState neighbourSum
  rw [packCounts_add, packCounts_list_sum]

theorem adjacency_list_sum {G : Consts} (hG : AdjacencyCounts G E)
    {s : List ℕ} (hs : ∀ u ∈ s, u < 36) :
    (s.map (adj64 G)).sum = packCounts (neighbourSum E s) := by
  unfold neighbourSum
  rw [packCounts_list_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro u hu
  exact hG ⟨u, hs u hu⟩

theorem adjSum_counts {G : Consts} (hG : AdjacencyCounts G E) {k wl : ℕ}
    (hw : ∀ u ∈ packedList k wl, u < 36) :
    adjSum G k wl = packCounts (neighbourSum E (packedList k wl)) := by
  rw [adjSum_eq_list_sum]
  exact adjacency_list_sum E hG hw

theorem add_adj64_countState {G : Consts} (hG : AdjacencyCounts G E)
    (h : Fin 36 → ℕ) (s : List ℕ) (u : Fin 36) :
    packCounts (countState E h s) + adj64 G u =
      packCounts (countState E h (s ++ [u.val])) := by
  rw [countState_snoc, packCounts_add, hG]

theorem add_adjSum_countState {G : Consts} (hG : AdjacencyCounts G E)
    (h : Fin 36 → ℕ) (s : List ℕ) {k wl : ℕ}
    (hw : ∀ u ∈ packedList k wl, u < 36) :
    packCounts (countState E h s) + adjSum G k wl =
      packCounts (countState E h (s ++ packedList k wl)) := by
  rw [adjSum_counts E hG hw, countState_append]
  exact (packCounts_add _ _).symm

theorem witSwitch_counts {G : Consts} (hG : AdjacencyCounts G E)
    (h : Fin 36 → ℕ) (s : List ℕ) {k wl : ℕ}
    (hw : ∀ u ∈ packedList k wl, u < 36) (base : ℕ) :
    (witSwitch G k wl base (packCounts (countState E h s))).2 =
      packCounts (countState E h (s ++ packedList k wl)) :=
  add_adjSum_countState E hG h s hw

end Sarkozy.F3Kernel
