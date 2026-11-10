module

public import Sarkozy.F3Kernel.CountStates

/-!
# The arithmetic of the witness exponent

At the witness switch, subtracting the initial free-degree sum leaves the number of
adjacencies to the already labelled cover. The difference after labelling the witness
is its internal adjacency sum; the checker divides this double count by two.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

def vertexValue (f : Fin 36 → ℕ) (u : ℕ) : ℕ := if hu : u < 36 then f ⟨u, hu⟩ else 0

theorem vertexValue_fin (f : Fin 36 → ℕ) (u : Fin 36) : vertexValue f u = f u := by
  simp [vertexValue, u.isLt]

theorem vertexValue_add (f g : Fin 36 → ℕ) (u : ℕ) :
    vertexValue (fun v => f v + g v) u = vertexValue f u + vertexValue g u := by
  unfold vertexValue
  split <;> simp

def sumVertices (f : Fin 36 → ℕ) (s : List ℕ) : ℕ := (s.map (vertexValue f)).sum

theorem sumVertices_add (f g : Fin 36 → ℕ) (s : List ℕ) :
    sumVertices (fun v => f v + g v) s = sumVertices f s + sumVertices g s := by
  unfold sumVertices
  rw [show vertexValue (fun v => f v + g v) =
    fun u => vertexValue f u + vertexValue g u from funext (vertexValue_add f g)]
  exact List.sum_map_add

theorem hSum_packCounts (f : Fin 36 → ℕ) (hf : ∀ v, f v < 128) {k wl : ℕ}
    (hw : ∀ u ∈ packedList k wl, u < 36) :
    hSum (packCounts f) k wl = sumVertices f (packedList k wl) := by
  rw [hSum_eq_list_sum, sumVertices]
  apply congrArg List.sum
  apply List.map_congr_left
  intro u hu
  exact (signature_packCounts f hf ⟨u, hw u hu⟩).trans
    (vertexValue_fin f ⟨u, hw u hu⟩).symm

variable (E : Fin 36 → Fin 36 → Prop) [DecidableRel E]

theorem sumVertices_countState (h : Fin 36 → ℕ) (s w : List ℕ) :
    sumVertices (countState E h s) w =
      sumVertices h w + sumVertices (neighbourSum E s) w :=
  sumVertices_add _ _ _

theorem hSum_countState {h : Fin 36 → ℕ} (hh : ∀ v, h v ≤ 36)
    {s : List ℕ} (hs : s.length ≤ 36) {k wl : ℕ}
    (hw : ∀ u ∈ packedList k wl, u < 36) :
    hSum (packCounts (countState E h s)) k wl =
      sumVertices h (packedList k wl) +
        sumVertices (neighbourSum E s) (packedList k wl) := by
  rw [hSum_packCounts _ (countState_lt_128 E hh hs) hw, sumVertices_countState]

/-- The checker's exact exponent contribution, with both truncated subtractions cancelled. -/
theorem witSwitch_exponent {G : Consts} (hG : AdjacencyCounts G E)
    {h : Fin 36 → ℕ} (hh : ∀ v, h v ≤ 36) {s : List ℕ} {k wl : ℕ}
    (hlen : s.length + k ≤ 36) (hw : ∀ u ∈ packedList k wl, u < 36) :
    (witSwitch G k wl (hSum (packCounts h) k wl) (packCounts (countState E h s))).1 =
      sumVertices (neighbourSum E s) (packedList k wl) +
        sumVertices (neighbourSum E (packedList k wl)) (packedList k wl) / 2 := by
  have hs : s.length ≤ 36 := by omega
  have hsw : (s ++ packedList k wl).length ≤ 36 := by
    simpa only [List.length_append, packedList_length] using hlen
  have hh' : ∀ v, h v < 128 := fun v => lt_of_le_of_lt (hh v) (by decide)
  change (hSum (packCounts (countState E h s)) k wl - hSum (packCounts h) k wl) +
    ((hSum (packCounts (countState E h s) + adjSum G k wl) k wl -
      hSum (packCounts h) k wl) -
        (hSum (packCounts (countState E h s)) k wl - hSum (packCounts h) k wl)) / 2 = _
  rw [add_adjSum_countState E hG h s hw, hSum_countState E hh hs hw,
    hSum_countState E hh hsw hw, hSum_packCounts h hh' hw]
  have ha : neighbourSum E (s ++ packedList k wl) =
      fun v => neighbourSum E s v + neighbourSum E (packedList k wl) v := by
    funext v
    exact neighbourSum_append E _ _ _
  rw [ha, sumVertices_add]
  omega

end Sarkozy.F3Kernel
