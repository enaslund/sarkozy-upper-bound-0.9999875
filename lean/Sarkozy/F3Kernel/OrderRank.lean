module

public import Sarkozy.F3Kernel.OrderLoops

/-!
# Orders with the cover first and integrated vertices last

The packed witness and non-witness lists supply ranks within each of the three stages:
cover, witness, integrated vertices. Disjoint rank intervals preserve injectivity and give
the segment conditions in `LeafRecordData.Valid`.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

def orderBlock (w : List ℕ) (C : Finset (Fin 36)) (v : Fin 36) : ℕ :=
  if v ∈ C then 0 else if v.val ∈ w then 1 else 2

def orderPosition (w s : List ℕ) (v : Fin 36) : ℕ :=
  if v.val ∈ w then w.idxOf v.val else s.idxOf v.val

def orderRank (w s : List ℕ) (C : Finset (Fin 36)) (v : Fin 36) : ℕ :=
  36 * orderBlock w C v + orderPosition w s v

theorem orderPosition_lt {w s : List ℕ} (hw : w.length ≤ 36) (hs : s.length ≤ 36)
    (hcomplete : ∀ v : Fin 36, v.val ∈ s ↔ v.val ∉ w) (v : Fin 36) :
    orderPosition w s v < 36 := by
  unfold orderPosition
  split_ifs with hv
  · exact (List.idxOf_lt_length_of_mem hv).trans_le hw
  · exact (List.idxOf_lt_length_of_mem ((hcomplete v).mpr hv)).trans_le hs

theorem orderRank_injective {w s : List ℕ} {C : Finset (Fin 36)}
    (hw : w.length ≤ 36) (hs : s.length ≤ 36)
    (hcomplete : ∀ v : Fin 36, v.val ∈ s ↔ v.val ∉ w)
    (hdisj : ∀ v ∈ C, v.val ∉ w) : Function.Injective (orderRank w s C) := by
  intro a b he
  have ha := orderPosition_lt hw hs hcomplete a
  have hb := orderPosition_lt hw hs hcomplete b
  have he' : 36 * orderBlock w C a + orderPosition w s a =
      36 * orderBlock w C b + orderPosition w s b := he
  have hblock : orderBlock w C a = orderBlock w C b := by omega
  have hpos : orderPosition w s a = orderPosition w s b := by omega
  by_cases haw : a.val ∈ w
  · by_cases hbw : b.val ∈ w
    · simp only [orderPosition, haw, hbw, ite_true] at hpos
      exact Fin.ext ((List.idxOf_inj haw).mp hpos)
    · have hac : a ∉ C := fun hc => hdisj a hc haw
      simp only [orderBlock, hac, haw, hbw, ite_false, ite_true] at hblock
      split_ifs at hblock
      omega
  · by_cases hbw : b.val ∈ w
    · have hbc : b ∉ C := fun hc => hdisj b hc hbw
      simp only [orderBlock, haw, hbc, hbw, ite_false, ite_true] at hblock
      split_ifs at hblock
      omega
    · simp only [orderPosition, haw, hbw, ite_false] at hpos
      exact Fin.ext ((List.idxOf_inj ((hcomplete a).mpr haw)).mp hpos)

theorem orderRank_cover_first {w s : List ℕ} {C : Finset (Fin 36)}
    (hw : w.length ≤ 36) (hs : s.length ≤ 36)
    (hcomplete : ∀ v : Fin 36, v.val ∈ s ↔ v.val ∉ w)
    {a b : Fin 36} (ha : a ∈ C) (hb : b ∉ C) :
    orderRank w s C a < orderRank w s C b := by
  have hapos := orderPosition_lt hw hs hcomplete a
  unfold orderRank orderBlock
  simp only [ha, hb, ite_true, ite_false, mul_zero, zero_add]
  split_ifs <;> omega

theorem orderRank_integrated_last {w s : List ℕ} {C : Finset (Fin 36)}
    (hw : w.length ≤ 36) (hs : s.length ≤ 36)
    (hcomplete : ∀ v : Fin 36, v.val ∈ s ↔ v.val ∉ w)
    {a b : Fin 36} (ha : a.val ∈ w ∨ a ∈ C) (hbw : b.val ∉ w) (hbc : b ∉ C) :
    orderRank w s C a < orderRank w s C b := by
  have hapos := orderPosition_lt hw hs hcomplete a
  unfold orderRank orderBlock
  simp only [hbw, hbc, ite_false]
  rcases ha with haw | hac
  · simp only [haw, ite_true]
    split_ifs <;> omega
  · simp only [hac, ite_true]
    omega

/-- The order conditions required on one side of an extraction record. -/
structure RecordOrder (W C : Finset (Fin 36)) (ord : Fin 36 → ℕ) : Prop where
  injective : Function.Injective ord
  coverFirst : ∀ a ∈ C, ∀ b, b ∉ C → ord a < ord b
  integratedLast : ∀ a, a ∉ Finset.univ \ (W ∪ C) →
    ∀ b ∈ Finset.univ \ (W ∪ C), ord a < ord b

theorem orderRank_recordOrder {w s : List ℕ} {W C : Finset (Fin 36)}
    (hw : w.length ≤ 36) (hs : s.length ≤ 36)
    (hcomplete : ∀ v : Fin 36, v.val ∈ s ↔ v.val ∉ w)
    (hW : ∀ v : Fin 36, v ∈ W ↔ v.val ∈ w) (hdisj : Disjoint C W) :
    RecordOrder W C (orderRank w s C) := by
  refine ⟨orderRank_injective hw hs hcomplete ?_, ?_, ?_⟩
  · intro v hv hwv
    exact Finset.disjoint_left.mp hdisj hv ((hW v).mpr hwv)
  · intro a ha b hb
    exact orderRank_cover_first hw hs hcomplete ha hb
  · intro a ha b hb
    have ha' : a ∈ W ∨ a ∈ C := by simpa only [Finset.mem_sdiff, Finset.mem_univ,
      true_and, Finset.mem_union, not_not] using ha
    have hb' := not_or.mp (show ¬(b ∈ W ∨ b ∈ C) from
      fun hbc => (Finset.mem_sdiff.mp hb).2 (Finset.mem_union.mpr hbc))
    exact orderRank_integrated_last hw hs hcomplete (ha'.imp ((hW a).mp) id)
      (fun hwv => hb'.1 ((hW b).mpr hwv)) hb'.2

end Sarkozy.F3Kernel
