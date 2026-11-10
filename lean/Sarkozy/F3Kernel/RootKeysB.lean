module

public import Sarkozy.F3Kernel.ClassRootChecksB

/-!
# Uniqueness of kind-zero root keys

The first edge and the first row and column arms can be recovered from the decoded present
set. Their bit positions recover all three edge fields of the key.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Extraction

theorem key_eq_of_parts {a b : ℕ}
    (h₁ : Nat.shiftRight a 25 = Nat.shiftRight b 25)
    (hk : Nat.land (Nat.shiftRight a 24) 1 = Nat.land (Nat.shiftRight b 24) 1)
    (h₂ : Nat.land (Nat.shiftRight a 12) 4095 = Nat.land (Nat.shiftRight b 12) 4095)
    (h₃ : Nat.land a 4095 = Nat.land b 4095) : a = b := by
  change a >>> 25 = b >>> 25 at h₁
  change (a >>> 24) &&& (2 ^ 1 - 1) = (b >>> 24) &&& (2 ^ 1 - 1) at hk
  change (a >>> 12) &&& (2 ^ 12 - 1) = (b >>> 12) &&& (2 ^ 12 - 1) at h₂
  change a &&& (2 ^ 12 - 1) = b &&& (2 ^ 12 - 1) at h₃
  simp only [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow] at h₁ hk h₂ h₃
  omega

structure RootBKeyParts (key : ℕ) (P : Finset (Fin 36 × Fin 36)) where
  e : Fin 36 × Fin 36
  f : Fin 36 × Fin 36
  g : Fin 36 × Fin 36
  armF : f ≠ e ∧ f.1 = e.1
  armG : g ≠ e ∧ g.2 = e.2
  rankF : edgeRank e < edgeRank f
  rankG : edgeRank e < edgeRank g
  present : P = {e, f, g}
  firstKey : edgeRank e = Nat.shiftRight key 25
  secondKey : edgeRank f = Nat.land (Nat.shiftRight key 12) 4095
  thirdKey : edgeRank g = Nat.land key 4095

theorem classRoot_B_key_parts {G : Consts} (hG : G.WellFormedT) {key : ℕ} {c : Cyl}
    (hkind : Nat.land (Nat.shiftRight key 24) 1 = 0)
    (h : classRoot G key = some c) : Nonempty (RootBKeyParts key (decT c.pt)) := by
  unfold classRoot at h
  dsimp only at h
  simp only [hkind, Bool.cond_eq_ite, Nat.beq_eq, ite_true] at h
  split at h
  next hguard =>
    split at h
    next har =>
      simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hguard har
      obtain ⟨⟨⟨_, hp1⟩, hp2⟩, h12⟩ := hguard
      obtain ⟨⟨⟨hp3, hx⟩, hy⟩, h13⟩ := har
      obtain ⟨e, _, hpe, hxe, hye⟩ := isEdge_decode hG hp1
      obtain ⟨f, _, hpf, hxf, _⟩ := isEdge_decode hG hp2
      obtain ⟨g, _, hpg, _, hyg⟩ := isEdge_decode hG hp3
      have hef : edgeRank e < edgeRank f := by rw [hpe, hpf]; exact h12
      have heg : edgeRank e < edgeRank g := by rw [hpe, hpg]; exact h13
      have hfx : f.1 = e.1 := Fin.ext (by rw [hxf, hxe]; exact hx)
      have hgy : g.2 = e.2 := Fin.ext (by rw [hyg, hye]; exact hy)
      have hnF : f ≠ e := fun heq => (ne_of_lt hef) (congrArg edgeRank heq.symm)
      have hnG : g ≠ e := fun heq => (ne_of_lt heg) (congrArg edgeRank heq.symm)
      have hc := Option.some.inj h
      have hpt : c.pt = classBP e f g := by
        rw [← hc]
        dsimp only
        simp only [classBP, hpe, hpf, hpg]
      exact ⟨⟨e, f, g, ⟨hnF, hfx⟩, ⟨hnG, hgy⟩, hef, heg,
        by rw [hpt, decT_classBP], hpe, hpf, hpg⟩⟩
    next => cases h
  next => cases h

namespace RootBKeyParts

variable {key : ℕ} {P : Finset (Fin 36 × Fin 36)} (t : RootBKeyParts key P)

theorem first : IsFirst edgeRank P t.e := by
  simp only [IsFirst, t.present]
  refine ⟨by simp, ?_⟩
  intro q hq
  simp only [mem_insert, mem_singleton] at hq
  rcases hq with rfl | rfl | rfl
  · exact le_rfl
  · exact t.rankF.le
  · exact t.rankG.le

theorem row_eq : rowArms P t.e = {t.f} := by
  ext q
  simp only [rowArms, t.present, mem_filter, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hq, hne, hx⟩
    rcases hq with rfl | rfl | rfl
    · exact False.elim (hne rfl)
    · rfl
    · exact False.elim (t.armG.1 (Prod.ext hx t.armG.2))
  · rintro rfl
    exact ⟨Or.inr (Or.inl rfl), t.armF⟩

theorem col_eq : colArms P t.e = {t.g} := by
  ext q
  simp only [colArms, t.present, mem_filter, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hq, hne, hy⟩
    rcases hq with rfl | rfl | rfl
    · exact False.elim (hne rfl)
    · exact False.elim (t.armF.1 (Prod.ext t.armF.2 hy))
    · rfl
  · rintro rfl
    exact ⟨Or.inr (Or.inr rfl), t.armG⟩

theorem noDisjoint : ∀ q ∈ P, ¬ PairDisj t.e q := by
  intro q hq
  rw [t.present] at hq
  simp only [mem_insert, mem_singleton] at hq
  rcases hq with rfl | rfl | rfl
  · simp [PairDisj]
  · simp [PairDisj, t.armF.2]
  · simp [PairDisj, t.armG.2]

theorem fields_eq {key' : ℕ} (s : RootBKeyParts key' P) :
    t.e = s.e ∧ t.f = s.f ∧ t.g = s.g := by
  have he : t.e = s.e := IsFirst.unique edgeRank edgeRank_injective.injOn
    (subset_univ P) t.first s.first
  have hr : ({t.f} : Finset _) = {s.f} := by rw [← t.row_eq, he, s.row_eq]
  have hc : ({t.g} : Finset _) = {s.g} := by rw [← t.col_eq, he, s.col_eq]
  exact ⟨he, singleton_injective hr, singleton_injective hc⟩

end RootBKeyParts

theorem classRoot_B_key_injective {G : Consts} (hG : G.WellFormedT)
    {key key' : ℕ} {c c' : Cyl}
    (hk : Nat.land (Nat.shiftRight key 24) 1 = 0)
    (hk' : Nat.land (Nat.shiftRight key' 24) 1 = 0)
    (h : classRoot G key = some c) (h' : classRoot G key' = some c')
    (hP : decT c.pt = decT c'.pt) : key = key' := by
  obtain ⟨t⟩ := classRoot_B_key_parts hG hk h
  obtain ⟨s⟩ := classRoot_B_key_parts hG hk' h'
  rw [← hP] at s
  obtain ⟨he, hf, hg⟩ := t.fields_eq s
  apply key_eq_of_parts
  · rw [← t.firstKey, ← s.firstKey, he]
  · rw [hk, hk']
  · rw [← t.secondKey, ← s.secondKey, hf]
  · rw [← t.thirdKey, ← s.thirdKey, hg]

end Sarkozy.F3Kernel
