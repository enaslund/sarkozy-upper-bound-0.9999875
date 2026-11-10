module

public import Sarkozy.F3Kernel.ClassRootChecksA
public import Sarkozy.F3Kernel.ConnectorKeys
public import Sarkozy.F3Kernel.RootKeysB

/-!
# Recovering a kind-one key from its present edges

The first edge, the first disjoint edge, and the two connector decisions are determined by
the present set. Hence two accepted kind-one keys with the same present set are equal.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Extraction

theorem classA_firsts {G : Consts} {e f : Fin 36 × Fin 36}
    (he : e ∈ decT G.ET) (hf : f ∈ decT G.ET) (hef : edgeRank e < edgeRank f)
    (hdis : PairDisj e f) {c₁ c₂ : Cyl}
    (h₁ : ConnectorChange G (classAStart G e f) (e.1, f.2) c₁)
    (h₂ : ConnectorChange G c₁ (f.1, e.2) c₂) :
    IsFirst edgeRank (decT c₂.pt) e ∧
    IsFirst edgeRank ((decT c₂.pt).filter (PairDisj e)) f := by
  have hv := (classA_connectors_valid he hf hef hdis h₁ h₂).1
  have hep : e ∈ decT c₂.pt := h₂.bounds.monoP (h₁.bounds.monoP (by
    rw [classAStart_present]; exact mem_insert_self _ _))
  have hfp : f ∈ decT c₂.pt := h₂.bounds.monoP (h₁.bounds.monoP (by
    rw [classAStart_present]; exact mem_insert_of_mem (mem_singleton_self _)))
  constructor
  · refine ⟨hep, ?_⟩
    intro q hq
    by_contra hn
    have hb : q ∈ baseAbsent (decT G.ET) e f :=
      mem_union_left _ (mem_filter.mpr ⟨hv.1 hq, by omega⟩)
    have hA : q ∈ decT c₂.qt := h₂.bounds.monoA (h₁.bounds.monoA (by
      rwa [classAStart_absent G e f hef]))
    exact disjoint_left.mp hv.2.2 hq hA
  · refine ⟨mem_filter.mpr ⟨hfp, hdis⟩, ?_⟩
    intro q hq
    obtain ⟨hq, hqd⟩ := mem_filter.mp hq
    rcases h₂.bounds.addedP q hq with hq₁ | ⟨rfl, _⟩
    · rcases h₁.bounds.addedP q hq₁ with hq₀ | ⟨rfl, _⟩
      · rw [classAStart_present, mem_insert, mem_singleton] at hq₀
        rcases hq₀ with rfl | rfl
        · exact False.elim (hqd.1 rfl)
        · exact le_rfl
      · exact False.elim (hqd.1 rfl)
    · exact False.elim (hqd.2 rfl)

structure RootAKeyParts (key : ℕ) (P : Finset (Fin 36 × Fin 36)) where
  e : Fin 36 × Fin 36
  f : Fin 36 × Fin 36
  first : IsFirst edgeRank P e
  next : IsFirst edgeRank (P.filter (PairDisj e)) f
  firstKey : edgeRank e = Nat.shiftRight key 25
  secondKey : edgeRank f = Nat.land (Nat.shiftRight key 12) 4095
  thirdBound : Nat.land key 4095 < 4
  lowBit : Nat.land (Nat.land key 4095) 1 = 1 ↔ (e.1, f.2) ∈ P
  highBit : Nat.shiftRight (Nat.land key 4095) 1 = 1 ↔ (f.1, e.2) ∈ P

theorem classRoot_A_key_parts {G : Consts} (hG : G.WellFormedT) {key : ℕ} {c : Cyl}
    (hkind : Nat.land (Nat.shiftRight key 24) 1 ≠ 0)
    (h : classRoot G key = some c) : Nonempty (RootAKeyParts key (decT c.pt)) := by
  unfold classRoot at h
  dsimp only at h
  simp only [Bool.cond_eq_ite, Nat.beq_eq, ite_eq_right hkind] at h
  split at h
  next hguard =>
    split at h
    next hdis =>
      simp only [Bool.and_eq_true, Nat.blt_eq] at hguard
      obtain ⟨⟨⟨_, hp1⟩, hp2⟩, h12⟩ := hguard
      simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff] at hdis
      obtain ⟨⟨hx, hy⟩, hthird⟩ := hdis
      have hb : Nat.land key 4095 < 4 := Nat.blt_eq.mp hthird
      obtain ⟨e, he, hpe, hxe, hye⟩ := isEdge_decode hG hp1
      obtain ⟨f, hf, hpf, hxf, hyf⟩ := isEdge_decode hG hp2
      have hef : edgeRank e < edgeRank f := by rw [hpe, hpf]; exact h12
      have hxy : PairDisj e f := by
        constructor
        · intro heq
          apply hx
          rw [← hxf, ← hxe, heq, Nat.beq_refl]
        · intro heq
          apply hy
          rw [← hyf, ← hye, heq, Nat.beq_refl]
      split at h
      next => cases h
      next mid hmid =>
        have hfirst : connector G (classAStart G e f) e.1.val f.2.val
            (Nat.land (Nat.land key 4095) 1) = some mid := by
          simp only [classAStart, classAPM, classAAM, disjointM, classAP, classAA,
            disjointT, hpe, hpf, hxe, hye, hxf, hyf]
          exact hmid
        have hsecond : connector G mid f.1.val e.2.val
            (Nat.shiftRight (Nat.land key 4095) 1) = some c := by
          rw [hxf, hye]
          exact h
        have h₁ := connector_change (e.1, f.2) hfirst
        have h₂ := connector_change (f.1, e.2) hsecond
        have hfs := classA_firsts he hf hef hxy h₁ h₂
        obtain ⟨hn₁, hn₂, hne⟩ := corners_not_present hxy
        have hn₁' : (e.1, f.2) ∉ decT (classAStart G e f).pt := by
          rwa [classAStart_present]
        have hn₂' : (f.1, e.2) ∉ decT mid.pt := by
          intro hm
          rcases h₁.bounds.addedP _ hm with hm | ⟨heq, _⟩
          · exact hn₂ ((classAStart_present G e f) ▸ hm)
          · exact hne heq.symm
        refine ⟨⟨e, f, hfs.1, hfs.2, hpe, hpf, hb, ?_, ?_⟩⟩
        · exact (connector_one_iff_present _ hn₁' hfirst).trans
            (connector_other_present _ _ hne hsecond).symm
        · exact connector_one_iff_present _ hn₂' hsecond
    next => cases h
  next => cases h

theorem key_kind_one {key : ℕ} (h : Nat.land (Nat.shiftRight key 24) 1 ≠ 0) :
    Nat.land (Nat.shiftRight key 24) 1 = 1 := by
  change (key >>> 24) &&& (2 ^ 1 - 1) ≠ 0 at h
  change (key >>> 24) &&& (2 ^ 1 - 1) = 1
  rw [Nat.and_two_pow_sub_one_eq_mod] at h ⊢
  omega

namespace RootAKeyParts

variable {key : ℕ} {P : Finset (Fin 36 × Fin 36)} (t : RootAKeyParts key P)

include t

theorem fields_eq {key' : ℕ} (s : RootAKeyParts key' P) : t.e = s.e ∧ t.f = s.f := by
  have he : t.e = s.e := IsFirst.unique edgeRank edgeRank_injective.injOn
    (subset_univ P) t.first s.first
  have hnext := t.next
  rw [he] at hnext
  exact ⟨he, IsFirst.unique edgeRank edgeRank_injective.injOn (subset_univ _) hnext s.next⟩

theorem third_eq {key' : ℕ} (s : RootAKeyParts key' P) :
    Nat.land key 4095 = Nat.land key' 4095 := by
  obtain ⟨he, hf⟩ := t.fields_eq s
  have hl : Nat.land (Nat.land key 4095) 1 = 1 ↔ Nat.land (Nat.land key' 4095) 1 = 1 := by
    rw [t.lowBit, s.lowBit, he, hf]
  have hh : Nat.shiftRight (Nat.land key 4095) 1 = 1 ↔
      Nat.shiftRight (Nat.land key' 4095) 1 = 1 := by
    rw [t.highBit, s.highBit, he, hf]
  change (Nat.land key 4095) &&& (2 ^ 1 - 1) = 1 ↔
    (Nat.land key' 4095) &&& (2 ^ 1 - 1) = 1 at hl
  change (Nat.land key 4095) >>> 1 = 1 ↔ (Nat.land key' 4095) >>> 1 = 1 at hh
  simp only [Nat.and_two_pow_sub_one_eq_mod] at hl
  simp only [Nat.shiftRight_eq_div_pow] at hh
  have ht := t.thirdBound
  have hs := s.thirdBound
  omega

end RootAKeyParts

theorem classRoot_A_key_injective {G : Consts} (hG : G.WellFormedT)
    {key key' : ℕ} {c c' : Cyl}
    (hk : Nat.land (Nat.shiftRight key 24) 1 ≠ 0)
    (hk' : Nat.land (Nat.shiftRight key' 24) 1 ≠ 0)
    (h : classRoot G key = some c) (h' : classRoot G key' = some c')
    (hP : decT c.pt = decT c'.pt) : key = key' := by
  obtain ⟨t⟩ := classRoot_A_key_parts hG hk h
  obtain ⟨s⟩ := classRoot_A_key_parts hG hk' h'
  rw [← hP] at s
  obtain ⟨he, hf⟩ := t.fields_eq s
  apply key_eq_of_parts
  · rw [← t.firstKey, ← s.firstKey, he]
  · rw [key_kind_one hk, key_kind_one hk']
  · rw [← t.secondKey, ← s.secondKey, hf]
  · exact t.third_eq s

end Sarkozy.F3Kernel
