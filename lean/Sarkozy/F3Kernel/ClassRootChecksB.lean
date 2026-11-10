module

public import Sarkozy.F3Kernel.RootLayouts

/-!
# Accepted case-(B) root keys

The actual guards in `classRoot` imply the hypotheses of the compressed case-(B) formula.
This is a semantic statement about any accepted key, rather than a finite check of a list
of particular roots.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Extraction

theorem isEdge_decode {G : Consts} (hG : G.WellFormedT) {p : ℕ}
    (hp : isEdge G p = true) :
    ∃ e ∈ decT G.ET, edgeRank e = p ∧ e.1.val = Nat.land p 63 ∧
      e.2.val = Nat.shiftRight p 6 := by
  have hbit : G.ET.testBit p = true := by
    simpa only [isEdge, bit_eq_testBit] using hp
  obtain ⟨hx, hy⟩ := hG p hbit
  refine ⟨pairOf p hx hy, (pairOf_mem_decT _ _ hx hy).mpr hbit, ?_, ?_, ?_⟩
  · change 64 * (p / 64) + p % 64 = p
    omega
  · change p % 64 = p &&& (2 ^ 6 - 1)
    rw [Nat.and_two_pow_sub_one_eq_mod]
  · change p / 64 = p >>> 6
    rw [Nat.shiftRight_eq_div_pow]

/-- The mathematical data exposed by a successful kind-zero root check. -/
structure RootBTrace (G : Consts) (c : Cyl) where
  e : Fin 36 × Fin 36
  f : Fin 36 × Fin 36
  g : Fin 36 × Fin 36
  memE : e ∈ decT G.ET
  memF : f ∈ decT G.ET
  memG : g ∈ decT G.ET
  armF : f ≠ e ∧ f.1 = e.1
  armG : g ≠ e ∧ g.2 = e.2
  rankF : edgeRank e < edgeRank f
  rankG : edgeRank e < edgeRank g
  present : c.pt = classBP e f g
  absent : c.qt = Nat.xor (classBA G e f g)
    (Nat.land (classBA G e f g) (classBP e f g))
  matrixPresent : c.pm = classBPM e f g
  matrixAbsent : c.am = Nat.xor (classBAM G e f g)
    (Nat.land (classBAM G e f g) (classBPM e f g))

theorem classRoot_B_trace {G : Consts} (hG : G.WellFormedT) {key : ℕ} {c : Cyl}
    (hkind : Nat.land (Nat.shiftRight key 24) 1 = 0)
    (h : classRoot G key = some c) : Nonempty (RootBTrace G c) := by
  unfold classRoot at h
  dsimp only at h
  simp only [hkind, Bool.cond_eq_ite, Nat.beq_eq, ite_true] at h
  split at h
  next hguard =>
    split at h
    next harms =>
      simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hguard harms
      obtain ⟨⟨⟨_, hp1⟩, hp2⟩, h12⟩ := hguard
      obtain ⟨⟨⟨hp3, hx⟩, hy⟩, h13⟩ := harms
      obtain ⟨e, he, hpe, hxe, hye⟩ := isEdge_decode hG hp1
      obtain ⟨f, hf, hpf, hxf, hyf⟩ := isEdge_decode hG hp2
      obtain ⟨g, hg, hpg, hxg, hyg⟩ := isEdge_decode hG hp3
      have hef : edgeRank e < edgeRank f := by rw [hpe, hpf]; exact h12
      have heg : edgeRank e < edgeRank g := by rw [hpe, hpg]; exact h13
      have hfx : f.1 = e.1 := Fin.ext (by rw [hxf, hxe]; exact hx)
      have hgy : g.2 = e.2 := Fin.ext (by rw [hyg, hye]; exact hy)
      have hneF : f ≠ e := fun heq => (ne_of_lt hef) (congrArg edgeRank heq.symm)
      have hneG : g ≠ e := fun heq => (ne_of_lt heg) (congrArg edgeRank heq.symm)
      have hc := Option.some.inj h
      refine ⟨⟨e, f, g, he, hf, hg, ⟨hneF, hfx⟩, ⟨hneG, hgy⟩, hef, heg,
        ?_, ?_, ?_, ?_⟩⟩
      · rw [← hc]
        dsimp only
        simp only [classBP, hpe, hpf, hpg]
      · rw [← hc]
        dsimp only
        simp only [classBA, disjointT, classBP, hpe, hpf, hpg, hxe, hye]
      · rw [← hc]
        dsimp only
        simp only [classBPM, hgy, hxe, hye, hxf, hyf, hxg]
        rfl
      · rw [← hc]
        dsimp only
        simp only [classBAM, disjointM, classBPM, hpe, hpf, hpg, hgy, hxe, hye,
          hxf, hyf, hxg]
        rfl
    next => cases h
  next => cases h

namespace RootBTrace

variable {G : Consts} {c : Cyl} (t : RootBTrace G c)

include t

theorem datum_eq : (decT c.pt, decT c.qt) = datumB edgeRank (decT G.ET) t.e t.f t.g := by
  apply Prod.ext
  · rw [t.present, decT_classBP]
    rfl
  · rw [t.absent, decT_classB_absent G t.e t.f t.g t.memE t.memF t.memG
      t.armF t.armG t.rankF t.rankG]

theorem compressed :
    IsCompressedDatum edgeRank (decT G.ET) (decT c.pt) (decT c.pt, decT c.qt) := by
  rw [t.datum_eq, t.present, decT_classBP]
  exact datumB_of_arms _ _ _ _ t.armF t.armG t.rankF t.rankG

theorem isClassDatum : IsClassDatum (decT G.ET) (decT c.pt, decT c.qt) := by
  apply IsCompressedDatum.isClassDatum edgeRank (h := t.compressed)
  rw [t.present, decT_classBP]
  simp only [insert_subset_iff, singleton_subset_iff]
  exact ⟨t.memE, t.memF, t.memG⟩

theorem coherent (hG : G.Coherent) : c.Coherent := by
  change decM c.pm = decT c.pt ∧ decM c.am = decT c.qt
  rw [t.matrixPresent, t.matrixAbsent, t.present, t.absent]
  have hP := classBP_coherent t.e t.f t.g
  have hA := classBA_coherent hG t.e t.f t.g
  exact ⟨hP, hA.xor (hA.land hP)⟩

end RootBTrace

theorem classRoot_B_isClassDatum {G : Consts} (hG : G.WellFormedT) {key : ℕ} {c : Cyl}
    (hkind : Nat.land (Nat.shiftRight key 24) 1 = 0) (h : classRoot G key = some c) :
    IsClassDatum (decT G.ET) (decT c.pt, decT c.qt) := by
  obtain ⟨t⟩ := classRoot_B_trace hG hkind h
  exact t.isClassDatum

theorem classRoot_B_coherent {G : Consts} (hG : G.WellFormedT) (hcoh : G.Coherent)
    {key : ℕ} {c : Cyl} (hkind : Nat.land (Nat.shiftRight key 24) 1 = 0)
    (h : classRoot G key = some c) : c.Coherent := by
  obtain ⟨t⟩ := classRoot_B_trace hG hkind h
  exact t.coherent hcoh

end Sarkozy.F3Kernel
