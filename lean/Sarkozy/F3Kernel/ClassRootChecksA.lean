module

public import Sarkozy.F3Kernel.ClassConnectors
public import Sarkozy.F3Kernel.ClassRootChecksB

/-!
# Accepted case-(A) root keys

Successful kind-one keys expose two disjoint edges and their two accepted connector
decisions. The semantic connector theorem then supplies the compressed class and coherence.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Extraction

structure RootATrace (G : Consts) (c : Cyl) where
  e : Fin 36 × Fin 36
  f : Fin 36 × Fin 36
  mid : Cyl
  memE : e ∈ decT G.ET
  memF : f ∈ decT G.ET
  rankF : edgeRank e < edgeRank f
  disjoint : PairDisj e f
  first : ConnectorChange G (classAStart G e f) (e.1, f.2) mid
  second : ConnectorChange G mid (f.1, e.2) c

theorem classRoot_A_trace {G : Consts} (hG : G.WellFormedT) {key : ℕ} {c : Cyl}
    (hkind : Nat.land (Nat.shiftRight key 24) 1 ≠ 0)
    (h : classRoot G key = some c) : Nonempty (RootATrace G c) := by
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
      obtain ⟨⟨hx, hy⟩, _⟩ := hdis
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
        exact ⟨⟨e, f, mid, he, hf, hef, hxy,
          connector_change _ hfirst, connector_change _ hsecond⟩⟩
    next => cases h
  next => cases h

namespace RootATrace

variable {G : Consts} {c : Cyl} (t : RootATrace G c)

include t

theorem isClassDatum : IsClassDatum (decT G.ET) (decT c.pt, decT c.qt) :=
  (classA_connectors_valid t.memE t.memF t.rankF t.disjoint t.first t.second).1

theorem compressed :
    IsCompressedDatum edgeRank (decT G.ET) (decT c.pt) (decT c.pt, decT c.qt) :=
  (classA_connectors_valid t.memE t.memF t.rankF t.disjoint t.first t.second).2

theorem coherent (hG : G.Coherent) : c.Coherent :=
  classA_connectors_coherent hG t.first t.second

end RootATrace

/-- Every accepted root key denotes a valid compressed class. -/
theorem classRoot_compressed {G : Consts} (hG : G.WellFormedT) {key : ℕ} {c : Cyl}
    (h : classRoot G key = some c) :
    IsClassDatum (decT G.ET) (decT c.pt, decT c.qt) ∧
    IsCompressedDatum edgeRank (decT G.ET) (decT c.pt) (decT c.pt, decT c.qt) := by
  by_cases hkind : Nat.land (Nat.shiftRight key 24) 1 = 0
  · obtain ⟨t⟩ := classRoot_B_trace hG hkind h
    exact ⟨t.isClassDatum, t.compressed⟩
  · obtain ⟨t⟩ := classRoot_A_trace hG hkind h
    exact ⟨t.isClassDatum, t.compressed⟩

theorem classRoot_coherent {G : Consts} (hG : G.WellFormedT) (hcoh : G.Coherent)
    {key : ℕ} {c : Cyl} (h : classRoot G key = some c) : c.Coherent := by
  by_cases hkind : Nat.land (Nat.shiftRight key 24) 1 = 0
  · exact classRoot_B_coherent hG hcoh hkind h
  · obtain ⟨t⟩ := classRoot_A_trace hG hkind h
    exact t.coherent hcoh

end Sarkozy.F3Kernel
