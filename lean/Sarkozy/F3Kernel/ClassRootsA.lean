module

public import Sarkozy.F3Kernel.RootLayouts

/-!
# Compressed roots with a disjoint pair

Case (A) starts with its first edge and its first disjoint edge. Its two connectors are
then assigned present or absent. The finite-set characterization below identifies any
such completed assignment with the paper's compressed class.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Extraction

def baseAbsent (Ex : Finset (Fin 36 × Fin 36)) (e f : Fin 36 × Fin 36) :=
  (Ex.filter fun q => edgeRank q < edgeRank e) ∪
    (Ex.filter fun q => PairDisj e q ∧ edgeRank q < edgeRank f)

def classAP (e f : Fin 36 × Fin 36) : ℕ :=
  Nat.lor (Nat.shiftLeft 1 (edgeRank e)) (Nat.shiftLeft 1 (edgeRank f))

def classAPM (e f : Fin 36 × Fin 36) : ℕ :=
  Nat.lor (Nat.shiftLeft 1 (64 * e.1.val + e.2.val))
    (Nat.shiftLeft 1 (64 * f.1.val + f.2.val))

def classAA (G : Consts) (e f : Fin 36 × Fin 36) : ℕ :=
  Nat.lor (beforeT G (edgeRank e)) (Nat.land (disjointT G e) (beforeT G (edgeRank f)))

def classAAM (G : Consts) (e f : Fin 36 × Fin 36) : ℕ :=
  Nat.lor (beforeM G (edgeRank e)) (Nat.land (disjointM G e) (beforeM G (edgeRank f)))

def classAStart (G : Consts) (e f : Fin 36 × Fin 36) : Cyl :=
  ⟨classAPM e f, Nat.xor (classAAM G e f) (Nat.land (classAAM G e f) (classAPM e f)),
    classAP e f, Nat.xor (classAA G e f) (Nat.land (classAA G e f) (classAP e f))⟩

theorem classAStart_coherent {G : Consts} (hG : G.Coherent) (e f : Fin 36 × Fin 36) :
    (classAStart G e f).Coherent := by
  have hP : SameMask (classAPM e f) (classAP e f) :=
    (single_coherent e).lor (single_coherent f)
  have hA : SameMask (classAAM G e f) (classAA G e f) :=
    SameMask.lor (before_coherent hG e) ((disjoint_coherent hG e).land (before_coherent hG f))
  exact ⟨hP, hA.xor (hA.land hP)⟩

theorem decT_classAP (e f : Fin 36 × Fin 36) : decT (classAP e f) = {e, f} := by
  rw [classAP, decT_lor, decT_single, decT_single]
  exact singleton_union _ _

theorem decT_classAA (G : Consts) (e f : Fin 36 × Fin 36) :
    decT (classAA G e f) = baseAbsent (decT G.ET) e f := by
  rw [classAA, decT_lor, decT_land, decT_before, decT_before, decT_disjointT]
  ext q
  simp only [baseAbsent, mem_union, mem_inter, mem_filter]
  change (q ∈ decT G.ET ∧ edgeRank q < edgeRank e) ∨
    (q ∈ decT G.ET ∧ PairDisj e q) ∧ (q ∈ decT G.ET ∧ edgeRank q < edgeRank f) ↔
    (q ∈ decT G.ET ∧ edgeRank q < edgeRank e) ∨
    (q ∈ decT G.ET ∧ PairDisj e q ∧ edgeRank q < edgeRank f)
  tauto

theorem pair_disjoint_baseAbsent (Ex : Finset (Fin 36 × Fin 36)) (e f : Fin 36 × Fin 36)
    (hef : edgeRank e < edgeRank f) : Disjoint ({e, f} : Finset _) (baseAbsent Ex e f) := by
  rw [disjoint_left]
  intro q hq
  simp only [mem_insert, mem_singleton] at hq
  rcases hq with rfl | rfl
  · intro hA
    rcases mem_union.mp hA with hb | hd
    · exact (lt_irrefl _) (mem_filter.mp hb).2
    · exact (mem_filter.mp hd).2.1.1 rfl
  · intro hA
    rcases mem_union.mp hA with hb | hd
    · exact (not_lt_of_ge hef.le) (mem_filter.mp hb).2
    · exact (lt_irrefl _) (mem_filter.mp hd).2.2

theorem classAStart_present (G : Consts) (e f : Fin 36 × Fin 36) :
    decT (classAStart G e f).pt = {e, f} := decT_classAP e f

theorem classAStart_absent (G : Consts) (e f : Fin 36 × Fin 36)
    (hef : edgeRank e < edgeRank f) :
    decT (classAStart G e f).qt = baseAbsent (decT G.ET) e f := by
  change decT (Nat.xor (classAA G e f) (Nat.land (classAA G e f) (classAP e f))) = _
  rw [decT_xor_land, decT_classAA, decT_classAP]
  exact sdiff_eq_left.mpr (pair_disjoint_baseAbsent _ e f hef).symm

theorem classAStart_valid (G : Consts) (e f : Fin 36 × Fin 36)
    (he : e ∈ decT G.ET) (hf : f ∈ decT G.ET) (hef : edgeRank e < edgeRank f) :
    IsClassDatum (decT G.ET) (decT (classAStart G e f).pt, decT (classAStart G e f).qt) := by
  rw [classAStart_present, classAStart_absent G e f hef]
  refine ⟨insert_subset_iff.mpr ⟨he, singleton_subset_iff.mpr hf⟩,
    ?_, pair_disjoint_baseAbsent _ e f hef⟩
  exact union_subset (filter_subset _ _) (filter_subset _ _)

theorem not_pairDisj_of_mem_con {Ex : Finset (Fin 36 × Fin 36)}
    {e f q : Fin 36 × Fin 36} (hq : q ∈ con Ex e f) : ¬ PairDisj e q := by
  obtain ⟨_, hq⟩ := mem_filter.mp hq
  rcases hq with rfl | rfl <;> simp [PairDisj]

/-- Class validity, the initial absent set, and the completed connector decisions suffice
to recover the unique compressed case-(A) datum. -/
theorem compressedA_of_invariants {Ex P A : Finset (Fin 36 × Fin 36)}
    {e f : Fin 36 × Fin 36} (hv : IsClassDatum Ex (P, A))
    (he : e ∈ P) (hf : f ∈ P) (hef : edgeRank e < edgeRank f) (hdis : PairDisj e f)
    (hP : P ⊆ {e, f} ∪ con Ex e f) (hA : baseAbsent Ex e f ⊆ A)
    (hA' : A ⊆ baseAbsent Ex e f ∪ con Ex e f) (hc : con Ex e f ⊆ P ∪ A) :
    IsCompressedDatum edgeRank Ex P (P, A) := by
  have hnot : ∀ q ∈ P, q ∉ A := fun q hq => disjoint_left.mp hv.2.2 hq
  have hfirst : IsFirst edgeRank P e := by
    refine ⟨he, ?_⟩
    intro q hq
    by_contra hlt
    have hbefore : q ∈ baseAbsent Ex e f :=
      mem_union_left _ (mem_filter.mpr ⟨hv.1 hq, by omega⟩)
    exact hnot q hq (hA hbefore)
  have hfirstF : IsFirst edgeRank (P.filter (PairDisj e)) f := by
    refine ⟨mem_filter.mpr ⟨hf, hdis⟩, ?_⟩
    intro q hq
    obtain ⟨hq, hqd⟩ := mem_filter.mp hq
    have hqp := hP hq
    simp only [mem_union, mem_insert, mem_singleton] at hqp
    rcases hqp with (rfl | rfl) | hcon
    · exact False.elim (hqd.1 rfl)
    · exact le_rfl
    · exact False.elim (not_pairDisj_of_mem_con hcon hqd)
  refine ⟨e, hfirst, Or.inl ⟨f, hfirstF, ?_⟩⟩
  apply Prod.ext
  · change P = {e, f} ∪ (P ∩ con Ex e f)
    ext q
    simp only [mem_union, mem_inter, mem_insert, mem_singleton]
    constructor
    · intro hq
      have hqp := hP hq
      simp only [mem_union, mem_insert, mem_singleton] at hqp
      tauto
    · rintro ((rfl | rfl) | ⟨hq, _⟩)
      · exact he
      · exact hf
      · exact hq
  · change A = baseAbsent Ex e f ∪ (con Ex e f \ P)
    ext q
    simp only [mem_union, mem_sdiff]
    constructor
    · intro hq
      rcases mem_union.mp (hA' hq) with hb | hcon
      · exact Or.inl hb
      · exact Or.inr ⟨hcon, fun hp => hnot q hp hq⟩
    · rintro (hb | ⟨hcon, hnp⟩)
      · exact hA hb
      · exact (mem_union.mp (hc hcon)).resolve_left hnp

end Sarkozy.F3Kernel
