module

public import Sarkozy.PositiveRoots.CoherentMixedFrame
public import Sarkozy.PositiveRoots.CoherentMeanBounds

/-! Core/private coordinates of the physical invariant-mean features. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.SpectralC Sarkozy.SpectralD
open scoped BigOperators

def coreVertex : Fin 4 → Fin 6 := ![0, 1, 4, 5]
def privateVertex : Fin 2 → Fin 6 := ![2, 3]

def corePart (S : Finset (Fin 6)) : Finset (Fin 4) :=
  univ.filter fun i => coreVertex i ∈ S

def privatePart (S : Finset (Fin 6)) : Finset (Fin 2) :=
  univ.filter fun i => privateVertex i ∈ S

theorem coreVertex_injective : Function.Injective coreVertex := by decide +kernel
theorem privateVertex_injective : Function.Injective privateVertex := by decide +kernel

theorem core_private_partition : ∀ S : Finset (Fin 6),
    S = (corePart S).image coreVertex ∪ (privatePart S).image privateVertex := by
  decide +kernel

theorem core_private_disjoint : ∀ S : Finset (Fin 6),
    Disjoint ((corePart S).image coreVertex) ((privatePart S).image privateVertex) := by
  decide +kernel

def meanSupport (k : CoherentMean.Kind) (i : Fin (CoherentMean.size k)) : Finset (Fin 6) :=
  CoherentMatrix.support (CoherentMean.index k i)

theorem meanSupport_nonempty : ∀ k i, (meanSupport k i).Nonempty := by
  intro k
  cases k <;> decide +kernel

theorem meanSupport_injective (k : CoherentMean.Kind) :
    Function.Injective (meanSupport k) := by
  cases k <;> decide +kernel

theorem mixed_parts_nonempty : ∀ i : Fin 10,
    (corePart (meanSupport .mixed i)).Nonempty ∧
      (privatePart (meanSupport .mixed i)).Nonempty := by
  decide +kernel

def mixedIndex (i : Fin 10) : CoreSupport × PrivateSupport :=
  (⟨corePart (meanSupport .mixed i),
    mem_filter.mpr ⟨mem_univ _, (mixed_parts_nonempty i).1⟩⟩,
   ⟨privatePart (meanSupport .mixed i),
    mem_filter.mpr ⟨mem_univ _, (mixed_parts_nonempty i).2⟩⟩)

theorem mixedIndex_injective : Function.Injective mixedIndex := by decide +kernel

def mixedEmbedding : Fin 10 ↪ CoreSupport × PrivateSupport :=
  ⟨mixedIndex, mixedIndex_injective⟩

variable {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
theorem emb_core (c : Fin 4 → ZMod p) (b : Fin 2 → ZMod p) (i : Fin 4) :
    L20Cap.emb c (b 0, b 1) (coreVertex i) = c i := by fin_cases i <;> rfl

omit [Fact p.Prime] in
theorem emb_private (c : Fin 4 → ZMod p) (b : Fin 2 → ZMod p) (i : Fin 2) :
    L20Cap.emb c (b 0, b 1) (privateVertex i) = b i := by fin_cases i <;> rfl

theorem psi_emb (S : Finset (Fin 6)) (z : ZMod p)
    (c : Fin 4 → ZMod p) (b : Fin 2 → ZMod p) :
    StarMatrix.psi S z (L20Cap.emb c (b 0, b 1)) =
      StarMatrix.psi (corePart S) z c * StarMatrix.psi (privatePart S) z b := by
  unfold StarMatrix.psi
  conv_lhs => rw [core_private_partition S]
  rw [prod_union (core_private_disjoint S), prod_image coreVertex_injective.injOn,
    prod_image privateVertex_injective.injOn]
  simp only [emb_core, emb_private]

theorem starMean_emb (S : Finset (Fin 6))
    (c : Fin 4 → ZMod p) (b : Fin 2 → ZMod p) :
    starMean S (L20Cap.emb c (b 0, b 1)) =
      (FiniteLaw.uniform (ZMod p)).expect (fun z =>
        StarMatrix.psi (corePart S) z c * StarMatrix.psi (privatePart S) z b) := by
  rw [FiniteLaw.expect_uniform, ZMod.card]
  unfold starMean starKer
  rw [← mul_sum]
  change (p : ℝ)⁻¹ * (∑ z, StarMatrix.psi S z (L20Cap.emb c (b 0, b 1))) = _
  simp_rw [psi_emb]
  ring

theorem mixedMean_physical (i : Fin 10) (c : Fin 4 → ZMod p) (b : Fin 2 → ZMod p) :
    starMean (meanSupport .mixed i) (L20Cap.emb c (b 0, b 1)) =
      mixedMean (mixedIndex i).1 (mixedIndex i).2 c b :=
  starMean_emb (meanSupport .mixed i) c b

end Sarkozy.PositiveRoots.CoherentFrame
