module

public import Sarkozy.Mixing.Conductor

/-!
# Single-slot mixing is block mixing at a singleton

`def:mixing` defines `(γ, v)`-mixing as `(γ, Z)`-mixing for the block `Z = {v}`. The
conductor lemma (`Sarkozy.Mixing.prefix_conductor`) states its hypothesis with the single-slot
joint law `slotJoint ρ v` (labels `z_v ∈ X` and `z_{V∖{v}}`). This file proves that the two
encodings give the same mixing property (`isMixing_singleton_iff`) and the same uniform
marginal (`srcWeight_blockJoint_singleton`), via the invariance of `ContractsMeanZero` under
relabelling of source and target (`contractsMeanZero_congr`).
-/

@[expose] public section

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.Mixing

section Relabel

variable {A B A' B' : Type*} [Fintype A] [Fintype B] [Fintype A'] [Fintype B']

theorem srcWeight_congr {κ : FiniteLaw (A × B)} {κ' : FiniteLaw (A' × B')} (σ : A ≃ A')
    (τ : B ≃ B') (h : ∀ a b, κ'.weight (σ a, τ b) = κ.weight (a, b)) (a : A) :
    srcWeight κ' (σ a) = srcWeight κ a := by
  unfold srcWeight
  rw [← Fintype.sum_equiv τ (fun b => κ'.weight (σ a, τ b)) (fun b' => κ'.weight (σ a, b'))
    (fun b => rfl)]
  exact sum_congr rfl (fun b _ => h a b)

theorem tgtWeight_congr {κ : FiniteLaw (A × B)} {κ' : FiniteLaw (A' × B')} (σ : A ≃ A')
    (τ : B ≃ B') (h : ∀ a b, κ'.weight (σ a, τ b) = κ.weight (a, b)) (b : B) :
    tgtWeight κ' (τ b) = tgtWeight κ b := by
  unfold tgtWeight
  rw [← Fintype.sum_equiv σ (fun a => κ'.weight (σ a, τ b)) (fun a' => κ'.weight (a', τ b))
    (fun a => rfl)]
  exact sum_congr rfl (fun a _ => h a b)

theorem condOp_congr {κ : FiniteLaw (A × B)} {κ' : FiniteLaw (A' × B')} (σ : A ≃ A')
    (τ : B ≃ B') (h : ∀ a b, κ'.weight (σ a, τ b) = κ.weight (a, b)) (f : A' → ℝ) (b : B) :
    tgtWeight κ' (τ b) * condOp κ' f (τ b) = tgtWeight κ b * condOp κ (f ∘ σ) b := by
  rw [tgt_mul_condOp, tgt_mul_condOp]
  rw [← Fintype.sum_equiv σ (fun a => κ'.weight (σ a, τ b) * f (σ a))
    (fun a' => κ'.weight (a', τ b) * f a') (fun a => rfl)]
  exact sum_congr rfl (fun a _ => by rw [h a b]; rfl)

theorem contractsMeanZero_of_congr {κ : FiniteLaw (A × B)} {κ' : FiniteLaw (A' × B')}
    (σ : A ≃ A') (τ : B ≃ B') (h : ∀ a b, κ'.weight (σ a, τ b) = κ.weight (a, b)) {c : ℝ}
    (hκ : ContractsMeanZero κ c) : ContractsMeanZero κ' c := by
  intro f hf
  have hsrc := srcWeight_congr σ τ h
  have hmean : ∑ a, srcWeight κ a * (f ∘ σ) a = 0 := by
    rw [← hf, ← Fintype.sum_equiv σ (fun a => srcWeight κ' (σ a) * f (σ a))
      (fun a' => srcWeight κ' a' * f a') (fun a => rfl)]
    exact sum_congr rfl (fun a _ => by rw [hsrc a]; rfl)
  have hb := hκ (f ∘ σ) hmean
  have hE : ∑ b', tgtWeight κ' b' * condOp κ' f b' ^ 2 =
      ∑ b, tgtWeight κ b * condOp κ (f ∘ σ) b ^ 2 := by
    rw [← Fintype.sum_equiv τ (fun b => tgtWeight κ' (τ b) * condOp κ' f (τ b) ^ 2)
      (fun b' => tgtWeight κ' b' * condOp κ' f b' ^ 2) (fun b => rfl)]
    apply sum_congr rfl
    intro b _
    have h1 := condOp_congr σ τ h f b
    have h2 := tgtWeight_congr σ τ h b
    by_cases h0 : tgtWeight κ b = 0
    · rw [h2, h0, zero_mul, zero_mul]
    · have hT : condOp κ' f (τ b) = condOp κ (f ∘ σ) b := by
        rw [h2] at h1
        exact mul_left_cancel₀ h0 h1
      rw [h2, hT]
  have hN : ∑ a', srcWeight κ' a' * f a' ^ 2 = ∑ a, srcWeight κ a * (f ∘ σ) a ^ 2 := by
    rw [← Fintype.sum_equiv σ (fun a => srcWeight κ' (σ a) * f (σ a) ^ 2)
      (fun a' => srcWeight κ' a' * f a' ^ 2) (fun a => rfl)]
    exact sum_congr rfl (fun a _ => by rw [hsrc a]; rfl)
  rw [hE, hN]
  exact hb

/-- Mixing is invariant under relabelling the source and the target. -/
theorem contractsMeanZero_congr {κ : FiniteLaw (A × B)} {κ' : FiniteLaw (A' × B')}
    (σ : A ≃ A') (τ : B ≃ B') (h : ∀ a b, κ'.weight (σ a, τ b) = κ.weight (a, b)) (c : ℝ) :
    ContractsMeanZero κ c ↔ ContractsMeanZero κ' c := by
  refine ⟨contractsMeanZero_of_congr σ τ h, contractsMeanZero_of_congr σ.symm τ.symm ?_⟩
  intro a' b'
  have := h (σ.symm a') (τ.symm b')
  simp only [Equiv.apply_symm_apply] at this
  exact this.symm

end Relabel

section Singleton

variable {V : Type*} [Fintype V] [DecidableEq V] {X : Type*} [Fintype X] [DecidableEq X]

/-- The labels of the block `{v}` are the labels at `v`. -/
def singletonEquiv (v : V) : ({w // w ∈ ({v} : Finset V)} → X) ≃ X where
  toFun a := a ⟨v, mem_singleton_self v⟩
  invFun x := fun _ => x
  left_inv a := by
    funext w
    have hw : w = ⟨v, mem_singleton_self v⟩ := Subtype.ext (mem_singleton.mp w.2)
    rw [hw]
  right_inv x := rfl

/-- The labels outside `{v}` are the labels at `w ≠ v`. -/
def complSingletonEquiv (v : V) :
    ({w // w ∉ ({v} : Finset V)} → X) ≃ ({w // w ≠ v} → X) :=
  Equiv.arrowCongr (Equiv.subtypeEquivRight (fun w => by simp)) (Equiv.refl X)

theorem slotJoint_weight_singleton (ρ : FiniteLaw (V → X)) (v : V)
    (a : {w // w ∈ ({v} : Finset V)} → X) (b : {w // w ∉ ({v} : Finset V)} → X) :
    (slotJoint ρ v).weight (singletonEquiv v a, complSingletonEquiv v b) =
      (blockJoint ρ {v}).weight (a, b) := by
  rw [slotJoint_weight, blockJoint_weight]
  congr 1
  funext w
  by_cases hw : w = v
  · subst hw
    simp [singletonEquiv, Equiv.piEquivPiSubtypeProd]
  · simp [complSingletonEquiv, Equiv.piEquivPiSubtypeProd, hw, Equiv.arrowCongr]
    rfl

/-- **`(c, v)`-mixing is `(c, {v})`-mixing** (`def:mixing`). -/
theorem isMixing_singleton_iff (ρ : FiniteLaw (V → X)) (v : V) (c : ℝ) :
    IsMixing ρ {v} c ↔ ContractsMeanZero (slotJoint ρ v) c :=
  contractsMeanZero_congr (singletonEquiv v) (complSingletonEquiv v)
    (slotJoint_weight_singleton ρ v) c

/-- The `{v}`-marginal of `ρ` is its `v`-marginal. -/
theorem srcWeight_blockJoint_singleton (ρ : FiniteLaw (V → X)) (v : V)
    (a : {w // w ∈ ({v} : Finset V)} → X) :
    srcWeight (blockJoint ρ {v}) a = srcWeight (slotJoint ρ v) (singletonEquiv v a) :=
  (srcWeight_congr (singletonEquiv v) (complSingletonEquiv v)
    (slotJoint_weight_singleton ρ v) a).symm

end Singleton

end Sarkozy.Mixing
