module

public import Sarkozy.IndexSupport.CRT

/-!
# Non-vacuity examples

These `example`s (which add no declarations) instantiate the main theorems with simple
data, to check that their hypotheses can be met: identity transitions with full inclusion
for `one_cut_coupling` and `index_support_lemma`, and unit tails for the coupled index
(`coupled_index_sectorOperator`, `unsplit_sectorOperator`), where the norm hypothesis
`hnorm` holds because convolutions by probability laws are contractions
(`DoublyStochastic.contraction`).
-/

@[expose] public section

open Function
open scoped BigOperators Matrix

namespace Sarkozy.IndexSupport

theorem identity_doublyStochastic {Ω : Type*} [Fintype Ω] [DecidableEq Ω] :
    DoublyStochastic (1 : Matrix Ω Ω ℝ) :=
  ⟨fun x y => by by_cases h : x = y <;> simp [Matrix.one_apply, h],
    fun x => by simp [Matrix.one_apply], fun y => by simp [Matrix.one_apply]⟩

/-- Unit tails `δ_l = 1`. -/
def Tails.one (h : ℕ) : Tails h := ⟨fun _ => 1, rfl, fun _ _ => le_rfl, zero_le_one⟩

example {K : Type} [Fintype K] [DecidableEq K] {Ω : K → Type} [∀ j, Fintype (Ω j)]
    [∀ j, DecidableEq (Ω j)] [∀ j, Nonempty (Ω j)] {ι : Type} [Fintype ι]
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (X Y : (∀ j, Ω j) → ι → ℝ) : True := by
  have _h := one_cut_coupling hC (fun j => (1 : Matrix (Ω j) (Ω j) ℝ))
    (fun _ => identity_doublyStochastic) (fun _ => 1) (fun _ => zero_le_one) (fun _ => le_rfl)
    (fun j f _ => by simp) X Y
  trivial

example {K : Type} [Fintype K] [DecidableEq K] {Ω : K → Type} [∀ j, Fintype (Ω j)]
    [∀ j, DecidableEq (Ω j)] [∀ j, Nonempty (Ω j)] {ι : Type} [Fintype ι]
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (X Y : (∀ j, Ω j) → ι → ℝ) : True := by
  have hop := coupling_sectorOperator (fun j => (1 : Matrix (Ω j) (Ω j) ℝ))
    (fun _ => identity_doublyStochastic) (fun _ => 1) (fun _ => zero_le_one) (fun _ => le_rfl)
    (fun j f _ => by simp)
  have _h := index_support_lemma (wholeChains Ω) _ _ hop.maps hop.id_zero hop.norm_le
    (joint_self hC) X Y
  trivial

example (Kint : ℕ) [NeZero Kint] {P : Type} [Fintype P] [DecidableEq P] (pr h : P → ℕ)
    [∀ p, NeZero (pr p ^ h p)] {E : Type} [Fintype E] [DecidableEq E]
    (μ : E → ∀ p, ZMod (pr p ^ h p) → ℝ) (hμ : ∀ e p r, 0 ≤ μ e p r)
    (hμ1 : ∀ e p, ∑ r, μ e p r = 1) : True := by
  have _h := coupled_index_sectorOperator Kint pr h μ hμ hμ1
    (fun _ p => Tails.one (Chain.residues (pr p) (h p)).depth)
    (fun e p l f _ => by
      change _ ≤ 1 ^ 2 * _
      rw [one_pow, one_mul]
      exact (convMatrix_doublyStochastic (hμ e p) (hμ1 e p)).contraction f)
  trivial

example (Kint : ℕ) [NeZero Kint] {P : Type} [Fintype P] [DecidableEq P] (pr h : P → ℕ)
    [∀ p, NeZero (pr p ^ h p)] (hcop : Pairwise (Nat.Coprime on fun p => pr p ^ h p))
    {E : Type} [Fintype E] [DecidableEq E]
    (μ : E → ∀ p, ZMod (pr p ^ h p) → ℝ) (hμ : ∀ e p r, 0 ≤ μ e p r)
    (hμ1 : ∀ e p, ∑ r, μ e p r = 1) : True := by
  have _h := unsplit_sectorOperator Kint pr h hcop μ hμ hμ1
    (fun _ p => Tails.one (Chain.residues (pr p) (h p)).depth)
    (fun e p l f _ => by
      change _ ≤ 1 ^ 2 * _
      rw [one_pow, one_mul]
      exact (convMatrix_doublyStochastic (hμ e p) (hμ1 e p)).contraction f)
  trivial

end Sarkozy.IndexSupport
