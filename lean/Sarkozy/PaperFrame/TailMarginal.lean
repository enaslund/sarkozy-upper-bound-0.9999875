module

public import Sarkozy.PaperFrame.Reference

@[expose] public section

/-!
# Marginals and translations of the reference law across scales

Bookkeeping for `lem:record:fibre-scale`(c) at the paper's actual scales. The tail
coordinates at the scale `L` are the primes of a finite set `T L` (`J L = ↥(T L)`,
`p L j = j`), and the reference law is the comparison worker's
`paperLaw = μ₀ ⊗ ⊗_{q ∈ T L} μ_q` (`Sarkozy.Comparison.paperLaw`), with atom laws that do
not depend on the scale ((R1)).

* `tensor_expect_sum`: the expectation under a tensor of slot laws as a finite sum.
* `tensor_expect_restrict`: the marginal of a tensor law on a subset of its factors is the
  tensor over that subset.
* `primeTailLaw_marginal`: if `T ℓ ⊆ T L`, the marginal of the tail law at the scale `L`
  on the primes of `T ℓ` is the tail law at the scale `ℓ`.
* `paperLaw_marginal`: the same for the full reference law, with the prefix coordinate
  kept.
* `tensor_translate`, `paperLaw_translate`: if every atom law is invariant under the
  simultaneous translation of all slots (the case `r_p = 1` of (R3)), so is the
  reference law.
-/

open Finset

namespace Sarkozy.PaperFrame

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.Comparison

/-! ### Tensor laws: sums, marginals, translations -/

section Tensor

variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
  {X : I → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

/-- The expectation under a tensor of slot laws as a finite sum over the factor
configurations. -/
theorem tensor_expect_sum (μ : ∀ i, FiniteLaw (V → X i)) (F : (V → ∀ i, X i) → ℝ) :
    (FiniteLaw.tensor μ).expect F =
      ∑ z : ∀ i, V → X i, (∏ i, (μ i).weight (z i)) * F (fun v i => z i v) := by
  rw [FiniteLaw.expect_eq_signedIntegral, FiniteLaw.signedIntegral_tensor]
  change (∑ z : ∀ i, V → X i,
      (∏ i, lawDensity (signedIntegral (μ i).weight) (z i)) * F (fun v i => z i v)) = _
  simp_rw [lawDensity_signedIntegral]

/-- The marginal of a tensor law on the factors satisfying `P` is the tensor law over them. -/
theorem tensor_expect_restrict (μ : ∀ i, FiniteLaw (V → X i)) (P : I → Prop) [DecidablePred P]
    (H : (V → ∀ s : {i // P i}, X s.1) → ℝ) :
    (FiniteLaw.tensor μ).expect (fun z => H (fun v s => z v s.1)) =
      (FiniteLaw.tensor (fun s : {i // P i} => μ s.1)).expect H := by
  rw [tensor_expect_sum, tensor_expect_sum]
  set e := Equiv.piEquivPiSubtypeProd P (fun i => V → X i)
  rw [Fintype.sum_equiv e _ (fun ab => (∏ i, (μ i).weight (e.symm ab i)) *
      H (fun v s => e.symm ab s.1 v)) (fun z => by rw [Equiv.symm_apply_apply])]
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a _
  have hpos : ∀ (b : ∀ c : {i // ¬P i}, V → X c.1) (s : {i // P i}), e.symm (a, b) s.1 = a s := by
    intro b s
    simp [e, s.2]
  have hneg : ∀ (b : ∀ c : {i // ¬P i}, V → X c.1) (c : {i // ¬P i}), e.symm (a, b) c.1 = b c := by
    intro b c
    simp [e, c.2]
  have hterm : ∀ b : ∀ c : {i // ¬P i}, V → X c.1,
      (∏ i, (μ i).weight (e.symm (a, b) i)) * H (fun v s => e.symm (a, b) s.1 v) =
        ((∏ s : {i // P i}, (μ s.1).weight (a s)) * H (fun v s => a s v)) *
          ∏ c : {i // ¬P i}, (μ c.1).weight (b c) := by
    intro b
    rw [← Fintype.prod_subtype_mul_prod_subtype P (fun i => (μ i).weight (e.symm (a, b) i))]
    simp only [hpos, hneg]
    ring
  rw [sum_congr rfl (fun b _ => hterm b), ← mul_sum]
  have hone : ∑ b : ∀ c : {i // ¬P i}, V → X c.1, ∏ c : {i // ¬P i}, (μ c.1).weight (b c) = 1 := by
    have hps := Fintype.prod_sum (fun (c : {i // ¬P i}) (t : V → X c.1) => (μ c.1).weight t)
    rw [← hps]
    simp only [(μ _).total, prod_const_one]
  rw [hone, mul_one]

/-- Invariance of a finite law under the simultaneous translation of all slots, in terms of
its weights. -/
theorem weight_translate {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]
    (ν : FiniteLaw (V → G)) (r : G)
    (hinv : ∀ F : (V → G) → ℝ, ν.expect (fun z => F (fun v => z v + r)) = ν.expect F)
    (y : V → G) : ν.weight (fun v => y v - r) = ν.weight y := by
  have h := hinv (fun z => if z = y then 1 else 0)
  simp only [FiniteLaw.expect, mul_ite, mul_one, mul_zero] at h
  rw [sum_ite_eq' univ y, ite_eq_left (mem_univ y)] at h
  rw [Finset.sum_eq_single (fun v => y v - r)] at h
  · simpa using h
  · intro z _ hz
    have : (fun v => z v + r) ≠ y := by
      intro h'
      apply hz
      funext v
      have hv : z v + r = y v := congrFun h' v
      rw [← hv]
      simp
    simp [this]
  · intro h'; exact absurd (mem_univ _) h'

/-- A tensor of laws each invariant under the simultaneous translation of all slots is
invariant under the simultaneous translation by every `r = (r_i)_i`. -/
theorem tensor_translate {G : I → Type*} [∀ i, AddGroup (G i)] [∀ i, Fintype (G i)]
    [∀ i, DecidableEq (G i)] (μ : ∀ i, FiniteLaw (V → G i))
    (hinv : ∀ i (r : G i) (F : (V → G i) → ℝ),
      (μ i).expect (fun z => F (fun v => z v + r)) = (μ i).expect F)
    (r : ∀ i, G i) (F : (V → ∀ i, G i) → ℝ) :
    (FiniteLaw.tensor μ).expect (fun w => F (fun v => w v + r)) = (FiniteLaw.tensor μ).expect F := by
  rw [tensor_expect_sum, tensor_expect_sum]
  let σ : (∀ i, V → G i) ≃ (∀ i, V → G i) :=
    { toFun := fun z i v => z i v + r i
      invFun := fun z i v => z i v - r i
      left_inv := fun z => by funext i v; simp
      right_inv := fun z => by funext i v; simp }
  refine Fintype.sum_equiv σ _ _ (fun z => ?_)
  have hw : ∀ i, (μ i).weight (z i) = (μ i).weight (σ z i) := by
    intro i
    have := weight_translate (μ i) (r i) (hinv i (r i)) (σ z i)
    rw [← this]
    congr 1
    funext v
    simp [σ]
  rw [prod_congr rfl (fun i _ => hw i)]
  rfl

end Tensor

/-! ### The paper's tail and reference laws at two scales -/

section Scales

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  (T : ℕ → Finset ℕ) [∀ L (j : ↥(T L)), NeZero (j : ℕ)]

/-- The restriction of the tail coordinates at the scale `L` to the primes of `T ℓ`. -/
def tailRestrict {ℓ L : ℕ} (hT : T ℓ ⊆ T L) (z : ∀ j : ↥(T L), ZMod (j : ℕ)) :
    ∀ j : ↥(T ℓ), ZMod (j : ℕ) :=
  fun j => z ⟨j.1, hT j.2⟩

/-- `lem:record:fibre-scale`(c), bookkeeping: if `T ℓ ⊆ T L`, the marginal of the tail law
`⊗_{q ∈ T L} μ_q` on the primes of `T ℓ` is the tail law `⊗_{q ∈ T ℓ} μ_q` (the prime laws
do not depend on the scale, (R1)). -/
theorem primeTailLaw_marginal (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q))
    {ℓ L : ℕ} (hT : T ℓ ⊆ T L) (H : (Slot → ∀ j : ↥(T ℓ), ZMod (j : ℕ)) → ℝ) :
    (primeTailLaw (J := fun L => ↥(T L)) (fun _ j => (j : ℕ)) μp L).expect
        (fun z => H (fun v => tailRestrict T hT (z v))) =
      (primeTailLaw (J := fun L => ↥(T L)) (fun _ j => (j : ℕ)) μp ℓ).expect H := by
  unfold primeTailLaw
  -- restrict to the factors in `T ℓ`
  have h1 := tensor_expect_restrict (V := Slot) (X := fun j : ↥(T L) => ZMod (j : ℕ))
    (fun j : ↥(T L) => μp (j : ℕ)) (fun j : ↥(T L) => (j : ℕ) ∈ T ℓ)
    (fun y => H (fun v j => y v ⟨⟨j.1, hT j.2⟩, j.2⟩))
  refine (h1.trans ?_)
  -- reindex the factors `{j : ↥(T L) // j ∈ T ℓ} ≃ ↥(T ℓ)`
  rw [tensor_expect_sum, tensor_expect_sum]
  let e2 : (∀ s : {j : ↥(T L) // (j : ℕ) ∈ T ℓ}, Slot → ZMod (s.1 : ℕ)) ≃
      (∀ j : ↥(T ℓ), Slot → ZMod (j : ℕ)) :=
    { toFun := fun a j => a ⟨⟨j.1, hT j.2⟩, j.2⟩
      invFun := fun a s => a ⟨s.1.1, s.2⟩
      left_inv := fun a => rfl
      right_inv := fun a => rfl }
  let σ : {j : ↥(T L) // (j : ℕ) ∈ T ℓ} ≃ ↥(T ℓ) :=
    { toFun := fun s => ⟨s.1.1, s.2⟩
      invFun := fun j => ⟨⟨j.1, hT j.2⟩, j.2⟩
      left_inv := fun s => rfl
      right_inv := fun j => rfl }
  refine Fintype.sum_equiv e2 _ _ (fun a => ?_)
  have hprod : ∏ s : {j : ↥(T L) // (j : ℕ) ∈ T ℓ}, (μp ((s.1 : ↥(T L)) : ℕ)).weight (a s) =
      ∏ j : ↥(T ℓ), (μp (j : ℕ)).weight (e2 a j) :=
    Fintype.prod_equiv σ _ _ (fun s => rfl)
  rw [hprod]
  rfl

/-- The marginal of the reference law `paperLaw` at the scale `L` on the prefix and the
primes of `T ℓ` is the reference law at the scale `ℓ`. -/
theorem paperLaw_marginal (μ₀ : FiniteLaw (Slot → ResidueSpace m₀))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q))
    {ℓ L : ℕ} (hT : T ℓ ⊆ T L)
    (G : (Slot → ResidueSpace m₀ × ∀ j : ↥(T ℓ), ZMod (j : ℕ)) → ℝ) :
    (paperLaw m₀ (J := fun L => ↥(T L)) (fun _ j => (j : ℕ)) μ₀ μp L).expect
        (fun w => G (fun v => ((w v).1, tailRestrict T hT (w v).2))) =
      (paperLaw m₀ (J := fun L => ↥(T L)) (fun _ j => (j : ℕ)) μ₀ μp ℓ).expect G := by
  unfold paperLaw
  rw [FiniteLaw.expect_slotProduct, FiniteLaw.expect_slotProduct]
  apply FiniteLaw.expect_congr
  intro z
  exact primeTailLaw_marginal T μp hT (fun t => G (fun v => (z v, t v)))

end Scales

section Translate

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]

/-- If the prefix law and every prime law are invariant under the simultaneous
translation of all slots (the case `r_p = 1` of (R3)), so is the reference law
`paperLaw = μ₀ ⊗ ⊗_q μ_q`, for every translation `s` of `X₀ × X_tail`. -/
theorem paperLaw_translate (μ₀ : FiniteLaw (Slot → ResidueSpace m₀))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q))
    (h₀ : ∀ (s₀ : ResidueSpace m₀) (F : (Slot → ResidueSpace m₀) → ℝ),
      μ₀.expect (fun z => F (fun v => z v + s₀)) = μ₀.expect F)
    (hq : ∀ (q : ℕ) [NeZero q] (r : ZMod q) (F : (Slot → ZMod q) → ℝ),
      (μp q).expect (fun z => F (fun v => z v + r)) = (μp q).expect F)
    (L : ℕ) (s : ResidueSpace m₀ × ResidueSpace (p L))
    (F : (Slot → ResidueSpace m₀ × ResidueSpace (p L)) → ℝ) :
    (paperLaw m₀ p μ₀ μp L).expect (fun w => F (fun v => w v + s)) =
      (paperLaw m₀ p μ₀ μp L).expect F := by
  unfold paperLaw
  rw [FiniteLaw.expect_slotProduct, FiniteLaw.expect_slotProduct]
  have htail : ∀ z : Slot → ResidueSpace m₀,
      (primeTailLaw p μp L).expect (fun t => F (fun v => (z v, t v) + s)) =
        (primeTailLaw p μp L).expect (fun t => F (fun v => (z v + s.1, t v))) := by
    intro z
    unfold primeTailLaw
    exact tensor_translate (fun j : J L => μp (p L j)) (fun j r F => hq (p L j) r F) s.2
      (fun t => F (fun v => (z v + s.1, t v)))
  simp only [htail]
  exact h₀ s.1 (fun z => (primeTailLaw p μp L).expect (fun t => F (fun v => (z v, t v))))

end Translate

end Sarkozy.PaperFrame
