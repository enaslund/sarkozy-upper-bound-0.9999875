module

public import Sarkozy.OpsVariance.Forms
public import Sarkozy.SignedComponents.Support
public import Sarkozy.NormBoundsPaper3.ELaw

@[expose] public section

/-!
# Zero marginals of the matching changes (`eq:record:zero-marginal`)

`paper/sections/21_middle_records.tex`, `subsec:record:e_side`: "At `ι` the reference's two-layer
matching record is the uniform law of pairs of disjoint halves, `K^E_0 = I_×/z^E_0`, with both half
marginals `ν_E`", and `lem:record:e-law`(a): the replacement `K₁` has "two half marginals both
equal `ν_E`"; `lem:record:exact-marginal-e`: "the block record is the tensor product over the
primes"; `paper/sections/22_variance.tex`, `eq:record:zero-marginal`.

A record of a middle block is emitted from a two-layer law `λ` on `O × Fin 2` by a pattern `φ`
(`emit λ (midEmission φ)`): at the reserved cut `ι` its plus half reads layer `0` and its minus
half reads layer `1` (B8's `plusHalf_mid`, `minusHalf_mid`). So:

* **`zeroMarginals_emit`**: if two two-layer laws have the same law at each layer, the difference
  of their emissions by one pattern has zero marginals at `ι`;
* **`tensor_layer_expect`**: the layer laws of a tensor over the primes are the tensors of the layer
  laws (by `tensorLaw_fubini` on indicators);
* `layer_expect_eq_of_tw`: NB3's layer law `tw μ (lay ℓ)` determines the layer expectations;
* at one prime, `eLaw` (`K₁`) and V1's `E` law have the layer law `ν_E` (NB3's `P3_row`, `P3_col`,
  `tw_match`): `eLaw_layer`, `matchLaw_layer`;
* **`zeroMarginals_matchRec`**: at a middle block (every prime `≡ 3 (mod 4)`, `≥ 7`), the matching
  replacement `matchRec s = ⊗_p K₁` and the record `Π_{E_s}` (V1's `E` law, emitted by `E_s`) have
  the same half marginals, so `matchRec s − Π_{E_s}` has zero marginals. This is
  `eq:record:zero-marginal` for the matching changes `Δ_{E_s} = c (ν'_{E_s} − Π_{E_s})` of B7.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.OpsVariance

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.RecordExpansion Sarkozy.Labellings
open Sarkozy.SignedComponents (plusHalf_mid minusHalf_mid halfRead)
open Sarkozy.NormBoundsPaper3 (tw rd lay m3 P3 P3_row P3_col tw_match cmT_row cmT_col)
open Sarkozy.MiddleComparison (eLaw eSet blockE_nonempty matchRec)
open Sarkozy.PartVRecords (ClassThreeBlock)

/-! ## Emissions with equal layer laws -/

section Emission

variable {X : Type} [Fintype X] [DecidableEq X] {O : Type} [Fintype O] [DecidableEq O]

omit [DecidableEq X] in
/-- The cut form of a nonnegative weight against `1` on the right: the expectation of the plus
half. -/
theorem form_one_right_eq_expect (μ : FiniteLaw (Slot → X)) (F : (reservedCut.Half → X) → ℝ) :
    reservedCut.form (signedIntegral μ.weight) F 1 =
      μ.expect (fun z => F (fun v : reservedCut.Half => z v.1)) := by
  unfold ReflectionCut.form FiniteLaw.expect
  change ∑ z, μ.weight z * (F (fun v => z v.1) * 1) = _
  simp only [mul_one]

omit [DecidableEq X] in
/-- The cut form against `1` on the left: the expectation of the minus half. -/
theorem form_one_left_eq_expect (μ : FiniteLaw (Slot → X)) (G : (reservedCut.Half → X) → ℝ) :
    reservedCut.form (signedIntegral μ.weight) 1 G =
      μ.expect (fun z => G (fun v : reservedCut.Half => z (reservedCut.flip v.1))) := by
  unfold ReflectionCut.form FiniteLaw.expect
  change ∑ z, μ.weight z * (1 * G (fun v => z (reservedCut.flip v.1))) = _
  simp only [one_mul]

/-- **Equal layer laws give zero marginals.** If the two-layer laws `λ, λ'` have the same law at
each layer, then the emission by any pattern `φ` of `λ'` minus that of `λ` annihilates the
constants on both sides of `ι`. -/
theorem zeroMarginals_emit (lam lam' : FiniteLaw (O × Fin 2 → X)) (φ : ZMod 6 → O)
    (h : ∀ (ℓ : Fin 2) (g : (O → X) → ℝ),
      lam'.expect (fun y => g (fun o => y (o, ℓ))) = lam.expect (fun y => g (fun o => y (o, ℓ)))) :
    ZeroMarginals reservedCut (signedIntegral (emit lam' (midEmission φ)).weight -
      signedIntegral (emit lam (midEmission φ)).weight) := by
  constructor
  · intro F
    rw [form_sub_law, form_one_right_eq_expect, form_one_right_eq_expect, expect_emit,
      expect_emit]
    have e : ∀ y : O × Fin 2 → X, F (fun v : reservedCut.Half => (y ∘ midEmission φ) v.1) =
        (fun t : O → X => F (fun v => t (φ v.1.1))) (fun o => y (o, 0)) := by
      intro y
      have := plusHalf_mid (X := X) φ y
      simp only at this ⊢
      exact congrArg F this
    simp only [e]
    rw [sub_eq_zero]
    exact h 0 (fun t => F (fun v => t (φ v.1.1)))
  · intro G
    rw [form_sub_law, form_one_left_eq_expect, form_one_left_eq_expect, expect_emit,
      expect_emit]
    have e : ∀ y : O × Fin 2 → X,
        G (fun v : reservedCut.Half => (y ∘ midEmission φ) (reservedCut.flip v.1)) =
        (fun t : O → X => G (fun v => t (φ v.1.1))) (fun o => y (o, 1)) := by
      intro y
      have := minusHalf_mid (X := X) φ y
      simp only at this ⊢
      exact congrArg G this
    simp only [e]
    rw [sub_eq_zero]
    exact h 1 (fun t => G (fun v => t (φ v.1.1)))

end Emission

/-! ## Layer laws of tensors -/

section Tensor

variable {J : Type} [Fintype J] [DecidableEq J] {X : J → Type} [∀ j, Fintype (X j)]
  [∀ j, DecidableEq (X j)] {O : Type} [Fintype O] [DecidableEq O]

/-- **The layer laws of a tensor are the tensors of the layer laws**: if at every factor `j` the
law of `μ'_j` at the layer `ℓ` is that of `μ_j` at the layer `ℓ'`, the same holds for their
tensors. -/
theorem tensor_layer_expect₂ (μ μ' : ∀ j, FiniteLaw (O × Fin 2 → X j)) (ℓ ℓ' : Fin 2)
    (h : ∀ j (g : (O → X j) → ℝ), (μ' j).expect (fun y => g (fun o => y (o, ℓ))) =
      (μ j).expect (fun y => g (fun o => y (o, ℓ'))))
    (G : (O → ∀ j, X j) → ℝ) :
    (FiniteLaw.tensor μ').expect (fun y => G (fun o => y (o, ℓ))) =
      (FiniteLaw.tensor μ).expect (fun y => G (fun o => y (o, ℓ'))) := by
  classical
  -- decompose `G` over the values `t` of the layer, and the indicator over the factors
  have hdec : ∀ (ℓ : Fin 2) (y : O × Fin 2 → ∀ j, X j), G (fun o => y (o, ℓ)) =
      ∑ t : O → ∀ j, X j,
        G t * ∏ j, (if (fun o => y (o, ℓ) j) = (fun o => t o j) then 1 else 0) := by
    intro ℓ y
    rw [sum_eq_single (fun o => y (o, ℓ))]
    · rw [prod_eq_one fun j _ => by simp, mul_one]
    · intro t _ ht
      have : ∃ j, (fun o => y (o, ℓ) j) ≠ (fun o => t o j) := by
        by_contra hall
        push Not at hall
        apply ht
        funext o j
        exact (congrFun (hall j) o).symm
      obtain ⟨j, hj⟩ := this
      rw [prod_eq_zero (mem_univ j) (by simp [hj]), mul_zero]
    · intro hn
      exact absurd (mem_univ _) hn
  have hexp : ∀ (ℓ : Fin 2) (ν : ∀ j, FiniteLaw (O × Fin 2 → X j)) (t : O → ∀ j, X j),
      (FiniteLaw.tensor ν).expect (fun y =>
        ∏ j, (if (fun o => y (o, ℓ) j) = (fun o => t o j) then (1 : ℝ) else 0)) =
      ∏ j, (ν j).expect (fun y => if (fun o => y (o, ℓ)) = (fun o => t o j) then 1 else 0) := by
    intro ℓ ν t
    have e1 : (FiniteLaw.tensor ν).expect (fun y =>
        ∏ j, (if (fun o => y (o, ℓ) j) = (fun o => t o j) then (1 : ℝ) else 0)) =
        signedIntegral (FiniteLaw.tensor ν).weight (fun y =>
          ∏ j, (fun yj : O × Fin 2 → X j =>
            if (fun o => yj (o, ℓ)) = (fun o => t o j) then (1 : ℝ) else 0) (fun v => y v j)) :=
      rfl
    rw [e1, FiniteLaw.signedIntegral_tensor]
    exact tensorLaw_fubini _ (fun j yj => if (fun o => yj (o, ℓ)) = (fun o => t o j) then (1 : ℝ)
      else 0)
  have hlin : ∀ (ℓ : Fin 2) (ν : ∀ j, FiniteLaw (O × Fin 2 → X j)),
      (FiniteLaw.tensor ν).expect (fun y => G (fun o => y (o, ℓ))) =
        ∑ t : O → ∀ j, X j, G t * ∏ j, (ν j).expect
          (fun y => if (fun o => y (o, ℓ)) = (fun o => t o j) then 1 else 0) := by
    intro ℓ ν
    unfold FiniteLaw.expect
    simp_rw [hdec ℓ]
    rw [show (∑ y, (FiniteLaw.tensor ν).weight y * ∑ t : O → ∀ j, X j, G t *
        ∏ j, (if (fun o => y (o, ℓ) j) = (fun o => t o j) then (1 : ℝ) else 0)) =
        ∑ t : O → ∀ j, X j, G t * ∑ y, (FiniteLaw.tensor ν).weight y *
        ∏ j, (if (fun o => y (o, ℓ) j) = (fun o => t o j) then (1 : ℝ) else 0) by
      simp_rw [mul_sum]
      rw [sum_comm]
      exact sum_congr rfl fun t _ => sum_congr rfl fun y _ => by ring]
    refine sum_congr rfl fun t _ => ?_
    congr 1
    have := hexp ℓ ν t
    unfold FiniteLaw.expect at this
    exact this
  rw [hlin ℓ μ', hlin ℓ' μ]
  refine sum_congr rfl fun t _ => ?_
  congr 1
  exact prod_congr rfl fun j _ => h j (fun s => if s = (fun o => t o j) then 1 else 0)

/-- `tensor_layer_expect₂` at one layer. -/
theorem tensor_layer_expect (μ μ' : ∀ j, FiniteLaw (O × Fin 2 → X j)) (ℓ : Fin 2)
    (h : ∀ j (g : (O → X j) → ℝ), (μ' j).expect (fun y => g (fun o => y (o, ℓ))) =
      (μ j).expect (fun y => g (fun o => y (o, ℓ))))
    (G : (O → ∀ j, X j) → ℝ) :
    (FiniteLaw.tensor μ').expect (fun y => G (fun o => y (o, ℓ))) =
      (FiniteLaw.tensor μ).expect (fun y => G (fun o => y (o, ℓ))) :=
  tensor_layer_expect₂ μ μ' ℓ ℓ h G

end Tensor

/-! ## The layer laws at one prime -/

section Prime

variable {p : ℕ} [Fact p.Prime]

/-- The triple `((x₀, x₁), x₂)` of a function on `Fin 3`. -/
def trip {F : Type} (t : Fin 3 → F) : (F × F) × F := ((t 0, t 1), t 2)

/-- The function on `Fin 3` of a triple. -/
def untrip {F : Type} (x : (F × F) × F) : Fin 3 → F := ![x.1.1, x.1.2, x.2]

theorem untrip_rd {W F : Type} (z : W → F) (u : Fin 3 → W) :
    untrip (rd z u) = fun o => z (u o) := by
  funext o
  fin_cases o <;> rfl

/-- **NB3's layer law determines the layer expectations**:
`E_μ g(y_{·,ℓ}) = ∑_x g(x) tw μ (lay ℓ) x`. -/
theorem layer_expect_eq_of_tw {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F]
    (μ μ' : FiniteLaw (W → F)) (u : Fin 3 → W) (h : ∀ x, tw μ' u x = tw μ u x)
    (g : (Fin 3 → F) → ℝ) :
    μ'.expect (fun y => g (fun o => y (u o))) = μ.expect (fun y => g (fun o => y (u o))) := by
  have hrep : ∀ ν : FiniteLaw (W → F),
      ν.expect (fun y => g (fun o => y (u o))) = ∑ x, g (untrip x) * tw ν u x := by
    intro ν
    unfold tw FiniteLaw.expect
    simp_rw [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun z _ => ?_
    rw [sum_eq_single (rd z u)]
    · simp only [↓reduceIte, mul_one, untrip_rd]
      ring
    · intro x _ hx
      simp [Ne.symm hx]
    · intro hn
      exact absurd (mem_univ _) hn
  rw [hrep μ', hrep μ]
  exact sum_congr rfl fun x _ => by rw [h x]

/-- **`K₁` has the layer laws `ν_E`** (NB3's `P3_row`, `P3_col`: both half marginals of `K₁` are
`ν_E`). -/
theorem eLaw_layer (hE : (eSet (F := ZMod p)).Nonempty) (hp : 7 ≤ p) (h3 : p % 4 = 3)
    (ℓ : Fin 2) (x : (ZMod p × ZMod p) × ZMod p) : tw (eLaw hE) (lay ℓ) x = m3 p x := by
  rcases Fin.exists_fin_two.mp ⟨ℓ, rfl⟩ with h | h
  · rw [h, ← cmT_row (eLaw hE) (lay 0) (lay 1) x]
    exact P3_row hE hp h3 x
  · rw [h, ← cmT_col (eLaw hE) (lay 0) (lay 1) x]
    exact P3_col hE hp h3 x

/-- **V1's `E` law (six distinct labels) has the layer laws `ν_E`** (NB3's `tw_match`). -/
theorem matchLaw_layer (hne : (injLabellings (ZMod p) (matchGraph (Fin 2))).Nonempty)
    (hp : 3 ≤ p) (ℓ : Fin 2) (x : (ZMod p × ZMod p) × ZMod p) :
    tw (graphLaw (matchGraph (Fin 2)) hne) (lay ℓ) x = m3 p x :=
  tw_match hne hp ℓ x

end Prime

/-! ## The matching changes of a middle block -/

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- **`eq:record:zero-marginal` for the matching records of a middle block**: the replacement
`matchRec s = ⊗_p K₁` (emitted by `E_s`) and the record `Π_{E_s}` of V1's middle field laws (the
`E` law, six distinct labels at every prime, emitted by `E_s`) have the same half marginals at `ι`,
so their difference annihilates the constants on both sides. -/
theorem zeroMarginals_matchRec (h : ClassThreeBlock pr) (hne : MiddleNonempty pr)
    (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (s : Fin 2) :
    ZeroMarginals reservedCut (signedIntegral (matchRec pr h s).weight -
      signedIntegral (midComponent (middleBlockFieldLaws pr hne root)
        (true, ⟨PType.S, s⟩)).weight) := by
  apply zeroMarginals_emit
    (FiniteLaw.tensor fun i => graphLaw (matchGraph (Fin 2)) (hne.E2 i))
    (FiniteLaw.tensor fun i => eLaw (blockE_nonempty pr h i)) (matching s)
  intro ℓ g
  apply tensor_layer_expect
  intro i g'
  apply layer_expect_eq_of_tw (u := lay ℓ)
  intro x
  rw [eLaw_layer _ (h.ge7 i) (h.mod4 i), matchLaw_layer _ (by have := h.ge7 i; omega)]

end Block

/-! ## The fold changes of a middle block -/

section Fold

variable {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ} [∀ i, Fact (pr i).Prime]

/-- **A law invariant under the layer swap has the same law at both layers.** -/
theorem layer_one_eq_zero {X : Type} [Fintype X] [DecidableEq X]
    (lam : FiniteLaw (Fin 3 × Fin 2 → X))
    (hsw : ∀ y, lam.weight (y ∘ layerSwapMap (Fin 3)) = lam.weight y) (g : (Fin 3 → X) → ℝ) :
    lam.expect (fun y => g (fun o => y (o, 1))) = lam.expect (fun y => g (fun o => y (o, 0))) := by
  unfold FiniteLaw.expect
  let e : (Fin 3 × Fin 2 → X) ≃ (Fin 3 × Fin 2 → X) :=
    { toFun := fun y => y ∘ layerSwapMap (Fin 3)
      invFun := fun y => y ∘ layerSwapMap (Fin 3)
      left_inv := fun y => by
        funext w
        rcases w with ⟨o, ℓ⟩
        simp [layerSwapMap, Equiv.swap_apply_self]
      right_inv := fun y => by
        funext w
        rcases w with ⟨o, ℓ⟩
        simp [layerSwapMap, Equiv.swap_apply_self] }
  rw [← Equiv.sum_comp e]
  refine sum_congr rfl fun y _ => ?_
  change lam.weight (y ∘ layerSwapMap (Fin 3)) *
      g (fun o => (y ∘ layerSwapMap (Fin 3)) (o, 1)) = _
  rw [hsw]
  congr 2

/-- **`eq:record:zero-marginal` for the components of the fold records**: each normalized
component `⊗_p P_{c,p}` of the signed record of `F_{j+1}` (both of its half marginals are `m₀`,
B8's `FoldPrimeComponents.half`) and the fold record `Π_{F_{j+1}}` of V1's middle field laws (the
fold graph law, invariant under the layer swap) have the same half marginals at `ι`. -/
theorem zeroMarginals_foldRec (hne : MiddleNonempty pr)
    (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (C : SignedComponents.FoldComponents pr hne)
    (j : Fin 2) (c : Fin 3) :
    ZeroMarginals reservedCut (signedIntegral (SignedComponents.foldRec C j c).weight -
      signedIntegral (midComponent (middleBlockFieldLaws pr hne root)
        (true, ⟨PType.D, MiddleComparison.foldPat j⟩)).weight) := by
  apply zeroMarginals_emit
    (FiniteLaw.tensor fun i => graphLaw (foldGraph (Fin 2)) (hne.F2 i))
    (FiniteLaw.tensor fun i => (C i).law j c) (fold (MiddleComparison.foldPat j))
  intro ℓ g
  have h0 := tensor_layer_expect₂ (fun i => graphLaw (foldGraph (Fin 2)) (hne.F2 i))
    (fun i => (C i).law j c) ℓ 0 (fun i g' => (C i).half j c ℓ g') g
  rw [h0]
  rcases Fin.exists_fin_two.mp ⟨ℓ, rfl⟩ with h | h
  · rw [h]
  · rw [h]
    exact (layer_one_eq_zero _ (fun y => blockGraphLaw_weight_auto pr (foldGraph (Fin 2)) hne.F2
      (layerSwapMap (Fin 3)) foldGraph_layerSwap y) g).symm

/-- **A signed combination of mass one of laws with the half marginals of `Π`**: if every
`X_c − Π` annihilates the constants and `∑_c a_c = 1`, so does `∑_c a_c X_c − Π`. -/
theorem zeroMarginals_comb {W Y : Type} [Fintype W] [DecidableEq W] {c : ReflectionCut W}
    (a : Fin 3 → ℝ) (ha : ∑ k, a k = 1) (Xc : Fin 3 → ((W → Y) → ℝ) →ₗ[ℝ] ℝ)
    (P : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) (h : ∀ k, ZeroMarginals c (Xc k - P)) :
    ZeroMarginals c ((∑ k, a k • Xc k) - P) := by
  have e : (∑ k, a k • Xc k) - P = ∑ k, a k • (Xc k - P) := by
    have : P = ∑ k, a k • P := by rw [← sum_smul, ha, one_smul]
    conv_lhs => rw [this]
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun k _ => (smul_sub (a k) (Xc k) P).symm
  rw [e]
  constructor
  · intro F
    rw [Variance.form_sum_smul]
    exact sum_eq_zero fun k _ => by rw [(h k).1 F, mul_zero]
  · intro G
    rw [Variance.form_sum_smul]
    exact sum_eq_zero fun k _ => by rw [(h k).2 G, mul_zero]

/-- **`eq:record:zero-marginal` for the signed fold records**: the replacement
`K_{t,𝔅} = ∑_c a_c ⊗_p P_{c,p}` (`signedCoef t`, mass one) of `F_{j+1}` minus its record. -/
theorem zeroMarginals_signedFold (hne : MiddleNonempty pr)
    (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (C : SignedComponents.FoldComponents pr hne)
    (t : ℝ) (j : Fin 2) :
    ZeroMarginals reservedCut
      ((∑ k, MiddleComparison.signedCoef t k •
          signedIntegral (SignedComponents.foldRec C j k).weight) -
        signedIntegral (midComponent (middleBlockFieldLaws pr hne root)
          (true, ⟨PType.D, MiddleComparison.foldPat j⟩)).weight) :=
  zeroMarginals_comb _ (MiddleComparison.sum_signedCoef t) _ _
    fun k => zeroMarginals_foldRec hne root C j k

end Fold

end Sarkozy.OpsVariance
