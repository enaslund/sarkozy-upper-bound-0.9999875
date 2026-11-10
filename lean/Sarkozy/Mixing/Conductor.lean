module

public import Sarkozy.Mixing.Decay
public import Sarkozy.Moments.Holder

/-!
# Conductor decay with a finite prefix

`lem:record:prefix-conductor` of `paper/sections/06_lifts_sectors.tex`, with the Fourier
support condition stated through the exact-support sectors.

Setting. Finitely many coordinates `j ∈ K` with finite label sets `X_j` (the prefix group
`X'` and the tail fields `𝔽_p`), and for each coordinate a law `ρ_j` on `V → X_j` with
uniform one-slot marginals (`UniformSlot`). The product law `ρ = ⊗_j ρ_j` is the law of the
configuration `z ∈ ∏_j X_j^V`; the integral `∫ ∏_w g_w(z_w) dρ(z)` is `prodIntegral`
(configurations are stored coordinate by coordinate, as in `Sarkozy.tensorLaw`).

* `prodIntegral_eq`: conditioning on `z_{V∖{v}}`, the integral is `E_λ[(T g_v) R]` with `T`
  the conditional operator from slot `v` (the product of the coordinate conditional
  operators, `prodJoint`) and `R = ∏_{w ≠ v} g_w(y_w)`.
* `slot_conductor_decay` (abstract form): if the coordinate operators contract mean-zero
  functions by `δ_j`, and every nonzero exact-support component of `g_v` has weight
  `δ_S ≤ θ`, then `|∫ ∏_w g_w dρ| ≤ θ ‖g_v‖₂ ∏_{w≠v} ‖g_w‖_{2(d-1)}`.
* `prefix_conductor` (`lem:record:prefix-conductor`): with `δ_j = q_j^{-γ}` (`q_j = p` at a
  tail prime, `(γ,v)`-mixing; `q_j = 1` at the prefix, where no mixing is needed since the
  conditional operator is a contraction) and the support hypothesis "every nonzero component
  of `g_v` of exact support `S` has `H < C' q_S`", the bound is `(C'/H)^γ ‖g_v‖₂ ∏ ‖g_w‖_{2(d-1)}`.

The bridge from the paper's Fourier hypothesis (`ĝ_v(ξ) = 0` whenever `q(ξ) ≤ H`) to the
support hypothesis is the paper's: a character `ξ' + ξ_𝒯` of exact tail support `U` lies in
the sector `H_U` (spectator `X'`) and has conductor `q(ξ') q_U ≤ C' q_U`; so a nonzero
component in `H_U` forces `H < C' q_U`. This step involves characters and is not formalized
here. Real-valued `g_w` are treated (the paper's inputs `g^{I,D,s}` are real).
-/

@[expose] public section

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.Mixing

open Sarkozy.IndexSupport

section Slot

variable {V : Type*} [Fintype V] [DecidableEq V] {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- The joint law of `(z_v, z_{V∖{v}})` under a law on `V → Y`. -/
noncomputable def slotJoint (ρ : FiniteLaw (V → Y)) (v : V) :
    FiniteLaw (Y × ({w // w ≠ v} → Y)) :=
  ρ.map (Equiv.funSplitAt v Y)

theorem slotJoint_weight (ρ : FiniteLaw (V → Y)) (v : V) (x : Y × ({w // w ≠ v} → Y)) :
    (slotJoint ρ v).weight x = ρ.weight ((Equiv.funSplitAt v Y).symm x) := by
  classical
  unfold slotJoint FiniteLaw.map
  simp only
  rw [Finset.sum_eq_single ((Equiv.funSplitAt v Y).symm x)]
  · rw [ite_eq_left (Equiv.apply_symm_apply _ _)]
  · intro z _ hz
    rw [ite_eq_right]
    intro h
    exact hz (by rw [← h, Equiv.symm_apply_apply])
  · intro h
    exact absurd (mem_univ _) h

/-- Uniform one-slot marginal at `w`. -/
def UniformSlot [Nonempty Y] (ρ : FiniteLaw (V → Y)) (w : V) : Prop :=
  ∀ φ : Y → ℝ, ρ.expect (fun z => φ (z w)) = (FiniteLaw.uniform Y).expect φ

theorem srcWeight_slotJoint [Nonempty Y] {ρ : FiniteLaw (V → Y)} {v : V} (hρ : UniformSlot ρ v)
    (a : Y) : srcWeight (slotJoint ρ v) a = (Fintype.card Y : ℝ)⁻¹ := by
  have h := hρ (fun y => if y = a then 1 else 0)
  rw [FiniteLaw.expect_uniform] at h
  simp only [Finset.sum_ite_eq', mem_univ, ite_true] at h
  have hs : srcWeight (slotJoint ρ v) a = ρ.expect (fun z => if z v = a then 1 else 0) := by
    simp only [srcWeight, slotJoint_weight, FiniteLaw.expect, mul_ite, mul_one, mul_zero]
    rw [Fintype.sum_equiv (Equiv.funSplitAt v Y) (fun z => if z v = a then ρ.weight z else 0)
      (fun p => if p.1 = a then ρ.weight ((Equiv.funSplitAt v Y).symm p) else 0)
      (fun z => by simp only [Equiv.symm_apply_apply]; rfl), Fintype.sum_prod_type,
      Finset.sum_eq_single a]
    · simp
    · intro x _ hx
      simp [hx]
    · intro h
      exact absurd (mem_univ a) h
  rw [hs, h, one_div]

end Slot

section Product

variable {V : Type*} [Fintype V] [DecidableEq V] {K : Type*} [Fintype K] [DecidableEq K]
  {X : K → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]

/-- The integral `∫ ∏_w g_w(z_w) dρ(z)` for the product law `ρ = ⊗_j ρ_j`; a configuration is
stored coordinate by coordinate, `z_j ∈ X_j^V`, and the label at slot `w` is `(z_j w)_j`. -/
noncomputable def prodIntegral (ρ : ∀ j, FiniteLaw (V → X j)) (g : V → (∀ j, X j) → ℝ) : ℝ :=
  ∑ z : (∀ j, V → X j), (∏ j, (ρ j).weight (z j)) * ∏ w, g w (fun j => z j w)

/-- Splitting a configuration at the slot `v`. -/
def splitAt (v : V) : (∀ j, V → X j) ≃ (∀ j, X j) × (∀ j, {w // w ≠ v} → X j) where
  toFun z := (fun j => z j v, fun j w => z j w)
  invFun p j := (Equiv.funSplitAt v (X j)).symm (p.1 j, p.2 j)
  left_inv z := by
    funext j
    exact (Equiv.funSplitAt v (X j)).symm_apply_apply (z j)
  right_inv p := by
    refine Prod.ext (funext fun j => ?_) (funext fun j => funext fun w => ?_)
    · simp
    · simp [w.2]

/-- **Conditioning on the other slots.** `∫ ∏_w g_w dρ = E_λ[(T g_v) R]`, with `T` the
conditional operator of `⊗_j (z_{j,v}, z_{j,V∖v})` and `R(y) = ∏_{w ≠ v} g_w(y_w)`. -/
theorem prodIntegral_eq (ρ : ∀ j, FiniteLaw (V → X j)) (g : V → (∀ j, X j) → ℝ) (v : V) :
    prodIntegral ρ g =
      ∑ b, tgtWeight (prodJoint (fun j => slotJoint (ρ j) v)) b *
        condOp (prodJoint (fun j => slotJoint (ρ j) v)) (g v) b *
          ∏ w : {w // w ≠ v}, g w (fun j => b j w) := by
  unfold prodIntegral
  rw [Fintype.sum_equiv (splitAt v) _
    (fun p => (∏ j, (ρ j).weight ((splitAt v).symm p j)) *
      ∏ w, g w (fun j => (splitAt v).symm p j w)) (fun z => by rw [Equiv.symm_apply_apply])]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply sum_congr rfl
  intro b _
  rw [tgt_mul_condOp, Finset.sum_mul]
  apply sum_congr rfl
  intro a _
  have hw : (∏ j, (ρ j).weight ((splitAt v).symm (a, b) j)) =
      (prodJoint (fun j => slotJoint (ρ j) v)).weight (a, b) := by
    simp only [prodJoint, slotJoint_weight]
    rfl
  have hg : ∏ w, g w (fun j => (splitAt v).symm (a, b) j w) =
      g v a * ∏ w : {w // w ≠ v}, g w (fun j => b j w) := by
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ v]
    congr 1
    · congr 1
      funext j
      simp [splitAt]
    · apply prod_congr rfl
      intro w _
      congr 1
      funext j
      simp [splitAt, w.2]
  rw [hw, hg]
  ring

/-- The one-slot marginals of the target law of the product are uniform. -/
theorem tgt_slot_uniform [∀ j, Nonempty (X j)] (ρ : ∀ j, FiniteLaw (V → X j)) (v : V)
    {w : V} (hw : w ≠ v) (hρ : ∀ j, UniformSlot (ρ j) w) (φ : (∀ j, X j) → ℝ) :
    ∑ b, tgtWeight (prodJoint (fun j => slotJoint (ρ j) v)) b * φ (fun j => b j ⟨w, hw⟩) =
      (FiniteLaw.uniform (∀ j, X j)).expect φ := by
  classical
  -- the coordinate marginals
  have hcoord (j : K) (x : X j) :
      ∑ b : {u // u ≠ v} → X j, tgtWeight (slotJoint (ρ j) v) b * (if b ⟨w, hw⟩ = x then 1 else 0) =
        (Fintype.card (X j) : ℝ)⁻¹ := by
    have h := hρ j (fun y => if y = x then 1 else 0)
    rw [FiniteLaw.expect_uniform] at h
    simp only [Finset.sum_ite_eq', mem_univ, ite_true] at h
    rw [one_div] at h
    rw [← h]
    simp only [tgtWeight, slotJoint_weight, FiniteLaw.expect, Finset.sum_mul]
    rw [Finset.sum_comm]
    rw [← Fintype.sum_prod_type']
    exact Fintype.sum_equiv (Equiv.funSplitAt v (X j)).symm _ _ (fun p => by simp [hw])
  have hφ (b : ∀ j, {u // u ≠ v} → X j) : φ (fun j => b j ⟨w, hw⟩) =
      ∑ x : (∀ j, X j), φ x * ∏ j, (if b j ⟨w, hw⟩ = x j then 1 else 0) := by
    rw [Finset.sum_eq_single (fun j => b j ⟨w, hw⟩)]
    · simp
    · intro x _ hx
      have : ¬ ∀ j, b j ⟨w, hw⟩ = x j := fun h => hx (funext h).symm
      obtain ⟨j, hj⟩ := not_forall.mp this
      rw [Finset.prod_eq_zero (mem_univ j) (ite_eq_right hj), mul_zero]
    · intro h
      exact absurd (mem_univ _) h
  simp only [hφ, Finset.mul_sum, tgtWeight_prodJoint]
  rw [Finset.sum_comm, FiniteLaw.expect_uniform, div_eq_inv_mul, Finset.mul_sum]
  apply sum_congr rfl
  intro x _
  have hprod : ∑ b : (∀ j, {u // u ≠ v} → X j), (∏ j, tgtWeight (slotJoint (ρ j) v) (b j)) *
      (φ x * ∏ j, (if b j ⟨w, hw⟩ = x j then (1 : ℝ) else 0)) =
      φ x * ∏ j, ∑ b : {u // u ≠ v} → X j,
        tgtWeight (slotJoint (ρ j) v) b * (if b ⟨w, hw⟩ = x j then 1 else 0) := by
    rw [Fintype.prod_sum (fun j b => tgtWeight (slotJoint (ρ j) v) b *
      (if b ⟨w, hw⟩ = x j then (1 : ℝ) else 0)), Finset.mul_sum]
    apply sum_congr rfl
    intro b _
    rw [Finset.prod_mul_distrib]
    ring
  rw [hprod]
  simp only [hcoord]
  rw [Finset.prod_inv_distrib, ← Nat.cast_prod, ← Fintype.card_pi]
  ring

end Product

section Decay

variable {V : Type*} [Fintype V] [DecidableEq V] {K : Type*} [Fintype K] [DecidableEq K]
  {X : K → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] [∀ j, Nonempty (X j)]

/-- **Conductor decay, abstract form.** Let `ρ_j` have uniform one-slot marginals, let the
conditional operator of `ρ_j` from slot `v` contract mean-zero functions by `δ_j`, and let
every nonzero exact-support component `g_{v,S}` of `g_v` have `δ_S ≤ θ` (`θ ≥ 0`). Then, with
norms for the uniform law on `∏_j X_j` and `d = |V| ≥ 2`,
`|∫ ∏_w g_w dρ| ≤ θ ‖g_v‖₂ ∏_{w ≠ v} ‖g_w‖_{2(d-1)}`. -/
theorem slot_conductor_decay (ρ : ∀ j, FiniteLaw (V → X j)) (v : V)
    (hV : 2 ≤ Fintype.card V) (hunif : ∀ j w, UniformSlot (ρ j) w)
    {δ : K → ℝ} (hmix : ∀ j, ContractsMeanZero (slotJoint (ρ j) v) (δ j))
    {θ : ℝ} (hθ : 0 ≤ θ) (g : V → (∀ j, X j) → ℝ)
    (hsupp : ∀ l : K → Bool, sectorProj X l *ᵥ g v ≠ 0 → supportWeight δ l ^ 2 ≤ θ ^ 2) :
    |prodIntegral ρ g| ≤ θ * (FiniteLaw.uniform (∀ j, X j)).lpNorm 2 (g v) *
      ∏ w : {w // w ≠ v}, (FiniteLaw.uniform (∀ j, X j)).lpNorm (2 * (Fintype.card V - 1)) (g w) := by
  set κ := prodJoint (fun j => slotJoint (ρ j) v)
  have hsrc (j : K) (a : X j) : srcWeight (slotJoint (ρ j) v) a = (Fintype.card (X j) : ℝ)⁻¹ :=
    srcWeight_slotJoint (hunif j v) a
  -- the target law as a finite law
  let lam : FiniteLaw (∀ j, {w // w ≠ v} → X j) :=
    ⟨tgtWeight κ, tgtWeight_nonneg κ, sum_tgtWeight κ⟩
  -- the energy bound for `T g_v`
  have hdecay := (exact_support_decay (fun j => slotJoint (ρ j) v) hsrc hmix (g v)).2
  have henergy : ∑ b, tgtWeight κ b * condOp κ (g v) b ^ 2 ≤
      θ ^ 2 * (FiniteLaw.uniform (∀ j, X j)).expect (fun a => g v a ^ 2) := by
    apply hdecay.trans
    have hterm (l : K → Bool) : supportWeight δ l ^ 2 *
        (FiniteLaw.uniform (∀ j, X j)).expect (fun a => (sectorProj X l *ᵥ g v) a ^ 2) ≤
        θ ^ 2 * (FiniteLaw.uniform (∀ j, X j)).expect (fun a => (sectorProj X l *ᵥ g v) a ^ 2) := by
      by_cases hl : sectorProj X l *ᵥ g v = 0
      · rw [hl]
        simp
      · exact mul_le_mul_of_nonneg_right (hsupp l hl)
          ((FiniteLaw.uniform _).expect_nonneg (fun a => sq_nonneg _))
    apply (Finset.sum_le_sum (fun l _ => hterm l)).trans
    rw [← Finset.mul_sum]
    apply le_of_eq
    congr 1
    simp only [FiniteLaw.expect_uniform, ← Finset.sum_div]
    congr 1
    have := sum_sectorProj_sq (g v) (A := X)
    simp only [dotProduct, ← sq] at this
    exact this
  -- Hölder with exponent 2 for `T g_v` and `2(d-1)` for the other slots
  set n := Fintype.card {w // w ≠ v} with hn
  have hn' : n = Fintype.card V - 1 := by
    rw [hn, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  have hnpos : 1 ≤ n := by omega
  let p : Option {w // w ≠ v} → ℝ := fun i => match i with
    | none => 2
    | some _ => 2 * (n : ℝ)
  let F : Option {w // w ≠ v} → (∀ j, {w // w ≠ v} → X j) → ℝ := fun i b => match i with
    | none => condOp κ (g v) b
    | some w => g w (fun j => b j w)
  have hp (i : Option {w // w ≠ v}) : 0 < p i := by
    cases i
    · norm_num
    · change (0 : ℝ) < 2 * (n : ℝ)
      have : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
      linarith
  have hsum : ∑ i, 1 / p i = 1 := by
    rw [Fintype.sum_option]
    change 1 / (2 : ℝ) + ∑ _w : {w // w ≠ v}, 1 / (2 * (n : ℝ)) = 1
    rw [sum_const, card_univ, ← hn, nsmul_eq_mul]
    have : (n : ℝ) ≠ 0 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
      linarith
    field_simp
    ring
  have hH := lam.abs_expect_prod_le_lpNorm p hp hsum F
  have hint : prodIntegral ρ g = lam.expect (fun b => ∏ i, F i b) := by
    rw [prodIntegral_eq ρ g v]
    simp only [FiniteLaw.expect, Fintype.prod_option, F, lam]
    apply sum_congr rfl
    intro b _
    ring
  rw [hint]
  apply hH.trans
  rw [Fintype.prod_option]
  change lam.lpNorm 2 (condOp κ (g v)) * ∏ w : {w // w ≠ v}, lam.lpNorm (2 * (n : ℝ)) (fun b => g w (fun j => b j w)) ≤ _
  have hslot (w : {w // w ≠ v}) : lam.lpNorm (2 * (n : ℝ)) (fun b => g w (fun j => b j w)) =
      (FiniteLaw.uniform (∀ j, X j)).lpNorm (2 * (Fintype.card V - 1)) (g w) := by
    have hcast : (2 * (n : ℝ)) = 2 * ((Fintype.card V : ℝ) - 1) := by
      rw [hn']
      have : 1 ≤ Fintype.card V := by omega
      push_cast [Nat.cast_sub this]
      ring
    rw [hcast]
    unfold FiniteLaw.lpNorm FiniteLaw.moment
    congr 1
    exact tgt_slot_uniform ρ v w.2 (fun j => hunif j w) (fun x => |g w x| ^ (2 * ((Fintype.card V : ℝ) - 1)))
  simp only [hslot]
  have hT : lam.lpNorm 2 (condOp κ (g v)) ≤ θ * (FiniteLaw.uniform (∀ j, X j)).lpNorm 2 (g v) := by
    have h1 : lam.lpNorm 2 (condOp κ (g v)) = Real.sqrt (∑ b, tgtWeight κ b * condOp κ (g v) b ^ 2) := by
      unfold FiniteLaw.lpNorm FiniteLaw.moment
      rw [Real.sqrt_eq_rpow]
      congr 1
      simp only [FiniteLaw.expect, lam]
      apply sum_congr rfl
      intro b _
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    have h2 : (FiniteLaw.uniform (∀ j, X j)).lpNorm 2 (g v) =
        Real.sqrt ((FiniteLaw.uniform (∀ j, X j)).expect (fun a => g v a ^ 2)) := by
      unfold FiniteLaw.lpNorm FiniteLaw.moment
      rw [Real.sqrt_eq_rpow]
      congr 1
      apply FiniteLaw.expect_congr
      intro a
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    rw [h1, h2]
    calc Real.sqrt (∑ b, tgtWeight κ b * condOp κ (g v) b ^ 2)
        ≤ Real.sqrt (θ ^ 2 * (FiniteLaw.uniform (∀ j, X j)).expect (fun a => g v a ^ 2)) :=
          Real.sqrt_le_sqrt henergy
      _ = θ * Real.sqrt ((FiniteLaw.uniform (∀ j, X j)).expect (fun a => g v a ^ 2)) := by
          rw [Real.sqrt_mul (sq_nonneg θ), Real.sqrt_sq hθ]
  have hprod_nonneg : 0 ≤ ∏ w : {w // w ≠ v},
      (FiniteLaw.uniform (∀ j, X j)).lpNorm (2 * (Fintype.card V - 1)) (g w) :=
    Finset.prod_nonneg (fun w _ => FiniteLaw.lpNorm_nonneg _ _ _)
  calc _ ≤ θ * (FiniteLaw.uniform (∀ j, X j)).lpNorm 2 (g v) *
        ∏ w : {w // w ≠ v}, (FiniteLaw.uniform (∀ j, X j)).lpNorm (2 * (Fintype.card V - 1)) (g w) :=
        mul_le_mul_of_nonneg_right hT hprod_nonneg
    _ = _ := rfl

end Decay

section Conductors

variable {K : Type*} [Fintype K]

/-- The conductor `q_S = ∏_{j ∈ S} q_j` of an exact support `S = {j : l_j}`. -/
def supportConductor (q : K → ℕ) (l : K → Bool) : ℝ := ∏ j, if l j then (q j : ℝ) else 1

theorem supportConductor_pos {q : K → ℕ} (hq : ∀ j, 0 < q j) (l : K → Bool) :
    0 < supportConductor q l :=
  Finset.prod_pos (fun j _ => by split_ifs <;> [exact_mod_cast hq j; exact one_pos])

/-- With `δ_j = q_j^{-γ}`, the sector weight is `δ_S = q_S^{-γ}`. -/
theorem supportWeight_rpow {q : K → ℕ} (γ : ℝ) (l : K → Bool) :
    supportWeight (fun j => (q j : ℝ) ^ (-γ)) l = supportConductor q l ^ (-γ) := by
  unfold supportWeight supportConductor
  rw [← Real.finsetProd_rpow _ _ (fun j _ => by split_ifs <;> positivity)]
  apply prod_congr rfl
  intro j _
  split_ifs
  · rfl
  · rw [Real.one_rpow]

end Conductors

/-- Every conditional operator contracts mean-zero functions by `1` (conditional Jensen); this
is the case `q = 1` of the mixing hypothesis (the prefix coordinates). -/
theorem contractsMeanZero_one {A B : Type*} [Fintype A] [Fintype B] (κ : FiniteLaw (A × B)) :
    ContractsMeanZero κ 1 := by
  intro f _
  rw [one_pow, one_mul]
  exact condOp_contraction κ f

section Prefix

variable {V : Type*} [Fintype V] [DecidableEq V] {K : Type*} [Fintype K] [DecidableEq K]
  {X : K → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] [∀ j, Nonempty (X j)]

/-- **Conductor decay with a finite prefix** (`lem:record:prefix-conductor`), with the support
hypothesis in sector form. Coordinates `j` carry laws `ρ_j` on `X_j^V` with uniform one-slot
marginals and conditional operators from the slot `v` that contract mean-zero functions by
`q_j^{-γ}` (`(γ,v)`-mixing at a tail prime `q_j = p`; `q_j = 1` for the prefix coordinates,
where `contractsMeanZero_one` supplies the hypothesis). If every nonzero exact-support
component `g_{v,S}` of `g_v` has `H < C' q_S`, then
`|∫ ∏_w g_w(z_w) dρ| ≤ (C'/H)^γ ‖g_v‖₂ ∏_{w≠v} ‖g_w‖_{2(d-1)}`, `d = |V| ≥ 2`. -/
theorem prefix_conductor (ρ : ∀ j, FiniteLaw (V → X j)) (v : V) (hV : 2 ≤ Fintype.card V)
    (hunif : ∀ j w, UniformSlot (ρ j) w) (q : K → ℕ) (hq : ∀ j, 0 < q j) {γ : ℝ} (hγ : 0 ≤ γ)
    (hmix : ∀ j, ContractsMeanZero (slotJoint (ρ j) v) ((q j : ℝ) ^ (-γ)))
    {C' H : ℝ} (hC' : 0 < C') (hH : 0 < H) (g : V → (∀ j, X j) → ℝ)
    (hsupp : ∀ l : K → Bool, sectorProj X l *ᵥ g v ≠ 0 → H < C' * supportConductor q l) :
    |prodIntegral ρ g| ≤ (C' / H) ^ γ * (FiniteLaw.uniform (∀ j, X j)).lpNorm 2 (g v) *
      ∏ w : {w // w ≠ v}, (FiniteLaw.uniform (∀ j, X j)).lpNorm (2 * (Fintype.card V - 1)) (g w) := by
  apply slot_conductor_decay ρ v hV hunif hmix (Real.rpow_nonneg (div_pos hC' hH).le γ) g
  intro l hl
  have hlt := hsupp l hl
  have hqS := supportConductor_pos hq l
  rw [supportWeight_rpow]
  have hle : supportConductor q l ^ (-γ) ≤ (C' / H) ^ γ := by
    rw [Real.rpow_neg hqS.le, ← Real.inv_rpow hqS.le]
    apply Real.rpow_le_rpow (inv_nonneg.mpr hqS.le) _ hγ
    rw [inv_le_iff_one_le_mul₀ hqS, div_mul_eq_mul_div, one_le_div hH]
    nlinarith
  have h0 : 0 ≤ supportConductor q l ^ (-γ) := Real.rpow_nonneg hqS.le _
  exact pow_le_pow_left₀ h0 hle 2

end Prefix

end Sarkozy.Mixing
