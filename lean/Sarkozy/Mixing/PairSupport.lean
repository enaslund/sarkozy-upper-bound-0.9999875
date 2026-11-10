module

public import Sarkozy.Mixing.Conductor

/-!
# Decay by exact pair support

`lem:tr:pairsupport` of `paper/sections/06_lifts_sectors.tex`.

For each tail coordinate `p` let `ρ_p` be a law on `X_p^V` whose marginal on the block
`Z = {u, v}` is uniform and which is `(γ, Z)`-mixing (`IsMixing (ρ p) Z (q_p^{-γ})`), and
let `ρ = ⊗_p ρ_p`. For `U` a set of coordinates let `E_U` be the conditional expectation,
under the uniform law on the block labels, onto the block coordinates at `U`
(`condProjOn U = ⊗_{p∈U} I ⊗ ⊗_{p∉U} (average)`), and `q_U = ∏_{p∈U} q_p`. Then for `T_0 ≥ 1`,
every block function `φ` and every function `W` of the labels of the other slots,
`|∫ φ(z_Z) W(z_{V∖Z}) dρ|² ≤ ‖W‖²_{L²(λ)} [T_0^{-2γ} ‖φ‖² + ∑_{q_U ≤ T_0} q_U^{-2γ} ‖E_U φ‖²]`.

* `pair_support_decay`: the abstract form for a product of joint laws with uniform source
  marginals.
* `blockIntegral_eq`, `pair_support`: the slot-block form; the pair `(u,v)` is the block
  `Z = {u, v}`, whose labels `Z → X_p` are the ordered pairs. **`pair_support` assumes the block
  marginal uniform on all of `Z → X_p` (on `𝔽_p²` for a pair), which is not the paper's case.**
* `pair_support_decay_on`, `pair_support_on`: **the paper's form of `lem:tr:pairsupport`**: the
  block marginal of each `ρ_p` is uniform on a nonempty set `S_p` of block labels (`S_p = Ω`, the
  strict-square pairs, for an accepted query pair), with the norms and conditional expectations
  of `L²(⊗_p Unif(S_p))`. The proof restricts each joint law to the source alphabet `S_p`
  (`restrictSrc`; mixing passes to the restriction, `restrictSrc_mix`) and applies
  `pair_support_decay` there.
-/

@[expose] public section

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.Mixing

open Sarkozy.IndexSupport

section Abstract

variable {K : Type*} [Fintype K] [DecidableEq K] {A B : K → Type*} [∀ j, Fintype (A j)]
  [∀ j, Fintype (B j)] [∀ j, DecidableEq (A j)] [∀ j, Nonempty (A j)]

/-- `E_U`: the conditional expectation, for the uniform law, onto the coordinates of `U`. -/
noncomputable def condProjOn (A : K → Type*) [∀ j, Fintype (A j)] [∀ j, DecidableEq (A j)]
    (U : K → Bool) : Matrix (∀ j, A j) (∀ j, A j) ℝ :=
  piKron (fun j => if U j then 1 else meanMatrix (A j))

/-- The `U`-component of `E_U φ` is the `U`-component of `φ`. -/
theorem sectorProj_mul_condProjOn (U : K → Bool) :
    sectorProj A U * condProjOn A U = sectorProj A U := by
  rw [sectorProj, condProjOn, piKron_mul]
  congr 1
  funext j
  cases hU : U j
  · simp only [coordProj, Bool.false_eq_true, ite_false]
    exact meanMatrix_mul_self (A j)
  · simp only [coordProj, ite_true, Matrix.mul_one]

/-- A sector component is no larger than the function: `‖φ_U‖ ≤ ‖φ‖`. -/
theorem sectorProj_sq_le (U : K → Bool) (φ : (∀ j, A j) → ℝ) :
    (FiniteLaw.uniform (∀ j, A j)).expect (fun a => (sectorProj A U *ᵥ φ) a ^ 2) ≤
      (FiniteLaw.uniform (∀ j, A j)).expect (fun a => φ a ^ 2) := by
  have h := sum_sectorProj_sq φ (A := A)
  have hle : (sectorProj A U *ᵥ φ) ⬝ᵥ (sectorProj A U *ᵥ φ) ≤ φ ⬝ᵥ φ := by
    rw [← h]
    exact Finset.single_le_sum (f := fun l => (sectorProj A l *ᵥ φ) ⬝ᵥ (sectorProj A l *ᵥ φ))
      (fun l _ => dotProduct_self_nonneg _) (mem_univ U)
  simp only [FiniteLaw.expect_uniform]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  simpa only [dotProduct, sq] using hle

/-- **Decay by exact pair support**, abstract form. -/
theorem pair_support_decay (κ : ∀ j, FiniteLaw (A j × B j))
    (hsrc : ∀ j a, srcWeight (κ j) a = (Fintype.card (A j) : ℝ)⁻¹) (q : K → ℕ)
    (hq : ∀ j, 0 < q j) {γ : ℝ} (hγ : 0 ≤ γ)
    (hmix : ∀ j, ContractsMeanZero (κ j) ((q j : ℝ) ^ (-γ))) {T₀ : ℝ} (hT₀ : 1 ≤ T₀)
    (φ : (∀ j, A j) → ℝ) (W : (∀ j, B j) → ℝ) :
    (∑ b, tgtWeight (prodJoint κ) b * condOp (prodJoint κ) φ b * W b) ^ 2 ≤
      (∑ b, tgtWeight (prodJoint κ) b * W b ^ 2) *
        (T₀ ^ (-2 * γ) * (FiniteLaw.uniform (∀ j, A j)).expect (fun a => φ a ^ 2) +
          ∑ U ∈ univ.filter (fun U : K → Bool => supportConductor q U ≤ T₀),
            supportConductor q U ^ (-2 * γ) *
              (FiniteLaw.uniform (∀ j, A j)).expect (fun a => (condProjOn A U *ᵥ φ) a ^ 2)) := by
  set κp := prodJoint κ
  -- Cauchy--Schwarz in `L²(λ)`
  let lam : FiniteLaw (∀ j, B j) := ⟨tgtWeight κp, tgtWeight_nonneg κp, sum_tgtWeight κp⟩
  have hcs := lam.cauchy_schwarz_sq (condOp κp φ) W
  simp only [FiniteLaw.expect, lam] at hcs
  have hcs' : (∑ b, tgtWeight κp b * condOp κp φ b * W b) ^ 2 ≤
      (∑ b, tgtWeight κp b * condOp κp φ b ^ 2) * ∑ b, tgtWeight κp b * W b ^ 2 := by
    simpa only [mul_assoc] using hcs
  apply hcs'.trans
  rw [mul_comm (∑ b, tgtWeight κp b * condOp κp φ b ^ 2)]
  apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun b _ =>
    mul_nonneg (tgtWeight_nonneg _ _) (sq_nonneg _)))
  -- exact-support decay and the split at `T₀`
  have hdec := (exact_support_decay κ hsrc hmix φ).2
  apply hdec.trans
  set e : (K → Bool) → ℝ := fun U =>
    (FiniteLaw.uniform (∀ j, A j)).expect (fun a => (sectorProj A U *ᵥ φ) a ^ 2) with he
  have he0 (U : K → Bool) : 0 ≤ e U :=
    (FiniteLaw.uniform _).expect_nonneg (fun a => sq_nonneg _)
  have hw (U : K → Bool) : supportWeight (fun j => (q j : ℝ) ^ (-γ)) U ^ 2 =
      supportConductor q U ^ (-2 * γ) := by
    rw [supportWeight_rpow, ← Real.rpow_natCast, ← Real.rpow_mul
      (supportConductor_pos hq U).le]
    congr 1
    push_cast
    ring
  simp only [hw]
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun U : K → Bool => supportConductor q U ≤ T₀)]
  rw [add_comm]
  apply add_le_add
  · -- large conductors
    have hbig : ∀ U ∈ univ.filter (fun U : K → Bool => ¬ supportConductor q U ≤ T₀),
        supportConductor q U ^ (-2 * γ) * e U ≤ T₀ ^ (-2 * γ) * e U := by
      intro U hU
      simp only [mem_filter, mem_univ, true_and, not_le] at hU
      apply mul_le_mul_of_nonneg_right _ (he0 U)
      exact Real.rpow_le_rpow_of_nonpos (by linarith) hU.le (by linarith)
    apply (Finset.sum_le_sum hbig).trans
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith) _)
    calc ∑ U ∈ univ.filter (fun U : K → Bool => ¬ supportConductor q U ≤ T₀), e U
        ≤ ∑ U, e U := Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun U _ _ => he0 U)
      _ = (FiniteLaw.uniform (∀ j, A j)).expect (fun a => φ a ^ 2) := by
          simp only [he, FiniteLaw.expect_uniform, ← Finset.sum_div]
          congr 1
          have := sum_sectorProj_sq φ (A := A)
          simp only [dotProduct, ← sq] at this
          exact this
  · -- small conductors: `‖φ_U‖ ≤ ‖E_U φ‖`
    apply Finset.sum_le_sum
    intro U _
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (supportConductor_pos hq U).le _)
    have h := sectorProj_sq_le U (condProjOn A U *ᵥ φ)
    rwa [Matrix.mulVec_mulVec, sectorProj_mul_condProjOn] at h

end Abstract


section Restrict

variable {A' B' : Type*} [Fintype A'] [Fintype B'] [DecidableEq A']

omit [DecidableEq A'] in
theorem weight_zero_off {κ : FiniteLaw (A' × B')} {S : Finset A'}
    (hS : ∀ a, a ∉ S → srcWeight κ a = 0) {a : A'} (ha : a ∉ S) (b : B') : κ.weight (a, b) = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => κ.nonneg (a, b))).mp (hS a ha) b (mem_univ b)

/-- The restriction of a joint law whose source marginal vanishes off `S` to the source
alphabet `S`. -/
noncomputable def restrictSrc (κ : FiniteLaw (A' × B')) (S : Finset A')
    (hS : ∀ a, a ∉ S → srcWeight κ a = 0) : FiniteLaw ({a // a ∈ S} × B') where
  weight x := κ.weight (x.1.1, x.2)
  nonneg x := κ.nonneg _
  total := by
    rw [Fintype.sum_prod_type]
    have h1 : ∑ a' : {a // a ∈ S}, ∑ b, κ.weight (a'.1, b) = ∑ a ∈ S, srcWeight κ a :=
      Finset.sum_coe_sort S (fun a => srcWeight κ a)
    rw [h1, Finset.sum_subset (subset_univ S) (fun a _ ha => hS a ha)]
    exact sum_srcWeight κ

omit [DecidableEq A'] in
theorem sum_off (S : Finset A') (g : A' → ℝ) (hg : ∀ a, a ∉ S → g a = 0) :
    ∑ a, g a = ∑ a' : {a // a ∈ S}, g a'.1 := by
  rw [Finset.sum_coe_sort S g]
  exact (Finset.sum_subset (subset_univ S) (fun a _ ha => hg a ha)).symm

omit [DecidableEq A'] in
theorem restrictSrc_tgt (κ : FiniteLaw (A' × B')) (S : Finset A')
    (hS : ∀ a, a ∉ S → srcWeight κ a = 0) (b : B') :
    tgtWeight (restrictSrc κ S hS) b = tgtWeight κ b := by
  unfold tgtWeight
  rw [sum_off S (fun a => κ.weight (a, b)) (fun a ha => weight_zero_off hS ha b)]
  rfl

/-- **Mixing passes to the restriction.** -/
theorem restrictSrc_mix (κ : FiniteLaw (A' × B')) (S : Finset A')
    (hS : ∀ a, a ∉ S → srcWeight κ a = 0) {c : ℝ} (h : ContractsMeanZero κ c) :
    ContractsMeanZero (restrictSrc κ S hS) c := by
  intro f' hf'
  let f : A' → ℝ := fun a => if h : a ∈ S then f' ⟨a, h⟩ else 0
  have hf (a' : {a // a ∈ S}) : f a'.1 = f' a' := by simp [f, a'.2]
  have hf0 : ∑ a, srcWeight κ a * f a = 0 := by
    rw [sum_off S _ (fun a ha => by rw [hS a ha, zero_mul])]
    rw [← hf']
    exact sum_congr rfl fun a' _ => by rw [hf]; rfl
  have hmain := h f hf0
  have hL : ∑ b, tgtWeight (restrictSrc κ S hS) b * condOp (restrictSrc κ S hS) f' b ^ 2 =
      ∑ b, tgtWeight κ b * condOp κ f b ^ 2 := by
    refine sum_congr rfl fun b _ => ?_
    by_cases hb : tgtWeight κ b = 0
    · rw [restrictSrc_tgt, hb, zero_mul, zero_mul]
    · have hb' : tgtWeight (restrictSrc κ S hS) b ≠ 0 := by rw [restrictSrc_tgt]; exact hb
      rw [condOp_apply_of_ne _ _ hb', condOp_apply_of_ne _ _ hb, restrictSrc_tgt]
      congr 3
      rw [sum_off S (fun a => κ.weight (a, b) * f a)
        (fun a ha => by rw [weight_zero_off hS ha b, zero_mul])]
      exact sum_congr rfl fun a' _ => by rw [hf]; rfl
  have hR : ∑ a', srcWeight (restrictSrc κ S hS) a' * f' a' ^ 2 =
      ∑ a, srcWeight κ a * f a ^ 2 := by
    rw [sum_off S (fun a => srcWeight κ a * f a ^ 2) (fun a ha => by rw [hS a ha, zero_mul])]
    exact sum_congr rfl fun a' _ => by rw [hf]; rfl
  rw [hL, hR]
  exact hmain

end Restrict

section AbstractOn

variable {K : Type*} [Fintype K] [DecidableEq K] {A B : K → Type*} [∀ j, Fintype (A j)]
  [∀ j, Fintype (B j)] [∀ j, DecidableEq (A j)]

/-- Restricting the source alphabets of a product joint law to the supports `S_j`. -/
theorem prodJoint_restrict_sum (κ : ∀ j, FiniteLaw (A j × B j)) (S : ∀ j, Finset (A j))
    (hS : ∀ j a, a ∉ S j → srcWeight (κ j) a = 0) (b : ∀ j, B j) (G : (∀ j, A j) → ℝ) :
    ∑ a, (prodJoint κ).weight (a, b) * G a =
      ∑ a' : (∀ j, {a // a ∈ S j}),
        (prodJoint (fun j => restrictSrc (κ j) (S j) (hS j))).weight (a', b) *
          G (fun j => (a' j).1) := by
  symm
  apply Finset.sum_of_injOn (fun (a' : ∀ j, {a // a ∈ S j}) j => (a' j).1)
  · intro a' _ a'' _ h
    funext j
    exact Subtype.ext (congrFun h j)
  · intro a' _
    exact mem_coe.mpr (mem_univ _)
  · intro a _ ha
    have hex : ∃ j, a j ∉ S j := by
      by_contra hcon
      push Not at hcon
      exact ha ⟨fun j => ⟨a j, hcon j⟩, mem_coe.mpr (mem_univ _), rfl⟩
    obtain ⟨j, hj⟩ := hex
    simp only [prodJoint]
    rw [Finset.prod_eq_zero (mem_univ j) (weight_zero_off (hS j) hj (b j)), zero_mul]
  · intro a' _
    rfl

/-- **Decay by exact pair support, for marginals uniform on a subset** (`lem:tr:pairsupport`
with the paper's hypothesis): if the source marginal of each `κ_j` is uniform on a nonempty
`S_j ⊆ A_j`, the bound of `pair_support_decay` holds with the norms and conditional
expectations of `L²(⊗_j Unif(S_j))`. -/
theorem pair_support_decay_on (κ : ∀ j, FiniteLaw (A j × B j)) (S : ∀ j, Finset (A j))
    [∀ j, Nonempty {a // a ∈ S j}]
    (hsrc : ∀ j a, srcWeight (κ j) a = if a ∈ S j then ((S j).card : ℝ)⁻¹ else 0) (q : K → ℕ)
    (hq : ∀ j, 0 < q j) {γ : ℝ} (hγ : 0 ≤ γ)
    (hmix : ∀ j, ContractsMeanZero (κ j) ((q j : ℝ) ^ (-γ))) {T₀ : ℝ} (hT₀ : 1 ≤ T₀)
    (φ : (∀ j, A j) → ℝ) (W : (∀ j, B j) → ℝ) :
    (∑ b, tgtWeight (prodJoint κ) b * condOp (prodJoint κ) φ b * W b) ^ 2 ≤
      (∑ b, tgtWeight (prodJoint κ) b * W b ^ 2) *
        (T₀ ^ (-2 * γ) * (FiniteLaw.uniform (∀ j, {a // a ∈ S j})).expect
            (fun a' => φ (fun j => (a' j).1) ^ 2) +
          ∑ U ∈ univ.filter (fun U : K → Bool => supportConductor q U ≤ T₀),
            supportConductor q U ^ (-2 * γ) *
              (FiniteLaw.uniform (∀ j, {a // a ∈ S j})).expect
                (fun a' => (condProjOn (fun j => {a // a ∈ S j}) U *ᵥ
                  (fun a'' => φ (fun j => (a'' j).1))) a' ^ 2)) := by
  have hoff : ∀ j a, a ∉ S j → srcWeight (κ j) a = 0 := fun j a ha => by
    rw [hsrc j a, ite_eq_right ha]
  set κ' : ∀ j, FiniteLaw ({a // a ∈ S j} × B j) := fun j => restrictSrc (κ j) (S j) (hoff j)
  have hsrc' : ∀ j a', srcWeight (κ' j) a' = (Fintype.card {a // a ∈ S j} : ℝ)⁻¹ := by
    intro j a'
    change srcWeight (κ j) a'.1 = _
    rw [hsrc j a'.1, ite_eq_left a'.2, Fintype.card_coe]
  have hmix' : ∀ j, ContractsMeanZero (κ' j) ((q j : ℝ) ^ (-γ)) :=
    fun j => restrictSrc_mix (κ j) (S j) (hoff j) (hmix j)
  have htgt : ∀ b, tgtWeight (prodJoint κ') b = tgtWeight (prodJoint κ) b := by
    intro b
    unfold tgtWeight
    have := prodJoint_restrict_sum κ S hoff b (fun _ => 1)
    simp only [mul_one] at this
    exact this.symm
  have hint : ∑ b, tgtWeight (prodJoint κ) b * condOp (prodJoint κ) φ b * W b =
      ∑ b, tgtWeight (prodJoint κ') b * condOp (prodJoint κ') (fun a'' => φ (fun j => (a'' j).1)) b *
        W b := by
    refine sum_congr rfl fun b _ => ?_
    rw [tgt_mul_condOp, tgt_mul_condOp, prodJoint_restrict_sum κ S hoff b φ]
  have hW : ∑ b, tgtWeight (prodJoint κ) b * W b ^ 2 = ∑ b, tgtWeight (prodJoint κ') b * W b ^ 2 :=
    sum_congr rfl fun b _ => by rw [htgt]
  rw [hint, hW]
  exact pair_support_decay κ' hsrc' q hq hγ hmix' hT₀ (fun a'' => φ (fun j => (a'' j).1)) W

end AbstractOn

section Block

variable {V : Type*} [Fintype V] [DecidableEq V] {K : Type*} [Fintype K] [DecidableEq K]
  {X : K → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]

/-- The integral `∫ φ(z_Z) W(z_{V∖Z}) dρ(z)` for the product law `ρ = ⊗_j ρ_j`. -/
noncomputable def blockIntegral (ρ : ∀ j, FiniteLaw (V → X j)) (Z : Finset V)
    (φ : (∀ j, {w // w ∈ Z} → X j) → ℝ) (W : (∀ j, {w // w ∉ Z} → X j) → ℝ) : ℝ :=
  ∑ z : (∀ j, V → X j), (∏ j, (ρ j).weight (z j)) * φ (fun j w => z j w) * W (fun j w => z j w)

/-- Splitting a configuration at the block `Z`. -/
def splitBlock (Z : Finset V) :
    (∀ j, V → X j) ≃ (∀ j, {w // w ∈ Z} → X j) × (∀ j, {w // w ∉ Z} → X j) where
  toFun z := (fun j w => z j w, fun j w => z j w)
  invFun p j := (Equiv.piEquivPiSubtypeProd (fun w => w ∈ Z) (fun _ => X j)).symm (p.1 j, p.2 j)
  left_inv z := by
    funext j
    exact (Equiv.piEquivPiSubtypeProd (fun w => w ∈ Z) (fun _ => X j)).symm_apply_apply (z j)
  right_inv p := by
    refine Prod.ext (funext fun j => funext fun w => ?_) (funext fun j => funext fun w => ?_)
    · simp [Equiv.piEquivPiSubtypeProd, w.2]
    · simp [Equiv.piEquivPiSubtypeProd, w.2]

/-- Conditioning on the other slots: `∫ φ(z_Z) W(z_{V∖Z}) dρ = E_λ[(T^{ρ,Z} φ) W]`. -/
theorem blockIntegral_eq (ρ : ∀ j, FiniteLaw (V → X j)) (Z : Finset V)
    (φ : (∀ j, {w // w ∈ Z} → X j) → ℝ) (W : (∀ j, {w // w ∉ Z} → X j) → ℝ) :
    blockIntegral ρ Z φ W =
      ∑ b, tgtWeight (prodJoint (fun j => blockJoint (ρ j) Z)) b *
        condOp (prodJoint (fun j => blockJoint (ρ j) Z)) φ b * W b := by
  unfold blockIntegral
  rw [Fintype.sum_equiv (splitBlock Z) _
    (fun p => (∏ j, (ρ j).weight ((splitBlock Z).symm p j)) * φ p.1 * W p.2)
    (fun z => by rw [Equiv.symm_apply_apply]; rfl)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply sum_congr rfl
  intro b _
  rw [tgt_mul_condOp, Finset.sum_mul]
  apply sum_congr rfl
  intro a _
  have hw : (∏ j, (ρ j).weight ((splitBlock Z).symm (a, b) j)) =
      (prodJoint (fun j => blockJoint (ρ j) Z)).weight (a, b) := by
    simp only [prodJoint, blockJoint_weight]
    rfl
  rw [hw]

variable [∀ j, Nonempty (X j)]

/-- **Decay by exact pair support**, slot-block form, for a block marginal uniform on **all** of
`Z → X_j` (hypothesis `hunif`). This is not the case used in the paper, where the marginal of an
accepted query pair is `Unif(Ω)`; for that case use `pair_support_on`. For each
coordinate the marginal of `ρ_j` on the block `Z` is uniform and `ρ_j` is
`(q_j^{-γ}, Z)`-mixing; then for `T₀ ≥ 1`,
`|∫ φ(z_Z) W(z_{V∖Z}) dρ|² ≤ ‖W‖²_{L²(λ)} [T₀^{-2γ} ‖φ‖² + ∑_{q_U ≤ T₀} q_U^{-2γ} ‖E_U φ‖²]`. -/
theorem pair_support (ρ : ∀ j, FiniteLaw (V → X j)) (Z : Finset V)
    (hunif : ∀ j a, srcWeight (blockJoint (ρ j) Z) a =
      (Fintype.card ({w // w ∈ Z} → X j) : ℝ)⁻¹)
    (q : K → ℕ) (hq : ∀ j, 0 < q j) {γ : ℝ} (hγ : 0 ≤ γ)
    (hmix : ∀ j, IsMixing (ρ j) Z ((q j : ℝ) ^ (-γ))) {T₀ : ℝ} (hT₀ : 1 ≤ T₀)
    (φ : (∀ j, {w // w ∈ Z} → X j) → ℝ) (W : (∀ j, {w // w ∉ Z} → X j) → ℝ) :
    blockIntegral ρ Z φ W ^ 2 ≤
      (∑ b, tgtWeight (prodJoint (fun j => blockJoint (ρ j) Z)) b * W b ^ 2) *
        (T₀ ^ (-2 * γ) * (FiniteLaw.uniform (∀ j, {w // w ∈ Z} → X j)).expect (fun a => φ a ^ 2) +
          ∑ U ∈ univ.filter (fun U : K → Bool => supportConductor q U ≤ T₀),
            supportConductor q U ^ (-2 * γ) *
              (FiniteLaw.uniform (∀ j, {w // w ∈ Z} → X j)).expect
                (fun a => (condProjOn (fun j => {w // w ∈ Z} → X j) U *ᵥ φ) a ^ 2)) := by
  rw [blockIntegral_eq]
  exact pair_support_decay (fun j => blockJoint (ρ j) Z) hunif q hq hγ hmix hT₀ φ W


omit [∀ j, Nonempty (X j)] in
/-- **Decay by exact pair support** (`lem:tr:pairsupport`), slot-block form, **with the paper's
hypothesis**: the marginal of each `ρ_j` on the block `Z` is uniform on a nonempty set `S_j` of
block labels — for a pair `Z = {u, v}` and an accepted query, `S_j = Ω`, the strict-square
pairs — and the norms and conditional expectations are those of `L²(⊗_j Unif(S_j))`. -/
theorem pair_support_on (ρ : ∀ j, FiniteLaw (V → X j)) (Z : Finset V)
    (S : ∀ j, Finset ({w // w ∈ Z} → X j)) [∀ j, Nonempty {a // a ∈ S j}]
    (hunif : ∀ j a, srcWeight (blockJoint (ρ j) Z) a =
      if a ∈ S j then ((S j).card : ℝ)⁻¹ else 0)
    (q : K → ℕ) (hq : ∀ j, 0 < q j) {γ : ℝ} (hγ : 0 ≤ γ)
    (hmix : ∀ j, IsMixing (ρ j) Z ((q j : ℝ) ^ (-γ))) {T₀ : ℝ} (hT₀ : 1 ≤ T₀)
    (φ : (∀ j, {w // w ∈ Z} → X j) → ℝ) (W : (∀ j, {w // w ∉ Z} → X j) → ℝ) :
    blockIntegral ρ Z φ W ^ 2 ≤
      (∑ b, tgtWeight (prodJoint (fun j => blockJoint (ρ j) Z)) b * W b ^ 2) *
        (T₀ ^ (-2 * γ) * (FiniteLaw.uniform (∀ j, {a // a ∈ S j})).expect
            (fun a' => φ (fun j => (a' j).1) ^ 2) +
          ∑ U ∈ univ.filter (fun U : K → Bool => supportConductor q U ≤ T₀),
            supportConductor q U ^ (-2 * γ) *
              (FiniteLaw.uniform (∀ j, {a // a ∈ S j})).expect
                (fun a' => (condProjOn (fun j => {a // a ∈ S j}) U *ᵥ
                  (fun a'' => φ (fun j => (a'' j).1))) a' ^ 2)) := by
  rw [blockIntegral_eq]
  exact pair_support_decay_on (fun j => blockJoint (ρ j) Z) S hunif q hq hγ hmix hT₀ φ W

end Block

end Sarkozy.Mixing
