module

public import Sarkozy.Cancellation.TheoremCGlue
public import Sarkozy.Mixing.PairSupport

@[expose] public section

/-!
# Step 1 of `lem:record:density-can`: the encoding at the tail primes

`paper/sections/08_scale_comparison.tex`, `lem:record:density-can`, Step 1, in the terms of
`Sarkozy.Cancellation.PairLawForm` (`TheoremCGlue`).

* **The tail pair laws.** Let `ρ` be a law on `𝔽_q^V` whose `(u, v)`-marginal is `Unif(Ω_q)`
  (WP-FI's corrected `PairUniformOmega`). Then `tailLaw` is `ρ` read as a law on `Ω_q × B`, with
  `Ω_q = PairAlphabet` and `B` the labels of the other slots. It is built by restricting
  `blockJoint ρ {u, v}` to the strict-square blocks (`restrictSrc`, WP-S) and transporting along
  `omegaEquiv` (`mapSrc`).
  - `tailLaw_src`: its source marginal is uniform on `Ω_q`.
  - `tailLaw_mix`: if `ρ` is `(γ, {u, v})`-mixing, it contracts mean-zero functions by `q^{-γ}`
    (`restrictSrc_mix`, `mapSrc_mix`).

  These are the hypotheses `hsrc` and `hmix` of `PairLawForm`.
* **The tail integral** (`tail_integral_eq`). For such laws `ρ_k`, the integral of
  `F₁(z_u) F₂(z_v) W(z_{V∖{u,v}})` against `⊗_k ρ_k` is
  `∑_b κ_B(b) T^κ φ(b) W(b)`, where `κ = ⊗_k tailLaw` and `φ(a) = F₁(x(a)) F₂(y(a))`. This is the
  form of `I` in `PairLawForm`. The proof combines WP-S's `blockIntegral_eq`, the restriction
  `prodJoint_restrict_sum` and the transport `prodJoint_mapSrc_sum`.
* **The atoms** (`coupled_integral_split`). The coupled integral `∫∏_w G_w dϱ` over the atoms
  equals `∑_x μ(x) ∑_y ∏_{high} ϱ_i(y_i) ∏_w G_w(x, y)`, with `μ` the product over the low atoms
  (`multilinear_tensor_eq`, `sum_split_atoms`). The slot split is `prod_slots_split`.

New material for this paper.
-/

namespace Sarkozy.Cancellation

open Finset
open scoped BigOperators Matrix
open Sarkozy.Mixing

/-! ## Transport of a joint law along an equivalence of the source alphabet -/

section MapSrc

variable {A A₂ B : Type*} [Fintype A] [Fintype A₂] [Fintype B]

/-- The joint law `κ` read on the source alphabet `A₂ ≃ A`. -/
noncomputable def mapSrc (κ : FiniteLaw (A × B)) (e : A ≃ A₂) : FiniteLaw (A₂ × B) where
  weight x := κ.weight (e.symm x.1, x.2)
  nonneg x := κ.nonneg _
  total := by
    rw [← κ.total]
    exact Fintype.sum_equiv ((e.prodCongr (Equiv.refl B)).symm) _ _ (fun x => rfl)

lemma srcWeight_mapSrc (κ : FiniteLaw (A × B)) (e : A ≃ A₂) (a₂ : A₂) :
    srcWeight (mapSrc κ e) a₂ = srcWeight κ (e.symm a₂) := rfl

lemma tgtWeight_mapSrc (κ : FiniteLaw (A × B)) (e : A ≃ A₂) (b : B) :
    tgtWeight (mapSrc κ e) b = tgtWeight κ b := by
  unfold tgtWeight
  exact Fintype.sum_equiv e.symm _ _ (fun a₂ => rfl)

lemma condOp_mapSrc (κ : FiniteLaw (A × B)) (e : A ≃ A₂) (f : A₂ → ℝ) (b : B) :
    condOp (mapSrc κ e) f b = condOp κ (fun a => f (e a)) b := by
  unfold condOp
  simp only [Matrix.mulVec, dotProduct, condMatrix, tgtWeight_mapSrc, srcWeight_mapSrc]
  refine Fintype.sum_equiv e.symm _ _ (fun a₂ => ?_)
  rw [Equiv.apply_symm_apply]
  rfl

/-- **Mixing passes to the transported law.** -/
theorem mapSrc_mix (κ : FiniteLaw (A × B)) (e : A ≃ A₂) {c : ℝ} (h : ContractsMeanZero κ c) :
    ContractsMeanZero (mapSrc κ e) c := by
  intro f hf
  have hf' : ∑ a, srcWeight κ a * f (e a) = 0 := by
    rw [← hf]
    exact (Fintype.sum_equiv e.symm _ _ (fun a₂ => by
      rw [srcWeight_mapSrc, Equiv.apply_symm_apply])).symm
  have hmain := h (fun a => f (e a)) hf'
  have hL : ∑ b, tgtWeight (mapSrc κ e) b * condOp (mapSrc κ e) f b ^ 2 =
      ∑ b, tgtWeight κ b * condOp κ (fun a => f (e a)) b ^ 2 :=
    sum_congr rfl fun b _ => by rw [tgtWeight_mapSrc, condOp_mapSrc]
  have hR : ∑ a₂, srcWeight (mapSrc κ e) a₂ * f a₂ ^ 2 = ∑ a, srcWeight κ a * f (e a) ^ 2 :=
    (Fintype.sum_equiv e.symm _ _ (fun a₂ => by
      rw [srcWeight_mapSrc, Equiv.apply_symm_apply])).symm.symm
  rw [hL, hR]
  exact hmain

end MapSrc

/-! ## The source marginal of a block joint law -/

section BlockSrc

variable {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X]

/-- `κ_Z(a) = ρ(z_Z = a)`. -/
lemma srcWeight_blockJoint_eq (ρ : FiniteLaw (V → X)) (Z : Finset V) (a : {w // w ∈ Z} → X) :
    srcWeight (blockJoint ρ Z) a =
      ρ.expect (fun z => if (fun w : {w // w ∈ Z} => z w.1) = a then 1 else 0) := by
  set e := Equiv.piEquivPiSubtypeProd (fun w => w ∈ Z) (fun _ => X) with he
  unfold srcWeight FiniteLaw.expect
  simp only [blockJoint_weight]
  rw [← Fintype.sum_equiv e.symm (fun y => ρ.weight (e.symm y) *
    (if (fun w : {w // w ∈ Z} => (e.symm y) w.1) = a then 1 else 0)) _ (fun y => rfl)]
  rw [Fintype.sum_prod_type]
  have h1 : ∀ (a' : {w // w ∈ Z} → X) (b : {w // w ∉ Z} → X),
      (fun w : {w // w ∈ Z} => (e.symm (a', b)) w.1) = a' := by
    intro a' b
    have := congrArg Prod.fst (e.apply_symm_apply (a', b))
    exact this
  simp only [h1, mul_ite, mul_one, mul_zero]
  rw [sum_comm]
  simp only [Finset.sum_ite_eq', mem_univ, ite_true, he]

end BlockSrc

/-! ## The tail pair law on `Ω_q × B` -/

section Pair

variable {K : Type*} (q : K → ℕ) [∀ j, NeZero (q j)]

/-- The slot `u` of the pair block `{u, v}`. -/
def slotU (u v : Slot) : {w // w ∈ ({u, v} : Finset Slot)} := ⟨u, by simp⟩

/-- The slot `v` of the pair block `{u, v}`. -/
def slotV (u v : Slot) : {w // w ∈ ({u, v} : Finset Slot)} := ⟨v, by simp⟩

/-- The pair-block labels with a strict-square difference. -/
def omegaBlock (j : K) (u v : Slot) : Finset ({w // w ∈ ({u, v} : Finset Slot)} → ZMod (q j)) :=
  univ.filter (fun a => a (slotV u v) - a (slotU u v) ∈ sqSet q j)

/-- The pair-block labels with a strict-square difference are the strict-square pairs `Ω_q`. -/
def omegaEquiv (j : K) {u v : Slot} (huv : u ≠ v) :
    {a // a ∈ omegaBlock q j u v} ≃ PairAlphabet q j where
  toFun a := ⟨(a.1 (slotU u v), a.1 (slotV u v)), (mem_filter.mp a.2).2⟩
  invFun c := ⟨fun w => if w.1 = u then c.1.1 else c.1.2, by
    rw [omegaBlock, mem_filter]
    refine ⟨mem_univ _, ?_⟩
    show (if v = u then c.1.1 else c.1.2) - (if u = u then c.1.1 else c.1.2) ∈ sqSet q j
    rw [ite_eq_right (Ne.symm huv), ite_eq_left rfl]
    exact c.2⟩
  left_inv a := by
    apply Subtype.ext
    funext w
    have hw := w.2
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with hw | hw
    · have : w = slotU u v := Subtype.ext hw
      subst this
      show (if u = u then _ else _) = _
      rw [ite_eq_left rfl]
    · have : w = slotV u v := Subtype.ext hw
      subst this
      show (if v = u then _ else _) = _
      rw [ite_eq_right (Ne.symm huv)]
  right_inv c := by
    apply Subtype.ext
    show ((if u = u then c.1.1 else c.1.2), (if v = u then c.1.1 else c.1.2)) = c.1
    rw [ite_eq_left rfl, ite_eq_right (Ne.symm huv)]

/-- `|Ω_q| = |PairAlphabet|`. -/
lemma card_strictSquarePairs (j : K) :
    ((Sarkozy.TheoremC.strictSquarePairs (q j)).card : ℝ) =
      (Fintype.card (PairAlphabet q j) : ℝ) := by
  rw [Fintype.card_subtype]
  congr 2
  unfold Sarkozy.TheoremC.strictSquarePairs
  refine filter_congr fun xy _ => ?_
  rw [sqSet, mem_filter]
  simp

/-- Under `PairUniformOmega`, the pair-block marginal is uniform on the strict-square blocks. -/
lemma srcWeight_blockJoint_omega (j : K) {u v : Slot}
    (ρ : FiniteLaw (Slot → ZMod (q j))) (hU : Sarkozy.TheoremC.PairUniformOmega ρ u v)
    (a : {w // w ∈ ({u, v} : Finset Slot)} → ZMod (q j)) :
    srcWeight (blockJoint ρ {u, v}) a =
      if a ∈ omegaBlock q j u v then ((Fintype.card (PairAlphabet q j) : ℝ))⁻¹ else 0 := by
  rw [srcWeight_blockJoint_eq]
  have hind : ∀ z : Slot → ZMod (q j),
      (if (fun w : {w // w ∈ ({u, v} : Finset Slot)} => z w.1) = a then (1 : ℝ) else 0) =
        if z u = a (slotU u v) ∧ z v = a (slotV u v) then (1 : ℝ) else 0 := by
    intro z
    have hiff : (fun w : {w // w ∈ ({u, v} : Finset Slot)} => z w.1) = a ↔
        z u = a (slotU u v) ∧ z v = a (slotV u v) := by
      constructor
      · intro h
        exact ⟨congrFun h (slotU u v), congrFun h (slotV u v)⟩
      · rintro ⟨h1, h2⟩
        funext w
        have hw := w.2
        simp only [mem_insert, mem_singleton] at hw
        rcases hw with hw | hw
        · have : w = slotU u v := Subtype.ext hw
          subst this; exact h1
        · have : w = slotV u v := Subtype.ext hw
          subst this; exact h2
    by_cases h : (fun w : {w // w ∈ ({u, v} : Finset Slot)} => z w.1) = a
    · rw [ite_eq_left h, ite_eq_left (hiff.mp h)]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (hiff.mpr h'))]
  have h2 := hU (fun x y => if x = a (slotU u v) ∧ y = a (slotV u v) then (1 : ℝ) else 0)
  rw [FiniteLaw.expect_congr ρ hind, h2, card_strictSquarePairs]
  have hsum : ∑ xy ∈ Sarkozy.TheoremC.strictSquarePairs (q j),
      (if xy.1 = a (slotU u v) ∧ xy.2 = a (slotV u v) then (1 : ℝ) else 0) =
      if a ∈ omegaBlock q j u v then 1 else 0 := by
    have e : ∀ xy : ZMod (q j) × ZMod (q j),
        (if xy.1 = a (slotU u v) ∧ xy.2 = a (slotV u v) then (1 : ℝ) else 0) =
          if xy = (a (slotU u v), a (slotV u v)) then 1 else 0 := by
      intro xy
      simp only [Prod.ext_iff]
    rw [sum_congr rfl fun xy _ => e xy, sum_ite_eq']
    congr 1
    unfold Sarkozy.TheoremC.strictSquarePairs omegaBlock
    rw [mem_filter, mem_filter, sqSet, mem_filter]
    simp
  rw [hsum]
  split_ifs <;> simp

/-- **The tail pair law** at the prime `q_j`: the law of `ϱ_p` read as a law on
`Ω_{q_j} × B_j` (pair labels with a strict-square difference, labels of the other slots). -/
noncomputable def tailLaw (j : K) {u v : Slot} (huv : u ≠ v) (ρ : FiniteLaw (Slot → ZMod (q j)))
    (hU : Sarkozy.TheoremC.PairUniformOmega ρ u v) :
    FiniteLaw (PairAlphabet q j × ({w // w ∉ ({u, v} : Finset Slot)} → ZMod (q j))) :=
  mapSrc (restrictSrc (blockJoint ρ {u, v}) (omegaBlock q j u v)
    (fun a ha => by rw [srcWeight_blockJoint_omega q j ρ hU, ite_eq_right ha]))
    (omegaEquiv q j huv)

/-- **The tail pair law is uniform on `Ω_q`** (`lem:record:density-can`(a)). -/
theorem tailLaw_src (j : K) {u v : Slot} (huv : u ≠ v) (ρ : FiniteLaw (Slot → ZMod (q j)))
    (hU : Sarkozy.TheoremC.PairUniformOmega ρ u v) (c : PairAlphabet q j) :
    srcWeight (tailLaw q j huv ρ hU) c = (Fintype.card (PairAlphabet q j) : ℝ)⁻¹ := by
  unfold tailLaw
  rw [srcWeight_mapSrc]
  show srcWeight (blockJoint ρ {u, v}) ((omegaEquiv q j huv).symm c).1 = _
  rw [srcWeight_blockJoint_omega q j ρ hU, ite_eq_left ((omegaEquiv q j huv).symm c).2]

/-- `γ = 255/1024`. -/
lemma stageGamma_eq : stageGamma = Sarkozy.AnalyticStage.γ := by
  unfold stageGamma Sarkozy.AnalyticStage.γ; rfl

/-- **The tail pair law contracts mean-zero functions by `q_j^{-γ}`**, from `IsGammaMixing` on the
pair block (`lem:record:density-can`(a)). -/
theorem tailLaw_mix (j : K) {u v : Slot} (huv : u ≠ v) (ρ : FiniteLaw (Slot → ZMod (q j)))
    (hU : Sarkozy.TheoremC.PairUniformOmega ρ u v)
    (hmix : IsGammaMixing (q j) Sarkozy.AnalyticStage.γ ρ {u, v}) :
    ContractsMeanZero (tailLaw q j huv ρ hU) ((q j : ℝ) ^ (-stageGamma)) := by
  rw [stageGamma_eq]
  exact mapSrc_mix _ _ (restrictSrc_mix _ _ _ hmix)

end Pair

/-! ## The tail integral in pair-law form -/

section TailIntegral

/-- `κ_B(b) T^κ f(b) = ∑_a κ(a, b) f(a)`. -/
lemma tgt_mul_condOp {A B : Type*} [Fintype A] [Fintype B] (κ : FiniteLaw (A × B))
    (f : A → ℝ) (b : B) : tgtWeight κ b * condOp κ f b = ∑ a, κ.weight (a, b) * f a := by
  by_cases hb : tgtWeight κ b = 0
  · rw [hb, zero_mul]
    symm
    exact sum_eq_zero fun a _ => by rw [weight_eq_zero_of_tgt hb a, zero_mul]
  · rw [condOp_apply_of_ne κ f hb]
    field_simp

variable {K : Type*} [Fintype K] [DecidableEq K] {A A₂ B : K → Type*} [∀ j, Fintype (A j)]
  [∀ j, Fintype (A₂ j)] [∀ j, Fintype (B j)]

/-- Sums against a product of transported laws. -/
lemma prodJoint_mapSrc_sum (κ : ∀ j, FiniteLaw (A j × B j)) (e : ∀ j, A j ≃ A₂ j)
    (b : ∀ j, B j) (G : (∀ j, A j) → ℝ) :
    ∑ a, (prodJoint κ).weight (a, b) * G a =
      ∑ c, (prodJoint (fun j => mapSrc (κ j) (e j))).weight (c, b) *
        G (fun j => (e j).symm (c j)) := by
  refine Fintype.sum_equiv (Equiv.piCongrRight e) _ _ (fun a => ?_)
  have h : (fun j => (e j).symm ((Equiv.piCongrRight e) a j)) = a := by
    funext j; exact (e j).symm_apply_apply (a j)
  rw [h]
  congr 1
  show ∏ j, (κ j).weight (a j, b j) = ∏ j, (κ j).weight ((e j).symm (e j (a j)), b j)
  simp only [Equiv.symm_apply_apply]

end TailIntegral

section TailPairs

variable {K : Type*} [Fintype K] [DecidableEq K] (q : K → ℕ) [∀ j, NeZero (q j)]

omit [Fintype K] [DecidableEq K] in
lemma omegaEquiv_symm_u (j : K) {u v : Slot} (huv : u ≠ v) (c : PairAlphabet q j) :
    ((omegaEquiv q j huv).symm c).1 (slotU u v) = c.1.1 := by
  show (if u = u then c.1.1 else c.1.2) = c.1.1
  rw [ite_eq_left rfl]

omit [Fintype K] [DecidableEq K] in
lemma omegaEquiv_symm_v (j : K) {u v : Slot} (huv : u ≠ v) (c : PairAlphabet q j) :
    ((omegaEquiv q j huv).symm c).1 (slotV u v) = c.1.2 := by
  show (if v = u then c.1.1 else c.1.2) = c.1.2
  rw [ite_eq_right (Ne.symm huv)]

/-- **The tail integral in pair-law form** (Step 1 of `lem:record:density-can` at the tail
primes): for laws `ρ_k` on `𝔽_{q_k}^V` with `(u, v)`-marginal `Unif(Ω_{q_k})`, the integral of
`F₁(z_u) F₂(z_v) W(z_{V∖{u,v}})` against `⊗_k ρ_k` is `∑_b κ_B(b) T^κ φ(b) W(b)` for the product
`κ = ⊗_k κ_k` of the tail pair laws (`tailLaw`) and `φ(a) = F₁(x(a)) F₂(y(a))`. -/
theorem tail_integral_eq {u v : Slot} (huv : u ≠ v) (ρ : ∀ k, FiniteLaw (Slot → ZMod (q k)))
    (hU : ∀ k, Sarkozy.TheoremC.PairUniformOmega (ρ k) u v)
    (F₁ F₂ : Sarkozy.FourierArithmetic.ResidueSpace q → ℝ)
    (W : (∀ k, {w // w ∉ ({u, v} : Finset Slot)} → ZMod (q k)) → ℝ) :
    (∑ y : (∀ k, Slot → ZMod (q k)), (∏ k, (ρ k).weight (y k)) *
        (F₁ (fun k => y k u) * F₂ (fun k => y k v)) * W (fun k w => y k w.1)) =
      ∑ b, tgtWeight (prodJoint (fun k => tailLaw q k huv (ρ k) (hU k))) b *
        condOp (prodJoint (fun k => tailLaw q k huv (ρ k) (hU k)))
          (fun a => F₁ (pairsToVectors q a).1 * F₂ (pairsToVectors q a).2) b * W b := by
  set φbl : (∀ k, {w // w ∈ ({u, v} : Finset Slot)} → ZMod (q k)) → ℝ :=
    fun a => F₁ (fun k => a k (slotU u v)) * F₂ (fun k => a k (slotV u v)) with hφbl
  have hL : (∑ y : (∀ k, Slot → ZMod (q k)), (∏ k, (ρ k).weight (y k)) *
      (F₁ (fun k => y k u) * F₂ (fun k => y k v)) * W (fun k w => y k w.1)) =
      blockIntegral ρ {u, v} φbl W := rfl
  rw [hL, blockIntegral_eq]
  refine sum_congr rfl fun b _ => ?_
  rw [tgt_mul_condOp, tgt_mul_condOp]
  congr 1
  have hoff : ∀ k a, a ∉ omegaBlock q k u v → srcWeight (blockJoint (ρ k) {u, v}) a = 0 :=
    fun k a ha => by rw [srcWeight_blockJoint_omega q k (ρ k) (hU k), ite_eq_right ha]
  rw [prodJoint_restrict_sum (fun k => blockJoint (ρ k) {u, v}) (fun k => omegaBlock q k u v)
    hoff b φbl]
  rw [prodJoint_mapSrc_sum (fun k => restrictSrc (blockJoint (ρ k) {u, v}) (omegaBlock q k u v)
    (hoff k)) (fun k => omegaEquiv q k huv) b]
  refine sum_congr rfl fun c _ => ?_
  congr 1
  simp only [hφbl, omegaEquiv_symm_u, omegaEquiv_symm_v]
  rfl

end TailPairs

/-! ## The multilinear integral over the atoms -/

section Atoms

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : ι → Type*} [∀ i, Fintype (Y i)]
  [∀ i, DecidableEq (Y i)]

omit [Fintype ι] [DecidableEq ι] in
lemma lawDensity_signedIntegral {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (w : Ω → ℝ) (x : Ω) :
    lawDensity (signedIntegral w) x = w x := by
  show ∑ y, w y * (if y = x then 1 else 0) = w x
  simp

/-- **Fubini for the coupled integral**: `∫ ∏_w G_w(z_w) d(⊗_i ϱ_i) =
∑_z ∏_i ϱ_i(z_i) ∏_w G_w((z_i(w))_i)`. -/
lemma multilinear_tensor_eq (ϱ : ∀ i, FiniteLaw (Slot → Y i)) (G : Slot → (∀ i, Y i) → ℝ) :
    multilinearIntegral (tensorLaw fun i => signedIntegral (ϱ i).weight) G =
      ∑ z : (∀ i, Slot → Y i), (∏ i, (ϱ i).weight (z i)) * ∏ w, G w (fun i => z i w) := by
  show ∑ z : (∀ i, Slot → Y i), (∏ i, lawDensity (signedIntegral (ϱ i).weight) (z i)) *
    (∏ w, G w (fun i => z i w)) = _
  simp only [lawDensity_signedIntegral]

omit [∀ i, DecidableEq (Y i)] in
/-- Splitting the atoms by a predicate: the atoms with `P` (the prefix and the small primes) and
the atoms without (the tail primes). -/
lemma sum_split_atoms (P : ι → Prop) [DecidablePred P] (F : (∀ i, Slot → Y i) → ℝ) :
    ∑ z, F z = ∑ x : (∀ i : {i // P i}, Slot → Y i), ∑ y : (∀ i : {i // ¬ P i}, Slot → Y i),
      F ((Equiv.piEquivPiSubtypeProd P (fun i => Slot → Y i)).symm (x, y)) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd P (fun i => Slot → Y i)) F _
    (fun z => by rw [Equiv.symm_apply_apply])

/-- **The coupled integral, split at the atoms**: with `μ = ⊗_{P} ϱ_i` on the low atoms,
`∫ ∏_w G_w dϱ = ∑_x μ(x) ∑_y ∏_{¬P} ϱ_i(y_i) ∏_w G_w(x, y)`. -/
theorem coupled_integral_split (ϱ : ∀ i, FiniteLaw (Slot → Y i)) (G : Slot → (∀ i, Y i) → ℝ)
    (P : ι → Prop) [DecidablePred P] :
    multilinearIntegral (tensorLaw fun i => signedIntegral (ϱ i).weight) G =
      ∑ x : (∀ i : {i // P i}, Slot → Y i), (∏ i : {i // P i}, (ϱ i.1).weight (x i)) *
        ∑ y : (∀ i : {i // ¬ P i}, Slot → Y i), (∏ i : {i // ¬ P i}, (ϱ i.1).weight (y i)) *
          ∏ w, G w (fun i =>
            (Equiv.piEquivPiSubtypeProd P (fun i => Slot → Y i)).symm (x, y) i w) := by
  rw [multilinear_tensor_eq, sum_split_atoms P]
  refine sum_congr rfl fun x _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun y _ => ?_
  rw [← Fintype.prod_subtype_mul_prod_subtype P]
  have hx : ∀ i : {i // P i},
      (Equiv.piEquivPiSubtypeProd P (fun i => Slot → Y i)).symm (x, y) i.1 = x i := by
    intro i
    show (if h : P i.1 then x ⟨i.1, h⟩ else y ⟨i.1, h⟩) = x i
    rw [dite_eq_left i.2]
  have hy : ∀ i : {i // ¬ P i},
      (Equiv.piEquivPiSubtypeProd P (fun i => Slot → Y i)).symm (x, y) i.1 = y i := by
    intro i
    show (if h : P i.1 then x ⟨i.1, h⟩ else y ⟨i.1, h⟩) = y i
    rw [dite_eq_right i.2]
  simp only [hx, hy]
  ring

/-- **The slot split**: `∏_w f(w) = f(u) f(v) ∏_{w ≠ u, v} f(w)` for `u ≠ v`. -/
lemma prod_slots_split {u v : Slot} (huv : u ≠ v) (f : Slot → ℝ) :
    ∏ w, f w = f u * f v * ∏ w : {w // w ∉ ({u, v} : Finset Slot)}, f w.1 := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun w => w ∈ ({u, v} : Finset Slot)) f]
  congr 1
  rw [← Finset.prod_subtype ({u, v} : Finset Slot) (fun _ => Iff.rfl) f, prod_pair huv]

end Atoms

end Sarkozy.Cancellation
