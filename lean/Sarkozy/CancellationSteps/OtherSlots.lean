module

public import Sarkozy.CancellationSteps.PairFactor

/-!
# Step 2 for the other slots

`paper/sections/08_scale_comparison.tex`, `lem:record:density-can`, Step 2: the bound
`∫_x ‖W_x‖₂² ≤ C₂ N^{72δ} α` of the other factors `W = ∏_{w ≠ u, v} G_w`.

* `tailLaw_tgt_slot`: the target marginal of the tail pair law (`tailLaw`) at a slot `w ≠ u, v`
  is uniform.

New material for this paper.
-/

@[expose] public section

namespace Sarkozy.CancellationSteps

open Finset
open scoped BigOperators
open Sarkozy.Cancellation Sarkozy.Mixing Sarkozy.PaperFrame Sarkozy.FourierArithmetic
  Sarkozy.Functional

section TailTarget

variable {K : Type*} (q : K → ℕ) [∀ j, NeZero (q j)]

/-- The target marginal of the tail pair law is the other-slot marginal of `ρ`. -/
lemma tgtWeight_tailLaw (j : K) {u v : Slot} (huv : u ≠ v) (ρ : FiniteLaw (Slot → ZMod (q j)))
    (hU : Sarkozy.TheoremC.PairUniformOmega ρ u v)
    (b : {w // w ∉ ({u, v} : Finset Slot)} → ZMod (q j)) :
    tgtWeight (tailLaw q j huv ρ hU) b = tgtWeight (blockJoint ρ {u, v}) b := by
  classical
  unfold tailLaw
  rw [tgtWeight_mapSrc]
  unfold tgtWeight restrictSrc
  simp only
  rw [Finset.sum_coe_sort (omegaBlock q j u v) (fun a => (blockJoint ρ {u, v}).weight (a, b))]
  refine sum_subset (subset_univ _) fun a _ ha => ?_
  have hs : srcWeight (blockJoint ρ {u, v}) a = 0 := by
    rw [srcWeight_blockJoint_omega q j ρ hU, ite_eq_right ha]
  unfold srcWeight at hs
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun b' _ => (blockJoint ρ {u, v}).nonneg _)).mp hs b
    (mem_univ _)

/-- **The target marginal of the tail pair law at a slot `w ≠ u, v` is uniform**: for every
`t ∈ ℤ/q`, `∑_b κ_B(b) [b_w = t] = q⁻¹`. -/
lemma tailLaw_tgt_slot [∀ j, Fact (q j).Prime] (j : K) {u v : Slot} (huv : u ≠ v)
    (ρ : FiniteLaw (Slot → ZMod (q j))) (hU : Sarkozy.TheoremC.PairUniformOmega ρ u v)
    (hρ : HasUniformMarginals ρ) (w : {w // w ∉ ({u, v} : Finset Slot)}) (t : ZMod (q j)) :
    ∑ b, tgtWeight (tailLaw q j huv ρ hU) b * (if b w = t then (1 : ℝ) else 0) =
      (q j : ℝ)⁻¹ := by
  classical
  simp_rw [tgtWeight_tailLaw]
  unfold tgtWeight
  simp_rw [sum_mul]
  rw [sum_comm, ← Fintype.sum_prod_type']
  have h := hρ w.1 (fun s => if s = t then (1 : ℝ) else 0)
  rw [FiniteLaw.expect_uniform, sum_ite_eq', ZMod.card] at h
  simp only [mem_univ, ↓reduceIte] at h
  rw [one_div] at h
  rw [← h]
  unfold FiniteLaw.expect
  rw [← (Equiv.piEquivPiSubtypeProd (fun w => w ∈ ({u, v} : Finset Slot))
    (fun _ => ZMod (q j))).symm.sum_comp]
  refine sum_congr rfl fun x _ => ?_
  rw [blockJoint_weight]
  have hw : ((Equiv.piEquivPiSubtypeProd (fun w => w ∈ ({u, v} : Finset Slot))
      (fun _ => ZMod (q j))).symm x) w.1 = x.2 w := by
    rw [Equiv.piEquivPiSubtypeProd_symm_apply]
    simp [w.2]
  simp only [Prod.mk.eta]
  rw [hw]

end TailTarget

/-! ## The other-slot labels are uniform -/

section OtherSlot

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]

omit [DecidableEq J₀] [∀ i, NeZero (m₀ i)] [∀ L, DecidableEq (J L)] [∀ L j, NeZero (p L j)] in
lemma frozenCoords_allTrue (L P5 : ℕ) :
    frozenCoords (J₀ := J₀) p L P5 (fun _ => true) = univ := by
  ext c
  simp only [mem_univ, iff_true]
  by_contra h
  have := (not_mem_frozenCoords p L P5 (fun _ => true) c).mp h
  cases c with
  | inl i => exact this
  | inr j =>
    obtain ⟨_, h2⟩ := this
    exact Bool.noConfusion h2

/-- **The other-slot labels are uniform on `G_N`**: for a slot `w ≠ u, v`, under `μ` and the target
marginal of the tail pair laws, the label `mergeAt x_w b_w` is uniform on `G_N`. -/
theorem other_slot_uniform [∀ L j, Fact (p L j).Prime] (L P5 : ℕ) {u v : Slot} (huv : u ≠ v)
    (ϱ : ∀ b : PaperAtom J L, FiniteLaw (Slot → AtomLabel m₀ p L b))
    (hϱ : ∀ b, HasUniformMarginals (ϱ b))
    (hU : ∀ k : TailIdx p L P5,
      Sarkozy.TheoremC.PairUniformOmega (q := tailQ p L P5 k) (ϱ (some k.1)) u v)
    (w : {w // w ∉ ({u, v} : Finset Slot)}) (f : ResidueSpace (joinModuli m₀ (p L)) → ℝ) :
    (FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1)).expect (fun x =>
      ∑ b, tgtWeight (prodJoint (encKappa m₀ p L P5 ϱ huv hU)) b *
        f (atomGroupEquiv m₀ p L (mergeAt m₀ p L P5 (fun i => x i w.1) (fun k => b k w)))) =
      (FiniteLaw.uniform (ResidueSpace (joinModuli m₀ (p L)))).expect f := by
  classical
  set μ := FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1) with hμ
  set κ := encKappa m₀ p L P5 ϱ huv hU with hκ
  set lab : LowLabels m₀ p L P5 →
      (∀ k : TailIdx p L P5, {w // w ∉ ({u, v} : Finset Slot)} → ZMod (tailQ p L P5 k)) →
      ResidueSpace (joinModuli m₀ (p L)) := fun x b =>
    atomGroupEquiv m₀ p L (mergeAt m₀ p L P5 (fun i => x i w.1) (fun k => b k w)) with hlab
  -- the probability of a point
  have hpoint : ∀ z₀ : ResidueSpace (joinModuli m₀ (p L)),
      μ.expect (fun x => ∑ b, tgtWeight (prodJoint κ) b * (if lab x b = z₀ then (1 : ℝ) else 0)) =
        (Fintype.card (ResidueSpace (joinModuli m₀ (p L))) : ℝ)⁻¹ := by
    intro z₀
    have hiff : ∀ x b, lab x b = z₀ ↔
        (∀ i : {b : PaperAtom J L // IsLow p L P5 b}, x i w.1 = atomTarget m₀ p L z₀ i.1) ∧
          (∀ k : TailIdx p L P5, b k w = z₀ (Sum.inr k.1)) := by
      intro x b
      have h := frozen_eq_iff m₀ p L P5 (fun _ => true) w.1 x (fun k => b k w) z₀
      rw [frozenCoords_allTrue] at h
      simp only [mem_univ, forall_const] at h
      rw [← h]
      constructor
      · intro hx e
        rw [← hx]
        rfl
      · intro hx
        funext e
        exact hx e
    have hind : ∀ x b, (if lab x b = z₀ then (1 : ℝ) else 0) =
        (∏ i : {b : PaperAtom J L // IsLow p L P5 b},
          if x i w.1 = atomTarget m₀ p L z₀ i.1 then (1 : ℝ) else 0) *
        ∏ k : TailIdx p L P5, (if b k w = z₀ (Sum.inr k.1) then (1 : ℝ) else 0) := by
      intro x b
      rw [if_congr (hiff x b) rfl rfl, Finset.prod_boole, Finset.prod_boole, ite_zero_mul_ite_zero,
        mul_one]
      simp
    simp_rw [hind]
    unfold FiniteLaw.expect
    have hsplit : ∀ x : LowLabels m₀ p L P5,
        μ.weight x * ∑ b, tgtWeight (prodJoint κ) b *
          ((∏ i : {b : PaperAtom J L // IsLow p L P5 b},
            if x i w.1 = atomTarget m₀ p L z₀ i.1 then (1 : ℝ) else 0) *
          ∏ k : TailIdx p L P5, (if b k w = z₀ (Sum.inr k.1) then (1 : ℝ) else 0)) =
        (μ.weight x * ∏ i : {b : PaperAtom J L // IsLow p L P5 b},
            if x i w.1 = atomTarget m₀ p L z₀ i.1 then (1 : ℝ) else 0) *
          ∑ b, tgtWeight (prodJoint κ) b *
            ∏ k : TailIdx p L P5, (if b k w = z₀ (Sum.inr k.1) then (1 : ℝ) else 0) := by
      intro x
      rw [mul_sum, mul_sum]
      exact sum_congr rfl fun b _ => by ring
    simp_rw [hsplit]
    rw [← sum_mul]
    -- the low atoms
    have hlow : ∑ x : LowLabels m₀ p L P5, μ.weight x *
        ∏ i : {b : PaperAtom J L // IsLow p L P5 b},
          (if x i w.1 = atomTarget m₀ p L z₀ i.1 then (1 : ℝ) else 0) =
        (∏ i : {b : PaperAtom J L // IsLow p L P5 b},
          (Fintype.card (AtomLabel m₀ p L i.1) : ℝ))⁻¹ := by
      have h1 : ∀ x : LowLabels m₀ p L P5, μ.weight x *
          ∏ i : {b : PaperAtom J L // IsLow p L P5 b},
            (if x i w.1 = atomTarget m₀ p L z₀ i.1 then (1 : ℝ) else 0) =
          ∏ i : {b : PaperAtom J L // IsLow p L P5 b},
            ((ϱ i.1).weight (x i) * if x i w.1 = atomTarget m₀ p L z₀ i.1 then (1 : ℝ) else 0) := by
        intro x
        rw [prod_mul_distrib]
        rfl
      simp_rw [h1]
      rw [← Fintype.prod_sum (fun i : {b : PaperAtom J L // IsLow p L P5 b} =>
        fun t : Slot → AtomLabel m₀ p L i.1 =>
          (ϱ i.1).weight t * if t w.1 = atomTarget m₀ p L z₀ i.1 then (1 : ℝ) else 0)]
      rw [← prod_inv_distrib]
      refine Fintype.prod_congr _ _ fun i => ?_
      have h2 := hϱ i.1 w.1 (fun t => if t = atomTarget m₀ p L z₀ i.1 then (1 : ℝ) else 0)
      rw [FiniteLaw.expect_uniform, sum_ite_eq'] at h2
      have h3 : ∑ t : Slot → AtomLabel m₀ p L i.1,
          (ϱ i.1).weight t * (if t w.1 = atomTarget m₀ p L z₀ i.1 then (1 : ℝ) else 0) =
          (ϱ i.1).expect (fun z => if z w.1 = atomTarget m₀ p L z₀ i.1 then (1 : ℝ) else 0) := rfl
      rw [h3, h2]
      simp
    -- the tail primes
    have htail : ∑ b, tgtWeight (prodJoint κ) b *
        ∏ k : TailIdx p L P5, (if b k w = z₀ (Sum.inr k.1) then (1 : ℝ) else 0) =
        (∏ k : TailIdx p L P5, (p L k.1 : ℝ))⁻¹ := by
      simp_rw [tgtWeight_prodJoint, ← prod_mul_distrib]
      rw [← Fintype.prod_sum (fun k : TailIdx p L P5 =>
        fun t : {w // w ∉ ({u, v} : Finset Slot)} → ZMod (tailQ p L P5 k) =>
          tgtWeight (κ k) t * (if t w = z₀ (Sum.inr k.1) then (1 : ℝ) else 0))]
      rw [← prod_inv_distrib]
      refine Fintype.prod_congr _ _ fun k => ?_
      have := tailLaw_tgt_slot (tailQ p L P5) k huv (ϱ (some k.1)) (hU k) (hϱ (some k.1)) w
        (z₀ (Sum.inr k.1))
      convert this using 3 <;> first | rfl | (split_ifs <;> rfl)
    rw [hlow, htail, prod_card_lowAtoms, ← mul_inv]
    congr 1
    -- `|G_N| = ∏ m₀ · ∏_{p_j < P₅} p_j · ∏_{p_j ≥ P₅} p_j`
    have hall := prod_frozenCoords_nat (J₀ := J₀) m₀ p L P5 (fun _ => true)
    rw [frozenCoords_allTrue] at hall
    simp only [↓reduceIte] at hall
    rw [Fintype.card_pi]
    simp only [ZMod.card]
    have hcast : ((∏ c, joinModuli m₀ (p L) c : ℕ) : ℝ) =
        (((∏ i, m₀ i) * (∏ j ∈ univ.filter (fun j => p L j < P5), p L j) *
          ∏ k : TailIdx p L P5, p L k.1 : ℕ) : ℝ) := by
      rw [hall]
    push_cast at hcast ⊢
    rw [hcast]
  -- linearity
  have key : ∀ x, ∑ b, tgtWeight (prodJoint κ) b * f (lab x b) =
      ∑ z₀, f z₀ * ∑ b, tgtWeight (prodJoint κ) b * (if lab x b = z₀ then (1 : ℝ) else 0) := by
    intro x
    have hlin : ∀ b, f (lab x b) = ∑ z₀, f z₀ * (if lab x b = z₀ then (1 : ℝ) else 0) := by
      intro b
      simp
    simp_rw [hlin, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun z₀ _ => ?_
    exact sum_congr rfl fun b _ => by ring
  have hL : μ.expect (fun x => ∑ b, tgtWeight (prodJoint κ) b *
      f (atomGroupEquiv m₀ p L (mergeAt m₀ p L P5 (fun i => x i w.1) (fun k => b k w)))) =
      ∑ z₀, f z₀ * μ.expect (fun x => ∑ b, tgtWeight (prodJoint κ) b *
        (if lab x b = z₀ then (1 : ℝ) else 0)) := by
    have e : ∀ x, ∑ b, tgtWeight (prodJoint κ) b *
        f (atomGroupEquiv m₀ p L (mergeAt m₀ p L P5 (fun i => x i w.1) (fun k => b k w))) =
        ∑ z₀, f z₀ * ∑ b, tgtWeight (prodJoint κ) b *
          (if lab x b = z₀ then (1 : ℝ) else 0) := key
    unfold FiniteLaw.expect
    simp_rw [e, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun z₀ _ => ?_
    refine sum_congr rfl fun x _ => ?_
    ring_nf
  rw [hL, FiniteLaw.expect_uniform, sum_div]
  refine sum_congr rfl fun z₀ _ => ?_
  rw [hpoint z₀, div_eq_mul_inv]

end OtherSlot

/-! ## Moments of all orders -/

/-- **The `2r`-th moments of the query inputs** (`lem:record:lift-moments`(c)): given the
moment bound of `DensityDC.moment_input_le` (`ε = 1440 δ`) with constant `C`, for
`N = K L`, `L ≥ 2^{20} K`, every interval `I_b` and residue `s` modulo `D₀`:
`E_{G_N} |g^{I_b, D₀, s}|^{2r} ≤ (D₀^{2r} |X₀|^{2r} C K) N^{72δ} α`. -/
theorem indexedInput_moment {J₀ J : Type} [Fintype J₀] [DecidableEq J₀] [Fintype J]
    [DecidableEq J] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)] (q : J → ℕ) [∀ j, NeZero (q j)] (r : ℕ)
    (C : ℝ)
    (hmom : ∀ (Q : ℝ), 1 ≤ Q → ∀ (c : ℤ) (M : ℕ), 0 < M → 2 * ⌊Q⌋₊ ≤ M + 1 →
      ⌊Q⌋₊ ^ 5 ≤ M + 1 → ∀ {D0 : ℕ} (s : ZMod D0) (A : Finset ℤ),
      (FiniteLaw.uniform (ResidueSpace (joinModuli m₀ q))).moment ((2 * r : ℕ) : ℝ)
          (fun x => (input (joinModuli m₀ q) Q (Icc (c + 1) (c + M)) D0 s A x).re) ≤
        (D0 : ℝ) ^ (2 * r) * ((Fintype.card (ResidueSpace m₀) : ℝ) ^ (2 * r) * C *
          Q ^ (1440 * stageDelta) *
          ((((Icc 1 (M : ℤ)).filter fun x => ((x + c : ℤ) : ZMod D0) = s ∧ x + c ∈ A).card : ℝ) /
            M)))
    (hC : 0 < C) {K L : ℕ} [NeZero K] (hK : 1 ≤ K) (hL : 2 ^ 20 * K ≤ L) {D0 : ℕ}
    (A : Finset ℤ) (b : ZMod K) (s : ZMod D0) :
    (FiniteLaw.uniform (ResidueSpace (joinModuli m₀ q))).expect (fun z =>
        |indexedInput (joinModuli m₀ q) (paperCutoff (K * L)) K L D0 A (b, s) z| ^ (2 * r)) ≤
      ((D0 : ℝ) ^ (2 * r) * ((Fintype.card (ResidueSpace m₀) : ℝ) ^ (2 * r) * C) * K) *
        ((K * L : ℕ) : ℝ) ^ (72 * stageDelta) * density (K * L) A := by
  have hL1 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hKL : 1 ≤ K * L := Nat.one_le_iff_ne_zero.mpr (by positivity)
  set c : ℤ := ((leastPosRep b : ℤ) - 1) * L with hc
  have hI : blockInterval K L b = Icc (c + 1) (c + L) := by
    unfold blockInterval
    rw [Ioc_eq_Icc_int]
    congr 1
    rw [hc]
    ring
  obtain ⟨hf1, hf2⟩ := floor_cutoff_bounds hK hL
  have hm := hmom (paperCutoff (K * L)) (one_le_paperCutoff hKL) c L hL1 hf1 hf2 s A
  have hexp : (FiniteLaw.uniform (ResidueSpace (joinModuli m₀ q))).expect (fun z =>
      |indexedInput (joinModuli m₀ q) (paperCutoff (K * L)) K L D0 A (b, s) z| ^ (2 * r)) =
      (FiniteLaw.uniform (ResidueSpace (joinModuli m₀ q))).moment ((2 * r : ℕ) : ℝ)
        (fun x => (input (joinModuli m₀ q) (paperCutoff (K * L)) (Icc (c + 1) (c + L)) D0 s A
          x).re) := by
    unfold FiniteLaw.moment indexedInput
    rw [← hI]
    congr 1
    funext z
    rw [Real.rpow_natCast]
  rw [hexp]
  refine hm.trans ?_
  -- `Q^ε = N^{72δ}`
  have hQε : paperCutoff (K * L) ^ (1440 * stageDelta) = ((K * L : ℕ) : ℝ) ^ (72 * stageDelta) := by
    unfold paperCutoff liftExponent
    rw [← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    ring
  rw [hQε]
  -- `|B| / L ≤ K α`
  set B := (Icc 1 (L : ℤ)).filter fun x => ((x + c : ℤ) : ZMod D0) = s ∧ x + c ∈ A with hB
  have hBA : B.card ≤ A.card := by
    refine card_le_card_of_injOn (fun x => x + c) (fun x hx => ?_) (fun x _ y _ h => by
      simpa using h)
    exact ((mem_filter.mp hx).2).2
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL1
  have hKr : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hBL : (B.card : ℝ) / L ≤ K * density (K * L) A := by
    unfold density
    rw [Nat.cast_mul, div_le_iff₀ hLr]
    have : (B.card : ℝ) ≤ A.card := by exact_mod_cast hBA
    calc (B.card : ℝ) ≤ A.card := this
      _ = (K : ℝ) * ((A.card : ℝ) / ((K : ℝ) * L)) * L := by field_simp
  have hN0 : (0 : ℝ) ≤ ((K * L : ℕ) : ℝ) ^ (72 * stageDelta) := by positivity

  calc (D0 : ℝ) ^ (2 * r) * ((Fintype.card (ResidueSpace m₀) : ℝ) ^ (2 * r) * C *
        ((K * L : ℕ) : ℝ) ^ (72 * stageDelta) * ((B.card : ℝ) / L))
      = (D0 : ℝ) ^ (2 * r) * ((Fintype.card (ResidueSpace m₀) : ℝ) ^ (2 * r) * C) *
          ((K * L : ℕ) : ℝ) ^ (72 * stageDelta) * ((B.card : ℝ) / L) := by ring
    _ ≤ (D0 : ℝ) ^ (2 * r) * ((Fintype.card (ResidueSpace m₀) : ℝ) ^ (2 * r) * C) *
          ((K * L : ℕ) : ℝ) ^ (72 * stageDelta) * (K * density (K * L) A) :=
        mul_le_mul_of_nonneg_left hBL (by positivity)
    _ = ((D0 : ℝ) ^ (2 * r) * ((Fintype.card (ResidueSpace m₀) : ℝ) ^ (2 * r) * C) * K) *
          ((K * L : ℕ) : ℝ) ^ (72 * stageDelta) * density (K * L) A := by ring


/-- `F_A = g^{[N], 1, 0}`: the whole-interval lift is the input with `D₀ = 1`. -/
lemma wholeLift_eq_input {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)]
    (Q : ℝ) (N : ℕ) (A : Finset ℤ) (z : ResidueSpace m) :
    wholeLift m Q N A z = input m Q (Icc (0 + 1) (0 + (N : ℤ))) 1 0 A z := by
  unfold wholeLift input
  rw [zero_add, zero_add]
  congr 1
  funext n
  unfold indicator inputFun
  have : ((n : ZMod 1) = 0) := Subsingleton.elim _ _
  simp [this]

/-- **The `2r`-th moments of `F_A`** (`lem:record:lift-moments`(c) for `g^{[N],1,0}`), with the
constant `|X₀|^{2r} C ≤ M₀^{2r} |X₀|^{2r} C K`. -/
theorem wholeLift_moment {J₀ J : Type} [Fintype J₀] [DecidableEq J₀] [Fintype J]
    [DecidableEq J] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)] (q : J → ℕ) [∀ j, NeZero (q j)] (r : ℕ)
    (C : ℝ)
    (hmom : ∀ (Q : ℝ), 1 ≤ Q → ∀ (c : ℤ) (M : ℕ), 0 < M → 2 * ⌊Q⌋₊ ≤ M + 1 →
      ⌊Q⌋₊ ^ 5 ≤ M + 1 → ∀ {D0 : ℕ} (s : ZMod D0) (A : Finset ℤ),
      (FiniteLaw.uniform (ResidueSpace (joinModuli m₀ q))).moment ((2 * r : ℕ) : ℝ)
          (fun x => (input (joinModuli m₀ q) Q (Icc (c + 1) (c + M)) D0 s A x).re) ≤
        (D0 : ℝ) ^ (2 * r) * ((Fintype.card (ResidueSpace m₀) : ℝ) ^ (2 * r) * C *
          Q ^ (1440 * stageDelta) *
          ((((Icc 1 (M : ℤ)).filter fun x => ((x + c : ℤ) : ZMod D0) = s ∧ x + c ∈ A).card : ℝ) /
            M)))
    (hC : 0 < C) {K L : ℕ} (hK : 1 ≤ K) (hL : 2 ^ 20 * K ≤ L) (M₀ : ℕ) (hM₀ : 1 ≤ M₀)
    (A : Finset ℤ) :
    (FiniteLaw.uniform (ResidueSpace (joinModuli m₀ q))).expect (fun z =>
        |(wholeLift (joinModuli m₀ q) (paperCutoff (K * L)) (K * L) A z).re| ^ (2 * r)) ≤
      ((M₀ : ℝ) ^ (2 * r) * ((Fintype.card (ResidueSpace m₀) : ℝ) ^ (2 * r) * C) * K) *
        ((K * L : ℕ) : ℝ) ^ (72 * stageDelta) * density (K * L) A := by
  have hL1 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hKL : 1 ≤ K * L := Nat.one_le_iff_ne_zero.mpr (by positivity)
  obtain ⟨hf1, hf2⟩ := floor_cutoff_bounds hK hL
  have hLN : L ≤ K * L := Nat.le_mul_of_pos_left L (by omega)
  have hm := hmom (paperCutoff (K * L)) (one_le_paperCutoff hKL) 0 (K * L) (by omega)
    (by omega) (by omega) (0 : ZMod 1) A
  have hexp : (FiniteLaw.uniform (ResidueSpace (joinModuli m₀ q))).expect (fun z =>
      |(wholeLift (joinModuli m₀ q) (paperCutoff (K * L)) (K * L) A z).re| ^ (2 * r)) =
      (FiniteLaw.uniform (ResidueSpace (joinModuli m₀ q))).moment ((2 * r : ℕ) : ℝ)
        (fun x => (input (joinModuli m₀ q) (paperCutoff (K * L))
          (Icc (0 + 1) (0 + ((K * L : ℕ) : ℤ))) 1 0 A x).re) := by
    unfold FiniteLaw.moment
    congr 1
    funext z
    rw [wholeLift_eq_input, Real.rpow_natCast]
  rw [hexp]
  refine hm.trans ?_
  have hQε : paperCutoff (K * L) ^ (1440 * stageDelta) = ((K * L : ℕ) : ℝ) ^ (72 * stageDelta) := by
    unfold paperCutoff liftExponent
    rw [← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    ring
  rw [hQε]
  set B := (Icc 1 ((K * L : ℕ) : ℤ)).filter
    fun x => ((x + 0 : ℤ) : ZMod 1) = 0 ∧ x + 0 ∈ A with hB
  have hBA : B.card ≤ A.card := by
    refine card_le_card_of_injOn (fun x => x + 0) (fun x hx => ?_) (fun x _ y _ h => by
      simpa using h)
    exact ((mem_filter.mp hx).2).2
  have hNr : (0 : ℝ) < ((K * L : ℕ) : ℝ) := by exact_mod_cast (show 0 < K * L by omega)
  have hBN : (B.card : ℝ) / ((K * L : ℕ) : ℝ) ≤ density (K * L) A := by
    unfold density
    exact div_le_div_of_nonneg_right (by exact_mod_cast hBA) hNr.le
  have hM₀r : (1 : ℝ) ≤ (M₀ : ℝ) ^ (2 * r) := one_le_pow₀ (by exact_mod_cast hM₀)
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hα : 0 ≤ density (K * L) A := density_nonneg _ _
  have hX : (0 : ℝ) ≤ (Fintype.card (ResidueSpace m₀) : ℝ) ^ (2 * r) * C := by positivity
  have hN0 : (0 : ℝ) ≤ ((K * L : ℕ) : ℝ) ^ (72 * stageDelta) := by positivity
  simp only [Nat.cast_one, one_pow, one_mul]
  calc (Fintype.card (ResidueSpace m₀) : ℝ) ^ (2 * r) * C *
        ((K * L : ℕ) : ℝ) ^ (72 * stageDelta) * ((B.card : ℝ) / ((K * L : ℕ) : ℝ))
      ≤ (Fintype.card (ResidueSpace m₀) : ℝ) ^ (2 * r) * C *
          ((K * L : ℕ) : ℝ) ^ (72 * stageDelta) * density (K * L) A :=
        mul_le_mul_of_nonneg_left hBN (by positivity)
    _ ≤ ((M₀ : ℝ) ^ (2 * r) * ((Fintype.card (ResidueSpace m₀) : ℝ) ^ (2 * r) * C) * K) *
          ((K * L : ℕ) : ℝ) ^ (72 * stageDelta) * density (K * L) A := by
        apply mul_le_mul_of_nonneg_right _ hα
        apply mul_le_mul_of_nonneg_right _ hN0
        nlinarith [mul_le_mul hM₀r hKr zero_le_one (by linarith)]

/-! ## `DensityCancellation` from elementary facts about the data -/

section Final

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)] [∀ L j, Fact (p L j).Prime] {P : Type} [Fintype P] (pr h : P → ℕ)
  [∀ q, NeZero (pr q ^ h q)]

/-- `70` slots outside a pair. -/
lemma card_otherSlots {u v : Slot} (huv : u ≠ v) :
    Fintype.card {w // w ∉ ({u, v} : Finset Slot)} = 70 := by
  rw [Fintype.card_subtype_compl, Fintype.card_coe, card_pair huv]
  rfl

open Sarkozy.TheoremC Sarkozy.IndexSupport Sarkozy.Comparison in

theorem densityCancellation_of_data (P5 : ℕ) (pp ep : J₀ → ℕ)
    (hinj : ∀ L, Function.Injective (p L)) (h64 : 64 ≤ P5)
    (hcop0 : ∀ L (c : J₀ ⊕ J L), Nat.Coprime (modulus pr h) (joinModuli m₀ (p L) c))
    (hcopE : ∀ L, ∀ i j : J₀ ⊕ J L, i ≠ j →
      Nat.Coprime (joinModuli m₀ (p L) i) (joinModuli m₀ (p L) j))
    (hpre : ∀ i, (pp i).Prime ∧ 1 ≤ ep i ∧ m₀ i = pp i ^ ep i)
    (hcover : ∀ L : ℕ, ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ (1 / 40 : ℝ) →
      ℓ ∣ modulus pr h ∨ (∃ i, ℓ ∣ m₀ i) ∨ ∃ j, p L j = ℓ) :
    DensityCancellation m₀ p pr h P5 pp ep := by
  obtain ⟨C, hC, hmomC⟩ := DensityDC.moment_input_le 70 (by norm_num) (1440 * stageDelta)
    (by unfold stageDelta; norm_num)
  have hK : 1 ≤ blockScale := by unfold blockScale; norm_num
  have : NeZero blockScale := ⟨by unfold blockScale; norm_num⟩
  have hMod : 1 ≤ modulus pr h :=
    Nat.one_le_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun q _ => NeZero.ne _)
  set C₂ : ℝ := ((modulus pr h : ℕ) : ℝ) ^ (2 * 70) *
    ((Fintype.card (ResidueSpace m₀) : ℝ) ^ (2 * 70) * C) * blockScale with hC₂
  have hC₂0 : 0 ≤ C₂ := by positivity
  apply densityCancellation_of_otherSlots m₀ p pr h P5 pp ep hinj h64 hC₂0
    (2 ^ 20 * blockScale) hcop0 hcopE hpre hcover
  intro L hL A hA ϱ hϱ u v huv ha hb bI s r hbI hr G hGu hGv hGw
  have hNα : 0 ≤ C₂ * ((blockScale * L : ℕ) : ℝ) ^ (72 * stageDelta) * density (blockScale * L) A :=
    mul_nonneg (mul_nonneg hC₂0 (by positivity)) (density_nonneg _ _)
  refine step2_other_slots
    (FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1))
    (encKappa m₀ p L P5 ϱ huv (fun k => (ha k.1 k.2).1)) 70 (card_otherSlots huv) (by norm_num)
    (fun i xb => atomGroupEquiv m₀ p L (mergeAt m₀ p L P5 (fun i' => xb.1 i' i.1)
      (fun k => xb.2 k i)))
    (fun i y => G i.1 ((atomGroupEquiv m₀ p L).symm y)) (encW m₀ p L P5 G u v)
    (fun x b => by
      unfold encW
      simp only [Equiv.symm_apply_apply])
    (fun i f => other_slot_uniform m₀ p L P5 huv ϱ hϱ (fun k => (ha k.1 k.2).1) i f) hNα
    (fun i => ?_)
  have hiu : i.1 ≠ u := fun h => i.2 (by rw [h]; simp)
  have hiv : i.1 ≠ v := fun h => i.2 (by rw [h]; simp)
  rcases hGw i.1 hiu hiv with hG | ⟨ω, hG⟩
  · have hm := wholeLift_moment m₀ (p L) 70 C
      (fun Q hQ c M hM h1 h2 => hmomC m₀ (p L) (fun j => (Fact.out : (p L j).Prime)) (hinj L)
        Q hQ c M hM h1 h2) hC hK hL (modulus pr h) hMod A
    refine le_of_eq_of_le (FiniteLaw.expect_congr _ fun y => ?_) hm
    rw [Real.rpow_natCast, hG]
    unfold atomLift
    rw [Equiv.apply_symm_apply]
  · have hm := indexedInput_moment m₀ (p L) 70 C
      (fun Q hQ c M hM h1 h2 => hmomC m₀ (p L) (fun j => (Fact.out : (p L j).Prime)) (hinj L)
        Q hQ c M hM h1 h2) hC hK hL A ω.1 ω.2
    refine le_of_eq_of_le (FiniteLaw.expect_congr _ fun y => ?_) hm
    rw [Real.rpow_natCast, hG]
    unfold indexInputAt
    rw [Equiv.apply_symm_apply]

end Final

/-! ## From WP-FI's standing data -/

section Standing

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)] {P : Type} [Fintype P] (pr h : P → ℕ)
  [∀ q, NeZero (pr q ^ h q)]

open Sarkozy.TheoremC Sarkozy.IndexSupport Sarkozy.Comparison in
/-- **`DensityCancellation` from WP-FI's standing data** (`TheoremC.StandingData`, `def:cp0`): the
prefix moduli `m₀ i = pp_i^{ep_i}`, the distinct prime tail coordinates and `M₀` coprime to every
atom modulus are fields of the standing data. What remains are three facts of the paper's
construction of `G_N` that the standing data does not record:
* `P₅ ≥ 64`;
* the atom moduli are pairwise coprime (`hcopE`: distinct prefix primes, none of them a tail
  prime);
* every prime `ℓ ≤ N^{1/40}` divides `M₀` or a prefix modulus or is a tail prime (`hcover`). -/
theorem densityCancellation_of_standing {E : Type} [Fintype E] [DecidableEq E]
    (D : StandingData m₀ p pr h E) (P5 : ℕ) (h64 : 64 ≤ P5)
    (hcopE : ∀ L, ∀ i j : J₀ ⊕ J L, i ≠ j →
      Nat.Coprime (joinModuli m₀ (p L) i) (joinModuli m₀ (p L) j))
    (hcover : ∀ L : ℕ, ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ (1 / 40 : ℝ) →
      ℓ ∣ modulus pr h ∨ (∃ i, ℓ ∣ m₀ i) ∨ ∃ j, p L j = ℓ) :
    DensityCancellation m₀ p pr h P5 D.pp D.ep := by
  have : ∀ L j, Fact (p L j).Prime := fun L j => ⟨D.p_prime L j⟩
  exact densityCancellation_of_data m₀ p pr h P5 D.pp D.ep D.p_inj h64 D.modulus_coprime hcopE
    (fun i => ⟨D.pp_prime i, D.ep_pos i, D.m₀_eq i⟩) hcover

end Standing

end Sarkozy.CancellationSteps
