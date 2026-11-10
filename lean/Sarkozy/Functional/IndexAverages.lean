module

public import Sarkozy.Functional.Lift

@[expose] public section

/-!
# Index averages of lifts (`lem:twointerval`)

The intervals `I_b` of `def:record:functional`(f), and `lem:twointerval`
(`paper/sections/06_lifts_sectors.tex`): the partition identity
`𝓛_{I,N} f = ∑_j (|J_j|/|I|) 𝓛_{J_j,N}(f|_{J_j})` and its consequences
(i) (average over the intervals `I_b`), (ii) (conditional expectation over
residues) and (iii) (the mean identity `E_{b,s} g^{I_b,D₀,s} = F_A`).

The partition identity is proved for a partition of an arbitrary finite set of
integers into arbitrary pairwise disjoint finite parts (empty parts are
allowed, and contribute nothing); the paper's statement is the case of
intervals. As in the paper, only the linearity of the lift and the
independence of the retained set from the interval are used; the moduli are
arbitrary.

The conditional expectation in (ii) is the average over the fibre
`{s ∈ ℤ/D₀ℤ : s ≡ t (mod D')}`, which has `D₀/D'` elements
(`card_residueFibre`); this is the conditional expectation for uniform `s`.
-/

open Finset Complex
open scoped BigOperators ComplexConjugate

namespace Sarkozy.Functional

open Sarkozy.FourierArithmetic

/-! ### The intervals `I_b` -/

section Intervals

/-- The least positive residue of `b ∈ ℤ/Kℤ`, in `{1, …, K}`
(`def:record:functional`(f)). -/
def leastPosRep {K : ℕ} (b : ZMod K) : ℕ := if b.val = 0 then K else b.val

/-- The interval `I_b = ((b − 1)L, bL] ∩ ℤ` (`def:record:functional`(f)). -/
def blockInterval (K L : ℕ) (b : ZMod K) : Finset ℤ :=
  Ioc (((leastPosRep b : ℤ) - 1) * L) ((leastPosRep b : ℤ) * L)

variable {K : ℕ} [NeZero K]

theorem one_le_leastPosRep (b : ZMod K) : 1 ≤ leastPosRep b := by
  unfold leastPosRep
  split_ifs with h
  · exact Nat.one_le_iff_ne_zero.mpr (NeZero.ne K)
  · omega

theorem leastPosRep_le (b : ZMod K) : leastPosRep b ≤ K := by
  unfold leastPosRep
  split_ifs with h
  · exact le_rfl
  · exact (ZMod.val_lt b).le

theorem natCast_leastPosRep (b : ZMod K) : ((leastPosRep b : ℕ) : ZMod K) = b := by
  unfold leastPosRep
  split_ifs with h
  · rw [ZMod.natCast_self]
    exact ((ZMod.val_eq_zero b).mp h).symm
  · exact ZMod.natCast_zmod_val b

theorem leastPosRep_natCast {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ K) :
    leastPosRep (k : ZMod K) = k := by
  unfold leastPosRep
  rcases h2.lt_or_eq with h | h
  · rw [ZMod.val_natCast, Nat.mod_eq_of_lt h]
    simp [show k ≠ 0 by omega]
  · subst h
    simp

theorem leastPosRep_injective : Function.Injective (leastPosRep (K := K)) := by
  intro a b h
  rw [← natCast_leastPosRep a, ← natCast_leastPosRep b, h]

/-- The shift `b ↦ b + 1` moves `I_b` to the next interval, and wraps `I_K` to `I_1`. -/
theorem leastPosRep_add_one (b : ZMod K) :
    leastPosRep (b + 1) = if leastPosRep b < K then leastPosRep b + 1 else 1 := by
  have hb : b + 1 = ((leastPosRep b + 1 : ℕ) : ZMod K) := by
    rw [Nat.cast_add, natCast_leastPosRep, Nat.cast_one]
  split_ifs with h
  · rw [hb, leastPosRep_natCast (by omega) (by omega)]
  · have he : leastPosRep b = K := le_antisymm (leastPosRep_le b) (not_lt.mp h)
    rw [hb, he, Nat.cast_add, ZMod.natCast_self, zero_add]
    exact leastPosRep_natCast le_rfl (Nat.one_le_iff_ne_zero.mpr (NeZero.ne K))

omit [NeZero K] in
theorem mem_blockInterval {L : ℕ} {b : ZMod K} {n : ℤ} :
    n ∈ blockInterval K L b ↔
      ((leastPosRep b : ℤ) - 1) * L < n ∧ n ≤ (leastPosRep b : ℤ) * L := by
  simp [blockInterval]

omit [NeZero K] in
/-- The intervals `I_b` have length `L`. -/
theorem card_blockInterval (L : ℕ) (b : ZMod K) : (blockInterval K L b).card = L := by
  rw [blockInterval, Int.card_Ioc]
  have : (leastPosRep b : ℤ) * L - ((leastPosRep b : ℤ) - 1) * L = L := by ring
  rw [this, Int.toNat_natCast]

/-- Every element of `I_b` is smaller than every element of `I_{b+1}` when `b < K`. -/
theorem blockInterval_lt_succ {L : ℕ} {b : ZMod K} (hb : leastPosRep b < K) {x y : ℤ}
    (hx : x ∈ blockInterval K L b) (hy : y ∈ blockInterval K L (b + 1)) : x < y := by
  rw [mem_blockInterval] at hx hy
  rw [leastPosRep_add_one, ite_eq_left hb] at hy
  push_cast at hy
  linarith [hx.2, hy.1]

theorem blockInterval_pairwiseDisjoint (L : ℕ) :
    ((univ : Finset (ZMod K)) : Set (ZMod K)).PairwiseDisjoint (blockInterval K L) := by
  intro a _ b _ hab
  have hne : leastPosRep a ≠ leastPosRep b := fun h => hab (leastPosRep_injective h)
  rw [Function.onFun, Finset.disjoint_left]
  intro n hna hnb
  rw [mem_blockInterval] at hna hnb
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have h' : (leastPosRep a : ℤ) ≤ (leastPosRep b : ℤ) - 1 := by omega
    have : (leastPosRep a : ℤ) * L ≤ ((leastPosRep b : ℤ) - 1) * L :=
      mul_le_mul_of_nonneg_right h' (Nat.cast_nonneg L)
    linarith [hna.2, hnb.1]
  · have h' : (leastPosRep b : ℤ) ≤ (leastPosRep a : ℤ) - 1 := by omega
    have : (leastPosRep b : ℤ) * L ≤ ((leastPosRep a : ℤ) - 1) * L :=
      mul_le_mul_of_nonneg_right h' (Nat.cast_nonneg L)
    linarith [hnb.2, hna.1]

/-- The intervals `I_b`, `b ∈ ℤ/Kℤ`, partition `[N] = {1, …, KL}`. -/
theorem biUnion_blockInterval (L : ℕ) :
    (univ : Finset (ZMod K)).biUnion (blockInterval K L) = Icc 1 ((K * L : ℕ) : ℤ) := by
  ext n
  simp only [mem_biUnion, mem_univ, true_and, mem_blockInterval, mem_Icc]
  constructor
  · rintro ⟨b, h1, h2⟩
    have hb1 := one_le_leastPosRep b
    have hb2 := leastPosRep_le b
    have h0 : 0 ≤ ((leastPosRep b : ℤ) - 1) * L :=
      mul_nonneg (by omega) (Nat.cast_nonneg L)
    have h3 : (leastPosRep b : ℤ) * L ≤ (K : ℤ) * L :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hb2) (Nat.cast_nonneg L)
    push_cast
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    have hL : 0 < L := by
      rcases Nat.eq_zero_or_pos L with hL | hL
      · subst hL
        push_cast at h2
        omega
      · exact hL
    -- the block index k = ⌈n / L⌉
    set k : ℕ := ((n - 1) / L).toNat + 1 with hk
    have hq0 : 0 ≤ (n - 1) / (L : ℤ) := Int.ediv_nonneg (by omega) (by omega)
    have hkq : (k : ℤ) = (n - 1) / L + 1 := by
      rw [hk]; push_cast; rw [Int.toNat_of_nonneg hq0]
    have hdiv := Int.mul_ediv_add_emod (n - 1) (L : ℤ)
    have hmod0 := Int.emod_nonneg (n - 1) (show (L : ℤ) ≠ 0 by omega)
    have hmodL := Int.emod_lt_of_pos (n - 1) (show (0 : ℤ) < L by omega)
    have hk1 : 1 ≤ k := by omega
    have hkK : k ≤ K := by
      have : ((n - 1) / L) * (L : ℤ) < (K : ℤ) * L := by
        push_cast at h2
        nlinarith
      have : (n - 1) / (L : ℤ) < K := lt_of_mul_lt_mul_right this (Nat.cast_nonneg L)
      omega
    refine ⟨(k : ZMod K), ?_⟩
    rw [leastPosRep_natCast hk1 hkK, hkq]
    constructor <;> nlinarith

end Intervals

/-! ### Linearity and the partition identity -/

section Partition

variable {J : Type*} [Fintype J] (m : J → ℕ) [∀ j, NeZero (m j)]

theorem liftOn_sum {ι : Type*} (S : Finset ι) (T : Finset (ResidueSpace m)) (I : Finset ℤ)
    (f : ι → ℤ → ℂ) (z : ResidueSpace m) :
    liftOn m T I (fun n => ∑ i ∈ S, f i n) z = ∑ i ∈ S, liftOn m T I (f i) z := by
  unfold liftOn intervalCoeff
  simp only [sum_mul, mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply sum_congr rfl
  intro a _
  exact Finset.sum_comm

/-- The coefficient form of the partition identity. -/
theorem intervalCoeff_biUnion {ι : Type*} (P : Finset ι) (parts : ι → Finset ℤ)
    (hdisj : (P : Set ι).PairwiseDisjoint parts) (f : ℤ → ℂ) (a : ResidueSpace m) :
    intervalCoeff m (P.biUnion parts) f a =
      ∑ i ∈ P, ((parts i).card / (P.biUnion parts).card : ℂ) *
        intervalCoeff m (parts i) f a := by
  unfold intervalCoeff
  rw [sum_biUnion hdisj, mul_sum]
  apply sum_congr rfl
  intro i _
  by_cases h : (parts i).card = 0
  · rw [card_eq_zero.mp h]
    simp
  · have hc : ((parts i).card : ℂ) ≠ 0 := by exact_mod_cast h
    calc
      _ = ((P.biUnion parts).card : ℂ)⁻¹ *
            (∑ n ∈ parts i, f n * conj (prodChar m a (integerResidue m n))) *
            (((parts i).card : ℂ) * ((parts i).card : ℂ)⁻¹) := by
        rw [mul_inv_cancel₀ hc, mul_one]
      _ = _ := by ring

/-- `lem:twointerval`, partition identity:
`𝓛_I f = ∑_j (|J_j|/|I|) 𝓛_{J_j}(f|_{J_j})` for `I = ⨆_j J_j` (disjoint). -/
theorem liftOn_biUnion (T : Finset (ResidueSpace m)) {ι : Type*} (P : Finset ι)
    (parts : ι → Finset ℤ) (hdisj : (P : Set ι).PairwiseDisjoint parts) (f : ℤ → ℂ)
    (z : ResidueSpace m) :
    liftOn m T (P.biUnion parts) f z =
      ∑ i ∈ P, ((parts i).card / (P.biUnion parts).card : ℂ) * liftOn m T (parts i) f z := by
  unfold liftOn
  simp_rw [intervalCoeff_biUnion m P parts hdisj f, sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro a _
  ring

/-- `lem:twointerval`, partition identity, for an arbitrary partition
`I = J_1 ⊔ ⋯ ⊔ J_k` (given as a pairwise disjoint family with union `I`). -/
theorem liftOn_partition (T : Finset (ResidueSpace m)) {ι : Type*} (P : Finset ι)
    (parts : ι → Finset ℤ) (hdisj : (P : Set ι).PairwiseDisjoint parts) {I : Finset ℤ}
    (hI : P.biUnion parts = I) (f : ℤ → ℂ) (z : ResidueSpace m) :
    liftOn m T I f z = ∑ i ∈ P, ((parts i).card / I.card : ℂ) * liftOn m T (parts i) f z := by
  subst hI
  exact liftOn_biUnion m T P parts hdisj f z

end Partition

/-! ### Consequences (i)–(iii) -/

section Consequences

variable {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)]

omit [DecidableEq J] in
/-- `lem:twointerval`(i) for an arbitrary input: averaging the lifts on the
intervals `I_b` gives the lift on `[N]`, `N = KL`. -/
theorem average_blocks_liftOn (T : Finset (ResidueSpace m)) {K : ℕ} [NeZero K] {L : ℕ}
    (hL : 1 ≤ L) (f : ℤ → ℂ) (z : ResidueSpace m) :
    (K : ℂ)⁻¹ * ∑ b : ZMod K, liftOn m T (blockInterval K L b) f z =
      liftOn m T (Icc 1 ((K * L : ℕ) : ℤ)) f z := by
  rw [liftOn_partition m T univ (blockInterval K L) (blockInterval_pairwiseDisjoint L)
    (biUnion_blockInterval L) f z, mul_sum]
  apply sum_congr rfl
  intro b _
  have hK : (K : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne K
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
  have hc : ((Icc 1 ((K * L : ℕ) : ℤ)).card : ℂ) = (K : ℂ) * L := by
    rw [card_Icc_one]; push_cast; ring
  rw [card_blockInterval, hc]
  field_simp

/-- `lem:twointerval`(i): `K⁻¹ ∑_{b ∈ ℤ/Kℤ} g^{I_b,D₀,s} = g^{[N],D₀,s}`. -/
theorem average_blocks_input (Q : ℝ) {K : ℕ} [NeZero K] {L : ℕ} (hL : 1 ≤ L) (D0 : ℕ)
    (s : ZMod D0) (A : Finset ℤ) (z : ResidueSpace m) :
    (K : ℂ)⁻¹ * ∑ b : ZMod K, input m Q (blockInterval K L b) D0 s A z =
      input m Q (Icc 1 ((K * L : ℕ) : ℤ)) D0 s A z :=
  average_blocks_liftOn m _ hL _ z

/-- The fibre `{s ∈ ℤ/D₀ℤ : s ≡ t (mod D')}` of the reduction map. -/
noncomputable def residueFibre {D0 D' : ℕ} [NeZero D0] (h : D' ∣ D0) (t : ZMod D') : Finset (ZMod D0) :=
  univ.filter fun s => ZMod.castHom h (ZMod D') s = t

/-- Each residue fibre has `D₀/D'` elements, so the fibre average is the
conditional expectation of a uniform `s` given `s mod D'`. -/
theorem card_residueFibre {D0 D' : ℕ} [NeZero D0] (h : D' ∣ D0) (t : ZMod D') :
    (residueFibre h t).card * D' = D0 := by
  have hD' : D' ≠ 0 := fun h0 => NeZero.ne D0 (Nat.eq_zero_of_zero_dvd (h0 ▸ h))
  have : NeZero D' := ⟨hD'⟩
  have hsurj := ZMod.castHom_surjective h
  have hall : ∀ t' : ZMod D', (residueFibre h t').card = (residueFibre h t).card := by
    intro t'
    exact AddMonoidHom.card_fiber_eq_of_mem_range (ZMod.castHom h (ZMod D'))
      (hsurj t') (hsurj t)
  have hsum := card_eq_sum_card_fiberwise (f := ZMod.castHom h (ZMod D'))
    (s := (univ : Finset (ZMod D0))) (t := (univ : Finset (ZMod D'))) (fun _ _ => mem_univ _)
  rw [card_univ, ZMod.card] at hsum
  have h2 : (∑ t' ∈ (univ : Finset (ZMod D')),
      (univ.filter fun s : ZMod D0 => ZMod.castHom h (ZMod D') s = t').card) =
        (residueFibre h t).card * D' := by
    have hc : ∀ t' ∈ (univ : Finset (ZMod D')),
        (univ.filter fun s : ZMod D0 => ZMod.castHom h (ZMod D') s = t').card =
          (residueFibre h t).card := fun t' _ => hall t'
    rw [sum_congr rfl hc, sum_const, card_univ, ZMod.card, smul_eq_mul, mul_comm]
  omega

/-- The residue identity behind `lem:twointerval`(ii):
`∑_{s ≡ t (D')} D₀ 1_{n ≡ s (D₀)} = (D₀/D') · D' 1_{n ≡ t (D')}`. -/
theorem sum_inputFun_residueFibre {D0 D' : ℕ} [NeZero D0] (h : D' ∣ D0) (t : ZMod D')
    (A : Finset ℤ) (n : ℤ) :
    ∑ s ∈ residueFibre h t, inputFun D0 s A n =
      ((residueFibre h t).card : ℂ) * inputFun D' t A n := by
  have hD' : D' ≠ 0 := fun h0 => NeZero.ne D0 (Nat.eq_zero_of_zero_dvd (h0 ▸ h))
  have hcard := card_residueFibre h t
  have hcast : ZMod.castHom h (ZMod D') (n : ZMod D0) = (n : ZMod D') := by
    rw [ZMod.castHom_apply, ZMod.cast_intCast h]
  unfold inputFun
  rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
  have hfil : (residueFibre h t).filter (fun s => (n : ZMod D0) = s ∧ n ∈ A) =
      if (n : ZMod D') = t ∧ n ∈ A then {(n : ZMod D0)} else ∅ := by
    ext s
    simp only [residueFibre, mem_filter, mem_univ, true_and]
    split_ifs with hc
    · simp only [mem_singleton]
      constructor
      · rintro ⟨_, hs, _⟩; exact hs.symm
      · rintro rfl; exact ⟨by rw [hcast]; exact hc.1, rfl, hc.2⟩
    · simp only [Finset.notMem_empty, iff_false, not_and]
      rintro hs rfl hA
      exact hc ⟨by rw [← hcast]; exact hs, hA⟩
  rw [hfil]
  split_ifs with hc
  · rw [card_singleton, Nat.cast_one, one_mul]
    exact_mod_cast hcard.symm
  · simp

/-- `lem:twointerval`(ii): `E[g^{I,D₀,s} | s mod D'] = g^{I,D',s mod D'}`, the
conditional expectation being the average over the residue fibre. -/
theorem fibreAverage_input (Q : ℝ) (I : Finset ℤ) {D0 D' : ℕ} [NeZero D0] (h : D' ∣ D0)
    (t : ZMod D') (A : Finset ℤ) (z : ResidueSpace m) :
    ((residueFibre h t).card : ℂ)⁻¹ * ∑ s ∈ residueFibre h t, input m Q I D0 s A z =
      input m Q I D' t A z := by
  have hD' : D' ≠ 0 := fun h0 => NeZero.ne D0 (Nat.eq_zero_of_zero_dvd (h0 ▸ h))
  have hpos : (residueFibre h t).card ≠ 0 := by
    intro h0
    have := card_residueFibre h t
    rw [h0, zero_mul] at this
    exact NeZero.ne D0 this.symm
  have hc : ((residueFibre h t).card : ℂ) ≠ 0 := by exact_mod_cast hpos
  unfold input lift
  rw [← liftOn_sum]
  simp_rw [sum_inputFun_residueFibre h t A]
  rw [liftOn_smul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-- With `D' = 1` the input is the plain indicator. -/
theorem inputFun_one (t : ZMod 1) (A : Finset ℤ) : inputFun 1 t A = indicator A := by
  funext n
  simp only [inputFun, indicator, Nat.cast_one, Subsingleton.elim (n : ZMod 1) t, true_and]

/-- `lem:twointerval`(ii) with `D' = 1`: `E_s g^{I,D₀,s} = 𝓛_{I,N}(1_A|_I)`. -/
theorem average_input_residues (Q : ℝ) (I : Finset ℤ) (D0 : ℕ) [NeZero D0] (A : Finset ℤ)
    (z : ResidueSpace m) :
    (D0 : ℂ)⁻¹ * ∑ s : ZMod D0, input m Q I D0 s A z = lift m Q I (indicator A) z := by
  have h := fibreAverage_input m Q I (one_dvd D0) (0 : ZMod 1) A z
  have hfib : residueFibre (one_dvd D0) (0 : ZMod 1) = univ := by
    ext s; simp [residueFibre, Subsingleton.elim _ (0 : ZMod 1)]
  rw [hfib, card_univ, ZMod.card] at h
  rw [h, input, inputFun_one]

/-- `lem:twointerval`(iii), whole interval: `E_s g^{[N],D₀,s} = F_A`. -/
theorem average_input_whole (Q : ℝ) (N D0 : ℕ) [NeZero D0] (A : Finset ℤ)
    (z : ResidueSpace m) :
    (D0 : ℂ)⁻¹ * ∑ s : ZMod D0, input m Q (Icc 1 (N : ℤ)) D0 s A z = wholeLift m Q N A z :=
  average_input_residues m Q _ D0 A z

/-- `lem:twointerval`(iii): for independent uniform `b ∈ ℤ/Kℤ` and
`s ∈ ℤ/D₀ℤ`, `E_{b,s} g^{I_b,D₀,s} = F_A` identically on the group. -/
theorem average_input_blocks (Q : ℝ) {K : ℕ} [NeZero K] {L : ℕ} (hL : 1 ≤ L) (D0 : ℕ)
    [NeZero D0] (A : Finset ℤ) (z : ResidueSpace m) :
    (K : ℂ)⁻¹ * ∑ b : ZMod K, ((D0 : ℂ)⁻¹ * ∑ s : ZMod D0,
      input m Q (blockInterval K L b) D0 s A z) = wholeLift m Q (K * L) A z := by
  simp_rw [average_input_residues m Q _ D0 A z]
  exact average_blocks_liftOn m _ hL _ z

end Consequences

end Sarkozy.Functional
