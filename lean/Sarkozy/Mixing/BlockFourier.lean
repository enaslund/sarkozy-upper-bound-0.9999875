module

public import Sarkozy.Mixing.Fourier

/-!
# The conductor hypothesis for block label groups

`lem:record:prefix-conductor` as stated in the paper: the prefix `X'` is a finite product of
cyclic groups carrying an arbitrary law `ρ'` with uniform one-slot marginals (not necessarily a
product over its cyclic factors), and the conductor `q(ξ)` of a character is its reduced
denominator, that is the order `ord(a)` (`addOrderOf a`) of its frequency `a`.

Coordinates `j ∈ K` carry block label groups `X_j = ∏_{i ∈ I_j} ℤ/n_{j,i}ℤ`
(`ResidueSpace (n j)`). The coordinates outside `T` are prefix blocks (one coordinate `X'`, or
for instance the atoms below `P₅` of `lem:record:density-dc`, each with its own joint law); the
coordinates of `T` are tail blocks with a number `q_j` divisible by their moduli (the tail
fields `𝔽_p`: `I_j` a singleton and `n_{j,*} = q_j = p`).

* `block_fourier_inversion`, `sectorProj_blockChar`, `sectorProj_eq_zero_of_blockCoeff`:
  Fourier analysis on `∏_j X_j`; the exact-support projection of the block structure keeps
  `χ_a` if the blocks where `a` is nonzero form `S` and kills it otherwise.
* `addOrderOf_le_of_blockSupport`: a frequency `a` of exact block support `S` has
  `ord(a) ≤ C' q_{S ∩ T}` as soon as every prefix modulus divides `C'` (equivalently, `C'` is
  divisible by the reduced denominator of every character of the prefix) and every modulus of
  a tail block `j` divides `q_j`. Neither primality of the tail moduli nor coprimality of `C'`
  and the tail primes is needed for this inequality.
* `support_of_blockCoeff` (the bridge) and `prefix_conductor_blocks` (the lemma).
-/

@[expose] public section

open Finset Complex
open scoped BigOperators Matrix ComplexConjugate

namespace Sarkozy.Mixing

open Sarkozy.IndexSupport Sarkozy.FourierArithmetic

/-- The coordinate projections on a character of a block `ResidueSpace p`. -/
theorem coordProj_prodChar {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ)
    [∀ i, NeZero (p i)] (s : Bool) (b x : ResidueSpace p) :
    ∑ y, (coordProj (ResidueSpace p) s x y : ℂ) * prodChar p b y =
      if (b ≠ 0) = (s = true) then prodChar p b x else 0 := by
  have hmean : ∑ y : ResidueSpace p, ((meanMatrix (ResidueSpace p) x y : ℝ) : ℂ) *
      prodChar p b y = if b = 0 then 1 else 0 := by
    have h := prodChar_expect p b
    rw [expect_eq_sum_div_card] at h
    rw [← h]
    simp only [meanMatrix_apply, Complex.ofReal_inv, Complex.ofReal_natCast, card_univ]
    rw [div_eq_inv_mul, Finset.mul_sum]
  cases s
  · simp only [coordProj, Bool.false_eq_true, ite_false, hmean]
    by_cases hb : b = 0
    · simp [hb]
    · simp [hb]
  · simp only [coordProj, ite_true, Matrix.sub_apply, Complex.ofReal_sub, sub_mul,
      Finset.sum_sub_distrib, hmean, Matrix.one_apply]
    simp only [apply_ite (fun r : ℝ => (r : ℂ)), Complex.ofReal_one, Complex.ofReal_zero,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, mem_univ, ite_true]
    by_cases hb : b = 0
    · simp [hb]
    · simp [hb]

variable {K : Type*} [Fintype K] [DecidableEq K] {I : K → Type*} [∀ j, Fintype (I j)]
  [∀ j, DecidableEq (I j)] (n : ∀ j, I j → ℕ) [∀ j, ∀ i, NeZero (n j i)]

/-- The characters `χ_a(z) = ∏_j χ_{a_j}(z_j)` of `∏_j X_j`, `X_j = ResidueSpace (n j)`. -/
noncomputable def blockChar (a z : ∀ j, ResidueSpace (n j)) : ℂ :=
  ∏ j, prodChar (n j) (a j) (z j)

/-- The Fourier coefficient `ĝ(a) = E_z g(z) conj(χ_a(z))` on `∏_j X_j`. -/
noncomputable def blockCoeff (g : (∀ j, ResidueSpace (n j)) → ℝ)
    (a : ∀ j, ResidueSpace (n j)) : ℂ :=
  𝔼 z, (g z : ℂ) * conj (blockChar n a z)

/-- Dual orthogonality: `∑_a χ_a(z) conj(χ_a(y)) = |X| [z = y]`. -/
theorem sum_blockChar_mul_conj (z y : ∀ j, ResidueSpace (n j)) :
    ∑ a, blockChar n a z * conj (blockChar n a y) =
      if z = y then (Fintype.card (∀ j, ResidueSpace (n j)) : ℂ) else 0 := by
  simp only [blockChar, map_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun j b => prodChar (n j) b (z j) * conj (prodChar (n j) b (y j)))]
  simp only [sum_prodChar_mul_conj]
  rw [Fintype.card_pi, Nat.cast_prod]
  by_cases h : z = y
  · subst h
    simp
  · rw [ite_eq_right h]
    obtain ⟨j, hj⟩ : ∃ j, z j ≠ y j := by
      by_contra h'
      push Not at h'
      exact h (funext h')
    exact prod_eq_zero (mem_univ j) (ite_eq_right hj)

/-- Fourier inversion `g(z) = ∑_a ĝ(a) χ_a(z)` on `∏_j X_j`. -/
theorem block_fourier_inversion (g : (∀ j, ResidueSpace (n j)) → ℝ)
    (z : ∀ j, ResidueSpace (n j)) :
    (g z : ℂ) = ∑ a, blockCoeff n g a * blockChar n a z := by
  have hc : (Fintype.card (∀ j, ResidueSpace (n j)) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [blockCoeff, expect_eq_sum_div_card, card_univ, Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hy (y : ∀ j, ResidueSpace (n j)) : ∑ a, (g y : ℂ) * conj (blockChar n a y) /
      (Fintype.card (∀ j, ResidueSpace (n j)) : ℂ) * blockChar n a z =
      (g y : ℂ) / (Fintype.card (∀ j, ResidueSpace (n j)) : ℂ) *
        ∑ a, blockChar n a z * conj (blockChar n a y) := by
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro a _
    ring
  simp only [hy, sum_blockChar_mul_conj, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [mem_univ, ite_true]
  field_simp

/-- `P_S χ_a = [the blocks where a ≠ 0 form S] χ_a`. -/
theorem sectorProj_blockChar (l : K → Bool) (a z : ∀ j, ResidueSpace (n j)) :
    ∑ y, (sectorProj (fun j => ResidueSpace (n j)) l z y : ℂ) * blockChar n a y =
      if (∀ j, (a j ≠ 0) = (l j = true)) then blockChar n a z else 0 := by
  simp only [sectorProj, piKron_apply, Complex.ofReal_prod, blockChar,
    ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun j y => (coordProj (ResidueSpace (n j)) (l j) (z j) y : ℂ) *
    prodChar (n j) (a j) y)]
  simp only [coordProj_prodChar]
  by_cases h : ∀ j, (a j ≠ 0) = (l j = true)
  · rw [ite_eq_left h]
    exact prod_congr rfl (fun j _ => by rw [ite_eq_left (h j)])
  · rw [ite_eq_right h]
    obtain ⟨j, hj⟩ := not_forall.mp h
    exact prod_eq_zero (mem_univ j) (by rw [ite_eq_right hj])

/-- If `ĝ` vanishes on the characters of exact block support `S`, then `g_S = 0`. -/
theorem sectorProj_eq_zero_of_blockCoeff (g : (∀ j, ResidueSpace (n j)) → ℝ) (l : K → Bool)
    (h : ∀ a : ∀ j, ResidueSpace (n j), (∀ j, (a j ≠ 0) = (l j = true)) →
      blockCoeff n g a = 0) :
    sectorProj (fun j => ResidueSpace (n j)) l *ᵥ g = 0 := by
  funext z
  have hc : ((sectorProj (fun j => ResidueSpace (n j)) l *ᵥ g) z : ℂ) = 0 := by
    simp only [Matrix.mulVec, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul]
    simp only [block_fourier_inversion n g, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro a _
    have hs := sectorProj_blockChar n l a z
    calc ∑ y, (sectorProj (fun j => ResidueSpace (n j)) l z y : ℂ) *
          (blockCoeff n g a * blockChar n a y)
        = blockCoeff n g a *
            ∑ y, (sectorProj (fun j => ResidueSpace (n j)) l z y : ℂ) * blockChar n a y := by
          rw [Finset.mul_sum]
          apply sum_congr rfl
          intro y _
          ring
      _ = 0 := by
          rw [hs]
          by_cases ha : ∀ j, (a j ≠ 0) = (l j = true)
          · rw [h a ha, zero_mul]
          · rw [ite_eq_right ha, mul_zero]
  exact_mod_cast hc

omit [∀ j, DecidableEq (I j)] [∀ j, ∀ i, NeZero (n j i)] in
/-- **The conductor of a character of exact block support `S`.** If every prefix modulus
divides `C'` and every modulus of a tail block `j ∈ T` divides `q_j`, a frequency `a` whose
nonzero blocks form `S` has order `ord(a) ≤ C' q_{S ∩ T}`, since `(C' q_{S ∩ T}) a = 0`. -/
theorem addOrderOf_le_of_blockSupport (T : Finset K) (q : K → ℕ) (hq : ∀ j ∈ T, 0 < q j)
    {C' : ℕ} (hC' : 0 < C') (hpre : ∀ j ∉ T, ∀ i, n j i ∣ C')
    (htail : ∀ j ∈ T, ∀ i, n j i ∣ q j) (l : K → Bool) (a : ∀ j, ResidueSpace (n j))
    (ha : ∀ j, (a j ≠ 0) = (l j = true)) :
    (addOrderOf a : ℝ) ≤ (C' : ℝ) * supportConductor (fun j => if j ∈ T then q j else 1) l := by
  set Q : ℕ := ∏ j, (if j ∈ T then (if l j then q j else 1) else 1) with hQ
  have hQpos : 0 < Q := Finset.prod_pos (fun j _ => by
    split_ifs with hT
    · exact hq j hT
    · exact one_pos
    · exact one_pos)
  have hzmod {N p : ℕ} (hdvd : p ∣ N) (x : ZMod p) : N • x = 0 := by
    obtain ⟨r, rfl⟩ := hdvd
    rw [nsmul_eq_mul, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_mul]
  have hkill : (C' * Q) • a = 0 := by
    funext j i
    simp only [Pi.smul_apply, Pi.zero_apply]
    by_cases hT : j ∈ T
    · by_cases hlj : l j = true
      · apply hzmod
        have h1 : q j ∣ Q := by
          rw [hQ]
          have := Finset.dvd_prod_of_mem
            (fun k => if k ∈ T then (if l k then q k else 1) else 1) (mem_univ j)
          simpa only [hT, hlj, ite_true] using this
        exact ((htail j hT i).trans h1).mul_left C'
      · have hz : a j = 0 := by
          by_contra hne
          exact hlj (Eq.mp (ha j) hne)
        rw [hz, Pi.zero_apply, smul_zero]
    · exact hzmod ((hpre j hT i).mul_right Q) _
  have hle : addOrderOf a ≤ C' * Q :=
    Nat.le_of_dvd (Nat.mul_pos hC' hQpos) (addOrderOf_dvd_of_nsmul_eq_zero hkill)
  have hqc : supportConductor (fun j => if j ∈ T then q j else 1) l = (Q : ℝ) := by
    unfold supportConductor
    rw [hQ, Nat.cast_prod]
    apply prod_congr rfl
    intro j _
    by_cases hT : j ∈ T <;> by_cases hlj : l j <;> simp [hT, hlj]
  rw [hqc]
  exact_mod_cast hle

/-- **The Fourier-to-sector bridge of `lem:record:prefix-conductor`, block form.** If
`ĝ(a) = 0` whenever `ord(a) ≤ H`, then every nonzero exact-support component `g_S` has
`H < C' q_{S ∩ T}`. -/
theorem support_of_blockCoeff (T : Finset K) (q : K → ℕ) (hq : ∀ j ∈ T, 0 < q j) {C' : ℕ}
    (hC' : 0 < C') (hpre : ∀ j ∉ T, ∀ i, n j i ∣ C') (htail : ∀ j ∈ T, ∀ i, n j i ∣ q j)
    {H : ℝ} (g : (∀ j, ResidueSpace (n j)) → ℝ)
    (hF : ∀ a : ∀ j, ResidueSpace (n j), (addOrderOf a : ℝ) ≤ H → blockCoeff n g a = 0)
    (l : K → Bool) (hl : sectorProj (fun j => ResidueSpace (n j)) l *ᵥ g ≠ 0) :
    H < (C' : ℝ) * supportConductor (fun j => if j ∈ T then q j else 1) l := by
  by_contra hcon
  push Not at hcon
  apply hl
  apply sectorProj_eq_zero_of_blockCoeff n g l
  intro a ha
  apply hF a
  exact (addOrderOf_le_of_blockSupport n T q hq hC' hpre htail l a ha).trans hcon

/-- **`lem:record:prefix-conductor`** (block form, the paper's hypotheses). Labels lie in
`∏_j X_j`, `X_j = ResidueSpace (n j)`; the blocks outside `T` form the prefix (any laws, for
instance one block `X'` with an arbitrary law `ρ'`), those of `T` the tail. Each `ρ_j` has
uniform one-slot marginals; for `j ∈ T`, `ρ_j` is `(γ, v)`-mixing with the parameter `q_j`
(`IsGammaMixing (q j) γ (ρ j) {v}`, `def:mixing`) and the moduli of block `j` divide `q_j`; no
mixing is assumed on the prefix. If every prefix modulus divides `C' > 0` and `ĝ_v(ξ) = 0`
whenever `q(ξ) = ord(ξ) ≤ H`, then
`|∫ ∏_w g_w(z_w) dρ| ≤ (C'/H)^γ ‖g_v‖₂ ∏_{w≠v} ‖g_w‖_{2(d-1)}`, `d = |V| ≥ 2`, with norms
for the uniform probability measure. -/
theorem prefix_conductor_blocks {V : Type*} [Fintype V] [DecidableEq V]
    (ρ : ∀ j, FiniteLaw (V → ResidueSpace (n j))) (v : V) (hV : 2 ≤ Fintype.card V)
    (hunif : ∀ j w, UniformSlot (ρ j) w) (T : Finset K) (q : K → ℕ) (hq : ∀ j ∈ T, 0 < q j)
    {γ : ℝ} (hγ : 0 ≤ γ) (hmix : ∀ j ∈ T, IsGammaMixing (q j) γ (ρ j) {v})
    {C' : ℕ} (hC' : 0 < C') (hpre : ∀ j ∉ T, ∀ i, n j i ∣ C')
    (htail : ∀ j ∈ T, ∀ i, n j i ∣ q j)
    {H : ℝ} (hH : 0 < H) (g : V → (∀ j, ResidueSpace (n j)) → ℝ)
    (hF : ∀ a : ∀ j, ResidueSpace (n j), (addOrderOf a : ℝ) ≤ H → blockCoeff n (g v) a = 0) :
    |prodIntegral ρ g| ≤ ((C' : ℝ) / H) ^ γ *
      (FiniteLaw.uniform (∀ j, ResidueSpace (n j))).lpNorm 2 (g v) *
      ∏ w : {w // w ≠ v}, (FiniteLaw.uniform (∀ j, ResidueSpace (n j))).lpNorm
        (2 * (Fintype.card V - 1)) (g w) := by
  have hq' : ∀ j, 0 < (fun j => if j ∈ T then q j else 1) j := by
    intro j
    by_cases hj : j ∈ T
    · simp only [hj, ite_true]
      exact hq j hj
    · simp only [hj, ite_false]
      exact one_pos
  have hmix' : ∀ j, ContractsMeanZero (slotJoint (ρ j) v)
      (((fun j => if j ∈ T then q j else 1) j : ℕ) ^ (-γ) : ℝ) := by
    intro j
    by_cases hj : j ∈ T
    · simp only [hj, ite_true]
      exact (isMixing_singleton_iff (ρ j) v ((q j : ℝ) ^ (-γ))).mp (hmix j hj)
    · simp only [hj, ite_false, Nat.cast_one, Real.one_rpow]
      exact contractsMeanZero_one _
  exact prefix_conductor ρ v hV hunif (fun j => if j ∈ T then q j else 1) hq' hγ hmix'
    (by exact_mod_cast hC') hH g (support_of_blockCoeff n T q hq hC' hpre htail (g v) hF)

end Sarkozy.Mixing
