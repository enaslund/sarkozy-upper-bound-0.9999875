module

public import Sarkozy.Mixing.Singleton
public import Sarkozy.FourierArithmetic.ResidueMoments

/-!
# The Fourier form of the conductor hypothesis

`lem:record:prefix-conductor` assumes `ĝ_v(ξ) = 0` whenever the conductor `q(ξ) ≤ H`. This
file derives the sector form used by `Sarkozy.Mixing.prefix_conductor`, for label groups that
are finite products of cyclic groups `X = ∏_j ℤ/m_jℤ` (`ResidueSpace m`; the prefix group `X'`
contributes its cyclic factors, the tail primes contribute `𝔽_p`).

* `fourier_inversion`: `g = ∑_a ĝ(a) χ_a` for the characters `χ_a = prodChar m a`.
* `sectorProj_char`: the exact-support projection `P_S` keeps `χ_a` if the support of `a` is
  `S` and kills it otherwise; hence `sectorProj_eq_zero_of_fourier`: if `ĝ` vanishes on the
  characters of support `S`, then `g_S = 0`.
* `support_of_fourier` (the bridge of `lem:record:prefix-conductor`): if the tail moduli are
  prime, `C'` is divisible by the conductor of every character of the prefix part, and `ĝ`
  vanishes at every character of conductor at most `H`, then every nonzero exact-support
  component `g_S` has `H < C' q_S`.
* `prefix_conductor_fourier`: `lem:record:prefix-conductor` with the paper's Fourier
  hypothesis.

The characters and their orthogonality are those of `Sarkozy.FourierArithmetic`
(`ResidueMoments.lean`, adapted from OpenAI's `RationalLift.lean`; see NOTICES.md). The
conductor `charConductor m a = ∏_j addOrderOf (a j)` is the definition of
`Sarkozy.Functional.conductor` (not imported here).
-/

@[expose] public section

open Finset Complex
open scoped BigOperators Matrix ComplexConjugate

namespace Sarkozy.Mixing

open Sarkozy.IndexSupport Sarkozy.FourierArithmetic

variable {K : Type*} [Fintype K] [DecidableEq K] (m : K → ℕ) [∀ j, NeZero (m j)]

/-- The Fourier coefficient `ĝ(a) = E_z g(z) conj(χ_a(z))`. -/
noncomputable def fourierCoeff (g : ResidueSpace m → ℝ) (a : ResidueSpace m) : ℂ :=
  𝔼 z, (g z : ℂ) * conj (prodChar m a z)

/-- The conductor `q(ξ) = ∏_j addOrderOf (a j)` of the character `χ_a`. -/
noncomputable def charConductor (a : ResidueSpace m) : ℕ := ∏ j, addOrderOf (a j)

/-- Dual orthogonality: `∑_a χ_a(z) conj(χ_a(y)) = |X| [z = y]`. -/
theorem sum_prodChar_mul_conj (z y : ResidueSpace m) :
    ∑ a, prodChar m a z * conj (prodChar m a y) =
      if z = y then (Fintype.card (ResidueSpace m) : ℂ) else 0 := by
  have h := prodChar_orthogonal m z y
  rw [expect_eq_sum_div_card] at h
  have hc : (Fintype.card (ResidueSpace m) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have h' : ∑ a, prodChar m z a * conj (prodChar m y a) =
      (if z = y then 1 else 0) * (Fintype.card (ResidueSpace m) : ℂ) := by
    rw [← h, card_univ]
    field_simp
  simp only [prodChar_symm m _ z, prodChar_symm m _ y]
  rw [h']
  split_ifs <;> simp

/-- Fourier inversion `g(z) = ∑_a ĝ(a) χ_a(z)`. -/
theorem fourier_inversion (g : ResidueSpace m → ℝ) (z : ResidueSpace m) :
    (g z : ℂ) = ∑ a, fourierCoeff m g a * prodChar m a z := by
  have hc : (Fintype.card (ResidueSpace m) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [fourierCoeff, expect_eq_sum_div_card, card_univ, Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hy (y : ResidueSpace m) : ∑ a, (g y : ℂ) * conj (prodChar m a y) /
      (Fintype.card (ResidueSpace m) : ℂ) * prodChar m a z =
      (g y : ℂ) / (Fintype.card (ResidueSpace m) : ℂ) *
        ∑ a, prodChar m a z * conj (prodChar m a y) := by
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro a _
    ring
  simp only [hy, sum_prodChar_mul_conj, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [mem_univ, ite_true]
  field_simp

omit [Fintype K] [DecidableEq K] in
/-- The coordinate projections on a one-dimensional character. -/
theorem coordProj_char (j : K) (s : Bool) (a x : ZMod (m j)) :
    ∑ y, (coordProj (ZMod (m j)) s x y : ℂ) * ZMod.stdAddChar (a * y) =
      if (a ≠ 0) = (s = true) then ZMod.stdAddChar (a * x) else 0 := by
  have hmean : ∑ y : ZMod (m j), ((meanMatrix (ZMod (m j)) x y : ℝ) : ℂ) * ZMod.stdAddChar (a * y) =
      if a = 0 then 1 else 0 := by
    have h := prime_char_expect m j a
    rw [expect_eq_sum_div_card] at h
    rw [← h]
    simp only [meanMatrix_apply, Complex.ofReal_inv, Complex.ofReal_natCast, card_univ]
    rw [div_eq_inv_mul, Finset.mul_sum]
  cases s
  · simp only [coordProj, Bool.false_eq_true, ite_false, hmean]
    by_cases ha : a = 0
    · simp [ha]
    · simp [ha]
  · simp only [coordProj, ite_true, Matrix.sub_apply, Complex.ofReal_sub, sub_mul,
      Finset.sum_sub_distrib, hmean, Matrix.one_apply]
    simp only [apply_ite (fun r : ℝ => (r : ℂ)), Complex.ofReal_one, Complex.ofReal_zero,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, mem_univ, ite_true]
    by_cases ha : a = 0
    · simp [ha]
    · simp [ha]

/-- `P_S χ_a = [supp a = S] χ_a`. -/
theorem sectorProj_char (l : K → Bool) (a z : ResidueSpace m) :
    ∑ y, (sectorProj (fun j => ZMod (m j)) l z y : ℂ) * prodChar m a y =
      if (∀ j, (a j ≠ 0) = (l j = true)) then prodChar m a z else 0 := by
  simp only [sectorProj, piKron_apply, Complex.ofReal_prod, prodChar, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun j y => (coordProj (ZMod (m j)) (l j) (z j) y : ℂ) *
    ZMod.stdAddChar (a j * y))]
  simp only [coordProj_char]
  by_cases h : ∀ j, (a j ≠ 0) = (l j = true)
  · rw [ite_eq_left h]
    exact prod_congr rfl (fun j _ => by rw [ite_eq_left (h j)])
  · rw [ite_eq_right h]
    obtain ⟨j, hj⟩ := not_forall.mp h
    exact prod_eq_zero (mem_univ j) (by rw [ite_eq_right hj])

/-- If `ĝ` vanishes on the characters of exact support `S`, the component `g_S` vanishes. -/
theorem sectorProj_eq_zero_of_fourier (g : ResidueSpace m → ℝ) (l : K → Bool)
    (h : ∀ a : ResidueSpace m, (∀ j, (a j ≠ 0) = (l j = true)) → fourierCoeff m g a = 0) :
    sectorProj (fun j => ZMod (m j)) l *ᵥ g = 0 := by
  funext z
  have hc : ((sectorProj (fun j => ZMod (m j)) l *ᵥ g) z : ℂ) = 0 := by
    simp only [Matrix.mulVec, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul]
    simp only [fourier_inversion m g, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro a _
    have hs := sectorProj_char m l a z
    calc ∑ y, (sectorProj (fun j => ZMod (m j)) l z y : ℂ) * (fourierCoeff m g a * prodChar m a y)
        = fourierCoeff m g a *
            ∑ y, (sectorProj (fun j => ZMod (m j)) l z y : ℂ) * prodChar m a y := by
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

/-- **The Fourier-to-sector bridge of `lem:record:prefix-conductor`.** Let the coordinates of
`T` (tail) have prime moduli, let `C' > 0` be divisible by the conductor of every character of
the prefix coordinates (those outside `T`), and let `ĝ(a) = 0` whenever `q(a) ≤ H`. Then every
nonzero exact-support component `g_S` has `H < C' q_S`, where `q_j = m_j` on `T` and `1` off
`T`. -/
theorem support_of_fourier (T : Finset K) (hprime : ∀ j ∈ T, (m j).Prime) {C' : ℕ}
    (hC' : 0 < C') (hdiv : ∀ a : ResidueSpace m, (∏ j ∈ univ.filter (· ∉ T), addOrderOf (a j)) ∣ C')
    {H : ℝ} (g : ResidueSpace m → ℝ)
    (hF : ∀ a, (charConductor m a : ℝ) ≤ H → fourierCoeff m g a = 0) (l : K → Bool)
    (hl : sectorProj (fun j => ZMod (m j)) l *ᵥ g ≠ 0) :
    H < (C' : ℝ) * supportConductor (fun j => if j ∈ T then m j else 1) l := by
  by_contra hcon
  push Not at hcon
  apply hl
  apply sectorProj_eq_zero_of_fourier m g l
  intro a ha
  apply hF a
  -- the conductor of a character of support `l`
  have hcond : (charConductor m a : ℝ) ≤
      (C' : ℝ) * supportConductor (fun j => if j ∈ T then m j else 1) l := by
    have hsplit : charConductor m a =
        (∏ j ∈ univ.filter (· ∉ T), addOrderOf (a j)) *
          ∏ j ∈ univ.filter (· ∈ T), addOrderOf (a j) := by
      unfold charConductor
      rw [mul_comm, Finset.prod_filter_mul_prod_filter_not]
    have htail : ∏ j ∈ univ.filter (· ∈ T), addOrderOf (a j) =
        ∏ j, (if j ∈ T then (if l j then m j else 1) else 1) := by
      rw [Finset.prod_filter]
      apply prod_congr rfl
      intro j _
      split_ifs with hT hlj
      · have : Fact (m j).Prime := ⟨hprime j hT⟩
        have hne : a j ≠ 0 := by
          have := ha j
          rw [hlj] at this
          simpa using this
        apply addOrderOf_eq_prime _ hne
        have h1 := card_nsmul_eq_zero (x := a j)
        rwa [ZMod.card] at h1
      · have hz : a j = 0 := by
          have := ha j
          simp only [hlj, Bool.false_eq_true, eq_iff_iff, iff_false, not_not] at this
          exact this
        rw [hz, addOrderOf_zero]
      · rfl
    have hq : supportConductor (fun j => if j ∈ T then m j else 1) l =
        ((∏ j, (if j ∈ T then (if l j then m j else 1) else 1) : ℕ) : ℝ) := by
      unfold supportConductor
      rw [Nat.cast_prod]
      apply prod_congr rfl
      intro j _
      by_cases hT : j ∈ T <;> by_cases hlj : l j <;> simp [hT, hlj]
    have hpre : ((∏ j ∈ univ.filter (· ∉ T), addOrderOf (a j) : ℕ) : ℝ) ≤ (C' : ℝ) := by
      exact_mod_cast Nat.le_of_dvd hC' (hdiv a)
    rw [hsplit, htail, Nat.cast_mul, hq]
    exact mul_le_mul_of_nonneg_right hpre (Nat.cast_nonneg _)
  linarith

/-- **Conductor decay with a finite prefix** (`lem:record:prefix-conductor`), with the paper's
Fourier hypothesis. Labels lie in `X = ∏_j ℤ/m_jℤ`, the coordinates outside `T` forming the
prefix `X'` and those of `T` the tail fields `𝔽_p` (`m_j` prime). Each `ρ_j` has uniform
one-slot marginals; for `j ∈ T` it is `(γ, v)`-mixing (no mixing is assumed on the prefix);
`C' > 0` is divisible by the conductor of every character of `X'`; and `ĝ_v(ξ) = 0` whenever
`q(ξ) ≤ H`. Then
`|∫ ∏_w g_w(z_w) dρ| ≤ (C'/H)^γ ‖g_v‖₂ ∏_{w≠v} ‖g_w‖_{2(d-1)}`, `d = |V| ≥ 2`. -/
theorem prefix_conductor_fourier {V : Type*} [Fintype V] [DecidableEq V]
    (ρ : ∀ j, FiniteLaw (V → ZMod (m j))) (v : V) (hV : 2 ≤ Fintype.card V)
    (hunif : ∀ j w, UniformSlot (ρ j) w) (T : Finset K) (hprime : ∀ j ∈ T, (m j).Prime)
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hmix : ∀ j ∈ T, ContractsMeanZero (slotJoint (ρ j) v) ((m j : ℝ) ^ (-γ)))
    {C' : ℕ} (hC' : 0 < C')
    (hdiv : ∀ a : ResidueSpace m, (∏ j ∈ univ.filter (· ∉ T), addOrderOf (a j)) ∣ C')
    {H : ℝ} (hH : 0 < H) (g : V → ResidueSpace m → ℝ)
    (hF : ∀ a, (charConductor m a : ℝ) ≤ H → fourierCoeff m (g v) a = 0) :
    |prodIntegral ρ g| ≤ ((C' : ℝ) / H) ^ γ *
      (FiniteLaw.uniform (ResidueSpace m)).lpNorm 2 (g v) *
      ∏ w : {w // w ≠ v},
        (FiniteLaw.uniform (ResidueSpace m)).lpNorm (2 * (Fintype.card V - 1)) (g w) := by
  have hq : ∀ j, 0 < (fun j => if j ∈ T then m j else 1) j := by
    intro j
    by_cases hj : j ∈ T
    · simp only [hj, ite_true]
      exact Nat.pos_of_ne_zero (NeZero.ne (m j))
    · simp only [hj, ite_false]
      exact one_pos
  have hmix' : ∀ j, ContractsMeanZero (slotJoint (ρ j) v)
      (((fun j => if j ∈ T then m j else 1) j : ℕ) ^ (-γ) : ℝ) := by
    intro j
    by_cases hj : j ∈ T
    · simp only [hj, ite_true]
      exact hmix j hj
    · simp only [hj, ite_false, Nat.cast_one, Real.one_rpow]
      exact contractsMeanZero_one _
  exact prefix_conductor ρ v hV hunif (fun j => if j ∈ T then m j else 1) hq hγ hmix'
    (by exact_mod_cast hC') hH g (support_of_fourier m T hprime hC' hdiv (g v) hF)

end Sarkozy.Mixing
