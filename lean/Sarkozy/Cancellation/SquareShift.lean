module

public import Sarkozy.Functional.FibreScale
public import Sarkozy.Kernel.SievedFourier

@[expose] public section

/-!
# The strict-square pair law and its multiplier (`lem:square-shift`(d))

`paper/sections/04_notation.tex`, `lem:square-shift`(d). For a finite family of odd primes
`p_j`, `X = ∏_j 𝔽_{p_j}` with the uniform probability and `π` the uniform probability on
`∏_j Ω_{p_j}`, `Ω_p = {(x, y) : y − x a nonzero square mod p}` (the strict-square pair law),
`∫ g₁(x) g₂(y) dπ(x, y) = ∑_ξ ĝ₁(−ξ) ĝ₂(ξ) λ(ξ)`,
the sum running over the characters `ξ` of `X`, with the multiplier
`λ(ξ) = ∏_j λ_{p_j}(a_j)`, `λ_p(c) = E_{u ∈ Q_p} e(c u/p)` the eigenvalues of the square shift
(`lem:square-shift`(a)). The coefficients are those of `def:record:functional`(b)
(`Sarkozy.Functional.groupCoeff`, `ĝ(ξ) = E_z g(z) e(−z ξ)`).

* `pairAvg_fourier`: the expansion;
* `shiftEigen_zero`, `shiftEigen_eq_gauss`: `λ_p(0) = 1` and `λ_p(c) = (G_p(c) − 1)/(p − 1)`
  for `c ≠ 0`, `G_p(c) = ∑_v e(c v²/p)`;
* `norm_shiftEigen_le`: `|λ_p(c)| ≤ (√p + 1)/(p − 1)`, and `≤ p^{-1/3}` for `p ≥ 64`;
* `norm_pairMultiplier_le`: `|λ(ξ)| ≤ q(ξ)^{-1/3}` when every prime is at least `64`.

New material for this paper; the Gauss-sum bound is upstream `HasFourierBound.gauss`
(OpenAI, `SievedFourier.lean`, ported in `Sarkozy.Kernel`).
-/

namespace Sarkozy.Cancellation

/- Mathlib's instance "a simple nilpotent additive group is commutative" makes `ZMod q` with
`[Fact q.Prime]` pick an `AddCommGroup` structure for `-` that is not reducibly the ring's, so
`ring` and the ring lemmas fail on negations. It is switched off in this file. -/
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Finset Complex
open scoped BigOperators ComplexConjugate
open Sarkozy.FourierArithmetic Sarkozy.Functional

section PairLaw

variable {K : Type*} [Fintype K] [DecidableEq K] (p : K → ℕ) [∀ j, NeZero (p j)]

/-- The nonzero squares `Q_p` of `ZMod p`. -/
def sqSet (j : K) : Finset (ZMod (p j)) := univ.filter (fun u => u ≠ 0 ∧ IsSquare u)

/-- The support `∏_j Ω_{p_j}` of the strict-square pair law. -/
def pairSet : Finset (ResidueSpace p × ResidueSpace p) :=
  univ.filter (fun xy => ∀ j, xy.2 j - xy.1 j ∈ sqSet p j)

/-- The strict-square pair average `∫ g₁(x) g₂(y) dπ(x, y)`, `π` uniform on `∏_j Ω_{p_j}`. -/
noncomputable def pairAvg (g₁ g₂ : ResidueSpace p → ℂ) : ℂ :=
  ((pairSet p).card : ℂ)⁻¹ * ∑ xy ∈ pairSet p, g₁ xy.1 * g₂ xy.2

/-- The eigenvalue `λ_p(c) = E_{u ∈ Q_p} e(c u/p)` of the square shift (`lem:square-shift`(a)). -/
noncomputable def shiftEigen (j : K) (c : ZMod (p j)) : ℂ :=
  ((sqSet p j).card : ℂ)⁻¹ * ∑ u ∈ sqSet p j, (ZMod.stdAddChar (c * u) : ℂ)

/-- The multiplier `λ(ξ) = ∏_j λ_{p_j}(a_j)` of the strict-square pair law. -/
noncomputable def pairMultiplier (a : ResidueSpace p) : ℂ := ∏ j, shiftEigen p j (a j)

/-- The shift parametrization `(x, u) ↦ (x, x + u)` of `∏_j Ω_{p_j}`. -/
lemma sum_pairSet (F : ResidueSpace p × ResidueSpace p → ℂ) :
    ∑ xy ∈ pairSet p, F xy = ∑ x : ResidueSpace p, ∑ u ∈ Fintype.piFinset (sqSet p), F (x, x + u) := by
  rw [← Finset.sum_product']
  symm
  apply Finset.sum_nbij' (fun xu => (xu.1, xu.1 + xu.2)) (fun xy => (xy.1, xy.2 - xy.1))
  · intro xu hxu
    rw [mem_product, Fintype.mem_piFinset] at hxu
    rw [pairSet, mem_filter]
    refine ⟨mem_univ _, fun j => ?_⟩
    simp only [Pi.add_apply, add_sub_cancel_left]
    exact hxu.2 j
  · intro xy hxy
    rw [pairSet, mem_filter] at hxy
    rw [mem_product, Fintype.mem_piFinset]
    exact ⟨mem_univ _, fun j => hxy.2 j⟩
  · intro xu _
    simp
  · intro xy _
    simp
  · intro xu _
    rfl

lemma card_pairSet :
    (pairSet p).card = Fintype.card (ResidueSpace p) * ∏ j, (sqSet p j).card := by
  have h := sum_pairSet p (fun _ => (1 : ℂ))
  simp only [sum_const, nsmul_eq_mul, mul_one, Fintype.card_piFinset, card_univ] at h
  exact_mod_cast h

/-- The character sum over the shifts: `∑_{u ∈ ∏ Q_j} χ_a(u) = ∏_j ∑_{u ∈ Q_j} e(a_j u)`. -/
lemma sum_piFinset_prodChar (a : ResidueSpace p) :
    ∑ u ∈ Fintype.piFinset (sqSet p), prodChar p a u =
      ∏ j, ∑ u ∈ sqSet p j, (ZMod.stdAddChar (a j * u) : ℂ) := by
  unfold prodChar
  rw [Finset.prod_univ_sum]

lemma sum_prodChar_univ (a : ResidueSpace p) :
    ∑ x : ResidueSpace p, prodChar p a x =
      if a = 0 then (Fintype.card (ResidueSpace p) : ℂ) else 0 := by
  have h := prodChar_expect p a
  rw [expect_eq_sum_div_card] at h
  have hc : (Fintype.card (ResidueSpace p) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [card_univ] at h
  have h' := (div_eq_iff hc).mp h
  rw [h']
  split_ifs <;> simp

lemma groupCoeff_expansion (g : ResidueSpace p → ℂ) (z : ResidueSpace p) :
    g z = ∑ a, groupCoeff p g a * prodChar p a z := by
  have h := fourierPolynomial_reconstruction p g z
  unfold fourierPolynomial at h
  rw [← h]
  rfl

omit [Fintype K] [DecidableEq K] in
lemma one_mem_sqSet [∀ j, Fact (p j).Prime] (j : K) : (1 : ZMod (p j)) ∈ sqSet p j := by
  rw [sqSet, mem_filter]
  exact ⟨mem_univ _, one_ne_zero, ⟨1, by ring⟩⟩

omit [Fintype K] [DecidableEq K] in
lemma card_sqSet_pos [∀ j, Fact (p j).Prime] (j : K) : 0 < (sqSet p j).card :=
  card_pos.mpr ⟨1, one_mem_sqSet p j⟩

/-- **`lem:square-shift`(d)**: the strict-square pair law in characters,
`∫ g₁(x) g₂(y) dπ = ∑_ξ ĝ₁(−ξ) ĝ₂(ξ) λ(ξ)`. -/
theorem pairAvg_fourier [∀ j, Fact (p j).Prime] (g₁ g₂ : ResidueSpace p → ℂ) :
    pairAvg p g₁ g₂ = ∑ a, groupCoeff p g₁ (-a) * groupCoeff p g₂ a * pairMultiplier p a := by
  classical
  set c₁ := groupCoeff p g₁ with hc₁
  set c₂ := groupCoeff p g₂ with hc₂
  set X := Fintype.card (ResidueSpace p) with hX
  have hX0 : (X : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hQ0 : ∀ j, ((sqSet p j).card : ℂ) ≠ 0 := fun j => by
    exact_mod_cast (card_sqSet_pos p j).ne'
  -- expand both functions in characters
  have hterm : ∀ x u : ResidueSpace p, g₁ x * g₂ (x + u) =
      ∑ b, ∑ a, c₁ b * c₂ a * (prodChar p (b + a) x * prodChar p a u) := by
    intro x u
    rw [groupCoeff_expansion p g₁ x, groupCoeff_expansion p g₂ (x + u), sum_mul]
    apply sum_congr rfl
    intro b _
    rw [mul_sum]
    apply sum_congr rfl
    intro a _
    rw [prodChar_add_right, prodChar_add]
    ring
  unfold pairAvg
  rw [sum_pairSet]
  simp_rw [hterm]
  -- exchange the sums
  have hswap : ∑ x : ResidueSpace p, ∑ u ∈ Fintype.piFinset (sqSet p),
      ∑ b, ∑ a, c₁ b * c₂ a * (prodChar p (b + a) x * prodChar p a u) =
      ∑ b, ∑ a, c₁ b * c₂ a * ((∑ x : ResidueSpace p, prodChar p (b + a) x) *
        ∑ u ∈ Fintype.piFinset (sqSet p), prodChar p a u) := by
    calc ∑ x : ResidueSpace p, ∑ u ∈ Fintype.piFinset (sqSet p),
          ∑ b, ∑ a, c₁ b * c₂ a * (prodChar p (b + a) x * prodChar p a u)
        = ∑ x : ResidueSpace p, ∑ b, ∑ u ∈ Fintype.piFinset (sqSet p),
          ∑ a, c₁ b * c₂ a * (prodChar p (b + a) x * prodChar p a u) := by
          apply sum_congr rfl; intro x _; rw [Finset.sum_comm]
      _ = ∑ x : ResidueSpace p, ∑ b, ∑ a, ∑ u ∈ Fintype.piFinset (sqSet p),
          c₁ b * c₂ a * (prodChar p (b + a) x * prodChar p a u) := by
          apply sum_congr rfl; intro x _; apply sum_congr rfl; intro b _; rw [Finset.sum_comm]
      _ = ∑ b, ∑ x : ResidueSpace p, ∑ a, ∑ u ∈ Fintype.piFinset (sqSet p),
          c₁ b * c₂ a * (prodChar p (b + a) x * prodChar p a u) := Finset.sum_comm
      _ = ∑ b, ∑ a, ∑ x : ResidueSpace p, ∑ u ∈ Fintype.piFinset (sqSet p),
          c₁ b * c₂ a * (prodChar p (b + a) x * prodChar p a u) := by
          apply sum_congr rfl; intro b _; rw [Finset.sum_comm]
      _ = _ := by
          apply sum_congr rfl; intro b _
          apply sum_congr rfl; intro a _
          rw [sum_mul_sum, mul_sum]
          apply sum_congr rfl; intro x _
          rw [mul_sum]
  rw [hswap]
  simp_rw [sum_prodChar_univ, sum_piFinset_prodChar]
  -- only `b = -a` survives
  have hcollapse : ∑ b, ∑ a, c₁ b * c₂ a * ((if b + a = 0 then (X : ℂ) else 0) *
      ∏ j, ∑ u ∈ sqSet p j, (ZMod.stdAddChar (a j * u) : ℂ)) =
      ∑ a, c₁ (-a) * c₂ a * ((X : ℂ) * ∏ j, ∑ u ∈ sqSet p j, (ZMod.stdAddChar (a j * u) : ℂ)) := by
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro a _
    rw [Finset.sum_eq_single (-a)]
    · split_ifs with h
      · rfl
      · exact absurd (neg_add_cancel a) h
    · intro b _ hb
      split_ifs with h
      · exact absurd (eq_neg_of_add_eq_zero_left h) hb
      · ring
    · intro h; exact absurd (mem_univ _) h
  rw [hcollapse, card_pairSet, mul_sum]
  apply sum_congr rfl
  intro a _
  unfold pairMultiplier shiftEigen
  rw [prod_mul_distrib, prod_inv_distrib]
  have hP : (∏ j, ((sqSet p j).card : ℂ)) ≠ 0 := prod_ne_zero_iff.mpr (fun j _ => hQ0 j)
  rw [← hX]
  push_cast
  field_simp

end PairLaw

/-! ## The eigenvalues of the square shift -/

section Eigen

variable {q : ℕ} [Fact q.Prime]

/-- The nonzero squares of `ZMod q`. -/
def sqSetZ (q : ℕ) [Fact q.Prime] : Finset (ZMod q) := univ.filter (fun u => u ≠ 0 ∧ IsSquare u)

/-- Every nonzero square has exactly two square roots (`q` odd). -/
lemma card_sqrt_fiber (hq2 : q ≠ 2) (u : ZMod q) (hu : u ∈ sqSetZ q) :
    ((univ.erase (0 : ZMod q)).filter (fun v => v ^ 2 = u)).card = 2 := by
  rw [sqSetZ, mem_filter] at hu
  obtain ⟨_, hu0, ⟨w, hw⟩⟩ := hu
  have hw0 : w ≠ 0 := by rintro rfl; apply hu0; rw [hw]; ring
  have hchar : ringChar (ZMod q) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; exact hq2
  have hww : w ≠ -w := by
    intro h
    have h2 : (2 : ZMod q) * w = 0 := by
      rw [two_mul]; nth_rewrite 2 [h]; exact add_neg_cancel w
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact (Ring.two_ne_zero hchar) h3
    · exact hw0 h3
  have hfib : (univ.erase (0 : ZMod q)).filter (fun v => v ^ 2 = u) = {w, -w} := by
    ext v
    simp only [mem_filter, mem_erase, mem_univ, and_true, mem_insert, mem_singleton]
    constructor
    · rintro ⟨_, hv⟩
      have : (v - w) * (v + w) = 0 := by rw [hw] at hv; linear_combination hv
      rcases mul_eq_zero.mp this with h | h
      · left; exact sub_eq_zero.mp h
      · right; exact eq_neg_of_add_eq_zero_left h
    · rintro (rfl | rfl)
      · exact ⟨hw0, by rw [hw, sq]⟩
      · exact ⟨neg_ne_zero.mpr hw0, by rw [hw, neg_sq, sq]⟩
  rw [hfib, card_insert_of_notMem (by simpa using hww), card_singleton]

/-- `∑_{v} f(v²) = f(0) + 2 ∑_{u ∈ Q} f(u)` (`q` odd). -/
lemma sum_sq_eq (hq2 : q ≠ 2) (f : ZMod q → ℂ) :
    ∑ v : ZMod q, f (v ^ 2) = f 0 + 2 * ∑ u ∈ sqSetZ q, f u := by
  classical
  rw [← add_sum_erase _ _ (mem_univ (0 : ZMod q))]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  congr 1
  have hmaps : ∀ v ∈ univ.erase (0 : ZMod q), v ^ 2 ∈ sqSetZ q := by
    intro v hv
    rw [mem_erase] at hv
    rw [sqSetZ, mem_filter]
    exact ⟨mem_univ _, pow_ne_zero 2 hv.1, ⟨v, by ring⟩⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  rw [mul_sum]
  apply sum_congr rfl
  intro u hu
  have hc : ∀ v ∈ (univ.erase (0 : ZMod q)).filter (fun v => v ^ 2 = u), f (v ^ 2) = f u := by
    intro v hv
    rw [(mem_filter.mp hv).2]
  rw [sum_congr rfl hc, sum_const, card_sqrt_fiber hq2 u hu]
  simp

lemma card_sqSetZ (hq2 : q ≠ 2) : ((sqSetZ q).card : ℂ) = ((q : ℂ) - 1) / 2 := by
  have h := sum_sq_eq (q := q) hq2 (fun _ => (1 : ℂ))
  simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_one] at h
  linear_combination (-1 / 2 : ℂ) * h

/-- The quadratic Gauss sum `G_q(c) = ∑_v e(c v²/q)`. -/
noncomputable def quadGauss (c : ZMod q) : ℂ := ∑ v : ZMod q, (ZMod.stdAddChar (c * v ^ 2) : ℂ)

/-- `E_{u ∈ Q} e(cu/q) = (G_q(c) − 1)/(q − 1)` for `c ≠ 0`, and `= 1` for `c = 0`
(`lem:square-shift`(a)). -/
lemma sqAvg_eq (hq2 : q ≠ 2) (c : ZMod q) :
    ((sqSetZ q).card : ℂ)⁻¹ * ∑ u ∈ sqSetZ q, (ZMod.stdAddChar (c * u) : ℂ) =
      (quadGauss c - 1) / ((q : ℂ) - 1) := by
  have h := sum_sq_eq (q := q) hq2 (fun u => (ZMod.stdAddChar (c * u) : ℂ))
  simp only [mul_zero, AddChar.map_zero_eq_one] at h
  unfold quadGauss
  rw [h, card_sqSetZ hq2]
  have hq1 : ((q : ℂ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast (Fact.out : q.Prime).two_le
    intro h0
    have h1 : ((q : ℂ) - 1).re = 0 := by rw [h0]; simp
    simp at h1
    linarith
  field_simp
  ring

/-- `|G_q(c)| ≤ √q` for `c ≠ 0`, `q` odd (upstream `HasFourierBound.gauss`). -/
lemma norm_quadGauss_le (hq2 : q ≠ 2) (c : ZMod q) (hc : c ≠ 0) :
    ‖quadGauss c‖ ≤ Real.sqrt q := by
  have hchar : ringChar (ZMod q) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hq2
  have hunit : IsUnit (2 * c) := by
    apply IsUnit.mul
    · exact (Ring.two_ne_zero hchar).isUnit
    · exact hc.isUnit
  have h := Sarkozy.Kernel.HasFourierBound.gauss (Sarkozy.Kernel.hasFourierBound_one
    (ZMod.stdAddChar (N := q))) (ZMod.isPrimitive_stdAddChar q) c hunit
  simp only [one_mul, ZMod.card] at h
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have he : quadGauss c = (q : ℂ) * 𝔼 x : ZMod q, (ZMod.stdAddChar (c * x ^ 2) : ℂ) := by
    unfold quadGauss
    rw [expect_eq_sum_div_card, card_univ, ZMod.card]
    field_simp
  rw [he, norm_mul, Complex.norm_natCast]
  calc (q : ℝ) * ‖𝔼 x : ZMod q, (ZMod.stdAddChar (c * x ^ 2) : ℂ)‖ ≤ q * (q : ℝ) ^ (-(1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left h hq0.le
    _ = Real.sqrt q := by
        rw [Real.sqrt_eq_rpow, show -(1 : ℝ) / 2 = 1 / 2 - 1 by ring, Real.rpow_sub hq0,
          Real.rpow_one]
        field_simp

/-- `|λ_q(c)| ≤ (√q + 1)/(q − 1)` for `c ≠ 0` (`lem:square-shift`(a)). -/
lemma norm_sqAvg_le (hq2 : q ≠ 2) (c : ZMod q) (hc : c ≠ 0) :
    ‖((sqSetZ q).card : ℂ)⁻¹ * ∑ u ∈ sqSetZ q, (ZMod.stdAddChar (c * u) : ℂ)‖ ≤
      (Real.sqrt q + 1) / ((q : ℝ) - 1) := by
  rw [sqAvg_eq hq2 c]
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast (Fact.out : q.Prime).two_le
  have hden : ((q : ℂ) - 1) = (((q : ℝ) - 1 : ℝ) : ℂ) := by push_cast; ring
  rw [hden, norm_div, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  apply div_le_div_of_nonneg_right _ (by linarith)
  calc ‖quadGauss c - 1‖ ≤ ‖quadGauss c‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ ≤ Real.sqrt q + 1 := by rw [norm_one]; linarith [norm_quadGauss_le hq2 c hc]

/-- `(√q + 1)/(q − 1) ≤ q^{-1/3}` for `q ≥ 64`. -/
lemma sqrt_add_one_div_le (x : ℝ) (hx : 64 ≤ x) : (Real.sqrt x + 1) / (x - 1) ≤ x ^ (-(1 : ℝ) / 3) := by
  have hx0 : 0 < x := by linarith
  set s := x ^ ((1 : ℝ) / 6) with hs
  have hs2 : 2 ≤ s := by
    have h64 : (64 : ℝ) ^ ((1 : ℝ) / 6) = 2 := by
      rw [show (64 : ℝ) = 2 ^ (6 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [hs, ← h64]
    exact Real.rpow_le_rpow (by norm_num) hx (by norm_num)
  have hs0 : 0 < s := by linarith
  have hx6 : x = s ^ 6 := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have hsq : Real.sqrt x = s ^ 3 := by
    rw [Real.sqrt_eq_rpow, hs, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have hcube : x ^ (-(1 : ℝ) / 3) = (s ^ 2)⁻¹ := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_neg hx0.le]; norm_num
  rw [hsq, hcube, hx6]
  have hs3 : 8 ≤ s ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hs2 3]
  have hden : 0 < s ^ 6 - 1 := by nlinarith
  have hs2' : 0 < s ^ 2 := by positivity
  rw [div_le_iff₀ hden, inv_mul_eq_div, le_div_iff₀ hs2']
  have h5 : s ^ 5 * (s - 1) ≥ s ^ 5 := by
    have : 0 ≤ s ^ 5 := by positivity
    nlinarith
  have h6 : s ^ 5 ≥ 8 * s ^ 2 := by
    have : s ^ 5 = s ^ 3 * s ^ 2 := by ring
    rw [this]; nlinarith
  have h7 : s ^ 2 ≥ 4 := by nlinarith
  nlinarith

end Eigen

/-! ## The multiplier bound and the high part -/

section Multiplier

variable {K : Type*} [Fintype K] [DecidableEq K] (p : K → ℕ) [∀ j, NeZero (p j)]
  [∀ j, Fact (p j).Prime]

omit [Fintype K] [DecidableEq K] in
lemma shiftEigen_zero (j : K) : shiftEigen p j 0 = 1 := by
  unfold shiftEigen
  simp only [zero_mul, AddChar.map_zero_eq_one, sum_const, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (by exact_mod_cast (card_sqSet_pos p j).ne')

omit [Fintype K] [DecidableEq K] in
/-- `|λ_p(c)| ≤ p^{-1/3}` for `c ≠ 0` and `p ≥ 64` (`lem:square-shift`(a)). -/
lemma norm_shiftEigen_le (j : K) (h64 : 64 ≤ p j) (c : ZMod (p j)) (hc : c ≠ 0) :
    ‖shiftEigen p j c‖ ≤ (p j : ℝ) ^ (-(1 : ℝ) / 3) := by
  have hq2 : p j ≠ 2 := by omega
  have h := norm_sqAvg_le (q := p j) hq2 c hc
  exact h.trans (sqrt_add_one_div_le _ (by exact_mod_cast h64))

omit [DecidableEq K] in
/-- **`lem:square-shift`(d), the multiplier bound**: `|λ(ξ)| ≤ q(ξ)^{-1/3}` when every prime is
at least `64`, `q(ξ)` the conductor (`supportDenominator`). -/
theorem norm_pairMultiplier_le (h64 : ∀ j, 64 ≤ p j) (a : ResidueSpace p) :
    ‖pairMultiplier p a‖ ≤ (supportDenominator p a : ℝ) ^ (-(1 : ℝ) / 3) := by
  classical
  unfold pairMultiplier supportDenominator
  rw [← prod_filter_mul_prod_filter_not univ (fun j => a j ≠ 0)]
  have hrest : ∏ j ∈ univ.filter (fun j => ¬ a j ≠ 0), shiftEigen p j (a j) = 1 := by
    apply prod_eq_one
    intro j hj
    rw [mem_filter, not_not] at hj
    rw [hj.2, shiftEigen_zero]
  rw [hrest, mul_one, norm_prod]
  have hsupp : primeSupport p a = univ.filter (fun j => a j ≠ 0) := rfl
  rw [hsupp, Nat.cast_prod, ← Real.finsetProd_rpow _ _ (fun j _ => by positivity)]
  apply prod_le_prod₀ (fun j _ => norm_nonneg _)
  intro j hj
  exact norm_shiftEigen_le p j (h64 j) (a j) (mem_filter.mp hj).2

omit [∀ j, Fact (p j).Prime] in
/-- Parseval for the coefficients of `def:record:functional`(b): `∑_ξ |ĝ(ξ)|² = E|g|²`. -/
lemma groupCoeff_parseval (g : ResidueSpace p → ℂ) :
    ∑ a, ‖groupCoeff p g a‖ ^ 2 = 𝔼 z, ‖g z‖ ^ 2 := by
  have h := fourierPolynomial_parseval p (groupCoeff p g)
  have hrec : ∀ z, fourierPolynomial p (groupCoeff p g) z = g z :=
    fun z => fourierPolynomial_reconstruction p g z
  simp_rw [hrec] at h
  exact h.symm

/-- The low part `Ψ_{≤H} = ∑_{q(ξ) ≤ H} ĝ₁(−ξ) ĝ₂(ξ) λ(ξ)` of the pair average. -/
noncomputable def lowPart (H : ℝ) (g₁ g₂ : ResidueSpace p → ℂ) : ℂ :=
  ∑ a ∈ univ.filter (fun a => (supportDenominator p a : ℝ) ≤ H),
    groupCoeff p g₁ (-a) * groupCoeff p g₂ a * pairMultiplier p a

/-- The high part `Ψ_{>H} = ∑_{q(ξ) > H} ĝ₁(−ξ) ĝ₂(ξ) λ(ξ)` of the pair average. -/
noncomputable def highPart (H : ℝ) (g₁ g₂ : ResidueSpace p → ℂ) : ℂ :=
  ∑ a ∈ univ.filter (fun a => ¬ (supportDenominator p a : ℝ) ≤ H),
    groupCoeff p g₁ (-a) * groupCoeff p g₂ a * pairMultiplier p a

/-- `∫ g₁(x) g₂(y) dπ = Ψ_{≤H} + Ψ_{>H}` (Step 3 of `lem:record:density-can`). -/
theorem pairAvg_eq_low_add_high (H : ℝ) (g₁ g₂ : ResidueSpace p → ℂ) :
    pairAvg p g₁ g₂ = lowPart p H g₁ g₂ + highPart p H g₁ g₂ := by
  rw [pairAvg_fourier, lowPart, highPart, sum_filter_add_sum_filter_not]

/-- **The high part** (Step 3 of `lem:record:density-can`): since every prime exceeds `64`,
`|g(ξ)| ≤ q(ξ)^{-1/3} < H^{-1/3}` for `q(ξ) > H`, and Cauchy–Schwarz and Parseval give
`|Ψ_{>H}| ≤ H^{-1/3} ‖g₁‖₂ ‖g₂‖₂`. -/
theorem norm_highPart_le (h64 : ∀ j, 64 ≤ p j) {H : ℝ} (hH : 0 < H)
    (g₁ g₂ : ResidueSpace p → ℂ) :
    ‖highPart p H g₁ g₂‖ ≤
      H ^ (-(1 : ℝ) / 3) * (Real.sqrt (𝔼 z, ‖g₁ z‖ ^ 2) * Real.sqrt (𝔼 z, ‖g₂ z‖ ^ 2)) := by
  classical
  unfold highPart
  set c₁ := groupCoeff p g₁
  set c₂ := groupCoeff p g₂
  have hterm : ∀ a ∈ univ.filter (fun a => ¬ (supportDenominator p a : ℝ) ≤ H),
      ‖c₁ (-a) * c₂ a * pairMultiplier p a‖ ≤ H ^ (-(1 : ℝ) / 3) * (‖c₁ (-a)‖ * ‖c₂ a‖) := by
    intro a ha
    rw [mem_filter, not_le] at ha
    rw [norm_mul, norm_mul, mul_comm]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact (norm_pairMultiplier_le p h64 a).trans
      (Real.rpow_le_rpow_of_nonpos hH ha.2.le (by norm_num))
  calc ‖∑ a ∈ univ.filter (fun a => ¬ (supportDenominator p a : ℝ) ≤ H),
        c₁ (-a) * c₂ a * pairMultiplier p a‖
      ≤ ∑ a ∈ univ.filter (fun a => ¬ (supportDenominator p a : ℝ) ≤ H),
        ‖c₁ (-a) * c₂ a * pairMultiplier p a‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ univ.filter (fun a => ¬ (supportDenominator p a : ℝ) ≤ H),
        H ^ (-(1 : ℝ) / 3) * (‖c₁ (-a)‖ * ‖c₂ a‖) := sum_le_sum hterm
    _ ≤ ∑ a, H ^ (-(1 : ℝ) / 3) * (‖c₁ (-a)‖ * ‖c₂ a‖) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    _ = H ^ (-(1 : ℝ) / 3) * ∑ a, ‖c₁ (-a)‖ * ‖c₂ a‖ := by rw [mul_sum]
    _ ≤ H ^ (-(1 : ℝ) / 3) * (Real.sqrt (∑ a, ‖c₁ (-a)‖ ^ 2) * Real.sqrt (∑ a, ‖c₂ a‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) (by positivity)
    _ = H ^ (-(1 : ℝ) / 3) * (Real.sqrt (𝔼 z, ‖g₁ z‖ ^ 2) * Real.sqrt (𝔼 z, ‖g₂ z‖ ^ 2)) := by
        have hneg : ∑ a, ‖c₁ (-a)‖ ^ 2 = ∑ a, ‖c₁ a‖ ^ 2 :=
          Fintype.sum_equiv (Equiv.neg _) _ _ (fun _ => rfl)
        rw [hneg, groupCoeff_parseval, groupCoeff_parseval]

end Multiplier

end Sarkozy.Cancellation
