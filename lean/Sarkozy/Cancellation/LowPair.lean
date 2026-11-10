module

public import Sarkozy.Cancellation.FrequencyTransfer
public import Sarkozy.Kernel.All

@[expose] public section

/-!
# Step 3 of `lem:record:density-can`: a low pair support

`paper/sections/08_scale_comparison.tex`, proof of `lem:record:density-can`, Step 3. Fix `U`
and the labels at `U`; let `g₁, g₂` be the two pair inputs as functions on `X_{𝒮'}`, the tail
primes outside `U`. By `lem:square-shift`(d), `E_U φ_x(y) = Ψ_{≤H} + Ψ_{>H}`
(`pairAvg_eq_low_add_high`), with `|Ψ_{>H}| ≤ H^{-1/3} ‖g₁‖₂ ‖g₂‖₂` (`norm_highPart_le`).
For the low part, `lem:record:fibre-scale`(a) gives, for `q(ξ) ≤ H`,
`ĝ_i(ξ) = (D/L) ∑_{n ∈ A ∩ I_{b+i-1}, n ≡ 𝔞_i (D)} e(−nξ)`; the characters with `q(ξ) ≤ H` are
`Ξ_{H,D}` (`sum_low_eq_sum_frequencySet`), the multiplier is `g(ξ)`
(`pairMultiplier_eq_unitQuadraticAverage`), and `prop:record:kernel20`(iii) in the form of
`cor:kernel20` (`Sarkozy.Kernel.prop_kernel20_squareDifferenceFree` at
`cor_kernel20_admissible`, `C_D = C_H = 1`) gives
`|Ψ_{≤H}| ≤ C (N/L) N^{-1/120} √(α_{f,1} α_{f,2})`,
`α_{f,i} = (D/L) #{n ∈ A ∩ I_{b+i-1} : n ≡ 𝔞_i (D)}` (`norm_lowPart_le`).

The fibre formula is a hypothesis here, in the exact form of WP-FI's `groupCoeff_input_freeze`
(`Sarkozy.Functional.FibreScale`), stated for functions on `X_{𝒮'}`; the CRT reading of WP-FI's
`InFibre` as one class modulo `D` is not repeated.

New material for this paper.
-/

namespace Sarkozy.Cancellation

universe u v

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Finset Complex
open scoped BigOperators ComplexConjugate
open Sarkozy.FourierArithmetic Sarkozy.Functional

section Transforms

variable {K : Type*} [Fintype K] [DecidableEq K] (p : K → ℕ) [∀ j, NeZero (p j)]
  [∀ j, Fact (p j).Prime]

omit [DecidableEq K] [∀ j, NeZero (p j)] in
lemma supportDenominator_neg (a : ResidueSpace p) :
    supportDenominator p (-a) = supportDenominator p a := by
  unfold supportDenominator primeSupport
  congr 1
  ext j
  simp

omit [DecidableEq K] [∀ j, Fact (p j).Prime] in
/-- `∑_{n ∈ S} e(−n ξ_a) = N · F̂_S(ξ_a)` with `F̂` normalized by `N` (`kernelTransform`). -/
lemma fibreSum_eq_kernelTransform (N : ℕ) (hN : 0 < N) (S : Finset ℤ) (a : ResidueSpace p) :
    ∑ n ∈ S, conj (prodChar p a (integerResidue p n)) =
      (N : ℂ) * Kernel.kernelTransform N (Kernel.setIndicator S) (charFreq p a : ℝ) := by
  unfold Kernel.kernelTransform
  rw [Kernel.setIndicator_support, ← mul_assoc,
    mul_inv_cancel₀ (by exact_mod_cast hN.ne' : (N : ℂ) ≠ 0), one_mul]
  apply sum_congr rfl
  intro n hn
  rw [Kernel.setIndicator_apply, ite_eq_left hn, one_mul, conj_prodChar_integerResidue,
    kernel_expPhase_eq]

omit [DecidableEq K] in
/-- `∑_{n ∈ S} e(n ξ_a) = N · F̂_S(−ξ_a)`: the coefficient at `−a`. -/
lemma fibreSum_neg_eq_kernelTransform (N : ℕ) (hN : 0 < N) (S : Finset ℤ)
    (a : ResidueSpace p) :
    ∑ n ∈ S, conj (prodChar p (-a) (integerResidue p n)) =
      (N : ℂ) * Kernel.kernelTransform N (Kernel.setIndicator S) (-(charFreq p a : ℝ)) := by
  unfold Kernel.kernelTransform
  rw [Kernel.setIndicator_support, ← mul_assoc,
    mul_inv_cancel₀ (by exact_mod_cast hN.ne' : (N : ℂ) ≠ 0), one_mul]
  apply sum_congr rfl
  intro n hn
  rw [Kernel.setIndicator_apply, ite_eq_left hn, one_mul, prodChar_neg, Complex.conj_conj,
    prodChar_integerResidue_charFreq, kernel_expPhase_eq]
  congr 1
  ring

/-- **The low part as the kernel pairing.** Under the fibre formula of
`lem:record:fibre-scale`(a) for both inputs, `Ψ_{≤H} = (DN/L)² ∑_{ξ ∈ Ξ_{H,D}} g(ξ) F̂₁(−ξ) F̂₂(ξ)`,
`F_i = 1_{S_i}`. -/
theorem lowPart_eq_kernelPairing (hinj : Function.Injective p) (hodd : ∀ j, p j ≠ 2)
    (N : ℕ) (hN : 0 < N) {H : ℝ} (hH : 0 ≤ H) (D : ℕ) (hcopD : ∀ j, Nat.Coprime (p j) D)
    (hcover : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℝ) ≤ H → ¬ ℓ ∣ D → ∃ j, p j = ℓ)
    (L : ℝ) (S₁ S₂ : Finset ℤ) (g₁ g₂ : ResidueSpace p → ℂ)
    (hg₁ : ∀ a, (supportDenominator p a : ℝ) ≤ H → groupCoeff p g₁ a =
      (D : ℂ) * (L : ℂ)⁻¹ * ∑ n ∈ S₁, conj (prodChar p a (integerResidue p n)))
    (hg₂ : ∀ a, (supportDenominator p a : ℝ) ≤ H → groupCoeff p g₂ a =
      (D : ℂ) * (L : ℂ)⁻¹ * ∑ n ∈ S₂, conj (prodChar p a (integerResidue p n))) :
    lowPart p H g₁ g₂ = ((D : ℂ) * N * (L : ℂ)⁻¹) ^ 2 *
      ∑ ξ ∈ Kernel.frequencySet H D, Kernel.unitQuadraticAverage ξ *
        Kernel.kernelTransform N (Kernel.setIndicator S₁) (-(ξ : ℝ)) *
        Kernel.kernelTransform N (Kernel.setIndicator S₂) (ξ : ℝ) := by
  unfold lowPart
  rw [mul_sum, ← sum_low_eq_sum_frequencySet p hinj hH D hcopD hcover]
  apply sum_congr rfl
  intro a ha
  have haH := (mem_filter.mp ha).2
  have haH' : (supportDenominator p (-a) : ℝ) ≤ H := by rwa [supportDenominator_neg]
  rw [hg₁ (-a) haH', hg₂ a haH, fibreSum_neg_eq_kernelTransform p N hN,
    fibreSum_eq_kernelTransform p N hN, pairMultiplier_eq_unitQuadraticAverage p hinj hodd]
  ring

end Transforms

/-! ## The low-part bound from the kernel -/

/-- **The low part** (Step 3 of `lem:record:density-can`): with the constant `C` of
`prop:record:kernel20`(iii) at the triple of `cor:kernel20` (`C_D = C_H = 1`), for `N ≥ N₀`,
`D ≤ N^{1/20}`, `H = N^{1/40}`, a nonvanishing square class `𝔞₂ − 𝔞₁` modulo `D`, ordered
intervals `[u₁, v₁]`, `[u₂, v₂]` and inputs `g₁, g₂` on `X_{𝒮'}` whose coefficients at
`q(ξ) ≤ H` are given by the fibre formula of `lem:record:fibre-scale`(a),
`|Ψ_{≤H}| ≤ C (N/L) N^{-1/120} √(α_{f,1} α_{f,2})`,
`α_{f,i} = (D/L) #{n ∈ A ∩ [u_i, v_i] : n ≡ 𝔞_i (D)}`. -/
theorem norm_lowPart_le :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (K : Type u) [Fintype K] [DecidableEq K] (p : K → ℕ) [∀ j, NeZero (p j)]
        [∀ j, Fact (p j).Prime], Function.Injective p → (∀ j, 64 ≤ p j) →
      ∀ D : ℕ, (D : ℝ) ≤ (N : ℝ) ^ (1 / 20 : ℝ) → (∀ j, Nat.Coprime (p j) D) →
      (∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℝ) ≤ (N : ℝ) ^ (1 / 40 : ℝ) → ¬ ℓ ∣ D → ∃ j, p j = ℓ) →
      ∀ 𝔞₁ 𝔞₂ : ℤ, Kernel.IsNonvanishingSquareClass D (𝔞₂ - 𝔞₁) →
      ∀ A : Finset ℤ, Admissible N A →
      ∀ u₁ v₁ u₂ v₂ : ℤ, v₁ < u₂ →
      ∀ L : ℝ, 0 < L →
      ∀ g₁ g₂ : ResidueSpace p → ℂ,
        (∀ a, (supportDenominator p a : ℝ) ≤ (N : ℝ) ^ (1 / 40 : ℝ) → groupCoeff p g₁ a =
          (D : ℂ) * (L : ℂ)⁻¹ * ∑ n ∈ Kernel.classPart A u₁ v₁ 𝔞₁ D,
            conj (prodChar p a (integerResidue p n))) →
        (∀ a, (supportDenominator p a : ℝ) ≤ (N : ℝ) ^ (1 / 40 : ℝ) → groupCoeff p g₂ a =
          (D : ℂ) * (L : ℂ)⁻¹ * ∑ n ∈ Kernel.classPart A u₂ v₂ 𝔞₂ D,
            conj (prodChar p a (integerResidue p n))) →
        ‖lowPart p ((N : ℝ) ^ (1 / 40 : ℝ)) g₁ g₂‖ ≤
          C * ((N : ℝ) / L) * (N : ℝ) ^ (-(1 / 120 : ℝ)) *
            Real.sqrt (((D : ℝ) / L * (Kernel.classPart A u₁ v₁ 𝔞₁ D).card) *
              ((D : ℝ) / L * (Kernel.classPart A u₂ v₂ 𝔞₂ D).card)) := by
  obtain ⟨C, hC, N₀, hker⟩ := Kernel.prop_kernel20_squareDifferenceFree (1 / 20) (1 / 20)
    (17 / 100) Kernel.cor_kernel20_admissible 1 1 le_rfl le_rfl
  refine ⟨C, hC, max N₀ 1, ?_⟩
  intro N hN K _ _ p _ _ hinj h64 D hD hcopD hcover 𝔞₁ 𝔞₂ hsq A hA u₁ v₁ u₂ v₂ huv L hL g₁ g₂
    hg₁ hg₂
  have hN0 : 0 < N := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hN)
  have hH : (0 : ℝ) ≤ (N : ℝ) ^ (1 / 40 : ℝ) := by positivity
  have hodd : ∀ j, p j ≠ 2 := fun j => by have := h64 j; omega
  have hD0 : 0 < D := by
    rcases Nat.eq_zero_or_pos D with h | h
    · exfalso
      have h3 := hsq.1
      rw [h, Nat.factorization_zero] at h3
      simp at h3
    · exact h
  rw [lowPart_eq_kernelPairing p hinj hodd N hN0 hH D hcopD hcover L _ _ g₁ g₂ hg₁ hg₂]
  have he2 : (1 / 20 : ℝ) / 2 = 1 / 40 := by norm_num
  have hk := hker N (le_trans (le_max_left _ _) hN) ((N : ℝ) ^ (1 / 40 : ℝ))
    (by rw [inv_one, one_mul, he2]) (by rw [one_mul, he2]) D (by rw [one_mul]; exact hD)
    𝔞₁ 𝔞₂ hsq A hA u₁ v₁ u₂ v₂ huv
  have he6 : -((1 / 20 : ℝ) / 6) = -(1 / 120) := by norm_num
  rw [he6, norm_mul, Complex.norm_natCast] at hk
  set X := ‖∑ ξ ∈ Kernel.frequencySet ((N : ℝ) ^ (1 / 40 : ℝ)) D,
      Kernel.unitQuadraticAverage ξ *
        Kernel.kernelTransform N (Kernel.setIndicator (Kernel.classPart A u₁ v₁ 𝔞₁ D)) (-(ξ : ℝ)) *
        Kernel.kernelTransform N (Kernel.setIndicator (Kernel.classPart A u₂ v₂ 𝔞₂ D)) (ξ : ℝ)‖
    with hX
  set c₁ := ((Kernel.classPart A u₁ v₁ 𝔞₁ D).card : ℝ)
  set c₂ := ((Kernel.classPart A u₂ v₂ 𝔞₂ D).card : ℝ)
  set e := (N : ℝ) ^ (-(1 / 120 : ℝ))
  have hnorm : ‖((D : ℂ) * N * (L : ℂ)⁻¹) ^ 2‖ = ((D : ℝ) * N / L) ^ 2 := by
    rw [norm_pow, norm_mul, norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_natCast,
      Complex.norm_real, Real.norm_of_nonneg hL.le, div_eq_mul_inv]
  rw [norm_mul, hnorm]
  have hsqrt : Real.sqrt ((D : ℝ) / L * c₁ * ((D : ℝ) / L * c₂)) = (D : ℝ) / L * Real.sqrt (c₁ * c₂) := by
    rw [show (D : ℝ) / L * c₁ * ((D : ℝ) / L * c₂) = ((D : ℝ) / L) ^ 2 * (c₁ * c₂) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  rw [hsqrt]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD0
  calc ((D : ℝ) * N / L) ^ 2 * X = ((D : ℝ) * N ^ 2 / L ^ 2) * ((D : ℝ) * X) := by ring
    _ ≤ ((D : ℝ) * N ^ 2 / L ^ 2) * (C * e * Real.sqrt (c₁ * c₂) / N) :=
        mul_le_mul_of_nonneg_left hk (by positivity)
    _ = C * ((N : ℝ) / L) * e * ((D : ℝ) / L * Real.sqrt (c₁ * c₂)) := by
        field_simp

/-! ## Averaging over the labels -/

lemma rpow_neg_sq (x : ℝ) (hx : 0 < x) (c : ℝ) : (x ^ (-c)) ^ 2 = x ^ (-(2 * c)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  congr 1
  push_cast
  ring

/-- **The averaging of Step 3** of `lem:record:density-can`: with `|Ψ| ≤ |Ψ_{≤H}| + |Ψ_{>H}|`,
`|Ψ_{≤H}| ≤ C K N^{-1/120} √(α_{f,1} α_{f,2})`, `|Ψ_{>H}| ≤ H^{-1/3} ‖g₁‖₂ ‖g₂‖₂`,
`α_{f,2} ≤ 2`, `E α_{f,1} ≤ M₀ K α` and `E(‖g₁‖₂² ‖g₂‖₂²) ≤ C_ε N^ε α` under a probability
(or sub-probability) weight `w`,
`E|Ψ|² ≤ 4 C² K³ M₀ N^{-1/60} α + 2 H^{-2/3} C_ε N^ε α`. -/
theorem step3_average {Ω : Type*} (s : Finset Ω) (w : Ω → ℝ) (hw : ∀ ω ∈ s, 0 ≤ w ω)
    (Ψl Ψh : Ω → ℂ) (af₁ af₂ m₁ m₂ : Ω → ℝ) {C Kc M₀ α Cε ε N H : ℝ}
    (hN : 0 < N) (hH : 0 < H)
    (hl : ∀ ω ∈ s, ‖Ψl ω‖ ≤ C * Kc * N ^ (-(1 / 120 : ℝ)) * Real.sqrt (af₁ ω * af₂ ω))
    (hh : ∀ ω ∈ s, ‖Ψh ω‖ ≤ H ^ (-(1 : ℝ) / 3) * (Real.sqrt (m₁ ω) * Real.sqrt (m₂ ω)))
    (haf₁ : ∀ ω ∈ s, 0 ≤ af₁ ω) (haf₂ : ∀ ω ∈ s, 0 ≤ af₂ ω ∧ af₂ ω ≤ 2)
    (hm : ∀ ω ∈ s, 0 ≤ m₁ ω ∧ 0 ≤ m₂ ω)
    (hE₁ : ∑ ω ∈ s, w ω * af₁ ω ≤ M₀ * Kc * α)
    (hEm : ∑ ω ∈ s, w ω * (m₁ ω * m₂ ω) ≤ Cε * N ^ ε * α) :
    ∑ ω ∈ s, w ω * ‖Ψl ω + Ψh ω‖ ^ 2 ≤
      4 * C ^ 2 * Kc ^ 3 * M₀ * N ^ (-(1 / 60 : ℝ)) * α +
        2 * H ^ (-(2 : ℝ) / 3) * (Cε * N ^ ε * α) := by
  have hpt : ∀ ω ∈ s, ‖Ψl ω + Ψh ω‖ ^ 2 ≤
      4 * C ^ 2 * Kc ^ 2 * N ^ (-(1 / 60 : ℝ)) * af₁ ω +
        2 * H ^ (-(2 : ℝ) / 3) * (m₁ ω * m₂ ω) := by
    intro ω hω
    have h1 := hl ω hω
    have h2 := hh ω hω
    obtain ⟨ha2, ha2'⟩ := haf₂ ω hω
    have ha1 := haf₁ ω hω
    obtain ⟨hm1, hm2⟩ := hm ω hω
    have hl2 : ‖Ψl ω‖ ^ 2 ≤ C ^ 2 * Kc ^ 2 * N ^ (-(1 / 60 : ℝ)) * (af₁ ω * af₂ ω) := by
      calc ‖Ψl ω‖ ^ 2 ≤ (C * Kc * N ^ (-(1 / 120 : ℝ)) * Real.sqrt (af₁ ω * af₂ ω)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ = C ^ 2 * Kc ^ 2 * (N ^ (-(1 / 120 : ℝ))) ^ 2 * (Real.sqrt (af₁ ω * af₂ ω)) ^ 2 := by
            ring
        _ = C ^ 2 * Kc ^ 2 * N ^ (-(1 / 60 : ℝ)) * (af₁ ω * af₂ ω) := by
            rw [rpow_neg_sq N hN, Real.sq_sqrt (mul_nonneg ha1 ha2)]
            norm_num
    have hh2 : ‖Ψh ω‖ ^ 2 ≤ H ^ (-(2 : ℝ) / 3) * (m₁ ω * m₂ ω) := by
      calc ‖Ψh ω‖ ^ 2 ≤ (H ^ (-(1 : ℝ) / 3) * (Real.sqrt (m₁ ω) * Real.sqrt (m₂ ω))) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h2 2
        _ = (H ^ (-(1 : ℝ) / 3)) ^ 2 * ((Real.sqrt (m₁ ω)) ^ 2 * (Real.sqrt (m₂ ω)) ^ 2) := by
            ring
        _ = H ^ (-(2 : ℝ) / 3) * (m₁ ω * m₂ ω) := by
            rw [Real.sq_sqrt hm1, Real.sq_sqrt hm2, show -(1 : ℝ) / 3 = -(1 / 3) by ring,
              rpow_neg_sq H hH]
            norm_num
    have hadd : ‖Ψl ω + Ψh ω‖ ^ 2 ≤ 2 * ‖Ψl ω‖ ^ 2 + 2 * ‖Ψh ω‖ ^ 2 := by
      have := norm_add_le (Ψl ω) (Ψh ω)
      nlinarith [sq_nonneg (‖Ψl ω‖ - ‖Ψh ω‖), norm_nonneg (Ψl ω + Ψh ω)]
    have hprod : af₁ ω * af₂ ω ≤ 2 * af₁ ω := by nlinarith
    have hc : 0 ≤ C ^ 2 * Kc ^ 2 * N ^ (-(1 / 60 : ℝ)) := by positivity
    calc ‖Ψl ω + Ψh ω‖ ^ 2 ≤ 2 * ‖Ψl ω‖ ^ 2 + 2 * ‖Ψh ω‖ ^ 2 := hadd
      _ ≤ 2 * (C ^ 2 * Kc ^ 2 * N ^ (-(1 / 60 : ℝ)) * (af₁ ω * af₂ ω)) +
          2 * (H ^ (-(2 : ℝ) / 3) * (m₁ ω * m₂ ω)) := by linarith
      _ ≤ 2 * (C ^ 2 * Kc ^ 2 * N ^ (-(1 / 60 : ℝ)) * (2 * af₁ ω)) +
          2 * (H ^ (-(2 : ℝ) / 3) * (m₁ ω * m₂ ω)) := by
          have := mul_le_mul_of_nonneg_left hprod hc
          linarith
      _ = _ := by ring
  have hc4 : 0 ≤ 4 * C ^ 2 * Kc ^ 2 * N ^ (-(1 / 60 : ℝ)) := by positivity
  have hc2 : 0 ≤ 2 * H ^ (-(2 : ℝ) / 3) := by positivity
  calc ∑ ω ∈ s, w ω * ‖Ψl ω + Ψh ω‖ ^ 2
      ≤ ∑ ω ∈ s, w ω * (4 * C ^ 2 * Kc ^ 2 * N ^ (-(1 / 60 : ℝ)) * af₁ ω +
          2 * H ^ (-(2 : ℝ) / 3) * (m₁ ω * m₂ ω)) :=
        sum_le_sum (fun ω hω => mul_le_mul_of_nonneg_left (hpt ω hω) (hw ω hω))
    _ = 4 * C ^ 2 * Kc ^ 2 * N ^ (-(1 / 60 : ℝ)) * ∑ ω ∈ s, w ω * af₁ ω +
          2 * H ^ (-(2 : ℝ) / 3) * ∑ ω ∈ s, w ω * (m₁ ω * m₂ ω) := by
        rw [mul_sum, mul_sum, ← sum_add_distrib]
        apply sum_congr rfl
        intro ω _
        ring
    _ ≤ 4 * C ^ 2 * Kc ^ 2 * N ^ (-(1 / 60 : ℝ)) * (M₀ * Kc * α) +
          2 * H ^ (-(2 : ℝ) / 3) * (Cε * N ^ ε * α) := by
        have := mul_le_mul_of_nonneg_left hE₁ hc4
        have := mul_le_mul_of_nonneg_left hEm hc2
        linarith
    _ = _ := by ring

/-! ## Step 3 -/

/-- **Step 3 of `lem:record:density-can` (a low pair support).** Fix `U` with `q_U ≤ T₀`; the
tail primes outside `U` are the coordinates `p_j ≥ 64` of `X_{𝒮'}`, coprime to the fibre
modulus `D = M₀ D_pre q_U ≤ N^{1/20}`, and every prime `ℓ ≤ H = N^{1/40}` with `ℓ ∤ D` is one
of them. For labels `ω = (x, y)` under a (sub-)probability weight `w`, let `g₁(ω), g₂(ω)` be the
two pair inputs on `X_{𝒮'}`, with the fibre formula of `lem:record:fibre-scale`(a) at the
classes `𝔞₁(ω), 𝔞₂(ω)` modulo `D` (`𝔞₂ − 𝔞₁` a nonvanishing square class), and
`E_U φ_x(y) = ∫ g₁(x') g₂(y') dπ` (`pairAvg`, `π = ⊗_{p ∈ 𝒮'} Unif(Ω_p)`). If
`α_{f,2} ≤ 2`, `E α_{f,1} ≤ M₀ K α` and `E(‖g₁‖₂² ‖g₂‖₂²) ≤ C_ε N^ε α`, then
`∫ ‖E_U φ_x‖₂² ≤ 4 C² K³ M₀ N^{-1/60} α + 2 H^{-2/3} C_ε N^ε α`,
with `C` the constant of `prop:record:kernel20`(iii) at the triple of `cor:kernel20`. -/
theorem step3_low_pair_support :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (K : Type u) [Fintype K] [DecidableEq K] (p : K → ℕ) [∀ j, NeZero (p j)]
        [∀ j, Fact (p j).Prime], Function.Injective p → (∀ j, 64 ≤ p j) →
      ∀ D : ℕ, (D : ℝ) ≤ (N : ℝ) ^ (1 / 20 : ℝ) → (∀ j, Nat.Coprime (p j) D) →
      (∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℝ) ≤ (N : ℝ) ^ (1 / 40 : ℝ) → ¬ ℓ ∣ D → ∃ j, p j = ℓ) →
      ∀ A : Finset ℤ, Admissible N A →
      ∀ u₁ v₁ u₂ v₂ : ℤ, v₁ < u₂ →
      ∀ L : ℝ, 0 < L →
      ∀ (Ω : Type v) (s : Finset Ω) (w : Ω → ℝ), (∀ ω ∈ s, 0 ≤ w ω) →
      ∀ (𝔞₁ 𝔞₂ : Ω → ℤ) (g₁ g₂ : Ω → ResidueSpace p → ℂ),
      (∀ ω ∈ s, Kernel.IsNonvanishingSquareClass D (𝔞₂ ω - 𝔞₁ ω)) →
      (∀ ω ∈ s, ∀ a, (supportDenominator p a : ℝ) ≤ (N : ℝ) ^ (1 / 40 : ℝ) →
        groupCoeff p (g₁ ω) a = (D : ℂ) * (L : ℂ)⁻¹ *
          ∑ n ∈ Kernel.classPart A u₁ v₁ (𝔞₁ ω) D, conj (prodChar p a (integerResidue p n))) →
      (∀ ω ∈ s, ∀ a, (supportDenominator p a : ℝ) ≤ (N : ℝ) ^ (1 / 40 : ℝ) →
        groupCoeff p (g₂ ω) a = (D : ℂ) * (L : ℂ)⁻¹ *
          ∑ n ∈ Kernel.classPart A u₂ v₂ (𝔞₂ ω) D, conj (prodChar p a (integerResidue p n))) →
      ∀ Kc M₀ α Cε ε : ℝ, (N : ℝ) / L ≤ Kc →
      (∀ ω ∈ s, (D : ℝ) / L * (Kernel.classPart A u₂ v₂ (𝔞₂ ω) D).card ≤ 2) →
      ∑ ω ∈ s, w ω * ((D : ℝ) / L * (Kernel.classPart A u₁ v₁ (𝔞₁ ω) D).card) ≤ M₀ * Kc * α →
      ∑ ω ∈ s, w ω * ((𝔼 z, ‖g₁ ω z‖ ^ 2) * (𝔼 z, ‖g₂ ω z‖ ^ 2)) ≤ Cε * (N : ℝ) ^ ε * α →
      ∑ ω ∈ s, w ω * ‖pairAvg p (g₁ ω) (g₂ ω)‖ ^ 2 ≤
        4 * C ^ 2 * Kc ^ 3 * M₀ * (N : ℝ) ^ (-(1 / 60 : ℝ)) * α +
          2 * ((N : ℝ) ^ (1 / 40 : ℝ)) ^ (-(2 : ℝ) / 3) * (Cε * (N : ℝ) ^ ε * α) := by
  obtain ⟨C, hC, N₀, hlow⟩ := norm_lowPart_le.{u}
  refine ⟨C, hC, max N₀ 1, ?_⟩
  intro N hN K _ _ p _ _ hinj h64 D hD hcopD hcover A hA u₁ v₁ u₂ v₂ huv L hL Ω s w hw
    𝔞₁ 𝔞₂ g₁ g₂ hsq hg₁ hg₂ Kc M₀ α Cε ε hKc haf₂ hE₁ hEm
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  have hHpos : (0 : ℝ) < (N : ℝ) ^ (1 / 40 : ℝ) := by positivity
  have hD0 : (0 : ℝ) ≤ D := by positivity
  simp_rw [pairAvg_eq_low_add_high p ((N : ℝ) ^ (1 / 40 : ℝ))]
  apply step3_average s w hw _ _
    (fun ω => (D : ℝ) / L * (Kernel.classPart A u₁ v₁ (𝔞₁ ω) D).card)
    (fun ω => (D : ℝ) / L * (Kernel.classPart A u₂ v₂ (𝔞₂ ω) D).card)
    (fun ω => 𝔼 z, ‖g₁ ω z‖ ^ 2) (fun ω => 𝔼 z, ‖g₂ ω z‖ ^ 2) hNr hHpos
  · intro ω hω
    have h := hlow N (le_trans (le_max_left _ _) hN) K p hinj h64 D hD hcopD hcover (𝔞₁ ω) (𝔞₂ ω)
      (hsq ω hω) A hA u₁ v₁ u₂ v₂ huv L hL (g₁ ω) (g₂ ω) (hg₁ ω hω) (hg₂ ω hω)
    refine h.trans ?_
    have hs0 : 0 ≤ (N : ℝ) ^ (-(1 / 120 : ℝ)) *
        Real.sqrt ((D : ℝ) / L * (Kernel.classPart A u₁ v₁ (𝔞₁ ω) D).card *
          ((D : ℝ) / L * (Kernel.classPart A u₂ v₂ (𝔞₂ ω) D).card)) := by positivity
    have := mul_le_mul_of_nonneg_left hKc hC.le
    calc C * ((N : ℝ) / L) * (N : ℝ) ^ (-(1 / 120 : ℝ)) *
          Real.sqrt ((D : ℝ) / L * (Kernel.classPart A u₁ v₁ (𝔞₁ ω) D).card *
            ((D : ℝ) / L * (Kernel.classPart A u₂ v₂ (𝔞₂ ω) D).card))
        = (C * ((N : ℝ) / L)) * ((N : ℝ) ^ (-(1 / 120 : ℝ)) *
          Real.sqrt ((D : ℝ) / L * (Kernel.classPart A u₁ v₁ (𝔞₁ ω) D).card *
            ((D : ℝ) / L * (Kernel.classPart A u₂ v₂ (𝔞₂ ω) D).card))) := by ring
      _ ≤ (C * Kc) * ((N : ℝ) ^ (-(1 / 120 : ℝ)) *
          Real.sqrt ((D : ℝ) / L * (Kernel.classPart A u₁ v₁ (𝔞₁ ω) D).card *
            ((D : ℝ) / L * (Kernel.classPart A u₂ v₂ (𝔞₂ ω) D).card))) :=
          mul_le_mul_of_nonneg_right this hs0
      _ = _ := by ring
  · intro ω _
    exact norm_highPart_le p (fun j => h64 j) hHpos (g₁ ω) (g₂ ω)
  · intro ω _
    positivity
  · intro ω hω
    exact ⟨by positivity, haf₂ ω hω⟩
  · intro ω _
    exact ⟨by positivity, by positivity⟩
  · exact hE₁
  · exact hEm

/-- Step 3 in the form used by Step 4: `∫ ‖E_U φ_x‖₂² ≤ C'_ε N^{-1/60+ε} α`,
`C'_ε = 4 C² K³ M₀ + 2 C_ε`, uniformly in `U`. -/
lemma step3_rhs_le {C Kc M₀ α Cε ε : ℝ} {N : ℕ} (hN : 1 ≤ N) (hKc : 0 ≤ Kc) (hM₀ : 0 ≤ M₀)
    (hα : 0 ≤ α) (hε : 0 ≤ ε) :
    4 * C ^ 2 * Kc ^ 3 * M₀ * (N : ℝ) ^ (-(1 / 60 : ℝ)) * α +
        2 * ((N : ℝ) ^ (1 / 40 : ℝ)) ^ (-(2 : ℝ) / 3) * (Cε * (N : ℝ) ^ ε * α) ≤
      (4 * C ^ 2 * Kc ^ 3 * M₀ + 2 * Cε) * (N : ℝ) ^ (-(1 : ℝ) / 60 + ε) * α := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hH : ((N : ℝ) ^ (1 / 40 : ℝ)) ^ (-(2 : ℝ) / 3) = (N : ℝ) ^ (-(1 / 60 : ℝ)) := by
    rw [← Real.rpow_mul hN0.le]
    norm_num
  have h1 : (N : ℝ) ^ (-(1 / 60 : ℝ)) ≤ (N : ℝ) ^ (-(1 : ℝ) / 60 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have h2 : (N : ℝ) ^ (-(1 / 60 : ℝ)) * (N : ℝ) ^ ε = (N : ℝ) ^ (-(1 : ℝ) / 60 + ε) := by
    rw [← Real.rpow_add hN0]
    norm_num
  rw [hH]
  have hk : 0 ≤ 4 * C ^ 2 * Kc ^ 3 * M₀ * α := by positivity
  calc 4 * C ^ 2 * Kc ^ 3 * M₀ * (N : ℝ) ^ (-(1 / 60 : ℝ)) * α +
        2 * (N : ℝ) ^ (-(1 / 60 : ℝ)) * (Cε * (N : ℝ) ^ ε * α)
      = (4 * C ^ 2 * Kc ^ 3 * M₀ * α) * (N : ℝ) ^ (-(1 / 60 : ℝ)) +
        2 * Cε * α * ((N : ℝ) ^ (-(1 / 60 : ℝ)) * (N : ℝ) ^ ε) := by ring
    _ ≤ (4 * C ^ 2 * Kc ^ 3 * M₀ * α) * (N : ℝ) ^ (-(1 : ℝ) / 60 + ε) +
        2 * Cε * α * (N : ℝ) ^ (-(1 : ℝ) / 60 + ε) := by
        rw [h2]
        have := mul_le_mul_of_nonneg_left h1 hk
        linarith
    _ = _ := by ring

end Sarkozy.Cancellation
