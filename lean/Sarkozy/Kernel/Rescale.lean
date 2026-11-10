module

public import Sarkozy.Kernel.KernelEstimate

@[expose] public section

/-!
# Division by an even-valuation square (`lem:record:nonunit-rescale`)

The rescaling identity of `prop:record:kernel20`(ii): if `R = s²` divides `D`, `D = R D_R`,
every prime of `D` divides `D_R`, and `F, J` live on the classes `a, b mod D` with
`a ≡ b mod R`, then with `a_R ≡ a mod R`, `F'(n') = F(a_R + R n')`, `J'(n') = J(a_R + R n')`
and any normalizing length `N'`,
`D ∑_{ξ ∈ Ξ_{H,D}} g(ξ) F̂_N(-ξ) Ĵ_N(ξ) = R (N'/N)² D_R ∑_{ξ' ∈ Ξ_{H,D_R}} g(ξ') F̂'_{N'}(-ξ') Ĵ'_{N'}(ξ')`
(part (d) of the lemma; part (c), `Ξ_{H,D_R} = Ξ_{H,D}` and `ξ ↦ Rξ` permutes it preserving
`g`, is `frequencySet_eq_of_rad` and `unitQuadraticAverage_mul_square`). The paper takes
`N' = ⌈N/R⌉`; the identity holds for every `N' > 0`. The support statements (a), (b) of the
lemma are `rescaled_support`.

This identity is explanatory in the paper: the estimate of part (ii) is proved as a special case
of part (iii) (`prop_kernel20_twentieth`). New material for this paper.
-/

namespace Sarkozy

namespace Kernel

open Finset

/-! ## The frequency set depends only on the primes of `D` -/

lemma coprime_iff_of_rad {D DR q : ℕ} (hDR : DR ∣ D) (hrad : ∀ p : ℕ, p.Prime → p ∣ D → p ∣ DR) :
    Nat.Coprime q D ↔ Nat.Coprime q DR := by
  constructor
  · intro h; exact h.coprime_dvd_right hDR
  · intro h
    apply Nat.coprime_of_dvd
    intro p hp hpq hpD
    have h1 := Nat.dvd_gcd hpq (hrad p hp hpD)
    rw [h.gcd_eq_one] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)

lemma frequencySet_eq_of_rad (H : ℝ) {D DR : ℕ} (hDR : DR ∣ D)
    (hrad : ∀ p : ℕ, p.Prime → p ∣ D → p ∣ DR) : frequencySet H D = frequencySet H DR := by
  unfold frequencySet
  apply filter_congr
  intro ξ _
  rw [coprime_iff_of_rad hDR hrad]

/-! ## Multiplying a frequency by a square coprime to its denominator -/

lemma den_natCast_mul (R : ℕ) (ξ : ℚ) (h : Nat.Coprime R ξ.den) : ((R : ℚ) * ξ).den = ξ.den := by
  rw [Rat.mul_den]
  simp only [Rat.num_natCast, Rat.den_natCast, one_mul]
  have hg : Nat.gcd ((R : ℤ) * ξ.num).natAbs ξ.den = 1 := by
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.coprime_mul_iff_left.mpr ⟨h, ξ.reduced⟩
  rw [hg, Nat.div_one]

lemma unitQuadraticAverage_fract (ξ : ℚ) :
    unitQuadraticAverage (Int.fract ξ) = unitQuadraticAverage ξ := by
  unfold unitQuadraticAverage
  rw [Rat.den_intFract]
  congr 1
  apply sum_congr rfl
  intro m _
  have : ((Int.fract ξ : ℚ) : ℝ) * (m : ℝ)^2 = (ξ : ℝ) * (m : ℝ)^2 + ((-(⌊ξ⌋ * m^2) : ℤ) : ℝ) := by
    rw [Int.fract]
    push_cast
    ring
  rw [this, expPhase_add, expPhase_int, mul_one]

/-- Multiplication by a unit permutes the units modulo `q`. -/
lemma sum_units_mul_perm (q s : ℕ) (hq : 0 < q) (hs : Nat.Coprime s q) (f : ℕ → ℂ) :
    ∑ m ∈ (range q).filter (fun m => Nat.Coprime m q), f ((s * m) % q) =
      ∑ m ∈ (range q).filter (fun m => Nat.Coprime m q), f m := by
  set U := (range q).filter (fun m => Nat.Coprime m q) with hU
  have hmaps : ∀ m ∈ U, (s * m) % q ∈ U := by
    intro m hm
    rw [hU, mem_filter, mem_range] at hm ⊢
    refine ⟨Nat.mod_lt _ hq, ?_⟩
    have h1 : Nat.Coprime (s * m) q := Nat.coprime_mul_iff_left.mpr ⟨hs, hm.2⟩
    show Nat.gcd ((s * m) % q) q = 1
    rw [← Nat.gcd_rec]
    exact h1.symm
  have hinj : ∀ m ∈ U, ∀ m' ∈ U, (s * m) % q = (s * m') % q → m = m' := by
    intro m hm m' hm' he
    rw [hU, mem_filter, mem_range] at hm hm'
    have h1 : s * m ≡ s * m' [MOD q] := he
    have h2 := Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hs) h1
    unfold Nat.ModEq at h2
    rwa [Nat.mod_eq_of_lt hm.1, Nat.mod_eq_of_lt hm'.1] at h2
  apply Finset.sum_nbij (fun m => (s * m) % q)
  · exact hmaps
  · intro m hm m' hm' he
    exact hinj m hm m' hm' he
  · intro m' hm'
    obtain ⟨m, hm, he⟩ := Finset.surj_on_of_inj_on_of_card_le (s := U) (t := U)
      (fun m _ => (s * m) % q) (fun m hm => hmaps m hm)
      (fun a b ha hb he => hinj a ha b hb he) le_rfl m' hm'
    exact ⟨m, hm, he.symm⟩
  · intro m _
    rfl

/-- `g(s² ξ) = g(ξ)` when `s` is coprime to the denominator of `ξ` (`lem:record:nonunit-rescale`(c)). -/
lemma unitQuadraticAverage_mul_square (s : ℕ) (ξ : ℚ) (hs : Nat.Coprime s ξ.den) :
    unitQuadraticAverage ((s ^ 2 : ℕ) * ξ) = unitQuadraticAverage ξ := by
  have hR : Nat.Coprime (s ^ 2) ξ.den := hs.pow_left 2
  unfold unitQuadraticAverage
  rw [den_natCast_mul _ _ hR]
  congr 1
  have hper := expPhase_rat_sq_periodic ξ
  have hterm : ∀ m : ℕ, expPhase ((((s ^ 2 : ℕ) * ξ : ℚ) : ℝ) * (m : ℝ)^2) =
      (fun n : ℕ => expPhase ((ξ : ℝ) * (n : ℝ)^2)) ((s * m) % ξ.den) := by
    intro m
    simp only
    rw [periodic_nat_mod _ _ hper (s * m)]
    push_cast
    ring_nf
  simp_rw [hterm]
  exact sum_units_mul_perm ξ.den s ξ.pos hs (fun n : ℕ => expPhase ((ξ : ℝ) * (n : ℝ)^2))

/-- `ξ ↦ s² ξ` permutes `Ξ_{H,D}` when every prime of `s` divides `D`, and preserves `g`
(`lem:record:nonunit-rescale`(c)). -/
lemma sum_frequencySet_mul_square (H : ℝ) (hH : 0 ≤ H) (D s : ℕ) (hs : 0 < s)
    (hsD : ∀ p : ℕ, p.Prime → p ∣ s → p ∣ D) (f : ℚ → ℂ) (hf : ∀ (x : ℚ) (k : ℤ), f (x + k) = f x) :
    ∑ ξ ∈ frequencySet H D, unitQuadraticAverage ξ * f ((s ^ 2 : ℕ) * ξ) =
      ∑ ξ ∈ frequencySet H D, unitQuadraticAverage ξ * f ξ := by
  have hcop : ∀ ξ ∈ frequencySet H D, Nat.Coprime s ξ.den := by
    intro ξ hξ
    have h := ((mem_frequencySet hH D ξ).mp hξ).2.2.2.2
    apply Nat.coprime_of_dvd
    intro p hp hps hpξ
    have h1 := Nat.dvd_gcd hpξ (hsD p hp hps)
    rw [h.gcd_eq_one] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hden : ∀ ξ ∈ frequencySet H D, (Int.fract (((s ^ 2 : ℕ) : ℚ) * ξ)).den = ξ.den := by
    intro ξ hξ
    rw [Rat.den_intFract, den_natCast_mul _ _ ((hcop ξ hξ).pow_left 2)]
  have hmaps : ∀ ξ ∈ frequencySet H D, Int.fract (((s ^ 2 : ℕ) : ℚ) * ξ) ∈ frequencySet H D := by
    intro ξ hξ
    have h := (mem_frequencySet hH D ξ).mp hξ
    rw [mem_frequencySet hH, hden ξ hξ]
    exact ⟨Int.fract_nonneg _, Int.fract_lt_one _, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  have hinj : ∀ ξ ∈ frequencySet H D, ∀ ξ' ∈ frequencySet H D,
      Int.fract (((s ^ 2 : ℕ) : ℚ) * ξ) = Int.fract (((s ^ 2 : ℕ) : ℚ) * ξ') → ξ = ξ' := by
    intro ξ hξ ξ' hξ' he
    obtain ⟨k, hk⟩ := Int.fract_eq_fract.mp he
    have h := (mem_frequencySet hH D ξ).mp hξ
    have h' := (mem_frequencySet hH D ξ').mp hξ'
    set δ := ξ - ξ' with hδ
    have hR0 : ((s ^ 2 : ℕ) : ℚ) ≠ 0 := by positivity
    have hδR : δ = (k : ℚ) / ((s ^ 2 : ℕ) : ℚ) := by
      rw [eq_div_iff hR0, hδ]
      linarith
    have hd1 : δ.den ∣ s ^ 2 := by rw [hδR]; exact rat_div_den_dvd k (s ^ 2)
    have hd2 : δ.den ∣ ξ.den * ξ'.den := Rat.sub_den_dvd _ _
    have hcop2 : Nat.Coprime (s ^ 2) (ξ.den * ξ'.den) :=
      Nat.Coprime.mul_right ((hcop ξ hξ).pow_left 2) ((hcop ξ' hξ').pow_left 2)
    have hδ1 : δ.den = 1 := by
      have := Nat.dvd_gcd hd1 hd2
      rw [hcop2.gcd_eq_one] at this
      exact Nat.dvd_one.mp this
    have hδint : (δ.num : ℚ) = δ := (Rat.den_eq_one_iff δ).mp hδ1
    have hlo : -1 < δ := by rw [hδ]; linarith [h.1, h'.2.1]
    have hhi : δ < 1 := by rw [hδ]; linarith [h.2.1, h'.1]
    have hnum : δ.num = 0 := by
      have h1 : (-1 : ℚ) < (δ.num : ℚ) := by rw [hδint]; exact hlo
      have h2 : (δ.num : ℚ) < 1 := by rw [hδint]; exact hhi
      have h1' : -1 < δ.num := by exact_mod_cast h1
      have h2' : δ.num < 1 := by exact_mod_cast h2
      omega
    have hδ0 : δ = 0 := by rw [← hδint, hnum]; simp
    rw [hδ] at hδ0
    linarith
  apply Finset.sum_nbij (fun ξ => Int.fract (((s ^ 2 : ℕ) : ℚ) * ξ))
  · exact hmaps
  · intro ξ hξ ξ' hξ' he
    exact hinj ξ hξ ξ' hξ' he
  · intro ξ' hξ'
    obtain ⟨ξ, hξ, he⟩ := Finset.surj_on_of_inj_on_of_card_le (s := frequencySet H D)
      (t := frequencySet H D) (fun ξ _ => Int.fract (((s ^ 2 : ℕ) : ℚ) * ξ))
      (fun ξ hξ => hmaps ξ hξ) (fun a b ha hb he => hinj a ha b hb he) le_rfl ξ' hξ'
    exact ⟨ξ, hξ, he.symm⟩
  · intro ξ hξ
    rw [unitQuadraticAverage_fract, unitQuadraticAverage_mul_square s ξ (hcop ξ hξ)]
    congr 1
    have := hf (((s ^ 2 : ℕ) : ℚ) * ξ) (-⌊((s ^ 2 : ℕ) : ℚ) * ξ⌋)
    rw [Int.fract]
    push_cast at this ⊢
    rw [← this]
    ring_nf

/-! ## Rescaled functions and the normalized transforms -/

lemma affine_injective (aR : ℤ) (R : ℕ) (hR : 0 < R) :
    Function.Injective (fun n' : ℤ => aR + (R : ℤ) * n') := by
  intro x y h
  simp only at h
  have hR' : (R : ℤ) ≠ 0 := by exact_mod_cast hR.ne'
  have : (R : ℤ) * x = (R : ℤ) * y := by linarith
  exact mul_left_cancel₀ hR' this

/-- `F'(n') = F(a_R + R n')` (`lem:record:nonunit-rescale`). -/
noncomputable def rescaled (F : ℤ →₀ ℂ) (aR : ℤ) (R : ℕ) (hR : 0 < R) : ℤ →₀ ℂ :=
  Finsupp.comapDomain (fun n' : ℤ => aR + (R : ℤ) * n') F
    ((affine_injective aR R hR).injOn)

lemma rescaled_apply (F : ℤ →₀ ℂ) (aR : ℤ) (R : ℕ) (hR : 0 < R) (n' : ℤ) :
    rescaled F aR R hR n' = F (aR + (R : ℤ) * n') := rfl

/-- `F̂_N(ξ) = (N'/N) e(-a_R ξ) F̂'_{N'}(R ξ)` (proof of `lem:record:nonunit-rescale`(d)). -/
lemma kernelTransform_rescaled (N N' : ℕ) (hN' : 0 < N') (F : ℤ →₀ ℂ) (aR : ℤ) (R : ℕ)
    (hR : 0 < R) (hF : ∀ n ∈ F.support, n ≡ aR [ZMOD (R : ℤ)]) (ξ : ℝ) :
    kernelTransform N F ξ = ((N' : ℂ) / N) * expPhase (-(aR : ℝ) * ξ) *
      kernelTransform N' (rescaled F aR R hR) ((R : ℝ) * ξ) := by
  unfold kernelTransform rescaled
  rw [Finsupp.comapDomain_support]
  have hsum : ∑ n ∈ F.support, F n * expPhase (-(n : ℝ) * ξ) =
      ∑ n' ∈ F.support.preimage (fun n' : ℤ => aR + (R : ℤ) * n')
        ((affine_injective aR R hR).injOn),
        F (aR + (R : ℤ) * n') * expPhase (-((aR + (R : ℤ) * n' : ℤ) : ℝ) * ξ) := by
    symm
    apply Finset.sum_preimage (fun n' : ℤ => aR + (R : ℤ) * n') F.support
      ((affine_injective aR R hR).injOn) (fun n => F n * expPhase (-(n : ℝ) * ξ))
    intro x hx hxr
    exfalso
    apply hxr
    obtain ⟨k, hk⟩ := (Int.ModEq.dvd (hF x hx).symm)
    exact ⟨k, by simp only; linarith⟩
  rw [hsum]
  have hN0 : (N' : ℂ) ≠ 0 := by exact_mod_cast hN'.ne'
  have hterm : ∀ n' : ℤ, F (aR + (R : ℤ) * n') * expPhase (-((aR + (R : ℤ) * n' : ℤ) : ℝ) * ξ) =
      expPhase (-(aR : ℝ) * ξ) * ((Finsupp.comapDomain (fun n' : ℤ => aR + (R : ℤ) * n') F
        ((affine_injective aR R hR).injOn)) n' * expPhase (-(n' : ℝ) * ((R : ℝ) * ξ))) := by
    intro n'
    rw [Finsupp.comapDomain_apply]
    have : -((aR + (R : ℤ) * n' : ℤ) : ℝ) * ξ = -(aR : ℝ) * ξ + -(n' : ℝ) * ((R : ℝ) * ξ) := by
      push_cast; ring
    rw [this, expPhase_add]
    ring
  simp_rw [hterm]
  rw [← mul_sum]
  have key : ∀ (e S : ℂ), (N : ℂ)⁻¹ * (e * S) = ((N' : ℂ) / N) * e * ((N' : ℂ)⁻¹ * S) := by
    intro e S
    calc (N : ℂ)⁻¹ * (e * S) = ((N' : ℂ) * (N' : ℂ)⁻¹) * (N : ℂ)⁻¹ * e * S := by
          rw [mul_inv_cancel₀ hN0]; ring
      _ = _ := by rw [div_eq_mul_inv]; ring
  exact key _ _

/-- **Division by an even-valuation square** (`lem:record:nonunit-rescale`(d), the rescaling
identity of `prop:record:kernel20`(ii)): for `D = R D_R` with `R = s²`, every prime of `D`
dividing `D_R`, `F, J` on the classes `a, b mod D` with `R ∣ b - a`, `a_R ≡ a mod R`, and
`F' = F(a_R + R ·)`, `J' = J(a_R + R ·)`:
`D ∑_{Ξ_{H,D}} g F̂_N(-ξ) Ĵ_N(ξ) = R (N'/N)² D_R ∑_{Ξ_{H,D_R}} g F̂'_{N'}(-ξ') Ĵ'_{N'}(ξ')`. -/
theorem nonunit_rescale_identity (N N' : ℕ) (hN' : 0 < N') (H : ℝ) (hH : 0 ≤ H)
    (D DR s : ℕ) (hs : 0 < s) (hD : D = s ^ 2 * DR)
    (hrad : ∀ p : ℕ, p.Prime → p ∣ D → p ∣ DR) (a b aR : ℤ)
    (hab : ((s ^ 2 : ℕ) : ℤ) ∣ b - a) (haR : aR ≡ a [ZMOD ((s ^ 2 : ℕ) : ℤ)])
    (F J : ℤ →₀ ℂ) (hF : ∀ x ∈ F.support, x ≡ a [ZMOD (D : ℤ)])
    (hJ : ∀ y ∈ J.support, y ≡ b [ZMOD (D : ℤ)]) :
    (D : ℂ) * ∑ ξ ∈ frequencySet H D,
        unitQuadraticAverage ξ * kernelTransform N F (-(ξ : ℝ)) * kernelTransform N J (ξ : ℝ) =
      ((s ^ 2 : ℕ) : ℂ) * ((N' : ℂ) / N) ^ 2 *
        ((DR : ℂ) * ∑ ξ ∈ frequencySet H DR,
          unitQuadraticAverage ξ *
            kernelTransform N' (rescaled F aR (s ^ 2) (by positivity)) (-(ξ : ℝ)) *
            kernelTransform N' (rescaled J aR (s ^ 2) (by positivity)) (ξ : ℝ)) := by
  have hR : 0 < s ^ 2 := by positivity
  have hRD : ((s ^ 2 : ℕ) : ℤ) ∣ (D : ℤ) := by rw [hD]; push_cast; exact dvd_mul_right _ _
  have hDR : DR ∣ D := by rw [hD]; exact dvd_mul_left _ _
  have hFR : ∀ x ∈ F.support, x ≡ aR [ZMOD ((s ^ 2 : ℕ) : ℤ)] := by
    intro x hx
    exact ((hF x hx).of_dvd hRD).trans haR.symm
  have hJR : ∀ y ∈ J.support, y ≡ aR [ZMOD ((s ^ 2 : ℕ) : ℤ)] := by
    intro y hy
    have h1 : y ≡ b [ZMOD ((s ^ 2 : ℕ) : ℤ)] := (hJ y hy).of_dvd hRD
    have h2 : b ≡ a [ZMOD ((s ^ 2 : ℕ) : ℤ)] := (Int.modEq_iff_dvd.mpr hab).symm
    exact (h1.trans h2).trans haR.symm
  have hsD : ∀ p : ℕ, p.Prime → p ∣ s → p ∣ D := by
    intro p _ hps
    rw [hD]
    exact (hps.trans (dvd_pow_self s two_ne_zero)).trans (dvd_mul_right _ _)
  rw [← frequencySet_eq_of_rad H hDR hrad]
  set F' := rescaled F aR (s ^ 2) hR
  set J' := rescaled J aR (s ^ 2) hR
  have hterm : ∀ ξ : ℚ, unitQuadraticAverage ξ * kernelTransform N F (-(ξ : ℝ)) *
      kernelTransform N J (ξ : ℝ) =
      ((N' : ℂ) / N) ^ 2 * (unitQuadraticAverage ξ *
        (fun η : ℚ => kernelTransform N' F' (-(η : ℝ)) * kernelTransform N' J' (η : ℝ))
          ((s ^ 2 : ℕ) * ξ)) := by
    intro ξ
    rw [kernelTransform_rescaled N N' hN' F aR (s ^ 2) hR hFR,
      kernelTransform_rescaled N N' hN' J aR (s ^ 2) hR hJR]
    have he : expPhase (-(aR : ℝ) * -(ξ : ℝ)) * expPhase (-(aR : ℝ) * (ξ : ℝ)) = 1 := by
      rw [← expPhase_add, show -(aR : ℝ) * -(ξ : ℝ) + -(aR : ℝ) * (ξ : ℝ) = ((0 : ℤ) : ℝ) by
        push_cast; ring, expPhase_int]
    have hA : ((s ^ 2 : ℕ) : ℝ) * -(ξ : ℝ) = -(((((s ^ 2 : ℕ) : ℚ) * ξ : ℚ)) : ℝ) := by
      push_cast; ring
    have hB : ((s ^ 2 : ℕ) : ℝ) * (ξ : ℝ) = ((((s ^ 2 : ℕ) : ℚ) * ξ : ℚ) : ℝ) := by
      push_cast; ring
    rw [hA, hB]
    beta_reduce
    calc _ = ((N' : ℂ) / N) ^ 2 *
          (expPhase (-(aR : ℝ) * -(ξ : ℝ)) * expPhase (-(aR : ℝ) * (ξ : ℝ))) *
          (unitQuadraticAverage ξ *
            (kernelTransform N' F' (-(((((s ^ 2 : ℕ) : ℚ) * ξ : ℚ)) : ℝ)) *
              kernelTransform N' J' ((((s ^ 2 : ℕ) : ℚ) * ξ : ℚ) : ℝ))) := by ring
      _ = _ := by rw [he, mul_one]
  have hper : ∀ (G : ℤ →₀ ℂ) (t : ℝ) (k : ℤ),
      kernelTransform N' G (t + (k : ℝ)) = kernelTransform N' G t := by
    intro G t k
    unfold kernelTransform
    congr 1
    apply sum_congr rfl
    intro n _
    rw [show -(n : ℝ) * (t + (k : ℝ)) = -(n : ℝ) * t + ((-(n * k)) : ℤ) by push_cast; ring,
      expPhase_add, expPhase_int, mul_one]
  simp_rw [hterm]
  rw [← mul_sum]
  rw [sum_frequencySet_mul_square H hH D s hs hsD
    (fun η : ℚ => kernelTransform N' F' (-(η : ℝ)) * kernelTransform N' J' (η : ℝ)) (by
      intro x k
      have h1 := hper F' (-(x : ℝ)) (-k)
      have h2 := hper J' (x : ℝ) k
      push_cast at h1 h2 ⊢
      rw [show -((x : ℝ) + (k : ℝ)) = -(x : ℝ) + -(k : ℝ) by ring, h1, h2])]
  rw [frequencySet_eq_of_rad H hDR hrad, hD]
  simp_rw [mul_assoc]
  push_cast
  ring

/-- Supports of the rescaled functions (`lem:record:nonunit-rescale`(a),(b)): for
`-R < a_R ≤ 0`, the function `F' = F(a_R + R ·)` is supported in `[1, ⌈N/R⌉]`; the order of
the supports is preserved, and no difference of the rescaled supports is a positive square
when no difference of the original supports is one (`R = s²`). -/
lemma rescaled_support (N R : ℕ) (hR : 0 < R) (F : ℤ →₀ ℂ) (aR : ℤ)
    (haR : -(R : ℤ) < aR ∧ aR ≤ 0) (hF : ∀ x ∈ F.support, 1 ≤ x ∧ x ≤ N) :
    ∀ n' ∈ (rescaled F aR R hR).support, 1 ≤ n' ∧ (n' : ℚ) ≤ ⌈(N : ℚ) / R⌉ := by
  intro n' hn'
  have hmem : aR + (R : ℤ) * n' ∈ F.support := by
    rw [Finsupp.mem_support_iff] at hn' ⊢
    exact hn'
  obtain ⟨h1, h2⟩ := hF _ hmem
  have hR' : (0 : ℤ) < R := by exact_mod_cast hR
  constructor
  · by_contra hlt
    push Not at hlt
    have : (R : ℤ) * n' ≤ 0 := by nlinarith
    omega
  · have hRq : (0 : ℚ) < R := by exact_mod_cast hR
    have h3 : ((R : ℤ) * n' : ℤ) ≤ (N : ℤ) + R - 1 := by omega
    have h4 : (n' : ℚ) < (N : ℚ) / R + 1 := by
      have h5 : ((R : ℚ) * n') ≤ (N : ℚ) + R - 1 := by exact_mod_cast h3
      rw [div_add_one hRq.ne', lt_div_iff₀ hRq]
      linarith
    have h6 := Int.le_ceil ((N : ℚ) / R)
    have h7 : (n' : ℚ) - 1 < ⌈(N : ℚ) / R⌉ := by linarith
    have h8 : n' - 1 < ⌈(N : ℚ) / R⌉ := by exact_mod_cast h7
    have h9 : n' ≤ ⌈(N : ℚ) / R⌉ := by omega
    exact_mod_cast h9

lemma rescaled_order (R : ℕ) (hR : 0 < R) (F J : ℤ →₀ ℂ) (aR : ℤ)
    (hord : ∀ x ∈ F.support, ∀ y ∈ J.support, x < y) :
    ∀ x' ∈ (rescaled F aR R hR).support, ∀ y' ∈ (rescaled J aR R hR).support, x' < y' := by
  intro x' hx' y' hy'
  have hx : aR + (R : ℤ) * x' ∈ F.support := by
    rw [Finsupp.mem_support_iff] at hx' ⊢; exact hx'
  have hy : aR + (R : ℤ) * y' ∈ J.support := by
    rw [Finsupp.mem_support_iff] at hy' ⊢; exact hy'
  have h := hord _ hx _ hy
  have hR' : (0 : ℤ) < R := by exact_mod_cast hR
  by_contra hle
  push Not at hle
  have : (R : ℤ) * y' ≤ (R : ℤ) * x' := mul_le_mul_of_nonneg_left hle hR'.le
  omega

lemma rescaled_no_square (s : ℕ) (hs : 0 < s) (F J : ℤ →₀ ℂ) (aR : ℤ)
    (hsq : ∀ x ∈ F.support, ∀ y ∈ J.support, ∀ m : ℕ, 1 ≤ m → y - x ≠ (m : ℤ) ^ 2) :
    ∀ x' ∈ (rescaled F aR (s ^ 2) (by positivity)).support,
      ∀ y' ∈ (rescaled J aR (s ^ 2) (by positivity)).support,
        ∀ m : ℕ, 1 ≤ m → y' - x' ≠ (m : ℤ) ^ 2 := by
  intro x' hx' y' hy' m hm he
  have hx : aR + ((s ^ 2 : ℕ) : ℤ) * x' ∈ F.support := by
    rw [Finsupp.mem_support_iff] at hx' ⊢; exact hx'
  have hy : aR + ((s ^ 2 : ℕ) : ℤ) * y' ∈ J.support := by
    rw [Finsupp.mem_support_iff] at hy' ⊢; exact hy'
  apply hsq _ hx _ hy (s * m) (Nat.one_le_iff_ne_zero.mpr (by positivity))
  push_cast
  have : (aR + (s : ℤ) ^ 2 * y') - (aR + (s : ℤ) ^ 2 * x') = (s : ℤ) ^ 2 * (y' - x') := by ring
  rw [this, he]
  ring

end Kernel

end Sarkozy
