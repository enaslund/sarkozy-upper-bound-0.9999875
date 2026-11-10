module

public import Sarkozy.Kernel.Rescale

@[expose] public section

/-!
# The divided class after rescaling is strict (`lem:record:nonunit-rescale`(a))

In the setting of `prop:record:kernel20`(ii), with the primes `P₁ ⊆ P₀` at which
`v_p(b - a) = 2 j_p ≥ 2` and `R = ∏_{p ∈ P₁} p^{2 j_p}`, the paper's
`lem:record:nonunit-rescale`(a) states: `R ∣ b - a`, `R ∣ d`, `D_R = 8 d_R` with `d_R = d/R`
odd, `D_R` and `D` have the same prime divisors, and `(b - a)/R` is a strict square class
modulo `D_R`. This module proves these claims (`dividedData_rescale`), with the exponents
`j_p` and unit parts `u_p` given explicitly (`DividedData`; `dividedData_of_isDivided` extracts
such data from the hypotheses `IsDividedSquareClass` of (ii)). Combined with `Rescale.lean`,
`prop_kernel20_ii_rescaling` is the whole of `lem:record:nonunit-rescale` in the setting of (ii):
the rescaled functions satisfy the hypotheses of part (i) at the modulus `D_R` and the length
`N' = ⌈N/R⌉`, with the parameter ranges of `rescaled_parameters`.

New material for this paper.
-/

namespace Sarkozy

namespace Kernel

open Finset

/-- Explicit data for `prop:record:kernel20`(ii): `P₁` is the set of primes of `P₀` at which
`b - a` is not a unit, with `v_p(8d) = 2 m_p`, `r ≡ p^{2 j_p} u_p mod p^{2 m_p}`,
`1 ≤ j_p < m_p`, `p ∤ u_p` and `u_p` a square modulo `p`; at the other primes of `d`, `r` is a
nonzero square; and `r ≡ 1 mod 8`. -/
structure DividedData (d : ℕ) (P₁ : Finset ℕ) (m j : ℕ → ℕ) (u : ℕ → ℤ) (r : ℤ) : Prop where
  prime : ∀ p ∈ P₁, p.Prime ∧ p ≠ 2
  exps : ∀ p ∈ P₁, 1 ≤ j p ∧ j p < m p ∧ (8 * d).factorization p = 2 * m p
  unit : ∀ p ∈ P₁, ¬ (p : ℤ) ∣ u p
  congr : ∀ p ∈ P₁, r ≡ (p : ℤ) ^ (2 * j p) * u p [ZMOD (p : ℤ) ^ (2 * m p)]
  square : ∀ p ∈ P₁, IsSquare (u p : ZMod p)
  outside : ∀ p : ℕ, p.Prime → p ∣ d → p ∉ P₁ → (r : ZMod p) ≠ 0 ∧ IsSquare (r : ZMod p)
  eight : r ≡ 1 [ZMOD 8]

/-- `R = ∏_{p ∈ P₁} p^{2 j_p}`. -/
def divisionSquare (P₁ : Finset ℕ) (j : ℕ → ℕ) : ℕ := ∏ p ∈ P₁, p ^ (2 * j p)

/-- Its square root `∏_{p ∈ P₁} p^{j_p}`. -/
def divisionRoot (P₁ : Finset ℕ) (j : ℕ → ℕ) : ℕ := ∏ p ∈ P₁, p ^ j p

lemma divisionSquare_eq (P₁ : Finset ℕ) (j : ℕ → ℕ) :
    divisionSquare P₁ j = divisionRoot P₁ j ^ 2 := by
  unfold divisionSquare divisionRoot
  rw [← prod_pow]
  apply prod_congr rfl
  intro p _
  ring

section

variable {d : ℕ} {P₁ : Finset ℕ} {m j : ℕ → ℕ} {u : ℕ → ℤ} {r : ℤ}

lemma DividedData.pairwise (h : DividedData d P₁ m j u r) :
    (P₁ : Set ℕ).Pairwise (fun p q => Nat.Coprime (p ^ (2 * j p)) (q ^ (2 * j q))) := by
  intro p hp q hq hpq
  apply Nat.Coprime.pow
  exact (Nat.coprime_primes (h.prime p hp).1 (h.prime q hq).1).mpr hpq

lemma DividedData.local_dvd_r (h : DividedData d P₁ m j u r) (p : ℕ) (hp : p ∈ P₁) :
    ((p ^ (2 * j p) : ℕ) : ℤ) ∣ r := by
  have hc := h.congr p hp
  obtain ⟨_, hjm, _⟩ := h.exps p hp
  have h1 : ((p : ℤ) ^ (2 * j p)) ∣ (p : ℤ) ^ (2 * m p) := pow_dvd_pow _ (by omega)
  have h2 : ((p : ℤ) ^ (2 * m p)) ∣ r - (p : ℤ) ^ (2 * j p) * u p := (Int.ModEq.dvd hc.symm)
  have h3 := h1.trans h2
  have h4 : ((p : ℤ) ^ (2 * j p)) ∣ (p : ℤ) ^ (2 * j p) * u p := dvd_mul_right _ _
  push_cast
  have := dvd_add h3 h4
  simpa using this

lemma DividedData.local_dvd_d (h : DividedData d P₁ m j u r) (hd : Odd d) (p : ℕ) (hp : p ∈ P₁) :
    p ^ (2 * j p) ∣ d := by
  obtain ⟨hpp, hp2⟩ := h.prime p hp
  obtain ⟨_, hjm, hfac⟩ := h.exps p hp
  have hd0 : d ≠ 0 := by rintro rfl; exact Nat.not_odd_zero hd
  have hfd : d.factorization p = 2 * m p := by
    rw [Nat.factorization_mul (by norm_num) hd0, Finsupp.add_apply] at hfac
    have h8 : (8 : ℕ).factorization p = 0 := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num, Nat.Prime.factorization_pow Nat.prime_two]
      simp [Ne.symm hp2]
    omega
  rw [hpp.pow_dvd_iff_le_factorization hd0, hfd]
  omega

/-- `R ∣ b - a` (`lem:record:nonunit-rescale`). -/
lemma DividedData.square_dvd_r (h : DividedData d P₁ m j u r) :
    ((divisionSquare P₁ j : ℕ) : ℤ) ∣ r := by
  unfold divisionSquare
  push_cast
  apply Finset.prod_dvd_of_coprime
  · intro p hp q hq hpq
    have := h.pairwise hp hq hpq
    have h' := Nat.isCoprime_iff_coprime.mpr this
    push_cast at h'
    exact h'
  · intro p hp
    have := h.local_dvd_r p hp
    push_cast at this
    exact this

/-- `R ∣ d`. -/
lemma DividedData.square_dvd_d (h : DividedData d P₁ m j u r) (hd : Odd d) :
    divisionSquare P₁ j ∣ d := by
  unfold divisionSquare
  apply nat_pairwise_coprime_prod_dvd
  · intro p hp q hq hpq; exact h.pairwise hp hq hpq
  · intro p hp; exact h.local_dvd_d hd p hp

lemma divisionRoot_odd (h : DividedData d P₁ m j u r) : Odd (divisionRoot P₁ j) := by
  unfold divisionRoot
  apply Finset.prod_induction _ Odd
  · intro x y hx hy; exact hx.mul hy
  · exact odd_one
  · intro p hp
    obtain ⟨hpp, hp2⟩ := h.prime p hp
    exact (hpp.odd_of_ne_two hp2).pow

lemma divisionSquare_eq_mul (P₁ : Finset ℕ) (j : ℕ → ℕ) (p : ℕ) (hp : p ∈ P₁) :
    divisionSquare P₁ j = p ^ (2 * j p) * divisionSquare (P₁.erase p) j := by
  unfold divisionSquare
  rw [← mul_prod_erase P₁ (fun q => q ^ (2 * j q)) hp]

lemma isSquare_zmod_of_root (p : ℕ) [Fact p.Prime] (root : ℕ) (hroot : ¬ p ∣ root) :
    ((root ^ 2 : ℕ) : ZMod p) ≠ 0 ∧ IsSquare ((root ^ 2 : ℕ) : ZMod p) := by
  have hr : ((root : ℕ) : ZMod p) ≠ 0 := by
    intro h0
    exact hroot ((ZMod.natCast_eq_zero_iff root p).mp h0)
  push_cast
  exact ⟨pow_ne_zero 2 hr, ⟨(root : ZMod p), by ring⟩⟩

/-- Quotients of nonzero squares in `ZMod p` are nonzero squares. -/
lemma isSquare_div (p : ℕ) [Fact p.Prime] (x y : ZMod p) (hx : x ≠ 0 ∧ IsSquare x)
    (hy : y ≠ 0 ∧ IsSquare y) : x * y⁻¹ ≠ 0 ∧ IsSquare (x * y⁻¹) := by
  obtain ⟨a, ha⟩ := hx.2
  obtain ⟨c, hc⟩ := hy.2
  have hc0 : c ≠ 0 := by rintro rfl; apply hy.1; rw [hc]; ring
  refine ⟨mul_ne_zero hx.1 (inv_ne_zero hy.1), ⟨a * c⁻¹, ?_⟩⟩
  rw [ha, hc]
  field_simp

/-- **`lem:record:nonunit-rescale`(a), arithmetic part**: in the setting of
`prop:record:kernel20`(ii), with `R = ∏_{p ∈ P₁} p^{2 j_p}`, one has `R ∣ b - a`, `R ∣ d`,
`d/R` odd, every prime of `d` divides `d/R` (so `D_R = 8 d/R` and `D = 8d` have the same prime
divisors), and `(b - a)/R` is a strict square class modulo `D_R`. -/
theorem dividedData_rescale (hd : Odd d) (h : DividedData d P₁ m j u r) :
    ((divisionSquare P₁ j : ℕ) : ℤ) ∣ r ∧ divisionSquare P₁ j ∣ d ∧
      Odd (d / divisionSquare P₁ j) ∧
      (∀ p : ℕ, p.Prime → p ∣ d → p ∣ d / divisionSquare P₁ j) ∧
      IsStrictSquareClass (d / divisionSquare P₁ j) (r / (divisionSquare P₁ j : ℤ)) := by
  classical
  have hRr := h.square_dvd_r
  have hRd := h.square_dvd_d hd
  set R := divisionSquare P₁ j with hRdef
  have hd0 : d ≠ 0 := by rintro rfl; exact Nat.not_odd_zero hd
  have hR0 : 0 < R := Nat.pos_of_ne_zero (fun h0 => by rw [h0, zero_dvd_iff] at hRd; exact hd0 hRd)
  obtain ⟨dR, hdR⟩ := hRd
  obtain ⟨r', hr'⟩ := hRr
  have hdRe : d / R = dR := by rw [hdR, Nat.mul_div_cancel_left _ hR0]
  have hr'e : r / (R : ℤ) = r' := by
    rw [hr', Int.mul_ediv_cancel_left _ (by exact_mod_cast hR0.ne')]
  rw [hdRe, hr'e]
  have hRroot : R = divisionRoot P₁ j ^ 2 := divisionSquare_eq P₁ j
  have hodd_root := divisionRoot_odd h
  -- the primes of `R` are the primes of `P₁`
  have hprimeR : ∀ p : ℕ, p.Prime → p ∣ R → p ∈ P₁ := by
    intro p hp hpR
    rw [hRdef] at hpR
    unfold divisionSquare at hpR
    obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hpR
    have := (Nat.prime_dvd_prime_iff_eq hp (h.prime q hq).1).mp (hp.dvd_of_dvd_pow hpq)
    rw [this]; exact hq
  refine ⟨⟨r', hr'⟩, ⟨dR, hdR⟩, ?_, ?_, ?_⟩
  · -- `d / R` is odd
    rw [hdR] at hd
    exact (Nat.odd_mul.mp hd).2
  · -- same primes
    intro p hp hpd
    by_cases hpP : p ∈ P₁
    · obtain ⟨hpp, _⟩ := h.prime p hpP
      obtain ⟨_, hjm, hfac⟩ := h.exps p hpP
      have hfd : d.factorization p = 2 * m p := by
        rw [Nat.factorization_mul (by norm_num) hd0, Finsupp.add_apply] at hfac
        have h8 : (8 : ℕ).factorization p = 0 := by
          rw [show (8 : ℕ) = 2 ^ 3 by norm_num, Nat.Prime.factorization_pow Nat.prime_two]
          simp [Ne.symm (h.prime p hpP).2]
        omega
      have hR' := divisionSquare_eq_mul P₁ j p hpP
      have hfR : R.factorization p = 2 * j p := by
        rw [hRdef, hR', Nat.factorization_mul (pow_ne_zero _ hpp.ne_zero) (by
          unfold divisionSquare
          exact Finset.prod_ne_zero_iff.mpr (fun q hq => pow_ne_zero _ (h.prime q (mem_of_mem_erase hq)).1.ne_zero)),
          Finsupp.add_apply, hpp.factorization_pow, Finsupp.single_eq_same]
        have : (divisionSquare (P₁.erase p) j).factorization p = 0 := by
          apply Nat.factorization_eq_zero_of_not_dvd
          intro hdvd
          unfold divisionSquare at hdvd
          obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).mp hdvd
          have hqP := mem_of_mem_erase hq
          have := (Nat.prime_dvd_prime_iff_eq hpp (h.prime q hqP).1).mp (hpp.dvd_of_dvd_pow hpq)
          exact (ne_of_mem_erase hq) this.symm
        omega
      have hdR0 : dR ≠ 0 := by rintro rfl; rw [mul_zero] at hdR; exact hd0 hdR
      have hfdR : dR.factorization p = 2 * m p - 2 * j p := by
        have := congrArg (fun n => n.factorization p) hdR
        rw [Nat.factorization_mul hR0.ne' hdR0, Finsupp.add_apply, hfR, hfd] at this
        omega
      rw [hpp.dvd_iff_one_le_factorization hdR0, hfdR]
      omega
    · have hpR : ¬ p ∣ R := fun hpR => hpP (hprimeR p hp hpR)
      rw [hdR] at hpd
      exact (Nat.Coprime.dvd_of_dvd_mul_left ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpR) hpd)
  · refine ⟨?_, ?_⟩
    · -- `r' ≡ 1 mod 8`
      have hR8 : (R : ℤ) ≡ 1 [ZMOD 8] := by
        have h1 := Int.eight_dvd_sq_sub_one_of_odd (show Odd ((divisionRoot P₁ j : ℕ) : ℤ) by
          exact_mod_cast hodd_root)
        rw [hRroot]
        push_cast
        exact (Int.modEq_iff_dvd.mpr h1).symm
      have h8 := h.eight
      rw [hr'] at h8
      have : (R : ℤ) * r' ≡ 1 * r' [ZMOD 8] := hR8.mul_right r'
      rw [one_mul] at this
      exact this.symm.trans h8
    · intro p hp hpdR
      have : Fact p.Prime := ⟨hp⟩
      by_cases hpP : p ∈ P₁
      · -- at the divided primes: `R_p r' ≡ u_p mod p`
        obtain ⟨_, hjm, _⟩ := h.exps p hpP
        have hc := h.congr p hpP
        have hR' := divisionSquare_eq_mul P₁ j p hpP
        set Rp := divisionSquare (P₁.erase p) j with hRp
        have hkey : (p : ℤ) ^ (2 * m p - 2 * j p) ∣ (Rp : ℤ) * r' - u p := by
          obtain ⟨k, hk⟩ := (Int.ModEq.dvd hc.symm)
          -- r - p^{2j} u = p^{2m} k
          refine ⟨k, ?_⟩
          have hpj : ((p : ℤ) ^ (2 * j p)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
          apply mul_left_cancel₀ hpj
          have e1 : (p : ℤ) ^ (2 * m p) = (p : ℤ) ^ (2 * j p) * (p : ℤ) ^ (2 * m p - 2 * j p) := by
            rw [← pow_add]; congr 1; omega
          rw [hr', hRdef, hR'] at hk
          push_cast at hk
          rw [e1] at hk
          linear_combination hk
        have hmod : ((Rp : ZMod p)) * (r' : ZMod p) = (u p : ZMod p) := by
          have h1 : (p : ℤ) ∣ (Rp : ℤ) * r' - u p :=
            (dvd_pow_self (p : ℤ) (by omega : 2 * m p - 2 * j p ≠ 0)).trans hkey
          have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h1
          push_cast at this
          exact sub_eq_zero.mp this
        have hu0 : (u p : ZMod p) ≠ 0 := fun h0 =>
          h.unit p hpP ((ZMod.intCast_zmod_eq_zero_iff_dvd (u p) p).mp h0)
        have hRpsq : ((Rp : ℕ) : ZMod p) ≠ 0 ∧ IsSquare ((Rp : ℕ) : ZMod p) := by
          have hRproot : Rp = divisionRoot (P₁.erase p) j ^ 2 := divisionSquare_eq _ j
          rw [hRproot]
          apply isSquare_zmod_of_root
          intro hdvd
          unfold divisionRoot at hdvd
          obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hdvd
          have hqP := mem_of_mem_erase hq
          have := (Nat.prime_dvd_prime_iff_eq hp (h.prime q hqP).1).mp (hp.dvd_of_dvd_pow hpq)
          exact (ne_of_mem_erase hq) this.symm
        have hr'eq : (r' : ZMod p) = (u p : ZMod p) * ((Rp : ℕ) : ZMod p)⁻¹ := by
          rw [← hmod]
          field_simp [hRpsq.1]
        rw [hr'eq]
        exact isSquare_div p _ _ ⟨hu0, h.square p hpP⟩ hRpsq
      · -- at the other primes: `r ≡ R r'` with `R` a nonzero square
        have hpd : p ∣ d := by rw [hdR]; exact dvd_mul_of_dvd_right hpdR _
        have hout := h.outside p hp hpd hpP
        have hRsq : ((R : ℕ) : ZMod p) ≠ 0 ∧ IsSquare ((R : ℕ) : ZMod p) := by
          rw [hRroot]
          apply isSquare_zmod_of_root
          intro hdvd
          exact hpP (hprimeR p hp (by rw [hRroot]; exact dvd_pow hdvd two_ne_zero))
        have hr'eq : (r' : ZMod p) = (r : ZMod p) * ((R : ℕ) : ZMod p)⁻¹ := by
          rw [hr']
          push_cast
          field_simp [hRsq.1]
        rw [hr'eq]
        exact isSquare_div p _ _ hout hRsq

/-! ## The rescaled functions satisfy the hypotheses of part (i) -/

lemma rescaled_mem_support {F : ℤ →₀ ℂ} {aR : ℤ} {R : ℕ} {hR : 0 < R} {n' : ℤ}
    (h : n' ∈ (rescaled F aR R hR).support) : aR + (R : ℤ) * n' ∈ F.support := by
  rw [Finsupp.mem_support_iff] at h ⊢; exact h

lemma rescaled_class (R DR : ℕ) (hR : 0 < R) (D : ℕ) (hD : D = R * DR) (F : ℤ →₀ ℂ) (a aR : ℤ)
    (haR : aR ≡ a [ZMOD (R : ℤ)]) (hF : ∀ x ∈ F.support, x ≡ a [ZMOD (D : ℤ)]) :
    ∀ n' ∈ (rescaled F aR R hR).support, n' ≡ (a - aR) / R [ZMOD (DR : ℤ)] := by
  intro n' hn'
  have hx := hF _ (rescaled_mem_support hn')
  obtain ⟨t, ht⟩ := Int.ModEq.dvd haR
  -- a - aR = R * t
  have hdiv : (a - aR) / R = t := by
    rw [ht, Int.mul_ediv_cancel_left _ (by exact_mod_cast hR.ne')]
  rw [hdiv]
  obtain ⟨k, hk⟩ := Int.ModEq.dvd hx.symm
  -- aR + R n' - a = D k = R DR k
  apply Int.ModEq.symm
  apply (Int.modEq_iff_dvd).mpr
  refine ⟨k, ?_⟩
  have hR' : (R : ℤ) ≠ 0 := by exact_mod_cast hR.ne'
  apply mul_left_cancel₀ hR'
  rw [hD] at hk
  push_cast at hk
  linear_combination hk + ht

lemma rescaled_l2norm (F : ℤ →₀ ℂ) (aR : ℤ) (R : ℕ) (hR : 0 < R)
    (hF : ∀ x ∈ F.support, x ≡ aR [ZMOD (R : ℤ)]) : l2norm (rescaled F aR R hR) = l2norm F := by
  unfold l2norm rescaled
  congr 1
  rw [Finsupp.comapDomain_support]
  apply Finset.sum_preimage (fun n' : ℤ => aR + (R : ℤ) * n') F.support
    ((affine_injective aR R hR).injOn) (fun n => ‖F n‖ ^ 2)
  intro x hx hxr
  exfalso
  apply hxr
  obtain ⟨k, hk⟩ := (Int.ModEq.dvd (hF x hx).symm)
  exact ⟨k, by simp only; linarith⟩

/-- **`lem:record:nonunit-rescale` in the setting of `prop:record:kernel20`(ii).** With
`R = ∏_{p ∈ P₁} p^{2 j_p}`, `D_R = 8 (d/R)`, `N' = ⌈N/R⌉`, `a_R ∈ (-R, 0]`, `a_R ≡ a mod R` and
`F' = F(a_R + R ·)`, `J' = J(a_R + R ·)`:
the pairing at `(D, N, F, J)` equals `R (N'/N)²` times the pairing at `(D_R, N', F', J')`
(part (d)); `F', J'` are supported in `[1, N']`, in the classes `(a - a_R)/R`, `(b - a_R)/R`
modulo `D_R`, keep their `ℓ²` norms, keep the order of the supports and the absence of square
differences, and their class difference `(b - a)/R` is a strict square class modulo `D_R`
(parts (a), (b)). So part (i) applies to `(D_R, N', F', J')`. -/
theorem prop_kernel20_ii_rescaling (d : ℕ) (hd : Odd d) (P₁ : Finset ℕ) (m j : ℕ → ℕ)
    (u : ℕ → ℤ) (a b : ℤ) (hdiv : DividedData d P₁ m j u (b - a)) (N : ℕ) (hN : 0 < N)
    (H : ℝ) (hH : 0 ≤ H) (aR : ℤ)
    (haR1 : -((divisionSquare P₁ j : ℕ) : ℤ) < aR ∧ aR ≤ 0)
    (haR2 : aR ≡ a [ZMOD ((divisionSquare P₁ j : ℕ) : ℤ)])
    (F J : ℤ →₀ ℂ)
    (hF : ∀ x ∈ F.support, 1 ≤ x ∧ x ≤ N ∧ x ≡ a [ZMOD ((8 * d : ℕ) : ℤ)])
    (hJ : ∀ y ∈ J.support, 1 ≤ y ∧ y ≤ N ∧ y ≡ b [ZMOD ((8 * d : ℕ) : ℤ)])
    (hord : ∀ x ∈ F.support, ∀ y ∈ J.support, x < y)
    (hsq : ∀ x ∈ F.support, ∀ y ∈ J.support, ∀ m : ℕ, 1 ≤ m → y - x ≠ (m : ℤ) ^ 2) :
    let R := divisionSquare P₁ j
    let N' := ⌈(N : ℚ) / R⌉₊
    let F' := rescaled F aR (divisionRoot P₁ j ^ 2) (by
      have := (divisionRoot_odd hdiv).pos; positivity)
    let J' := rescaled J aR (divisionRoot P₁ j ^ 2) (by
      have := (divisionRoot_odd hdiv).pos; positivity)
    ((8 * d : ℕ) : ℂ) * ∑ ξ ∈ frequencySet H (8 * d),
        unitQuadraticAverage ξ * kernelTransform N F (-(ξ : ℝ)) * kernelTransform N J (ξ : ℝ) =
      (R : ℂ) * ((N' : ℂ) / N) ^ 2 *
        (((8 * (d / R) : ℕ) : ℂ) * ∑ ξ ∈ frequencySet H (8 * (d / R)),
          unitQuadraticAverage ξ * kernelTransform N' F' (-(ξ : ℝ)) *
            kernelTransform N' J' (ξ : ℝ)) ∧
      (∀ x ∈ F'.support, 1 ≤ x ∧ x ≤ N' ∧ x ≡ (a - aR) / R [ZMOD ((8 * (d / R) : ℕ) : ℤ)]) ∧
      (∀ y ∈ J'.support, 1 ≤ y ∧ y ≤ N' ∧ y ≡ (b - aR) / R [ZMOD ((8 * (d / R) : ℕ) : ℤ)]) ∧
      (∀ x ∈ F'.support, ∀ y ∈ J'.support, x < y) ∧
      (∀ x ∈ F'.support, ∀ y ∈ J'.support, ∀ m : ℕ, 1 ≤ m → y - x ≠ (m : ℤ) ^ 2) ∧
      Odd (d / R) ∧ IsStrictSquareClass (d / R) ((b - aR) / R - (a - aR) / R) ∧
      l2norm F' = l2norm F ∧ l2norm J' = l2norm J := by
  intro R N' F' J'
  obtain ⟨hRr, hRd, hodd, hrad, hstrict⟩ := dividedData_rescale hd hdiv
  have hRroot : R = divisionRoot P₁ j ^ 2 := divisionSquare_eq P₁ j
  have hs : 0 < divisionRoot P₁ j := (divisionRoot_odd hdiv).pos
  have hR0 : 0 < R := by rw [hRroot]; positivity
  have hRs : ((divisionRoot P₁ j ^ 2 : ℕ) : ℤ) = (R : ℤ) := by rw [hRroot]
  obtain ⟨dR, hdR⟩ := hRd
  have hdRe : d / R = dR := by rw [hdR, Nat.mul_div_cancel_left _ hR0]
  have hD : 8 * d = divisionRoot P₁ j ^ 2 * (8 * (d / R)) := by
    rw [hdRe, ← hRroot, hdR]; ring
  -- a ≡ b mod R
  have haR2' : aR ≡ a [ZMOD ((divisionRoot P₁ j ^ 2 : ℕ) : ℤ)] := by rw [hRs]; exact haR2
  have hab : ((divisionRoot P₁ j ^ 2 : ℕ) : ℤ) ∣ b - a := by rw [hRs]; exact hRr
  have hbR : aR ≡ b [ZMOD (R : ℤ)] :=
    haR2.trans (Int.modEq_iff_dvd.mpr hRr)
  -- the radical condition
  have hrad8 : ∀ p : ℕ, p.Prime → p ∣ 8 * d → p ∣ 8 * (d / R) := by
    intro p hp hpd
    rcases (Nat.Prime.dvd_mul hp).mp hpd with h8 | hpd'
    · exact dvd_mul_of_dvd_left h8 _
    · exact dvd_mul_of_dvd_right (hrad p hp hpd') _
  have hN'pos : 0 < N' := by
    apply Nat.ceil_pos.mpr
    have : (0 : ℚ) < N := by exact_mod_cast hN
    positivity
  have hFR : ∀ x ∈ F.support, x ≡ aR [ZMOD (R : ℤ)] := by
    intro x hx
    have h1 : x ≡ a [ZMOD (R : ℤ)] := (hF x hx).2.2.of_dvd (by
      rw [hdR]; push_cast; exact Dvd.intro (8 * (dR : ℤ)) (by ring))
    exact h1.trans haR2.symm
  have hJR : ∀ y ∈ J.support, y ≡ aR [ZMOD (R : ℤ)] := by
    intro y hy
    have h1 : y ≡ b [ZMOD (R : ℤ)] := (hJ y hy).2.2.of_dvd (by
      rw [hdR]; push_cast; exact Dvd.intro (8 * (dR : ℤ)) (by ring))
    exact h1.trans hbR.symm
  have hceil : ∀ n' : ℤ, (n' : ℚ) ≤ ⌈(N : ℚ) / R⌉ → n' ≤ N' := by
    intro n' hn'
    have h1 : ((N' : ℕ) : ℤ) = ⌈(N : ℚ) / R⌉ := Int.natCast_ceil_eq_ceil (by positivity)
    have h2 : n' ≤ ⌈(N : ℚ) / R⌉ := by exact_mod_cast hn'
    omega
  have hsuppF := rescaled_support N (divisionRoot P₁ j ^ 2) (by positivity) F aR
    (by rw [hRs]; exact haR1) (fun x hx => ⟨(hF x hx).1, (hF x hx).2.1⟩)
  have hsuppJ := rescaled_support N (divisionRoot P₁ j ^ 2) (by positivity) J aR
    (by rw [hRs]; exact haR1) (fun y hy => ⟨(hJ y hy).1, (hJ y hy).2.1⟩)
  refine ⟨?_, ?_, ?_, ?_, ?_, hodd, ?_, ?_, ?_⟩
  · -- the identity (d)
    have hid := nonunit_rescale_identity N N' hN'pos H hH (8 * d) (8 * (d / R)) (divisionRoot P₁ j)
      hs hD hrad8 a b aR hab haR2' F J (fun x hx => (hF x hx).2.2) (fun y hy => (hJ y hy).2.2)
    rw [hid, hRroot]
  · intro x hx
    obtain ⟨h1, h2⟩ := hsuppF x hx
    refine ⟨h1, hceil x (by rw [← hRroot] at h2; exact h2), ?_⟩
    have := rescaled_class (divisionRoot P₁ j ^ 2) (8 * (d / R)) (by positivity) (8 * d) hD F a aR
      haR2' (fun x hx => (hF x hx).2.2) x hx
    rw [hRs] at this
    exact this
  · intro y hy
    obtain ⟨h1, h2⟩ := hsuppJ y hy
    refine ⟨h1, hceil y (by rw [← hRroot] at h2; exact h2), ?_⟩
    have := rescaled_class (divisionRoot P₁ j ^ 2) (8 * (d / R)) (by positivity) (8 * d) hD J b aR
      (by rw [hRs]; exact hbR) (fun y hy => (hJ y hy).2.2) y hy
    rw [hRs] at this
    exact this
  · exact rescaled_order _ _ F J aR hord
  · exact rescaled_no_square _ hs F J aR hsq
  · -- the class difference is `(b - a)/R`
    obtain ⟨t₁, ht₁⟩ := Int.ModEq.dvd haR2
    obtain ⟨t₂, ht₂⟩ := Int.ModEq.dvd hbR
    obtain ⟨t, ht⟩ := hRr
    have hR' : (R : ℤ) ≠ 0 := by exact_mod_cast hR0.ne'
    have e1 : (a - aR) / R = t₁ := by rw [ht₁, Int.mul_ediv_cancel_left _ hR']
    have e2 : (b - aR) / R = t₂ := by rw [ht₂, Int.mul_ediv_cancel_left _ hR']
    have e3 : (b - a) / R = t := by rw [ht, Int.mul_ediv_cancel_left _ hR']
    have ht₁' : a - aR = (R : ℤ) * t₁ := ht₁
    have ht' : b - a = (R : ℤ) * t := ht
    have e4 : t₂ - t₁ = t := by
      apply mul_left_cancel₀ hR'
      linear_combination ht₁' + ht' - ht₂
    rw [e1, e2, e4, ← e3]
    exact hstrict
  · exact rescaled_l2norm F aR _ (by positivity) (by rw [hRs]; exact hFR)
  · exact rescaled_l2norm J aR _ (by positivity) (by rw [hRs]; exact hJR)

/-- The parameter ranges of `prop:record:kernel20`(ii)'s remark: after division by `R ≥ 1` and
passage to the length `N' = ⌈N/R⌉`, the modulus `D_R = 8 (d/R)` and the cutoff `H` satisfy the
hypotheses of part (i) with the constants `C_D R^κ` and `C_H R^{β/2}`. -/
lemma rescaled_parameters (κ β CD CH : ℝ) (hκ : 0 ≤ κ) (hβ : 0 ≤ β) (hCH : 0 < CH)
    (N d R : ℕ) (hN : 0 < N) (hR : 0 < R) (H : ℝ)
    (hD : ((8 * d : ℕ) : ℝ) ≤ CD * (N : ℝ) ^ κ)
    (hH1 : CH⁻¹ * (N : ℝ) ^ (β / 2) ≤ H) (hH2 : H ≤ CH * (N : ℝ) ^ (β / 2)) :
    ((8 * (d / R) : ℕ) : ℝ) ≤ (CD * (R : ℝ) ^ κ) * ((⌈(N : ℚ) / R⌉₊ : ℕ) : ℝ) ^ κ ∧
      (CH * (R : ℝ) ^ (β / 2))⁻¹ * ((⌈(N : ℚ) / R⌉₊ : ℕ) : ℝ) ^ (β / 2) ≤ H ∧
      H ≤ (CH * (R : ℝ) ^ (β / 2)) * ((⌈(N : ℚ) / R⌉₊ : ℕ) : ℝ) ^ (β / 2) := by
  set N' := ⌈(N : ℚ) / R⌉₊ with hN'
  have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNRN' : (N : ℝ) ≤ (R : ℝ) * N' := by
    have h1 : (N : ℚ) / R ≤ N' := Nat.le_ceil _
    have h2 : (N : ℚ) ≤ (R : ℚ) * N' := by
      have hRq : (0 : ℚ) < R := by exact_mod_cast hR
      rw [div_le_iff₀ hRq] at h1
      linarith
    exact_mod_cast h2
  have hN'N : (N' : ℝ) ≤ (R : ℝ) * N := by
    have h1 : N' ≤ N := by
      apply Nat.ceil_le.mpr
      have hRq : (1 : ℚ) ≤ R := by exact_mod_cast hR
      have hNq : (0 : ℚ) ≤ N := by positivity
      exact div_le_self hNq hRq
    have : (N' : ℝ) ≤ N := by exact_mod_cast h1
    nlinarith
  have hN'0 : (0 : ℝ) ≤ N' := Nat.cast_nonneg _
  have hmul : ∀ e : ℝ, 0 ≤ e → (N : ℝ) ^ e ≤ (R : ℝ) ^ e * (N' : ℝ) ^ e := by
    intro e he
    rw [← Real.mul_rpow (by positivity) hN'0]
    exact Real.rpow_le_rpow hNr.le hNRN' he
  refine ⟨?_, ?_, ?_⟩
  · have h1 : ((8 * (d / R) : ℕ) : ℝ) ≤ ((8 * d : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_left 8 (Nat.div_le_self d R)
    have hCD : 0 ≤ CD := by
      have : (0 : ℝ) ≤ ((8 * d : ℕ) : ℝ) := Nat.cast_nonneg _
      by_contra hneg
      push Not at hneg
      have h2 : CD * (N : ℝ) ^ κ < 0 := mul_neg_of_neg_of_pos hneg (by positivity)
      linarith
    calc ((8 * (d / R) : ℕ) : ℝ) ≤ CD * (N : ℝ) ^ κ := h1.trans hD
      _ ≤ CD * ((R : ℝ) ^ κ * (N' : ℝ) ^ κ) := mul_le_mul_of_nonneg_left (hmul κ hκ) hCD
      _ = _ := by ring
  · have h1 : (N' : ℝ) ^ (β / 2) ≤ (R : ℝ) ^ (β / 2) * (N : ℝ) ^ (β / 2) := by
      rw [← Real.mul_rpow (by positivity) hNr.le]
      exact Real.rpow_le_rpow hN'0 hN'N (by linarith)
    have hRb : 0 < (R : ℝ) ^ (β / 2) := by positivity
    calc (CH * (R : ℝ) ^ (β / 2))⁻¹ * (N' : ℝ) ^ (β / 2)
        ≤ (CH * (R : ℝ) ^ (β / 2))⁻¹ * ((R : ℝ) ^ (β / 2) * (N : ℝ) ^ (β / 2)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = CH⁻¹ * (N : ℝ) ^ (β / 2) := by field_simp
      _ ≤ H := hH1
  · calc H ≤ CH * (N : ℝ) ^ (β / 2) := hH2
      _ ≤ CH * ((R : ℝ) ^ (β / 2) * (N' : ℝ) ^ (β / 2)) :=
          mul_le_mul_of_nonneg_left (hmul (β / 2) (by linarith)) hCH.le
      _ = _ := by ring

/-- The hypotheses `IsDividedSquareClass` of (ii) provide explicit data `DividedData`: `P₁` is
the set of primes of `P₀` dividing `b - a`, with the exponents and unit parts chosen from the
existential statements. -/
theorem dividedData_of_isDivided (d : ℕ) (P₀ : Finset ℕ) (m : ℕ → ℕ) (r : ℤ)
    (h : IsDividedSquareClass d P₀ m r) :
    ∃ (P₁ : Finset ℕ) (j : ℕ → ℕ) (u : ℕ → ℤ), P₁ ⊆ P₀ ∧ DividedData d P₁ m j u r := by
  classical
  obtain ⟨hP₀, h8, hout, hin⟩ := h
  set P₁ := P₀.filter (fun p => (r : ZMod p) = 0) with hP₁
  have hex : ∀ p ∈ P₁, ∃ j : ℕ, 1 ≤ j ∧ j < m p ∧ ∃ u : ℤ, ¬ (p : ℤ) ∣ u ∧
      r ≡ (p : ℤ) ^ (2 * j) * u [ZMOD (p : ℤ) ^ (2 * m p)] ∧ IsSquare (u : ZMod p) := by
    intro p hp
    rw [hP₁, mem_filter] at hp
    rcases hin p hp.1 with ⟨hr0, _⟩ | hnon
    · exact absurd hp.2 hr0
    · exact hnon
  let j : ℕ → ℕ := fun p => if hp : p ∈ P₁ then Classical.choose (hex p hp) else 0
  let u : ℕ → ℤ := fun p => if hp : p ∈ P₁ then
    Classical.choose (Classical.choose_spec (hex p hp)).2.2 else 0
  have hj : ∀ p (hp : p ∈ P₁), j p = Classical.choose (hex p hp) := by
    intro p hp; simp only [j, dite_eq_left hp]
  have hu : ∀ p (hp : p ∈ P₁), u p = Classical.choose (Classical.choose_spec (hex p hp)).2.2 := by
    intro p hp; simp only [u, dite_eq_left hp]
  have hspec : ∀ p ∈ P₁, 1 ≤ j p ∧ j p < m p ∧ ¬ (p : ℤ) ∣ u p ∧
      r ≡ (p : ℤ) ^ (2 * j p) * u p [ZMOD (p : ℤ) ^ (2 * m p)] ∧ IsSquare (u p : ZMod p) := by
    intro p hp
    have h1 := Classical.choose_spec (hex p hp)
    have h2 := Classical.choose_spec h1.2.2
    rw [hj p hp, hu p hp]
    exact ⟨h1.1, h1.2.1, h2.1, h2.2.1, h2.2.2⟩
  refine ⟨P₁, j, u, filter_subset _ _, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h8⟩
  · intro p hp
    have := hP₀ p (mem_filter.mp hp).1
    exact ⟨this.1, this.2.1⟩
  · intro p hp
    have := hP₀ p (mem_filter.mp hp).1
    exact ⟨(hspec p hp).1, (hspec p hp).2.1, this.2.2.2⟩
  · intro p hp; exact (hspec p hp).2.2.1
  · intro p hp; exact (hspec p hp).2.2.2.1
  · intro p hp; exact (hspec p hp).2.2.2.2
  · intro p hp hpd hpP₁
    by_cases hpP₀ : p ∈ P₀
    · have hr0 : (r : ZMod p) ≠ 0 := by
        intro h0
        exact hpP₁ (mem_filter.mpr ⟨hpP₀, h0⟩)
      rcases hin p hpP₀ with hunit | ⟨jj, hj1, hjm, uu, _, hc, _⟩
      · exact hunit
      · exfalso
        apply hr0
        have h1 : (p : ℤ) ∣ (p : ℤ) ^ (2 * m p) := dvd_pow_self _ (by omega)
        have h2 : (p : ℤ) ∣ r - (p : ℤ) ^ (2 * jj) * uu := h1.trans (Int.ModEq.dvd hc.symm)
        have h3 : (p : ℤ) ∣ (p : ℤ) ^ (2 * jj) * uu :=
          (dvd_pow_self _ (by omega)).mul_right _
        have h4 : (p : ℤ) ∣ r := by
          have := dvd_add h2 h3
          simpa using this
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd r p).mpr h4
    · exact hout p hp hpd hpP₀

end

end Kernel

end Sarkozy
