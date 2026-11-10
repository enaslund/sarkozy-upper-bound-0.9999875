module

public import Sarkozy.Kernel.DualCoordinates
public import Sarkozy.Kernel.RatesTwentieth
public import Sarkozy.Kernel.CoefficientIdentity
public import Sarkozy.Kernel.RootDatum

@[expose] public section

/-!
# The actual-square kernel estimate at `β = 1/20` (squarefree odd part)

This module proves the pairing bound `eq:record:K20` of the paper's
`prop:record:kernel20`(i) at the triple of `cor:kernel20`, in the special case
`D = 8d` with `d` odd **and squarefree**:
for `F, J` supported in `[1,N]`, in residue classes `a, b mod D`, with every
point of `supp F` below every point of `supp J`, no difference a positive square,
and `b - a` a strict square class,
`|D ∑_{ξ ∈ Ξ_{H,D}} g(ξ) F̂(-ξ) Ĵ(ξ)| ≤ C N^(-1/120) ‖F‖₂ ‖J‖₂ / N`.

Notation (`def:kernel-notation`): `F̂(ξ) = N⁻¹ ∑_n F(n) e(-nξ)` (`kernelTransform`),
`g` the unit quadratic average (`unitQuadraticAverage`), `Ξ_{H,D}` the frequencies of
squarefree denominator `≤ H` coprime to `D` (`frequencySet`), `e(t) = exp(2πit)`
(`expPhase`, see `expPhase_eq_exp`).

Proof structure (Appendix C): the actual kernel supported on the squares has zero
pairing (`B_k = 0`); the model kernel's pairing is the paper's expression
(`model_sum_reindex` and the phase computation `pairing_phase`); Plancherel on a
cyclic group (`ordered_square_kernel_bilinear_l2`, adapted from upstream
`ordered_square_kernel_bilinear` of `DualCoordinates.lean`) bounds their
difference by the sup norm of the transform difference, which is
`actual_kernel_rate_twentieth`.

The prime family is the set of all primes `≤ N`; the root classes are `m ≡ 1 mod 2`
and `m ≡ c_p mod p` with `c_p² ≡ b - a` for `p ∣ d`, as in the upstream (OpenAI)
construction for squarefree moduli.
-/

namespace Sarkozy

section
open Finset
open scoped ComplexConjugate BigOperators
namespace Kernel

/-! ## Notation of the paper -/

lemma expPhase_eq_exp (t : ℝ) : expPhase t = Complex.exp (2 * Real.pi * Complex.I * t) := by
  unfold expPhase
  rw [Real.fourierChar_apply]
  congr 1
  push_cast
  ring

/-- The normalized Fourier transform of `def:kernel-notation`:
`F̂(ξ) = N⁻¹ ∑_n F(n) e(-nξ)` for a finitely supported `F : ℤ → ℂ`. -/
noncomputable def kernelTransform (N : ℕ) (F : ℤ →₀ ℂ) (ξ : ℝ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ F.support, F n * expPhase (-(n : ℝ) * ξ)

/-- The `ℓ²` norm `‖F‖_{ℓ²} = (∑_n |F(n)|²)^(1/2)` of a finitely supported `F`. -/
noncomputable def l2norm (F : ℤ →₀ ℂ) : ℝ :=
  Real.sqrt (∑ n ∈ F.support, ‖F n‖ ^ 2)

/-! ## Plancherel on a cyclic group, `ℓ²` form -/

section Bilinear

variable {q : ℕ} [NeZero q]

/-- The bilinear kernel estimate in `ℓ²` form: adapted from upstream
`ordered_square_kernel_bilinear` (`DualCoordinates.lean`), with the normalization
`∑|F|² ≤ N` replaced by the factor `‖F‖₂ ‖G‖₂ / N`. -/
lemma ordered_square_kernel_bilinear_l2 {B : Type*} [Fintype B]
    (M N : ℕ) (hN : 0 < N) (hq : N < q) (w : ℕ → ℂ)
    (β : B → ℝ) (c : B → ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hkernel : ∀ α : ℝ,
      ‖(∑ m ∈ range M, squareWeight N α m * w (m+1)) -
        ∑ b, c b * normalizedLinearSum N (α - β b)‖ ≤ δ)
    (F G : ZMod q → ℂ)
    (hord : ∀ x y, F x * G y ≠ 0 → x.val < y.val ∧ y.val ≤ N)
    (hsquare : ∀ x y m, m ∈ range M → (((m+1)^2 : ℕ) : ZMod q) = y - x → F x * G y = 0) :
    ‖∑ b, c b * intervalFourier N F (-β b) * intervalFourier N G (β b)‖ ≤
      δ * Real.sqrt (∑ x, ‖F x‖^2) * Real.sqrt (∑ x, ‖G x‖^2) / N := by
  let k₁ : ZMod q → ℂ := cyclicPush (range M) (fun m => (((m+1)^2 : ℕ) : ZMod q))
    (fun m => (2*((m : ℝ)+1)/(N : ℝ) : ℝ) • w (m+1))
  let k₂ : ZMod q → ℂ := cyclicPush (range N) (fun n => ((n+1 : ℕ) : ZMod q))
    (intervalModelWeight N β c)
  have hk : ∀ a, ‖∑ z, (k₁ z - k₂ z) * conj (cyclicChar a z)‖ ≤ δ := by
    intro a
    simp only [sub_mul, sum_sub_distrib]
    rw [show (∑ z, k₁ z * conj (cyclicChar a z)) =
      ∑ m ∈ range M, squareWeight N (-(a.val : ℝ)/q) m * w (m+1) from
      cyclic_square_transform M N w a]
    rw [show (∑ z, k₂ z * conj (cyclicChar a z)) =
      ∑ b, c b * normalizedLinearSum N (-(a.val : ℝ)/q - β b) from
      cyclic_model_transform N β c a]
    exact hkernel _
  have hz : (∑ x, ∑ y, F x * G y * k₁ (y - x)) = 0 :=
    cyclicPush_bilinear_zero _ _ _ F G hsquare
  have he := intervalModel_bilinear N hq β c F G hord
  have hb := cyclic_bilinear_counting F G (fun z => k₁ z - k₂ z) δ hδ hk
  simp only [mul_sub, sum_sub_distrib, hz, zero_sub, norm_neg] at hb
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [← he, norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right hb hN'.le

end Bilinear

/-! ## The prime family, the root set and the root classes for `D = 8d` -/

/-- The primes up to `N`, the index set of the sieve and root weights. -/
abbrev PrimeFamily (N : ℕ) := {ℓ : ℕ // ℓ ∈ (range (N+1)).filter Nat.Prime}

instance primeFamily_fact (N : ℕ) (i : PrimeFamily N) : Fact (Nat.Prime (i : ℕ)) :=
  ⟨(mem_filter.mp i.2).2⟩

lemma primeFamily_injective (N : ℕ) : Function.Injective (fun i : PrimeFamily N => (i : ℕ)) :=
  Subtype.val_injective

lemma primeFamily_exists (N ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ≤ N) :
    ∃ i : PrimeFamily N, (i : ℕ) = ℓ :=
  ⟨⟨ℓ, mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hℓN), hℓ⟩⟩, rfl⟩

/-- The primes of `D = 8d`. -/
noncomputable def rootSet (N d : ℕ) : Finset (PrimeFamily N) :=
  univ.filter (fun i => (i : ℕ) ∣ 8 * d)

lemma mem_rootSet (N d : ℕ) (i : PrimeFamily N) : i ∈ rootSet N d ↔ (i : ℕ) ∣ 8 * d := by
  simp [rootSet]

/-- The root classes: `m ≡ 1 mod 2`, and `m ≡ c_p mod p` with `c_p² ≡ r` for `p ∣ d`. -/
noncomputable def rootClass (N d : ℕ) (r : ℤ) (hr : IsStrictSquareClass d r)
    (i : PrimeFamily N) : ZMod (i : ℕ) :=
  if h : (i : ℕ) ∣ d then Classical.choose (hr.2 (i : ℕ) (mem_filter.mp i.2).2 h).2 else 1

lemma rootClass_sq (N d : ℕ) (r : ℤ) (hr : IsStrictSquareClass d r) (i : PrimeFamily N)
    (h : (i : ℕ) ∣ d) : (r : ZMod (i : ℕ)) = rootClass N d r hr i * rootClass N d r hr i := by
  unfold rootClass
  rw [dite_eq_left h]
  exact Classical.choose_spec (hr.2 (i : ℕ) (mem_filter.mp i.2).2 h).2

lemma rootSet_two (N d : ℕ) : ∀ i : PrimeFamily N, (i : ℕ) = 2 → i ∈ rootSet N d := by
  intro i hi
  rw [mem_rootSet, hi]
  exact Dvd.dvd.mul_right (by norm_num) d

lemma rootClass_spec (N d : ℕ) (hd : Odd d) (r : ℤ) (hr : IsStrictSquareClass d r) :
    ∀ i ∈ rootSet N d, if (i : ℕ) = 2 then rootClass N d r hr i = 1
      else rootClass N d r hr i ≠ 0 := by
  intro i hi
  split_ifs with h2
  · unfold rootClass
    have h2d : ¬ (i : ℕ) ∣ d := by
      rw [h2]
      exact fun h => (Nat.not_even_iff_odd.mpr hd) (even_iff_two_dvd.mpr h)
    rw [dite_eq_right h2d]
  · have hip : (i : ℕ).Prime := (mem_filter.mp i.2).2
    have hid : (i : ℕ) ∣ d := by
      have h8 := (mem_rootSet N d i).mp hi
      have hc : Nat.Coprime (i : ℕ) 8 := by
        have : Nat.Coprime (i : ℕ) 2 := (Nat.coprime_primes hip Nat.prime_two).mpr h2
        simpa using this.pow_right 3
      exact hc.dvd_of_dvd_mul_left h8
    intro h0
    have hsq := rootClass_sq N d r hr i hid
    rw [h0, mul_zero] at hsq
    exact (hr.2 (i : ℕ) hip hid).1 hsq

lemma primeFactors_eight_mul (d : ℕ) (hd : Odd d) :
    (8 * d).primeFactors = insert 2 d.primeFactors := by
  have hd0 : d ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hd)
  rw [Nat.primeFactors_mul (by norm_num) hd0]
  rw [show (8 : ℕ) = 2^3 by norm_num, Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two]
  rfl

lemma rootSquareModulus_rootSet (N d : ℕ) (hd : Odd d) (hsq : Squarefree d) (hdN : 8 * d ≤ N) :
    rootSquareModulus (fun i : PrimeFamily N => (i : ℕ)) (rootSet N d) = 8 * d := by
  have hd0 : d ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hd)
  unfold rootSquareModulus
  have h1 : ∏ i ∈ rootSet N d, (if (i : ℕ) = 2 then 8 else (i : ℕ)) =
      ∏ ℓ ∈ (8 * d).primeFactors, (if ℓ = 2 then 8 else ℓ) := by
    apply Finset.prod_nbij (fun i : PrimeFamily N => (i : ℕ))
    · intro i hi
      rw [mem_rootSet] at hi
      exact Nat.mem_primeFactors.mpr ⟨(mem_filter.mp i.2).2, hi, by positivity⟩
    · intro i _ k _ h
      exact Subtype.val_injective h
    · intro ℓ hℓ
      obtain ⟨hℓp, hℓd, _⟩ := Nat.mem_primeFactors.mp hℓ
      obtain ⟨i, rfl⟩ := primeFamily_exists N ℓ hℓp ((Nat.le_of_dvd (by positivity) hℓd).trans hdN)
      exact ⟨i, (mem_rootSet N d i).mpr hℓd, rfl⟩
    · intro i _
      rfl
  rw [h1, primeFactors_eight_mul d hd]
  have h2 : 2 ∉ d.primeFactors := by
    intro h
    exact (Nat.not_even_iff_odd.mpr hd) (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors h))
  rw [prod_insert h2, ite_eq_left rfl]
  congr 1
  conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree hsq]
  apply prod_congr rfl
  intro ℓ hℓ
  rw [ite_eq_right]
  rintro rfl
  exact h2 hℓ

lemma rootClass_root (N d : ℕ) (hd : Odd d) (hsq : Squarefree d) (hdN : 8 * d ≤ N)
    (r : ℤ) (hr : IsStrictSquareClass d r) (n : ℕ)
    (hn : actualRootWeight (fun i : PrimeFamily N => (i : ℕ)) (rootSet N d)
      (rootClass N d r hr) n ≠ 0) :
    ((8 * d : ℕ) : ℤ) ∣ (n : ℤ)^2 - r := by
  have hall : ∀ i ∈ rootSet N d, (n : ZMod (i : ℕ)) = rootClass N d r hr i := by
    intro i hi
    by_contra hne
    apply hn
    unfold actualRootWeight
    apply prod_eq_zero hi
    rw [ite_eq_right hne]
  have hd0 : d ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hd)
  -- the prime 2
  obtain ⟨i₂, hi₂⟩ := primeFamily_exists N 2 Nat.prime_two (by omega)
  have hodd : Odd (n : ℤ) := by
    have h := hall i₂ (rootSet_two N d i₂ hi₂)
    have hc : rootClass N d r hr i₂ = 1 := by
      have := rootClass_spec N d hd r hr i₂ (rootSet_two N d i₂ hi₂)
      rwa [ite_eq_left hi₂] at this
    rw [hc] at h
    have key : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ = 2 → ((n : ZMod ℓ) = 1) → n % 2 = 1 := by
      intro ℓ _ hℓ h'
      subst hℓ
      have := congrArg ZMod.val h'
      rwa [ZMod.val_natCast, ZMod.val_one] at this
    have h3 := key (i₂ : ℕ) hi₂ h
    exact_mod_cast Nat.odd_iff.mpr h3
  have h8 : (8 : ℤ) ∣ (n : ℤ)^2 - r := by
    have h1 := Int.eight_dvd_sq_sub_one_of_odd hodd
    have h2 : (8 : ℤ) ∣ r - 1 := (Int.ModEq.dvd hr.1.symm)
    have : (n : ℤ)^2 - r = ((n : ℤ)^2 - 1) - (r - 1) := by ring
    rw [this]
    exact dvd_sub h1 h2
  -- the odd primes
  have hp : ∀ ℓ ∈ d.primeFactors, (ℓ : ℤ) ∣ (n : ℤ)^2 - r := by
    intro ℓ hℓ
    obtain ⟨hℓp, hℓd, _⟩ := Nat.mem_primeFactors.mp hℓ
    obtain ⟨i, rfl⟩ := primeFamily_exists N ℓ hℓp
      ((Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hℓd).trans (by omega))
    have hiR : i ∈ rootSet N d := (mem_rootSet N d i).mpr (Dvd.dvd.mul_left hℓd 8)
    have h := hall i hiR
    have hsq' := rootClass_sq N d r hr i hℓd
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    push_cast
    rw [h, hsq']
    ring
  have hdvd : (d : ℤ) ∣ (n : ℤ)^2 - r := by
    have h := Finset.prod_dvd_of_coprime (t := d.primeFactors) (s := fun ℓ : ℕ => (ℓ : ℤ))
      (z := (n : ℤ)^2 - r) (by
        intro ℓ hℓ k hk hne
        exact Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes
          (Nat.prime_of_mem_primeFactors hℓ) (Nat.prime_of_mem_primeFactors hk)).mpr hne)) hp
    have he : (∏ ℓ ∈ d.primeFactors, (ℓ : ℤ)) = (d : ℤ) := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
    rwa [he] at h
  have hcop : IsCoprime (8 : ℤ) (d : ℤ) := by
    have : Nat.Coprime 8 d := by
      have h2 : Nat.Coprime 2 d := Nat.coprime_two_left.mpr hd
      simpa using h2.pow_left 3
    exact Nat.isCoprime_iff_coprime.mpr this
  push_cast
  exact hcop.mul_dvd h8 hdvd

lemma primeFamily_cover (N : ℕ) (b : ℚ) (hb : b.den ≤ N) :
    b.den ∣ ∏ i : PrimeFamily N, primaryModulus b.den (i : ℕ) := by
  apply primary_cover_of_prime_support (fun i : PrimeFamily N => (i : ℕ)) (primeFamily_injective N)
    b.den b.den_nz
  intro ℓ hℓ hdvd
  exact primeFamily_exists N ℓ hℓ ((Nat.le_of_dvd b.pos hdvd).trans hb)

/-! ## From functions on `ℤ` to functions on a cyclic group -/

/-- A function supported in `[1,N]`, viewed on `ℤ/(N+1)ℤ` through the representatives
`0, …, N`. -/
noncomputable def liftCyclic (N : ℕ) (F : ℤ →₀ ℂ) : ZMod (N+1) → ℂ := fun x => F (x.val : ℤ)

lemma sum_zmod_succ (N : ℕ) (f : ℕ → ℂ) : ∑ x : ZMod (N+1), f x.val = ∑ n ∈ range (N+1), f n :=
  Fin.sum_univ_eq_sum_range (fun n => f n) (N+1)

lemma sum_support_eq_range (N : ℕ) (F : ℤ →₀ ℂ) (hF : ∀ x ∈ F.support, 1 ≤ x ∧ x ≤ N)
    {E : Type*} [AddCommMonoid E] (G : ℤ → E) (hG : ∀ x, F x = 0 → G x = 0) :
    ∑ n ∈ F.support, G n = ∑ n ∈ range (N+1), G (n : ℤ) := by
  have hm : ∑ n ∈ range (N+1), G (n : ℤ) = ∑ x ∈ (range (N+1)).map Nat.castEmbedding, G x := by
    rw [Finset.sum_map]; rfl
  rw [hm]
  apply Finset.sum_subset
  · intro x hx
    have h := hF x hx
    rw [Finset.mem_map]
    refine ⟨x.toNat, mem_range.mpr (by omega), ?_⟩
    simp only [Nat.castEmbedding_apply]
    omega
  · intro x _ hx
    exact hG x (Finsupp.notMem_support_iff.mp hx)

lemma intervalFourier_liftCyclic (N : ℕ) (F : ℤ →₀ ℂ) (hF : ∀ x ∈ F.support, 1 ≤ x ∧ x ≤ N)
    (α : ℝ) : intervalFourier N (liftCyclic N F) α = kernelTransform N F α := by
  unfold intervalFourier kernelTransform liftCyclic
  congr 1
  rw [sum_zmod_succ N (fun n => F (n : ℤ) * expPhase (-(n : ℝ) * α))]
  rw [sum_support_eq_range N F hF (fun n => F n * expPhase (-(n : ℝ) * α))
    (fun x hx => by simp [hx])]
  simp

lemma sum_norm_sq_liftCyclic (N : ℕ) (F : ℤ →₀ ℂ) (hF : ∀ x ∈ F.support, 1 ≤ x ∧ x ≤ N) :
    ∑ x : ZMod (N+1), ‖liftCyclic N F x‖^2 = ∑ n ∈ F.support, ‖F n‖^2 := by
  unfold liftCyclic
  have h := Fin.sum_univ_eq_sum_range (fun n => ‖F (n : ℤ)‖^2) (N+1)
  rw [sum_support_eq_range N F hF (fun n => ‖F n‖^2) (fun x hx => by simp [hx])]
  exact h

/-! ## The phase computation on residue classes -/

lemma kernelTransform_shift (N D : ℕ) (hD : 0 < D) (F : ℤ →₀ ℂ) (a : ℤ)
    (hF : ∀ x ∈ F.support, x ≡ a [ZMOD (D : ℤ)]) (j : ℤ) (ξ : ℝ) :
    kernelTransform N F (ξ + (j : ℝ) / D) = expPhase (-((a : ℝ) * j / D)) * kernelTransform N F ξ := by
  unfold kernelTransform
  have hsum : ∑ x ∈ F.support, F x * expPhase (-(x : ℝ) * (ξ + (j : ℝ) / D)) =
      expPhase (-((a : ℝ) * j / D)) * ∑ x ∈ F.support, F x * expPhase (-(x : ℝ) * ξ) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro x hx
    obtain ⟨k, hk⟩ := (Int.ModEq.dvd (hF x hx).symm)
    have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    have hxr : (x : ℝ) = (a : ℝ) + (D : ℝ) * k := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hk
      push_cast at this
      linarith
    have he : -(x : ℝ) * (ξ + (j : ℝ) / D) =
        (-((a : ℝ) * j / D) + -(x : ℝ) * ξ) + ((-(k * j) : ℤ) : ℝ) := by
      rw [hxr]
      push_cast
      field_simp
      ring
    rw [he, expPhase_add, expPhase_int, mul_one, expPhase_add]
    ring
  rw [hsum]
  ring

/-- The phase computation of `prop:record:kernel20`'s proof: summing the model coefficients
`e(j r/D)` against the shifted transforms collapses the sum over `j` to the factor `D`. -/
lemma pairing_phase (N D : ℕ) (hD : 0 < D) (F J : ℤ →₀ ℂ) (a b : ℤ)
    (hF : ∀ x ∈ F.support, x ≡ a [ZMOD (D : ℤ)]) (hJ : ∀ y ∈ J.support, y ≡ b [ZMOD (D : ℤ)])
    (Ξ : Finset ℚ) (g : ℚ → ℂ) :
    ∑ j ∈ range D, ∑ ξ ∈ Ξ, expPhase ((j : ℝ) * ((b - a : ℤ) : ℝ) / D) * g ξ *
        (kernelTransform N F (-((((j : ℚ) / D + ξ : ℚ)) : ℝ)) *
          kernelTransform N J ((((j : ℚ) / D + ξ : ℚ)) : ℝ)) =
      (D : ℂ) * ∑ ξ ∈ Ξ, g ξ * kernelTransform N F (-(ξ : ℝ)) * kernelTransform N J (ξ : ℝ) := by
  have hterm : ∀ j : ℕ, ∀ ξ : ℚ,
      expPhase ((j : ℝ) * ((b - a : ℤ) : ℝ) / D) * g ξ *
        (kernelTransform N F (-((((j : ℚ) / D + ξ : ℚ)) : ℝ)) *
          kernelTransform N J ((((j : ℚ) / D + ξ : ℚ)) : ℝ)) =
      g ξ * kernelTransform N F (-(ξ : ℝ)) * kernelTransform N J (ξ : ℝ) := by
    intro j ξ
    have h1 : -((((j : ℚ) / D + ξ : ℚ)) : ℝ) = -(ξ : ℝ) + (((-(j : ℤ)) : ℤ) : ℝ) / D := by
      push_cast; ring
    have h2 : ((((j : ℚ) / D + ξ : ℚ)) : ℝ) = (ξ : ℝ) + (((j : ℤ)) : ℝ) / D := by
      push_cast; ring
    rw [h1, h2, kernelTransform_shift N D hD F a hF, kernelTransform_shift N D hD J b hJ]
    have hph : expPhase ((j : ℝ) * ((b - a : ℤ) : ℝ) / D) * expPhase (-((a : ℝ) * ((-(j : ℤ) : ℤ) : ℝ) / D)) *
        expPhase (-((b : ℝ) * ((j : ℤ) : ℝ) / D)) = 1 := by
      rw [← expPhase_add, ← expPhase_add]
      have : (j : ℝ) * ((b - a : ℤ) : ℝ) / D + -((a : ℝ) * ((-(j : ℤ) : ℤ) : ℝ) / D) +
          -((b : ℝ) * ((j : ℤ) : ℝ) / D) = ((0 : ℤ) : ℝ) := by
        push_cast; ring
      rw [this, expPhase_int]
    calc _ = (expPhase ((j : ℝ) * ((b - a : ℤ) : ℝ) / D) * expPhase (-((a : ℝ) * ((-(j : ℤ) : ℤ) : ℝ) / D)) *
        expPhase (-((b : ℝ) * ((j : ℤ) : ℝ) / D))) *
          (g ξ * kernelTransform N F (-(ξ : ℝ)) * kernelTransform N J (ξ : ℝ)) := by ring
      _ = _ := by rw [hph, one_mul]
  simp_rw [hterm]
  rw [sum_const, card_range, nsmul_eq_mul]

/-! ## Elementary scale inequalities -/

lemma scale_le_self (n K e : ℝ) (hn : 1 ≤ n) (hnK : K ^ 2 ≤ n) (he : e ≤ 1 / 2) :
    K * n ^ e ≤ n := by
  have hn0 : 0 < n := by linarith
  have h1 : n ^ e ≤ n ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hn he
  have h2 : K ≤ n ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le hnK
  calc K * n ^ e ≤ n ^ ((1 : ℝ) / 2) * n ^ ((1 : ℝ) / 2) :=
        mul_le_mul h2 h1 (by positivity) (by positivity)
    _ = n := by rw [← Real.rpow_add hn0]; norm_num

lemma cutoff_saving (n H CH : ℝ) (hn : 1 ≤ n) (hCH : 0 < CH)
    (hH : CH⁻¹ * n ^ ((1 : ℝ) / 40) ≤ H) :
    H ^ (-(1 : ℝ) / 3) ≤ CH ^ ((1 : ℝ) / 3) * n ^ (-(1 : ℝ) / 120) := by
  have hn0 : 0 < n := by linarith
  have hlow : 0 < CH⁻¹ * n ^ ((1 : ℝ) / 40) := by positivity
  have hb : H ^ (-(1 : ℝ) / 3) ≤ (CH⁻¹ * n ^ ((1 : ℝ) / 40)) ^ (-(1 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_nonpos hlow hH (by norm_num)
  have hsplit : (CH⁻¹ * n ^ ((1 : ℝ) / 40)) ^ (-(1 : ℝ) / 3) =
      CH ^ ((1 : ℝ) / 3) * n ^ (-(1 : ℝ) / 120) := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hn0.le,
      Real.inv_rpow hCH.le, ← Real.rpow_neg hCH.le]
    norm_num
  rw [hsplit] at hb
  exact hb

/-! ## The kernel estimate -/

/-- **The actual-square kernel at `β = 1/20`** (`prop:record:kernel20`(i) at the triple
`(β, κ, η) = (1/20, 1/20, 17/100)` of `cor:kernel20`), **for squarefree odd `d`**.

Fix `C_D, C_H ≥ 1`. There are `C` and `N₀`, depending only on `C_D, C_H`, such that for
`N ≥ N₀`, `D = 8d ≤ C_D N^(1/20)` with `d` odd and squarefree,
`C_H⁻¹ N^(1/40) ≤ H ≤ C_H N^(1/40)`, integers `a, b` with `b - a` a strict square class
modulo `D`, and finitely supported `F, J : ℤ → ℂ` supported in `[1,N]` and in the classes
`a`, `b` modulo `D`, with `x < y` and `y - x` not the square of a positive integer for all
`x ∈ supp F`, `y ∈ supp J`:
`|D ∑_{ξ ∈ Ξ_{H,D}} g(ξ) F̂(-ξ) Ĵ(ξ)| ≤ C N^(-1/120) ‖F‖₂ ‖J‖₂ / N` (`eq:record:K20`).

Special case relative to the paper: `d` is assumed squarefree (the paper allows any odd `d`
in part (i)). -/
theorem kernel_pairing_twentieth (CD CH : ℝ) (hCD : 1 ≤ CD) (hCH : 1 ≤ CH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ d : ℕ, Odd d → Squarefree d → ((8 * d : ℕ) : ℝ) ≤ CD * (N : ℝ) ^ ((1 : ℝ) / 20) →
      ∀ H : ℝ, CH⁻¹ * (N : ℝ) ^ ((1 : ℝ) / 40) ≤ H → H ≤ CH * (N : ℝ) ^ ((1 : ℝ) / 40) →
      ∀ a b : ℤ, IsStrictSquareClass d (b - a) →
      ∀ F J : ℤ →₀ ℂ,
        (∀ x ∈ F.support, 1 ≤ x ∧ x ≤ N ∧ x ≡ a [ZMOD ((8 * d : ℕ) : ℤ)]) →
        (∀ y ∈ J.support, 1 ≤ y ∧ y ≤ N ∧ y ≡ b [ZMOD ((8 * d : ℕ) : ℤ)]) →
        (∀ x ∈ F.support, ∀ y ∈ J.support, x < y) →
        (∀ x ∈ F.support, ∀ y ∈ J.support, ∀ m : ℕ, 1 ≤ m → y - x ≠ (m : ℤ) ^ 2) →
        ‖((8 * d : ℕ) : ℂ) * ∑ ξ ∈ frequencySet H (8 * d),
            unitQuadraticAverage ξ * kernelTransform N F (-(ξ : ℝ)) *
              kernelTransform N J (ξ : ℝ)‖ ≤
          C * (N : ℝ) ^ (-(1 : ℝ) / 120) * (l2norm F * l2norm J) / N := by
  obtain ⟨C₁, hC₁, N₁, hrate⟩ := actual_kernel_rate_twentieth CD CH hCD hCH
  refine ⟨C₁ * CH ^ ((1 : ℝ) / 3), by positivity, max N₁ (⌈(CD * CH) ^ 2⌉₊ + 1), ?_⟩
  intro N hN d hd hsq hD H hH1 hH2 a b hab F J hF hJ hord hnosq
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans hN
  have hNK' : ⌈(CD * CH) ^ 2⌉₊ + 1 ≤ N := (le_max_right _ _).trans hN
  have hNpos : 0 < N := by omega
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hNK : (CD * CH) ^ 2 ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈(CD * CH) ^ 2⌉₊ ≤ N by omega))
  have hCD0 : 0 ≤ CD := by linarith
  have hCH0 : 0 < CH := by linarith
  have hK0 : 0 ≤ CD * CH := by positivity
  have hd0 : d ≠ 0 := by rintro rfl; exact Nat.not_odd_zero hd
  set D := 8 * d with hDdef
  have hDpos : 0 < D := by positivity
  -- scale facts
  have hDN : D ≤ N := by
    have h : CD * CH * (N : ℝ) ^ ((1 : ℝ) / 20) ≤ N := scale_le_self N (CD * CH) _ hn1 hNK
      (by norm_num)
    have h' : CD * (N : ℝ) ^ ((1 : ℝ) / 20) ≤ CD * CH * (N : ℝ) ^ ((1 : ℝ) / 20) := by
      have : CD ≤ CD * CH := le_mul_of_one_le_right hCD0 hCH
      exact mul_le_mul_of_nonneg_right this (by positivity)
    exact_mod_cast hD.trans (h'.trans h)
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) hH1
  have hHN : H ≤ N := by
    have h : CD * CH * (N : ℝ) ^ ((1 : ℝ) / 40) ≤ N := scale_le_self N (CD * CH) _ hn1 hNK
      (by norm_num)
    have h' : CH * (N : ℝ) ^ ((1 : ℝ) / 40) ≤ CD * CH * (N : ℝ) ^ ((1 : ℝ) / 40) := by
      have : CH ≤ CD * CH := le_mul_of_one_le_left hCH0.le hCD
      exact mul_le_mul_of_nonneg_right this (by positivity)
    exact hH2.trans (h'.trans h)
  have hDHN : (D : ℝ) * H ≤ N := by
    have h : CD * CH * (N : ℝ) ^ ((3 : ℝ) / 40) ≤ N := scale_le_self N (CD * CH) _ hn1 hNK
      (by norm_num)
    have hn0 : (0 : ℝ) < N := by linarith
    calc (D : ℝ) * H ≤ (CD * (N : ℝ) ^ ((1 : ℝ) / 20)) * (CH * (N : ℝ) ^ ((1 : ℝ) / 40)) :=
          mul_le_mul hD hH2 hH0.le (by positivity)
      _ = CD * CH * (N : ℝ) ^ ((3 : ℝ) / 40) := by
          rw [show (3 : ℝ) / 40 = 1 / 20 + 1 / 40 by norm_num, Real.rpow_add hn0]; ring
      _ ≤ N := h
  -- the prime family, the root set and the root classes
  set p : PrimeFamily N → ℕ := fun i => (i : ℕ) with hpdef
  set R := rootSet N d with hRdef
  set c := rootClass N d (b - a) hab with hcdef
  have hinj : Function.Injective p := primeFamily_injective N
  have hRD : rootSquareModulus p R = D := rootSquareModulus_rootSet N d hd hsq hDN
  have hroot : ∀ n : ℕ, actualRootWeight p R c n ≠ 0 →
      (rootSquareModulus p R : ℤ) ∣ (n : ℤ)^2 - (b - a) := by
    intro n hn
    rw [hRD]
    exact rootClass_root N d hd hsq hDN (b - a) hab n hn
  have htwo := rootSet_two N d
  have hc := rootClass_spec N d hd (b - a) hab
  -- the uniform kernel approximation
  have hk := hrate N hN₁ p R c hinj H hH1 hH2 (by rw [hRD]; exact hD)
    (fun q hq => primeFamily_cover N q (by
      have h1 : (q.den : ℝ) ≤ N := hq.trans
        (Real.rpow_le_self_of_one_le hn1 (by norm_num))
      exact_mod_cast h1)) htwo hc
  -- Plancherel on `ℤ/(N+1)ℤ`
  have hFs : ∀ x ∈ F.support, 1 ≤ x ∧ x ≤ N := fun x hx => ⟨(hF x hx).1, (hF x hx).2.1⟩
  have hJs : ∀ y ∈ J.support, 1 ≤ y ∧ y ≤ N := fun y hy => ⟨(hJ y hy).1, (hJ y hy).2.1⟩
  have hordc : ∀ x y : ZMod (N+1), liftCyclic N F x * liftCyclic N J y ≠ 0 →
      x.val < y.val ∧ y.val ≤ N := by
    intro x y hxy
    have hx : (x.val : ℤ) ∈ F.support :=
      Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul hxy)
    have hy : (y.val : ℤ) ∈ J.support :=
      Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hxy)
    have h1 := hord _ hx _ hy
    have h2 := (hJ _ hy).2.1
    constructor
    · exact_mod_cast h1
    · exact_mod_cast h2
  have hsquarec : ∀ (x y : ZMod (N+1)) (m : ℕ), m ∈ range N.sqrt →
      (((m+1)^2 : ℕ) : ZMod (N+1)) = y - x → liftCyclic N F x * liftCyclic N J y = 0 := by
    intro x y m hm hxy
    by_contra hne
    obtain ⟨hlt, hyN⟩ := hordc x y hne
    have hx : (x.val : ℤ) ∈ F.support :=
      Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul hne)
    have hy : (y.val : ℤ) ∈ J.support :=
      Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hne)
    have hm' : m + 1 ≤ N.sqrt := mem_range.mp hm
    have hsqN : (m+1)^2 ≤ N := by
      have := Nat.sqrt_le' N
      calc (m+1)^2 ≤ N.sqrt^2 := Nat.pow_le_pow_left hm' 2
        _ ≤ N := this
    have hval := congrArg ZMod.val hxy
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), ZMod.val_sub hlt.le] at hval
    apply hnosq _ hx _ hy (m+1) (by omega)
    have : ((y.val - x.val : ℕ) : ℤ) = (y.val : ℤ) - (x.val : ℤ) := by
      rw [Nat.cast_sub hlt.le]
    rw [← this, ← hval]
    push_cast
    ring
  have hbil := ordered_square_kernel_bilinear_l2 (q := N+1) N.sqrt N hNpos (by omega)
    (actualDivisorWeight p R c H)
    (fun q : boundedRationals ⌈(rootSquareModulus p R : ℝ) * H⌉₊ => ((q.val : ℚ) : ℝ))
    (fun q => kernelModelCoefficient p R c H q.val) (C₁ * H ^ (-(1 : ℝ) / 3)) (by positivity)
    (fun α => hk α) (liftCyclic N F) (liftCyclic N J) hordc hsquarec
  rw [sum_norm_sq_liftCyclic N F hFs, sum_norm_sq_liftCyclic N J hJs] at hbil
  -- identify the model pairing with the paper's pairing
  have hmodel : (∑ q : boundedRationals ⌈(rootSquareModulus p R : ℝ) * H⌉₊,
      kernelModelCoefficient p R c H q.val *
        intervalFourier N (liftCyclic N F) (-((q.val : ℚ) : ℝ)) *
        intervalFourier N (liftCyclic N J) ((q.val : ℚ) : ℝ)) =
      (D : ℂ) * ∑ ξ ∈ frequencySet H D,
        unitQuadraticAverage ξ * kernelTransform N F (-(ξ : ℝ)) * kernelTransform N J (ξ : ℝ) := by
    simp_rw [intervalFourier_liftCyclic N F hFs, intervalFourier_liftCyclic N J hJs]
    rw [Finset.sum_coe_sort (boundedRationals ⌈(rootSquareModulus p R : ℝ) * H⌉₊)
      (fun q : ℚ => kernelModelCoefficient p R c H q *
        kernelTransform N F (-((q : ℚ) : ℝ)) * kernelTransform N J ((q : ℚ) : ℝ))]
    have hre := model_sum_reindex p R c hinj htwo hc (b - a) hroot H hH0.le
      (fun q hq => primeFamily_cover N q (by
        have h1 : (⌈(rootSquareModulus p R : ℝ) * H⌉₊ : ℝ) ≤ N := by
          rw [hRD]
          exact (Nat.ceil_le.mpr (by exact_mod_cast hDHN) : ⌈(D : ℝ) * H⌉₊ ≤ N) |> fun h =>
            by exact_mod_cast h
        exact_mod_cast (Nat.cast_le.mpr hq).trans h1))
      (fun ℓ hℓ hℓH => primeFamily_exists N ℓ hℓ (by exact_mod_cast hℓH.trans hHN))
      (fun q => kernelTransform N F (-((q : ℚ) : ℝ)) * kernelTransform N J ((q : ℚ) : ℝ))
      (fun q k => by
        have h1 : kernelTransform N F (-(((q + k : ℚ)) : ℝ)) = kernelTransform N F (-((q : ℚ) : ℝ)) := by
          unfold kernelTransform
          congr 1
          apply sum_congr rfl
          intro n _
          have : -(n : ℝ) * (-(((q + k : ℚ)) : ℝ)) = -(n : ℝ) * (-((q : ℚ) : ℝ)) + ((n * k : ℤ) : ℝ) := by
            push_cast; ring
          rw [this, expPhase_add, expPhase_int, mul_one]
        have h2 : kernelTransform N J ((((q + k : ℚ)) : ℝ)) = kernelTransform N J ((q : ℚ) : ℝ) := by
          unfold kernelTransform
          congr 1
          apply sum_congr rfl
          intro n _
          have : -(n : ℝ) * ((((q + k : ℚ)) : ℝ)) = -(n : ℝ) * (((q : ℚ) : ℝ)) + ((-(n * k) : ℤ) : ℝ) := by
            push_cast; ring
          rw [this, expPhase_add, expPhase_int, mul_one]
        rw [h1, h2])
    simp_rw [mul_assoc] at hre ⊢
    rw [hre, hRD]
    have hph := pairing_phase N D hDpos F J a b (fun x hx => (hF x hx).2.2)
      (fun y hy => (hJ y hy).2.2) (frequencySet H D) unitQuadraticAverage
    simp_rw [mul_assoc] at hph
    rw [← hph]
  rw [hmodel] at hbil
  have hsave := cutoff_saving N H CH hn1 hCH0 hH1
  have hN0 : (0 : ℝ) < N := by linarith
  calc _ = ‖(D : ℂ) * ∑ ξ ∈ frequencySet H D, unitQuadraticAverage ξ *
        kernelTransform N F (-(ξ : ℝ)) * kernelTransform N J (ξ : ℝ)‖ := by rfl
    _ ≤ C₁ * H ^ (-(1 : ℝ) / 3) * Real.sqrt (∑ n ∈ F.support, ‖F n‖^2) *
        Real.sqrt (∑ n ∈ J.support, ‖J n‖^2) / N := hbil
    _ ≤ C₁ * (CH ^ ((1 : ℝ) / 3) * (N : ℝ) ^ (-(1 : ℝ) / 120)) * Real.sqrt (∑ n ∈ F.support, ‖F n‖^2) *
        Real.sqrt (∑ n ∈ J.support, ‖J n‖^2) / N := by gcongr
    _ = _ := by unfold l2norm; ring

end Kernel
end
end Sarkozy
