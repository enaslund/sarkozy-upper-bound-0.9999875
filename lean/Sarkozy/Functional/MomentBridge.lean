module

public import Sarkozy.Functional.PrefixModel
public import Sarkozy.Functional.FibreCount

@[expose] public section

/-!
# Moments of the square-step pieces (`lem:record:fibre-scale`(e), unconditional)

`FibreCount.moment_squareStepModel` derives `lem:record:fibre-scale`(e) from a
moment bound for the pieces `h_j` (the paper cites `lem:record:lift-moments`(c)).
For the paper's groups — a prime-power prefix (the clique coordinates) and a
prime tail — this module proves that bound from the project's arithmetic
moment theorem `FourierArithmetic.uniform_prefixed_indicator_moment`:

* `complexLift_prefix_eq_liftOn`: a lift on the joined group whose labels are
  given by a set of prefix labels and character-dependent tail supports is the
  project's prefixed `complexLift`;
* `retainedOff_eq_jointLabels`: the labels of `h_j` (vanishing on `E`, conductor
  at most `Q'`) are of this form;
* `moment_stepLift_le`: `E|h_j|^{2r} ≤ |X₀|^{2r} C Q'^ε |B|/n`, with `C` depending
  only on `r` and `ε`, under the cutoff conditions `2⌊Q'⌋ ≤ n+1`, `⌊Q'⌋^5 ≤ n+1`
  (automatic for `Q' = n^{1/20}`);
* `moment_squareStepModel_prefix`: `lem:record:fibre-scale`(e),
  `E|g̃|^{2r} ≤ C' λ^{2r−1} α_f`, with no moment hypothesis.
-/

open Finset Complex
open scoped BigOperators ComplexConjugate

namespace Sarkozy.Functional

open Sarkozy.FourierArithmetic

section General

variable {J₀ J : Type*} [Fintype J₀] [DecidableEq J₀] [Fintype J] [DecidableEq J]
  (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)] (p : J → ℕ) [∀ j, NeZero (p j)]

/-- Labels on the joined group from prefix labels `S₀` and tail supports `F'`. -/
noncomputable def jointLabels (S₀ : Finset (ResidueSpace m₀))
    (F' : ResidueSpace m₀ → Finset (Finset J)) : Finset (ResidueSpace (joinModuli m₀ p)) :=
  univ.filter fun b => (splitEquiv m₀ p b).1 ∈ S₀ ∧
    primeSupport p (splitEquiv m₀ p b).2 ∈ F' (splitEquiv m₀ p b).1

/-- The prefixed `complexLift` with prefix characters `S₀` and tail supports `F'`
is the lift on the joined group with the labels `jointLabels S₀ F'`. -/
theorem complexLift_prefix_eq_liftOn (S₀ : Finset (ResidueSpace m₀))
    (F' : ResidueSpace m₀ → Finset (Finset J)) (N : ℕ) {B : Finset ℤ}
    (hB : B ⊆ Icc 1 (N : ℤ)) (z : ResidueSpace (joinModuli m₀ p)) :
    complexLift ((integerResidue m₀).prod (integerResidue p)) N B
        (prefixCharacters p (S₀.image (productCharacter m₀)) (fun χ => F' (prefixLabel m₀ χ)))
        (splitEquiv m₀ p z) =
      liftOn (joinModuli m₀ p) (jointLabels m₀ p S₀ F') (Icc 1 (N : ℤ)) (indicator B) z := by
  unfold complexLift
  rw [sum_prefixCharacters, sum_image (fun a _ b _ h => productCharacter_injective m₀ h)]
  simp only [prefixLabel_productCharacter]
  unfold liftOn jointLabels
  rw [sum_filter]
  rw [← (splitEquiv m₀ p).toEquiv.symm.sum_comp, Fintype.sum_prod_type]
  rw [← sum_filter_add_sum_filter_not univ (fun a₀ => a₀ ∈ S₀)]
  have hzero : ∑ a₀ ∈ univ.filter (fun a₀ => a₀ ∉ S₀), ∑ a : ResidueSpace p,
      (if (splitEquiv m₀ p ((splitEquiv m₀ p).toEquiv.symm (a₀, a))).1 ∈ S₀ ∧
          primeSupport p (splitEquiv m₀ p ((splitEquiv m₀ p).toEquiv.symm (a₀, a))).2 ∈
            F' (splitEquiv m₀ p ((splitEquiv m₀ p).toEquiv.symm (a₀, a))).1 then
        intervalCoeff (joinModuli m₀ p) (Icc 1 (N : ℤ)) (indicator B)
            ((splitEquiv m₀ p).toEquiv.symm (a₀, a)) *
          prodChar (joinModuli m₀ p) ((splitEquiv m₀ p).toEquiv.symm (a₀, a)) z
      else 0) = 0 := by
    apply sum_eq_zero
    intro a₀ ha₀
    apply sum_eq_zero
    intro a _
    have hs : (splitEquiv m₀ p ((splitEquiv m₀ p).toEquiv.symm (a₀, a))) = (a₀, a) :=
      (splitEquiv m₀ p).toEquiv.apply_symm_apply _
    rw [hs]
    exact ite_eq_right (fun h => (mem_filter.mp ha₀).2 h.1)
  rw [hzero, add_zero, filter_mem_eq_inter, univ_inter]
  apply sum_congr rfl
  intro a₀ ha₀
  rw [supportFrequencies, sum_filter]
  apply sum_congr rfl
  intro a _
  set b := (splitEquiv m₀ p).toEquiv.symm (a₀, a) with hb
  have hsplit : splitEquiv m₀ p b = (a₀, a) := (splitEquiv m₀ p).toEquiv.apply_symm_apply _
  have hcoeff : fourierCoefficient ((integerResidue m₀).prod (integerResidue p)) N B
      (prefixCharacter p (productCharacter m₀ a₀) a) =
      intervalCoeff (joinModuli m₀ p) (Icc 1 (N : ℤ)) (indicator B) b := by
    rw [fourierCoefficient, intervalCoeff, card_Icc_one, div_eq_inv_mul]
    congr 1
    simp only [indicator, ite_mul, one_mul, zero_mul]
    rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.mpr hB]
    apply sum_congr rfl
    intro n _
    rw [prodChar_split, hsplit, splitEquiv_integerResidue]
    rfl
  have hval : prefixCharacter p (productCharacter m₀ a₀) a (splitEquiv m₀ p z) =
      prodChar (joinModuli m₀ p) b z := by
    rw [prodChar_split, hsplit]
    rfl
  rw [hsplit]
  by_cases h : primeSupport p a ∈ F' a₀
  · rw [ite_eq_left h, ite_eq_left ⟨ha₀, h⟩, hcoeff, hval]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h h'.2)]

/-- The labels of `h_j` — vanishing on `E` and of conductor `≤ Q'` — as joint
labels: prefix labels vanishing on the prefix coordinates of `E`, tail supports
avoiding `E` with `q(a₀) ∏_U p ≤ Q'`. -/
theorem retainedOff_eq_jointLabels (hp : ∀ j, (p j).Prime) (E : Finset (J₀ ⊕ J)) (Q' : ℝ) :
    retainedOff (joinModuli m₀ p) E Q' =
      jointLabels m₀ p (univ.filter fun a₀ => ∀ i, Sum.inl i ∈ E → a₀ i = 0)
        (fun a₀ => univ.filter fun U => (∀ j ∈ U, Sum.inr j ∉ E) ∧
          ((conductor m₀ a₀ * ∏ j ∈ U, p j : ℕ) : ℝ) ≤ Q') := by
  ext b
  simp only [retainedOff, jointLabels, mem_filter, mem_univ, true_and]
  rw [conductor_split, conductor_eq_supportDenominator p hp, supportDenominator]
  have hsplit1 : ∀ i, (splitEquiv m₀ p b).1 i = b (Sum.inl i) := fun i => rfl
  have hsplit2 : ∀ j, (splitEquiv m₀ p b).2 j = b (Sum.inr j) := fun j => rfl
  constructor
  · rintro ⟨hE, hc⟩
    refine ⟨fun i hi => by rw [hsplit1]; exact hE _ hi, fun j hj hjE => ?_, by exact_mod_cast hc⟩
    simp only [primeSupport, mem_filter, mem_univ, true_and, hsplit2] at hj
    exact hj (hE _ hjE)
  · rintro ⟨hE0, hEt, hc⟩
    refine ⟨fun k hk => ?_, by exact_mod_cast hc⟩
    rcases k with i | j
    · have := hE0 i hk
      rwa [hsplit1] at this
    · by_contra hne
      have hj : j ∈ primeSupport p (splitEquiv m₀ p b).2 := by
        simp only [primeSupport, mem_filter, mem_univ, true_and, hsplit2]
        exact hne
      exact hEt j hj hk

theorem neg_mem_retainedOff {J' : Type*} [Fintype J'] [DecidableEq J'] {m : J' → ℕ}
    [∀ j, NeZero (m j)] {E : Finset J'} {Q' : ℝ} {a : ResidueSpace m}
    (ha : a ∈ retainedOff m E Q') : -a ∈ retainedOff m E Q' := by
  simp only [retainedOff, mem_filter, mem_univ, true_and] at ha ⊢
  refine ⟨fun i hi => by simp [ha.1 i hi], ?_⟩
  rw [conductor_neg]
  exact ha.2

end General

/-! ### The moment bound for the pieces and `lem:record:fibre-scale`(e) -/

section Moments

/-- `lem:record:lift-moments`(c) for the pieces `h_j` on the paper's groups (a
finite prefix of arbitrary moduli, a tail of distinct primes):
`E_y |h_j(y)|^{2r} ≤ |X₀|^{2r} C Q'^ε |B|/n`, with `C` depending only on `r, ε`. -/
theorem moment_stepLift_le (r : ℕ) (hr : 1 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {J₀ J : Type} [Fintype J₀] [DecidableEq J₀] [Fintype J] [DecidableEq J]
      (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)] (p : J → ℕ) [∀ j, NeZero (p j)],
      (∀ j, (p j).Prime) → Function.Injective p →
      ∀ (E : Finset (J₀ ⊕ J)) (Q' : ℝ), 1 ≤ Q' → ∀ n : ℕ, 0 < n →
      2 * ⌊Q'⌋₊ ≤ n + 1 → ⌊Q'⌋₊ ^ 5 ≤ n + 1 → ∀ B : Finset ℤ, B ⊆ Icc 1 (n : ℤ) →
      𝔼 y, ‖stepLift (joinModuli m₀ p) E Q' B n y‖ ^ (2 * r) ≤
        (Fintype.card (ResidueSpace m₀) : ℝ) ^ (2 * r) * C * Q' ^ ε * ((B.card : ℝ) / n) := by
  obtain ⟨C, hC, hc⟩ := uniform_prefixed_indicator_moment r hr ε hε
  refine ⟨C, hC, ?_⟩
  intro J₀ J _ _ _ _ m₀ _ p _ hp hinj E Q' hQ' n hn hsmall hsmall' B hB
  set S₀ : Finset (ResidueSpace m₀) := univ.filter fun a₀ => ∀ i, Sum.inl i ∈ E → a₀ i = 0
  set F' : ResidueSpace m₀ → Finset (Finset J) := fun a₀ => univ.filter fun U =>
    (∀ j ∈ U, Sum.inr j ∉ E) ∧ ((conductor m₀ a₀ * ∏ j ∈ U, p j : ℕ) : ℝ) ≤ Q'
  set H := S₀.image (productCharacter m₀)
  set F := fun χ => F' (prefixLabel m₀ χ)
  set Q := ⌊Q'⌋₊ with hQdef
  have hQpos : 0 < Q := Nat.floor_pos.mpr hQ'
  have hcop : Pairwise fun i j => (p i).Coprime (p j) := fun i j hij =>
    (Nat.coprime_primes (hp i) (hp j)).mpr (fun h => hij (hinj h))
  have hden : ∀ χ ∈ H, ∀ U ∈ F χ, ∏ j ∈ U, p j ≤ Q := by
    intro χ _ U hU
    simp only [F, F', mem_filter, mem_univ, true_and] at hU
    apply Nat.le_floor
    have hcond := conductor_pos m₀ (prefixLabel m₀ χ)
    have : ((∏ j ∈ U, p j : ℕ) : ℝ) ≤
        ((conductor m₀ (prefixLabel m₀ χ) * ∏ j ∈ U, p j : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_mul_of_pos_left _ hcond
    exact this.trans hU.2
  have hB0 : B ⊆ Icc 0 (n : ℤ) := fun x hx => by
    have := mem_Icc.mp (hB hx); exact mem_Icc.mpr ⟨by omega, this.2⟩
  have hm := hc p (integerResidue m₀) hcop hinj H F Q hQpos hden n hn
    (by exact_mod_cast hsmall) (by exact_mod_cast hsmall') B hB0
  -- identify the prefixed lift with `h_j`
  have hlift : ∀ w : ResidueSpace m₀ × ResidueSpace p,
      fourierLift ((integerResidue m₀).prod (integerResidue p)) n B (prefixCharacters p H F) w =
        (stepLift (joinModuli m₀ p) E Q' B n ((splitEquiv m₀ p).symm w)).re := by
    intro w
    have h := complexLift_prefix_eq_liftOn m₀ p S₀ F' n hB ((splitEquiv m₀ p).symm w)
    rw [AddEquiv.apply_symm_apply] at h
    unfold fourierLift stepLift
    rw [h, retainedOff_eq_jointLabels m₀ p hp E Q']
  have hreal : ∀ y, ‖stepLift (joinModuli m₀ p) E Q' B n y‖ =
      |(stepLift (joinModuli m₀ p) E Q' B n y).re| := by
    intro y
    have h := conj_liftOn_of_real (joinModuli m₀ p) (retainedOff (joinModuli m₀ p) E Q')
      (fun a ha => neg_mem_retainedOff ha) (Icc 1 (n : ℤ)) (indicator B) (conj_indicator B) y
    have hre : ((stepLift (joinModuli m₀ p) E Q' B n y).re : ℂ) =
        stepLift (joinModuli m₀ p) E Q' B n y := Complex.conj_eq_iff_re.mp h
    conv_lhs => rw [← hre]
    rw [Complex.norm_real, Real.norm_eq_abs]
  -- the left side of `hm` is the moment of `h_j`
  have hmom : (FiniteLaw.uniform (ResidueSpace m₀ × ResidueSpace p)).moment (2 * r : ℕ)
      (fourierLift ((integerResidue m₀).prod (integerResidue p)) n B (prefixCharacters p H F)) =
        𝔼 y, ‖stepLift (joinModuli m₀ p) E Q' B n y‖ ^ (2 * r) := by
    unfold FiniteLaw.moment
    rw [uniform_expect_eq_expect]
    simp_rw [hlift, Real.rpow_natCast]
    symm
    apply Fintype.expect_equiv (splitEquiv m₀ p).toEquiv
    intro y
    rw [hreal, show (splitEquiv m₀ p).symm ((splitEquiv m₀ p).toEquiv y) = y from
      (splitEquiv m₀ p).symm_apply_apply y]
  rw [hmom] at hm
  apply hm.trans
  -- compare the constants
  have hHcard : (H.card : ℝ) ≤ Fintype.card (ResidueSpace m₀) := by
    exact_mod_cast (card_image_le.trans (card_le_univ _))
  have hQle : (Q : ℝ) ^ ε ≤ Q' ^ ε :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (by linarith)) hε.le
  have hdens : density n B = (B.card : ℝ) / n := rfl
  rw [hdens]
  have h1 : (0 : ℝ) ≤ (B.card : ℝ) / n := by positivity
  have h2 : (H.card : ℝ) ^ (2 * r) ≤ (Fintype.card (ResidueSpace m₀) : ℝ) ^ (2 * r) :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hHcard _
  have h3 : (0 : ℝ) ≤ (Q : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc (H.card : ℝ) ^ (2 * r) * C * (Q : ℝ) ^ ε * ((B.card : ℝ) / n)
      ≤ (Fintype.card (ResidueSpace m₀) : ℝ) ^ (2 * r) * C * (Q : ℝ) ^ ε * ((B.card : ℝ) / n) := by
        gcongr
    _ ≤ _ := by gcongr

/-- `lem:record:fibre-scale`(e) on the paper's groups (prime-power prefix, prime
tail), with no moment hypothesis: for every `r ≥ 1` and `ε > 0` there is `C`
(depending only on `r, ε`) such that
`E|g̃|^{2r} ≤ |X₀|^{2r} C Q'^ε · λ^{2r−1} α_f`, where `R = sq(D)`, `n = K⌈M/(KR)⌉`,
`λ = Rn/M`, `α_f = (D/M) #{x ∈ A ∩ I : x ≡ 𝔞 (D)}`, and `Q'` (the paper's `n^β`)
satisfies `1 ≤ Q'`, `2⌊Q'⌋ ≤ n+1`, `⌊Q'⌋^5 ≤ n+1`. The paper's constant
`C_{r,ε} N^ε` corresponds to `|X₀|^{2r} C Q'^ε` (`Q' ≤ N`, `|X₀| = Q_cl` fixed). -/
theorem moment_squareStepModel_prefix (r : ℕ) (hr : 1 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {J₀ J : Type} [Fintype J₀] [DecidableEq J₀] [Fintype J] [DecidableEq J]
      (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)] (p : J → ℕ) [∀ j, NeZero (p j)],
      (∀ j, (p j).Prime) → Function.Injective p →
      (Pairwise fun i j => (joinModuli m₀ p i).Coprime (joinModuli m₀ p j)) →
      ∀ (E : Finset (J₀ ⊕ J)) (z : ResidueSpace (joinModuli m₀ p)) {D0 : ℕ}, 1 ≤ D0 →
      ∀ (s : ZMod D0), (∀ k, D0.Coprime (joinModuli m₀ p k)) →
      ∀ {K : ℕ}, 1 ≤ K → ∀ (A : Finset ℤ) (c : ℤ) {M : ℕ}, 1 ≤ M → ∀ (Q' : ℝ), 1 ≤ Q' →
      2 * ⌊Q'⌋₊ ≤ K * stepScale K M (leastSquare (D0 * ∏ j ∈ E, joinModuli m₀ p j)) + 1 →
      ⌊Q'⌋₊ ^ 5 ≤ K * stepScale K M (leastSquare (D0 * ∏ j ∈ E, joinModuli m₀ p j)) + 1 →
      𝔼 y, ‖squareStepModel (joinModuli m₀ p) E z s A (Icc (c + 1) (c + M)) c M
          (leastSquare (D0 * ∏ j ∈ E, joinModuli m₀ p j))
          (K * stepScale K M (leastSquare (D0 * ∏ j ∈ E, joinModuli m₀ p j))) Q' y‖ ^ (2 * r) ≤
        ((Fintype.card (ResidueSpace m₀) : ℝ) ^ (2 * r) * C * Q' ^ ε) *
          (((leastSquare (D0 * ∏ j ∈ E, joinModuli m₀ p j) *
              (K * stepScale K M (leastSquare (D0 * ∏ j ∈ E, joinModuli m₀ p j))) : ℕ) : ℝ) /
            M) ^ (2 * r - 1) *
          ((((D0 * ∏ j ∈ E, joinModuli m₀ p j : ℕ) : ℝ) / M) *
            ((A ∩ Icc (c + 1) (c + M)).filter (InFibre (joinModuli m₀ p) E z s)).card) := by
  obtain ⟨C, hC, hc⟩ := moment_stepLift_le r hr ε hε
  refine ⟨C, hC, ?_⟩
  intro J₀ J _ _ _ _ m₀ _ p _ hp hinj hpair E z D0 hD0 s hcop0 K hK A c M hM Q' hQ' hs1 hs2
  set R := leastSquare (D0 * ∏ j ∈ E, joinModuli m₀ p j) with hR
  set n := K * stepScale K M R with hn
  have hR1 : 1 ≤ R := leastSquare_pos _
  have hMR := (stepScale_bounds (M := M) hK hR1).1
  have hn1 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [← hn, h, mul_zero] at hMR; omega
    · exact h
  have h := moment_squareStepModel_sq (joinModuli m₀ p) (E := E) z hD0 s hcop0 hpair hK A c hM
    (R := R) (n := n) rfl rfl Q' (p := 2 * r) (by omega)
    (C := (Fintype.card (ResidueSpace m₀) : ℝ) ^ (2 * r) * C * Q' ^ ε)
    (fun j _ => hc m₀ p hp hinj E Q' hQ' n hn1 hs1 hs2 _ (filter_subset _ _))
  push_cast at h ⊢
  exact h

/-- The cutoff conditions of the moment theorem hold for the paper's cutoff
`Q' = n^{1/20}` at every scale `n ≥ 1` (they follow from `⌊n^{1/20}⌋^{20} ≤ n`). -/
theorem paperCutoff_conditions {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ paperCutoff n ∧ 2 * ⌊paperCutoff n⌋₊ ≤ n + 1 ∧ ⌊paperCutoff n⌋₊ ^ 5 ≤ n + 1 := by
  have hQ := one_le_paperCutoff hn
  have hc1 : 1 ≤ ⌊paperCutoff n⌋₊ := Nat.one_le_floor_iff _ |>.mpr hQ
  have hc20 := cutoff_pow_le (N := n)
  set c := ⌊paperCutoff n⌋₊
  have hc2 : c ^ 2 ≤ c ^ 20 := Nat.pow_le_pow_right hc1 (by norm_num)
  have hc5 : c ^ 5 ≤ c ^ 20 := Nat.pow_le_pow_right hc1 (by norm_num)
  refine ⟨hQ, ?_, by omega⟩
  nlinarith

/-- `lem:record:fibre-scale`(e) with the paper's cutoff `n^β`, `β = 1/20`, for the
pieces: for every `r ≥ 1`, `ε > 0` there is `C` with
`E|g̃|^{2r} ≤ |X₀|^{2r} C (n^{1/20})^ε λ^{2r−1} α_f`, with no side condition. -/
theorem moment_squareStepModel_paperCutoff (r : ℕ) (hr : 1 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {J₀ J : Type} [Fintype J₀] [DecidableEq J₀] [Fintype J] [DecidableEq J]
      (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)] (p : J → ℕ) [∀ j, NeZero (p j)],
      (∀ j, (p j).Prime) → Function.Injective p →
      (Pairwise fun i j => (joinModuli m₀ p i).Coprime (joinModuli m₀ p j)) →
      ∀ (E : Finset (J₀ ⊕ J)) (z : ResidueSpace (joinModuli m₀ p)) {D0 : ℕ}, 1 ≤ D0 →
      ∀ (s : ZMod D0), (∀ k, D0.Coprime (joinModuli m₀ p k)) →
      ∀ {K : ℕ}, 1 ≤ K → ∀ (A : Finset ℤ) (c : ℤ) {M : ℕ}, 1 ≤ M →
      𝔼 y, ‖squareStepModel (joinModuli m₀ p) E z s A (Icc (c + 1) (c + M)) c M
          (leastSquare (D0 * ∏ j ∈ E, joinModuli m₀ p j))
          (K * stepScale K M (leastSquare (D0 * ∏ j ∈ E, joinModuli m₀ p j)))
          (paperCutoff (K * stepScale K M (leastSquare (D0 * ∏ j ∈ E, joinModuli m₀ p j)))) y‖ ^
          (2 * r) ≤
        ((Fintype.card (ResidueSpace m₀) : ℝ) ^ (2 * r) * C *
            paperCutoff (K * stepScale K M (leastSquare (D0 * ∏ j ∈ E, joinModuli m₀ p j))) ^ ε) *
          (((leastSquare (D0 * ∏ j ∈ E, joinModuli m₀ p j) *
              (K * stepScale K M (leastSquare (D0 * ∏ j ∈ E, joinModuli m₀ p j))) : ℕ) : ℝ) /
            M) ^ (2 * r - 1) *
          ((((D0 * ∏ j ∈ E, joinModuli m₀ p j : ℕ) : ℝ) / M) *
            ((A ∩ Icc (c + 1) (c + M)).filter (InFibre (joinModuli m₀ p) E z s)).card) := by
  obtain ⟨C, hC, hc⟩ := moment_squareStepModel_prefix r hr ε hε
  refine ⟨C, hC, ?_⟩
  intro J₀ J _ _ _ _ m₀ _ p _ hp hinj hpair E z D0 hD0 s hcop0 K hK A c M hM
  have hR1 : 1 ≤ leastSquare (D0 * ∏ j ∈ E, joinModuli m₀ p j) := leastSquare_pos _
  have hMR := (stepScale_bounds (M := M) hK hR1).1
  have hn1 : 1 ≤ K * stepScale K M (leastSquare (D0 * ∏ j ∈ E, joinModuli m₀ p j)) := by
    rcases Nat.eq_zero_or_pos (K * stepScale K M (leastSquare (D0 * ∏ j ∈ E, joinModuli m₀ p j)))
      with h | h
    · rw [h, mul_zero] at hMR; omega
    · exact h
  obtain ⟨h1, h2, h3⟩ := paperCutoff_conditions hn1
  exact hc m₀ p hp hinj hpair E z hD0 s hcop0 hK A c hM _ h1 h2 h3

end Moments

end Sarkozy.Functional
