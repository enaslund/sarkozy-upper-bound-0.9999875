module

public import Sarkozy.Functional.FibreScale

@[expose] public section

/-!
# The fibre class and the moments of the square-step model

Two complements to `lem:record:fibre-scale` (`paper/sections/08_scale_comparison.tex`)
and to `Sarkozy.Functional.FibreScale`:

* The Chinese remainder theorem for the fibre. With `D₀` coprime to every
  coordinate modulus and pairwise coprime moduli, there is a unique class
  `𝔞 mod D`, `D = D₀ D_E`, with `𝔞 ≡ s (mod D₀)` and `𝔞 ≡ z_j (mod m_j)` for
  `j ∈ E` (`existsUnique_fibreClass`), and the fibre predicate `InFibre` used in
  `FibreScale` is exactly `x ≡ 𝔞 (mod D)` (`inFibre_iff_fibreClass`). Hence
  `|J_𝔞| = R/D` when `D ∣ R` (`card_stepResidues`), the parenthetical claim of
  `lem:record:fibre-scale`(b).
* `lem:record:fibre-scale`(e), derived from the lift-moment bound
  `lem:record:lift-moments`(c), which is taken as a hypothesis on the pieces
  `h_j` (`moment_squareStepModel`). The paper argues with Minkowski's inequality
  and the concavity of `x ↦ x^{1/(2r)}`; here the same bound
  `‖g̃‖_{2r}^{2r} ≤ C λ^{2r−1} α_f` is obtained from the pointwise convexity
  (power-mean) inequality with the weights `D/R`, which sum to one over `J_𝔞`.
  Any exponent `p ≥ 1` is allowed (the paper uses `p = 2r`).
-/

open Finset Complex
open scoped BigOperators ComplexConjugate

namespace Sarkozy.Functional

open Sarkozy.FourierArithmetic

section CRT

variable {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)]

omit [Fintype J] [DecidableEq J] [∀ j, NeZero (m j)] in
/-- Two integers of the fibre are congruent modulo `D = D₀ ∏_{j ∈ E} m_j`. -/
theorem dvd_sub_of_inFibre {E : Finset J} {z : ResidueSpace m} {D0 : ℕ} {s : ZMod D0}
    (hcop0 : ∀ k, D0.Coprime (m k)) (hpair : Pairwise fun i j => (m i).Coprime (m j))
    {x y : ℤ} (hx : InFibre m E z s x) (hy : InFibre m E z s y) :
    ((D0 * ∏ j ∈ E, m j : ℕ) : ℤ) ∣ x - y := by
  have h0 : (D0 : ℤ) ∣ x - y :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub y x D0).mp (hy.1.trans hx.1.symm)
  have hE : ∀ j ∈ E, ((m j : ℕ) : ℤ) ∣ x - y := fun j hj =>
    (ZMod.intCast_eq_intCast_iff_dvd_sub y x (m j)).mp ((hy.2 j hj).trans (hx.2 j hj).symm)
  have hprod : (∏ j ∈ E, ((m j : ℕ) : ℤ)) ∣ x - y := by
    apply Finset.prod_dvd_of_coprime _ hE
    intro i _ j _ hij
    exact Nat.isCoprime_iff_coprime.mpr (hpair hij)
  have hco : IsCoprime (D0 : ℤ) (∏ j ∈ E, ((m j : ℕ) : ℤ)) :=
    IsCoprime.prod_right fun j _ => Nat.isCoprime_iff_coprime.mpr (hcop0 j)
  push_cast
  exact hco.mul_dvd h0 hprod

omit [Fintype J] [DecidableEq J] [∀ j, NeZero (m j)] in
/-- The fibre is a union of classes modulo `D`. -/
theorem inFibre_of_dvd_sub {E : Finset J} {z : ResidueSpace m} {D0 : ℕ} {s : ZMod D0}
    {x y : ℤ} (hy : InFibre m E z s y) (hxy : ((D0 * ∏ j ∈ E, m j : ℕ) : ℤ) ∣ x - y) :
    InFibre m E z s x := by
  constructor
  · have hd : (D0 : ℤ) ∣ x - y := by
      apply dvd_trans _ hxy
      exact_mod_cast dvd_mul_right D0 _
    rw [← hy.1]
    exact ((ZMod.intCast_eq_intCast_iff_dvd_sub y x D0).mpr hd).symm
  · intro j hj
    have hd : ((m j : ℕ) : ℤ) ∣ x - y := by
      apply dvd_trans _ hxy
      exact_mod_cast (Finset.dvd_prod_of_mem m hj).trans (dvd_mul_left _ D0)
    rw [← hy.2 j hj]
    exact ((ZMod.intCast_eq_intCast_iff_dvd_sub y x (m j)).mpr hd).symm

omit [Fintype J] in
/-- The Chinese remainder theorem: the fibre is nonempty. -/
theorem exists_inFibre {E : Finset J} (z : ResidueSpace m) {D0 : ℕ} (hD0 : 1 ≤ D0) (s : ZMod D0)
    (hcop0 : ∀ k, D0.Coprime (m k)) (hpair : Pairwise fun i j => (m i).Coprime (m j)) :
    ∃ x : ℕ, ((x : ℤ) : ZMod D0) = s ∧ ∀ j ∈ E, ((x : ℤ) : ZMod (m j)) = z j := by
  have : NeZero D0 := ⟨by omega⟩
  induction E using Finset.induction_on with
  | empty =>
    refine ⟨s.val, ?_, fun j hj => absurd hj (Finset.notMem_empty j)⟩
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  | @insert a E ha ih =>
    obtain ⟨x, hx0, hxE⟩ := ih
    have hco : (D0 * ∏ j ∈ E, m j).Coprime (m a) := by
      apply Nat.Coprime.mul_left (hcop0 a)
      apply Nat.Coprime.prod_left
      intro j hj
      exact hpair (fun h => ha (h ▸ hj))
    obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hco x (z a).val
    refine ⟨k, ?_, ?_⟩
    · rw [Int.cast_natCast, ← hx0, Int.cast_natCast]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hk1.of_dvd (dvd_mul_right D0 _))
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · rw [Int.cast_natCast, ← ZMod.natCast_zmod_val (z j)]
        exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hk2
      · rw [Int.cast_natCast, ← hxE j hj, Int.cast_natCast]
        exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr
          (hk1.of_dvd ((Finset.dvd_prod_of_mem m hj).trans (dvd_mul_left _ D0)))

/-- The CRT class `𝔞 mod D`, `D = D₀ D_E`, of `s mod D₀` and of `z` on `E`
(`lem:record:fibre-scale`). It is the class of any integer of the fibre (and
`0` if the fibre is empty, which does not happen under the coprimality
hypotheses, `exists_inFibre`). -/
noncomputable def fibreClass (E : Finset J) (z : ResidueSpace m) {D0 : ℕ} (s : ZMod D0) :
    ZMod (D0 * ∏ j ∈ E, m j) := by
  classical
  exact if h : ∃ x : ℤ, InFibre m E z s x then ((Classical.choose h : ℤ) : ZMod _) else 0

omit [Fintype J] in
/-- The fibre predicate of `FibreScale` is the congruence `x ≡ 𝔞 (mod D)`. -/
theorem inFibre_iff_fibreClass {E : Finset J} (z : ResidueSpace m) {D0 : ℕ} (hD0 : 1 ≤ D0)
    (s : ZMod D0) (hcop0 : ∀ k, D0.Coprime (m k))
    (hpair : Pairwise fun i j => (m i).Coprime (m j)) (x : ℤ) :
    InFibre m E z s x ↔ (x : ZMod (D0 * ∏ j ∈ E, m j)) = fibreClass m E z s := by
  obtain ⟨x0, hx0⟩ := exists_inFibre m (E := E) z hD0 s hcop0 hpair
  have hex : ∃ x : ℤ, InFibre m E z s x := ⟨x0, hx0⟩
  have hspec : InFibre m E z s (Classical.choose hex) := Classical.choose_spec hex
  have hdef : fibreClass m E z s = ((Classical.choose hex : ℤ) : ZMod (D0 * ∏ j ∈ E, m j)) := by
    unfold fibreClass
    rw [dite_eq_left hex]
  rw [hdef]
  constructor
  · intro hx
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr
      (dvd_sub_of_inFibre m hcop0 hpair hspec hx)
  · intro hx
    exact inFibre_of_dvd_sub m hspec ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hx.symm)

omit [Fintype J] in
/-- `lem:record:fibre-scale`: the class `𝔞 mod D` with `𝔞 ≡ s (mod D₀)` and
`𝔞 ≡ z_j (mod m_j)` for `j ∈ E` exists and is unique. -/
theorem existsUnique_fibreClass {E : Finset J} (z : ResidueSpace m) {D0 : ℕ} (hD0 : 1 ≤ D0)
    (s : ZMod D0) (hcop0 : ∀ k, D0.Coprime (m k))
    (hpair : Pairwise fun i j => (m i).Coprime (m j)) :
    ∃! 𝔞 : ZMod (D0 * ∏ j ∈ E, m j),
      (𝔞.cast : ZMod D0) = s ∧ ∀ j ∈ E, (𝔞.cast : ZMod (m j)) = z j := by
  have hD : NeZero (D0 * ∏ j ∈ E, m j) :=
    ⟨Nat.mul_ne_zero (by omega) (prod_ne_zero_iff.mpr fun j _ => NeZero.ne (m j))⟩
  have hdvd0 : D0 ∣ D0 * ∏ j ∈ E, m j := dvd_mul_right _ _
  have hdvdE : ∀ j ∈ E, m j ∣ D0 * ∏ j ∈ E, m j := fun j hj =>
    (Finset.dvd_prod_of_mem m hj).trans (dvd_mul_left _ D0)
  -- an element satisfies the congruences iff its representative lies in the fibre
  have hchar : ∀ 𝔞 : ZMod (D0 * ∏ j ∈ E, m j),
      ((𝔞.cast : ZMod D0) = s ∧ ∀ j ∈ E, (𝔞.cast : ZMod (m j)) = z j) ↔
        InFibre m E z s (𝔞.val : ℤ) := by
    intro 𝔞
    have h1 : ((𝔞.val : ℤ) : ZMod D0) = (𝔞.cast : ZMod D0) := by
      rw [ZMod.cast_eq_val, Int.cast_natCast]
    have h2 : ∀ j, ((𝔞.val : ℤ) : ZMod (m j)) = (𝔞.cast : ZMod (m j)) := by
      intro j; rw [ZMod.cast_eq_val, Int.cast_natCast]
    unfold InFibre
    rw [h1]
    simp only [h2]
  refine ⟨fibreClass m E z s, (hchar _).mpr ?_, ?_⟩
  · rw [inFibre_iff_fibreClass m z hD0 s hcop0 hpair, Int.cast_natCast,
      ZMod.natCast_zmod_val]
  · intro 𝔟 h𝔟
    have h := (hchar 𝔟).mp h𝔟
    rw [inFibre_iff_fibreClass m z hD0 s hcop0 hpair, Int.cast_natCast,
      ZMod.natCast_zmod_val] at h
    exact h

/-- `lem:record:fibre-scale`(b): `|J_𝔞| = R/D`, i.e. `|J_𝔞| · D = R`, when `D ∣ R`. -/
theorem card_stepResidues {E : Finset J} (z : ResidueSpace m) {D0 : ℕ} (hD0 : 1 ≤ D0)
    (s : ZMod D0) (hcop0 : ∀ k, D0.Coprime (m k))
    (hpair : Pairwise fun i j => (m i).Coprime (m j)) {R : ℕ} (hR : 1 ≤ R)
    (hDR : D0 * ∏ j ∈ E, m j ∣ R) (c : ℤ) :
    (stepResidues m E z s R c).card * (D0 * ∏ j ∈ E, m j) = R := by
  have : NeZero R := ⟨by omega⟩
  have hcard := card_residueFibre hDR (fibreClass m E z s - (c : ZMod (D0 * ∏ j ∈ E, m j)))
  have hcast : ∀ t : ℤ, ZMod.castHom hDR (ZMod (D0 * ∏ j ∈ E, m j)) (t : ZMod R) =
      (t : ZMod (D0 * ∏ j ∈ E, m j)) := fun t => by
    rw [ZMod.castHom_apply, ZMod.cast_intCast hDR]
  have hfib : ∀ t : ℤ, InFibre m E z s (t + c) ↔
      (t : ZMod (D0 * ∏ j ∈ E, m j)) = fibreClass m E z s - (c : ZMod _) := by
    intro t
    rw [inFibre_iff_fibreClass m z hD0 s hcop0 hpair, eq_sub_iff_add_eq]
    push_cast
    rfl
  have hcardeq : (stepResidues m E z s R c).card =
      (residueFibre hDR (fibreClass m E z s - (c : ZMod (D0 * ∏ j ∈ E, m j)))).card := by
    apply card_nbij' (fun j : ℤ => (j : ZMod R)) (fun t => ((leastPosRep t : ℕ) : ℤ))
    · intro j hj
      rw [Finset.mem_coe] at hj ⊢
      have hj' := (mem_filter.mp hj).2
      unfold residueFibre
      rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      rw [hcast]
      exact (hfib j).mp hj'
    · intro t ht
      rw [Finset.mem_coe] at ht ⊢
      have ht' : ZMod.castHom hDR (ZMod (D0 * ∏ j ∈ E, m j)) t =
          fibreClass m E z s - (c : ZMod _) := (mem_filter.mp ht).2
      dsimp only
      unfold stepResidues
      rw [mem_filter, mem_Icc]
      refine ⟨⟨by exact_mod_cast one_le_leastPosRep t, by exact_mod_cast leastPosRep_le t⟩, ?_⟩
      rw [hfib, ← ht', ← hcast, Int.cast_natCast, natCast_leastPosRep t]
    · intro j hj
      rw [Finset.mem_coe] at hj
      have hj' := mem_Icc.mp (mem_filter.mp hj).1
      have hj0 : 0 ≤ j := by omega
      have hjt : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg hj0
      simp only
      rw [← hjt, Int.cast_natCast, leastPosRep_natCast (by omega) (by omega)]
    · intro t _
      simp only [Int.cast_natCast, natCast_leastPosRep]
  rw [hcardeq]
  exact hcard

end CRT

/-! ### `lem:record:fibre-scale`(e): moments of the square-step model -/

section Moments

variable {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)]

/-- The pieces `h_j` are functions on `X_𝒮`: they depend only on the
coordinates off `E`, since the labels in `retainedOff` vanish on `E`. -/
theorem stepLift_congr {E : Finset J} {Q' : ℝ} (B : Finset ℤ) (n : ℕ) {y y' : ResidueSpace m}
    (h : ∀ k ∉ E, y k = y' k) : stepLift m E Q' B n y = stepLift m E Q' B n y' := by
  unfold stepLift liftOn
  apply sum_congr rfl
  intro b hb
  have hbE : ∀ i ∈ E, b i = 0 := (mem_filter.mp hb).2.1
  congr 1
  unfold prodChar
  apply prod_congr rfl
  intro k _
  by_cases hk : k ∈ E
  · simp [hbE k hk]
  · rw [h k hk]

/-- `T_j` acting off `E` and as the identity on `E`. -/
noncomputable def stepMapOff (E : Finset J) (R : ℕ) (c j : ℤ)
    (y : ResidueSpace m) : ResidueSpace m :=
  fun k => if k ∈ E then y k else stepMap m R c j y k

/-- If `R` is a unit off `E`, `stepMapOff` is a bijection of the group. -/
theorem stepMapOff_bijective {E : Finset J} {R : ℕ} (hcop : ∀ k ∉ E, R.Coprime (m k))
    (c j : ℤ) : Function.Bijective (stepMapOff m E R c j) := by
  apply Finite.injective_iff_bijective.mp
  intro y y' h
  funext k
  have hk := congrFun h k
  by_cases hkE : k ∈ E
  · simpa [stepMapOff, hkE] using hk
  · simp only [stepMapOff, hkE, ↓reduceIte, stepMap] at hk
    have hu : (R : ZMod (m k)) * (R : ZMod (m k))⁻¹ = 1 :=
      ZMod.coe_mul_inv_eq_one R (hcop k hkE)
    have h2 := congrArg (fun t => (R : ZMod (m k)) * t) hk
    simp only [← mul_assoc, hu, one_mul] at h2
    exact sub_left_injective h2

/-- `T_j` preserves the uniform measure on functions of the coordinates off `E`
(proof of `lem:record:fibre-scale`(e)). -/
theorem expect_stepLift_comp {E : Finset J} {Q' : ℝ} (B : Finset ℤ) (n : ℕ) {R : ℕ}
    (hcop : ∀ k ∉ E, R.Coprime (m k)) (c j : ℤ) (φ : ℂ → ℝ) :
    𝔼 y, φ (stepLift m E Q' B n (stepMap m R c j y)) = 𝔼 y, φ (stepLift m E Q' B n y) := by
  have hcongr : ∀ y, stepLift m E Q' B n (stepMap m R c j y) =
      stepLift m E Q' B n (stepMapOff m E R c j y) := by
    intro y
    apply stepLift_congr
    intro k hk
    simp [stepMapOff, hk]
  simp_rw [hcongr]
  rw [expect_eq_sum_div_card, expect_eq_sum_div_card]
  congr 1
  exact Fintype.sum_bijective _ (stepMapOff_bijective m hcop c j) _ _ (fun y => rfl)

/-- `lem:record:fibre-scale`(e), derived from the moment bound of the pieces
(`lem:record:lift-moments`(c)): if `E_y |h_j|^p ≤ C α_j` for every
`j ∈ J_𝔞`, `α_j = |A'_j|/n`, then `E_y |g̃|^p ≤ C λ^{p-1} α_f`, with
`λ = Rn/|I|` and `α_f = (D/|I|) #{x ∈ A ∩ I : x ≡ 𝔞 (D)}`. The paper's case is
`p = 2r` and `C = C_{r,ε} N^ε`; its hypothesis `n ≥ 10 n^{6β}` is used only
to obtain the bound on the pieces. -/
theorem moment_squareStepModel {E : Finset J} (z : ResidueSpace m) {D0 : ℕ} (hD0 : 1 ≤ D0)
    (s : ZMod D0) (hcop0 : ∀ k, D0.Coprime (m k))
    (hpair : Pairwise fun i j => (m i).Coprime (m j))
    (A : Finset ℤ) (c : ℤ) {M R n : ℕ} (hM : 1 ≤ M) (hR : 1 ≤ R) (hMR : M ≤ R * n)
    (hDR : D0 * ∏ j ∈ E, m j ∣ R) (hcop : ∀ k ∉ E, R.Coprime (m k)) (Q' : ℝ)
    {p : ℕ} (hp : 1 ≤ p) {C : ℝ}
    (hmom : ∀ j ∈ stepResidues m E z s R c,
      𝔼 y, ‖stepLift m E Q' (stepChild A (Icc (c + 1) (c + M)) R n c j) n y‖ ^ p ≤
        C * (((stepChild A (Icc (c + 1) (c + M)) R n c j).card : ℝ) / n)) :
    𝔼 y, ‖squareStepModel m E z s A (Icc (c + 1) (c + M)) c M R n Q' y‖ ^ p ≤
      C * ((R * n : ℝ) / M) ^ (p - 1) *
        ((((D0 * ∏ j ∈ E, m j : ℕ) : ℝ) / M) *
          ((A ∩ Icc (c + 1) (c + M)).filter (InFibre m E z s)).card) := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; omega
    · exact h
  have hD0R : D0 ∣ R := (dvd_mul_right D0 _).trans hDR
  have hER : ∀ i ∈ E, m i ∣ R := fun i hi =>
    ((Finset.dvd_prod_of_mem m hi).trans (dvd_mul_left _ D0)).trans hDR
  set I := Icc (c + 1) (c + (M : ℤ)) with hI
  set S := stepResidues m E z s R c with hS
  set D : ℕ := D0 * ∏ j ∈ E, m j with hD
  set lam : ℝ := (R * n : ℝ) / M with hlam
  set w : ℝ := (D : ℝ) / R with hw
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hlampos : 0 < lam := by positivity
  have hw0 : 0 ≤ w := by positivity
  -- the weights `D/R` sum to one over `J_𝔞`
  have hwsum : ∑ _j ∈ S, w = 1 := by
    rw [sum_const, nsmul_eq_mul, hw]
    have hc := card_stepResidues m z hD0 s hcop0 hpair hR hDR c
    have hc' : ((S.card : ℝ) * (D : ℝ)) = R := by exact_mod_cast hc
    rw [mul_div_assoc', hc', div_self hRpos.ne']
  -- pointwise convexity bound
  have hpoint : ∀ y, ‖squareStepModel m E z s A I c M R n Q' y‖ ^ p ≤
      lam ^ p * ∑ j ∈ S, w * ‖stepLift m E Q' (stepChild A I R n c j) n (stepMap m R c j y)‖ ^ p := by
    intro y
    have hscal : ((R * n : ℂ) / M) * ((D : ℕ) : ℂ) / R = ((lam * w : ℝ) : ℂ) := by
      rw [hlam, hw]
      push_cast
      ring
    have hnorm : ‖squareStepModel m E z s A I c M R n Q' y‖ ≤
        lam * ∑ j ∈ S, w * ‖stepLift m E Q' (stepChild A I R n c j) n (stepMap m R c j y)‖ := by
      unfold squareStepModel
      rw [hscal, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hlampos.le hw0), ← mul_sum, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hlampos.le
      apply mul_le_mul_of_nonneg_left (norm_sum_le _ _) hw0
    calc ‖squareStepModel m E z s A I c M R n Q' y‖ ^ p
        ≤ (lam * ∑ j ∈ S,
            w * ‖stepLift m E Q' (stepChild A I R n c j) n (stepMap m R c j y)‖) ^ p :=
          pow_le_pow_left₀ (norm_nonneg _) hnorm p
      _ = lam ^ p * (∑ j ∈ S,
            w * ‖stepLift m E Q' (stepChild A I R n c j) n (stepMap m R c j y)‖) ^ p := by
          rw [mul_pow]
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hlampos.le p)
          exact Real.pow_arith_mean_le_arith_mean_pow S (fun _ => w)
            (fun j => ‖stepLift m E Q' (stepChild A I R n c j) n (stepMap m R c j y)‖)
            (fun _ _ => hw0) hwsum (fun _ _ => norm_nonneg _) p
  -- average over the group
  have hdens := stepChild_density m (E := E) (z := z) (s := s) A c hM hR hMR hD0R hER
  calc 𝔼 y, ‖squareStepModel m E z s A I c M R n Q' y‖ ^ p
      ≤ 𝔼 y, lam ^ p * ∑ j ∈ S,
          w * ‖stepLift m E Q' (stepChild A I R n c j) n (stepMap m R c j y)‖ ^ p :=
        expect_le_expect fun y _ => hpoint y
    _ = lam ^ p * ∑ j ∈ S, w *
          𝔼 y, ‖stepLift m E Q' (stepChild A I R n c j) n (stepMap m R c j y)‖ ^ p := by
        rw [← mul_expect, expect_sum_comm]
        congr 1
        apply sum_congr rfl
        intro j _
        rw [mul_expect]
    _ = lam ^ p * ∑ j ∈ S, w *
          𝔼 y, ‖stepLift m E Q' (stepChild A I R n c j) n y‖ ^ p := by
        congr 1
        apply sum_congr rfl
        intro j _
        rw [expect_stepLift_comp m _ n hcop c j (fun t => ‖t‖ ^ p)]
    _ ≤ lam ^ p * ∑ j ∈ S, w * (C * (((stepChild A I R n c j).card : ℝ) / n)) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hlampos.le p)
        apply sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hmom j hj) hw0
    _ = lam ^ p * C * (w * ∑ j ∈ S, (((stepChild A I R n c j).card : ℝ) / n)) := by
        rw [mul_assoc (lam ^ p) C]
        congr 1
        rw [mul_sum, mul_sum]
        apply sum_congr rfl
        intro j _
        ring
    _ = lam ^ p * C * (((D : ℝ) / M * ((A ∩ I).filter (InFibre m E z s)).card) / lam) := by
        rw [hw, hdens]
    _ = _ := by
        have hp' : lam ^ p = lam ^ (p - 1) * lam := by
          rw [← pow_succ, Nat.sub_add_cancel hp]
        rw [hp']
        field_simp

/-- `lem:record:fibre-scale`(e) with the paper's parameters: `R = sq(D)`,
`D = D₀ D_E`, `ℓ = ⌈|I|/(KR)⌉` and `n = Kℓ` (`stepScale`). -/
theorem moment_squareStepModel_sq {E : Finset J} (z : ResidueSpace m) {D0 : ℕ} (hD0 : 1 ≤ D0)
    (s : ZMod D0) (hcop0 : ∀ k, D0.Coprime (m k))
    (hpair : Pairwise fun i j => (m i).Coprime (m j)) {K : ℕ} (hK : 1 ≤ K)
    (A : Finset ℤ) (c : ℤ) {M R n : ℕ} (hM : 1 ≤ M)
    (hRdef : R = leastSquare (D0 * ∏ j ∈ E, m j)) (hndef : n = K * stepScale K M R)
    (Q' : ℝ) {p : ℕ} (hp : 1 ≤ p) {C : ℝ}
    (hmom : ∀ j ∈ stepResidues m E z s R c,
      𝔼 y, ‖stepLift m E Q' (stepChild A (Icc (c + 1) (c + M)) R n c j) n y‖ ^ p ≤
        C * (((stepChild A (Icc (c + 1) (c + M)) R n c j).card : ℝ) / n)) :
    𝔼 y, ‖squareStepModel m E z s A (Icc (c + 1) (c + M)) c M R n Q' y‖ ^ p ≤
      C * ((R * n : ℝ) / M) ^ (p - 1) *
        ((((D0 * ∏ j ∈ E, m j : ℕ) : ℝ) / M) *
          ((A ∩ Icc (c + 1) (c + M)).filter (InFibre m E z s)).card) := by
  obtain ⟨hR, _, _, hcop⟩ := leastSquare_step_conditions m (E := E) hD0 hcop0 hpair
  have hD : D0 * ∏ j ∈ E, m j ≠ 0 :=
    Nat.mul_ne_zero (by omega) (prod_ne_zero_iff.mpr fun j _ => NeZero.ne (m j))
  subst hRdef
  have hMR := (stepScale_bounds (M := M) hK hR).1
  rw [← hndef] at hMR
  exact moment_squareStepModel m z hD0 s hcop0 hpair A c hM hR hMR (dvd_leastSquare hD) hcop Q'
    hp hmom

end Moments

end Sarkozy.Functional
