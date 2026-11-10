module

public import Sarkozy.CancellationSteps.Analytic

/-!
# The equidistribution of the fibre classes (Step 3 of `lem:record:density-can`)

`paper/sections/08_scale_comparison.tex`, `lem:record:density-can`, Step 3: "the class `𝔞₁` is
uniform among the classes modulo `D` above `s`". For the encoded data of a query:

* `sum_range_modEq`: for a `D`-periodic `f`, `∑_{c < D} [c ≡ a (D)] f(c) = f(a)`;
* `card_pairAlphabet_fst`: in `Ω_q = {(x, y) : y − x a nonzero square}` every first coordinate
  occurs `|sqSet|` times, so the first coordinate of `Unif(Ω_q)` is uniform;
* `frozen_uniform`: under `μ ⊗ Unif(∏ Ω)` the frozen label of a slot, restricted to the
  conditioned coordinates `E`, is uniform: it takes each value with probability `(∏_E m)⁻¹`
  (the low atoms by `HasUniformMarginals`, the primes of `U` by `card_pairAlphabet_fst`);
* `equidist_fibreClass`: hence, for every class `𝔞₁` of the fibres, `E f(𝔞₁) =
  (M₀/D) ∑_{c < D, c ≡ s (M₀)} f(c)` for `D`-periodic `f`, the first clause of `FibreEquidist`.

New material for this paper.
-/

@[expose] public section

namespace Sarkozy.CancellationSteps

open Finset
open scoped BigOperators
open Sarkozy.Cancellation Sarkozy.Mixing Sarkozy.PaperFrame Sarkozy.FourierArithmetic
  Sarkozy.Functional

/-! ## Periodic sums -/

lemma periodic_add_mul {f : ℤ → ℝ} {D : ℕ} (hf : ∀ c, f (c + D) = f c) (x k : ℤ) :
    f (x + D * k) = f x := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [show x + (D : ℤ) * (k + 1) = (x + D * k) + D by ring, hf, ih]
  | pred k ih =>
    have h := hf (x + D * (-(k : ℤ) - 1))
    rw [show x + (D : ℤ) * (-(k : ℤ) - 1) + D = x + D * (-(k : ℤ)) by ring, ih] at h
    exact h.symm

lemma periodic_of_modEq {f : ℤ → ℝ} {D : ℕ} (hf : ∀ c, f (c + D) = f c) {a b : ℤ}
    (h : a ≡ b [ZMOD D]) : f a = f b := by
  obtain ⟨k, hk⟩ := (Int.modEq_iff_dvd.mp h)
  have hb : b = a + D * k := by linarith
  rw [hb, periodic_add_mul hf]

/-- For a `D`-periodic `f`, `∑_{c < D} [c ≡ a (D)] f(c) = f(a)`. -/
lemma sum_range_modEq {f : ℤ → ℝ} {D : ℕ} (hD : 0 < D) (hf : ∀ c, f (c + D) = f c) (a : ℤ) :
    ∑ c ∈ range D, (if (c : ℤ) ≡ a [ZMOD D] then f c else 0) = f a := by
  have hDz : (0 : ℤ) < D := by exact_mod_cast hD
  have hmod0 : 0 ≤ a % (D : ℤ) := Int.emod_nonneg a hDz.ne'
  have hlt : a % (D : ℤ) < D := Int.emod_lt_of_pos a hDz
  set c₀ : ℕ := (a % (D : ℤ)).toNat with hc₀
  have hc₀z : (c₀ : ℤ) = a % (D : ℤ) := Int.toNat_of_nonneg hmod0
  have hc₀mod : (c₀ : ℤ) ≡ a [ZMOD D] := by rw [hc₀z]; exact Int.mod_modEq a D
  rw [sum_eq_single c₀]
  · simp only [hc₀mod, ↓reduceIte]
    exact periodic_of_modEq hf hc₀mod
  · intro c hc hne
    have hc' : (c : ℤ) < D := by exact_mod_cast (mem_range.mp hc)
    have : ¬ (c : ℤ) ≡ a [ZMOD D] := by
      intro h
      apply hne
      have h1 : (c : ℤ) % D = a % D := h
      rw [Int.emod_eq_of_lt (by positivity) hc'] at h1
      have : (c : ℤ) = c₀ := by rw [hc₀z, h1]
      exact_mod_cast this
    simp only [this, ↓reduceIte]
  · intro h
    exact absurd (mem_range.mpr (by omega)) h

/-! ## The first coordinate of the strict-square pairs -/

section PairFst

variable {K : Type*} [Fintype K] [DecidableEq K] (q : K → ℕ) [∀ j, NeZero (q j)]

omit [Fintype K] [DecidableEq K] in
/-- In `Ω_q` every first coordinate occurs `|sqSet|` times. -/
lemma card_pairAlphabet_fst (j : K) (x₀ : ZMod (q j)) :
    (univ.filter (fun a : PairAlphabet q j => a.1.1 = x₀)).card = (sqSet q j).card := by
  refine card_bij (fun a _ => a.1.2 - a.1.1) (fun a ha => a.2) ?_ ?_
  · intro a ha b hb hab
    have ha' := (mem_filter.mp ha).2
    have hb' := (mem_filter.mp hb).2
    apply Subtype.ext
    apply Prod.ext
    · rw [ha', hb']
    · have : a.1.2 = b.1.2 := by
        have h := hab
        rw [ha', hb'] at h
        exact sub_left_injective h
      exact this
  · intro d hd
    refine ⟨⟨(x₀, x₀ + d), by simpa using hd⟩, mem_filter.mpr ⟨mem_univ _, rfl⟩, ?_⟩
    simp

omit [Fintype K] [DecidableEq K] in
/-- The first coordinate of `Unif(Ω_q)` is uniform: `|Ω_q|⁻¹ #{a : a₁ = x₀} = q⁻¹`. -/
lemma prob_pairAlphabet_fst [∀ j, Fact (q j).Prime] (j : K) (x₀ : ZMod (q j)) :
    (Fintype.card (PairAlphabet q j) : ℝ)⁻¹ *
        ((univ.filter (fun a : PairAlphabet q j => a.1.1 = x₀)).card : ℝ) = (q j : ℝ)⁻¹ := by
  have hfib : ∀ x : ZMod (q j),
      (univ.filter (fun a : PairAlphabet q j => a.1.1 = x)).card = (sqSet q j).card :=
    card_pairAlphabet_fst q j
  have htot : Fintype.card (PairAlphabet q j) = q j * (sqSet q j).card := by
    rw [← card_univ, card_eq_sum_card_fiberwise (f := fun a : PairAlphabet q j => a.1.1)
      (t := univ) (fun _ _ => mem_univ _)]
    simp only [hfib, sum_const, card_univ, ZMod.card, smul_eq_mul]
  rw [hfib, htot]
  have hs : (0 : ℝ) < (sqSet q j).card := by exact_mod_cast card_sqSet_pos q j
  have hq : (0 : ℝ) < q j := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (q j))
  push_cast
  field_simp

end PairFst

/-! ## The frozen label restricted to `E` is uniform -/

section Frozen

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]

/-- The target labels at the atoms of a point `z₀` of `G_N`. -/
noncomputable def atomTarget (L : ℕ) (z₀ : ResidueSpace (joinModuli m₀ (p L))) :
    ∀ b, AtomLabel m₀ p L b :=
  (atomGroupEquiv m₀ p L).symm z₀

omit [Fintype J₀] [DecidableEq J₀] [∀ i, NeZero (m₀ i)] [∀ L, Fintype (J L)]
  [∀ L, DecidableEq (J L)] [∀ L j, NeZero (p L j)] in
lemma atomTarget_none (L : ℕ) (z₀ : ResidueSpace (joinModuli m₀ (p L))) (i : J₀) :
    atomTarget m₀ p L z₀ none i = z₀ (Sum.inl i) := rfl

omit [Fintype J₀] [DecidableEq J₀] [∀ i, NeZero (m₀ i)] [∀ L, Fintype (J L)]
  [∀ L, DecidableEq (J L)] [∀ L j, NeZero (p L j)] in
lemma atomTarget_some (L : ℕ) (z₀ : ResidueSpace (joinModuli m₀ (p L))) (j : J L) :
    atomTarget m₀ p L z₀ (some j) = z₀ (Sum.inr j) := rfl

omit [DecidableEq J₀] [∀ i, NeZero (m₀ i)] [∀ L, DecidableEq (J L)] [∀ L j, NeZero (p L j)] in
lemma inl_mem_frozenCoords (L P5 : ℕ) (U : TailIdx p L P5 → Bool) (i : J₀) :
    (Sum.inl i : J₀ ⊕ J L) ∈ frozenCoords (J₀ := J₀) p L P5 U := by
  by_contra h
  exact (not_mem_frozenCoords p L P5 U _).mp h

omit [DecidableEq J₀] [∀ i, NeZero (m₀ i)] [∀ L, DecidableEq (J L)] [∀ L j, NeZero (p L j)] in
lemma inr_mem_frozenCoords_low (L P5 : ℕ) (U : TailIdx p L P5 → Bool) {j : J L}
    (hj : p L j < P5) : (Sum.inr j : J₀ ⊕ J L) ∈ frozenCoords (J₀ := J₀) p L P5 U := by
  by_contra h
  obtain ⟨h1, _⟩ := (not_mem_frozenCoords p L P5 U _).mp h
  omega

omit [DecidableEq J₀] [∀ i, NeZero (m₀ i)] [∀ L, DecidableEq (J L)] [∀ L j, NeZero (p L j)] in
lemma inr_mem_frozenCoords_U (L P5 : ℕ) (U : TailIdx p L P5 → Bool) {k : TailIdx p L P5}
    (hk : U k = true) : (Sum.inr k.1 : J₀ ⊕ J L) ∈ frozenCoords (J₀ := J₀) p L P5 U := by
  by_contra h
  obtain ⟨h1, h2⟩ := (not_mem_frozenCoords p L P5 U _).mp h
  have : U k = false := h2
  rw [hk] at this
  exact Bool.noConfusion this

omit [DecidableEq J₀] [∀ i, NeZero (m₀ i)] [∀ L j, NeZero (p L j)] in
/-- The frozen label agrees with `z₀` on `E` iff every low label of the slot is the target and
every tail label at a prime of `U` is the target. -/
lemma frozen_eq_iff (L P5 : ℕ) (U : TailIdx p L P5 → Bool) (w : Slot) (x : LowLabels m₀ p L P5)
    (y : ∀ k : TailIdx p L P5, ZMod (tailQ p L P5 k)) (z₀ : ResidueSpace (joinModuli m₀ (p L))) :
    (∀ e ∈ frozenCoords (J₀ := J₀) p L P5 U, frozenAt m₀ p L P5 w x y e = z₀ e) ↔
      (∀ i : {b : PaperAtom J L // IsLow p L P5 b}, x i w = atomTarget m₀ p L z₀ i.1) ∧
        (∀ k : TailIdx p L P5, U k = true → y k = z₀ (Sum.inr k.1)) := by
  constructor
  · intro h
    refine ⟨fun i => ?_, fun k hk => ?_⟩
    · obtain ⟨b, hb⟩ := i
      cases b with
      | none =>
        funext i'
        have := h (Sum.inl i') (inl_mem_frozenCoords p L P5 U i')
        rw [frozenAt_inl] at this
        exact this
      | some j =>
        have hj : p L j < P5 := hb j rfl
        have := h (Sum.inr j) (inr_mem_frozenCoords_low p L P5 U hj)
        rw [frozenAt_low m₀ p L P5 w x y j hb] at this
        exact this
    · have := h (Sum.inr k.1) (inr_mem_frozenCoords_U p L P5 U hk)
      rw [frozenAt_tail] at this
      exact this
  · rintro ⟨h1, h2⟩ e he
    cases e with
    | inl i =>
      rw [frozenAt_inl]
      exact congrFun (h1 ⟨none, isLow_none p L P5⟩) i
    | inr j =>
      by_cases hj : p L j < P5
      · have hlow : IsLow p L P5 (some j) := fun j' h => by cases h; exact hj
        rw [frozenAt_low m₀ p L P5 w x y j hlow]
        exact h1 ⟨some j, hlow⟩
      · have hj' : P5 ≤ p L j := not_lt.mp hj
        have hU : U ⟨j, hj'⟩ = true := by
          by_contra hU
          exact (not_mem_frozenCoords p L P5 U (Sum.inr j : J₀ ⊕ J L)).mpr
            ⟨hj', by simpa using hU⟩ he
        have := frozenAt_tail m₀ p L P5 w x y ⟨j, hj'⟩
        rw [this]
        exact h2 ⟨j, hj'⟩ hU

/-- `∏_{b low} |AtomLabel b| = ∏ m₀ · ∏_{p_j < P₅} p_j`. -/
lemma prod_card_lowAtoms (L P5 : ℕ) :
    ∏ i : {b : PaperAtom J L // IsLow p L P5 b}, (Fintype.card (AtomLabel m₀ p L i.1) : ℝ) =
      ((∏ i, m₀ i : ℕ) : ℝ) * ((∏ j ∈ univ.filter (fun j => p L j < P5), p L j : ℕ) : ℝ) := by
  classical
  rw [← Finset.prod_subtype (univ.filter (IsLow p L P5)) (fun b => by simp)
    (fun b => (Fintype.card (AtomLabel m₀ p L b) : ℝ))]
  rw [prod_filter, Fintype.prod_option]
  have h0 : IsLow p L P5 none := isLow_none p L P5
  simp only [h0, ↓reduceIte]
  congr 1
  · show (Fintype.card (ResidueSpace m₀) : ℝ) = _
    rw [Fintype.card_pi]
    push_cast
    simp [ZMod.card]
  · push_cast
    rw [prod_filter]
    refine Fintype.prod_congr _ _ fun j => ?_
    have hiff : IsLow p L P5 (some j) ↔ p L j < P5 :=
      ⟨fun h => h j rfl, fun h j' hj' => by cases hj'; exact h⟩
    by_cases hj : p L j < P5
    · simp only [hiff.mpr hj, hj, ↓reduceIte]
      show (Fintype.card (ZMod (p L j)) : ℝ) = _
      rw [ZMod.card]
    · simp only [(not_congr hiff).mpr hj, hj, ↓reduceIte]

/-- **The frozen label restricted to `E` is uniform**: under `μ ⊗ Unif(∏_k Ω_k)` (`μ` the product
of laws with uniform one-slot marginals) the frozen label of the slot `w` agrees with a given
`z₀` on the conditioned coordinates `E` with probability `(∏_{c ∈ E} m_c)⁻¹`. -/
theorem frozen_uniform [∀ L j, Fact (p L j).Prime] (L P5 : ℕ) (U : TailIdx p L P5 → Bool)
    (w : Slot) (ϱ : ∀ b : PaperAtom J L, FiniteLaw (Slot → AtomLabel m₀ p L b))
    (hϱ : ∀ b, HasUniformMarginals (ϱ b)) (z₀ : ResidueSpace (joinModuli m₀ (p L))) :
    ∑ ω : LowLabels m₀ p L P5 × (∀ k, PairAlphabet (tailQ p L P5) k),
        ((FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1)).weight ω.1 *
          (Fintype.card (∀ k, PairAlphabet (tailQ p L P5) k) : ℝ)⁻¹) *
        (if ∀ e ∈ frozenCoords (J₀ := J₀) p L P5 U,
            frozenAt m₀ p L P5 w ω.1 (pairsToVectors (tailQ p L P5) ω.2).1 e = z₀ e
          then 1 else 0) =
      ((∏ c ∈ frozenCoords (J₀ := J₀) p L P5 U, joinModuli m₀ (p L) c : ℕ) : ℝ)⁻¹ := by
  classical
  set F : LowLabels m₀ p L P5 → ℝ := fun x =>
    ∏ i : {b : PaperAtom J L // IsLow p L P5 b},
      if x i w = atomTarget m₀ p L z₀ i.1 then (1 : ℝ) else 0 with hF
  set G : (∀ k, PairAlphabet (tailQ p L P5) k) → ℝ := fun a =>
    ∏ k : TailIdx p L P5, (if U k = true then
      (if (a k).1.1 = z₀ (Sum.inr k.1) then (1 : ℝ) else 0) else 1) with hG
  have hind : ∀ ω : LowLabels m₀ p L P5 × (∀ k, PairAlphabet (tailQ p L P5) k),
      (if ∀ e ∈ frozenCoords (J₀ := J₀) p L P5 U,
          frozenAt m₀ p L P5 w ω.1 (pairsToVectors (tailQ p L P5) ω.2).1 e = z₀ e
        then (1 : ℝ) else 0) = F ω.1 * G ω.2 := by
    intro ω
    rw [if_congr (frozen_eq_iff m₀ p L P5 U w ω.1 _ z₀) rfl rfl]
    have hA : F ω.1 = if ∀ i : {b : PaperAtom J L // IsLow p L P5 b},
        ω.1 i w = atomTarget m₀ p L z₀ i.1 then 1 else 0 := by
      rw [hF]
      simp only
      rw [Finset.prod_boole]
      simp
    have hB : G ω.2 = if ∀ k : TailIdx p L P5, U k = true →
        (pairsToVectors (tailQ p L P5) ω.2).1 k = z₀ (Sum.inr k.1) then 1 else 0 := by
      rw [hG]
      simp only
      rw [show (∏ k : TailIdx p L P5, (if U k = true then
          (if (ω.2 k).1.1 = z₀ (Sum.inr k.1) then (1 : ℝ) else 0) else 1)) =
          ∏ k : TailIdx p L P5, (if (U k = true → (ω.2 k).1.1 = z₀ (Sum.inr k.1))
            then (1 : ℝ) else 0) from
        Fintype.prod_congr _ _ fun k => by by_cases hk : U k = true <;> simp [hk]]
      rw [Finset.prod_boole]
      simp [pairsToVectors]
    rw [hA, hB, ite_zero_mul_ite_zero, mul_one]
  simp_rw [hind]
  rw [Fintype.sum_prod_type]
  have hfac : ∀ x a, ((FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} =>
      ϱ i.1)).weight x *
      (Fintype.card (∀ k, PairAlphabet (tailQ p L P5) k) : ℝ)⁻¹) * (F x * G a) =
      ((FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1)).weight x * F x) *
        ((Fintype.card (∀ k, PairAlphabet (tailQ p L P5) k) : ℝ)⁻¹ * G a) := fun x a => by ring
  simp_rw [hfac, ← mul_sum, ← sum_mul]
  -- the low atoms
  have hlow : ∑ x : LowLabels m₀ p L P5,
      (FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1)).weight x * F x =
      (∏ i : {b : PaperAtom J L // IsLow p L P5 b},
        (Fintype.card (AtomLabel m₀ p L i.1) : ℝ))⁻¹ := by
    have h1 : ∀ x : LowLabels m₀ p L P5,
        (FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1)).weight x * F x =
        ∏ i : {b : PaperAtom J L // IsLow p L P5 b},
          ((ϱ i.1).weight (x i) * if x i w = atomTarget m₀ p L z₀ i.1 then (1 : ℝ) else 0) := by
      intro x
      rw [prod_mul_distrib]
      rfl
    simp_rw [h1]
    rw [← Fintype.prod_sum (fun i : {b : PaperAtom J L // IsLow p L P5 b} =>
      fun t : Slot → AtomLabel m₀ p L i.1 =>
        (ϱ i.1).weight t * if t w = atomTarget m₀ p L z₀ i.1 then (1 : ℝ) else 0)]
    rw [← prod_inv_distrib]
    refine Fintype.prod_congr _ _ fun i => ?_
    have h2 := hϱ i.1 w (fun t => if t = atomTarget m₀ p L z₀ i.1 then (1 : ℝ) else 0)
    rw [FiniteLaw.expect_uniform, sum_ite_eq'] at h2
    have h3 : ∑ t : Slot → AtomLabel m₀ p L i.1,
        (ϱ i.1).weight t * (if t w = atomTarget m₀ p L z₀ i.1 then (1 : ℝ) else 0) =
        (ϱ i.1).expect (fun z => if z w = atomTarget m₀ p L z₀ i.1 then (1 : ℝ) else 0) := rfl
    rw [h3, h2]
    simp
  -- the tail primes
  have htail : (Fintype.card (∀ k, PairAlphabet (tailQ p L P5) k) : ℝ)⁻¹ *
      ∑ a : (∀ k, PairAlphabet (tailQ p L P5) k), G a =
      (∏ k : TailIdx p L P5, (if U k = true then (p L k.1 : ℝ) else 1))⁻¹ := by
    rw [hG]
    simp only
    rw [← Fintype.prod_sum (fun k : TailIdx p L P5 => fun t : PairAlphabet (tailQ p L P5) k =>
      if U k = true then (if t.1.1 = z₀ (Sum.inr k.1) then (1 : ℝ) else 0) else 1)]
    rw [Fintype.card_pi, Nat.cast_prod, ← prod_inv_distrib, ← prod_mul_distrib,
      ← prod_inv_distrib]
    refine Fintype.prod_congr _ _ fun k => ?_
    by_cases hk : U k = true
    · simp only [hk, ↓reduceIte]
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
      have h4 := prob_pairAlphabet_fst (tailQ p L P5) k (z₀ (Sum.inr k.1))
      convert h4 using 4
      · ext a
        simp
      · rfl
    · simp only [hk, Bool.false_eq_true, ↓reduceIte, sum_const, card_univ, nsmul_eq_mul, mul_one,
        inv_one]
      have : (Fintype.card (PairAlphabet (tailQ p L P5) k) : ℝ) ≠ 0 := by
        exact_mod_cast Fintype.card_ne_zero
      field_simp
  rw [hlow, htail, prod_card_lowAtoms, ← mul_inv, prod_frozenCoords_nat]
  push_cast
  ring_nf

/-- **The equidistribution of the fibre classes** (Step 3 of `lem:record:density-can`: "the class
`𝔞₁` is uniform among the classes modulo `D` above `s`"): for every class `𝔞₁` of the fibres of
the frozen label of the slot `u` (residue `s`), and every `D`-periodic `f`,
`E_ω f(𝔞₁(ω)) = (M/D) ∑_{c < D, c ≡ s (M)} f(c)`, under `μ ⊗ Unif(∏_k Ω_k)` with `μ` a product of
laws with uniform one-slot marginals. -/
theorem equidist_fibreClass [∀ L j, Fact (p L j).Prime] (L P5 : ℕ) (U : TailIdx p L P5 → Bool)
    {M : ℕ} [NeZero M] (s : ZMod M) (u : Slot)
    (ϱ : ∀ b : PaperAtom J L, FiniteLaw (Slot → AtomLabel m₀ p L b))
    (hϱ : ∀ b, HasUniformMarginals (ϱ b))
    (𝔞₁ : LowLabels m₀ p L P5 × (∀ k, PairAlphabet (tailQ p L P5) k) → ℤ)
    (c₁ : ∀ ω n, InFibre (joinModuli m₀ (p L)) (frozenCoords (J₀ := J₀) p L P5 U)
        (frozenAt m₀ p L P5 u ω.1 (pairsToVectors (tailQ p L P5) ω.2).1) s n ↔
        n ≡ 𝔞₁ ω [ZMOD ((fibreModulus m₀ p L P5 U M : ℕ) : ℤ)])
    (f : ℤ → ℝ) (hf : ∀ c, f (c + fibreModulus m₀ p L P5 U M) = f c) :
    ∑ ω : LowLabels m₀ p L P5 × (∀ k, PairAlphabet (tailQ p L P5) k),
        ((FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1)).weight ω.1 *
          (Fintype.card (∀ k, PairAlphabet (tailQ p L P5) k) : ℝ)⁻¹) * f (𝔞₁ ω) =
      (M : ℝ) / (fibreModulus m₀ p L P5 U M : ℕ) *
        ∑ c ∈ (range (fibreModulus m₀ p L P5 U M)).filter
          (fun c : ℕ => (c : ℤ) ≡ (s.val : ℤ) [ZMOD (M : ℤ)]), f c := by
  classical
  set D := fibreModulus m₀ p L P5 U M with hDdef
  set w : LowLabels m₀ p L P5 × (∀ k, PairAlphabet (tailQ p L P5) k) → ℝ := fun ω =>
    (FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1)).weight ω.1 *
      (Fintype.card (∀ k, PairAlphabet (tailQ p L P5) k) : ℝ)⁻¹ with hw
  have hProd0 : (∏ c ∈ frozenCoords (J₀ := J₀) p L P5 U, joinModuli m₀ (p L) c) ≠ 0 :=
    prod_ne_zero_iff.mpr fun c _ => NeZero.ne _
  have hD : 0 < D := by
    rw [hDdef]
    unfold fibreModulus
    exact Nat.pos_of_ne_zero (mul_ne_zero (NeZero.ne M) hProd0)
  -- expand `f(𝔞₁ ω)` over the residues modulo `D`
  rw [sum_congr rfl fun ω _ => by rw [← sum_range_modEq hD hf (𝔞₁ ω)]]
  simp_rw [mul_sum]
  rw [sum_comm]
  have hcs_iff : ∀ n : ℤ, ((n : ZMod M) = s ↔ n ≡ (s.val : ℤ) [ZMOD (M : ℤ)]) := by
    intro n
    rw [← ZMod.intCast_eq_intCast_iff, Int.cast_natCast, ZMod.natCast_zmod_val]
  have key : ∀ c : ℕ, ∑ ω, w ω * (if (c : ℤ) ≡ 𝔞₁ ω [ZMOD D] then f c else 0) =
      if (c : ℤ) ≡ (s.val : ℤ) [ZMOD (M : ℤ)] then
        f c * ((∏ e ∈ frozenCoords (J₀ := J₀) p L P5 U, joinModuli m₀ (p L) e : ℕ) : ℝ)⁻¹
        else 0 := by
    intro c
    have hiff : ∀ ω : LowLabels m₀ p L P5 × (∀ k, PairAlphabet (tailQ p L P5) k),
        ((c : ℤ) ≡ 𝔞₁ ω [ZMOD D]) ↔ ((c : ℤ) ≡ (s.val : ℤ) [ZMOD (M : ℤ)]) ∧
          ∀ e ∈ frozenCoords (J₀ := J₀) p L P5 U,
            frozenAt m₀ p L P5 u ω.1 (pairsToVectors (tailQ p L P5) ω.2).1 e =
              integerResidue (joinModuli m₀ (p L)) (c : ℤ) e := by
      intro ω
      rw [← c₁ ω c]
      unfold InFibre
      rw [hcs_iff]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun e he => (h2 e he).symm⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun e he => (h2 e he).symm⟩
    by_cases hcs : (c : ℤ) ≡ (s.val : ℤ) [ZMOD (M : ℤ)]
    · simp only [hiff, hcs, true_and, ↓reduceIte]
      have h1 : ∀ ω, w ω * (if ∀ e ∈ frozenCoords (J₀ := J₀) p L P5 U, frozenAt m₀ p L P5 u ω.1
          (pairsToVectors (tailQ p L P5) ω.2).1 e =
            integerResidue (joinModuli m₀ (p L)) (c : ℤ) e then f c else 0) =
          f c * (w ω * (if ∀ e ∈ frozenCoords (J₀ := J₀) p L P5 U, frozenAt m₀ p L P5 u ω.1
            (pairsToVectors (tailQ p L P5) ω.2).1 e =
              integerResidue (joinModuli m₀ (p L)) (c : ℤ) e then (1 : ℝ) else 0)) := by
        intro ω
        split_ifs <;> ring
      rw [sum_congr rfl fun ω _ => h1 ω, ← mul_sum]
      congr 1
      exact frozen_uniform m₀ p L P5 U u ϱ hϱ (integerResidue (joinModuli m₀ (p L)) (c : ℤ))
    · simp only [hiff, hcs, false_and, ↓reduceIte, mul_zero, sum_const_zero]
  rw [sum_congr rfl fun c _ => key c, ← sum_filter, ← sum_mul]
  have hinv : ((∏ e ∈ frozenCoords (J₀ := J₀) p L P5 U, joinModuli m₀ (p L) e : ℕ) : ℝ)⁻¹ =
      (M : ℝ) / (D : ℝ) := by
    have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
    have hP : ((∏ e ∈ frozenCoords (J₀ := J₀) p L P5 U, joinModuli m₀ (p L) e : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast hProd0
    rw [hDdef]
    unfold fibreModulus
    rw [Nat.cast_mul]
    field_simp
  rw [hinv, mul_comm, mul_sum]

end Frozen

/-! ## `DensityCancellation` from the moment inputs alone -/

section Final

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]

/-- **The `L²` bound of Step 3** at a low support `U`, for the encoded data and every choice of
fibre classes: `E_ω(‖g₁(ω)‖₂² ‖g₂(ω)‖₂²) ≤ C_ε N^{72δ} α` for the frozen inputs. (The bound does
not involve the classes; the quantifier only matches `FibreEquidist`.) -/
def FibreL2 (L P5 : ℕ) (U : TailIdx p L P5 → Bool) (μ : FiniteLaw (LowLabels m₀ p L P5))
    (F₁ F₂ : LowLabels m₀ p L P5 → ResidueSpace (tailQ p L P5) → ℝ) (N : ℕ) (Cε α : ℝ) : Prop :=
  ∑ ω : LowLabels m₀ p L P5 × (∀ k, PairAlphabet (tailQ p L P5) k),
      (μ.weight ω.1 * (Fintype.card (∀ k, PairAlphabet (tailQ p L P5) k) : ℝ)⁻¹) *
        ((𝔼 z, ‖(F₁ ω.1 (mergeFree U (pairsToVectors (tailQ p L P5) ω.2).1 z) : ℂ)‖ ^ 2) *
          (𝔼 z, ‖(F₂ ω.1 (mergeFree U (pairsToVectors (tailQ p L P5) ω.2).2 z) : ℂ)‖ ^ 2)) ≤
    Cε * (N : ℝ) ^ (72 * stageDelta) * α

variable [∀ L j, Fact (p L j).Prime] {P : Type} [Fintype P] (pr h : P → ℕ)
  [∀ q, NeZero (pr q ^ h q)]

open Sarkozy.TheoremC Sarkozy.IndexSupport Sarkozy.Comparison in
/-- **`lem:record:density-can` (WP-FI's `DensityCancellation`) from the moment inputs alone.**
Hypotheses:
* elementary facts about the data (as in `densityCancellation_of_analytic`): distinct tail primes,
  `P₅ ≥ 64`, `M₀` coprime to every atom modulus, the atom moduli pairwise coprime, the prefix
  moduli prime powers `pp_i^{ep_i}`, and the coverage of the primes up to `N^{1/40}`;
* for every query at every scale `L ≥ L₁`: Step 2, `LiftMoments` (`lem:record:lift-moments`(c))
  at the encoded data, and the `L²` bound `FibreL2` of Step 3 at every low support.

Proved: Step 1 (WP-K), the intervals, the fibre formulas, the size of `D`, `H D_E ≤ Q`, the
coprimality and coverage conditions, the square class of `𝔞₂ − 𝔞₁` (from the acceptance (b)), and
the uniformity of `𝔞₁` (from the uniform one-slot marginals and the strict-square pairs). -/
theorem densityCancellation_of_moments (P5 : ℕ) (pp ep : J₀ → ℕ)
    (hinj : ∀ L, Function.Injective (p L)) (h64 : 64 ≤ P5) {C₂ Cε : ℝ} (hC₂ : 0 ≤ C₂)
    (hCε : 0 ≤ Cε) (L₁ : ℕ)
    (hcop0 : ∀ L (c : J₀ ⊕ J L), Nat.Coprime (modulus pr h) (joinModuli m₀ (p L) c))
    (hcopE : ∀ L, ∀ i j : J₀ ⊕ J L, i ≠ j →
      Nat.Coprime (joinModuli m₀ (p L) i) (joinModuli m₀ (p L) j))
    (hpre : ∀ i, (pp i).Prime ∧ 1 ≤ ep i ∧ m₀ i = pp i ^ ep i)
    (hcover : ∀ L : ℕ, ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ (1 / 40 : ℝ) →
      ℓ ∣ modulus pr h ∨ (∃ i, ℓ ∣ m₀ i) ∨ ∃ j, p L j = ℓ)
    (hSteps : ∀ L : ℕ, L₁ ≤ L → ∀ A : Finset ℤ, Admissible (blockScale * L) A →
      ∀ ϱ : ∀ b : PaperAtom J L, FiniteLaw (Slot → AtomLabel m₀ p L b),
      (∀ b, HasUniformMarginals (ϱ b)) → ∀ (u v : Slot) (huv : u ≠ v),
      ∀ ha : (∀ j : J L, P5 ≤ p L j → PairUniformOmega (q := p L j) (ϱ (some j)) u v ∧
        Sarkozy.Mixing.IsGammaMixing (p L j) Sarkozy.AnalyticStage.γ (ϱ (some j)) {u, v}),
      (∀ b : PaperAtom J L, (∀ j, b = some j → p L j < P5) → ∀ z, (ϱ b).weight z ≠ 0 →
        AcceptedPair m₀ p pp ep L b (z u) (z v)) →
      ∀ (bI : ZMod blockScale) (s r : ZMod (modulus pr h)), bI ≠ 0 →
      IsNonvanishingSquareClass (modulus pr h) r →
      ∀ G : Slot → (∀ b, AtomLabel m₀ p L b) → ℝ,
      G u = indexInputAt m₀ p pr h L A (bI, s) →
      G v = indexInputAt m₀ p pr h L A (bI + 1, s + r) →
      (∀ w, w ≠ u → w ≠ v → IsQueryInput m₀ p pr h L A (G w)) →
        LiftMoments (tailQ p L P5)
          (FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1))
          (encKappa m₀ p L P5 ϱ huv (fun k => (ha k.1 k.2).1)) (encF m₀ p L P5 G u)
          (encF m₀ p L P5 G v) (encW m₀ p L P5 G u v) (blockScale * L) C₂
          (density (blockScale * L) A) ∧
        ∀ U : TailIdx p L P5 → Bool,
          supportConductor (tailQ p L P5) U ≤
            ((blockScale * L : ℕ) : ℝ) ^ Cancellation.stageTan →
          FibreL2 m₀ p L P5 U
            (FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1))
            (encF m₀ p L P5 G u) (encF m₀ p L P5 G v) (blockScale * L) Cε
            (density (blockScale * L) A)) :
    DensityCancellation m₀ p pr h P5 pp ep := by
  have hMod : modulus pr h ≠ 0 := prod_ne_zero_iff.mpr fun q _ => NeZero.ne _
  have : NeZero (modulus pr h) := ⟨hMod⟩
  apply densityCancellation_of_equidist m₀ p pr h P5 pp ep hinj h64 hC₂ hCε L₁ hcop0 hcopE hpre
    hcover
  intro L hL A hA ϱ hϱ u v huv ha hb bI s r hbI hr G hGu hGv hGw
  obtain ⟨hMom, hL2⟩ := hSteps L hL A hA ϱ hϱ u v huv ha hb bI s r hbI hr G hGu hGv hGw
  refine ⟨hMom, fun U hU => ?_⟩
  intro 𝔞₁ 𝔞₂ c₁ _
  exact ⟨fun f hf => equidist_fibreClass m₀ p L P5 U s u ϱ hϱ 𝔞₁ c₁ f hf, hL2 U hU⟩

end Final

end Sarkozy.CancellationSteps
