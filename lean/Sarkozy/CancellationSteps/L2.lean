module

public import Sarkozy.CancellationSteps.Equidist
public import Sarkozy.Cancellation.MomentsLaws

/-!
# The slot labels are uniform on `G_N`, and the `L²` bound of Step 3

`paper/sections/08_scale_comparison.tex`, `lem:record:density-can`, Step 3: "Cauchy–Schwarz and
Jensen's inequality … because `(x_u, y_u)` together with the uniform outside label is uniform on
`G_N`".

* `slot_uniform`: under `μ ⊗ Unif(∏_k Ω_k) ⊗ Unif(X_{𝒮'})` the label
  `mergeAt x_w (mergeFree U y_w y)` of a slot, read in `G_N`, is uniform on `G_N`
  (`frozen_uniform` on `E`, the free label `y` off `E`);
* `fibreL2_of_fourth_moments`: hence (WP-K's `step3_fourth_moments`) the `L²` bound `FibreL2` of
  Step 3 follows from the fourth-moment bounds `E_{G_N} |G_u|⁴, E_{G_N} |G_v|⁴ ≤ C_ε N^{72δ} α` of
  the two query inputs (`lem:record:lift-moments`(c) with `r = 2`).

New material for this paper.
-/

@[expose] public section

namespace Sarkozy.CancellationSteps

open Finset Complex
open scoped BigOperators ComplexConjugate
open Sarkozy.Cancellation Sarkozy.Mixing Sarkozy.PaperFrame Sarkozy.FourierArithmetic
  Sarkozy.Functional

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]

omit [∀ i, NeZero (m₀ i)] [∀ L j, NeZero (p L j)] in
/-- The slot label is `z₀` iff the frozen label agrees with `z₀` on `E` and the free label is the
restriction of `z₀`. -/
lemma slotLabel_eq_iff (L P5 : ℕ) (U : TailIdx p L P5 → Bool) (w : Slot) (x : LowLabels m₀ p L P5)
    (y₀ : ∀ k : TailIdx p L P5, ZMod (tailQ p L P5 k))
    (y : ResidueSpace (fun k : {k : TailIdx p L P5 // U k = false} => tailQ p L P5 k.1))
    (z₀ : ResidueSpace (joinModuli m₀ (p L))) :
    atomGroupEquiv m₀ p L (mergeAt m₀ p L P5 (fun i => x i w) (mergeFree U y₀ y)) = z₀ ↔
      (∀ e ∈ frozenCoords (J₀ := J₀) p L P5 U, frozenAt m₀ p L P5 w x y₀ e = z₀ e) ∧
        freeLabel m₀ p L P5 U y =
          Cancellation.restrictFree (joinModuli m₀ (p L)) (frozenCoords (J₀ := J₀) p L P5 U)
            z₀ := by
  rw [atomGroupEquiv_mergeAt_freeze]
  constructor
  · intro h
    refine ⟨fun e he => ?_, ?_⟩
    · have := congrFun h e
      unfold coordinateFreeze at this
      simp only [he, ↓reduceIte] at this
      exact this
    · funext c
      have := congrFun h c.1
      unfold coordinateFreeze Cancellation.extendFree at this
      simp only [c.2, ↓reduceIte, ↓reduceDIte] at this
      exact this
  · rintro ⟨h1, h2⟩
    funext c
    unfold coordinateFreeze
    by_cases hc : c ∈ frozenCoords (J₀ := J₀) p L P5 U
    · simp only [hc, ↓reduceIte]
      exact h1 c hc
    · simp only [hc, ↓reduceIte]
      unfold Cancellation.extendFree
      simp only [hc, ↓reduceDIte]
      rw [h2]
      rfl

/-- `|G_N| = ∏_{c ∈ E} m_c · |X_{𝒮'}|`. -/
lemma card_joinGroup_eq (L P5 : ℕ) (U : TailIdx p L P5 → Bool) :
    (Fintype.card (ResidueSpace (joinModuli m₀ (p L))) : ℝ) =
      ((∏ c ∈ frozenCoords (J₀ := J₀) p L P5 U, joinModuli m₀ (p L) c : ℕ) : ℝ) *
        (Fintype.card (ResidueSpace
          (fun k : {k : TailIdx p L P5 // U k = false} => tailQ p L P5 k.1)) : ℝ) := by
  classical
  have h1 : Fintype.card (ResidueSpace
      (fun k : {k : TailIdx p L P5 // U k = false} => tailQ p L P5 k.1)) =
      Fintype.card (ResidueSpace (freeJoinModuli m₀ p L P5 U)) :=
    Fintype.card_congr (freeLabel m₀ p L P5 U)
  rw [h1]
  simp only [Fintype.card_pi, ZMod.card]
  push_cast
  rw [← prod_filter_mul_prod_filter_not univ (fun c => c ∈ frozenCoords (J₀ := J₀) p L P5 U)]
  congr 1
  · congr 1
    ext c
    simp
  · exact Finset.prod_subtype _ (fun c => by simp) (fun c => (joinModuli m₀ (p L) c : ℝ))

/-- **The slot labels are uniform on `G_N`**: under `μ ⊗ Unif(∏_k Ω_k)` and `y` uniform on the free
coordinates, the label `mergeAt x_w (mergeFree U y_w y)` of the slot `w`, read in `G_N`, is
uniform (`μ` a product of laws with uniform one-slot marginals; `y_w` the first coordinates of the
strict-square pairs). -/
theorem slot_uniform [∀ L j, Fact (p L j).Prime] (L P5 : ℕ) (U : TailIdx p L P5 → Bool)
    (w : Slot) (ϱ : ∀ b : PaperAtom J L, FiniteLaw (Slot → AtomLabel m₀ p L b))
    (hϱ : ∀ b, HasUniformMarginals (ϱ b)) (f : ResidueSpace (joinModuli m₀ (p L)) → ℝ) :
    ∑ ω : LowLabels m₀ p L P5 × (∀ k, PairAlphabet (tailQ p L P5) k),
        ((FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1)).weight ω.1 *
          (Fintype.card (∀ k, PairAlphabet (tailQ p L P5) k) : ℝ)⁻¹) *
        𝔼 y, f (atomGroupEquiv m₀ p L (mergeAt m₀ p L P5 (fun i => ω.1 i w)
          (mergeFree U (pairsToVectors (tailQ p L P5) ω.2).1 y))) =
      (FiniteLaw.uniform (ResidueSpace (joinModuli m₀ (p L)))).expect f := by
  classical
  set W : LowLabels m₀ p L P5 × (∀ k, PairAlphabet (tailQ p L P5) k) → ℝ := fun ω =>
    (FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1)).weight ω.1 *
      (Fintype.card (∀ k, PairAlphabet (tailQ p L P5) k) : ℝ)⁻¹ with hW
  set lab : LowLabels m₀ p L P5 × (∀ k, PairAlphabet (tailQ p L P5) k) →
      ResidueSpace (fun k : {k : TailIdx p L P5 // U k = false} => tailQ p L P5 k.1) →
      ResidueSpace (joinModuli m₀ (p L)) := fun ω y =>
    atomGroupEquiv m₀ p L (mergeAt m₀ p L P5 (fun i => ω.1 i w)
      (mergeFree U (pairsToVectors (tailQ p L P5) ω.2).1 y)) with hlab
  set cf : ℝ := (Fintype.card (ResidueSpace
    (fun k : {k : TailIdx p L P5 // U k = false} => tailQ p L P5 k.1)) : ℝ) with hcf
  have hcf0 : cf ≠ 0 := by rw [hcf]; exact_mod_cast Fintype.card_ne_zero
  -- the probability of a point
  have hpoint : ∀ z₀ : ResidueSpace (joinModuli m₀ (p L)),
      ∑ ω, W ω * 𝔼 y, (if lab ω y = z₀ then (1 : ℝ) else 0) =
        (Fintype.card (ResidueSpace (joinModuli m₀ (p L))) : ℝ)⁻¹ := by
    intro z₀
    have hE : ∀ ω, 𝔼 y, (if lab ω y = z₀ then (1 : ℝ) else 0) =
        (if ∀ e ∈ frozenCoords (J₀ := J₀) p L P5 U, frozenAt m₀ p L P5 w ω.1
          (pairsToVectors (tailQ p L P5) ω.2).1 e = z₀ e then (1 : ℝ) else 0) * cf⁻¹ := by
      intro ω
      have h1 : ∀ y, (if lab ω y = z₀ then (1 : ℝ) else 0) =
          (if ∀ e ∈ frozenCoords (J₀ := J₀) p L P5 U, frozenAt m₀ p L P5 w ω.1
            (pairsToVectors (tailQ p L P5) ω.2).1 e = z₀ e then (1 : ℝ) else 0) *
          (if freeLabel m₀ p L P5 U y = Cancellation.restrictFree (joinModuli m₀ (p L))
            (frozenCoords (J₀ := J₀) p L P5 U) z₀ then (1 : ℝ) else 0) := by
        intro y
        rw [ite_zero_mul_ite_zero, mul_one]
        exact if_congr (slotLabel_eq_iff m₀ p L P5 U w ω.1 _ y z₀) rfl rfl
      simp_rw [h1]
      rw [← Finset.mul_expect, Fintype.expect_eq_sum_div_card]
      congr 1
      rw [show (∑ y, if freeLabel m₀ p L P5 U y = Cancellation.restrictFree (joinModuli m₀ (p L))
          (frozenCoords (J₀ := J₀) p L P5 U) z₀ then (1 : ℝ) else 0) = 1 from by
        rw [← (freeLabel m₀ p L P5 U).symm.sum_comp]
        simp]
      rw [hcf, one_div]
    simp_rw [hE]
    rw [show (∑ ω, W ω * ((if ∀ e ∈ frozenCoords (J₀ := J₀) p L P5 U, frozenAt m₀ p L P5 w ω.1
        (pairsToVectors (tailQ p L P5) ω.2).1 e = z₀ e then (1 : ℝ) else 0) * cf⁻¹)) =
        (∑ ω, W ω * (if ∀ e ∈ frozenCoords (J₀ := J₀) p L P5 U, frozenAt m₀ p L P5 w ω.1
          (pairsToVectors (tailQ p L P5) ω.2).1 e = z₀ e then (1 : ℝ) else 0)) * cf⁻¹ from by
      rw [sum_mul]
      exact sum_congr rfl fun ω _ => by ring]
    rw [frozen_uniform m₀ p L P5 U w ϱ hϱ z₀, card_joinGroup_eq m₀ p L P5 U, mul_inv]
  -- linearity
  have hlin : ∀ ω y, f (lab ω y) = ∑ z₀, f z₀ * (if lab ω y = z₀ then (1 : ℝ) else 0) := by
    intro ω y
    simp
  simp_rw [show ∀ ω, 𝔼 y, f (atomGroupEquiv m₀ p L (mergeAt m₀ p L P5 (fun i => ω.1 i w)
      (mergeFree U (pairsToVectors (tailQ p L P5) ω.2).1 y))) = 𝔼 y, f (lab ω y) from fun ω => rfl]
  simp_rw [hlin, Finset.expect_sum_comm, ← Finset.mul_expect, mul_sum]
  rw [sum_comm]
  rw [FiniteLaw.expect_uniform, sum_div]
  refine sum_congr rfl fun z₀ _ => ?_
  have := hpoint z₀
  calc ∑ ω, W ω * (f z₀ * 𝔼 y, (if lab ω y = z₀ then (1 : ℝ) else 0)) =
      f z₀ * ∑ ω, W ω * 𝔼 y, (if lab ω y = z₀ then (1 : ℝ) else 0) := by
        rw [mul_sum]
        exact sum_congr rfl fun ω _ => by ring
    _ = f z₀ / (Fintype.card (ResidueSpace (joinModuli m₀ (p L))) : ℝ) := by
        rw [this, div_eq_mul_inv]


/-! ## The second coordinate of the strict-square pairs -/

section PairSnd

variable {K : Type*} (q : K → ℕ) [∀ j, NeZero (q j)]

/-- In `Ω_q` every second coordinate occurs `|sqSet|` times. -/
lemma card_pairAlphabet_snd (j : K) (y₀ : ZMod (q j)) :
    (univ.filter (fun a : PairAlphabet q j => a.1.2 = y₀)).card = (sqSet q j).card := by
  refine card_bij (fun a _ => a.1.2 - a.1.1) (fun a ha => a.2) ?_ ?_
  · intro a ha b hb hab
    have ha' := (mem_filter.mp ha).2
    have hb' := (mem_filter.mp hb).2
    apply Subtype.ext
    apply Prod.ext
    · have h := hab
      rw [ha', hb'] at h
      exact sub_right_injective h
    · rw [ha', hb']
  · intro d hd
    refine ⟨⟨(y₀ - d, y₀), by simpa using hd⟩, mem_filter.mpr ⟨mem_univ _, rfl⟩, ?_⟩
    simp

/-- The second coordinate of `Unif(Ω_q)` is uniform. -/
lemma prob_pairAlphabet_snd [∀ j, Fact (q j).Prime] (j : K) (y₀ : ZMod (q j)) :
    (Fintype.card (PairAlphabet q j) : ℝ)⁻¹ *
        ((univ.filter (fun a : PairAlphabet q j => a.1.2 = y₀)).card : ℝ) = (q j : ℝ)⁻¹ := by
  have hfib : ∀ y : ZMod (q j),
      (univ.filter (fun a : PairAlphabet q j => a.1.2 = y)).card = (sqSet q j).card :=
    card_pairAlphabet_snd q j
  have htot : Fintype.card (PairAlphabet q j) = q j * (sqSet q j).card := by
    rw [← card_univ, card_eq_sum_card_fiberwise (f := fun a : PairAlphabet q j => a.1.2)
      (t := univ) (fun _ _ => mem_univ _)]
    simp only [hfib, sum_const, card_univ, ZMod.card, smul_eq_mul]
  rw [hfib, htot]
  have hs : (0 : ℝ) < (sqSet q j).card := by exact_mod_cast card_sqSet_pos q j
  have hq : (0 : ℝ) < q j := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (q j))
  push_cast
  field_simp

end PairSnd

/-- **The frozen label restricted to `E` is uniform** (second coordinates of the pairs): under
`μ ⊗ Unif(∏_k Ω_k)` (`μ` the product
of laws with uniform one-slot marginals) the frozen label of the slot `w` agrees with a given
`z₀` on the conditioned coordinates `E` with probability `(∏_{c ∈ E} m_c)⁻¹`. -/
theorem frozen_uniform_snd [∀ L j, Fact (p L j).Prime] (L P5 : ℕ) (U : TailIdx p L P5 → Bool)
    (w : Slot) (ϱ : ∀ b : PaperAtom J L, FiniteLaw (Slot → AtomLabel m₀ p L b))
    (hϱ : ∀ b, HasUniformMarginals (ϱ b)) (z₀ : ResidueSpace (joinModuli m₀ (p L))) :
    ∑ ω : LowLabels m₀ p L P5 × (∀ k, PairAlphabet (tailQ p L P5) k),
        ((FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1)).weight ω.1 *
          (Fintype.card (∀ k, PairAlphabet (tailQ p L P5) k) : ℝ)⁻¹) *
        (if ∀ e ∈ frozenCoords (J₀ := J₀) p L P5 U,
            frozenAt m₀ p L P5 w ω.1 (pairsToVectors (tailQ p L P5) ω.2).2 e = z₀ e
          then 1 else 0) =
      ((∏ c ∈ frozenCoords (J₀ := J₀) p L P5 U, joinModuli m₀ (p L) c : ℕ) : ℝ)⁻¹ := by
  classical
  set F : LowLabels m₀ p L P5 → ℝ := fun x =>
    ∏ i : {b : PaperAtom J L // IsLow p L P5 b},
      if x i w = atomTarget m₀ p L z₀ i.1 then (1 : ℝ) else 0 with hF
  set G : (∀ k, PairAlphabet (tailQ p L P5) k) → ℝ := fun a =>
    ∏ k : TailIdx p L P5, (if U k = true then
      (if (a k).1.2 = z₀ (Sum.inr k.1) then (1 : ℝ) else 0) else 1) with hG
  have hind : ∀ ω : LowLabels m₀ p L P5 × (∀ k, PairAlphabet (tailQ p L P5) k),
      (if ∀ e ∈ frozenCoords (J₀ := J₀) p L P5 U,
          frozenAt m₀ p L P5 w ω.1 (pairsToVectors (tailQ p L P5) ω.2).2 e = z₀ e
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
        (pairsToVectors (tailQ p L P5) ω.2).2 k = z₀ (Sum.inr k.1) then 1 else 0 := by
      rw [hG]
      simp only
      rw [show (∏ k : TailIdx p L P5, (if U k = true then
          (if (ω.2 k).1.2 = z₀ (Sum.inr k.1) then (1 : ℝ) else 0) else 1)) =
          ∏ k : TailIdx p L P5, (if (U k = true → (ω.2 k).1.2 = z₀ (Sum.inr k.1))
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
      if U k = true then (if t.1.2 = z₀ (Sum.inr k.1) then (1 : ℝ) else 0) else 1)]
    rw [Fintype.card_pi, Nat.cast_prod, ← prod_inv_distrib, ← prod_mul_distrib,
      ← prod_inv_distrib]
    refine Fintype.prod_congr _ _ fun k => ?_
    by_cases hk : U k = true
    · simp only [hk, ↓reduceIte]
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
      have h4 := prob_pairAlphabet_snd (tailQ p L P5) k (z₀ (Sum.inr k.1))
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

/-- **The slot labels are uniform on `G_N`** (second coordinates of the pairs): under
`μ ⊗ Unif(∏_k Ω_k)` and `y` uniform on the free
coordinates, the label `mergeAt x_w (mergeFree U y_w y)` of the slot `w`, read in `G_N`, is
uniform (`μ` a product of laws with uniform one-slot marginals; `y_w` the first coordinates of the
strict-square pairs). -/
theorem slot_uniform_snd [∀ L j, Fact (p L j).Prime] (L P5 : ℕ) (U : TailIdx p L P5 → Bool)
    (w : Slot) (ϱ : ∀ b : PaperAtom J L, FiniteLaw (Slot → AtomLabel m₀ p L b))
    (hϱ : ∀ b, HasUniformMarginals (ϱ b)) (f : ResidueSpace (joinModuli m₀ (p L)) → ℝ) :
    ∑ ω : LowLabels m₀ p L P5 × (∀ k, PairAlphabet (tailQ p L P5) k),
        ((FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1)).weight ω.1 *
          (Fintype.card (∀ k, PairAlphabet (tailQ p L P5) k) : ℝ)⁻¹) *
        𝔼 y, f (atomGroupEquiv m₀ p L (mergeAt m₀ p L P5 (fun i => ω.1 i w)
          (mergeFree U (pairsToVectors (tailQ p L P5) ω.2).2 y))) =
      (FiniteLaw.uniform (ResidueSpace (joinModuli m₀ (p L)))).expect f := by
  classical
  set W : LowLabels m₀ p L P5 × (∀ k, PairAlphabet (tailQ p L P5) k) → ℝ := fun ω =>
    (FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1)).weight ω.1 *
      (Fintype.card (∀ k, PairAlphabet (tailQ p L P5) k) : ℝ)⁻¹ with hW
  set lab : LowLabels m₀ p L P5 × (∀ k, PairAlphabet (tailQ p L P5) k) →
      ResidueSpace (fun k : {k : TailIdx p L P5 // U k = false} => tailQ p L P5 k.1) →
      ResidueSpace (joinModuli m₀ (p L)) := fun ω y =>
    atomGroupEquiv m₀ p L (mergeAt m₀ p L P5 (fun i => ω.1 i w)
      (mergeFree U (pairsToVectors (tailQ p L P5) ω.2).2 y)) with hlab
  set cf : ℝ := (Fintype.card (ResidueSpace
    (fun k : {k : TailIdx p L P5 // U k = false} => tailQ p L P5 k.1)) : ℝ) with hcf
  have hcf0 : cf ≠ 0 := by rw [hcf]; exact_mod_cast Fintype.card_ne_zero
  -- the probability of a point
  have hpoint : ∀ z₀ : ResidueSpace (joinModuli m₀ (p L)),
      ∑ ω, W ω * 𝔼 y, (if lab ω y = z₀ then (1 : ℝ) else 0) =
        (Fintype.card (ResidueSpace (joinModuli m₀ (p L))) : ℝ)⁻¹ := by
    intro z₀
    have hE : ∀ ω, 𝔼 y, (if lab ω y = z₀ then (1 : ℝ) else 0) =
        (if ∀ e ∈ frozenCoords (J₀ := J₀) p L P5 U, frozenAt m₀ p L P5 w ω.1
          (pairsToVectors (tailQ p L P5) ω.2).2 e = z₀ e then (1 : ℝ) else 0) * cf⁻¹ := by
      intro ω
      have h1 : ∀ y, (if lab ω y = z₀ then (1 : ℝ) else 0) =
          (if ∀ e ∈ frozenCoords (J₀ := J₀) p L P5 U, frozenAt m₀ p L P5 w ω.1
            (pairsToVectors (tailQ p L P5) ω.2).2 e = z₀ e then (1 : ℝ) else 0) *
          (if freeLabel m₀ p L P5 U y = Cancellation.restrictFree (joinModuli m₀ (p L))
            (frozenCoords (J₀ := J₀) p L P5 U) z₀ then (1 : ℝ) else 0) := by
        intro y
        rw [ite_zero_mul_ite_zero, mul_one]
        exact if_congr (slotLabel_eq_iff m₀ p L P5 U w ω.1 _ y z₀) rfl rfl
      simp_rw [h1]
      rw [← Finset.mul_expect, Fintype.expect_eq_sum_div_card]
      congr 1
      rw [show (∑ y, if freeLabel m₀ p L P5 U y = Cancellation.restrictFree (joinModuli m₀ (p L))
          (frozenCoords (J₀ := J₀) p L P5 U) z₀ then (1 : ℝ) else 0) = 1 from by
        rw [← (freeLabel m₀ p L P5 U).symm.sum_comp]
        simp]
      rw [hcf, one_div]
    simp_rw [hE]
    rw [show (∑ ω, W ω * ((if ∀ e ∈ frozenCoords (J₀ := J₀) p L P5 U, frozenAt m₀ p L P5 w ω.1
        (pairsToVectors (tailQ p L P5) ω.2).2 e = z₀ e then (1 : ℝ) else 0) * cf⁻¹)) =
        (∑ ω, W ω * (if ∀ e ∈ frozenCoords (J₀ := J₀) p L P5 U, frozenAt m₀ p L P5 w ω.1
          (pairsToVectors (tailQ p L P5) ω.2).2 e = z₀ e then (1 : ℝ) else 0)) * cf⁻¹ from by
      rw [sum_mul]
      exact sum_congr rfl fun ω _ => by ring]
    rw [frozen_uniform_snd m₀ p L P5 U w ϱ hϱ z₀, card_joinGroup_eq m₀ p L P5 U, mul_inv]
  -- linearity
  have hlin : ∀ ω y, f (lab ω y) = ∑ z₀, f z₀ * (if lab ω y = z₀ then (1 : ℝ) else 0) := by
    intro ω y
    simp
  simp_rw [show ∀ ω, 𝔼 y, f (atomGroupEquiv m₀ p L (mergeAt m₀ p L P5 (fun i => ω.1 i w)
      (mergeFree U (pairsToVectors (tailQ p L P5) ω.2).2 y))) = 𝔼 y, f (lab ω y) from fun ω => rfl]
  simp_rw [hlin, Finset.expect_sum_comm, ← Finset.mul_expect, mul_sum]
  rw [sum_comm]
  rw [FiniteLaw.expect_uniform, sum_div]
  refine sum_congr rfl fun z₀ _ => ?_
  have := hpoint z₀
  calc ∑ ω, W ω * (f z₀ * 𝔼 y, (if lab ω y = z₀ then (1 : ℝ) else 0)) =
      f z₀ * ∑ ω, W ω * 𝔼 y, (if lab ω y = z₀ then (1 : ℝ) else 0) := by
        rw [mul_sum]
        exact sum_congr rfl fun ω _ => by ring
    _ = f z₀ / (Fintype.card (ResidueSpace (joinModuli m₀ (p L))) : ℝ) := by
        rw [this, div_eq_mul_inv]

/-! ## The `L²` bound from the fourth moments -/

/-- **The `L²` bound of Step 3 from the fourth moments** (`step3_fourth_moments`,
"Cauchy–Schwarz and
Jensen's inequality"): if the pair factors are `G_u`, `G_v` read on `G_N` through `atomGroupEquiv`,
and `E_{G_N} |G_u|⁴, E_{G_N} |G_v|⁴ ≤ C_ε N^{72δ} α`, then `FibreL2` holds at every low support. -/
theorem fibreL2_of_fourth_moments [∀ L j, Fact (p L j).Prime] (L P5 : ℕ)
    (U : TailIdx p L P5 → Bool) (u v : Slot)
    (ϱ : ∀ b : PaperAtom J L, FiniteLaw (Slot → AtomLabel m₀ p L b))
    (hϱ : ∀ b, HasUniformMarginals (ϱ b)) (G : Slot → (∀ b, AtomLabel m₀ p L b) → ℝ)
    (Gu Gv : ResidueSpace (joinModuli m₀ (p L)) → ℝ)
    (hGu : ∀ x, G u x = Gu (atomGroupEquiv m₀ p L x))
    (hGv : ∀ x, G v x = Gv (atomGroupEquiv m₀ p L x)) (N : ℕ) (Cε α : ℝ)
    (hM : 0 ≤ Cε * (N : ℝ) ^ (72 * stageDelta) * α)
    (hmu : (FiniteLaw.uniform (ResidueSpace (joinModuli m₀ (p L)))).expect
      (fun z => |Gu z| ^ 4) ≤ Cε * (N : ℝ) ^ (72 * stageDelta) * α)
    (hmv : (FiniteLaw.uniform (ResidueSpace (joinModuli m₀ (p L)))).expect
      (fun z => |Gv z| ^ 4) ≤ Cε * (N : ℝ) ^ (72 * stageDelta) * α) :
    FibreL2 m₀ p L P5 U (FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1))
      (encF m₀ p L P5 G u) (encF m₀ p L P5 G v) N Cε α := by
  unfold FibreL2
  have hw : ∀ ω ∈ (univ : Finset (LowLabels m₀ p L P5 × (∀ k, PairAlphabet (tailQ p L P5) k))),
      0 ≤ (FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1)).weight ω.1 *
        (Fintype.card (∀ k, PairAlphabet (tailQ p L P5) k) : ℝ)⁻¹ := fun ω _ =>
    mul_nonneg (FiniteLaw.nonneg _ _) (by positivity)
  exact step3_fourth_moments univ _ hw
    (fun ω y => ((encF m₀ p L P5 G u ω.1 (mergeFree U (pairsToVectors (tailQ p L P5) ω.2).1 y)
      : ℝ) : ℂ))
    (fun ω y => ((encF m₀ p L P5 G v ω.1 (mergeFree U (pairsToVectors (tailQ p L P5) ω.2).2 y)
      : ℝ) : ℂ))
    (fun ω y => atomGroupEquiv m₀ p L (mergeAt m₀ p L P5 (fun i => ω.1 i u)
      (mergeFree U (pairsToVectors (tailQ p L P5) ω.2).1 y)))
    (fun ω y => atomGroupEquiv m₀ p L (mergeAt m₀ p L P5 (fun i => ω.1 i v)
      (mergeFree U (pairsToVectors (tailQ p L P5) ω.2).2 y))) Gu Gv
    (fun ω y => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      unfold encF
      rw [hGu])
    (fun ω y => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      unfold encF
      rw [hGv])
    (fun f => by simpa using slot_uniform m₀ p L P5 U u ϱ hϱ f)
    (fun f => by simpa using slot_uniform_snd m₀ p L P5 U v ϱ hϱ f) hM hmu hmv

/-! ## `DensityCancellation` from `lem:record:lift-moments`(c) alone -/

section Final

variable [∀ L j, Fact (p L j).Prime] {P : Type} [Fintype P] (pr h : P → ℕ)
  [∀ q, NeZero (pr q ^ h q)]

open Sarkozy.TheoremC Sarkozy.IndexSupport Sarkozy.Comparison in
/-- **`lem:record:density-can` (WP-FI's `DensityCancellation`) from the lift moments alone.**
Hypotheses:
* elementary facts about the data: distinct tail primes, `P₅ ≥ 64`, `M₀` coprime to every atom
  modulus, the atom moduli pairwise coprime, the prefix moduli prime powers `pp_i^{ep_i}`, and the
  coverage of the primes up to `N^{1/40}`;
* `lem:record:lift-moments`(c) in two forms:
  - `hmom4`: the fourth moments `E_{G_N} |g^{I_b, M₀, s}|⁴ ≤ C_ε N^{72δ} α` of the inputs, for all
    `b`, `s` (`r = 2`);
  - `hSteps`: Step 2, `LiftMoments` at the encoded data of every query.

Proved: Step 1 (WP-K), and all of Step 3: the intervals, the fibre formulas, the size of `D`,
`H D_E ≤ Q`, the coprimality and coverage conditions, the square class of `𝔞₂ − 𝔞₁` (from the
acceptance (b)), the uniformity of `𝔞₁` and the `L²` bound (from the uniform one-slot marginals
and the strict-square pairs). -/
theorem densityCancellation_of_lift_moments (P5 : ℕ) (pp ep : J₀ → ℕ)
    (hinj : ∀ L, Function.Injective (p L)) (h64 : 64 ≤ P5) {C₂ Cε : ℝ} (hC₂ : 0 ≤ C₂)
    (hCε : 0 ≤ Cε) (L₁ : ℕ)
    (hcop0 : ∀ L (c : J₀ ⊕ J L), Nat.Coprime (modulus pr h) (joinModuli m₀ (p L) c))
    (hcopE : ∀ L, ∀ i j : J₀ ⊕ J L, i ≠ j →
      Nat.Coprime (joinModuli m₀ (p L) i) (joinModuli m₀ (p L) j))
    (hpre : ∀ i, (pp i).Prime ∧ 1 ≤ ep i ∧ m₀ i = pp i ^ ep i)
    (hcover : ∀ L : ℕ, ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ (1 / 40 : ℝ) →
      ℓ ∣ modulus pr h ∨ (∃ i, ℓ ∣ m₀ i) ∨ ∃ j, p L j = ℓ)
    (hmom4 : ∀ L : ℕ, L₁ ≤ L → ∀ A : Finset ℤ, Admissible (blockScale * L) A →
      ∀ (bI : ZMod blockScale) (s : ZMod (modulus pr h)),
      (FiniteLaw.uniform (ResidueSpace (joinModuli m₀ (p L)))).expect (fun z =>
        |indexedInput (joinModuli m₀ (p L)) (paperCutoff (blockScale * L)) blockScale L
          (modulus pr h) A (bI, s) z| ^ 4) ≤
        Cε * ((blockScale * L : ℕ) : ℝ) ^ (72 * stageDelta) * density (blockScale * L) A)
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
          (density (blockScale * L) A)) :
    DensityCancellation m₀ p pr h P5 pp ep := by
  apply densityCancellation_of_moments m₀ p pr h P5 pp ep hinj h64 hC₂ hCε L₁ hcop0 hcopE hpre
    hcover
  intro L hL A hA ϱ hϱ u v huv ha hb bI s r hbI hr G hGu hGv hGw
  refine ⟨hSteps L hL A hA ϱ hϱ u v huv ha hb bI s r hbI hr G hGu hGv hGw, fun U _ => ?_⟩
  have hM : 0 ≤ Cε * ((blockScale * L : ℕ) : ℝ) ^ (72 * stageDelta) * density (blockScale * L) A :=
    mul_nonneg (mul_nonneg hCε (by positivity)) (density_nonneg _ _)
  exact fibreL2_of_fourth_moments m₀ p L P5 U u v ϱ hϱ G
    (indexedInput (joinModuli m₀ (p L)) (paperCutoff (blockScale * L)) blockScale L
      (modulus pr h) A (bI, s))
    (indexedInput (joinModuli m₀ (p L)) (paperCutoff (blockScale * L)) blockScale L
      (modulus pr h) A (bI + 1, s + r))
    (fun x => by rw [hGu]; rfl) (fun x => by rw [hGv]; rfl) (blockScale * L) Cε
    (density (blockScale * L) A) hM (hmom4 L hL A hA bI s) (hmom4 L hL A hA (bI + 1) (s + r))

end Final

end Sarkozy.CancellationSteps
