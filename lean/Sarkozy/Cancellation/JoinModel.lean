module

public import Sarkozy.Cancellation.FibreRestriction
public import Sarkozy.Cancellation.CondExpectation
public import Sarkozy.Cancellation.SquareClass

@[expose] public section

/-!
# The fibre formula of Step 3 in WP-FI's model `G_N = X_pre × X_tail`

WP-FI models the group as `ResidueSpace (joinModuli m₀ q)` on the coordinates `J₀ ⊕ J`: prefix
atoms `J₀` and tail primes `J` (`Sarkozy.Functional.PrefixModel`). In Step 3 of
`lem:record:density-can`, the conditioned atoms are the prefix and the tail primes of `U`
(`frozenSet U`); the free coordinates are the tail primes outside `U`, `{j // U j = false}`,
the indexing used by `density_can_of_pair_laws`.

`fibre_formula_joinModel` is `lem:record:fibre-scale`(a) (WP-FI's `groupCoeff_input_freeze`) for
`g = (g^{[u,v],D₀,s})(x₀, merge(y, ·))` on `X_{𝒮'}`, in exactly the form of the fibre hypothesis
of `density_can_of_pair_laws`: there is a class `𝔞` modulo `D = D₀ ∏_{E} m_j` with
`ĝ(ξ) = (D/𝔏) ∑_{n ∈ A ∩ [u,v], n ≡ 𝔞 (D)} e(−nξ)` for `q(ξ) ≤ H`, `H ∏_E m_j ≤ Q`.

New material for this paper.
-/

namespace Sarkozy.Cancellation

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Finset Complex
open scoped BigOperators ComplexConjugate
open Sarkozy.FourierArithmetic Sarkozy.Functional

section JoinModel

variable {J₀ J : Type*} [Fintype J₀] [DecidableEq J₀] [Fintype J] [DecidableEq J]
  (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)] (q : J → ℕ) [∀ j, NeZero (q j)] (U : J → Bool)

/-- The label `(x₀, y)` of `G_N = X_pre × X_tail`. -/
def joinVec (x₀ : ResidueSpace m₀) (y : ResidueSpace q) : ResidueSpace (joinModuli m₀ q) :=
  (splitEquiv m₀ q).symm (x₀, y)

omit [Fintype J₀] [DecidableEq J₀] [Fintype J] [DecidableEq J] [∀ i, NeZero (m₀ i)]
  [∀ j, NeZero (q j)] in
@[simp] lemma joinVec_inl (x₀ : ResidueSpace m₀) (y : ResidueSpace q) (i : J₀) :
    joinVec m₀ q x₀ y (Sum.inl i) = x₀ i := rfl

omit [Fintype J₀] [DecidableEq J₀] [Fintype J] [DecidableEq J] [∀ i, NeZero (m₀ i)]
  [∀ j, NeZero (q j)] in
@[simp] lemma joinVec_inr (x₀ : ResidueSpace m₀) (y : ResidueSpace q) (j : J) :
    joinVec m₀ q x₀ y (Sum.inr j) = y j := rfl

/-- The conditioned coordinates of Step 3: the prefix and the tail primes of `U`. -/
def frozenSet : Finset (J₀ ⊕ J) :=
  univ.map Function.Embedding.inl ∪
    (univ.filter (fun j => U j = true)).map Function.Embedding.inr

lemma inl_mem_frozenSet (i : J₀) : (Sum.inl i : J₀ ⊕ J) ∈ frozenSet U := by
  simp [frozenSet]

lemma inr_mem_frozenSet (j : J) : (Sum.inr j : J₀ ⊕ J) ∈ frozenSet U ↔ U j = true := by
  simp [frozenSet]

/-- The free moduli: the tail primes outside `U`. -/
abbrev tailFree : {j : J // U j = false} → ℕ := fun k => q k.1

/-- The restriction of a label of `G_N` to the free coordinates. -/
def restrictJoin (z : ResidueSpace (joinModuli m₀ q)) : ResidueSpace (tailFree q U) :=
  fun k => z (Sum.inr k.1)

/-- The extension of a free label by `0`. -/
def extendJoin (a : ResidueSpace (tailFree q U)) : ResidueSpace (joinModuli m₀ q) :=
  joinVec m₀ q 0 (mergeFree U (0 : ResidueSpace q) a)

omit [DecidableEq J] in
lemma prod_tail_free {M : Type*} [CommMonoid M] (f : J → M) (hf : ∀ j, U j = true → f j = 1) :
    ∏ j, f j = ∏ k : {j : J // U j = false}, f k.1 := by
  rw [← prod_filter_mul_prod_filter_not univ (fun j => U j = false)]
  have h1 : ∏ j ∈ univ.filter (fun j => ¬ U j = false), f j = 1 := by
    apply prod_eq_one
    intro j hj
    rw [mem_filter] at hj
    exact hf j (by simpa using hj.2)
  rw [h1, mul_one]
  exact prod_subtype _ (fun j => by simp) f

omit [Fintype J₀] [DecidableEq J₀] [Fintype J] [DecidableEq J] [∀ i, NeZero (m₀ i)]
  [∀ j, NeZero (q j)] in
lemma splitEquiv_extendJoin (a : ResidueSpace (tailFree q U)) :
    splitEquiv m₀ q (extendJoin m₀ q U a) = (0, mergeFree U (0 : ResidueSpace q) a) := by
  unfold extendJoin joinVec
  exact (splitEquiv m₀ q).apply_symm_apply _

omit [DecidableEq J₀] [DecidableEq J] in
lemma prodChar_extendJoin (a : ResidueSpace (tailFree q U)) (z : ResidueSpace (joinModuli m₀ q)) :
    prodChar (joinModuli m₀ q) (extendJoin m₀ q U a) z =
      prodChar (tailFree q U) a (restrictJoin m₀ q U z) := by
  rw [prodChar_split, splitEquiv_extendJoin, prodChar_zero, one_mul]
  unfold prodChar
  have hf : ∀ j, U j = true →
      (ZMod.stdAddChar (mergeFree U (0 : ResidueSpace q) a j * (splitEquiv m₀ q z).2 j) : ℂ) = 1 := by
    intro j hj
    rw [mergeFree_fixed (A := fun j => ZMod (q j)) U 0 a hj, Pi.zero_apply, zero_mul, AddChar.map_zero_eq_one]
  rw [prod_tail_free U _ hf]
  apply prod_congr rfl
  intro k _
  rw [mergeFree_free (A := fun j => ZMod (q j))]
  rfl

omit [DecidableEq J₀] [DecidableEq J] [∀ i, NeZero (m₀ i)] [∀ j, NeZero (q j)] in
lemma conductor_extendJoin (a : ResidueSpace (tailFree q U)) :
    Functional.conductor (joinModuli m₀ q) (extendJoin m₀ q U a) =
      Functional.conductor (tailFree q U) a := by
  rw [conductor_split, splitEquiv_extendJoin, conductor_zero, one_mul]
  unfold Functional.conductor
  have hf : ∀ j, U j = true → addOrderOf (mergeFree U (0 : ResidueSpace q) a j) = 1 := by
    intro j hj
    rw [mergeFree_fixed (A := fun j => ZMod (q j)) U 0 a hj, Pi.zero_apply, addOrderOf_zero]
  rw [prod_tail_free U _ hf]
  apply prod_congr rfl
  intro k _
  rw [mergeFree_free (A := fun j => ZMod (q j))]

lemma expect_restrictJoin (F : ResidueSpace (tailFree q U) → ℂ) :
    𝔼 z : ResidueSpace (joinModuli m₀ q), F (restrictJoin m₀ q U z) =
      𝔼 x' : ResidueSpace (tailFree q U), F x' := by
  classical
  rw [Fintype.expect_equiv (splitEquiv m₀ q).toEquiv (fun z => F (restrictJoin m₀ q U z))
    (fun w => F (fun k => w.2 k.1)) (fun z => rfl)]
  rw [← univ_product_univ, expect_product]
  simp only [Fintype.expect_const]
  let e := Equiv.piEquivPiSubtypeProd (fun j => U j = false) (fun j => ZMod (q j))
  rw [Fintype.expect_equiv e (fun y => F (fun k => y k.1)) (fun w => F w.1) (fun y => rfl)]
  rw [← univ_product_univ, expect_product]
  simp only [Fintype.expect_const]

omit [∀ i, NeZero (m₀ i)] [∀ j, NeZero (q j)] in
lemma freeze_joinVec (x₀ : ResidueSpace m₀) (y : ResidueSpace q)
    (z : ResidueSpace (joinModuli m₀ q)) :
    coordinateFreeze (joinModuli m₀ q) (frozenSet U) (joinVec m₀ q x₀ y) z =
      joinVec m₀ q x₀ (mergeFree U y (restrictJoin m₀ q U z)) := by
  funext k
  unfold coordinateFreeze
  cases k with
  | inl i => rw [ite_eq_left (inl_mem_frozenSet U i), joinVec_inl, joinVec_inl]
  | inr j =>
    by_cases hj : U j = true
    · rw [ite_eq_left ((inr_mem_frozenSet U j).mpr hj), joinVec_inr, joinVec_inr,
        mergeFree_fixed (A := fun j => ZMod (q j)) U y _ hj]
    · have hj' : U j = false := by simpa using hj
      rw [ite_eq_right (fun h => hj ((inr_mem_frozenSet U j).mp h)), joinVec_inr]
      simp [mergeFree, hj', restrictJoin]

/-- The coefficient on `X_{𝒮'}` of `G(x₀, merge(y, ·))` is the coefficient on `G_N` of the frozen
function at the extension by `0`. -/
theorem groupCoeff_joinVec (G : ResidueSpace (joinModuli m₀ q) → ℂ) (x₀ : ResidueSpace m₀)
    (y : ResidueSpace q) (a : ResidueSpace (tailFree q U)) :
    groupCoeff (tailFree q U) (fun x' => G (joinVec m₀ q x₀ (mergeFree U y x'))) a =
      groupCoeff (joinModuli m₀ q)
        (fun z => G (coordinateFreeze (joinModuli m₀ q) (frozenSet U) (joinVec m₀ q x₀ y) z))
        (extendJoin m₀ q U a) := by
  unfold groupCoeff
  have hpt : ∀ z, G (coordinateFreeze (joinModuli m₀ q) (frozenSet U) (joinVec m₀ q x₀ y) z) *
      conj (prodChar (joinModuli m₀ q) (extendJoin m₀ q U a) z) =
      (fun x' => G (joinVec m₀ q x₀ (mergeFree U y x')) * conj (prodChar (tailFree q U) a x'))
        (restrictJoin m₀ q U z) := by
    intro z
    simp only
    rw [freeze_joinVec, prodChar_extendJoin]
  simp_rw [hpt]
  exact (expect_restrictJoin m₀ q U _).symm

/-- **The fibre formula of Step 3 in WP-FI's model.** For the input `g^{[u,v],D₀,s}` of WP-FI
read at `(x₀, merge(y, ·))` on the tail primes outside `U` (its real part, which is the input,
by `input_real`), with `D₀` and the frozen moduli pairwise coprime, the free coordinates prime and
`H ∏_{E} m_j ≤ Q`: there is a class `𝔞` modulo `D = D₀ ∏_{E} m_j` with
`ĝ(ξ) = (D/𝔏) ∑_{n ∈ A ∩ [u,v], n ≡ 𝔞 (D)} e(−nξ)` for `q(ξ) ≤ H`, `𝔏 = #[u, v]`. -/
theorem fibre_formula_joinModel [∀ k : {j : J // U j = false}, Fact (q k.1).Prime]
    {Q H : ℝ} (u v : ℤ) {D0 : ℕ} (s : ZMod D0) (A : Finset ℤ) (x₀ : ResidueSpace m₀)
    (y : ResidueSpace q)
    (hcop0 : ∀ j ∈ frozenSet U, Nat.Coprime D0 (joinModuli m₀ q j))
    (hcopE : ∀ i ∈ frozenSet U, ∀ j ∈ frozenSet U, i ≠ j →
      Nat.Coprime (joinModuli m₀ q i) (joinModuli m₀ q j))
    (hHQ : H * (∏ j ∈ frozenSet U, joinModuli m₀ q j : ℕ) ≤ Q) :
    ∃ 𝔞 : ℤ, InFibre (joinModuli m₀ q) (frozenSet U) (joinVec m₀ q x₀ y) s 𝔞 ∧
      ∀ a : ResidueSpace (tailFree q U), (supportDenominator (tailFree q U) a : ℝ) ≤ H →
      groupCoeff (tailFree q U)
          (fun x' => ((input (joinModuli m₀ q) Q (Icc u v) D0 s A
            (joinVec m₀ q x₀ (mergeFree U y x'))).re : ℂ)) a =
        ((D0 * ∏ j ∈ frozenSet U, joinModuli m₀ q j : ℕ) : ℂ) *
          ((((Icc u v).card : ℕ) : ℝ) : ℂ)⁻¹ *
          ∑ n ∈ Kernel.classPart A u v 𝔞 (D0 * ∏ j ∈ frozenSet U, joinModuli m₀ q j),
            conj (prodChar (tailFree q U) a (integerResidue (tailFree q U) n)) := by
  obtain ⟨𝔞, h𝔞⟩ := inFibre_iff_modEq (joinModuli m₀ q) (frozenSet U) s
    (joinVec m₀ q x₀ y) hcop0 hcopE
  refine ⟨𝔞, (h𝔞 𝔞).mpr (Int.ModEq.refl _), ?_⟩
  intro a ha
  have hre : (fun x' => ((input (joinModuli m₀ q) Q (Icc u v) D0 s A
      (joinVec m₀ q x₀ (mergeFree U y x'))).re : ℂ)) =
      fun x' => input (joinModuli m₀ q) Q (Icc u v) D0 s A (joinVec m₀ q x₀ (mergeFree U y x')) := by
    funext x'
    exact input_real (joinModuli m₀ q) Q (Icc u v) D0 s A _
  rw [hre, groupCoeff_joinVec m₀ q U (input (joinModuli m₀ q) Q (Icc u v) D0 s A) x₀ y a]
  have hcond : (Functional.conductor (joinModuli m₀ q) (extendJoin m₀ q U a) : ℝ) *
      (∏ j ∈ frozenSet U, joinModuli m₀ q j : ℕ) ≤ Q := by
    rw [conductor_extendJoin, conductor_eq_supportDenominator (tailFree q U) (fun k => Fact.out) a]
    exact le_trans (mul_le_mul_of_nonneg_right ha (by positivity)) hHQ
  have hvan : ∀ j ∈ frozenSet U, extendJoin m₀ q U a j = 0 := by
    intro j hj
    cases j with
    | inl i => rfl
    | inr k =>
      have hk : U k = true := (inr_mem_frozenSet U k).mp hj
      change mergeFree U (0 : ResidueSpace q) a k = 0
      rw [mergeFree_fixed (A := fun j => ZMod (q j)) U 0 a hk, Pi.zero_apply]
  rw [groupCoeff_input_freeze (joinModuli m₀ q) (Icc u v) s A (frozenSet U) (joinVec m₀ q x₀ y)
    (extendJoin m₀ q U a) hvan hcond]
  have hset : (A ∩ Icc u v).filter (InFibre (joinModuli m₀ q) (frozenSet U) (joinVec m₀ q x₀ y) s) =
      Kernel.classPart A u v 𝔞 (D0 * ∏ j ∈ frozenSet U, joinModuli m₀ q j) := by
    ext x
    unfold Kernel.classPart
    rw [mem_filter, mem_filter, mem_inter, mem_Icc, h𝔞 x]
    tauto
  rw [hset, Complex.ofReal_natCast]
  congr 1
  apply sum_congr rfl
  intro n _
  rw [prodChar_extendJoin]
  rfl

/-- **The fibre hypothesis of `density_can_of_pair_laws`, discharged in WP-FI's model.** With the
pair factor `F(x, y) = Re g^{[u,v],D₀,s}(x_w(x), y)` (the input at the prefix label `x_w(x)` of
the slot `w`), for all labels `ω = (x, a)` the coefficient of `F(x, merge(sel(a), ·))` on the tail
primes outside `U` is given by the fibre formula at a class `𝔞(ω)` modulo
`D = D₀ ∏_{E} m_j`. Here `sel(a)` is the tail label of the slot: `x(a)` for `u`, `y(a)` for `v`. -/
theorem fibre_hypothesis_joinModel [∀ k : {j : J // U j = false}, Fact (q k.1).Prime]
    {X : Type*} {Q H : ℝ} (u v : ℤ) {D0 : ℕ} (s : ZMod D0) (A : Finset ℤ)
    (xu : X → ResidueSpace m₀) (sel : (∀ j, PairAlphabet q j) → ResidueSpace q)
    (hcop0 : ∀ j ∈ frozenSet U, Nat.Coprime D0 (joinModuli m₀ q j))
    (hcopE : ∀ i ∈ frozenSet U, ∀ j ∈ frozenSet U, i ≠ j →
      Nat.Coprime (joinModuli m₀ q i) (joinModuli m₀ q j))
    (hHQ : H * (∏ j ∈ frozenSet U, joinModuli m₀ q j : ℕ) ≤ Q) :
    ∃ 𝔞 : X × (∀ j, PairAlphabet q j) → ℤ,
      (∀ ω : X × (∀ j, PairAlphabet q j),
        InFibre (joinModuli m₀ q) (frozenSet U) (joinVec m₀ q (xu ω.1) (sel ω.2)) s (𝔞 ω)) ∧
      ∀ ω : X × (∀ j, PairAlphabet q j),
      ∀ a : ResidueSpace (fun k : {j // U j = false} => q k.1),
        (supportDenominator (fun k : {j // U j = false} => q k.1) a : ℝ) ≤ H →
        groupCoeff (fun k : {j // U j = false} => q k.1)
            (fun x' => (((fun x y => (input (joinModuli m₀ q) Q (Icc u v) D0 s A
              (joinVec m₀ q (xu x) y)).re) ω.1 (mergeFree U (sel ω.2) x') : ℝ) : ℂ))
            a =
          ((D0 * ∏ j ∈ frozenSet U, joinModuli m₀ q j : ℕ) : ℂ) *
            ((((Icc u v).card : ℕ) : ℝ) : ℂ)⁻¹ *
            ∑ n ∈ Kernel.classPart A u v (𝔞 ω) (D0 * ∏ j ∈ frozenSet U, joinModuli m₀ q j),
              conj (prodChar (fun k : {j // U j = false} => q k.1) a
                (integerResidue (fun k : {j // U j = false} => q k.1) n)) := by
  refine ⟨fun ω => Classical.choose (fibre_formula_joinModel m₀ q U (Q := Q) (H := H) u v s A
    (xu ω.1) (sel ω.2) hcop0 hcopE hHQ), fun ω => (Classical.choose_spec
      (fibre_formula_joinModel m₀ q U (Q := Q) (H := H) u v s A
        (xu ω.1) (sel ω.2) hcop0 hcopE hHQ)).1, ?_⟩
  intro ω a ha
  exact (Classical.choose_spec (fibre_formula_joinModel m₀ q U (Q := Q) (H := H) u v s A
    (xu ω.1) (sel ω.2) hcop0 hcopE hHQ)).2 a ha

/-- **The square class of Step 3 from the fibres.** Let `𝔞₁` lie in the fibre of
`(s, z₁)` and `𝔞₂` in the fibre of `(s + r, z₂)` over the frozen coordinates, the frozen moduli
being prime powers `P_j^{e_j}` with distinct primes coprime to `D₀`. If `r` is a nonvanishing
square class modulo `D₀` and the label differences `z₂ − z₁` satisfy the odd local condition at
every frozen coordinate (hypothesis (b) of `lem:record:density-can`, and `y_v − y_u ∈ Q_p` at
`U`), then `𝔞₂ − 𝔞₁` is a nonvanishing square class modulo `D = D₀ ∏_E m_j`. -/
theorem squareClass_of_fibres {D0 : ℕ} (hD0 : D0 ≠ 0) (P e : J₀ ⊕ J → ℕ)
    (hP : ∀ j ∈ frozenSet U, (P j).Prime)
    (hinj : Set.InjOn P ((frozenSet (J₀ := J₀) U : Finset (J₀ ⊕ J)) : Set (J₀ ⊕ J)))
    (hPe : ∀ j ∈ frozenSet U, joinModuli m₀ q j = P j ^ e j)
    (hcop : ∀ j ∈ frozenSet U, Nat.Coprime D0 (P j))
    {s : ZMod D0} {r : ℤ} (hr : Kernel.IsNonvanishingSquareClass D0 r)
    (z₁ z₂ : ResidueSpace (joinModuli m₀ q)) {𝔞₁ 𝔞₂ : ℤ}
    (h₁ : InFibre (joinModuli m₀ q) (frozenSet U) z₁ s 𝔞₁)
    (h₂ : InFibre (joinModuli m₀ q) (frozenSet U) z₂ (s + (r : ZMod D0)) 𝔞₂)
    (hloc : ∀ j ∈ frozenSet U, OddLocalSquare (P j) (e j) (((z₂ j - z₁ j).val : ℕ) : ℤ)) :
    Kernel.IsNonvanishingSquareClass (D0 * ∏ j ∈ frozenSet U, joinModuli m₀ q j) (𝔞₂ - 𝔞₁) := by
  have hprod : ∏ j ∈ frozenSet U, joinModuli m₀ q j = ∏ j ∈ frozenSet U, P j ^ e j :=
    prod_congr rfl hPe
  rw [hprod]
  apply squareClass_difference (frozenSet U) P e hP hinj hD0 hcop hr
  · -- `𝔞₂ − 𝔞₁ ≡ r (mod D₀)`
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    rw [h₁.1, h₂.1]
    ring
  · intro j hj
    apply oddLocalSquare_congr _ (hloc j hj)
    rw [← Nat.cast_pow, ← hPe j hj, ← ZMod.intCast_eq_intCast_iff]
    push_cast
    rw [ZMod.natCast_zmod_val, h₁.2 j hj, h₂.2 j hj]

end JoinModel

end Sarkozy.Cancellation
