module

public import Sarkozy.Functional.FibreScale
public import Sarkozy.Functional.PrefixModel
public import Sarkozy.Kernel.IndicatorCorollary

@[expose] public section

/-!
# `lem:record:fibre-scale`(a) on the free coordinates `X_{𝒮'}`

Step 3 of `lem:record:density-can` applies `lem:record:fibre-scale`(a) "with the conditioned atoms
in the role of `E`" and reads the result as a statement about the functions
`g = G(x, y, ·)` on `X_{𝒮'}`, the free coordinates. WP-FI's `groupCoeff_input_freeze`
(`Sarkozy.Functional.FibreScale`) states the formula on the whole group for the frozen function
`y ↦ g(coordinateFreeze E z y)` and a frequency vanishing on `E`. This file transfers it to the
group of the free coordinates `{j // j ∉ E}`:

* `groupCoeff_restrictFree`: the coefficient on `X_{𝒮'}` of `y' ↦ G(freeze(z, y'))` at `a` is
  the coefficient on the whole group of `y ↦ G(freeze(z, y))` at the extension of `a` by `0`;
* `groupCoeff_input_free`: hence, for `g = g^{I,D₀,s}` and `q(a) ∏_{j ∈ E} m_j ≤ Q`,
  `ĝ(a) = (D/|I|) ∑_{x ∈ A ∩ I, x ∈ fibre} e(−x ξ_a)` on `X_{𝒮'}`, `D = D₀ ∏_{j ∈ E} m_j`;
* `inFibre_iff_modEq`: for coprime moduli the fibre is one class `𝔞` modulo `D` (CRT), so the
  sum runs over `A ∩ I ∩ (𝔞 + Dℤ)`;
* `fibre_formula_of_input`: the fibre formula in the form used by Step 3
  (`Sarkozy.Cancellation.norm_lowPart_le`), with `I = [u, v]`, `𝔏 = |I|` and
  `H ∏_{j ∈ E} m_j ≤ Q` (`lem:scale-conditions`(vi)).

New material for this paper.
-/

namespace Sarkozy.Cancellation

open Finset Complex
open scoped BigOperators ComplexConjugate
open Sarkozy.FourierArithmetic Sarkozy.Functional

section Restriction

variable {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)] (E : Finset J)

/-- The moduli of the free coordinates `{j // j ∉ E}`. -/
abbrev freeModuli : {j : J // j ∉ E} → ℕ := fun k => m k.1

/-- The restriction of a label to the free coordinates. -/
def restrictFree (y : ResidueSpace m) : ResidueSpace (freeModuli m E) := fun k => y k.1

/-- The extension of a free label by `0` on `E`. -/
def extendFree (y : ResidueSpace (freeModuli m E)) : ResidueSpace m :=
  fun j => if h : j ∈ E then 0 else y ⟨j, h⟩

omit [Fintype J] [∀ j, NeZero (m j)] in
lemma extendFree_mem (y : ResidueSpace (freeModuli m E)) {j : J} (hj : j ∈ E) :
    extendFree m E y j = 0 := by
  simp [extendFree, hj]

omit [Fintype J] [∀ j, NeZero (m j)] in
lemma extendFree_free (y : ResidueSpace (freeModuli m E)) (k : {j : J // j ∉ E}) :
    extendFree m E y k.1 = y k := by
  simp [extendFree, k.2]

lemma prod_free_eq {M : Type*} [CommMonoid M] (f : J → M) (hf : ∀ j ∈ E, f j = 1) :
    ∏ j, f j = ∏ k : {j : J // j ∉ E}, f k.1 := by
  rw [← prod_compl_mul_prod E, prod_eq_one hf, mul_one]
  exact prod_subtype Eᶜ (fun j => mem_compl) f

lemma prodChar_extendFree (a : ResidueSpace (freeModuli m E)) (y : ResidueSpace m) :
    prodChar m (extendFree m E a) y = prodChar (freeModuli m E) a (restrictFree m E y) := by
  unfold prodChar
  rw [prod_free_eq E _ (fun j hj => by rw [extendFree_mem m E a hj, zero_mul,
    AddChar.map_zero_eq_one])]
  apply prod_congr rfl
  intro k _
  rw [extendFree_free]
  rfl

omit [∀ j, NeZero (m j)] in
lemma conductor_extendFree (a : ResidueSpace (freeModuli m E)) :
    Functional.conductor m (extendFree m E a) = Functional.conductor (freeModuli m E) a := by
  unfold Functional.conductor
  rw [prod_free_eq E _ (fun j hj => by rw [extendFree_mem m E a hj, addOrderOf_zero])]
  apply prod_congr rfl
  intro k _
  rw [extendFree_free]

/-- Averaging a function of the free coordinates over the whole group. -/
lemma expect_restrictFree (F : ResidueSpace (freeModuli m E) → ℂ) :
    𝔼 y : ResidueSpace m, F (restrictFree m E y) = 𝔼 y' : ResidueSpace (freeModuli m E), F y' := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun j => j ∈ E) (fun j => ZMod (m j))
  rw [Fintype.expect_equiv e (fun y => F (restrictFree m E y)) (fun w => F w.2) (fun y => rfl)]
  rw [← univ_product_univ, expect_product]
  simp only [Fintype.expect_const]

/-- The coefficient on `X_{𝒮'}` of a frozen function is its coefficient on the whole group at
the extension by `0`. -/
theorem groupCoeff_restrictFree (G : ResidueSpace m → ℂ) (z : ResidueSpace m)
    (a : ResidueSpace (freeModuli m E)) :
    groupCoeff (freeModuli m E) (fun y' => G (coordinateFreeze m E z (extendFree m E y'))) a =
      groupCoeff m (fun y => G (coordinateFreeze m E z y)) (extendFree m E a) := by
  unfold groupCoeff
  have hfreeze : ∀ y, coordinateFreeze m E z y =
      coordinateFreeze m E z (extendFree m E (restrictFree m E y)) := by
    intro y
    funext j
    unfold coordinateFreeze
    by_cases hj : j ∈ E
    · simp [hj]
    · simp [hj, extendFree, restrictFree]
  have hpt : ∀ y, G (coordinateFreeze m E z y) * conj (prodChar m (extendFree m E a) y) =
      (fun y' => G (coordinateFreeze m E z (extendFree m E y')) *
        conj (prodChar (freeModuli m E) a y')) (restrictFree m E y) := by
    intro y
    simp only
    rw [prodChar_extendFree, ← hfreeze]
  simp_rw [hpt]
  exact (expect_restrictFree m E _).symm

/-- **`lem:record:fibre-scale`(a) on `X_{𝒮'}`**: for `g = g^{I,D₀,s}` frozen at `z` on `E` and a
frequency `a` of the free coordinates with `q(a) ∏_{j ∈ E} m_j ≤ Q`,
`ĝ(a) = (D/|I|) ∑_{x ∈ A ∩ I, x ∈ fibre} e(−x ξ_a)`, `D = D₀ ∏_{j ∈ E} m_j`. -/
theorem groupCoeff_input_free {Q : ℝ} (I : Finset ℤ) {D0 : ℕ} (s : ZMod D0) (A : Finset ℤ)
    (z : ResidueSpace m) (a : ResidueSpace (freeModuli m E))
    (hQ : (Functional.conductor (freeModuli m E) a : ℝ) * (∏ j ∈ E, m j : ℕ) ≤ Q) :
    groupCoeff (freeModuli m E)
        (fun y' => input m Q I D0 s A (coordinateFreeze m E z (extendFree m E y'))) a =
      ((D0 * ∏ j ∈ E, m j : ℕ) : ℂ) * (I.card : ℂ)⁻¹ *
        ∑ x ∈ (A ∩ I).filter (InFibre m E z s),
          conj (prodChar (freeModuli m E) a (integerResidue (freeModuli m E) x)) := by
  rw [groupCoeff_restrictFree m E (input m Q I D0 s A) z a]
  rw [groupCoeff_input_freeze m I s A E z (extendFree m E a)
    (fun j hj => extendFree_mem m E a hj) (by rw [conductor_extendFree]; exact hQ)]
  congr 1
  apply sum_congr rfl
  intro x _
  rw [prodChar_extendFree]
  congr 2

end Restriction

/-! ## The fibre as one residue class -/

section Fibre

variable {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)] (E : Finset J)

/-- The moduli `D₀` and `m_j` (`j ∈ E`) of the fibre conditions, indexed by `Option E`. -/
def fibreModuli (D0 : ℕ) : Option {j : J // j ∈ E} → ℕ
  | none => D0
  | some j => m j.1

omit [Fintype J] [DecidableEq J] [∀ j, NeZero (m j)] in
lemma prod_fibreModuli (D0 : ℕ) :
    ∏ i, fibreModuli m E D0 i = D0 * ∏ j ∈ E, m j := by
  rw [Fintype.prod_option]
  simp only [fibreModuli]
  rw [prod_coe_sort E m]

omit [Fintype J] [DecidableEq J] [∀ j, NeZero (m j)] in
/-- **The fibre is one residue class** (CRT): if `D₀` and the `m_j`, `j ∈ E`, are pairwise
coprime, there is `𝔞` with `x ∈ fibre ⟺ x ≡ 𝔞 (mod D₀ ∏_{j ∈ E} m_j)`. -/
theorem inFibre_iff_modEq {D0 : ℕ} (s : ZMod D0) (z : ResidueSpace m)
    (hcop0 : ∀ j ∈ E, Nat.Coprime D0 (m j))
    (hcopE : ∀ i ∈ E, ∀ j ∈ E, i ≠ j → Nat.Coprime (m i) (m j)) :
    ∃ 𝔞 : ℤ, ∀ x : ℤ, InFibre m E z s x ↔ x ≡ 𝔞 [ZMOD ((D0 * ∏ j ∈ E, m j : ℕ) : ℤ)] := by
  classical
  have hcop : Pairwise (Function.onFun Nat.Coprime (fibreModuli m E D0)) := by
    intro i k hik
    cases i with
    | none =>
      cases k with
      | none => exact absurd rfl hik
      | some k => exact hcop0 k.1 k.2
    | some i =>
      cases k with
      | none => exact (hcop0 i.1 i.2).symm
      | some k =>
        exact hcopE i.1 i.2 k.1 k.2 (fun h => hik (congrArg some (Subtype.ext h)))
  set φ := ZMod.prodEquivPi (fibreModuli m E D0) hcop with hφ
  let t : ∀ i, ZMod (fibreModuli m E D0 i) := fun i =>
    match i with
    | none => s
    | some j => z j.1
  set w := φ.symm t with hw
  refine ⟨(w.cast : ℤ), ?_⟩
  intro x
  have hprod := prod_fibreModuli m E D0
  have key : InFibre m E z s x ↔ (x : ZMod (∏ i, fibreModuli m E D0 i)) = w := by
    rw [hw, RingEquiv.eq_symm_apply]
    constructor
    · rintro ⟨h0, hE⟩
      funext i
      rw [ZMod.prodEquivPi_apply, map_intCast]
      cases i with
      | none => exact h0
      | some j => exact hE j.1 j.2
    · intro h
      refine ⟨?_, ?_⟩
      · have := congrFun h none
        rwa [ZMod.prodEquivPi_apply, map_intCast] at this
      · intro j hj
        have := congrFun h (some ⟨j, hj⟩)
        rwa [ZMod.prodEquivPi_apply, map_intCast] at this
  rw [key, ← hprod, ← ZMod.intCast_eq_intCast_iff, ZMod.intCast_zmod_cast]

end Fibre

/-! ## The fibre formula in the form of Step 3 -/

section Step3Form

variable {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)] (E : Finset J)

/-- **The fibre formula of Step 3** (`lem:record:fibre-scale`(a) with the conditioned atoms in
the role of `E`, read on `X_{𝒮'}`): for the input `g = g^{[u,v],D₀,s}` frozen at `z` on `E`, with
`D₀` and the `m_j`, `j ∈ E`, pairwise coprime, the free coordinates prime and
`H ∏_{j ∈ E} m_j ≤ Q`, there is a class `𝔞` modulo `D = D₀ ∏_{j ∈ E} m_j` with
`ĝ(ξ) = (D/𝔏) ∑_{n ∈ A ∩ [u,v], n ≡ 𝔞 (D)} e(−nξ)` for `q(ξ) ≤ H`, `𝔏 = #[u, v]`. -/
theorem fibre_formula_of_input [∀ k : {j : J // j ∉ E}, Fact (m k.1).Prime]
    {Q H : ℝ} (u v : ℤ) {D0 : ℕ} (s : ZMod D0) (A : Finset ℤ) (z : ResidueSpace m)
    (hcop0 : ∀ j ∈ E, Nat.Coprime D0 (m j))
    (hcopE : ∀ i ∈ E, ∀ j ∈ E, i ≠ j → Nat.Coprime (m i) (m j))
    (hHQ : H * (∏ j ∈ E, m j : ℕ) ≤ Q) :
    ∃ 𝔞 : ℤ, ∀ a : ResidueSpace (freeModuli m E), (supportDenominator (freeModuli m E) a : ℝ) ≤ H →
      groupCoeff (freeModuli m E)
          (fun y' => input m Q (Icc u v) D0 s A (coordinateFreeze m E z (extendFree m E y'))) a =
        ((D0 * ∏ j ∈ E, m j : ℕ) : ℂ) * ((((Icc u v).card : ℕ) : ℝ) : ℂ)⁻¹ *
          ∑ n ∈ Kernel.classPart A u v 𝔞 (D0 * ∏ j ∈ E, m j),
            conj (prodChar (freeModuli m E) a (integerResidue (freeModuli m E) n)) := by
  obtain ⟨𝔞, h𝔞⟩ := inFibre_iff_modEq m E s z hcop0 hcopE
  refine ⟨𝔞, ?_⟩
  intro a ha
  have hcond : (Functional.conductor (freeModuli m E) a : ℝ) * (∏ j ∈ E, m j : ℕ) ≤ Q := by
    rw [conductor_eq_supportDenominator (freeModuli m E) (fun k => Fact.out) a]
    exact le_trans (mul_le_mul_of_nonneg_right ha (by positivity)) hHQ
  rw [groupCoeff_input_free m E (Icc u v) s A z a hcond]
  have hset : (A ∩ Icc u v).filter (InFibre m E z s) =
      Kernel.classPart A u v 𝔞 (D0 * ∏ j ∈ E, m j) := by
    ext x
    unfold Kernel.classPart
    rw [mem_filter, mem_filter, mem_inter, mem_Icc, h𝔞 x]
    tauto
  rw [hset, Complex.ofReal_natCast]

end Step3Form

end Sarkozy.Cancellation
