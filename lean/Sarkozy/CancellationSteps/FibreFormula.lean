module

public import Sarkozy.CancellationSteps.FreeCoords

/-!
# The fibre formulas of `FibreData` for the encoded query inputs

`paper/sections/08_scale_comparison.tex`, `lem:record:density-can`, Step 3, "by
`lem:record:fibre-scale`(a) with the conditioned atoms in the role of `E`": for the encoded pair
factor `F₁(x, ·) = g^{I, D₀, s}(mergeAt x ·)` of `PaperEncoding` (WP-FI's input, read through
`mergeAt` and `atomGroupEquiv`), frozen on the conditioned atoms (`frozenCoords`: the prefix, the
tail primes below `P₅` and those of `U`), the coefficient on the free tail primes
`{k // U k = false}` at a frequency `a` with `q(a) ≤ H` is
`(D/|I|) ∑_{n ∈ A ∩ I, n ≡ 𝔞 (D)} e(−n ξ_a)`, `D = D₀ ∏_{c ∈ E} m_c`, for every class `𝔞` of the
fibre (`encInput_fibre_formula`). The class exists when `D₀` and the frozen moduli are pairwise
coprime (`Cancellation.inFibre_iff_modEq`, CRT).

This is the fibre-formula part of WP-K's `FibreData`, which was a hypothesis of
`Cancellation.densityCancellation_of_steps`.

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

omit [DecidableEq J₀] [∀ i, NeZero (m₀ i)] [∀ L, DecidableEq (J L)] [∀ L j, NeZero (p L j)] in
/-- The free coordinates of the joined group are tail primes. -/
theorem freeJoinModuli_prime [hprime : ∀ L j, Fact (p L j).Prime] (L P5 : ℕ)
    (U : TailIdx p L P5 → Bool) (c : {c : J₀ ⊕ J L // c ∉ frozenCoords (J₀ := J₀) p L P5 U}) :
    (freeJoinModuli m₀ p L P5 U c).Prime := by
  obtain ⟨c, hc⟩ := c
  have hfree := (not_mem_frozenCoords p L P5 U c).mp hc
  cases c with
  | inl i => exact absurd hfree id
  | inr j => exact (hprime L j).out

/-- The fibre modulus `D = D₀ ∏_{c ∈ E} m_c` of Step 3. -/
def fibreModulus (L P5 : ℕ) (U : TailIdx p L P5 → Bool) (D0 : ℕ) : ℕ :=
  D0 * ∏ c ∈ frozenCoords (J₀ := J₀) p L P5 U, joinModuli m₀ (p L) c

/-- **The fibre formula for an encoded query input** (`lem:record:fibre-scale`(a) on the free
tail primes, Step 3 of `lem:record:density-can`): let `F(x') = Re g^{I, D₀, s}(mergeAt x
(mergeFree U y x'))` be the input read through the encoding of `PaperEncoding`, with `I = [u, v]`,
and let `𝔞` be a class of the fibre at the frozen label `z = mergeAt x y` (`n ∈ fibre ⟺
n ≡ 𝔞 (D)`). If `H ∏_{c ∈ E} m_c ≤ Q`, then for every frequency `a` of the free tail primes with
`q(a) ≤ H`, `F̂(a) = (D/|I|) ∑_{n ∈ A ∩ [u, v], n ≡ 𝔞 (D)} e(−n ξ_a)`, `D = fibreModulus`. -/
theorem encInput_fibre_formula [∀ L j, Fact (p L j).Prime] (L P5 : ℕ) (U : TailIdx p L P5 → Bool)
    {Q H : ℝ} (u v : ℤ) {D0 : ℕ} (s : ZMod D0) (A : Finset ℤ)
    (xw : ∀ i : {b : PaperAtom J L // IsLow p L P5 b}, AtomLabel m₀ p L i.1)
    (y₀ : ∀ k : TailIdx p L P5, ZMod (tailQ p L P5 k)) (𝔞 : ℤ)
    (h𝔞 : ∀ n : ℤ, InFibre (joinModuli m₀ (p L)) (frozenCoords (J₀ := J₀) p L P5 U)
      (atomGroupEquiv m₀ p L (mergeAt m₀ p L P5 xw y₀)) s n ↔
        n ≡ 𝔞 [ZMOD ((fibreModulus m₀ p L P5 U D0 : ℕ) : ℤ)])
    (hHQ : H * (∏ c ∈ frozenCoords (J₀ := J₀) p L P5 U, joinModuli m₀ (p L) c : ℕ) ≤ Q)
    (a : ResidueSpace (fun k : {k : TailIdx p L P5 // U k = false} => tailQ p L P5 k.1))
    (ha : (supportDenominator (fun k : {k : TailIdx p L P5 // U k = false} => tailQ p L P5 k.1) a
      : ℝ) ≤ H) :
    groupCoeff (fun k : {k : TailIdx p L P5 // U k = false} => tailQ p L P5 k.1)
        (fun x' => ((input (joinModuli m₀ (p L)) Q (Icc u v) D0 s A
          (atomGroupEquiv m₀ p L (mergeAt m₀ p L P5 xw (mergeFree U y₀ x')))).re : ℂ)) a =
      ((fibreModulus m₀ p L P5 U D0 : ℕ) : ℂ) * (((Icc u v).card : ℝ) : ℂ)⁻¹ *
        ∑ n ∈ Kernel.classPart A u v 𝔞 (fibreModulus m₀ p L P5 U D0),
          conj (prodChar (fun k : {k : TailIdx p L P5 // U k = false} => tailQ p L P5 k.1) a
            (integerResidue (fun k : {k : TailIdx p L P5 // U k = false} => tailQ p L P5 k.1)
              n)) := by
  set E := frozenCoords (J₀ := J₀) p L P5 U with hE
  set m := joinModuli m₀ (p L) with hm
  set z := atomGroupEquiv m₀ p L (mergeAt m₀ p L P5 xw y₀) with hz
  set R := freeLabel m₀ p L P5 U with hR
  -- the input is real; the encoded label is a frozen label
  have hfun : (fun x' : ResidueSpace (fun k : {k : TailIdx p L P5 // U k = false} =>
      tailQ p L P5 k.1) => ((input m Q (Icc u v) D0 s A
        (atomGroupEquiv m₀ p L (mergeAt m₀ p L P5 xw (mergeFree U y₀ x')))).re : ℂ)) =
      fun x' => input m Q (Icc u v) D0 s A
        (coordinateFreeze m E z (Cancellation.extendFree m E (R x'))) := by
    funext x'
    rw [input_real, atomGroupEquiv_mergeAt_freeze]
  rw [hfun]
  -- reindex the free coordinates
  have hre : groupCoeff (fun k : {k : TailIdx p L P5 // U k = false} => tailQ p L P5 k.1)
      (fun x' => input m Q (Icc u v) D0 s A
        (coordinateFreeze m E z (Cancellation.extendFree m E (R x')))) a =
      groupCoeff (Cancellation.freeModuli m E)
        (fun y => input m Q (Icc u v) D0 s A
          (coordinateFreeze m E z (Cancellation.extendFree m E y))) (R a) := by
    have h := groupCoeff_reindex (freeEquiv (J₀ := J₀) p L P5 U) (freeJoinModuli m₀ p L P5 U)
      (fun x' => input m Q (Icc u v) D0 s A
        (coordinateFreeze m E z (Cancellation.extendFree m E (R x')))) a
    refine h.trans ?_
    congr 1
    funext y
    show input m Q (Icc u v) D0 s A (coordinateFreeze m E z (Cancellation.extendFree m E
      (R (R.symm y)))) = _
    rw [Equiv.apply_symm_apply]
  rw [hre]
  -- the fibre formula on the free coordinates of the joined group
  have hsd :
      supportDenominator (fun k : {k : TailIdx p L P5 // U k = false} => tailQ p L P5 k.1) a =
        supportDenominator (Cancellation.freeModuli m E) (R a) :=
    supportDenominator_reindex (freeEquiv (J₀ := J₀) p L P5 U) (freeJoinModuli m₀ p L P5 U) a
  have hcond : (Functional.conductor (Cancellation.freeModuli m E) (R a) : ℝ) *
      (∏ c ∈ E, m c : ℕ) ≤ Q := by
    rw [conductor_eq_supportDenominator (Cancellation.freeModuli m E)
      (fun c => freeJoinModuli_prime m₀ p L P5 U c) (R a), ← hsd]
    exact le_trans (mul_le_mul_of_nonneg_right ha (by positivity)) hHQ
  rw [groupCoeff_input_free m E (Icc u v) s A z (R a) hcond]
  have hset : (A ∩ Icc u v).filter (InFibre m E z s) =
      Kernel.classPart A u v 𝔞 (fibreModulus m₀ p L P5 U D0) := by
    ext n
    unfold Kernel.classPart
    rw [mem_filter, mem_filter, mem_inter, mem_Icc, h𝔞 n]
    tauto
  rw [hset]
  have hchar : ∀ n : ℤ, prodChar (Cancellation.freeModuli m E) (R a)
      (integerResidue (Cancellation.freeModuli m E) n) =
      prodChar (fun k : {k : TailIdx p L P5 // U k = false} => tailQ p L P5 k.1) a
        (integerResidue (fun k : {k : TailIdx p L P5 // U k = false} => tailQ p L P5 k.1) n) := by
    intro n
    have h1 : reindexLabel (freeEquiv (J₀ := J₀) p L P5 U) (freeJoinModuli m₀ p L P5 U)
        (integerResidue (fun k : {k : TailIdx p L P5 // U k = false} => tailQ p L P5 k.1) n) =
        integerResidue (freeJoinModuli m₀ p L P5 U) n :=
      integerResidue_reindex _ _ n
    have h2 := prodChar_reindex (freeEquiv (J₀ := J₀) p L P5 U) (freeJoinModuli m₀ p L P5 U) a
      (integerResidue (fun k : {k : TailIdx p L P5 // U k = false} => tailQ p L P5 k.1) n)
    rw [h1] at h2
    exact h2
  simp_rw [hchar]
  unfold fibreModulus
  rw [Complex.ofReal_natCast]

end Sarkozy.CancellationSteps
