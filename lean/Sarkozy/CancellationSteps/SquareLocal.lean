module

public import Sarkozy.Cancellation.SquareClass
public import Sarkozy.Functional.UnitSquares

/-!
# Local square conditions for Step 3 of `lem:record:density-can`

* `kernel_of_functional_squareClass`: WP-FI's `def:nonvanishing-square-class` on `ℤ/Dℤ`
  (`Functional.IsNonvanishingSquareClass`, through the coordinate representatives) gives the
  congruence form of WP-K's kernel (`Kernel.IsNonvanishingSquareClass`) for the representative
  `r.val`;
* `oddLocalSquare_of_prefix`: the prefix acceptance condition (`TheoremC.AcceptedPair` at the
  prefix: nonzero, `p^{2j}` times a unit square, `2j < e`) modulo `m = p^e` gives the odd local
  condition at `p` for every integer lift;
* `oddLocalSquare_of_square`: a nonzero square modulo a prime `p` gives the odd local condition
  with exponent `1`.

New material for this paper.
-/

@[expose] public section

namespace Sarkozy.CancellationSteps

open Finset Sarkozy.Cancellation

/-- **The two forms of `def:nonvanishing-square-class`**: `Functional.IsNonvanishingSquareClass D r`
(`r ∈ ℤ/Dℤ`) gives `Kernel.IsNonvanishingSquareClass D r.val`. -/
theorem kernel_of_functional_squareClass {D : ℕ} (hD : D ≠ 0) {r : ZMod D}
    (h : Functional.IsNonvanishingSquareClass D r) :
    Kernel.IsNonvanishingSquareClass D (r.val : ℤ) := by
  obtain ⟨h2, hp⟩ := h
  refine ⟨h2, fun p hpp hpD => ?_⟩
  have hpf : p ∈ D.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hpD, hD⟩
  obtain ⟨hc0, hev, hrest⟩ := hp p hpf
  set c := Functional.coordinateRep D p r with hc
  set v := padicValNat p c with hv
  obtain ⟨j, hj⟩ := hev
  set u := c / p ^ v with hu
  have hdvd : p ^ v ∣ c := pow_padicValNat_dvd
  have hcu : c = p ^ v * u := (Nat.mul_div_cancel' hdvd).symm
  have hnot : ¬ p ∣ u := by
    have := Nat.not_dvd_ordCompl hpp hc0
    rwa [Nat.factorization_def c hpp] at this
  have hpos : 0 < p ^ D.factorization p := pow_pos hpp.pos _
  have hmod : (r.val : ℤ) ≡ (c : ℤ) [ZMOD (p : ℤ) ^ D.factorization p] := by
    have hc' : (c : ℤ) = (r.val : ℤ) % ((p : ℤ) ^ D.factorization p) := by
      rw [hc]
      unfold Functional.coordinateRep
      push_cast
      rfl
    rw [hc']
    exact (Int.mod_modEq _ _).symm
  have hvj : v = 2 * j := by omega
  refine ⟨j, (u : ℤ), by exact_mod_cast hnot, ?_, ?_⟩
  · refine hmod.trans ?_
    rw [hcu, ← hvj]
    push_cast
    rfl
  · split_ifs at hrest with hp2
    · simp only [hp2, ↓reduceIte]
      subst hp2
      obtain ⟨h3, h8⟩ := hrest
      refine ⟨by rw [← hvj]; exact h3, ?_⟩
      have : u % 8 = 1 := h8
      exact Int.ModEq.symm (by
        unfold Int.ModEq
        have h' : ((u : ℕ) : ℤ) % 8 = 1 := by exact_mod_cast this
        rw [h']
        norm_num)
    · simp only [hp2, ↓reduceIte]
      obtain ⟨hsq, -⟩ := hrest
      refine ⟨?_, by exact_mod_cast hsq⟩
      have hclt : c < p ^ D.factorization p := by
        rw [hc]
        unfold Functional.coordinateRep
        exact Nat.mod_lt _ hpos
      have hle : p ^ v ≤ c := Nat.le_of_dvd (Nat.pos_of_ne_zero hc0) hdvd
      have := lt_of_le_of_lt hle hclt
      rw [← hvj]
      exact (Nat.pow_lt_pow_iff_right hpp.one_lt).mp this

/-- **The prefix acceptance condition gives the odd local condition**: if `d ∈ ℤ/p^eℤ` is
nonzero and `d = p^{2j} ρ` with `2j < e` and `ρ` a unit square, then every integer `δ` with
`δ ≡ d (mod p^e)` satisfies `OddLocalSquare p e δ`. -/
theorem oddLocalSquare_of_prefix {m P e : ℕ} (hm : m = P ^ e) (hP : P.Prime) (he : 1 ≤ e)
    {d : ZMod m}
    (hacc : ∃ jj : ℕ, 2 * jj < e ∧ ∃ ρ : ZMod m, IsUnit ρ ∧ IsSquare ρ ∧
      d = ((P : ℕ) : ZMod m) ^ (2 * jj) * ρ)
    {δ : ℤ} (hδ : (δ : ZMod m) = d) : OddLocalSquare P e δ := by
  subst hm
  obtain ⟨jj, hjj, ρ, hunit, hsq, hd⟩ := hacc
  have hne : NeZero (P ^ e) := ⟨pow_ne_zero _ hP.ne_zero⟩
  refine ⟨jj, (ρ.val : ℤ), ?_, ?_, hjj, ?_⟩
  · intro hdiv
    have hcop : Nat.Coprime ρ.val (P ^ e) := by
      have := ZMod.val_coe_unit_coprime hunit.unit
      simpa using this
    have hPdvd : P ∣ ρ.val := by exact_mod_cast hdiv
    have hPe : P ∣ P ^ e := dvd_pow_self P (by omega)
    have h1 := (Nat.Coprime.coprime_dvd_left hPdvd hcop).eq_one_of_dvd hPe
    exact hP.one_lt.ne' h1
  · rw [show ((P : ℤ)) ^ e = ((P ^ e : ℕ) : ℤ) by push_cast; rfl,
      ← ZMod.intCast_eq_intCast_iff]
    push_cast
    rw [hδ, hd, ZMod.natCast_zmod_val]
  · obtain ⟨σ, hσ⟩ := hsq
    refine ⟨ZMod.castHom (dvd_pow_self P (by omega : e ≠ 0)) (ZMod P) σ, ?_⟩
    rw [← map_mul, ← hσ, ZMod.castHom_apply, ZMod.cast_eq_val]
    push_cast
    rfl

/-- A nonzero square modulo a prime `p` gives the odd local condition at `p` with exponent `1`. -/
theorem oddLocalSquare_of_square {P : ℕ} {d : ZMod P} (hd : d ≠ 0) (hsq : IsSquare d) {δ : ℤ}
    (hδ : (δ : ZMod P) = d) : OddLocalSquare P 1 δ := by
  refine oddLocalSquare_one ?_ (by rw [hδ]; exact hsq)
  intro hdiv
  apply hd
  rw [← hδ]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd δ P).mpr hdiv

end Sarkozy.CancellationSteps
