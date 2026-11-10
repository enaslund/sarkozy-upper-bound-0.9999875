module

public import Sarkozy.Structured.DensityStructured
public import Sarkozy.Functional.FibreCount

/-!
# The changed-slot bound for the paper's square-step model

This file instantiates the changed-slot step of `prop:record:density-structured`
(`Sarkozy.Structured.changed_slot_bound`) with the objects of WP-FI's Functional
layer (`Sarkozy/Functional/FibreScale.lean`, `FibreCount.lean`). These are:

* the group `ResidueSpace m` with coordinates `J` and pairwise coprime moduli `m`;
* the selected coordinates `E`;
* the specialized label `z`;
* the index `(I, D₀, s)` with `I = Icc (c+1) (c+M)`;
* the square step `R = sq(D₀ D_E)` (`stepR`);
* the scale `ℓ = ⌈M/(KR)⌉` (`stepEll`), with `n = K ℓ`;
* the children `h_j = Re 𝓛^𝒮_{[n],Q'} 1_{A'_j}` (`child`) and the maps `T_j` (`stepMap`);
* the paper's model `g̃ = Re squareStepModel`.

A function on `X_𝒮` is represented, as in WP-FI's layer, by a function on the
whole group that does not depend on the coordinates of `E`; the reference law
`μ_𝒮` is a `FiniteLaw` on `Slot → ResidueSpace m`.

* `re_squareStepModel`: `g̃ = λ ∑_{j ∈ J_𝔞} |J_𝔞|⁻¹ (h_j ∘ T_j)`, using `|J_𝔞| D = R`
  (`card_stepResidues`).
* `referenceEnergy_child_comp`: `Z_𝒮(h_j ∘ T_j) = Z_𝒮(h_j)`. This holds when `μ_𝒮` is
  invariant under the maps `T_j` acting off `E` ((R3) for the primes of `𝒮`); since
  `h_j` does not depend on the coordinates of `E` (`stepLift_congr`), only
  `stepMapOff` enters.
* `changed_slot_bound_paper`: **the bound at a changed slot for the paper's model**,
  `Z_𝒮(g̃) ≤ (1 + u) C₀ L^{-a} ξ^a α_f^θ`, with `ξ = (N/|I|) R` and `α_f` the fibre
  density. Its remaining hypotheses are:
  - the restoration inequality `Z_𝒮(h) ≤ Y(ℓ, B)` at the scale `ℓ`
    (`lem:record:fibre-scale`(c), hypothesis `hrest`). WP-FI's
    `Sarkozy.Functional.referenceEnergy_stepLift_le_scale` proves it in two-scale
    product form, i.e. when the scale-`N` law is the product of the scale-`ℓ`
    law and a law on the extra coordinates of modulus `> n^β`, and is invariant
    under translations supported on `E`. `restoration_of_two_scales`
    (`Sarkozy/Structured/ScaleInputs.lean`) derives `hrest` from it for a group of the
    form `joinModuli m₀ p`;
  - (R3) for the maps `T_j` (`hinvT`);
  - the scale condition `λ^{72} ≤ 1 + u` (`hlamu`, from
    `Sarkozy.Functional.scaleConsequences` with `u = u_L`);
  - the hypothesis on smaller scales of `def:record:counterexample`.
-/

@[expose] public section

open Finset Complex
open scoped BigOperators

namespace Sarkozy.Structured

open Sarkozy.Functional Sarkozy.FourierArithmetic

section Paper

variable {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)]

/-- The square step `R = sq(D₀ D_E)`, `D_E = ∏_{j ∈ E} m_j`. -/
noncomputable def stepR (E : Finset J) (D0 : ℕ) : ℕ := leastSquare (D0 * ∏ j ∈ E, m j)

/-- The scale `ℓ = ⌈|I|/(K R)⌉` of the children, `K = blockScale`. -/
noncomputable def stepEll (E : Finset J) (D0 M : ℕ) : ℕ := stepScale blockScale M (stepR m E D0)

/-- The children `h_j = Re 𝓛^𝒮_{[n],Q'} 1_B` as real functions on the group. -/
noncomputable def child (E : Finset J) (Q' : ℝ) (B : Finset ℤ) (n : ℕ) :
    ResidueSpace m → ℝ :=
  fun y => (stepLift m E Q' B n y).re

/-- The fibre density `α_f = (D/|I|) #{x ∈ A ∩ I : x ≡ 𝔞 (mod D)}`, `I = Icc (c+1) (c+M)`. -/
noncomputable def fibreDensity (E : Finset J) (z : ResidueSpace m) {D0 : ℕ} (s : ZMod D0)
    (A : Finset ℤ) (c : ℤ) (M : ℕ) : ℝ :=
  ((D0 * ∏ j ∈ E, m j : ℕ) : ℝ) / M *
    ((A ∩ Icc (c + 1) (c + M)).filter (InFibre m E z s)).card

/-- **The square-step model as an average**: `g̃ = λ ∑_{j ∈ J_𝔞} |J_𝔞|⁻¹ (h_j ∘ T_j)`. -/
theorem re_squareStepModel (E : Finset J) (z : ResidueSpace m) {D0 : ℕ} (s : ZMod D0)
    (A : Finset ℤ) (c : ℤ) (M R n : ℕ) (Q' : ℝ) (hR : R ≠ 0)
    (hcard : ((stepResidues m E z s R c).card : ℝ) * ((D0 * ∏ j ∈ E, m j : ℕ) : ℝ) = R) :
    (fun y => (squareStepModel m E z s A (Icc (c + 1) (c + M)) c M R n Q' y).re) =
      ((R * n : ℝ) / M) • ∑ j ∈ stepResidues m E z s R c,
        (((stepResidues m E z s R c).card : ℝ)⁻¹) •
          (child m E Q' (stepChild A (Icc (c + 1) (c + M)) R n c j) n ∘ stepMap m R c j) := by
  have hJ : ((stepResidues m E z s R c).card : ℝ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hcard
    exact hR (by exact_mod_cast hcard.symm)
  have hR' : (R : ℝ) ≠ 0 := by exact_mod_cast hR
  have hD : ((D0 * ∏ j ∈ E, m j : ℕ) : ℝ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hcard
    exact hR' hcard.symm
  have hDR : ((D0 * ∏ j ∈ E, m j : ℕ) : ℝ) / R = ((stepResidues m E z s R c).card : ℝ)⁻¹ := by
    rw [← hcard]
    field_simp
  funext y
  have hpre : ((R * n : ℂ) / M) * ((D0 * ∏ j ∈ E, m j : ℕ) : ℂ) / R =
      ((((R * n : ℝ) / M) * (((D0 * ∏ j ∈ E, m j : ℕ) : ℝ) / R) : ℝ) : ℂ) := by
    push_cast
    ring
  unfold squareStepModel
  rw [hpre, Complex.re_ofReal_mul, Complex.re_sum, hDR]
  simp only [Finset.sum_apply, Pi.smul_apply, Function.comp, child, smul_eq_mul]
  simp only [Finset.mul_sum]
  apply sum_congr rfl
  intro j _
  ring

/-- `Z_𝒮(h_j ∘ T_j) = Z_𝒮(h_j)` when `μ_𝒮` is invariant under `T_j` acting off `E`. -/
theorem referenceEnergy_child_comp (μS : FiniteLaw (Slot → ResidueSpace m)) (E : Finset J)
    (Q' : ℝ) (B : Finset ℤ) (n R : ℕ) (c j : ℤ)
    (hinv : ∀ F : (Slot → ResidueSpace m) → ℝ,
      μS.expect (fun w => F (fun v => stepMapOff m E R c j (w v))) = μS.expect F) :
    referenceEnergy μS (child m E Q' B n ∘ stepMap m R c j) =
      referenceEnergy μS (child m E Q' B n) := by
  have hcongr : child m E Q' B n ∘ stepMap m R c j = child m E Q' B n ∘ stepMapOff m E R c j := by
    funext y
    simp only [Function.comp, child]
    congr 1
    apply stepLift_congr
    intro k hk
    simp [stepMapOff, hk]
  rw [hcongr]
  exact SignedHolder.diagonalIntegral_comp_of_invariant (L := signedIntegral μS.weight) _ hinv _

/-- **The bound at a changed slot for the paper's square-step model**
(`prop:record:density-structured`, changed slots, with `lem:record:fibre-scale`(b), (d)):
`Z_𝒮(g̃) ≤ (1 + u) C₀ L^{-a} ξ^a α_f^θ`, `ξ = (N/|I|) R`, `N = K L`. -/
theorem changed_slot_bound_paper (μS : FiniteLaw (Slot → ResidueSpace m))
    (hμS : SlotReflectionPositive (signedIntegral μS.weight)) (E : Finset J)
    (z : ResidueSpace m) {D0 : ℕ} (hD0 : 1 ≤ D0) (s : ZMod D0)
    (hcop0 : ∀ k, D0.Coprime (m k)) (hpair : Pairwise fun i j => (m i).Coprime (m j))
    (A : Finset ℤ) (hA : IsSquareDifferenceFree A) (c : ℤ) {M L : ℕ} (hM : 1 ≤ M) (hL : 2 ≤ L)
    (hML : M = blockScale * L ∨ M = L)
    (hchg : ¬(D0 * ∏ j ∈ E, m j = 1 ∧ M = blockScale * L)) (Q' : ℝ)
    {Yf : ℕ → Finset ℤ → ℝ} {a θ C0 u : ℝ} (ha : 0 ≤ a) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 72)
    (hC0 : 0 ≤ C0) (hsmall : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < L → ScaleBound Yf a θ C0 ℓ)
    (hrest : ∀ B : Finset ℤ, B ⊆ Icc 1 ((blockScale * stepEll m E D0 M : ℕ) : ℤ) →
      referenceEnergy μS (child m E Q' B (blockScale * stepEll m E D0 M)) ≤
        Yf (stepEll m E D0 M) B)
    (hinvT : ∀ j : ℤ, ∀ F : (Slot → ResidueSpace m) → ℝ,
      μS.expect (fun w => F (fun v => stepMapOff m E (stepR m E D0) c j (w v))) = μS.expect F)
    (hlamu : (((stepR m E D0 : ℕ) : ℝ) * ((blockScale * stepEll m E D0 M : ℕ) : ℝ) / M) ^ 72 ≤
      1 + u) :
    referenceEnergy μS (fun y => (squareStepModel m E z s A (Icc (c + 1) (c + M)) c M
        (stepR m E D0) (blockScale * stepEll m E D0 M) Q' y).re) ≤
      (1 + u) * C0 * (L : ℝ) ^ (-a) *
        ((((blockScale * L : ℕ) : ℝ) / M) * (stepR m E D0 : ℕ)) ^ a *
        fibreDensity m E z s A c M ^ θ := by
  set R := stepR m E D0 with hRdef
  set ℓ := stepEll m E D0 M with hℓdef
  set n := blockScale * ℓ with hndef
  have hcond := leastSquare_step_conditions m (E := E) hD0 hcop0 hpair
  have hR1 : 1 ≤ R := hcond.1
  have hD0R : D0 ∣ R := hcond.2.1
  have hER : ∀ i ∈ E, m i ∣ R := hcond.2.2.1
  have hDne : D0 * ∏ j ∈ E, m j ≠ 0 :=
    Nat.mul_ne_zero (by omega) (prod_ne_zero_iff.mpr fun j _ => NeZero.ne (m j))
  have hDR : D0 * ∏ j ∈ E, m j ∣ R := dvd_leastSquare hDne
  have hcardN : (stepResidues m E z s R c).card * (D0 * ∏ j ∈ E, m j) = R :=
    card_stepResidues m z hD0 s hcop0 hpair hR1 hDR c
  have hcard : ((stepResidues m E z s R c).card : ℝ) * ((D0 * ∏ j ∈ E, m j : ℕ) : ℝ) = R := by
    exact_mod_cast hcardN
  have hK : 1 ≤ blockScale := by norm_num [blockScale]
  have hK2 : 2 ≤ blockScale := by norm_num [blockScale]
  have hMRn : M ≤ R * n := (stepScale_bounds (M := M) hK hR1).1
  have hlam1 : 1 ≤ (R * n : ℝ) / M := by
    have h := (stepScale_lambda (M := M) hK hR1 hM).1
    have e : ((n : ℕ) : ℝ) = (blockScale : ℝ) * (stepScale blockScale M R : ℝ) := by
      rw [hndef]
      push_cast
      rfl
    rw [e]
    exact h
  have hℓgeL : (L : ℝ) / (((blockScale * L : ℕ) : ℝ) / M * R) ≤ ℓ :=
    stepScale_ge_scale (K := blockScale) (L := L) hK (by omega) hR1 hM
  have hℓlt : ℓ < L := stepScale_lt hK2 hL (Nat.one_le_iff_ne_zero.mpr hDne) hML hchg
  have hℓ1 : 1 ≤ ℓ := by
    rcases Nat.eq_zero_or_pos ℓ with h0 | h0
    · exfalso
      have : n = 0 := by rw [hndef, h0, mul_zero]
      rw [this, mul_zero] at hMRn
      omega
    · exact h0
  have hJne : (stepResidues m E z s R c).Nonempty := by
    rw [← Finset.card_pos]
    rcases Nat.eq_zero_or_pos (stepResidues m E z s R c).card with h0 | h0
    · rw [h0, zero_mul] at hcardN
      omega
    · exact h0
  -- the square-step model as an average
  rw [re_squareStepModel m E z s A c M R n Q' (by omega) hcard]
  -- apply the abstract bound
  have hmain := changed_slot_bound μS hμS (stepResidues m E z s R c) hJne
    (fun j => child m E Q' (stepChild A (Icc (c + 1) (c + M)) R n c j) n)
    (fun j => stepMap m R c j)
    (fun j _ => referenceEnergy_child_comp m μS E Q' _ n R c j (hinvT j))
    (lam := ((R * n : ℝ) / M)) (C0 := C0) (a := a) (θ := θ) (ℓ := (ℓ : ℝ)) (L := (L : ℝ))
    (ξ := (((blockScale * L : ℕ) : ℝ) / M) * (R : ℕ)) (αf := fibreDensity m E z s A c M)
    (u := u) hlam1
    (by
      have e : ((R : ℕ) : ℝ) * ((n : ℕ) : ℝ) / M = (R * n : ℝ) / M := rfl
      rw [← e]
      exact hlamu) hC0 ha hθ0 hθ1 (by exact_mod_cast (show 0 < L by omega))
    (by
      have hM' : (0 : ℝ) < M := by exact_mod_cast hM
      have hN' : (0 : ℝ) < ((blockScale * L : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_pos (by omega) (by omega)
      have hR' : (0 : ℝ) < ((R : ℕ) : ℝ) := by exact_mod_cast hR1
      positivity)
    hℓgeL
    (fun j => density (blockScale * ℓ) (stepChild A (Icc (c + 1) (c + M)) R n c j))
    (fun j _ => density_nonneg _ _)
    (by
      intro j _
      have hadm : Admissible (blockScale * ℓ) (stepChild A (Icc (c + 1) (c + M)) R n c j) := by
        constructor
        · intro x hx
          exact (mem_filter.mp hx).1
        · obtain ⟨r, hr⟩ := exists_sq_eq_leastSquare (D0 * ∏ j ∈ E, m j)
          have hr1 : 1 ≤ r := by
            rcases Nat.eq_zero_or_pos r with h0 | h0
            · rw [h0] at hr
              have := leastSquare_pos (D0 * ∏ j ∈ E, m j)
              simp at hr
              omega
            · exact h0
          exact stepChild_free hA (Icc (c + 1) (c + M)) hr hr1 n c j
      refine (hrest _ (fun x hx => (mem_filter.mp hx).1)).trans ?_
      exact hsmall ℓ hℓ1 hℓlt _ hadm)
    (by
      have hdens := stepChild_density m (E := E) (z := z) (s := s) A c (n := n) hM hR1 hMRn
        hD0R hER
      have hDRr : ((D0 * ∏ j ∈ E, m j : ℕ) : ℝ) / R =
          ((stepResidues m E z s R c).card : ℝ)⁻¹ := by
        have hR' : (R : ℝ) ≠ 0 := by exact_mod_cast (show R ≠ 0 by omega)
        rw [← hcard]
        have hJ : ((stepResidues m E z s R c).card : ℝ) ≠ 0 := by
          exact_mod_cast (Finset.card_pos.mpr hJne).ne'
        field_simp
      rw [hDRr] at hdens
      unfold fibreDensity density
      rw [← hdens])
  exact hmain

end Paper

end Sarkozy.Structured
