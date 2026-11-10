module

public import Sarkozy.BracketEnergy.TwoInterval
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.Convex.Jensen

@[expose] public section

/-!
# The local densities of the revealed inputs average to the density

At a fixed index the revealed-input chain (`EnvFirst`) prices the query slot of `e` with the
**local** density `ᾱ_e = (D_𝒥/L) #(A ∩ I_b ∩ {x ≡ s (mod D_𝒥)})` of the revealed input
`g^{I_b, D_𝒥, s mod D_𝒥}`, which can exceed `α`. The paper bounds the energy at fixed `𝒥` after
the average over the index (`lem:envelope-energy`, proof; `def:record:structured-energy`, the
mean density `ᾱ_v`). This file proves the averaging:

* `sum_residue_card`: `∑_{s mod M₀} #(B ∩ {x ≡ s (mod D)}) = (M₀/D) #B` for `D ∣ M₀`;
* **`mean_localDensity`**: over a uniform index `(b, s) ∈ ℤ/Kℤ × ℤ/M₀ℤ`,
  `E ᾱ(b, s mod D) = α` (`lem:twointerval`(iii) for the densities);
* `expect_rpow_le` (Jensen): `E X^p ≤ (E X)^p` for `X ≥ 0`, `0 ≤ p ≤ 1`;
* `mean_localDensity_rpow_le`: `E (ᾱ/α)^p ≤ 1`;
* **`env_localDensity_mean_le`**: over a uniform index `ω` of the queries, with each query at its
  own depth `𝒥_e`, `E_ω ∏_e (ᾱ_e(ω_e)/α)^{p} ≤ 1` (independence of the queries,
  `expect_uniform_pi_prod`). With `p = 2θ/72` (the two slots of a query) this is the factor by
  which the per-index chain bound exceeds the conductor price `Π_𝒥 Y`; its mean is at most one,
  so the main part of the signed remainders of `hfirst` averages to at most zero.
-/

open Finset Function
open scoped BigOperators

namespace Sarkozy.BracketEnergy

open Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.FourierArithmetic

/-- **Jensen's inequality for a finite law and `x ↦ x^p`, `0 ≤ p ≤ 1`.** -/
theorem expect_rpow_le {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω) (X : Ω → ℝ)
    (hX : ∀ ω, 0 ≤ X ω) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    P.expect (fun ω => X ω ^ p) ≤ (P.expect X) ^ p := by
  have h := (Real.concaveOn_rpow hp0 hp1).le_map_sum (t := univ) (w := P.weight) (p := X)
    (fun i _ => P.nonneg i) P.total (fun i _ => Set.mem_Ici.mpr (hX i))
  unfold FiniteLaw.expect
  simpa only [smul_eq_mul] using h

/-- The normalized local density `(D/L) #(A ∩ I_b ∩ {x ≡ t (mod D)})`. -/
noncomputable def localDensity (K L : ℕ) (A : Finset ℤ) (D : ℕ) (b : ZMod K) (t : ZMod D) : ℝ :=
  (D : ℝ) / L * (((A ∩ blockInterval K L b).filter fun x : ℤ => (x : ZMod D) = t).card : ℝ)

theorem localDensity_nonneg (K L : ℕ) (A : Finset ℤ) (D : ℕ) (b : ZMod K) (t : ZMod D) :
    0 ≤ localDensity K L A D b t :=
  mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

/-- `∑_{s mod M₀} #(B ∩ {x ≡ s (mod D)}) = (M₀/D) #B` for `D ∣ M₀`. -/
theorem sum_residue_card {M0 D : ℕ} [NeZero M0] (hD : D ∣ M0) (B : Finset ℤ) :
    ∑ s : ZMod M0,
        ((B.filter fun x : ℤ => (x : ZMod D) = ZMod.castHom hD (ZMod D) s).card : ℝ) =
      ((M0 : ℝ) / D) * B.card := by
  have hD0 : D ≠ 0 := fun h0 => NeZero.ne M0 (Nat.eq_zero_of_zero_dvd (h0 ▸ hD))
  have hfib : ∀ x : ℤ, ((univ.filter fun s : ZMod M0 =>
      (x : ZMod D) = ZMod.castHom hD (ZMod D) s).card : ℝ) = (M0 : ℝ) / D := by
    intro x
    have hc := card_residueFibre hD (x : ZMod D)
    have heq : (univ.filter fun s : ZMod M0 => (x : ZMod D) = ZMod.castHom hD (ZMod D) s) =
        residueFibre hD (x : ZMod D) := by
      ext s
      simp only [residueFibre, mem_filter, mem_univ, true_and]
      exact eq_comm
    rw [heq, eq_div_iff (by exact_mod_cast hD0)]
    exact_mod_cast hc
  simp only [card_filter, Nat.cast_sum]
  rw [sum_comm]
  have h2 : ∀ x ∈ B, ∑ s : ZMod M0,
      (((if (x : ZMod D) = ZMod.castHom hD (ZMod D) s then 1 else 0 : ℕ)) : ℝ) =
        (M0 : ℝ) / D := by
    intro x _
    rw [← hfib x, card_filter, Nat.cast_sum]
  rw [sum_congr rfl h2, sum_const, nsmul_eq_mul, mul_comm]

/-- **The mean of the local densities is the density** (`lem:twointerval`(iii) for the
densities): over a uniform `(b, s) ∈ ℤ/Kℤ × ℤ/M₀ℤ`, `E ᾱ(b, s mod D) = α`. -/
theorem mean_localDensity {K L M0 D : ℕ} [NeZero K] [NeZero M0] (hL : 1 ≤ L) (hD : D ∣ M0)
    (A : Finset ℤ) (hA : A ⊆ Icc 1 ((K * L : ℕ) : ℤ)) :
    (FiniteLaw.uniform (ZMod K × ZMod M0)).expect
        (fun x => localDensity K L A D x.1 (ZMod.castHom hD (ZMod D) x.2)) =
      density (K * L) A := by
  have hD0 : (D : ℝ) ≠ 0 := by
    have : D ≠ 0 := fun h0 => NeZero.ne M0 (Nat.eq_zero_of_zero_dvd (h0 ▸ hD))
    exact_mod_cast this
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
  have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne K
  have hM0 : (M0 : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M0
  -- the blocks partition `A`
  have hpart : ∑ b : ZMod K, ((A ∩ blockInterval K L b).card : ℝ) = A.card := by
    have hdisj : ((univ : Finset (ZMod K)) : Set (ZMod K)).PairwiseDisjoint
        (fun b => A ∩ blockInterval K L b) :=
      (blockInterval_pairwiseDisjoint L).mono fun b => inter_subset_right
    have hU : (univ : Finset (ZMod K)).biUnion (fun b => A ∩ blockInterval K L b) = A := by
      rw [← inter_biUnion, biUnion_blockInterval, inter_eq_left.mpr hA]
    calc ∑ b : ZMod K, ((A ∩ blockInterval K L b).card : ℝ)
        = (((univ : Finset (ZMod K)).biUnion (fun b => A ∩ blockInterval K L b)).card : ℝ) := by
          rw [card_biUnion hdisj, Nat.cast_sum]
      _ = A.card := by rw [hU]
  rw [FiniteLaw.expect_uniform, Fintype.card_prod, ZMod.card, ZMod.card, Fintype.sum_prod_type]
  unfold localDensity
  simp_rw [← mul_sum]
  simp_rw [sum_residue_card hD]
  rw [← Finset.mul_sum, hpart]
  unfold density
  push_cast
  field_simp

/-- `E (ᾱ/α)^p ≤ 1` for `0 ≤ p ≤ 1` and `α > 0`. -/
theorem mean_localDensity_rpow_le {K L M0 D : ℕ} [NeZero K] [NeZero M0] (hL : 1 ≤ L)
    (hD : D ∣ M0) (A : Finset ℤ) (hA : A ⊆ Icc 1 ((K * L : ℕ) : ℤ))
    (hα : 0 < density (K * L) A) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (FiniteLaw.uniform (ZMod K × ZMod M0)).expect
        (fun x => (localDensity K L A D x.1 (ZMod.castHom hD (ZMod D) x.2) /
          density (K * L) A) ^ p) ≤ 1 := by
  refine le_trans (expect_rpow_le _ _ (fun x => div_nonneg (localDensity_nonneg _ _ _ _ _ _)
    hα.le) hp0 hp1) ?_
  have hmean : (FiniteLaw.uniform (ZMod K × ZMod M0)).expect
      (fun x => localDensity K L A D x.1 (ZMod.castHom hD (ZMod D) x.2) / density (K * L) A) =
      1 := by
    rw [show (fun x : ZMod K × ZMod M0 =>
        localDensity K L A D x.1 (ZMod.castHom hD (ZMod D) x.2) / density (K * L) A) =
        fun x => (density (K * L) A)⁻¹ *
          localDensity K L A D x.1 (ZMod.castHom hD (ZMod D) x.2) by
      funext x; rw [div_eq_inv_mul],
      FiniteLaw.expect_const_mul, mean_localDensity hL hD A hA, inv_mul_cancel₀ hα.ne']
  rw [hmean, Real.one_rpow]

/-- The uniform law is invariant under an equivalence. -/
theorem expect_uniform_equiv {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (σ : X ≃ Y) (F : Y → ℝ) :
    (FiniteLaw.uniform Y).expect F = (FiniteLaw.uniform X).expect (F ∘ σ) := by
  rw [FiniteLaw.expect_uniform, FiniteLaw.expect_uniform, Fintype.card_congr σ]
  congr 1
  exact (σ.sum_comp F).symm

variable {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- The local density of the revealed input of `envC` at the index `η` of one query, at the
depth vector `J`: `ᾱ = (D_J/L) #(A ∩ I_b ∩ {x ≡ s (mod D_J)})`, `b = η_none`. -/
noncomputable def queryLocalDensity (L : ℕ) (A : Finset ℤ)
    (J : ∀ j, Fin ((coordChain blockScale pr h j).depth + 1))
    (η : ∀ j : Option P, CoordSpace blockScale pr h j) : ℝ :=
  localDensity blockScale L A (revealedModulus blockScale pr h J) (η none)
    (revealedResidue hcop J η)

/-- **The local densities of the revealed inputs average out**: for every assignment of depth
vectors to the queries, over a uniform index `ω`,
`E_ω ∏_e (ᾱ_e(ω_e)/α)^p ≤ 1` (`0 ≤ p ≤ 1`, `α > 0`). -/
theorem env_localDensity_mean_le {E : Type} [Fintype E] [DecidableEq E] {L : ℕ} (hL : 1 ≤ L)
    (A : Finset ℤ) (hA : A ⊆ Icc 1 ((blockScale * L : ℕ) : ℤ))
    (hα : 0 < density (blockScale * L) A) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) :
    (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
        (fun ω => ∏ e, (queryLocalDensity hcop L A (Jq e) (ω e) /
          density (blockScale * L) A) ^ p) ≤ 1 := by
  rw [expect_uniform_pi_prod (Ωe := fun _ : E => ∀ j : Option P, CoordSpace blockScale pr h j)
    (fun e η => (queryLocalDensity hcop L A (Jq e) η / density (blockScale * L) A) ^ p)]
  apply prod_le_one₀
  · intro e _
    exact FiniteLaw.expect_nonneg _ fun η => Real.rpow_nonneg
      (div_nonneg (localDensity_nonneg _ _ _ _ _ _) hα.le) _
  · intro e _
    rw [expect_uniform_equiv (crtEquiv blockScale pr h hcop)]
    have hx : ∀ x : ZMod blockScale × ZMod (modulus pr h),
        ((fun η => (queryLocalDensity hcop L A (Jq e) η / density (blockScale * L) A) ^ p) ∘
          crtEquiv blockScale pr h hcop) x =
        (localDensity blockScale L A (revealedModulus blockScale pr h (Jq e)) x.1
          (ZMod.castHom (revealedModulus_dvd (Jq e))
            (ZMod (revealedModulus blockScale pr h (Jq e))) x.2) /
          density (blockScale * L) A) ^ p := by
      intro x
      simp only [Function.comp_apply, queryLocalDensity, revealedResidue,
        Equiv.symm_apply_apply]
      rfl
    rw [show ((fun η => (queryLocalDensity hcop L A (Jq e) η / density (blockScale * L) A) ^ p) ∘
        crtEquiv blockScale pr h hcop) = fun x : ZMod blockScale × ZMod (modulus pr h) =>
        (localDensity blockScale L A (revealedModulus blockScale pr h (Jq e)) x.1
          (ZMod.castHom (revealedModulus_dvd (Jq e))
            (ZMod (revealedModulus blockScale pr h (Jq e))) x.2) /
          density (blockScale * L) A) ^ p from funext hx]
    exact mean_localDensity_rpow_le hL (revealedModulus_dvd (Jq e)) A hA hα hp0 hp1

end Sarkozy.BracketEnergy
