module

public import Sarkozy.PaperFrame.RestorationPaper
public import Sarkozy.PaperFrame.StepInvariance
public import Sarkozy.Comparison.FibreEnergy

@[expose] public section

/-!
# The fibre energy bound for the paper's square-step model

The comparison worker's `Sarkozy.SignedHolder.fibre_energy_le` (`Comparison/FibreEnergy.lean`,
the core of `prop:record:density-structured`) bounds `Z(λ · ∑_j |J|⁻¹ (h_j ∘ T_j))` from the
energies of the children and the invariance of the maps `T_j`. Here it is instantiated with
the paper's objects at the scale `L`:

* `g̃ = squareStepModel …`, the square-step model of the input `g(z, ·)` on a fibre
  (`lem:record:fibre-scale`(b), with `R = sq(D)`, `ℓ = ⌈|I|/(KR)⌉`, `n = Kℓ`, cutoff
  `n^{1/20}`), read on `X₀ × X_tail`;
* `|J_𝔞| = R/D` (`card_stepResidues`), so `λD/R = λ |J_𝔞|⁻¹`;
* `Z(h_j ∘ T_j) = Z(h_j)` (`energy_stepMap_invariant`, (R3));
* `Z(h_j) ≤ C ℓ^{-a} α_j^θ` (`fibreScale_child_energy_le`: `lem:record:fibre-scale`(c) and the
  induction hypothesis at the scale `ℓ`);
* `(D/R) ∑_j α_j = α_f/λ` (`stepChild_density`).

`paper_fibre_energy_le`: `Z_{μ_N}(g̃) ≤ λ^{72} C ℓ^{-a} (α_f/λ)^θ`, `θ = densityExponent`,
`a = decay`.
-/

open Finset Function
open scoped BigOperators ComplexConjugate

namespace Sarkozy.PaperFrame

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.Comparison

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  (T : ℕ → Finset ℕ) [∀ L (j : ↥(T L)), NeZero (j : ℕ)]

/-- The real part of the square-step model as `λ · ∑_j |J|⁻¹ (h_j ∘ T_j)` on `X₀ × X_tail`. -/
theorem squareStepModel_re_eq {L : ℕ} (E : Finset (J₀ ⊕ ↥(T L)))
    (z : ResidueSpace (joinModuli m₀ (tailModuli T L))) {D0 : ℕ} (s : ZMod D0)
    (A : Finset ℤ) (c : ℤ) (M R n : ℕ) (Q' : ℝ)
    (hJ : ((stepResidues (joinModuli m₀ (tailModuli T L)) E z s R c).card : ℝ)⁻¹ =
      ((D0 * ∏ k ∈ E, joinModuli m₀ (tailModuli T L) k : ℕ) : ℝ) / R) :
    (fun x => (squareStepModel (joinModuli m₀ (tailModuli T L)) E z s A (Icc (c + 1) (c + M)) c M
        R n Q' ((splitEquiv m₀ (tailModuli T L)).symm x)).re) =
      ((R * n : ℝ) / M) • ∑ j ∈ stepResidues (joinModuli m₀ (tailModuli T L)) E z s R c,
        ((stepResidues (joinModuli m₀ (tailModuli T L)) E z s R c).card : ℝ)⁻¹ •
          ((fun x => (stepLift (joinModuli m₀ (tailModuli T L)) E Q'
              (stepChild A (Icc (c + 1) (c + M)) R n c j) n
              ((splitEquiv m₀ (tailModuli T L)).symm x)).re) ∘
            (fun x => splitEquiv m₀ (tailModuli T L) (stepMap (joinModuli m₀ (tailModuli T L)) R c j
              ((splitEquiv m₀ (tailModuli T L)).symm x)))) := by
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply,
    AddEquiv.symm_apply_apply]
  rw [hJ]
  unfold squareStepModel
  have hc : ((R * n : ℂ) / M) * ((D0 * ∏ k ∈ E, joinModuli m₀ (tailModuli T L) k : ℕ) : ℂ) / R =
      ((((R * n : ℝ) / M) * (((D0 * ∏ k ∈ E, joinModuli m₀ (tailModuli T L) k : ℕ) : ℝ) / R) :
        ℝ) : ℂ) := by
    push_cast
    ring
  rw [hc, Complex.re_ofReal_mul, Complex.re_sum, Finset.mul_sum, Finset.mul_sum]
  apply sum_congr rfl
  intro j _
  ring

/-- **The fibre energy bound for the paper's square-step model.**

At the scale `L` (tail `T L`), for a selection `E` of coordinates, a fibre label `z`, a
residue `s mod D₀`, a square-difference-free `A` and an interval `I = c + [M]`, with
`D = D₀ D_E`, `R = sq(D)`, `ℓ = ⌈M/(KR)⌉`, `n = Kℓ`, `λ = Rn/M` and
`α_f = (D/M) #{x ∈ A ∩ I : x ≡ 𝔞 (D)}`:

`Z_{μ_N}(g̃) ≤ λ^{72} · C ℓ^{-a} · (α_f/λ)^θ`,

provided the smaller scale has `T ℓ ⊆ T L` with all missing primes above `n^{1/20}`, the
atom laws are reflection positive and square-affine invariant ((R2), (R3)), and the
induction hypothesis holds at the scale `ℓ` with the constant `C ≥ 0`. -/
theorem paper_fibre_energy_le {L : ℕ} (E : Finset (J₀ ⊕ ↥(T L)))
    (hpair : Pairwise fun i j => (joinModuli m₀ (tailModuli T L) i).Coprime
      (joinModuli m₀ (tailModuli T L) j))
    (z : ResidueSpace (joinModuli m₀ (tailModuli T L))) {D0 : ℕ} (hD0 : 1 ≤ D0) (s : ZMod D0)
    (hcop0 : ∀ k, D0.Coprime (joinModuli m₀ (tailModuli T L) k))
    {A : Finset ℤ} (hA : IsSquareDifferenceFree A) (c : ℤ) {M : ℕ} (hM : 1 ≤ M)
    (hT : T (stepScale blockScale M (leastSquare (D0 * ∏ k ∈ E, joinModuli m₀ (tailModuli T L) k)))
      ⊆ T L)
    (hprime : ∀ q ∈ T L, q.Prime)
    (hlarge : ∀ q ∈ T L,
      q ∉ T (stepScale blockScale M (leastSquare (D0 * ∏ k ∈ E, joinModuli m₀ (tailModuli T L) k))) →
      paperCutoff (blockScale *
        stepScale blockScale M (leastSquare (D0 * ∏ k ∈ E, joinModuli m₀ (tailModuli T L) k))) < q)
    (μ₀ : FiniteLaw (Slot → ResidueSpace m₀))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q))
    (hp₀ : SlotReflectionPositive (signedIntegral μ₀.weight))
    (hpp : ∀ (q : ℕ) [NeZero q], q.Prime → SlotReflectionPositive (signedIntegral (μp q).weight))
    (hμ₀ : ∀ (a : ∀ i, (ZMod (m₀ i))ˣ) (b : ResidueSpace m₀),
      (∀ i, IsSquare ((a i : ZMod (m₀ i)))) → ∀ F : (Slot → ResidueSpace m₀) → ℝ,
        μ₀.expect (fun z => F (fun v => piAffineEquiv m₀ a b (z v))) = μ₀.expect F)
    (hμp : ∀ (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) (b : ZMod q), IsSquare (a : ZMod q) →
      ∀ F : (Slot → ZMod q) → ℝ,
        (μp q).expect (fun z => F (fun v => affineEquiv a b (z v))) = (μp q).expect F)
    {C : ℝ} (hC : 0 ≤ C)
    (hind : EnergyUpperBoundAt (prefixedFunctional m₀ (J := fun L => ↥(T L)) (fun _ j => (j : ℕ))
      (paperLaw m₀ (J := fun L => ↥(T L)) (fun _ j => (j : ℕ)) μ₀ μp)) C
      (stepScale blockScale M (leastSquare (D0 * ∏ k ∈ E, joinModuli m₀ (tailModuli T L) k)))) :
    diagonalIntegral (signedIntegral
        (paperLaw m₀ (J := fun L => ↥(T L)) (fun _ j => (j : ℕ)) μ₀ μp L).weight)
        (fun x => (squareStepModel (joinModuli m₀ (tailModuli T L)) E z s A (Icc (c + 1) (c + M)) c M
          (leastSquare (D0 * ∏ k ∈ E, joinModuli m₀ (tailModuli T L) k))
          (blockScale * stepScale blockScale M
            (leastSquare (D0 * ∏ k ∈ E, joinModuli m₀ (tailModuli T L) k)))
          (paperCutoff (blockScale * stepScale blockScale M
            (leastSquare (D0 * ∏ k ∈ E, joinModuli m₀ (tailModuli T L) k))))
          ((splitEquiv m₀ (tailModuli T L)).symm x)).re) ≤
      ((leastSquare (D0 * ∏ k ∈ E, joinModuli m₀ (tailModuli T L) k) *
            (blockScale * stepScale blockScale M
              (leastSquare (D0 * ∏ k ∈ E, joinModuli m₀ (tailModuli T L) k))) : ℝ) / M) ^ 72 *
        (C * (stepScale blockScale M
            (leastSquare (D0 * ∏ k ∈ E, joinModuli m₀ (tailModuli T L) k)) : ℝ) ^ (-decay)) *
        (((((D0 * ∏ k ∈ E, joinModuli m₀ (tailModuli T L) k : ℕ) : ℝ) / M) *
            ((A ∩ Icc (c + 1) (c + M)).filter (InFibre (joinModuli m₀ (tailModuli T L)) E z s)).card) /
          ((leastSquare (D0 * ∏ k ∈ E, joinModuli m₀ (tailModuli T L) k) *
            (blockScale * stepScale blockScale M
              (leastSquare (D0 * ∏ k ∈ E, joinModuli m₀ (tailModuli T L) k))) : ℝ) / M)) ^
          densityExponent := by
  set D : ℕ := D0 * ∏ k ∈ E, (joinModuli m₀ (tailModuli T L)) k with hDdef
  set R : ℕ := leastSquare D with hRdef
  set ℓ : ℕ := stepScale blockScale M R with hℓdef
  set n : ℕ := blockScale * ℓ with hndef
  obtain ⟨hR1', hD0R', hER', hcopR'⟩ :=
    leastSquare_step_conditions (joinModuli m₀ (tailModuli T L)) (E := E) hD0 hcop0 hpair
  have hR1 : 1 ≤ R := hR1'
  have hD0R : D0 ∣ R := hD0R'
  have hER : ∀ i ∈ E, joinModuli m₀ (tailModuli T L) i ∣ R := hER'
  have hcopR : ∀ k ∉ E, R.Coprime (joinModuli m₀ (tailModuli T L) k) := hcopR'
  have hDR : D ∣ R := dvd_leastSquare (Nat.mul_ne_zero (by omega)
    (prod_ne_zero_iff.mpr fun k _ => NeZero.ne ((joinModuli m₀ (tailModuli T L)) k)))
  have hK : 1 ≤ blockScale := by norm_num [blockScale]
  have hMR : M ≤ R * n := (stepScale_bounds (M := M) hK hR1).1
  have hcard : (stepResidues (joinModuli m₀ (tailModuli T L)) E z s R c).card * D = R :=
    card_stepResidues (joinModuli m₀ (tailModuli T L)) z hD0 s hcop0 hpair hR1 hDR c
  have hJpos : 0 < (stepResidues (joinModuli m₀ (tailModuli T L)) E z s R c).card := by
    rcases Nat.eq_zero_or_pos (stepResidues (joinModuli m₀ (tailModuli T L)) E z s R c).card with h | h
    · rw [h, zero_mul] at hcard; omega
    · exact h
  have hDpos : (0 : ℝ) < D := by
    have : 0 < D := Nat.pos_of_ne_zero (Nat.mul_ne_zero (by omega)
      (prod_ne_zero_iff.mpr fun k _ => NeZero.ne ((joinModuli m₀ (tailModuli T L)) k)))
    exact_mod_cast this
  have hJ : ((stepResidues (joinModuli m₀ (tailModuli T L)) E z s R c).card : ℝ)⁻¹ = (D : ℝ) / R := by
    have h1 : ((stepResidues (joinModuli m₀ (tailModuli T L)) E z s R c).card : ℝ) * D = R := by exact_mod_cast hcard
    have hR0 : (R : ℝ) ≠ 0 := by exact_mod_cast (show R ≠ 0 by omega)
    rw [eq_div_iff hR0, ← h1]
    field_simp
  -- the model as `λ · ∑_j |J|⁻¹ (h_j ∘ T_j)`
  rw [squareStepModel_re_eq m₀ T E z s A c M R n _ hJ]
  have hrp : SlotReflectionPositive (signedIntegral
      (paperLaw m₀ (J := fun L => ↥(T L)) (fun _ j => (j : ℕ)) μ₀ μp L).weight) :=
    slotReflectionPositive_slotProduct hp₀
      (tensor_slot_reflection_positive _ fun j => hpp _ (hprime j.1 j.2))
  have hinv₀ : ∀ (s₀ : ResidueSpace m₀) (F : (Slot → ResidueSpace m₀) → ℝ),
      μ₀.expect (fun z => F (fun v => z v + s₀)) = μ₀.expect F := by
    intro s₀ F
    have h := hμ₀ (fun _ => 1) s₀ (fun i => ⟨1, by simp⟩) F
    have he : ∀ x : ResidueSpace m₀, piAffineEquiv m₀ (fun _ => 1) s₀ x = x + s₀ := by
      intro x; funext i; simp [piAffineEquiv]
    simp only [he] at h
    exact h
  have hinvp : ∀ (q : ℕ) [NeZero q] (r : ZMod q) (F : (Slot → ZMod q) → ℝ),
      (μp q).expect (fun z => F (fun v => z v + r)) = (μp q).expect F := by
    intro q _ r F
    have h := hμp q 1 r ⟨1, by simp⟩ F
    have he : ∀ x : ZMod q, affineEquiv 1 r x = x + r := by
      intro x; simp [affineEquiv]
    simp only [he] at h
    exact h
  have hroot : R = leastSquareRoot D ^ 2 := leastSquare_eq_root_sq D
  have hr1 : 1 ≤ leastSquareRoot D := by
    rcases Nat.eq_zero_or_pos (leastSquareRoot D) with h | h
    · rw [h] at hroot; simp at hroot; omega
    · exact h
  have hB : 0 ≤ C * (ℓ : ℝ) ^ (-decay) := mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hθd : densityExponent ≤ (Fintype.card Slot : ℝ) := by
    rw [card_slot]; norm_num [densityExponent]
  have hmain := SignedHolder.fibre_energy_le (slot_signedHolder hrp) (stepResidues (joinModuli m₀ (tailModuli T L)) E z s R c)
    (Finset.card_pos.mp hJpos)
    (fun j => fun x => (stepLift (joinModuli m₀ (tailModuli T L)) E (paperCutoff n) (stepChild A (Icc (c + 1) (c + M)) R n c j) n
      ((splitEquiv m₀ (tailModuli T L)).symm x)).re)
    (fun j => fun x => splitEquiv m₀ (tailModuli T L) (stepMap (joinModuli m₀ (tailModuli T L)) R c j
      ((splitEquiv m₀ (tailModuli T L)).symm x)))
    (fun j _ => energy_stepMap_invariant m₀ (J := fun L => ↥(T L)) (fun _ j => (j : ℕ)) μ₀ μp
      hμ₀ hμp L E hroot hcopR c j (paperCutoff n) _ n)
    (lam := (R * n : ℝ) / M) (by positivity) hB
    (le_trans (by norm_num) densityExponent_bounds.1) hθd
    (fun j => density n (stepChild A (Icc (c + 1) (c + M)) R n c j))
    (fun j _ => density_nonneg _ _)
    (fun j _ => fibreScale_child_energy_le m₀ T hT hprime hlarge μ₀ μp hp₀ hpp hinv₀ hinvp hind E
      hA _ hroot hr1 c j)
  -- `(D/R) ∑_j α_j = α_f/λ`
  have hkey : ((stepResidues (joinModuli m₀ (tailModuli T L)) E z s R c).card : ℝ)⁻¹ *
      ∑ j ∈ stepResidues (joinModuli m₀ (tailModuli T L)) E z s R c,
        density n (stepChild A (Icc (c + 1) (c + M)) R n c j) =
      (((D : ℝ) / M) * ((A ∩ Icc (c + 1) (c + M)).filter
        (InFibre (joinModuli m₀ (tailModuli T L)) E z s)).card) / ((R * n : ℝ) / M) := by
    rw [hJ]
    have hdens := stepChild_density (joinModuli m₀ (tailModuli T L)) (E := E) (z := z) (s := s)
      A c hM hR1 hMR hD0R hER
    simp only [density]
    exact hdens
  refine hmain.trans_eq ?_
  rw [card_slot, hkey, hndef]
  push_cast
  ring

end Sarkozy.PaperFrame
