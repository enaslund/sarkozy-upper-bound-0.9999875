module

public import Sarkozy.Structured.FibreMean

/-!
# `prop:record:density-structured` for the paper's inputs

The structured energies of `def:record:structured-energy` with the paper's inputs
`g_v^ω = g^{I_v, D_{0,v}, s_v}` (WP-FI's `Sarkozy.Functional.input`), specialized at
the selected labels by `coordinateFreeze`, and the estimate
`prop:record:density-structured` for them.

Data:

* `m` — the moduli of the coordinates, pairwise coprime;
* `E` — the selected coordinates;
* `μ_𝒮` — the reference law, on the whole group: functions on `X_𝒮` are functions that
  do not depend on the coordinates of `E`;
* `ρ` — the selected measure, with uniform one-slot marginals of `|ρ|`;
* for every slot `v` — a divisor `D_{0,v} ≥ 1` coprime to the moduli and a length
  `M_v ∈ {L, N}`;
* `P` — a law of index vectors `ω`, with interval starts `c_v(ω)`
  (`I_v = Icc (c+1) (c+M_v)`) and residues `s_v(ω)`;
* the set `changed` of changed slots.

`paperInputs` are the inputs. The square-step models `g̃` at the changed slots are WP-FI's
`squareStepModel` with the paper's `R = sq(D₀ D_E)` and `ℓ = ⌈M/(KR)⌉`. The prices are
`ξ_v = (N/M_v) R_v` (`paperPrice`; equal to the paper's `(N/M_v) sq(D_{0,v}) R_E` by
multiplicativity of `sq` on coprime factors, `Sarkozy.Functional.leastSquare_selection`)
and `ᾱ_v = E_P (D_{0,v}/M_v) #{x ∈ A ∩ I_v : x ≡ s_v (mod D_{0,v})}` (`paperMeanDensity`).

`density_structured_paper` gives `|𝔈| ≤ ‖ρ‖ [(1 + u) Π_main Y + C_dc L^{-σ} α]` at a least
normalized counterexample. The hypotheses still open are:

* `hdc` — `lem:record:density-dc`;
* `hrest` — restoration `lem:record:fibre-scale`(c) at the scales `ℓ_v`, proved by WP-FI
  in two-scale product form (`referenceEnergy_stepLift_le_scale`);
* `hinvT` — (R3) for the maps `T_j`. For a product of atom laws it follows from (R3)
  of `hyp:record:reference` (`tensor_expect_stepMapOff`,
  `Sarkozy/Structured/AffineInvariance.lean`);
* `hlamu` — the scale condition `λ_v^{72} ≤ 1 + u`, from `lem:scale-conditions`;
* `hun` — the identity `Z(F_A) = Y` at unchanged slots, which is the definition of `Y` when
  `E = ∅` and `μ_𝒮 = μ_N`.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.Structured

open Sarkozy.Functional Sarkozy.FourierArithmetic

section PaperEnergy

variable {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)]
  {Ω : Type*} [Fintype Ω]

/-- The paper's specialized inputs `g_v^ω(z_v, ·) = g^{I_v, D_{0,v}, s_v}(z_v, ·)`. -/
noncomputable def paperInputs (E : Finset J) (Q : ℝ) (A : Finset ℤ) (D0 M : Slot → ℕ)
    (c : Ω → Slot → ℤ) (s : ∀ (_ : Ω) (v : Slot), ZMod (D0 v)) :
    Ω → Slot → ResidueSpace m → ResidueSpace m → ℝ :=
  fun ω v x y =>
    (input m Q (Icc (c ω v + 1) (c ω v + M v)) (D0 v) (s ω v) A (coordinateFreeze m E x y)).re

/-- The slot price `ξ_v = (N/M_v) R_v`, `R_v = sq(D_{0,v} D_E)`, `N = K L`. -/
noncomputable def paperPrice (E : Finset J) (D0 M : Slot → ℕ) (L : ℕ) (v : Slot) : ℝ :=
  (((blockScale * L : ℕ) : ℝ) / M v) * (stepR m E (D0 v) : ℕ)

/-- The mean density `ᾱ_v = E_P (D_{0,v}/M_v) #{x ∈ A ∩ I_v : x ≡ s_v (mod D_{0,v})}`. -/
noncomputable def paperMeanDensity (P : FiniteLaw Ω) (A : Finset ℤ) (D0 M : Slot → ℕ)
    (c : Ω → Slot → ℤ) (s : ∀ (_ : Ω) (v : Slot), ZMod (D0 v)) (v : Slot) : ℝ :=
  P.expect fun ω => (D0 v : ℝ) / M v *
    ((A ∩ Icc (c ω v + 1) (c ω v + M v)).filter fun x : ℤ => (x : ZMod (D0 v)) = s ω v).card

/-- **`prop:record:density-structured` for the paper's inputs.** -/
theorem density_structured_paper (hpair : Pairwise fun i j => (m i).Coprime (m j))
    {Yf : ℕ → Finset ℤ → ℝ} {a θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hcex : IsLeastCounterexample Yf a θ C0 L A) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (ha : 0 ≤ a)
    (hC0 : 0 ≤ C0) (hL : 2 ≤ L) (hY0 : Yf L ∅ ≤ 0)
    (μS : FiniteLaw (Slot → ResidueSpace m))
    (hμS : SlotReflectionPositive (signedIntegral μS.weight)) (E : Finset J)
    (P : FiniteLaw Ω) (ρ : (Slot → ResidueSpace m) → ℝ) (hunif : selectedMarginalsUniform ρ)
    (D0 : Slot → ℕ) (hD0 : ∀ v, 1 ≤ D0 v) (hcop0 : ∀ v k, (D0 v).Coprime (m k))
    (M : Slot → ℕ) (hM : ∀ v, M v = blockScale * L ∨ M v = L)
    (c : Ω → Slot → ℤ) (s : ∀ (_ : Ω) (v : Slot), ZMod (D0 v))
    (changed : Slot → Prop) [DecidablePred changed]
    (hchg : ∀ v, changed v → ¬(D0 v * ∏ j ∈ E, m j = 1 ∧ M v = blockScale * L))
    (Q : ℝ) (Q' : Slot → ℝ) (gt : Ω → Slot → ResidueSpace m → ResidueSpace m → ℝ)
    (hgt : ∀ ω v x, changed v → gt ω v x = fun y =>
      (squareStepModel m E x (s ω v) A (Icc (c ω v + 1) (c ω v + M v)) (c ω v) (M v)
        (stepR m E (D0 v)) (blockScale * stepEll m E (D0 v) (M v)) (Q' v) y).re)
    (hun : ∀ v, ¬changed v → ∀ ω x, referenceEnergy μS (gt ω v x) ≤ Yf L A)
    {u Cdc σ : ℝ} (hu : 0 ≤ u)
    (hrest : ∀ v, changed v → ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll m E (D0 v) (M v) : ℕ) : ℤ) →
      referenceEnergy μS (child m E (Q' v) B (blockScale * stepEll m E (D0 v) (M v))) ≤
        Yf (stepEll m E (D0 v) (M v)) B)
    (hinvT : ∀ v, changed v → ∀ ω (j : ℤ) (F : (Slot → ResidueSpace m) → ℝ),
      μS.expect (fun w => F (fun v' => stepMapOff m E (stepR m E (D0 v)) (c ω v) j (w v'))) =
        μS.expect F)
    (hlamu : ∀ v, changed v →
      (((stepR m E (D0 v) : ℕ) : ℝ) * ((blockScale * stepEll m E (D0 v) (M v) : ℕ) : ℝ) /
        M v) ^ 72 ≤ 1 + u)
    (hdc : |structuredEnergy μS P ρ (paperInputs m E Q A D0 M c s) -
        structuredEnergy μS P ρ gt| ≤
      Cdc * totalVariation ρ * (L : ℝ) ^ (-σ) * density (blockScale * L) A) :
    |structuredEnergy μS P ρ (paperInputs m E Q A D0 M c s)| ≤
      totalVariation ρ * ((1 + u) *
        mainPrice (paperPrice m E D0 M L) (paperMeanDensity P A D0 M c s) changed a θ
          (density (blockScale * L) A) * Yf L A +
        Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  have hM1 : ∀ v, 1 ≤ M v := by
    intro v
    rcases hM v with h | h
    · rw [h]; exact Nat.mul_pos (by norm_num [blockScale]) (by omega)
    · rw [h]; omega
  have hA := hcex.admissible
  have hξ : ∀ v, 1 ≤ paperPrice m E D0 M L v := by
    intro v
    unfold paperPrice
    have hR1 : 1 ≤ stepR m E (D0 v) := leastSquare_pos _
    have hR1' : (1 : ℝ) ≤ ((stepR m E (D0 v) : ℕ) : ℝ) := by exact_mod_cast hR1
    have hNM : (1 : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) / M v := by
      have hMpos : (0 : ℝ) < M v := by exact_mod_cast hM1 v
      rw [le_div_iff₀ hMpos, one_mul]
      rcases hM v with h | h
      · rw [h]
      · rw [h]
        exact_mod_cast Nat.le_mul_of_pos_left L (by norm_num [blockScale])
    nlinarith
  have hαbar : ∀ v, 0 ≤ paperMeanDensity P A D0 M c s v := by
    intro v
    unfold paperMeanDensity
    apply P.expect_nonneg
    intro ω
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hαf : ∀ ω v x, 0 ≤ fibreDensity m E x (s ω v) A (c ω v) (M v) := by
    intro ω v x
    unfold fibreDensity
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hch : ∀ v, changed v → ∀ ω x, referenceEnergy μS (gt ω v x) ≤
      (1 + u) * C0 * (L : ℝ) ^ (-a) * paperPrice m E D0 M L v ^ a *
        fibreDensity m E x (s ω v) A (c ω v) (M v) ^ θ := by
    intro v hv ω x
    rw [hgt ω v x hv]
    have h := changed_slot_bound_paper m μS hμS E x (hD0 v) (s ω v) (hcop0 v) hpair A hA.2
      (c ω v) (hM1 v) hL (hM v) (hchg v hv) (Q' v) ha hθ.le (by linarith) hC0
      (fun ℓ hℓ hℓL => hcex.2.2 ℓ hℓ hℓL) (hrest v hv) (fun j => hinvT v hv ω j) (hlamu v hv)
    unfold paperPrice
    exact h
  have hmean : ∀ hρ : 0 < totalVariation ρ, ∀ v, changed v →
      (P.product (variationLaw ρ hρ)).expect
        (fun p => fibreDensity m E (p.2 v) (s p.1 v) A (c p.1 v) (M v)) =
      paperMeanDensity P A D0 M c s v := by
    intro hρ v _
    rw [FiniteLaw.expect_product]
    unfold paperMeanDensity
    apply P.expect_congr
    intro ω
    rw [expect_variationLaw_slot ρ hρ hunif v
      (fun x => fibreDensity m E x (s ω v) A (c ω v) (M v)), uniform_fibreDensity]
  exact density_structured_counterexample hcex hθ hθ1 ha hC0 (by omega) hY0 μS hμS P ρ
    (paperInputs m E Q A D0 M c s) gt changed hu (paperPrice m E D0 M L)
    (paperMeanDensity P A D0 M c s) hξ hαbar hun
    (fun ω v x => fibreDensity m E x (s ω v) A (c ω v) (M v)) hαf hch hmean hdc

end PaperEnergy

end Sarkozy.Structured
