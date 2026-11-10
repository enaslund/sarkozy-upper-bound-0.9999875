module

public import Sarkozy.DensityDC.Paper

/-!
# The averaged moments of `lem:record:density-dc`

Step 2 of the proof of `lem:record:density-dc` averages the moments of the specialized
inputs and models over `ω ∼ P` and `z ∼ |ρ|/‖ρ‖`.

* For the inputs: "under `|ρ|/‖ρ‖` each `z_w` is uniform and independent of `ω`. Hence by
  Fubini, `E ‖g_w^ω(z_w,·)‖_{2r}^{2r} = E_ω ‖g_w^ω‖_{L^{2r}(G_N)}^{2r}`"
  (`expect_variation_freeze`, from `expect_freeze_uniform`). The specialization at a
  uniform label has the moments of the function on the whole group.
* For the square-step models: a per-sample bound `E_y |g̃(z,·)|^{2r} ≤ K α_f(z)`
  (`lem:record:fibre-scale`(e)) averages to `K ᾱ_v` (`expect_model_moment_le`), by
  `E α_f = ᾱ` (`Sarkozy.Structured.uniform_fibreDensity`).
* `moment_two_sub_le`: `‖g - g̃‖₂² ≤ 2 ‖g‖₂² + 2 ‖g̃‖₂²`.

`density_dc_lift_moments` is `density_dc_paper` with the averaged moments replaced by:
* `hlift2`, `hlift142`: per-index moment bounds of the inputs on the whole group
  (`lem:record:lift-moments`(c));
* `hmod2`, `hmod142`: per-sample bounds of the models (`lem:record:fibre-scale`(e)).
-/

@[expose] public section

open Finset Complex
open scoped BigOperators ComplexConjugate

namespace Sarkozy.DensityDC

open Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.Mixing

variable {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)]

/-! ## Fubini for the specialization -/

omit [Fintype J] [∀ j, NeZero (m j)] in
/-- `(z, y) ↦ (freeze(z, y), freeze(y, z))` exchanges the coordinates of `E`; it is an
involution. -/
theorem freeze_swap_involutive (E : Finset J) :
    Function.Involutive (fun p : ResidueSpace m × ResidueSpace m =>
      (coordinateFreeze m E p.1 p.2, coordinateFreeze m E p.2 p.1)) := by
  intro p
  ext k
  · unfold coordinateFreeze
    by_cases hk : k ∈ E
    · simp [hk]
    · simp [hk]
  · unfold coordinateFreeze
    by_cases hk : k ∈ E
    · simp [hk]
    · simp [hk]

/-- **Fubini for the specialization**: for independent uniform `z` and `y`,
`freeze(z, y)` is uniform on the group. -/
theorem expect_freeze_uniform (E : Finset J) (G : ResidueSpace m → ℝ) :
    (FiniteLaw.uniform (ResidueSpace m)).expect (fun z =>
        (FiniteLaw.uniform (ResidueSpace m)).expect (fun y => G (coordinateFreeze m E z y))) =
      (FiniteLaw.uniform (ResidueSpace m)).expect G := by
  set U := FiniteLaw.uniform (ResidueSpace m)
  have h1 : U.expect (fun z => U.expect (fun y => G (coordinateFreeze m E z y))) =
      (U.product U).expect (fun p => G (coordinateFreeze m E p.1 p.2)) := by
    rw [FiniteLaw.expect_product]
  have h2 : U.expect G = (U.product U).expect (fun p => G p.1) := by
    rw [FiniteLaw.expect_product]
    simp only [FiniteLaw.expect_const]
  rw [h1, h2]
  unfold FiniteLaw.expect FiniteLaw.product
  simp only
  set φ := (freeze_swap_involutive m E).toPerm _
  apply Fintype.sum_equiv φ
  intro p
  change U.weight p.1 * U.weight p.2 * G (coordinateFreeze m E p.1 p.2) =
    U.weight (coordinateFreeze m E p.1 p.2) * U.weight (coordinateFreeze m E p.2 p.1) *
      G (coordinateFreeze m E p.1 p.2)
  rfl

/-- **The averaged moments of the specialized inputs** are the whole-group moments: under
uniform one-slot marginals of `|ρ|`,
`E_{(ω,z)} ‖F_ω(freeze(z_w, ·))‖_r^r = E_ω ‖F_ω‖_{L^r(G)}^r`. -/
theorem expect_variation_freeze {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
    (ρ : (Slot → ResidueSpace m) → ℝ) (hρ : 0 < totalVariation ρ)
    (hunif : selectedMarginalsUniform ρ) (E : Finset J) (w : Slot)
    (F : Ω → ResidueSpace m → ℝ) (r : ℝ) :
    (P.product (variationLaw ρ hρ)).expect (fun p =>
        (FiniteLaw.uniform (ResidueSpace m)).moment r
          (fun y => F p.1 (coordinateFreeze m E (p.2 w) y))) =
      P.expect (fun ω => (FiniteLaw.uniform (ResidueSpace m)).moment r (F ω)) := by
  rw [FiniteLaw.expect_product]
  apply P.expect_congr
  intro ω
  rw [expect_variationLaw_slot ρ hρ hunif w (fun x =>
    (FiniteLaw.uniform (ResidueSpace m)).moment r (fun y => F ω (coordinateFreeze m E x y)))]
  unfold FiniteLaw.moment
  exact expect_freeze_uniform m E (fun x => |F ω x| ^ r)

/-- **The averaged moments of the square-step models**: a per-sample bound
`‖g̃(x,·)‖_r^r ≤ K α_f(x)` averages to `K ᾱ_v`. -/
theorem expect_model_moment_le {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
    (ρ : (Slot → ResidueSpace m) → ℝ) (hρ : 0 < totalVariation ρ)
    (hunif : selectedMarginalsUniform ρ) (E : Finset J) (A : Finset ℤ) (D0 M : Slot → ℕ)
    (c : Ω → Slot → ℤ) (s : ∀ (_ : Ω) (v : Slot), ZMod (D0 v)) (v : Slot)
    (G : Ω → ResidueSpace m → ResidueSpace m → ℝ) (r : ℝ) {K : ℝ}
    (hG : ∀ ω x, (FiniteLaw.uniform (ResidueSpace m)).moment r (G ω x) ≤
      K * fibreDensity m E x (s ω v) A (c ω v) (M v)) :
    (P.product (variationLaw ρ hρ)).expect (fun p =>
        (FiniteLaw.uniform (ResidueSpace m)).moment r (G p.1 (p.2 v))) ≤
      K * paperMeanDensity P A D0 M c s v := by
  rw [FiniteLaw.expect_product]
  unfold paperMeanDensity
  rw [← P.expect_const_mul]
  apply P.expect_mono
  intro ω
  calc (variationLaw ρ hρ).expect (fun z =>
        (FiniteLaw.uniform (ResidueSpace m)).moment r (G ω (z v)))
      ≤ (variationLaw ρ hρ).expect (fun z =>
          K * fibreDensity m E (z v) (s ω v) A (c ω v) (M v)) :=
        (variationLaw ρ hρ).expect_mono fun z => hG ω (z v)
    _ = K * ((D0 v : ℝ) / M v *
          ((A ∩ Icc (c ω v + 1) (c ω v + M v)).filter fun x : ℤ =>
            (x : ZMod (D0 v)) = s ω v).card) := by
        rw [(variationLaw ρ hρ).expect_const_mul,
          expect_variationLaw_slot ρ hρ hunif v
            (fun x => fibreDensity m E x (s ω v) A (c ω v) (M v)), uniform_fibreDensity]

/-- `‖f - g‖₂² ≤ 2 ‖f‖₂² + 2 ‖g‖₂²`. -/
theorem moment_two_sub_le {X : Type*} [Fintype X] (U : FiniteLaw X) (f g : X → ℝ) :
    U.moment 2 (fun y => f y - g y) ≤ 2 * U.moment 2 f + 2 * U.moment 2 g := by
  unfold FiniteLaw.moment
  rw [← U.expect_const_mul, ← U.expect_const_mul, ← U.expect_add]
  apply U.expect_mono
  intro y
  have h2 : ∀ t : ℝ, |t| ^ (2 : ℝ) = t ^ 2 := by
    intro t
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  rw [h2, h2, h2]
  nlinarith [sq_nonneg (f y + g y)]

/-! ## `lem:record:density-dc` from the cited moment bounds -/

section Lift

variable {Ω : Type*} [Fintype Ω]

/-- **`lem:record:density-dc` from the cited moment bounds.** This is `density_dc_paper`
with the averaged moments derived from:
* `hlift2`, `hlift142`: the whole-group moments of the inputs `g^{I,D₀,s}`, per index
  (`lem:record:lift-moments`(c));
* `hmod2`, `hmod142`: the per-sample moments of the square-step models,
  `‖g̃(x,·)‖_r^r ≤ K_r α_f(x)` (`lem:record:fibre-scale`(e));
* `hᾱ`: `ᾱ_v ≤ ᾱ_max` at the changed slots.

The result is
`|𝔈 - 𝔈̃| ≤ ‖ρ‖ |C| (C'/H)^γ (2K_in,2 + 2K_2 ᾱ_max)^{1/2} (max(K_in,142, K_142 ᾱ_max))^{71/142}`. -/
theorem density_dc_lift_moments (hpair : Pairwise fun i j => (m i).Coprime (m j))
    (μb : ∀ b, FiniteLaw (Slot → ZMod (m b))) (hR3 : SquareAffineInvariant m μb)
    (T : Finset J) (hprime : ∀ j ∈ T, (m j).Prime) {γ : ℝ} (hγ : 0 ≤ γ)
    (hmix : ∀ j ∈ T, ∀ v, IsGammaMixing (m j) γ (μb j) {v}) {C' : ℕ} (hC' : 0 < C')
    (hdiv : ∀ a : ResidueSpace m, (∏ j ∈ univ.filter (· ∉ T), addOrderOf (a j)) ∣ C')
    (E : Finset J) (P : FiniteLaw Ω) (ρ : (Slot → ResidueSpace m) → ℝ)
    (hunif : selectedMarginalsUniform ρ) {A : Finset ℤ}
    (D0 : Slot → ℕ) (hD0 : ∀ v, 1 ≤ D0 v) (hcop0 : ∀ v k, (D0 v).Coprime (m k))
    (M : Slot → ℕ) (hM1 : ∀ v, 1 ≤ M v)
    (c : Ω → Slot → ℤ) (s : ∀ (_ : Ω) (v : Slot), ZMod (D0 v))
    (changed : Slot → Prop) [DecidablePred changed]
    (Q : ℝ) (Q' : Slot → ℝ) (gt : Ω → Slot → ResidueSpace m → ResidueSpace m → ℝ)
    (hgt : ∀ ω v x, changed v → gt ω v x = fun y =>
      (squareStepModel m E x (s ω v) A (Icc (c ω v + 1) (c ω v + M v)) (c ω v) (M v)
        (stepR m E (D0 v)) (blockScale * stepEll m E (D0 v) (M v)) (Q' v) y).re)
    (hgu : ∀ v, ¬changed v → ∀ ω x, gt ω v x = paperInputs m E Q A D0 M c s ω v x)
    {H : ℝ} (hH : 0 < H) (hHQ' : ∀ v, changed v → H ≤ Q' v)
    (hHQ : H * (∏ j ∈ E, m j : ℕ) ≤ Q)
    {Kin2 Kin142 K2 K142 αmax : ℝ} (hK2 : 0 ≤ K2) (hK142 : 0 ≤ K142)
    (hlift2 : ∀ ω v, (FiniteLaw.uniform (ResidueSpace m)).moment 2
      (fun x => (input m Q (Icc (c ω v + 1) (c ω v + M v)) (D0 v) (s ω v) A x).re) ≤ Kin2)
    (hlift142 : ∀ ω v, (FiniteLaw.uniform (ResidueSpace m)).moment 142
      (fun x => (input m Q (Icc (c ω v + 1) (c ω v + M v)) (D0 v) (s ω v) A x).re) ≤ Kin142)
    (hmod2 : ∀ ω v x, changed v → (FiniteLaw.uniform (ResidueSpace m)).moment 2 (gt ω v x) ≤
      K2 * fibreDensity m E x (s ω v) A (c ω v) (M v))
    (hmod142 : ∀ ω v x, changed v →
      (FiniteLaw.uniform (ResidueSpace m)).moment 142 (gt ω v x) ≤
        K142 * fibreDensity m E x (s ω v) A (c ω v) (M v))
    (hᾱ : ∀ v, changed v → paperMeanDensity P A D0 M c s v ≤ αmax) (hαmax : 0 ≤ αmax) :
    |structuredEnergy (FiniteLaw.tensor μb) P ρ (paperInputs m E Q A D0 M c s) -
        structuredEnergy (FiniteLaw.tensor μb) P ρ gt| ≤
      totalVariation ρ * (((univ.filter changed).card : ℝ) *
        (((C' : ℝ) / H) ^ γ * ((2 * Kin2 + 2 * (K2 * αmax)) ^ ((1 : ℝ) / 2) *
          (max Kin142 (K142 * αmax)) ^ ((71 : ℝ) / 142)))) := by
  set U := FiniteLaw.uniform (ResidueSpace m) with hU
  have hne : Nonempty Ω := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := P.total
    simp at this
  obtain ⟨ω0⟩ := hne
  have hKin2 : 0 ≤ Kin2 := (U.moment_nonneg _ _).trans (hlift2 ω0 (0, 0, 0))
  have hKin142 : 0 ≤ Kin142 := (U.moment_nonneg _ _).trans (hlift142 ω0 (0, 0, 0))
  -- the inputs are specializations of whole-group functions
  set F : Slot → Ω → ResidueSpace m → ℝ := fun w ω x =>
    (input m Q (Icc (c ω w + 1) (c ω w + M w)) (D0 w) (s ω w) A x).re with hFdef
  have hin : ∀ (hρ : 0 < totalVariation ρ) (w : Slot) (r : ℝ),
      (P.product (variationLaw ρ hρ)).expect (fun p =>
        U.moment r (paperInputs m E Q A D0 M c s p.1 w (p.2 w))) =
        P.expect (fun ω => U.moment r (F w ω)) := by
    intro hρ w r
    exact expect_variation_freeze m P ρ hρ hunif E w (F w) r
  apply density_dc_paper m hpair μb hR3 T hprime hγ hmix hC' hdiv E P ρ D0 hD0 hcop0 M hM1 c s
    changed Q Q' gt hgt hgu hH hHQ' hHQ (by positivity) (le_max_of_le_left hKin142)
  · -- the second moments of `g_v - g̃_v`
    intro hρ v hv
    have hg : (P.product (variationLaw ρ hρ)).expect (fun p =>
        U.moment 2 (paperInputs m E Q A D0 M c s p.1 v (p.2 v))) ≤ Kin2 := by
      rw [hin hρ v 2]
      exact P.expect_le_const fun ω => hlift2 ω v
    have hgt2 : (P.product (variationLaw ρ hρ)).expect (fun p =>
        U.moment 2 (gt p.1 v (p.2 v))) ≤ K2 * αmax :=
      (expect_model_moment_le m P ρ hρ hunif E A D0 M c s v (fun ω x => gt ω v x) 2
        (fun ω x => hmod2 ω v x hv)).trans (mul_le_mul_of_nonneg_left (hᾱ v hv) hK2)
    calc (P.product (variationLaw ρ hρ)).expect (fun p => U.moment 2
          (fun y => paperInputs m E Q A D0 M c s p.1 v (p.2 v) y - gt p.1 v (p.2 v) y))
        ≤ (P.product (variationLaw ρ hρ)).expect (fun p =>
            2 * U.moment 2 (paperInputs m E Q A D0 M c s p.1 v (p.2 v)) +
              2 * U.moment 2 (gt p.1 v (p.2 v))) :=
          (P.product (variationLaw ρ hρ)).expect_mono fun p => moment_two_sub_le U _ _
      _ = 2 * (P.product (variationLaw ρ hρ)).expect (fun p =>
            U.moment 2 (paperInputs m E Q A D0 M c s p.1 v (p.2 v))) +
          2 * (P.product (variationLaw ρ hρ)).expect (fun p => U.moment 2 (gt p.1 v (p.2 v))) := by
          rw [FiniteLaw.expect_add, FiniteLaw.expect_const_mul, FiniteLaw.expect_const_mul]
      _ ≤ 2 * Kin2 + 2 * (K2 * αmax) := by linarith
  · -- the 142-th moments of the inputs
    intro hρ w
    rw [hin hρ w 142]
    exact (P.expect_le_const fun ω => hlift142 ω w).trans (le_max_left _ _)
  · -- the 142-th moments of the models
    intro hρ w
    by_cases hw : changed w
    · refine (expect_model_moment_le m P ρ hρ hunif E A D0 M c s w (fun ω x => gt ω w x) 142
        (fun ω x => hmod142 ω w x hw)).trans ?_
      exact (mul_le_mul_of_nonneg_left (hᾱ w hw) hK142).trans (le_max_right _ _)
    · have hgw : ∀ p : Ω × (Slot → ResidueSpace m),
          U.moment 142 (gt p.1 w (p.2 w)) =
            U.moment 142 (paperInputs m E Q A D0 M c s p.1 w (p.2 w)) := by
        intro p
        rw [hgu w hw p.1 (p.2 w)]
      rw [(P.product (variationLaw ρ hρ)).expect_congr hgw, hin hρ w 142]
      exact (P.expect_le_const fun ω => hlift142 ω w).trans (le_max_left _ _)

end Lift

end Sarkozy.DensityDC
