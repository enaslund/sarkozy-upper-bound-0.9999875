module

public import Sarkozy.DensityDC.Conductor
public import Sarkozy.Structured.AffineInvariance

/-!
# `lem:record:density-dc` for the paper's structured energies

`lem:record:density-dc` (`paper/sections/08_scale_comparison.tex`): for a structured energy
at `(L, A)` with the paper's inputs `g_v^ω = g^{I_v,D_{0,v},s_v}`, and `g̃` the square-step
models at the changed slots (`g̃ = g` at the unchanged slots),
`|𝔈 - 𝔈̃| ≤ C_dc ‖ρ‖ N^{-γβ/2+72δ} α ≤ C_dc ‖ρ‖ L^{-σ} α`.

The reference law is `μ_N = ⊗_b μ_b`, with the coordinates of the group as atoms (the
whole-group representation of `Sarkozy/Structured/PaperEnergy.lean`).

* `uniformSlot_of_squareAffine`: (R3) gives uniform one-slot marginals.
* `density_dc_paper`: Steps 1 and 2 of the proof. Telescoping (`Telescoping.lean`),
  `lem:record:prefix-conductor` with `lem:record:fibre-scale`(b) for every telescoping
  term (`Conductor.lean`), and Hölder with exponents `2` and `142` (`Averaged.lean`) give
  `|𝔈 - 𝔈̃| ≤ ‖ρ‖ |C| (C'/H)^γ B₂^{1/2} B^{71/142}`, where `B₂` and `B` bound the averaged
  moments.
* `dc_constant_le`: if `B₂ ≤ c₂ N^ε α`, `B ≤ c₁ N^ε α` (the lift moments, with the paper's
  `N^ε` factors), `H = N^{1/40}` and `ε - γ/40 ≤ -σ` ((S1)), then
  `72 (C'/H)^γ B₂^{1/2} B^{71/142} ≤ C_dc L^{-σ} α` with `C_dc = 72 C'^γ c₂^{1/2} c₁^{71/142}`.
* `density_structured_dc`: `prop:record:density-structured` for the paper's inputs, with
  `hdc` derived. Its remaining hypotheses are those of `density_structured_reference`
  except `hdc`, plus:
  - (R4) on the tail coordinates;
  - the prefix conductor bound `C' = Q_pre`;
  - `H ≤ n_v^β`, `H D_E ≤ Q` (`lem:scale-conditions`);
  - the averaged moment bounds of `lem:record:lift-moments`(c) and
    `lem:record:fibre-scale`(e) in the form `B₂ ≤ c₂ N^ε α`, `B ≤ c₁ N^ε α`;
  - (S1).
-/

@[expose] public section

open Finset Complex
open scoped BigOperators ComplexConjugate

namespace Sarkozy.DensityDC

open Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.Mixing

/-! ## (R3) gives uniform marginals -/

/-- (R3) with `r = 1` (translation invariance at all slots simultaneously) gives uniform
one-slot marginals. -/
theorem uniformSlot_of_translate {n : ℕ} [NeZero n] (μ : FiniteLaw (Slot → ZMod n))
    (h : ∀ (t : ZMod n) (F : (Slot → ZMod n) → ℝ),
      μ.expect (fun w => F (fun v => w v + t)) = μ.expect F) (w0 : Slot) :
    UniformSlot μ w0 := by
  intro φ
  have h1 : ∀ t : ZMod n, μ.expect (fun z => φ (z w0 + t)) = μ.expect (fun z => φ (z w0)) :=
    fun t => h t (fun z => φ (z w0))
  have hn : (Fintype.card (ZMod n) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h2 : μ.expect (fun z => φ (z w0)) =
      μ.expect (fun z => (∑ t : ZMod n, φ (z w0 + t)) / (Fintype.card (ZMod n) : ℝ)) := by
    have hsum : ∑ t : ZMod n, μ.expect (fun z => φ (z w0 + t)) =
        (Fintype.card (ZMod n) : ℝ) * μ.expect (fun z => φ (z w0)) := by
      simp_rw [h1]
      rw [sum_const, card_univ, nsmul_eq_mul]
    have hlin : μ.expect (fun z => (∑ t : ZMod n, φ (z w0 + t)) / (Fintype.card (ZMod n) : ℝ)) =
        (∑ t : ZMod n, μ.expect (fun z => φ (z w0 + t))) / (Fintype.card (ZMod n) : ℝ) := by
      unfold FiniteLaw.expect
      rw [sum_div]
      simp_rw [mul_div_assoc', Finset.mul_sum, sum_div]
      exact Finset.sum_comm
    rw [hlin, hsum]
    field_simp
  rw [h2, FiniteLaw.expect_uniform]
  have h3 : ∀ z : Slot → ZMod n, (∑ t : ZMod n, φ (z w0 + t)) = ∑ u : ZMod n, φ u := by
    intro z
    exact Fintype.sum_equiv (Equiv.addLeft (z w0)) _ _ (fun t => rfl)
  simp_rw [h3]
  exact μ.expect_const _

/-- **(R3) gives uniform one-slot marginals** (`hyp:record:reference`(R3): "in particular
every one-slot marginal of `μ_B` is `Unif(X_B)`"). -/
theorem uniformSlot_of_squareAffine {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ)
    [∀ j, NeZero (m j)] (μb : ∀ b, FiniteLaw (Slot → ZMod (m b)))
    (hR3 : SquareAffineInvariant m μb) (b : J) (w0 : Slot) : UniformSlot (μb b) w0 := by
  apply uniformSlot_of_translate
  intro t F
  have h := hR3 b 1 t isUnit_one ⟨1, (mul_one 1).symm⟩ F
  simpa only [one_mul] using h

/-! ## Steps 1 and 2 for the paper's inputs -/

section Paper

variable {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)]
  {Ω : Type*} [Fintype Ω]

/-- **`lem:record:density-dc`, Steps 1 and 2, for the paper's inputs.** Assume:
* the reference law is `μ_N = ⊗_b μ_b` with (R3);
* the tail coordinates `T` are primes with (R4);
* `C'` is divisible by the conductor of every prefix character;
* `H ≤ Q'_v` and `H D_E ≤ Q` (`lem:record:fibre-scale`(b));
* the averaged moments of `g_v - g̃_v` (changed slots) and of `g_w`, `g̃_w` are at most
  `B₂` and `B`.

Then `|𝔈 - 𝔈̃| ≤ ‖ρ‖ |C| (C'/H)^γ B₂^{1/2} B^{71/142}`, `C` the set of changed slots. -/
theorem density_dc_paper (hpair : Pairwise fun i j => (m i).Coprime (m j))
    (μb : ∀ b, FiniteLaw (Slot → ZMod (m b))) (hR3 : SquareAffineInvariant m μb)
    (T : Finset J) (hprime : ∀ j ∈ T, (m j).Prime) {γ : ℝ} (hγ : 0 ≤ γ)
    (hmix : ∀ j ∈ T, ∀ v, IsGammaMixing (m j) γ (μb j) {v}) {C' : ℕ} (hC' : 0 < C')
    (hdiv : ∀ a : ResidueSpace m, (∏ j ∈ univ.filter (· ∉ T), addOrderOf (a j)) ∣ C')
    (E : Finset J) (P : FiniteLaw Ω) (ρ : (Slot → ResidueSpace m) → ℝ) {A : Finset ℤ}
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
    (hHQ : H * (∏ j ∈ E, m j : ℕ) ≤ Q) {B2 B : ℝ} (hB2 : 0 ≤ B2) (hB : 0 ≤ B)
    (hm2 : ∀ hρ : 0 < totalVariation ρ, ∀ v, changed v →
      (P.product (variationLaw ρ hρ)).expect (fun p =>
        (FiniteLaw.uniform (ResidueSpace m)).moment 2
          (fun y => paperInputs m E Q A D0 M c s p.1 v (p.2 v) y - gt p.1 v (p.2 v) y)) ≤ B2)
    (hmg : ∀ hρ : 0 < totalVariation ρ, ∀ w,
      (P.product (variationLaw ρ hρ)).expect (fun p =>
        (FiniteLaw.uniform (ResidueSpace m)).moment 142
          (paperInputs m E Q A D0 M c s p.1 w (p.2 w))) ≤ B)
    (hmgt : ∀ hρ : 0 < totalVariation ρ, ∀ w,
      (P.product (variationLaw ρ hρ)).expect (fun p =>
        (FiniteLaw.uniform (ResidueSpace m)).moment 142 (gt p.1 w (p.2 w))) ≤ B) :
    |structuredEnergy (FiniteLaw.tensor μb) P ρ (paperInputs m E Q A D0 M c s) -
        structuredEnergy (FiniteLaw.tensor μb) P ρ gt| ≤
      totalVariation ρ * (((univ.filter changed).card : ℝ) *
        (((C' : ℝ) / H) ^ γ * (B2 ^ ((1 : ℝ) / 2) * B ^ ((71 : ℝ) / 142)))) := by
  have hunif : ∀ j w, UniformSlot (μb j) w := uniformSlot_of_squareAffine m μb hR3
  apply abs_structuredEnergy_sub_le_of_conductor (FiniteLaw.tensor μb)
    (FiniteLaw.uniform (ResidueSpace m)) P ρ _ gt (univ.filter changed) _
    (Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) hH.le) _) hB2 hB _ _ hmg hmgt
  · -- outside the changed slots the inputs agree
    intro w hw ω x
    rw [hgu w (fun h => hw (mem_filter.mpr ⟨mem_univ w, h⟩)) ω x]
  · -- every telescoping term: `lem:record:prefix-conductor` and `lem:record:fibre-scale`(b)
    intro ω z v hv Tv _
    have hvc : changed v := (mem_filter.mp hv).2
    apply abs_multilinear_le_prefix_conductor m μb hunif T hprime hγ hmix hC' hdiv hH
    intro a ha
    rw [hybrid_self]
    have h := groupCoeff_input_sub_model_eq_zero m hpair E (z v) (hD0 v) (s ω v) (hcop0 v) A
      (c ω v) (hM1 v) (K := blockScale) (by norm_num [blockScale]) (Q := Q) (Q' := Q' v)
      (hHQ' v hvc) hHQ a ha
    rw [hgt ω v (z v) hvc]
    convert h using 2
    funext y
    rfl
  · intro hρ v hv
    exact hm2 hρ v (mem_filter.mp hv).2

/-! ## The constant -/

/-- **The constant of `lem:record:density-dc`**. If `B₂ ≤ c₂ N^ε α`, `B ≤ c₁ N^ε α`,
`H = N^{1/40}` and `ε - γ/40 ≤ -σ` ((S1), the paper's `-γβ/2 + 72δ ≤ -σ`), then
`72 (C'/H)^γ B₂^{1/2} B^{71/142} ≤ C_dc L^{-σ} α` with `C_dc = 72 C'^γ c₂^{1/2} c₁^{71/142}`,
for `N ≥ L ≥ 1`. -/
theorem dc_constant_le {C' c2 c1 B2 B N L α γ ε σ : ℝ} (hC' : 0 ≤ C') (hc2 : 0 ≤ c2)
    (hc1 : 0 ≤ c1) (hB2 : 0 ≤ B2) (hB : 0 ≤ B) (hα : 0 ≤ α) (hL : 1 ≤ L) (hN : L ≤ N)
    (hσ : 0 ≤ σ) (hS1 : ε - γ / 40 ≤ -σ)
    (hB2le : B2 ≤ c2 * N ^ ε * α) (hBle : B ≤ c1 * N ^ ε * α) :
    72 * ((C' / N ^ ((1 : ℝ) / 40)) ^ γ * (B2 ^ ((1 : ℝ) / 2) * B ^ ((71 : ℝ) / 142))) ≤
      72 * C' ^ γ * c2 ^ ((1 : ℝ) / 2) * c1 ^ ((71 : ℝ) / 142) * L ^ (-σ) * α := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one (hL.trans hN)
  have hNe : 0 ≤ N ^ ε := Real.rpow_nonneg hN0.le _
  -- the moments
  have h1 : B2 ^ ((1 : ℝ) / 2) ≤ (c2 * N ^ ε * α) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow hB2 hB2le (by norm_num)
  have h2 : B ^ ((71 : ℝ) / 142) ≤ (c1 * N ^ ε * α) ^ ((71 : ℝ) / 142) :=
    Real.rpow_le_rpow hB hBle (by norm_num)
  have hsplit : (c2 * N ^ ε * α) ^ ((1 : ℝ) / 2) * (c1 * N ^ ε * α) ^ ((71 : ℝ) / 142) =
      c2 ^ ((1 : ℝ) / 2) * c1 ^ ((71 : ℝ) / 142) * N ^ ε * α := by
    rw [Real.mul_rpow (mul_nonneg hc2 hNe) hα, Real.mul_rpow hc2 hNe,
      Real.mul_rpow (mul_nonneg hc1 hNe) hα, Real.mul_rpow hc1 hNe]
    have he : (N ^ ε) ^ ((1 : ℝ) / 2) * (N ^ ε) ^ ((71 : ℝ) / 142) = N ^ ε := by
      rw [← Real.rpow_add' hNe (by norm_num)]
      norm_num
    have ha : α ^ ((1 : ℝ) / 2) * α ^ ((71 : ℝ) / 142) = α := by
      rw [← Real.rpow_add' hα (by norm_num)]
      norm_num
    calc c2 ^ ((1 : ℝ) / 2) * (N ^ ε) ^ ((1 : ℝ) / 2) * α ^ ((1 : ℝ) / 2) *
          (c1 ^ ((71 : ℝ) / 142) * (N ^ ε) ^ ((71 : ℝ) / 142) * α ^ ((71 : ℝ) / 142))
        = c2 ^ ((1 : ℝ) / 2) * c1 ^ ((71 : ℝ) / 142) *
            ((N ^ ε) ^ ((1 : ℝ) / 2) * (N ^ ε) ^ ((71 : ℝ) / 142)) *
            (α ^ ((1 : ℝ) / 2) * α ^ ((71 : ℝ) / 142)) := by ring
      _ = c2 ^ ((1 : ℝ) / 2) * c1 ^ ((71 : ℝ) / 142) * N ^ ε * α := by rw [he, ha]
  have hmom : B2 ^ ((1 : ℝ) / 2) * B ^ ((71 : ℝ) / 142) ≤
      c2 ^ ((1 : ℝ) / 2) * c1 ^ ((71 : ℝ) / 142) * N ^ ε * α := by
    rw [← hsplit]
    exact mul_le_mul h1 h2 (Real.rpow_nonneg hB _)
      (Real.rpow_nonneg (mul_nonneg (mul_nonneg hc2 hNe) hα) _)
  -- the conductor factor
  have hcond : (C' / N ^ ((1 : ℝ) / 40)) ^ γ = C' ^ γ * N ^ (-(γ / 40)) := by
    rw [Real.div_rpow hC' (Real.rpow_nonneg hN0.le _), ← Real.rpow_mul hN0.le, div_eq_mul_inv,
      Real.rpow_neg hN0.le, show (1 : ℝ) / 40 * γ = γ / 40 by ring]
  -- the exponent: `N^{ε - γ/40} ≤ N^{-σ} ≤ L^{-σ}`
  have hexp : N ^ (-(γ / 40)) * N ^ ε ≤ L ^ (-σ) := by
    rw [← Real.rpow_add hN0]
    have hN1 : 1 ≤ N := hL.trans hN
    calc N ^ (-(γ / 40) + ε) ≤ N ^ (-σ) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ ≤ L ^ (-σ) := by
        apply Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one hL) hN (by linarith)
  have hC'γ : 0 ≤ C' ^ γ := Real.rpow_nonneg hC' _
  have hcc : 0 ≤ c2 ^ ((1 : ℝ) / 2) * c1 ^ ((71 : ℝ) / 142) :=
    mul_nonneg (Real.rpow_nonneg hc2 _) (Real.rpow_nonneg hc1 _)
  rw [hcond]
  calc 72 * (C' ^ γ * N ^ (-(γ / 40)) * (B2 ^ ((1 : ℝ) / 2) * B ^ ((71 : ℝ) / 142)))
      ≤ 72 * (C' ^ γ * N ^ (-(γ / 40)) *
          (c2 ^ ((1 : ℝ) / 2) * c1 ^ ((71 : ℝ) / 142) * N ^ ε * α)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_left hmom (mul_nonneg hC'γ (Real.rpow_nonneg hN0.le _))
    _ = 72 * C' ^ γ * (c2 ^ ((1 : ℝ) / 2) * c1 ^ ((71 : ℝ) / 142)) *
          (N ^ (-(γ / 40)) * N ^ ε) * α := by ring
    _ ≤ 72 * C' ^ γ * (c2 ^ ((1 : ℝ) / 2) * c1 ^ ((71 : ℝ) / 142)) * L ^ (-σ) * α := by
        apply mul_le_mul_of_nonneg_right _ hα
        exact mul_le_mul_of_nonneg_left hexp (mul_nonneg (by positivity) hcc)
    _ = 72 * C' ^ γ * c2 ^ ((1 : ℝ) / 2) * c1 ^ ((71 : ℝ) / 142) * L ^ (-σ) * α := by ring

end Paper

end Sarkozy.DensityDC
