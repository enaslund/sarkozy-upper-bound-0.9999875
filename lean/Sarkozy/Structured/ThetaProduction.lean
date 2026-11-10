module

public import Sarkozy.Structured.DensityStructured
public import Sarkozy.ProbabilityProducts

/-!
# The structured energy beyond `θ ≤ 1` (`prop:density:production`, the final step)

`prop:record:density-structured` (`Sarkozy/Structured/DensityStructured.lean`) uses `θ ≤ 1`
exactly once: in `expect_changed_slot_bound`, the Jensen inequality
`E α_f^θ ≤ (E α_f)^θ` after the Hölder inequality with 72 equal exponents over the samples.
The improved route of the paper (`prop:density:production`,
`paper/sections/31_density_induction_upgrade.tex:498`, at `1 < θ ≤ 1.014587`, `d = 72`)
keeps the pointwise fibre argument and replaces that last step by a two-slot
Cauchy–Schwarz inequality: each production query index occurs in exactly two slots, with
fibre-density means `A`, `B`, and with `u = θ/d`,
`E[A^u B^u] ≤ (E A^{2u} E B^{2u})^{1/2} ≤ (E A E B)^u` (since `2u ≤ 1`); distinct query
indices are independent.

This file supplies the two θ-free pieces and the replacement step.

* `abs_structuredEnergy_le_expect_root`: **the pointwise step, θ-free**:
  `|𝔈| ≤ ‖ρ‖ E_{P ⊗ |ρ|/‖ρ‖} ∏_v Z_𝒮(g_v(z_v, ·))^{1/72}` (signed Hölder for every sample,
  before any averaging over the samples).
* `abs_structuredEnergy_le_of_pointwise`: with pointwise bounds `Z_𝒮(g_v(z_v,·)) ≤ b_v(p)`
  (the fibre bound `Z_𝒮(g̃) ≤ (1+u)C₀L^{-a}ξ^a α_f^θ` of `changed_slot_bound`, which needs
  only `θ ≤ 72`), `|𝔈| ≤ ‖ρ‖ E ∏_v b_v^{1/72}`. No condition on `θ`.
* `expect_rpow_mul_rpow_le`: **the two-occurrence Cauchy–Schwarz bound**: for `A, B ≥ 0`
  on a finite probability space and `0 ≤ u`, `2u ≤ 1`, `E[A^u B^u] ≤ (E A · E B)^u`.
* `expect_prod_pairs_le`: with independent query indices (a product law `⊗_e ν_e` over
  the indices, each `ν_e` a law of the pair of fibre densities of the two slots of `e`),
  `E ∏_e (A_e B_e)^u ≤ ∏_e (E A_e E B_e)^u`.
* `density_structured_theta`: the conclusion of `density_structured` (the abstract
  `prop:record:density-structured`) **without `θ ≤ 1`**. It assumes `2θ/72 ≤ 1` and the
  two-occurrence structure of `prop:density:production` as named hypotheses: the changed
  slots are indexed by `I × Bool` (`slotOf`), and distinct indices are independent
  (`hindep`). At `θ = densityExponent = 1.014587` the condition `2θ/72 ≤ 1` holds.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.Structured

variable {X XE Ω : Type*} [Fintype X] [Fintype XE] [Fintype Ω]

/-- The root energy is `Z_𝒮^{1/72}`. -/
theorem rootEnergy_eq_rpow (μS : FiniteLaw (Slot → X))
    (hμS : SlotReflectionPositive (signedIntegral μS.weight)) (g : X → ℝ) :
    rootEnergy (signedIntegral μS.weight) g = referenceEnergy μS g ^ ((1 : ℝ) / 72) := by
  have hh := slot_signedHolder hμS
  have h0 := hh.rootEnergy_nonneg g
  rw [← rootEnergy_rpow_72 hμS g, abs_of_nonneg h0, ← Real.rpow_mul h0]
  norm_num

/-- **The pointwise step of `prop:record:density-structured`, θ-free**:
`|𝔈| ≤ ‖ρ‖ E_{P ⊗ |ρ|/‖ρ‖} ∏_v Z_𝒮(g_v^ω(z_v, ·))^{1/72}`, from the signed Hölder
inequality at every sample. -/
theorem abs_structuredEnergy_le_expect_root (μS : FiniteLaw (Slot → X))
    (hμS : SlotReflectionPositive (signedIntegral μS.weight)) (P : FiniteLaw Ω)
    (ρ : (Slot → XE) → ℝ) (hρ : 0 < totalVariation ρ) (g : Ω → Slot → XE → X → ℝ) :
    |structuredEnergy μS P ρ g| ≤ totalVariation ρ *
      (P.product (variationLaw ρ hρ)).expect
        (fun p => ∏ v, referenceEnergy μS (g p.1 v (p.2 v)) ^ ((1 : ℝ) / 72)) := by
  set L := signedIntegral μS.weight
  have hh := slot_signedHolder hμS
  set W : Slot → Ω × (Slot → XE) → ℝ := fun v p => rootEnergy L (g p.1 v (p.2 v))
  have hpoint : ∀ ω z, |multilinearIntegral L (fun v => g ω v (z v))| ≤ ∏ v, W v (ω, z) :=
    fun ω z => hh.2 _
  have hW : ∀ p, ∏ v, W v p = ∏ v, referenceEnergy μS (g p.1 v (p.2 v)) ^ ((1 : ℝ) / 72) := by
    intro p
    exact prod_congr rfl fun v _ => rootEnergy_eq_rpow μS hμS _
  have h1 : |structuredEnergy μS P ρ g| ≤
      totalVariation ρ * (P.product (variationLaw ρ hρ)).expect (fun p => ∏ v, W v p) := by
    unfold structuredEnergy
    refine (P.abs_expect_le _).trans ?_
    rw [FiniteLaw.expect_product]
    have hω : ∀ ω, |∑ z, ρ z * multilinearIntegral L (fun v => g ω v (z v))| ≤
        totalVariation ρ * (variationLaw ρ hρ).expect (fun z => ∏ v, W v (ω, z)) := by
      intro ω
      rw [expect_variationLaw, mul_div_cancel₀ _ hρ.ne']
      refine (abs_sum_le_sum_abs _ _).trans ?_
      apply sum_le_sum
      intro z _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hpoint ω z) (abs_nonneg _)
    refine (P.expect_mono hω).trans_eq ?_
    exact P.expect_const_mul _ _
  refine h1.trans_eq ?_
  rw [(P.product (variationLaw ρ hρ)).expect_congr hW]

/-- **The pointwise fibre argument, θ-free**: if `Z_𝒮(g_v^ω(z_v, ·)) ≤ b_v(ω, z)` at every
sample and slot, then `|𝔈| ≤ ‖ρ‖ E ∏_v b_v^{1/72}`. With the fibre bound of
`changed_slot_bound` (which needs only `θ ≤ 72`) at the changed slots and `Z_𝒮(F_A) ≤ Y` at
the unchanged ones, this is `prop:record:density-structured` up to its final Jensen step. -/
theorem abs_structuredEnergy_le_of_pointwise (μS : FiniteLaw (Slot → X))
    (hμS : SlotReflectionPositive (signedIntegral μS.weight)) (P : FiniteLaw Ω)
    (ρ : (Slot → XE) → ℝ) (hρ : 0 < totalVariation ρ) (g : Ω → Slot → XE → X → ℝ)
    (b : Slot → Ω × (Slot → XE) → ℝ)
    (hb : ∀ v ω z, referenceEnergy μS (g ω v (z v)) ≤ b v (ω, z)) :
    |structuredEnergy μS P ρ g| ≤ totalVariation ρ *
      (P.product (variationLaw ρ hρ)).expect (fun p => ∏ v, b v p ^ ((1 : ℝ) / 72)) := by
  refine (abs_structuredEnergy_le_expect_root μS hμS P ρ hρ g).trans ?_
  apply mul_le_mul_of_nonneg_left _ (totalVariation_nonneg ρ)
  apply FiniteLaw.expect_mono
  intro p
  apply prod_le_prod₀
  · intro v _
    exact Real.rpow_nonneg (referenceEnergy_nonneg μS hμS _) _
  · intro v _
    exact Real.rpow_le_rpow (referenceEnergy_nonneg μS hμS _) (hb v p.1 p.2) (by norm_num)

/-- **The two-occurrence Cauchy–Schwarz bound** (`prop:density:production`, the step that
replaces Jensen's inequality): for nonnegative `A`, `B` on a finite probability space and
`0 ≤ u` with `2u ≤ 1`, `E[A^u B^u] ≤ (E A^{2u} E B^{2u})^{1/2} ≤ (E A · E B)^u`. -/
theorem expect_rpow_mul_rpow_le {Ω' : Type*} [Fintype Ω'] (μ : FiniteLaw Ω')
    {A B : Ω' → ℝ} (hA : ∀ ω, 0 ≤ A ω) (hB : ∀ ω, 0 ≤ B ω) {u : ℝ} (hu : 0 ≤ u)
    (hu2 : 2 * u ≤ 1) :
    μ.expect (fun ω => A ω ^ u * B ω ^ u) ≤ (μ.expect A * μ.expect B) ^ u := by
  have hEA : 0 ≤ μ.expect A := μ.expect_nonneg hA
  have hEB : 0 ≤ μ.expect B := μ.expect_nonneg hB
  -- Cauchy–Schwarz
  have hcs := μ.abs_expect_mul_le (fun ω => A ω ^ u) (fun ω => B ω ^ u)
  -- `(C^u)² = C^{2u}`
  have hsq : ∀ (C : Ω' → ℝ), (∀ ω, 0 ≤ C ω) →
      μ.expect (fun ω => (C ω ^ u) ^ 2) = μ.expect (fun ω => C ω ^ (2 * u)) := by
    intro C hC
    apply μ.expect_congr
    intro ω
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hC ω), Nat.cast_ofNat, mul_comm u 2]
  rw [hsq A hA, hsq B hB] at hcs
  -- `√(x^{2u}) = x^u`
  have hpow : ∀ x : ℝ, 0 ≤ x → Real.sqrt (x ^ (2 * u)) = x ^ u := by
    intro x hx
    have h2 : x ^ (2 * u) = (x ^ u) ^ 2 := by
      rw [← Real.rpow_natCast (x ^ u) 2, ← Real.rpow_mul hx, Nat.cast_ofNat, mul_comm u 2]
    rw [h2, Real.sqrt_sq (Real.rpow_nonneg hx _)]
  -- Jensen with the exponent `2u ≤ 1`
  have hjA := expect_rpow_le_rpow_expect μ hA (by linarith : 0 ≤ 2 * u) hu2
  have hjB := expect_rpow_le_rpow_expect μ hB (by linarith : 0 ≤ 2 * u) hu2
  have h1 : μ.expect (fun ω => A ω ^ u * B ω ^ u) ≤ μ.expect A ^ u * μ.expect B ^ u := by
    refine (le_abs_self _).trans (hcs.trans ?_)
    rw [← hpow _ hEA, ← hpow _ hEB]
    exact mul_le_mul (Real.sqrt_le_sqrt hjA) (Real.sqrt_le_sqrt hjB) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
  rw [Real.mul_rpow hEA hEB]
  exact h1

/-- **Independent query indices**: under a product law `⊗_e ν_e` over the query indices,
where `ν_e` is a law of the pair `(A_e, B_e)` of fibre densities of the two slots of `e`,
`E ∏_e (A_e B_e)^u ≤ ∏_e (E A_e E B_e)^u` for `0 ≤ u`, `2u ≤ 1`
(`expect_rpow_mul_rpow_le` at each index). -/
theorem expect_prod_pairs_le {I Ω' : Type*} [Fintype I] [DecidableEq I] [Fintype Ω']
    (ν : I → FiniteLaw Ω') (A B : I → Ω' → ℝ) (hA : ∀ e ω, 0 ≤ A e ω)
    (hB : ∀ e ω, 0 ≤ B e ω) {u : ℝ} (hu : 0 ≤ u) (hu2 : 2 * u ≤ 1) :
    (FiniteLaw.pi (Ω := fun _ : I => Ω') ν).expect
        (fun x => ∏ e, (A e (x e) ^ u * B e (x e) ^ u)) ≤
      ∏ e, ((ν e).expect (A e) * (ν e).expect (B e)) ^ u := by
  rw [FiniteLaw.expect_pi_product (Ω := fun _ : I => Ω') ν (fun e ω => A e ω ^ u * B e ω ^ u)]
  apply prod_le_prod₀
  · intro e _
    exact (ν e).expect_nonneg fun ω =>
      mul_nonneg (Real.rpow_nonneg (hA e ω) _) (Real.rpow_nonneg (hB e ω) _)
  · intro e _
    exact expect_rpow_mul_rpow_le (ν e) (hA e) (hB e) hu hu2

/-- **`prop:record:density-structured` at density exponents `θ > 1`**, with the final step
of `prop:density:production`: the conclusion of `density_structured` without `θ ≤ 1`. It
needs `2θ/72 ≤ 1` and the two-occurrence structure of the production arguments, stated as
named hypotheses:
* `slotOf`: the changed slots are indexed by `I × Bool`, so each query index `e : I` occurs
  in exactly two changed slots, `slotOf (e, true)` and `slotOf (e, false)`;
* `hindep`: distinct query indices are independent. Under the sample law `P ⊗ |ρ|/‖ρ‖`,
  the expectation of the product over the indices of the pair terms `A_e^u B_e^u`
  (`u = θ/72`, `A_e`, `B_e` the fibre densities of the two slots of `e`) is the product of
  their expectations.

The final step is then `expect_rpow_mul_rpow_le` at every index in place of Jensen's
inequality. -/
theorem density_structured_theta (μS : FiniteLaw (Slot → X))
    (hμS : SlotReflectionPositive (signedIntegral μS.weight)) (P : FiniteLaw Ω)
    (ρ : (Slot → XE) → ℝ) (g gt : Ω → Slot → XE → X → ℝ)
    (changed : Slot → Prop) [DecidablePred changed]
    {Y C0 a θ L α u Cdc σ : ℝ} (hC0 : 0 ≤ C0) (ha : 0 ≤ a) (hθ0 : 0 ≤ θ)
    (hθ2 : 2 * (θ / 72) ≤ 1)
    (hL : 0 < L) (hα : 0 < α) (hu : 0 ≤ u) (hY : 0 ≤ Y)
    (hlow : C0 * L ^ (-a) * α ^ θ < Y)
    (ξ αbar : Slot → ℝ) (hξ : ∀ v, 1 ≤ ξ v) (hαbar : ∀ v, 0 ≤ αbar v)
    (hun : ∀ v, ¬changed v → ∀ ω z, referenceEnergy μS (gt ω v z) ≤ Y)
    (αf : Ω → Slot → XE → ℝ) (hαf : ∀ ω v z, 0 ≤ αf ω v z)
    (hch : ∀ v, changed v → ∀ ω z,
      referenceEnergy μS (gt ω v z) ≤ (1 + u) * C0 * L ^ (-a) * ξ v ^ a * αf ω v z ^ θ)
    (hmean : ∀ hρ : 0 < totalVariation ρ, ∀ v, changed v →
      (P.product (variationLaw ρ hρ)).expect (fun p => αf p.1 v (p.2 v)) = αbar v)
    {I : Type*} [Fintype I] [DecidableEq I] (slotOf : I × Bool ≃ {v // changed v})
    (hindep : ∀ hρ : 0 < totalVariation ρ,
      (P.product (variationLaw ρ hρ)).expect (fun p => ∏ e,
        (αf p.1 (slotOf (e, true)) (p.2 (slotOf (e, true))) ^ (θ / 72) *
          αf p.1 (slotOf (e, false)) (p.2 (slotOf (e, false))) ^ (θ / 72))) =
      ∏ e, (P.product (variationLaw ρ hρ)).expect (fun p =>
        αf p.1 (slotOf (e, true)) (p.2 (slotOf (e, true))) ^ (θ / 72) *
          αf p.1 (slotOf (e, false)) (p.2 (slotOf (e, false))) ^ (θ / 72)))
    (hdc : |structuredEnergy μS P ρ g - structuredEnergy μS P ρ gt| ≤
      Cdc * totalVariation ρ * L ^ (-σ) * α) :
    |structuredEnergy μS P ρ g| ≤
      totalVariation ρ * ((1 + u) * mainPrice ξ αbar changed a θ α * Y +
        Cdc * L ^ (-σ) * α) := by
  rcases (totalVariation_nonneg ρ).lt_or_eq with hρ | hρ0
  · set Jt := P.product (variationLaw ρ hρ)
    have hξ0 : ∀ v, 0 ≤ ξ v := fun v => le_trans zero_le_one (hξ v)
    have hξa : ∀ v, 1 ≤ ξ v ^ a := fun v => Real.one_le_rpow (hξ v) ha
    set K : Slot → ℝ := fun v => (1 + u) * C0 * L ^ (-a) * ξ v ^ a with hKdef
    have hK0 : ∀ v, 0 ≤ K v := fun v =>
      mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hC0) (Real.rpow_nonneg hL.le _))
        (Real.rpow_nonneg (hξ0 v) _)
    -- the pointwise bounds
    set b : Slot → Ω × (Slot → XE) → ℝ := fun v p =>
      if changed v then K v * αf p.1 v (p.2 v) ^ θ else Y with hbdef
    have hb : ∀ v ω z, referenceEnergy μS (gt ω v (z v)) ≤ b v (ω, z) := by
      intro v ω z
      simp only [hbdef]
      split_ifs with hv
      · exact hch v hv ω (z v)
      · exact hun v hv ω (z v)
    have hmain := abs_structuredEnergy_le_of_pointwise μS hμS P ρ hρ gt b hb
    -- split off the constants: `∏_v b_v^{1/72} = (∏_v k_v) · ∏_{v changed} α_v^{θ/72}`
    set k : Slot → ℝ := fun v => (if changed v then K v else Y) ^ ((1 : ℝ) / 72) with hkdef
    have hsplit : ∀ p, ∏ v, b v p ^ ((1 : ℝ) / 72) =
        (∏ v, k v) * ∏ v ∈ univ.filter changed, αf p.1 v (p.2 v) ^ (θ / 72) := by
      intro p
      have hv : ∀ v, b v p ^ ((1 : ℝ) / 72) =
          k v * (if changed v then αf p.1 v (p.2 v) ^ (θ / 72) else 1) := by
        intro v
        simp only [hbdef, hkdef]
        split_ifs
        · rw [Real.mul_rpow (hK0 v) (Real.rpow_nonneg (hαf _ _ _) _),
            ← Real.rpow_mul (hαf _ _ _)]
          ring_nf
        · rw [mul_one]
      rw [prod_congr rfl fun v _ => hv v, prod_mul_distrib, prod_ite, prod_const_one, mul_one]
    -- the two-occurrence step
    have hpairs : Jt.expect (fun p => ∏ v ∈ univ.filter changed, αf p.1 v (p.2 v) ^ (θ / 72)) ≤
        ∏ v ∈ univ.filter changed, αbar v ^ (θ / 72) := by
      have hre : ∀ (F : Slot → ℝ), ∏ v ∈ univ.filter changed, F v =
          ∏ e, (F (slotOf (e, true)) * F (slotOf (e, false))) := by
        intro F
        rw [Finset.prod_subtype (p := changed) (univ.filter changed) (fun x => by simp) F,
          ← slotOf.prod_comp (fun v : {v // changed v} => F v.1), Fintype.prod_prod_type]
        exact prod_congr rfl fun e _ => by rw [Fintype.prod_bool]
      have hθu : 0 ≤ θ / 72 := by positivity
      calc Jt.expect (fun p => ∏ v ∈ univ.filter changed, αf p.1 v (p.2 v) ^ (θ / 72))
          = Jt.expect (fun p => ∏ e,
              (αf p.1 (slotOf (e, true)) (p.2 (slotOf (e, true))) ^ (θ / 72) *
                αf p.1 (slotOf (e, false)) (p.2 (slotOf (e, false))) ^ (θ / 72))) :=
            Jt.expect_congr fun p => hre (fun v => αf p.1 v (p.2 v) ^ (θ / 72))
        _ = ∏ e, Jt.expect (fun p =>
              αf p.1 (slotOf (e, true)) (p.2 (slotOf (e, true))) ^ (θ / 72) *
                αf p.1 (slotOf (e, false)) (p.2 (slotOf (e, false))) ^ (θ / 72)) := hindep hρ
        _ ≤ ∏ e, (αbar (slotOf (e, true)) * αbar (slotOf (e, false))) ^ (θ / 72) := by
            apply prod_le_prod₀
            · intro e _
              exact Jt.expect_nonneg fun p => mul_nonneg (Real.rpow_nonneg (hαf _ _ _) _)
                (Real.rpow_nonneg (hαf _ _ _) _)
            · intro e _
              have h := expect_rpow_mul_rpow_le Jt
                (A := fun p => αf p.1 (slotOf (e, true)) (p.2 (slotOf (e, true))))
                (B := fun p => αf p.1 (slotOf (e, false)) (p.2 (slotOf (e, false))))
                (fun p => hαf _ _ _) (fun p => hαf _ _ _) hθu hθ2
              rwa [hmean hρ _ (slotOf (e, true)).2, hmean hρ _ (slotOf (e, false)).2] at h
        _ = ∏ v ∈ univ.filter changed, αbar v ^ (θ / 72) := by
            rw [hre (fun v => αbar v ^ (θ / 72))]
            exact prod_congr rfl fun e _ =>
              Real.mul_rpow (hαbar _) (hαbar _)
    -- the old per-slot constants `c_v`
    set c : Slot → ℝ := fun v =>
      (1 + u) * Y * ξ v ^ a * (if changed v then (αbar v / α) ^ θ else 1) with hcdef
    have hkc : (∏ v, k v) * ∏ v ∈ univ.filter changed, αbar v ^ (θ / 72) ≤
        ∏ v, c v ^ ((1 : ℝ) / 72) := by
      have hfac : (∏ v, k v) * ∏ v ∈ univ.filter changed, αbar v ^ (θ / 72) =
          ∏ v, (k v * (if changed v then αbar v ^ (θ / 72) else 1)) := by
        rw [prod_mul_distrib, prod_ite, prod_const_one, mul_one]
      rw [hfac]
      apply prod_le_prod₀
      · intro v _
        apply mul_nonneg (Real.rpow_nonneg (by split_ifs; exacts [hK0 v, hY]) _)
        split_ifs
        · exact Real.rpow_nonneg (hαbar v) _
        · exact zero_le_one
      · intro v _
        simp only [hkdef, hcdef]
        by_cases hv : changed v
        · simp only [hv, ↓reduceIte]
          rw [show αbar v ^ (θ / 72) = (αbar v ^ θ) ^ ((1 : ℝ) / 72) by
            rw [← Real.rpow_mul (hαbar v)]; ring_nf,
            ← Real.mul_rpow (hK0 v) (Real.rpow_nonneg (hαbar v) _)]
          apply Real.rpow_le_rpow (mul_nonneg (hK0 v) (Real.rpow_nonneg (hαbar v) _)) _
            (by norm_num)
          -- `K ᾱ^θ ≤ (1+u) Y ξ^a (ᾱ/α)^θ`
          have hsp : αbar v ^ θ = α ^ θ * (αbar v / α) ^ θ := by
            rw [← Real.mul_rpow hα.le (div_nonneg (hαbar v) hα.le), mul_div_cancel₀ _ hα.ne']
          rw [hsp]
          have hr : 0 ≤ (αbar v / α) ^ θ := Real.rpow_nonneg (div_nonneg (hαbar v) hα.le) _
          have hY' : C0 * L ^ (-a) * α ^ θ * (αbar v / α) ^ θ ≤ Y * (αbar v / α) ^ θ :=
            mul_le_mul_of_nonneg_right hlow.le hr
          have hpre : 0 ≤ (1 + u) * ξ v ^ a :=
            mul_nonneg (by linarith) (Real.rpow_nonneg (hξ0 v) _)
          have := mul_le_mul_of_nonneg_left hY' hpre
          simp only [hKdef]
          calc (1 + u) * C0 * L ^ (-a) * ξ v ^ a * (α ^ θ * (αbar v / α) ^ θ)
              = (1 + u) * ξ v ^ a * (C0 * L ^ (-a) * α ^ θ * (αbar v / α) ^ θ) := by ring
            _ ≤ (1 + u) * ξ v ^ a * (Y * (αbar v / α) ^ θ) := this
            _ = (1 + u) * Y * ξ v ^ a * (αbar v / α) ^ θ := by ring
        · simp only [hv, ↓reduceIte, mul_one]
          apply Real.rpow_le_rpow hY _ (by norm_num)
          have h2 : Y ≤ Y * ξ v ^ a := le_mul_of_one_le_right hY (hξa v)
          have h3 : Y * ξ v ^ a ≤ (1 + u) * (Y * ξ v ^ a) :=
            le_mul_of_one_le_left (mul_nonneg hY (le_trans zero_le_one (hξa v))) (by linarith)
          linarith
    -- `∏_v c_v^{1/72} = (1 + u) Π_main Y`
    have hprod : ∏ v, c v ^ ((1 : ℝ) / 72) = (1 + u) * mainPrice ξ αbar changed a θ α * Y := by
      have hfac : ∀ v, c v ^ ((1 : ℝ) / 72) = ((1 + u) * Y) ^ ((1 : ℝ) / 72) *
          (ξ v ^ (a / 72) * (if changed v then (αbar v / α) ^ (θ / 72) else 1)) := by
        intro v
        simp only [hcdef]
        have hA : 0 ≤ (1 + u) * Y := mul_nonneg (by linarith) hY
        have hB : 0 ≤ ξ v ^ a := Real.rpow_nonneg (hξ0 v) _
        have hC : 0 ≤ (if changed v then (αbar v / α) ^ θ else 1) := by
          split_ifs
          · exact Real.rpow_nonneg (div_nonneg (hαbar v) hα.le) _
          · exact zero_le_one
        rw [Real.mul_rpow (mul_nonneg hA hB) hC, Real.mul_rpow hA hB, mul_assoc]
        congr 2
        · rw [← Real.rpow_mul (hξ0 v)]
          ring_nf
        · split_ifs
          · rw [← Real.rpow_mul (div_nonneg (hαbar v) hα.le)]
            ring_nf
          · exact Real.one_rpow _
      simp only [hfac, prod_mul_distrib]
      rw [prod_slot_rpow _ (mul_nonneg (by linarith) hY), prod_ite, prod_const_one, mul_one]
      unfold mainPrice
      ring
    have hk0 : 0 ≤ ∏ v, k v := prod_nonneg fun v _ =>
      Real.rpow_nonneg (by split_ifs; exacts [hK0 v, hY]) _
    have hE : Jt.expect (fun p => ∏ v, b v p ^ ((1 : ℝ) / 72)) ≤
        (1 + u) * mainPrice ξ αbar changed a θ α * Y := by
      rw [Jt.expect_congr hsplit, Jt.expect_const_mul]
      calc (∏ v, k v) * Jt.expect (fun p =>
            ∏ v ∈ univ.filter changed, αf p.1 v (p.2 v) ^ (θ / 72)) ≤
          (∏ v, k v) * ∏ v ∈ univ.filter changed, αbar v ^ (θ / 72) :=
            mul_le_mul_of_nonneg_left hpairs hk0
        _ ≤ ∏ v, c v ^ ((1 : ℝ) / 72) := hkc
        _ = _ := hprod
    have hmain' : |structuredEnergy μS P ρ gt| ≤
        totalVariation ρ * ((1 + u) * mainPrice ξ αbar changed a θ α * Y) :=
      hmain.trans (mul_le_mul_of_nonneg_left hE (totalVariation_nonneg ρ))
    have htri : |structuredEnergy μS P ρ g| ≤
        |structuredEnergy μS P ρ gt| +
          |structuredEnergy μS P ρ g - structuredEnergy μS P ρ gt| := by
      have := abs_sub_abs_le_abs_sub (structuredEnergy μS P ρ g) (structuredEnergy μS P ρ gt)
      linarith
    calc |structuredEnergy μS P ρ g|
        ≤ totalVariation ρ * ((1 + u) * mainPrice ξ αbar changed a θ α * Y) +
            Cdc * totalVariation ρ * L ^ (-σ) * α := by linarith
      _ = _ := by ring
  · rw [structuredEnergy_eq_zero_of_totalVariation μS P ρ hρ0.symm g, ← hρ0]
    simp

/-- At the paper's exponent `ϑ = densityExponent = 1.014587`, `2ϑ/72 ≤ 1`. -/
theorem two_mul_densityExponent_div_le : 2 * (densityExponent / 72) ≤ 1 := by
  unfold densityExponent
  norm_num

/-- **`density_structured_theta` at a least normalized counterexample** (any `θ > 0` with
`2θ/72 ≤ 1`, e.g. `θ = densityExponent`): `Y = Y(L, A)`, `α = |A|/N`, and the two-occurrence
structure of `prop:density:production` as named hypotheses (`slotOf`, `hindep`). -/
theorem density_structured_theta_counterexample {Yf : ℕ → Finset ℤ → ℝ} {a θ C0 : ℝ} {L : ℕ}
    {A : Finset ℤ} (hcex : IsLeastCounterexample Yf a θ C0 L A) (hθ : 0 < θ)
    (hθ2 : 2 * (θ / 72) ≤ 1)
    (ha : 0 ≤ a) (hC0 : 0 ≤ C0) (hL : 1 ≤ L) (hY0 : Yf L ∅ ≤ 0)
    (μS : FiniteLaw (Slot → X)) (hμS : SlotReflectionPositive (signedIntegral μS.weight))
    (P : FiniteLaw Ω) (ρ : (Slot → XE) → ℝ) (g gt : Ω → Slot → XE → X → ℝ)
    (changed : Slot → Prop) [DecidablePred changed] {u Cdc σ : ℝ} (hu : 0 ≤ u)
    (ξ αbar : Slot → ℝ) (hξ : ∀ v, 1 ≤ ξ v) (hαbar : ∀ v, 0 ≤ αbar v)
    (hun : ∀ v, ¬changed v → ∀ ω z, referenceEnergy μS (gt ω v z) ≤ Yf L A)
    (αf : Ω → Slot → XE → ℝ) (hαf : ∀ ω v z, 0 ≤ αf ω v z)
    (hch : ∀ v, changed v → ∀ ω z, referenceEnergy μS (gt ω v z) ≤
      (1 + u) * C0 * (L : ℝ) ^ (-a) * ξ v ^ a * αf ω v z ^ θ)
    (hmean : ∀ hρ : 0 < totalVariation ρ, ∀ v, changed v →
      (P.product (variationLaw ρ hρ)).expect (fun p => αf p.1 v (p.2 v)) = αbar v)
    {I : Type*} [Fintype I] [DecidableEq I] (slotOf : I × Bool ≃ {v // changed v})
    (hindep : ∀ hρ : 0 < totalVariation ρ,
      (P.product (variationLaw ρ hρ)).expect (fun p => ∏ e,
        (αf p.1 (slotOf (e, true)) (p.2 (slotOf (e, true))) ^ (θ / 72) *
          αf p.1 (slotOf (e, false)) (p.2 (slotOf (e, false))) ^ (θ / 72))) =
      ∏ e, (P.product (variationLaw ρ hρ)).expect (fun p =>
        αf p.1 (slotOf (e, true)) (p.2 (slotOf (e, true))) ^ (θ / 72) *
          αf p.1 (slotOf (e, false)) (p.2 (slotOf (e, false))) ^ (θ / 72)))
    (hdc : |structuredEnergy μS P ρ g - structuredEnergy μS P ρ gt| ≤
      Cdc * totalVariation ρ * (L : ℝ) ^ (-σ) * density (blockScale * L) A) :
    |structuredEnergy μS P ρ g| ≤
      totalVariation ρ * ((1 + u) *
        mainPrice ξ αbar changed a θ (density (blockScale * L) A) * Yf L A +
        Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  have hα := hcex.density_pos hθ.ne' hY0
  have hlow := hcex.lower
  have hYpos : 0 ≤ Yf L A := le_trans (by
    exact mul_nonneg (mul_nonneg hC0 (Real.rpow_nonneg (by positivity) _))
      (Real.rpow_nonneg (density_nonneg _ _) _)) hlow.le
  exact density_structured_theta μS hμS P ρ g gt changed hC0 ha hθ.le hθ2
    (by exact_mod_cast hL) hα hu hYpos hlow ξ αbar hξ hαbar hun αf hαf hch hmean slotOf hindep hdc

end Sarkozy.Structured
