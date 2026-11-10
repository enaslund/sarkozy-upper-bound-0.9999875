module

public import Sarkozy.Structured.ProductionIndex

/-!
# `prop:density:production` from the coupled index law (WP-S, fifth package)

`paper/sections/31_density_induction_upgrade.tex:540–548`. WP-R's `density_structured_theta`
(`Sarkozy/Structured/ThetaProduction.lean`) uses its two-occurrence hypotheses `slotOf`, `hindep`
(packaged as `ProductionTwoOccurrence`, `Sarkozy/Structured/ProductionIndex.lean`) at exactly one
place, the product bound

  `(hpairs)  E_{P ⊗ |ρ|/‖ρ‖} ∏_{v changed} α_f^{θ/72} ≤ ∏_{v changed} ᾱ_v^{θ/72}`.

* `density_structured_theta_of_pairs`: the conclusion of `density_structured_theta` from `hpairs`
  alone (WP-R's proof with `hpairs` as hypothesis; `2θ/72 ≤ 1`, `hmean`, `slotOf`, `hindep` are
  not needed). `pairs_of_twoOccurrence`: WP-R's `ProductionTwoOccurrence` implies `hpairs`, so
  `hpairs` is the weaker hypothesis.
* `expect_prod_rpow_le_prod`: **Hölder with `m` equal exponents, then Jensen**:
  `E ∏_{i∈C} f_i^u ≤ ∏_{i∈C} (E f_i)^u` whenever `|C| u ≤ 1`, for **any** joint law.
  Hence `density_structured_theta_few`: if `#changed · θ/72 ≤ 1` — at `θ = densityExponent`,
  at most 70 changed slots (`few_of_card_le_seventy`) — the conclusion holds **with no
  two-occurrence or independence hypothesis at all**. Independence is needed only when all 72
  slots change.
* `density_structured_theta_two_occ`: with only part (a) of `ProductionTwoOccurrence` (changed
  slots indexed by `E × Bool`) and `2|E| θ/72 ≤ 1` (e.g. the six queries `𝓔_6`), part (b) is
  not needed.
* `production_pairs_of_index`, `density_structured_theta_index`: **the paper's route** for the
  general case. The index is `ω = (ω_e)_e` under a product law `⊗_e ν_e` over the production
  queries (`def:hyb:coupled`). Assume (G) the labels are integrated first: for every index `ω`,
  `E_z ∏_{v changed} α_f(ω,v,z_v)^u ≤ ∏_{v changed} (E_z α_f(ω,v,z_v))^u` (the output of the
  complementary geometric means, `lem:density:coupled`); and (L) the fibre-density means
  `E_z α_f(ω, slotOf (e,s), ·)` are functions of the query's own index `ω_e`. Then `hpairs`
  follows from the independence of distinct query indices alone (`expect_pi_product`) and the
  two-slot Cauchy–Schwarz bound at each query (WP-R's `expect_rpow_mul_rpow_le`).

* `label_bound_of_pair_indep`: (G) follows from the label part of WP-R's independence (pairs of
  labels of distinct queries independent for each fixed index).
* `label_bound_fails`: (G) can fail when `|changed| u > 1` (a fair bit shared by all slots), so for
  all 72 slots changed and `θ > 1` it is a genuine input.

**What WP-R's form asks beyond the paper.** `ProductionTwoOccurrence.indep` requires the pairs
`(α_f(ω, src e, z_{src e}), α_f(ω, tgt e, z_{tgt e}))` to be independent across queries under
`P ⊗ |ρ|/‖ρ‖`, which involves the labels `z`; a product index law does not give this when the
labels of different queries are correlated under `|ρ|`. The paper never needs it: the labels are
integrated before the index law (hypothesis (G)), and then only index independence is used.
(G) itself is not automatic when all 72 slots change and `θ > 1` (Jensen goes the wrong way for a
label shared by many slots); it is the content of the folded-law estimate `lem:density:coupled`
(cf. `Sarkozy.DensityUpgrade.coupled_conditional_bound`, whose bound at a fixed spectator tuple is
`δ ∏_v b_v (E_x a_v(x,z_v))^{θ/d}`).
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.TraceMixing

open Sarkozy.Structured

variable {X XE Ω : Type*} [Fintype X] [Fintype XE] [Fintype Ω]

/-- **`prop:record:density-structured` at `θ > 1` from the product bound alone**: the
conclusion of WP-R's `density_structured_theta` with its two-occurrence hypotheses replaced by
the only consequence its proof uses, `hpairs`. (The proof is WP-R's, unchanged otherwise.) -/
theorem density_structured_theta_of_pairs (μS : FiniteLaw (Slot → X))
    (hμS : SlotReflectionPositive (signedIntegral μS.weight)) (P : FiniteLaw Ω)
    (ρ : (Slot → XE) → ℝ) (g gt : Ω → Slot → XE → X → ℝ)
    (changed : Slot → Prop) [DecidablePred changed]
    {Y C0 a θ L α u Cdc σ : ℝ} (hC0 : 0 ≤ C0) (ha : 0 ≤ a)
    (hL : 0 < L) (hα : 0 < α) (hu : 0 ≤ u) (hY : 0 ≤ Y)
    (hlow : C0 * L ^ (-a) * α ^ θ < Y)
    (ξ αbar : Slot → ℝ) (hξ : ∀ v, 1 ≤ ξ v) (hαbar : ∀ v, 0 ≤ αbar v)
    (hun : ∀ v, ¬changed v → ∀ ω z, referenceEnergy μS (gt ω v z) ≤ Y)
    (αf : Ω → Slot → XE → ℝ) (hαf : ∀ ω v z, 0 ≤ αf ω v z)
    (hch : ∀ v, changed v → ∀ ω z,
      referenceEnergy μS (gt ω v z) ≤ (1 + u) * C0 * L ^ (-a) * ξ v ^ a * αf ω v z ^ θ)
    (hpairs : ∀ hρ : 0 < totalVariation ρ,
      (P.product (variationLaw ρ hρ)).expect
          (fun p => ∏ v ∈ univ.filter changed, αf p.1 v (p.2 v) ^ (θ / 72)) ≤
        ∏ v ∈ univ.filter changed, αbar v ^ (θ / 72))
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
    have hpairs := hpairs hρ
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


/-- **Hölder with `m` equal exponents, then Jensen**: for nonnegative `f_i` (`i ∈ C`) on a finite
probability space and `0 ≤ u` with `|C| u ≤ 1`, `E ∏_{i∈C} f_i^u ≤ ∏_{i∈C} (E f_i)^u`, for
**any** joint law (no independence). Proof: weighted AM–GM for `f_i/E f_i` with weights `1/|C|`,
then Jensen for `x ↦ x^{|C|u}`. -/
theorem expect_prod_rpow_le_prod {Θ ι : Type*} [Fintype Θ] (μ : FiniteLaw Θ) (C : Finset ι)
    (f : ι → Θ → ℝ) (hf : ∀ i t, 0 ≤ f i t) {u : ℝ} (hu : 0 ≤ u)
    (hCu : (C.card : ℝ) * u ≤ 1) :
    μ.expect (fun t => ∏ i ∈ C, f i t ^ u) ≤ ∏ i ∈ C, μ.expect (f i) ^ u := by
  classical
  rcases C.eq_empty_or_nonempty with hC | hC
  · subst hC
    simp
  rcases hu.lt_or_eq with hu0 | hu0
  swap
  · subst hu0
    simp
  by_cases hz : ∃ i ∈ C, μ.expect (f i) = 0
  · obtain ⟨i, hi, hAi⟩ := hz
    have hpt : ∀ t, μ.weight t * ∏ j ∈ C, f j t ^ u = 0 := by
      intro t
      have h0 : μ.weight t * f i t = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun t _ => mul_nonneg (μ.nonneg t) (hf i t))).mp
          hAi t (mem_univ t)
      rcases mul_eq_zero.mp h0 with h | h
      · rw [h, zero_mul]
      · rw [Finset.prod_eq_zero hi (by rw [h, Real.zero_rpow hu0.ne']), mul_zero]
    have hL : μ.expect (fun t => ∏ j ∈ C, f j t ^ u) = 0 := by
      unfold FiniteLaw.expect
      exact Finset.sum_eq_zero fun t _ => hpt t
    rw [hL]
    exact prod_nonneg fun j _ => Real.rpow_nonneg (μ.expect_nonneg (hf j)) _
  push Not at hz
  have hApos : ∀ i ∈ C, 0 < μ.expect (f i) := fun i hi =>
    lt_of_le_of_ne (μ.expect_nonneg (hf i)) (Ne.symm (hz i hi))
  set m : ℝ := (C.card : ℝ) with hm_def
  have hm : 0 < m := by rw [hm_def]; exact_mod_cast hC.card_pos
  set g : ι → Θ → ℝ := fun i t => f i t / μ.expect (f i) with hg_def
  have hg0 : ∀ i t, 0 ≤ g i t := fun i t => div_nonneg (hf i t) (μ.expect_nonneg (hf i))
  have hamgm : ∀ t, ∏ i ∈ C, g i t ^ u ≤ ∑ i ∈ C, (1 / m) * g i t ^ (m * u) := by
    intro t
    have h := Real.geom_mean_le_arith_mean_weighted C (fun _ => 1 / m)
      (fun i => g i t ^ (m * u)) (fun i _ => by positivity)
      (by rw [Finset.sum_const, nsmul_eq_mul, ← hm_def]; field_simp)
      (fun i _ => Real.rpow_nonneg (hg0 i t) _)
    have e : ∀ i ∈ C, (g i t ^ (m * u)) ^ (1 / m) = g i t ^ u := fun i _ => by
      rw [← Real.rpow_mul (hg0 i t)]
      congr 1
      field_simp
    rw [Finset.prod_congr rfl e] at h
    exact h
  have hJ : ∀ i ∈ C, μ.expect (fun t => g i t ^ (m * u)) ≤ 1 := by
    intro i hi
    have h := expect_rpow_le_rpow_expect μ (hg0 i) (by positivity) hCu
    have hEg : μ.expect (g i) = 1 := by
      have hA := (hApos i hi).ne'
      have e : μ.expect (g i) = μ.expect (f i) / μ.expect (f i) := by
        simp only [hg_def]
        unfold FiniteLaw.expect
        rw [Finset.sum_div]
        exact sum_congr rfl fun t _ => by ring
      rw [e, div_self hA]
    rw [hEg, Real.one_rpow] at h
    exact h
  have hEprod : μ.expect (fun t => ∏ i ∈ C, g i t ^ u) ≤ 1 := by
    calc μ.expect (fun t => ∏ i ∈ C, g i t ^ u)
        ≤ μ.expect (fun t => ∑ i ∈ C, (1 / m) * g i t ^ (m * u)) := μ.expect_mono hamgm
      _ = ∑ i ∈ C, (1 / m) * μ.expect (fun t => g i t ^ (m * u)) := by
          unfold FiniteLaw.expect
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact sum_congr rfl fun i _ => sum_congr rfl fun t _ => by ring
      _ ≤ ∑ i ∈ C, (1 / m) * 1 :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hJ i hi) (by positivity)
      _ = 1 := by
          rw [Finset.sum_const, nsmul_eq_mul, ← hm_def]
          field_simp
  have hfac : ∀ t, ∏ i ∈ C, f i t ^ u =
      (∏ i ∈ C, μ.expect (f i) ^ u) * ∏ i ∈ C, g i t ^ u := by
    intro t
    rw [← Finset.prod_mul_distrib]
    refine prod_congr rfl fun i hi => ?_
    rw [← Real.mul_rpow (μ.expect_nonneg (hf i)) (hg0 i t)]
    congr 1
    simp only [hg_def]
    field_simp [(hApos i hi).ne']
  rw [μ.expect_congr hfac, μ.expect_const_mul]
  have hP0 : 0 ≤ ∏ i ∈ C, μ.expect (f i) ^ u :=
    prod_nonneg fun i _ => Real.rpow_nonneg (μ.expect_nonneg (hf i)) _
  calc (∏ i ∈ C, μ.expect (f i) ^ u) * μ.expect (fun t => ∏ i ∈ C, g i t ^ u)
      ≤ (∏ i ∈ C, μ.expect (f i) ^ u) * 1 := mul_le_mul_of_nonneg_left hEprod hP0
    _ = ∏ i ∈ C, μ.expect (f i) ^ u := mul_one _

/-- **`prop:density:production` needs no independence when at most `72/θ` slots change**: if
`#changed · θ/72 ≤ 1` (at `θ = densityExponent` this is `#changed ≤ 70`), the conclusion of
`density_structured_theta` holds with no two-occurrence or independence hypothesis
(`expect_prod_rpow_le_prod` over the changed slots, then `density_structured_theta_of_pairs`). -/
theorem density_structured_theta_few (μS : FiniteLaw (Slot → X))
    (hμS : SlotReflectionPositive (signedIntegral μS.weight)) (P : FiniteLaw Ω)
    (ρ : (Slot → XE) → ℝ) (g gt : Ω → Slot → XE → X → ℝ)
    (changed : Slot → Prop) [DecidablePred changed]
    {Y C0 a θ L α u Cdc σ : ℝ} (hC0 : 0 ≤ C0) (ha : 0 ≤ a) (hθ0 : 0 ≤ θ)
    (hfew : ((univ.filter changed).card : ℝ) * (θ / 72) ≤ 1)
    (hL : 0 < L) (hα : 0 < α) (hu : 0 ≤ u) (hY : 0 ≤ Y)
    (hlow : C0 * L ^ (-a) * α ^ θ < Y)
    (ξ αbar : Slot → ℝ) (hξ : ∀ v, 1 ≤ ξ v) (hαbar : ∀ v, 0 ≤ αbar v)
    (hun : ∀ v, ¬changed v → ∀ ω z, referenceEnergy μS (gt ω v z) ≤ Y)
    (αf : Ω → Slot → XE → ℝ) (hαf : ∀ ω v z, 0 ≤ αf ω v z)
    (hch : ∀ v, changed v → ∀ ω z,
      referenceEnergy μS (gt ω v z) ≤ (1 + u) * C0 * L ^ (-a) * ξ v ^ a * αf ω v z ^ θ)
    (hmean : ∀ hρ : 0 < totalVariation ρ, ∀ v, changed v →
      (P.product (variationLaw ρ hρ)).expect (fun p => αf p.1 v (p.2 v)) = αbar v)
    (hdc : |structuredEnergy μS P ρ g - structuredEnergy μS P ρ gt| ≤
      Cdc * totalVariation ρ * L ^ (-σ) * α) :
    |structuredEnergy μS P ρ g| ≤
      totalVariation ρ * ((1 + u) * mainPrice ξ αbar changed a θ α * Y +
        Cdc * L ^ (-σ) * α) := by
  refine density_structured_theta_of_pairs μS hμS P ρ g gt changed hC0 ha hL hα hu hY hlow ξ αbar
    hξ hαbar hun αf hαf hch ?_ hdc
  intro hρ
  have h := expect_prod_rpow_le_prod (P.product (variationLaw ρ hρ)) (univ.filter changed)
    (fun v p => αf p.1 v (p.2 v)) (fun v p => hαf _ _ _) (by positivity) hfew
  refine h.trans (le_of_eq (prod_congr rfl fun v hv => ?_))
  rw [hmean hρ v (mem_filter.mp hv).2]

/-- At `θ = densityExponent = 1.014587`, at most `70` changed slots satisfy `#changed · θ/72 ≤ 1`. -/
theorem few_of_card_le_seventy {n : ℕ} (hn : n ≤ 70) : (n : ℝ) * (densityExponent / 72) ≤ 1 := by
  have h : (n : ℝ) ≤ 70 := by exact_mod_cast hn
  unfold densityExponent
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith


/-- The `e`-th coordinate of a product law has law `ν_e` (dependent coordinates). -/
theorem expect_pi_coord {E : Type*} [Fintype E] [DecidableEq E] {I : E → Type*}
    [∀ e, Fintype (I e)] (ν : ∀ e, FiniteLaw (I e)) (e : E) (f : I e → ℝ) :
    (FiniteLaw.pi ν).expect (fun ω => f (ω e)) = (ν e).expect f := by
  have h := FiniteLaw.expect_pi_product ν (fun i x => if h : i = e then f (h ▸ x) else 1)
  have hl : ∀ ω : ∀ i, I i, ∏ i, (if h : i = e then f (h ▸ ω i) else 1) = f (ω e) := by
    intro ω
    rw [Finset.prod_eq_single e]
    · simp
    · intro i _ hi
      simp [hi]
    · intro he
      exact absurd (mem_univ e) he
  have hr : ∏ i, (ν i).expect (fun x => if h : i = e then f (h ▸ x) else 1) = (ν e).expect f := by
    rw [Finset.prod_eq_single e]
    · simp
    · intro i _ hi
      simp [hi]
    · intro he
      exact absurd (mem_univ e) he
  rw [← hr, ← h]
  exact (FiniteLaw.pi ν).expect_congr fun ω => (hl ω).symm

/-- **The paper's route** (`prop:density:production`, `31_density_induction_upgrade.tex:540–548`,
with `lem:density:coupled` and `def:hyb:coupled`): the index is `ω = (ω_e)_e`, one coordinate per
production query, under the product law `⊗_e ν_e` of `def:hyb:coupled`; the two slots of `e` are
`slotOf (e, true)`, `slotOf (e, false)`. Assume
* (G) **the labels are integrated first** (the output of the complementary geometric means,
  `lem:density:coupled`): for every index `ω`,
  `E_z ∏_{v changed} α_f(ω,v,z_v)^u ≤ ∏_{v changed} (E_z α_f(ω,v,z_v))^u`;
* (L) the fibre-density means `E_z α_f(ω, slotOf (e,s), ·)` are functions `a e s (ω_e)` of the
  query's own index.
Then `E ∏_{v changed} α_f^u ≤ ∏_{v changed} ᾱ_v^u` for `2u ≤ 1`, using only the independence of
distinct query indices (`expect_pi_product`) and the two-slot Cauchy–Schwarz bound
`expect_rpow_mul_rpow_le` at each query. -/
theorem production_pairs_of_index {E : Type*} [Fintype E] [DecidableEq E] {I : E → Type*}
    [∀ e, Fintype (I e)] [∀ e, DecidableEq (I e)] [∀ e, Nonempty (I e)] (ν : ∀ e, FiniteLaw (I e)) (ρ : (Slot → XE) → ℝ)
    (αf : (∀ e, I e) → Slot → XE → ℝ) (hαf : ∀ ω v z, 0 ≤ αf ω v z)
    (changed : Slot → Prop) [DecidablePred changed] (slotOf : E × Bool ≃ {v // changed v})
    (a : ∀ e, Bool → I e → ℝ) {u : ℝ} (hu : 0 ≤ u) (hu2 : 2 * u ≤ 1) (αbar : Slot → ℝ)
    (hρ : 0 < totalVariation ρ)
    (hlabel : ∀ ω, (variationLaw ρ hρ).expect
        (fun z => ∏ v ∈ univ.filter changed, αf ω v (z v) ^ u) ≤
      ∏ v ∈ univ.filter changed, (variationLaw ρ hρ).expect (fun z => αf ω v (z v)) ^ u)
    (hloc : ∀ ω e s, (variationLaw ρ hρ).expect (fun z => αf ω (slotOf (e, s)) (z (slotOf (e, s))))
      = a e s (ω e))
    (hmean : ∀ v, changed v →
      ((FiniteLaw.pi ν).product (variationLaw ρ hρ)).expect (fun p => αf p.1 v (p.2 v)) =
        αbar v) :
    ((FiniteLaw.pi ν).product (variationLaw ρ hρ)).expect
        (fun p => ∏ v ∈ univ.filter changed, αf p.1 v (p.2 v) ^ u) ≤
      ∏ v ∈ univ.filter changed, αbar v ^ u := by
  set lz := variationLaw ρ hρ
  have hre : ∀ (F : Slot → ℝ), ∏ v ∈ univ.filter changed, F v =
      ∏ e, (F (slotOf (e, true)) * F (slotOf (e, false))) := by
    intro F
    rw [Finset.prod_subtype (p := changed) (univ.filter changed) (fun x => by simp) F,
      ← slotOf.prod_comp (fun v : {v // changed v} => F v.1), Fintype.prod_prod_type]
    exact prod_congr rfl fun e _ => by rw [Fintype.prod_bool]
  have ha0 : ∀ e s x, 0 ≤ a e s x := by
    intro e s x
    obtain ⟨ω₀⟩ : Nonempty (∀ e, I e) := inferInstance
    have := hloc (Function.update ω₀ e x) e s
    rw [Function.update_self] at this
    rw [← this]
    exact lz.expect_nonneg fun z => hαf _ _ _
  -- (G), then (L)
  have hstep1 : ((FiniteLaw.pi ν).product lz).expect
      (fun p => ∏ v ∈ univ.filter changed, αf p.1 v (p.2 v) ^ u) ≤
      (FiniteLaw.pi ν).expect (fun ω => ∏ e, (a e true (ω e) ^ u * a e false (ω e) ^ u)) := by
    rw [FiniteLaw.expect_product]
    apply (FiniteLaw.pi ν).expect_mono
    intro ω
    refine (hlabel ω).trans (le_of_eq ?_)
    rw [hre (fun v => lz.expect (fun z => αf ω v (z v)) ^ u)]
    exact prod_congr rfl fun e _ => by rw [hloc ω e true, hloc ω e false]
  -- independence of distinct query indices
  rw [FiniteLaw.expect_pi_product ν (fun e x => a e true x ^ u * a e false x ^ u)] at hstep1
  refine hstep1.trans ?_
  -- the means
  have hmean' : ∀ e s, (ν e).expect (a e s) = αbar (slotOf (e, s)) := by
    intro e s
    rw [← hmean _ (slotOf (e, s)).2, FiniteLaw.expect_product]
    have : (FiniteLaw.pi ν).expect (fun ω => lz.expect (fun z => αf ω (slotOf (e, s))
        (z (slotOf (e, s))))) = (FiniteLaw.pi ν).expect (fun ω => a e s (ω e)) :=
      (FiniteLaw.pi ν).expect_congr fun ω => hloc ω e s
    rw [this]
    exact (expect_pi_coord ν e (a e s)).symm
  rw [hre (fun v => αbar v ^ u)]
  apply prod_le_prod₀
  · intro e _
    exact (ν e).expect_nonneg fun x => mul_nonneg (Real.rpow_nonneg (ha0 e true x) _)
      (Real.rpow_nonneg (ha0 e false x) _)
  · intro e _
    have h := expect_rpow_mul_rpow_le (ν e) (ha0 e true) (ha0 e false) hu hu2
    rw [hmean' e true, hmean' e false] at h
    refine h.trans (le_of_eq ?_)
    have h1 : 0 ≤ αbar (slotOf (e, true)) := by rw [← hmean' e true]; exact (ν e).expect_nonneg (ha0 e true)
    have h2 : 0 ≤ αbar (slotOf (e, false)) := by rw [← hmean' e false]; exact (ν e).expect_nonneg (ha0 e false)
    exact Real.mul_rpow h1 h2

/-- **`prop:density:production` from the coupled index law** (all slots may change): the
conclusion of `density_structured_theta` for an index law that is a product over the production
queries (`def:hyb:coupled`), assuming (G) the label integration and (L) the locality of the
fibre-density means of `production_pairs_of_index`, instead of WP-R's `hindep`. Only the
independence of distinct query indices is used. -/
theorem density_structured_theta_index (μS : FiniteLaw (Slot → X))
    (hμS : SlotReflectionPositive (signedIntegral μS.weight))
    {E : Type*} [Fintype E] [DecidableEq E] {I : E → Type*} [∀ e, Fintype (I e)]
    [∀ e, DecidableEq (I e)] [∀ e, Nonempty (I e)] (ν : ∀ e, FiniteLaw (I e))
    (ρ : (Slot → XE) → ℝ) (g gt : (∀ e, I e) → Slot → XE → X → ℝ)
    (changed : Slot → Prop) [DecidablePred changed]
    {Y C0 a θ L α u Cdc σ : ℝ} (hC0 : 0 ≤ C0) (ha : 0 ≤ a) (hθ0 : 0 ≤ θ)
    (hθ2 : 2 * (θ / 72) ≤ 1)
    (hL : 0 < L) (hα : 0 < α) (hu : 0 ≤ u) (hY : 0 ≤ Y)
    (hlow : C0 * L ^ (-a) * α ^ θ < Y)
    (ξ αbar : Slot → ℝ) (hξ : ∀ v, 1 ≤ ξ v) (hαbar : ∀ v, 0 ≤ αbar v)
    (hun : ∀ v, ¬changed v → ∀ ω z, referenceEnergy μS (gt ω v z) ≤ Y)
    (αf : (∀ e, I e) → Slot → XE → ℝ) (hαf : ∀ ω v z, 0 ≤ αf ω v z)
    (hch : ∀ v, changed v → ∀ ω z,
      referenceEnergy μS (gt ω v z) ≤ (1 + u) * C0 * L ^ (-a) * ξ v ^ a * αf ω v z ^ θ)
    (hmean : ∀ hρ : 0 < totalVariation ρ, ∀ v, changed v →
      ((FiniteLaw.pi ν).product (variationLaw ρ hρ)).expect (fun p => αf p.1 v (p.2 v)) =
        αbar v)
    (slotOf : E × Bool ≃ {v // changed v}) (afib : ∀ e, Bool → I e → ℝ)
    (hlabel : ∀ hρ : 0 < totalVariation ρ, ∀ ω, (variationLaw ρ hρ).expect
        (fun z => ∏ v ∈ univ.filter changed, αf ω v (z v) ^ (θ / 72)) ≤
      ∏ v ∈ univ.filter changed, (variationLaw ρ hρ).expect (fun z => αf ω v (z v)) ^ (θ / 72))
    (hloc : ∀ hρ : 0 < totalVariation ρ, ∀ ω e s, (variationLaw ρ hρ).expect
      (fun z => αf ω (slotOf (e, s)) (z (slotOf (e, s)))) = afib e s (ω e))
    (hdc : |structuredEnergy μS (FiniteLaw.pi ν) ρ g - structuredEnergy μS (FiniteLaw.pi ν) ρ gt|
      ≤ Cdc * totalVariation ρ * L ^ (-σ) * α) :
    |structuredEnergy μS (FiniteLaw.pi ν) ρ g| ≤
      totalVariation ρ * ((1 + u) * mainPrice ξ αbar changed a θ α * Y +
        Cdc * L ^ (-σ) * α) :=
  density_structured_theta_of_pairs μS hμS (FiniteLaw.pi ν) ρ g gt changed hC0 ha hL hα hu hY
    hlow ξ αbar hξ hαbar hun αf hαf hch
    (fun hρ => production_pairs_of_index ν ρ αf hαf changed slotOf afib (by positivity) hθ2 αbar
      hρ (hlabel hρ) (hloc hρ) (hmean hρ)) hdc

/-- **WP-R's two-occurrence hypothesis implies the product bound**: `ProductionTwoOccurrence`
(with `2θ/72 ≤ 1` and the means `hmean`) gives the hypothesis `hpairs` of
`density_structured_theta_of_pairs` (this is the `hpairs` step of WP-R's proof). So `hpairs` is
weaker than `ProductionTwoOccurrence`. -/
theorem pairs_of_twoOccurrence (P : FiniteLaw Ω) (ρ : (Slot → XE) → ℝ)
    (αf : Ω → Slot → XE → ℝ) (hαf : ∀ ω v z, 0 ≤ αf ω v z) (changed : Slot → Prop)
    [DecidablePred changed] {E : Type*} [Fintype E] [DecidableEq E] {src tgt : E → Slot}
    (hprod : ProductionTwoOccurrence P ρ αf changed src tgt) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ2 : 2 * (θ / 72) ≤ 1) (αbar : Slot → ℝ) (hαbar : ∀ v, 0 ≤ αbar v)
    (hmean : ∀ hρ : 0 < totalVariation ρ, ∀ v, changed v →
      (P.product (variationLaw ρ hρ)).expect (fun p => αf p.1 v (p.2 v)) = αbar v)
    (hρ : 0 < totalVariation ρ) :
    (P.product (variationLaw ρ hρ)).expect
        (fun p => ∏ v ∈ univ.filter changed, αf p.1 v (p.2 v) ^ (θ / 72)) ≤
      ∏ v ∈ univ.filter changed, αbar v ^ (θ / 72) := by
  set Jt := P.product (variationLaw ρ hρ)
  set slotOf := hprod.slotOf
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
            αf p.1 (slotOf (e, false)) (p.2 (slotOf (e, false))) ^ (θ / 72)) := hprod.hindep θ hρ
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
        exact prod_congr rfl fun e _ => Real.mul_rpow (hαbar _) (hαbar _)

/-- **(G) from label-pair independence**: if, for a fixed index `ω`, the pairs of labels at the two
slots of distinct queries are independent under the label law `λ` (the label part of WP-R's
`ProductionTwoOccurrence.indep`), then the label integration bound (G) of
`production_pairs_of_index` holds (for `2u ≤ 1`). So (G) is implied by WP-R's label
independence, and it is also implied by `|changed| u ≤ 1` (`expect_prod_rpow_le_prod`). -/
theorem label_bound_of_pair_indep {E : Type*} [Fintype E] [DecidableEq E]
    (lz : FiniteLaw (Slot → XE)) (f : Slot → XE → ℝ) (hf : ∀ v x, 0 ≤ f v x)
    (changed : Slot → Prop) [DecidablePred changed] (slotOf : E × Bool ≃ {v // changed v})
    {u : ℝ} (hu : 0 ≤ u) (hu2 : 2 * u ≤ 1)
    (hindep : lz.expect (fun z => ∏ e, (f (slotOf (e, true)) (z (slotOf (e, true))) ^ u *
        f (slotOf (e, false)) (z (slotOf (e, false))) ^ u)) =
      ∏ e, lz.expect (fun z => f (slotOf (e, true)) (z (slotOf (e, true))) ^ u *
        f (slotOf (e, false)) (z (slotOf (e, false))) ^ u)) :
    lz.expect (fun z => ∏ v ∈ univ.filter changed, f v (z v) ^ u) ≤
      ∏ v ∈ univ.filter changed, lz.expect (fun z => f v (z v)) ^ u := by
  have hre : ∀ (F : Slot → ℝ), ∏ v ∈ univ.filter changed, F v =
      ∏ e, (F (slotOf (e, true)) * F (slotOf (e, false))) := by
    intro F
    rw [Finset.prod_subtype (p := changed) (univ.filter changed) (fun x => by simp) F,
      ← slotOf.prod_comp (fun v : {v // changed v} => F v.1), Fintype.prod_prod_type]
    exact prod_congr rfl fun e _ => by rw [Fintype.prod_bool]
  rw [lz.expect_congr fun z => hre (fun v => f v (z v) ^ u), hindep,
    hre (fun v => lz.expect (fun z => f v (z v)) ^ u)]
  apply prod_le_prod₀
  · intro e _
    exact lz.expect_nonneg fun z => mul_nonneg (Real.rpow_nonneg (hf _ _) _)
      (Real.rpow_nonneg (hf _ _) _)
  · intro e _
    have h := expect_rpow_mul_rpow_le lz (A := fun z => f (slotOf (e, true)) (z (slotOf (e, true))))
      (B := fun z => f (slotOf (e, false)) (z (slotOf (e, false)))) (fun z => hf _ _)
      (fun z => hf _ _) hu hu2
    refine h.trans (le_of_eq ?_)
    exact Real.mul_rpow (lz.expect_nonneg fun z => hf _ _) (lz.expect_nonneg fun z => hf _ _)

/-- **(G) is a genuine input when too many slots change**: on any finite set `S` of slots with
`|S| u > 1`, there is a label law (a fair bit shared by all slots) and nonnegative `f` with
`E ∏_v f_v^u > ∏_v (E f_v)^u`. At `u = θ/72` with all 72 slots changed and `θ > 1`, this is a
failure of (G), hence of `hpairs` for a one-point index law: the pointwise hypotheses of
`density_structured_theta` and a product index law do not give `hpairs` without structure on the
labels (the paper supplies it by `lem:density:coupled`). -/
theorem label_bound_fails {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S] {u : ℝ}
    (hu : 0 < u) (hSu : 1 < (Fintype.card S : ℝ) * u) :
    ∃ lz : FiniteLaw (S → Bool), ∃ f : S → Bool → ℝ, (∀ v b, 0 ≤ f v b) ∧
      ∏ v, lz.expect (fun z => f v (z v)) ^ u < lz.expect (fun z => ∏ v, f v (z v) ^ u) := by
  set T : S → Bool := fun _ => true
  set F : S → Bool := fun _ => false
  obtain ⟨v₀⟩ : Nonempty S := inferInstance
  have hTF : T ≠ F := fun h => by
    have := congrFun h v₀
    simp [T, F] at this
  let lz : FiniteLaw (S → Bool) :=
    { weight := fun z => (if z = T then 1 / 2 else 0) + (if z = F then 1 / 2 else 0)
      nonneg := fun z => by
        apply add_nonneg <;> split_ifs <;> norm_num
      total := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
        simp only [mem_univ, ite_true]
        norm_num }
  have hexp : ∀ g : (S → Bool) → ℝ, lz.expect g = 1 / 2 * g T + 1 / 2 * g F := by
    intro g
    simp only [FiniteLaw.expect, lz, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
      Finset.sum_ite_eq', mem_univ, ite_true]
  refine ⟨lz, fun _ b => if b then 1 else 0, fun v b => by beta_reduce; split_ifs <;> norm_num, ?_⟩
  have h1 : ∀ v, lz.expect (fun z => if z v then (1 : ℝ) else 0) = 1 / 2 := by
    intro v
    rw [hexp]
    simp [T, F]
  have h2 : lz.expect (fun z => ∏ v, (if z v then (1 : ℝ) else 0) ^ u) = 1 / 2 := by
    rw [hexp]
    have hT1 : ∏ v, (if T v then (1 : ℝ) else 0) ^ u = 1 := by simp [T]
    have hF0 : ∏ v, (if F v then (1 : ℝ) else 0) ^ u = 0 := by
      apply Finset.prod_eq_zero (mem_univ v₀)
      simp [F, Real.zero_rpow hu.ne']
    rw [hT1, hF0]
    ring
  simp only [h1, h2]
  rw [Finset.prod_const, card_univ, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have hlt := Real.rpow_lt_rpow_of_exponent_gt (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 : ℝ) / 2 < 1) (by linarith [hSu] : (1 : ℝ) < u * Fintype.card S)
  rw [Real.rpow_one] at hlt
  exact hlt

/-- **Two occurrences and few queries need no independence**: if the changed slots are indexed by
`E × Bool` (part (a) of `ProductionTwoOccurrence`, e.g. via `ProductionTwoOccurrence.slotOf`) and
`2|E| θ/72 ≤ 1` — at `θ = densityExponent`, `|E| ≤ 35`; the paper's six queries `𝓔_6` give
`2|E| = 12` — then the conclusion of `density_structured_theta` holds without part (b). -/
theorem density_structured_theta_two_occ (μS : FiniteLaw (Slot → X))
    (hμS : SlotReflectionPositive (signedIntegral μS.weight)) (P : FiniteLaw Ω)
    (ρ : (Slot → XE) → ℝ) (g gt : Ω → Slot → XE → X → ℝ)
    (changed : Slot → Prop) [DecidablePred changed]
    {Y C0 a θ L α u Cdc σ : ℝ} (hC0 : 0 ≤ C0) (ha : 0 ≤ a) (hθ0 : 0 ≤ θ)
    {E : Type*} [Fintype E] (slotOf : E × Bool ≃ {v // changed v})
    (hE : 2 * (Fintype.card E : ℝ) * (θ / 72) ≤ 1)
    (hL : 0 < L) (hα : 0 < α) (hu : 0 ≤ u) (hY : 0 ≤ Y)
    (hlow : C0 * L ^ (-a) * α ^ θ < Y)
    (ξ αbar : Slot → ℝ) (hξ : ∀ v, 1 ≤ ξ v) (hαbar : ∀ v, 0 ≤ αbar v)
    (hun : ∀ v, ¬changed v → ∀ ω z, referenceEnergy μS (gt ω v z) ≤ Y)
    (αf : Ω → Slot → XE → ℝ) (hαf : ∀ ω v z, 0 ≤ αf ω v z)
    (hch : ∀ v, changed v → ∀ ω z,
      referenceEnergy μS (gt ω v z) ≤ (1 + u) * C0 * L ^ (-a) * ξ v ^ a * αf ω v z ^ θ)
    (hmean : ∀ hρ : 0 < totalVariation ρ, ∀ v, changed v →
      (P.product (variationLaw ρ hρ)).expect (fun p => αf p.1 v (p.2 v)) = αbar v)
    (hdc : |structuredEnergy μS P ρ g - structuredEnergy μS P ρ gt| ≤
      Cdc * totalVariation ρ * L ^ (-σ) * α) :
    |structuredEnergy μS P ρ g| ≤
      totalVariation ρ * ((1 + u) * mainPrice ξ αbar changed a θ α * Y +
        Cdc * L ^ (-σ) * α) := by
  have hcard : ((univ.filter changed).card : ℝ) = 2 * (Fintype.card E : ℝ) := by
    have h1 : (univ.filter changed).card = Fintype.card {v // changed v} :=
      (Fintype.card_subtype changed).symm
    have h2 : Fintype.card {v // changed v} = Fintype.card E * 2 := by
      rw [← Fintype.card_congr slotOf, Fintype.card_prod, Fintype.card_bool]
    rw [h1, h2]
    push_cast
    ring
  exact density_structured_theta_few μS hμS P ρ g gt changed hC0 ha hθ0 (by rw [hcard]; exact hE)
    hL hα hu hY hlow ξ αbar hξ hαbar hun αf hαf hch hmean hdc

end Sarkozy.TraceMixing
