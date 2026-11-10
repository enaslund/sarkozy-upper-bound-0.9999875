module

public import Sarkozy.Structured.FibreSlot
public import Sarkozy.Structured.Counterexample

/-!
# The density-structured energy estimate (`prop:record:density-structured`)

`prop:record:density-structured` of the paper (`paper/sections/08_scale_comparison.tex`):
at a least normalized counterexample `(L, A)` for `(a, θ, C₀)`, `L ≥ L_*`,
`Y = Y(L, A)`, every structured energy satisfies

  `|𝔈| ≤ ‖ρ‖ [(1 + u_L) Π_main Y + C_dc L^{-σ} α]
       ≤ ‖ρ‖ (1 + u_L + (C_dc/C₀) L^{a-σ} α^{1-θ}) Π Y`.

The proof is assembled from the steps formalized in `MainTerm` and `FibreSlot`:

1. `lem:record:density-dc` replaces `𝔈` by the energy `𝔈̃` of the square-step
   models, with additive error `C_dc ‖ρ‖ L^{-σ} α`. **This lemma is a hypothesis**
   (`hdc`); it needs `lem:record:prefix-conductor` and the lift moments.
2. For fixed `(ω, z)`, the signed Hölder inequality, and Hölder with 72 equal
   exponents over `(ω, z)` (`abs_structuredEnergy_le_of_slot_bounds`).
3. At an unchanged slot `Z_𝒮(F_A) = Y` (hypothesis `hun`, an inequality `≤ Y`).
4. At a changed slot, the per-sample bound `Z_𝒮(g̃) ≤ (1 + u) C₀ L^{-a} ξ^a α_f^θ`
   (hypothesis `hch`, which `changed_slot_bound` derives from the fibre data),
   Jensen's inequality and `E α_f = ᾱ` (hypothesis `hmean`), and
   `C₀ L^{-a} α^θ < Y`.

`mainPrice ξ ᾱ changed a θ α` is `Π_main = ∏_v ξ_v^{a/72} ∏_{v changed} (ᾱ_v/α)^{θ/72}`.
The theorem `density_structured` is the abstract form, with real parameters.
`density_structured_counterexample` takes `Y`, `α` and the lower bound from a least
normalized counterexample (`def:record:counterexample`).
`density_structured_coarse` is the second inequality, for any coarse price
`Π ≥ max(1, Π_main)`.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.Structured

/-- The main price `Π_main = ∏_v ξ_v^{a/72} ∏_{v changed} (ᾱ_v/α)^{θ/72}`. -/
noncomputable def mainPrice (ξ αbar : Slot → ℝ) (changed : Slot → Prop) [DecidablePred changed]
    (a θ α : ℝ) : ℝ :=
  (∏ v, ξ v ^ (a / 72)) * ∏ v ∈ univ.filter changed, (αbar v / α) ^ (θ / 72)

variable {X XE Ω : Type*} [Fintype X] [Fintype XE] [Fintype Ω]

/-- The product over the 72 slots of `c^{1/72}` is `c`. -/
theorem prod_slot_rpow (c : ℝ) (hc : 0 ≤ c) : ∏ _v : Slot, c ^ ((1 : ℝ) / 72) = c := by
  rw [prod_const, card_univ, card_slot, ← Real.rpow_natCast, ← Real.rpow_mul hc]
  norm_num

/-- **`prop:record:density-structured`, abstract form.** -/
theorem density_structured (μS : FiniteLaw (Slot → X))
    (hμS : SlotReflectionPositive (signedIntegral μS.weight)) (P : FiniteLaw Ω)
    (ρ : (Slot → XE) → ℝ) (g gt : Ω → Slot → XE → X → ℝ)
    (changed : Slot → Prop) [DecidablePred changed]
    {Y C0 a θ L α u Cdc σ : ℝ} (hC0 : 0 ≤ C0) (ha : 0 ≤ a) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
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
  rcases (totalVariation_nonneg ρ).lt_or_eq with hρ | hρ0
  · -- the main term
    set Jt := P.product (variationLaw ρ hρ)
    set c : Slot → ℝ := fun v =>
      (1 + u) * Y * ξ v ^ a * (if changed v then (αbar v / α) ^ θ else 1) with hcdef
    have hξ0 : ∀ v, 0 ≤ ξ v := fun v => le_trans zero_le_one (hξ v)
    have hξa : ∀ v, 1 ≤ ξ v ^ a := fun v => Real.one_le_rpow (hξ v) ha
    have hc0 : ∀ v, 0 ≤ c v := by
      intro v
      simp only [hcdef]
      apply mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hY) (le_trans zero_le_one (hξa v)))
      split_ifs
      · exact Real.rpow_nonneg (div_nonneg (hαbar v) hα.le) _
      · exact zero_le_one
    have hslot : ∀ v, Jt.expect (fun p => referenceEnergy μS (gt p.1 v (p.2 v))) ≤ c v := by
      intro v
      by_cases hv : changed v
      · have hK : 0 ≤ (1 + u) * C0 * L ^ (-a) * ξ v ^ a :=
          mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hC0) (Real.rpow_nonneg hL.le _))
            (Real.rpow_nonneg (hξ0 v) _)
        have h1 := expect_changed_slot_bound Jt μS (fun p => gt p.1 v (p.2 v))
          (fun p => αf p.1 v (p.2 v)) (fun p => hαf _ _ _) hK hθ0 hθ1
          (fun p => hch v hv p.1 (p.2 v)) (hmean hρ v hv)
        refine h1.trans ?_
        simp only [hcdef, hv, ↓reduceIte]
        -- `C₀ L^{-a} ᾱ^θ ≤ Y (ᾱ/α)^θ`
        have hsplit : αbar v ^ θ = α ^ θ * (αbar v / α) ^ θ := by
          rw [← Real.mul_rpow hα.le (div_nonneg (hαbar v) hα.le), mul_div_cancel₀ _ hα.ne']
        rw [hsplit]
        have hr : 0 ≤ (αbar v / α) ^ θ := Real.rpow_nonneg (div_nonneg (hαbar v) hα.le) _
        have hY' : C0 * L ^ (-a) * α ^ θ * (αbar v / α) ^ θ ≤ Y * (αbar v / α) ^ θ :=
          mul_le_mul_of_nonneg_right hlow.le hr
        have hpre : 0 ≤ (1 + u) * ξ v ^ a :=
          mul_nonneg (by linarith) (Real.rpow_nonneg (hξ0 v) _)
        have := mul_le_mul_of_nonneg_left hY' hpre
        calc (1 + u) * C0 * L ^ (-a) * ξ v ^ a * (α ^ θ * (αbar v / α) ^ θ)
            = (1 + u) * ξ v ^ a * (C0 * L ^ (-a) * α ^ θ * (αbar v / α) ^ θ) := by ring
          _ ≤ (1 + u) * ξ v ^ a * (Y * (αbar v / α) ^ θ) := this
          _ = (1 + u) * Y * ξ v ^ a * (αbar v / α) ^ θ := by ring
      · have h1 : Jt.expect (fun p => referenceEnergy μS (gt p.1 v (p.2 v))) ≤ Y :=
          Jt.expect_le_const fun p => hun v hv p.1 (p.2 v)
        refine h1.trans ?_
        simp only [hcdef, hv, ↓reduceIte, mul_one]
        have h2 : Y ≤ Y * ξ v ^ a := le_mul_of_one_le_right hY (hξa v)
        have h3 : Y * ξ v ^ a ≤ (1 + u) * (Y * ξ v ^ a) :=
          le_mul_of_one_le_left (mul_nonneg hY (le_trans zero_le_one (hξa v))) (by linarith)
        linarith
    have hmain := abs_structuredEnergy_le_of_slot_bounds μS hμS P ρ hρ gt c hslot
    -- evaluate `∏_v c_v^{1/72}`
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
    rw [hprod] at hmain
    have htri : |structuredEnergy μS P ρ g| ≤
        |structuredEnergy μS P ρ gt| + |structuredEnergy μS P ρ g - structuredEnergy μS P ρ gt| := by
      have := abs_sub_abs_le_abs_sub (structuredEnergy μS P ρ g) (structuredEnergy μS P ρ gt)
      linarith
    calc |structuredEnergy μS P ρ g|
        ≤ totalVariation ρ * ((1 + u) * mainPrice ξ αbar changed a θ α * Y) +
            Cdc * totalVariation ρ * L ^ (-σ) * α := by linarith
      _ = _ := by ring
  · -- `ρ = 0`
    rw [structuredEnergy_eq_zero_of_totalVariation μS P ρ hρ0.symm g, ← hρ0]
    simp

/-- **`prop:record:density-structured` at a least normalized counterexample**: with
`Y = Y(L, A)`, `α = |A|/N` and the hypothesis on smaller scales built into the
per-sample bound `hch` (for instance through `changed_slot_bound`). -/
theorem density_structured_counterexample {Yf : ℕ → Finset ℤ → ℝ} {a θ C0 : ℝ} {L : ℕ}
    {A : Finset ℤ} (hcex : IsLeastCounterexample Yf a θ C0 L A) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
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
  exact density_structured μS hμS P ρ g gt changed hC0 ha hθ.le hθ1
    (by exact_mod_cast hL) hα hu hYpos hlow ξ αbar hξ hαbar hun αf hαf hch hmean hdc

/-- **The second inequality of `prop:record:density-structured`**: for a coarse price
`Π ≥ max(1, Π_main)` and `C₀ > 0`,
`|𝔈| ≤ ‖ρ‖ (1 + u + (C_dc/C₀) L^{a-σ} α^{1-θ}) Π Y`. -/
theorem density_structured_coarse {E Y C0 a θ L α u Cdc σ Pm Pc ρn : ℝ}
    (hE : |E| ≤ ρn * ((1 + u) * Pm * Y + Cdc * L ^ (-σ) * α)) (hρn : 0 ≤ ρn)
    (hC0 : 0 < C0) (hL : 0 < L) (hα : 0 < α) (hu : 0 ≤ u) (hY : 0 ≤ Y) (hCdc : 0 ≤ Cdc)
    (hlow : C0 * L ^ (-a) * α ^ θ < Y) (hPm : Pm ≤ Pc) (hP1 : 1 ≤ Pc) :
    |E| ≤ ρn * (1 + u + Cdc / C0 * L ^ (a - σ) * α ^ (1 - θ)) * Pc * Y := by
  have hsplit : Cdc * L ^ (-σ) * α =
      Cdc / C0 * L ^ (a - σ) * α ^ (1 - θ) * (C0 * L ^ (-a) * α ^ θ) := by
    have h1 : L ^ (a - σ) * L ^ (-a) = L ^ (-σ) := by
      rw [← Real.rpow_add hL]; ring_nf
    have h2 : α ^ (1 - θ) * α ^ θ = α := by
      rw [← Real.rpow_add hα]; simp
    calc Cdc * L ^ (-σ) * α = Cdc * (L ^ (a - σ) * L ^ (-a)) * (α ^ (1 - θ) * α ^ θ) := by
          rw [h1, h2]
      _ = _ := by field_simp
  have hk : 0 ≤ Cdc / C0 * L ^ (a - σ) * α ^ (1 - θ) :=
    mul_nonneg (mul_nonneg (div_nonneg hCdc hC0.le) (Real.rpow_nonneg hL.le _))
      (Real.rpow_nonneg hα.le _)
  have h1 : Cdc * L ^ (-σ) * α ≤ Cdc / C0 * L ^ (a - σ) * α ^ (1 - θ) * (Pc * Y) := by
    rw [hsplit]
    apply mul_le_mul_of_nonneg_left _ hk
    calc C0 * L ^ (-a) * α ^ θ ≤ Y := hlow.le
      _ ≤ Pc * Y := le_mul_of_one_le_left hY hP1
  have h2 : (1 + u) * Pm * Y ≤ (1 + u) * Pc * Y :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPm (by linarith)) hY
  calc |E| ≤ ρn * ((1 + u) * Pm * Y + Cdc * L ^ (-σ) * α) := hE
    _ ≤ ρn * ((1 + u) * Pc * Y + Cdc / C0 * L ^ (a - σ) * α ^ (1 - θ) * (Pc * Y)) := by
        apply mul_le_mul_of_nonneg_left _ hρn
        linarith
    _ = ρn * (1 + u + Cdc / C0 * L ^ (a - σ) * α ^ (1 - θ)) * Pc * Y := by ring

end Sarkozy.Structured
