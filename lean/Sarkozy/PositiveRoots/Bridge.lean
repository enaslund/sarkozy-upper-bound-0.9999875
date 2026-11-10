module

public import Sarkozy.PositiveRoots.Moments
public import Sarkozy.PositiveRoots.Layer
public import Sarkozy.PositiveRoots.RootProduct
public import Sarkozy.L20Cap.Rectangle
public import Sarkozy.ProbabilityConstructions

@[expose] public section

/-!
# Links between the chamber side and the layer side

* `h0_eq_layer`: the bound `h₀` produced by `Moments.root_normalization_b`,
  `(qr + 36q(2 + r) + 2qr/(1 − q))/(1 − 36q)`, is the paper's
  `h₀ = (72q + 37qr + 2qr/(1 − q))/(1 − 36q)` (`Layer.h0`, `lem:root-normalization`(b)).
* `cond_expect_eq_ratio`: the expectation under the conditional law `Peyre.condLaw μ G`
  (`λ_p(G_{L,2})` as the root before global injectivity conditioned on injectivity) is the ratio
  of filtered sums used in `Moments`.
* **`product_moments`**: if a score is `H(π₁ω₁, π₂ω₂)` under a product law `μ₁ ⊗ μ₂`, where each
  `πᵢ` has the uniform law of the ordered distinct pairs as its image, then `E H = qr` and
  `E H² = (n − 2)²/n² + (n − 3)²/(n²(n − 1))`. This is the step "each score pairs two independent
  uniform ordered distinct pairs" of the proof of `lem:root-normalization`(b), given the uniform
  marginals of the two component laws (which are not formalized here);
* **`gamma0_tilt_mass`**: for the actual `Γ_{p,0} = λ_p(G_{L,2})`, the mass step of
  `prop:root-layer`, `E_{Γ_{p,0}} w_u ≥ z^ι_u`, from `RootProduct.gamma0_score_bounds`, given only
  the coincidence counts of the proof of `lem:root-normalization`(b) for the three scores;
* **`tilt_mass_of_moments`**: `lem:root-normalization`(b) feeds the mass step of
  `prop:root-layer`: under the hypotheses of `root_normalization_b` for the three scores
  `H_j = PartV.rootScore p j` (the coincidence counts, `E_μH_j = qr`, `E_μH_j² ≥ 1 − 4q`), the
  conditioned law `Γ_{p,0} = μ(· | G)` has `E_{Γ_{p,0}} w_u ≥ z^ι_u` (`Layer.tilt_mass_ge_zI`).
-/

namespace Sarkozy.PositiveRoots

open Finset Sarkozy Sarkozy.Peyre

/-- `h₀` of `root_normalization_b` equals `Layer.h0`. -/
theorem h0_eq_layer (q r : ℝ) :
    (q * r + 36 * q * (2 + r) + 2 * q * r / (1 - q)) / (1 - 36 * q) = Layer.h0 q r := by
  unfold Layer.h0
  ring

theorem filter_sum_eq_ind {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (G : Ω → Prop)
    [DecidablePred G] (u : Ω → ℝ) :
    ∑ ω ∈ univ.filter G, μ.weight ω * u ω = μ.expect (fun ω => ind G ω * u ω) := by
  unfold FiniteLaw.expect
  rw [Finset.sum_filter]
  refine sum_congr rfl fun ω _ => ?_
  by_cases h : G ω
  · simp only [h, ↓reduceIte, ind_of_pos h, one_mul]
  · simp only [h, ↓reduceIte, ind_of_neg h, zero_mul, mul_zero]

theorem prob_eq_filter_sum {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (G : Ω → Prop)
    [DecidablePred G] : prob μ G = ∑ ω ∈ univ.filter G, μ.weight ω := by
  have h := filter_sum_eq_ind μ G (fun _ => 1)
  simp only [mul_one] at h
  rw [h]
  rfl

/-- The expectation under `μ(· | G)` is the ratio of the filtered sums. -/
theorem cond_expect_eq_ratio {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (G : Ω → Prop)
    [DecidablePred G] (hG : 0 < prob μ G) (u : Ω → ℝ) :
    (condLaw μ G hG).expect u =
      (∑ ω ∈ univ.filter G, μ.weight ω * u ω) / (∑ ω ∈ univ.filter G, μ.weight ω) := by
  rw [cond_expect, filter_sum_eq_ind, prob_eq_filter_sum]

/-- The good event has positive probability: `μ(G) ≥ 1 − 36q > 0`. -/
theorem prob_pos_of_bad_le {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (G : Ω → Prop)
    [DecidablePred G] {q : ℝ} (hq36 : 36 * q < 1)
    (hGc : ∑ ω ∈ univ.filter (fun ω => ¬ G ω), μ.weight ω ≤ 36 * q) : 0 < prob μ G := by
  rw [prob_eq_filter_sum]
  have h := Finset.sum_filter_add_sum_filter_not univ G (fun ω => μ.weight ω)
  rw [μ.total] at h
  linarith

/-- **`lem:root-normalization`(b) gives the mass step of `prop:root-layer`.** Let `μ` be the
twelve-label root before global injectivity and `G` the injectivity event, and suppose, for each
score `H_j = PartV.rootScore p j`, the hypotheses of `Moments.root_normalization_b` (with the spike
event `S j`). Then `Γ_{p,0} = μ(· | G)` has `E_{Γ_{p,0}} w_u ≥ z^ι_u` (`Layer.zI`) for every
rational `u ≥ 0`. -/
theorem tilt_mass_of_moments {p : ℕ} [Fact p.Prime] (μ : FiniteLaw (ZMod 6 × Fin 2 → ZMod p))
    (G : (ZMod 6 × Fin 2 → ZMod p) → Prop) [DecidablePred G]
    (S : Fin 3 → (ZMod 6 × Fin 2 → ZMod p) → Prop) [∀ j, DecidablePred (S j)]
    (u : ℚ) (hu : 0 ≤ u) {q r : ℝ} (hr : 0 < r) (hq : q = r ^ 2) (hq2 : q < 1 / 2)
    (hq36 : 36 * q < 1)
    (hGc : ∑ ω ∈ univ.filter (fun ω => ¬ G ω), μ.weight ω ≤ 36 * q)
    (hS : ∀ j, ∑ ω ∈ univ.filter (fun ω => ¬ G ω ∧ S j ω), μ.weight ω ≤ 2 * q ^ 2 / (1 - q))
    (hB : ∀ j ω, ¬ G ω → ¬ S j ω → |PartV.rootScore p j ω| ≤ 2 + r)
    (hA : ∀ j ω, ¬ G ω → S j ω →
      |PartV.rootScore p j ω| ≤ 1 / r ∧ PartV.rootScore p j ω ^ 2 ≤ (1 - 2 * q) ^ 2 / q)
    (hmean : ∀ j, μ.expect (PartV.rootScore p j) = q * r)
    (hsq : ∀ j, 1 - 4 * q ≤ μ.expect (fun ω => PartV.rootScore p j ω ^ 2)) :
    ∃ hG : 0 < prob μ G,
      Layer.zI (u : ℝ) q r ≤ (condLaw μ G hG).expect (PartV.individualWeight p u) := by
  have hG := prob_pos_of_bad_le μ G hq36 hGc
  refine ⟨hG, Layer.tilt_mass_ge_zI (condLaw μ G hG) u hu ?_ ?_⟩
  · intro j
    obtain ⟨h1, -⟩ := root_normalization_b μ G (S j) (PartV.rootScore p j) hr hq hq2 hq36 hGc
      (hS j) (hB j) (hA j) (hmean j) (hsq j)
    rw [cond_expect_eq_ratio, ← h0_eq_layer]
    exact h1
  · intro j
    obtain ⟨-, h2⟩ := root_normalization_b μ G (S j) (PartV.rootScore p j) hr hq hq2 hq36 hGc
      (hS j) (hB j) (hA j) (hmean j) (hsq j)
    rw [cond_expect_eq_ratio μ G hG (fun ω => PartV.rootScore p j ω ^ 2)]
    unfold Layer.BH
    exact h2

/-! ## The moments under a product law with uniform pair marginals -/

section ProductMoments

open Sarkozy.L20Cap

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Nonempty (PairT F)]

omit [Nonempty (PairT F)] in
theorem pairLaw_sum (g : F × F → ℝ) :
    ∑ b : PairT F, g b.1 = ∑ y ∈ distinctPairs F, g y := by
  unfold distinctPairs
  rw [Finset.sum_subtype (p := fun y : F × F => y.1 ≠ y.2) (univ.filter fun y : F × F => y.1 ≠ y.2)
    (fun y => by simp) g]

omit [Nonempty (PairT F)] in
theorem card_PairT_eq : (Fintype.card (PairT F) : ℝ) = ((distinctPairs F).card : ℝ) := by
  have h := pairLaw_sum (F := F) (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  exact h

/-- The expectation of `g(b₁, b₂)` for two independent uniform ordered distinct pairs. -/
theorem pairLaw_pair_expect (g : F × F → F × F → ℝ) :
    (pairLaw (F := F)).expect (fun b₁ => (pairLaw (F := F)).expect (fun b₂ => g b₁.1 b₂.1)) =
      (∑ y ∈ distinctPairs F, ∑ y' ∈ distinctPairs F, g y y') /
        ((distinctPairs F).card : ℝ) ^ 2 := by
  have hc : (0 : ℝ) < ((distinctPairs F).card : ℝ) := by
    rw [← card_PairT_eq]; exact_mod_cast Fintype.card_pos
  simp only [pairLaw, FiniteLaw.expect_uniform]
  rw [card_PairT_eq]
  have e : ∀ b₁ : PairT F, (∑ b₂ : PairT F, g b₁.1 b₂.1) = ∑ y' ∈ distinctPairs F, g b₁.1 y' :=
    fun b₁ => pairLaw_sum (g b₁.1)
  simp only [e]
  rw [← Finset.sum_div, pairLaw_sum (fun y => ∑ y' ∈ distinctPairs F, g y y')]
  field_simp

/-- **The score moments under a product law with uniform pair marginals**
(`lem:root-normalization`(b)): if `πᵢ : Ωᵢ → PairT F` push `μᵢ` forward to the uniform law of the
ordered distinct pairs, then under `μ₁ ⊗ μ₂` the score `H = H(π₁ω₁, π₂ω₂)` has `E H = qr` and
`E H² = (n − 2)²/n² + (n − 3)²/(n²(n − 1)) = (1 − 2q)² + q(1 − 3q)²/(1 − q)`. -/
theorem product_moments (hF : ringChar F ≠ 2) {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂]
    (μ₁ : FiniteLaw Ω₁) (μ₂ : FiniteLaw Ω₂) (π₁ : Ω₁ → PairT F) (π₂ : Ω₂ → PairT F)
    (h₁ : ∀ g : PairT F → ℝ, μ₁.expect (fun ω => g (π₁ ω)) = (pairLaw (F := F)).expect g)
    (h₂ : ∀ g : PairT F → ℝ, μ₂.expect (fun ω => g (π₂ ω)) = (pairLaw (F := F)).expect g) :
    (μ₁.product μ₂).expect (fun ω => pairScore (π₁ ω.1).1 (π₂ ω.2).1) =
        1 / (Fintype.card F : ℝ) * (1 / Real.sqrt (Fintype.card F)) ∧
      (μ₁.product μ₂).expect (fun ω => pairScore (π₁ ω.1).1 (π₂ ω.2).1 ^ 2) =
        ((Fintype.card F : ℝ) - 2) ^ 2 / (Fintype.card F : ℝ) ^ 2 +
          ((Fintype.card F : ℝ) - 3) ^ 2 /
            ((Fintype.card F : ℝ) ^ 2 * ((Fintype.card F : ℝ) - 1)) := by
  have key : ∀ g : F × F → F × F → ℝ,
      (μ₁.product μ₂).expect (fun ω => g (π₁ ω.1).1 (π₂ ω.2).1) =
        (∑ y ∈ distinctPairs F, ∑ y' ∈ distinctPairs F, g y y') /
          ((distinctPairs F).card : ℝ) ^ 2 := by
    intro g
    rw [FiniteLaw.expect_product]
    have e2 : ∀ ω₁ : Ω₁, μ₂.expect (fun ω₂ => g (π₁ (ω₁, ω₂).1).1 (π₂ (ω₁, ω₂).2).1) =
        (pairLaw (F := F)).expect (fun b₂ => g (π₁ ω₁).1 b₂.1) :=
      fun ω₁ => h₂ (fun b₂ => g (π₁ ω₁).1 b₂.1)
    simp only [e2]
    rw [h₁ (fun b₁ => (pairLaw (F := F)).expect (fun b₂ => g b₁.1 b₂.1))]
    exact pairLaw_pair_expect g
  exact ⟨(key (fun y y' => pairScore y y')).trans (pairScore_mean hF),
    (key (fun y y' => pairScore y y' ^ 2)).trans (pairScore_sq_mean hF)⟩

end ProductMoments

/-! ## The mass step for the actual root -/

open Sarkozy.Labellings

/-- **The mass step of `prop:root-layer` for `Γ_{p,0} = λ_p(G_{L,2})`**: given the coincidence
counts of the proof of `lem:root-normalization`(b) for each of the three scores (on the product of
the two component laws, `RootProduct`), `E_{Γ_{p,0}} w_u ≥ z^ι_u` for every rational `u ≥ 0`. -/
theorem gamma0_tilt_mass {p : ℕ} [Fact p.Prime] (hm1 : quadraticChar (ZMod p) (-1) = -1)
    (hp2 : p ≠ 2) (hneR : (injLabellings (ZMod p) (recordGraph (Fin 2))).Nonempty)
    (hneC : (injLabellings (ZMod p) compGraph).Nonempty)
    (S : Fin 3 → (Fin 3 × Fin 2 → ZMod p) × (Fin 3 × Fin 2 → ZMod p) → Prop)
    [∀ j, DecidablePred (S j)] (u : ℚ) (hu : 0 ≤ u)
    {q r : ℝ} (hr : r = 1 / Real.sqrt p) (hq : q = r ^ 2) (hq2 : q < 1 / 2) (hq36 : 36 * q < 1)
    (hGc : ∑ ω ∈ univ.filter (fun ω => ¬ GInj ω),
      ((graphLaw compGraph hneC).product (graphLaw compGraph hneC)).weight ω ≤ 36 * q)
    (hS : ∀ j, ∑ ω ∈ univ.filter (fun ω => ¬ GInj ω ∧ S j ω),
      ((graphLaw compGraph hneC).product (graphLaw compGraph hneC)).weight ω ≤
        2 * q ^ 2 / (1 - q))
    (hB : ∀ j ω, ¬ GInj ω → ¬ S j ω → |PartV.rootScore p j (joinC ω)| ≤ 2 + r)
    (hA : ∀ j ω, ¬ GInj ω → S j ω → |PartV.rootScore p j (joinC ω)| ≤ 1 / r ∧
      PartV.rootScore p j (joinC ω) ^ 2 ≤ (1 - 2 * q) ^ 2 / q) :
    Layer.zI (u : ℝ) q r ≤
      (graphLaw (recordGraph (Fin 2)) hneR).expect (PartV.individualWeight p u) := by
  refine Layer.tilt_mass_ge_zI (graphLaw (recordGraph (Fin 2)) hneR) u hu ?_ ?_
  · intro j
    rw [← h0_eq_layer]
    exact (gamma0_score_bounds hm1 hp2 hneR hneC j (S j) hr hq hq2 hq36 hGc (hS j) (hB j)
      (hA j)).1
  · intro j
    unfold Layer.BH
    exact (gamma0_score_bounds hm1 hp2 hneR hneC j (S j) hr hq hq2 hq36 hGc (hS j) (hB j)
      (hA j)).2

end Sarkozy.PositiveRoots
