module

public import Sarkozy.SharpSums.InputsY

@[expose] public section

/-!
# The main-price means of the folds of `envC`: `PriceMeansEnvL/R` proved

SUM (8 November 2026). The main price of one fold of the envelope energies is
`P = (∏_v ξ_v^{a/72}) ∏_v (ᾱ_v/α)^{1/72}` (`envFoldP`, `θ = 1`) at the slot data of the fold. Here:

* `paperPrice_envSlots_le`: `0 ≤ ξ_v ≤ K M²` at every slot (`M = modulus`: a query slot has
  `ξ = K sq(D₀) ≤ K D₀² ≤ K M²`, a whole slot `ξ = 1`);
* `envFoldP_le_mean`: by AM–GM over the 72 slots,
  `P ≤ (K M²)^a ∑_v (1/72) ᾱ_v/α`;
* `expect_datumDensity_le`: `E_ω ᾱ_v/α ≤ 1` at every slot (a whole slot has `ᾱ = α`; a query
  slot is B9's `env_localDensity_mean_le` at one query and `p = 1`);
* **`priceMeansEnvL`, `priceMeansEnvR`**: `PriceMeansEnvL/R` with `C_P = (K M²)^a`.

This is `prop:record:density-structured`'s main price averaged over the query law
(`lem:sharp-first`, the cross terms), by B9's mean bound with the arithmetic mean in place of the
per-query exponents.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.SharpSums

open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.CancellationSteps Sarkozy.BlockAnchor Sarkozy.DensityChain2
  Sarkozy.SharpBase2 Sarkozy.SharpBase
open Sarkozy.Param (Params)

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- The constant `K M²` (`M = modulus pr h`) of the slot prices. -/
noncomputable def slotPriceBound (pr h : P → ℕ) : ℝ :=
  (blockScale : ℝ) * (modulus pr h : ℝ) ^ 2

omit [DecidableEq P] [∀ q, NeZero (pr q ^ h q)] in
theorem one_le_slotPriceBound [∀ q, NeZero (pr q ^ h q)] : 1 ≤ slotPriceBound pr h := by
  unfold slotPriceBound
  have hM : (1 : ℝ) ≤ (modulus pr h : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hK : (1 : ℝ) ≤ (blockScale : ℝ) := by norm_num [blockScale]
  nlinarith [one_le_pow₀ (n := 2) hM]

omit [DecidableEq P] [DecidableEq J₀] [∀ (i : J₀), NeZero (m₀ i)] [Fintype Bk] [DecidableEq E] in
/-- **The slot prices are bounded**: `0 ≤ ξ_w ≤ K M²` at every slot `w` of the envelope data. -/
theorem paperPrice_envSlots_le (u : E → reservedCut.Half) {L : ℕ} (hL : 1 ≤ L)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (w : Slot) :
    0 ≤ datumPrice (crtModuli m₀ blk paperTail L) ∅ L (envSlots hcop u L Jq ω w) ∧
      datumPrice (crtModuli m₀ blk paperTail L) ∅ L (envSlots hcop u L Jq ω w) ≤
        slotPriceBound pr h := by
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
  have hN : ((blockScale * L : ℕ) : ℝ) ≠ 0 := by
    have : 0 < blockScale * L := Nat.mul_pos (by norm_num [blockScale]) (by omega)
    exact_mod_cast this.ne'
  unfold envSlots slotDatum
  rcases hq : slotQuery u w with _ | e
  · simp only
    unfold datumPrice wholeDatum stepR
    simp only [prod_empty, mul_one, leastSquare_one, Nat.cast_one]
    rw [div_self hN]
    exact ⟨zero_le_one, one_le_slotPriceBound⟩
  · simp only
    unfold datumPrice envDatum stepR
    simp only [prod_empty, mul_one]
    have hr : revealedModulus blockScale pr h (Jq e) ≠ 0 :=
      fun h0 => (NeZero.ne (modulus pr h))
        (Nat.eq_zero_of_zero_dvd (h0 ▸ revealedModulus_dvd (Jq e)))
    have hsq : (leastSquare (revealedModulus blockScale pr h (Jq e)) : ℝ) ≤
        (modulus pr h : ℝ) ^ 2 := by
      have h1 := leastSquare_le_sq hr
      have h2 : revealedModulus blockScale pr h (Jq e) ≤ modulus pr h :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne _)) (revealedModulus_dvd (Jq e))
      have h3 : (revealedModulus blockScale pr h (Jq e)) ^ 2 ≤ (modulus pr h) ^ 2 :=
        Nat.pow_le_pow_left h2 2
      exact_mod_cast h1.trans h3
    have hKL : ((blockScale * L : ℕ) : ℝ) / (L : ℝ) = blockScale := by
      push_cast
      field_simp
    rw [hKL]
    refine ⟨by positivity, ?_⟩
    unfold slotPriceBound
    exact mul_le_mul_of_nonneg_left hsq (by norm_num [blockScale])

omit [DecidableEq P] [DecidableEq J₀] [∀ (i : J₀), NeZero (m₀ i)] [Fintype Bk] [DecidableEq E] in
/-- **AM–GM over the slots**: `P ≤ (K M²)^a ∑_v (1/72) ᾱ_v/α` for the main price of any fold
`fo` of the envelope slot data (`θ = 1`, `a ≥ 0`). -/
theorem envFoldP_le_mean (u : E → reservedCut.Half) {L : ℕ} (hL : 1 ≤ L) (A : Finset ℤ)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (fo : Slot → Slot) (ha : 0 ≤ a) :
    envFoldP (a := a) m₀ blk hcop u L A Jq ω fo ≤
      slotPriceBound pr h ^ a *
        ∑ v, (1 / 72 : ℝ) * (datumDensity A (envSlots hcop u L Jq ω (fo v)) /
          density (blockScale * L) A) := by
  unfold envFoldP mainPrice
  have hfil : (univ.filter fun _ : Slot => True) = univ := filter_true_of_mem fun _ _ => trivial
  rw [hfil]
  have hΞ0 : 0 ≤ slotPriceBound pr h := zero_le_one.trans one_le_slotPriceBound
  have hp : ∀ v, paperPrice (crtModuli m₀ blk paperTail L) ∅
      (fun v => (envSlots hcop u L Jq ω (fo v)).1) (fun v => (envSlots hcop u L Jq ω (fo v)).2.2.1)
      L v = datumPrice (crtModuli m₀ blk paperTail L) ∅ L (envSlots hcop u L Jq ω (fo v)) :=
    fun v => rfl
  have hd : ∀ v, paperMeanDensity (FiniteLaw.uniform Unit) A
      (fun v => (envSlots hcop u L Jq ω (fo v)).1)
      (fun v => (envSlots hcop u L Jq ω (fo v)).2.2.1)
      (fun _ v => (envSlots hcop u L Jq ω (fo v)).2.2.2)
      (fun _ v => (envSlots hcop u L Jq ω (fo v)).2.1) v =
      datumDensity A (envSlots hcop u L Jq ω (fo v)) := by
    intro v
    unfold paperMeanDensity datumDensity
    rw [FiniteLaw.expect_const]
  simp_rw [hp, hd]
  have h1 : ∏ v, datumPrice (crtModuli m₀ blk paperTail L) ∅ L
      (envSlots hcop u L Jq ω (fo v)) ^ (a / 72) ≤ slotPriceBound pr h ^ a := by
    calc ∏ v, datumPrice (crtModuli m₀ blk paperTail L) ∅ L
          (envSlots hcop u L Jq ω (fo v)) ^ (a / 72)
        ≤ ∏ _v : Slot, slotPriceBound pr h ^ (a / 72) :=
          prod_le_prod₀ (fun v _ => Real.rpow_nonneg
            (paperPrice_envSlots_le hcop u hL Jq ω (fo v)).1 _)
            fun v _ => Real.rpow_le_rpow (paperPrice_envSlots_le hcop u hL Jq ω (fo v)).1
              (paperPrice_envSlots_le hcop u hL Jq ω (fo v)).2 (by positivity)
      _ = slotPriceBound pr h ^ a := by
          rw [prod_const, card_univ, card_slot, ← Real.rpow_natCast, ← Real.rpow_mul hΞ0]
          norm_num
  have hden : ∀ v, 0 ≤ datumDensity A (envSlots hcop u L Jq ω (fo v)) /
      density (blockScale * L) A := fun v => div_nonneg (by
        unfold datumDensity
        positivity) (density_nonneg _ _)
  have h2 : ∏ v, (datumDensity A (envSlots hcop u L Jq ω (fo v)) /
      density (blockScale * L) A) ^ (densityExponent / 72) ≤
      ∑ v, (1 / 72 : ℝ) * (datumDensity A (envSlots hcop u L Jq ω (fo v)) /
        density (blockScale * L) A) := by
    rw [show densityExponent / 72 = (1 : ℝ) / 72 by norm_num [densityExponent]]
    exact Real.geom_mean_le_arith_mean_weighted univ (fun _ => (1 : ℝ) / 72) _
      (fun _ _ => by norm_num) (by rw [sum_const, card_univ, card_slot]; norm_num)
      fun v _ => hden v
  exact mul_le_mul h1 h2 (prod_nonneg fun v _ => Real.rpow_nonneg (hden v) _)
    (Real.rpow_nonneg hΞ0 _)

omit [DecidableEq J₀] [∀ (i : J₀), NeZero (m₀ i)] [Fintype Bk] in
/-- **The mean densities average to at most one** at every slot: `E_ω ᾱ_w/α ≤ 1` (a whole slot
has `ᾱ = α`; a query slot `e` has `ᾱ = ᾱ_e(ω_e)`, and B9's `env_localDensity_mean_le` at one query
and `p = 1` applies after marginalizing the uniform `ω`). -/
theorem expect_datumDensity_le (u : E → reservedCut.Half) {L : ℕ} (hL : 1 ≤ L) (A : Finset ℤ)
    (hA : A ⊆ Icc 1 ((blockScale * L : ℕ) : ℤ)) (hα : 0 < density (blockScale * L) A)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (w : Slot) :
    (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
      (fun ω => datumDensity A (envSlots hcop u L Jq ω w) / density (blockScale * L) A) ≤ 1 := by
  unfold envSlots slotDatum
  rcases hq : slotQuery u w with _ | e
  · simp only
    rw [datumDensity_wholeDatum A hA, div_self hα.ne', FiniteLaw.expect_const]
  · simp only
    have hq2 : ∀ η, datumDensity A (envDatum hcop L Jq e η) =
        queryLocalDensity hcop L A (Jq e) η := by
      intro η
      unfold datumDensity envDatum queryLocalDensity localDensity
      simp only
      rw [BracketEnergy.blockInterval_eq_Icc]
    simp_rw [hq2]
    set g : (∀ j : Option P, CoordSpace blockScale pr h j) → ℝ := fun η =>
      queryLocalDensity hcop L A (Jq e) η / density (blockScale * L) A with hg
    -- marginalize the uniform index at the query `e`
    have hm1 : (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
        (fun ω => g (ω e)) =
        (FiniteLaw.uniform (∀ j : Option P, CoordSpace blockScale pr h j)).expect g := by
      have h1 := expect_uniform_pi_prod (Ωe := fun _ : E => ∀ j : Option P,
        CoordSpace blockScale pr h j) (fun e' η => if e' = e then g η else 1)
      have hl : (fun ω : E → ∀ j : Option P, CoordSpace blockScale pr h j =>
          ∏ e', (if e' = e then g (ω e') else 1)) = fun ω => g (ω e) := by
        funext ω
        rw [prod_ite_eq' univ e (fun e' => g (ω e'))]
        simp only [mem_univ, ↓reduceIte]
      have hr : (fun e' => (FiniteLaw.uniform (∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun η => if e' = e then g η else 1)) = fun e' => if e' = e then
            (FiniteLaw.uniform (∀ j : Option P, CoordSpace blockScale pr h j)).expect g else 1 := by
        funext e'
        split_ifs
        · rfl
        · exact FiniteLaw.expect_const _ _
      have h1' : (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => ∏ e', (if e' = e then g (ω e') else 1)) =
          ∏ e', (if e' = e then
            (FiniteLaw.uniform (∀ j : Option P, CoordSpace blockScale pr h j)).expect g
          else 1) := by
        rw [← hr]
        exact h1
      rw [hl, prod_ite_eq' univ e] at h1'
      simpa only [mem_univ, ↓reduceIte] using h1'
    have hm2 : (FiniteLaw.uniform (Unit → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
        (fun ω => ∏ x : Unit, (queryLocalDensity hcop L A ((fun _ => Jq e) x) (ω x) /
          density (blockScale * L) A) ^ (1 : ℝ)) =
        (FiniteLaw.uniform (∀ j : Option P, CoordSpace blockScale pr h j)).expect g := by
      have h2 := expect_uniform_pi_prod (Ωe := fun _ : Unit => ∀ j : Option P,
        CoordSpace blockScale pr h j) (fun _ η => (g η) ^ (1 : ℝ))
      simp only [Real.rpow_one, Fintype.prod_unique] at h2 ⊢
      exact h2
    have hB := env_localDensity_mean_le (E := Unit) hcop hL A hA hα (p := 1) zero_le_one le_rfl
      (fun _ => Jq e)
    rw [hm2] at hB
    rw [hm1]
    exact hB

/-- **`PriceMeansEnvL` proved** (`C_P = (K M²)^a`): the main prices of the folds of `envC` (left)
average to at most `(K M²)^a` over the query law and `ω`, at every counterexample. -/
theorem priceMeansEnvL (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (ha : 0 ≤ a) : PriceMeansEnvL hcop D (slotPriceBound pr h ^ a) := by
  unfold PriceMeansEnvL
  filter_upwards [eventually_ge_atTop 1] with L hL
  intro C hC _ A hA hY j
  have hα := density_pos_cex D hL hC hY
  have key : ∀ fo : Slot → Slot, (queryLaw D.index.C D.index.t).expect (fun Jq =>
      (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
        (fun ω => envFoldP (a := a) m₀ blk hcop D.index.u L A Jq ω fo)) ≤
      slotPriceBound pr h ^ a := by
    intro fo
    refine FiniteLaw.expect_le_const _ fun Jq => ?_
    have hΞ : 0 ≤ slotPriceBound pr h ^ a :=
      Real.rpow_nonneg (zero_le_one.trans one_le_slotPriceBound) _
    calc (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => envFoldP (a := a) m₀ blk hcop D.index.u L A Jq ω fo)
        ≤ (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => slotPriceBound pr h ^ a * ∑ v, (1 / 72 : ℝ) *
            (datumDensity A (envSlots hcop D.index.u L Jq ω (fo v)) /
              density (blockScale * L) A)) :=
          FiniteLaw.expect_mono _ fun ω => envFoldP_le_mean hcop D.index.u hL A Jq ω fo ha
      _ = slotPriceBound pr h ^ a * ∑ v, (1 / 72 : ℝ) *
            (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
              (fun ω => datumDensity A (envSlots hcop D.index.u L Jq ω (fo v)) /
                density (blockScale * L) A) := by
          rw [FiniteLaw.expect_const_mul, FiniteLaw.expect_sum]
          simp_rw [FiniteLaw.expect_const_mul]
      _ ≤ slotPriceBound pr h ^ a * ∑ _v : Slot, (1 / 72 : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left (sum_le_sum fun v _ => mul_le_mul_of_nonneg_left
            (expect_datumDensity_le hcop D.index.u hL A hA.1 hα Jq (fo v)) (by norm_num)) hΞ
      _ = slotPriceBound pr h ^ a := by
          rw [sum_const, card_univ, card_slot]
          norm_num
  exact ⟨key _, key _⟩

/-- **`PriceMeansEnvR` proved** (`C_P = (K M²)^a`), as `priceMeansEnvL` with the right queries
`D.index.w`. -/
theorem priceMeansEnvR (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (ha : 0 ≤ a) : PriceMeansEnvR hcop D (slotPriceBound pr h ^ a) := by
  unfold PriceMeansEnvR
  filter_upwards [eventually_ge_atTop 1] with L hL
  intro C hC _ A hA hY j
  have hα := density_pos_cex D hL hC hY
  have key : ∀ fo : Slot → Slot, (queryLaw D.index.C D.index.t).expect (fun Jq =>
      (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
        (fun ω => envFoldP (a := a) m₀ blk hcop D.index.w L A Jq ω fo)) ≤
      slotPriceBound pr h ^ a := by
    intro fo
    refine FiniteLaw.expect_le_const _ fun Jq => ?_
    have hΞ : 0 ≤ slotPriceBound pr h ^ a :=
      Real.rpow_nonneg (zero_le_one.trans one_le_slotPriceBound) _
    calc (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => envFoldP (a := a) m₀ blk hcop D.index.w L A Jq ω fo)
        ≤ (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => slotPriceBound pr h ^ a * ∑ v, (1 / 72 : ℝ) *
            (datumDensity A (envSlots hcop D.index.w L Jq ω (fo v)) /
              density (blockScale * L) A)) :=
          FiniteLaw.expect_mono _ fun ω => envFoldP_le_mean hcop D.index.w hL A Jq ω fo ha
      _ = slotPriceBound pr h ^ a * ∑ v, (1 / 72 : ℝ) *
            (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
              (fun ω => datumDensity A (envSlots hcop D.index.w L Jq ω (fo v)) /
                density (blockScale * L) A) := by
          rw [FiniteLaw.expect_const_mul, FiniteLaw.expect_sum]
          simp_rw [FiniteLaw.expect_const_mul]
      _ ≤ slotPriceBound pr h ^ a * ∑ _v : Slot, (1 / 72 : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left (sum_le_sum fun v _ => mul_le_mul_of_nonneg_left
            (expect_datumDensity_le hcop D.index.w hL A hA.1 hα Jq (fo v)) (by norm_num)) hΞ
      _ = slotPriceBound pr h ^ a := by
          rw [sum_const, card_univ, card_slot]
          norm_num
  exact ⟨key _, key _⟩

end Sarkozy.SharpSums
