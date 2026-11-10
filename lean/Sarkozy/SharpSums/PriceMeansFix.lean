module

public import Sarkozy.SharpSums.PriceMeans

@[expose] public section

/-!
# The main-price means of the folds of `fixC`: `PriceMeansFixL/R` proved

SUM (8 November 2026). As `SharpSums.PriceMeans`, at the slot data `fixSlots` of the wrapping
energies (a query `e ∈ 𝒮` reveals the fixed interval of index `t`; the other queries and the
outside slots carry `F_A`):

* `paperPrice_fixSlots_le`: `0 ≤ ξ_w ≤ K M²`;
* `fixFoldP_le_mean`: `P ≤ (K M²)^a ∑_v (1/72) ᾱ_v/α` (AM–GM over the slots);
* `expect_fixDatumDensity_le`: `E_ω ᾱ_w/α ≤ K` (B9's `fix_localDensity_mean_le` at one query,
  `p = 1`; the fixed interval has `1/K` of the range);
* **`priceMeansFixL`, `priceMeansFixR`**: `PriceMeansFixL/R` with `C_P = (K M²)^a K`.
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

omit [DecidableEq P] [DecidableEq J₀] [∀ (i : J₀), NeZero (m₀ i)] [Fintype Bk] in
/-- **The slot prices of `fixC` are bounded**: `0 ≤ ξ_w ≤ K M²`. -/
theorem paperPrice_fixSlots_le (u : E → reservedCut.Half) {L : ℕ} (hL : 1 ≤ L) (S : Finset E)
    (t : ZMod blockScale)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (w : Slot) :
    0 ≤ datumPrice (crtModuli m₀ blk paperTail L) ∅ L (fixSlots hcop u L S t Jq ω w) ∧
      datumPrice (crtModuli m₀ blk paperTail L) ∅ L (fixSlots hcop u L S t Jq ω w) ≤
        slotPriceBound pr h := by
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
  have hN : ((blockScale * L : ℕ) : ℝ) ≠ 0 := by
    have : 0 < blockScale * L := Nat.mul_pos (by norm_num [blockScale]) (by omega)
    exact_mod_cast this.ne'
  have hwhole : 0 ≤ datumPrice (crtModuli m₀ blk paperTail L) ∅ L (wholeDatum L) ∧
      datumPrice (crtModuli m₀ blk paperTail L) ∅ L (wholeDatum L) ≤ slotPriceBound pr h := by
    unfold datumPrice wholeDatum stepR
    simp only [prod_empty, mul_one, leastSquare_one, Nat.cast_one]
    rw [div_self hN]
    exact ⟨zero_le_one, one_le_slotPriceBound⟩
  unfold fixSlots slotDatum
  rcases hq : slotQuery u w with _ | e
  · exact hwhole
  · simp only
    unfold fixDatum
    split_ifs with he
    · unfold datumPrice stepR
      simp only [prod_empty, mul_one]
      have hr : revealedModulus blockScale pr h (Jq e) ≠ 0 := fun h0 =>
        (NeZero.ne (modulus pr h)) (Nat.eq_zero_of_zero_dvd (h0 ▸ revealedModulus_dvd (Jq e)))
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
    · exact hwhole

omit [DecidableEq P] [DecidableEq J₀] [∀ (i : J₀), NeZero (m₀ i)] [Fintype Bk] in
/-- **AM–GM over the slots for `fixC`**: `P ≤ (K M²)^a ∑_v (1/72) ᾱ_v/α`. -/
theorem fixFoldP_le_mean (u : E → reservedCut.Half) {L : ℕ} (hL : 1 ≤ L) (A : Finset ℤ)
    (S : Finset E) (t : ZMod blockScale)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (fo : Slot → Slot) (ha : 0 ≤ a) :
    fixFoldP (a := a) m₀ blk hcop u L A S t Jq ω fo ≤
      slotPriceBound pr h ^ a *
        ∑ v, (1 / 72 : ℝ) * (datumDensity A (fixSlots hcop u L S t Jq ω (fo v)) /
          density (blockScale * L) A) := by
  unfold fixFoldP mainPrice
  have hfil : (univ.filter fun _ : Slot => True) = univ := filter_true_of_mem fun _ _ => trivial
  rw [hfil]
  have hΞ0 : 0 ≤ slotPriceBound pr h := zero_le_one.trans one_le_slotPriceBound
  have hp : ∀ v, paperPrice (crtModuli m₀ blk paperTail L) ∅
      (fun v => (fixSlots hcop u L S t Jq ω (fo v)).1)
      (fun v => (fixSlots hcop u L S t Jq ω (fo v)).2.2.1)
      L v = datumPrice (crtModuli m₀ blk paperTail L) ∅ L (fixSlots hcop u L S t Jq ω (fo v)) :=
    fun v => rfl
  have hd : ∀ v, paperMeanDensity (FiniteLaw.uniform Unit) A
      (fun v => (fixSlots hcop u L S t Jq ω (fo v)).1)
      (fun v => (fixSlots hcop u L S t Jq ω (fo v)).2.2.1)
      (fun _ v => (fixSlots hcop u L S t Jq ω (fo v)).2.2.2)
      (fun _ v => (fixSlots hcop u L S t Jq ω (fo v)).2.1) v =
      datumDensity A (fixSlots hcop u L S t Jq ω (fo v)) := by
    intro v
    unfold paperMeanDensity datumDensity
    rw [FiniteLaw.expect_const]
  simp_rw [hp, hd]
  have h1 : ∏ v, datumPrice (crtModuli m₀ blk paperTail L) ∅ L
      (fixSlots hcop u L S t Jq ω (fo v)) ^ (a / 72) ≤ slotPriceBound pr h ^ a := by
    calc ∏ v, datumPrice (crtModuli m₀ blk paperTail L) ∅ L
          (fixSlots hcop u L S t Jq ω (fo v)) ^ (a / 72)
        ≤ ∏ _v : Slot, slotPriceBound pr h ^ (a / 72) :=
          prod_le_prod₀ (fun v _ => Real.rpow_nonneg
            (paperPrice_fixSlots_le hcop u hL S t Jq ω (fo v)).1 _)
            fun v _ => Real.rpow_le_rpow (paperPrice_fixSlots_le hcop u hL S t Jq ω (fo v)).1
              (paperPrice_fixSlots_le hcop u hL S t Jq ω (fo v)).2 (by positivity)
      _ = slotPriceBound pr h ^ a := by
          rw [prod_const, card_univ, card_slot, ← Real.rpow_natCast, ← Real.rpow_mul hΞ0]
          norm_num
  have hden : ∀ v, 0 ≤ datumDensity A (fixSlots hcop u L S t Jq ω (fo v)) /
      density (blockScale * L) A := fun v => div_nonneg (by
        unfold datumDensity
        positivity) (density_nonneg _ _)
  have h2 : ∏ v, (datumDensity A (fixSlots hcop u L S t Jq ω (fo v)) /
      density (blockScale * L) A) ^ (densityExponent / 72) ≤
      ∑ v, (1 / 72 : ℝ) * (datumDensity A (fixSlots hcop u L S t Jq ω (fo v)) /
        density (blockScale * L) A) := by
    rw [show densityExponent / 72 = (1 : ℝ) / 72 by norm_num [densityExponent]]
    exact Real.geom_mean_le_arith_mean_weighted univ (fun _ => (1 : ℝ) / 72) _
      (fun _ _ => by norm_num) (by rw [sum_const, card_univ, card_slot]; norm_num)
      fun v _ => hden v
  exact mul_le_mul h1 h2 (prod_nonneg fun v _ => Real.rpow_nonneg (hden v) _)
    (Real.rpow_nonneg hΞ0 _)

omit [DecidableEq J₀] [∀ (i : J₀), NeZero (m₀ i)] [Fintype Bk] in
/-- **The mean densities of `fixC` average to at most `K`** at every slot (B9's
`fix_localDensity_mean_le` at one query and `p = 1`). -/
theorem expect_fixDatumDensity_le (u : E → reservedCut.Half) {L : ℕ} (hL : 1 ≤ L)
    (A : Finset ℤ) (hA : A ⊆ Icc 1 ((blockScale * L : ℕ) : ℤ))
    (hα : 0 < density (blockScale * L) A) (S : Finset E) (t : ZMod blockScale)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (w : Slot) :
    (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
      (fun ω => datumDensity A (fixSlots hcop u L S t Jq ω w) / density (blockScale * L) A) ≤
      blockScale := by
  have hK1 : (1 : ℝ) ≤ blockScale := by norm_num [blockScale]
  have hwhole : (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
      (fun _ => datumDensity A (wholeDatum L) / density (blockScale * L) A) ≤ blockScale := by
    rw [datumDensity_wholeDatum A hA, div_self hα.ne', FiniteLaw.expect_const]
    exact hK1
  unfold fixSlots slotDatum
  rcases hq : slotQuery u w with _ | e
  · exact hwhole
  · simp only
    unfold fixDatum
    by_cases he : e ∈ S
    · simp only [he, ↓reduceIte]
      have hq2 : ∀ η, datumDensity A (⟨revealedModulus blockScale pr h (Jq e),
          revealedResidue hcop (Jq e) η, L, ((leastPosRep t : ℤ) - 1) * L⟩ : SlotDatum) =
          fixQueryLocalDensity hcop L A t (Jq e) η := by
        intro η
        unfold datumDensity fixQueryLocalDensity localDensity
        simp only
        rw [BracketEnergy.blockInterval_eq_Icc]
      simp_rw [hq2]
      set g : (∀ j : Option P, CoordSpace blockScale pr h j) → ℝ := fun η =>
        fixQueryLocalDensity hcop L A t (Jq e) η / density (blockScale * L) A with hg
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
        have hr : (fun e' => (FiniteLaw.uniform (∀ j : Option P,
            CoordSpace blockScale pr h j)).expect (fun η => if e' = e then g η else 1)) =
            fun e' => if e' = e then
              (FiniteLaw.uniform (∀ j : Option P, CoordSpace blockScale pr h j)).expect g
            else 1 := by
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
          (fun ω => ∏ x : Unit, if x ∈ (univ : Finset Unit) then
            (fixQueryLocalDensity hcop L A t ((fun _ => Jq e) x) (ω x) /
              density (blockScale * L) A) ^ (1 : ℝ) else 1) =
          (FiniteLaw.uniform (∀ j : Option P, CoordSpace blockScale pr h j)).expect g := by
        have h2 := expect_uniform_pi_prod (Ωe := fun _ : Unit => ∀ j : Option P,
          CoordSpace blockScale pr h j) (fun _ η => (g η) ^ (1 : ℝ))
        simp only [Real.rpow_one, Fintype.prod_unique, mem_univ, ↓reduceIte] at h2 ⊢
        exact h2
      have hB := fix_localDensity_mean_le (E := Unit) hcop hL A hα (p := 1) zero_le_one le_rfl
        univ t (fun _ => Jq e)
      rw [hm2] at hB
      simp only [mem_univ, ↓reduceIte, Real.rpow_one, Fintype.prod_unique] at hB
      rw [hm1]
      exact hB
    · simp only [he, ↓reduceIte]
      exact hwhole

/-- **`PriceMeansFixL` proved** (`C_P = (K M²)^a K`): the main prices of the folds of `fixC`
(left) average to at most `(K M²)^a K` over the query law and `ω`, at every counterexample
and every `𝒮 ≠ ∅`. -/
theorem priceMeansFixL (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (ha : 0 ≤ a) : PriceMeansFixL hcop D (slotPriceBound pr h ^ a * blockScale) := by
  unfold PriceMeansFixL
  filter_upwards [eventually_ge_atTop 1] with L hL
  intro C hC _ A hA hY S _ j
  have hα := density_pos_cex D hL hC hY
  have key : ∀ fo : Slot → Slot, (queryLaw (fun (_ : E) => coordChain blockScale pr h)
      (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
      (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
        (fun ω => fixFoldP (a := a) m₀ blk hcop D.S.Q.u L A S 0 Jq ω fo)) ≤
      slotPriceBound pr h ^ a * blockScale := by
    intro fo
    refine FiniteLaw.expect_le_const _ fun Jq => ?_
    have hΞ : 0 ≤ slotPriceBound pr h ^ a :=
      Real.rpow_nonneg (zero_le_one.trans one_le_slotPriceBound) _
    calc (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => fixFoldP (a := a) m₀ blk hcop D.S.Q.u L A S 0 Jq ω fo)
        ≤ (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => slotPriceBound pr h ^ a * ∑ v, (1 / 72 : ℝ) *
            (datumDensity A (fixSlots hcop D.S.Q.u L S 0 Jq ω (fo v)) /
              density (blockScale * L) A)) :=
          FiniteLaw.expect_mono _ fun ω => fixFoldP_le_mean hcop D.S.Q.u hL A S 0 Jq ω fo ha
      _ = slotPriceBound pr h ^ a * ∑ v, (1 / 72 : ℝ) *
            (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
              (fun ω => datumDensity A (fixSlots hcop D.S.Q.u L S 0 Jq ω (fo v)) /
                density (blockScale * L) A) := by
          rw [FiniteLaw.expect_const_mul, FiniteLaw.expect_sum]
          simp_rw [FiniteLaw.expect_const_mul]
      _ ≤ slotPriceBound pr h ^ a * ∑ _v : Slot, (1 / 72 : ℝ) * (blockScale : ℝ) :=
          mul_le_mul_of_nonneg_left (sum_le_sum fun v _ => mul_le_mul_of_nonneg_left
            (expect_fixDatumDensity_le hcop D.S.Q.u hL A hA.1 hα S 0 Jq (fo v)) (by norm_num))
            hΞ
      _ = slotPriceBound pr h ^ a * blockScale := by
          rw [sum_const, card_univ, card_slot]
          ring
  exact ⟨key _, key _⟩

/-- **`PriceMeansFixR` proved** (`C_P = (K M²)^a K`): the main prices of the folds of `fixC`
(right) average to at most `(K M²)^a K` over the query law and `ω`, at every counterexample
and every `𝒮 ≠ ∅`. -/
theorem priceMeansFixR (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (ha : 0 ≤ a) : PriceMeansFixR hcop D (slotPriceBound pr h ^ a * blockScale) := by
  unfold PriceMeansFixR
  filter_upwards [eventually_ge_atTop 1] with L hL
  intro C hC _ A hA hY S _ j
  have hα := density_pos_cex D hL hC hY
  have key : ∀ fo : Slot → Slot, (queryLaw (fun (_ : E) => coordChain blockScale pr h)
      (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
      (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
        (fun ω => fixFoldP (a := a) m₀ blk hcop D.S.Q.w L A S 1 Jq ω fo)) ≤
      slotPriceBound pr h ^ a * blockScale := by
    intro fo
    refine FiniteLaw.expect_le_const _ fun Jq => ?_
    have hΞ : 0 ≤ slotPriceBound pr h ^ a :=
      Real.rpow_nonneg (zero_le_one.trans one_le_slotPriceBound) _
    calc (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => fixFoldP (a := a) m₀ blk hcop D.S.Q.w L A S 1 Jq ω fo)
        ≤ (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => slotPriceBound pr h ^ a * ∑ v, (1 / 72 : ℝ) *
            (datumDensity A (fixSlots hcop D.S.Q.w L S 1 Jq ω (fo v)) /
              density (blockScale * L) A)) :=
          FiniteLaw.expect_mono _ fun ω => fixFoldP_le_mean hcop D.S.Q.w hL A S 1 Jq ω fo ha
      _ = slotPriceBound pr h ^ a * ∑ v, (1 / 72 : ℝ) *
            (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
              (fun ω => datumDensity A (fixSlots hcop D.S.Q.w L S 1 Jq ω (fo v)) /
                density (blockScale * L) A) := by
          rw [FiniteLaw.expect_const_mul, FiniteLaw.expect_sum]
          simp_rw [FiniteLaw.expect_const_mul]
      _ ≤ slotPriceBound pr h ^ a * ∑ _v : Slot, (1 / 72 : ℝ) * (blockScale : ℝ) :=
          mul_le_mul_of_nonneg_left (sum_le_sum fun v _ => mul_le_mul_of_nonneg_left
            (expect_fixDatumDensity_le hcop D.S.Q.w hL A hA.1 hα S 1 Jq (fo v)) (by norm_num))
            hΞ
      _ = slotPriceBound pr h ^ a * blockScale := by
          rw [sum_const, card_univ, card_slot]
          ring
  exact ⟨key _, key _⟩

/-- The constant `C_P = (K M²)^a K` of the four main-price means, read off the datum. -/
noncomputable def cPrice (_D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E) : ℝ :=
  slotPriceBound pr h ^ a * blockScale

omit [DecidableEq P] in
theorem slotPriceBound_rpow_le_cPrice (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E) :
    slotPriceBound pr h ^ a ≤ cPrice D := by
  unfold cPrice
  have h0 := Real.rpow_nonneg (zero_le_one.trans
    (one_le_slotPriceBound (pr := pr) (h := h))) a
  have hK : (1 : ℝ) ≤ blockScale := by norm_num [blockScale]
  nlinarith

/-- **The four main-price means at the common constant `cPrice D`** (envelopes: `(K M²)^a ≤
cPrice D`). -/
theorem priceMeans_all (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (ha : 0 ≤ a) :
    PriceMeansEnvL hcop D (cPrice D) ∧ PriceMeansEnvR hcop D (cPrice D) ∧
      PriceMeansFixL hcop D (cPrice D) ∧ PriceMeansFixR hcop D (cPrice D) := by
  have hle : slotPriceBound pr h ^ a ≤ cPrice D := slotPriceBound_rpow_le_cPrice D
  refine ⟨?_, ?_, priceMeansFixL hcop D ha, priceMeansFixR hcop D ha⟩
  · have hP := priceMeansEnvL hcop D ha
    unfold PriceMeansEnvL at hP ⊢
    filter_upwards [hP] with L hL
    intro C hC hk A hA hY j
    obtain ⟨h1, h2⟩ := hL C hC hk A hA hY j
    exact ⟨h1.trans hle, h2.trans hle⟩
  · have hP := priceMeansEnvR hcop D ha
    unfold PriceMeansEnvR at hP ⊢
    filter_upwards [hP] with L hL
    intro C hC hk A hA hY j
    obtain ⟨h1, h2⟩ := hL C hC hk A hA hY j
    exact ⟨h1.trans hle, h2.trans hle⟩

end Sarkozy.SharpSums
