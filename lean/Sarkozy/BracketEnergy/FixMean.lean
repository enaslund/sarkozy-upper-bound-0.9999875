module

public import Sarkozy.BracketEnergy.EnvMean

@[expose] public section

/-!
# The first bound of `lem:bracket-energy` for `fixC`, averaged over the residues

The fixed-interval energies of `fixC` carry, at a query `e ∈ 𝒮`, the revealed input
`g^{I_t, D_{𝒥_e}, s mod D_{𝒥_e}}` on the **fixed** interval `I_t` (`revealedSlot_wrapInputCRT`).
The mean of its local density over the residues is `#(A ∩ I_t)/L ≤ K α`, not `α`: this is the
factor `κ_e^{2θ/d} = K^{2θ/d}` of the fixed-interval price of `lem:envelope-energy`
(`fixedPrice`).

* `mean_fixLocalDensity`, `fixLocal_le`: `E_s ᾱ_t(s mod D) = #(A ∩ I_t)/L ≤ K α`;
* `fix_localDensity_mean_le`: `E_ω ∏_{e ∈ 𝒮} (ᾱ_e/α)^p ≤ K^{p |𝒮|}` (Jensen, independence);
* `fixMainPrice_eq`: the main price at the data of `fixC`;
* **`fix_first_mean_le`**:
  `E_ω |E_{f,g}(𝒥, ω)| ≤ (1 + u_L) Π_𝒮 Y ∏_f u ∏_g u' + ∏ ‖Λ‖ C_dc L^{-σ} α` with
  `Π_𝒮 = fixedPrice` (at `θ = ϑ`), from the chain's per-term inputs.
-/

open Finset Function
open scoped BigOperators

namespace Sarkozy.BracketEnergy

open Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper Sarkozy.Structured Sarkozy.Functional
  Sarkozy.FourierArithmetic Sarkozy.PaperFrame Sarkozy.BlockFrame Sarkozy.IndexSupport
  Sarkozy.TheoremC

/-- **The mean over the residues of the local density on a fixed interval**:
`E_s ᾱ_t(s mod D) = #(A ∩ I_t)/L`. -/
theorem mean_fixLocalDensity {K L M0 D : ℕ} [NeZero M0] (hL : 1 ≤ L) (hD : D ∣ M0)
    (A : Finset ℤ) (t : ZMod K) :
    (FiniteLaw.uniform (ZMod M0)).expect
        (fun s => localDensity K L A D t (ZMod.castHom hD (ZMod D) s)) =
      ((A ∩ blockInterval K L t).card : ℝ) / L := by
  have hD0 : (D : ℝ) ≠ 0 := by
    have : D ≠ 0 := fun h0 => NeZero.ne M0 (Nat.eq_zero_of_zero_dvd (h0 ▸ hD))
    exact_mod_cast this
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
  have hM0 : (M0 : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M0
  rw [FiniteLaw.expect_uniform, ZMod.card]
  unfold localDensity
  rw [← mul_sum, sum_residue_card hD]
  field_simp

/-- `#(A ∩ I_t)/L ≤ K α` for `A ⊆ [1, KL]`. -/
theorem fixLocal_le {K L : ℕ} [NeZero K] (hL : 1 ≤ L) (A : Finset ℤ) (t : ZMod K) :
    ((A ∩ blockInterval K L t).card : ℝ) / L ≤ K * density (K * L) A := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hK0 : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne K)
  have hc : ((A ∩ blockInterval K L t).card : ℝ) ≤ A.card := by
    exact_mod_cast card_le_card inter_subset_left
  unfold density
  rw [div_le_iff₀ hL0]
  push_cast
  field_simp
  linarith

/-- The uniform law on a product, against a function of the second coordinate. -/
theorem expect_uniform_snd {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (F : Y → ℝ) :
    (FiniteLaw.uniform (X × Y)).expect (fun x => F x.2) = (FiniteLaw.uniform Y).expect F := by
  rw [FiniteLaw.expect_uniform, FiniteLaw.expect_uniform, Fintype.sum_prod_type,
    Fintype.card_prod]
  simp only [sum_const, card_univ, nsmul_eq_mul]
  have hX : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hY : (Fintype.card Y : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  push_cast
  field_simp

variable {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- The local density of the revealed input of `fixC` at the interval `t`. -/
noncomputable def fixQueryLocalDensity (L : ℕ) (A : Finset ℤ) (t : ZMod blockScale)
    (J : ∀ j, Fin ((coordChain blockScale pr h j).depth + 1))
    (η : ∀ j : Option P, CoordSpace blockScale pr h j) : ℝ :=
  localDensity blockScale L A (revealedModulus blockScale pr h J) t (revealedResidue hcop J η)

/-- **The local densities on the fixed intervals average to at most `K^p` per active query**:
`E_ω ∏_e (e ∈ 𝒮 ? (ᾱ_e/α)^p : 1) ≤ ∏_e (e ∈ 𝒮 ? K^p : 1)`. -/
theorem fix_localDensity_mean_le {E : Type} [Fintype E] [DecidableEq E] {L : ℕ} (hL : 1 ≤ L)
    (A : Finset ℤ) (hα : 0 < density (blockScale * L) A) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Finset E) (t : ZMod blockScale)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) :
    (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
        (fun ω => ∏ e, if e ∈ S then (fixQueryLocalDensity hcop L A t (Jq e) (ω e) /
          density (blockScale * L) A) ^ p else 1) ≤
      ∏ e, if e ∈ S then (blockScale : ℝ) ^ p else 1 := by
  rw [expect_uniform_pi_prod (Ωe := fun _ : E => ∀ j : Option P, CoordSpace blockScale pr h j)
    (fun e η => if e ∈ S then (fixQueryLocalDensity hcop L A t (Jq e) η /
      density (blockScale * L) A) ^ p else 1)]
  apply prod_le_prod₀
  · intro e _
    apply FiniteLaw.expect_nonneg
    intro η
    split_ifs
    · exact Real.rpow_nonneg (div_nonneg (localDensity_nonneg _ _ _ _ _ _) hα.le) _
    · exact zero_le_one
  · intro e _
    split_ifs with he
    · rw [expect_uniform_equiv (crtEquiv blockScale pr h hcop)]
      have hx : ((fun η => (fixQueryLocalDensity hcop L A t (Jq e) η /
          density (blockScale * L) A) ^ p) ∘ crtEquiv blockScale pr h hcop) =
          fun x : ZMod blockScale × ZMod (modulus pr h) =>
            (localDensity blockScale L A (revealedModulus blockScale pr h (Jq e)) t
              (ZMod.castHom (revealedModulus_dvd (Jq e))
                (ZMod (revealedModulus blockScale pr h (Jq e))) x.2) /
              density (blockScale * L) A) ^ p := by
        funext x
        simp only [Function.comp_apply, fixQueryLocalDensity, revealedResidue,
          Equiv.symm_apply_apply]
      rw [hx, expect_uniform_snd (fun s : ZMod (modulus pr h) =>
        (localDensity blockScale L A (revealedModulus blockScale pr h (Jq e)) t
          (ZMod.castHom (revealedModulus_dvd (Jq e))
            (ZMod (revealedModulus blockScale pr h (Jq e))) s) /
          density (blockScale * L) A) ^ p)]
      refine le_trans (expect_rpow_le _ _ (fun s => div_nonneg (localDensity_nonneg _ _ _ _ _ _)
        hα.le) hp0 hp1) ?_
      have hmean : (FiniteLaw.uniform (ZMod (modulus pr h))).expect (fun s =>
          localDensity blockScale L A (revealedModulus blockScale pr h (Jq e)) t
            (ZMod.castHom (revealedModulus_dvd (Jq e))
              (ZMod (revealedModulus blockScale pr h (Jq e))) s) /
            density (blockScale * L) A) ≤ blockScale := by
        rw [show (fun s : ZMod (modulus pr h) =>
            localDensity blockScale L A (revealedModulus blockScale pr h (Jq e)) t
              (ZMod.castHom (revealedModulus_dvd (Jq e))
                (ZMod (revealedModulus blockScale pr h (Jq e))) s) /
              density (blockScale * L) A) = fun s => (density (blockScale * L) A)⁻¹ *
            localDensity blockScale L A (revealedModulus blockScale pr h (Jq e)) t
              (ZMod.castHom (revealedModulus_dvd (Jq e))
                (ZMod (revealedModulus blockScale pr h (Jq e))) s) by
          funext s; rw [div_eq_inv_mul], FiniteLaw.expect_const_mul,
          mean_fixLocalDensity hL (revealedModulus_dvd (Jq e)) A t]
        rw [inv_mul_le_iff₀ hα, mul_comm]
        exact fixLocal_le hL A t
      exact Real.rpow_le_rpow (FiniteLaw.expect_nonneg _ fun s => div_nonneg
        (localDensity_nonneg _ _ _ _ _ _) hα.le) hmean hp0
    · rw [FiniteLaw.expect_const]

section FixPrice

variable {E : Type} [Fintype E] [DecidableEq E]
  {J : Type} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)]

omit [DecidableEq P] [Fintype J] [DecidableEq J] [∀ j, NeZero (m j)] in
/-- **The main price of the revealed-input chain at the data of `fixC`**: with `D_{𝒥_e}` coprime
to `D_E`, `Π_main = sq(D_E)^a ∏_{e ∈ 𝒮} (K sq(D_{𝒥_e}))^{2a/72} ∏_{e ∈ 𝒮} (ᾱ_e/α)^{2θ/72}`. -/
theorem fixMainPrice_eq {L : ℕ} (hL : 1 ≤ L) (u : E → reservedCut.Half) (hu : Injective u)
    (Es : Finset J) (A : Finset ℤ) (hA : A ⊆ Icc 1 ((blockScale * L : ℕ) : ℤ))
    (hα : 0 < density (blockScale * L) A) (a θ : ℝ) (S : Finset E) (t : ZMod blockScale)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j)
    (hcopJ : ∀ e, (revealedModulus blockScale pr h (Jq e)).Coprime (∏ j ∈ Es, m j)) :
    mainPrice (paperPrice m Es (fun v => (fixSlots hcop u L S t Jq ω v).1)
        (fun v => (fixSlots hcop u L S t Jq ω v).2.2.1) L)
      (paperMeanDensity (FiniteLaw.uniform Unit) A (fun v => (fixSlots hcop u L S t Jq ω v).1)
        (fun v => (fixSlots hcop u L S t Jq ω v).2.2.1)
        (fun _ v => (fixSlots hcop u L S t Jq ω v).2.2.2)
        (fun _ v => (fixSlots hcop u L S t Jq ω v).2.1)) (fun _ => True) a θ
        (density (blockScale * L) A) =
      ((stepR m Es 1 : ℕ) : ℝ) ^ a *
        (∏ e, if e ∈ S then queryPrice pr h (2 * a / 72) (Jq e) else 1) *
        ∏ e, (if e ∈ S then (fixQueryLocalDensity hcop L A t (Jq e) (ω e) /
          density (blockScale * L) A) ^ (2 * θ / 72) else 1) := by
  have hmp := mainPrice_slotDatum m u hu (fun e => fixDatum hcop L S t Jq e (ω e)) (wholeDatum L)
    Es L A a θ (density (blockScale * L) A)
  unfold fixSlots
  rw [hmp]
  set α := density (blockScale * L) A
  set x : ℝ := ((leastSquare (∏ j ∈ Es, m j) : ℕ) : ℝ)
  have hx : 0 < x := Nat.cast_pos.mpr (leastSquare_pos _)
  have hK : (0 : ℝ) < blockScale := by norm_num [blockScale]
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
  have hN : ((blockScale * L : ℕ) : ℝ) ≠ 0 := by
    have : 0 < blockScale * L := Nat.mul_pos (by norm_num [blockScale]) (by omega)
    exact_mod_cast this.ne'
  have hk : 2 * Fintype.card E ≤ 72 := by
    have := card_slotQuery_none u hu
    omega
  have hpow : ∀ (y : ℝ) (hy : 0 ≤ y) (c : ℝ) (n : ℕ), (y ^ c) ^ n = y ^ (c * n) := by
    intro y hy c n
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy]
  have hw1 : datumPrice m Es L (wholeDatum L) = x := by
    unfold datumPrice wholeDatum stepR
    simp only [one_mul]
    rw [div_self hN, one_mul]
  have hw2 : datumDensity A (wholeDatum L) = α := datumDensity_wholeDatum A hA
  have hfd : ∀ e, e ∈ S → fixDatum hcop L S t Jq e (ω e) =
      ⟨revealedModulus blockScale pr h (Jq e), revealedResidue hcop (Jq e) (ω e), L,
        ((leastPosRep t : ℤ) - 1) * L⟩ := by
    intro e he
    unfold fixDatum
    rw [ite_eq_left_of_eq_true _ _ (eq_true he)]
  have hfw : ∀ e, e ∉ S → fixDatum hcop L S t Jq e (ω e) = wholeDatum L := by
    intro e he
    unfold fixDatum
    rw [ite_eq_right_of_eq_false _ _ (eq_false he)]
  have hquery : ∀ e, ((datumPrice m Es L (fixDatum hcop L S t Jq e (ω e))) ^ (a / 72)) ^ 2 =
      (if e ∈ S then queryPrice pr h (2 * a / 72) (Jq e) else 1) * x ^ (2 * a / 72) := by
    intro e
    by_cases he : e ∈ S
    · have hq1 : datumPrice m Es L (fixDatum hcop L S t Jq e (ω e)) =
          (blockScale * (leastSquare (revealedModulus blockScale pr h (Jq e)) : ℝ)) * x := by
        rw [hfd e he]
        unfold datumPrice stepR
        simp only
        rw [leastSquare_mul (hcopJ e)]
        push_cast
        field_simp
        ring
      have hy : 0 ≤ (blockScale : ℝ) *
          (leastSquare (revealedModulus blockScale pr h (Jq e)) : ℝ) :=
        mul_nonneg hK.le (Nat.cast_nonneg _)
      rw [hq1, hpow _ (mul_nonneg hy hx.le), Real.mul_rpow hy hx.le]
      simp only [he, ↓reduceIte]
      unfold queryPrice queryConductor
      congr 2 <;> push_cast <;> ring
    · rw [hfw e he, hw1, hpow _ hx.le]
      simp only [he, ↓reduceIte, one_mul]
      congr 1
      push_cast
      ring
  have hdens : ∀ e, ((datumDensity A (fixDatum hcop L S t Jq e (ω e)) / α) ^ (θ / 72)) ^ 2 =
      if e ∈ S then (fixQueryLocalDensity hcop L A t (Jq e) (ω e) / α) ^ (2 * θ / 72)
        else 1 := by
    intro e
    by_cases he : e ∈ S
    · have hq2 : datumDensity A (fixDatum hcop L S t Jq e (ω e)) =
          fixQueryLocalDensity hcop L A t (Jq e) (ω e) := by
        rw [hfd e he]
        unfold datumDensity fixQueryLocalDensity localDensity
        simp only
        rw [blockInterval_eq_Icc]
      rw [hq2, hpow (fixQueryLocalDensity hcop L A t (Jq e) (ω e) / α)
        (div_nonneg (localDensity_nonneg _ _ _ _ _ _) hα.le)]
      simp only [he, ↓reduceIte]
      congr 1
      push_cast
      ring
    · rw [hfw e he, hw2, div_self hα.ne', Real.one_rpow, one_pow]
      simp only [he, ↓reduceIte]
  simp only [hw1, hw2, hquery, hdens, div_self hα.ne', Real.one_rpow, one_pow, one_mul,
    prod_mul_distrib, prod_const, card_univ]
  rw [hpow _ hx.le, hpow _ hx.le]
  have hxx : x ^ (2 * a / 72 * (Fintype.card E : ℝ)) *
      x ^ (a / 72 * ((72 - 2 * Fintype.card E : ℕ) : ℝ)) = x ^ a := by
    rw [← Real.rpow_add hx]
    congr 1
    rw [Nat.cast_sub hk]
    push_cast
    ring
  have hst : ((stepR m Es 1 : ℕ) : ℝ) = x := by
    unfold x stepR
    rw [one_mul]
  rw [hst, ← hxx]
  ring

end FixPrice

section FixFirst

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- **The first bound of `hfirst` for `fixC`, averaged over the residues**
(`lem:bracket-energy` first bound with the structured slot data of `lem:envelope-energy` at fixed
intervals, at `ϑ`): for a valid term with `D_{f∪g} ≠ 1` (all slots changed),
`E_ω |E_{f,g}(𝒥, ω)| ≤ (1 + u_L) Π_𝒮 Y ∏_f u ∏_g u' + ∏ ‖Λ‖ C_dc L^{-σ} α`, with
`Π_𝒮 = fixedPrice` (the factor `K^{2θ/72}` per active query is the mean of the local density on
the fixed interval, `fix_localDensity_mean_le`). -/
theorem fix_first_mean_le (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    {Yf : ℕ → Finset ℤ → ℝ} {a' θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (hcex : IsLeastCounterexample Yf a' θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1)
    (hθd : θ = densityExponent)
    (ha : 0 ≤ a') (hC0 : 0 ≤ C0) (hL : 2 ≤ L) (hY0 : Yf L ∅ ≤ 0)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0)
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (f g : BlockAtom Bk J L → Bool)
    (hg : g ∈ validChoices f)
    {qE cE : ℕ} (hDE : ∏ b ∈ (termSet f g), crtModuli m₀ blk p L b = qE * cE) (hqE : Squarefree qE)
    (hcE : IsSquare cE) (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl) (hcopE : qE.Coprime cE)
    (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    (S : Finset E) (t : ZMod blockScale)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (hcopJ : ∀ e, (revealedModulus blockScale pr h (Jq e)).Coprime
      (∏ j ∈ termSet f g, crtModuli m₀ blk p L j))
    (u : E → reservedCut.Half) (hu : Injective u)
    (hD0 : ∀ ω v, 1 ≤ (fixSlots hcop u L S t Jq ω v).1)
    (hD0M : ∀ ω v, (fixSlots hcop u L S t Jq ω v).1 ∣ M0)
    (hcop0 : ∀ ω v k, ((fixSlots hcop u L S t Jq ω v).1).Coprime (crtModuli m₀ blk p L k))
    (hM : ∀ ω v, (fixSlots hcop u L S t Jq ω v).2.2.1 = blockScale * L ∨
      (fixSlots hcop u L S t Jq ω v).2.2.1 = L)
    (hchg : ∀ ω v, ¬((fixSlots hcop u L S t Jq ω v).1 *
      ∏ j ∈ (termSet f g), crtModuli m₀ blk p L j = 1 ∧
      (fixSlots hcop u L S t Jq ω v).2.2.1 = blockScale * L))
    (Q' : Slot → ℝ)
    {Cdc σ : ℝ}
    (hrest : ∀ ω v, True → ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll (crtModuli m₀ blk p L) (termSet f g)
        (fixSlots hcop u L S t Jq ω v).1 (fixSlots hcop u L S t Jq ω v).2.2.1 : ℕ) : ℤ) →
      referenceEnergy (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
          (child (crtModuli m₀ blk p L) (termSet f g) (Q' v) B
            (blockScale * stepEll (crtModuli m₀ blk p L)
            (termSet f g) (fixSlots hcop u L S t Jq ω v).1
            (fixSlots hcop u L S t Jq ω v).2.2.1)) ≤
        Yf (stepEll (crtModuli m₀ blk p L) (termSet f g) (fixSlots hcop u L S t Jq ω v).1
          (fixSlots hcop u L S t Jq ω v).2.2.1) B)
    (hdc : ∀ ω, |structuredEnergy
          (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
          (FiniteLaw.uniform Unit)
          (liftWeight (termSet f g)
            (selectedWeight (termSet f g)
              (crtLaws blk (prefix_pairwise hpair) L (termLaw D L Qb f g)))
            (uniformRest (Xa := fun b => ZMod (crtModuli m₀ blk p L b)) (termSet f g)))
          (paperInputs (crtModuli m₀ blk p L) (termSet f g) (paperCutoff (blockScale * L)) A
            (fun v => (fixSlots hcop u L S t Jq ω v).1)
            (fun v => (fixSlots hcop u L S t Jq ω v).2.2.1)
            (fun _ v => (fixSlots hcop u L S t Jq ω v).2.2.2)
            (fun _ v => (fixSlots hcop u L S t Jq ω v).2.1)) -
        structuredEnergy
          (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
          (FiniteLaw.uniform Unit)
          (liftWeight (termSet f g)
            (selectedWeight (termSet f g)
              (crtLaws blk (prefix_pairwise hpair) L (termLaw D L Qb f g)))
            (uniformRest (Xa := fun b => ZMod (crtModuli m₀ blk p L b)) (termSet f g)))
          (fun _ => revealedModel (crtModuli m₀ blk p L) (termSet f g) A
            (fun v => (fixSlots hcop u L S t Jq ω v).1)
            (fun v => (fixSlots hcop u L S t Jq ω v).2.2.1)
            (fun v => (fixSlots hcop u L S t Jq ω v).2.2.2)
            (fun v => (fixSlots hcop u L S t Jq ω v).2.1) Q')| ≤
      Cdc * totalVariation
        (selectedWeight (termSet f g)
          (crtLaws blk (prefix_pairwise hpair) L (termLaw D L Qb f g))) *
        (L : ℝ) ^ (-σ) * density (blockScale * L) A)
    (hatom : ∀ b ∈ termSet f g, ∀ hb : 0 < totalVariation (lawDensity (termLaw D L Qb f g b)),
      MixedLpBound (variationLaw _ hb) (72 / θ) 1)
    (uQ : BlockAtom Bk J L → ℝ)
    (hQ : ∀ b, (∑ z, |lawDensity (Qb b) z|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a' ≤ uQ b)
    (hR : ∀ b, (∑ z, |lawDensity (recLaw D L b) z|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a' ≤ D.GB.uprice L b) :
    (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect (fun ω =>
      |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise hpair) L
        (termLaw D L Qb f g)))
        (pairInputs u u (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
          (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
          (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)|) ≤
      (1 + scaleU blockScale M0 Qcl stageTau L) *
          (fixedPrice pr h (2 * a' / 72) S Jq * Yf L A *
            ((∏ b, if f b then uQ b else 1) * ∏ b, (if g b then D.GB.uprice L b else 1))) +
        (∏ b : {b // b ∈ termSet f g}, ∑ x : Slot → BlockLabel m₀ blk p L b.1,
          |lawDensity (termLaw D L Qb f g b.1) x|) *
          (Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  have hα := hcex.density_pos hθ.ne' hY0
  have hA := hcex.admissible.1
  have hYpos : 0 ≤ Yf L A := le_trans (by
    exact mul_nonneg (mul_nonneg hC0 (Real.rpow_nonneg (by positivity) _))
      (Real.rpow_nonneg (density_nonneg _ _) _)) hcex.lower.le
  set NΛ := ∏ b : {b // b ∈ termSet f g}, ∑ x : Slot → BlockLabel m₀ blk p L b.1,
    |lawDensity (termLaw D L Qb f g b.1) x| with hNΛ
  have hN0 : 0 ≤ NΛ := prod_nonneg fun b _ => sum_nonneg fun _ _ => abs_nonneg _
  set α := density (blockScale * L) A
  set R := ((stepR (crtModuli m₀ blk p L) (termSet f g) 1 : ℕ) : ℝ) ^ a'
  set Pq := ∏ e, if e ∈ S then queryPrice pr h (2 * a' / 72) (Jq e) else 1
  set KS := ∏ e, if e ∈ S then (blockScale : ℝ) ^ (2 * θ / 72) else 1
  set uL := scaleU blockScale M0 Qcl stageTau L
  set C := Cdc * (L : ℝ) ^ (-σ) * α
  set Dens : (E → ∀ j : Option P, CoordSpace blockScale pr h j) → ℝ := fun ω =>
    ∏ e, if e ∈ S then (fixQueryLocalDensity hcop L A t (Jq e) (ω e) / α) ^ (2 * θ / 72)
      else 1
  have hR0 : 0 ≤ R := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hPq0 : 0 ≤ Pq := prod_nonneg fun e _ => by
    split_ifs
    · exact queryPrice_nonneg pr h _ _
    · exact zero_le_one
  have hu0 : 0 ≤ uL := scaleU_nonneg _ _ _ _ _
  have hpt : ∀ ω, |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise hpair) L
        (termLaw D L Qb f g)))
        (pairInputs u u (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
          (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
          (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
      (NΛ * (1 + uL) * R * Pq * Yf L A) * Dens ω + NΛ * C := by
    intro ω
    have h := fix_first_le_chain hcop D hpair hcex hθ hθ2 ha hC0 hL hY0 hsc hM0 Qb f g hDE hqE
      hcE hcE0 hcQ hcopE hqN S t Jq ω u (hD0 ω) (hD0M ω) (hcop0 ω) (hM ω) (fun _ => True)
      (fun v _ => hchg ω v) Q' (fun v hv _ => absurd trivial hv) (hrest ω) (hdc ω)
      hatom
    rw [fixMainPrice_eq hcop (crtModuli m₀ blk p L) (by omega) u hu (termSet f g) A hA hα a' θ
      S t Jq ω hcopJ] at h
    refine h.trans (le_of_eq ?_)
    ring
  have hmean : (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
      Dens ≤ KS :=
    fix_localDensity_mean_le hcop (by omega) A hα (by positivity) (by linarith) S t Jq
  have hprice := termPrice_le D L hpair Qb uQ f g hg hQ hR
  have hK : 0 ≤ NΛ * (1 + uL) * R * Pq * Yf L A := by positivity
  have hfix : Pq * KS = fixedPrice pr h (2 * a' / 72) S Jq := by
    unfold fixedPrice
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro e _
    split_ifs
    · rw [hθd]
      ring
    · ring
  calc (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect (fun ω =>
        |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise hpair) L
          (termLaw D L Qb f g)))
          (pairInputs u u (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
            (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
            (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)|)
      ≤ (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect (fun ω =>
          (NΛ * (1 + uL) * R * Pq * Yf L A) * Dens ω + NΛ * C) :=
        FiniteLaw.expect_mono _ hpt
    _ = (NΛ * (1 + uL) * R * Pq * Yf L A) *
          (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect Dens +
          NΛ * C := by
        rw [FiniteLaw.expect_add, FiniteLaw.expect_const_mul, FiniteLaw.expect_const]
    _ ≤ (NΛ * (1 + uL) * R * Pq * Yf L A) * KS + NΛ * C := by
        have := mul_le_mul_of_nonneg_left hmean hK
        linarith
    _ = (1 + uL) * (Pq * KS) * Yf L A * (NΛ * R) + NΛ * C := by ring
    _ ≤ (1 + uL) * (fixedPrice pr h (2 * a' / 72) S Jq * Yf L A *
          ((∏ b, if f b then uQ b else 1) * ∏ b, (if g b then D.GB.uprice L b else 1))) +
          NΛ * C := by
        rw [hfix]
        have h1 : 0 ≤ (1 + uL) * fixedPrice pr h (2 * a' / 72) S Jq * Yf L A := by
          have := fixedPrice_nonneg pr h (2 * a' / 72) S Jq
          positivity
        have := mul_le_mul_of_nonneg_left hprice h1
        nlinarith


/-- The slots whose datum is not `F_A`: the two slots of each active query `e ∈ 𝒮`. -/
noncomputable def fixChanged (u : E → reservedCut.Half) (S : Finset E) (v : Slot) : Bool :=
  (slotQuery u v).any fun e => decide (e ∈ S)

omit [DecidableEq J₀] [DecidableEq P] in
/-- A slot of `F_A` carries the outside datum. -/
theorem fixSlots_of_not_changed {L : ℕ} (u : E → reservedCut.Half) (S : Finset E)
    (t : ZMod blockScale)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (v : Slot)
    (hv : fixChanged u S v = false) : fixSlots hcop u L S t Jq ω v = wholeDatum L := by
  unfold fixSlots
  rw [slotDatum_eq_optDatum]
  unfold fixChanged at hv
  rcases hq : slotQuery u v with _ | e
  · rfl
  · rw [hq] at hv
    simp only [Option.any_some, decide_eq_false_iff_not] at hv
    change fixDatum hcop L S t Jq e (ω e) = wholeDatum L
    unfold fixDatum
    rw [ite_eq_right_of_eq_false _ _ (eq_false hv)]

omit [DecidableEq J₀] [DecidableEq P] in
/-- A slot of an active query has an interval of length `L`. -/
theorem fixSlots_length_of_changed {L : ℕ} (u : E → reservedCut.Half) (S : Finset E)
    (t : ZMod blockScale)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (v : Slot)
    (hv : fixChanged u S v = true) : (fixSlots hcop u L S t Jq ω v).2.2.1 = L := by
  unfold fixSlots
  rw [slotDatum_eq_optDatum]
  unfold fixChanged at hv
  rcases hq : slotQuery u v with _ | e
  · rw [hq] at hv
    simp at hv
  · rw [hq] at hv
    simp only [Option.any_some, decide_eq_true_eq] at hv
    change (fixDatum hcop L S t Jq e (ω e)).2.2.1 = L
    unfold fixDatum
    rw [ite_eq_left_of_eq_true _ _ (eq_true hv)]

omit [DecidableEq J₀] [DecidableEq P] in
/-- **The main price does not see the slots of `F_A`** (data of `fixC`). -/
theorem mainPrice_fixSlots_congr {Jt : Type} [Fintype Jt] [DecidableEq Jt] (m : Jt → ℕ)
    [∀ j, NeZero (m j)] {L : ℕ} (u : E → reservedCut.Half) (Es : Finset Jt) (A : Finset ℤ)
    (hA : A ⊆ Icc 1 ((blockScale * L : ℕ) : ℤ)) (hα : 0 < density (blockScale * L) A)
    (a θ : ℝ) (S : Finset E) (t : ZMod blockScale)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (changed : Slot → Prop)
    [DecidablePred changed] (hch : ∀ v, ¬changed v → fixChanged u S v = false) :
    mainPrice (paperPrice m Es (fun v => (fixSlots hcop u L S t Jq ω v).1)
        (fun v => (fixSlots hcop u L S t Jq ω v).2.2.1) L)
      (paperMeanDensity (FiniteLaw.uniform Unit) A (fun v => (fixSlots hcop u L S t Jq ω v).1)
        (fun v => (fixSlots hcop u L S t Jq ω v).2.2.1)
        (fun _ v => (fixSlots hcop u L S t Jq ω v).2.2.2)
        (fun _ v => (fixSlots hcop u L S t Jq ω v).2.1)) changed a θ
        (density (blockScale * L) A) =
    mainPrice (paperPrice m Es (fun v => (fixSlots hcop u L S t Jq ω v).1)
        (fun v => (fixSlots hcop u L S t Jq ω v).2.2.1) L)
      (paperMeanDensity (FiniteLaw.uniform Unit) A (fun v => (fixSlots hcop u L S t Jq ω v).1)
        (fun v => (fixSlots hcop u L S t Jq ω v).2.2.1)
        (fun _ v => (fixSlots hcop u L S t Jq ω v).2.2.2)
        (fun _ v => (fixSlots hcop u L S t Jq ω v).2.1)) (fun _ => True) a θ
        (density (blockScale * L) A) := by
  unfold mainPrice
  congr 1
  rw [prod_filter, prod_filter]
  apply prod_congr rfl
  intro v _
  by_cases hv : changed v
  · simp only [hv, ↓reduceIte]
  · have hq := hch v hv
    have hd : paperMeanDensity (FiniteLaw.uniform Unit) A
        (fun v => (fixSlots hcop u L S t Jq ω v).1)
        (fun v => (fixSlots hcop u L S t Jq ω v).2.2.1)
        (fun _ v => (fixSlots hcop u L S t Jq ω v).2.2.2)
        (fun _ v => (fixSlots hcop u L S t Jq ω v).2.1) v = density (blockScale * L) A := by
      have h1 : paperMeanDensity (FiniteLaw.uniform Unit) A
          (fun v => (fixSlots hcop u L S t Jq ω v).1)
          (fun v => (fixSlots hcop u L S t Jq ω v).2.2.1)
          (fun _ v => (fixSlots hcop u L S t Jq ω v).2.2.2)
          (fun _ v => (fixSlots hcop u L S t Jq ω v).2.1) v =
          datumDensity A (fixSlots hcop u L S t Jq ω v) := by
        unfold paperMeanDensity
        rw [FiniteLaw.expect_const]
        rfl
      rw [h1, fixSlots_of_not_changed hcop u S t Jq ω v hq, datumDensity_wholeDatum A hA]
    simp only [hv, ↓reduceIte, hd, div_self hα.ne', Real.one_rpow]

/-- **The first bound for `fixC` with only the active query slots changed**
(`fix_first_mean_le` with the slots of `F_A` unchanged; for the term `f = g = ∅`). The slots of
`F_A` need `hun`. -/
theorem fix_first_mean_le_query (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    {Yf : ℕ → Finset ℤ → ℝ} {a' θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (hcex : IsLeastCounterexample Yf a' θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1)
    (hθd : θ = densityExponent)
    (ha : 0 ≤ a') (hC0 : 0 ≤ C0) (hL : 2 ≤ L) (hY0 : Yf L ∅ ≤ 0)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0)
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (f g : BlockAtom Bk J L → Bool)
    (hg : g ∈ validChoices f)
    {qE cE : ℕ} (hDE : ∏ b ∈ (termSet f g), crtModuli m₀ blk p L b = qE * cE) (hqE : Squarefree qE)
    (hcE : IsSquare cE) (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl) (hcopE : qE.Coprime cE)
    (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    (S : Finset E) (t : ZMod blockScale)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (hcopJ : ∀ e, (revealedModulus blockScale pr h (Jq e)).Coprime
      (∏ j ∈ termSet f g, crtModuli m₀ blk p L j))
    (u : E → reservedCut.Half) (hu : Injective u)
    (hD0 : ∀ ω v, 1 ≤ (fixSlots hcop u L S t Jq ω v).1)
    (hD0M : ∀ ω v, (fixSlots hcop u L S t Jq ω v).1 ∣ M0)
    (hcop0 : ∀ ω v k, ((fixSlots hcop u L S t Jq ω v).1).Coprime (crtModuli m₀ blk p L k))
    (hM : ∀ ω v, (fixSlots hcop u L S t Jq ω v).2.2.1 = blockScale * L ∨
      (fixSlots hcop u L S t Jq ω v).2.2.1 = L)
    (Q' : Slot → ℝ)
    (hun : ∀ ω v, fixChanged u S v = false → ∀ x, referenceEnergy
      (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
      (revealedModel (crtModuli m₀ blk p L) (termSet f g) A
        (fun v => (fixSlots hcop u L S t Jq ω v).1)
        (fun v => (fixSlots hcop u L S t Jq ω v).2.2.1)
        (fun v => (fixSlots hcop u L S t Jq ω v).2.2.2)
        (fun v => (fixSlots hcop u L S t Jq ω v).2.1) Q' v x) ≤ Yf L A)
    {Cdc σ : ℝ}
    (hrest : ∀ ω v, fixChanged u S v = true → ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll (crtModuli m₀ blk p L) (termSet f g)
        (fixSlots hcop u L S t Jq ω v).1 (fixSlots hcop u L S t Jq ω v).2.2.1 : ℕ) : ℤ) →
      referenceEnergy (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
          (child (crtModuli m₀ blk p L) (termSet f g) (Q' v) B
            (blockScale * stepEll (crtModuli m₀ blk p L)
            (termSet f g) (fixSlots hcop u L S t Jq ω v).1
            (fixSlots hcop u L S t Jq ω v).2.2.1)) ≤
        Yf (stepEll (crtModuli m₀ blk p L) (termSet f g) (fixSlots hcop u L S t Jq ω v).1
          (fixSlots hcop u L S t Jq ω v).2.2.1) B)
    (hdc : ∀ ω, |structuredEnergy
          (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
          (FiniteLaw.uniform Unit)
          (liftWeight (termSet f g)
            (selectedWeight (termSet f g)
              (crtLaws blk (prefix_pairwise hpair) L (termLaw D L Qb f g)))
            (uniformRest (Xa := fun b => ZMod (crtModuli m₀ blk p L b)) (termSet f g)))
          (paperInputs (crtModuli m₀ blk p L) (termSet f g) (paperCutoff (blockScale * L)) A
            (fun v => (fixSlots hcop u L S t Jq ω v).1)
            (fun v => (fixSlots hcop u L S t Jq ω v).2.2.1)
            (fun _ v => (fixSlots hcop u L S t Jq ω v).2.2.2)
            (fun _ v => (fixSlots hcop u L S t Jq ω v).2.1)) -
        structuredEnergy
          (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
          (FiniteLaw.uniform Unit)
          (liftWeight (termSet f g)
            (selectedWeight (termSet f g)
              (crtLaws blk (prefix_pairwise hpair) L (termLaw D L Qb f g)))
            (uniformRest (Xa := fun b => ZMod (crtModuli m₀ blk p L b)) (termSet f g)))
          (fun _ => revealedModel (crtModuli m₀ blk p L) (termSet f g) A
            (fun v => (fixSlots hcop u L S t Jq ω v).1)
            (fun v => (fixSlots hcop u L S t Jq ω v).2.2.1)
            (fun v => (fixSlots hcop u L S t Jq ω v).2.2.2)
            (fun v => (fixSlots hcop u L S t Jq ω v).2.1) Q')| ≤
      Cdc * totalVariation
        (selectedWeight (termSet f g)
          (crtLaws blk (prefix_pairwise hpair) L (termLaw D L Qb f g))) *
        (L : ℝ) ^ (-σ) * density (blockScale * L) A)
    (hatom : ∀ b ∈ termSet f g, ∀ hb : 0 < totalVariation (lawDensity (termLaw D L Qb f g b)),
      MixedLpBound (variationLaw _ hb) (72 / θ) 1)
    (uQ : BlockAtom Bk J L → ℝ)
    (hQ : ∀ b, (∑ z, |lawDensity (Qb b) z|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a' ≤ uQ b)
    (hR : ∀ b, (∑ z, |lawDensity (recLaw D L b) z|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a' ≤ D.GB.uprice L b) :
    (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect (fun ω =>
      |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise hpair) L
        (termLaw D L Qb f g)))
        (pairInputs u u (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
          (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
          (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)|) ≤
      (1 + scaleU blockScale M0 Qcl stageTau L) *
          (fixedPrice pr h (2 * a' / 72) S Jq * Yf L A *
            ((∏ b, if f b then uQ b else 1) * ∏ b, (if g b then D.GB.uprice L b else 1))) +
        (∏ b : {b // b ∈ termSet f g}, ∑ x : Slot → BlockLabel m₀ blk p L b.1,
          |lawDensity (termLaw D L Qb f g b.1) x|) *
          (Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  have hα := hcex.density_pos hθ.ne' hY0
  have hA := hcex.admissible.1
  have hYpos : 0 ≤ Yf L A := le_trans (by
    exact mul_nonneg (mul_nonneg hC0 (Real.rpow_nonneg (by positivity) _))
      (Real.rpow_nonneg (density_nonneg _ _) _)) hcex.lower.le
  set NΛ := ∏ b : {b // b ∈ termSet f g}, ∑ x : Slot → BlockLabel m₀ blk p L b.1,
    |lawDensity (termLaw D L Qb f g b.1) x| with hNΛ
  have hN0 : 0 ≤ NΛ := prod_nonneg fun b _ => sum_nonneg fun _ _ => abs_nonneg _
  set α := density (blockScale * L) A
  set R := ((stepR (crtModuli m₀ blk p L) (termSet f g) 1 : ℕ) : ℝ) ^ a'
  set Pq := ∏ e, if e ∈ S then queryPrice pr h (2 * a' / 72) (Jq e) else 1
  set KS := ∏ e, if e ∈ S then (blockScale : ℝ) ^ (2 * θ / 72) else 1
  set uL := scaleU blockScale M0 Qcl stageTau L
  set C := Cdc * (L : ℝ) ^ (-σ) * α
  set Dens : (E → ∀ j : Option P, CoordSpace blockScale pr h j) → ℝ := fun ω =>
    ∏ e, if e ∈ S then (fixQueryLocalDensity hcop L A t (Jq e) (ω e) / α) ^ (2 * θ / 72)
      else 1
  have hR0 : 0 ≤ R := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hPq0 : 0 ≤ Pq := prod_nonneg fun e _ => by
    split_ifs
    · exact queryPrice_nonneg pr h _ _
    · exact zero_le_one
  have hu0 : 0 ≤ uL := scaleU_nonneg _ _ _ _ _
  have hpt : ∀ ω, |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise hpair) L
        (termLaw D L Qb f g)))
        (pairInputs u u (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
          (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
          (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
      (NΛ * (1 + uL) * R * Pq * Yf L A) * Dens ω + NΛ * C := by
    intro ω
    have hchg : ∀ v, fixChanged u S v = true → ¬((fixSlots hcop u L S t Jq ω v).1 *
        ∏ j ∈ termSet f g, crtModuli m₀ blk p L j = 1 ∧
        (fixSlots hcop u L S t Jq ω v).2.2.1 = blockScale * L) := by
      intro v hv h1
      have hKL : L ≠ blockScale * L := by
        have : 2 ≤ blockScale := by norm_num [blockScale]
        nlinarith
      rw [fixSlots_length_of_changed hcop u S t Jq ω v hv] at h1
      exact hKL h1.2
    have h := fix_first_le_chain hcop D hpair hcex hθ hθ2 ha hC0 hL hY0 hsc hM0 Qb f g hDE hqE
      hcE hcE0 hcQ hcopE hqN S t Jq ω u (hD0 ω) (hD0M ω) (hcop0 ω) (hM ω)
      (fun v => fixChanged u S v = true) hchg Q'
      (fun v hv x => hun ω v (by simpa using hv) x) (hrest ω) (hdc ω) hatom
    rw [mainPrice_fixSlots_congr hcop (crtModuli m₀ blk p L) u (termSet f g) A hA hα a' θ S t
      Jq ω (fun v => fixChanged u S v = true) (fun v hv => by simpa using hv)] at h
    rw [fixMainPrice_eq hcop (crtModuli m₀ blk p L) (by omega) u hu (termSet f g) A hA hα a' θ
      S t Jq ω hcopJ] at h
    refine h.trans (le_of_eq ?_)
    ring
  have hmean : (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
      Dens ≤ KS :=
    fix_localDensity_mean_le hcop (by omega) A hα (by positivity) (by linarith) S t Jq
  have hprice := termPrice_le D L hpair Qb uQ f g hg hQ hR
  have hK : 0 ≤ NΛ * (1 + uL) * R * Pq * Yf L A := by positivity
  have hfix : Pq * KS = fixedPrice pr h (2 * a' / 72) S Jq := by
    unfold fixedPrice
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro e _
    split_ifs
    · rw [hθd]
      ring
    · ring
  calc (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect (fun ω =>
        |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise hpair) L
          (termLaw D L Qb f g)))
          (pairInputs u u (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
            (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
            (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)|)
      ≤ (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect (fun ω =>
          (NΛ * (1 + uL) * R * Pq * Yf L A) * Dens ω + NΛ * C) :=
        FiniteLaw.expect_mono _ hpt
    _ = (NΛ * (1 + uL) * R * Pq * Yf L A) *
          (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect Dens +
          NΛ * C := by
        rw [FiniteLaw.expect_add, FiniteLaw.expect_const_mul, FiniteLaw.expect_const]
    _ ≤ (NΛ * (1 + uL) * R * Pq * Yf L A) * KS + NΛ * C := by
        have := mul_le_mul_of_nonneg_left hmean hK
        linarith
    _ = (1 + uL) * (Pq * KS) * Yf L A * (NΛ * R) + NΛ * C := by ring
    _ ≤ (1 + uL) * (fixedPrice pr h (2 * a' / 72) S Jq * Yf L A *
          ((∏ b, if f b then uQ b else 1) * ∏ b, (if g b then D.GB.uprice L b else 1))) +
          NΛ * C := by
        rw [hfix]
        have h1 : 0 ≤ (1 + uL) * fixedPrice pr h (2 * a' / 72) S Jq * Yf L A := by
          have := fixedPrice_nonneg pr h (2 * a' / 72) S Jq
          positivity
        have := mul_le_mul_of_nonneg_left hprice h1
        nlinarith

end FixFirst

end Sarkozy.BracketEnergy
