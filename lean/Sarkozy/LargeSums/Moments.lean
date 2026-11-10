module

public import Sarkozy.LargeSums.Core

@[expose] public section

/-!
# The `72`-th moments of the revealed inputs, and the decay `N^{-τ/4 + ε} ≤ L^{-1/825}`

LP (8 November 2026). The two scalar inputs of `lem:record:density-lp` at the large pieces:

* **`fixInputs_moment_le`**, **`envInputs_moment_le`**: the averaged `72`-th moments of the
  revealed inputs of `fixC` (every depth vector) and of `envC` (depth vectors that reveal the
  intervals) are at most `M₀^{72} |X₀|^{72} C_ε Q^ε K α` (`lem:record:lift-moments`(c), DC1's
  `input_moment_le_density` with `r = 36`). These are the moment steps of DC1's `fix_term_lp`,
  `env_term_lp`, stated for one slot;
* **`lp_decay_le`** ((S4)): `Q(N)^{1/2000} (N^τ)^{-1/4} ≤ L^{-1/825}` for `N = KL`, `L ≥ 1`
  (`1/40000 − 1/804 ≤ −1/825`).
-/

namespace Sarkozy.LargeSums

open Finset Function
open scoped BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.DensityDC Sarkozy.DensityChain

/-- **(S4) at `ε = 1/2000`**: `Q(KL)^{1/2000} ((KL)^τ)^{-1/4} ≤ L^{-1/825}` for `L ≥ 1`. -/
theorem lp_decay_le {L : ℕ} (hL : 1 ≤ L) :
    paperCutoff (blockScale * L) ^ ((1 : ℝ) / 2000) *
        ((((blockScale * L : ℕ) : ℝ) ^ stageTau) ^ (-((1 : ℝ) / 4))) ≤
      (L : ℝ) ^ (-Sarkozy.cancellationDecay) := by
  have hKL : (1 : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (by norm_num [blockScale]) (by omega)
  have hN0 : (0 : ℝ) < ((blockScale * L : ℕ) : ℝ) := lt_of_lt_of_le zero_lt_one hKL
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hLN : (L : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_mul_of_pos_left L (by norm_num [blockScale])
  unfold paperCutoff liftExponent
  rw [← Real.rpow_mul hN0.le, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
  have hexp : 1 / 20 * (1 / 2000) + stageTau * -(1 / 4) ≤ -Sarkozy.cancellationDecay := by
    norm_num [stageTau, Sarkozy.cancellationDecay]
  calc ((blockScale * L : ℕ) : ℝ) ^ (1 / 20 * (1 / 2000) + stageTau * -(1 / 4))
      ≤ (L : ℝ) ^ (1 / 20 * (1 / 2000) + stageTau * -(1 / 4)) :=
        Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one hL1) hLN
          (by norm_num [stageTau])
    _ ≤ (L : ℝ) ^ (-Sarkozy.cancellationDecay) := Real.rpow_le_rpow_of_exponent_le hL1 hexp

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

omit [DecidableEq J₀] in
/-- **The moments of the revealed inputs of `fixC`** (`lem:record:lift-moments`(c); the moment
step of DC1's `fix_term_lp`, at one slot). -/
theorem fixInputs_moment_le (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (u : E → reservedCut.Half) (t : ZMod blockScale)
    {L : ℕ} {A : Finset ℤ} {M0 Qcl Qpre N0 N0' : ℕ}
    (_hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L) (_hL : 1 ≤ L) (_hM0 : 1 ≤ M0)
    (_hp : ∀ j, (p L j).Prime) (_hinj : Injective (p L))
    (_hMod : modulus pr h ∣ M0) (S : Finset E)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (v : Slot),
    (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect (fun ω =>
      (FiniteLaw.uniform (ResidueSpace (crtModuli m₀ blk p L))).moment 72
        (pairInputs u u (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
          (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
          (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω v)) ≤
      (M0 : ℝ) ^ 72 * ((Fintype.card (ResidueSpace (blockModulus m₀ blk)) : ℝ) ^ 72 * C *
        paperCutoff (blockScale * L) ^ ε * ((blockScale : ℝ) * density (blockScale * L) A)) := by
  obtain ⟨C, hC, hc⟩ := input_moment_le_density 36 (by norm_num) ε hε
  refine ⟨C, hC, ?_⟩
  intro u t L A M0 Qcl Qpre N0 N0' hsc hL hM0 hp hinj hMod S Jq v
  set Q := paperCutoff (blockScale * L) with hQ
  have hJd : ∀ e, revealedModulus blockScale pr h (Jq e) ∣ modulus pr h :=
    fun e => revealedModulus_dvd (Jq e)
  have hD0M : ∀ ω v, (fixSlots hcop u L S t Jq ω v).1 ∣ M0 := by
    intro ω v
    rw [fixSlots_fst]
    unfold fixD0
    rcases slotQuery u v with _ | e
    · exact one_dvd _
    · change (if e ∈ S then revealedModulus blockScale pr h (Jq e) else 1) ∣ M0
      split_ifs
      · exact dvd_trans (hJd e) hMod
      · exact one_dvd _
  have hM : ∀ ω v, (fixSlots hcop u L S t Jq ω v).2.2.1 = blockScale * L ∨
      (fixSlots hcop u L S t Jq ω v).2.2.1 = L := by
    intro ω v
    rw [fixSlots_len]
    unfold fixM
    rcases slotQuery u v with _ | e
    · exact Or.inl rfl
    · change (if e ∈ S then L else blockScale * L) = blockScale * L ∨
        (if e ∈ S then L else blockScale * L) = L
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
  have hinputs : ∀ ω, pairInputs u u (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
      (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
      (unchangedInput (crtModuli m₀ blk p L) Q A L) ω ω =
      fun v => paperForm (crtModuli m₀ blk p L) Q A (fixSlots hcop u L S t Jq ω v) := by
    intro ω
    exact pairInputs_eq_slotDatum (crtModuli m₀ blk p L) u _ _ ω Q A _ (wholeDatum L)
      (fun e => revealedSlot_wrapInputCRT_eq_paperForm hcop L A S t Jq e (ω e))
      (unchangedInput_eq_paperForm _ Q A L)
  have hKL : 1 ≤ blockScale * L := Nat.mul_pos (by norm_num [blockScale]) (by omega)
  have hQ1 : 1 ≤ Q := one_le_paperCutoff hKL
  apply FiniteLaw.expect_le_const
  intro ω
  rw [hinputs ω]
  have hLM : L ≤ (fixSlots hcop u L S t Jq ω v).2.2.1 := by
    rcases hM ω v with h1 | h1
    · rw [h1]; exact Nat.le_mul_of_pos_left L (by norm_num [blockScale])
    · rw [h1]
  have hcut := cutoff_conditions_of_scale hsc hKL hLM
  have hD0le : (fixSlots hcop u L S t Jq ω v).1 ≤ M0 :=
    Nat.le_of_dvd (by omega) (hD0M ω v)
  have key := hc (blockModulus m₀ blk) (p L) hp hinj Q hQ1
    (fixSlots hcop u L S t Jq ω v).2.2.2 hL hLM hcut.1 hcut.2 hD0le
    (fixSlots hcop u L S t Jq ω v).2.1 A
  simp only [show (2 * 36 : ℕ) = 72 from rfl, Nat.cast_ofNat] at key
  exact key

/-- **The moments of the revealed inputs of `envC`** at a depth vector that reveals the
intervals (`lem:record:lift-moments`(c); the moment step of DC1's `env_term_lp`, at one slot). -/
theorem envInputs_moment_le (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (u : E → reservedCut.Half)
    {L : ℕ} {A : Finset ℤ} {M0 Qcl Qpre N0 N0' : ℕ}
    (_hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L) (_hL : 1 ≤ L) (_hM0 : 1 ≤ M0)
    (_hp : ∀ j, (p L j).Prime) (_hinj : Injective (p L))
    (_hMod : modulus pr h ∣ M0)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (_hJ : ∀ e, (Jq e none : ℕ) ≠ 0) (v : Slot),
    (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
      (fun ω => (FiniteLaw.uniform (ResidueSpace (crtModuli m₀ blk p L))).moment 72
        (pairInputs u u (revealedInputCRT blk hcop D L A Jq) (revealedInputCRT blk hcop D L A Jq)
          (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω v)) ≤
      (M0 : ℝ) ^ 72 * ((Fintype.card (ResidueSpace (blockModulus m₀ blk)) : ℝ) ^ 72 * C *
        paperCutoff (blockScale * L) ^ ε * ((blockScale : ℝ) * density (blockScale * L) A)) := by
  obtain ⟨C, hC, hc⟩ := input_moment_le_density 36 (by norm_num) ε hε
  refine ⟨C, hC, ?_⟩
  intro D u L A M0 Qcl Qpre N0 N0' hsc hL hM0 hp hinj hMod Jq hJ v
  set Q := paperCutoff (blockScale * L) with hQ
  have hdat : ∀ ω v, envSlots hcop u L Jq ω v =
      optDatum (fun e => envDatum hcop L Jq e (ω e)) (wholeDatum L) (slotQuery u v) :=
    fun ω v => slotDatum_eq_optDatum u _ _ v
  have hJd : ∀ e, revealedModulus blockScale pr h (Jq e) ∣ modulus pr h :=
    fun e => revealedModulus_dvd (Jq e)
  have hD0M : ∀ ω v, (envSlots hcop u L Jq ω v).1 ∣ M0 := by
    intro ω v
    rw [hdat]
    rcases slotQuery u v with _ | e
    · exact one_dvd _
    · exact dvd_trans (hJd e) hMod
  have hM : ∀ ω v, (envSlots hcop u L Jq ω v).2.2.1 = blockScale * L ∨
      (envSlots hcop u L Jq ω v).2.2.1 = L := by
    intro ω v
    rw [hdat]
    rcases slotQuery u v with _ | e
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hinputs : ∀ ω, pairInputs u u (revealedInputCRT blk hcop D L A Jq)
      (revealedInputCRT blk hcop D L A Jq) (unchangedInput (crtModuli m₀ blk p L) Q A L) ω ω =
      fun v => paperForm (crtModuli m₀ blk p L) Q A (envSlots hcop u L Jq ω v) := by
    intro ω
    exact pairInputs_eq_slotDatum (crtModuli m₀ blk p L) u _ _ ω Q A _ (wholeDatum L)
      (fun e => revealedInputCRT_eq_paperForm hcop D L A Jq e (ω e) (hJ e))
      (unchangedInput_eq_paperForm _ Q A L)
  have hKL : 1 ≤ blockScale * L := Nat.mul_pos (by norm_num [blockScale]) (by omega)
  have hQ1 : 1 ≤ Q := one_le_paperCutoff hKL
  apply FiniteLaw.expect_le_const
  intro ω
  rw [hinputs ω]
  have hLM : L ≤ (envSlots hcop u L Jq ω v).2.2.1 := by
    rcases hM ω v with h1 | h1
    · rw [h1]; exact Nat.le_mul_of_pos_left L (by norm_num [blockScale])
    · rw [h1]
  have hcut := cutoff_conditions_of_scale hsc hKL hLM
  have hD0le : (envSlots hcop u L Jq ω v).1 ≤ M0 :=
    Nat.le_of_dvd (by omega) (hD0M ω v)
  have key := hc (blockModulus m₀ blk) (p L) hp hinj Q hQ1 (envSlots hcop u L Jq ω v).2.2.2
    hL hLM hcut.1 hcut.2 hD0le (envSlots hcop u L Jq ω v).2.1 A
  simp only [show (2 * 36 : ℕ) = 72 from rfl, Nat.cast_ofNat] at key
  exact key

end Sarkozy.LargeSums
