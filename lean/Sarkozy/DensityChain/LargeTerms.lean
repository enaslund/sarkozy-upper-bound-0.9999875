module

public import Sarkozy.DensityChain.Records
public import Sarkozy.DensityChain.LargeProducts
public import Sarkozy.DensityChain.ChainTerms

@[expose] public section

/-!
# `lem:record:density-lp` at the terms of `envC`

`lem:record:density-lp` bounds a term of the bracket expansion whose selected product is large
by Hölder in `L^{72}` (uniform one-slot marginals of the variation) and the `72`-th moments of
the inputs (`lem:record:lift-moments`(c)). This file instantiates the steps of
`DensityChain.LargeProducts` at the energies of `envC`:

* `isPositiveRecord_signedIntegral`, `isPositiveRecord_muLaw`: the reference laws of the atoms
  are positive records, by (R3) (`Reference.unif₀`, `unifp`);
* `totalVariation_prod`: the mass of a product weight is the product of the masses;
* **`env_term_lp`**: for every `ε > 0` there is `C > 0` such that every term `(f, g)` of `envC`
  at a depth vector that reveals the intervals satisfies
  `E_ω |E_{f,g}(𝒥, ω)| ≤ ∏_𝔟 termWeight(𝔟, f 𝔟, g 𝔟) · M₀^{72} |X₀|^{72} C Q^ε K α`,
  `Q = Q(KL)`, when the increments `Q_𝔟` are positive records. No other per-term input is
  needed: the bound holds for **every** term, and Rankin's trick (`sum_choice_large_le`) sums it
  over the large unions.
-/

namespace Sarkozy.DensityChain

open Finset Function
open scoped BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.DensityDC

/-- A probability law with uniform one-slot marginals is a positive record. -/
theorem isPositiveRecord_signedIntegral {X : Type} [Fintype X] [Nonempty X]
    (μ : FiniteLaw (Slot → X)) (hμ : HasUniformMarginals μ) :
    IsPositiveRecord (signedIntegral μ.weight) := by
  refine ⟨fun f hf => ?_, fun v g => ?_⟩
  · change 0 ≤ ∑ z, μ.weight z * f z
    exact sum_nonneg fun z _ => mul_nonneg (μ.nonneg z) (hf z)
  · have h1 := hμ v g
    rw [FiniteLaw.expect_uniform] at h1
    unfold mass
    change ∑ z, μ.weight z * g (z v) = (∑ z, μ.weight z * 1) * _
    have h2 : ∑ z, μ.weight z * (1 : ℝ) = 1 := by
      simp only [mul_one]
      exact μ.total
    rw [h2, one_mul]
    exact h1

/-- **The mass of a product weight is the product of the masses.** -/
theorem totalVariation_prod {I : Type*} [Fintype I] [DecidableEq I] {Y : I → Type*}
    [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)] (ρ : ∀ i, (Slot → Y i) → ℝ) :
    totalVariation (fun z : Slot → ∀ i, Y i => ∏ i, ρ i (fun v => z v i)) =
      ∏ i, totalVariation (ρ i) := by
  set e : (Slot → ∀ i, Y i) ≃ (∀ i, Slot → Y i) := Equiv.piComm (fun (_ : Slot) (i : I) => Y i)
  unfold totalVariation
  rw [← Equiv.sum_comp e.symm]
  simp_rw [Finset.abs_prod]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rfl

/-- The mass of a positive record is its total variation. -/
theorem totalVariation_lawDensity_of_positive {X : Type} [Fintype X] [DecidableEq X]
    {κ : SlotMeasure X} (h : IsPositiveRecord κ) :
    totalVariation (lawDensity κ) = mass κ := by
  have hpos : ∀ z, 0 ≤ lawDensity κ z := fun z => h.1 _ fun y => by split_ifs <;> norm_num
  unfold totalVariation mass
  rw [apply_eq_sum_lawDensity' κ (fun _ => 1)]
  exact sum_congr rfl fun z _ => by rw [abs_of_nonneg (hpos z), mul_one]

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

omit [DecidableEq P] in
/-- The reference law of an atom is a positive record, by (R3) (the tail moduli are prime). -/
theorem isPositiveRecord_muLaw (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (hp : ∀ j, (p L j).Prime) (b : BlockAtom Bk J L) : IsPositiveRecord (muLaw D L b) := by
  unfold muLaw TheoremCBlock.Reference.law
  rcases b with β | j
  · exact isPositiveRecord_signedIntegral (D.R.μ₀ β) (D.R.unif₀ β)
  · exact isPositiveRecord_signedIntegral (D.R.μp (p L j)) (D.R.unifp (p L j) (hp j))

omit [DecidableEq P] in
/-- The atom laws of a term are positive records. -/
theorem isPositiveRecord_termLaw (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (hp : ∀ j, (p L j).Prime) (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (hQ : ∀ b, IsPositiveRecord (Qb b)) (f g : BlockAtom Bk J L → Bool) (b : BlockAtom Bk J L) :
    IsPositiveRecord (BracketEnergy.termLaw D L Qb f g b) := by
  unfold BracketEnergy.termLaw
  by_cases hf : f b = true
  · simp only [hf, ↓reduceIte]
    exact hQ b
  · by_cases hg : g b = true
    · simp only [hf, hg, Bool.false_eq_true, ↓reduceIte]
      exact isPositiveRecord_recLaw D L b
    · simp only [hf, hg, Bool.false_eq_true, ↓reduceIte]
      exact isPositiveRecord_muLaw D L hp b

omit [DecidableEq P] in
/-- The mass of an atom law of a term is its `termWeight`. -/
theorem totalVariation_termLaw (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (hp : ∀ j, (p L j).Prime) (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (f g : BlockAtom Bk J L → Bool) (b : BlockAtom Bk J L) :
    totalVariation (lawDensity (BracketEnergy.termLaw D L Qb f g b)) =
      termWeight D L Qb b (f b) (g b) := by
  unfold termWeight
  by_cases hf : f b = true
  · simp only [hf, ↓reduceIte]
    unfold BracketEnergy.termLaw
    simp only [hf, ↓reduceIte]
    rfl
  · by_cases hg : g b = true
    · simp only [hf, hg, Bool.false_eq_true, ↓reduceIte]
      unfold BracketEnergy.termLaw
      simp only [hf, hg, Bool.false_eq_true, ↓reduceIte]
      rfl
    · simp only [hf, hg, Bool.false_eq_true, ↓reduceIte]
      have h1 : BracketEnergy.termLaw D L Qb f g b = muLaw D L b := by
        unfold BracketEnergy.termLaw
        simp only [hf, hg, Bool.false_eq_true, ↓reduceIte]
      rw [h1, totalVariation_lawDensity_of_positive (isPositiveRecord_muLaw D L hp b)]
      unfold muLaw TheoremCBlock.Reference.law mass
      rcases b with β | j
      · change ∑ z, (D.R.μ₀ β).weight z * 1 = 1
        simp only [mul_one]
        exact (D.R.μ₀ β).total
      · change ∑ z, (D.R.μp (p L j)).weight z * 1 = 1
        simp only [mul_one]
        exact (D.R.μp (p L j)).total

/-- **`lem:record:density-lp`, per term, at the energies of `envC`** (see the module docstring):
Hölder in `L^{72}` with the uniform marginals of the positive-record atom laws, and the
`72`-th moments of the paper's inputs `g^{I, D₀, s}` (`lem:record:lift-moments`(c),
`input_moment_le_density` with `r = 36`). -/
theorem env_term_lp (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (Qb : ∀ L b, TheoremCBlock.AtomMeasure m₀ blk p L b) (u : E → reservedCut.Half)
    {L : ℕ} {A : Finset ℤ} {M0 Qcl Qpre N0 N0' : ℕ}
    (_hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L) (_hL : 1 ≤ L) (_hM0 : 1 ≤ M0)
    (_hp : ∀ j, (p L j).Prime) (_hinj : Injective (p L))
    (_hMod : modulus pr h ∣ M0) (_hQpos : ∀ b, IsPositiveRecord (Qb L b))
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (_hJ : ∀ e, (Jq e none : ℕ) ≠ 0) (f g : BlockAtom Bk J L → Bool),
    (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
        (fun ω => envTermEnergy hcop D hpair Qb u L A Jq ω f g) ≤
      (∏ b, termWeight D L (Qb L) b (f b) (g b)) *
        ((M0 : ℝ) ^ 72 * ((Fintype.card (ResidueSpace (blockModulus m₀ blk)) : ℝ) ^ 72 * C *
          paperCutoff (blockScale * L) ^ ε * ((blockScale : ℝ) * density (blockScale * L) A))) := by
  obtain ⟨C, hC, hc⟩ := input_moment_le_density 36 (by norm_num) ε hε
  refine ⟨C, hC, ?_⟩
  intro D hpair Qb u L A M0 Qcl Qpre N0 N0' hsc hL hM0 hp hinj hMod hQpos Jq hJ f g
  set Λ' := crtLaws blk (prefix_pairwise (hpair L)) L (BracketEnergy.termLaw D L (Qb L) f g)
    with hΛ'
  set ρ : (Slot → ResidueSpace (crtModuli m₀ blk p L)) → ℝ := lawDensity (tensorLaw Λ') with hρ
  set Q := paperCutoff (blockScale * L) with hQ
  set a : (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) → Slot →
      ResidueSpace (crtModuli m₀ blk p L) → ℝ := fun ω =>
    pairInputs u u (revealedInputCRT blk hcop D L A Jq) (revealedInputCRT blk hcop D L A Jq)
      (unchangedInput (crtModuli m₀ blk p L) Q A L) ω ω with ha
  -- the energy as a signed sum
  have hE : ∀ ω, envTermEnergy hcop D hpair Qb u L A Jq ω f g =
      |∑ z, ρ z * ∏ v, a ω v (z v)| := by
    intro ω
    unfold envTermEnergy multilinearIntegral
    rw [apply_eq_sum_lawDensity']
    rfl
  -- the weight is a product of positive-record densities
  have hρprod : ρ = fun z => ∏ b, lawDensity (Λ' b) (fun v => z v b) := by
    funext z
    rw [hρ, Sarkozy.DensityDC.lawDensity_tensorLaw]
  have hpos : ∀ b, IsPositiveRecord (Λ' b) := fun b =>
    isPositiveRecord_pullLaw _ (isPositiveRecord_termLaw D L hp (Qb L) hQpos f g b)
  have hunif : selectedMarginalsUniform ρ := by
    rw [hρprod]
    exact selectedMarginalsUniform_prod (fun b => lawDensity (Λ' b))
      fun b => selectedMarginalsUniform_lawDensity (hpos b)
  have htv : totalVariation ρ = ∏ b, termWeight D L (Qb L) b (f b) (g b) := by
    rw [hρprod, totalVariation_prod]
    apply prod_congr rfl
    intro b _
    rw [← totalVariation_termLaw D L hp (Qb L) f g b]
    unfold totalVariation
    rw [hΛ']
    exact sum_abs_lawDensity_pullLaw _ _
  -- the slot data of the inputs
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
  have hinputs : ∀ ω, a ω = fun v => paperForm (crtModuli m₀ blk p L) Q A
      (envSlots hcop u L Jq ω v) := by
    intro ω
    exact pairInputs_eq_slotDatum (crtModuli m₀ blk p L) u _ _ ω Q A _ (wholeDatum L)
      (fun e => revealedInputCRT_eq_paperForm hcop D L A Jq e (ω e) (hJ e))
      (unchangedInput_eq_paperForm _ Q A L)
  have hKL : 1 ≤ blockScale * L := Nat.mul_pos (by norm_num [blockScale]) (by omega)
  have hQ1 : 1 ≤ Q := one_le_paperCutoff hKL
  -- the moments
  have hB : ∀ v, (FiniteLaw.uniform (∀ (_e : E) (j : Option P),
      CoordSpace blockScale pr h j)).expect (fun ω =>
        (FiniteLaw.uniform (ResidueSpace (crtModuli m₀ blk p L))).moment 72 (a ω v)) ≤
      (M0 : ℝ) ^ 72 * ((Fintype.card (ResidueSpace (blockModulus m₀ blk)) : ℝ) ^ 72 * C *
        Q ^ ε * ((blockScale : ℝ) * density (blockScale * L) A)) := by
    intro v
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
  rw [FiniteLaw.expect_congr _ hE]
  refine (expect_abs_signed_energy_le_moment _ ρ hunif a hB).trans (le_of_eq ?_)
  rw [htv]

/-- **`lem:record:density-lp`, per term, at the energies of `fixC`** (as `env_term_lp`; every
depth vector, the increments `wrapInc` are positive records by the data). -/
theorem fix_term_lp (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (u : E → reservedCut.Half) (t : ZMod blockScale)
    {L : ℕ} {A : Finset ℤ} {M0 Qcl Qpre N0 N0' : ℕ}
    (_hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L) (_hL : 1 ≤ L) (_hM0 : 1 ≤ M0)
    (_hp : ∀ j, (p L j).Prime) (_hinj : Injective (p L))
    (_hMod : modulus pr h ∣ M0) (S : Finset E)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (f g : BlockAtom Bk J L → Bool),
    (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
        (fun ω => fixTermEnergy hcop D hpair u t L A S Jq ω f g) ≤
      (∏ b, termWeight D L (TheoremCBlock.Structured.wrapInc D L) b (f b) (g b)) *
        ((M0 : ℝ) ^ 72 * ((Fintype.card (ResidueSpace (blockModulus m₀ blk)) : ℝ) ^ 72 * C *
          paperCutoff (blockScale * L) ^ ε * ((blockScale : ℝ) * density (blockScale * L) A))) := by
  obtain ⟨C, hC, hc⟩ := input_moment_le_density 36 (by norm_num) ε hε
  refine ⟨C, hC, ?_⟩
  intro D hpair u t L A M0 Qcl Qpre N0 N0' hsc hL hM0 hp hinj hMod S Jq f g
  set Λ' := crtLaws blk (prefix_pairwise (hpair L)) L
    (BracketEnergy.termLaw D L (TheoremCBlock.Structured.wrapInc D L) f g) with hΛ'
  set ρ : (Slot → ResidueSpace (crtModuli m₀ blk p L)) → ℝ := lawDensity (tensorLaw Λ') with hρ
  set Q := paperCutoff (blockScale * L) with hQ
  set a : (E → ∀ j : Option P, CoordSpace blockScale pr h j) → Slot →
      ResidueSpace (crtModuli m₀ blk p L) → ℝ := fun ω =>
    pairInputs u u (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
      (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
      (unchangedInput (crtModuli m₀ blk p L) Q A L) ω ω with ha
  have hE : ∀ ω, fixTermEnergy hcop D hpair u t L A S Jq ω f g =
      |∑ z, ρ z * ∏ v, a ω v (z v)| := by
    intro ω
    unfold fixTermEnergy multilinearIntegral
    rw [apply_eq_sum_lawDensity']
    rfl
  have hρprod : ρ = fun z => ∏ b, lawDensity (Λ' b) (fun v => z v b) := by
    funext z
    rw [hρ, Sarkozy.DensityDC.lawDensity_tensorLaw]
  have hpos : ∀ b, IsPositiveRecord (Λ' b) := fun b =>
    isPositiveRecord_pullLaw _ (isPositiveRecord_termLaw D L hp _
      (isPositiveRecord_wrapInc D L) f g b)
  have hunif : selectedMarginalsUniform ρ := by
    rw [hρprod]
    exact selectedMarginalsUniform_prod (fun b => lawDensity (Λ' b))
      fun b => selectedMarginalsUniform_lawDensity (hpos b)
  have htv : totalVariation ρ =
      ∏ b, termWeight D L (TheoremCBlock.Structured.wrapInc D L) b (f b) (g b) := by
    rw [hρprod, totalVariation_prod]
    apply prod_congr rfl
    intro b _
    rw [← totalVariation_termLaw D L hp _ f g b]
    unfold totalVariation
    rw [hΛ']
    exact sum_abs_lawDensity_pullLaw _ _
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
  have hinputs : ∀ ω, a ω = fun v => paperForm (crtModuli m₀ blk p L) Q A
      (fixSlots hcop u L S t Jq ω v) := by
    intro ω
    exact pairInputs_eq_slotDatum (crtModuli m₀ blk p L) u _ _ ω Q A _ (wholeDatum L)
      (fun e => revealedSlot_wrapInputCRT_eq_paperForm hcop L A S t Jq e (ω e))
      (unchangedInput_eq_paperForm _ Q A L)
  have hKL : 1 ≤ blockScale * L := Nat.mul_pos (by norm_num [blockScale]) (by omega)
  have hQ1 : 1 ≤ Q := one_le_paperCutoff hKL
  have hB : ∀ v, (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
      (fun ω => (FiniteLaw.uniform (ResidueSpace (crtModuli m₀ blk p L))).moment 72 (a ω v)) ≤
      (M0 : ℝ) ^ 72 * ((Fintype.card (ResidueSpace (blockModulus m₀ blk)) : ℝ) ^ 72 * C *
        Q ^ ε * ((blockScale : ℝ) * density (blockScale * L) A)) := by
    intro v
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
  rw [FiniteLaw.expect_congr _ hE]
  refine (expect_abs_signed_energy_le_moment _ ρ hunif a hB).trans (le_of_eq ?_)
  rw [htv]

end Sarkozy.DensityChain
