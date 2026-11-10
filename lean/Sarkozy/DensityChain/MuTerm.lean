module

public import Sarkozy.DensityChain.Reduced

@[expose] public section

/-!
# The `μ`-term of `envC` (`f = g = ∅`), with `hdc` and `hun` discharged

The term `f = g = ∅` of the bracket expansion is the `μ`-part of the envelope energy: only the
`2k` query slots carry revealed inputs, the outside slots carry `F_A`. B9's
`env_first_mean_le_query` bounds it from `hrest` (at the query slots), `hdc` and `hun` (the
square-step model at an outside slot has reference energy at most `Y`). Here:

* `squareStepModel_whole`: at a whole-datum slot (`E = ∅`, `D₀ = 1`, `I = [N]`) the square-step
  model at the paper's cutoff **is** `F_A` (`R = 1`, `ℓ = L`, one residue, `T_1 = id`);
* `dataY_eq_referenceEnergy`: `Y(L, A) = Z_μ(F_A)` on B5's cyclic coordinates (B5's
  `multilinearIntegral_crt`, `blockLift_crtLabel`, `crtLaws_blockRefLaws`);
* so `hun` holds with equality (`env_hun_whole`), and **`env_mu_chain`** gives the `μ`-term's
  first bound from restoration at the query slots alone (`hdc` from `density_dc_block` with all
  slots changed).
-/

namespace Sarkozy.DensityChain

open Finset Function
open scoped BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.DensityDC

section Model
variable {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)]

omit [Fintype J] [DecidableEq J] [∀ j, NeZero (m j)] in
theorem stepR_empty_one : stepR m ∅ 1 = 1 := by
  unfold stepR
  simp [leastSquare]

omit [Fintype J] [DecidableEq J] [∀ j, NeZero (m j)] in
theorem stepEll_empty_whole (L : ℕ) : stepEll m ∅ 1 (blockScale * L) = L := by
  unfold stepEll
  rw [stepR_empty_one]
  unfold stepScale
  have hK : 0 < blockScale := by norm_num [blockScale]
  rw [mul_one, show blockScale * L + blockScale - 1 = blockScale * L + (blockScale - 1) by omega,
    Nat.mul_add_div hK, Nat.div_eq_of_lt (by omega), add_zero]

/-- **The square-step model of a whole-datum slot is `F_A`**: with `E = ∅`, `D₀ = 1`,
`I = [N]`, the model `g̃` is the lift of `A` itself, at the paper's cutoff. -/
theorem squareStepModel_whole (A : Finset ℤ) (L : ℕ) (hL : 1 ≤ L) (x : ResidueSpace m)
    (s : ZMod 1) (y : ResidueSpace m) :
    (squareStepModel m ∅ x s A (Icc (0 + 1) (0 + ((blockScale * L : ℕ) : ℤ))) 0 (blockScale * L)
      (stepR m ∅ 1) (blockScale * stepEll m ∅ 1 (blockScale * L))
      (paperCutoff (blockScale * stepEll m ∅ 1 (blockScale * L))) y).re =
      unchangedInput m (paperCutoff (blockScale * L)) A L y := by
  rw [stepEll_empty_whole, stepR_empty_one]
  have hKL : (blockScale * L : ℕ) ≠ 0 := by
    have : 0 < blockScale := by norm_num [blockScale]
    positivity
  unfold squareStepModel
  have hres : stepResidues m ∅ x s 1 0 = {1} := by
    unfold stepResidues
    ext j
    simp only [mem_filter, mem_Icc, mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, _⟩
      omega
    · intro hj
      subst hj
      refine ⟨⟨le_refl _, le_refl _⟩, ?_⟩
      unfold InFibre
      exact ⟨Subsingleton.elim _ _, fun j hj => absurd hj (notMem_empty j)⟩
  rw [hres, sum_singleton]
  have hmap : stepMap m 1 0 1 y = y := by
    funext k
    unfold stepMap
    simp
  rw [hmap]
  unfold stepLift
  rw [retainedOff_empty]
  unfold unchangedInput input
  rw [inputFun_of_eq_one rfl]
  simp only [prod_empty, mul_one, Nat.cast_one, div_one, zero_add, one_mul]
  rw [div_self (by exact_mod_cast hKL), one_mul]
  congr 1
  unfold lift liftOn intervalCoeff
  apply sum_congr rfl
  intro a _
  congr 2
  apply sum_congr rfl
  intro n hn
  congr 1
  unfold stepChild indicator
  rw [mem_Icc] at hn
  simp only [mem_filter, mem_Icc, mem_inter, Nat.cast_one, one_mul, sub_self, add_zero]
  have hn2 : n ≤ (blockScale : ℤ) * (L : ℤ) := by
    have := hn.2
    push_cast at this
    exact this
  by_cases hA : n ∈ A
  · simp [hA, hn.1, hn2]
  · simp [hA]

end Model

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

omit [DecidableEq P] in
/-- **`Y(L, A) = Z_μ(F_A)` on the cyclic coordinates** (the reference energy of the data is the
energy of `F_A` under `crtRef`). -/
theorem dataY_eq_referenceEnergy (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (A : Finset ℤ) :
    D.Y L A = referenceEnergy
      (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
      (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) := by
  unfold TheoremCBlock.ComparisonData.Y
  rw [energyFirst_eq_diagonalIntegral]
  unfold diagonalIntegral
  rw [multilinearIntegral_crt blk (prefix_pairwise hpair) L]
  have h1 : crtLaws blk (prefix_pairwise hpair) L (D.R.law p L) =
      fun b => signedIntegral (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L b).weight :=
    funext fun b => crtLaws_blockRefLaws blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L b
  rw [h1]
  simp_rw [blockLift_crtLabel blk L hpair A]
  unfold referenceEnergy multilinearIntegral FiniteLaw.tensor
  rw [FiniteLaw.expect_ofFunctional]

omit [DecidableEq P] in
/-- **`hun` of the `μ`-term, with equality**: at an outside slot the square-step model (with the
paper's cutoff) is `F_A`, whose reference energy is `Y(L, A)`. -/
theorem env_hun_whole (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) {L : ℕ} (hL : 1 ≤ L)
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (A : Finset ℤ) (u : E → reservedCut.Half)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (v : Slot)
    (hv : slotQuery u v = none) (x : ResidueSpace (crtModuli m₀ blk p L)) :
    referenceEnergy (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
      (revealedModel (crtModuli m₀ blk p L) ∅ A (fun v => (envSlots hcop u L Jq ω v).1)
        (fun v => (envSlots hcop u L Jq ω v).2.2.1) (fun v => (envSlots hcop u L Jq ω v).2.2.2)
        (fun v => (envSlots hcop u L Jq ω v).2.1)
        (fun v => paperCutoff (blockScale * stepEll (crtModuli m₀ blk p L) ∅ (envD0 u Jq v)
          (envM u L v))) v x) ≤ D.Y L A := by
  rw [dataY_eq_referenceEnergy D L hpair A]
  apply le_of_eq
  congr 1
  have hd : envSlots hcop u L Jq ω v = wholeDatum L := by
    unfold envSlots
    rw [slotDatum_eq_optDatum u _ _ v, hv]
    rfl
  have hD0 : envD0 u Jq v = 1 := by
    unfold envD0
    rw [hv]
  have hM : envM u L v = blockScale * L := by
    unfold envM
    rw [hv]
  funext y
  simp only [revealedModel]
  rw [hD0, hM, hd]
  exact squareStepModel_whole _ A L hL x _ y

omit [DecidableEq Bk] [∀ L, DecidableEq (J L)] [DecidableEq P] [Fintype E] [DecidableEq E] in
theorem termSet_false {L : ℕ} :
    termSet (Bk := Bk) (J := J) (L := L) (fun _ => false) (fun _ => false) = ∅ := by
  unfold termSet
  simp

/-- **The `μ`-term's first bound** (`f = g = ∅`), for any constants `C₁, C₇₁` with the
property of `density_dc_block` (`DCBlockProp`) ( `lem:bracket-energy`, the `μ`-part of
`lem:envelope-energy`): B9's `env_first_mean_le_query` with `hdc` from `density_dc_block` (all
slots changed, the square-step model at the outside slots) and `hun` from `env_hun_whole`. The
only per-term input left is restoration at the query slots. -/
theorem env_mu_chain_of (ε C1 C71 : ℝ) (hdcb : DCBlockProp ε C1 C71) :
    ∀ (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) {C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (_hcex : IsLeastCounterexample D.Y a densityExponent C0 L A) (_ha : 0 ≤ a) (_hC0 : 0 ≤ C0)
    (_hL : 2 ≤ L)
    {M0 Qcl Qpre N0 N0' : ℕ} (_hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (_hM0 : 1 ≤ M0) (_hQcl : 1 ≤ Qcl) (_hp : ∀ j, (p L j).Prime) (_hinj : Injective (p L))
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (_hJ : ∀ e, (Jq e none : ℕ) ≠ 0)
    (u : E → reservedCut.Half) (_hu : Injective u)
    (_hMod : modulus pr h ∣ M0)
    (_hcopM : ∀ k, (modulus pr h).Coprime (crtModuli m₀ blk p L k))
    {σ : ℝ} (_hσ : 0 ≤ σ) (_hS1 : ε / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ)
    (_hrest : ∀ ω v, ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll (crtModuli m₀ blk p L) ∅
        (envSlots hcop u L Jq ω v).1 (envSlots hcop u L Jq ω v).2.2.1 : ℕ) : ℤ) →
      referenceEnergy (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
          (child (crtModuli m₀ blk p L) ∅
            (paperCutoff (blockScale * stepEll (crtModuli m₀ blk p L) ∅
              (envSlots hcop u L Jq ω v).1 (envSlots hcop u L Jq ω v).2.2.1)) B
            (blockScale * stepEll (crtModuli m₀ blk p L) ∅ (envSlots hcop u L Jq ω v).1
            (envSlots hcop u L Jq ω v).2.2.1)) ≤
        D.Y (stepEll (crtModuli m₀ blk p L) ∅ (envSlots hcop u L Jq ω v).1
          (envSlots hcop u L Jq ω v).2.2.1) B)
    (uQ : BlockAtom Bk J L → ℝ)
    (_hQ : ∀ b, (∑ z, |lawDensity (Qb b) z|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a ≤ uQ b)
    (_hR : ∀ b, (∑ z, |lawDensity (recLaw D L b) z|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a ≤ D.GB.uprice L b),
    (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect (fun ω =>
      |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise hpair) L
        (BracketEnergy.termLaw D L Qb (fun _ => false) (fun _ => false))))
        (pairInputs u u (revealedInputCRT blk hcop D L A Jq)
          (revealedInputCRT blk hcop D L A Jq)
          (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)|) ≤
      (1 + scaleU blockScale M0 Qcl stageTau L) *
          (conductorPrice pr h (2 * a / 72) Jq * D.Y L A *
            ((∏ b, if (fun _ => false : BlockAtom Bk J L → Bool) b then uQ b else 1) *
              ∏ b, (if (fun _ => false : BlockAtom Bk J L → Bool) b then D.GB.uprice L b
                else 1))) +
        (∏ b, termWeight D L Qb b false false) *
          (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
            (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
            (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  intro D C0 L A hpair hcex ha hC0 hL M0 Qcl Qpre N0 N0' hsc hM0 hQcl hp hinj Qb Jq hJ u hu hMod
    hcopM σ hσ hS1 hrest uQ hQ hR
  set f : BlockAtom Bk J L → Bool := fun _ => false with hf
  have hT : termSet f f = ∅ := termSet_false
  have hg : f ∈ validChoices f := by
    unfold validChoices
    simp [hf]
  have hθ := densityExponent_facts
  have hY0 : D.Y L ∅ ≤ 0 := by rw [dataY_empty D L]
  set Q' : Slot → ℝ := fun v => paperCutoff (blockScale * stepEll (crtModuli m₀ blk p L)
    ∅ (envD0 u Jq v) (envM u L v)) with hQ'def
  have hQ' : ∀ ω v, Q' v = paperCutoff (blockScale * stepEll (crtModuli m₀ blk p L)
      ∅ (envSlots hcop u L Jq ω v).1 (envSlots hcop u L Jq ω v).2.2.1) := by
    intro ω v
    have h1 := envSlots_fst hcop u L Jq ω v
    have h2 := envSlots_len hcop u L Jq ω v
    simp only [hQ'def]
    rw [h2, h1]
  have hdat : ∀ ω v, envSlots hcop u L Jq ω v =
      optDatum (fun e => envDatum hcop L Jq e (ω e)) (wholeDatum L) (slotQuery u v) :=
    fun ω v => slotDatum_eq_optDatum u _ _ v
  have hJd : ∀ e, revealedModulus blockScale pr h (Jq e) ∣ modulus pr h :=
    fun e => revealedModulus_dvd (Jq e)
  have hmpos : 0 < modulus pr h := Nat.pos_of_ne_zero (NeZero.ne _)
  have hD0 : ∀ ω v, 1 ≤ (envSlots hcop u L Jq ω v).1 := by
    intro ω v
    rw [hdat]
    rcases slotQuery u v with _ | e
    · exact le_refl 1
    · exact Nat.pos_of_dvd_of_pos (hJd e) hmpos
  have hD0M : ∀ ω v, (envSlots hcop u L Jq ω v).1 ∣ M0 := by
    intro ω v
    rw [hdat]
    rcases slotQuery u v with _ | e
    · exact one_dvd _
    · exact dvd_trans (hJd e) hMod
  have hcop0 : ∀ ω v k, ((envSlots hcop u L Jq ω v).1).Coprime (crtModuli m₀ blk p L k) := by
    intro ω v k
    rw [hdat]
    rcases slotQuery u v with _ | e
    · exact Nat.coprime_one_left _
    · exact Nat.Coprime.coprime_dvd_left (hJd e) (hcopM k)
  have hM : ∀ ω v, (envSlots hcop u L Jq ω v).2.2.1 = blockScale * L ∨
      (envSlots hcop u L Jq ω v).2.2.1 = L := by
    intro ω v
    rw [hdat]
    rcases slotQuery u v with _ | e
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hcopJ : ∀ e, (revealedModulus blockScale pr h (Jq e)).Coprime
      (∏ j ∈ termSet f f, crtModuli m₀ blk p L j) :=
    fun e => Nat.Coprime.prod_right fun k _ => Nat.Coprime.coprime_dvd_left (hJd e) (hcopM k)
  have hDE : ∏ b ∈ termSet f f, crtModuli m₀ blk p L b = 1 * 1 := by
    rw [hT, prod_empty, mul_one]
  have hKL : 1 ≤ blockScale * L := Nat.mul_pos (by norm_num [blockScale]) (by omega)
  have hqN : ((1 : ℕ) : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau := by
    rw [Nat.cast_one]
    exact Real.one_le_rpow (by exact_mod_cast hKL) (by norm_num [stageTau])
  have hun : ∀ ω v, slotQuery u v = none → ∀ x, referenceEnergy
      (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
      (revealedModel (crtModuli m₀ blk p L) (termSet f f) A
        (fun v => (envSlots hcop u L Jq ω v).1)
        (fun v => (envSlots hcop u L Jq ω v).2.2.1)
        (fun v => (envSlots hcop u L Jq ω v).2.2.2)
        (fun v => (envSlots hcop u L Jq ω v).2.1) Q' v x) ≤ D.Y L A := by
    intro ω v hv x
    rw [hT]
    exact env_hun_whole hcop D (by omega) hpair A u Jq ω v hv x
  have hdc : ∀ ω, |structuredEnergy
        (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
        (FiniteLaw.uniform Unit)
        (liftWeight (termSet f f)
          (selectedWeight (termSet f f)
            (crtLaws blk (prefix_pairwise hpair) L (BracketEnergy.termLaw D L Qb f f)))
          (uniformRest (Xa := fun b => ZMod (crtModuli m₀ blk p L b)) (termSet f f)))
        (paperInputs (crtModuli m₀ blk p L) (termSet f f) (paperCutoff (blockScale * L)) A
          (fun v => (envSlots hcop u L Jq ω v).1)
          (fun v => (envSlots hcop u L Jq ω v).2.2.1)
          (fun _ v => (envSlots hcop u L Jq ω v).2.2.2)
          (fun _ v => (envSlots hcop u L Jq ω v).2.1)) -
      structuredEnergy
        (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
        (FiniteLaw.uniform Unit)
        (liftWeight (termSet f f)
          (selectedWeight (termSet f f)
            (crtLaws blk (prefix_pairwise hpair) L (BracketEnergy.termLaw D L Qb f f)))
          (uniformRest (Xa := fun b => ZMod (crtModuli m₀ blk p L b)) (termSet f f)))
        (fun _ => revealedModel (crtModuli m₀ blk p L) (termSet f f) A
          (fun v => (envSlots hcop u L Jq ω v).1)
          (fun v => (envSlots hcop u L Jq ω v).2.2.1)
          (fun v => (envSlots hcop u L Jq ω v).2.2.2)
          (fun v => (envSlots hcop u L Jq ω v).2.1) Q')| ≤
      dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
          (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
        totalVariation (selectedWeight (termSet f f)
          (crtLaws blk (prefix_pairwise hpair) L (BracketEnergy.termLaw D L Qb f f))) *
        (L : ℝ) ^ (-σ) * density (blockScale * L) A := by
    intro ω
    have hsel : selectedMarginalsUniform (selectedWeight (termSet f f)
        (crtLaws blk (prefix_pairwise hpair) L (BracketEnergy.termLaw D L Qb f f))) := by
      intro v x
      have hempty : IsEmpty {b // b ∈ termSet f f} := by
        rw [hT]
        exact ⟨fun b => notMem_empty _ b.2⟩
      have h1 : ∀ z : Slot → ∀ b : {b // b ∈ termSet f f},
          ZMod (crtModuli m₀ blk p L b.1), z = fun _ b => (hempty.false b).elim := by
        intro z
        funext v' b
        exact (hempty.false b).elim
      have hcard : Fintype.card (∀ b : {b // b ∈ termSet f f},
          ZMod (crtModuli m₀ blk p L b.1)) = 1 := Fintype.card_eq_one_iff.mpr
        ⟨fun b => (hempty.false b).elim, fun y => funext fun b => (hempty.false b).elim⟩
      rw [hcard, Nat.cast_one, div_one]
      apply sum_congr _ (fun _ _ => rfl)
      ext z
      simp only [mem_filter, mem_univ, true_and, iff_true]
      funext b
      exact (hempty.false b).elim
    have key := hdcb blk p D.R hpair hp hinj hL hsc hM0 (termSet f f) hDE
      (by simp) (by exact ⟨1, rfl⟩) one_ne_zero hQcl (Nat.coprime_one_left 1) hqN
      (FiniteLaw.uniform Unit) _
      (selectedMarginalsUniform_liftWeight_uniform (termSet f f) _ hsel)
      (fun v => (envSlots hcop u L Jq ω v).1) (hD0 ω) (hD0M ω) (hcop0 ω)
      (fun v => (envSlots hcop u L Jq ω v).2.2.1) (hM ω)
      (fun _ v => (envSlots hcop u L Jq ω v).2.2.2) (fun _ v => (envSlots hcop u L Jq ω v).2.1)
      (fun _ => True)
      (fun _ => revealedModel (crtModuli m₀ blk p L) (termSet f f) A
        (fun v => (envSlots hcop u L Jq ω v).1)
        (fun v => (envSlots hcop u L Jq ω v).2.2.1)
        (fun v => (envSlots hcop u L Jq ω v).2.2.2)
        (fun v => (envSlots hcop u L Jq ω v).2.1) Q')
      (fun _ v x _ => by
        funext y
        simp only [revealedModel]
        rw [hT, hQ' ω v])
      (fun v hv => absurd trivial hv) hσ hS1
    rw [totalVariation_liftWeight] at key
    exact key
  have hatom : ∀ b ∈ termSet f f,
      ∀ hb : 0 < totalVariation (lawDensity (BracketEnergy.termLaw D L Qb f f b)),
      MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1 := by
    intro b hb
    rw [hT] at hb
    exact absurd hb (notMem_empty b)
  have hrest' : ∀ ω v, slotQuery u v ≠ none → ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll (crtModuli m₀ blk p L) (termSet f f)
        (envSlots hcop u L Jq ω v).1 (envSlots hcop u L Jq ω v).2.2.1 : ℕ) : ℤ) →
      referenceEnergy (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
          (child (crtModuli m₀ blk p L) (termSet f f) (Q' v) B
            (blockScale * stepEll (crtModuli m₀ blk p L)
            (termSet f f) (envSlots hcop u L Jq ω v).1
            (envSlots hcop u L Jq ω v).2.2.1)) ≤
        D.Y (stepEll (crtModuli m₀ blk p L) (termSet f f) (envSlots hcop u L Jq ω v).1
          (envSlots hcop u L Jq ω v).2.2.1) B := by
    intro ω v _ B hB
    rw [hT] at hB ⊢
    rw [hQ' ω v]
    exact hrest ω v B hB
  have key := env_first_mean_le_query hcop D hpair hcex hθ.1 hθ.2 ha hC0 hL hY0 hsc hM0 Qb f f
    hg hDE (by simp) (by exact ⟨1, rfl⟩) one_ne_zero hQcl (Nat.coprime_one_left 1) hqN Jq hJ
    hcopJ u hu hD0 hD0M hcop0 hM Q' hun hrest' hdc hatom uQ hQ hR
  refine key.trans (le_of_eq ?_)
  rw [termNorm_eq_prod]

omit [DecidableEq P] in
/-- **`hun` of the `μ`-term of `fixC`, with equality** (the slots of `F_A`): at an outside slot
the square-step model (with the
paper's cutoff) is `F_A`, whose reference energy is `Y(L, A)`. -/
theorem fix_hun_whole (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) {L : ℕ} (hL : 1 ≤ L)
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (A : Finset ℤ) (u : E → reservedCut.Half) (S : Finset E) (t : ZMod blockScale)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (v : Slot)
    (hv : fixChanged u S v = false) (x : ResidueSpace (crtModuli m₀ blk p L)) :
    referenceEnergy (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
      (revealedModel (crtModuli m₀ blk p L) ∅ A (fun v => (fixSlots hcop u L S t Jq ω v).1)
        (fun v => (fixSlots hcop u L S t Jq ω v).2.2.1)
        (fun v => (fixSlots hcop u L S t Jq ω v).2.2.2)
        (fun v => (fixSlots hcop u L S t Jq ω v).2.1)
        (fun v => paperCutoff (blockScale * stepEll (crtModuli m₀ blk p L) ∅ (fixD0 u S Jq v)
          (fixM u S L v))) v x) ≤ D.Y L A := by
  rw [dataY_eq_referenceEnergy D L hpair A]
  apply le_of_eq
  congr 1
  have hd : fixSlots hcop u L S t Jq ω v = wholeDatum L :=
    fixSlots_of_not_changed hcop u S t Jq ω v hv
  have hD0 : fixD0 u S Jq v = 1 := by
    rw [← fixSlots_fst hcop u L S t Jq ω v, hd]
    rfl
  have hM : fixM u S L v = blockScale * L := by
    rw [← fixSlots_len hcop u L S t Jq ω v, hd]
    rfl
  funext y
  simp only [revealedModel]
  rw [hD0, hM, hd]
  exact squareStepModel_whole _ A L hL x _ y

/-- **The `μ`-term's first bound for `fixC`** (`f = g = ∅`), for any constants `C₁, C₇₁` with the
property of `density_dc_block` (`DCBlockProp`) ( `lem:bracket-energy`, the `μ`-part of
`lem:envelope-energy`): B9's `fix_first_mean_le_query` with `hdc` from `density_dc_block` (all
slots changed, the square-step model at the outside slots) and `hun` from `env_hun_whole`. The
only per-term input left is restoration at the query slots. -/
theorem fix_mu_chain_of (ε C1 C71 : ℝ) (hdcb : DCBlockProp ε C1 C71) :
    ∀ (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) {C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (_hcex : IsLeastCounterexample D.Y a densityExponent C0 L A) (_ha : 0 ≤ a) (_hC0 : 0 ≤ C0)
    (_hL : 2 ≤ L)
    {M0 Qcl Qpre N0 N0' : ℕ} (_hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (_hM0 : 1 ≤ M0) (_hQcl : 1 ≤ Qcl) (_hp : ∀ j, (p L j).Prime) (_hinj : Injective (p L))
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (S : Finset E) (t : ZMod blockScale)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (u : E → reservedCut.Half) (_hu : Injective u)
    (_hMod : modulus pr h ∣ M0)
    (_hcopM : ∀ k, (modulus pr h).Coprime (crtModuli m₀ blk p L k))
    {σ : ℝ} (_hσ : 0 ≤ σ) (_hS1 : ε / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ)
    (_hrest : ∀ ω v, ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll (crtModuli m₀ blk p L) ∅
        (fixSlots hcop u L S t Jq ω v).1 (fixSlots hcop u L S t Jq ω v).2.2.1 : ℕ) : ℤ) →
      referenceEnergy (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
          (child (crtModuli m₀ blk p L) ∅
            (paperCutoff (blockScale * stepEll (crtModuli m₀ blk p L) ∅
              (fixSlots hcop u L S t Jq ω v).1 (fixSlots hcop u L S t Jq ω v).2.2.1)) B
            (blockScale * stepEll (crtModuli m₀ blk p L) ∅ (fixSlots hcop u L S t Jq ω v).1
            (fixSlots hcop u L S t Jq ω v).2.2.1)) ≤
        D.Y (stepEll (crtModuli m₀ blk p L) ∅ (fixSlots hcop u L S t Jq ω v).1
          (fixSlots hcop u L S t Jq ω v).2.2.1) B)
    (uQ : BlockAtom Bk J L → ℝ)
    (_hQ : ∀ b, (∑ z, |lawDensity (Qb b) z|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a ≤ uQ b)
    (_hR : ∀ b, (∑ z, |lawDensity (recLaw D L b) z|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a ≤ D.GB.uprice L b),
    (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect (fun ω =>
      |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise hpair) L
        (BracketEnergy.termLaw D L Qb (fun _ => false) (fun _ => false))))
        (pairInputs u u (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
          (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
          (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)|) ≤
      (1 + scaleU blockScale M0 Qcl stageTau L) *
          (fixedPrice pr h (2 * a / 72) S Jq * D.Y L A *
            ((∏ b, if (fun _ => false : BlockAtom Bk J L → Bool) b then uQ b else 1) *
              ∏ b, (if (fun _ => false : BlockAtom Bk J L → Bool) b then D.GB.uprice L b
                else 1))) +
        (∏ b, termWeight D L Qb b false false) *
          (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
            (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
            (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  intro D C0 L A hpair hcex ha hC0 hL M0 Qcl Qpre N0 N0' hsc hM0 hQcl hp hinj Qb S t Jq u hu hMod
    hcopM σ hσ hS1 hrest uQ hQ hR
  set f : BlockAtom Bk J L → Bool := fun _ => false with hf
  have hT : termSet f f = ∅ := termSet_false
  have hg : f ∈ validChoices f := by
    unfold validChoices
    simp [hf]
  have hθ := densityExponent_facts
  have hY0 : D.Y L ∅ ≤ 0 := by rw [dataY_empty D L]
  set Q' : Slot → ℝ := fun v => paperCutoff (blockScale * stepEll (crtModuli m₀ blk p L)
    ∅ (fixD0 u S Jq v) (fixM u S L v)) with hQ'def
  have hQ' : ∀ ω v, Q' v = paperCutoff (blockScale * stepEll (crtModuli m₀ blk p L)
      ∅ (fixSlots hcop u L S t Jq ω v).1 (fixSlots hcop u L S t Jq ω v).2.2.1) := by
    intro ω v
    have h1 := fixSlots_fst hcop u L S t Jq ω v
    have h2 := fixSlots_len hcop u L S t Jq ω v
    simp only [hQ'def]
    rw [h2, h1]
  have hJd : ∀ e, revealedModulus blockScale pr h (Jq e) ∣ modulus pr h :=
    fun e => revealedModulus_dvd (Jq e)
  have hmpos : 0 < modulus pr h := Nat.pos_of_ne_zero (NeZero.ne _)
  have hD0 : ∀ ω v, 1 ≤ (fixSlots hcop u L S t Jq ω v).1 := by
    intro ω v
    rw [fixSlots_fst]
    unfold fixD0
    rcases slotQuery u v with _ | e
    · exact le_refl 1
    · change 1 ≤ (if e ∈ S then revealedModulus blockScale pr h (Jq e) else 1)
      split_ifs
      · exact Nat.pos_of_dvd_of_pos (hJd e) hmpos
      · exact le_refl 1
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
  have hcop0 : ∀ ω v k, ((fixSlots hcop u L S t Jq ω v).1).Coprime (crtModuli m₀ blk p L k) := by
    intro ω v k
    rw [fixSlots_fst]
    unfold fixD0
    rcases slotQuery u v with _ | e
    · exact Nat.coprime_one_left _
    · change (if e ∈ S then revealedModulus blockScale pr h (Jq e) else 1).Coprime _
      split_ifs
      · exact Nat.Coprime.coprime_dvd_left (hJd e) (hcopM k)
      · exact Nat.coprime_one_left _
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
  have hcopJ : ∀ e, (revealedModulus blockScale pr h (Jq e)).Coprime
      (∏ j ∈ termSet f f, crtModuli m₀ blk p L j) :=
    fun e => Nat.Coprime.prod_right fun k _ => Nat.Coprime.coprime_dvd_left (hJd e) (hcopM k)
  have hDE : ∏ b ∈ termSet f f, crtModuli m₀ blk p L b = 1 * 1 := by
    rw [hT, prod_empty, mul_one]
  have hKL : 1 ≤ blockScale * L := Nat.mul_pos (by norm_num [blockScale]) (by omega)
  have hqN : ((1 : ℕ) : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau := by
    rw [Nat.cast_one]
    exact Real.one_le_rpow (by exact_mod_cast hKL) (by norm_num [stageTau])
  have hun : ∀ ω v, fixChanged u S v = false → ∀ x, referenceEnergy
      (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
      (revealedModel (crtModuli m₀ blk p L) (termSet f f) A
        (fun v => (fixSlots hcop u L S t Jq ω v).1)
        (fun v => (fixSlots hcop u L S t Jq ω v).2.2.1)
        (fun v => (fixSlots hcop u L S t Jq ω v).2.2.2)
        (fun v => (fixSlots hcop u L S t Jq ω v).2.1) Q' v x) ≤ D.Y L A := by
    intro ω v hv x
    rw [hT]
    exact fix_hun_whole hcop D (by omega) hpair A u S t Jq ω v hv x
  have hdc : ∀ ω, |structuredEnergy
        (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
        (FiniteLaw.uniform Unit)
        (liftWeight (termSet f f)
          (selectedWeight (termSet f f)
            (crtLaws blk (prefix_pairwise hpair) L (BracketEnergy.termLaw D L Qb f f)))
          (uniformRest (Xa := fun b => ZMod (crtModuli m₀ blk p L b)) (termSet f f)))
        (paperInputs (crtModuli m₀ blk p L) (termSet f f) (paperCutoff (blockScale * L)) A
          (fun v => (fixSlots hcop u L S t Jq ω v).1)
          (fun v => (fixSlots hcop u L S t Jq ω v).2.2.1)
          (fun _ v => (fixSlots hcop u L S t Jq ω v).2.2.2)
          (fun _ v => (fixSlots hcop u L S t Jq ω v).2.1)) -
      structuredEnergy
        (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
        (FiniteLaw.uniform Unit)
        (liftWeight (termSet f f)
          (selectedWeight (termSet f f)
            (crtLaws blk (prefix_pairwise hpair) L (BracketEnergy.termLaw D L Qb f f)))
          (uniformRest (Xa := fun b => ZMod (crtModuli m₀ blk p L b)) (termSet f f)))
        (fun _ => revealedModel (crtModuli m₀ blk p L) (termSet f f) A
          (fun v => (fixSlots hcop u L S t Jq ω v).1)
          (fun v => (fixSlots hcop u L S t Jq ω v).2.2.1)
          (fun v => (fixSlots hcop u L S t Jq ω v).2.2.2)
          (fun v => (fixSlots hcop u L S t Jq ω v).2.1) Q')| ≤
      dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
          (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
        totalVariation (selectedWeight (termSet f f)
          (crtLaws blk (prefix_pairwise hpair) L (BracketEnergy.termLaw D L Qb f f))) *
        (L : ℝ) ^ (-σ) * density (blockScale * L) A := by
    intro ω
    have hsel : selectedMarginalsUniform (selectedWeight (termSet f f)
        (crtLaws blk (prefix_pairwise hpair) L (BracketEnergy.termLaw D L Qb f f))) := by
      intro v x
      have hempty : IsEmpty {b // b ∈ termSet f f} := by
        rw [hT]
        exact ⟨fun b => notMem_empty _ b.2⟩
      have h1 : ∀ z : Slot → ∀ b : {b // b ∈ termSet f f},
          ZMod (crtModuli m₀ blk p L b.1), z = fun _ b => (hempty.false b).elim := by
        intro z
        funext v' b
        exact (hempty.false b).elim
      have hcard : Fintype.card (∀ b : {b // b ∈ termSet f f},
          ZMod (crtModuli m₀ blk p L b.1)) = 1 := Fintype.card_eq_one_iff.mpr
        ⟨fun b => (hempty.false b).elim, fun y => funext fun b => (hempty.false b).elim⟩
      rw [hcard, Nat.cast_one, div_one]
      apply sum_congr _ (fun _ _ => rfl)
      ext z
      simp only [mem_filter, mem_univ, true_and, iff_true]
      funext b
      exact (hempty.false b).elim
    have key := hdcb blk p D.R hpair hp hinj hL hsc hM0 (termSet f f) hDE
      (by simp) (by exact ⟨1, rfl⟩) one_ne_zero hQcl (Nat.coprime_one_left 1) hqN
      (FiniteLaw.uniform Unit) _
      (selectedMarginalsUniform_liftWeight_uniform (termSet f f) _ hsel)
      (fun v => (fixSlots hcop u L S t Jq ω v).1) (hD0 ω) (hD0M ω) (hcop0 ω)
      (fun v => (fixSlots hcop u L S t Jq ω v).2.2.1) (hM ω)
      (fun _ v => (fixSlots hcop u L S t Jq ω v).2.2.2)
      (fun _ v => (fixSlots hcop u L S t Jq ω v).2.1)
      (fun _ => True)
      (fun _ => revealedModel (crtModuli m₀ blk p L) (termSet f f) A
        (fun v => (fixSlots hcop u L S t Jq ω v).1)
        (fun v => (fixSlots hcop u L S t Jq ω v).2.2.1)
        (fun v => (fixSlots hcop u L S t Jq ω v).2.2.2)
        (fun v => (fixSlots hcop u L S t Jq ω v).2.1) Q')
      (fun _ v x _ => by
        funext y
        simp only [revealedModel]
        rw [hT, hQ' ω v])
      (fun v hv => absurd trivial hv) hσ hS1
    rw [totalVariation_liftWeight] at key
    exact key
  have hatom : ∀ b ∈ termSet f f,
      ∀ hb : 0 < totalVariation (lawDensity (BracketEnergy.termLaw D L Qb f f b)),
      MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1 := by
    intro b hb
    rw [hT] at hb
    exact absurd hb (notMem_empty b)
  have hrest' : ∀ ω v, fixChanged u S v = true → ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll (crtModuli m₀ blk p L) (termSet f f)
        (fixSlots hcop u L S t Jq ω v).1 (fixSlots hcop u L S t Jq ω v).2.2.1 : ℕ) : ℤ) →
      referenceEnergy (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
          (child (crtModuli m₀ blk p L) (termSet f f) (Q' v) B
            (blockScale * stepEll (crtModuli m₀ blk p L)
            (termSet f f) (fixSlots hcop u L S t Jq ω v).1
            (fixSlots hcop u L S t Jq ω v).2.2.1)) ≤
        D.Y (stepEll (crtModuli m₀ blk p L) (termSet f f) (fixSlots hcop u L S t Jq ω v).1
          (fixSlots hcop u L S t Jq ω v).2.2.1) B := by
    intro ω v _ B hB
    rw [hT] at hB ⊢
    rw [hQ' ω v]
    exact hrest ω v B hB
  have key := fix_first_mean_le_query hcop D hpair hcex hθ.1 hθ.2 rfl ha hC0 hL hY0 hsc hM0 Qb
    f f hg hDE (by simp) (by exact ⟨1, rfl⟩) one_ne_zero hQcl (Nat.coprime_one_left 1) hqN S t
    Jq hcopJ u hu hD0 hD0M hcop0 hM Q' hun hrest' hdc hatom uQ hQ hR
  refine key.trans (le_of_eq ?_)
  rw [termNorm_eq_prod]

end Sarkozy.DensityChain
