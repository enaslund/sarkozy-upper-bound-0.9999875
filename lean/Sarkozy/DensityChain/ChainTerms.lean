module

public import Sarkozy.DensityChain.BlockDC
public import Sarkozy.DensityChain.MeanAssembly

@[expose] public section

/-!
# The chain-covered terms of `envC`, with `lem:record:density-dc` discharged

B9's `env_first_mean_le_of_moduli` bounds the residue average of a term `(f, g)` of the bracket
expansion of `envC` by the chain, from the per-term inputs `hrest`, `hdc`, `hatom` and the
modulus and price conditions. This file discharges **`hdc`** (`lem:record:density-dc` with
`lem:record:fibre-scale`) by `density_dc_block` (`DensityChain.BlockDC`), at the paper's
cutoffs `Q' v = Q(K ℓ_v)`:

* **`env_term_chain`**: for every `ε > 0` there are moment constants `C₁, C₇₁` such that every
  chain-covered term satisfies
  `E_ω |E_{f,g}| ≤ (1 + u_L) Π_𝒥 Y ∏_f u ∏_g u' + ∏_{f∪g} ‖Λ_𝔟‖ · C_dc L^{-σ} α`,
  with `C_dc = dcConstant Q_pre γ M₀ |X₀| C₁ C₇₁` uniform in `L, A, 𝒥, f, g`. The inputs that
  remain are those the paper names: restoration (`hrest`), the unit mixed `L^{72/ϑ}` moments of
  the selected laws (`hatom`, `lem:density:coupled`, `lem:density:packets`), condition (b) of
  `def:record:structured-energy` for the selected laws (`hsel`), the modulus conditions on
  `D_{f∪g}`, the price inequalities, distinct prime tail moduli, and (S1).
* **`termNorm_eq_prod`**: the factor `∏_{f∪g} ‖Λ_𝔟‖` of B9's bound is `∏_𝔟 G(𝔟, f 𝔟, g 𝔟)` with
  `G 𝔟 x y = ‖Q_𝔟‖, ‖Ñ_{0,𝔟} − μ_𝔟‖, 1`, the per-atom weights of `envMeanBound_of_terms`.
-/

namespace Sarkozy.DensityChain

open Finset Function
open scoped BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- The per-atom weight of a term: `‖Q_𝔟‖` on `f`, `‖Ñ_{0,𝔟} − μ_𝔟‖` on `g`, `1` elsewhere. -/
noncomputable def termWeight (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (b : BlockAtom Bk J L) (x y : Bool) : ℝ :=
  if x then ∑ z, |lawDensity (Qb b) z| else if y then ∑ z, |lawDensity (recLaw D L b) z| else 1

omit [DecidableEq P] in
theorem termWeight_nonneg (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (b : BlockAtom Bk J L) (x y : Bool) :
    0 ≤ termWeight D L Qb b x y := by
  unfold termWeight
  split_ifs
  · exact sum_nonneg fun _ _ => abs_nonneg _
  · exact sum_nonneg fun _ _ => abs_nonneg _
  · exact zero_le_one

omit [DecidableEq P] in
/-- **The factor `∏_{f∪g} ‖Λ_𝔟‖` of the chain is a product of per-atom weights.** -/
theorem termNorm_eq_prod (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (f g : BlockAtom Bk J L → Bool) :
    (∏ b : {b // b ∈ termSet f g}, ∑ x : Slot → BlockLabel m₀ blk p L b.1,
        |lawDensity (BracketEnergy.termLaw D L Qb f g b.1) x|) =
      ∏ b, termWeight D L Qb b (f b) (g b) := by
  rw [prod_coe_sort (termSet f g) (fun b => ∑ x : Slot → BlockLabel m₀ blk p L b,
    |lawDensity (BracketEnergy.termLaw D L Qb f g b) x|)]
  unfold termSet
  rw [prod_filter]
  apply prod_congr rfl
  intro b _
  unfold termWeight BracketEnergy.termLaw
  cases hf : f b <;> cases hg : g b <;> simp

/-- The modulus `D_{0,v}` of the slot datum of `envC` (it does not depend on the residues). -/
noncomputable def envD0 (u : E → reservedCut.Half)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) (v : Slot) :
    ℕ :=
  match slotQuery u v with
  | some e => revealedModulus blockScale pr h (Jq e)
  | none => 1

/-- The length `M_v` of the slot datum of `envC`. -/
noncomputable def envM (u : E → reservedCut.Half) (L : ℕ) (v : Slot) : ℕ :=
  match slotQuery u v with
  | some _ => L
  | none => blockScale * L

omit [DecidableEq P] [DecidableEq E] in
theorem envSlots_fst (u : E → reservedCut.Half) (L : ℕ)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (v : Slot) :
    (envSlots hcop u L Jq ω v).1 = envD0 u Jq v := by
  unfold envSlots envD0
  rw [slotDatum_eq_optDatum]
  rcases slotQuery u v with _ | e <;> rfl

omit [DecidableEq P] [DecidableEq E] in
theorem envSlots_len (u : E → reservedCut.Half) (L : ℕ)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (v : Slot) :
    (envSlots hcop u L Jq ω v).2.2.1 = envM u L v := by
  unfold envSlots envM
  rw [slotDatum_eq_optDatum]
  rcases slotQuery u v with _ | e <;> rfl

/-- **The chain-covered first bound of a term of `envC`, with `hdc` discharged**
(`lem:bracket-energy` first bound, `prop:record:density-structured`, `lem:record:density-dc`,
`lem:twointerval`(ii); B9's `env_first_mean_le_of_moduli` with `density_dc_block`). For every
`ε > 0` there are `C₁, C₇₁ > 0` such that every term `(f, g)`, `g ⊥ f`, at a depth vector that
reveals the intervals, with `D_{f∪g} ≠ 1` and the modulus conditions, satisfies
`E_ω |E_{f,g}| ≤ (1 + u_L) Π_𝒥 Y ∏_f u ∏_g u' + ∏_{f∪g} ‖Λ_𝔟‖ · C_dc L^{-σ} α`, with
`C_dc = dcConstant Q_pre γ M₀ |X₀| C₁ C₇₁`, for every `σ ≥ 0` with `ε/20 − γ/40 ≤ −σ`.

Remaining inputs (as the paper states them): `hrest` (restoration at the child scales, with the
paper's cutoffs), `hatom` (unit mixed `L^{72/ϑ}` of the selected laws), `hsel`
(`def:record:structured-energy`(b) for the selected laws), the modulus conditions, the price
inequalities `hQ`, `hR`, and distinct prime tail moduli (`hp`, `hinj`). -/
theorem env_term_chain (ε : ℝ) (hε : 0 < ε) :
    ∃ C1 C71 : ℝ, 0 < C1 ∧ 0 < C71 ∧ DCBlockProp ε C1 C71 ∧
    ∀ (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    {Yf : ℕ → Finset ℤ → ℝ} {a' θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (_hcex : IsLeastCounterexample Yf a' θ C0 L A) (_hθ : 0 < θ) (_hθ2 : 2 * (θ / 72) ≤ 1)
    (_ha : 0 ≤ a') (_hC0 : 0 ≤ C0) (_hL : 2 ≤ L) (_hY0 : Yf L ∅ ≤ 0)
    {M0 Qcl Qpre N0 N0' : ℕ} (_hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (_hM0 : 1 ≤ M0) (_hp : ∀ j, (p L j).Prime) (_hinj : Injective (p L))
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (f g : BlockAtom Bk J L → Bool)
    (_hg : g ∈ validChoices f)
    {qE cE : ℕ} (_hDE : ∏ b ∈ (termSet f g), crtModuli m₀ blk p L b = qE * cE)
    (_hqE : Squarefree qE) (_hcE : IsSquare cE) (_hcE0 : cE ≠ 0) (_hcQ : cE ≤ Qcl)
    (_hcopE : qE.Coprime cE) (_hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (_hJ : ∀ e, (Jq e none : ℕ) ≠ 0)
    (u : E → reservedCut.Half) (_hu : Injective u)
    (_hMod : modulus pr h ∣ M0)
    (_hcopM : ∀ k, (modulus pr h).Coprime (crtModuli m₀ blk p L k))
    (_hne : ∏ j ∈ termSet f g, crtModuli m₀ blk p L j ≠ 1)
    (_hsel : selectedMarginalsUniform (selectedWeight (termSet f g)
      (crtLaws blk (prefix_pairwise hpair) L (BracketEnergy.termLaw D L Qb f g))))
    {σ : ℝ} (_hσ : 0 ≤ σ) (_hS1 : ε / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ)
    (_hrest : ∀ ω v, ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll (crtModuli m₀ blk p L) (termSet f g)
        (envSlots hcop u L Jq ω v).1 (envSlots hcop u L Jq ω v).2.2.1 : ℕ) : ℤ) →
      referenceEnergy (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
          (child (crtModuli m₀ blk p L) (termSet f g)
            (paperCutoff (blockScale * stepEll (crtModuli m₀ blk p L) (termSet f g)
              (envSlots hcop u L Jq ω v).1 (envSlots hcop u L Jq ω v).2.2.1)) B
            (blockScale * stepEll (crtModuli m₀ blk p L)
            (termSet f g) (envSlots hcop u L Jq ω v).1
            (envSlots hcop u L Jq ω v).2.2.1)) ≤
        Yf (stepEll (crtModuli m₀ blk p L) (termSet f g) (envSlots hcop u L Jq ω v).1
          (envSlots hcop u L Jq ω v).2.2.1) B)
    (_hatom : ∀ b ∈ termSet f g,
      ∀ hb : 0 < totalVariation (lawDensity (BracketEnergy.termLaw D L Qb f g b)),
      MixedLpBound (variationLaw _ hb) (72 / θ) 1)
    (uQ : BlockAtom Bk J L → ℝ)
    (_hQ : ∀ b, (∑ z, |lawDensity (Qb b) z|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a' ≤ uQ b)
    (_hR : ∀ b, (∑ z, |lawDensity (recLaw D L b) z|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a' ≤ D.GB.uprice L b),
    (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect (fun ω =>
      |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise hpair) L
        (BracketEnergy.termLaw D L Qb f g)))
        (pairInputs u u (revealedInputCRT blk hcop D L A Jq)
          (revealedInputCRT blk hcop D L A Jq)
          (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)|) ≤
      (1 + scaleU blockScale M0 Qcl stageTau L) *
          (conductorPrice pr h (2 * a' / 72) Jq * Yf L A *
            ((∏ b, if f b then uQ b else 1) * ∏ b, (if g b then D.GB.uprice L b else 1))) +
        (∏ b, termWeight D L Qb b (f b) (g b)) *
          (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
            (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
            (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  obtain ⟨C1, C71, hC1, hC71, hdcb⟩ := density_dc_block' ε hε
  refine ⟨C1, C71, hC1, hC71, hdcb, ?_⟩
  intro D Yf a' θ C0 L A hpair hcex hθ hθ2 ha hC0 hL hY0 M0 Qcl Qpre N0 N0' hsc hM0 hp hinj Qb
    f g hg qE cE hDE hqE hcE hcE0 hcQ hcopE hqN Jq hJ u hu hMod hcopM hne hsel σ hσ hS1 hrest
    hatom uQ hQ hR
  set Q' : Slot → ℝ := fun v => paperCutoff (blockScale * stepEll (crtModuli m₀ blk p L)
    (termSet f g) (envD0 u Jq v) (envM u L v)) with hQ'def
  have hQ' : ∀ ω v, Q' v = paperCutoff (blockScale * stepEll (crtModuli m₀ blk p L)
      (termSet f g) (envSlots hcop u L Jq ω v).1 (envSlots hcop u L Jq ω v).2.2.1) := by
    intro ω v
    have h1 := envSlots_fst hcop u L Jq ω v
    have h2 := envSlots_len hcop u L Jq ω v
    simp only [hQ'def]
    rw [h2, h1]
  -- the slot conditions (as in `env_first_mean_le_of_moduli`)
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
  -- `hdc` from `density_dc_block`
  have hdc : ∀ ω, |structuredEnergy
        (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
        (FiniteLaw.uniform Unit)
        (liftWeight (termSet f g)
          (selectedWeight (termSet f g)
            (crtLaws blk (prefix_pairwise hpair) L (BracketEnergy.termLaw D L Qb f g)))
          (uniformRest (Xa := fun b => ZMod (crtModuli m₀ blk p L b)) (termSet f g)))
        (paperInputs (crtModuli m₀ blk p L) (termSet f g) (paperCutoff (blockScale * L)) A
          (fun v => (envSlots hcop u L Jq ω v).1)
          (fun v => (envSlots hcop u L Jq ω v).2.2.1)
          (fun _ v => (envSlots hcop u L Jq ω v).2.2.2)
          (fun _ v => (envSlots hcop u L Jq ω v).2.1)) -
      structuredEnergy
        (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
        (FiniteLaw.uniform Unit)
        (liftWeight (termSet f g)
          (selectedWeight (termSet f g)
            (crtLaws blk (prefix_pairwise hpair) L (BracketEnergy.termLaw D L Qb f g)))
          (uniformRest (Xa := fun b => ZMod (crtModuli m₀ blk p L b)) (termSet f g)))
        (fun _ => revealedModel (crtModuli m₀ blk p L) (termSet f g) A
          (fun v => (envSlots hcop u L Jq ω v).1)
          (fun v => (envSlots hcop u L Jq ω v).2.2.1)
          (fun v => (envSlots hcop u L Jq ω v).2.2.2)
          (fun v => (envSlots hcop u L Jq ω v).2.1) Q')| ≤
      dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
          (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
        totalVariation (selectedWeight (termSet f g)
          (crtLaws blk (prefix_pairwise hpair) L (BracketEnergy.termLaw D L Qb f g))) *
        (L : ℝ) ^ (-σ) * density (blockScale * L) A := by
    intro ω
    have key := hdcb blk p D.R hpair hp hinj hL hsc hM0 (termSet f g) hDE hqE hcE hcE0 hcQ
      hcopE hqN (FiniteLaw.uniform Unit) _
      (selectedMarginalsUniform_liftWeight_uniform (termSet f g) _ hsel)
      (fun v => (envSlots hcop u L Jq ω v).1) (hD0 ω) (hD0M ω) (hcop0 ω)
      (fun v => (envSlots hcop u L Jq ω v).2.2.1) (hM ω)
      (fun _ v => (envSlots hcop u L Jq ω v).2.2.2) (fun _ v => (envSlots hcop u L Jq ω v).2.1)
      (fun _ => True)
      (fun _ => revealedModel (crtModuli m₀ blk p L) (termSet f g) A
        (fun v => (envSlots hcop u L Jq ω v).1)
        (fun v => (envSlots hcop u L Jq ω v).2.2.1)
        (fun v => (envSlots hcop u L Jq ω v).2.2.2)
        (fun v => (envSlots hcop u L Jq ω v).2.1) Q')
      (fun _ v x _ => by
        funext y
        simp only [revealedModel]
        rw [hQ' ω v])
      (fun v hv => absurd trivial hv) hσ hS1
    rw [totalVariation_liftWeight] at key
    exact key
  exact env_first_mean_le_of_moduli hcop D hpair hcex hθ hθ2 ha hC0 hL hY0 hsc hM0 Qb f g hg hDE
    hqE hcE hcE0 hcQ hcopE hqN Jq hJ u hu hMod hcopM hne Q'
    (fun ω v _ B hB => by rw [hQ' ω v]; exact hrest ω v B hB) hdc hatom uQ hQ hR |>.trans
    (le_of_eq (by rw [termNorm_eq_prod]))

/-- The modulus `D_{0,v}` of the slot datum of `fixC`. -/
noncomputable def fixD0 (u : E → reservedCut.Half) (S : Finset E)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) (v : Slot) :
    ℕ :=
  match slotQuery u v with
  | some e => if e ∈ S then revealedModulus blockScale pr h (Jq e) else 1
  | none => 1

/-- The length `M_v` of the slot datum of `fixC`. -/
noncomputable def fixM (u : E → reservedCut.Half) (S : Finset E) (L : ℕ) (v : Slot) : ℕ :=
  match slotQuery u v with
  | some e => if e ∈ S then L else blockScale * L
  | none => blockScale * L

omit [DecidableEq P] in
theorem fixSlots_fst (u : E → reservedCut.Half) (L : ℕ) (S : Finset E) (t : ZMod blockScale)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (v : Slot) :
    (fixSlots hcop u L S t Jq ω v).1 = fixD0 u S Jq v := by
  unfold fixSlots fixD0
  rw [slotDatum_eq_optDatum]
  rcases slotQuery u v with _ | e
  · rfl
  · change (fixDatum hcop L S t Jq e (ω e)).1 =
      (if e ∈ S then revealedModulus blockScale pr h (Jq e) else 1)
    unfold fixDatum
    split_ifs <;> rfl

omit [DecidableEq P] in
theorem fixSlots_len (u : E → reservedCut.Half) (L : ℕ) (S : Finset E) (t : ZMod blockScale)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (v : Slot) :
    (fixSlots hcop u L S t Jq ω v).2.2.1 = fixM u S L v := by
  unfold fixSlots fixM
  rw [slotDatum_eq_optDatum]
  rcases slotQuery u v with _ | e
  · rfl
  · change (fixDatum hcop L S t Jq e (ω e)).2.2.1 = (if e ∈ S then L else blockScale * L)
    unfold fixDatum
    by_cases he : e ∈ S
    · rw [ite_eq_left_of_eq_true _ _ (eq_true he), ite_eq_left_of_eq_true _ _ (eq_true he)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false he), ite_eq_right_of_eq_false _ _ (eq_false he)]
      rfl

/-- **The chain-covered first bound of a term of `fixC`, with `hdc` discharged** (as
`env_term_chain`, for B9's `fix_first_mean_le`; the slot conditions are derived from
`M₀^{index} ∣ M₀`, the coprimality with the atom moduli and `D_{f∪g} ≠ 1`). -/
theorem fix_term_chain (ε : ℝ) (hε : 0 < ε) :
    ∃ C1 C71 : ℝ, 0 < C1 ∧ 0 < C71 ∧ DCBlockProp ε C1 C71 ∧
    ∀ (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    {Yf : ℕ → Finset ℤ → ℝ} {a' θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (_hcex : IsLeastCounterexample Yf a' θ C0 L A) (_hθ : 0 < θ) (_hθ2 : 2 * (θ / 72) ≤ 1)
    (_hθd : θ = densityExponent)
    (_ha : 0 ≤ a') (_hC0 : 0 ≤ C0) (_hL : 2 ≤ L) (_hY0 : Yf L ∅ ≤ 0)
    {M0 Qcl Qpre N0 N0' : ℕ} (_hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (_hM0 : 1 ≤ M0) (_hp : ∀ j, (p L j).Prime) (_hinj : Injective (p L))
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (f g : BlockAtom Bk J L → Bool)
    (_hg : g ∈ validChoices f)
    {qE cE : ℕ} (_hDE : ∏ b ∈ (termSet f g), crtModuli m₀ blk p L b = qE * cE)
    (_hqE : Squarefree qE) (_hcE : IsSquare cE) (_hcE0 : cE ≠ 0) (_hcQ : cE ≤ Qcl)
    (_hcopE : qE.Coprime cE) (_hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    (S : Finset E) (t : ZMod blockScale)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (u : E → reservedCut.Half) (_hu : Injective u)
    (_hMod : modulus pr h ∣ M0)
    (_hcopM : ∀ k, (modulus pr h).Coprime (crtModuli m₀ blk p L k))
    (_hne : ∏ j ∈ termSet f g, crtModuli m₀ blk p L j ≠ 1)
    (_hsel : selectedMarginalsUniform (selectedWeight (termSet f g)
      (crtLaws blk (prefix_pairwise hpair) L (BracketEnergy.termLaw D L Qb f g))))
    {σ : ℝ} (_hσ : 0 ≤ σ) (_hS1 : ε / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ)
    (_hrest : ∀ ω v, ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll (crtModuli m₀ blk p L) (termSet f g)
        (fixSlots hcop u L S t Jq ω v).1 (fixSlots hcop u L S t Jq ω v).2.2.1 : ℕ) : ℤ) →
      referenceEnergy (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
          (child (crtModuli m₀ blk p L) (termSet f g)
            (paperCutoff (blockScale * stepEll (crtModuli m₀ blk p L) (termSet f g)
              (fixSlots hcop u L S t Jq ω v).1 (fixSlots hcop u L S t Jq ω v).2.2.1)) B
            (blockScale * stepEll (crtModuli m₀ blk p L)
            (termSet f g) (fixSlots hcop u L S t Jq ω v).1
            (fixSlots hcop u L S t Jq ω v).2.2.1)) ≤
        Yf (stepEll (crtModuli m₀ blk p L) (termSet f g) (fixSlots hcop u L S t Jq ω v).1
          (fixSlots hcop u L S t Jq ω v).2.2.1) B)
    (_hatom : ∀ b ∈ termSet f g,
      ∀ hb : 0 < totalVariation (lawDensity (BracketEnergy.termLaw D L Qb f g b)),
      MixedLpBound (variationLaw _ hb) (72 / θ) 1)
    (uQ : BlockAtom Bk J L → ℝ)
    (_hQ : ∀ b, (∑ z, |lawDensity (Qb b) z|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a' ≤ uQ b)
    (_hR : ∀ b, (∑ z, |lawDensity (recLaw D L b) z|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a' ≤ D.GB.uprice L b),
    (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect (fun ω =>
      |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise hpair) L
        (BracketEnergy.termLaw D L Qb f g)))
        (pairInputs u u (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
          (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
          (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)|) ≤
      (1 + scaleU blockScale M0 Qcl stageTau L) *
          (fixedPrice pr h (2 * a' / 72) S Jq * Yf L A *
            ((∏ b, if f b then uQ b else 1) * ∏ b, (if g b then D.GB.uprice L b else 1))) +
        (∏ b, termWeight D L Qb b (f b) (g b)) *
          (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
            (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
            (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  obtain ⟨C1, C71, hC1, hC71, hdcb⟩ := density_dc_block' ε hε
  refine ⟨C1, C71, hC1, hC71, hdcb, ?_⟩
  intro D Yf a' θ C0 L A hpair hcex hθ hθ2 hθd ha hC0 hL hY0 M0 Qcl Qpre N0 N0' hsc hM0 hp
    hinj Qb f g hg qE cE hDE hqE hcE hcE0 hcQ hcopE hqN S t Jq u hu hMod hcopM hne hsel σ hσ
    hS1 hrest hatom uQ hQ hR
  set Q' : Slot → ℝ := fun v => paperCutoff (blockScale * stepEll (crtModuli m₀ blk p L)
    (termSet f g) (fixD0 u S Jq v) (fixM u S L v)) with hQ'def
  have hQ' : ∀ ω v, Q' v = paperCutoff (blockScale * stepEll (crtModuli m₀ blk p L)
      (termSet f g) (fixSlots hcop u L S t Jq ω v).1 (fixSlots hcop u L S t Jq ω v).2.2.1) := by
    intro ω v
    have h1 := fixSlots_fst hcop u L S t Jq ω v
    have h2 := fixSlots_len hcop u L S t Jq ω v
    simp only [hQ'def]
    rw [h2, h1]
  have hJd : ∀ e, revealedModulus blockScale pr h (Jq e) ∣ modulus pr h :=
    fun e => revealedModulus_dvd (Jq e)
  have hmpos : 0 < modulus pr h := Nat.pos_of_ne_zero (NeZero.ne _)
  have hKL : L ≠ blockScale * L := by
    have : 2 ≤ blockScale := by norm_num [blockScale]
    nlinarith
  have hcopJ : ∀ e, (revealedModulus blockScale pr h (Jq e)).Coprime
      (∏ j ∈ termSet f g, crtModuli m₀ blk p L j) :=
    fun e => Nat.Coprime.prod_right fun k _ => Nat.Coprime.coprime_dvd_left (hJd e) (hcopM k)
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
  have hchg : ∀ ω v, ¬((fixSlots hcop u L S t Jq ω v).1 *
      ∏ j ∈ (termSet f g), crtModuli m₀ blk p L j = 1 ∧
      (fixSlots hcop u L S t Jq ω v).2.2.1 = blockScale * L) := by
    intro ω v h1
    rw [fixSlots_len, fixSlots_fst] at h1
    unfold fixD0 fixM at h1
    rcases hq : slotQuery u v with _ | e
    · rw [hq] at h1
      apply hne
      have := h1.1
      change 1 * ∏ j ∈ termSet f g, crtModuli m₀ blk p L j = 1 at this
      rwa [one_mul] at this
    · rw [hq] at h1
      change (if e ∈ S then revealedModulus blockScale pr h (Jq e) else 1) *
          ∏ j ∈ termSet f g, crtModuli m₀ blk p L j = 1 ∧
        (if e ∈ S then L else blockScale * L) = blockScale * L at h1
      by_cases he : e ∈ S
      · simp only [he, ↓reduceIte] at h1
        exact hKL h1.2
      · simp only [he, ↓reduceIte, one_mul] at h1
        exact hne h1.1
  have hdc : ∀ ω, |structuredEnergy
        (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
        (FiniteLaw.uniform Unit)
        (liftWeight (termSet f g)
          (selectedWeight (termSet f g)
            (crtLaws blk (prefix_pairwise hpair) L (BracketEnergy.termLaw D L Qb f g)))
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
            (crtLaws blk (prefix_pairwise hpair) L (BracketEnergy.termLaw D L Qb f g)))
          (uniformRest (Xa := fun b => ZMod (crtModuli m₀ blk p L b)) (termSet f g)))
        (fun _ => revealedModel (crtModuli m₀ blk p L) (termSet f g) A
          (fun v => (fixSlots hcop u L S t Jq ω v).1)
          (fun v => (fixSlots hcop u L S t Jq ω v).2.2.1)
          (fun v => (fixSlots hcop u L S t Jq ω v).2.2.2)
          (fun v => (fixSlots hcop u L S t Jq ω v).2.1) Q')| ≤
      dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
          (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
        totalVariation (selectedWeight (termSet f g)
          (crtLaws blk (prefix_pairwise hpair) L (BracketEnergy.termLaw D L Qb f g))) *
        (L : ℝ) ^ (-σ) * density (blockScale * L) A := by
    intro ω
    have key := hdcb blk p D.R hpair hp hinj hL hsc hM0 (termSet f g) hDE hqE hcE hcE0 hcQ
      hcopE hqN (FiniteLaw.uniform Unit) _
      (selectedMarginalsUniform_liftWeight_uniform (termSet f g) _ hsel)
      (fun v => (fixSlots hcop u L S t Jq ω v).1) (hD0 ω) (hD0M ω) (hcop0 ω)
      (fun v => (fixSlots hcop u L S t Jq ω v).2.2.1) (hM ω)
      (fun _ v => (fixSlots hcop u L S t Jq ω v).2.2.2)
      (fun _ v => (fixSlots hcop u L S t Jq ω v).2.1)
      (fun _ => True)
      (fun _ => revealedModel (crtModuli m₀ blk p L) (termSet f g) A
        (fun v => (fixSlots hcop u L S t Jq ω v).1)
        (fun v => (fixSlots hcop u L S t Jq ω v).2.2.1)
        (fun v => (fixSlots hcop u L S t Jq ω v).2.2.2)
        (fun v => (fixSlots hcop u L S t Jq ω v).2.1) Q')
      (fun _ v x _ => by
        funext y
        simp only [revealedModel]
        rw [hQ' ω v])
      (fun v hv => absurd trivial hv) hσ hS1
    rw [totalVariation_liftWeight] at key
    exact key
  exact fix_first_mean_le hcop D hpair hcex hθ hθ2 hθd ha hC0 hL hY0 hsc hM0 Qb f g hg hDE
    hqE hcE hcE0 hcQ hcopE hqN S t Jq hcopJ u hu hD0 hD0M hcop0 hM hchg Q'
    (fun ω v _ B hB => by rw [hQ' ω v]; exact hrest ω v B hB) hdc hatom uQ hQ hR |>.trans
    (le_of_eq (by rw [termNorm_eq_prod]))

end Sarkozy.DensityChain
