module

public import Sarkozy.BracketEnergy.DataRevealed

@[expose] public section

/-!
# The first bound of `hfirst` for `envC` from the revealed-input chain

For a term `(f, g)` of the bracket expansion (`EnvelopeBracketInputs.hfirstL`), the selected law
is `termLaw` (`Q_𝔟` on `f`, the reserved records `Ñ_{0,𝔟} − μ_𝔟` on `g`, `μ_𝔟` elsewhere) and the
selected set is `termSet f g`.

* `termLaw_off`: the law is `μ` off `termSet f g`;
* `envDatum`, `revealedInputCRT_eq_paperForm`: at a depth vector that reveals the interval, the
  revealed input of the query `e` is `g^{I_b, D_{𝒥_e}, s mod D_{𝒥_e}}` (`lem:twointerval`(ii));
* **`env_first_le_chain`**: the energy of `hfirstL` at such a depth vector is bounded by the
  revealed-input chain (`data_block_energy_le_structured`), given the chain's per-term inputs.
  The main price is `def:record:structured-energy`'s
  `∏_v ξ_v^{a/72} ∏_{v changed} (ᾱ_v/α)^{θ/72}`, with `ξ_v = K sq(D_{𝒥_e} D_E)` at the two slots
  of the query `e` and `sq(D_E)` elsewhere, and `ᾱ_v` the density of `A` on
  `I_b ∩ {x ≡ s (mod D_{𝒥_e})}` at the query slots.
-/

open Finset Function
open scoped BigOperators

namespace Sarkozy.BracketEnergy

open Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper Sarkozy.Structured Sarkozy.Functional
  Sarkozy.FourierArithmetic Sarkozy.PaperFrame Sarkozy.BlockFrame Sarkozy.IndexSupport
  Sarkozy.TheoremC

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- The selected law of the term `(f, g)`: `Q` on `f`, the reserved records on `g`, `μ`
elsewhere. -/
noncomputable def termLaw (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (f g : BlockAtom Bk J L → Bool)
    (b : BlockAtom Bk J L) : TheoremCBlock.AtomMeasure m₀ blk p L b :=
  if f b then Qb b else if g b then recLaw D L b else muLaw D L b

/-- The selected set of the term `(f, g)`. -/
def termSet {L : ℕ} (f g : BlockAtom Bk J L → Bool) : Finset (BlockAtom Bk J L) :=
  univ.filter fun b => f b = true ∨ g b = true

omit [DecidableEq P] in
/-- The term law is the reference off the selected set. -/
theorem termLaw_off (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (f g : BlockAtom Bk J L → Bool) :
    ∀ b ∉ termSet f g, termLaw D L Qb f g b = D.R.law p L b := by
  intro b hb
  unfold termSet at hb
  simp only [mem_filter, mem_univ, true_and, not_or, Bool.not_eq_true] at hb
  unfold termLaw
  simp only [hb.1, hb.2, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- The slot datum of the query `e` of `envC` at a depth vector that reveals the interval
`b = η_none`: `D_{𝒥_e}`, `s mod D_{𝒥_e}`, the interval `I_b = [(b − 1)L + 1, bL]`. -/
noncomputable def envDatum (L : ℕ)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) (e : E)
    (η : ∀ j : Option P, CoordSpace blockScale pr h j) : SlotDatum :=
  ⟨revealedModulus blockScale pr h (Jq e), revealedResidue hcop (Jq e) η, L,
    ((leastPosRep (η none) : ℤ) - 1) * L⟩

/-- The slot data of the pair inputs of `envC` (queries at the half-slots `u`). -/
noncomputable def envSlots (u : E → reservedCut.Half) (L : ℕ)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (v : Slot) : SlotDatum :=
  slotDatum u (fun e => envDatum hcop L Jq e (ω e)) (wholeDatum L) v

/-- **The revealed input of `envC` is the paper's input** at a depth vector that reveals the
interval (`lem:twointerval`(ii), `revealedInputCRT_eq`). -/
theorem revealedInputCRT_eq_paperForm (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (L : ℕ) (A : Finset ℤ) (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (e : E) (η : ∀ j : Option P, CoordSpace blockScale pr h j) (hJ : (Jq e none : ℕ) ≠ 0) :
    revealedInputCRT blk hcop D L A Jq e η =
      paperForm (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A
        (envDatum hcop L Jq e η) := by
  funext y
  rw [revealedInputCRT_eq]
  unfold revealedEnvInput paperForm envDatum
  simp only [hJ, ↓reduceIte]
  rw [blockInterval_eq_Icc]

/-- **The first bound of `hfirstL`, `hfirstR` (`envC`) from the revealed-input chain**
(`lem:bracket-energy` first bound, `prop:record:density-structured` with the structured slot data
of `lem:envelope-energy`, at `ϑ`, `lem:record:density-dc`). With `Qb = envIncL D L`,
`u = D.index.u` it bounds the energy of `hfirstL`; with `envIncR`, `D.index.w`, that of
`hfirstR`. -/
theorem env_first_le_chain (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    {Yf : ℕ → Finset ℤ → ℝ} {a' θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (hcex : IsLeastCounterexample Yf a' θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1)
    (ha : 0 ≤ a') (hC0 : 0 ≤ C0) (hL : 2 ≤ L) (hY0 : Yf L ∅ ≤ 0)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0)
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (f g : BlockAtom Bk J L → Bool)
    {qE cE : ℕ} (hDE : ∏ b ∈ (termSet f g), crtModuli m₀ blk p L b = qE * cE) (hqE : Squarefree qE)
    (hcE : IsSquare cE) (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl) (hcopE : qE.Coprime cE)
    (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (hJ : ∀ e, (Jq e none : ℕ) ≠ 0) (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j)
    (u : E → reservedCut.Half)
    (hD0 : ∀ v, 1 ≤ (envSlots hcop u L Jq ω v).1)
    (hD0M : ∀ v, (envSlots hcop u L Jq ω v).1 ∣ M0)
    (hcop0 : ∀ v k, ((envSlots hcop u L Jq ω v).1).Coprime (crtModuli m₀ blk p L k))
    (hM : ∀ v, (envSlots hcop u L Jq ω v).2.2.1 = blockScale * L ∨
      (envSlots hcop u L Jq ω v).2.2.1 = L)
    (changed : Slot → Prop) [DecidablePred changed]
    (hchg : ∀ v, changed v → ¬((envSlots hcop u L Jq ω v).1 *
      ∏ j ∈ (termSet f g), crtModuli m₀ blk p L j = 1 ∧
      (envSlots hcop u L Jq ω v).2.2.1 = blockScale * L))
    (Q' : Slot → ℝ)
    (hun : ∀ v, ¬changed v → ∀ x, referenceEnergy
      (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
      (revealedModel (crtModuli m₀ blk p L) (termSet f g) A (fun v => (envSlots hcop u L Jq ω v).1)
        (fun v => (envSlots hcop u L Jq ω v).2.2.1)
        (fun v => (envSlots hcop u L Jq ω v).2.2.2)
        (fun v => (envSlots hcop u L Jq ω v).2.1) Q' v x) ≤ Yf L A)
    {Cdc σ : ℝ}
    (hrest : ∀ v, changed v → ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll (crtModuli m₀ blk p L) (termSet f g)
        (envSlots hcop u L Jq ω v).1 (envSlots hcop u L Jq ω v).2.2.1 : ℕ) : ℤ) →
      referenceEnergy (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
          (child (crtModuli m₀ blk p L) (termSet f g) (Q' v) B
            (blockScale * stepEll (crtModuli m₀ blk p L)
            (termSet f g) (envSlots hcop u L Jq ω v).1
            (envSlots hcop u L Jq ω v).2.2.1)) ≤
        Yf (stepEll (crtModuli m₀ blk p L) (termSet f g) (envSlots hcop u L Jq ω v).1
          (envSlots hcop u L Jq ω v).2.2.1) B)
    (hdc : |structuredEnergy
          (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
          (FiniteLaw.uniform Unit)
          (liftWeight (termSet f g)
            (selectedWeight (termSet f g)
              (crtLaws blk (prefix_pairwise hpair) L (termLaw D L Qb f g)))
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
              (crtLaws blk (prefix_pairwise hpair) L (termLaw D L Qb f g)))
            (uniformRest (Xa := fun b => ZMod (crtModuli m₀ blk p L b)) (termSet f g)))
          (fun _ => revealedModel (crtModuli m₀ blk p L) (termSet f g) A
            (fun v => (envSlots hcop u L Jq ω v).1)
            (fun v => (envSlots hcop u L Jq ω v).2.2.1)
            (fun v => (envSlots hcop u L Jq ω v).2.2.2)
            (fun v => (envSlots hcop u L Jq ω v).2.1) Q')| ≤
      Cdc * totalVariation
        (selectedWeight (termSet f g)
          (crtLaws blk (prefix_pairwise hpair) L (termLaw D L Qb f g))) *
        (L : ℝ) ^ (-σ) * density (blockScale * L) A)
    (hatom : ∀ b ∈ termSet f g, ∀ hb : 0 < totalVariation (lawDensity (termLaw D L Qb f g b)),
      MixedLpBound (variationLaw _ hb) (72 / θ) 1) :
    |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise hpair) L
        (termLaw D L Qb f g)))
        (pairInputs u u (revealedInputCRT blk hcop D L A Jq)
          (revealedInputCRT blk hcop D L A Jq)
          (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
      (∏ b : {b // b ∈ (termSet f g)}, ∑ x : Slot → BlockLabel m₀ blk p L b.1,
        |lawDensity (termLaw D L Qb f g b.1) x|) *
        ((1 + scaleU blockScale M0 Qcl stageTau L) *
          mainPrice (paperPrice (crtModuli m₀ blk p L) (termSet f g)
              (fun v => (envSlots hcop u L Jq ω v).1)
              (fun v => (envSlots hcop u L Jq ω v).2.2.1) L)
            (paperMeanDensity (FiniteLaw.uniform Unit) A
              (fun v => (envSlots hcop u L Jq ω v).1)
              (fun v => (envSlots hcop u L Jq ω v).2.2.1)
              (fun _ v => (envSlots hcop u L Jq ω v).2.2.2)
              (fun _ v => (envSlots hcop u L Jq ω v).2.1))
            changed a' θ (density (blockScale * L) A) * Yf L A +
          Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A) :=
  data_block_energy_le_structured D hpair hcex hθ hθ2 ha hC0 hL hY0 hsc hM0
    (termLaw D L Qb f g) (termSet f g)
    (termLaw_off D L _ f g) hDE hqE hcE hcE0 hcQ hcopE hqN u
    (revealedInputCRT blk hcop D L A Jq) ω (paperCutoff (blockScale * L))
    (fun e => envDatum hcop L Jq e (ω e))
    (fun e => revealedInputCRT_eq_paperForm hcop D L A Jq e (ω e) (hJ e)) hD0 hD0M hcop0 hM
    changed hchg Q' hun hrest hdc hatom

/-! ## `fixC` -/

/-- The slot datum of the query `e` of `fixC` at the interval `t`: for `e ∈ 𝒮`, `D_{𝒥_e}`,
`s mod D_{𝒥_e}`, `I_t`; for the other queries, `F_A`. -/
noncomputable def fixDatum (L : ℕ) (S : Finset E) (t : ZMod blockScale)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) (e : E)
    (η : ∀ j : Option P, CoordSpace blockScale pr h j) : SlotDatum :=
  if e ∈ S then
    ⟨revealedModulus blockScale pr h (Jq e), revealedResidue hcop (Jq e) η, L,
      ((leastPosRep t : ℤ) - 1) * L⟩
  else wholeDatum L

/-- The slot data of the pair inputs of `fixC`. -/
noncomputable def fixSlots (u : E → reservedCut.Half) (L : ℕ) (S : Finset E)
    (t : ZMod blockScale)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (v : Slot) : SlotDatum :=
  slotDatum u (fun e => fixDatum hcop L S t Jq e (ω e)) (wholeDatum L) v

omit [Fintype E] [DecidableEq J₀] in
/-- **The revealed input of `fixC` is the paper's input** (`lem:twointerval`(ii),
`revealedSlot_wrapInputCRT`), at every depth vector. -/
theorem revealedSlot_wrapInputCRT_eq_paperForm (L : ℕ) (A : Finset ℤ) (S : Finset E)
    (t : ZMod blockScale)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) (e : E)
    (η : ∀ j : Option P, CoordSpace blockScale pr h j) :
    revealedSlot Jq (wrapInputCRT blk hcop L A S t) e η =
      paperForm (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A
        (fixDatum hcop L S t Jq e η) := by
  funext y
  rw [revealedSlot_wrapInputCRT]
  unfold fixDatum
  split_ifs
  · unfold paperForm
    rw [blockInterval_eq_Icc]
  · rw [unchangedInput_eq_paperForm]

/-- **The first bound of `hfirstL`, `hfirstR` (`fixC`) from the revealed-input chain**, at every
depth vector (`lem:bracket-energy` first bound with the structured slot data of
`lem:envelope-energy` at fixed intervals). With `Qb = wrapInc D L`, `u = D.S.Q.u`, `t = 0` it
bounds the energy of `hfirstL`; with `u = D.S.Q.w`, `t = 1`, that of `hfirstR`. -/
theorem fix_first_le_chain (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    {Yf : ℕ → Finset ℤ → ℝ} {a' θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (hcex : IsLeastCounterexample Yf a' θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1)
    (ha : 0 ≤ a') (hC0 : 0 ≤ C0) (hL : 2 ≤ L) (hY0 : Yf L ∅ ≤ 0)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0)
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (f g : BlockAtom Bk J L → Bool)
    {qE cE : ℕ} (hDE : ∏ b ∈ (termSet f g), crtModuli m₀ blk p L b = qE * cE) (hqE : Squarefree qE)
    (hcE : IsSquare cE) (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl) (hcopE : qE.Coprime cE)
    (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    (S : Finset E) (t : ZMod blockScale)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (u : E → reservedCut.Half)
    (hD0 : ∀ v, 1 ≤ (fixSlots hcop u L S t Jq ω v).1)
    (hD0M : ∀ v, (fixSlots hcop u L S t Jq ω v).1 ∣ M0)
    (hcop0 : ∀ v k, ((fixSlots hcop u L S t Jq ω v).1).Coprime (crtModuli m₀ blk p L k))
    (hM : ∀ v, (fixSlots hcop u L S t Jq ω v).2.2.1 = blockScale * L ∨
      (fixSlots hcop u L S t Jq ω v).2.2.1 = L)
    (changed : Slot → Prop) [DecidablePred changed]
    (hchg : ∀ v, changed v → ¬((fixSlots hcop u L S t Jq ω v).1 *
      ∏ j ∈ (termSet f g), crtModuli m₀ blk p L j = 1 ∧
      (fixSlots hcop u L S t Jq ω v).2.2.1 = blockScale * L))
    (Q' : Slot → ℝ)
    (hun : ∀ v, ¬changed v → ∀ x, referenceEnergy
      (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
      (revealedModel (crtModuli m₀ blk p L) (termSet f g) A
        (fun v => (fixSlots hcop u L S t Jq ω v).1)
        (fun v => (fixSlots hcop u L S t Jq ω v).2.2.1)
        (fun v => (fixSlots hcop u L S t Jq ω v).2.2.2)
        (fun v => (fixSlots hcop u L S t Jq ω v).2.1) Q' v x) ≤ Yf L A)
    {Cdc σ : ℝ}
    (hrest : ∀ v, changed v → ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll (crtModuli m₀ blk p L) (termSet f g)
        (fixSlots hcop u L S t Jq ω v).1 (fixSlots hcop u L S t Jq ω v).2.2.1 : ℕ) : ℤ) →
      referenceEnergy (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
          (child (crtModuli m₀ blk p L) (termSet f g) (Q' v) B
            (blockScale * stepEll (crtModuli m₀ blk p L)
            (termSet f g) (fixSlots hcop u L S t Jq ω v).1
            (fixSlots hcop u L S t Jq ω v).2.2.1)) ≤
        Yf (stepEll (crtModuli m₀ blk p L) (termSet f g) (fixSlots hcop u L S t Jq ω v).1
          (fixSlots hcop u L S t Jq ω v).2.2.1) B)
    (hdc : |structuredEnergy
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
      MixedLpBound (variationLaw _ hb) (72 / θ) 1) :
    |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise hpair) L
        (termLaw D L Qb f g)))
        (pairInputs u u (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
          (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
          (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
      (∏ b : {b // b ∈ (termSet f g)}, ∑ x : Slot → BlockLabel m₀ blk p L b.1,
        |lawDensity (termLaw D L Qb f g b.1) x|) *
        ((1 + scaleU blockScale M0 Qcl stageTau L) *
          mainPrice (paperPrice (crtModuli m₀ blk p L) (termSet f g)
              (fun v => (fixSlots hcop u L S t Jq ω v).1)
              (fun v => (fixSlots hcop u L S t Jq ω v).2.2.1) L)
            (paperMeanDensity (FiniteLaw.uniform Unit) A
              (fun v => (fixSlots hcop u L S t Jq ω v).1)
              (fun v => (fixSlots hcop u L S t Jq ω v).2.2.1)
              (fun _ v => (fixSlots hcop u L S t Jq ω v).2.2.2)
              (fun _ v => (fixSlots hcop u L S t Jq ω v).2.1))
            changed a' θ (density (blockScale * L) A) * Yf L A +
          Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A) :=
  data_block_energy_le_structured D hpair hcex hθ hθ2 ha hC0 hL hY0 hsc hM0
    (termLaw D L Qb f g) (termSet f g)
    (termLaw_off D L _ f g) hDE hqE hcE hcE0 hcQ hcopE hqN u
    (revealedSlot Jq (wrapInputCRT blk hcop L A S t)) ω (paperCutoff (blockScale * L))
    (fun e => fixDatum hcop L S t Jq e (ω e))
    (fun e => revealedSlot_wrapInputCRT_eq_paperForm hcop L A S t Jq e (ω e)) hD0 hD0M hcop0 hM
    changed hchg Q' hun hrest hdc hatom

end Sarkozy.BracketEnergy
