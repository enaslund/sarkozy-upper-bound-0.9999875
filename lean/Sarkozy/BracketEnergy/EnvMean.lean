module

public import Sarkozy.BracketEnergy.EnvPrice
public import Sarkozy.BracketEnergy.PriceMatch

@[expose] public section

/-!
# The first bound of `lem:bracket-energy` for `envC`, averaged over the residues

**`env_first_mean_le`** (`lem:bracket-energy`, first bound, with the structured slot data of
`lem:envelope-energy`, at `ϑ`; `prop:record:density-structured`, `lem:record:density-dc`,
`lem:twointerval`(ii), `def:record:structured-energy`). Fix a depth vector `𝒥` that reveals every
interval and a valid term `(f, g)` of the bracket expansion (`g ⊥ f`) whose selected moduli
`D_{f∪g}` are coprime to the revealed conductors `D_{𝒥_e}`. Then, over the uniform index `ω`,

`E_ω |E_{f,g}(𝒥, ω)| ≤ (1 + u_L) Π_𝒥 Y ∏_{f} u_𝔟 ∏_{g} u'_𝔟 + ∏_{f∪g} ‖Λ_𝔟‖ C_dc L^{-σ} α`,

with `Π_𝒥 = ∏_e (K sq(D_{𝒥_e}))^{2a/72}` the conductor price of `lem:hyb:moment`. The inputs are
the chain's per-term inputs at every index `ω` (`hrest`, `hdc`), the modulus conditions on
`D_{f∪g}`, the slot conditions (`hD0`, `hD0M`, `hcop0`, `hM`, `hchg`; all slots changed, which
needs `D_{f∪g} ≠ 1`), the moments `hatom` of the selected laws, and the prices
`‖Q_𝔟‖ sq(D_𝔟)^a ≤ u_𝔟`, `‖Ñ_{0,𝔟} − μ_𝔟‖ sq(D_𝔟)^a ≤ u'_𝔟` (`PriceMatch`, from
`sq(D_𝔟)^a ≤ q_𝔟^{2a}`).

The proof: the chain at each `ω` (`env_first_le_chain`) with the main price evaluated
(`envMainPrice_eq`: `sq(D_E)^a Π_𝒥 ∏_e (ᾱ_e/α)^{2θ/72}`), the mean of the local-density factor
(`env_localDensity_mean_le`, Jensen), and the prices (`termPrice_le`).

So `hfirstL`/`hfirstR` of `EnvelopeBracketInputs` hold at such `(𝒥, f, g)` with `z = u_L` and
remainders whose index average is at most `∏ ‖Λ‖ C_dc L^{-σ} α`.
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

/-- **The first bound of `hfirst` for `envC`, averaged over the residues** (see the module
docstring). -/
theorem env_first_mean_le (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    {Yf : ℕ → Finset ℤ → ℝ} {a' θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (hcex : IsLeastCounterexample Yf a' θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1)
    (ha : 0 ≤ a') (hC0 : 0 ≤ C0) (hL : 2 ≤ L) (hY0 : Yf L ∅ ≤ 0)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0)
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (f g : BlockAtom Bk J L → Bool)
    (hg : g ∈ validChoices f)
    {qE cE : ℕ} (hDE : ∏ b ∈ (termSet f g), crtModuli m₀ blk p L b = qE * cE) (hqE : Squarefree qE)
    (hcE : IsSquare cE) (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl) (hcopE : qE.Coprime cE)
    (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (hJ : ∀ e, (Jq e none : ℕ) ≠ 0)
    (hcopJ : ∀ e, (revealedModulus blockScale pr h (Jq e)).Coprime
      (∏ j ∈ termSet f g, crtModuli m₀ blk p L j))
    (u : E → reservedCut.Half) (hu : Injective u)
    (hD0 : ∀ ω v, 1 ≤ (envSlots hcop u L Jq ω v).1)
    (hD0M : ∀ ω v, (envSlots hcop u L Jq ω v).1 ∣ M0)
    (hcop0 : ∀ ω v k, ((envSlots hcop u L Jq ω v).1).Coprime (crtModuli m₀ blk p L k))
    (hM : ∀ ω v, (envSlots hcop u L Jq ω v).2.2.1 = blockScale * L ∨
      (envSlots hcop u L Jq ω v).2.2.1 = L)
    (hchg : ∀ ω v, ¬((envSlots hcop u L Jq ω v).1 *
      ∏ j ∈ (termSet f g), crtModuli m₀ blk p L j = 1 ∧
      (envSlots hcop u L Jq ω v).2.2.1 = blockScale * L))
    (Q' : Slot → ℝ)
    {Cdc σ : ℝ}
    (hrest : ∀ ω v, True → ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll (crtModuli m₀ blk p L) (termSet f g)
        (envSlots hcop u L Jq ω v).1 (envSlots hcop u L Jq ω v).2.2.1 : ℕ) : ℤ) →
      referenceEnergy (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
          (child (crtModuli m₀ blk p L) (termSet f g) (Q' v) B
            (blockScale * stepEll (crtModuli m₀ blk p L)
            (termSet f g) (envSlots hcop u L Jq ω v).1
            (envSlots hcop u L Jq ω v).2.2.1)) ≤
        Yf (stepEll (crtModuli m₀ blk p L) (termSet f g) (envSlots hcop u L Jq ω v).1
          (envSlots hcop u L Jq ω v).2.2.1) B)
    (hdc : ∀ ω, |structuredEnergy
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
      MixedLpBound (variationLaw _ hb) (72 / θ) 1)
    (uQ : BlockAtom Bk J L → ℝ)
    (hQ : ∀ b, (∑ z, |lawDensity (Qb b) z|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a' ≤ uQ b)
    (hR : ∀ b, (∑ z, |lawDensity (recLaw D L b) z|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a' ≤ D.GB.uprice L b) :
    (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect (fun ω =>
      |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise hpair) L
        (termLaw D L Qb f g)))
        (pairInputs u u (revealedInputCRT blk hcop D L A Jq)
          (revealedInputCRT blk hcop D L A Jq)
          (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)|) ≤
      (1 + scaleU blockScale M0 Qcl stageTau L) *
          (conductorPrice pr h (2 * a' / 72) Jq * Yf L A *
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
  set Pc := conductorPrice pr h (2 * a' / 72) Jq
  set uL := scaleU blockScale M0 Qcl stageTau L
  set C := Cdc * (L : ℝ) ^ (-σ) * α
  set Dens : (E → ∀ j : Option P, CoordSpace blockScale pr h j) → ℝ := fun ω =>
    ∏ e, (queryLocalDensity hcop L A (Jq e) (ω e) / α) ^ (2 * θ / 72)
  have hR0 : 0 ≤ R := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hPc0 : 0 ≤ Pc := conductorPrice_nonneg pr h _ Jq
  have hu0 : 0 ≤ uL := scaleU_nonneg _ _ _ _ _
  have hpt : ∀ ω, |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise hpair) L
        (termLaw D L Qb f g)))
        (pairInputs u u (revealedInputCRT blk hcop D L A Jq)
          (revealedInputCRT blk hcop D L A Jq)
          (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
      (NΛ * (1 + uL) * R * Pc * Yf L A) * Dens ω + NΛ * C := by
    intro ω
    have h := env_first_le_chain hcop D hpair hcex hθ hθ2 ha hC0 hL hY0 hsc hM0 Qb f g hDE hqE
      hcE hcE0 hcQ hcopE hqN Jq hJ ω u (hD0 ω) (hD0M ω) (hcop0 ω) (hM ω) (fun _ => True)
      (fun v _ => hchg ω v) Q' (fun v hv _ => absurd trivial hv) (hrest ω) (hdc ω)
      hatom
    rw [envMainPrice_eq hcop (crtModuli m₀ blk p L) (by omega) u hu (termSet f g) A hA hα a' θ
      Jq ω hcopJ] at h
    refine h.trans (le_of_eq ?_)
    ring
  have hmean : (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
      Dens ≤ 1 :=
    env_localDensity_mean_le hcop (by omega) A hA hα (by positivity) (by linarith) Jq
  have hprice := termPrice_le D L hpair Qb uQ f g hg hQ hR
  have hK : 0 ≤ NΛ * (1 + uL) * R * Pc * Yf L A := by positivity
  calc (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect (fun ω =>
        |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise hpair) L
          (termLaw D L Qb f g)))
          (pairInputs u u (revealedInputCRT blk hcop D L A Jq)
            (revealedInputCRT blk hcop D L A Jq)
            (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)|)
      ≤ (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect (fun ω =>
          (NΛ * (1 + uL) * R * Pc * Yf L A) * Dens ω + NΛ * C) :=
        FiniteLaw.expect_mono _ hpt
    _ = (NΛ * (1 + uL) * R * Pc * Yf L A) *
          (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect Dens +
          NΛ * C := by
        rw [FiniteLaw.expect_add, FiniteLaw.expect_const_mul, FiniteLaw.expect_const]
    _ ≤ (NΛ * (1 + uL) * R * Pc * Yf L A) * 1 + NΛ * C := by
        have := mul_le_mul_of_nonneg_left hmean hK
        linarith
    _ ≤ (1 + uL) * (Pc * Yf L A *
          ((∏ b, if f b then uQ b else 1) * ∏ b, (if g b then D.GB.uprice L b else 1))) +
          NΛ * C := by
        have h1 : 0 ≤ (1 + uL) * Pc * Yf L A := by positivity
        have := mul_le_mul_of_nonneg_left hprice h1
        nlinarith

/-- **`env_first_mean_le` with the slot and conductor conditions discharged**: they hold when the
index modulus `M₀ = ∏_p p^{h_p}` divides the chain's `M₀` and is coprime to the atom moduli, and
the selected modulus `D_{f∪g}` is not `1`. -/
theorem env_first_mean_le_of_moduli (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    {Yf : ℕ → Finset ℤ → ℝ} {a' θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (hcex : IsLeastCounterexample Yf a' θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1)
    (ha : 0 ≤ a') (hC0 : 0 ≤ C0) (hL : 2 ≤ L) (hY0 : Yf L ∅ ≤ 0)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0)
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (f g : BlockAtom Bk J L → Bool)
    (hg : g ∈ validChoices f)
    {qE cE : ℕ} (hDE : ∏ b ∈ (termSet f g), crtModuli m₀ blk p L b = qE * cE) (hqE : Squarefree qE)
    (hcE : IsSquare cE) (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl) (hcopE : qE.Coprime cE)
    (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (hJ : ∀ e, (Jq e none : ℕ) ≠ 0)
    (u : E → reservedCut.Half) (hu : Injective u)
    (hMod : modulus pr h ∣ M0)
    (hcopM : ∀ k, (modulus pr h).Coprime (crtModuli m₀ blk p L k))
    (hne : ∏ j ∈ termSet f g, crtModuli m₀ blk p L j ≠ 1)
    (Q' : Slot → ℝ)
    {Cdc σ : ℝ}
    (hrest : ∀ ω v, True → ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll (crtModuli m₀ blk p L) (termSet f g)
        (envSlots hcop u L Jq ω v).1 (envSlots hcop u L Jq ω v).2.2.1 : ℕ) : ℤ) →
      referenceEnergy (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
          (child (crtModuli m₀ blk p L) (termSet f g) (Q' v) B
            (blockScale * stepEll (crtModuli m₀ blk p L)
            (termSet f g) (envSlots hcop u L Jq ω v).1
            (envSlots hcop u L Jq ω v).2.2.1)) ≤
        Yf (stepEll (crtModuli m₀ blk p L) (termSet f g) (envSlots hcop u L Jq ω v).1
          (envSlots hcop u L Jq ω v).2.2.1) B)
    (hdc : ∀ ω, |structuredEnergy
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
      MixedLpBound (variationLaw _ hb) (72 / θ) 1)
    (uQ : BlockAtom Bk J L → ℝ)
    (hQ : ∀ b, (∑ z, |lawDensity (Qb b) z|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a' ≤ uQ b)
    (hR : ∀ b, (∑ z, |lawDensity (recLaw D L b) z|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a' ≤ D.GB.uprice L b) :
    (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect (fun ω =>
      |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise hpair) L
        (termLaw D L Qb f g)))
        (pairInputs u u (revealedInputCRT blk hcop D L A Jq)
          (revealedInputCRT blk hcop D L A Jq)
          (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)|) ≤
      (1 + scaleU blockScale M0 Qcl stageTau L) *
          (conductorPrice pr h (2 * a' / 72) Jq * Yf L A *
            ((∏ b, if f b then uQ b else 1) * ∏ b, (if g b then D.GB.uprice L b else 1))) +
        (∏ b : {b // b ∈ termSet f g}, ∑ x : Slot → BlockLabel m₀ blk p L b.1,
          |lawDensity (termLaw D L Qb f g b.1) x|) *
          (Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  have hdat : ∀ ω v, envSlots hcop u L Jq ω v =
      optDatum (fun e => envDatum hcop L Jq e (ω e)) (wholeDatum L) (slotQuery u v) :=
    fun ω v => slotDatum_eq_optDatum u _ _ v
  have hJd : ∀ e, revealedModulus blockScale pr h (Jq e) ∣ modulus pr h :=
    fun e => revealedModulus_dvd (Jq e)
  have hmpos : 0 < modulus pr h := Nat.pos_of_ne_zero (NeZero.ne _)
  have hKL : L ≠ blockScale * L := by
    have : 2 ≤ blockScale := by norm_num [blockScale]
    nlinarith
  have hcopJ : ∀ e, (revealedModulus blockScale pr h (Jq e)).Coprime
      (∏ j ∈ termSet f g, crtModuli m₀ blk p L j) :=
    fun e => Nat.Coprime.prod_right fun k _ => Nat.Coprime.coprime_dvd_left (hJd e) (hcopM k)
  refine env_first_mean_le hcop D hpair hcex hθ hθ2 ha hC0 hL hY0 hsc hM0 Qb f g hg hDE hqE hcE
    hcE0 hcQ hcopE hqN Jq hJ hcopJ u hu ?_ ?_ ?_ ?_ ?_ Q' hrest hdc hatom uQ hQ hR
  · intro ω v
    rw [hdat]
    rcases slotQuery u v with _ | e
    · exact le_refl 1
    · exact Nat.pos_of_dvd_of_pos (hJd e) hmpos
  · intro ω v
    rw [hdat]
    rcases slotQuery u v with _ | e
    · exact one_dvd _
    · exact dvd_trans (hJd e) hMod
  · intro ω v k
    rw [hdat]
    rcases slotQuery u v with _ | e
    · exact Nat.coprime_one_left _
    · exact Nat.Coprime.coprime_dvd_left (hJd e) (hcopM k)
  · intro ω v
    rw [hdat]
    rcases slotQuery u v with _ | e
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro ω v
    rw [hdat]
    rcases slotQuery u v with _ | e
    · intro h1
      apply hne
      have := h1.1
      change 1 * ∏ j ∈ termSet f g, crtModuli m₀ blk p L j = 1 at this
      rwa [one_mul] at this
    · intro h1
      exact hKL h1.2

omit [DecidableEq J₀] [DecidableEq P] in
/-- The outside datum has the density of `A`. -/
theorem datumDensity_wholeDatum {L : ℕ} (A : Finset ℤ) (hA : A ⊆ Icc 1 ((blockScale * L : ℕ) : ℤ)) :
    datumDensity A (wholeDatum L) = density (blockScale * L) A := by
  unfold datumDensity wholeDatum
  have hfilter : ((A ∩ Icc (0 + 1) (0 + ((blockScale * L : ℕ) : ℤ))).filter
      fun x : ℤ => (x : ZMod 1) = 0) = A := by
    rw [filter_true_of_mem (fun x _ => Subsingleton.elim _ _), zero_add, zero_add]
    exact inter_eq_left.mpr hA
  simp only at hfilter ⊢
  rw [hfilter]
  unfold density
  push_cast
  ring

omit [DecidableEq J₀] [DecidableEq P] [DecidableEq E] in
/-- An outside slot carries the datum of `F_A`. -/
theorem envSlots_of_none {L : ℕ} (u : E → reservedCut.Half)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (v : Slot)
    (hq : slotQuery u v = none) : envSlots hcop u L Jq ω v = wholeDatum L := by
  unfold envSlots
  rw [slotDatum_eq_optDatum, hq]
  rfl

omit [DecidableEq J₀] [DecidableEq P] [DecidableEq E] in
/-- A query slot has an interval of length `L`. -/
theorem envSlots_length_of_some {L : ℕ} (u : E → reservedCut.Half)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (v : Slot) (e : E)
    (hq : slotQuery u v = some e) : (envSlots hcop u L Jq ω v).2.2.1 = L := by
  unfold envSlots
  rw [slotDatum_eq_optDatum, hq]
  rfl

omit [DecidableEq J₀] [DecidableEq P] [DecidableEq E] in
/-- **The main price does not see the outside slots**: for the data of `envC`, declaring the
outside slots (`F_A`, density `α`) unchanged does not change the main price. -/
theorem mainPrice_envSlots_congr {Jt : Type} [Fintype Jt] [DecidableEq Jt] (m : Jt → ℕ)
    [∀ j, NeZero (m j)] {L : ℕ} (u : E → reservedCut.Half) (Es : Finset Jt) (A : Finset ℤ)
    (hA : A ⊆ Icc 1 ((blockScale * L : ℕ) : ℤ)) (hα : 0 < density (blockScale * L) A)
    (a θ : ℝ) (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (changed : Slot → Prop)
    [DecidablePred changed] (hch : ∀ v, ¬changed v → slotQuery u v = none) :
    mainPrice (paperPrice m Es (fun v => (envSlots hcop u L Jq ω v).1)
        (fun v => (envSlots hcop u L Jq ω v).2.2.1) L)
      (paperMeanDensity (FiniteLaw.uniform Unit) A (fun v => (envSlots hcop u L Jq ω v).1)
        (fun v => (envSlots hcop u L Jq ω v).2.2.1)
        (fun _ v => (envSlots hcop u L Jq ω v).2.2.2)
        (fun _ v => (envSlots hcop u L Jq ω v).2.1)) changed a θ (density (blockScale * L) A) =
    mainPrice (paperPrice m Es (fun v => (envSlots hcop u L Jq ω v).1)
        (fun v => (envSlots hcop u L Jq ω v).2.2.1) L)
      (paperMeanDensity (FiniteLaw.uniform Unit) A (fun v => (envSlots hcop u L Jq ω v).1)
        (fun v => (envSlots hcop u L Jq ω v).2.2.1)
        (fun _ v => (envSlots hcop u L Jq ω v).2.2.2)
        (fun _ v => (envSlots hcop u L Jq ω v).2.1)) (fun _ => True) a θ
        (density (blockScale * L) A) := by
  unfold mainPrice
  congr 1
  rw [prod_filter, prod_filter]
  apply prod_congr rfl
  intro v _
  by_cases hv : changed v
  · simp only [hv, ↓reduceIte]
  · have hq := hch v hv
    have hd : paperMeanDensity (FiniteLaw.uniform Unit) A (fun v => (envSlots hcop u L Jq ω v).1)
        (fun v => (envSlots hcop u L Jq ω v).2.2.1)
        (fun _ v => (envSlots hcop u L Jq ω v).2.2.2)
        (fun _ v => (envSlots hcop u L Jq ω v).2.1) v = density (blockScale * L) A := by
      have h1 : paperMeanDensity (FiniteLaw.uniform Unit) A
          (fun v => (envSlots hcop u L Jq ω v).1) (fun v => (envSlots hcop u L Jq ω v).2.2.1)
          (fun _ v => (envSlots hcop u L Jq ω v).2.2.2)
          (fun _ v => (envSlots hcop u L Jq ω v).2.1) v =
          datumDensity A (envSlots hcop u L Jq ω v) := by
        unfold paperMeanDensity
        rw [FiniteLaw.expect_const]
        rfl
      rw [h1, envSlots_of_none hcop u Jq ω v hq, datumDensity_wholeDatum A hA]
    simp only [hv, ↓reduceIte, hd, div_self hα.ne', Real.one_rpow]

/-- **The first bound with only the query slots changed** (`env_first_mean_le` with the outside
slots unchanged; for the term `f = g = ∅`, the `μ`-part of the envelope energy, whose changed
slots are the `2k ≤ 70` query endpoints). The outside slots need `hun`: the model there has
reference energy at most `Y`. -/
theorem env_first_mean_le_query (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    {Yf : ℕ → Finset ℤ → ℝ} {a' θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (hcex : IsLeastCounterexample Yf a' θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1)
    (ha : 0 ≤ a') (hC0 : 0 ≤ C0) (hL : 2 ≤ L) (hY0 : Yf L ∅ ≤ 0)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0)
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (f g : BlockAtom Bk J L → Bool)
    (hg : g ∈ validChoices f)
    {qE cE : ℕ} (hDE : ∏ b ∈ (termSet f g), crtModuli m₀ blk p L b = qE * cE) (hqE : Squarefree qE)
    (hcE : IsSquare cE) (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl) (hcopE : qE.Coprime cE)
    (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (hJ : ∀ e, (Jq e none : ℕ) ≠ 0)
    (hcopJ : ∀ e, (revealedModulus blockScale pr h (Jq e)).Coprime
      (∏ j ∈ termSet f g, crtModuli m₀ blk p L j))
    (u : E → reservedCut.Half) (hu : Injective u)
    (hD0 : ∀ ω v, 1 ≤ (envSlots hcop u L Jq ω v).1)
    (hD0M : ∀ ω v, (envSlots hcop u L Jq ω v).1 ∣ M0)
    (hcop0 : ∀ ω v k, ((envSlots hcop u L Jq ω v).1).Coprime (crtModuli m₀ blk p L k))
    (hM : ∀ ω v, (envSlots hcop u L Jq ω v).2.2.1 = blockScale * L ∨
      (envSlots hcop u L Jq ω v).2.2.1 = L)
    (Q' : Slot → ℝ)
    (hun : ∀ ω v, slotQuery u v = none → ∀ x, referenceEnergy
      (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
      (revealedModel (crtModuli m₀ blk p L) (termSet f g) A (fun v => (envSlots hcop u L Jq ω v).1)
        (fun v => (envSlots hcop u L Jq ω v).2.2.1)
        (fun v => (envSlots hcop u L Jq ω v).2.2.2)
        (fun v => (envSlots hcop u L Jq ω v).2.1) Q' v x) ≤ Yf L A)
    {Cdc σ : ℝ}
    (hrest : ∀ ω v, slotQuery u v ≠ none → ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll (crtModuli m₀ blk p L) (termSet f g)
        (envSlots hcop u L Jq ω v).1 (envSlots hcop u L Jq ω v).2.2.1 : ℕ) : ℤ) →
      referenceEnergy (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
          (child (crtModuli m₀ blk p L) (termSet f g) (Q' v) B
            (blockScale * stepEll (crtModuli m₀ blk p L)
            (termSet f g) (envSlots hcop u L Jq ω v).1
            (envSlots hcop u L Jq ω v).2.2.1)) ≤
        Yf (stepEll (crtModuli m₀ blk p L) (termSet f g) (envSlots hcop u L Jq ω v).1
          (envSlots hcop u L Jq ω v).2.2.1) B)
    (hdc : ∀ ω, |structuredEnergy
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
      MixedLpBound (variationLaw _ hb) (72 / θ) 1)
    (uQ : BlockAtom Bk J L → ℝ)
    (hQ : ∀ b, (∑ z, |lawDensity (Qb b) z|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a' ≤ uQ b)
    (hR : ∀ b, (∑ z, |lawDensity (recLaw D L b) z|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a' ≤ D.GB.uprice L b) :
    (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect (fun ω =>
      |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise hpair) L
        (termLaw D L Qb f g)))
        (pairInputs u u (revealedInputCRT blk hcop D L A Jq)
          (revealedInputCRT blk hcop D L A Jq)
          (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)|) ≤
      (1 + scaleU blockScale M0 Qcl stageTau L) *
          (conductorPrice pr h (2 * a' / 72) Jq * Yf L A *
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
  set Pc := conductorPrice pr h (2 * a' / 72) Jq
  set uL := scaleU blockScale M0 Qcl stageTau L
  set C := Cdc * (L : ℝ) ^ (-σ) * α
  set Dens : (E → ∀ j : Option P, CoordSpace blockScale pr h j) → ℝ := fun ω =>
    ∏ e, (queryLocalDensity hcop L A (Jq e) (ω e) / α) ^ (2 * θ / 72)
  have hR0 : 0 ≤ R := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hPc0 : 0 ≤ Pc := conductorPrice_nonneg pr h _ Jq
  have hu0 : 0 ≤ uL := scaleU_nonneg _ _ _ _ _
  have hpt : ∀ ω, |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise hpair) L
        (termLaw D L Qb f g)))
        (pairInputs u u (revealedInputCRT blk hcop D L A Jq)
          (revealedInputCRT blk hcop D L A Jq)
          (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
      (NΛ * (1 + uL) * R * Pc * Yf L A) * Dens ω + NΛ * C := by
    intro ω
    have hchg : ∀ v, slotQuery u v ≠ none → ¬((envSlots hcop u L Jq ω v).1 *
        ∏ j ∈ termSet f g, crtModuli m₀ blk p L j = 1 ∧
        (envSlots hcop u L Jq ω v).2.2.1 = blockScale * L) := by
      intro v hv h1
      rcases hq : slotQuery u v with _ | e
      · exact hv hq
      · have hKL : L ≠ blockScale * L := by
          have : 2 ≤ blockScale := by norm_num [blockScale]
          nlinarith
        rw [envSlots_length_of_some hcop u Jq ω v e hq] at h1
        exact hKL h1.2
    have h := env_first_le_chain hcop D hpair hcex hθ hθ2 ha hC0 hL hY0 hsc hM0 Qb f g hDE hqE
      hcE hcE0 hcQ hcopE hqN Jq hJ ω u (hD0 ω) (hD0M ω) (hcop0 ω) (hM ω)
      (fun v => slotQuery u v ≠ none) hchg Q'
      (fun v hv x => hun ω v (not_not.mp hv) x) (hrest ω) (hdc ω) hatom
    rw [mainPrice_envSlots_congr hcop (crtModuli m₀ blk p L) u (termSet f g) A hA hα a' θ Jq ω
      (fun v => slotQuery u v ≠ none) (fun v hv => not_not.mp hv)] at h
    rw [envMainPrice_eq hcop (crtModuli m₀ blk p L) (by omega) u hu (termSet f g) A hA hα a' θ
      Jq ω hcopJ] at h
    refine h.trans (le_of_eq ?_)
    ring
  have hmean : (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
      Dens ≤ 1 :=
    env_localDensity_mean_le hcop (by omega) A hA hα (by positivity) (by linarith) Jq
  have hprice := termPrice_le D L hpair Qb uQ f g hg hQ hR
  have hK : 0 ≤ NΛ * (1 + uL) * R * Pc * Yf L A := by positivity
  calc (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect (fun ω =>
        |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise hpair) L
          (termLaw D L Qb f g)))
          (pairInputs u u (revealedInputCRT blk hcop D L A Jq)
            (revealedInputCRT blk hcop D L A Jq)
            (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)|)
      ≤ (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect (fun ω =>
          (NΛ * (1 + uL) * R * Pc * Yf L A) * Dens ω + NΛ * C) :=
        FiniteLaw.expect_mono _ hpt
    _ = (NΛ * (1 + uL) * R * Pc * Yf L A) *
          (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect Dens +
          NΛ * C := by
        rw [FiniteLaw.expect_add, FiniteLaw.expect_const_mul, FiniteLaw.expect_const]
    _ ≤ (NΛ * (1 + uL) * R * Pc * Yf L A) * 1 + NΛ * C := by
        have := mul_le_mul_of_nonneg_left hmean hK
        linarith
    _ ≤ (1 + uL) * (Pc * Yf L A *
          ((∏ b, if f b then uQ b else 1) * ∏ b, (if g b then D.GB.uprice L b else 1))) +
          NΛ * C := by
        have h1 : 0 ≤ (1 + uL) * Pc * Yf L A := by positivity
        have := mul_le_mul_of_nonneg_left hprice h1
        nlinarith


end Sarkozy.BracketEnergy
