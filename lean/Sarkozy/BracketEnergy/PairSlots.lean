module

public import Sarkozy.BracketEnergy.RevealedChain
public import Sarkozy.BracketEnergy.TwoInterval

@[expose] public section

/-!
# The pair inputs of the envelope energies as structured slot data

The energies of `envC`, `fixC` (and of their bracket reductions `hfirst`) carry the pair inputs
`pairInputs u u φ φ F_A ω ω`: the revealed input of the query `e` at its source `u_e` and at the
reflected source `ι u_e`, and `F_A` at every other slot. When every query input is of the paper's
form `g^{I_e, D_e, s_e}` (`TwoInterval`), these are structured slot data
(`def:record:structured-energy`) with

* `D_{0,v} = D_e`, `s_v = s_e`, `I_v = I_e` at the two slots of `e`;
* `D_{0,v} = 1`, `s_v = 0`, `I_v = [1, N]` elsewhere.

* `slotQuery`, `slotDatum`: the query of a slot and its datum;
* `pairInputs_eq_slotDatum`: the pair inputs are `g^{I_v, D_{0,v}, s_v}` for these data;
* **`abs_pair_energy_le_structured`**: the chain `abs_tensor_energy_le_structured` for the pair
  inputs (the first bound of `lem:bracket-energy` for one energy of `lem:envelope-energy` at a
  fixed index, given its per-term inputs);
* `blockInterval_eq_Icc`, `revealedEnvInput_eq_paperForm`, `revealedSlot_wrapInputCRT_eq`: the
  revealed inputs of `envC` (interval revealed) and of `fixC` are of the paper's form.
-/

open Finset Function
open scoped BigOperators

namespace Sarkozy.BracketEnergy

open Sarkozy.EnvelopeInputs Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic
  Sarkozy.PaperFrame Sarkozy.TheoremC Sarkozy.IndexSupport

/-- A slot datum: the modulus `D₀`, the residue `s mod D₀`, the length `M` and the offset `c` of
the interval `[c + 1, c + M]`. -/
abbrev SlotDatum : Type := Σ D : ℕ, ZMod D × ℕ × ℤ

variable {J : Type} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)]

/-- The paper's input `g^{I, D₀, s}` of a datum, `I = [c + 1, c + M]`. -/
noncomputable def paperForm (Q : ℝ) (A : Finset ℤ) (d : SlotDatum) (y : ResidueSpace m) : ℝ :=
  (input m Q (Icc (d.2.2.2 + 1) (d.2.2.2 + d.2.2.1)) d.1 d.2.1 A y).re

/-- The datum of `F_A`: `D₀ = 1`, `s = 0`, `I = [1, N]`. -/
def wholeDatum (L : ℕ) : SlotDatum := ⟨1, 0, blockScale * L, 0⟩

/-- `F_A` is the paper's input of `wholeDatum`. -/
theorem unchangedInput_eq_paperForm (Q : ℝ) (A : Finset ℤ) (L : ℕ) :
    unchangedInput m Q A L = paperForm m Q A (wholeDatum L) := by
  funext y
  unfold unchangedInput paperForm wholeDatum
  simp only [zero_add]

variable {E : Type} [Fintype E] [DecidableEq E]

/-- The query of a slot: `e` at `u_e` and at `ι u_e`, none elsewhere. -/
noncomputable def slotQuery (u : E → reservedCut.Half) (v : Slot) : Option E :=
  if hs : v ∈ reservedCut.half then
    (if h : ∃ e, u e = ⟨v, hs⟩ then some h.choose else none)
  else
    (if h : ∃ e, u e = ⟨reservedCut.flip v, (reservedCut.crosses v).mpr hs⟩ then some h.choose
      else none)

/-- The datum of a slot. -/
noncomputable def slotDatum (u : E → reservedCut.Half) (qdat : E → SlotDatum) (fdat : SlotDatum)
    (v : Slot) : SlotDatum :=
  match slotQuery u v with
  | some e => qdat e
  | none => fdat

omit [DecidableEq E] in
/-- **The pair inputs are structured slot data**: if every query input is `g^{I_e, D_e, s_e}`
and the other input is the paper's input of `fdat`, then the pair inputs are the paper's inputs
of `slotDatum`. -/
theorem pairInputs_eq_slotDatum {Ωi : Type} (u : E → reservedCut.Half)
    (φ : E → Ωi → ResidueSpace m → ℝ) (F : ResidueSpace m → ℝ) (ω : E → Ωi) (Q : ℝ)
    (A : Finset ℤ) (qdat : E → SlotDatum) (fdat : SlotDatum)
    (hφ : ∀ e, φ e (ω e) = paperForm m Q A (qdat e)) (hF : F = paperForm m Q A fdat) :
    pairInputs u u φ φ F ω ω = fun v => paperForm m Q A (slotDatum u qdat fdat v) := by
  funext v
  unfold pairInputs halfInput slotDatum slotQuery
  by_cases hs : v ∈ reservedCut.half
  · simp only [hs, ↓reduceDIte]
    by_cases h : ∃ e, u e = ⟨v, hs⟩
    · simp only [h, ↓reduceDIte]
      exact hφ _
    · simp only [h, ↓reduceDIte]
      exact hF
  · simp only [hs, ↓reduceDIte]
    by_cases h : ∃ e, u e = ⟨reservedCut.flip v, (reservedCut.crosses v).mpr hs⟩
    · simp only [h, ↓reduceDIte]
      exact hφ _
    · simp only [h, ↓reduceDIte]
      exact hF

omit [DecidableEq E] in
/-- **The first bound for a pair-input energy** (`lem:bracket-energy` first bound for one energy
of `lem:envelope-energy` at a fixed index, `prop:record:density-structured` with structured slot
data at `ϑ`): `abs_tensor_energy_le_structured` with the slot data of the pair inputs. -/
theorem abs_pair_energy_le_structured (hpair : Pairwise fun i j => (m i).Coprime (m j))
    {Yf : ℕ → Finset ℤ → ℝ} {a θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hcex : IsLeastCounterexample Yf a θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1) (ha : 0 ≤ a)
    (hC0 : 0 ≤ C0) (hL : 2 ≤ L) (hY0 : Yf L ∅ ≤ 0)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0)
    (μb : ∀ b, FiniteLaw (Slot → ZMod (m b)))
    (hμb : ∀ b, SlotReflectionPositive (signedIntegral (μb b).weight))
    (hR3 : SquareAffineInvariant m μb)
    (Λ : ∀ b, ((Slot → ZMod (m b)) → ℝ) →ₗ[ℝ] ℝ) (Es : Finset J)
    (hE : ∀ b ∉ Es, Λ b = signedIntegral (μb b).weight)
    {qE cE : ℕ} (hDE : ∏ j ∈ Es, m j = qE * cE) (hqE : Squarefree qE) (hcE : IsSquare cE)
    (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl) (hcopE : qE.Coprime cE)
    (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    {Ωi : Type} (u : E → reservedCut.Half) (φ : E → Ωi → ResidueSpace m → ℝ) (ω : E → Ωi)
    (Q : ℝ) (qdat : E → SlotDatum) (hφ : ∀ e, φ e (ω e) = paperForm m Q A (qdat e))
    (hD0 : ∀ v, 1 ≤ (slotDatum u qdat (wholeDatum L) v).1)
    (hD0M : ∀ v, (slotDatum u qdat (wholeDatum L) v).1 ∣ M0)
    (hcop0 : ∀ v k, ((slotDatum u qdat (wholeDatum L) v).1).Coprime (m k))
    (hM : ∀ v, (slotDatum u qdat (wholeDatum L) v).2.2.1 = blockScale * L ∨
      (slotDatum u qdat (wholeDatum L) v).2.2.1 = L)
    (changed : Slot → Prop) [DecidablePred changed]
    (hchg : ∀ v, changed v → ¬((slotDatum u qdat (wholeDatum L) v).1 * ∏ j ∈ Es, m j = 1 ∧
      (slotDatum u qdat (wholeDatum L) v).2.2.1 = blockScale * L))
    (Q' : Slot → ℝ)
    (hun : ∀ v, ¬changed v → ∀ x, referenceEnergy (FiniteLaw.tensor μb)
      (revealedModel m Es A (fun v => (slotDatum u qdat (wholeDatum L) v).1)
        (fun v => (slotDatum u qdat (wholeDatum L) v).2.2.1)
        (fun v => (slotDatum u qdat (wholeDatum L) v).2.2.2)
        (fun v => (slotDatum u qdat (wholeDatum L) v).2.1) Q' v x) ≤ Yf L A)
    {Cdc σ : ℝ}
    (hrest : ∀ v, changed v → ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll m Es (slotDatum u qdat (wholeDatum L) v).1
        (slotDatum u qdat (wholeDatum L) v).2.2.1 : ℕ) : ℤ) →
      referenceEnergy (FiniteLaw.tensor μb)
          (child m Es (Q' v) B (blockScale * stepEll m Es (slotDatum u qdat (wholeDatum L) v).1
            (slotDatum u qdat (wholeDatum L) v).2.2.1)) ≤
        Yf (stepEll m Es (slotDatum u qdat (wholeDatum L) v).1
          (slotDatum u qdat (wholeDatum L) v).2.2.1) B)
    (hdc : |structuredEnergy (FiniteLaw.tensor μb) (FiniteLaw.uniform Unit)
          (liftWeight Es (selectedWeight Es Λ) (uniformRest (Xa := fun b => ZMod (m b)) Es))
          (paperInputs m Es Q A (fun v => (slotDatum u qdat (wholeDatum L) v).1)
            (fun v => (slotDatum u qdat (wholeDatum L) v).2.2.1)
            (fun _ v => (slotDatum u qdat (wholeDatum L) v).2.2.2)
            (fun _ v => (slotDatum u qdat (wholeDatum L) v).2.1)) -
        structuredEnergy (FiniteLaw.tensor μb) (FiniteLaw.uniform Unit)
          (liftWeight Es (selectedWeight Es Λ) (uniformRest (Xa := fun b => ZMod (m b)) Es))
          (fun _ => revealedModel m Es A (fun v => (slotDatum u qdat (wholeDatum L) v).1)
            (fun v => (slotDatum u qdat (wholeDatum L) v).2.2.1)
            (fun v => (slotDatum u qdat (wholeDatum L) v).2.2.2)
            (fun v => (slotDatum u qdat (wholeDatum L) v).2.1) Q')| ≤
      Cdc * totalVariation (selectedWeight Es Λ) * (L : ℝ) ^ (-σ) * density (blockScale * L) A)
    (hatom : ∀ (b : {b // b ∈ Es}) (hb : 0 < totalVariation (lawDensity (Λ b))),
      MixedLpBound (variationLaw _ hb) (72 / θ) 1) :
    |multilinearIntegral (tensorLaw Λ) (pairInputs u u φ φ (unchangedInput m Q A L) ω ω)| ≤
      (∏ b : {b // b ∈ Es}, ∑ y : Slot → ZMod (m b), |lawDensity (Λ b) y|) *
        ((1 + scaleU blockScale M0 Qcl stageTau L) *
          mainPrice (paperPrice m Es (fun v => (slotDatum u qdat (wholeDatum L) v).1)
              (fun v => (slotDatum u qdat (wholeDatum L) v).2.2.1) L)
            (paperMeanDensity (FiniteLaw.uniform Unit) A
              (fun v => (slotDatum u qdat (wholeDatum L) v).1)
              (fun v => (slotDatum u qdat (wholeDatum L) v).2.2.1)
              (fun _ v => (slotDatum u qdat (wholeDatum L) v).2.2.2)
              (fun _ v => (slotDatum u qdat (wholeDatum L) v).2.1))
            changed a θ (density (blockScale * L) A) * Yf L A +
          Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  rw [pairInputs_eq_slotDatum m u φ (unchangedInput m Q A L) ω Q A qdat (wholeDatum L) hφ
    (unchangedInput_eq_paperForm m Q A L)]
  exact abs_tensor_energy_le_structured m hpair hcex hθ hθ2 ha hC0 hL hY0 hsc hM0 μb hμb hR3 Λ Es
    hE hDE hqE hcE hcE0 hcQ hcopE hqN _ hD0 hD0M hcop0 _ hM _ _ changed hchg Q Q' hun hrest hdc
    hatom

/-- `I_b = [(b − 1)L + 1, bL]` as an interval `[c + 1, c + L]`. -/
theorem blockInterval_eq_Icc {K : ℕ} (L : ℕ) (b : ZMod K) :
    blockInterval K L b =
      Icc (((leastPosRep b : ℤ) - 1) * L + 1) (((leastPosRep b : ℤ) - 1) * L + L) := by
  unfold blockInterval
  ext x
  simp only [mem_Ioc, mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · omega
    · linarith
  · rintro ⟨h1, h2⟩
    constructor
    · omega
    · linarith

end Sarkozy.BracketEnergy
