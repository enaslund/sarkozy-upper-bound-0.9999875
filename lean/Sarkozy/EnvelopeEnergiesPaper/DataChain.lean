module

public import Sarkozy.EnvelopeEnergiesPaper.BlockChain
public import Sarkozy.TheoremCBlock.Main
public import Sarkozy.CancellationSteps.Paper

@[expose] public section

/-!
# The block density chain for comparison data, and for the paper's moduli

`abs_block_energy_le_unchanged` with its (R2), (R3) hypotheses read off K0's
`TheoremCBlock.Reference` of the data (`rp₀`, `rpp`, `inv₀`, `invp`):

* `data_block_energy_le_unchanged`: for any block-atom comparison data with pairwise coprime joined
  moduli;
* `paper_pairwise`: for the paper's moduli (`paperM0`, `paperTail`) the coprimality hypothesis
  holds at every scale (`CancellationSteps.paper_hcopE`), so for the paper's data, with any block
  assignment, `data_block_energy_le_unchanged` applies with `hpair := paper_pairwise L`.

What remains per term: the restoration `hrest` and the density-dc replacement `hdc` in cyclic
coordinates (`lem:record:density-dc`, `lem:record:fibre-scale`), the modulus conditions on `D_E`
(`def:record:structured-energy`, `lem:scale-conditions`), and the moment inputs `hatom` of the
selected block laws (`lem:density:coupled`).
-/

open Finset Function
open scoped BigOperators

namespace Sarkozy.EnvelopeEnergiesPaper

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.PaperFrame Sarkozy.BlockFrame
  Sarkozy.Structured Sarkozy.TheoremC

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

omit [DecidableEq P] in
/-- **The density chain on the block atoms for comparison data** (`prop:record:density-structured`
at `θ = ϑ`, (E1)'s first bound): `abs_block_energy_le_unchanged` with (R2) and (R3) from the data's
reference. -/
theorem data_block_energy_le_unchanged (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    {Yf : ℕ → Finset ℤ → ℝ} {a' θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (hcex : IsLeastCounterexample Yf a' θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1)
    (ha : 0 ≤ a') (hC0 : 0 ≤ C0) (hL : 2 ≤ L) (hY0 : Yf L ∅ ≤ 0)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0)
    (Λ : ∀ b : BlockAtom Bk J L, ((Slot → BlockLabel m₀ blk p L b) → ℝ) →ₗ[ℝ] ℝ)
    (Es : Finset (BlockAtom Bk J L)) (hE : ∀ b ∉ Es, Λ b = D.R.law p L b)
    {qE cE : ℕ} (hDE : ∏ b ∈ Es, crtModuli m₀ blk p L b = qE * cE) (hqE : Squarefree qE)
    (hcE : IsSquare cE) (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl) (hcopE : qE.Coprime cE)
    (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    (hne : ∏ b ∈ Es, crtModuli m₀ blk p L b ≠ 1)
    {Ω : Type*} [Fintype Ω] (Pw : FiniteLaw Ω) (Q' : Slot → ℝ) {Cdc σ : ℝ}
    (hrest : ∀ (v : Slot) (B : Finset ℤ),
      B ⊆ Icc 1 ((blockScale * stepEll (crtModuli m₀ blk p L) Es 1 (blockScale * L) : ℕ) : ℤ) →
      referenceEnergy (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
          (child (crtModuli m₀ blk p L) Es (Q' v) B
            (blockScale * stepEll (crtModuli m₀ blk p L) Es 1 (blockScale * L))) ≤
        Yf (stepEll (crtModuli m₀ blk p L) Es 1 (blockScale * L)) B)
    (hdc : |structuredEnergy (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair)
            D.R.μ₀ D.R.μp L)) Pw
          (liftWeight Es (selectedWeight Es (crtLaws blk (prefix_pairwise hpair) L Λ))
            (uniformRest (Xa := fun b => ZMod (crtModuli m₀ blk p L b)) Es))
          (paperInputs (crtModuli m₀ blk p L) Es (paperCutoff (blockScale * L)) A (fun _ => 1)
            (fun _ => blockScale * L) (fun _ _ => 0) (fun _ _ => 0)) -
        structuredEnergy (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair)
            D.R.μ₀ D.R.μp L)) Pw
          (liftWeight Es (selectedWeight Es (crtLaws blk (prefix_pairwise hpair) L Λ))
            (uniformRest (Xa := fun b => ZMod (crtModuli m₀ blk p L b)) Es))
          (unchangedModel (crtModuli m₀ blk p L) Es A L Q')| ≤
      Cdc * totalVariation (selectedWeight Es (crtLaws blk (prefix_pairwise hpair) L Λ)) *
        (L : ℝ) ^ (-σ) * density (blockScale * L) A)
    (hatom : ∀ b ∈ Es, ∀ hb : 0 < totalVariation (lawDensity (Λ b)),
      MixedLpBound (variationLaw _ hb) (72 / θ) 1) :
    |diagonalIntegral (tensorLaw Λ) (blockLift m₀ blk p L A)| ≤
      (∏ b : {b // b ∈ Es}, ∑ x : Slot → BlockLabel m₀ blk p L b.1, |lawDensity (Λ b.1) x|) *
        ((1 + scaleU blockScale M0 Qcl stageTau L) *
            ((stepR (crtModuli m₀ blk p L) Es 1 : ℕ) : ℝ) ^ a' * Yf L A +
          Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A) :=
  abs_block_energy_le_unchanged blk p hpair hcex hθ hθ2 ha hC0 hL hY0 hsc hM0 D.R.μ₀ D.R.μp
    (fun β => (D.R.rp₀ β).slot) (fun j => (D.R.rpp (p L j) (D.S.p_prime L j)).slot)
    D.R.inv₀ D.R.invp Λ Es hE hDE hqE hcE hcE0 hcQ hcopE hqN hne Pw Q' hrest hdc hatom

/-- **The paper's joined moduli are pairwise coprime at every scale**
(`CancellationSteps.paper_hcopE`: distinct fixed primes below `P₄`, distinct tail primes at least
`P₄`). -/
theorem paper_pairwise (L : ℕ) :
    Pairwise fun i j =>
      (joinModuli CancellationSteps.paperM0 (CancellationSteps.paperTail L) i).Coprime
        (joinModuli CancellationSteps.paperM0 (CancellationSteps.paperTail L) j) :=
  fun i j hij => CancellationSteps.paper_hcopE L i j hij

end Sarkozy.EnvelopeEnergiesPaper
