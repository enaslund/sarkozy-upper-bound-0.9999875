module

public import Sarkozy.SignedGram.Paper

@[expose] public section

/-!
# The F1 main statement with MRG's `SG` reduced to prime-level hypotheses (SGA)

`MiddleRefinement.MainFinalObligations3g` (7 fields: `PC`, `BA`, `Cmp`, **`SG`**, `SA`, `Cls`,
`Sh`) with `SG` (the block Grams of `prop:signed-sides`(i),(ii) for `F₁` and `F₂` as cut brackets
of slot measures at `ι`) replaced by **`SGp`**: at every middle block of piece `i`, `PrimeAt` for
the signed record of `F₁` at the side `paperSide i`, i.e. at the shift
`σ = r · paperSide i / H_𝔅`, `H_𝔅 = ∏_{p∈𝔅} (1 + e₀(p))`:
- the **prime Gram on the centred functions** of `L²(m_{0,p})²` at every prime of the block
  (`PrimeGramC`);
- **prime centred norms** `ρ₀` (reference) and `ρ₁` (components) of the Markov operators, with
  `ρ₀, ρ₁ ≤ 1` and `ρ₀² + (1 + t) ρ₁² ≤ σ` (`CentredNorm`).

These are the per-prime statements from which the paper's proof of `prop:signed-sides`(i) gets the
two hypotheses of `lem:record:asymmetric-gram`(b) (from `prop:signed-bounds`(c),(d),
`lem:old-f-law`(f), `lem:record:direct-gram`).

* **`SignedGramInputs`** (the block Gram `OpGramAt` on `L²(m_{0,𝔅})²`), **`.toSG`**;
* **`SignedSectorInputs`** (the two hypotheses of (b), `SectorAt`), **`.toGram`**;
* **`SignedPrimeInputs`** (the field `SGp`), **`.toSector`**;
* **`MainFinalObligations3h`**, **`to3g`**, **`main_target_f1_final3h`**, **`main_goal_f1f`**.

What is now proved between `SGp` and MRG's `SG`:
- the constants of the prime Gram (`primeGram_of_centered`);
- the sector bound on supports of at least two primes from the prime centred norms
  (`multiBound_of_centred`, through MX's `lem:sector`(e));
- the sector argument of (b) (`opGram_of_sectors`);
- the passage from cut forms of slot measures at `ι` to kernel forms (`form_two`, `form_diag`,
  `form_newMeas`);
- the replacement of `Diag_ι(m₀)` by `H_𝔅 D¹`, with the density bound `dm₀/dν ≤ H_𝔅`
  (`densityLe_block`, from E1's `g0_bound`), and the enlargement (a);
- the symmetry of the diagonal blocks;
- the whole Gram of `F₂` (`lem:record:asymmetric-gram`(c), `opGram_refl`).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.SignedGram

open Sarkozy.PartV Sarkozy.BlockSpecPaper Sarkozy.MiddleRefinement
open Sarkozy.MainFinal (BlockAnalytic)
open Sarkozy.MainFinal2 (PrimeCertificates2)
open Sarkozy.AnalyticCells (f1Cell)
open Sarkozy.MainFinalF1 (specF analyticInputs)
open Sarkozy.MainFinalF1b (ClassPartsE4B)
open Sarkozy.MainFinalF1c (ComparisonPartsTC)
open Sarkozy.MainFinalF1d (SAPartsTCP)
open Sarkozy.MainFinal2 (SharpParts2)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {A : PaperAnalyticInputs f1Cell}

/-- **The block Gram of the signed record of `F₁` on `L²(m₀)²` at every middle block**, at the
paper's side `paperSide i` of the piece (`lem:record:asymmetric-gram`(b), conclusion of the sector
argument; `prop:signed-sides`(i)). 1 field. *Open* (analytic). -/
structure SignedGramInputs (C : ComparisonPartsTC hW hMR hFour A) : Prop where
  gram : ∀ b i, blockSite b = .inl i →
    SpecOpGram hW (paperIn f1Cell) (paperSide i) (specF hW A b) (C.blk b)

theorem paperSide_nonneg (i : Fin 33) : 0 ≤ paperSide i := by
  unfold paperSide sideQ
  positivity

/-- **MRG's `SG` from the block Gram of `F₁`** (`specSides_of_gram`; `specSides_at` for the
middle records priced at their bounds, RP). -/
theorem SignedGramInputs.toSG {C : ComparisonPartsTC hW hMR hFour A} (G : SignedGramInputs C) :
    SignedSideInputs C.toK1 where
  gram b i hb := specSides_at hW (paperIn f1Cell) _ _ _ _ (specF hW A b) (C.blk b)
    (specSides_of_gram hW (paperIn f1Cell) (paperSide i) (specF hW A b) (C.blk b)
      (specGram_of_opGram hW (paperIn f1Cell) (paperSide_nonneg i) (specF hW A b) (C.blk b)
        (G.gram b i hb)))

/-- **The hypotheses of `lem:record:asymmetric-gram`(b) at every middle block** (prime Grams and
sector bounds), at the paper's side `paperSide i` of the piece (`prop:signed-sides`(i)). 1 field.
*Open* (analytic). -/
structure SignedSectorInputs (C : ComparisonPartsTC hW hMR hFour A) : Prop where
  sector : ∀ b i, blockSite b = .inl i →
    SpecSector hW (paperIn f1Cell) (paperSide i) (specF hW A b) (C.blk b)

/-- **The sector argument at every middle block** (`specOpGram_of_sector`). -/
theorem SignedSectorInputs.toGram {C : ComparisonPartsTC hW hMR hFour A}
    (G : SignedSectorInputs C) : SignedGramInputs C where
  gram b i hb := specOpGram_of_sector hW (paperIn f1Cell) (paperSide_nonneg i) (specF hW A b)
    (C.blk b) (G.sector b i hb)

/-- **The prime-level hypotheses at every middle block** (centred prime Grams and prime centred
norms), at the paper's side `paperSide i` of the piece (`prop:signed-sides`(i)). 1 field.
*Open* (analytic). -/
structure SignedPrimeInputs (C : ComparisonPartsTC hW hMR hFour A) : Prop where
  prime : ∀ b i, blockSite b = .inl i →
    SpecPrime hW (paperIn f1Cell) (paperSide i) (specF hW A b) (C.blk b)

/-- **The sector bounds from the prime centred norms at every middle block**
(`specSector_of_prime`). -/
theorem SignedPrimeInputs.toSector {C : ComparisonPartsTC hW hMR hFour A}
    (G : SignedPrimeInputs C) : SignedSectorInputs C where
  sector b i hb := specSector_of_prime hW (paperIn f1Cell) (specF hW A b) (C.blk b)
    (G.prime b i hb)

/-- **The obligations of the F1 statement with `SG` reduced to prime-level hypotheses**:
`MainFinalObligations3g` with `SG` replaced by `SGp`. 7 fields. -/
structure MainFinalObligations3h (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) (hRR : Target.ThetaSmallRR) where
  /-- The per-prime cut certificates (C8, C9). -/
  PC : PrimeCertificates2
  /-- The block-level analytic inputs (B6). -/
  BA : BlockAnalytic
  /-- The (CP4) inputs (upper blocks; the tail proved). -/
  Cmp : ComparisonPartsTC hW hMR hFour (analyticInputs (PC.toPC hW hMR hFour) BA)
  /-- **The centred prime Grams and prime centred norms of `F₁`** at the paper's sides.
  *Open* (analytic). -/
  SGp : SignedPrimeInputs Cmp
  /-- `hSA` in reduced form (as in `MainFinalObligations3g`). -/
  SA : SAPartsTCP hW hMR hFour (analyticInputs (PC.toPC hW hMR hFour) BA) Cmp
  /-- The class inputs (as in `MainFinalObligations3g`). -/
  Cls : ClassPartsE4B ((dvOf PC BA Cmp SGp.toSector.toGram.toSG).toK1 hB SA.toTC
    (hmidOf hB hRR PC BA Cmp SGp.toSector.toGram.toSG SA)).data
  /-- The inputs of `SF`, `fix`, `env` (as in `MainFinalObligations3g`). -/
  Sh : SharpParts2 ((dvOf PC BA Cmp SGp.toSector.toGram.toSG).toK1 hB SA.toTC
    (hmidOf hB hRR PC BA Cmp SGp.toSector.toGram.toSG SA)).toJoint

/-- The obligations of `main_target_f1_final3g`. -/
noncomputable def MainFinalObligations3h.to3g {hB : Target.BMOR} {hRR : Target.ThetaSmallRR}
    (O : MainFinalObligations3h hW hMR hFour hB hRR) :
    MainFinalObligations3g hW hMR hFour hB hRR where
  PC := O.PC
  BA := O.BA
  Cmp := O.Cmp
  SG := O.SGp.toSector.toGram.toSG
  SA := O.SA
  Cls := O.Cls
  Sh := O.Sh

/-- **The main statement at `ε = a_T/71 ≈ 1.19975·10⁻⁵`, F1 partition, with `SG` reduced to the
prime-level hypotheses of `prop:signed-sides`(i)** (`main_target_f1_final3g` with `O.to3g`). -/
theorem main_target_f1_final3h (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligations3h hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_f1_final3g hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR O.to3g

/-- **`main_target_f1_final3h` at the owner's goal exponent** `N^{0.99999}`. -/
theorem main_goal_f1f (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligations3h hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  main_goal_f1e hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR O.to3g

end Sarkozy.SignedGram
