module

public import Sarkozy.SignedComponents.PrimeComponents
public import Sarkozy.SignedComponents.Data

@[expose] public section

/-!
# The paper's middle blocks: `ReplacementData` and B2's `ComparisonInputs` from the defect bounds

`paper/sections/21_middle_records.tex`, `lem:signed-components`, `def:record:mixture`,
`subsec:middle-comparison`.

On every class-three block of the paper's partition the primes are `≡ 3 (4)` and at least
`Q₃ ≥ 19` (`blockPrimes_mod_ge`), so the per-prime components of
`Sarkozy.SignedComponents.PrimeComponents` exist at every prime.

* **`DefectConstants b hne t`**: the constants `M_{c,p} ≥ 0` of a middle block with the defect
  bound `|α|, |β| ≤ M_{c,p}` of `lem:signed-components`(c) at every prime and component: the one
  remaining input of the fold records (with `M = M_c` it is `lem:signed-components`(c), proved in
  the paper from `thm:weil`). `DefectConstants.max`: it is satisfiable, with `M = ∑|α| + ∑|β|`.
* `paperComponents`: the fold components of the block (`def:record:mixture`(b)–(d)).
* **`DefectSpec`**, `DefectSpec.toFoldSpec`: B2's `UpperAtomInputs` on an upper block,
  `DefectConstants` on a middle block; **`comparisonInputsOfDefects`**: B2's `ComparisonInputs`.
* **`MaxSpec`**, **`comparisonInputsMax`**: the same with `M = ∑|α| + ∑|β|` on every middle block,
  so that B2's `ComparisonInputs` needs no middle-block input at all. This is a non-vacuity
  witness: its fold records are not the paper's (`M ≠ M_c`), and the paper's norm bounds are
  stated for the paper's records.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.SignedComponents

open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.BlockFrame Sarkozy.RecordExpansion
open Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.FirstStagePaper Sarkozy.ComparisonLawPaper
open Sarkozy.PartVLaws Sarkozy.MiddleComparison Sarkozy.MiddleRecords
open Sarkozy.TargetLedger (targetDecay)
open Sarkozy.CancellationSteps

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}

omit [Fintype B] [DecidableEq B] in
/-- The primes of a class-three block are at least `19`. -/
theorem blockPrimes_ge19 (b : B) (j : {j : PaperJ0 // paperAtomMap blockOf j = .inr b}) :
    19 ≤ blockPrimes blockOf b j :=
  le_trans (by norm_num [PartV.Q3]) (blockPrimes_mod_ge b j).2

/-- **The defect constants of a middle block** (`lem:signed-components`(c) as a hypothesis): for
every prime `p` of the block and component `c`, a constant `M_{c,p} ≥ 0` with `|α|, |β| ≤ M_{c,p}`
on the support of `m₀`. -/
structure DefectConstants (b : B) (hne : MiddleNonempty (blockPrimes blockOf b)) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) where
  M : {j : PaperJ0 // paperAtomMap blockOf j = .inr b} → Fin 3 → ℝ
  nonneg : ∀ i c, 0 ≤ M i c
  bound : ∀ i c, (repairAt (blockPrimes_mod_ge b i).1 (blockPrimes_ge19 b i) (hne.F2 i) ht0 ht1
    c).DefectBound (M i c)

/-- The defect constants are satisfiable (`M = ∑|α| + ∑|β|`). -/
noncomputable def DefectConstants.max (b : B) (hne : MiddleNonempty (blockPrimes blockOf b))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : DefectConstants b hne ht0 ht1 where
  M i c := (repairAt (blockPrimes_mod_ge b i).1 (blockPrimes_ge19 b i) (hne.F2 i) ht0 ht1 c).Mmax
  nonneg _ _ := RepairInput.Mmax_nonneg _
  bound _ _ := RepairInput.defectBound_Mmax _

/-- **The fold components of a middle block of the paper** (`def:record:mixture`(b)–(d)). -/
noncomputable def paperComponents {b : B} {hne : MiddleNonempty (blockPrimes blockOf b)} {t : ℝ}
    {ht0 : 0 ≤ t} {ht1 : t ≤ 1} (Dc : DefectConstants b hne ht0 ht1) :
    FoldComponents (blockPrimes blockOf b) hne :=
  blockComponents (fun i => (blockPrimes_mod_ge b i).1) (blockPrimes_ge19 b) hne ht0 ht1 Dc.M
    Dc.nonneg Dc.bound

/-- **The (CP4) inputs of a class-three block, with the defect constants as the only middle-block
input**: B2's `UpperAtomInputs` on an upper block, `DefectConstants` on a middle block. -/
def DefectSpec (hW : Target.Weil) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {b : B} :
    PaperBlockSpec blockOf b → Type 1
  | .upper U => ULift (UpperAtomInputs (blockPrimes blockOf b) (upperNe hW U) U.W U.r)
  | .middleUniform M => ULift (DefectConstants b M.hne ht0 ht1)
  | .middleIndividual M => ULift (DefectConstants b M.hne ht0 ht1)
  | .middleCoherent M => ULift (DefectConstants b M.hne ht0 ht1)

/-- `DefectSpec` gives `FoldSpec` (`paperComponents` on every middle block). -/
noncomputable def DefectSpec.toFoldSpec (hW : Target.Weil) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {b : B} : (S : PaperBlockSpec blockOf b) → DefectSpec hW ht0 ht1 S → FoldSpec hW S
  | .upper _, U => U
  | .middleUniform _, Dc => ⟨paperComponents Dc.down⟩
  | .middleIndividual _, Dc => ⟨paperComponents Dc.down⟩
  | .middleCoherent _, Dc => ⟨paperComponents Dc.down⟩

variable (blockOf) in
/-- **B2's `ComparisonInputs` with every middle atom built from the paper's fold components**,
given the defect constants (`lem:signed-components`(c)) on every middle block. -/
noncomputable def comparisonInputsOfDefects (hW : Target.Weil)
    (spec : ∀ b, PaperBlockSpec blockOf b) (hC : TailInputsCorr PartV.P4)
    (In : FirstStageInputs blockOf)
    (clique : ∀ q : PrefixCoord, DeletionInputs ((v2Reference blockOf hW spec hC).μ₀ (.inl q))
      (paperPrefixAccepted blockOf (.inl q)) MainAnchor.paperQueries)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (blk : ∀ b : B, DefectSpec hW ht0 ht1 (spec b))
    (tail : ∀ (q : ℕ) [Fact q.Prime] (h4 : PartV.P4 ≤ q),
      TailAtomInputs q (tailNe hW h4)
        (signedIntegral ((v2Reference blockOf hW spec hC).μp q).weight))
    (St At : ℝ)
    (tail_S : ∀ L, ∑ j : PaperJt L, (tail (paperTail L j) (P4_le_paperTail j)).toAtom.sprice
      (((paperTail L j : ℕ) : ℝ) ^ (2 * targetDecay)) ≤ St)
    (tail_A : ∀ L, ∑ j : PaperJt L, (tail (paperTail L j) (P4_le_paperTail j)).toAtom.aprice
      (((paperTail L j : ℕ) : ℝ) ^ (2 * targetDecay)) ≤ At) :
    ComparisonInputs blockOf hW spec hC In :=
  comparisonInputsOfFold blockOf hW spec hC In clique ht0 ht1
    (fun b => DefectSpec.toFoldSpec hW ht0 ht1 (spec b) (blk b)) tail St At tail_S tail_A

/-- **The (CP4) inputs with no middle-block input**: B2's `UpperAtomInputs` on an upper block,
nothing on a middle block. -/
def MaxSpec (hW : Target.Weil) {b : B} : PaperBlockSpec blockOf b → Type 1
  | .upper U => ULift (UpperAtomInputs (blockPrimes blockOf b) (upperNe hW U) U.W U.r)
  | .middleUniform _ => PUnit
  | .middleIndividual _ => PUnit
  | .middleCoherent _ => PUnit

/-- `MaxSpec` gives `DefectSpec` (`DefectConstants.max` on every middle block). -/
noncomputable def MaxSpec.toDefectSpec (hW : Target.Weil) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {b : B} : (S : PaperBlockSpec blockOf b) → MaxSpec hW S → DefectSpec hW ht0 ht1 S
  | .upper _, U => U
  | .middleUniform M, _ => ⟨DefectConstants.max b M.hne ht0 ht1⟩
  | .middleIndividual M, _ => ⟨DefectConstants.max b M.hne ht0 ht1⟩
  | .middleCoherent M, _ => ⟨DefectConstants.max b M.hne ht0 ht1⟩

variable (blockOf) in
/-- **B2's `ComparisonInputs` with no middle-block input** (non-vacuity witness; the fold records
use `M = ∑|α| + ∑|β|`, not the paper's `M_c`). -/
noncomputable def comparisonInputsMax (hW : Target.Weil) (spec : ∀ b, PaperBlockSpec blockOf b)
    (hC : TailInputsCorr PartV.P4) (In : FirstStageInputs blockOf)
    (clique : ∀ q : PrefixCoord, DeletionInputs ((v2Reference blockOf hW spec hC).μ₀ (.inl q))
      (paperPrefixAccepted blockOf (.inl q)) MainAnchor.paperQueries)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (blk : ∀ b : B, MaxSpec hW (spec b))
    (tail : ∀ (q : ℕ) [Fact q.Prime] (h4 : PartV.P4 ≤ q),
      TailAtomInputs q (tailNe hW h4)
        (signedIntegral ((v2Reference blockOf hW spec hC).μp q).weight))
    (St At : ℝ)
    (tail_S : ∀ L, ∑ j : PaperJt L, (tail (paperTail L j) (P4_le_paperTail j)).toAtom.sprice
      (((paperTail L j : ℕ) : ℝ) ^ (2 * targetDecay)) ≤ St)
    (tail_A : ∀ L, ∑ j : PaperJt L, (tail (paperTail L j) (P4_le_paperTail j)).toAtom.aprice
      (((paperTail L j : ℕ) : ℝ) ^ (2 * targetDecay)) ≤ At) :
    ComparisonInputs blockOf hW spec hC In :=
  comparisonInputsOfDefects blockOf hW spec hC In clique ht0 ht1
    (fun b => MaxSpec.toDefectSpec hW ht0 ht1 (spec b) (blk b)) tail St At tail_S tail_A

/-! ## The block price of a middle block (B2's `hm`), from the twelve norm bounds -/

omit [Fintype B] in
/-- **The block price of a middle block with the uniform root** (B2's per-block bound `M_𝔅` of
`SAExplicit_of_bands`, hypothesis `hm`): with the paper's fold components (`paperComponents`),
B2's atom of the block has `s_𝔅 + a_𝔅` at most the bound of `lem:middle-comparison-prices`, given
the twelve norm bounds `NormBounds` (hypotheses). -/
theorem defect_uniform_price_le (hW : Target.Weil) (In : FirstStageInputs blockOf) {b : B}
    (M : MiddleUniformInputs blockOf b) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (Dc : DefectConstants b M.hne ht0 ht1) {Xn : ℕ} {b' sel : ℝ} (hX : 4 ≤ Xn)
    (hb : (Xn : ℝ) ≤ b') (hrb : M.r = 1 / Real.sqrt b') (hsel : 0 ≤ sel)
    (hfh : 0 ≤ M.I.f₁ + M.I.h₁) {sF aF ℓ sE aE : ℝ}
    (NB : NormBounds (blockPrimes blockOf b) (classThree_blockPrimes b) M.hne
      (uniformRoot _ M.hne) M.W M.I M.hr (In.bmin b) (paperComponents Dc) t b' sF aF ℓ sE aE) :
    (BlockInputs.toAtom hW In _ (SpecInputs.toBlockInputs hW In (.middleUniform M)
        (SpecData.toSpecInputs hW In (.middleUniform M) (FoldSpec.toSpecData hW In ht0 ht1
          (.middleUniform M) (DefectSpec.toFoldSpec hW ht0 ht1 (.middleUniform M) ⟨Dc⟩))))).sprice
        sel +
      (BlockInputs.toAtom hW In _ (SpecInputs.toBlockInputs hW In (.middleUniform M)
        (SpecData.toSpecInputs hW In (.middleUniform M) (FoldSpec.toSpecData hW In ht0 ht1
          (.middleUniform M) (DefectSpec.toFoldSpec hW ht0 ht1 (.middleUniform M) ⟨Dc⟩))))).aprice
        sel ≤
      ((coefS2 M.W sE * (1 / Real.sqrt b') ^ 2 + coefS3 M.W M.I sF * (1 / Real.sqrt b') ^ 3 +
          coefS4 M.W (gS (1 / (Xn : ℝ))) * (1 / Real.sqrt b') ^ 4 +
          coefS5 M.W (1 / (Xn : ℝ)) * (1 / Real.sqrt b') ^ 5) +
        (coefA2 M.W ℓ aE * (1 / Real.sqrt b') ^ 2 +
          coefA3 M.W aF (gA (1 / (Xn : ℝ)) (rXof Xn)) * (1 / Real.sqrt b') ^ 3 +
          coefA4 M.W (1 / (Xn : ℝ)) * (1 / Real.sqrt b') ^ 4)) * sel :=
  ofFold_price_sum_le_of _ (classThree_blockPrimes b) M.hne _ M.W M.I M.hr (In.bmin b)
    (paperComponents Dc) ht0 ht1 (factsU In M) hX hb hrb hsel hfh NB

omit [Fintype B] in
/-- **The block price of a middle block with the individual-square root** (the bands `2³⁶`,
`2⁴⁰` under ALLp), as `defect_uniform_price_le`. -/
theorem defect_individual_price_le (hW : Target.Weil) (In : FirstStageInputs blockOf) {b : B}
    (M : MiddleIndividualInputs blockOf b) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (Dc : DefectConstants b M.hne ht0 ht1) {Xn : ℕ} {b' sel : ℝ} (hX : 4 ≤ Xn)
    (hb : (Xn : ℝ) ≤ b') (hrb : M.r = 1 / Real.sqrt b') (hsel : 0 ≤ sel)
    (hfh : 0 ≤ M.I.f₁ + M.I.h₁) {sF aF ℓ sE aE : ℝ}
    (NB : NormBounds (blockPrimes blockOf b) (classThree_blockPrimes b) M.hne
      (individualBlockRoot _ M.u M.hne.L2) M.W M.I M.hr (In.bmin b) (paperComponents Dc) t b' sF
      aF ℓ sE aE) :
    (BlockInputs.toAtom hW In _ (SpecInputs.toBlockInputs hW In (.middleIndividual M)
        (SpecData.toSpecInputs hW In (.middleIndividual M) (FoldSpec.toSpecData hW In ht0 ht1
          (.middleIndividual M) (DefectSpec.toFoldSpec hW ht0 ht1 (.middleIndividual M)
            ⟨Dc⟩))))).sprice sel +
      (BlockInputs.toAtom hW In _ (SpecInputs.toBlockInputs hW In (.middleIndividual M)
        (SpecData.toSpecInputs hW In (.middleIndividual M) (FoldSpec.toSpecData hW In ht0 ht1
          (.middleIndividual M) (DefectSpec.toFoldSpec hW ht0 ht1 (.middleIndividual M)
            ⟨Dc⟩))))).aprice sel ≤
      ((coefS2 M.W sE * (1 / Real.sqrt b') ^ 2 + coefS3 M.W M.I sF * (1 / Real.sqrt b') ^ 3 +
          coefS4 M.W (gS (1 / (Xn : ℝ))) * (1 / Real.sqrt b') ^ 4 +
          coefS5 M.W (1 / (Xn : ℝ)) * (1 / Real.sqrt b') ^ 5) +
        (coefA2 M.W ℓ aE * (1 / Real.sqrt b') ^ 2 +
          coefA3 M.W aF (gA (1 / (Xn : ℝ)) (rXof Xn)) * (1 / Real.sqrt b') ^ 3 +
          coefA4 M.W (1 / (Xn : ℝ)) * (1 / Real.sqrt b') ^ 4)) * sel :=
  ofFold_price_sum_le_of _ (classThree_blockPrimes b) M.hne _ M.W M.I M.hr (In.bmin b)
    (paperComponents Dc) ht0 ht1 (factsI In M) hX hb hrb hsel hfh NB

end Sarkozy.SignedComponents
