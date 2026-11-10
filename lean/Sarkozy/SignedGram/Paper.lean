module

public import Sarkozy.SignedGram.Block
public import Sarkozy.SignedGram.SectorBlock
public import Sarkozy.SignedGram.SectorNorm
public import Sarkozy.SignedGram.Density
public import Sarkozy.SignedEstimates.Paper
public import Sarkozy.MiddleRefinement.Main

@[expose] public section

/-!
# MRG's `SignedSideInputs` from the block Gram of `F₁` on `L²(m₀)²` (SGA)

`paper/sections/24_matching_mean.tex`, `prop:signed-sides`(i),(ii),
`lem:record:asymmetric-gram`(a)–(c).

At every middle block of the F1 data, with the paper's records (B8's `ofFold` at E1's
`paperComponents`, `t = 127/500`):

* **`GramAt pr hne C r d`**: there are a shift `σ ≥ 0` and a density bound `H` with
  `dm₀/dν ≤ H`, `H σ ≤ r d`, and the block Gram of the signed record of `F₁` on `L²(m₀)²` with the
  equal shifts `σ` (`OpGram`). This is the paper's conclusion of the sector argument of
  `lem:record:asymmetric-gram`(b) at `σ = r_b max(d_t, c_{≥2} r_X) = r_b d_t(X)`, with
  `H = H̄_X` (`prop:signed-sides`(i)) and `d = paperSide i ≥ H̄_X d_t(X)`.
* **`SpecGram`**: `GramAt` at the frame of the block, by specification (`True` on an upper
  block).
* **`specSides_of_gram`**: `SpecGram` gives MRG's `SpecSides` (both folds: `F₁` by the measure
  form of (b), `F₂` by (c), the paper's components being reflected transposes); `specSides_at`
  (RP): `SpecSides` reads only the records, so it transfers to the front's data priced at the
  bounds (`MainFinalF1c.SignedSpec.toSpecDataAt`).
* **`OpGramAt pr hne C r d`**: the block Gram of `F₁` on `L²(m₀)²` with the equal shifts
  `σ = r d / H_𝔅`, `H_𝔅 = ∏_{p∈𝔅} (1 + e₀(p))`; **`gramAt_of_opGramAt`**: it gives `GramAt`, the
  density bound being proved (`densityLe_block`). **`SpecOpGram`**, **`specGram_of_opGram`**: the
  same by specification.
* **`SectorAt pr hne C r d`**: the two hypotheses of `lem:record:asymmetric-gram`(b) at the shift
  `σ = r d / H_𝔅`: the prime Gram of the signed record of `F₁` at every prime of the block
  (`PrimeGram`), and the bound `a + n ≤ σ` on every sector of at least two primes
  (`MultiBound`); **`opGramAt_of_sectorAt`** (the sector argument, `opGram_of_sectors`);
  **`SpecSector`**, **`specOpGram_of_sector`**.
* **`PrimeInputs pr hne C σ`**: the centred prime Grams, and prime centred norms `ρ₀` (old) and
  `ρ₁` (the three components) with `ρ₀² + (1 + t) ρ₁² ≤ σ`; **`sectorInputs_of_prime`**
  (`multiBound_of_centred`). **`PrimeAt`**, **`SpecPrime`**, **`specSector_of_prime`**.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.SignedGram

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.MiddleComparison Sarkozy.SignedComponents Sarkozy.MiddleRefinement
open Sarkozy.Labellings Sarkozy.FirstStagePaper Sarkozy.IndexSupport
open Sarkozy.PartVLaws (PaperBlockSpec blockPrimes paperAtomMap)
open Sarkozy.MainFinal2 (tPaper tPaper_nonneg tPaper_le_one)
open Sarkozy.MainFinalF1 (bOf Blk SignedSpec)

/-- **The block Gram input of a middle block** (`lem:record:asymmetric-gram`(b), conclusion of
the sector argument, for the signed record of `F₁`; `prop:signed-sides`(i)): a shift `σ ≥ 0` and
a density bound `H` (`dm₀/dν ≤ H`, the paper's `H_𝔅 = H̄_X`) with `H σ ≤ r d`, such that the block
Gram of `K'_{F₁}` holds on `L²(m₀)²` with the shifts `σ I`. *Hypothesis* (analytic). -/
def GramAt {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
    (hne : MiddleNonempty pr) (C : FoldComponents pr hne) (r d : ℝ) : Prop :=
  ∃ σ H : ℝ, 0 ≤ σ ∧
    DensityLe (lawF pr hne).weight (blockGraphLaw pr (foldGraph (Fin 1)) hne.F1).weight H ∧
    H * σ ≤ r * d ∧ OpGram (lawF pr hne).weight (newW C tPaper 0) σ σ

/-- The paper's fold components are reflected transposes (`def:record:mixture`(d)). -/
theorem paperComponents_reflected {b : Blk} {hne : MiddleNonempty (blockPrimes bOf b)}
    (Dc : DefectConstants b hne tPaper_nonneg tPaper_le_one) :
    Reflected (paperComponents Dc) :=
  blockComponents_reflected _ _ _ _ _ _ _

variable (hW : Target.Weil) (In : FirstStageInputs bOf)

/-- **`GramAt` at a class-three block of the F1 data**, by specification, at the paper's records
(`paperComponents`, `t = 127/500`) and the frame's scale `r`. `True` on an upper block. -/
def SpecGram {b : Blk} (d : ℝ) : (S : PaperBlockSpec bOf b) → SignedSpec hW S → Prop
  | .upper _, _ => True
  | .middleUniform M, E =>
      GramAt (blockPrimes bOf b) M.hne (paperComponents E.down.toDC) (frameU In M).r d
  | .middleIndividual M, E =>
      GramAt (blockPrimes bOf b) M.hne (paperComponents E.down.toDC) (frameI In M).r d
  | .middleCoherent M, E =>
      GramAt (blockPrimes bOf b) M.hne (paperComponents E.down.toDC) (frameC In M).r d

/-- **MRG's `SpecSides` from `SpecGram`** (`prop:signed-sides`(i),(ii) at the block, from
`lem:record:asymmetric-gram`(a),(b) in measure form and (c)). -/
theorem specSides_of_gram {b : Blk} (d : ℝ) :
    (S : PaperBlockSpec bOf b) → (E : SignedSpec hW S) → SpecGram hW In d S E →
      SpecSides hW In d d S (MainFinalF1.SignedSpec.toSpecData hW In S E)
  | .upper _, _, _ => trivial
  | .middleUniform M, E, ⟨_, _, hσ, hd, hH, hG⟩ =>
      signedSideGrams_of_opGram (classThree_blockPrimes b) _ M.W M.I M.hr (In.bmin b)
        (paperComponents E.down.toDC) (paperComponents_reflected _) tPaper_nonneg tPaper_le_one
        hσ hσ hd hH hH hG
  | .middleIndividual M, E, ⟨_, _, hσ, hd, hH, hG⟩ =>
      signedSideGrams_of_opGram (classThree_blockPrimes b) _ M.W M.I M.hr (In.bmin b)
        (paperComponents E.down.toDC) (paperComponents_reflected _) tPaper_nonneg tPaper_le_one
        hσ hσ hd hH hH hG
  | .middleCoherent M, E, ⟨_, _, hσ, hd, hH, hG⟩ =>
      signedSideGrams_of_opGram (classThree_blockPrimes b) _ M.W M.I M.hr (In.bmin b)
        (paperComponents E.down.toDC) (paperComponents_reflected _) tPaper_nonneg tPaper_le_one
        hσ hσ hd hH hH hG

/-- **The block Grams transfer to the data priced at the bounds** (RP): MRG's `SpecSides` reads
only the replacements `ν'_{F₁}`, `ν'_{F₂}`, which `toSpecDataAt` shares with K2's
`SignedSpec.toSpecData`. -/
theorem specSides_at {b : Blk} (κ : MainFinal.MiddleConsts) (bl dL dR : ℝ) :
    (S : PaperBlockSpec bOf b) → (E : SignedSpec hW S) →
      SpecSides hW In dL dR S (MainFinalF1.SignedSpec.toSpecData hW In S E) →
      SpecSides hW In dL dR S (MainFinalF1c.SignedSpec.toSpecDataAt hW In κ bl S E)
  | .upper _, _, _ => trivial
  | .middleUniform _, _, G => ⟨G.gram₁, G.gram₂⟩
  | .middleIndividual _, _, G => ⟨G.gram₁, G.gram₂⟩
  | .middleCoherent _, _, G => ⟨G.gram₁, G.gram₂⟩

/-- **The block Gram of `F₁` on `L²(m₀)²` at the shift `σ = r d / H_𝔅`**
(`lem:record:asymmetric-gram`(b), conclusion of the sector argument, with the density
`H_𝔅 = ∏_{p∈𝔅} (1 + e₀(p))` of `lem:old-f-law`(a)). In the paper `σ ≥ r_b d_t(X)`, since
`d ≥ H̄_X d_t(X)` and `H_𝔅 ≤ H̄_X`. *Hypothesis* (analytic). -/
def OpGramAt {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
    (hne : MiddleNonempty pr) (C : FoldComponents pr hne) (r d : ℝ) : Prop :=
  OpGram (lawF pr hne).weight (newW C tPaper 0) (r * d / Hblock pr) (r * d / Hblock pr)

theorem Hblock_pos {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) (h19 : ∀ i, 19 ≤ pr i) :
    0 < Hblock pr := by
  unfold Hblock
  refine Finset.prod_pos fun i _ => ?_
  have h : (5 : ℝ) ≤ (pr i : ℝ) := by exact_mod_cast le_trans (by norm_num) (h19 i)
  linarith [SignedEstimates.e0_nonneg h]

/-- **`OpGramAt` gives `GramAt`**: the density bound is `densityLe_block`, and
`H_𝔅 · (r d / H_𝔅) = r d`. -/
theorem gramAt_of_opGramAt {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ}
    [∀ i, Fact (pr i).Prime] {hne : MiddleNonempty pr} {C : FoldComponents pr hne} {r d : ℝ}
    (h3 : ∀ i, pr i % 4 = 3) (h19 : ∀ i, 19 ≤ pr i) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (hG : OpGramAt pr hne C r d) : GramAt pr hne C r d := by
  have hH := Hblock_pos pr h19
  refine ⟨r * d / Hblock pr, Hblock pr, div_nonneg (mul_nonneg hr hd) hH.le,
    densityLe_block pr hne h3 h19, ?_, hG⟩
  rw [mul_div_cancel₀ _ hH.ne']

/-- **`OpGramAt` at a class-three block of the F1 data**, by specification. `True` on an upper
block. -/
def SpecOpGram {b : Blk} (d : ℝ) : (S : PaperBlockSpec bOf b) → SignedSpec hW S → Prop
  | .upper _, _ => True
  | .middleUniform M, E =>
      OpGramAt (blockPrimes bOf b) M.hne (paperComponents E.down.toDC) (frameU In M).r d
  | .middleIndividual M, E =>
      OpGramAt (blockPrimes bOf b) M.hne (paperComponents E.down.toDC) (frameI In M).r d
  | .middleCoherent M, E =>
      OpGramAt (blockPrimes bOf b) M.hne (paperComponents E.down.toDC) (frameC In M).r d

theorem specGram_of_opGram {b : Blk} {d : ℝ} (hd : 0 ≤ d) :
    (S : PaperBlockSpec bOf b) → (E : SignedSpec hW S) → SpecOpGram hW In d S E →
      SpecGram hW In d S E
  | .upper _, _, _ => trivial
  | .middleUniform M, _, h => gramAt_of_opGramAt (fun i => (blockPrimes_mod_ge b i).1)
      (blockPrimes_ge19 b) M.hr hd h
  | .middleIndividual M, _, h => gramAt_of_opGramAt (fun i => (blockPrimes_mod_ge b i).1)
      (blockPrimes_ge19 b) M.hr hd h
  | .middleCoherent M, _, h => gramAt_of_opGramAt (fun i => (blockPrimes_mod_ge b i).1)
      (blockPrimes_ge19 b) M.hr hd h

/-- **The hypotheses of `lem:record:asymmetric-gram`(b) at a middle block**, at the shift `σ`
(`prop:signed-sides`(i): "the signed comparison record of `F₁` satisfies the hypotheses of
`lem:record:asymmetric-gram`(b)"):
- the prime Gram on the centred functions of `L²(m₀)²` at every prime of the block, with the
  shifts `σ` (the paper's `r_p d_t(1/p, p^{-1/2}) ≤ r_b d_t(X) ≤ σ`; the constants are proved,
  `primeGram_of_centered`);
- on every sector of at least two primes, norms `a` (old) and `n` (new) with `a + n ≤ σ` (the
  paper's `c_{≥2}(X) r_X r_b ≤ σ`).

*Hypothesis* (analytic: `prop:signed-bounds`(c),(d), `lem:old-f-law`(f),
`lem:record:direct-gram`). -/
def SectorInputs {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
    (hne : MiddleNonempty pr) (C : FoldComponents pr hne) (σ : ℝ) : Prop :=
  (∀ i, PrimeGramC (mP hne) (oldP hne) (compP hne C) (signedCoef tPaper) σ σ i) ∧
    ∀ l : ι → Bool, 2 ≤ (univ.filter fun j => l j = true).card →
      MultiBound (mP hne) (piKron (oldP hne))
        (∑ c, signedCoef tPaper c • piKron (compP hne C c)) σ l

/-- `SectorInputs` at the shift `σ = r d / H_𝔅`. -/
def SectorAt {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
    (hne : MiddleNonempty pr) (C : FoldComponents pr hne) (r d : ℝ) : Prop :=
  SectorInputs pr hne C (r * d / Hblock pr)

/-- **`lem:record:asymmetric-gram`(b)** at the shift `r d / H_𝔅`: the sector argument. -/
theorem opGramAt_of_sectorAt {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ}
    [∀ i, Fact (pr i).Prime] {hne : MiddleNonempty pr} {C : FoldComponents pr hne} {r d : ℝ}
    (h19 : ∀ i, 19 ≤ pr i) (hr : 0 ≤ r) (hd : 0 ≤ d) (h : SectorAt pr hne C r d) :
    OpGramAt pr hne C r d := by
  have hσ := div_nonneg (mul_nonneg hr hd) (Hblock_pos pr h19).le
  exact opGram_of_sectors hne C tPaper hσ (fun i => primeGram_of_centered (mP_total hne)
    (sum_signedCoef tPaper) (oldP_coupling hne) (compP_coupling hne C) hσ hσ (h.1 i)) h.2

/-- **`SectorAt` at a class-three block of the F1 data**, by specification. `True` on an upper
block. -/
def SpecSector {b : Blk} (d : ℝ) : (S : PaperBlockSpec bOf b) → SignedSpec hW S → Prop
  | .upper _, _ => True
  | .middleUniform M, E =>
      SectorAt (blockPrimes bOf b) M.hne (paperComponents E.down.toDC) (frameU In M).r d
  | .middleIndividual M, E =>
      SectorAt (blockPrimes bOf b) M.hne (paperComponents E.down.toDC) (frameI In M).r d
  | .middleCoherent M, E =>
      SectorAt (blockPrimes bOf b) M.hne (paperComponents E.down.toDC) (frameC In M).r d

theorem specOpGram_of_sector {b : Blk} {d : ℝ} (hd : 0 ≤ d) :
    (S : PaperBlockSpec bOf b) → (E : SignedSpec hW S) → SpecSector hW In d S E →
      SpecOpGram hW In d S E
  | .upper _, _, _ => trivial
  | .middleUniform M, _, h => opGramAt_of_sectorAt (blockPrimes_ge19 b) M.hr hd h
  | .middleIndividual M, _, h => opGramAt_of_sectorAt (blockPrimes_ge19 b) M.hr hd h
  | .middleCoherent M, _, h => opGramAt_of_sectorAt (blockPrimes_ge19 b) M.hr hd h

theorem sum_abs_signedCoef {t : ℝ} (ht : 0 ≤ t) : ∑ c, |signedCoef t c| = 1 + t := by
  simp only [signedCoef, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, abs_one, abs_neg,
    abs_of_nonneg (div_nonneg ht (by norm_num : (0 : ℝ) ≤ 2))]
  ring

/-- **The prime-level hypotheses of `prop:signed-sides`(i) at a middle block**, at the shift `σ`:
- the prime Gram on the centred functions at every prime (`PrimeGramC`);
- prime centred norms (`CentredNorm`, the Markov operators on the `m₀`-mean-zero functions):
  `ρ₀` for the reference coupling `K₀` and `ρ₁` for each of the three components `P_{c,p}`,
  with `ρ₀, ρ₁ ≤ 1` and `ρ₀² + (1 + t) ρ₁² ≤ σ`.

In the paper `ρ₀ = (Γ_A + e_o r) r`, `ρ₁ = c_+ r` at `r = r_b`, and
`ρ₀² + (1 + t) ρ₁² ≤ c_{≥2}(X) r_X r_b < r_b d_t(X) ≤ σ` (proof of `prop:signed-sides`(i),
"Supports of at least two primes"). *Hypothesis* (analytic: `prop:signed-bounds`(c),(d),
`lem:old-f-law`(f), `lem:record:direct-gram`, `lem:actual-features`). -/
def PrimeInputs {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
    (hne : MiddleNonempty pr) (C : FoldComponents pr hne) (σ : ℝ) : Prop :=
  (∀ i, PrimeGramC (mP hne) (oldP hne) (compP hne C) (signedCoef tPaper) σ σ i) ∧
    ∃ ρ₀ ρ₁ : ℝ, 0 ≤ ρ₀ ∧ ρ₀ ≤ 1 ∧ 0 ≤ ρ₁ ∧ ρ₁ ≤ 1 ∧
      (∀ j, CentredNorm (mP hne j) (oldP hne j) ρ₀) ∧
      (∀ c j, CentredNorm (mP hne j) (compP hne C c j) ρ₁) ∧
      ρ₀ ^ 2 + (1 + tPaper) * ρ₁ ^ 2 ≤ σ

/-- **The sector bounds from the prime centred norms** (`multiBound_of_centred`). -/
theorem sectorInputs_of_prime {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ}
    [∀ i, Fact (pr i).Prime] {hne : MiddleNonempty pr} {C : FoldComponents pr hne} {σ : ℝ}
    (h : PrimeInputs pr hne C σ) : SectorInputs pr hne C σ := by
  obtain ⟨hp, ρ₀, ρ₁, h0, h01, h1, h11, hc0, hc1, hσ⟩ := h
  refine ⟨hp, fun l hl => multiBound_of_centred (mP_nonneg hne) (mP_total hne)
    (oldP_coupling hne) (compP_coupling hne C) (fun j a b => (K0 (hne.F2 j)).nonneg _)
    (fun c j a b => ((C j).law 0 c).nonneg _) (signedCoef tPaper) h0 h01 h1 h11 hc0 hc1 ?_ l hl⟩
  rw [sum_abs_signedCoef tPaper_nonneg]
  exact hσ

/-- `PrimeInputs` at the shift `σ = r d / H_𝔅`. -/
def PrimeAt {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
    (hne : MiddleNonempty pr) (C : FoldComponents pr hne) (r d : ℝ) : Prop :=
  PrimeInputs pr hne C (r * d / Hblock pr)

/-- **`PrimeAt` at a class-three block of the F1 data**, by specification. `True` on an upper
block. -/
def SpecPrime {b : Blk} (d : ℝ) : (S : PaperBlockSpec bOf b) → SignedSpec hW S → Prop
  | .upper _, _ => True
  | .middleUniform M, E =>
      PrimeAt (blockPrimes bOf b) M.hne (paperComponents E.down.toDC) (frameU In M).r d
  | .middleIndividual M, E =>
      PrimeAt (blockPrimes bOf b) M.hne (paperComponents E.down.toDC) (frameI In M).r d
  | .middleCoherent M, E =>
      PrimeAt (blockPrimes bOf b) M.hne (paperComponents E.down.toDC) (frameC In M).r d

theorem specSector_of_prime {b : Blk} {d : ℝ} :
    (S : PaperBlockSpec bOf b) → (E : SignedSpec hW S) → SpecPrime hW In d S E →
      SpecSector hW In d S E
  | .upper _, _, _ => trivial
  | .middleUniform _, _, h => sectorInputs_of_prime h
  | .middleIndividual _, _, h => sectorInputs_of_prime h
  | .middleCoherent _, _, h => sectorInputs_of_prime h

end Sarkozy.SignedGram
