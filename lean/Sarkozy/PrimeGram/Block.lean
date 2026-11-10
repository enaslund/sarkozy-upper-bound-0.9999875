module

public import Sarkozy.PrimeGram.Gram
public import Sarkozy.SignedGram.Main
public import Sarkozy.SignedGram.Sanity

@[expose] public section

/-!
# SGA's `SignedPrimeInputs` from the prime decompositions (PG)

`paper/sections/24_matching_mean.tex`, proof of `prop:signed-sides`(i);
`paper/sections/21_middle_records.tex`, `lem:old-f-law`(f), `prop:signed-bounds`(c),(d),
`lem:actual-features`(d).

At every prime `p_i` of a middle block (SGA's objects: `mP = m₀`, `oldP = K₀`, `compP = P_c`,
`α = signedCoef t`, `t = 127/500`), with `r_i = p_i^{-1/2}`, `q_i = 1/p_i` and W6's frame constant
`Γ_i = gammaW ≤ Γ_A(q_i, r_i)` (proved, `frame_block`):

* **`DecompAt`** (hypotheses, the paper's prime decompositions, with constants per prime):
  - `old`: `lem:old-f-law`(f), `T_old = O₀ + R_o`, `‖R_o‖ ≤ e_o q` (`OldDecomp`);
  - `new`: `prop:signed-bounds`(c), `Π_⊥ T' Π_⊥ = O₀ + L^m_t + R^new`, `‖R^new‖ ≤ e_sg q`
    (`NewDecomp`);
  - `comp`: `prop:signed-bounds`(c), every centred component has norm at most `c_+ r`.
* **`GateAt`** (the numerical gates, elementary inequalities between the constants and the shift
  `σ`): `(s_t Γ_i + (e_o + e_sg) r_i) r_i ≤ σ` (the paper's `r_p d_t(1/p, p^{-1/2}) ≤ σ`), and
  `ρ₀ ≥ min(1, (Γ_i + e_o r_i) r_i)`, `ρ₁ ≥ min(1, c_+ r_i)`, `ρ₀, ρ₁ ∈ [0, 1]`,
  `ρ₀² + (1 + t) ρ₁² ≤ σ` (the paper's
  `c_{≥2} q ≤ σ`).
* **`primeInputs_of_decomp`**: `DecompAt` and `GateAt` give SGA's `PrimeInputs` — the centred
  prime Gram at every prime (`primeGramC_of_decomp`, through `lem:record:direct-gram` and the frame
  `frame_analysis`) and the prime centred norms (`centredNorm_of_decomp` for the reference).
* **`SpecDecomp`**, **`specPrime_of_decomp`**: the same at every class-three block of the F1 data,
  at the shift `σ = r · d / H_𝔅` of `PrimeAt`.
* **`SignedDecompInputs`**, **`SignedDecompInputs.toPrime`**: a constructor of SGA's
  `SignedPrimeInputs` (the field `SGp` of `main_goal_f1i`) from `SpecDecomp` at every middle block.
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.PrimeGram

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.MiddleComparison Sarkozy.SignedComponents Sarkozy.MiddleRefinement
open Sarkozy.Labellings Sarkozy.FirstStagePaper Sarkozy.IndexSupport
open Sarkozy.SignedGram Sarkozy.Envelopes
open Sarkozy.PartVLaws (PaperBlockSpec blockPrimes paperAtomMap)
open Sarkozy.MainFinal2 (tPaper tPaper_nonneg tPaper_le_one)
open Sarkozy.MainFinalF1 (bOf Blk SignedSpec)

/-! ## Monotonicity of the centred norm -/

theorem centredNorm_mono {B : Type} [Fintype B] [DecidableEq B] {μ : B → ℝ}
    {C : Matrix B B ℝ} {δ δ' : ℝ} (hμ : ∀ a, 0 ≤ μ a) (h : CentredNorm μ C δ) (hδ : 0 ≤ δ)
    (hle : δ ≤ δ') : CentredNorm μ C δ' := by
  intro f hf
  have h1 := h f hf
  have h2 : δ ^ 2 ≤ δ' ^ 2 := pow_le_pow_left₀ hδ hle 2
  have h3 : 0 ≤ ∑ a, μ a * f a ^ 2 := sum_nonneg fun a _ => mul_nonneg (hμ a) (sq_nonneg _)
  exact h1.trans (mul_le_mul_of_nonneg_right h2 h3)

/-! ## One middle block -/

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ} [∀ i, Fact (pr i).Prime]

/-- `r_i = p_i^{-1/2}`. -/
noncomputable def rP (pr : ι → ℕ) (i : ι) : ℝ := (√(pr i : ℝ))⁻¹

/-- W6's frame constant `Γ` at the prime `p_i` (`≤ Γ_A(1/p_i, p_i^{-1/2})`, `gammaW_le`). -/
noncomputable def gammaP (pr : ι → ℕ) [∀ i, Fact (pr i).Prime] (i : ι) : ℝ :=
  gammaW (F := ZMod (pr i))

omit [Fintype ι] [DecidableEq ι] in
theorem card_zmod (i : ι) : (Fintype.card (ZMod (pr i)) : ℝ) = (pr i : ℝ) := by
  rw [ZMod.card]

omit [Fintype ι] [DecidableEq ι] in
theorem primeHyps (h3 : ∀ i, pr i % 4 = 3) (h19 : ∀ i, 19 ≤ pr i) (i : ι) :
    ringChar (ZMod (pr i)) ≠ 2 ∧ Fintype.card (ZMod (pr i)) % 4 = 3 ∧
      19 ≤ Fintype.card (ZMod (pr i)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ZMod.ringChar_zmod_n]
    intro h
    have := h3 i
    omega
  · rw [ZMod.card]; exact h3 i
  · rw [ZMod.card]; exact h19 i

omit [Fintype ι] [DecidableEq ι] in
/-- **The frame bound at the paper's marginal**, at every prime of the block
(`lem:actual-features`(d), `frame_analysis`). -/
theorem frame_block (hne : MiddleNonempty pr) (h3 : ∀ i, pr i % 4 = 3) (h19 : ∀ i, 19 ≤ pr i)
    (i : ι) (f : Ai pr i → ℝ) : FrameAt (mP hne i) (gammaP pr i) f := by
  obtain ⟨hR, h3', h19'⟩ := primeHyps h3 h19 i
  exact frame_analysis (hne.F2 i) hR h3' h19' f

omit [Fintype ι] [DecidableEq ι] in
theorem gammaP_nonneg (h19 : ∀ i, 19 ≤ pr i) (i : ι) : 0 ≤ gammaP pr i := by
  apply gammaW_nonneg
  rw [ZMod.card]
  have : (19 : ℝ) ≤ pr i := by exact_mod_cast h19 i
  linarith

variable (pr) in
/-- **The prime decompositions of a middle block** (hypotheses, constants per prime):
* `old`: `lem:old-f-law`(f), `T_old = O₀ + R_o` with `‖R_o‖ ≤ e_o q` on the centred functions;
* `new`: `prop:signed-bounds`(c), `Π_⊥ T' Π_⊥ = O₀ + L^m_t + R^new` with `‖R^new‖ ≤ e_sg q`;
* `comp`: `prop:signed-bounds`(c), `‖Π_⊥ T[P_{c,p}] Π_⊥‖ ≤ c_+ r` for the three components;
* the constants are nonnegative (the paper's `e_o ≥ 56119/10000`, `e_sg`, `c_+ ≥ √3 Γ_A`). -/
structure DecompAt (hne : MiddleNonempty pr) (C : FoldComponents pr hne) (eo esg cp : ι → ℝ) :
    Prop where
  old : ∀ i, OldDecomp (mP hne i) (oldP hne i) (eo i)
  new : ∀ i, NewDecomp (mP hne i) (∑ c, signedCoef tPaper c • compP hne C c i) tPaper (esg i)
  comp : ∀ c i, CentredNorm (mP hne i) (compP hne C c i) (cp i * rP pr i)
  eo_nonneg : ∀ i, 0 ≤ eo i
  esg_nonneg : ∀ i, 0 ≤ esg i
  cp_nonneg : ∀ i, 0 ≤ cp i

variable (pr) in
/-- **The numerical gates at the shift `σ`** (`prop:signed-sides`(i), `prop:signed-bounds`(d),
`cert:signed-local`):
* at every prime, `(s_t Γ_i + (e_o + e_sg) r_i) r_i ≤ σ` (the paper's
  `r_p d_t(1/p, p^{-1/2}) ≤ r_b d_t(X) ≤ σ`, `d_t = s_t Γ_A + (e_o + e_sg) r`);
* norms `ρ₀ ≥ min(1, (Γ_i + e_o r_i) r_i)`, `ρ₁ ≥ min(1, c_+ r_i)` in `[0, 1]` with
  `ρ₀² + (1 + t) ρ₁² ≤ σ` (the paper's `ρ₀ = (Γ_A + e_o r_b) r_b`, `ρ₁ = c_+ r_b`,
  `ρ₀² + (1 + t) ρ₁² = c_{≥2} q_b ≤ σ`). The `min` with `1` (a Markov operator is a contraction,
  SGA's `centredNorm_one`) only serves the toy instance of `Sanity.lean`. -/
def GateAt (eo esg cp : ι → ℝ) (σ : ℝ) : Prop :=
  (∀ i, (sT tPaper * gammaP pr i + (eo i + esg i) * rP pr i) * rP pr i ≤ σ) ∧
    ∃ ρ₀ ρ₁ : ℝ, 0 ≤ ρ₀ ∧ ρ₀ ≤ 1 ∧ 0 ≤ ρ₁ ∧ ρ₁ ≤ 1 ∧
      (∀ i, min 1 ((gammaP pr i + eo i * rP pr i) * rP pr i) ≤ ρ₀) ∧
      (∀ i, min 1 (cp i * rP pr i) ≤ ρ₁) ∧
      ρ₀ ^ 2 + (1 + tPaper) * ρ₁ ^ 2 ≤ σ

/-- **SGA's `PrimeInputs` from the prime decompositions and the gates**: the centred prime Gram at
every prime (`primeGramC_of_decomp`: `lem:record:direct-gram` with the frame of
`lem:actual-features`(d)), and the prime centred norms (`centredNorm_of_decomp` for the reference,
`DecompAt.comp` for the components). -/
theorem primeInputs_of_decomp (hne : MiddleNonempty pr) (C : FoldComponents pr hne)
    {eo esg cp : ι → ℝ} {σ : ℝ} (h3 : ∀ i, pr i % 4 = 3) (h19 : ∀ i, 19 ≤ pr i)
    (D : DecompAt pr hne C eo esg cp) (G : GateAt pr eo esg cp σ) :
    PrimeInputs pr hne C σ := by
  obtain ⟨hg, ρ₀, ρ₁, h0, h01, h1, h11, hρ₀, hρ₁, hs⟩ := G
  have hr : ∀ i, (√(Fintype.card (ZMod (pr i)) : ℝ))⁻¹ = rP pr i := fun i => by
    rw [card_zmod]; rfl
  have hq : ∀ i, ((Fintype.card (ZMod (pr i)) : ℝ))⁻¹ = rP pr i * rP pr i := fun i => by
    rw [card_zmod, rP, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  have hrnn : ∀ i, 0 ≤ rP pr i := fun i => inv_nonneg.mpr (Real.sqrt_nonneg _)
  refine ⟨fun i f g hf hg' => ?_, ρ₀, ρ₁, h0, h01, h1, h11, fun j => ?_, fun c j => ?_, hs⟩
  · have hσ : (sT tPaper * gammaP pr i + (eo i + esg i) *
        (√(Fintype.card (ZMod (pr i)) : ℝ))⁻¹) * (√(Fintype.card (ZMod (pr i)) : ℝ))⁻¹ ≤ σ := by
      rw [hr]; exact hg i
    exact primeGramC_of_decomp (mP_nonneg hne i) (D.esg_nonneg i) (frame_block hne h3 h19 i)
      (D.old i) (D.new i) hσ f g hf hg'
  · have hco := oldP_coupling hne
    have hcn := centredNorm_of_decomp (mP_nonneg hne j) (gammaP_nonneg h19 j)
      (fun a b => (K0 (hne.F2 j)).nonneg _) (hco.row j) (hco.col j) (frame_block hne h3 h19 j)
      (D.old j)
    rw [hr, hq] at hcn
    have hδ : 0 ≤ gammaP pr j * rP pr j + eo j * (rP pr j * rP pr j) :=
      add_nonneg (mul_nonneg (gammaP_nonneg h19 j) (hrnn j))
        (mul_nonneg (D.eo_nonneg j) (mul_nonneg (hrnn j) (hrnn j)))
    have h1 := centredNorm_one (fun a b => (K0 (hne.F2 j)).nonneg _) (mP_nonneg hne j)
      (hco.row j) (hco.col j)
    have e : (gammaP pr j + eo j * rP pr j) * rP pr j =
        gammaP pr j * rP pr j + eo j * (rP pr j * rP pr j) := by ring
    have := hρ₀ j
    rw [e] at this
    rcases le_total 1 (gammaP pr j * rP pr j + eo j * (rP pr j * rP pr j)) with hc | hc
    · rw [min_eq_left hc] at this
      exact centredNorm_mono (mP_nonneg hne j) h1 zero_le_one this
    · rw [min_eq_right hc] at this
      exact centredNorm_mono (mP_nonneg hne j) hcn hδ this
  · have hcc := compP_coupling hne C c
    have h1 := centredNorm_one (fun a b => ((C j).law 0 c).nonneg _) (mP_nonneg hne j)
      (hcc.row j) (hcc.col j)
    have := hρ₁ j
    rcases le_total 1 (cp j * rP pr j) with hc | hc
    · rw [min_eq_left hc] at this
      exact centredNorm_mono (mP_nonneg hne j) h1 zero_le_one this
    · rw [min_eq_right hc] at this
      exact centredNorm_mono (mP_nonneg hne j) (D.comp c j)
        (mul_nonneg (D.cp_nonneg j) (hrnn j)) this

end Block

/-! ## Every middle block of the F1 data -/

section Paper

variable (hW : Target.Weil) (In : FirstStageInputs bOf)

/-- **The prime decompositions and gates of a middle block** at the shift `σ = r d / H_𝔅` of
SGA's `PrimeAt` (`r` the frame's scale), with constants per prime. -/
def DecompGateAt {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
    (hne : MiddleNonempty pr) (C : FoldComponents pr hne) (r d : ℝ) : Prop :=
  ∃ eo esg cp : ι → ℝ, DecompAt pr hne C eo esg cp ∧ GateAt pr eo esg cp (r * d / Hblock pr)

/-- **`DecompGateAt` at a class-three block of the F1 data**, by specification, at the paper's
records (`paperComponents`, `t = 127/500`). `True` on an upper block. -/
def SpecDecomp {b : Blk} (d : ℝ) : (S : PaperBlockSpec bOf b) → SignedSpec hW S → Prop
  | .upper _, _ => True
  | .middleUniform M, E =>
      DecompGateAt (blockPrimes bOf b) M.hne (paperComponents E.down.toDC) (frameU In M).r d
  | .middleIndividual M, E =>
      DecompGateAt (blockPrimes bOf b) M.hne (paperComponents E.down.toDC) (frameI In M).r d
  | .middleCoherent M, E =>
      DecompGateAt (blockPrimes bOf b) M.hne (paperComponents E.down.toDC) (frameC In M).r d

/-- **`SpecPrime` from `SpecDecomp`** (`primeInputs_of_decomp`, the block primes being
`≡ 3 (mod 4)` and `≥ Q₃ ≥ 19`). -/
theorem specPrime_of_decomp {b : Blk} {d : ℝ} :
    (S : PaperBlockSpec bOf b) → (E : SignedSpec hW S) → SpecDecomp hW In d S E →
      SpecPrime hW In d S E
  | .upper _, _, _ => trivial
  | .middleUniform _, _, ⟨_, _, _, D, G⟩ => primeInputs_of_decomp _ _
      (fun i => (blockPrimes_mod_ge b i).1) (blockPrimes_ge19 b) D G
  | .middleIndividual _, _, ⟨_, _, _, D, G⟩ => primeInputs_of_decomp _ _
      (fun i => (blockPrimes_mod_ge b i).1) (blockPrimes_ge19 b) D G
  | .middleCoherent _, _, ⟨_, _, _, D, G⟩ => primeInputs_of_decomp _ _
      (fun i => (blockPrimes_mod_ge b i).1) (blockPrimes_ge19 b) D G

end Paper

section Main

open Sarkozy.BlockSpecPaper
open Sarkozy.AnalyticCells (f1Cell)
open Sarkozy.MainFinalF1 (specF analyticInputs)
open Sarkozy.MainFinalF1c (ComparisonPartsTC)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {A : PaperAnalyticInputs f1Cell}

/-- **The prime decompositions and gates at every middle block** of the F1 data, at the paper's
side `paperSide i` of the piece. 1 field. *Hypothesis*: `lem:old-f-law`(f),
`prop:signed-bounds`(c) at every prime, and the numerical gates. -/
structure SignedDecompInputs (C : ComparisonPartsTC hW hMR hFour A) : Prop where
  decomp : ∀ b i, blockSite b = .inl i →
    SpecDecomp hW (paperIn f1Cell) (paperSide i) (specF hW A b) (C.blk b)

/-- **A constructor of SGA's `SignedPrimeInputs`** (the field `SGp` of `main_goal_f1i`) from the
prime decompositions and gates (`specPrime_of_decomp`). -/
theorem SignedDecompInputs.toPrime {C : ComparisonPartsTC hW hMR hFour A}
    (G : SignedDecompInputs C) : SignedPrimeInputs C where
  prime b i hb := specPrime_of_decomp hW (paperIn f1Cell) (specF hW A b) (C.blk b)
    (G.decomp b i hb)

end Main

end Sarkozy.PrimeGram
