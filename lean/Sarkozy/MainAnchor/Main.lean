module

public import Sarkozy.LedgerAnchor.All
public import Sarkozy.TheoremCParam.All
public import Sarkozy.TargetDLK
public import Sarkozy.CancellationSteps.Final
public import Sarkozy.EnvelopeInputs.GroupFacts

@[expose] public section






open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.MainAnchor

open Sarkozy.TheoremC Sarkozy.TheoremCParam Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.Comparison (PrimitiveLedger)
open Sarkozy.Param (Params)
open Sarkozy.LedgerAnchor (AnchorBounds)
open Sarkozy.Cancellation Sarkozy.CancellationSteps Sarkozy.Mixing Sarkozy.PaperFrame
  Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport

/-- The prime powers of the index coordinates are pairwise coprime ((CP0)(d)): their primes are
distinct primes (`StandingData.pr_prime`, `StandingData.pr_inj`). -/
theorem index_coprime {a : ℝ}
    {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
    {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
    [∀ L j, NeZero (p L j)]
    {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
    {E : Type} [Fintype E] [DecidableEq E] (D : TheoremCParam.ComparisonData a m₀ p pr h E) :
    Pairwise (Nat.Coprime on fun q => pr q ^ h q) := by
  intro q q' hqq'
  have hne : pr q ≠ pr q' := fun e => hqq' (D.S.pr_inj e)
  exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (D.S.pr_prime q) (D.S.pr_prime q')).mpr hne)

/-- **Everything that remains between the tree and the target at `a₀`.**

Parameters: the shape of the paper's construction (`def:construction`): the prefix moduli `m₀`,
the tail primes `p L`, the prime powers `pr q ^ h q` of the index coordinates, and the query set
`E`. Fields, in four groups: the data, the class bounds, the ledger, the analytic inputs. Each
field names its paper label and its status (owner, or "open"). -/
structure PartVObligations
    {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
    {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
    [∀ L j, NeZero (p L j)]
    {P : Type} [Fintype P] [DecidableEq P] (pr h : P → ℕ) [∀ q, NeZero (pr q ^ h q)]
    (E : Type) [Fintype E] [DecidableEq E] where
  -- The data (Part V)
  /-- **The comparison data (CP0)–(CP8) of the paper's construction at the price exponent `a₀`**
  (`def:cp0` … `def:cp8`, `def:construction`): standing data, reference (CP1), first stage
  (CP2), bracket (CP3), comparison law (CP4), matching envelopes (CP6), mean credit (CP7),
  summability (CP8), with every price total taken with the selection factors `p^{2a₀}`.
  *Open* (Part V). Partial inputs elsewhere: the square-clique prefix law (`Construction/`), the
  tail mixing (R4) for the reference's `mixing` field (`TraceMixing/`), the prefix moments
  (`DensityMoments/`, M1). WP-FI reviewed the fields against the paper (no contradiction); no
  model is built. -/
  D : TheoremCParam.ComparisonData Params.anchorDecay m₀ p pr h E
  /-- Six queries (`def:construction`). *Open* (Part V; a choice). -/
  hcard : Fintype.card E = 6
  -- The class bounds (Part V)
  /-- **The (CP5) class bounds** (`def:cp5`) of the comparison law at `a₀`: the paper's 16
  classes `(n, m)` with their class polynomials. *Open* (Part V). -/
  CB : TheoremCParam.ClassBounds Params.anchorDecay m₀ p D.CL
  /-- The energy constant `𝓔` of the closing (`thm:comparison`, classes form). -/
  𝓔 : ℝ
  /-- **The complete polynomial with class bounds is at most `𝓔`** at every scale (`def:cp5`,
  `thm:comparison`; the class savings `D_{n,m}` of the ledger enter here). *Open* (Part V,
  certificate family F15 for the class algebra and gates). -/
  hΨ : ∀ L, ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
    (if CB.cls L ω = none then D.B * monomial (D.CL.π L) ω else CB.phi L ω) ≤ 𝓔
  /-- The class bounds are robust with nonnegative remainders (`def:robust`, (CP5)). *Open*
  (Part V). -/
  hCB : CB.RobustNonneg
  -- The ledger at `a₀` (Part V certificates)
  /-- The primitive totals of the four-routes closing at `a₀`. -/
  l : PrimitiveLedger
  /-- **The outward ledger bounds at `a₀`** (`tab:four-routes-ledger`, `cert:four-routes-closing`
  at `a₀`), formalization-friendly variant (R1: F1, F2 replaced under H2′, F4 dropped;
  `LedgerAnchor.AnchorBounds`, `Θ < 0.95836` proved from them). *Open*: each entry is a Part V
  certificate (families F1, F2, F3, F5–F15; see the report's ledger table); the entries with
  upper parts rest on F3. -/
  hl : AnchorBounds l
  /-- `B ≤` the ledger's `B` ((CP3), `def:closing-quantities`). *Open* (Part V). -/
  hB : D.B ≤ l.B
  /-- `L₀ ≤` the ledger's `L₀` ((CP2)). *Open* (Part V). -/
  hL₀ : D.L₀ ≤ l.L₀
  /-- `T ≤` the ledger's `T` ((CP6)). *Open* (Part V). -/
  hT : D.ME.T ≤ l.T
  /-- `R_I ≤` the ledger's `R_I` (`cert:index-moment`, family F2). *Open* (Part V). -/
  hR : D.S.index.R_I ≤ l.R_I
  /-- `S + A ≤` the ledger's `S + A` ((CP4)). *Open* (Part V). -/
  hSA : D.CL.S + D.CL.A ≤ l.S + l.A
  /-- `𝓔 ≤` the ledger's `E = B(e^S cosh A − 1) − D` (the savings `D`: class savings and
  `D_var`). *Open* (Part V). -/
  h𝓔 : 𝓔 ≤ l.E
  /-- **The mean credit pays the joint-closing allocations** (`cor:joint-closing`,
  `prop:joint-middle-mean`, `prop:joint-upper-mean`): `m ≥ m₁ + 2⁶(Δ_α + Δ_M + Δ_O + Δ_K + Δ_u
  − R_u)`. *Open* (Part V). -/
  hm : l.m₁ + 64 * ((l.deltaAlpha + l.deltaMatching + l.deltaOdd + l.deltaEven) +
    l.deltaUpper - l.upperError) ≤ D.MC.m
  -- The analytic inputs of Theorem C at `a₀`
  /-- **(E1), the envelope bound with nonnegative remainders** (`lem:bracket-energy` at `ϑ`, via
  `prop:density:production`). *Open at `a₀`.* I1 (`EnvelopeInputs`) proves the plain
  `EnvelopeBound` at the record exponent, for `TheoremC.ComparisonData`, from folded-piece
  density-structured bounds (`envelopeBound_of_foldedPieces`, `_uniform`). **At `a₀`** it is
  reduced to WP-R's per-term bounds with nonnegative remainders by
  `TheoremCParam.Structured.envelopeBoundNonneg_of_terms` (fifth package); the per-term bounds
  at `a₀`, and I1's folded route at `a₀`, are open. -/
  hE1 : D.EnvelopeBoundNonneg
  /-- **The sharp first-stage terms** (`lem:sharp-first` with `lem:record:folded-energy`, at
  `ϑ`). *Open at `a₀`.* I1 proves them at the record exponent from folded pieces
  (`EnvelopeInputs.sharpFirstTerms_of_foldedPieces`, `_uniform`); WP-R's
  `Structured.sharpFirstTerms_of_folded` likewise. At `a₀`, WP-R's reduction is
  `TheoremCParam.Structured.sharpFirstTerms_of_folded` (fifth package); its inputs are open. -/
  hSF : D.SharpFirstTerms
  /-- **The fixed-interval envelope energies** (`lem:envelope-energy`, fixed interval). *Open at
  `a₀`.* I1 proves them at the record exponent
  (`EnvelopeInputs.fixedIntervalEnvelopeEnergies_of_inputs`, `_of_conductor`); WP-R's
  `Structured.fixedIntervalEnvelopeEnergies_of_terms`. At `a₀`, WP-R's reduction is
  `TheoremCParam.Structured.fixedIntervalEnvelopeEnergies_of_terms`; its inputs are open. -/
  hfix : D.FixedIntervalEnvelopeEnergies (index_coprime D)
  /-- **The envelope energies** (`lem:envelope-energy`). *Open at `a₀`.* I1 proves them at the
  record exponent (`EnvelopeInputs.envelopeEnergies_of_inputs`, `_of_conductor`); WP-R's
  `Structured.envelopeEnergies_of_terms`. At `a₀`, WP-R's reduction is
  `TheoremCParam.Structured.envelopeEnergies_of_terms`; its inputs are open. -/
  henv : D.EnvelopeEnergies (index_coprime D)
  -- `lem:record:density-can`, through D1's reduction
  -- `CancellationSteps.densityCancellation_of_core`
  -- (the statement does not depend on the exponent, so the reduction applies at `a₀` as it
  -- stands; D1's file is in progress, and these fields are its current hypotheses).
  /-- The threshold `P₅ ≥ 64` of (R4) (`hyp:record:reference`). *Open* (Part V; a choice). -/
  h64 : 64 ≤ D.R.P5
  /-- The constant `C₂` of `lem:record:lift-moments`(c) (Step 2). -/
  C₂ : ℝ
  hC₂ : 0 ≤ C₂
  /-- The uniformity constant `M₀'` of the fibre classes (Step 3). -/
  Mfib : ℝ
  hMfib : 0 ≤ Mfib
  /-- The constant `C_ε` of the `L²` bound (Step 3). -/
  Cε : ℝ
  hCε : 0 ≤ Cε
  /-- The scale from which Steps 2–3 hold. -/
  Lstep : ℕ
  /-- The prefix primes are distinct (`def:cp0`). *Open* (Part V; elementary). With `hne` it gives
  the pairwise coprimality of the atom moduli by I1's `EnvelopeInputs.standing_pairwise_coprime`
  (supplied in `main_anchor`). -/
  hppinj : Function.Injective D.S.pp
  /-- No prefix prime is a tail prime (`def:construction`). *Open* (Part V; elementary). -/
  hne : ∀ L i j, D.S.pp i ≠ p L j
  /-- Every prime `ℓ ≤ N^{1/40}` divides `M₀` or a prefix modulus or is a tail prime
  (`lem:scale-conditions`(v) and the choice of the atoms). *Open* (Part V; elementary). -/
  hcover : ∀ L : ℕ, ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ (1 / 40 : ℝ) →
    ℓ ∣ modulus pr h ∨ (∃ i, ℓ ∣ m₀ i) ∨ ∃ j, p L j = ℓ
  /-- **Step 2 and the analytic clauses of Step 3 of `lem:record:density-can`**, at every query
  at every scale `L ≥ Lstep`: `LiftMoments` (`lem:record:lift-moments`(c)) at the encoded data,
  and `FibreCore` (the square class from (b), the uniformity of `𝔞₁`, the `L²` bound) at every
  low support. *Open*: D1 (`CancellationSteps`, in progress) and WP-K; the encoding (Step 1),
  the intervals, the fibre formulas and the structural clauses are proved there. -/
  hSteps : haveI : ∀ L j, Fact (p L j).Prime := fun L j => ⟨D.S.p_prime L j⟩
    ∀ L : ℕ, Lstep ≤ L → ∀ A : Finset ℤ, Admissible (blockScale * L) A →
    ∀ ϱ : ∀ b : PaperAtom J L, FiniteLaw (Slot → AtomLabel m₀ p L b),
    (∀ b, HasUniformMarginals (ϱ b)) → ∀ (u v : Slot) (huv : u ≠ v),
    ∀ ha : (∀ j : J L, D.R.P5 ≤ p L j → PairUniformOmega (q := p L j) (ϱ (some j)) u v ∧
      Sarkozy.Mixing.IsGammaMixing (p L j) Sarkozy.AnalyticStage.γ (ϱ (some j)) {u, v}),
    (∀ b : PaperAtom J L, (∀ j, b = some j → p L j < D.R.P5) → ∀ z, (ϱ b).weight z ≠ 0 →
      AcceptedPair m₀ p D.S.pp D.S.ep L b (z u) (z v)) →
    ∀ (bI : ZMod blockScale) (s r : ZMod (modulus pr h)), bI ≠ 0 →
    IsNonvanishingSquareClass (modulus pr h) r →
    ∀ G : Slot → (∀ b, AtomLabel m₀ p L b) → ℝ,
    G u = indexInputAt m₀ p pr h L A (bI, s) →
    G v = indexInputAt m₀ p pr h L A (bI + 1, s + r) →
    (∀ w, w ≠ u → w ≠ v → IsQueryInput m₀ p pr h L A (G w)) →
      LiftMoments (tailQ p L D.R.P5)
        (FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L D.R.P5 b} => ϱ i.1))
        (encKappa m₀ p L D.R.P5 ϱ huv (fun k => (ha k.1 k.2).1)) (encF m₀ p L D.R.P5 G u)
        (encF m₀ p L D.R.P5 G v) (encW m₀ p L D.R.P5 G u v) (blockScale * L) C₂
        (density (blockScale * L) A) ∧
      ∀ U : TailIdx p L D.R.P5 → Bool,
        supportConductor (tailQ p L D.R.P5) U ≤
          ((blockScale * L : ℕ) : ℝ) ^ Cancellation.stageTan →
        FibreCore m₀ p L D.R.P5 U s (s + r) u v
          (FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L D.R.P5 b} => ϱ i.1))
          (encF m₀ p L D.R.P5 G u) (encF m₀ p L D.R.P5 G v) A (((bI.val : ℤ) - 1) * L + 1)
          ((bI.val : ℤ) * L) (blockScale * L) (L : ℝ) (blockScale : ℝ) Mfib Cε
          (density (blockScale * L) A)
  /-- **The unit mixed `L³⁶` bound of the large-prime reference laws** (`lem:density:global-moment`,
  tail part). *Open for the paper's tail laws*, which are mixtures over the upper-reference
  components (Part V). WP-P proves it for a single fixed graph law from `Target.Weil` and a
  correlation bound (`TailMoment.graphLaw_unit_mixed_L36`). -/
  hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (D.R.μp q) 36 1

/-- **`lem:record:density-can` for the data, from D1's inputs**
(`CancellationSteps.densityCancellation_of_core`):
the injectivity of the tail primes comes from the standing data (`StandingData.p_inj`), and the
pairwise coprimality of the atom moduli from I1's `EnvelopeInputs.standing_pairwise_coprime`. -/
theorem densityCancellation
    {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
    {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
    [∀ L j, NeZero (p L j)]
    {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
    {E : Type} [Fintype E] [DecidableEq E] (O : PartVObligations m₀ p pr h E) :
    DensityCancellation m₀ p pr h O.D.R.P5 O.D.S.pp O.D.S.ep := by
  have : ∀ L j, Fact (p L j).Prime := fun L j => ⟨O.D.S.p_prime L j⟩
  exact CancellationSteps.densityCancellation_of_core m₀ p pr h O.D.R.P5 O.D.S.pp O.D.S.ep
    O.D.S.p_inj O.h64 O.hC₂ O.hMfib O.hCε O.Lstep O.D.S.modulus_coprime
    (fun L i j hij => EnvelopeInputs.standing_pairwise_coprime O.D.S O.hppinj O.hne L hij)
    O.hcover O.hSteps

/-- **The assembly skeleton: the target at `a₀` from the literature inputs and the Part V
obligations.** Every square-difference-free `A ⊆ [1, N]` has `|A| ≤ C N^{1−ε′}`,
`ε′ = Target.epsAnchor = a₀/(72 − ϑ)`.

The literature inputs are not used yet (named `_h…`): no field of `PartVObligations` is
derived from them yet. They are listed so that the statement has the target's final form. -/
theorem main_anchor
    {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
    {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
    [∀ L j, NeZero (p L j)]
    {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
    {E : Type} [Fintype E] [DecidableEq E]
    (_hWeil : Target.Weil)
    (_hMovingRoot : Target.MovingRoot) (_hFourCycle : Target.FourCycle)
    (O : PartVObligations m₀ p pr h E) :
    Target.SarkozyBound Param.anchorSaving :=
  LedgerAnchor.ComparisonData.theoremC_classes_reduced_anchor_of_ledger O.D (index_coprime O.D) O.hl
    O.hcard
    O.D.B_nonneg O.hB O.hL₀ O.hT O.D.S.index.hR_I O.hR O.hSA O.hm O.CB O.h𝓔 O.hΨ O.hE1 O.hCB
    O.hSF (densityCancellation O) O.hfix O.henv O.hunit

end Sarkozy.MainAnchor
