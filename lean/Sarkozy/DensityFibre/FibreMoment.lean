module

public import Sarkozy.EnvelopeEnergiesPaper.SharpFirstCoupled
public import Sarkozy.DensityFibre.MomentAlgebra

@[expose] public section

/-!
# `Sh.fibre`: the fibre-moment input `CoupledFibreMoment` from the square-step models

K2's field `Sh.fibre` (B5's `SharpFirstCoupledInputs.fibre`) asks, at every least
counterexample and for every term `f` of the coupled expansion of `lem:sharp-first`,
`CoupledFibreMoment`:
`(E_q Z(q)^{1/θ})^θ ≤ (∏_{𝔟 ∈ E} sel_𝔟)(1 + ε_L) Y + r`, with
`(∏ w) r ≤ (∏ m) c₁ L^{-σ} α`.
Here `q` runs over the labels of the term's atoms `E`, and `Z(q) = Z_{μ_𝒮}(F_A(q, ·))` is the
outside energy of the actual fibre of the lift.

The paper's proof (`prop:density:production`, with `prop:record:density-structured`,
`lem:record:fibre-scale`, `lem:record:density-dc`) has three steps:
1. **Model.** The fibre energy of the square-step model satisfies
   `Z̃(q) ≤ (1 + u_L) C L^{-a} R_E^a α_f(q)^θ`. This is `lem:record:fibre-scale`(b)–(d) with the
   restoration (c) and the hypothesis on smaller scales; formally it is
   `Structured.changed_slot_bound_paper` on the cyclic coordinates at `D₀ = 1`, `I = [N]`.
2. **Comparison.** The actual fibres differ from the models on average by
   `E_q |Z(q) − Z̃(q)| ≤ C_dc N^{-γβ/2+72δ} α` (`lem:record:density-dc`, first display, with the
   diagonal uniform `ρ`).
3. **Mean.** The fibre densities average to the density: `E_q α_f(q) = α`. This is proved here
   (`coupledMean_termFibreDensity`).

This file:
* defines the fibre density `termFibreDensity` of a term at the paper's objects. The residues of
  `x` at the term's atoms are the block residues (`blockResidue`), and
  `α_f(q) = (D_E/N) #{x ∈ A : x ↦ q}` with `D_E = #X_E`;
* proves **`coupledMean_termFibreDensity`**: `E_q α_f(q) = α`;
* proves **`coupledFibreMoment_of_model`**: one term's `CoupledFibreMoment` from a model family
  `Z̃` with the pointwise bound, the weighted averaged difference and the price. The step at
  `θ > 1` is `DensityFibre.fibre_moment_le_of_model`;
* defines **`FibreModelInputs`**, the labelled inputs 1 and 2 at the least counterexamples
  (`hmod`, `hdc`), and proves **`FibreModelInputs.fibre`**, which is exactly the type of K2's
  field `Sh.fibre` with `θ = ϑ = densityExponent` and `ε_L = (1 + η_L)^{ϑ-1}(1 + u_L) − 1`
  (`ε_L → 0` proved).

B5's `coupledFibreMoment_of_fibres` is the special case `Z̃ = Z` (`FibreModelInputs.ofActual`).
It asks the pointwise model bound for the actual fibres, which the paper does not prove; the
actual fibres carry characters of conductor above `H`.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.DensityFibre

open Sarkozy.EnvelopeEnergiesPaper Sarkozy.EnvelopeInputsBlock
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame
open Sarkozy.IndexSupport Sarkozy.Functional Sarkozy.TheoremC Sarkozy.Structured
  Sarkozy.PaperFrame Sarkozy.Comparison Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
  Sarkozy.DensityMoments Sarkozy.DensityUpgrade Sarkozy.FourierArithmetic

/-! ## The fibre densities and their mean -/

section Mean

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- The fibre density for a residue map `res : ℤ → Q`: `α_f(q) = (#Q/N) #{x ∈ A : res x = q}`. -/
noncomputable def fibreDensityOf (res : ℤ → Q) (N : ℕ) (A : Finset ℤ) (q : Q) : ℝ :=
  ((Fintype.card Q : ℝ) / N) * ((A.filter fun x => res x = q).card : ℝ)

theorem fibreDensityOf_nonneg (res : ℤ → Q) (N : ℕ) (A : Finset ℤ) (q : Q) :
    0 ≤ fibreDensityOf res N A q := by
  unfold fibreDensityOf
  positivity

/-- **The fibre densities average to the density** (`prop:record:density-structured`, the mean of
the fibre densities; `lem:record:density-dc`, "the class `𝔞(z)` is uniform"): for any residue map,
`E_q α_f(q) = #A/N`. -/
theorem coupledMean_fibreDensityOf (res : ℤ → Q) (N : ℕ) (A : Finset ℤ) :
    coupledMean (fibreDensityOf res N A) = density N A := by
  rcases isEmpty_or_nonempty Q with hQ | hQ
  · -- no labels: `A` is empty, since every `x ∈ A` has a label
    have hA : A = ∅ := by
      ext x
      simp only [Finset.notMem_empty, iff_false]
      intro _
      exact hQ.false (res x)
    subst hA
    unfold coupledMean density
    simp
  · have hcard : (0 : ℝ) < Fintype.card Q := by exact_mod_cast Fintype.card_pos
    have hsum : ∑ q : Q, ((A.filter fun x => res x = q).card : ℝ) = A.card := by
      have h := Finset.card_eq_sum_card_fiberwise (s := A) (t := (univ : Finset Q)) (f := res)
        (fun x _ => mem_univ (res x))
      rw [h]
      push_cast
      rfl
    unfold coupledMean fibreDensityOf density
    rw [← Finset.mul_sum, hsum]
    field_simp

end Mean

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

section Residues

variable (m₀ blk p)

/-- The residue of an integer at an atom: its residues modulo the primes of a prefix block, or
modulo the tail prime. -/
noncomputable def blockResidue (L : ℕ) (x : ℤ) : ∀ b : BlockAtom Bk J L, BlockLabel m₀ blk p L b
  | .inl β => integerResidue (blockModuli m₀ blk β) x
  | .inr j => (x : ZMod (p L j))

end Residues

section Term

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)

/-- The residues of `x` at the atoms of a term, as (sharp labels, spectator labels). -/
noncomputable def termResidue (f : ∀ b, CPiece D L b) (x : ℤ) :
    SharpLabels D L f × SpecLabels D L f :=
  (fun b => blockResidue m₀ blk p L x b.1.1, fun b => blockResidue m₀ blk p L x b.1.1)

open scoped Classical in
/-- **The fibre density of a term** (`lem:record:fibre-scale`, `α_f` at `D₀ = 1`, `I = [N]`):
`α_f(q) = (D_E/N) #{x ∈ A : x ≡ q at the atoms of E}`, with `D_E = #X_E`. -/
noncomputable def termFibreDensity (A : Finset ℤ) (f : ∀ b, CPiece D L b)
    (q : SharpLabels D L f × SpecLabels D L f) : ℝ :=
  fibreDensityOf (termResidue D L f) (blockScale * L) A q

omit [DecidableEq P] in
theorem termFibreDensity_nonneg (A : Finset ℤ) (f : ∀ b, CPiece D L b)
    (q : SharpLabels D L f × SpecLabels D L f) : 0 ≤ termFibreDensity D L A f q := by
  classical
  exact fibreDensityOf_nonneg _ _ _ _

omit [DecidableEq P] in
/-- **The mean of the fibre densities of a term is the density** `α = #A/N`. -/
theorem coupledMean_termFibreDensity (A : Finset ℤ) (f : ∀ b, CPiece D L b) :
    coupledMean (termFibreDensity D L A f) = density (blockScale * L) A := by
  classical
  exact coupledMean_fibreDensityOf _ _ _

omit [DecidableEq P] in
/-- **One term's `CoupledFibreMoment` from a model family** (`prop:density:production`, fibre
step at `θ ≥ 1`). The inputs are:
* the model bound `Z̃(q) ≤ K α_f(q)^θ` (`hmod`);
* the price `(1 + η)^{θ-1} K α^θ ≤ (∏_{𝔟 ∈ E} sel_𝔟)(1 + ε) Y` (`hprice`);
* the weighted averaged difference `(∏ w) (1 + 1/η)^{θ-1} E_q |Z(q) − Z̃(q)| ≤ (∏ m) c₁ L^{-σ} α`
  (`hdc`, `lem:record:density-dc`).

The remainder of `CoupledFibreMoment` is `r = (1 + 1/η)^{θ-1} E_q |Z − Z̃|`. -/
theorem coupledFibreMoment_of_model (A : Finset ℤ) (f : ∀ b, CPiece D L b) {θ ε c₁ K η : ℝ}
    (hθ : 1 ≤ θ) (hη : 0 < η) (hK : 0 ≤ K) (Zt : SharpLabels D L f × SpecLabels D L f → ℝ)
    (hmod : ∀ q, Zt q ≤ K * termFibreDensity D L A f q ^ θ)
    (hprice : (1 + η) ^ (θ - 1) * (K * density (blockScale * L) A ^ θ) ≤
      (∏ b ∈ termAtoms D L f, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
        ((1 + ε) * D.Y L A))
    (hdc : (∏ b, cpieceW D L b (f b)) * ((1 + 1 / η) ^ (θ - 1) *
        coupledMean (fun q : SharpLabels D L f × SpecLabels D L f =>
          |fibreEnergy D L A f q.1 q.2 - Zt q|)) ≤
      (∏ b, cpieceM D L b (f b)) * remainder c₁ L A) :
    CoupledFibreMoment D L A f θ ε c₁ := by
  refine ⟨(1 + 1 / η) ^ (θ - 1) * coupledMean (fun q : SharpLabels D L f × SpecLabels D L f =>
    |fibreEnergy D L A f q.1 q.2 - Zt q|), ?_, hdc⟩
  have hmain := fibre_moment_le_of_model
    (Z := fun q : SharpLabels D L f × SpecLabels D L f => fibreEnergy D L A f q.1 q.2)
    (fun q => fibreEnergy_nonneg L A f q.1 q.2) (termFibreDensity_nonneg D L A f) hK hθ hη hmod
  rw [coupledMean_termFibreDensity] at hmain
  linarith

end Term

/-! ## The inputs at the least counterexamples -/

/-- `Q C L A` at every least normalized counterexample `(L, A)` of every sufficiently large scale,
for every induction constant `C ≥ 1`, with `C` visible to `Q` (`Param.AtCounterexamples` hides it).
The model bound of `lem:record:fibre-scale` uses the hypothesis on smaller scales with this `C`. -/
def AtCounterexamplesC (P : Params) (Y : ℕ → Finset ℤ → ℝ) (Q : ℝ → ℕ → Finset ℤ → Prop) :
    Prop :=
  ∀ᶠ L : ℕ in atTop, ∀ C : ℝ, 1 ≤ C →
    (∀ k : ℕ, 1 ≤ k → k < L → Param.EnergyUpperBoundAt P Y C k) →
    ∀ A : Finset ℤ, Admissible (P.blockScale * L) A →
      C * (L : ℝ) ^ (-P.decay) * density (P.blockScale * L) A ^ P.densityExponent < Y L A →
      Q C L A

/-- **The fibre inputs of `Sh.fibre`, as the paper proves them** (`prop:density:production`).
* `η → 0`: the parameter of the convexity split at `ϑ > 1` (`η_L = L^{-κ}` with
  `κ(ϑ − 1) ≤ γβ/2 − 72δ − σ`);
* `u → 0`: the scale term `u_L` of `lem:scale-conditions` (`λ^{72} ≤ 1 + u_L`);
* `Zt`: the model fibre energies `Z̃_{L,A,f}(q)`. In the paper this is
  `Z_{μ_𝒮}(g̃_q)`, the energy of the square-step model of `lem:record:fibre-scale`(b) at
  `D₀ = 1`, `I = [N]`, at the fibre `q` of the term's atoms `E`;
* `price`: the price `R_E^a = sq(D_E)^a` of the term, at most `∏_{𝔟 ∈ E} sel_𝔟` (`hprice`;
  `sq(p)^a = p^{2a}` at a tail prime, `sq(D_β)^a ≤ selPre β` at a block);
* `hmod` (**`lem:record:fibre-scale`(b)–(d), restoration (c), the hypothesis on smaller scales**;
  formally `Structured.changed_slot_bound_paper` with `C₀ = C`):
  `Z̃(q) ≤ (1 + u_L) C L^{-a} R_E^a α_f(q)^ϑ` for every term and fibre. *Hypothesis.*
* `hdc` (**`lem:record:density-dc`, first display, diagonal uniform `ρ`**, weighted by the
  term's coefficients): `(∏ w)(1 + 1/η_L)^{ϑ-1} E_q |Z(q) − Z̃(q)| ≤ (∏ m) c₁ L^{-σ} α`.
  *Hypothesis.* With `dconst ≤ 2` the weights can be dropped (`prod_cpieceW_le_prod_cpieceM`).

The mean `E_q α_f = α` is proved (`coupledMean_termFibreDensity`), and so is the step at `ϑ > 1`
(`fibre_moment_le_of_model`). -/
structure FibreModelInputs (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) where
  η : ℕ → ℝ
  hη : ∀ L, 0 < η L
  hηt : Tendsto η atTop (𝓝 0)
  u : ℕ → ℝ
  hu : ∀ L, 0 ≤ u L
  hut : Tendsto u atTop (𝓝 0)
  c₁ : ℝ
  hc₁ : 0 ≤ c₁
  Zt : ∀ L, Finset ℤ → ∀ f : (∀ b, CPiece D L b), SharpLabels D L f × SpecLabels D L f → ℝ
  price : ∀ L, (∀ b, CPiece D L b) → ℝ
  hprice0 : ∀ L f, 0 ≤ price L f
  hprice : ∀ L f, price L f ≤
    ∏ b ∈ termAtoms D L f, TheoremCBlock.selectionFactor a p D.S.selPre L b
  hmod : AtCounterexamplesC (Params.ofDecay a) D.Y (fun C L A => ∀ f q,
    Zt L A f q ≤ (1 + u L) * C * (L : ℝ) ^ (-a) * price L f *
      termFibreDensity D L A f q ^ densityExponent)
  hdc : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ f : (∀ b, CPiece D L b),
    (∏ b, cpieceW D L b (f b)) * ((1 + 1 / η L) ^ (densityExponent - 1) *
      coupledMean (fun q : SharpLabels D L f × SpecLabels D L f =>
        |fibreEnergy D L A f q.1 q.2 - Zt L A f q|)) ≤
    (∏ b, cpieceM D L b (f b)) * remainder c₁ L A)

namespace FibreModelInputs

variable {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}

theorem one_le_densityExponent : (1 : ℝ) ≤ densityExponent := densityExponent_bounds.1

/-- The relative error `ε_L = (1 + η_L)^{ϑ-1}(1 + u_L) − 1`. -/
noncomputable def ε (I : FibreModelInputs D) (L : ℕ) : ℝ :=
  (1 + I.η L) ^ (densityExponent - 1) * (1 + I.u L) - 1

omit [DecidableEq P] in
theorem ε_nonneg (I : FibreModelInputs D) (L : ℕ) : 0 ≤ I.ε L := by
  unfold ε
  have h1 : 1 ≤ (1 + I.η L) ^ (densityExponent - 1) :=
    Real.one_le_rpow (by linarith [I.hη L]) (by linarith [one_le_densityExponent])
  have h2 : 1 ≤ 1 + I.u L := by linarith [I.hu L]
  nlinarith

omit [DecidableEq P] in
theorem tendsto_ε (I : FibreModelInputs D) : Tendsto I.ε atTop (𝓝 0) := by
  have h1 : Tendsto (fun L => (1 + I.η L) ^ (densityExponent - 1)) atTop (𝓝 1) := by
    have hc : Tendsto (fun L => 1 + I.η L) atTop (𝓝 (1 + 0)) := tendsto_const_nhds.add I.hηt
    rw [add_zero] at hc
    have := hc.rpow_const (p := densityExponent - 1) (Or.inl one_ne_zero)
    rwa [Real.one_rpow] at this
  have h2 : Tendsto (fun L => 1 + I.u L) atTop (𝓝 (1 + 0)) := tendsto_const_nhds.add I.hut
  rw [add_zero] at h2
  have h3 := (h1.mul h2).sub_const 1
  simp only [mul_one, sub_self] at h3
  exact h3

omit [DecidableEq P] in
/-- **`Sh.fibre` from the model inputs**: the type of B5's `SharpFirstCoupledInputs.fibre` and of
K2's `SharpParts2.fibre`, at `θ = ϑ` and `ε_L = (1 + η_L)^{ϑ-1}(1 + u_L) − 1`. It holds at every
term of the coupled expansion, and in fact at every `f`. -/
theorem fibre (I : FibreModelInputs D) :
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∀ σ : (∀ b, Option (D.FS.Ib L b)), σ ≠ (fun _ => none) → ∀ j,
        1 ≤ countVec (D.FS.tag L) σ j → ∀ f : (∀ b, CPiece D L b),
        (∀ b, cpieceCoef D L σ j b (f b) ≠ 0) →
          CoupledFibreMoment D L A f densityExponent (I.ε L) I.c₁) := by
  filter_upwards [I.hmod, I.hdc] with L hmodL hdcL
  intro C hC hind A hA hY _ _ _ _ f _
  have hmod := hmodL C hC hind A hA hY
  have hdc := hdcL C hC hind A hA hY
  have hY0 := Param.counterexample_pos (Params.ofDecay a) hC hY
  set α := density (blockScale * L) A
  set K := (1 + I.u L) * C * (L : ℝ) ^ (-a) * I.price L f with hKdef
  have hu1 : 0 ≤ 1 + I.u L := by linarith [I.hu L]
  have hK : 0 ≤ K :=
    mul_nonneg (mul_nonneg (mul_nonneg hu1 (by linarith)) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (I.hprice0 L f)
  refine coupledFibreMoment_of_model D L A f one_le_densityExponent (I.hη L) hK (I.Zt L A f)
    (fun q => hmod f q) ?_ (hdc f)
  -- the price: `(1 + η)^{ϑ-1} K α^ϑ ≤ (1 + η)^{ϑ-1}(1 + u) R^a Y ≤ (∏ sel)(1 + ε) Y`
  have hcex : C * (L : ℝ) ^ (-a) * α ^ densityExponent < D.Y L A := hY
  have hη1 : 0 ≤ (1 + I.η L) ^ (densityExponent - 1) :=
    Real.rpow_nonneg (by linarith [I.hη L]) _
  have hpr := I.hprice L f
  have hpr0 := I.hprice0 L f
  have hsel0 : 0 ≤ ∏ b ∈ termAtoms D L f, TheoremCBlock.selectionFactor a p D.S.selPre L b :=
    le_trans hpr0 hpr
  have e : K * α ^ densityExponent =
      ((1 + I.u L) * I.price L f) * (C * (L : ℝ) ^ (-a) * α ^ densityExponent) := by
    rw [hKdef]
    ring
  have hεdef : 1 + I.ε L = (1 + I.η L) ^ (densityExponent - 1) * (1 + I.u L) := by
    unfold ε
    ring
  rw [e, hεdef]
  have hA1 : 0 ≤ (1 + I.u L) * I.price L f := mul_nonneg hu1 hpr0
  calc (1 + I.η L) ^ (densityExponent - 1) *
        ((1 + I.u L) * I.price L f * (C * (L : ℝ) ^ (-a) * α ^ densityExponent))
      ≤ (1 + I.η L) ^ (densityExponent - 1) * ((1 + I.u L) * I.price L f * D.Y L A) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcex.le hA1) hη1
    _ ≤ (1 + I.η L) ^ (densityExponent - 1) *
          ((1 + I.u L) * (∏ b ∈ termAtoms D L f,
            TheoremCBlock.selectionFactor a p D.S.selPre L b) * D.Y L A) := by
        refine mul_le_mul_of_nonneg_left ?_ hη1
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpr hu1) hY0.le
    _ = _ := by ring

end FibreModelInputs

end Sarkozy.DensityFibre
