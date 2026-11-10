module

public import Sarkozy.DensityFibre.ChoiceExpansion
public import Sarkozy.DensityFibre.CoupledAtoms
public import Sarkozy.EnvelopeEnergiesPaper.SharpFirstCoupled

@[expose] public section

/-!
# `lem:density:coupled` for one term of the expansion of a sharp-first difference

This is B5's `SharpFirstCoupledInputs.term_bound` redone for the pieces `HPiece` of
`DensityFibre.ChoiceExpansion`, with **slot-dependent inputs** (the revealed inputs of `envC`,
`fixC`). The tool is `DensityFibre.abs_multilinearIntegral_coupled_le_atoms`.

A term `φ` with nonzero coefficients at the tag `j` has three kinds of atoms:
* **sharp atoms**: whole differences `κ'_i − κ_i` of tag `j`, folded at the cut `c_j`;
* **spectators**: the positive records `κu_k`, `κ'_i`, `κ_i` and the selected increments `Q`;
* **outside**: the reference laws `μ`, off the term's atoms.

The inputs are:
* the per-record data of B5's `SharpFirstCoupledInputs`. These are `fold` (the sharp
  decomposition of `κ' − κ` with unit folded moments) and `mom`, `mom'` (unit mixed `L^{72/θ}` of
  `κ/κ(1)`, `κ'/κ'(1)`). For the paper's data they are proved (`FirstStageMoments.paper`);
* `momU`, `momQ`: unit mixed `L^{72/θ}` of the reserved records `κu_k` and of the increments
  `Q_𝔟` (`lem:density:coupled`, positive spectators; `lem:density:packets`), and `Q_𝔟 ≥ 0`;
* per term, the fibre-and-price input `HFibrePrice`: slot-dependent fibre weights with
  `Z_{μ_𝒮}(G_v(x ⊔ y ⊔ ·))^{1/72} ≤ b_v a_v(x, y)^{θ/72}` and `∏ b ∏ (E a)^{θ/72} ≤ P`. This is the
  analogue of field 23 for revealed inputs (`prop:density:production`).

* **`hterm_coupled_bound`**: `|E_φ| ≤ (∏_𝔟 W_{φ_𝔟}) P`. Here `W` is `1` for `μ`, the mass of a
  spectator, and `κ(1) d` for a sharp atom.
* `prod_hpieceW_sel_le`: `∏ W ∏_E sel ≤ (∏ g) ∏_f u_Q` at a term with nonzero coefficients,
  given `‖Q‖ sel ≤ u_Q` (the price of `Q`).
* **`hterm_of_fibrePrice`**: the per-term hypothesis `hterm` of `DensityFibre.SharpTerms`, on the
  cyclic coordinates, from `HFibrePrice` at `P = (∏_E sel)(1 + ε) K₀ + r` with
  `(∏ W) r ≤ r_φ`.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.DensityFibre

open Sarkozy.BracketEnergy
open Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame Sarkozy.RecordExpansion
open Sarkozy.IndexSupport Sarkozy.Functional Sarkozy.TheoremC Sarkozy.Structured
  Sarkozy.PaperFrame Sarkozy.Comparison Sarkozy.FourierArithmetic Sarkozy.DensityMoments
  Sarkozy.DensityUpgrade ReflectionCut

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

section Terms

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)

/-- Whether a piece is `μ`. -/
def hpieceIsMu (b : BlockAtom Bk J L) : HPiece D L b → Bool
  | .inl none => true
  | _ => false

/-- Whether a piece is a whole difference `κ' − κ`. -/
def hpieceIsSharp (b : BlockAtom Bk J L) : HPiece D L b → Bool
  | .inr (.inl (_, none)) => true
  | _ => false

/-- The record index of a whole difference. -/
def hpieceIdx (b : BlockAtom Bk J L) :
    (x : HPiece D L b) → hpieceIsSharp D L b x = true → D.FS.Ib L b
  | .inr (.inl (i, none)), _ => i
  | .inl _, hx => absurd hx (by simp [hpieceIsSharp])
  | .inr (.inl (_, some _)), hx => absurd hx (by simp [hpieceIsSharp])
  | .inr (.inr _), hx => absurd hx (by simp [hpieceIsSharp])

omit [DecidableEq P] in
theorem eq_of_hpieceIsSharp (b : BlockAtom Bk J L) (x : HPiece D L b)
    (hx : hpieceIsSharp D L b x = true) : x = .inr (.inl (hpieceIdx D L b x hx, none)) := by
  rcases x with (_ | k) | (⟨i, _ | t⟩ | _)
  · simp [hpieceIsSharp] at hx
  · simp [hpieceIsSharp] at hx
  · rfl
  · simp [hpieceIsSharp] at hx
  · simp [hpieceIsSharp] at hx

/-- The mass weight of a piece: `1` for `μ`, the mass of a positive record or of `Q`, and
`κ(1) d` for a whole difference. -/
noncomputable def hpieceW (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (b : BlockAtom Bk J L) : HPiece D L b → ℝ
  | .inl none => 1
  | .inl (some k) => mass (D.GB.κu L b k)
  | .inr (.inl (i, none)) => mass (D.FS.κ L b i) * D.FS.dconst L b i
  | .inr (.inl (i, some t)) => if t then mass (D.FS.κ' L b i) else mass (D.FS.κ L b i)
  | .inr (.inr _) => mass (Qb b)

/-- The atoms of a term (its non-`μ` pieces). -/
def hTermAtoms (φ : ∀ b, HPiece D L b) : Finset (BlockAtom Bk J L) :=
  univ.filter (fun b => hpieceIsMu D L b (φ b) = false)

/-- The sharp atoms of a term. -/
def hTermSharp (φ : ∀ b, HPiece D L b) : Finset {b // b ∈ hTermAtoms D L φ} :=
  univ.filter (fun b => hpieceIsSharp D L b.1 (φ b.1) = true)

/-- The outside law of a term: the reference laws off its atoms. -/
noncomputable def hTermOutside (φ : ∀ b, HPiece D L b) :
    FiniteLaw (Slot → ∀ b : {b // b ∉ hTermAtoms D L φ}, BlockLabel m₀ blk p L b.1) :=
  FiniteLaw.tensor (fun b => blockRefLaw blk p D.R.μ₀ D.R.μp L b.1)

/-- The labels of the sharp atoms of a term. -/
abbrev HSharpLabels (φ : ∀ b, HPiece D L b) : Type :=
  ∀ b : {b' // b' ∈ hTermSharp D L φ}, BlockLabel m₀ blk p L b.1.1

/-- The labels of the spectators of a term. -/
abbrev HSpecLabels (φ : ∀ b, HPiece D L b) : Type :=
  ∀ b : {b' // b' ∉ hTermSharp D L φ}, BlockLabel m₀ blk p L b.1.1

/-- **The fibre-and-price input of one term with slot inputs `G'`** (`lem:density:coupled`, the
fibre step; `prop:density:production` for the price): slot-dependent fibre weights `a_v ≥ 0`,
constants `b_v ≥ 0`, `Z_{μ_𝒮}(G'_v(x ⊔ y ⊔ ·))^{1/72} ≤ b_v a_v(x, y)^{θ/72}`, and
`∏_v b_v ∏_v (E a_v)^{θ/72} ≤ P`. -/
def HFibrePrice (φ : ∀ b, HPiece D L b) (G' : Slot → (∀ b, BlockLabel m₀ blk p L b) → ℝ)
    (θ Pr : ℝ) : Prop :=
  ∃ (av : Slot → HSharpLabels D L φ → HSpecLabels D L φ → ℝ) (bv : Slot → ℝ),
    (∀ v x y, 0 ≤ av v x y) ∧ (∀ v, 0 ≤ bv v) ∧
    (∀ v x y, coupledEnergyV (multilinearIntegral (signedIntegral (hTermOutside D L φ).weight))
        (fun w => G' v (joinLabels (hTermAtoms D L φ) (joinLabels (hTermSharp D L φ) x y) w)) ^
          (1 / (72 : ℝ)) ≤ bv v * av v x y ^ (θ / 72)) ∧
    (∏ v, bv v) * (∏ v, coupledMean
        (fun q : HSharpLabels D L φ × HSpecLabels D L φ => av v q.1 q.2) ^ (θ / 72)) ≤ Pr

omit [DecidableEq P] in
theorem eq_mu_of_not_mem_hTermAtoms (φ : ∀ b, HPiece D L b) (b : BlockAtom Bk J L)
    (hb : b ∉ hTermAtoms D L φ) : φ b = .inl none := by
  have hmu : hpieceIsMu D L b (φ b) = true := by simpa [hTermAtoms] using hb
  rcases hx : φ b with (_ | k) | (⟨i, _ | t⟩ | _)
  · rfl
  all_goals (rw [hx] at hmu; simp [hpieceIsMu] at hmu)

omit [DecidableEq P] in
theorem hTermOutside_weight (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (φ : ∀ b, HPiece D L b)
    (w : Slot → ∀ b : {b // b ∉ hTermAtoms D L φ}, BlockLabel m₀ blk p L b.1) :
    (hTermOutside D L φ).weight w =
      ∏ b : {b // b ∉ hTermAtoms D L φ}, lawDensity (hpieceK D L Qb b.1 (φ b.1))
        (fun v => w v b) := by
  unfold hTermOutside
  rw [Structured.tensor_weight]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [eq_mu_of_not_mem_hTermAtoms D L φ b.1 b.2]
  change _ = lawDensity (blockRefLaws m₀ blk p D.R.μ₀ D.R.μp L b.1) _
  rw [blockRefLaws_eq, lawDensity_signedIntegral_eq]

omit [DecidableEq P] in
theorem hTermOutside_positive (φ : ∀ b, HPiece D L b) {c : ReflectionCut Slot}
    (hc : IsFamilyCut c) : c.Positive (signedIntegral (hTermOutside D L φ).weight) := by
  unfold hTermOutside
  rw [FiniteLaw.signedIntegral_tensor]
  refine Positive.tensor fun b => ?_
  obtain ⟨b, hb⟩ := b
  rcases b with β | jj
  · exact D.R.rp₀ β c hc
  · exact D.R.rpp (p L jj) (D.S.p_prime L jj) c hc

omit [DecidableEq P] in
theorem hTermOutside_holder (φ : ∀ b, HPiece D L b) :
    coupledOutsideHolderV (multilinearIntegral (signedIntegral (hTermOutside D L φ).weight)) := by
  have hsr : SlotReflectionPositive (signedIntegral (hTermOutside D L φ).weight) :=
    fun c hc => hTermOutside_positive D L φ (isFamilyCut_of_sorting c hc)
  refine ⟨fun g => slot_diagonal_nonneg hsr g, fun g => ?_⟩
  have h := slot_signed_holder hsr g
  rw [card_slot_real]
  exact h

omit [DecidableEq P] in
/-- A spectator piece (neither `μ` nor a whole difference) is a nonnegative measure whose weight is
its mass, and it has the unit moment of its kind. -/
theorem hspectator_facts (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (hQ0 : ∀ b, IsNonneg (Qb b)) {θ : ℝ}
    (mom : ∀ b i, RecordMoment (D.FS.κ L b i) θ) (mom' : ∀ b i, RecordMoment (D.FS.κ' L b i) θ)
    (momU : ∀ b k, RecordMoment (D.GB.κu L b k) θ) (momQ : ∀ b, RecordMoment (Qb b) θ)
    (b : BlockAtom Bk J L) (x : HPiece D L b)
    (h1 : hpieceIsMu D L b x = false) (h2 : hpieceIsSharp D L b x = false) :
    IsNonneg (hpieceK D L Qb b x) ∧ hpieceW D L Qb b x = mass (hpieceK D L Qb b x) ∧
      RecordMoment (hpieceK D L Qb b x) θ := by
  rcases x with (_ | k) | (⟨i, _ | t⟩ | _)
  · simp [hpieceIsMu] at h1
  · exact ⟨(D.GB.κu_pos L b k).1, rfl, momU b k⟩
  · simp [hpieceIsSharp] at h2
  · cases t
    · exact ⟨(D.FS.κ_pos L b i).1, rfl, mom b i⟩
    · exact ⟨(D.FS.κ'_pos L b i).1, rfl, mom' b i⟩
  · exact ⟨hQ0 b, rfl, momQ b⟩

omit [DecidableEq P] in
theorem hpieceW_nonneg (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (hQ0 : ∀ b, IsNonneg (Qb b)) (b : BlockAtom Bk J L) (x : HPiece D L b) :
    0 ≤ hpieceW D L Qb b x := by
  rcases x with (_ | k) | (⟨i, _ | t⟩ | _)
  · exact zero_le_one
  · exact TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.GB.κu_pos L b k).1
  · exact mul_nonneg (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1)
      (D.FS.dconst_nonneg L b i)
  · cases t
    · exact TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1
    · exact TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ'_pos L b i).1
  · exact TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (hQ0 b)

omit [DecidableEq P] in
/-- A whole difference with a nonzero coefficient has the term's tag. -/
theorem tag_of_hpieceCoef {f : BlockAtom Bk J L → Bool} {σ : ∀ b, Option (D.FS.Ib L b)}
    {j : D.FS.Tag} {b : BlockAtom Bk J L} {x : HPiece D L b} {i : D.FS.Ib L b}
    (hx : x = .inr (.inl (i, none))) (hc : hpieceCoef D L f σ j b x ≠ 0) :
    D.FS.tag L b i = j := by
  subst hx
  simp only [hpieceCoef] at hc
  by_contra hne
  exact hc (by simp [hne])

omit [DecidableEq P] in
/-- The weight of a term splits as `(∏_{S'} κ(1)) (∏_{S'} d) ∏_{others} W`. -/
theorem prod_hpieceW_split (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (φ : ∀ b, HPiece D L b)
    (idx : ∀ b : {b' // b' ∈ hTermSharp D L φ}, D.FS.Ib L b.1.1)
    (hfx : ∀ b : {b' // b' ∈ hTermSharp D L φ}, φ b.1.1 = .inr (.inl (idx b, none))) :
    ∏ b, hpieceW D L Qb b (φ b) =
      ((∏ b : {b' // b' ∈ hTermSharp D L φ}, mass (D.FS.κ L b.1.1 (idx b))) *
        ∏ b : {b' // b' ∈ hTermSharp D L φ}, D.FS.dconst L b.1.1 (idx b)) *
      ∏ b : {b' // b' ∉ hTermSharp D L φ}, hpieceW D L Qb b.1.1 (φ b.1.1) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun b => b ∈ hTermAtoms D L φ)]
  have h1 : ∏ b : {b // b ∉ hTermAtoms D L φ}, hpieceW D L Qb b.1 (φ b.1) = 1 := by
    refine Finset.prod_eq_one fun b _ => ?_
    rw [eq_mu_of_not_mem_hTermAtoms D L φ b.1 b.2]
    rfl
  rw [h1, mul_one, ← Finset.prod_mul_distrib]
  have hW : ∀ b : {b' // b' ∈ hTermSharp D L φ},
      mass (D.FS.κ L b.1.1 (idx b)) * D.FS.dconst L b.1.1 (idx b) =
        hpieceW D L Qb b.1.1 (φ b.1.1) := by
    intro b
    rw [hfx b]
    rfl
  rw [Finset.prod_congr rfl fun b _ => hW b]
  convert (Fintype.prod_subtype_mul_prod_subtype
    (fun b : {b // b ∈ hTermAtoms D L φ} => b ∈ hTermSharp D L φ)
    (fun b => hpieceW D L Qb b.1 (φ b.1))).symm using 2
  · exact congrArg (fun i => @Finset.univ _ i) (Subsingleton.elim _ _)
  · exact Finset.prod_congr (congrArg (fun i => @Finset.univ _ i) (Subsingleton.elim _ _))
      fun _ _ => rfl

omit [DecidableEq P] in
/-- **`lem:density:coupled` for one term of a sharp-first difference, slot-dependent inputs**
(block labels): `|E_φ| ≤ (∏_𝔟 W_{φ_𝔟}) P` from the per-record data, the spectator moments and the
term's fibre-and-price input. -/
theorem hterm_coupled_bound (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (hQ0 : ∀ b, IsNonneg (Qb b)) {θ : ℝ} (hθ : 0 < θ)
    (fold : ∀ b i, SharpFoldData (D.FS.cut (D.FS.tag L b i)) (D.FS.κ L b i)
      (D.FS.κ' L b i - D.FS.κ L b i) (D.FS.dconst L b i) θ)
    (mom : ∀ b i, RecordMoment (D.FS.κ L b i) θ) (mom' : ∀ b i, RecordMoment (D.FS.κ' L b i) θ)
    (momU : ∀ b k, RecordMoment (D.GB.κu L b k) θ) (momQ : ∀ b, RecordMoment (Qb b) θ)
    {f : BlockAtom Bk J L → Bool} {σ : ∀ b, Option (D.FS.Ib L b)} {j : D.FS.Tag}
    (φ : ∀ b, HPiece D L b) (hφ : ∀ b, hpieceCoef D L f σ j b (φ b) ≠ 0)
    (G' : Slot → (∀ b, BlockLabel m₀ blk p L b) → ℝ) {Pr : ℝ}
    (hFP : HFibrePrice D L φ G' θ Pr) :
    |multilinearIntegral (tensorLaw fun b => hpieceK D L Qb b (φ b)) G'| ≤
      (∏ b, hpieceW D L Qb b (φ b)) * Pr := by
  obtain ⟨av, bv, hav, hbv, hZ, hQ⟩ := hFP
  have hPr0 : 0 ≤ Pr := by
    refine le_trans ?_ hQ
    exact mul_nonneg (Finset.prod_nonneg fun v _ => hbv v)
      (Finset.prod_nonneg fun v _ => Real.rpow_nonneg (coupledMean_nonneg fun q => hav v _ _) _)
  by_cases hz : ∃ b, hpieceIsMu D L b (φ b) = false ∧ hpieceIsSharp D L b (φ b) = false ∧
      hpieceW D L Qb b (φ b) = 0
  · -- a spectator of mass `0`: the term vanishes
    obtain ⟨b0, h1, h2, h3⟩ := hz
    obtain ⟨hK, hW, _⟩ := hspectator_facts D L Qb hQ0 mom mom' momU momQ b0 (φ b0) h1 h2
    have hY0 : multilinearIntegral (tensorLaw fun b => hpieceK D L Qb b (φ b)) G' = 0 := by
      unfold multilinearIntegral
      rw [RecordExpansion.tensorLaw_apply]
      refine Finset.sum_eq_zero fun z _ => ?_
      rw [Finset.prod_eq_zero (mem_univ b0) (lawDensity_eq_zero_of_mass hK (hW ▸ h3) _),
        zero_mul]
    rw [hY0, abs_zero]
    exact mul_nonneg (Finset.prod_nonneg fun b _ => hpieceW_nonneg D L Qb hQ0 b _) hPr0
  · push Not at hz
    have hS : ∀ b : {b' // b' ∈ hTermSharp D L φ}, hpieceIsSharp D L b.1.1 (φ b.1.1) = true := by
      intro b
      have := b.2
      simpa [hTermSharp] using this
    let idx : ∀ b : {b' // b' ∈ hTermSharp D L φ}, D.FS.Ib L b.1.1 :=
      fun b => hpieceIdx D L b.1.1 (φ b.1.1) (hS b)
    have hfx : ∀ b : {b' // b' ∈ hTermSharp D L φ}, φ b.1.1 = .inr (.inl (idx b, none)) :=
      fun b => eq_of_hpieceIsSharp D L b.1.1 (φ b.1.1) (hS b)
    have htag : ∀ b : {b' // b' ∈ hTermSharp D L φ}, D.FS.tag L b.1.1 (idx b) = j :=
      fun b => tag_of_hpieceCoef D L (hfx b) (hφ b.1.1)
    have hT1 : ∀ b : {b' // b' ∉ hTermSharp D L φ}, hpieceIsMu D L b.1.1 (φ b.1.1) = false :=
      fun b => (Finset.mem_filter.mp b.1.2).2
    have hT2 : ∀ b : {b' // b' ∉ hTermSharp D L φ}, hpieceIsSharp D L b.1.1 (φ b.1.1) = false := by
      intro b
      have := b.2
      simpa [hTermSharp] using this
    have hm : ∀ b : {b' // b' ∉ hTermSharp D L φ}, 0 < hpieceW D L Qb b.1.1 (φ b.1.1) :=
      fun b => lt_of_le_of_ne (hpieceW_nonneg D L Qb hQ0 _ _) (hz b.1.1 (hT1 b) (hT2 b)).symm
    have hspec : ∀ b : {b' // b' ∉ hTermSharp D L φ},
        ∃ κh : FiniteLaw (Slot → BlockLabel m₀ blk p L b.1.1),
          (∀ z, κh.weight z = lawDensity (hpieceK D L Qb b.1.1 (φ b.1.1)) z /
            hpieceW D L Qb b.1.1 (φ b.1.1)) ∧ MixedLpBound κh (72 / θ) 1 := by
      intro b
      obtain ⟨_, hW, hmom⟩ := hspectator_facts D L Qb hQ0 mom mom' momU momQ b.1.1 (φ b.1.1)
        (hT1 b) (hT2 b)
      rw [hW]
      exact hmom (hW ▸ hm b)
    choose κhat hκhat hmκ using hspec
    have hcoupled := abs_multilinearIntegral_coupled_le_atoms
      (Xa := BlockLabel m₀ blk p L) (hTermAtoms D L φ) (hTermSharp D L φ)
      (fun b => hpieceK D L Qb b (φ b)) (hTermOutside D L φ) (hTermOutside_weight D L Qb φ)
      G' (D.FS.cut j)
      (fun b => D.FS.κ L b.1.1 (idx b)) (fun b => D.FS.dconst L b.1.1 (idx b))
      (fun b => (fold b.1.1 (idx b)).π) (fun b => (fold b.1.1 (idx b)).κs)
      (fun b => (fold b.1.1 (idx b)).Ks) (fun b => (fold b.1.1 (idx b)).prob)
      (fun b => by
        change hpieceK D L Qb b.1.1 (φ b.1.1) = _
        rw [hfx b]
        exact (fold b.1.1 (idx b)).dec_ζ)
      (fun b s => by
        rw [← htag b]
        exact (fold b.1.1 (idx b)).sharp s)
      (fun b => TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b.1.1 _).1)
      (fun b => D.FS.dconst_nonneg L b.1.1 _) hθ
      (hTermOutside_positive D L φ (D.FS.cut_family j)) (hTermOutside_holder D L φ)
      (fun b => (fold b.1.1 (idx b)).lp) (fun b => (fold b.1.1 (idx b)).lm)
      (fun b x => by
        rw [← htag b]
        exact (fold b.1.1 (idx b)).hlp x)
      (fun b x => by
        rw [← htag b]
        exact (fold b.1.1 (idx b)).hlm x)
      (fun b => (fold b.1.1 (idx b)).mp) (fun b => (fold b.1.1 (idx b)).mm)
      (fun b => hpieceW D L Qb b.1.1 (φ b.1.1)) hm κhat hκhat hmκ hav hbv hZ
    have hW := prod_hpieceW_split D L Qb φ idx hfx
    have hWnn : 0 ≤ ∏ b, hpieceW D L Qb b (φ b) :=
      Finset.prod_nonneg fun b _ => hpieceW_nonneg D L Qb hQ0 b _
    set W := ∏ b, hpieceW D L Qb b (φ b) with hWdef
    set Q := (∏ v, bv v) * ∏ v, coupledMean
      (fun q : HSharpLabels D L φ × HSpecLabels D L φ => av v q.1 q.2) ^ (θ / 72)
    have hY : |multilinearIntegral (tensorLaw fun b => hpieceK D L Qb b (φ b)) G'| ≤ W * Q := by
      rw [hW]
      refine hcoupled.trans (le_of_eq ?_)
      simp only [Q]
      ring
    exact hY.trans (mul_le_mul_of_nonneg_left hQ hWnn)

end Terms

end Sarkozy.DensityFibre
