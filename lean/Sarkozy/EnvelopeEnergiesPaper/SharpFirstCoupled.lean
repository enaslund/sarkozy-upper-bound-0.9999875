module

public import Sarkozy.EnvelopeEnergiesPaper.BlockReference
public import Sarkozy.EnvelopeInputs.CoupledProduct
public import Sarkozy.EnvelopeInputsBlock.Inputs
public import Sarkozy.EnvelopeInputsBlock.CoupledPrices

@[expose] public section

/-!
# `SF` on the block atoms from `lem:density:coupled`: per-record moments and per-term fibres

G1's bundle `EnvelopeInputsBlock.SharpFirstCoupledTerms` (named `SharpFirstInputs` until
7 November 2026) asks, at every least counterexample and for
every term `(σ, j, f)` of the coupled expansion of `lem:sharp-first`, the per-term bound
`|Y[⊗_𝔟 K_𝔟(f_𝔟)]| ≤ (∏ g)(1 + ε_L) Y + (∏ m) c₁ L^{-σ} α` (`hcoup`). I1 reduced this to
`lem:density:coupled` for one term (`EnvelopeInputs.abs_diagonalIntegral_coupled_le_atoms`), but did
not instantiate it at the pieces (I1's report, fourth package, "What remains", item 1). This file
does so **on the block atoms**, where the coupled lemma applies as it stands (it is generic in the
atoms; no product prefix is needed):

* the sharp atoms of a term are the atoms carrying a whole difference `κ' − κ` of tag `j`; the
  spectators are the other non-`μ` atoms; the outside law `μ_𝒮` is the product of the block and
  tail reference laws off the term's atoms (`termAtoms`, `termSharp`, `termOutside`);
* the positivity of `μ_𝒮` at the tag's cut and its signed Hölder property are **proved** from
  (R2) of the block laws (K0's `Reference.rp₀`, `rpp`);
* the term's weight `∏_𝔟 w_𝔟(f_𝔟)` is matched with the coupled lemma's
  `(∏_T m)(∏_{S'} κ(1))(∏_{S'} d)` (`prod_cpieceW_split`);
* terms with a spectator of mass `0` vanish and are handled separately.

**What remains** (`SharpFirstCoupledInputs`), with labels:
* per record, at every scale and atom: a sharp decomposition of `κ' − κ` relative to `κ` at the
  cut of its tag (a witness of K0's `FirstStage.sharp`) whose normalized full folded laws `λ̂±` have
  unit mixed `L^{72/θ}` (`fold`; `lem:density:middle-catalog`, "the own sharp folds",
  `lem:density:packets`);
* per positive record `κa_h`, `κ`, `κ'`: unit mixed `L^{72/θ}` of the normalized record
  (`momA`, `mom`, `mom'`; `lem:density:coupled`, positive spectators; the first-stage records are
  "the original nonconstant laws" of `prop:density:production`);
* per term: the fibre-moment input `CoupledFibreMoment`,
  `(E_{x,y} Z_O(x, y)^{1/θ})^θ ≤ (∏_{𝔟 ∈ E} sel_𝔟)(1 + ε) Y + r` with a density-linear `r`, where
  `Z_O(x, y)` is the outside energy of `F_A` on the fibre of the sharp labels `x` and the spectator
  labels `y`. It gives the coupled lemma's fibre-and-price input `CoupledFibrePrice` with the
  canonical weights `a_v = Z_O^{1/θ}`, `b_v = 1` (`coupledFibrePrice_of_moment`). This is the step
  of `prop:density:production` that uses the induction hypothesis on the fibres with
  `lem:record:density-dc` and `lem:record:fibre-scale`; the price `∏ sel = R_E^a` is
  `prop:record:density-structured`'s.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.EnvelopeEnergiesPaper

open Sarkozy.EnvelopeInputsBlock
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame
open Sarkozy.IndexSupport Sarkozy.Functional Sarkozy.TheoremC Sarkozy.Structured
  Sarkozy.PaperFrame Sarkozy.Comparison Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
  Sarkozy.DensityMoments Sarkozy.DensityUpgrade ReflectionCut

/-! ## Per-record data -/

section Records

variable {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]

/-- **A sharp decomposition of a difference with its folded moments** (`def:price`(b),
`lem:density:coupled`, `lem:density:middle-catalog`): a witness of `HasSharpBound c κ ζ d`
(`ζ = κ(1) ∑_s π_s K_s` with `K_s` sharp at `c` relative to the half marginals of the probability
measures `κ_s`, `κ = κ(1) ∑_s π_s κ_s`) whose normalized full folded laws
`λ̂± = ∑_s π_s Diag(m±(κ_s))` are probability laws with unit mixed `L^{72/θ}`. -/
structure SharpFoldData (c : ReflectionCut Slot) (κ ζ : SlotMeasure X) (d θ : ℝ) where
  S : Type
  [fin : Fintype S]
  π : FiniteLaw S
  κs : S → SlotMeasure X
  Ks : S → SlotMeasure X
  prob : ∀ s, IsProbability (κs s)
  dec_κ : κ = mass κ • ∑ s, π.weight s • κs s
  dec_ζ : ζ = mass κ • ∑ s, π.weight s • Ks s
  sharp : ∀ s, Sharp c (Ks s) (halfMarginalPlus c (κs s)) (halfMarginalMinus c (κs s)) d
  lp : FiniteLaw (Slot → X)
  lm : FiniteLaw (Slot → X)
  hlp : ∀ x, foldedLawPlus c π κs x = lp.weight x
  hlm : ∀ x, foldedLawMinus c π κs x = lm.weight x
  mp : MixedLpBound lp (72 / θ) 1
  mm : MixedLpBound lm (72 / θ) 1

attribute [instance] SharpFoldData.fin

/-- The data contain a witness of the sharp bound (`HasSharpBound`). -/
theorem SharpFoldData.hasSharpBound {c : ReflectionCut Slot} {κ ζ : SlotMeasure X} {d θ : ℝ}
    (H : SharpFoldData c κ ζ d θ) : HasSharpBound c κ ζ d :=
  ⟨H.S, H.fin, H.π, H.κs, H.Ks, H.prob, H.dec_κ, H.dec_ζ, H.sharp⟩

/-- **Unit mixed `L^{72/θ}` of a normalized positive record** (`lem:density:coupled`, positive
spectator): if `κ(1) > 0`, the probability law `κ/κ(1)` has unit mixed `L^{72/θ}`. -/
def RecordMoment (κ : SlotMeasure X) (θ : ℝ) : Prop :=
  0 < mass κ → ∃ κhat : FiniteLaw (Slot → X),
    (∀ z, κhat.weight z = lawDensity κ z / mass κ) ∧ MixedLpBound κhat (72 / θ) 1

omit [Nonempty X] in
/-- A nonnegative measure of mass `0` has zero density. -/
theorem lawDensity_eq_zero_of_mass {κ : SlotMeasure X} (hκ : IsNonneg κ) (h0 : mass κ = 0)
    (z : Slot → X) : lawDensity κ z = 0 := by
  have h1 : 0 ≤ lawDensity κ z := hκ _ (fun y => by split_ifs <;> norm_num)
  have h2 := hκ (fun y => 1 - if y = z then 1 else 0) (fun y => by split_ifs <;> norm_num)
  have hlin : κ (fun y => 1 - if y = z then (1 : ℝ) else 0) =
      κ (fun _ => 1) - κ (fun y => if y = z then 1 else 0) := by
    rw [← map_sub]
    rfl
  unfold mass at h0
  unfold lawDensity at h1 ⊢
  linarith

end Records

/-! ## The atoms of a coupled term -/

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

section Pieces

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)

/-- Whether a coupled piece is a whole sharp difference `κ' − κ`. -/
def isSharpPiece (b : BlockAtom Bk J L) : CPiece D L b → Bool
  | Sum.inr (_, none) => true
  | _ => false

/-- The difference index of a whole sharp difference. -/
def sharpIdx (b : BlockAtom Bk J L) :
    (x : CPiece D L b) → isSharpPiece D L b x = true → D.FS.Ib L b
  | Sum.inr (i, none), _ => i
  | Sum.inl _, hx => absurd hx (by simp [isSharpPiece])
  | Sum.inr (_, some _), hx => absurd hx (by simp [isSharpPiece])

omit [DecidableEq P] in
theorem eq_of_isSharpPiece (b : BlockAtom Bk J L) (x : CPiece D L b)
    (hx : isSharpPiece D L b x = true) : x = Sum.inr (sharpIdx D L b x hx, none) := by
  rcases x with _ | ⟨i, _ | t⟩
  · simp [isSharpPiece] at hx
  · rfl
  · simp [isSharpPiece] at hx

/-- The non-`μ` atoms `E` of a term `f`. -/
def termAtoms (f : ∀ b, CPiece D L b) : Finset (BlockAtom Bk J L) :=
  univ.filter (fun b => cpieceIsMu D L b (f b) = false)

/-- The sharp atoms `S' ⊆ E` of a term: those with a whole difference. -/
def termSharp (f : ∀ b, CPiece D L b) : Finset {b // b ∈ termAtoms D L f} :=
  univ.filter (fun b => isSharpPiece D L b.1 (f b.1) = true)

/-- The outside law `μ_𝒮` of a term: the reference laws off its atoms. -/
noncomputable def termOutside (f : ∀ b, CPiece D L b) :
    FiniteLaw (Slot → ∀ b : {b // b ∉ termAtoms D L f}, BlockLabel m₀ blk p L b.1) :=
  FiniteLaw.tensor (fun b => blockRefLaw blk p D.R.μ₀ D.R.μp L b.1)

omit [DecidableEq P] in
/-- Off its atoms a term carries `μ_𝔟`. -/
theorem eq_mu_of_not_mem (f : ∀ b, CPiece D L b) (b : BlockAtom Bk J L)
    (hb : b ∉ termAtoms D L f) : f b = Sum.inl none := by
  have hmu : cpieceIsMu D L b (f b) = true := by
    simpa [termAtoms] using hb
  rcases hx : f b with (_ | hh) | ⟨i, _ | t⟩
  · rfl
  all_goals (rw [hx] at hmu; simp [cpieceIsMu] at hmu)

omit [DecidableEq P] in
theorem cpieceK_of_eq_sharp {b : BlockAtom Bk J L} {x : CPiece D L b} {i : D.FS.Ib L b}
    (hx : x = Sum.inr (i, none)) : cpieceK D L b x = D.FS.κ' L b i - D.FS.κ L b i := by
  subst hx
  rfl

omit [DecidableEq P] in
theorem cpieceW_of_eq_sharp {b : BlockAtom Bk J L} {x : CPiece D L b} {i : D.FS.Ib L b}
    (hx : x = Sum.inr (i, none)) : cpieceW D L b x = mass (D.FS.κ L b i) * D.FS.dconst L b i := by
  subst hx
  rfl

omit [DecidableEq P] in
/-- The tag of a whole difference with a nonzero coefficient is the term's tag. -/
theorem tag_of_coef {σ : ∀ b, Option (D.FS.Ib L b)} {j : D.FS.Tag} {b : BlockAtom Bk J L}
    {x : CPiece D L b} {i : D.FS.Ib L b} (hx : x = Sum.inr (i, none))
    (hc : cpieceCoef D L σ j b x ≠ 0) : D.FS.tag L b i = j := by
  subst hx
  simp only [cpieceCoef] at hc
  by_contra hne
  exact hc (by simp [hne])

omit [DecidableEq P] in
/-- A spectator piece (neither `μ` nor a whole difference) is a positive record whose weight,
price and remainder weight are its mass, its mass times the selection factor, and its mass. -/
theorem spectator_facts (b : BlockAtom Bk J L) (x : CPiece D L b)
    (h1 : cpieceIsMu D L b x = false) (h2 : isSharpPiece D L b x = false) :
    IsNonneg (cpieceK D L b x) ∧ cpieceW D L b x = mass (cpieceK D L b x) ∧
      cpieceG D L b x = cpieceW D L b x * TheoremCBlock.selectionFactor a p D.S.selPre L b ∧
      cpieceM D L b x = cpieceW D L b x := by
  rcases x with (_ | hh) | ⟨i, _ | t⟩
  · simp [cpieceIsMu] at h1
  · exact ⟨(D.FS.κa_pos L b hh).1, rfl, rfl, rfl⟩
  · simp [isSharpPiece] at h2
  · cases t
    · exact ⟨(D.FS.κ_pos L b i).1, rfl, by simp [cpieceG, cpieceW], by simp [cpieceM, cpieceW]⟩
    · exact ⟨(D.FS.κ'_pos L b i).1, rfl, by simp [cpieceG, cpieceW], by simp [cpieceM, cpieceW]⟩

/-- The labels of the sharp atoms of a term. -/
abbrev SharpLabels (f : ∀ b, CPiece D L b) : Type :=
  ∀ b : {b' // b' ∈ termSharp D L f}, BlockLabel m₀ blk p L b.1.1

/-- The labels of the spectators of a term. -/
abbrev SpecLabels (f : ∀ b, CPiece D L b) : Type :=
  ∀ b : {b' // b' ∉ termSharp D L f}, BlockLabel m₀ blk p L b.1.1

/-- **The fibre-and-price input of one coupled term** (`lem:density:coupled`, its fibre step; with
`lem:record:density-dc` and `lem:record:fibre-scale` for the price, `prop:density:production`):
fibre weights `a_v ≥ 0` and constants `b_v ≥ 0` such that every outside fibre energy satisfies
`Z_O(F_A(x, y, ·))^{1/72} ≤ b_v a_v(x, y)^{θ/72}` (`x` the sharp labels, `y` the spectator labels,
`Z_O` the energy of the outside reference `μ_𝒮`), and
`∏_v b_v ∏_v (E a_v)^{θ/72} ≤ (∏_{𝔟 ∈ E} sel_𝔟)(1 + ε) Y + r` with a remainder `r` whose weighted
size is density-linear: `(∏ w) r ≤ (∏ m) c₁ L^{-σ} α`. -/
def CoupledFibrePrice (A : Finset ℤ) (f : ∀ b, CPiece D L b) (θ ε c₁ : ℝ) : Prop :=
  ∃ (av : Slot → SharpLabels D L f → SpecLabels D L f → ℝ) (bv : Slot → ℝ) (r : ℝ),
    (∀ v x y, 0 ≤ av v x y) ∧ (∀ v, 0 ≤ bv v) ∧
    (∀ v x y, coupledEnergyV (multilinearIntegral (signedIntegral (termOutside D L f).weight))
        (fun w => blockLift m₀ blk p L A
          (joinLabels (termAtoms D L f) (joinLabels (termSharp D L f) x y) w)) ^ (1 / (72 : ℝ)) ≤
        bv v * av v x y ^ (θ / 72)) ∧
    (∏ v, bv v) * (∏ v, coupledMean
        (fun q : SharpLabels D L f × SpecLabels D L f => av v q.1 q.2) ^ (θ / 72)) ≤
      (∏ b ∈ termAtoms D L f, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
        ((1 + ε) * D.Y L A) + r ∧
    (∏ b, cpieceW D L b (f b)) * r ≤ (∏ b, cpieceM D L b (f b)) * remainder c₁ L A

/-- The outside fibre energy `Z_O(x, y) = Λ_{μ_𝒮}(F_A(x, y, ·), …, F_A(x, y, ·))` of a term at the
sharp labels `x` and the spectator labels `y`. -/
noncomputable def fibreEnergy (A : Finset ℤ) (f : ∀ b, CPiece D L b) (x : SharpLabels D L f)
    (y : SpecLabels D L f) : ℝ :=
  coupledEnergyV (multilinearIntegral (signedIntegral (termOutside D L f).weight))
    (fun w => blockLift m₀ blk p L A
      (joinLabels (termAtoms D L f) (joinLabels (termSharp D L f) x y) w))

/-- **The fibre-moment input of one coupled term** (`lem:density:coupled` with the canonical
fibre weights `a = Z_O^{1/θ}`, `b = 1`): the `L^{1/θ}` mean of the outside fibre energies satisfies
`(E_{x,y} Z_O(x, y)^{1/θ})^θ ≤ (∏_{𝔟 ∈ E} sel_𝔟)(1 + ε) Y + r` with `(∏ w) r ≤ (∏ m) c₁ L^{-σ} α`.
In the paper the fibre energies are bounded by the induction hypothesis at the fibre densities, and
the mean of the fibre densities by `lem:record:density-dc` and `lem:record:fibre-scale`
(`prop:density:production`). It implies `CoupledFibrePrice` (`coupledFibrePrice_of_moment`). -/
def CoupledFibreMoment (A : Finset ℤ) (f : ∀ b, CPiece D L b) (θ ε c₁ : ℝ) : Prop :=
  ∃ r : ℝ,
    coupledMean (fun q : SharpLabels D L f × SpecLabels D L f =>
        fibreEnergy D L A f q.1 q.2 ^ (1 / θ)) ^ θ ≤
      (∏ b ∈ termAtoms D L f, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
        ((1 + ε) * D.Y L A) + r ∧
    (∏ b, cpieceW D L b (f b)) * r ≤ (∏ b, cpieceM D L b (f b)) * remainder c₁ L A

end Pieces

/-! ## The inputs and the per-term bound -/

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)

/-- **The inputs of `SharpFirstTerms` through `lem:density:coupled` on the block atoms.**
* `θ > 0`, the density endpoint (the paper's `ϑ`);
* `fold`: for every record `(L, 𝔟, i)` a sharp decomposition of `κ' − κ` relative to `κ` at the
  cut of its tag with constant `dconst`, whose folded laws have unit mixed `L^{72/θ}`
  (`lem:density:middle-catalog`, `lem:density:packets`);
* `momA`, `mom`, `mom'`: unit mixed `L^{72/θ}` of the normalized positive records `κa`, `κ`, `κ'`
  (`lem:density:coupled`, spectators);
* `ε → 0`, `c₁ ≥ 0` (as in G1's `SharpFirstInputs`);
* `fibre`: the fibre-moment input `CoupledFibreMoment` at every term of every least
  counterexample, `(E_{x,y} Z_O(x, y)^{1/θ})^θ ≤ (∏_{𝔟 ∈ E} sel_𝔟)(1 + ε) Y + r`
  (`prop:density:production`, `lem:record:density-dc`, `lem:record:fibre-scale`). -/
structure SharpFirstCoupledInputs where
  θ : ℝ
  hθ : 0 < θ
  fold : ∀ L b i, SharpFoldData (D.FS.cut (D.FS.tag L b i)) (D.FS.κ L b i)
    (D.FS.κ' L b i - D.FS.κ L b i) (D.FS.dconst L b i) θ
  momA : ∀ L b hh, RecordMoment (D.FS.κa L b hh) θ
  mom : ∀ L b i, RecordMoment (D.FS.κ L b i) θ
  mom' : ∀ L b i, RecordMoment (D.FS.κ' L b i) θ
  ε : ℕ → ℝ
  hε0 : ∀ L, 0 ≤ ε L
  hεt : Tendsto ε atTop (𝓝 0)
  c₁ : ℝ
  hc₁ : 0 ≤ c₁
  fibre : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
    ∀ σ : (∀ b, Option (D.FS.Ib L b)), σ ≠ (fun _ => none) → ∀ j,
      1 ≤ countVec (D.FS.tag L) σ j → ∀ f : (∀ b, CPiece D L b),
      (∀ b, cpieceCoef D L σ j b (f b) ≠ 0) → CoupledFibreMoment D L A f θ (ε L) c₁)

variable {D}

omit [DecidableEq P] in
/-- The moment input of a spectator piece. -/
theorem SharpFirstCoupledInputs.spectator_moment (I : SharpFirstCoupledInputs D) (L : ℕ)
    (b : BlockAtom Bk J L) (x : CPiece D L b) (h1 : cpieceIsMu D L b x = false)
    (h2 : isSharpPiece D L b x = false) : RecordMoment (cpieceK D L b x) I.θ := by
  rcases x with (_ | hh) | ⟨i, _ | t⟩
  · simp [cpieceIsMu] at h1
  · exact I.momA L b hh
  · simp [isSharpPiece] at h2
  · cases t
    · exact I.mom L b i
    · exact I.mom' L b i

omit [DecidableEq P] in
/-- The outside law of a term is the tensor of the reference laws off its atoms. -/
theorem termOutside_weight (L : ℕ) (f : ∀ b, CPiece D L b)
    (w : Slot → ∀ b : {b // b ∉ termAtoms D L f}, BlockLabel m₀ blk p L b.1) :
    (termOutside D L f).weight w =
      ∏ b : {b // b ∉ termAtoms D L f}, lawDensity (cpieceK D L b.1 (f b.1)) (fun v => w v b) := by
  unfold termOutside
  rw [Structured.tensor_weight]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [eq_mu_of_not_mem D L f b.1 b.2]
  change _ = lawDensity (blockRefLaws m₀ blk p D.R.μ₀ D.R.μp L b.1) _
  rw [blockRefLaws_eq, lawDensity_signedIntegral_eq]

omit [DecidableEq P] in
/-- (R2) of the reference: the outside law of a term is positive at every cut of the family. -/
theorem termOutside_positive (L : ℕ) (f : ∀ b, CPiece D L b) {c : ReflectionCut Slot}
    (hc : IsFamilyCut c) : c.Positive (signedIntegral (termOutside D L f).weight) := by
  unfold termOutside
  rw [FiniteLaw.signedIntegral_tensor]
  refine Positive.tensor fun b => ?_
  obtain ⟨b, hb⟩ := b
  rcases b with β | jj
  · exact D.R.rp₀ β c hc
  · exact D.R.rpp (p L jj) (D.S.p_prime L jj) c hc

omit [DecidableEq P] in
/-- (R2) of the reference gives the outside signed Hölder property of a term. -/
theorem termOutside_holder (L : ℕ) (f : ∀ b, CPiece D L b) :
    coupledOutsideHolderV (multilinearIntegral (signedIntegral (termOutside D L f).weight)) := by
  have hsr : SlotReflectionPositive (signedIntegral (termOutside D L f).weight) :=
    fun c hc => termOutside_positive L f (isFamilyCut_of_sorting c hc)
  refine ⟨fun g => slot_diagonal_nonneg hsr g, fun g => ?_⟩
  have h := slot_signed_holder hsr g
  rw [card_slot_real]
  exact h

omit [DecidableEq P] in
/-- The outside fibre energies are nonnegative ((R2) of the reference). -/
theorem fibreEnergy_nonneg (L : ℕ) (A : Finset ℤ) (f : ∀ b, CPiece D L b) (x : SharpLabels D L f)
    (y : SpecLabels D L f) : 0 ≤ fibreEnergy D L A f x y :=
  (termOutside_holder L f).1 _

omit [DecidableEq P] in
/-- **The canonical fibre weights**: the fibre-moment input gives the fibre-and-price input, with
`a_v = Z_O^{1/θ}` and `b_v = 1`. -/
theorem coupledFibrePrice_of_moment {L : ℕ} {A : Finset ℤ} {f : ∀ b, CPiece D L b}
    {θ ε c₁ : ℝ} (hθ : 0 < θ) (hM : CoupledFibreMoment D L A f θ ε c₁) :
    CoupledFibrePrice D L A f θ ε c₁ := by
  obtain ⟨r, hQ, hr⟩ := hM
  refine ⟨fun _ x y => fibreEnergy D L A f x y ^ (1 / θ), fun _ => 1, r,
    fun _ _ _ => Real.rpow_nonneg (fibreEnergy_nonneg L A f _ _) _, fun _ => zero_le_one,
    fun v x y => ?_, ?_, hr⟩
  · have h0 := fibreEnergy_nonneg L A f x y
    rw [one_mul, ← Real.rpow_mul h0]
    have e : 1 / θ * (θ / 72) = 1 / 72 := by field_simp
    rw [e]
    exact le_refl _
  · have hmean : 0 ≤ coupledMean (fun q : SharpLabels D L f × SpecLabels D L f =>
        fibreEnergy D L A f q.1 q.2 ^ (1 / θ)) := by
      unfold coupledMean
      exact div_nonneg (Finset.sum_nonneg fun q _ =>
        Real.rpow_nonneg (fibreEnergy_nonneg L A f _ _) _) (Nat.cast_nonneg _)
    rw [Finset.prod_const_one, one_mul, Finset.prod_const, Finset.card_univ, card_slot,
      ← Real.rpow_natCast, ← Real.rpow_mul hmean]
    have e : θ / 72 * ((72 : ℕ) : ℝ) = θ := by push_cast; ring
    rw [e]
    exact hQ

omit [DecidableEq P] in
/-- **The fibre-moment input from fibre bounds and a mean bound** (the two steps of the paper's
proof of `prop:density:production`): if every outside fibre energy is at most `K α(x, y)^θ` (the
induction hypothesis at the fibre density `α(x, y)`, after the density-dc replacement of
`lem:record:density-dc`), and `K (E α)^θ ≤ (∏ sel)(1 + ε) Y + r` (the mean of the fibre densities,
`lem:record:fibre-scale`, with the price `R_E^a`), then `CoupledFibreMoment` holds. -/
theorem coupledFibreMoment_of_fibres {L : ℕ} {A : Finset ℤ} {f : ∀ b, CPiece D L b}
    {θ ε c₁ : ℝ} (hθ : 0 < θ) {K : ℝ} (hK : 0 ≤ K) (α : SharpLabels D L f → SpecLabels D L f → ℝ)
    (hα : ∀ x y, 0 ≤ α x y) (hfib : ∀ x y, fibreEnergy D L A f x y ≤ K * α x y ^ θ) (r : ℝ)
    (hmean : K * coupledMean (fun q : SharpLabels D L f × SpecLabels D L f => α q.1 q.2) ^ θ ≤
      (∏ b ∈ termAtoms D L f, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
        ((1 + ε) * D.Y L A) + r)
    (hr : (∏ b, cpieceW D L b (f b)) * r ≤ (∏ b, cpieceM D L b (f b)) * remainder c₁ L A) :
    CoupledFibreMoment D L A f θ ε c₁ := by
  refine ⟨r, le_trans ?_ hmean, hr⟩
  have hpt : ∀ q : SharpLabels D L f × SpecLabels D L f,
      fibreEnergy D L A f q.1 q.2 ^ (1 / θ) ≤ K ^ (1 / θ) * α q.1 q.2 := by
    intro q
    have h0 := fibreEnergy_nonneg L A f q.1 q.2
    have h1 := Real.rpow_le_rpow h0 (hfib q.1 q.2) (by positivity : (0 : ℝ) ≤ 1 / θ)
    rw [Real.mul_rpow hK (Real.rpow_nonneg (hα q.1 q.2) _), ← Real.rpow_mul (hα q.1 q.2)] at h1
    have e : θ * (1 / θ) = 1 := by field_simp
    rw [e, Real.rpow_one] at h1
    exact h1
  have hmα : 0 ≤ coupledMean (fun q : SharpLabels D L f × SpecLabels D L f => α q.1 q.2) := by
    unfold coupledMean
    exact div_nonneg (Finset.sum_nonneg fun q _ => hα _ _) (Nat.cast_nonneg _)
  have hmZ : 0 ≤ coupledMean (fun q : SharpLabels D L f × SpecLabels D L f =>
      fibreEnergy D L A f q.1 q.2 ^ (1 / θ)) := by
    unfold coupledMean
    exact div_nonneg (Finset.sum_nonneg fun q _ =>
      Real.rpow_nonneg (fibreEnergy_nonneg L A f _ _) _) (Nat.cast_nonneg _)
  have hm : coupledMean (fun q : SharpLabels D L f × SpecLabels D L f =>
      fibreEnergy D L A f q.1 q.2 ^ (1 / θ)) ≤
      K ^ (1 / θ) * coupledMean (fun q : SharpLabels D L f × SpecLabels D L f => α q.1 q.2) := by
    unfold coupledMean
    rw [mul_div_assoc', Finset.mul_sum]
    exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun q _ => hpt q) (Nat.cast_nonneg _)
  have h2 := Real.rpow_le_rpow hmZ hm hθ.le
  rw [Real.mul_rpow (Real.rpow_nonneg hK _) hmα, ← Real.rpow_mul hK] at h2
  have e : 1 / θ * θ = 1 := by field_simp
  rw [e, Real.rpow_one] at h2
  exact h2

omit [DecidableEq P] in
/-- **The converse: the fibre-moment input is the weakest fibre input.** Any fibre weights
`(a_v, b_v)` of the coupled lemma give `(E Z_O^{1/θ})^θ ≤ ∏_v b_v ∏_v (E a_v)^{θ/72}`, so
`CoupledFibrePrice` implies `CoupledFibreMoment`: the reduction to the moment form loses nothing. -/
theorem coupledFibreMoment_of_price {L : ℕ} {A : Finset ℤ} {f : ∀ b, CPiece D L b}
    {θ ε c₁ : ℝ} (hθ : 0 < θ) (hP : CoupledFibrePrice D L A f θ ε c₁) :
    CoupledFibreMoment D L A f θ ε c₁ := by
  obtain ⟨av, bv, r, hav, hbv, hZ, hQ, hr⟩ := hP
  refine ⟨r, le_trans ?_ hQ, hr⟩
  set Z := fun q : SharpLabels D L f × SpecLabels D L f => fibreEnergy D L A f q.1 q.2 ^ (1 / θ)
  have hZ0 : ∀ q, 0 ≤ Z q := fun q => Real.rpow_nonneg (fibreEnergy_nonneg L A f _ _) _
  have hq : (0 : ℝ) < 72 / θ := by positivity
  -- pointwise: `Z^{1/θ} ≤ b^{72/θ} a`
  have hpt : ∀ v (q : SharpLabels D L f × SpecLabels D L f),
      Z q ≤ bv v ^ (72 / θ) * av v q.1 q.2 := by
    intro v q
    have h0 := fibreEnergy_nonneg L A f q.1 q.2
    have h1 := Real.rpow_le_rpow (Real.rpow_nonneg h0 _) (hZ v q.1 q.2) hq.le
    rw [← Real.rpow_mul h0, Real.mul_rpow (hbv v) (Real.rpow_nonneg (hav v q.1 q.2) _),
      ← Real.rpow_mul (hav v q.1 q.2)] at h1
    have e1 : 1 / (72 : ℝ) * (72 / θ) = 1 / θ := by field_simp
    have e2 : θ / 72 * (72 / θ) = 1 := by field_simp
    rw [e1, e2, Real.rpow_one] at h1
    exact h1
  have hmean0 : 0 ≤ coupledMean Z := by
    unfold coupledMean
    exact div_nonneg (Finset.sum_nonneg fun q _ => hZ0 q) (Nat.cast_nonneg _)
  -- the mean: `E Z ≤ b^{72/θ} E a`, so `(E Z)^{θ/72} ≤ b (E a)^{θ/72}`
  have hv : ∀ v, coupledMean Z ^ (θ / 72) ≤ bv v * coupledMean
      (fun q : SharpLabels D L f × SpecLabels D L f => av v q.1 q.2) ^ (θ / 72) := by
    intro v
    have hm : coupledMean Z ≤ bv v ^ (72 / θ) *
        coupledMean (fun q : SharpLabels D L f × SpecLabels D L f => av v q.1 q.2) := by
      unfold coupledMean
      rw [mul_div_assoc', Finset.mul_sum]
      exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun q _ => hpt v q) (Nat.cast_nonneg _)
    have hma : 0 ≤ coupledMean (fun q : SharpLabels D L f × SpecLabels D L f => av v q.1 q.2) := by
      unfold coupledMean
      exact div_nonneg (Finset.sum_nonneg fun q _ => hav v _ _) (Nat.cast_nonneg _)
    have h1 := Real.rpow_le_rpow hmean0 hm (by positivity : (0 : ℝ) ≤ θ / 72)
    rw [Real.mul_rpow (Real.rpow_nonneg (hbv v) _) hma, ← Real.rpow_mul (hbv v)] at h1
    have e : 72 / θ * (θ / 72) = 1 := by field_simp
    rw [e, Real.rpow_one] at h1
    exact h1
  calc coupledMean Z ^ θ = ∏ _v : Slot, coupledMean Z ^ (θ / 72) := by
        rw [Finset.prod_const, Finset.card_univ, card_slot, ← Real.rpow_natCast,
          ← Real.rpow_mul hmean0]
        congr 1
        push_cast
        ring
    _ ≤ ∏ v, (bv v * coupledMean
        (fun q : SharpLabels D L f × SpecLabels D L f => av v q.1 q.2) ^ (θ / 72)) :=
        Finset.prod_le_prod₀ (fun _ _ => Real.rpow_nonneg hmean0 _) fun v _ => hv v
    _ = _ := Finset.prod_mul_distrib

omit [DecidableEq P] in
/-- **The weight of a term is the coupled lemma's factor**:
`∏_𝔟 w_𝔟(f_𝔟) = (∏_{S'} κ(1) d) · ∏_T m` (the sharp atoms carry `κ(1) d`, the spectators their mass,
`μ` carries `1`). -/
theorem prod_cpieceW_split (L : ℕ) (f : ∀ b, CPiece D L b)
    (idx : ∀ b : {b' // b' ∈ termSharp D L f}, D.FS.Ib L b.1.1)
    (hfx : ∀ b : {b' // b' ∈ termSharp D L f}, f b.1.1 = Sum.inr (idx b, none)) :
    ∏ b, cpieceW D L b (f b) =
      ((∏ b : {b' // b' ∈ termSharp D L f}, mass (D.FS.κ L b.1.1 (idx b))) *
        ∏ b : {b' // b' ∈ termSharp D L f}, D.FS.dconst L b.1.1 (idx b)) *
      ∏ b : {b' // b' ∉ termSharp D L f}, cpieceW D L b.1.1 (f b.1.1) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun b => b ∈ termAtoms D L f)]
  have h1 : ∏ b : {b // b ∉ termAtoms D L f}, cpieceW D L b.1 (f b.1) = 1 := by
    refine Finset.prod_eq_one fun b _ => ?_
    rw [eq_mu_of_not_mem D L f b.1 b.2]
    rfl
  rw [h1, mul_one, ← Finset.prod_mul_distrib]
  rw [Finset.prod_congr rfl fun b _ => (cpieceW_of_eq_sharp D L (hfx b)).symm]
  convert (Fintype.prod_subtype_mul_prod_subtype
    (fun b : {b // b ∈ termAtoms D L f} => b ∈ termSharp D L f)
    (fun b => cpieceW D L b.1 (f b.1))).symm using 2
  · exact congrArg (fun i => @Finset.univ _ i) (Subsingleton.elim _ _)
  · exact Finset.prod_congr (congrArg (fun i => @Finset.univ _ i) (Subsingleton.elim _ _))
      fun _ _ => rfl

omit [DecidableEq P] in
/-- **`lem:density:coupled` for one term of the coupled expansion of `lem:sharp-first`, on the block
atoms**: the per-term bound of G1's `SharpFirstCoupledTerms.hcoup` from the per-record moments,
(R2) of
the reference and the term's fibre-and-price input. -/
theorem SharpFirstCoupledInputs.term_bound (I : SharpFirstCoupledInputs D) (L : ℕ)
    (A : Finset ℤ) {σ : ∀ b, Option (D.FS.Ib L b)} {j : D.FS.Tag} (f : ∀ b, CPiece D L b)
    (hf : ∀ b, cpieceCoef D L σ j b (f b) ≠ 0)
    (hFP : CoupledFibrePrice D L A f I.θ (I.ε L) I.c₁) :
    |diagonalIntegral (tensorLaw fun b => cpieceK D L b (f b)) (blockLift m₀ blk p L A)| ≤
      (∏ b, cpieceG D L b (f b)) * ((1 + I.ε L) * D.Y L A) +
        (∏ b, cpieceM D L b (f b)) * remainder I.c₁ L A := by
  by_cases hz : ∃ b, cpieceIsMu D L b (f b) = false ∧ isSharpPiece D L b (f b) = false ∧
      cpieceW D L b (f b) = 0
  · -- a spectator of mass `0`: the term vanishes, and so do both prices
    obtain ⟨b0, h1, h2, h3⟩ := hz
    obtain ⟨hK, hW, hG, hM⟩ := spectator_facts D L b0 (f b0) h1 h2
    have hG0 : ∏ b, cpieceG D L b (f b) = 0 :=
      Finset.prod_eq_zero (mem_univ b0) (by rw [hG, h3, zero_mul])
    have hM0 : ∏ b, cpieceM D L b (f b) = 0 := Finset.prod_eq_zero (mem_univ b0) (by rw [hM, h3])
    have hY0 : diagonalIntegral (tensorLaw fun b => cpieceK D L b (f b))
        (blockLift m₀ blk p L A) = 0 := by
      unfold diagonalIntegral multilinearIntegral
      rw [RecordExpansion.tensorLaw_apply]
      refine Finset.sum_eq_zero fun z _ => ?_
      rw [Finset.prod_eq_zero (mem_univ b0) (lawDensity_eq_zero_of_mass hK (hW ▸ h3) _),
        zero_mul]
    rw [hY0, hG0, hM0]
    simp
  · push Not at hz
    obtain ⟨av, bv, r, hav, hbv, hZ, hQ, hr⟩ := hFP
    have hS : ∀ b : {b' // b' ∈ termSharp D L f}, isSharpPiece D L b.1.1 (f b.1.1) = true := by
      intro b
      have := b.2
      simpa [termSharp] using this
    let idx : ∀ b : {b' // b' ∈ termSharp D L f}, D.FS.Ib L b.1.1 :=
      fun b => sharpIdx D L b.1.1 (f b.1.1) (hS b)
    have hfx : ∀ b : {b' // b' ∈ termSharp D L f}, f b.1.1 = Sum.inr (idx b, none) :=
      fun b => eq_of_isSharpPiece D L b.1.1 (f b.1.1) (hS b)
    have htag : ∀ b : {b' // b' ∈ termSharp D L f}, D.FS.tag L b.1.1 (idx b) = j :=
      fun b => tag_of_coef D L (hfx b) (hf b.1.1)
    have hT1 : ∀ b : {b' // b' ∉ termSharp D L f}, cpieceIsMu D L b.1.1 (f b.1.1) = false :=
      fun b => (Finset.mem_filter.mp b.1.2).2
    have hT2 : ∀ b : {b' // b' ∉ termSharp D L f}, isSharpPiece D L b.1.1 (f b.1.1) = false := by
      intro b
      have := b.2
      simpa [termSharp] using this
    have hm : ∀ b : {b' // b' ∉ termSharp D L f}, 0 < cpieceW D L b.1.1 (f b.1.1) :=
      fun b => lt_of_le_of_ne (cpieceW_nonneg D L _ _) (hz b.1.1 (hT1 b) (hT2 b)).symm
    have hspec : ∀ b : {b' // b' ∉ termSharp D L f},
        ∃ κh : FiniteLaw (Slot → BlockLabel m₀ blk p L b.1.1),
          (∀ z, κh.weight z = lawDensity (cpieceK D L b.1.1 (f b.1.1)) z /
            cpieceW D L b.1.1 (f b.1.1)) ∧ MixedLpBound κh (72 / I.θ) 1 := by
      intro b
      obtain ⟨_, hW, _, _⟩ := spectator_facts D L b.1.1 (f b.1.1) (hT1 b) (hT2 b)
      rw [hW]
      exact I.spectator_moment L b.1.1 (f b.1.1) (hT1 b) (hT2 b) (hW ▸ hm b)
    choose κhat hκhat hmκ using hspec
    have hcoupled := EnvelopeInputs.abs_diagonalIntegral_coupled_le_atoms
      (Xa := BlockLabel m₀ blk p L) (termAtoms D L f) (termSharp D L f)
      (fun b => cpieceK D L b (f b)) (termOutside D L f) (termOutside_weight L f)
      (blockLift m₀ blk p L A) (D.FS.cut j)
      (fun b => D.FS.κ L b.1.1 (idx b)) (fun b => D.FS.dconst L b.1.1 (idx b))
      (fun b => (I.fold L b.1.1 (idx b)).π) (fun b => (I.fold L b.1.1 (idx b)).κs)
      (fun b => (I.fold L b.1.1 (idx b)).Ks) (fun b => (I.fold L b.1.1 (idx b)).prob)
      (fun b => by
        change cpieceK D L b.1.1 (f b.1.1) = _
        rw [cpieceK_of_eq_sharp D L (hfx b)]
        exact (I.fold L b.1.1 (idx b)).dec_ζ)
      (fun b s => by
        rw [← htag b]
        exact (I.fold L b.1.1 (idx b)).sharp s)
      (fun b => TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b.1.1 _).1)
      (fun b => D.FS.dconst_nonneg L b.1.1 _) I.hθ
      (termOutside_positive L f (D.FS.cut_family j)) (termOutside_holder L f)
      (fun b => (I.fold L b.1.1 (idx b)).lp) (fun b => (I.fold L b.1.1 (idx b)).lm)
      (fun b x => by
        rw [← htag b]
        exact (I.fold L b.1.1 (idx b)).hlp x)
      (fun b x => by
        rw [← htag b]
        exact (I.fold L b.1.1 (idx b)).hlm x)
      (fun b => (I.fold L b.1.1 (idx b)).mp) (fun b => (I.fold L b.1.1 (idx b)).mm)
      (fun b => cpieceW D L b.1.1 (f b.1.1)) hm κhat hκhat hmκ hav hbv hZ
    have hW := prod_cpieceW_split L f idx hfx
    have hWnn : 0 ≤ ∏ b, cpieceW D L b (f b) :=
      Finset.prod_nonneg fun b _ => cpieceW_nonneg D L b _
    have hG := prod_cpieceG_eq D L f
    set W := ∏ b, cpieceW D L b (f b) with hWdef
    set Sel := ∏ b ∈ termAtoms D L f, TheoremCBlock.selectionFactor a p D.S.selPre L b
    set Q := (∏ v, bv v) * ∏ v, coupledMean
      (fun q : SharpLabels D L f × SpecLabels D L f => av v q.1 q.2) ^ (I.θ / 72)
    have hY : |diagonalIntegral (tensorLaw fun b => cpieceK D L b (f b))
        (blockLift m₀ blk p L A)| ≤ W * Q := by
      rw [hW]
      refine hcoupled.trans (le_of_eq ?_)
      simp only [Q]
      ring
    have hG' : ∏ b, cpieceG D L b (f b) = W * Sel := hG
    rw [hG']
    calc _ ≤ W * Q := hY
      _ ≤ W * (Sel * ((1 + I.ε L) * D.Y L A) + r) := mul_le_mul_of_nonneg_left hQ hWnn
      _ = W * Sel * ((1 + I.ε L) * D.Y L A) + W * r := by ring
      _ ≤ _ := by linarith

/-- **G1's `SharpFirstCoupledTerms` from the coupled inputs** (`lem:sharp-first` with
`lem:density:coupled`): `hcoup` holds term by term by `SharpFirstCoupledInputs.term_bound`. -/
noncomputable def SharpFirstCoupledInputs.toCoupledTerms (I : SharpFirstCoupledInputs D) :
    SharpFirstCoupledTerms D where
  ε := I.ε
  hε0 := I.hε0
  hεt := I.hεt
  c₁ := I.c₁
  hc₁ := I.hc₁
  hcoup := by
    filter_upwards [I.fibre] with L hL
    intro C hC hind A hA hY σ hσ j hj f hf
    exact I.term_bound L A f hf
      (coupledFibrePrice_of_moment I.hθ (hL C hC hind A hA hY σ hσ j hj f hf))

/-- **G1's `SF` from the coupled inputs** (`SharpFirstCoupledInputs.toCoupledTerms`). -/
noncomputable def SharpFirstCoupledInputs.toSharpFirstInputs (I : SharpFirstCoupledInputs D) :
    SharpFirstInputs D :=
  I.toCoupledTerms.toSharpFirstInputs

omit [DecidableEq P] in
/-- **`SharpFirstTerms` for block-atom data from the coupled inputs**, at every `a ≥ 0`. -/
theorem SharpFirstCoupledInputs.sharpFirstTerms (I : SharpFirstCoupledInputs D) (ha : 0 ≤ a) :
    D.SharpFirstTerms :=
  I.toSharpFirstInputs.sharpFirstTerms ha

end Sarkozy.EnvelopeEnergiesPaper
