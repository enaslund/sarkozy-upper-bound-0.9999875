module

public import Sarkozy.EnvelopeSteps.Regroup
public import Sarkozy.EnvelopeSteps.Multiplicative
public import Sarkozy.EnvelopeSteps.Constructor
public import Sarkozy.ClassInputsPaper.VarianceRecords

@[expose] public section

/-!
# The energies of Steps 1–2 at the paper's data: (P5) and (N4)

`paper/sections/23_envelopes.tex`, proof of `thm:envelopes`, Steps 1–2;
`paper/sections/10_comparison_lemmas.tex`, `it:record:P5`; (CP3) (the brackets
`(Ñ_𝔅 λ_𝔅; λ_𝔅 Ñ_𝔅) ⪰_ι 0`, `GramBracket.bracket`).

For the comparison data `D` of the construction (`TheoremCBlock.ComparisonData`), at a level `L`,
a set `A` and a block set `S` (the support of a selection):

* `lamOut`, `NOut`: the tensors of `λ_𝔅` and of the bracket `Ñ_𝔅` over the blocks outside `S`;
  `bracketOut`: they form a bracket (`Bracket.tensor` of (CP3));
* `paperElam`, `paperEN`: the energies `κ ↦ Y_{κ ⊗ λ_{-S}}` and `κ ↦ Y^Ñ[κ] = Y_{κ ⊗ Ñ_{-S}}`
  of joint laws `κ` on the labels of `S`, with the integrand `blockLift` of `A`;
* **`paper_P5`**: (P5) holds for them — `κ ± ζ ⪰_ι 0` gives `|Y_{ζ ⊗ λ_{-S}}| ≤ Y^Ñ[κ]`;
* **`term_eq_paperElam`**: the term `I_ω` of a selection is `paperElam` of the tensor of its
  selected factors (B10's `term_eq_support` and `jointEnergy_tensor`);
* **`hI_of_N4`**: hence (N4) of `DegreeOps` follows from the identity of laws
  `⊗_{𝔅 ∈ X} ζ_{ω(𝔅),𝔅} = π̃_ω ([L_ω]_ω + [Υ_ω]_ω)` (the star form (N1)–(N4) of the records);
* **`paperDegreeOps`**: `DegreeOps` at the paper's data, with `Eλ`, `EN`, (P5) and (N4) supplied
  as above;
* **`hN4_of_records`**: the identity of laws `hN4` from the per-block records
  `ζ_{ω(𝔅),𝔅} = w_𝔅 [Δ̂_𝔅]_{ω(𝔅)}` and `L_ω + Υ_ω = ⊗_𝔅 Δ̂_𝔅` (`place_tensor`).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.EnvelopeSteps

open Sarkozy.ClassInputsPaper Sarkozy.ClassBoundsPaper Sarkozy.TheoremC Sarkozy.TheoremCBlock
  Sarkozy.BlockFrame Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice

section Paper

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)

/-- The labels of a block set `S`. -/
abbrev PIn (L : ℕ) (S : Finset (BlockAtom Bk J L)) : Type :=
  InLabel (X := fun b => BlockLabel m₀ blk p L b) S

/-- The labels of the blocks outside `S`. -/
abbrev POut (L : ℕ) (S : Finset (BlockAtom Bk J L)) : Type :=
  OutLabel (X := fun b => BlockLabel m₀ blk p L b) S

/-- `λ_{-S}`: the tensor of the first-stage laws outside `S`. -/
noncomputable def lamOut (L : ℕ) (S : Finset (BlockAtom Bk J L)) :
    ((Slot → POut (m₀ := m₀) (blk := blk) (p := p) L S) → ℝ) →ₗ[ℝ] ℝ :=
  tensorLaw fun b : {b // b ∉ S} => D.FS.lam L b.1

/-- `Ñ_{-S}`: the tensor of the brackets outside `S`. -/
noncomputable def NOut (L : ℕ) (S : Finset (BlockAtom Bk J L)) :
    ((Slot → POut (m₀ := m₀) (blk := blk) (p := p) L S) → ℝ) →ₗ[ℝ] ℝ :=
  tensorLaw fun b : {b // b ∉ S} => D.GB.N L b.1

omit [DecidableEq P] in
/-- **The outside laws form a bracket** (`Bracket.tensor` of the brackets of (CP3)). -/
theorem bracketOut (L : ℕ) (S : Finset (BlockAtom Bk J L)) :
    reservedCut.Bracket (NOut D L S) (lamOut D L S) (NOut D L S) :=
  ReflectionCut.Bracket.tensor fun b => D.GB.bracket L b.1

/-- `κ ↦ Y_{κ ⊗ λ_{-S}}` on joint laws on the labels of `S`. -/
noncomputable def paperElam (L : ℕ) (A : Finset ℤ) (S : Finset (BlockAtom Bk J L)) :
    (((Slot → PIn (m₀ := m₀) (blk := blk) (p := p) L S) → ℝ) →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ :=
  jointEnergyL (lamOut D L S) (fun z => blockLift m₀ blk p L A (merge S z))

/-- `κ ↦ Y^Ñ[κ] = Y_{κ ⊗ Ñ_{-S}}` on joint laws on the labels of `S`. -/
noncomputable def paperEN (L : ℕ) (A : Finset ℤ) (S : Finset (BlockAtom Bk J L)) :
    (((Slot → PIn (m₀ := m₀) (blk := blk) (p := p) L S) → ℝ) →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ :=
  jointEnergyL (NOut D L S) (fun z => blockLift m₀ blk p L A (merge S z))

omit [DecidableEq P] in
/-- **(P5) at the paper's data**: `κ ± ζ ⪰_ι 0` gives `|Y_{ζ ⊗ λ_{-S}}| ≤ Y^Ñ[κ]`. -/
theorem paper_P5 (L : ℕ) (A : Finset ℤ) (S : Finset (BlockAtom Bk J L)) :
    P5 reservedCut (paperElam D L A S) (paperEN D L A S) := by
  intro κ ζ hp hm
  unfold paperElam paperEN
  rw [jointEnergyL_apply, jointEnergyL_apply]
  exact jointEnergy_P5 reservedCut (bracketOut D L S)
    (fun z => blockLift m₀ blk p L A (merge S z)) hp hm

/-- The tensor of the selected factors of a selection on its support. -/
noncomputable def selTensor (L : ℕ) (ω : Choice (D.CL.T L)) :
    ((Slot → PIn (m₀ := m₀) (blk := blk) (p := p) L (Choice.support ω)) → ℝ) →ₗ[ℝ] ℝ :=
  tensorLaw fun b : {b // b ∈ Choice.support ω} =>
    entryFactor (D.FS.lam L b.1) (D.CL.ζ L b.1) (ω b.1)

omit [DecidableEq P] in
/-- **The term of a selection is the joint energy of its selected tensor**:
`I_ω = Y_{(⊗_{𝔅 ∈ X} ζ_{ω(𝔅),𝔅}) ⊗ λ_{-X}}`. -/
theorem term_eq_paperElam (L : ℕ) (A : Finset ℤ) (ω : Choice (D.CL.T L)) :
    term (D.FS.lam L) (D.CL.ζ L) (blockLift m₀ blk p L A) ω =
      paperElam D L A (Choice.support ω) (selTensor D L ω) := by
  rw [term_eq_support]
  set S := Choice.support ω
  let L' : ∀ b : BlockAtom Bk J L, SlotMeasure (BlockLabel m₀ blk p L b) := fun b =>
    if b ∈ S then entryFactor (D.FS.lam L b) (D.CL.ζ L b) (ω b) else D.FS.lam L b
  have h1 : (fun b : {b // b ∈ S} => L' b.1) =
      fun b : {b // b ∈ S} => entryFactor (D.FS.lam L b.1) (D.CL.ζ L b.1) (ω b.1) := by
    funext b
    simp only [L', b.2, ↓reduceIte]
  have h2 : (fun b : {b // b ∉ S} => L' b.1) = fun b : {b // b ∉ S} => D.FS.lam L b.1 := by
    funext b
    simp only [L', b.2, ↓reduceIte]
  have key := jointEnergy_tensor S L' (blockLift m₀ blk p L A)
  rw [h1, h2] at key
  exact key.symm

omit [DecidableEq P] in
/-- **(N4) from the star form of the records**: if the selected tensor is
`π̃_ω ([L_ω]_ω + [Υ_ω]_ω)` as a law on the labels of `X`, then
`I_ω = π̃_ω (Y_{[L_ω]_ω ⊗ λ_{-X}} + Y_{[Υ_ω]_ω ⊗ λ_{-X}})`. -/
theorem hI_of_N4 (L : ℕ) (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (lead rem : ((Slot → PIn (m₀ := m₀) (blk := blk) (p := p) L (Choice.support ω)) → ℝ) →ₗ[ℝ] ℝ)
    (wt : ℝ) (hN4 : selTensor D L ω = wt • (lead + rem)) :
    term (D.FS.lam L) (D.CL.ζ L) (blockLift m₀ blk p L A) ω =
      wt * (paperElam D L A (Choice.support ω) lead +
        paperElam D L A (Choice.support ω) rem) := by
  rw [term_eq_paperElam, hN4, map_smul, map_add, smul_eq_mul]

omit [DecidableEq P] in
/-- **`DegreeOps` at the paper's data**: the energies are `paperElam`, `paperEN` on the support of
each selection, (P5) is `paper_P5`, and (N4) is reduced to the identity of laws
`⊗_{𝔅 ∈ X} ζ_{ω(𝔅),𝔅} = π̃_ω ([L_ω]_ω + [Υ_ω]_ω)` (`hN4`). The other inputs are those of
`DegreeOps`. -/
noncomputable def paperDegreeOps (L : ℕ) (A : Finset ℤ) (𝒞 : Finset (Choice (D.CL.T L)))
    (π ρ rr : Choice (D.CL.T L) → ℝ) (WZ z K : ℝ)
    (Obj : Choice (D.CL.T L) → Type) [∀ ω, Fintype (Obj ω)] [∀ ω, DecidableEq (Obj ω)]
    (m : ∀ ω, Obj ω → ℝ)
    (φ : ∀ ω, Obj ω → (reservedCut.Half → PIn (m₀ := m₀) (blk := blk) (p := p) L
      (Choice.support ω)))
    (Lop Υop Dop : ∀ ω, (Obj ω → ℝ) →ₗ[ℝ] (Obj ω → ℝ))
    (hdom : ∀ ω ∈ 𝒞, OpLE (m ω) (Lop ω) (Dop ω) ∧ OpLE (m ω) (-Lop ω) (Dop ω))
    (υ : Choice (D.CL.T L) → ℝ) (hυ : ∀ ω ∈ 𝒞, 0 ≤ υ ω)
    (hΥsym : ∀ ω ∈ 𝒞, ∀ f g, ip (m ω) f (Υop ω g) = ip (m ω) g (Υop ω f))
    (hΥ : ∀ ω ∈ 𝒞, ∀ f, |ip (m ω) f (Υop ω f)| ≤ υ ω * ip (m ω) f f)
    (B : ℝ) (CX r₁' : Choice (D.CL.T L) → ℝ)
    (hE1 : ∀ ω ∈ 𝒞, paperEN D L A (Choice.support ω)
      (reservedCut.diagonalLaw (push (m ω) (φ ω))) ≤ (B + z) * CX ω * D.Y L A + r₁' ω)
    (wt : Choice (D.CL.T L) → ℝ) (hwt : ∀ ω ∈ 𝒞, 0 ≤ wt ω)
    (hN4 : ∀ ω ∈ 𝒞, selTensor D L ω =
      wt ω • (place reservedCut (m ω) (φ ω) (Lop ω) + place reservedCut (m ω) (φ ω) (Υop ω)))
    (YN0 Mω Mh r₃ : Choice (D.CL.T L) → ℝ) (r₄ M Minv Rerr tU tδ : ℝ) (hR : 0 ≤ Rerr)
    (htδ : 0 ≤ tδ)
    (step3 : ∀ ω ∈ 𝒞, paperEN D L A (Choice.support ω)
      (place reservedCut (m ω) (φ ω) (Dop ω)) ≤
      YN0 ω + (Mω ω * Rerr - Mh ω * Real.exp tU * tδ + z) * CX ω * D.Y L A + r₃ ω)
    (step4 : ∑ ω ∈ 𝒞, wt ω * YN0 ω ≤ WZ + z * (∑ ω ∈ 𝒞, wt ω * CX ω) * D.Y L A + r₄)
    (hM : ∑ ω ∈ 𝒞, wt ω * CX ω * Mω ω ≤ M * ∑ ω ∈ 𝒞, wt ω * CX ω)
    (hMinv : Minv * ∑ ω ∈ 𝒞, wt ω * CX ω ≤ ∑ ω ∈ 𝒞, wt ω * CX ω * Mh ω)
    (hρ : (M * Rerr - Minv * Real.exp tU * tδ) * (∑ ω ∈ 𝒞, wt ω * CX ω) +
      B * (∑ ω ∈ 𝒞, wt ω * υ ω * CX ω) ≤ ∑ ω ∈ 𝒞, ρ ω)
    (hπ : ∀ ω ∈ 𝒞, wt ω * (2 + υ ω) * CX ω ≤ K * π ω)
    (hrr : ∑ ω ∈ 𝒞, wt ω * (υ ω * r₁' ω + r₃ ω) + r₄ ≤ ∑ ω ∈ 𝒞, rr ω) :
    DegreeOps reservedCut 𝒞 (fun ω => term (D.FS.lam L) (D.CL.ζ L) (blockLift m₀ blk p L A) ω)
      π ρ rr WZ (D.Y L A) z K where
  Obj := Obj
  instFO := inferInstance
  instDO := inferInstance
  Lab ω := PIn (m₀ := m₀) (blk := blk) (p := p) L (Choice.support ω)
  instFL _ := inferInstance
  instDL _ := inferInstance
  Elam ω := paperElam D L A (Choice.support ω)
  EN ω := paperEN D L A (Choice.support ω)
  hE ω _ := paper_P5 D L A (Choice.support ω)
  m := m
  φ := φ
  Lop := Lop
  Υop := Υop
  Dop := Dop
  hdom := hdom
  υ := υ
  hυ := hυ
  hΥsym := hΥsym
  hΥ := hΥ
  B := B
  CX := CX
  r₁' := r₁'
  hE1 := hE1
  wt := wt
  hwt := hwt
  hI ω hω := hI_of_N4 D L A ω _ _ (wt ω) (hN4 ω hω)
  YN0 := YN0
  Mω := Mω
  Mh := Mh
  r₃ := r₃
  r₄ := r₄
  M := M
  Minv := Minv
  Rerr := Rerr
  tU := tU
  tδ := tδ
  hR := hR
  htδ := htδ
  step3 := step3
  step4 := step4
  hM := hM
  hMinv := hMinv
  hρ := hρ
  hπ := hπ
  hrr := hrr

omit [DecidableEq P] in
/-- **(N4) from the records**: if every selected factor of `ω` is `w_𝔅 [Δ̂_𝔅]_{ω(𝔅)}` (the skew
change `ζ^a_{𝔅,φ} = w r_𝔅² [Δ̂_{φ,𝔅}]_φ` of `subsec:envelope-tools`, a per-block identity of laws),
and `L_ω + Υ_ω` is the tensor `⊗_𝔅 Δ̂_𝔅` (its kernel relative to the product marginal is the
product of the kernels; this is the definition of `Υ_ω`), then the identity of laws `hN4` of
`paperDegreeOps` holds with `π̃_ω = ∏_𝔅 w_𝔅`, the product marginal and the product placement
(`place_tensor`). -/
theorem hN4_of_records (L : ℕ) (ω : Choice (D.CL.T L))
    (O : {b // b ∈ Choice.support ω} → Type) [∀ b, Fintype (O b)] [∀ b, DecidableEq (O b)]
    (m : ∀ b, O b → ℝ) (φ : ∀ b, O b → (reservedCut.Half → BlockLabel m₀ blk p L b.1))
    (Δ : ∀ b, (O b → ℝ) →ₗ[ℝ] (O b → ℝ)) (w : {b // b ∈ Choice.support ω} → ℝ)
    (hrec : ∀ b, entryFactor (D.FS.lam L b.1) (D.CL.ζ L b.1) (ω b.1) =
      w b • place reservedCut (m b) (φ b) (Δ b))
    (Lop Υop : ((∀ b, O b) → ℝ) →ₗ[ℝ] ((∀ b, O b) → ℝ))
    (hK : ∀ x y, kern (prodWeight m) (Lop + Υop) x y = ∏ b, kern (m b) (Δ b) (x b) (y b)) :
    selTensor D L ω = (∏ b, w b) • (place reservedCut (prodWeight m) (prodPlace reservedCut φ) Lop +
      place reservedCut (prodWeight m) (prodPlace reservedCut φ) Υop) := by
  unfold selTensor
  rw [show (fun b : {b // b ∈ Choice.support ω} =>
      entryFactor (D.FS.lam L b.1) (D.CL.ζ L b.1) (ω b.1)) =
      fun b => w b • place reservedCut (m b) (φ b) (Δ b) from funext hrec,
    tensorLaw_smul, ← place_add, place_tensor reservedCut m φ Δ (Lop + Υop) hK]

end Paper

end Sarkozy.EnvelopeSteps
