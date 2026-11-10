module

public import Sarkozy.OpsCore.Tensor
public import Sarkozy.OpsCore.Assembly

@[expose] public section

/-!
# The star form of a selection: objects, (N4) and `hΥ` from per-record data (OPS-L)

`paper/sections/23_envelopes.tex`, `subsec:envelope-tools` (the normalized skew changes
`Δ̂_{φ,𝔅}`, the star form (N1)–(N4), `eq:oct24:star-tensor-error`), Step 1 of the proof of
`thm:envelopes`; `paper/sections/21_middle_records.tex`, `prop:signed-bounds`(b),(e).

For a selection `ω` with support `X`, the per-record data (`StarData`) are, at each block `𝔅` of
`X`: the actual half marginal `m_{ω(𝔅),𝔅}` on the half labellings, the raw-arm coefficient
`w_𝔅 > 0`, the leading star `L_𝔅` with its norm bounds `ℓ_𝔅`, `ρ_𝔅`, and a sign `ε_𝔅`. Then:

* the objects are the product of the half labellings, `m_ω = ⊗ m_𝔅`, `φ_ω` the product placement;
* `Δ̂_𝔅 = w_𝔅⁻¹ recOp(ζ_{ω(𝔅),𝔅})` (the paper's normalized skew change), `L_ω = ⊗ L_𝔅`,
  `Υ_ω = ⊗ Δ̂_𝔅 − ⊗ L_𝔅`, `π̃_ω = ∏ w_𝔅`, `υ_ω = ∏(ℓ + ρ) − ∏ ℓ`;
* **`StarOK.hN4`**: (N4) is a theorem (`hN4_of_records`, `record_eq_place`, `kern_tensorOp`),
  given only that each selected factor charges no plus half outside `m_𝔅` (`PlusIn`; B8's
  `HalvesIn` for the middle records);
* **`StarOK.hΥ`** (`star_tensor_error`) from `‖L_𝔅‖ ≤ ℓ_𝔅`, `‖Δ̂_𝔅 − L_𝔅‖ ≤ ρ_𝔅`;
  **`StarOK.hΥsym`** (`symm_tensorOp_sub`) from `ε_𝔅`-symmetric kernels with `∏ ε_𝔅 = 1`;
* **`DegreeInputs.ofStar`**: `DegreeInputs` from the star data and the other groups of inputs.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.OpsCore

open Sarkozy.ClassInputsPaper Sarkozy.EnvelopeSteps Sarkozy.MainFinal2
open Sarkozy.ClassBoundsPaper Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.BlockFrame
open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- The half labellings of a block of the support of `ω` (the objects of its record). -/
abbrev HalfB (L : ℕ) (S : Finset (BlockAtom Bk J L)) (b : {b // b ∈ S}) : Type :=
  reservedCut.Half → BlockLabel m₀ blk p L b.1

/-- **The per-record data of the star form of a selection** (data). -/
structure StarData (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (ω : Choice (D.CL.T L)) where
  /-- The actual half marginal `m_{ω(𝔅),𝔅}` of the selected record at each block. -/
  mB : ∀ b : {b // b ∈ Choice.support ω},
    HalfB (m₀ := m₀) (blk := blk) (p := p) L (Choice.support ω) b → ℝ
  /-- The raw-arm coefficient `w_𝔅`. -/
  w : {b // b ∈ Choice.support ω} → ℝ
  /-- The leading star `L_𝔅` (`it:env:N1`, `it:env:N3`). -/
  Lb : ∀ b : {b // b ∈ Choice.support ω},
    (HalfB (m₀ := m₀) (blk := blk) (p := p) L (Choice.support ω) b → ℝ) →ₗ[ℝ]
      (HalfB (m₀ := m₀) (blk := blk) (p := p) L (Choice.support ω) b → ℝ)
  /-- The norm bounds `ℓ_𝔅`, `ρ_𝔅` and the sign `ε_𝔅` (`−1` for a skew record). -/
  ℓ : {b // b ∈ Choice.support ω} → ℝ
  ρ : {b // b ∈ Choice.support ω} → ℝ
  ε : {b // b ∈ Choice.support ω} → ℝ

namespace StarData

variable {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} {L : ℕ} {ω : Choice (D.CL.T L)}
  (S : StarData D L ω)

/-- The selected factor `ζ_{ω(𝔅),𝔅}` at a block of the support. -/
noncomputable abbrev zeta (_S : StarData D L ω) (b : {b // b ∈ Choice.support ω}) :=
  entryFactor (D.FS.lam L b.1) (D.CL.ζ L b.1) (ω b.1)

/-- **The normalized record operator** `Δ̂_𝔅 = w_𝔅⁻¹ recOp(ζ_{ω(𝔅),𝔅})`. -/
noncomputable def Δhat (b : {b // b ∈ Choice.support ω}) :
    (HalfB (m₀ := m₀) (blk := blk) (p := p) L (Choice.support ω) b → ℝ) →ₗ[ℝ]
      (HalfB (m₀ := m₀) (blk := blk) (p := p) L (Choice.support ω) b → ℝ) :=
  (S.w b)⁻¹ • recOp reservedCut (S.mB b) (S.zeta b)

/-- The objects of the selection: the products of the half labellings. -/
abbrev Obj : Type :=
  ∀ b : {b // b ∈ Choice.support ω}, HalfB (m₀ := m₀) (blk := blk) (p := p) L (Choice.support ω) b

/-- `m_ω = ⊗ m_𝔅`. -/
noncomputable def m : Obj (D := D) (L := L) (ω := ω) → ℝ := prodWeight S.mB

/-- The product placement. -/
def φ (_S : StarData D L ω) : Obj (D := D) (L := L) (ω := ω) →
    (reservedCut.Half → PIn (m₀ := m₀) (blk := blk) (p := p) L (Choice.support ω)) :=
  prodPlace reservedCut fun _ => id

/-- `L_ω = ⊗ L_𝔅`. -/
noncomputable def Lop : ((Obj (D := D) (L := L) (ω := ω)) → ℝ) →ₗ[ℝ]
    ((Obj (D := D) (L := L) (ω := ω)) → ℝ) :=
  tensorOp S.Lb

/-- `Υ_ω = ⊗ Δ̂_𝔅 − ⊗ L_𝔅`. -/
noncomputable def Υop : ((Obj (D := D) (L := L) (ω := ω)) → ℝ) →ₗ[ℝ]
    ((Obj (D := D) (L := L) (ω := ω)) → ℝ) :=
  tensorOp S.Δhat - tensorOp S.Lb

/-- `π̃_ω = ∏ w_𝔅`. -/
noncomputable def wt : ℝ := ∏ b, S.w b

/-- `υ_ω = ∏ (ℓ_𝔅 + ρ_𝔅) − ∏ ℓ_𝔅`. -/
noncomputable def υ : ℝ := (∏ b, (S.ℓ b + S.ρ b)) - ∏ b, S.ℓ b

end StarData

/-- **The hypotheses of the star form** at one selection: the support condition of each selected
factor (`PlusIn`, from B8's `HalvesIn`), `m_𝔅 ≥ 0`, `w_𝔅 > 0`, the norm bounds of
`prop:signed-bounds`(b),(e) / (N1)–(N3), the `ε_𝔅`-symmetry of the kernels of `L_𝔅` and `Δ̂_𝔅`
(skew records: `ε = −1`), and `∏ ε_𝔅 = 1` (an even number of skew factors). -/
structure StarOK {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} {L : ℕ}
    {ω : Choice (D.CL.T L)} (S : StarData D L ω) : Prop where
  hplus : ∀ b, PlusIn reservedCut (S.mB b) (S.zeta b)
  hm : ∀ b x, 0 ≤ S.mB b x
  hw : ∀ b, 0 < S.w b
  hL : ∀ b, OpNormLE (S.mB b) (S.Lb b) (S.ℓ b)
  hE : ∀ b, OpNormLE (S.mB b) (S.Δhat b - S.Lb b) (S.ρ b)
  hε : ∏ b, S.ε b = 1
  hLs : ∀ b x y, kern (S.mB b) (S.Lb b) y x = S.ε b * kern (S.mB b) (S.Lb b) x y
  hΔs : ∀ b x y, kern (S.mB b) (S.Δhat b) y x = S.ε b * kern (S.mB b) (S.Δhat b) x y

namespace StarOK

variable {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} {L : ℕ} {ω : Choice (D.CL.T L)}
  {S : StarData D L ω}

omit [DecidableEq P] in
/-- **(N4) for the selection is a theorem**: `⊗_{𝔅 ∈ X} ζ_{ω(𝔅),𝔅} = π̃_ω([L_ω] + [Υ_ω])`. -/
theorem hN4 (H : StarOK S) :
    selTensor D L ω = S.wt • (place reservedCut S.m S.φ S.Lop + place reservedCut S.m S.φ S.Υop) :=
  hN4_of_records D L ω _ S.mB (fun _ => id) S.Δhat S.w
    (fun b => record_eq_place (H.hplus b) (H.hw b).ne') S.Lop S.Υop fun x y => by
      rw [StarData.Lop, StarData.Υop, add_sub_cancel, kern_tensorOp]

omit [DecidableEq P] in
theorem hwt (H : StarOK S) : 0 ≤ S.wt := prod_nonneg fun b _ => (H.hw b).le

omit [DecidableEq P] in
theorem hυ (H : StarOK S) : 0 ≤ S.υ := by
  unfold StarData.υ
  rw [sub_nonneg]
  exact Finset.prod_le_prod₀ (fun b _ => (H.hL b).1) fun b _ => le_add_of_nonneg_right (H.hE b).1

omit [DecidableEq P] in
/-- **`hΥ`** (`eq:oct24:star-tensor-error`): `|⟨f, Υ_ω f⟩| ≤ υ_ω ‖f‖²`. -/
theorem hΥ (H : StarOK S) (f : StarData.Obj (D := D) (L := L) (ω := ω) → ℝ) :
    |ip S.m f (S.Υop f)| ≤ S.υ * ip S.m f f := by
  have h := star_tensor_error H.hm H.hL H.hE f
  have e : (fun b => S.Lb b + (S.Δhat b - S.Lb b)) = S.Δhat := funext fun b => add_sub_cancel _ _
  rw [e] at h
  exact h

omit [DecidableEq P] in
/-- **`Υ_ω` is symmetric** (an even number of skew factors). -/
theorem hΥsym (H : StarOK S) (f g : StarData.Obj (D := D) (L := L) (ω := ω) → ℝ) :
    ip S.m f (S.Υop g) = ip S.m g (S.Υop f) := by
  have hEs : ∀ b x y, kern (S.mB b) (S.Δhat b - S.Lb b) y x =
      S.ε b * kern (S.mB b) (S.Δhat b - S.Lb b) x y := by
    intro b x y
    rw [kern_sub, kern_sub, H.hΔs, H.hLs]
    ring
  have h := symm_tensorOp_sub S.mB S.ε H.hε H.hLs hEs f g
  have e : (fun b => S.Lb b + (S.Δhat b - S.Lb b)) = S.Δhat := funext fun b => add_sub_cancel _ _
  rw [e] at h
  exact h

end StarOK

omit [DecidableEq P] in
/-- **`DegreeInputs` from the star form**: the objects, operators, (N4) and `hΥ` from the star
data (`StarOK`, proved fields), and the other groups of inputs as arguments: the envelope `D_ω`
with the domination (OPS-F), (E1) for `Diag_ω`, Steps 3 and 4 (OPS-S), the evaluations. -/
noncomputable def DegreeInputs.ofStar {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    {L : ℕ} {A : Finset ℤ} {𝒞 : Finset (Choice (D.CL.T L))} {π ρ rr : Choice (D.CL.T L) → ℝ}
    {Wd z K : ℝ} (S : ∀ ω, StarData D L ω) (hS : ∀ ω ∈ 𝒞, StarOK (S ω))
    (Dop : ∀ ω, (StarData.Obj (D := D) (L := L) (ω := ω) → ℝ) →ₗ[ℝ]
      (StarData.Obj (D := D) (L := L) (ω := ω) → ℝ))
    (hdom : ∀ ω ∈ 𝒞, OpLE (S ω).m (S ω).Lop (Dop ω) ∧ OpLE (S ω).m (-(S ω).Lop) (Dop ω))
    (B : ℝ) (CX r₁' : Choice (D.CL.T L) → ℝ)
    (hE1 : ∀ ω ∈ 𝒞, paperEN D L A (Choice.support ω)
      (reservedCut.diagonalLaw (push (S ω).m (S ω).φ)) ≤ (B + z) * CX ω * D.Y L A + r₁' ω)
    (YN0 Mω Mh r₃ : Choice (D.CL.T L) → ℝ) (Rerr tU tδ : ℝ) (hR : 0 ≤ Rerr) (htδ : 0 ≤ tδ)
    (step3 : ∀ ω ∈ 𝒞, paperEN D L A (Choice.support ω)
      (place reservedCut (S ω).m (S ω).φ (Dop ω)) ≤
      YN0 ω + (Mω ω * Rerr - Mh ω * Real.exp tU * tδ + z) * CX ω * D.Y L A + r₃ ω)
    (Wbg r₄ : ℝ)
    (step4 : ∑ ω ∈ 𝒞, (S ω).wt * YN0 ω ≤ Wbg + z * (∑ ω ∈ 𝒞, (S ω).wt * CX ω) * D.Y L A + r₄)
    (spill : ℝ) (hspill : Rerr ≠ 0 ∨ spill = 0)
    (hbg : Wbg ≤ Wd + spill * (∑ ω ∈ 𝒞, (S ω).wt * CX ω) * D.Y L A) (M Minv : ℝ)
    (hM : ∑ ω ∈ 𝒞, (S ω).wt * CX ω * Mω ω ≤ M * ∑ ω ∈ 𝒞, (S ω).wt * CX ω)
    (hMinv : Minv * ∑ ω ∈ 𝒞, (S ω).wt * CX ω ≤ ∑ ω ∈ 𝒞, (S ω).wt * CX ω * Mh ω)
    (hρ : (M * Rerr - Minv * Real.exp tU * tδ + spill) * (∑ ω ∈ 𝒞, (S ω).wt * CX ω) +
      B * (∑ ω ∈ 𝒞, (S ω).wt * (S ω).υ * CX ω) ≤ ∑ ω ∈ 𝒞, ρ ω)
    (hπ : ∀ ω ∈ 𝒞, (S ω).wt * (2 + (S ω).υ) * CX ω ≤ K * π ω)
    (hrr : ∑ ω ∈ 𝒞, (S ω).wt * ((S ω).υ * r₁' ω + r₃ ω) + r₄ ≤ ∑ ω ∈ 𝒞, rr ω) :
    DegreeInputs D L A 𝒞 π ρ rr Wd z K where
  Obj ω := StarData.Obj (D := D) (L := L) (ω := ω)
  m ω := (S ω).m
  φ ω := (S ω).φ
  Lop ω := (S ω).Lop
  Υop ω := (S ω).Υop
  Dop := Dop
  wt ω := (S ω).wt
  hwt ω hω := (hS ω hω).hwt
  hN4 ω hω := (hS ω hω).hN4
  υ ω := (S ω).υ
  hυ ω hω := (hS ω hω).hυ
  hΥsym ω hω := (hS ω hω).hΥsym
  hΥ ω hω := (hS ω hω).hΥ
  hdom := hdom
  B := B
  CX := CX
  r₁' := r₁'
  hE1 := hE1
  YN0 := YN0
  Mω := Mω
  Mh := Mh
  r₃ := r₃
  Rerr := Rerr
  tU := tU
  tδ := tδ
  hR := hR
  htδ := htδ
  step3 := step3
  Wbg := Wbg
  r₄ := r₄
  step4 := step4
  spill := spill
  hspill := hspill
  hbg := hbg
  M := M
  Minv := Minv
  hM := hM
  hMinv := hMinv
  hρ := hρ
  hπ := hπ
  hrr := hrr

end Sarkozy.OpsCore
