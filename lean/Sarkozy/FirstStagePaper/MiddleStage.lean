module

public import Sarkozy.FirstStagePaper.Assembly
public import Sarkozy.FirstStagePaper.BlockBound
public import Sarkozy.PartVRecords.Prices
public import Sarkozy.PartVRecords.Polarization

@[expose] public section

/-!
# The first stage of a middle block (`def:record:frame`, `def:cp2`)

`paper/sections/20c_middle_frame.tex`: `def:record:frame`(d)–(e), `lem:middle-polarization`, the
paragraph "(CP2)(b)" after `lem:record:one-stage-folded-e`, and `lem:record:middle-prices`.

On a middle block (V3's `middleFrame`: V1's block field laws with a root, the weights `W`, the
inputs `I`, `r`, the least prime `b`, and `κnew = blockPlusLaw`), the data of `def:cp2` at the atom:

* (a) `ρ = μ - F_fold + E_add + G`, with `ρ - μ = ∑ c_i κ_i` over the six normalized one-layer
  records `Diag_ι(Π⁽¹⁾_φ)` (`φ = F₁, F₂, E₀, E₁, G₀₀, G₁₁`), each a positive record (V3's
  `isPositiveRecord_diag`), with coefficients `∓P⁻¹ v_D r²` and `P⁻¹ (f₁ + h₁) r v_D r²`
  (`middle_rho_sub`); `ρ ⪰_{ϑ₀} μ` at `ϑ₀ = firstChamberCut 0` (V3's `middleFrame_rho_ge_mu`, from
  the rows `lem:front12:reference`(i), `j = 1`, a field of V2's block specification);
* (b) two tags `s ∈ {0, 1}`, with cuts `ϑ₁ = firstChamberCut 1`, `ϑ₂ = firstChamberCut 2`
  (`tagCut`, `cert:record:middle-geometry`); the difference of tag `s` is `κ'_s - κ_s` with
  `κ_s = oldRec s` (the folded matching record of type `E_s`) and `κ'_s = newRecN s` (its
  replacement), positive records of equal mass (V3's `newRecN_mass_eq`), with the sharp constant
  `d`.

The sharp bound of (b) is reduced, by scaling (`hasSharpBound_smul`), to the normalized block
statement **`BlockSharp pr hne h d`**: for `s = 0, 1`, the replacement `plusRec s` of the normalized
folded matching record `matchRec s` differs from it with sharp bound `d` at `tagCut s`
(`lem:record:one-stage-folded-e`(e), with `d = k_new(X) b^{-1/2}` by (d), `block_delta_form_le`).
`middleStage` is the data of the atom given `BlockSharp`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.FirstStagePaper

open Sarkozy.TheoremC Sarkozy.PartVRecords Sarkozy.PartV Sarkozy.Labellings Sarkozy.FiveType
  Sarkozy.RecordExpansion

/-! ## The tags -/

/-- **The cuts of the two tags** (`def:record:frame`(e), `cert:record:middle-geometry`): `ϑ₁` for
the records of type `E₀`, `ϑ₂` for those of type `E₁`. -/
def tagCut : Fin 2 → ReflectionCut Slot := ![firstChamberCut 1, firstChamberCut 2]

theorem tagCut_family (s : Fin 2) : IsFamilyCut (tagCut s) := by
  fin_cases s
  · exact Or.inl ⟨1, rfl⟩
  · exact Or.inl ⟨2, rfl⟩

/-- The polarization cut `ϑ₀` (`lem:middle-polarization`). -/
theorem firstChamberCut_zero_family : IsFamilyCut (firstChamberCut 0) := Or.inl ⟨0, rfl⟩

/-! ## Sharp bounds under scaling -/

/-- **A sharp bound scales** (`def:price`(b)): if `ζ` has sharp bound `d` relative to `κ`, then
`w ζ` has sharp bound `d` relative to `w κ`. -/
theorem hasSharpBound_smul {X : Type} [Fintype X] [DecidableEq X] {c : ReflectionCut Slot}
    {κ ζ : SlotMeasure X} {d : ℝ} (h : HasSharpBound c κ ζ d) (w : ℝ) :
    HasSharpBound c (w • κ) (w • ζ) d := by
  obtain ⟨S, hS, π, κs, Ks, hprob, hκ, hζ, hsharp⟩ := h
  have hm : mass (w • κ) = w * mass κ := rfl
  refine ⟨S, hS, π, κs, Ks, hprob, ?_, ?_, hsharp⟩
  · rw [hm, mul_smul, ← hκ]
  · rw [hm, mul_smul, ← hζ]

/-! ## The normalized records of a block -/

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- **The normalized folded matching record of type `E_s`** of a middle block: the one-layer `E`
block law (`Π⁽¹⁾_{E}`, uniform on the injective labellings at every prime) placed on the reserved
diagonal by `E_s` (`Diag_ι(Π⁽¹⁾_{E_s})`). -/
noncomputable def matchRec (hne : MiddleNonempty pr) (s : Fin 2) : SlotMeasure (BlockLabel pr) :=
  signedIntegral (emit (blockGraphLaw pr (matchGraph (Fin 1)) hne.E1)
    (midDiagEmission (matching s))).weight

/-- **Its replacement** (`lem:record:one-stage-folded-e`(e)): the block replacement law
`blockPlusLaw` (shared label uniform, private pair by `⊗_p 𝒦₊^{(c_p)}`) placed by `E_s`. -/
noncomputable def plusRec (h : ClassThreeBlock pr) (s : Fin 2) : SlotMeasure (BlockLabel pr) :=
  signedIntegral (emit (blockPlusLaw pr h) (midDiagEmission (matching s))).weight

/-- **The sharp bound of the one-stage replacement on a block** (`lem:record:one-stage-folded-e`(e),
the sharp operator bound, at the record's own first-coordinate cut, in the sense of
`def:price`(b)): for `s = 0, 1`, `plusRec s - matchRec s` has sharp bound `d` relative to
`matchRec s` at `tagCut s`. In the paper `d = k_new(X) b^{-1/2}`, from (d). -/
def BlockSharp (hne : MiddleNonempty pr) (h : ClassThreeBlock pr) (d : ℝ) : Prop :=
  ∀ s, HasSharpBound (tagCut s) (matchRec pr hne s) (plusRec pr h s - matchRec pr hne s) d

/-! ## The atom data of a middle block -/

variable (hne : MiddleNonempty pr) (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr))
  (W : MiddleWeights) (I : MiddleInputs) {r : ℝ} (hr : 0 ≤ r) (bmin : ℝ) (h : ClassThreeBlock pr)

/-- The coefficient `P⁻¹ v_D r²` of the fold and added matching records in `ρ - μ`. -/
noncomputable def coefD : ℝ :=
  (middleFrame pr hne root W I hr bmin h).P⁻¹ * (W.v .D * r ^ 2)

/-- The coefficient `P⁻¹ (f₁ + h₁) r v_D r²` of the merge records in `ρ - μ`. -/
noncomputable def coefG : ℝ :=
  (middleFrame pr hne root W I hr bmin h).P⁻¹ * ((I.f₁ + I.h₁) * r) * (W.v .D * r ^ 2)

/-- The six records of `ρ - μ`: `Diag_ι(Π⁽¹⁾_φ)` for `φ = F₁, F₂, E₀, E₁, G₀₀, G₁₁`. -/
noncomputable def rhoRecs : Fin 6 → SlotMeasure (BlockLabel pr) :=
  let D := middleFrame pr hne root W I hr bmin h
  ![D.diag .D (1 : Fin 3), D.diag .D (2 : Fin 3), D.diag .S (0 : Fin 2), D.diag .S (1 : Fin 2),
    D.diag .R ((0 : Fin 2), (0 : Fin 3)), D.diag .R ((1 : Fin 2), (1 : Fin 3))]

/-- Their coefficients `-P⁻¹ v_D r²` (twice), `P⁻¹ v_D r²` (twice),
`P⁻¹ (f₁ + h₁) r v_D r²` (twice). -/
noncomputable def rhoCoefs : Fin 6 → ℝ :=
  ![-coefD pr hne root W I hr bmin h, -coefD pr hne root W I hr bmin h,
    coefD pr hne root W I hr bmin h, coefD pr hne root W I hr bmin h,
    coefG pr hne root W I hr bmin h, coefG pr hne root W I hr bmin h]

/-- **`ρ - μ = ∑ c_i κ_i`** (`def:record:frame`(d), (CP2)(a)): `-F_fold + E_add + G` over `P(r)`,
record by record. -/
theorem middle_rho_sub :
    (middleFrame pr hne root W I hr bmin h).rho -
        signedIntegral (middleBlockReference pr hne root W hr).weight =
      ∑ i, rhoCoefs pr hne root W I hr bmin h i • rhoRecs pr hne root W I hr bmin h i := by
  rw [← middleFrame_mu pr hne root W I hr bmin h, FrameData.rho_sub_mu_eq]
  rw [Fin.sum_univ_six]
  apply LinearMap.ext
  intro f
  simp only [rhoCoefs, rhoRecs, coefD, coefG, FrameData.Ffold, FrameData.Eadd, FrameData.Gpol,
    FrameData.Ge, FrameData.Go, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  simp only [middleFrame]
  ring

theorem rhoRecs_positive (i : Fin 6) : IsPositiveRecord (rhoRecs pr hne root W I hr bmin h i) := by
  have h1 := middleFrame_one_uniform pr hne root W I hr bmin h
  have hpos := fun (t : PType) (φ : t.Pat) =>
    (middleFrame pr hne root W I hr bmin h).isPositiveRecord_diag h1 t φ zero_le_one
  simp only [one_smul] at hpos
  fin_cases i
  · exact hpos .D 1
  · exact hpos .D 2
  · exact hpos .S 0
  · exact hpos .S 1
  · exact hpos .R (0, 0)
  · exact hpos .R (1, 1)

/-- The folded matching record of the frame is the scaled normalized one. -/
theorem middle_oldRec (s : Fin 2) :
    (middleFrame pr hne root W I hr bmin h).oldRec s =
      ((middleFrame pr hne root W I hr bmin h).P⁻¹ * ((W.v .S + W.v .D) * r ^ 2)) •
        matchRec pr hne s := rfl

/-- The replacement record of the frame is the scaled normalized one. -/
theorem middle_newRecN (s : Fin 2) :
    (middleFrame pr hne root W I hr bmin h).newRecN s =
      ((middleFrame pr hne root W I hr bmin h).P⁻¹ * ((W.v .S + W.v .D) * r ^ 2)) •
        plusRec pr h s := rfl

/-- **The sharp bounds of the frame's tagged differences** (the paragraph "(CP2)(b)" after
`lem:record:one-stage-folded-e`), from the normalized block statement. -/
theorem middle_sharp {d : ℝ} (hs : BlockSharp pr hne h d) (s : Fin 2) :
    HasSharpBound (tagCut s) ((middleFrame pr hne root W I hr bmin h).oldRec s)
      ((middleFrame pr hne root W I hr bmin h).newRecN s -
        (middleFrame pr hne root W I hr bmin h).oldRec s) d := by
  have hw := hasSharpBound_smul (hs s)
    ((middleFrame pr hne root W I hr bmin h).P⁻¹ * ((W.v .S + W.v .D) * r ^ 2))
  rw [smul_sub] at hw
  rw [middle_oldRec, middle_newRecN]
  exact hw

/-- **The first-stage data of a middle block** (`def:cp2` at the atom; `def:record:frame`,
`lem:middle-polarization`, `lem:record:one-stage-folded-e`(e)), given the rows
`lem:front12:reference`(i) (`j = 1`) and the normalized block sharp bound `BlockSharp` with
constant `d ≥ 0`. -/
noncomputable def middleStage
    (hrows₁ : RowBounds (fieldDatum (middleBlock_datumHyp₁ pr hne)) I.f₁ I.h₁ r)
    {d : ℝ} (hd : 0 ≤ d) (hs : BlockSharp pr hne h d) :
    FirstStagePaper.AtomStage (signedIntegral (middleBlockReference pr hne root W hr).weight)
      (Fin 2) tagCut (firstChamberCut 0) where
  first := true
  ρ := (middleFrame pr hne root W I hr bmin h).rho
  Ia := Fin 6
  ca := rhoCoefs pr hne root W I hr bmin h
  κa := rhoRecs pr hne root W I hr bmin h
  κa_pos := rhoRecs_positive pr hne root W I hr bmin h
  ρ_sub := middle_rho_sub pr hne root W I hr bmin h
  ρ_ge _ := by
    rw [← middleFrame_mu pr hne root W I hr bmin h]
    exact middleFrame_rho_ge_mu pr hne root W I hr bmin h hrows₁
  ρ_off hf := absurd hf (by decide)
  Ib := Fin 2
  κ := (middleFrame pr hne root W I hr bmin h).oldRec
  κ' := (middleFrame pr hne root W I hr bmin h).newRecN
  κ_pos s := (middleFrame pr hne root W I hr bmin h).isPositiveRecord_diag
    (middleFrame_one_uniform pr hne root W I hr bmin h) .S s
    (middleFrame pr hne root W I hr bmin h).recCoef_nonneg
  κ'_pos s := middleFrame_newRec_positiveRecord pr hne root W I hr bmin h s
    (middleFrame pr hne root W I hr bmin h).recCoef_nonneg
  mass_eq := (middleFrame pr hne root W I hr bmin h).newRecN_mass_eq
  tag := id
  dconst _ := d
  dconst_nonneg _ := hd
  sharp := middle_sharp pr hne root W I hr bmin h hs
  off hf := absurd hf (by decide)

/-- **The first stage of a middle block is the frame's `λ`** (`def:record:frame`(d),
`λ = ρ + δ_E`, `δ_E = ∑_s (κ'_s - κ_s)`): the atom's `ρ + ∑_i (κ'_i - κ_i)` is V3's `lam`, the
law of `lem:record:gram` (the input of (CP3)). -/
theorem middleStage_lam
    (hrows₁ : RowBounds (fieldDatum (middleBlock_datumHyp₁ pr hne)) I.f₁ I.h₁ r)
    {d : ℝ} (hd : 0 ≤ d) (hs : BlockSharp pr hne h d) :
    (middleStage pr hne root W I hr bmin h hrows₁ hd hs).ρ +
        ∑ i, ((middleStage pr hne root W I hr bmin h hrows₁ hd hs).κ' i -
          (middleStage pr hne root W I hr bmin h hrows₁ hd hs).κ i) =
      (middleFrame pr hne root W I hr bmin h).lam := by
  rw [FrameData.lam_eq_rho_add_deltaE, FrameData.deltaE_eq_sum]
  rfl

/-! ## The prices of a middle block (`lem:record:middle-prices`) -/

variable (hrows₁ : RowBounds (fieldDatum (middleBlock_datumHyp₁ pr hne)) I.f₁ I.h₁ r)
  {d : ℝ} (hd : 0 ≤ d) (hs : BlockSharp pr hne h d)

/-- **The variation price of `ρ - μ`** (`lem:record:middle-prices`, `F_fold + E_add + G`): with
`c_D = P⁻¹ v_D r²` and `c_G = P⁻¹ (f₁ + h₁) r v_D r²`, `p_𝔅 = (4 |c_D| + 2 |c_G|) q_𝔅^{2a}`, i.e.
`P(r)⁻¹ (4 v_D r² + 2 v_D |f₁ + h₁| r³) q_𝔅^{2a}`. -/
theorem middleStage_pvar (sel : ℝ) :
    (middleStage pr hne root W I hr bmin h hrows₁ hd hs).pvar sel =
      (4 * |coefD pr hne root W I hr bmin h| + 2 * |coefG pr hne root W I hr bmin h|) * sel := by
  have hm : ∀ (t : PType) (φ : t.Pat),
      mass ((middleFrame pr hne root W I hr bmin h).diag t φ) = 1 :=
    fun t φ => (middleFrame pr hne root W I hr bmin h).diag_mass t φ
  change ∑ i : Fin 6, |rhoCoefs pr hne root W I hr bmin h i| *
    mass (rhoRecs pr hne root W I hr bmin h i) * sel = _
  rw [Fin.sum_univ_six]
  simp only [rhoCoefs, rhoRecs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hm,
    abs_neg]
  ring

/-- **The sharp price of tag `j`** (`lem:record:middle-prices`, `δ_E`, sharp, per tag):
`κ_j(1) d q_𝔅^{2a} = P(r)⁻¹ (v_S + v_D) r² d q_𝔅^{2a}`; with `d = k_new(X) b^{-1/2}` and
`r = b^{-1/2}` it is `P(r)⁻¹ (v_S + v_D) k_new(X) r³ q_𝔅^{2a}`, the same for both tags. -/
theorem middleStage_dTag (sel : ℝ) (j : Fin 2) :
    (middleStage pr hne root W I hr bmin h hrows₁ hd hs).dTag sel j =
      (middleFrame pr hne root W I hr bmin h).P⁻¹ * ((W.v .S + W.v .D) * r ^ 2) * d * sel := by
  change ∑ s : Fin 2, (if s = j then
    sharpPrice sel ((middleFrame pr hne root W I hr bmin h).oldRec s) d else 0) = _
  rw [Finset.sum_ite_eq' univ j, ite_eq_left (mem_univ j), sharpPrice, FrameData.oldRec_mass]
  rfl

/-- **The variation price of tag `j`** (`lem:record:middle-prices`, `δ_E`, variation, per tag):
`(κ_j(1) + κ'_j(1)) q_𝔅^{2a} = 2 P(r)⁻¹ (v_S + v_D) r² q_𝔅^{2a}`, the same for both tags. -/
theorem middleStage_vTag (sel : ℝ) (j : Fin 2) :
    (middleStage pr hne root W I hr bmin h hrows₁ hd hs).vTag sel j =
      2 * ((middleFrame pr hne root W I hr bmin h).P⁻¹ * ((W.v .S + W.v .D) * r ^ 2)) * sel := by
  change ∑ s : Fin 2, (if s = j then
    (mass ((middleFrame pr hne root W I hr bmin h).oldRec s) +
      mass ((middleFrame pr hne root W I hr bmin h).newRecN s)) * sel else 0) = _
  rw [Finset.sum_ite_eq' univ j, ite_eq_left (mem_univ j), FrameData.newRecN_mass,
    FrameData.oldRec_mass]
  have hW : (middleFrame pr hne root W I hr bmin h).W = W := rfl
  have hr' : (middleFrame pr hne root W I hr bmin h).r = r := rfl
  rw [hW, hr']
  ring

end Block

end Sarkozy.FirstStagePaper
