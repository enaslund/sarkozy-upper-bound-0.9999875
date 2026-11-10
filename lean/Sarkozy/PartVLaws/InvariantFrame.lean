module

public import Sarkozy.PartVRecords.Frame
public import Sarkozy.PartVLaws.InvariantBackground

@[expose] public section

/-!
# The invariant background of the middle frame (`lem:oct24:invariant-background`(iv))

`paper/sections/23_envelopes.tex`, `lem:oct24:invariant-background`(iv), on V3's middle frame
(`Sarkozy.PartVRecords.Frame`, `def:record:frame`): the records `E_add` (`FrameData.Eadd`), `H`
(`Hdiag`), `G` (`Gpol`) and `Ñ₀ = μ + E_add + G + H` (`Nbr0`), each divided by `P(r)` where V3
divides it.

**The statement.** At a middle block, `E_add` and `H` are `R_h`-invariant (`h = 1, 3, 5`) and `G`
is `R_5`-invariant; the *invariant background* `Ñ^inv = μ + E_add + H` (`NbrInv`) is invariant
under `R_1, R_3, R_5` and the group `𝒢₆` they generate; `Ñ₀` is `R_5`-invariant; and `Ñ^inv`,
`G` and `Ñ₀` are `⪰_ι 0`.

**The proof** (the paper's): `E_add` and `H` are combinations of the diagonal copies
`Diag_ι(Π⁽¹⁾_{E_s})`; `R_h` maps `Diag_ι(Π⁽¹⁾_{E_s})` to the diagonal copy of the one-layer `E` law
placed by `ψ_{h,s} ∘ E_s`, which is the same measure, the `E` law being exchangeable
(`diag_matching_slotR`). `G` is a multiple of the diagonal copies placed by `G_{00}` and `G_{11}`,
which `R_5` fixes (`diag_merge_slotR5`). `μ` is `𝒢₆`-invariant by part (i) (V1's
`middleTilde_g6_inv`). The diagonal copies are positive at `ι` (`lem:commoncut`(i)), and
`μ̃ ⪰_ι 0` is V1's fold pairing from the layer caps (`middleTilde_reserved_positive`).

**Hypotheses** (named, as in V1's (i)): the one-layer `E` law is exchangeable (`OneLayerExch`,
proved for the paper's block laws, `middleBlock_oneLayerExch`: `G_{E,1}` has no edges); the datum
hypotheses of V1's (i) (`DatumHyp`, proved by V1 for the paper's three roots); for positivity at
`ι`, the layer caps `MiddleLayerCaps` with the domination `k_𝔱 w_𝔱 ≤ v_𝔱` (V1), `f₁ + h₁ ≥ 0` and
`b > 3`.

The off-block statement ("off the middle blocks `Ñ₀ = Ñ^inv := μ_𝔅` is invariant under `𝒢₆` and
`⪰_ι 0`") is (ii) and (iii) (`InvariantBackground.lean`) with (R2) at `ι`.

This file depends on V3's `FrameData` (`diag`, `muT`, `P`, `Eadd`, `Ge`, `Go`, `Gpol`, `hCoef`,
`Hdiag`, `Nbr0`); it must be rebuilt if those change.
-/

namespace Sarkozy.PartVLaws

open Finset Sarkozy.Labellings Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.TheoremC

variable {X : Type} [Fintype X] [DecidableEq X]

/-! ## Invariance of slot functionals -/

/-- `κ` is invariant under the slot map `g`: `κ(f(· ∘ g)) = κ(f)` for every `f`. -/
def SlotInv (g : Slot → Slot) (κ : SlotMeasure X) : Prop :=
  ∀ f : (Slot → X) → ℝ, κ (fun z => f (z ∘ g)) = κ f

omit [DecidableEq X] in
theorem SlotInv.add {g : Slot → Slot} {κ κ' : SlotMeasure X} (h : SlotInv g κ)
    (h' : SlotInv g κ') : SlotInv g (κ + κ') := by
  intro f
  simp only [LinearMap.add_apply, h f, h' f]

omit [DecidableEq X] in
theorem SlotInv.smul {g : Slot → Slot} {κ : SlotMeasure X} (h : SlotInv g κ) (c : ℝ) :
    SlotInv g (c • κ) := by
  intro f
  simp only [LinearMap.smul_apply, h f]

omit [DecidableEq X] in
/-- **`𝒢₆`-invariance from `R_1, R_3, R_5`**, for slot functionals. -/
theorem slotInv_slotG_of_slotR {κ : SlotMeasure X}
    (hR : ∀ h : ZMod 6, (h = 1 ∨ h = 3 ∨ h = 5) → SlotInv (slotR h) κ) (k : Fin 6) :
    SlotInv (slotG k) κ := by
  intro f
  rcases slotG_eq_comp k with ⟨h, hh, hv⟩ | ⟨h, h', hh, hh', hv⟩
  · have : (fun z : Slot → X => f (z ∘ slotG k)) = fun z => f (z ∘ slotR h) := by
      funext z
      congr 1
      funext v
      simp only [Function.comp_apply, hv]
    rw [this, hR h hh f]
  · have : (fun z : Slot → X => f (z ∘ slotG k)) =
        fun z => (fun z' : Slot → X => f (z' ∘ slotR h')) (z ∘ slotR h) := by
      funext z
      congr 1
      funext v
      simp only [Function.comp_apply, hv]
    rw [this, hR h hh (fun z' => f (z' ∘ slotR h')), hR h' hh' f]

/-! ## The diagonal copies under `R_h` -/

/-- **The one-layer `E` law is exchangeable** in its object coordinate (for the paper's block laws
`G_{E,1}` has no edges, `middleBlock_oneLayerExch`). -/
def OneLayerExch (F : MiddleFieldLaws X) : Prop :=
  ∀ (σ : Equiv.Perm (Fin 3)) (g : (Fin 3 × Fin 1 → X) → ℝ),
    (F.one .E).expect (fun y => g (fun o => y (σ o.1, o.2))) = (F.one .E).expect g

/-- **`R_h` fixes every diagonal matching copy** `Diag_ι(Π⁽¹⁾_{E_s})`: it maps it to the copy placed
by `ψ_{h,s} ∘ E_s`, the same measure by exchangeability. -/
theorem diag_matching_slotR (D : FrameData X) (hE : OneLayerExch D.F) (h : ZMod 6)
    (hh : h = 1 ∨ h = 3 ∨ h = 5) (s : Fin 2) : SlotInv (slotR h) (D.diag .S s) := by
  intro f
  change (emit (D.F.one .E) (midDiagEmission (matching s))).expect (fun z => f (z ∘ slotR h)) =
    (emit (D.F.one .E) (midDiagEmission (matching s))).expect f
  rw [expect_emit, expect_emit]
  obtain ⟨ψ, hψ⟩ := (matching_generators s).2 h hh
  have hcomp : ∀ y : Fin 3 × Fin 1 → X, (y ∘ midDiagEmission (matching s)) ∘ slotR h =
      (fun o => y (ψ o.1, o.2)) ∘ midDiagEmission (matching s) := by
    intro y
    funext v
    simp only [Function.comp_apply, midDiagEmission, slotR, hψ]
  simp only [hcomp]
  exact hE ψ (fun y => f (y ∘ midDiagEmission (matching s)))

/-- **`R_5` fixes the diagonal copies of the merges `G_{00}` and `G_{11}`**
(`fixed_reflections`). -/
theorem diag_merge_slotR5 (D : FrameData X) :
    SlotInv (slotR 5) (D.diag .R ((0 : Fin 2), (0 : Fin 3))) ∧
      SlotInv (slotR 5) (D.diag .R ((1 : Fin 2), (1 : Fin 3))) := by
  constructor <;> intro f
  · change (emit (D.F.one .E) (midDiagEmission (fun u => (merge 0 0 u).castSucc))).expect
        (fun z => f (z ∘ slotR 5)) =
      (emit (D.F.one .E) (midDiagEmission (fun u => (merge 0 0 u).castSucc))).expect f
    rw [expect_emit, expect_emit]
    congr 1
    funext y
    congr 1
    funext v
    simp only [Function.comp_apply, midDiagEmission, slotR, (fixed_reflections v.1).2.1]
  · change (emit (D.F.one .E) (midDiagEmission (fun u => (merge 1 1 u).castSucc))).expect
        (fun z => f (z ∘ slotR 5)) =
      (emit (D.F.one .E) (midDiagEmission (fun u => (merge 1 1 u).castSucc))).expect f
    rw [expect_emit, expect_emit]
    congr 1
    funext y
    congr 1
    funext v
    simp only [Function.comp_apply, midDiagEmission, slotR, (fixed_reflections v.1).2.2.1]

/-! ## The records of the frame -/

/-- **`E_add` is `R_h`-invariant** (`lem:oct24:invariant-background`(iv)). -/
theorem Eadd_slotR_inv (D : FrameData X) (hE : OneLayerExch D.F) (h : ZMod 6)
    (hh : h = 1 ∨ h = 3 ∨ h = 5) : SlotInv (slotR h) D.Eadd :=
  ((diag_matching_slotR D hE h hh 0).add (diag_matching_slotR D hE h hh 1)).smul _

/-- **`H` is `R_h`-invariant** (`lem:oct24:invariant-background`(iv)). -/
theorem Hdiag_slotR_inv (D : FrameData X) (hE : OneLayerExch D.F) (h : ZMod 6)
    (hh : h = 1 ∨ h = 3 ∨ h = 5) : SlotInv (slotR h) D.Hdiag :=
  ((diag_matching_slotR D hE h hh 0).add (diag_matching_slotR D hE h hh 1)).smul _

/-- **`G` is `R_5`-invariant** (`lem:oct24:invariant-background`(iv)). -/
theorem Gpol_slotR5_inv (D : FrameData X) : SlotInv (slotR 5) D.Gpol :=
  (((diag_merge_slotR5 D).1.smul _).add ((diag_merge_slotR5 D).2.smul _)).smul _

/-- **`μ̃_𝔅` is `R_h`-invariant** (part (i), V1's `middleTilde_g6_inv`). -/
theorem muT_slotR_inv (D : FrameData X) (h₂ : DatumHyp (D.F.two .E) (D.F.two .F) (D.F.two .L))
    (h₁ : DatumHyp (D.F.one .E) (D.F.one .F) (D.F.one .L)) (h : ZMod 6)
    (hh : h = 1 ∨ h = 3 ∨ h = 5) : SlotInv (slotR h) D.muT := by
  have key : ∃ k : Fin 6, ∀ v, slotR h v = slotG k v := by
    rcases hh with rfl | rfl | rfl
    · exact ⟨3, fun v => (slotR_eq_slotG v).1⟩
    · exact ⟨4, fun v => (slotR_eq_slotG v).2.1⟩
    · exact ⟨5, fun v => (slotR_eq_slotG v).2.2⟩
  obtain ⟨k, hk⟩ := key
  intro f
  have : (fun z : Slot → X => f (z ∘ slotR h)) = fun z => f (z ∘ slotG k) := by
    funext z
    congr 1
    funext v
    simp only [Function.comp_apply, hk]
  change middleTilde D.F D.W D.r _ = middleTilde D.F D.W D.r f
  rw [this]
  exact middleTilde_g6_inv D.F h₂ h₁ D.W D.r k f

/-- **The invariant background** `Ñ^inv = μ + E_add + H`, divided by `P(r)` as V3's records are. -/
noncomputable def NbrInv (D : FrameData X) : SlotMeasure X := D.P⁻¹ • (D.muT + D.Eadd + D.Hdiag)

/-- `Ñ₀ = Ñ^inv + G` (with the common normalization). -/
theorem Nbr0_eq_NbrInv_add (D : FrameData X) : D.Nbr0 = NbrInv D + D.P⁻¹ • D.Gpol := by
  unfold FrameData.Nbr0 NbrInv
  refine LinearMap.ext fun f => ?_
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- **`lem:oct24:invariant-background`(iv): `Ñ^inv` is invariant under `R_1, R_3, R_5`.** -/
theorem NbrInv_slotR_inv (D : FrameData X) (hE : OneLayerExch D.F)
    (h₂ : DatumHyp (D.F.two .E) (D.F.two .F) (D.F.two .L))
    (h₁ : DatumHyp (D.F.one .E) (D.F.one .F) (D.F.one .L)) (h : ZMod 6)
    (hh : h = 1 ∨ h = 3 ∨ h = 5) : SlotInv (slotR h) (NbrInv D) :=
  (((muT_slotR_inv D h₂ h₁ h hh).add (Eadd_slotR_inv D hE h hh)).add
    (Hdiag_slotR_inv D hE h hh)).smul _

/-- **`lem:oct24:invariant-background`(iv): `Ñ^inv` is invariant under the group `𝒢₆`** generated
by `R_1, R_3, R_5`. -/
theorem NbrInv_slotG_inv (D : FrameData X) (hE : OneLayerExch D.F)
    (h₂ : DatumHyp (D.F.two .E) (D.F.two .F) (D.F.two .L))
    (h₁ : DatumHyp (D.F.one .E) (D.F.one .F) (D.F.one .L)) (k : Fin 6) :
    SlotInv (slotG k) (NbrInv D) :=
  slotInv_slotG_of_slotR (fun h hh => NbrInv_slotR_inv D hE h₂ h₁ h hh) k

/-- **`lem:oct24:invariant-background`(iv): `Ñ₀` is `R_5`-invariant.** -/
theorem Nbr0_slotR5_inv (D : FrameData X) (hE : OneLayerExch D.F)
    (h₂ : DatumHyp (D.F.two .E) (D.F.two .F) (D.F.two .L))
    (h₁ : DatumHyp (D.F.one .E) (D.F.one .F) (D.F.one .L)) : SlotInv (slotR 5) D.Nbr0 := by
  rw [Nbr0_eq_NbrInv_add]
  exact (NbrInv_slotR_inv D hE h₂ h₁ 5 (Or.inr (Or.inr rfl))).add ((Gpol_slotR5_inv D).smul _)

/-! ## Positivity at `ι` -/

/-- A diagonal copy is positive at `ι`. -/
theorem diag_reserved (D : FrameData X) (t : PType) (φ : t.Pat) :
    reservedCut.Positive (D.diag t φ) :=
  middleDiag_reserved_positive D.F t φ

/-- **`G ⪰_ι 0`** when `f₁ + h₁ ≥ 0`. -/
theorem Gpol_reserved (D : FrameData X) (hfh : 0 ≤ D.I.f₁ + D.I.h₁) :
    reservedCut.Positive D.Gpol := by
  have hv : 0 ≤ D.W.v .D * D.r ^ 2 := mul_nonneg (D.W.v_nonneg _) (pow_nonneg D.r_nonneg _)
  exact (((diag_reserved D _ _).smul hv).add ((diag_reserved D _ _).smul hv)).smul
    (mul_nonneg hfh D.r_nonneg)

/-- `E_add ⪰_ι 0`. -/
theorem Eadd_reserved (D : FrameData X) : reservedCut.Positive D.Eadd :=
  ((diag_reserved D _ _).add (diag_reserved D _ _)).smul
    (mul_nonneg (D.W.v_nonneg _) (pow_nonneg D.r_nonneg _))

/-- `H ⪰_ι 0` when `b > 3`. -/
theorem Hdiag_reserved (D : FrameData X) (hb : 3 < D.b) : reservedCut.Positive D.Hdiag := by
  have hc : 0 ≤ D.hCoef := by
    unfold FrameData.hCoef
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (D.W.w_nonneg _)) D.r_nonneg)
      (div_nonneg (by norm_num) (by linarith))
  exact ((diag_reserved D _ _).add (diag_reserved D _ _)).smul hc

/-- **`lem:oct24:invariant-background`(iv): `Ñ^inv ⪰_ι 0`**, given the layer caps of `μ̃` and the
domination `k_𝔱 w_𝔱 ≤ v_𝔱` (V1's fold pairing), and `b > 3`. -/
theorem NbrInv_reserved (D : FrameData X) (k : PType → ℝ) (hcap : MiddleLayerCaps D.F k D.r)
    (hdom : ∀ t, k t * D.W.w t ≤ D.W.v t) (hb : 3 < D.b) : reservedCut.Positive (NbrInv D) := by
  have hP : 0 ≤ D.P⁻¹ := inv_nonneg.mpr (le_trans zero_le_one (one_le_midPoly D.W D.r_nonneg))
  exact (((middleTilde_reserved_positive D.F D.W k D.r_nonneg hcap hdom).add
    (Eadd_reserved D)).add (Hdiag_reserved D hb)).smul hP

/-- **`lem:oct24:invariant-background`(iv): `Ñ₀ ⪰_ι 0`**, under the same hypotheses and
`f₁ + h₁ ≥ 0`. -/
theorem Nbr0_reserved (D : FrameData X) (k : PType → ℝ) (hcap : MiddleLayerCaps D.F k D.r)
    (hdom : ∀ t, k t * D.W.w t ≤ D.W.v t) (hb : 3 < D.b) (hfh : 0 ≤ D.I.f₁ + D.I.h₁) :
    reservedCut.Positive D.Nbr0 := by
  have hP : 0 ≤ D.P⁻¹ := inv_nonneg.mpr (le_trans zero_le_one (one_le_midPoly D.W D.r_nonneg))
  rw [Nbr0_eq_NbrInv_add]
  exact (NbrInv_reserved D k hcap hdom hb).add ((Gpol_reserved D hfh).smul hP)

/-! ## The paper's block laws -/

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- **The one-layer `E` block law is exchangeable**: every permutation of the objects is an
automorphism of the edgeless `G_{E,1}`. -/
theorem middleBlock_oneLayerExch (hne : MiddleNonempty pr)
    (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) :
    OneLayerExch (middleBlockFieldLaws pr hne root) := by
  intro σ g
  exact blockGraphLaw_expect_auto pr (matchGraph (Fin 1)) hne.E1
    (σ.prodCongr (Equiv.refl (Fin 1))) (matchGraph_auto (Fin 1) _) g

end Block

end Sarkozy.PartVLaws
