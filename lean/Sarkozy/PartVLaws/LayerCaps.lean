module

public import Sarkozy.PartVLaws.TailRP

@[expose] public section

/-!
# The layer caps (V3) at the level of the field laws

`paper/sections/25_upper_reference.tex`, `subsec:upper-reference-rp`, (V3) ("for every field pair
`φφ'`, the normalized block cut operator of the layer cut of `G_{φφ',2}` is at least
`-k_{φφ'} r`"), and the proof of `lem:upper-reference-rp`(i), "The reserved cut" (every two-layer
component inherits the field-law bound, by the last assertion of `lem:five-type`(e)).

V1's `UpperLayerCaps` asks the bound `Π_{𝔱,φ} ⪰_ι -k_𝔱 r Diag_ι(Π⁽¹⁾_{𝔱,φ})` for every component.
The paper's (V3) asks it for the nine field laws only:
`λ_{φφ'} ⪰_ι -k_{φφ'} r Diag_ι(λ⁽¹⁾_{φφ'})` (`FieldLayerCaps`). **`upperLayerCaps_of_field`**
derives V1's form from the paper's, through C1's `Reserved.comp_below_of_field` and the
identification of V1's components with C1's (`comp_two_eq'`, `comp_one_eq'`).
`ValidInputs.ofField` builds the validity bundle with (V3) in the paper's form, and
`tailLaw_familyPositive'` is `lem:tail-law`(ii) with it.
-/

namespace Sarkozy.PartVLaws

open Finset Sarkozy.Labellings Sarkozy.FiveType Sarkozy.PartV Sarkozy.FiveType.TwoCoord

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The pattern indices of V1 as C1's. -/
def patCast : (s : PType) → s.Pat → PatIdx (toTy s)
  | .L, φ => φ
  | .D, φ => φ
  | .S, φ => φ
  | .R, φ => φ
  | .C, φ => φ

/-- A two-layer component of V1 is C1's component. -/
theorem comp_two_eq' (F : UpperFieldLaws X) (t : PType × PType) (φ : t.1.Pat × t.2.Pat) :
    signedIntegral (upComponent F (true, ⟨t, φ⟩)).weight =
      comp (lam2 F) (toTy t.1) (patCast t.1 φ.1) (toTy t.2) (patCast t.2 φ.2) := by
  rcases t with ⟨t₀, t₁⟩
  cases t₀ <;> cases t₁ <;>
  exact two_comp_eq F (fieldOf _) (fieldOf _) (patMap _ (patCast _ φ.1)) (patMap _ (patCast _ φ.2))

/-- A one-layer diagonal component of V1 is C1's `Diag_ι` of the one-layer component. -/
theorem comp_one_eq' (F : UpperFieldLaws X) (t : PType × PType) (φ : t.1.Pat × t.2.Pat) :
    signedIntegral (upComponent F (false, ⟨t, φ⟩)).weight =
      pushFunctional (comp (lam1 F) (toTy t.1) (patCast t.1 φ.1) (toTy t.2) (patCast t.2 φ.2))
        Reserved.diagW := by
  rcases t with ⟨t₀, t₁⟩
  cases t₀ <;> cases t₁ <;>
  exact one_comp_eq F (fieldOf _) (fieldOf _) (patMap _ (patCast _ φ.1)) (patMap _ (patCast _ φ.2))

/-- **(V3) in the paper's form**: for every field pair, `λ_{φφ'} ⪰_ι -κ_{φφ'} r Diag_ι(λ⁽¹⁾_{φφ'})`,
at the layer swap of the field labels. -/
def FieldLayerCaps (F : UpperFieldLaws X) (κ : FieldTy → FieldTy → ℝ) (r : ℝ) : Prop :=
  ∀ f0 f1 : FieldTy, (Reserved.fieldCut f0.Obj f1.Obj).Below
    (-(κ f0 f1 * r) • pushFunctional (lawL (lam1 F f0 f1)) Reserved.diagF) (lawL (lam2 F f0 f1))

/-- **Every component inherits the field-law cap** (`lem:five-type`(e), last assertion; the merges
and the constants included): the paper's (V3) gives V1's `UpperLayerCaps` with `k_𝔱 = κ_{𝔣(𝔱)}`. -/
theorem upperLayerCaps_of_field (F : UpperFieldLaws X) (κ : FieldTy → FieldTy → ℝ) {r : ℝ}
    (h : FieldLayerCaps F κ r) :
    UpperLayerCaps F (fun t₀ t₁ => κ (fieldOf (toTy t₀)) (fieldOf (toTy t₁))) r := by
  intro t φ
  rw [comp_two_eq' F t φ, comp_one_eq' F t φ]
  exact Reserved.comp_below_of_field (lam2 F) (lam1 F) _ _ _ _ (h _ _)

/-- The caps of the tail datum on C1's field types. -/
noncomputable def tailKappa (f0 f1 : FieldTy) : ℝ :=
  ((tailFieldCap (toFType f0) (toFType f1) : ℚ) : ℝ)

theorem tailCap_eq :
    (fun t₀ t₁ => tailKappa (fieldOf (toTy t₀)) (fieldOf (toTy t₁))) = tailCap := by
  funext t₀ t₁
  cases t₀ <;> cases t₁ <;> rfl

/-- **The validity bundle with (V3) in the paper's form.** -/
theorem ValidInputs.ofField {F : UpperFieldLaws X} {H : UpperDatumHyp F} {r : ℝ}
    {ord res : FieldTy → CompletionInput} {κ : FieldTy → FieldTy → ℝ}
    (root20 : ∀ f', RootEnv (rowD0 (lam2 F) f' (H.two0 f')) (ord f').d r)
    (root21 : ∀ f', RootEnv (rowD1 (lam2 F) f' (H.two1 f')) (ord f').d r)
    (root10 : ∀ f', RootEnv (rowD0 (lam1 F) f' (H.one0 f')) (res f').d r)
    (root11 : ∀ f', RootEnv (rowD1 (lam1 F) f' (H.one1 f')) (res f').d r)
    (rows20 : ∀ f', ValidRows (rowD0 (lam2 F) f' (H.two0 f')) r (ord f').f (ord f').h (ord f').M)
    (rows21 : ∀ f', ValidRows (rowD1 (lam2 F) f' (H.two1 f')) r (ord f').f (ord f').h (ord f').M)
    (rows10 : ∀ f', ValidRows (rowD0 (lam1 F) f' (H.one0 f')) r (res f').f (res f').h (res f').M)
    (rows11 : ∀ f', ValidRows (rowD1 (lam1 F) f' (H.one1 f')) r (res f').f (res f').h (res f').M)
    (caps : FieldLayerCaps F κ r) :
    ValidInputs F H r ord res (fun t₀ t₁ => κ (fieldOf (toTy t₀)) (fieldOf (toTy t₁))) :=
  ⟨root20, root21, root10, root11, rows20, rows21, rows10, rows11,
    upperLayerCaps_of_field F κ caps⟩

/-- **`lem:tail-law`(ii), with (V3) at the level of the nine field laws**: at every prime
`p ≥ 2²⁰`, under H1, the root envelopes (V1), the valid rows (V2) and the field-law layer caps
(V3) of the tail datum make the tail law reflection positive at every cut of `𝔉`. -/
theorem tailLaw_familyPositive' (p : ℕ) [Fact p.Prime] (hW : WeilBound (ZMod p))
    (hp : (2 : ℝ) ^ 20 ≤ p) (hne : TailNonempty p)
    (hroot20 : ∀ f', RootEnv (rowD0 (lam2 (tailFieldLaws p hne)) f'
      ((tail_upperDatumHyp p hW hp hne).two0 f')) (tailOrd f').d (tailR p))
    (hroot21 : ∀ f', RootEnv (rowD1 (lam2 (tailFieldLaws p hne)) f'
      ((tail_upperDatumHyp p hW hp hne).two1 f')) (tailOrd f').d (tailR p))
    (hroot10 : ∀ f', RootEnv (rowD0 (lam1 (tailFieldLaws p hne)) f'
      ((tail_upperDatumHyp p hW hp hne).one0 f')) (tailRes f').d (tailR p))
    (hroot11 : ∀ f', RootEnv (rowD1 (lam1 (tailFieldLaws p hne)) f'
      ((tail_upperDatumHyp p hW hp hne).one1 f')) (tailRes f').d (tailR p))
    (hrows20 : ∀ f', ValidRows (rowD0 (lam2 (tailFieldLaws p hne)) f'
      ((tail_upperDatumHyp p hW hp hne).two0 f')) (tailR p) (tailOrd f').f (tailOrd f').h
        (tailOrd f').M)
    (hrows21 : ∀ f', ValidRows (rowD1 (lam2 (tailFieldLaws p hne)) f'
      ((tail_upperDatumHyp p hW hp hne).two1 f')) (tailR p) (tailOrd f').f (tailOrd f').h
        (tailOrd f').M)
    (hrows10 : ∀ f', ValidRows (rowD0 (lam1 (tailFieldLaws p hne)) f'
      ((tail_upperDatumHyp p hW hp hne).one0 f')) (tailR p) (tailRes f').f (tailRes f').h
        (tailRes f').M)
    (hrows11 : ∀ f', ValidRows (rowD1 (lam1 (tailFieldLaws p hne)) f'
      ((tail_upperDatumHyp p hW hp hne).one1 f')) (tailR p) (tailRes f').f (tailRes f').h
        (tailRes f').M)
    (hcaps : FieldLayerCaps (tailFieldLaws p hne) tailKappa (tailR p)) :
    TheoremC.FamilyReflectionPositive (signedIntegral (tailLaw p hne).weight) := by
  have hV := ValidInputs.ofField (H := tail_upperDatumHyp p hW hp hne) hroot20 hroot21 hroot10
    hroot11 hrows20 hrows21 hrows10 hrows11 hcaps
  rw [tailCap_eq] at hV
  exact tailLaw_familyPositive p hW hp hne hV

end Sarkozy.PartVLaws
