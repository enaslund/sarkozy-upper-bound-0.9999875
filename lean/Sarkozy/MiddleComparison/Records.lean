module

public import Sarkozy.PartVRecords.Frame

@[expose] public section

/-!
# The records of the first stage of a middle block (`def:record:frame`, `subsec:middle-comparison`)

`paper/sections/20c_middle_frame.tex`, `def:record:frame`(d), and
`paper/sections/21_middle_records.tex`, `subsec:middle-comparison`.

The first stage of a middle block is V3's `λ = μ - F_fold - E_fold + E_new + G`, all divided by
`P(r) = μ̃_𝔅(1)`. The comparison law treats its records in four groups
(`subsec:middle-comparison`):

* **kept** (`Kept = Fin 4`, `keptIdx`): the two-layer root, the folded root, the two-layer `F₀`
  and the folded `F₀`, with their weights in `μ̃_𝔅`; and the two records `E_new` of the first
  stage;
* **changed** (`Chg`, `chgPat`): the two-layer fold records `F₁, F₂` (weight `w_D r`), matching
  records `E₀, E₁` (`w_S r`), the six merge records (`w_R r²`) and the two constant records
  (`w_C r³`); `chgCoef` is their weight;
* **deleted** (`Del`, `delPat`): the six folded merge records (`v_R r³`), the two records of the
  polarization correction `G = (f₁ + h₁) r v_D r² (Diag_ι(Π⁽¹⁾_{G₀₀}) + Diag_ι(Π⁽¹⁾_{G₁₁}))`, and
  the two folded constant records (`v_C r⁴`); `delCoef` is their coefficient;
* the folded `F₁, F₂` and the folded matchings do not occur in `λ` (removed by `F_fold`, replaced
  by `E_new`).

**`lam_expand`**: `λ` is `P(r)⁻¹` times the sum of these records with these coefficients, record
by record. This is the identity behind "the first stage changes only one-layer folded records, so
the two-layer records enter `λ_𝔅` with the weights of `μ_𝔅`" (`subsec:middle-comparison`).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.MiddleComparison

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion

variable {X : Type} [Fintype X] [DecidableEq X]

/-! ## The index sets -/

/-- The kept records of the reference: the two-layer root, the folded root, the two-layer `F₀`
and the folded `F₀`. -/
abbrev Kept : Type := Fin 4

/-- The components of the kept records (`midComponent` indices). -/
def keptIdx : Kept → MidIdx :=
  ![(true, ⟨.L, ()⟩), (false, ⟨.L, ()⟩), (true, ⟨.D, (0 : Fin 3)⟩), (false, ⟨.D, (0 : Fin 3)⟩)]

/-- **The changed two-layer records** (`subsec:middle-comparison`): the folds `F₁, F₂`, the
matchings `E₀, E₁`, the six merges and the two constants. -/
abbrev Chg : Type := Fin 2 ⊕ Fin 2 ⊕ PType.Pat .R ⊕ PType.Pat .C

/-- The fold patterns `F₁, F₂` of the changed fold records. -/
def foldPat : Fin 2 → Fin 3 := ![1, 2]

/-- The pattern of a changed record. -/
def chgPat : Chg → Σ t : PType, t.Pat
  | .inl j => ⟨.D, foldPat j⟩
  | .inr (.inl s) => ⟨.S, s⟩
  | .inr (.inr (.inl φ)) => ⟨.R, φ⟩
  | .inr (.inr (.inr k)) => ⟨.C, k⟩

/-- **The deleted records** (the paragraph "Deletions" before `subsec:middle-comparison`): the six
folded merges, the two records `G_e`, `G_o` of the polarization correction, the two folded
constants. -/
abbrev Del : Type := PType.Pat .R ⊕ PType.Pat .C ⊕ Fin 2

/-- The merge patterns `G₀₀`, `G₁₁` of the polarization correction. -/
def gPat : Fin 2 → PType.Pat .R := ![((0 : Fin 2), (0 : Fin 3)), ((1 : Fin 2), (1 : Fin 3))]

/-- The pattern of a deleted (folded) record. -/
def delPat : Del → Σ t : PType, t.Pat
  | .inl φ => ⟨.R, φ⟩
  | .inr (.inl k) => ⟨.C, k⟩
  | .inr (.inr g) => ⟨.R, gPat g⟩

/-- The record `Π_ρ` of a component index, as a measure. -/
noncomputable abbrev recM (F : MiddleFieldLaws X) (ρ : MidIdx) : SlotMeasure X :=
  signedIntegral (midComponent F ρ).weight

variable (D : FrameData X)

/-- The weight of a kept record in `μ̃_𝔅`. -/
noncomputable def keptCoef (k : Kept) : ℝ := midCoeff D.W D.r (keptIdx k)

/-- The weight `w_𝔱 r^{deg 𝔱}` of a changed two-layer record in `μ̃_𝔅` (and in `λ_𝔅`). -/
noncomputable def chgCoef (t : Chg) : ℝ := midCoeff D.W D.r (true, chgPat t)

/-- The coefficient of a deleted record in `μ̃_𝔅 + G`: `v_R r³`, `v_C r⁴`, and
`(f₁ + h₁) r · v_D r²` for the two records of `G`. -/
noncomputable def delCoef : Del → ℝ
  | .inl φ => midCoeff D.W D.r (false, ⟨.R, φ⟩)
  | .inr (.inl k) => midCoeff D.W D.r (false, ⟨.C, k⟩)
  | .inr (.inr _) => (D.I.f₁ + D.I.h₁) * D.r * (D.W.v .D * D.r ^ 2)

/-- The common mass `(v_S + v_D) r²` of the two records `E_new`. -/
noncomputable def enewCoef : ℝ := (D.W.v .S + D.W.v .D) * D.r ^ 2

theorem keptCoef_nonneg (k : Kept) : 0 ≤ keptCoef D k := midCoeff_nonneg D.W D.r_nonneg _

theorem chgCoef_nonneg (t : Chg) : 0 ≤ chgCoef D t := midCoeff_nonneg D.W D.r_nonneg _

theorem enewCoef_nonneg : 0 ≤ enewCoef D :=
  mul_nonneg (add_nonneg (D.W.v_nonneg _) (D.W.v_nonneg _)) (pow_nonneg D.r_nonneg _)

/-- The root has weight one in `μ̃_𝔅`. -/
theorem keptCoef_root : keptCoef D 0 = 1 := by
  simp [keptCoef, keptIdx, midCoeff, PType.deg, D.W.w_L]

/-- The changed fold records have weight `w_D r`. -/
theorem chgCoef_fold (j : Fin 2) : chgCoef D (.inl j) = D.W.w .D * D.r := by
  simp [chgCoef, chgPat, midCoeff, PType.deg]

/-- The changed matching records have weight `w_S r`. -/
theorem chgCoef_match (s : Fin 2) : chgCoef D (.inr (.inl s)) = D.W.w .S * D.r := by
  simp [chgCoef, chgPat, midCoeff, PType.deg]

/-- The changed merge records have weight `w_R r²`. -/
theorem chgCoef_merge (φ : PType.Pat .R) : chgCoef D (.inr (.inr (.inl φ))) = D.W.w .R * D.r ^ 2 :=
  by simp [chgCoef, chgPat, midCoeff, PType.deg]

/-- The changed constant records have weight `w_C r³`. -/
theorem chgCoef_const (k : PType.Pat .C) :
    chgCoef D (.inr (.inr (.inr k))) = D.W.w .C * D.r ^ 3 := by
  simp [chgCoef, chgPat, midCoeff, PType.deg]

/-! ## `λ` record by record -/

/-- **`λ` record by record** (`def:record:frame`(d), `subsec:middle-comparison`):
`P(r) λ = ∑_{kept} c_k Π_k + (v_S + v_D) r² (E_new,0 + E_new,1) + ∑_{changed} w_t r^{deg} Π_t +
∑_{deleted} c_d Diag_ι(Π⁽¹⁾_d)`. -/
theorem lam_expand : D.lam = D.P⁻¹ • (∑ k, keptCoef D k • recM D.F (keptIdx k) +
    enewCoef D • (D.newRec 0 + D.newRec 1) + ∑ t, chgCoef D t • recM D.F (true, chgPat t) +
    ∑ d, delCoef D d • recM D.F (false, delPat d)) := by
  unfold FrameData.lam
  rw [D.muT_eq_sum, FrameData.sum_sigma_pType]
  congr 1
  apply LinearMap.ext
  intro f
  simp only [Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_four, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul,
    midCoeff, PType.deg,
    FrameData.pairTerm, FrameData.Ffold, FrameData.Efold, FrameData.Enew, FrameData.Gpol,
    FrameData.Ge, FrameData.Go, FrameData.diag, keptCoef, chgCoef, delCoef, enewCoef,
    keptIdx, chgPat, delPat, foldPat, gPat, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Finset.sum_add_distrib]
  ring

end Sarkozy.MiddleComparison
