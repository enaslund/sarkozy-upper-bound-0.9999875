module

public import Sarkozy.NormBoundsPaper4.MixSectors
public import Sarkozy.NormBoundsPaper.Merge2
public import Sarkozy.SignedGram.Block
public import Sarkozy.SignedGram.SectorBlock

@[expose] public section

/-!
# The fold changes at the reserved cut as forms of product couplings (FD)

`paper/sections/21_middle_records.tex`, `def:record:mixture`(c),(d), `prop:signed-bounds`
(statement: "`D_t = T[K_{t,𝔅}] − ⊗_p T_{old,p}` … an operator on `L²(m_{0,𝔅})`, with `T[·]` taken
relative to `m_{0,𝔅} ⊗ m_{0,𝔅}`"), and (e) ("For `F₂` the record difference is `𝒰 D_t^* 𝒰` …
with the same bounds").

For the change of the fold record `F_{j+1}` of B8's `ofFold` (any components, any `t`), with the
half functions `F, G` read through the fold (`φ = F ∘ hread`, SGA's `kform`):

* `form_newF`, `form_oldF`: the cut forms of the signed record and of the old fold record are the
  kernel forms of `K'_{F_{j+1}} = ∑_c α_c ⊗_p P_{c,p}` (SGA's `newW`) and of `K₀ = λ_𝔅(G_{F,2})`;
* `hsq_fold`: the actual half law of the fold record is the layer-`0` marginal of `K₀`
  (`‖F‖² = mform K₀ φ`);
* **`form_fold_sym`**, **`form_fold_skew`**: the symmetric part of the change is
  `symK = ½⟨φ, K'ψ⟩ + ½⟨ψ, K'φ⟩ − ⟨φ, K₀ψ⟩`, and its skew part is `skwK = ½⟨φ, K'ψ⟩ − ½⟨ψ, K'φ⟩`
  (the old record is symmetric at the cut: `lawF_swap`);
* **`symK_refl`**, **`skwK_refl`**, `mform_rf` (`prop:signed-bounds`(e)): for reflected components
  (SGA's `Reflected`, true of the paper's components) the forms of `F₂` at `(φ, ψ)` are those of
  `F₁` at `(ψ ∘ ς, φ ∘ ς)`, and `ς` preserves the norm;
* **`symK_dot`**, **`skwK_dot`**, `mform_ip`: for `F₁`, the forms are NB2-style forms
  `mixChg` of the product couplings `P_{c,p}` (SGA's `compP`) and `K_{0,p}` (`oldP`) on
  `∏_p (𝔽_p)³`, relative to `⊗_p m_{0,p}` (`mP`).
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.NormBoundsPaper4

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.Labellings Sarkozy.MiddleComparison Sarkozy.SignedComponents
open Sarkozy.IndexSupport Sarkozy.Mixing Sarkozy.SignedGram
open Sarkozy.NormBoundsPaper (hsq_emit_gen)
open Sarkozy.NormBoundsPaper2 (ip)

section Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (h : ClassThreeBlock pr) (hne : MiddleNonempty pr)
  (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
  {r : ℝ} (hr : 0 ≤ r) (b : ℝ)

/-- The half function `F` read through the fold `F_{j+1}`, as a function of the block triple. -/
abbrev fr (j : Fin 2) (F : (reservedCut.Half → BlockLabel pr) → ℝ) : (Fin 3 → BlockLabel pr) → ℝ :=
  fun x => F (hread (foldRead j) x)

/-- The cut form of the old fold record is the kernel form of `K₀`. -/
theorem form_oldF (j : Fin 2) (F G : (reservedCut.Half → BlockLabel pr) → ℝ) :
    reservedCut.form (recM (middleFrame pr hne root W I hr b h).F (true, chgPat (.inl j))) F G =
      kform (lawF pr hne).weight (fr pr j F) (fr pr j G) :=
  form_foldRec (middleFrame pr hne root W I hr b h) j F G

/-- The cut form of the signed fold record is the kernel form of `K'_{F_{j+1}}`. -/
theorem form_newF (C : FoldComponents pr hne) (t : ℝ) (j : Fin 2)
    (F G : (reservedCut.Half → BlockLabel pr) → ℝ) :
    reservedCut.form (newOf pr h t (foldRec C) (.inl j)) F G =
      kform (newW C t j) (fr pr j F) (fr pr j G) := by
  change reservedCut.form (∑ c, signedCoef t c • signedIntegral (foldRec C j c).weight) F G = _
  rw [form_sum_smul]
  have e : ∀ c, reservedCut.form (signedIntegral (foldRec C j c).weight) F G =
      kform (foldLaw C j c).weight (fr pr j F) (fr pr j G) := fun c => form_two _ _ F G
  simp only [e]
  unfold kform newW
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun y _ => sum_congr rfl fun c _ => ?_
  ring

/-- **The actual half law of the fold record** is the layer-`0` marginal `m_{0,𝔅}` of `K₀`. -/
theorem hsq_fold (j : Fin 2) (F : (reservedCut.Half → BlockLabel pr) → ℝ) :
    hsq reservedCut (mOf (middleFrame pr hne root W I hr b h) (.inl j)) F =
      mform (lawF pr hne).weight (fr pr j F) := by
  change hsq reservedCut (plusMarginal reservedCut
    (emit (lawF pr hne) (midEmission (foldRead j))).weight) F = _
  rw [hsq_emit_gen _ _ (fun y => hread (foldRead j) (lay2 y 0)) (fun y => by
    funext v
    simp only [Function.comp_apply, midEmission, hread, lay2, reservedCut_half_layer v]
    rfl)]
  rfl

/-- The symmetric form `½⟨φ, K'ψ⟩ + ½⟨ψ, K'φ⟩ − ⟨φ, K₀ψ⟩`. -/
noncomputable def symK (K' : (Fin 3 × Fin 2 → BlockLabel pr) → ℝ)
    (φ ψ : (Fin 3 → BlockLabel pr) → ℝ) : ℝ :=
  1 / 2 * kform K' φ ψ + 1 / 2 * kform K' ψ φ - kform (lawF pr hne).weight φ ψ

/-- The skew form `½⟨φ, K'ψ⟩ − ½⟨ψ, K'φ⟩`. -/
noncomputable def skwK (K' : (Fin 3 × Fin 2 → BlockLabel pr) → ℝ)
    (φ ψ : (Fin 3 → BlockLabel pr) → ℝ) : ℝ :=
  1 / 2 * kform K' φ ψ - 1 / 2 * kform K' ψ φ

/-- **The symmetric part of the change of the fold `F_{j+1}`.** -/
theorem form_fold_sym (C : FoldComponents pr hne) (t : ℝ) (j : Fin 2)
    (F G : (reservedCut.Half → BlockLabel pr) → ℝ) :
    reservedCut.form (foldChange pr h hne root W I hr b C t (.inl j) .sym) F G =
      symK pr hne (newW C t j) (fr pr j F) (fr pr j G) := by
  have hS : ∀ L₁ L₂ : SlotMeasure (BlockLabel pr), ∀ F G,
      reservedCut.form (L₁ - L₂) F G = reservedCut.form L₁ F G - reservedCut.form L₂ F G :=
    fun _ _ _ _ => rfl
  change reservedCut.form (symPart reservedCut (newOf pr h t (foldRec C) (.inl j) -
    recM (middleFrame pr hne root W I hr b h).F (true, chgPat (.inl j)))) F G = _
  unfold symPart
  rw [form_smul, form_add, form_reflect, hS, hS, form_newF, form_newF, form_oldF, form_oldF,
    kform_comm (lawF_swap pr hne) (fr pr j G)]
  unfold symK
  ring

/-- **The skew part of the change of the fold `F_{j+1}`** (the old record is symmetric). -/
theorem form_fold_skew (C : FoldComponents pr hne) (t : ℝ) (j : Fin 2)
    (F G : (reservedCut.Half → BlockLabel pr) → ℝ) :
    reservedCut.form (foldChange pr h hne root W I hr b C t (.inl j) .skew) F G =
      skwK pr (newW C t j) (fr pr j F) (fr pr j G) := by
  have hS : ∀ L₁ L₂ : SlotMeasure (BlockLabel pr), ∀ F G,
      reservedCut.form (L₁ - L₂) F G = reservedCut.form L₁ F G - reservedCut.form L₂ F G :=
    fun _ _ _ _ => rfl
  change reservedCut.form (skewPart reservedCut (newOf pr h t (foldRec C) (.inl j) -
    recM (middleFrame pr hne root W I hr b h).F (true, chgPat (.inl j)))) F G = _
  unfold skewPart
  rw [form_smul, hS, form_reflect, hS, hS, form_newF, form_newF, form_oldF, form_oldF,
    kform_comm (lawF_swap pr hne) (fr pr j G)]
  unfold skwK
  ring

/-! ## `F₂` from `F₁` (`prop:signed-bounds`(e)) -/

variable {pr} {hne}

theorem kformF_refl (φ ψ : (Fin 3 → BlockLabel pr) → ℝ) :
    kform (lawF pr hne).weight (fun x => ψ (rf x)) (fun x => φ (rf x)) =
      kform (lawF pr hne).weight φ ψ :=
  kform_reflT (fun y => (lawF_rT pr hne y).symm) φ ψ

/-- **`prop:signed-bounds`(e), symmetric part**: `Sym D^{F₂}(φ, ψ) = Sym D^{F₁}(ψ ∘ ς, φ ∘ ς)`. -/
theorem symK_refl {C : FoldComponents pr hne} (hC : Reflected C) (t : ℝ)
    (φ ψ : (Fin 3 → BlockLabel pr) → ℝ) :
    symK pr hne (newW C t 1) φ ψ =
      symK pr hne (newW C t 0) (fun x => ψ (rf x)) (fun x => φ (rf x)) := by
  unfold symK
  rw [← kform_reflT (newW_one hC t) φ ψ, ← kform_reflT (newW_one hC t) ψ φ, kformF_refl,
    kform_comm (lawF_swap pr hne) φ ψ, add_comm (1 / 2 * kform (newW C t 0) _ _)]

/-- **`prop:signed-bounds`(e), skew part**: `Skew D^{F₂}(φ, ψ) = Skew D^{F₁}(ψ ∘ ς, φ ∘ ς)`. -/
theorem skwK_refl {C : FoldComponents pr hne} (hC : Reflected C) (t : ℝ)
    (φ ψ : (Fin 3 → BlockLabel pr) → ℝ) :
    skwK pr (newW C t 1) φ ψ = skwK pr (newW C t 0) (fun x => ψ (rf x)) (fun x => φ (rf x)) := by
  unfold skwK
  rw [← kform_reflT (newW_one hC t) φ ψ, ← kform_reflT (newW_one hC t) ψ φ]

/-- `ς` preserves the norm of `L²(m_{0,𝔅})` (`g₀ ∘ ς = g₀`). -/
theorem mform_rf (φ : (Fin 3 → BlockLabel pr) → ℝ) :
    mform (lawF pr hne).weight (fun x => φ (rf x)) = mform (lawF pr hne).weight φ :=
  mform_refl_eq (lawF_rT pr hne) (lawF_swap pr hne) φ

/-! ## `F₁` as forms of product couplings on `∏_p 𝔽_p³` -/

variable (hne)

/-- A function of block triples as a function on `∏_p 𝔽_p³`. -/
abbrev ex (φ : (Fin 3 → BlockLabel pr) → ℝ) : (∀ i, Ai pr i) → ℝ := fun u => φ (eX u)

theorem kform_new_dot (C : FoldComponents pr hne) (t : ℝ) (φ ψ : (Fin 3 → BlockLabel pr) → ℝ) :
    kform (newW C t 0) φ ψ = ∑ c, signedCoef t c * (ex φ ⬝ᵥ (piKron (compP hne C c) *ᵥ ex ψ)) := by
  rw [kform_eq_dot, matW_newW hne, Matrix.sum_mulVec, dotProduct_sum]
  refine sum_congr rfl fun c _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem kform_old_dot (φ ψ : (Fin 3 → BlockLabel pr) → ℝ) :
    kform (lawF pr hne).weight φ ψ = ex φ ⬝ᵥ (piKron (oldP hne) *ᵥ ex ψ) := by
  rw [kform_eq_dot, matW_lawF hne]

/-- **The symmetric form of `F₁` is `mixChg` with `(½, ½, 1)`.** -/
theorem symK_dot (C : FoldComponents pr hne) (t : ℝ) (φ ψ : (Fin 3 → BlockLabel pr) → ℝ) :
    symK pr hne (newW C t 0) φ ψ =
      mixChg (compP hne C) (oldP hne) (signedCoef t) (1 / 2) (1 / 2) 1 (ex φ) (ex ψ) := by
  unfold symK mixChg
  rw [kform_new_dot, kform_new_dot, kform_old_dot, mul_sum, mul_sum, ← sum_add_distrib]
  congr 1
  · refine sum_congr rfl fun c _ => ?_
    ring
  · ring

/-- **The skew form of `F₁` is `mixChg` with `(½, −½, 0)`.** -/
theorem skwK_dot (C : FoldComponents pr hne) (t : ℝ) (φ ψ : (Fin 3 → BlockLabel pr) → ℝ) :
    skwK pr (newW C t 0) φ ψ =
      mixChg (compP hne C) (oldP hne) (signedCoef t) (1 / 2) (-1 / 2) 0 (ex φ) (ex ψ) := by
  unfold skwK mixChg
  rw [kform_new_dot, kform_new_dot, mul_sum, mul_sum, ← sum_sub_distrib, zero_mul, sub_zero]
  refine sum_congr rfl fun c _ => ?_
  ring

theorem mform_ip (φ : (Fin 3 → BlockLabel pr) → ℝ) :
    mform (lawF pr hne).weight φ = ip (mP hne) (ex φ) (ex φ) :=
  mform_eq_dot hne φ

end Frame

end Sarkozy.NormBoundsPaper4
