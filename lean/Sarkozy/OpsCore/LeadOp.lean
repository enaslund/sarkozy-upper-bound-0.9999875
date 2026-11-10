module

public import Sarkozy.OpsCore.LeadFold
public import Sarkozy.OpsCore.Tensor
public import Sarkozy.OpsCore.BracketOp

@[expose] public section

/-!
# The leading star of a fold record as an operator: `LeadOK` at the atom level (OPS-L)

`paper/sections/23_envelopes.tex`, the star form (N1), (N2); `paper/sections/21_middle_records.tex`,
`prop:signed-bounds`(b),(e).

`foldChange_skew_split` gives the split of the skew change of a fold record in form language.
`StarData`/`LeadOK` need operators on `L²(m)`. This file realizes bounded bilinear forms as
operators and assembles the per-record content of `LeadOK` for the fold records:

* `opOfForm m Bf`: the operator with kernel `Bf(δ_x, δ_y)`; **`ip_opOfForm`**:
  `⟨f, opOfForm Bf g⟩_m = Bf(f, g)` for a bilinear `Bf` bounded in `L²(m)`, `m ≥ 0`;
* `lFormBil`: PG's leading star form `L^m_t` as a bilinear map (linearity of `adj`, `uip`);
  `recordLeadBil`: the fold record's leading form `recordLead` as a bilinear map;
* **`fold_leadOK_atom`**: for the skew change `ζ^a` of the fold record `F_{j+1}` of a middle block,
  with `Δ̂ = w⁻¹ recOp(mOf, ζ^a)` and `L = opOfForm(w⁻¹ Lead_j)`: `‖L‖ ≤ w⁻¹ ℓ'`,
  `‖Δ̂ − L‖ ≤ w⁻¹ e_R` in `L²(mOf)`, and `L` has a skew kernel. These are the fields `hL`, `hE`,
  `hLs` of `LeadOK` for a fold record, at B8's frame (`mOf`, B8's `foldChange`).
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.OpsCore

open Sarkozy.EnvelopeSteps

/-! ## Operators of bounded bilinear forms -/

section Generic

variable {O : Type*} [Fintype O] [DecidableEq O]

/-- **The operator of a bilinear form** relative to `m`:
`(K g)(x) = m(x)⁻¹ ∑_y Bf(δ_x, δ_y) g(y)`. -/
noncomputable def opOfForm (m : O → ℝ) (Bf : (O → ℝ) → (O → ℝ) → ℝ) : (O → ℝ) →ₗ[ℝ] (O → ℝ) where
  toFun g x := (m x)⁻¹ * ∑ y, Bf (EnvelopeSteps.delta x) (EnvelopeSteps.delta y) * g y
  map_add' g g' := by
    funext x
    simp only [Pi.add_apply, mul_add, sum_add_distrib]
  map_smul' a g := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
    exact sum_congr rfl fun y _ => by ring

/-- The expansion of a bilinear map over the point masses. -/
theorem bilin_expand (β : (O → ℝ) →ₗ[ℝ] (O → ℝ) →ₗ[ℝ] ℝ) (f g : O → ℝ) :
    β f g = ∑ x, ∑ y, f x * g y * β (EnvelopeSteps.delta x) (EnvelopeSteps.delta y) := by
  have h1 : β f = ∑ x, f x • β (EnvelopeSteps.delta x) := by
    conv_lhs => rw [eq_sum_delta f]
    simp only [map_sum, map_smul]
  have h2 : ∀ x, β (EnvelopeSteps.delta x) g =
      ∑ y, g y * β (EnvelopeSteps.delta x) (EnvelopeSteps.delta y) := by
    intro x
    conv_lhs => rw [eq_sum_delta g]
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [h1, LinearMap.sum_apply]
  refine sum_congr rfl fun x _ => ?_
  rw [LinearMap.smul_apply, h2, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun y _ => by ring

theorem ip_delta_self (m : O → ℝ) (x : O) :
    ip m (EnvelopeSteps.delta x) (EnvelopeSteps.delta x) = m x := by
  unfold ip EnvelopeSteps.delta
  rw [Fintype.sum_eq_single x (fun y hy => by simp [hy])]
  simp

/-- **`⟨f, opOfForm Bf g⟩_m = Bf(f, g)`** for a bilinear map bounded in `L²(m)`. -/
theorem ip_opOfForm {m : O → ℝ} (β : (O → ℝ) →ₗ[ℝ] (O → ℝ) →ₗ[ℝ] ℝ) {C : ℝ}
    (hbd : ∀ f g, |β f g| ≤ C * Real.sqrt (ip m f f) * Real.sqrt (ip m g g)) (f g : O → ℝ) :
    ip m f (opOfForm m (fun f g => β f g) g) = β f g := by
  rw [bilin_expand β f g]
  unfold ip opOfForm
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  refine sum_congr rfl fun x _ => ?_
  by_cases hx : m x = 0
  · have h0 : ∀ y, β (EnvelopeSteps.delta x) (EnvelopeSteps.delta y) = 0 := by
      intro y
      have h := hbd (EnvelopeSteps.delta x) (EnvelopeSteps.delta y)
      rw [ip_delta_self, hx, Real.sqrt_zero, mul_zero, zero_mul] at h
      exact abs_nonpos_iff.mp h
    rw [hx, zero_mul]
    exact (sum_eq_zero fun y _ => by rw [h0 y, mul_zero]).symm
  · rw [mul_sum, mul_sum, mul_sum]
    refine sum_congr rfl fun y _ => ?_
    field_simp

/-- The operator of a bounded bilinear map has the form's bound. -/
theorem formLE_opOfForm {m : O → ℝ} (β : (O → ℝ) →ₗ[ℝ] (O → ℝ) →ₗ[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ f g, |β f g| ≤ C * Real.sqrt (ip m f f) * Real.sqrt (ip m g g)) :
    FormLE m (opOfForm m (fun f g => β f g)) C :=
  ⟨hC, fun f g => by rw [ip_opOfForm β hbd]; exact hbd f g⟩

/-- Its kernel is the form at the point masses. -/
theorem kern_opOfForm {m : O → ℝ} (β : (O → ℝ) →ₗ[ℝ] (O → ℝ) →ₗ[ℝ] ℝ) {C : ℝ}
    (hbd : ∀ f g, |β f g| ≤ C * Real.sqrt (ip m f f) * Real.sqrt (ip m g g)) (x y : O) :
    kern m (opOfForm m (fun f g => β f g)) x y =
      β (EnvelopeSteps.delta x) (EnvelopeSteps.delta y) := by
  have h := ip_opOfForm β hbd (EnvelopeSteps.delta x) (EnvelopeSteps.delta y)
  rw [ip_eq_kern] at h
  rw [← h, Fintype.sum_eq_single x, Fintype.sum_eq_single y]
  · simp [EnvelopeSteps.delta]
  · intro z hz
    simp [EnvelopeSteps.delta, hz]
  · intro z hz
    exact sum_eq_zero fun w _ => by simp [EnvelopeSteps.delta, hz]

end Generic

/-! ## The leading star forms are bilinear -/

section Prime

open Sarkozy.PrimeGram

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] in
theorem adj_add (m : (Fin 3 → F) → ℝ) (S : (F → ℝ) → (Fin 3 → F) → ℝ) (f g : (Fin 3 → F) → ℝ) :
    adj m S (f + g) = adj m S f + adj m S g := by
  funext a
  simp only [adj, cen, mip, Pi.add_apply, mul_add, sum_add_distrib]
  ring

omit [Field F] in
theorem adj_smul (m : (Fin 3 → F) → ℝ) (S : (F → ℝ) → (Fin 3 → F) → ℝ) (c : ℝ)
    (f : (Fin 3 → F) → ℝ) : adj m S (c • f) = c • adj m S f := by
  funext a
  simp only [adj, cen, mip, Pi.smul_apply, smul_eq_mul]
  rw [show (∑ x, m x * S (Sarkozy.PrimeGram.delta a) x * (c * f x)) =
      c * ∑ x, m x * S (Sarkozy.PrimeGram.delta a) x * f x by
    rw [mul_sum]; exact sum_congr rfl fun x _ => by ring]
  rw [show (∑ s, (Fintype.card F : ℝ) * ∑ x, m x * S (Sarkozy.PrimeGram.delta s) x * (c * f x)) =
      c * ∑ s, (Fintype.card F : ℝ) * ∑ x, m x * S (Sarkozy.PrimeGram.delta s) x * f x by
    rw [mul_sum]
    refine sum_congr rfl fun s _ => ?_
    rw [mul_sum, mul_sum, mul_sum]
    exact sum_congr rfl fun x _ => by ring]
  ring

omit [Field F] [DecidableEq F] in
theorem uip_add_left (h h' k : F → ℝ) : uip (h + h') k = uip h k + uip h' k := by
  simp only [uip, Pi.add_apply, add_mul, sum_add_distrib, mul_add]

omit [Field F] [DecidableEq F] in
theorem uip_add_right (h k k' : F → ℝ) : uip h (k + k') = uip h k + uip h k' := by
  simp only [uip, Pi.add_apply, mul_add, sum_add_distrib]

omit [Field F] [DecidableEq F] in
theorem uip_smul_left (c : ℝ) (h k : F → ℝ) : uip (c • h) k = c * uip h k := by
  simp only [uip, Pi.smul_apply, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun a _ => by ring

omit [Field F] [DecidableEq F] in
theorem uip_smul_right (c : ℝ) (h k : F → ℝ) : uip h (c • k) = c * uip h k := by
  simp only [uip, Pi.smul_apply, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun a _ => by ring

/-- **PG's leading star form `L^m_t` as a bilinear map.** -/
noncomputable def lFormBil (m : (Fin 3 → F) → ℝ) (t : ℝ) :
    ((Fin 3 → F) → ℝ) →ₗ[ℝ] ((Fin 3 → F) → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (lForm m t)
    (fun f f' g => by
      simp only [lForm, Ba, Wa, adj_add, uip_add_left, mul_add, sum_add_distrib]
      ring)
    (fun c f g => by
      simp only [lForm, Ba, Wa, adj_smul, uip_smul_left]
      rw [smul_eq_mul, mul_sub, mul_sum, mul_sum]
      congr 1 <;> exact sum_congr rfl fun i _ => by ring)
    (fun f g g' => by
      simp only [lForm, Ba, Wa, adj_add, uip_add_right, mul_add, sum_add_distrib]
      ring)
    (fun c f g => by
      simp only [lForm, Ba, Wa, adj_smul, uip_smul_right]
      rw [smul_eq_mul, mul_sub, mul_sum, mul_sum]
      congr 1 <;> exact sum_congr rfl fun i _ => by ring)

theorem lFormBil_apply (m : (Fin 3 → F) → ℝ) (t : ℝ) (f g : (Fin 3 → F) → ℝ) :
    lFormBil m t f g = lForm m t f g := rfl

end Prime

/-! ## The leading form of a fold record as a bilinear map, and `LeadOK` at the atom level -/

section Record

open Sarkozy.PrimeGram Sarkozy.NormBoundsPaper4 Sarkozy.SignedGram Sarkozy.PartV
  Sarkozy.SignedComponents Sarkozy.FoldSymSkew Sarkozy.PartVRecords Sarkozy.MiddleComparison

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- Reading a half function through the fold `F_{j+1}` (and, for `F₂`, the reflection `rf`), as a
function of the prime triples; linear. -/
noncomputable def readLin (j : Fin 2) :
    ((reservedCut.Half → BlockLabel pr) → ℝ) →ₗ[ℝ] ((∀ i, Ai pr i) → ℝ) where
  toFun F := ex (if j = 0 then fr pr 0 F else fun x => fr pr 1 F (rf x))
  map_add' F G := by
    funext u
    by_cases hj : j = 0 <;> simp [hj]
  map_smul' c F := by
    funext u
    by_cases hj : j = 0 <;> simp [hj]

/-- The evaluation of a block function on the line through `x₀` in the coordinate `i`; linear. -/
def evalLin (x₀ : ∀ i, Ai pr i) (i : ι) : ((∀ i, Ai pr i) → ℝ) →ₗ[ℝ] (Ai pr i → ℝ) where
  toFun φ a := φ (Function.update x₀ i a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The singleton component of a half function read through the fold `F_{j+1}`, as a linear map. -/
noncomputable def compLin (hne : MiddleNonempty pr) (x₀ : ∀ i, Ai pr i) (j : Fin 2) (i : ι) :
    ((reservedCut.Half → BlockLabel pr) → ℝ) →ₗ[ℝ] (Ai pr i → ℝ) :=
  evalLin pr x₀ i ∘ₗ Matrix.mulVecLin (SP (mP hne) (sing i)) ∘ₗ readLin pr j

/-- **The leading form of the fold record `F_{j+1}` as a bilinear map.** -/
noncomputable def recordLeadBil (hne : MiddleNonempty pr) (t : ℝ) (x₀ : ∀ i, Ai pr i)
    (j : Fin 2) :
    ((reservedCut.Half → BlockLabel pr) → ℝ) →ₗ[ℝ]
      ((reservedCut.Half → BlockLabel pr) → ℝ) →ₗ[ℝ] ℝ :=
  if j = 0 then ∑ i, (lFormBil (mP hne i) t).compl₁₂ (compLin pr hne x₀ 0 i) (compLin pr hne x₀ 0 i)
  else (∑ i, (lFormBil (mP hne i) t).compl₁₂ (compLin pr hne x₀ 1 i) (compLin pr hne x₀ 1 i)).flip

theorem recordLeadBil_apply (hne : MiddleNonempty pr) (t : ℝ) (x₀ : ∀ i, Ai pr i) (j : Fin 2)
    (F G : (reservedCut.Half → BlockLabel pr) → ℝ) :
    recordLeadBil pr hne t x₀ j F G = recordLead pr hne t x₀ j F G := by
  fin_cases j
  · simp only [recordLeadBil, Fin.zero_eta, Fin.isValue, ↓reduceIte]
    rw [LinearMap.sum_apply, LinearMap.sum_apply]
    simp only [LinearMap.compl₁₂_apply, lFormBil_apply]
    rfl
  · simp only [recordLeadBil, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte,
      LinearMap.flip_apply]
    rw [LinearMap.sum_apply, LinearMap.sum_apply]
    simp only [LinearMap.compl₁₂_apply, lFormBil_apply]
    rfl

theorem recordLead_skew (hne : MiddleNonempty pr) (t : ℝ) (x₀ : ∀ i, Ai pr i) (j : Fin 2)
    (F G : (reservedCut.Half → BlockLabel pr) → ℝ) :
    recordLead pr hne t x₀ j G F = -recordLead pr hne t x₀ j F G := by
  fin_cases j
  · simp only [recordLead, foldLead, singForm, Fin.isValue]
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun i _ => lForm_skew _ _ _ _
  · simp only [recordLead, foldLead, singForm, Fin.isValue]
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun i _ => lForm_skew _ _ _ _

variable (h : ClassThreeBlock pr) (hne : MiddleNonempty pr)
  (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
  {r : ℝ} (hr : 0 ≤ r) (b : ℝ)

/-- **`LeadOK` for a fold record at the atom level** (`prop:signed-bounds`(b),(e), the star form
(N1)–(N2)): for the skew change `ζ^a` of the fold record `F_{j+1}` of a middle block (B8's frame),
the normalized record operator `Δ̂ = w⁻¹ recOp(mOf, ζ^a)` and the leading operator
`L = opOfForm(w⁻¹ Lead_j)` satisfy `‖L‖ ≤ w⁻¹ ℓ'`, `‖Δ̂ − L‖ ≤ w⁻¹ e_R` in `L²(mOf)`, and `L` has a
skew kernel; from the prime split (`SkewSplitPrime`, PG's `NewDecomp`) and FD's fold inputs. -/
theorem fold_leadOK_atom (C : FoldComponents pr hne) (hC : Reflected C) {t ρ eR ℓ' : ℝ}
    (ht : 0 ≤ t) (heR : 0 ≤ eR) (hℓ' : 0 ≤ ℓ') (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hρ : ∀ c i, CentredNorm (mP hne i) (compP hne C c i) ρ) (hmulti : (1 + t) * ρ ^ 2 ≤ eR)
    (hsplit : ∀ i, SkewSplitPrime hne C t ℓ' eR i) (x₀ : ∀ i, Ai pr i) (j : Fin 2) {w : ℝ}
    (hw : 0 < w) :
    OpNormLE (mOf (middleFrame pr hne root W I hr b h) (.inl j))
        (opOfForm (mOf (middleFrame pr hne root W I hr b h) (.inl j))
          (fun F G => (w⁻¹ • recordLeadBil pr hne t x₀ j) F G)) (w⁻¹ * ℓ') ∧
      OpNormLE (mOf (middleFrame pr hne root W I hr b h) (.inl j))
        (w⁻¹ • recOp reservedCut (mOf (middleFrame pr hne root W I hr b h) (.inl j))
            (foldChange pr h hne root W I hr b C t (.inl j) .skew) -
          opOfForm (mOf (middleFrame pr hne root W I hr b h) (.inl j))
            (fun F G => (w⁻¹ • recordLeadBil pr hne t x₀ j) F G)) (w⁻¹ * eR) ∧
      ∀ x y, kern (mOf (middleFrame pr hne root W I hr b h) (.inl j))
          (opOfForm (mOf (middleFrame pr hne root W I hr b h) (.inl j))
            (fun F G => (w⁻¹ • recordLeadBil pr hne t x₀ j) F G)) y x =
        -kern (mOf (middleFrame pr hne root W I hr b h) (.inl j))
          (opOfForm (mOf (middleFrame pr hne root W I hr b h) (.inl j))
            (fun F G => (w⁻¹ • recordLeadBil pr hne t x₀ j) F G)) x y := by
  set m := mOf (middleFrame pr hne root W I hr b h) (.inl j)
  set ζ := foldChange pr h hne root W I hr b C t (.inl j) .skew
  have hm : ∀ x, 0 ≤ m x := mOf_nonneg _ _
  have hwi : 0 ≤ w⁻¹ := inv_nonneg.mpr hw.le
  have hsplit' := foldChange_skew_split pr h hne root W I hr b C hC ht heR hℓ' hρ0 hρ1 hρ hmulti
    hsplit x₀ j
  set β := w⁻¹ • recordLeadBil pr hne t x₀ j
  have hβ : ∀ F G, β F G = w⁻¹ * recordLead pr hne t x₀ j F G := fun F G => by
    simp only [β, LinearMap.smul_apply, smul_eq_mul, recordLeadBil_apply]
  -- the bounds of the leading form
  have hbd : ∀ F G, |β F G| ≤ w⁻¹ * ℓ' * Real.sqrt (ip m F F) * Real.sqrt (ip m G G) := by
    intro F G
    rw [hβ, abs_mul, abs_of_nonneg hwi]
    calc w⁻¹ * |recordLead pr hne t x₀ j F G|
        ≤ w⁻¹ * (ℓ' * Real.sqrt (hsq reservedCut m F) * Real.sqrt (hsq reservedCut m G)) :=
          mul_le_mul_of_nonneg_left (hsplit' F G).2 hwi
      _ = _ := by unfold hsq ip; ring
  -- the record charges only the support of `m`
  have hFB : FormBound reservedCut m ζ (eR + ℓ') := by
    refine ⟨add_nonneg heR hℓ', fun F G => ?_⟩
    obtain ⟨h1, h2⟩ := hsplit' F G
    calc |reservedCut.form ζ F G|
        ≤ |reservedCut.form ζ F G - recordLead pr hne t x₀ j F G| +
            |recordLead pr hne t x₀ j F G| := by
          have := abs_add_le (reservedCut.form ζ F G - recordLead pr hne t x₀ j F G)
            (recordLead pr hne t x₀ j F G)
          rwa [sub_add_cancel] at this
      _ ≤ _ := by
          have e : (eR + ℓ') * Real.sqrt (hsq reservedCut m F) * Real.sqrt (hsq reservedCut m G) =
              eR * Real.sqrt (hsq reservedCut m F) * Real.sqrt (hsq reservedCut m G) +
                ℓ' * Real.sqrt (hsq reservedCut m F) * Real.sqrt (hsq reservedCut m G) := by ring
          rw [e]
          exact add_le_add h1 h2
  have hplus : PlusIn reservedCut m ζ := plusIn_of_formBound hFB
  refine ⟨(formLE_opOfForm β (mul_nonneg hwi hℓ') hbd).opNormLE hm, ?_, ?_⟩
  · refine FormLE.opNormLE hm ⟨mul_nonneg hwi heR, fun F G => ?_⟩
    rw [LinearMap.sub_apply, ip_sub_right, LinearMap.smul_apply, ip_smul_right, ip_recOp hplus,
      ip_opOfForm β hbd, hβ, ← mul_sub, abs_mul, abs_of_nonneg hwi]
    calc w⁻¹ * |reservedCut.form ζ F G - recordLead pr hne t x₀ j F G|
        ≤ w⁻¹ * (eR * Real.sqrt (hsq reservedCut m F) * Real.sqrt (hsq reservedCut m G)) :=
          mul_le_mul_of_nonneg_left (hsplit' F G).1 hwi
      _ = _ := by unfold hsq ip; ring
  · intro x y
    rw [kern_opOfForm β hbd, kern_opOfForm β hbd, hβ, hβ, recordLead_skew]
    ring

end Record

end Sarkozy.OpsCore
