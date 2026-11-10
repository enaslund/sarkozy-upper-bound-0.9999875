module

public import Sarkozy.FiveType.PolarizationOrders
public import Sarkozy.Reflection.BracketMatrix
public import Sarkozy.Structured.Polarization

/-!
# Polarization over several blocks (`lem:tr:polarization`(c))

Source: `paper/sections/17_completion_repair.tex`, `lem:tr:polarization`(c) and its proof;
`lem:record:block-gram` (block-Gram tensorization; here the existing `ReflectionCut.Bracket.tensor`)
and `eq:cc:kron` (here `tensorLaw` and `Positive.tensor`, `Reflection/Tensor.lean`).

Let `J` be a finite nonempty set of blocks, and for each block `𝔅 ∈ J` a five-type datum on
`𝔛_𝔅` with `‖T_F^b - J‖ ≤ e_{F,𝔅}`, `‖T_E^b - J‖ ≤ e_{E,𝔅}` on `supp ν` and
`ε_𝔅 ≥ e_{F,𝔅} + e_{E,𝔅}`. Measures on `(∏_𝔅 𝔛_𝔅)^{ℤ/6ℤ}` are tensor products `tensorLaw`.

* `Datum.bracket_F1`: the block matrix `(A K; Kᵀ D)` of `lem:tr:polarization`(b), with
  `A = C(Π_{E_0} + εΠ_{G_e})`, `D = C(Π_{E_1} + εΠ_{G_o})`, `K = C(Π_{F_1})`, is positive
  semidefinite, as a bracket (`ReflectionCut.Bracket`) at `ϑ₀`. In form language the corner
  supports are automatic: the cut form of `Π_{F_1}` at `(g, g')` is `E_b ⟨U^g_b, T_F^b V^{g'}_b⟩`
  (`Datum.form_F1_bil`), so it sees `g` only through `U^g` and `g'` only through `V^{g'}`. Hence
  no hypothesis `ν^b({b}) = 0` is needed.
* `polarization_c_first`: **(c), first claim**, for both signs:
  `⊗(Π_{E_0} + εΠ_{G_e}) + ⊗(Π_{E_1} + εΠ_{G_o}) ± (⊗Π_{F_1} + ⊗Π_{F_2}) ⪰_{ϑ₀} 0`.
  The bracket tensorizes (`Bracket.tensor`), a bracket holds with `-K` as well
  (`Bracket.neg`), and the cut matrix of `⊗Π_{F_2}` is the transpose of that of `⊗Π_{F_1}`,
  because `⊗Π_{F_2}` is the image of `⊗Π_{F_1}` under `ϑ₀` (`tensorLaw_comp`).
* `polarization_c_second`: **(c), second claim**:
  `⊗(Π_{E_0} + Π_{E_1} + ε(Π_{G_e} + Π_{G_o})) ⪰_{ϑ₀} ⊗Π_{F_1} + ⊗Π_{F_2}`. The left side is
  expanded into the `2^{|J|}` products (`tensorLaw_add_expand`); the two constant choices give the
  first claim, and every other product is a tensor product of positive laws.
* `polarization_d_blocks`: **(d), last claim**: `⊗𝒬^E_𝔅 ± ⊗𝒬^F_𝔅 ⪰_{ϑ₀} 0` for both signs,
  from the two orders of (b) at every block and WP-R's `Structured.tensor_two_sign_positive`
  (the sign identity of (d)).
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.FiveType

open Sarkozy.Labellings ReflectionCut

/-- A finite law has a point of positive weight. -/
theorem exists_supp {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) : ∃ ω, μ.weight ω ≠ 0 := by
  obtain ⟨ω, -, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := μ.weight)
    (by rw [μ.total]; exact one_ne_zero)
  exact ⟨ω, h⟩

/-! ## Tensor products: relabelling and multilinear expansion -/

section TensorFacts

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]

/-- **Relabelling the slots commutes with tensor products**: if `L'_j f = L_j(f(· ∘ π))` for
every block, then `⊗L' = (⊗L)(· ∘ π)`. -/
theorem tensorLaw_comp (π : V ≃ V) (L L' : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (h : ∀ j (f : (V → X j) → ℝ), L' j f = L j (fun y => f (y ∘ π)))
    (F : (V → ∀ j, X j) → ℝ) : tensorLaw L' F = tensorLaw L (fun z => F (z ∘ π)) := by
  have hd : ∀ j (x : V → X j), lawDensity (L' j) x = lawDensity (L j) (x ∘ π.symm) := by
    intro j x
    unfold lawDensity
    rw [h j]
    congr 1
    funext y
    have hiff : (y ∘ π = x) ↔ (y = x ∘ π.symm) := by
      constructor
      · rintro rfl; funext v; simp
      · rintro rfl; funext v; simp
    by_cases hy : y ∘ π = x
    · have h1 : (y ∘ π = x) = True := eq_true hy
      have h2 : (y = x ∘ π.symm) = True := eq_true (hiff.mp hy)
      simp only [h1, h2, ↓reduceIte]
    · have h1 : (y ∘ π = x) = False := eq_false hy
      have h2 : (y = x ∘ π.symm) = False := eq_false fun h' => hy (hiff.mpr h')
      simp only [h1, h2, ↓reduceIte]
  let e : (∀ j, V → X j) ≃ (∀ j, V → X j) :=
    Equiv.piCongrRight (fun j => Equiv.arrowCongr π.symm (Equiv.refl (X j)))
  have he : ∀ w j, e w j = w j ∘ π := fun w j => by
    funext v
    simp [e, Equiv.arrowCongr_apply]
  change ∑ z : ∀ j, V → X j, (∏ j, lawDensity (L' j) (z j)) * F (fun v j => z j v) =
    ∑ z : ∀ j, V → X j, (∏ j, lawDensity (L j) (z j)) * F ((fun v j => z j v) ∘ π)
  simp_rw [hd]
  rw [← Fintype.sum_equiv e
    (fun w => (∏ j, lawDensity (L j) (e w j ∘ π.symm)) * F (fun v j => e w j v)) _
    (fun _ => rfl)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h1 : ∀ j, e w j ∘ π.symm = w j := fun j => by
    rw [he]; funext v; simp
  simp_rw [h1]
  congr 2

/-- A tensor product of functionals invariant under a relabelling is invariant. -/
theorem tensorLaw_inv (π : V ≃ V) (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (h : ∀ j (f : (V → X j) → ℝ), L j (fun y => f (y ∘ π)) = L j f)
    (F : (V → ∀ j, X j) → ℝ) : tensorLaw L (fun z => F (z ∘ π)) = tensorLaw L F :=
  (tensorLaw_comp π L L (fun j f => (h j f).symm) F).symm

/-- **Multilinear expansion** of `⊗_j (L⁰_j + L¹_j)` into the `2^{|J|}` products. -/
theorem tensorLaw_add_expand (L0 L1 : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) :
    tensorLaw (fun j => L0 j + L1 j) =
      ∑ s : J → Fin 2, tensorLaw (fun j => if s j = 0 then L0 j else L1 j) := by
  apply LinearMap.ext
  intro F
  rw [LinearMap.sum_apply]
  change ∑ z : ∀ j, V → X j, (∏ j, lawDensity (L0 j + L1 j) (z j)) * F (fun v j => z j v) =
    ∑ s : J → Fin 2, ∑ z : ∀ j, V → X j,
      (∏ j, lawDensity (if s j = 0 then L0 j else L1 j) (z j)) * F (fun v j => z j v)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← Finset.sum_mul]
  congr 1
  have hsplit : ∀ j, lawDensity (L0 j + L1 j) (z j) =
      ∑ k : Fin 2, (if k = 0 then lawDensity (L0 j) (z j) else lawDensity (L1 j) (z j)) := by
    intro j
    rw [Fin.sum_univ_two]
    simp only [Fin.isValue, ↓reduceIte, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one]
    rfl
  simp_rw [hsplit]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun s _ => Finset.prod_congr rfl fun j _ => ?_
  by_cases hs : s j = 0
  · simp only [hs, ↓reduceIte]
  · simp only [hs, ↓reduceIte]

end TensorFacts

/-! ## Brackets -/

section Brackets

variable {V X : Type*} [Fintype V] [DecidableEq V]

/-- A bracket holds with the opposite middle term. -/
theorem Bracket.neg {c : ReflectionCut V} {L K R : ((V → X) → ℝ) →ₗ[ℝ] ℝ}
    (h : c.Bracket L K R) : c.Bracket L (-K) R := by
  refine ⟨h.left_positive, h.right_positive, fun F G => ?_⟩
  have h1 := h.nonneg F ((-1 : ℝ) • G)
  rw [c.form_smul_right, c.form_smul_left, c.form_smul_right] at h1
  have h2 : c.form (-K) F G = -c.form K F G := rfl
  rw [h2]
  linarith

/-- If `M'` is the image of `M` under the reflection, the cut form of `M'` is the transposed
form of `M`. -/
theorem form_of_flip_image (c : ReflectionCut V) {M M' : ((V → X) → ℝ) →ₗ[ℝ] ℝ}
    (h : ∀ f : (V → X) → ℝ, M' f = M (fun z => f (z ∘ c.flip))) (F G : (c.Half → X) → ℝ) :
    c.form M' F G = c.form M G F := by
  change M' (fun z => F (fun v => z v.1) * G (fun v => z (c.flip v.1))) =
    M (fun z => G (fun v => z v.1) * F (fun v => z (c.flip v.1)))
  rw [h]
  congr 1
  funext z
  simp only [Function.comp_apply, c.flip_flip]
  ring

end Brackets

/-! ## One block -/

namespace Datum

variable {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛] (D : Datum 𝔛)

/-- `Π_{E_0} + εΠ_{G_e}`. -/
noncomputable def QE0 (ε : ℝ) : ((ZMod 6 → 𝔛) → ℝ) →ₗ[ℝ] ℝ := D.compE 0 + ε • D.compG 0 0

/-- `Π_{E_1} + εΠ_{G_o}`. -/
noncomputable def QE1 (ε : ℝ) : ((ZMod 6 → 𝔛) → ℝ) →ₗ[ℝ] ℝ := D.compE 1 + ε • D.compG 1 1

theorem QE_eq (ε : ℝ) : D.QE ε = D.QE0 ε + D.QE1 ε := by
  apply LinearMap.ext
  intro f
  simp only [QE, QE0, QE1, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- **The bilinear cut form of `Π_{F_1}`**: `Q_{Π_{F_1}}(g, g') = E_b ⟨U^g_b, T_F^b V^{g'}_b⟩`. -/
theorem form_F1_bil (F G : (Half0 → 𝔛) → ℝ) :
    (chamberCut 0).form (D.compF 1) F G =
      D.nu.expect (fun b => kf (D.nub b) (D.TF b) (Uf F b) (Vf G b)) := by
  unfold compF
  rw [form_pattern, expect_piF, ← triple_kf]
  obtain ⟨h0, h1, h2, h5, h4, h3⟩ : fold 1 0 = 1 ∧ fold 1 1 = 0 ∧ fold 1 2 = 0 ∧ fold 1 5 = 2 ∧
      fold 1 4 = 2 ∧ fold 1 3 = 1 := by decide
  simp only [h0, h1, h2, h3, h4, h5]
  rfl

theorem QE0_flip_inv (ε : ℝ) (f : (ZMod 6 → 𝔛) → ℝ) :
    D.QE0 ε (fun z => f (z ∘ (chamberCut 0).flip)) = D.QE0 ε f := by
  simp only [QE0, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [flip_inv_of_inv6 (D.compE_inv6 0), (D.compG_diag_flip_inv f).1]

theorem QE1_flip_inv (ε : ℝ) (f : (ZMod 6 → 𝔛) → ℝ) :
    D.QE1 ε (fun z => f (z ∘ (chamberCut 0).flip)) = D.QE1 ε f := by
  simp only [QE1, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [flip_inv_of_inv6 (D.compE_inv6 1), (D.compG_diag_flip_inv f).2]

/-- **The block matrix `(A K; Kᵀ D)` of `lem:tr:polarization`(b) is positive semidefinite**, as a
bracket at `ϑ₀`. -/
theorem bracket_F1 {eF eE ε : ℝ}
    (hF : ∀ b, D.nu.weight b ≠ 0 → NormBound (D.nub b) (D.TF b) eF)
    (hE : ∀ b, D.nu.weight b ≠ 0 → NormBound (D.nub b) (D.TE b) eE) (hε : eF + eE ≤ ε) :
    (chamberCut 0).Bracket (D.QE0 ε) (D.compF 1) (D.QE1 ε) := by
  have hdiag := D.polarization_b_diag hE (le_trans (le_add_of_nonneg_left
    (NormBound.nonneg (hF _ (exists_supp D.nu).choose_spec))) hε)
  refine ⟨hdiag.1, hdiag.2, fun F G => ?_⟩
  have e0 : (chamberCut 0).form (D.QE0 ε) F F = D.nu.expect (fun b =>
      kf (D.nub b) (D.TE b) (Uf F b) (Uf F b) + ε * ip (D.nub b) (Uf F b) (Uf F b)) := by
    simp only [QE0, form_add, form_smul]
    rw [D.form_E0, D.form_G00, FiniteLaw.expect_add, FiniteLaw.expect_const_mul]
  have e1 : (chamberCut 0).form (D.QE1 ε) G G = D.nu.expect (fun b =>
      kf (D.nub b) (D.TE b) (Vf G b) (Vf G b) + ε * ip (D.nub b) (Vf G b) (Vf G b)) := by
    simp only [QE1, form_add, form_smul]
    rw [D.form_E1, D.form_G11, FiniteLaw.expect_add, FiniteLaw.expect_const_mul]
  rw [e0, e1, D.form_F1_bil, ← FiniteLaw.expect_const_mul, ← FiniteLaw.expect_add,
    ← FiniteLaw.expect_add]
  refine expect_nonneg_supp D.nu fun b hb => ?_
  have hp := polarization_form (hF b hb) (hE b hb) (hE b hb) (Uf F b) (fun y => -Vf G b y)
  rw [kf_neg_neg, kf_neg_right] at hp
  have hip : ip (D.nub b) (fun y => -Vf G b y) (fun y => -Vf G b y) =
      ip (D.nub b) (Vf G b) (Vf G b) :=
    (D.nub b).expect_congr fun y => by ring
  have hmean : (D.nub b).expect (fun y => -Vf G b y) = -(D.nub b).expect (Vf G b) := by
    rw [show (fun y => -Vf G b y) = fun y => (-1) * Vf G b y from funext fun y => by ring,
      FiniteLaw.expect_const_mul]
    ring
  rw [hip, hmean] at hp
  have hU := ip_self_eq (D.nub b) (Uf F b)
  have hV := ip_self_eq (D.nub b) (Vf G b)
  have h0 : 0 ≤ (ε - (eF + eE)) * (ip (D.nub b) (Uf F b) (Uf F b) +
      ip (D.nub b) (Vf G b) (Vf G b)) := by
    rw [hU, hV]; exact mul_nonneg (by linarith) (by positivity)
  nlinarith [sq_nonneg ((D.nub b).expect (Uf F b) + (D.nub b).expect (Vf G b))]

end Datum

/-! ## Several blocks -/

section Blocks

variable {J : Type*} [Fintype J] [DecidableEq J] {X : J → Type*} [∀ j, Fintype (X j)]
  [∀ j, DecidableEq (X j)]

/-- **`lem:tr:polarization`(c), first claim**, both signs:
`⊗(Π_{E_0,𝔅} + ε_𝔅Π_{G_e,𝔅}) + ⊗(Π_{E_1,𝔅} + ε_𝔅Π_{G_o,𝔅}) ± (⊗Π_{F_1,𝔅} + ⊗Π_{F_2,𝔅}) ⪰_{ϑ₀} 0`. -/
theorem polarization_c_first (D : ∀ j, Datum (X j)) (eF eE ε : J → ℝ)
    (hF : ∀ j b, (D j).nu.weight b ≠ 0 → NormBound ((D j).nub b) ((D j).TF b) (eF j))
    (hE : ∀ j b, (D j).nu.weight b ≠ 0 → NormBound ((D j).nub b) ((D j).TE b) (eE j))
    (hε : ∀ j, eF j + eE j ≤ ε j) :
    (chamberCut 0).Positive (tensorLaw (fun j => (D j).QE0 (ε j)) +
        tensorLaw (fun j => (D j).QE1 (ε j)) -
        (tensorLaw (fun j => (D j).compF 1) + tensorLaw (fun j => (D j).compF 2))) ∧
    (chamberCut 0).Positive (tensorLaw (fun j => (D j).QE0 (ε j)) +
        tensorLaw (fun j => (D j).QE1 (ε j)) +
        (tensorLaw (fun j => (D j).compF 1) + tensorLaw (fun j => (D j).compF 2))) := by
  set A := tensorLaw (fun j => (D j).QE0 (ε j))
  set Dm := tensorLaw (fun j => (D j).QE1 (ε j))
  set K := tensorLaw (fun j => (D j).compF 1)
  set K2 := tensorLaw (fun j => (D j).compF 2)
  have hBr : (chamberCut 0).Bracket A K Dm :=
    Bracket.tensor fun j => (D j).bracket_F1 (hF j) (hE j) (hε j)
  have hK2 : ∀ f, K2 f = K (fun z => f (z ∘ (chamberCut 0).flip)) := fun f =>
    tensorLaw_comp (chamberCut 0).flip _ _ (fun j g => ((D j).compF12_flip g).1.symm) f
  have hA : ∀ f, A (fun z => f (z ∘ (chamberCut 0).flip)) = A f := fun f =>
    tensorLaw_inv (chamberCut 0).flip _ (fun j g => (D j).QE0_flip_inv (ε j) g) f
  have hD : ∀ f, Dm (fun z => f (z ∘ (chamberCut 0).flip)) = Dm f := fun f =>
    tensorLaw_inv (chamberCut 0).flip _ (fun j g => (D j).QE1_flip_inv (ε j) g) f
  have hKK : ∀ f, (K + K2) (fun z => f (z ∘ (chamberCut 0).flip)) = (K + K2) f := by
    intro f
    simp only [LinearMap.add_apply]
    rw [hK2 f, hK2 (fun z => f (z ∘ (chamberCut 0).flip))]
    have : (fun z : ZMod 6 → ∀ j, X j =>
        (fun z => f (z ∘ (chamberCut 0).flip)) (z ∘ (chamberCut 0).flip)) = f := by
      funext z
      simp only [Function.comp_def, (chamberCut 0).flip_flip]
    rw [this, add_comm]
  have hdiag : ∀ F, (chamberCut 0).form K2 F F = (chamberCut 0).form K F F := fun F =>
    form_of_flip_image (chamberCut 0) hK2 F F
  constructor
  · constructor
    · intro F G
      refine form_symm_of_flip_inv (chamberCut 0) (fun f => ?_) F G
      simp only [LinearMap.sub_apply, LinearMap.add_apply]
      rw [hA, hD]
      have := hKK f
      simp only [LinearMap.add_apply] at this
      rw [this]
    · intro F
      have h := (Bracket.neg hBr).nonneg F F
      rw [show (chamberCut 0).form (-K) F F = -(chamberCut 0).form K F F from rfl] at h
      rw [form_sub, form_add, form_add, hdiag]
      linarith
  · constructor
    · intro F G
      refine form_symm_of_flip_inv (chamberCut 0) (fun f => ?_) F G
      simp only [LinearMap.add_apply]
      rw [hA, hD]
      have := hKK f
      simp only [LinearMap.add_apply] at this
      rw [this]
    · intro F
      have h := hBr.nonneg F F
      rw [form_add, form_add, form_add, hdiag]
      linarith

/-- **`lem:tr:polarization`(c), second claim**:
`⊗(Π_{E_0,𝔅} + Π_{E_1,𝔅} + ε_𝔅(Π_{G_e,𝔅} + Π_{G_o,𝔅})) ⪰_{ϑ₀} ⊗Π_{F_1,𝔅} + ⊗Π_{F_2,𝔅}`. -/
theorem polarization_c_second [Nonempty J] (D : ∀ j, Datum (X j)) (eF eE ε : J → ℝ)
    (hF : ∀ j b, (D j).nu.weight b ≠ 0 → NormBound ((D j).nub b) ((D j).TF b) (eF j))
    (hE : ∀ j b, (D j).nu.weight b ≠ 0 → NormBound ((D j).nub b) ((D j).TE b) (eE j))
    (hε : ∀ j, eF j + eE j ≤ ε j) :
    (chamberCut 0).Below
      (tensorLaw (fun j => (D j).compF 1) + tensorLaw (fun j => (D j).compF 2))
      (tensorLaw (fun j => (D j).QE (ε j))) := by
  have hfirst := (polarization_c_first D eF eE ε hF hE hε).1
  have hdiag : ∀ j, (chamberCut 0).Positive ((D j).QE0 (ε j)) ∧
      (chamberCut 0).Positive ((D j).QE1 (ε j)) := fun j =>
    (D j).polarization_b_diag (hE j) (le_trans (le_add_of_nonneg_left
      (NormBound.nonneg (hF j _ (exists_supp (D j).nu).choose_spec))) (hε j))
  have hQE : tensorLaw (fun j => (D j).QE (ε j)) =
      tensorLaw (fun j => (D j).QE0 (ε j) + (D j).QE1 (ε j)) := by
    congr 1
    funext j
    exact (D j).QE_eq (ε j)
  set T : (J → Fin 2) → ((ZMod 6 → ∀ j, X j) → ℝ) →ₗ[ℝ] ℝ := fun s =>
    tensorLaw (fun j => if s j = 0 then (D j).QE0 (ε j) else (D j).QE1 (ε j)) with hT
  have hexp := tensorLaw_add_expand (fun j => (D j).QE0 (ε j)) (fun j => (D j).QE1 (ε j))
  let c0 : J → Fin 2 := fun _ => 0
  let c1 : J → Fin 2 := fun _ => 1
  have hc : c1 ≠ c0 := by
    intro h
    have := congrFun h (Classical.arbitrary J)
    exact absurd this (by decide)
  have hT0 : T c0 = tensorLaw (fun j => (D j).QE0 (ε j)) := by
    simp only [hT, c0, ↓reduceIte]
  have hT1 : T c1 = tensorLaw (fun j => (D j).QE1 (ε j)) := by
    simp only [hT, c1, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ↓reduceIte]
  have hsum : ∑ s, T s = T c0 + (T c1 + ∑ s ∈ (Finset.univ.erase c0).erase c1, T s) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c0),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hc, Finset.mem_univ c1⟩)]
  have hrest : (chamberCut 0).Positive (∑ s ∈ (Finset.univ.erase c0).erase c1, T s) :=
    Positive.sum _ fun s _ => Positive.tensor fun j => by
      by_cases hs : s j = 0
      · simp only [hs, ↓reduceIte]; exact (hdiag j).1
      · simp only [hs, ↓reduceIte]; exact (hdiag j).2
  change (chamberCut 0).Positive (tensorLaw (fun j => (D j).QE (ε j)) -
    (tensorLaw (fun j => (D j).compF 1) + tensorLaw (fun j => (D j).compF 2)))
  rw [hQE, hexp]
  change (chamberCut 0).Positive (∑ s, T s - _)
  rw [hsum, hT0, hT1]
  have he : tensorLaw (fun j => (D j).QE0 (ε j)) + (tensorLaw (fun j => (D j).QE1 (ε j)) +
      ∑ s ∈ (Finset.univ.erase c0).erase c1, T s) -
      (tensorLaw (fun j => (D j).compF 1) + tensorLaw (fun j => (D j).compF 2)) =
      (tensorLaw (fun j => (D j).QE0 (ε j)) + tensorLaw (fun j => (D j).QE1 (ε j)) -
        (tensorLaw (fun j => (D j).compF 1) + tensorLaw (fun j => (D j).compF 2))) +
      ∑ s ∈ (Finset.univ.erase c0).erase c1, T s := by
    abel
  rw [he]
  exact hfirst.add hrest

/-- **`lem:tr:polarization`(d), last claim**: `⊗_𝔅 𝒬^E_𝔅 ± ⊗_𝔅 𝒬^F_𝔅 ⪰_{ϑ₀} 0` for both signs,
with `𝒬^E = Π_{E_0} + Π_{E_1} + ε(Π_{G_e} + Π_{G_o})` and `𝒬^F = Π_{F_1} + Π_{F_2}`. -/
theorem polarization_d_blocks (D : ∀ j, Datum (X j)) (eF eE ε : J → ℝ)
    (hF : ∀ j b, (D j).nu.weight b ≠ 0 → NormBound ((D j).nub b) ((D j).TF b) (eF j))
    (hE : ∀ j b, (D j).nu.weight b ≠ 0 → NormBound ((D j).nub b) ((D j).TE b) (eE j))
    (hε : ∀ j, eF j + eE j ≤ ε j) :
    (chamberCut 0).Positive (tensorLaw (fun j => (D j).QE (ε j)) - tensorLaw (fun j => (D j).QF)) ∧
    (chamberCut 0).Positive (tensorLaw (fun j => (D j).QE (ε j)) + tensorLaw (fun j => (D j).QF)) :=
  Structured.tensor_two_sign_positive (chamberCut 0) (fun j => (D j).QE (ε j)) (fun j => (D j).QF)
    (fun j => by
      have h := ((D j).polarization_b (hF j) (hE j) (hε j)).2
      change (chamberCut 0).Positive ((D j).QE (ε j) - -(D j).QF) at h
      rwa [sub_neg_eq_add] at h)
    (fun j => ((D j).polarization_b (hF j) (hE j) (hε j)).1)

end Blocks

end Sarkozy.FiveType
