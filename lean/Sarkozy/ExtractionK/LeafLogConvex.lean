module

public import Sarkozy.ExtractionK.Leaf
public import Sarkozy.ExtractionK.LogConvex

@[expose] public section

/-!
# Log-convexity of the leaf coefficients (`lem:logconvex-coefficients` for `cor:extraction-leaf`(b))

`paper/sections/16_extraction.tex`, `lem:logconvex-coefficients`, applied to the coefficients
`C_k(q)` of `cor:extraction-leaf`(b) as formalized in `Leaf.lean` (`leafCoef`, summed over the
classes of witness size `k`: `leafCk`). `LogConvex.lean` proves the lemma for abstract data
(`LcData`); this file builds those data from a partition `𝔓` with records `rec`
(`leafLcData`) and identifies its coefficient with `leafCk`:

* `llVerts`: the `2(n - k)` non-witness vertices of a record, tagged by their set (`U_x`, `C_z`,
  `U_z`, `C_x`), `prod_llVerts`, `card_llVerts`; `llS`, `llN`, `llSc`: the count `s_v`, the `n'`
  of its count error (`n` or `2n`) and the constant `𝖲_m(s_v)` or `𝖲_ρ(s_v)` of a tagged vertex.
* `leafLcData`: the data, with the numerators `1 + e_{s_v}(P, n') + r² 2^{s_v} 𝖲(s_v)` in the form
  `1 + a r + b r²` (`lc_numerator_exp`), the errors `e_{d⁰_i}(P, n)` of `R_full` and
  `ê = e_{Δ⁺}(P, n)`.
* `leafLcData_Ck`: `LcData.Ck k (log q) = leafCk … k q` (when `ê(q) < 1`); `leafLcData_M`:
  `LcData.M (log q) = leafM q = R_full(q)² (1 - ê(q))^{-n}`; `leafLcData_valid`: the data are
  valid when every class has a valid record (`LeafRecordData.Valid`).
* **`logconvex_coefficients_leaf`**: the interpolation of the lemma for these coefficients,
  `C_k(Q) ≤ M(Q)(c₀/M(P₀))^{1-θ}(c₁/M(P₁))^θ ≤ c₀^{1-θ} c₁^θ`; `leafCk_antitone`: `C_k` is
  nonincreasing in `q ≥ P₀` when (S1) holds at `P₀`. The factorization `C_k = M D_k` and the
  log-convexity are `LcData.Ck_eq`, `LcData.logConvex_Ck` applied to `leafLcData`.

The error pair is the coarse one (`e_t(p, n')`), as everywhere in `ExtractionK/`.
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

section Bridge

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The `2(n - k)` non-witness vertices of a record, tagged by their set: `0` for `U_x`, `1` for
`C_z`, `2` for `U_z`, `3` for `C_x`. -/
def llVerts (R : LeafRecordData U) : Finset (Fin 4 × U) :=
  (({0} : Finset (Fin 4)) ×ˢ (univ \ (witV R.w ∪ R.Cx)) ∪ ({1} : Finset (Fin 4)) ×ˢ R.Cz) ∪
    (({2} : Finset (Fin 4)) ×ˢ (univ \ (witW R.w ∪ R.Cz)) ∪ ({3} : Finset (Fin 4)) ×ˢ R.Cx)

/-- The count `s_v` of a tagged non-witness vertex of a record of a class with free pairs `Fr`
(the transposed record's counts on `U_z` and `C_x`). -/
noncomputable def llS (G : OrientedGraph U) (Fr : Finset (U × U)) (R : LeafRecordData U)
    (v : Fin 4 × U) : ℕ :=
  if v.1 = 0 then intS G R.ordX Fr v.2
  else if v.1 = 1 then coverRowS G R.Cz R.ordZ (Fr.filter (fun e => e.2 ∈ R.Cz)) v.2
  else if v.1 = 2 then intS G R.ordZ (Fr.image Prod.swap) v.2
  else coverRowS G R.Cx R.ordX ((Fr.image Prod.swap).filter (fun e => e.2 ∈ R.Cx)) v.2

/-- `n'` of the count error of a tagged vertex: `n` for integrated vertices, `2n` for cover
vertices. -/
noncomputable def llN (n : ℕ) (v : Fin 4 × U) : ℝ := if v.1 = 1 ∨ v.1 = 3 then 2 * n else n

/-- The special constant `𝖲_m(s)` (integrated vertices) or `𝖲_ρ(s)` (cover vertices). -/
noncomputable def llSc (G : OrientedGraph U) (ς : U → U → ℤ) (v : Fin 4 × U) (s : ℕ) : ℝ :=
  if v.1 = 1 ∨ v.1 = 3 then leafS G ς (weightRho G ς) s else leafS G ς (weightM G ς) s

/-- The data of the nonstar coefficients `C_k` of `cor:extraction-leaf`(b) for a partition `𝔓`
with records `rec`, in the form of `lem:logconvex-coefficients` (`LcData`). -/
noncomputable def leafLcData (G : OrientedGraph U) (ς : U → U → ℤ) (n : ℕ)
    (Ex : Finset (U × U)) (𝔓 : Finset (Finset (U × U) × Finset (U × U)))
    (rec : Finset (U × U) × Finset (U × U) → LeafRecordData U) :
    LcData (Finset (U × U) × Finset (U × U)) (Fin 4 × U) U where
  cls := 𝔓
  ex c := recordExp G (Ex \ (c.1 ∪ c.2)) (witV (rec c).w) (witW (rec c).w) (rec c).ordX
    (rec c).ordZ + 2 * twoCycleCount (witnessIdx c.1 (rec c).w)
  wk c := (rec c).k
  verts c := llVerts (rec c)
  numA c v := 2 ^ llS G (Ex \ (c.1 ∪ c.2)) (rec c) v * coarseH (llS G (Ex \ (c.1 ∪ c.2)) (rec c) v)
  numB c v := 2 ^ llS G (Ex \ (c.1 ∪ c.2)) (rec c) v * llN n v +
    2 ^ llS G (Ex \ (c.1 ∪ c.2)) (rec c) v * llSc G ς v (llS G (Ex \ (c.1 ∪ c.2)) (rec c) v)
  degs := univ
  errA i := 2 ^ rowsDeg0 G i * coarseH (rowsDeg0 G i)
  errB i := 2 ^ rowsDeg0 G i * n
  hatA := 2 ^ (univ.sup (rowsDeg0 G)) * coarseH (univ.sup (rowsDeg0 G))
  hatB := 2 ^ (univ.sup (rowsDeg0 G)) * n
  n := Fintype.card U

/-- The coefficient `C_k(q)` of `cor:extraction-leaf`(b): the sum of the class coefficients
`leafCoef` over the classes of witness size `k`. -/
noncomputable def leafCk (G : OrientedGraph U) (ς : U → U → ℤ) (n : ℕ) (Ex : Finset (U × U))
    (𝔓 : Finset (Finset (U × U) × Finset (U × U)))
    (rec : Finset (U × U) × Finset (U × U) → LeafRecordData U) (k : ℕ) (q : ℝ) : ℝ :=
  ∑ c ∈ 𝔓.filter (fun c => (rec c).k = k), leafCoef G ς q n Ex c (rec c)

theorem lcPoly_log_eq_coarseError (t : ℕ) (n' : ℝ) {Q : ℝ} (hQ : 0 < Q) :
    lcPoly (2 ^ t * coarseH t) (2 ^ t * n') (Real.log Q) = coarseError t Q n' := by
  rw [← lc_coarseError_exp, Real.exp_log hQ]


theorem leafLcData_Rfull (G : OrientedGraph U) (ς : U → U → ℤ) (n : ℕ) (Ex : Finset (U × U))
    (𝔓 : Finset (Finset (U × U) × Finset (U × U)))
    (rec : Finset (U × U) × Finset (U × U) → LeafRecordData U) {Q : ℝ} (hQ : 0 < Q) :
    (leafLcData G ς n Ex 𝔓 rec).Rfull (Real.log Q) = rowsR G Q n univ := by
  unfold LcData.Rfull LcData.err rowsR
  refine prod_congr rfl fun i _ => ?_
  simp only [leafLcData]
  rw [lcPoly_log_eq_coarseError _ _ hQ]

theorem leafLcData_ehat (G : OrientedGraph U) (ς : U → U → ℤ) (n : ℕ) (Ex : Finset (U × U))
    (𝔓 : Finset (Finset (U × U) × Finset (U × U)))
    (rec : Finset (U × U) × Finset (U × U) → LeafRecordData U) {Q : ℝ} (hQ : 0 < Q) :
    (leafLcData G ς n Ex 𝔓 rec).ehat (Real.log Q) = leafEhat G Q n := by
  unfold LcData.ehat leafEhat
  simp only [leafLcData]
  rw [lcPoly_log_eq_coarseError _ _ hQ]

theorem leafLcData_num (G : OrientedGraph U) (ς : U → U → ℤ) (n : ℕ) (Ex : Finset (U × U))
    (𝔓 : Finset (Finset (U × U) × Finset (U × U)))
    (rec : Finset (U × U) × Finset (U × U) → LeafRecordData U) {Q : ℝ} (hQ : 0 < Q)
    (c : Finset (U × U) × Finset (U × U)) (v : Fin 4 × U) :
    (leafLcData G ς n Ex 𝔓 rec).num c v (Real.log Q) =
      1 + coarseError (llS G (Ex \ (c.1 ∪ c.2)) (rec c) v) Q (llN n v) +
        (Real.sqrt Q)⁻¹ ^ 2 * 2 ^ llS G (Ex \ (c.1 ∪ c.2)) (rec c) v *
          llSc G ς v (llS G (Ex \ (c.1 ∪ c.2)) (rec c) v) := by
  unfold LcData.num
  simp only [leafLcData]
  have h := lc_numerator_exp (llS G (Ex \ (c.1 ∪ c.2)) (rec c) v) (llN n v)
    (llSc G ς v (llS G (Ex \ (c.1 ∪ c.2)) (rec c) v)) (Real.log Q)
  rw [Real.exp_log hQ] at h
  rw [h]

omit [Fintype U] [DecidableEq U] in
theorem prod_tag (a : Fin 4) (S : Finset U) (g : Fin 4 × U → ℝ) :
    ∏ v ∈ ({a} : Finset (Fin 4)) ×ˢ S, g v = ∏ x ∈ S, g (a, x) := by
  rw [prod_product, prod_singleton]

omit [Fintype U] [DecidableEq U] in
theorem disjoint_tag {a b : Fin 4} (hab : a ≠ b) (S T : Finset U) :
    Disjoint (({a} : Finset (Fin 4)) ×ˢ S) (({b} : Finset (Fin 4)) ×ˢ T) := by
  rw [disjoint_left]
  intro v hv hv'
  rw [mem_product, mem_singleton] at hv hv'
  exact hab (hv.1.symm.trans hv'.1)

theorem prod_llVerts (R : LeafRecordData U) (g : Fin 4 × U → ℝ) :
    ∏ v ∈ llVerts R, g v = (∏ u ∈ univ \ (witV R.w ∪ R.Cx), g (0, u)) * (∏ b ∈ R.Cz, g (1, b)) *
      (∏ u ∈ univ \ (witW R.w ∪ R.Cz), g (2, u)) * ∏ b ∈ R.Cx, g (3, b) := by
  unfold llVerts
  have d01 := disjoint_tag (by decide : (0 : Fin 4) ≠ 1) (univ \ (witV R.w ∪ R.Cx)) R.Cz
  have d23 := disjoint_tag (by decide : (2 : Fin 4) ≠ 3) (univ \ (witW R.w ∪ R.Cz)) R.Cx
  have d : Disjoint (({0} : Finset (Fin 4)) ×ˢ (univ \ (witV R.w ∪ R.Cx)) ∪
      ({1} : Finset (Fin 4)) ×ˢ R.Cz)
      (({2} : Finset (Fin 4)) ×ˢ (univ \ (witW R.w ∪ R.Cz)) ∪ ({3} : Finset (Fin 4)) ×ˢ R.Cx) := by
    rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
    exact ⟨⟨disjoint_tag (by decide) _ _, disjoint_tag (by decide) _ _⟩,
      ⟨disjoint_tag (by decide) _ _, disjoint_tag (by decide) _ _⟩⟩
  rw [prod_union d, prod_union d01, prod_union d23, prod_tag, prod_tag, prod_tag, prod_tag]
  ring

theorem card_llVerts (R : LeafRecordData U) (hk1 : (witV R.w).card = R.k)
    (hk2 : (witW R.w).card = R.k) (hVC : Disjoint (witV R.w) R.Cx)
    (hWC : Disjoint (witW R.w) R.Cz) :
    (llVerts R).card = 2 * (Fintype.card U - R.k) := by
  unfold llVerts
  have d01 := disjoint_tag (by decide : (0 : Fin 4) ≠ 1) (univ \ (witV R.w ∪ R.Cx)) R.Cz
  have d23 := disjoint_tag (by decide : (2 : Fin 4) ≠ 3) (univ \ (witW R.w ∪ R.Cz)) R.Cx
  have d : Disjoint (({0} : Finset (Fin 4)) ×ˢ (univ \ (witV R.w ∪ R.Cx)) ∪
      ({1} : Finset (Fin 4)) ×ˢ R.Cz)
      (({2} : Finset (Fin 4)) ×ˢ (univ \ (witW R.w ∪ R.Cz)) ∪ ({3} : Finset (Fin 4)) ×ˢ R.Cx) := by
    rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
    exact ⟨⟨disjoint_tag (by decide) _ _, disjoint_tag (by decide) _ _⟩,
      ⟨disjoint_tag (by decide) _ _, disjoint_tag (by decide) _ _⟩⟩
  rw [card_union_of_disjoint d, card_union_of_disjoint d01, card_union_of_disjoint d23,
    card_product, card_product, card_product, card_product, card_singleton, card_singleton,
    card_singleton, card_singleton, card_sdiff_of_subset (subset_univ _),
    card_sdiff_of_subset (subset_univ _), card_union_of_disjoint hVC,
    card_union_of_disjoint hWC, card_univ, hk1, hk2]
  have h1 : R.k + R.Cx.card ≤ Fintype.card U := by
    rw [← hk1, ← card_union_of_disjoint hVC]
    exact card_le_univ _
  have h2 : R.k + R.Cz.card ≤ Fintype.card U := by
    rw [← hk2, ← card_union_of_disjoint hWC]
    exact card_le_univ _
  omega

theorem llNum_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) (n : ℕ) (Fr : Finset (U × U))
    (R : LeafRecordData U) {Q : ℝ} (v : Fin 4 × U) :
    0 ≤ 1 + coarseError (llS G Fr R v) Q (llN n v) +
      (Real.sqrt Q)⁻¹ ^ 2 * 2 ^ llS G Fr R v * llSc G ς v (llS G Fr R v) := by
  have hN : 0 ≤ llN n v := by
    unfold llN
    split_ifs <;> positivity
  have he := coarseError_nonneg (q := Q) hN (llS G Fr R v)
  have hS : 0 ≤ llSc G ς v (llS G Fr R v) := by
    unfold llSc
    split_ifs
    · exact leafS_nonneg G ς _ (weightRho_nonneg G ς) _
    · exact leafS_nonneg G ς _ (weightM_nonneg G ς) _
  have : 0 ≤ (Real.sqrt Q)⁻¹ ^ 2 * 2 ^ llS G Fr R v * llSc G ς v (llS G Fr R v) :=
    mul_nonneg (by positivity) hS
  linarith

/-- The class terms: `LcData.Ck` of `leafLcData` at `u = log q` is `C_k(q)` of
`cor:extraction-leaf`(b). -/
theorem leafLcData_Ck (G : OrientedGraph U) (ς : U → U → ℤ) (n : ℕ) (Ex : Finset (U × U))
    (𝔓 : Finset (Finset (U × U) × Finset (U × U)))
    (rec : Finset (U × U) × Finset (U × U) → LeafRecordData U) (k : ℕ) {Q : ℝ} (hQ : 0 < Q)
    (hS1 : leafEhat G Q n < 1) :
    (leafLcData G ς n Ex 𝔓 rec).Ck k (Real.log Q) = leafCk G ς n Ex 𝔓 rec k Q := by
  unfold LcData.Ck leafCk
  refine sum_congr rfl fun c hc => ?_
  have hk : (rec c).k = k := (mem_filter.mp hc).2
  rw [leafLcData_Rfull G ς n Ex 𝔓 rec hQ, leafLcData_ehat G ς n Ex 𝔓 rec hQ]
  have h1e : 0 < 1 - leafEhat G Q n := by linarith
  have hfac : ∀ v, (leafLcData G ς n Ex 𝔓 rec).num c v (Real.log Q) / (1 - leafEhat G Q n) =
      (1 + coarseError (llS G (Ex \ (c.1 ∪ c.2)) (rec c) v) Q (llN n v) +
        (Real.sqrt Q)⁻¹ ^ 2 * 2 ^ llS G (Ex \ (c.1 ∪ c.2)) (rec c) v *
          llSc G ς v (llS G (Ex \ (c.1 ∪ c.2)) (rec c) v)) / (1 - leafEhat G Q n) := by
    intro v
    rw [leafLcData_num G ς n Ex 𝔓 rec hQ c v]
  have hnn : ∀ v ∈ (leafLcData G ς n Ex 𝔓 rec).verts c,
      0 ≤ (leafLcData G ς n Ex 𝔓 rec).num c v (Real.log Q) / (1 - leafEhat G Q n) := by
    intro v _
    rw [hfac v]
    exact div_nonneg (llNum_nonneg G ς n (Ex \ (c.1 ∪ c.2)) (rec c) v) h1e.le
  rw [← Real.sqrt_prod _ hnn]
  have hprod : ∏ v ∈ (leafLcData G ς n Ex 𝔓 rec).verts c,
      (leafLcData G ς n Ex 𝔓 rec).num c v (Real.log Q) / (1 - leafEhat G Q n) =
      leafProd G ς Q n (leafEhat G Q n) (Ex \ (c.1 ∪ c.2)) (witV (rec c).w) (witW (rec c).w)
        (rec c).Cx (rec c).Cz (rec c).ordX (rec c).ordZ := by
    simp only [hfac]
    change ∏ v ∈ llVerts (rec c), _ = _
    rw [prod_llVerts]
    unfold leafProd leafProdOf leafFm leafFrho
    simp only [llS, llN, llSc]
    norm_num
  rw [hprod]
  have hex : (2 : ℝ) ^ (((leafLcData G ς n Ex 𝔓 rec).ex c : ℕ) / (2 : ℝ)) =
      Real.sqrt (2 ^ (leafLcData G ς n Ex 𝔓 rec).ex c) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  rw [hex]
  unfold leafCoef
  have hpow : (1 - leafEhat G Q n) ^ (rec c).k = (1 - leafEhat G Q n) ^ k := by rw [hk]
  rw [Real.sqrt_mul (by positivity), hpow]
  simp only [leafLcData]
  ring

/-- The data are valid (`LcData.Valid`) when every class of `𝔓` carries a valid record. -/
theorem leafLcData_valid (G : OrientedGraph U) (ς : U → U → ℤ) (n : ℕ) (Ex : Finset (U × U))
    (𝔓 : Finset (Finset (U × U) × Finset (U × U)))
    (rec : Finset (U × U) × Finset (U × U) → LeafRecordData U)
    (hrec : ∀ c ∈ 𝔓, (rec c).Valid Ex c) : (leafLcData G ς n Ex 𝔓 rec).Valid where
  numA_nonneg c v := mul_nonneg (by positivity) (lc_coarseH_nonneg _)
  numB_nonneg c v := by
    have hN : 0 ≤ llN n v := by
      unfold llN
      split_ifs <;> positivity
    have hS : 0 ≤ llSc G ς v (llS G (Ex \ (c.1 ∪ c.2)) (rec c) v) := by
      unfold llSc
      split_ifs
      · exact leafS_nonneg G ς _ (weightRho_nonneg G ς) _
      · exact leafS_nonneg G ς _ (weightM_nonneg G ς) _
    exact add_nonneg (mul_nonneg (by positivity) hN) (mul_nonneg (by positivity) hS)
  errA_nonneg i := mul_nonneg (by positivity) (lc_coarseH_nonneg _)
  errB_nonneg i := mul_nonneg (by positivity) (Nat.cast_nonneg n)
  hatA_nonneg := mul_nonneg (by positivity) (lc_coarseH_nonneg _)
  hatB_nonneg := mul_nonneg (by positivity) (Nat.cast_nonneg n)
  wk_le c hc := by
    have h := Fintype.card_le_of_injective _ (hrec c hc).witness.injective_fst
    show (rec c).k ≤ Fintype.card U
    simpa using h
  card_verts c hc := by
    have hv := hrec c hc
    have hk1 : (witV (rec c).w).card = (rec c).k := by
      unfold witV
      rw [card_image_of_injective _ hv.witness.injective_fst, card_univ, Fintype.card_fin]
    have hk2 : (witW (rec c).w).card = (rec c).k := by
      unfold witW
      rw [card_image_of_injective _ hv.witness.injective_snd, card_univ, Fintype.card_fin]
    have hVC : Disjoint (witV (rec c).w) (rec c).Cx := by
      rw [disjoint_left]
      intro u hu
      obtain ⟨i, -, rfl⟩ := mem_image.mp hu
      exact hv.cover.fst_not_mem i
    have hWC : Disjoint (witW (rec c).w) (rec c).Cz := by
      rw [disjoint_left]
      intro u hu
      obtain ⟨i, -, rfl⟩ := mem_image.mp hu
      exact hv.cover.snd_not_mem i
    exact card_llVerts (rec c) hk1 hk2 hVC hWC

/-- (S1) at `q` (`ê(q) < 1`) puts `log q` in the range of `LcData`. -/
theorem leafLcData_inRange (G : OrientedGraph U) (ς : U → U → ℤ) (n : ℕ) (Ex : Finset (U × U))
    (𝔓 : Finset (Finset (U × U) × Finset (U × U)))
    (rec : Finset (U × U) × Finset (U × U) → LeafRecordData U) {Q : ℝ} (hQ : 0 < Q)
    (hS1 : leafEhat G Q n < 1) : (leafLcData G ς n Ex 𝔓 rec).InRange (Real.log Q) := by
  refine ⟨by rw [leafLcData_ehat G ς n Ex 𝔓 rec hQ]; exact hS1, fun i _ => ?_⟩
  unfold LcData.err
  simp only [leafLcData]
  rw [lcPoly_log_eq_coarseError _ _ hQ]
  exact lt_of_le_of_lt (coarseError_le_leafEhat G Q n i) hS1

/-- `M(q) = R_full(q)² (1 - ê(q))^{-n}`, `n = |U⁺|` (`lem:logconvex-coefficients`). -/
noncomputable def leafM (G : OrientedGraph U) (n : ℕ) (q : ℝ) : ℝ :=
  rowsR G q n univ ^ 2 * ((1 - leafEhat G q n) ^ Fintype.card U)⁻¹

theorem leafLcData_M (G : OrientedGraph U) (ς : U → U → ℤ) (n : ℕ) (Ex : Finset (U × U))
    (𝔓 : Finset (Finset (U × U) × Finset (U × U)))
    (rec : Finset (U × U) × Finset (U × U) → LeafRecordData U) {Q : ℝ} (hQ : 0 < Q) :
    (leafLcData G ς n Ex 𝔓 rec).M (Real.log Q) = leafM G n Q := by
  unfold LcData.M leafM
  rw [leafLcData_Rfull G ς n Ex 𝔓 rec hQ, leafLcData_ehat G ς n Ex 𝔓 rec hQ]
  rfl

/-- **`lem:logconvex-coefficients` for the coefficients of `cor:extraction-leaf`(b).** For a
partition `𝔓` with valid records (`LeafRecordData.Valid`), the coarse error pair, (S1) at `P₀`
(`ê(P₀) < 1`), `P₀ ≤ Q ≤ P₁`, `P₀ < P₁`, `θ = log(Q/P₀)/log(P₁/P₀)` and `c_i ≥ C_k(P_i)`:
`C_k(Q) ≤ M(Q)(c₀/M(P₀))^{1-θ}(c₁/M(P₁))^θ ≤ c₀^{1-θ} c₁^θ`, with `C_k = leafCk` the sum of the
class coefficients `leafCoef` of witness size `k` and `M = leafM`. -/
theorem logconvex_coefficients_leaf (G : OrientedGraph U) (ς : U → U → ℤ) (n : ℕ)
    (Ex : Finset (U × U)) (𝔓 : Finset (Finset (U × U) × Finset (U × U)))
    (rec : Finset (U × U) × Finset (U × U) → LeafRecordData U)
    (hrec : ∀ c ∈ 𝔓, (rec c).Valid Ex c) (k : ℕ) {P₀ P₁ Q θ c₀ c₁ : ℝ} (hP₀ : 0 < P₀)
    (hP01 : P₀ < P₁) (hQ0 : P₀ ≤ Q) (hQ1 : Q ≤ P₁)
    (hθ : θ = Real.log (Q / P₀) / Real.log (P₁ / P₀)) (hS1 : leafEhat G P₀ n < 1)
    (hc₀ : leafCk G ς n Ex 𝔓 rec k P₀ ≤ c₀) (hc₁ : leafCk G ς n Ex 𝔓 rec k P₁ ≤ c₁) :
    leafCk G ς n Ex 𝔓 rec k Q ≤
        leafM G n Q * (c₀ / leafM G n P₀) ^ (1 - θ) * (c₁ / leafM G n P₁) ^ θ ∧
      leafM G n Q * (c₀ / leafM G n P₀) ^ (1 - θ) * (c₁ / leafM G n P₁) ^ θ ≤
        c₀ ^ (1 - θ) * c₁ ^ θ := by
  have hQ : 0 < Q := lt_of_lt_of_le hP₀ hQ0
  have hP₁ : 0 < P₁ := lt_trans hP₀ hP01
  have hS1Q : leafEhat G Q n < 1 := lt_of_le_of_lt (leafEhat_anti G hP₀ hQ0) hS1
  have hS11 : leafEhat G P₁ n < 1 := lt_of_le_of_lt (leafEhat_anti G hP₀ hP01.le) hS1
  have hD := leafLcData_valid G ς n Ex 𝔓 rec hrec
  have h := LcData.logconvex_coefficients (c₀ := c₀) (c₁ := c₁) hD k hP₀ hP01 hQ0 hQ1 hθ
    (leafLcData_inRange G ς n Ex 𝔓 rec hP₀ hS1)
    (by rw [leafLcData_Ck G ς n Ex 𝔓 rec k hP₀ hS1]; exact hc₀)
    (by rw [leafLcData_Ck G ς n Ex 𝔓 rec k hP₁ hS11]; exact hc₁)
  rw [leafLcData_Ck G ς n Ex 𝔓 rec k hQ hS1Q, leafLcData_M G ς n Ex 𝔓 rec hQ,
    leafLcData_M G ς n Ex 𝔓 rec hP₀, leafLcData_M G ς n Ex 𝔓 rec hP₁] at h
  exact h

/-- **`lem:logconvex-coefficients`, factorization and monotonicity**, for the coefficients of
`cor:extraction-leaf`(b): `C_k = M D_k` (`LcData.Ck_eq`) and `C_k(q') ≤ C_k(q)` for
`P₀ ≤ q ≤ q'` when (S1) holds at `P₀`. -/
theorem leafCk_antitone (G : OrientedGraph U) (ς : U → U → ℤ) (n : ℕ)
    (Ex : Finset (U × U)) (𝔓 : Finset (Finset (U × U) × Finset (U × U)))
    (rec : Finset (U × U) × Finset (U × U) → LeafRecordData U)
    (hrec : ∀ c ∈ 𝔓, (rec c).Valid Ex c) (k : ℕ) {P₀ q q' : ℝ} (hP₀ : 0 < P₀)
    (hS1 : leafEhat G P₀ n < 1) (h0 : P₀ ≤ q) (h1 : q ≤ q') :
    leafCk G ς n Ex 𝔓 rec k q' ≤ leafCk G ς n Ex 𝔓 rec k q := by
  have hq : 0 < q := lt_of_lt_of_le hP₀ h0
  have hq' : 0 < q' := lt_of_lt_of_le hq h1
  have hD := leafLcData_valid G ς n Ex 𝔓 rec hrec
  have h := LcData.Ck_antitone_P hD k hP₀ (leafLcData_inRange G ς n Ex 𝔓 rec hP₀ hS1) h0 h1
  rwa [leafLcData_Ck G ς n Ex 𝔓 rec k hq' (lt_of_le_of_lt (leafEhat_anti G hP₀ (h0.trans h1))
    hS1), leafLcData_Ck G ς n Ex 𝔓 rec k hq (lt_of_le_of_lt (leafEhat_anti G hP₀ h0) hS1)] at h

end Bridge

end Sarkozy.ExtractionK
