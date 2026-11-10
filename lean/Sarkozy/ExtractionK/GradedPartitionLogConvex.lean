module

public import Sarkozy.ExtractionK.GradedPartition

@[expose] public section

/-!
# Graded errors, V: `lem:logconvex-coefficients` for the graded coefficients

`paper/sections/16_extraction.tex`, `lem:logconvex-coefficients` ("fix … one error pair of the
setting") for the graded pair (*Graded errors*, `def:graphs:error-pair`, `eq:graphs:graded`), the
pair used by the nonstar coefficients of the root cuts below `2^52`. As `LeafLogConvex.lean` does
for the coarse pair, this file builds the data `LcData` of `LogConvex.lean` from a partition with
records and identifies its coefficient with the graded `C_k(q)` of `GradedPartition.lean`:

* `gp_grGraded_exp`, `gp_lcPoly_log_eq`: `e^-_t(n') = lcPoly a_t (b_t + 2^t n')` in `u = log P`
  (`a_t = gradedA t`, `b_t = gradedB t`, both `≥ 0`).
* `gpLcData` (numerators `1 + a_s r + (b_s + 2^s n' + 2^s 𝖲(s)) r²`), `gpLcData_Ck`
  (`LcData.Ck k (log q) = gpLeafCk … k q`, the sum of the graded class coefficients
  `gpLeafCoef`), `gpLcData_M` (`gpM q = R_full(q)² (1 - ê(q))^{-n}`), `gpLcData_valid`,
  `gpLcData_inRange`.
* **`gp_logconvex_coefficients_leaf`**: `C_k(Q) ≤ M(Q)(c₀/M(P₀))^{1-θ}(c₁/M(P₁))^θ ≤ c₀^{1-θ}
  c₁^θ` for the graded coefficients; `gp_leafCk_antitone`: nonincreasing in `q ≥ P₀`. The
  factorization and the log-convexity are `LcData.Ck_eq`, `LcData.logConvex_Ck` for `gpLcData`.
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

section GpBridge

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The graded error at `P = e^u` in the form `a r + b r²` of `lem:logconvex-coefficients`:
`e^-_t(n') = lcPoly a_t (b_t + 2^t n') u`. -/
theorem gp_grGraded_exp (t : ℕ) (n' u : ℝ) :
    grGraded (Real.exp u) t n' = lcPoly (gradedA t) (gradedB t + 2 ^ t * n') u := by
  rw [gp_grGraded_eq (Real.exp_pos u)]
  unfold lcPoly
  have h1 : (Real.sqrt (Real.exp u))⁻¹ = Real.exp ((-1 / 2) * u) := by
    rw [← Real.exp_half, ← Real.exp_neg]
    congr 1
    ring
  rw [lc_rsq_exp, h1]

theorem gp_lcPoly_log_eq (t : ℕ) (n' : ℝ) {Q : ℝ} (hQ : 0 < Q) :
    lcPoly (gradedA t) (gradedB t + 2 ^ t * n') (Real.log Q) = grGraded Q t n' := by
  rw [← gp_grGraded_exp, Real.exp_log hQ]

/-- The data of `lem:logconvex-coefficients` (`LcData`) for the graded coefficients of
`cor:extraction-leaf`(b): the numerators `1 + e^-_{s_v}(P, n') + r² 2^{s_v} 𝖲(s_v)` are
`1 + a_s r + (b_s + 2^s n' + 2^s 𝖲) r²` (`gp_grGraded_eq`), the errors of `R_full` are
`e^-_{d⁰_i}(P, n)` and `ê = e^-_{Δ⁺}(P, n)`. -/
noncomputable def gpLcData (G : OrientedGraph U) (ς : U → U → ℤ) (n : ℕ)
    (Ex : Finset (U × U)) (𝔓 : Finset (Finset (U × U) × Finset (U × U)))
    (rec : Finset (U × U) × Finset (U × U) → LeafRecordData U) :
    LcData (Finset (U × U) × Finset (U × U)) (Fin 4 × U) U where
  cls := 𝔓
  ex c := recordExp G (Ex \ (c.1 ∪ c.2)) (witV (rec c).w) (witW (rec c).w) (rec c).ordX
    (rec c).ordZ + 2 * twoCycleCount (witnessIdx c.1 (rec c).w)
  wk c := (rec c).k
  verts c := llVerts (rec c)
  numA c v := gradedA (llS G (Ex \ (c.1 ∪ c.2)) (rec c) v)
  numB c v := gradedB (llS G (Ex \ (c.1 ∪ c.2)) (rec c) v) +
    2 ^ llS G (Ex \ (c.1 ∪ c.2)) (rec c) v * llN n v +
    2 ^ llS G (Ex \ (c.1 ∪ c.2)) (rec c) v * llSc G ς v (llS G (Ex \ (c.1 ∪ c.2)) (rec c) v)
  degs := univ
  errA i := gradedA (rowsDeg0 G i)
  errB i := gradedB (rowsDeg0 G i) + 2 ^ rowsDeg0 G i * n
  hatA := gradedA (univ.sup (rowsDeg0 G))
  hatB := gradedB (univ.sup (rowsDeg0 G)) + 2 ^ (univ.sup (rowsDeg0 G)) * n
  n := Fintype.card U

/-- The graded coefficient `C_k(q)` of `cor:extraction-leaf`(b): the sum of the graded class
coefficients `gpLeafCoef` over the classes of witness size `k`. -/
noncomputable def gpLeafCk (G : OrientedGraph U) (ς : U → U → ℤ) (n : ℕ) (Ex : Finset (U × U))
    (𝔓 : Finset (Finset (U × U) × Finset (U × U)))
    (rec : Finset (U × U) × Finset (U × U) → LeafRecordData U) (k : ℕ) (q : ℝ) : ℝ :=
  ∑ c ∈ 𝔓.filter (fun c => (rec c).k = k), gpLeafCoef G ς q n Ex c (rec c)

theorem gpLcData_Rfull (G : OrientedGraph U) (ς : U → U → ℤ) (n : ℕ) (Ex : Finset (U × U))
    (𝔓 : Finset (Finset (U × U) × Finset (U × U)))
    (rec : Finset (U × U) × Finset (U × U) → LeafRecordData U) {Q : ℝ} (hQ : 0 < Q) :
    (gpLcData G ς n Ex 𝔓 rec).Rfull (Real.log Q) = grRowsR G (grGraded Q) n univ := by
  unfold LcData.Rfull LcData.err grRowsR
  refine prod_congr rfl fun i _ => ?_
  simp only [gpLcData]
  rw [gp_lcPoly_log_eq _ _ hQ]

theorem gpLcData_ehat (G : OrientedGraph U) (ς : U → U → ℤ) (n : ℕ) (Ex : Finset (U × U))
    (𝔓 : Finset (Finset (U × U) × Finset (U × U)))
    (rec : Finset (U × U) × Finset (U × U) → LeafRecordData U) {Q : ℝ} (hQ : 0 < Q) :
    (gpLcData G ς n Ex 𝔓 rec).ehat (Real.log Q) = gpEhat G Q n := by
  unfold LcData.ehat gpEhat
  simp only [gpLcData]
  rw [gp_lcPoly_log_eq _ _ hQ]

theorem gpLcData_num (G : OrientedGraph U) (ς : U → U → ℤ) (n : ℕ) (Ex : Finset (U × U))
    (𝔓 : Finset (Finset (U × U) × Finset (U × U)))
    (rec : Finset (U × U) × Finset (U × U) → LeafRecordData U) {Q : ℝ} (hQ : 0 < Q)
    (c : Finset (U × U) × Finset (U × U)) (v : Fin 4 × U) :
    (gpLcData G ς n Ex 𝔓 rec).num c v (Real.log Q) =
      1 + grGraded Q (llS G (Ex \ (c.1 ∪ c.2)) (rec c) v) (llN n v) +
        (Real.sqrt Q)⁻¹ ^ 2 * 2 ^ llS G (Ex \ (c.1 ∪ c.2)) (rec c) v *
          llSc G ς v (llS G (Ex \ (c.1 ∪ c.2)) (rec c) v) := by
  unfold LcData.num
  simp only [gpLcData]
  rw [gp_grGraded_eq hQ]
  unfold lcPoly
  have h1 : Real.exp ((-1 / 2) * Real.log Q) = (Real.sqrt Q)⁻¹ := by
    calc Real.exp ((-1 / 2) * Real.log Q) = (Real.exp (Real.log Q / 2))⁻¹ := by
          rw [← Real.exp_neg]
          congr 1
          ring
      _ = (Real.sqrt (Real.exp (Real.log Q)))⁻¹ := by rw [Real.exp_half]
      _ = (Real.sqrt Q)⁻¹ := by rw [Real.exp_log hQ]
  have h2 : Real.exp ((-1) * Real.log Q) = (Real.sqrt Q)⁻¹ ^ 2 := by
    have := lc_rsq_exp (Real.log Q)
    rw [Real.exp_log hQ] at this
    exact this.symm
  rw [h1, h2]
  ring

theorem gp_llNum_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) (n : ℕ) (Fr : Finset (U × U))
    (R : LeafRecordData U) {Q : ℝ} (hQ : 0 < Q) (v : Fin 4 × U) :
    0 ≤ 1 + grGraded Q (llS G Fr R v) (llN n v) +
      (Real.sqrt Q)⁻¹ ^ 2 * 2 ^ llS G Fr R v * llSc G ς v (llS G Fr R v) := by
  have hN : 0 ≤ llN n v := by
    unfold llN
    split_ifs <;> positivity
  have he := gp_grGraded_nonneg hQ (llS G Fr R v) hN
  have hS : 0 ≤ llSc G ς v (llS G Fr R v) := by
    unfold llSc
    split_ifs
    · exact leafS_nonneg G ς _ (weightRho_nonneg G ς) _
    · exact leafS_nonneg G ς _ (weightM_nonneg G ς) _
  have : 0 ≤ (Real.sqrt Q)⁻¹ ^ 2 * 2 ^ llS G Fr R v * llSc G ς v (llS G Fr R v) :=
    mul_nonneg (by positivity) hS
  linarith

/-- The graded class terms: `LcData.Ck` of `gpLcData` at `u = log q` is the graded `C_k(q)`. -/
theorem gpLcData_Ck (G : OrientedGraph U) (ς : U → U → ℤ) (n : ℕ) (Ex : Finset (U × U))
    (𝔓 : Finset (Finset (U × U) × Finset (U × U)))
    (rec : Finset (U × U) × Finset (U × U) → LeafRecordData U) (k : ℕ) {Q : ℝ} (hQ : 0 < Q)
    (hS1 : gpEhat G Q n < 1) :
    (gpLcData G ς n Ex 𝔓 rec).Ck k (Real.log Q) = gpLeafCk G ς n Ex 𝔓 rec k Q := by
  unfold LcData.Ck gpLeafCk
  refine sum_congr rfl fun c hc => ?_
  have hk : (rec c).k = k := (mem_filter.mp hc).2
  rw [gpLcData_Rfull G ς n Ex 𝔓 rec hQ, gpLcData_ehat G ς n Ex 𝔓 rec hQ]
  have h1e : 0 < 1 - gpEhat G Q n := by linarith
  have hfac : ∀ v, (gpLcData G ς n Ex 𝔓 rec).num c v (Real.log Q) / (1 - gpEhat G Q n) =
      (1 + grGraded Q (llS G (Ex \ (c.1 ∪ c.2)) (rec c) v) (llN n v) +
        (Real.sqrt Q)⁻¹ ^ 2 * 2 ^ llS G (Ex \ (c.1 ∪ c.2)) (rec c) v *
          llSc G ς v (llS G (Ex \ (c.1 ∪ c.2)) (rec c) v)) / (1 - gpEhat G Q n) := by
    intro v
    rw [gpLcData_num G ς n Ex 𝔓 rec hQ c v]
  have hnn : ∀ v ∈ (gpLcData G ς n Ex 𝔓 rec).verts c,
      0 ≤ (gpLcData G ς n Ex 𝔓 rec).num c v (Real.log Q) / (1 - gpEhat G Q n) := by
    intro v _
    rw [hfac v]
    exact div_nonneg (gp_llNum_nonneg G ς n (Ex \ (c.1 ∪ c.2)) (rec c) hQ v) h1e.le
  rw [← Real.sqrt_prod _ hnn]
  have hprod : ∏ v ∈ (gpLcData G ς n Ex 𝔓 rec).verts c,
      (gpLcData G ς n Ex 𝔓 rec).num c v (Real.log Q) / (1 - gpEhat G Q n) =
      grLeafProd G ς (grGraded Q) Q n (gpEhat G Q n) (Ex \ (c.1 ∪ c.2)) (witV (rec c).w)
        (witW (rec c).w) (rec c).Cx (rec c).Cz (rec c).ordX (rec c).ordZ := by
    simp only [hfac]
    change ∏ v ∈ llVerts (rec c), _ = _
    rw [prod_llVerts]
    unfold grLeafProd grLeafProdOf grLeafFm grLeafFrho
    simp only [llS, llN, llSc]
    norm_num
  rw [hprod]
  have hex : (2 : ℝ) ^ (((gpLcData G ς n Ex 𝔓 rec).ex c : ℕ) / (2 : ℝ)) =
      Real.sqrt (2 ^ (gpLcData G ς n Ex 𝔓 rec).ex c) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  rw [hex]
  unfold gpLeafCoef
  have hpow : (1 - gpEhat G Q n) ^ (rec c).k = (1 - gpEhat G Q n) ^ k := by rw [hk]
  rw [Real.sqrt_mul (by positivity), hpow]
  simp only [gpLcData]
  ring

/-- The graded data are valid (`LcData.Valid`) when every class of `𝔓` has a valid record. -/
theorem gpLcData_valid (G : OrientedGraph U) (ς : U → U → ℤ) (n : ℕ) (Ex : Finset (U × U))
    (𝔓 : Finset (Finset (U × U) × Finset (U × U)))
    (rec : Finset (U × U) × Finset (U × U) → LeafRecordData U)
    (hrec : ∀ c ∈ 𝔓, (rec c).Valid Ex c) : (gpLcData G ς n Ex 𝔓 rec).Valid where
  numA_nonneg c v := gradedA_nonneg _
  numB_nonneg c v := by
    have hN : 0 ≤ llN n v := by
      unfold llN
      split_ifs <;> positivity
    have hS : 0 ≤ llSc G ς v (llS G (Ex \ (c.1 ∪ c.2)) (rec c) v) := by
      unfold llSc
      split_ifs
      · exact leafS_nonneg G ς _ (weightRho_nonneg G ς) _
      · exact leafS_nonneg G ς _ (weightM_nonneg G ς) _
    exact add_nonneg (add_nonneg (gradedB_nonneg _) (mul_nonneg (by positivity) hN))
      (mul_nonneg (by positivity) hS)
  errA_nonneg i := gradedA_nonneg _
  errB_nonneg i := add_nonneg (gradedB_nonneg _) (mul_nonneg (by positivity) (Nat.cast_nonneg n))
  hatA_nonneg := gradedA_nonneg _
  hatB_nonneg := add_nonneg (gradedB_nonneg _) (mul_nonneg (by positivity) (Nat.cast_nonneg n))
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

/-- (S1) at `q` with the graded pair (`e^-_{Δ⁺}(q, n) < 1`) puts `log q` in the range. -/
theorem gpLcData_inRange (G : OrientedGraph U) (ς : U → U → ℤ) (n : ℕ) (Ex : Finset (U × U))
    (𝔓 : Finset (Finset (U × U) × Finset (U × U)))
    (rec : Finset (U × U) × Finset (U × U) → LeafRecordData U) {Q : ℝ} (hQ : 0 < Q)
    (hS1 : gpEhat G Q n < 1) : (gpLcData G ς n Ex 𝔓 rec).InRange (Real.log Q) := by
  refine ⟨by rw [gpLcData_ehat G ς n Ex 𝔓 rec hQ]; exact hS1, fun i _ => ?_⟩
  unfold LcData.err
  simp only [gpLcData]
  rw [gp_lcPoly_log_eq _ _ hQ]
  exact lt_of_le_of_lt (grGraded_le_gpEhat G hQ n i) hS1

/-- `M(q) = R_full(q)² (1 - ê(q))^{-n}` with the graded pair. -/
noncomputable def gpM (G : OrientedGraph U) (n : ℕ) (q : ℝ) : ℝ :=
  grRowsR G (grGraded q) n univ ^ 2 * ((1 - gpEhat G q n) ^ Fintype.card U)⁻¹

theorem gpLcData_M (G : OrientedGraph U) (ς : U → U → ℤ) (n : ℕ) (Ex : Finset (U × U))
    (𝔓 : Finset (Finset (U × U) × Finset (U × U)))
    (rec : Finset (U × U) × Finset (U × U) → LeafRecordData U) {Q : ℝ} (hQ : 0 < Q) :
    (gpLcData G ς n Ex 𝔓 rec).M (Real.log Q) = gpM G n Q := by
  unfold LcData.M gpM
  rw [gpLcData_Rfull G ς n Ex 𝔓 rec hQ, gpLcData_ehat G ς n Ex 𝔓 rec hQ]
  rfl

/-- **`lem:logconvex-coefficients` for the graded coefficients of `cor:extraction-leaf`(b)**
(*Graded errors*): for a partition `𝔓` with valid records, the graded pair, (S1) at `P₀`
(`e^-_{Δ⁺}(P₀, n) < 1`), `P₀ ≤ Q ≤ P₁`, `P₀ < P₁`, `θ = log(Q/P₀)/log(P₁/P₀)` and `c_i ≥ C_k(P_i)`:
`C_k(Q) ≤ M(Q)(c₀/M(P₀))^{1-θ}(c₁/M(P₁))^θ ≤ c₀^{1-θ} c₁^θ` (`C_k = gpLeafCk`, `M = gpM`). -/
theorem gp_logconvex_coefficients_leaf (G : OrientedGraph U) (ς : U → U → ℤ) (n : ℕ)
    (Ex : Finset (U × U)) (𝔓 : Finset (Finset (U × U) × Finset (U × U)))
    (rec : Finset (U × U) × Finset (U × U) → LeafRecordData U)
    (hrec : ∀ c ∈ 𝔓, (rec c).Valid Ex c) (k : ℕ) {P₀ P₁ Q θ c₀ c₁ : ℝ} (hP₀ : 0 < P₀)
    (hP01 : P₀ < P₁) (hQ0 : P₀ ≤ Q) (hQ1 : Q ≤ P₁)
    (hθ : θ = Real.log (Q / P₀) / Real.log (P₁ / P₀)) (hS1 : gpEhat G P₀ n < 1)
    (hc₀ : gpLeafCk G ς n Ex 𝔓 rec k P₀ ≤ c₀) (hc₁ : gpLeafCk G ς n Ex 𝔓 rec k P₁ ≤ c₁) :
    gpLeafCk G ς n Ex 𝔓 rec k Q ≤
        gpM G n Q * (c₀ / gpM G n P₀) ^ (1 - θ) * (c₁ / gpM G n P₁) ^ θ ∧
      gpM G n Q * (c₀ / gpM G n P₀) ^ (1 - θ) * (c₁ / gpM G n P₁) ^ θ ≤
        c₀ ^ (1 - θ) * c₁ ^ θ := by
  have hQ : 0 < Q := lt_of_lt_of_le hP₀ hQ0
  have hP₁ : 0 < P₁ := lt_trans hP₀ hP01
  have hS1Q : gpEhat G Q n < 1 := lt_of_le_of_lt (gpEhat_anti G n hP₀ hQ0) hS1
  have hS11 : gpEhat G P₁ n < 1 := lt_of_le_of_lt (gpEhat_anti G n hP₀ hP01.le) hS1
  have hD := gpLcData_valid G ς n Ex 𝔓 rec hrec
  have h := LcData.logconvex_coefficients (c₀ := c₀) (c₁ := c₁) hD k hP₀ hP01 hQ0 hQ1 hθ
    (gpLcData_inRange G ς n Ex 𝔓 rec hP₀ hS1)
    (by rw [gpLcData_Ck G ς n Ex 𝔓 rec k hP₀ hS1]; exact hc₀)
    (by rw [gpLcData_Ck G ς n Ex 𝔓 rec k hP₁ hS11]; exact hc₁)
  rw [gpLcData_Ck G ς n Ex 𝔓 rec k hQ hS1Q, gpLcData_M G ς n Ex 𝔓 rec hQ,
    gpLcData_M G ς n Ex 𝔓 rec hP₀, gpLcData_M G ς n Ex 𝔓 rec hP₁] at h
  exact h

/-- The graded `C_k(q)` is nonincreasing in `q ≥ P₀` when (S1) holds at `P₀` with the graded
pair (`lem:logconvex-coefficients`, monotonicity). -/
theorem gp_leafCk_antitone (G : OrientedGraph U) (ς : U → U → ℤ) (n : ℕ)
    (Ex : Finset (U × U)) (𝔓 : Finset (Finset (U × U) × Finset (U × U)))
    (rec : Finset (U × U) × Finset (U × U) → LeafRecordData U)
    (hrec : ∀ c ∈ 𝔓, (rec c).Valid Ex c) (k : ℕ) {P₀ q q' : ℝ} (hP₀ : 0 < P₀)
    (hS1 : gpEhat G P₀ n < 1) (h0 : P₀ ≤ q) (h1 : q ≤ q') :
    gpLeafCk G ς n Ex 𝔓 rec k q' ≤ gpLeafCk G ς n Ex 𝔓 rec k q := by
  have hq : 0 < q := lt_of_lt_of_le hP₀ h0
  have hq' : 0 < q' := lt_of_lt_of_le hq h1
  have hD := gpLcData_valid G ς n Ex 𝔓 rec hrec
  have h := LcData.Ck_antitone_P hD k hP₀ (gpLcData_inRange G ς n Ex 𝔓 rec hP₀ hS1) h0 h1
  rwa [gpLcData_Ck G ς n Ex 𝔓 rec k hq' (lt_of_le_of_lt (gpEhat_anti G n hP₀ (h0.trans h1))
    hS1), gpLcData_Ck G ς n Ex 𝔓 rec k hq (lt_of_le_of_lt (gpEhat_anti G n hP₀ h0) hS1)] at h

end GpBridge

end Sarkozy.ExtractionK
