module

public import Sarkozy.ExtractionK.GradedLeaf
public import Sarkozy.ExtractionK.LeafLogConvex

@[expose] public section

/-!
# Graded errors, IV: `cor:extraction-leaf`(b) with the graded error pair

`paper/sections/16_extraction.tex`, `cor:extraction-leaf`(b) with the paragraph *Graded errors*
of `subsec:extraction:partition` (`def:graphs:error-pair`, `eq:graphs:graded`): the nonstar
coefficients of the root cuts below `2^52` use the graded pair `e^-_t(n') = (𝔈_t + 2^t n')/q`
(`grGraded`).

* `gp_grGraded_eq`: `e^-_t(n') = a_t r + (b_t + 2^t n') r²`, `r = q^{-1/2}`; `gp_grGraded_anti`:
  nonincreasing in `q`; `gpEhat` (`ê = e^-_{Δ⁺}(q, n)`), `grGraded_le_gpEhat`, `gpEhat_anti`.
* `gp_leafFm_anti`, `gp_leafFrho_anti`, `gp_leafProdOf_anti`, `gp_rowsR_anti`: the graded leaf
  factors and `R_full` are nonincreasing in `q` where `ê(Q) < 1`; `gpLeafCoef` (the graded class
  coefficient, as `leafCoef`), `gpLeafCoef_anti`.
* **`gp_extraction_leaf_partition`**, **`gp_extraction_leaf_partition_grouped`**:
  `cor:extraction-leaf`(b) with the graded pair, `|⟨f, T_ns h⟩_μ| ≤ ∑_k C_k(Q) p^{-k/2} ‖f‖ ‖h‖`
  for every prime `p ≥ Q > 0` with `e^-_{Δ⁺}(Q, n) < 1`. Hypotheses: `WeilBound (ZMod p)` (H1)
  and `FourCycleBound p` (`cor:dl:normalized`(a)). As in `Leaf.lean`, the monotonicity in `q` is
  proved directly instead of through `lem:majorant`.
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

section GpError

/-- `e^-_t(n') = a_t r + (b_t + 2^t n') r²`, `r = q^{-1/2}`. -/
theorem gp_grGraded_eq {q : ℝ} (hq : 0 < q) (t : ℕ) (n' : ℝ) :
    grGraded q t n' = gradedA t * (Real.sqrt q)⁻¹ + (gradedB t + 2 ^ t * n') * (Real.sqrt q)⁻¹ ^ 2 := by
  unfold grGraded softError
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hsq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq.le
  rw [inv_pow, Real.sq_sqrt hq.le]
  have h1 : (Real.sqrt q)⁻¹ = Real.sqrt q / q := by
    rw [eq_div_iff hq.ne']
    calc (Real.sqrt q)⁻¹ * q = (Real.sqrt q)⁻¹ * (Real.sqrt q * Real.sqrt q) := by rw [hsq]
      _ = Real.sqrt q := by field_simp
  rw [h1]
  field_simp
  ring

theorem gp_grGraded_nonneg {q : ℝ} (hq : 0 < q) (t : ℕ) {n' : ℝ} (hn' : 0 ≤ n') :
    0 ≤ grGraded q t n' := (grErr_graded hq 0).nonneg t n' hn'

/-- `e^-_t(n')` is nonincreasing in `q > 0`. -/
theorem gp_grGraded_anti (t : ℕ) {n' : ℝ} (hn' : 0 ≤ n') {Q q : ℝ} (hQ : 0 < Q) (hQq : Q ≤ q) :
    grGraded q t n' ≤ grGraded Q t n' := by
  have hq : 0 < q := lt_of_lt_of_le hQ hQq
  rw [gp_grGraded_eq hq, gp_grGraded_eq hQ]
  have hr : (Real.sqrt q)⁻¹ ≤ (Real.sqrt Q)⁻¹ :=
    inv_anti₀ (Real.sqrt_pos.mpr hQ) (Real.sqrt_le_sqrt hQq)
  have hr0 : 0 ≤ (Real.sqrt q)⁻¹ := by positivity
  have hA := gradedA_nonneg t
  have hB : 0 ≤ gradedB t + 2 ^ t * n' := add_nonneg (gradedB_nonneg t) (by positivity)
  exact add_le_add (mul_le_mul_of_nonneg_left hr hA)
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr 2) hB)

end GpError

section GpDefs

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The graded `ê = e^-_{Δ⁺}(q, n)`, `Δ⁺ = max_i d⁰_i`. -/
noncomputable def gpEhat (G : OrientedGraph U) (q : ℝ) (n : ℕ) : ℝ :=
  grGraded q (univ.sup (rowsDeg0 G)) n

/-- The coefficient of a class with a record in `C_k(q)` (`cor:extraction-leaf`(b)) with the graded
error pair: `2^{ex*/2} R_full² (1 - ê)^{-k} ∏_u 𝖿_m(s_u)^{1/2} ∏_b 𝖿_ρ(s_b)^{1/2}`, every count error
being `e^-_t(n') = (𝔈_t + 2^t n')/q` (`grGraded`). -/
noncomputable def gpLeafCoef (G : OrientedGraph U) (ς : U → U → ℤ) (q : ℝ) (n : ℕ)
    (Ex : Finset (U × U)) (c : Finset (U × U) × Finset (U × U)) (R : LeafRecordData U) : ℝ :=
  Real.sqrt (2 ^ (recordExp G (Ex \ (c.1 ∪ c.2)) (witV R.w) (witW R.w) R.ordX R.ordZ +
      2 * twoCycleCount (witnessIdx c.1 R.w)) *
    grLeafProd G ς (grGraded q) q n (gpEhat G q n) (Ex \ (c.1 ∪ c.2)) (witV R.w) (witW R.w)
      R.Cx R.Cz R.ordX R.ordZ) * grRowsR G (grGraded q) n univ ^ 2 / (1 - gpEhat G q n) ^ R.k

theorem grGraded_le_gpEhat (G : OrientedGraph U) {q : ℝ} (hq : 0 < q) (n : ℕ) (i : U) :
    grGraded q (rowsDeg0 G i) n ≤ gpEhat G q n :=
  (grErr_graded hq n).mono n (Nat.cast_nonneg n) _ _ (le_sup (f := rowsDeg0 G) (mem_univ i))

theorem gpEhat_anti (G : OrientedGraph U) (n : ℕ) {Q q : ℝ} (hQ : 0 < Q) (hQq : Q ≤ q) :
    gpEhat G q n ≤ gpEhat G Q n :=
  gp_grGraded_anti _ (Nat.cast_nonneg n) hQ hQq

end GpDefs

section GpAnti

variable {U : Type*} [Fintype U] [DecidableEq U]

theorem gp_leafFm_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) {q : ℝ} (hq : 0 < q) (n : ℕ)
    {ehat : ℝ} (hehat1 : ehat < 1) (s : ℕ) : 0 ≤ grLeafFm G ς (grGraded q) q n ehat s := by
  unfold grLeafFm
  have he0 := gp_grGraded_nonneg hq s (Nat.cast_nonneg (α := ℝ) n)
  have hS := leafS_nonneg G ς (weightM G ς) (weightM_nonneg G ς) s
  exact div_nonneg (add_nonneg (by linarith) (mul_nonneg (by positivity) hS)) (by linarith)

theorem gp_leafFrho_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) {q : ℝ} (hq : 0 < q) (n : ℕ)
    {ehat : ℝ} (hehat1 : ehat < 1) (s : ℕ) : 0 ≤ grLeafFrho G ς (grGraded q) q n ehat s := by
  unfold grLeafFrho
  have he0 := gp_grGraded_nonneg hq s (by positivity : (0 : ℝ) ≤ 2 * n)
  have hS := leafS_nonneg G ς (weightRho G ς) (weightRho_nonneg G ς) s
  exact div_nonneg (add_nonneg (by linarith) (mul_nonneg (by positivity) hS)) (by linarith)

/-- The graded leaf factor `𝖿_m(s)` is nonincreasing in `q` (with `ê = e^-_{Δ⁺}(q, n)`). -/
theorem gp_leafFm_anti (G : OrientedGraph U) (ς : U → U → ℤ) {n : ℕ} {Q q : ℝ} (hQ : 0 < Q)
    (hQq : Q ≤ q) (hS1 : gpEhat G Q n < 1) (s : ℕ) :
    grLeafFm G ς (grGraded q) q n (gpEhat G q n) s ≤
      grLeafFm G ς (grGraded Q) Q n (gpEhat G Q n) s := by
  have hq : 0 < q := lt_of_lt_of_le hQ hQq
  unfold grLeafFm
  have he := gpEhat_anti G n hQ hQq
  have hes := gp_grGraded_anti s (Nat.cast_nonneg (α := ℝ) n) hQ hQq
  have he0 := gp_grGraded_nonneg hq s (Nat.cast_nonneg (α := ℝ) n)
  have hS := leafS_nonneg G ς (weightM G ς) (weightM_nonneg G ς) s
  have hr : (Real.sqrt q)⁻¹ ^ 2 ≤ (Real.sqrt Q)⁻¹ ^ 2 :=
    pow_le_pow_left₀ (by positivity)
      (inv_anti₀ (Real.sqrt_pos.mpr hQ) (Real.sqrt_le_sqrt hQq)) 2
  have hmul : (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s * leafS G ς (weightM G ς) s ≤
      (Real.sqrt Q)⁻¹ ^ 2 * 2 ^ s * leafS G ς (weightM G ς) s :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hr (by positivity)) hS
  have hm0 : 0 ≤ (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s * leafS G ς (weightM G ς) s :=
    mul_nonneg (by positivity) hS
  exact div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith)

/-- The graded leaf factor `𝖿_ρ(s)` is nonincreasing in `q`. -/
theorem gp_leafFrho_anti (G : OrientedGraph U) (ς : U → U → ℤ) {n : ℕ} {Q q : ℝ} (hQ : 0 < Q)
    (hQq : Q ≤ q) (hS1 : gpEhat G Q n < 1) (s : ℕ) :
    grLeafFrho G ς (grGraded q) q n (gpEhat G q n) s ≤
      grLeafFrho G ς (grGraded Q) Q n (gpEhat G Q n) s := by
  have hq : 0 < q := lt_of_lt_of_le hQ hQq
  unfold grLeafFrho
  have he := gpEhat_anti G n hQ hQq
  have hes := gp_grGraded_anti s (by positivity : (0 : ℝ) ≤ 2 * n) hQ hQq
  have he0 := gp_grGraded_nonneg hq s (by positivity : (0 : ℝ) ≤ 2 * n)
  have hS := leafS_nonneg G ς (weightRho G ς) (weightRho_nonneg G ς) s
  have hr : (Real.sqrt q)⁻¹ ^ 2 ≤ (Real.sqrt Q)⁻¹ ^ 2 :=
    pow_le_pow_left₀ (by positivity)
      (inv_anti₀ (Real.sqrt_pos.mpr hQ) (Real.sqrt_le_sqrt hQq)) 2
  have hmul : (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s * leafS G ς (weightRho G ς) s ≤
      (Real.sqrt Q)⁻¹ ^ 2 * 2 ^ s * leafS G ς (weightRho G ς) s :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hr (by positivity)) hS
  have hm0 : 0 ≤ (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s * leafS G ς (weightRho G ς) s :=
    mul_nonneg (by positivity) hS
  exact div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith)

theorem gp_leafProdOf_anti (G : OrientedGraph U) (ς : U → U → ℤ) {n : ℕ} {Q q : ℝ}
    (hQ : 0 < Q) (hQq : Q ≤ q) (hS1 : gpEhat G Q n < 1) (V W Cx Cz : Finset U)
    (sUx sCz sUz sCx : U → ℕ) :
    grLeafProdOf G ς (grGraded q) q n (gpEhat G q n) V W Cx Cz sUx sCz sUz sCx ≤
      grLeafProdOf G ς (grGraded Q) Q n (gpEhat G Q n) V W Cx Cz sUx sCz sUz sCx := by
  have hq : 0 < q := lt_of_lt_of_le hQ hQq
  have hq1 : gpEhat G q n < 1 := lt_of_le_of_lt (gpEhat_anti G n hQ hQq) hS1
  unfold grLeafProdOf
  have a1 := prod_le_prod₀ (s := univ \ (V ∪ Cx))
    (fun u _ => gp_leafFm_nonneg G ς hq n hq1 (sUx u))
    (fun u _ => gp_leafFm_anti G ς hQ hQq hS1 (sUx u))
  have a2 := prod_le_prod₀ (s := Cz)
    (fun b _ => gp_leafFrho_nonneg G ς hq n hq1 (sCz b))
    (fun b _ => gp_leafFrho_anti G ς hQ hQq hS1 (sCz b))
  have a3 := prod_le_prod₀ (s := univ \ (W ∪ Cz))
    (fun u _ => gp_leafFm_nonneg G ς hq n hq1 (sUz u))
    (fun u _ => gp_leafFm_anti G ς hQ hQq hS1 (sUz u))
  have a4 := prod_le_prod₀ (s := Cx)
    (fun b _ => gp_leafFrho_nonneg G ς hq n hq1 (sCx b))
    (fun b _ => gp_leafFrho_anti G ς hQ hQq hS1 (sCx b))
  have p1 := prod_nonneg fun u (_ : u ∈ univ \ (V ∪ Cx)) => gp_leafFm_nonneg G ς hq n hq1 (sUx u)
  have p2 := prod_nonneg fun b (_ : b ∈ Cz) => gp_leafFrho_nonneg G ς hq n hq1 (sCz b)
  have p3 := prod_nonneg fun u (_ : u ∈ univ \ (W ∪ Cz)) => gp_leafFm_nonneg G ς hq n hq1 (sUz u)
  have p4 := prod_nonneg fun b (_ : b ∈ Cx) => gp_leafFrho_nonneg G ς hq n hq1 (sCx b)
  have q1 := le_trans p1 a1
  have q2 := le_trans p2 a2
  have q3 := le_trans p3 a3
  exact mul_le_mul (mul_le_mul (mul_le_mul a1 a2 p2 q1) a3 p3 (mul_nonneg q1 q2)) a4 p4
    (mul_nonneg (mul_nonneg q1 q2) q3)

theorem gp_rowsR_anti (G : OrientedGraph U) {n : ℕ} {Q q : ℝ} (hQ : 0 < Q) (hQq : Q ≤ q)
    (hS1 : gpEhat G Q n < 1) : grRowsR G (grGraded q) n univ ≤ grRowsR G (grGraded Q) n univ := by
  have hq : 0 < q := lt_of_lt_of_le hQ hQq
  unfold grRowsR
  refine prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_)
  · have h0 := gp_grGraded_nonneg hq (rowsDeg0 G i) (Nat.cast_nonneg (α := ℝ) n)
    have h1 := (grGraded_le_gpEhat G hq n i).trans_lt
      (lt_of_le_of_lt (gpEhat_anti G n hQ hQq) hS1)
    exact div_nonneg (by linarith) (by linarith)
  · have h0 := gp_grGraded_nonneg hq (rowsDeg0 G i) (Nat.cast_nonneg (α := ℝ) n)
    have h1 := gp_grGraded_anti (rowsDeg0 G i) (Nat.cast_nonneg (α := ℝ) n) hQ hQq
    have h2 := (grGraded_le_gpEhat G hQ n i).trans_lt hS1
    exact div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith)

/-- The graded class coefficient is nonincreasing in `q` where `e^-_{Δ⁺}(Q, n) < 1`
(`cor:extraction-leaf`(b) with the graded pair; the paper uses `lem:majorant`). -/
theorem gpLeafCoef_anti (G : OrientedGraph U) (ς : U → U → ℤ) {n : ℕ} {Q q : ℝ} (hQ : 0 < Q)
    (hQq : Q ≤ q) (hS1 : gpEhat G Q n < 1) (Ex : Finset (U × U))
    (c : Finset (U × U) × Finset (U × U)) (R : LeafRecordData U) :
    gpLeafCoef G ς q n Ex c R ≤ gpLeafCoef G ς Q n Ex c R := by
  have hq : 0 < q := lt_of_lt_of_le hQ hQq
  have he := gpEhat_anti G n hQ hQq
  have hq1 : gpEhat G q n < 1 := lt_of_le_of_lt he hS1
  have hP := gp_leafProdOf_anti G ς hQ hQq hS1 (witV R.w) (witW R.w) R.Cx R.Cz
    (intS G R.ordX (Ex \ (c.1 ∪ c.2)))
    (coverRowS G R.Cz R.ordZ ((Ex \ (c.1 ∪ c.2)).filter (fun e => e.2 ∈ R.Cz)))
    (intS G R.ordZ ((Ex \ (c.1 ∪ c.2)).image Prod.swap))
    (coverRowS G R.Cx R.ordX (((Ex \ (c.1 ∪ c.2)).image Prod.swap).filter
      (fun e => e.2 ∈ R.Cx)))
  have hR := gp_rowsR_anti G hQ hQq hS1
  have hR0 : 0 ≤ grRowsR G (grGraded q) n univ :=
    le_trans zero_le_one (gr_rowsR_ge_one G (grErr_graded hq n)
      (fun i => (grGraded_le_gpEhat G hq n i).trans_lt hq1))
  unfold gpLeafCoef
  have hsq := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hP
    (by positivity : (0 : ℝ) ≤ 2 ^ (recordExp G (Ex \ (c.1 ∪ c.2)) (witV R.w) (witW R.w) R.ordX
      R.ordZ + 2 * twoCycleCount (witnessIdx c.1 R.w))))
  have hR2 : grRowsR G (grGraded q) n univ ^ 2 ≤ grRowsR G (grGraded Q) n univ ^ 2 :=
    pow_le_pow_left₀ hR0 hR 2
  have hnum := mul_le_mul hsq hR2 (sq_nonneg _) (Real.sqrt_nonneg _)
  refine div_le_div₀ (mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)) hnum
    (pow_pos (by linarith) _) (pow_le_pow_left₀ (by linarith) (by linarith) _)

end GpAnti

section GpPartition

variable {p : ℕ} [Fact p.Prime]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- **`cor:extraction-leaf`(b) with the graded error pair** (*Graded errors*,
`def:graphs:error-pair`, `eq:graphs:graded`): for an exact partition `𝔓` of the nonstar subsets
of `E_×` into classes with fixed records (`LeafRecordData.Valid`), if `e^-_{Δ⁺}(Q, n) < 1` at a
real `Q > 0`, then for every prime `p ≥ Q`
`|⟨f, T_ns h⟩_μ| ≤ ∑_{𝒞 ∈ 𝔓} p^{-k_𝒞/2} C_𝒞(Q) ‖f‖_μ ‖h‖_μ`, `C_𝒞(Q)` the graded class coefficient
`gpLeafCoef` at `r = Q^{-1/2}` (every count error `e^-_t(n') = (𝔈_t + 2^t n')/Q`). The
four-cycle bound (`cor:dl:normalized`(a)) is the hypothesis `FourCycleBound p`. -/
theorem gp_extraction_leaf_partition (hW : WeilBound (ZMod p)) (hp2 : p ≠ 2)
    (h4 : FourCycleBound p) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings (ZMod p) G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n)
    (Ex : Finset (U × U)) (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0)
    (𝔓 : Finset (Finset (U × U) × Finset (U × U)))
    (h𝔓 : IsExactPartition Ex 𝔓 (nonstars Ex))
    (rec : Finset (U × U) × Finset (U × U) → LeafRecordData U)
    (hrec : ∀ c ∈ 𝔓, (rec c).Valid Ex c) {Q : ℝ} (hQ : 0 < Q) (hQp : Q ≤ p)
    (hS1 : gpEhat G Q n < 1) (f h : (U → ZMod p) → ℝ) :
    |(graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
        (∑ S ∈ nonstars Ex, ∏ e ∈ S, chiPair ς e x x') * h x'))| ≤
      (∑ c ∈ 𝔓, (Real.sqrt p)⁻¹ ^ (rec c).k * gpLeafCoef G ς Q n Ex c (rec c)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by
  set μ := graphLaw G hne
  have hsplit : ∀ x x' : U → ZMod p, ∑ S ∈ nonstars Ex, ∏ e ∈ S, chiPair ς e x x' =
      ∑ c ∈ 𝔓, ∑ S ∈ cls Ex c.1 c.2, ∏ e ∈ S, chiPair ς e x x' := by
    intro x x'
    rw [← h𝔓.2.2, sum_biUnion h𝔓.2.1]
  have hlin : μ.expect (fun x => f x * μ.expect (fun x' =>
      (∑ S ∈ nonstars Ex, ∏ e ∈ S, chiPair ς e x x') * h x')) =
      ∑ c ∈ 𝔓, μ.expect (fun x => f x * μ.expect (fun x' =>
        (∑ S ∈ cls Ex c.1 c.2, ∏ e ∈ S, chiPair ς e x x') * h x')) := by
    simp_rw [hsplit, sum_mul]
    rw [← leaf_expect_finset_sum]
    refine μ.expect_congr fun x => ?_
    rw [leaf_expect_finset_sum, mul_sum]
  rw [hlin]
  have hpQ : (0 : ℝ) < p := lt_of_lt_of_le hQ hQp
  have hp1 : gpEhat G p n < 1 := lt_of_le_of_lt (gpEhat_anti G n hQ hQp) hS1
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [sum_mul, sum_mul]
  refine sum_le_sum fun c hc => ?_
  have hv := hrec c hc
  have hcls : IsClassDatum Ex (c.1, c.2) := h𝔓.1 c hc
  have hb := gr_extraction_leaf_twoCycles_graded hW hp2 h4 G ς hς hanti hne hn
    (fun i => grGraded_le_gpEhat G hpQ n i) hp1 Ex c.1 c.2 hEx hcls (rec c).w hv.witness
    hv.twoCycles (rec c).Cx (rec c).Cz hv.cover (rec c).ordX (rec c).ordZ hv.injX hv.injZ
    hv.segX0 hv.segZ0 hv.segX1 hv.segZ1 f h
  refine hb.trans ?_
  have hco := gpLeafCoef_anti G ς hQ hQp hS1 Ex c (rec c)
  unfold gpLeafCoef at hco
  have hX : 0 ≤ (Real.sqrt p)⁻¹ ^ (rec c).k * Real.sqrt (μ.expect (fun x => f x ^ 2)) *
      Real.sqrt (μ.expect (fun x => h x ^ 2)) := by positivity
  calc (Real.sqrt p)⁻¹ ^ (rec c).k *
        Real.sqrt (2 ^ (recordExp G (Ex \ (c.1 ∪ c.2)) (witV (rec c).w) (witW (rec c).w)
            (rec c).ordX (rec c).ordZ + 2 * twoCycleCount (witnessIdx c.1 (rec c).w)) *
          grLeafProd G ς (grGraded p) p n (gpEhat G p n) (Ex \ (c.1 ∪ c.2)) (witV (rec c).w)
            (witW (rec c).w) (rec c).Cx (rec c).Cz (rec c).ordX (rec c).ordZ) *
        grRowsR G (grGraded p) n univ ^ 2 / (1 - gpEhat G p n) ^ (rec c).k *
        Real.sqrt (μ.expect (fun x => f x ^ 2)) * Real.sqrt (μ.expect (fun x => h x ^ 2))
      = ((Real.sqrt p)⁻¹ ^ (rec c).k * Real.sqrt (μ.expect (fun x => f x ^ 2)) *
          Real.sqrt (μ.expect (fun x => h x ^ 2))) *
        (Real.sqrt (2 ^ (recordExp G (Ex \ (c.1 ∪ c.2)) (witV (rec c).w) (witW (rec c).w)
            (rec c).ordX (rec c).ordZ + 2 * twoCycleCount (witnessIdx c.1 (rec c).w)) *
          grLeafProd G ς (grGraded p) p n (gpEhat G p n) (Ex \ (c.1 ∪ c.2)) (witV (rec c).w)
            (witW (rec c).w) (rec c).Cx (rec c).Cz (rec c).ordX (rec c).ordZ) *
        grRowsR G (grGraded p) n univ ^ 2 / (1 - gpEhat G p n) ^ (rec c).k) := by ring
    _ ≤ ((Real.sqrt p)⁻¹ ^ (rec c).k * Real.sqrt (μ.expect (fun x => f x ^ 2)) *
          Real.sqrt (μ.expect (fun x => h x ^ 2))) * gpLeafCoef G ς Q n Ex c (rec c) :=
        mul_le_mul_of_nonneg_left hco hX
    _ = _ := by ring

/-- **`cor:extraction-leaf`(b) with the graded error pair, grouped by the witness size**:
`|⟨f, T_ns h⟩_μ| ≤ ∑_k C_k(Q) p^{-k/2} ‖f‖_μ ‖h‖_μ`, `C_k(Q)` the sum of the graded class
coefficients of the classes of witness size `k`. -/
theorem gp_extraction_leaf_partition_grouped (hW : WeilBound (ZMod p)) (hp2 : p ≠ 2)
    (h4 : FourCycleBound p) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings (ZMod p) G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n)
    (Ex : Finset (U × U)) (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0)
    (𝔓 : Finset (Finset (U × U) × Finset (U × U)))
    (h𝔓 : IsExactPartition Ex 𝔓 (nonstars Ex))
    (rec : Finset (U × U) × Finset (U × U) → LeafRecordData U)
    (hrec : ∀ c ∈ 𝔓, (rec c).Valid Ex c) {Q : ℝ} (hQ : 0 < Q) (hQp : Q ≤ p)
    (hS1 : gpEhat G Q n < 1) (f h : (U → ZMod p) → ℝ) :
    |(graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
        (∑ S ∈ nonstars Ex, ∏ e ∈ S, chiPair ς e x x') * h x'))| ≤
      (∑ k ∈ 𝔓.image (fun c => (rec c).k),
          (∑ c ∈ 𝔓.filter (fun c => (rec c).k = k), gpLeafCoef G ς Q n Ex c (rec c)) *
            (Real.sqrt p)⁻¹ ^ k) *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by
  refine (gp_extraction_leaf_partition hW hp2 h4 G ς hς hanti hne hn Ex hEx 𝔓 h𝔓 rec hrec hQ
    hQp hS1 f h).trans (le_of_eq ?_)
  congr 2
  rw [← sum_fiberwise_of_maps_to (g := fun c => (rec c).k) (t := 𝔓.image (fun c => (rec c).k))
    (fun c hc => mem_image_of_mem _ hc)]
  refine sum_congr rfl fun k _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun c hc => ?_
  rw [(mem_filter.mp hc).2]
  ring

end GpPartition

end Sarkozy.ExtractionK
