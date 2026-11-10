module

public import Sarkozy.JointRows.RowsAChain
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Positive potentials (`lem:joint-potential`)

Source: `paper/sections/16_extraction.tex`, `lem:joint-potential` and its proof.

The gate `eq:joint-gate` of `lem:joint-rows`(a) is replaced by the family of tests
`𝗄²I_S - 𝗄κ₀T_S - κ₀²𝒢_S ⪰ 0` (`S ∈ 𝒮`, `eq:joint-potential-gate`), where `T` is a real
symmetric matrix with `T ± i𝒵 ⪰ 0` and `X_S` is the principal submatrix on `S`.

* `quad_submatrix`: the quadratic form of a principal submatrix at `y|_S` is that of the matrix
  at `y`, for `y` supported in `S`.
* `potential_pointwise`: **the matrix bound of the proof.** If `D = diag(d)` vanishes outside
  `S`, `0 ≤ d_i ≤ √κ₀`, and the gate holds on `S`, then `(Dx)ᵀ(𝗄T + κ₀𝒢)(Dx) ≤ 𝗄²|x|²` for all
  `x`, i.e. `𝗄²I - D(𝗄T + κ₀𝒢)D ⪰ 0`. (The paper argues through `λ_max`; the form argument does not
  need `𝗄T + κ₀𝒢 ⪰ 0`.)
* `potential_sum`: the same for the multiplication by the matrix function
  `t ↦ 𝗄²I - D(t)(𝗄T + κ₀𝒢)D(t)` (`D(t) = diag(√ρ_i(t))`), integrated against a law on `t`.
* `pure_part_potential`: **the bound `ℙ ⪰ -r𝗄I` of the pure part.** The operator facts are
  hypotheses: `ℙ` is a compression of `𝕊` (`hcomp`); in `𝕊` the singleton block is
  `rD(𝒵 ⊗ Φ̂)D` and the coupling `√κ₀ r D(𝒜 ⊗ I)𝒲*` with `𝒲` a contraction, so its form is bounded
  by `√⟨Dy, (𝒢 ⊗ I)Dy⟩ ‖v‖` (`hcouple`); and `D(𝒵 ⊗ Φ̂)D ⪰ -D(T ⊗ I)D` (`heig`, from
  `T ± i𝒵 ⪰ 0` on the eigenspaces of `Φ̂`, `lem:spec:gauss`). The completion of the square
  (`lem:block-completion`(a)) and the pointwise bound are proved.
* **`joint_potential`**: the conclusion of `lem:joint-rows`(a) without `eq:joint-gate`, with
  `r𝗄/I₀` in place of `κ₀r𝗄/I₀`: `𝔨 = e^{ℓ_E}[(r𝗄 + κ₀r(e_F + e_E))/I₀ + 𝔠_F + 𝔠_E]`.

Not formalized: the remark that `T = |𝒵|` satisfies `T ± i𝒵 ⪰ 0`, and the rationality remark
(`rem:realified-gates`).
-/

@[expose] public section

open scoped BigOperators
open Matrix

namespace Sarkozy.JointRows

open Sarkozy.FiveType Sarkozy.FiveType.Blocks

namespace Potential

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- The quadratic form of the principal submatrix on `S` at `y|_S` is that of the matrix at `y`,
for `y` supported in `S`. -/
theorem quad_submatrix (M : Matrix n n ℝ) (S : Finset n) (y : n → ℝ)
    (hy : ∀ i, i ∉ S → y i = 0) :
    (fun i : S => y i) ⬝ᵥ (M.submatrix (fun i : S => (i : n)) (fun i : S => (i : n)) *ᵥ
      (fun i : S => y i)) = y ⬝ᵥ (M *ᵥ y) := by
  simp only [dotProduct, mulVec, submatrix_apply]
  have hout : ∀ i, i ∉ S → y i * ∑ j, M i j * y j = 0 := fun i hi => by rw [hy i hi, zero_mul]
  rw [← Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => hout i hi)]
  rw [← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have hout' : ∀ j, j ∉ S → M i j * y j = 0 := fun j hj => by rw [hy j hj, mul_zero]
  rw [← Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => hout' j hj),
    ← Finset.sum_coe_sort S]

/-- **The pointwise matrix bound of `lem:joint-potential`**: if `d` vanishes outside `S`,
`0 ≤ d_i`, `d_i² ≤ κ₀`, and `𝗄²I_S - 𝗄κ₀T_S - κ₀²𝒢_S ⪰ 0`, then
`(Dx)ᵀ(𝗄T + κ₀𝒢)(Dx) ≤ 𝗄²|x|²` for `D = diag(d)`. -/
theorem potential_pointwise (T G : Matrix n n ℝ) {k κ₀ : ℝ} (hκ₀ : 0 < κ₀) (S : Finset n)
    (hgate : ((k ^ 2 • (1 : Matrix n n ℝ) - (k * κ₀) • T - κ₀ ^ 2 • G).submatrix
      (fun i : S => (i : n)) (fun i : S => (i : n))).PosSemidef)
    (d : n → ℝ) (hdκ : ∀ i, d i ^ 2 ≤ κ₀) (hdS : ∀ i, i ∉ S → d i = 0) (x : n → ℝ) :
    (fun i => d i * x i) ⬝ᵥ ((k • T + κ₀ • G) *ᵥ (fun i => d i * x i)) ≤ k ^ 2 * (x ⬝ᵥ x) := by
  set y : n → ℝ := fun i => d i * x i with hydef
  have hy : ∀ i, i ∉ S → y i = 0 := fun i hi => by simp only [hydef, hdS i hi, zero_mul]
  have h0 := hgate.dotProduct_mulVec_nonneg (fun i : S => y i)
  simp only [star_trivial] at h0
  rw [quad_submatrix _ S y hy] at h0
  have hexp : y ⬝ᵥ ((k ^ 2 • (1 : Matrix n n ℝ) - (k * κ₀) • T - κ₀ ^ 2 • G) *ᵥ y) =
      k ^ 2 * (y ⬝ᵥ y) - κ₀ * (y ⬝ᵥ ((k • T + κ₀ • G) *ᵥ y)) := by
    simp only [sub_mulVec, add_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_add,
      dotProduct_smul, smul_eq_mul]
    ring
  rw [hexp] at h0
  have hyy : y ⬝ᵥ y ≤ κ₀ * (x ⬝ᵥ x) := by
    simp only [hydef, dotProduct, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have := mul_le_mul_of_nonneg_right (hdκ i) (mul_self_nonneg (x i))
    nlinarith
  have hk2 : k ^ 2 * (y ⬝ᵥ y) ≤ k ^ 2 * (κ₀ * (x ⬝ᵥ x)) :=
    mul_le_mul_of_nonneg_left hyy (sq_nonneg k)
  have h1 : κ₀ * (y ⬝ᵥ ((k • T + κ₀ • G) *ᵥ y)) ≤ κ₀ * (k ^ 2 * (x ⬝ᵥ x)) := by linarith
  exact le_of_mul_le_mul_left h1 hκ₀

variable {Ωt : Type*} [Fintype Ωt]

/-- **The multiplication by the matrix function** `t ↦ 𝗄²I - D(t)(𝗄T + κ₀𝒢)D(t)` is positive:
for `u : Ωt → (n → ℝ)` and a law `λ` on `t`,
`E_t[(D(t)u(t))ᵀ(𝗄T + κ₀𝒢)(D(t)u(t))] ≤ 𝗄² E_t|u(t)|²`, when at each `t` the potential `D(t)`
vanishes outside some `S(t) ∈ 𝒮` and `D(t)² ≤ κ₀`, and the gate holds on every `S ∈ 𝒮`. -/
theorem potential_sum (T G : Matrix n n ℝ) {k κ₀ : ℝ} (hκ₀ : 0 < κ₀) (𝒮 : Finset (Finset n))
    (hgate : ∀ S ∈ 𝒮, ((k ^ 2 • (1 : Matrix n n ℝ) - (k * κ₀) • T - κ₀ ^ 2 • G).submatrix
      (fun i : S => (i : n)) (fun i : S => (i : n))).PosSemidef)
    (lam : FiniteLaw Ωt) (D : Ωt → n → ℝ) (Sel : Ωt → Finset n) (hSel : ∀ t, Sel t ∈ 𝒮)
    (hdκ : ∀ t i, D t i ^ 2 ≤ κ₀) (hdS : ∀ t i, i ∉ Sel t → D t i = 0) (u : Ωt → n → ℝ) :
    lam.expect (fun t => (fun i => D t i * u t i) ⬝ᵥ ((k • T + κ₀ • G) *ᵥ
      (fun i => D t i * u t i))) ≤ k ^ 2 * lam.expect (fun t => u t ⬝ᵥ u t) := by
  rw [← FiniteLaw.expect_const_mul]
  exact lam.expect_mono fun t =>
    potential_pointwise T G hκ₀ (Sel t) (hgate _ (hSel t)) (D t) (hdκ t) (hdS t) (u t)

/-- **`ℙ ⪰ -r𝗄I`, the pure part of `lem:joint-potential`.** The space of `𝕊` is
`L²(𝔽_p)^{coordinates} ⊕ (higher part)`, written as pairs `(u, v)`, `u : Ωt → n → ℝ` with the
norm `E_t|u(t)|²`, and `v` in a normed space. The operator facts are hypotheses:
* `hcomp` (compression): `qP x = qS(u x, v x)` with `E|u x|² + ‖v x‖² ≤ ‖x‖²`;
* `hS` (the blocks of `𝕊`): `qS(u, v) = r·Zq(Du) + 2√κ₀ r·Bq(Du, v)`, with `Zq(y) = ⟨y, (𝒵 ⊗ Φ̂)y⟩`
  and `Bq(y, v) = ⟨y, (𝒜 ⊗ I)𝒲* v⟩`;
* `hcouple` (`𝒲` a contraction, `𝒢 = 𝒜𝒜*`): `|Bq(y, v)| ≤ √(E_t y(t)ᵀ𝒢y(t)) ‖v‖`;
* `heig` (`T ± i𝒵 ⪰ 0` on the eigenspaces of `Φ̂`, `lem:spec:gauss`):
  `Zq(y) ≥ -E_t y(t)ᵀTy(t)`;
* `hGpos`: `𝒢 ⪰ 0`.

The completion of the square (`lem:block-completion`(a) on the block `r𝗄I`) and the pointwise
bound `potential_sum` are proved. -/
theorem pure_part_potential {E Hs : Type*} [NormedAddCommGroup E] [NormedAddCommGroup Hs]
    (T G : Matrix n n ℝ) {k κ₀ r : ℝ} (hk : 0 < k) (hκ₀ : 0 < κ₀) (hr : 0 ≤ r)
    (𝒮 : Finset (Finset n))
    (hgate : ∀ S ∈ 𝒮, ((k ^ 2 • (1 : Matrix n n ℝ) - (k * κ₀) • T - κ₀ ^ 2 • G).submatrix
      (fun i : S => (i : n)) (fun i : S => (i : n))).PosSemidef)
    (lam : FiniteLaw Ωt) (D : Ωt → n → ℝ) (Sel : Ωt → Finset n) (hSel : ∀ t, Sel t ∈ 𝒮)
    (hdκ : ∀ t i, D t i ^ 2 ≤ κ₀) (hdS : ∀ t i, i ∉ Sel t → D t i = 0)
    (hGpos : ∀ y : n → ℝ, 0 ≤ y ⬝ᵥ (G *ᵥ y))
    (qP : E → ℝ) (qS : (Ωt → n → ℝ) → Hs → ℝ) (uc : E → Ωt → n → ℝ) (vc : E → Hs)
    (hcomp : ∀ x, qP x = qS (uc x) (vc x) ∧
      lam.expect (fun t => uc x t ⬝ᵥ uc x t) + ‖vc x‖ ^ 2 ≤ ‖x‖ ^ 2)
    (Zq : (Ωt → n → ℝ) → ℝ) (Bq : (Ωt → n → ℝ) → Hs → ℝ)
    (hS : ∀ u v, qS u v = r * Zq (fun t i => D t i * u t i) +
      2 * Real.sqrt κ₀ * r * Bq (fun t i => D t i * u t i) v)
    (hcouple : ∀ y v, |Bq y v| ≤ Real.sqrt (lam.expect (fun t => y t ⬝ᵥ (G *ᵥ y t))) * ‖v‖)
    (heig : ∀ y, -lam.expect (fun t => y t ⬝ᵥ (T *ᵥ y t)) ≤ Zq y) (x : E) :
    -(r * k) * ‖x‖ ^ 2 ≤ qP x := by
  obtain ⟨hPx, hnorm⟩ := hcomp x
  rw [hPx, hS]
  set u := uc x
  set v := vc x
  set y : Ωt → n → ℝ := fun t i => D t i * u t i
  set gq := lam.expect (fun t => y t ⬝ᵥ (G *ᵥ y t))
  set tq := lam.expect (fun t => y t ⬝ᵥ (T *ᵥ y t))
  have hgq : 0 ≤ gq := lam.expect_nonneg fun t => hGpos (y t)
  -- the pointwise bound, summed: `𝗄 tq + κ₀ gq ≤ 𝗄² E|u|²`
  have hsum := potential_sum T G hκ₀ 𝒮 hgate lam D Sel hSel hdκ hdS u
  have hlin : lam.expect (fun t => y t ⬝ᵥ ((k • T + κ₀ • G) *ᵥ y t)) = k * tq + κ₀ * gq := by
    rw [← FiniteLaw.expect_const_mul, ← FiniteLaw.expect_const_mul, ← FiniteLaw.expect_add]
    refine lam.expect_congr fun t => ?_
    simp only [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
  rw [hlin] at hsum
  -- completing the square: `2√κ₀ √gq ‖v‖ ≤ 𝗄‖v‖² + κ₀ gq/𝗄`
  have hB := neg_abs_le (Bq y v)
  have hc := hcouple y v
  have hsq : Real.sqrt gq ^ 2 = gq := Real.sq_sqrt hgq
  have hsk : Real.sqrt κ₀ ^ 2 = κ₀ := Real.sq_sqrt hκ₀.le
  have hyoung : 2 * Real.sqrt κ₀ * (Real.sqrt gq * ‖v‖) ≤ k * ‖v‖ ^ 2 + κ₀ * gq / k := by
    have h1 : 0 ≤ (k * ‖v‖ - Real.sqrt κ₀ * Real.sqrt gq) ^ 2 / k :=
      div_nonneg (sq_nonneg _) hk.le
    have h2 : (k * ‖v‖ - Real.sqrt κ₀ * Real.sqrt gq) ^ 2 / k =
        k * ‖v‖ ^ 2 + Real.sqrt κ₀ ^ 2 * Real.sqrt gq ^ 2 / k -
          2 * Real.sqrt κ₀ * (Real.sqrt gq * ‖v‖) := by
      field_simp
      ring
    rw [hsq, hsk] at h2
    linarith
  have hBlow : -(Real.sqrt gq * ‖v‖) ≤ Bq y v := by linarith
  have hsk0 : 0 ≤ 2 * Real.sqrt κ₀ * r := by positivity
  have t1 := mul_le_mul_of_nonneg_left hBlow hsk0
  have t2 := mul_le_mul_of_nonneg_left (heig y) hr
  -- `r Zq + 2√κ₀ r Bq ≥ -r tq - r(𝗄‖v‖² + κ₀ gq/𝗄)`
  have t3 : r * (2 * Real.sqrt κ₀ * (Real.sqrt gq * ‖v‖)) ≤ r * (k * ‖v‖ ^ 2 + κ₀ * gq / k) :=
    mul_le_mul_of_nonneg_left hyoung hr
  -- `tq + κ₀ gq/𝗄 ≤ 𝗄 E|u|²`
  have t4 : tq + κ₀ * gq / k ≤ k * lam.expect (fun t => u t ⬝ᵥ u t) := by
    have : (k * tq + κ₀ * gq) / k ≤ (k ^ 2 * lam.expect (fun t => u t ⬝ᵥ u t)) / k :=
      div_le_div_of_nonneg_right hsum hk.le
    have e1 : (k * tq + κ₀ * gq) / k = tq + κ₀ * gq / k := by field_simp
    have e2 : (k ^ 2 * lam.expect (fun t => u t ⬝ᵥ u t)) / k =
        k * lam.expect (fun t => u t ⬝ᵥ u t) := by field_simp
    linarith
  have t5 := mul_le_mul_of_nonneg_left t4 hr
  have t6 : r * k * (lam.expect (fun t => u t ⬝ᵥ u t) + ‖v‖ ^ 2) ≤ r * k * ‖x‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hnorm (mul_nonneg hr hk.le)
  have e3 : 2 * Real.sqrt κ₀ * r * Bq y v = r * (2 * Real.sqrt κ₀ * Bq y v) := by ring
  have e4 : 2 * Real.sqrt κ₀ * r * -(Real.sqrt gq * ‖v‖) =
      -(r * (2 * Real.sqrt κ₀ * (Real.sqrt gq * ‖v‖))) := by ring
  rw [e4] at t1
  nlinarith [t1, t2, t3, t5, t6]

variable {Ω : Type*} [Fintype Ω]

/-- **`lem:joint-potential`**: the conclusion of `lem:joint-rows`(a) holds without
`eq:joint-gate`, with `r𝗄/I₀` in place of `κ₀r𝗄/I₀`:
`𝔨 = e^{ℓ_E}[(r𝗄 + κ₀r(e_F + e_E))/I₀ + 𝔠_F + 𝔠_E]`. Here `𝕋 = ℙ + 𝕋_mean` with
`‖𝕋_mean‖ ≤ κ₀r(e_F + e_E)` (`prop:conditional-star`(b),(c)), and `ℙ ⪰ -r𝗄I` is
`pure_part_potential` (passed as `hP`). -/
theorem joint_potential {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ ν : FiniteLaw Ω) (g : Ω → ℝ) (ℓ : ℝ)
    (hν : ∀ x, ν.weight x = g x * μ.weight x) (hg : ∀ x, μ.weight x ≠ 0 → Real.exp (-ℓ) ≤ g x)
    (KE KF KstE KstF TnsE TnsF TcollE TcollF : Ω → Ω → ℝ)
    (hg1 : ∀ x, μ.weight x ≠ 0 → g x = RowsA.dens1 μ KE x)
    (hg2 : ∀ x, μ.weight x ≠ 0 → g x = RowsA.dens2 μ KE x)
    (hexpE : ∀ x y, μ.weight x ≠ 0 → μ.weight y ≠ 0 →
      KE x y = 1 + KstE x y + TnsE x y - TcollE x y)
    (hexpF : ∀ x y, μ.weight x ≠ 0 → μ.weight y ≠ 0 →
      KF x y = 1 + KstF x y + TnsF x y - TcollF x y)
    {εE SE NE nE nE' mE εF SF NF nF nF' mF : ℝ}
    (hεE : |RowsA.mass μ KE - 1| ≤ εE) (hεE1 : εE < 1) (hSE0 : 0 ≤ SE)
    (hSE : PerpBound μ KstE SE) (hnsE : FormBound μ TnsE nE) (hcollE : FormBound μ TcollE nE')
    (hNE : nE + nE' ≤ NE)
    (hmE1 : nrm μ (cen μ (kone μ KE)) ≤ mE) (hmE2 : nrm μ (cen μ (kone' μ KE)) ≤ mE)
    (hεF : |RowsA.mass μ KF - 1| ≤ εF) (hεF1 : εF < 1) (hSF0 : 0 ≤ SF)
    (hSF : PerpBound μ KstF SF) (hnsF : FormBound μ TnsF nF) (hcollF : FormBound μ TcollF nF')
    (hNF : nF + nF' ≤ NF)
    (hmF1 : nrm μ (cen μ (kone μ KF)) ≤ mF) (hmF2 : nrm μ (cen μ (kone' μ KF)) ≤ mF)
    (qT qPure qmean : E → ℝ) (ι : (Ω → ℝ) → (Ω → ℝ) → E) {P I₀ κ₀ r k eF eE : ℝ}
    (hrestr : ∀ Φ Ψ : Ω → ℝ, μ.expect Φ = 0 → μ.expect Ψ = 0 →
      RowsA.stForm μ KstE KstF Φ Ψ = qT (ι Φ Ψ) / P ∧
        ‖ι Φ Ψ‖ ^ 2 = nrm μ Φ ^ 2 + nrm μ Ψ ^ 2)
    (hI₀ : 0 < I₀) (hP : I₀ ≤ P) (hκ₀ : 0 ≤ κ₀) (hr : 0 ≤ r) (hk : 0 ≤ k) (heF : 0 ≤ eF)
    (heE : 0 ≤ eE)
    (hdec : ∀ x, qT x = qPure x + qmean x)
    (hmean : ∀ x, |qmean x| ≤ κ₀ * r * (eF + eE) * ‖x‖ ^ 2)
    (hPure : ∀ x, -(r * k) * ‖x‖ ^ 2 ≤ qPure x) :
    JointBlockLower ν (matchCov (RowsA.relDensity μ KE g)) (foldCov ν (RowsA.relDensity μ KF g))
      (Real.exp ℓ * ((r * k + κ₀ * r * (eF + eE)) / I₀ + RowsA.cconst εF SF NF mF +
        RowsA.cconst εE SE NE mE)) := by
  have hT : ∀ x, -(r * k + κ₀ * r * (eF + eE)) * ‖x‖ ^ 2 ≤ qT x := by
    intro x
    rw [hdec]
    have h1 := hPure x
    have h2 := neg_abs_le (qmean x)
    have h3 := hmean x
    nlinarith
  exact RowsA.joint_rows_chain μ ν g ℓ hν hg KE KF KstE KstF TnsE TnsF TcollE TcollF hg1 hg2
    hexpE hexpF hεE hεE1 hSE0 hSE hnsE hcollE hNE hmE1 hmE2 hεF hεF1 hSF0 hSF hnsF hcollF hNF
    hmF1 hmF2 qT ι hrestr hI₀ hP (by positivity) hT

end Potential

end Sarkozy.JointRows
