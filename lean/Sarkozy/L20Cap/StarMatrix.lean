module

public import Sarkozy.SpectralD.StarMatrixNorm
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

@[expose] public section

/-!
# The complete stars of L20, (a): the star matrix `M(i)` (`lem:l20-star-matrix`(a))

`paper/sections/20_middle_reference.tex`, `subsec:middle-l20`, `eq:l20-cross-matrix` and
`lem:l20-star-matrix`(a). The half `x = (a₀, a₁, b₀, b₁, c₀, c₁)` of the cut L20 has the
coordinates `0, …, 5` in this order; the core is `0, 1, 4, 5` and the pair is `2, 3`.

* `D20`: the signed cross matrix `D_20` of `eq:l20-cross-matrix` (rows: coordinates of `x`,
  columns: coordinates of `x'`), with integer copy `D20Z`. `D20_eq`: `D_ij = s_i a_j − a_i s_j`
  with the core signs `s = (−1, −1, 0, 0, 1, 1)` (`sZ`) and the pair indicator `a` (`aZ`).
  `D20_antisymm`: `D_20` is antisymmetric, so S1's `softM_hermitian` applies
  (`softM_D20_hermitian`).
* **The twelve supports** (`D20_active_iff`, `twelve_eq`, `twelve_card`): a set `S` with at least
  two elements carries a nonzero left- or right-star coefficient of the soft kernel
  (`softL D20 i S = ∏_{j∈S} D_ij`, `softR D20 S j = ∏_{i∈S} D_ij`) exactly when `S` is one of
  the twelve sets `01, 014, 0145, 015, 04, 045, 05, 14, 145, 15, 23, 45`, the subsets with at least
  two elements of the row supports `{2,3}` and `{0,1,4,5}`.
* **The rank-four decomposition** (`softM_D20_eq`): on the index set `U ⊔ 𝒮` of S1's `softM`
  (the six singletons and all `57` sets with at least two elements; the `45` sets outside the
  twelve give zero rows and columns),
  `M(i) = A Z^* + Z A^* + W E^* + E W^*` with
  `A = e₂ + e₃ = √2 v̂`, `Z = ∑_S σ_S e_S − 2i û = √15 ẑ` (`û = (e₀ + e₁ − e₄ − e₅)/2`,
  `σ_S = ∏_{k∈S} s_k`, the sum over the eleven supports inside `{0,1,4,5}`),
  `W = e₀ + e₁ + e₄ + e₅ = 2ŵ` and `E = e_{23} = ê`. This is the paper's
  `M(i) = √30 (v̂ẑ^* + ẑv̂^*) + 2(ŵê^* + êŵ^*)`. The four vectors are pairwise orthogonal with
  `|A|² = 2`, `|Z|² = 15`, `|W|² = 4`, `|E|² = 1` (`vecs_orth`).
* **The norm** (`normLe_softM_D20`): `‖M(i)‖ ≤ √30` in WP-K's bilinear form `NormLe`, the input
  `hM` of S1's `softStar_norm_le` for `D = D_20`. The route is the paper's: the rank-four form
  of the bilinear form (`bform_softM_D20`), Bessel's inequality for the orthogonal family
  (`bessel_orth`, `bessel_vecs`) and the Cauchy–Schwarz inequality (`rank4_bound`).
* **The spectrum** (`softM_D20_mulVec_vz`, `softM_D20_mulVec_we`, `softM_D20_mulVec_perp`):
  `M(i)` has the eigenvectors `√15 A ± √2 Z` (eigenvalues `±√30`) and `W ± 2E` (eigenvalues
  `±2`), and annihilates every vector orthogonal to `A, Z, W, E`. Hence `‖M(i)‖ = √30`
  (`sqrt30_le_of_normLe`: no smaller bound holds).
* **The characteristic polynomial** (`charpoly_M18`): on the eighteen coordinates (the six
  singletons and the twelve supports; `M18`, the restriction of `softM D20`),
  `det(λI − M(i)) = λ^{14}(λ² − 4)(λ² − 30)`. Proof: `M18 = P Q` with `P = [A, Z, W, E]` and
  `Q = [Z^*; A^*; E^*; W^*]` (`M18_eq`), `Q P = (0 15; 2 0) ⊕ (0 1; 4 0)` (`Q18_mul_P18`) and
  Mathlib's `charpoly_mul_comm_of_le`. The `45` other supports give zero rows and columns
  (`softM_D20_inactive`).
* **`cor:star-matrix` for `D_20`** (`softStar_D20_norm_le`): S1's `softStar_norm_le` with
  `‖M(i)‖ ≤ √30`, i.e. the coefficient `√30 ‖𝓕‖²` of `r`; the synthesis bound `‖𝓕‖² ≤ Γ_20` of
  `lem:l20-star-matrix`(b) stays a hypothesis.

Proved here: all of `lem:l20-star-matrix`(a) (the twelve supports, the characteristic
polynomial, `‖M(i)‖ = √30`), and the rank-four decomposition of `M(i)` used in the proof of
`eq:l20-rank4-operator`. Not in this file: parts (b) and (c) of the lemma (the synthesis bound
`Γ_20`, the identities for `𝖪`, and the identification of the synthesis of the four vectors with
the features `𝐯, 𝐳, 𝐰, 𝐞`, which turns this decomposition into `eq:l20-rank4-operator`).
-/

namespace Sarkozy.L20Cap

open Finset Complex Sarkozy.SpectralC Sarkozy.SpectralD.StarMatrix
open scoped BigOperators ComplexConjugate

/-! ## The signed cross matrix `D_20` -/

/-- The core signs `s = (s₀, s₁, s₄, s₅) = (−1, −1, 1, 1)`, extended by `0` on the pair
coordinates `2, 3`. -/
def sZ : Fin 6 → ℤ := ![-1, -1, 0, 0, 1, 1]

/-- The indicator of the pair coordinates `2, 3`. -/
def aZ : Fin 6 → ℤ := ![0, 0, 1, 1, 0, 0]

/-- The indicator of the core coordinates `0, 1, 4, 5`. -/
def wZ : Fin 6 → ℤ := ![1, 1, 0, 0, 1, 1]

/-- `D_20` with integer entries (`eq:l20-cross-matrix`). -/
def D20Z : Fin 6 → Fin 6 → ℤ :=
  ![![0, 0, -1, -1, 0, 0], ![0, 0, -1, -1, 0, 0], ![1, 1, 0, 0, -1, -1],
    ![1, 1, 0, 0, -1, -1], ![0, 0, 1, 1, 0, 0], ![0, 0, 1, 1, 0, 0]]

/-- **The signed cross matrix `D_20`** of `eq:l20-cross-matrix` (`lem:l20-star-matrix`): rows
indexed by the coordinates `a₀, a₁, b₀, b₁, c₀, c₁` of `x`, columns by those of `x'`; an edge
`y → y'` means `χ(y' − y) = 1`. -/
noncomputable def D20 (i j : Fin 6) : ℝ := (D20Z i j : ℝ)

theorem D20Z_eq : ∀ i j, D20Z i j = sZ i * aZ j - aZ i * sZ j := by decide

/-- `D_ij = s_i a_j − a_i s_j`: the core rows have the support `{2, 3}`, the pair rows the
support `{0, 1, 4, 5}`. -/
theorem D20_eq (i j : Fin 6) : D20 i j = (sZ i : ℝ) * aZ j - (aZ i : ℝ) * sZ j := by
  unfold D20
  rw [D20Z_eq]
  push_cast
  ring

theorem D20Z_antisymm : ∀ i j, D20Z j i = -D20Z i j := by decide

/-- **`D_20` is antisymmetric** (`lem:l20-star-matrix`, before (a)). -/
theorem D20_antisymm (i j : Fin 6) : D20 j i = -D20 i j := by
  unfold D20
  rw [D20Z_antisymm]
  push_cast
  ring

/-- **`M(i)` is Hermitian** (the remark after `cor:star-matrix`, for `D = D_20`). -/
theorem softM_D20_hermitian (a b : Feat (Fin 6) (supports (Fin 6))) :
    conj (softM D20 b a) = softM D20 a b :=
  softM_hermitian D20 D20_antisymm a b

/-! ## The twelve supports -/

/-- The twelve leaf supports of `lem:l20-star-matrix`(a): the subsets with at least two elements
of the row supports `{2, 3}` and `{0, 1, 4, 5}` of `D_20`. -/
def twelve : Finset (Finset (Fin 6)) :=
  ((({2, 3} : Finset (Fin 6)).powerset ∪ ({0, 1, 4, 5} : Finset (Fin 6)).powerset).filter
    (fun S => 2 ≤ S.card))

theorem twelve_card : twelve.card = 12 := by decide

/-- The twelve sets `01, 014, 0145, 015, 04, 045, 05, 14, 145, 15, 23, 45`. -/
theorem twelve_eq : twelve = {{0, 1}, {0, 1, 4}, {0, 1, 4, 5}, {0, 1, 5}, {0, 4}, {0, 4, 5},
    {0, 5}, {1, 4}, {1, 4, 5}, {1, 5}, {2, 3}, {4, 5}} := by decide

theorem twelve_subset_supports : twelve ⊆ supports (Fin 6) := by decide

theorem D20Z_active_iff : ∀ S : Finset (Fin 6), 2 ≤ S.card →
    (((∃ i, ∏ j ∈ S, D20Z i j ≠ 0) ∨ (∃ j, ∏ i ∈ S, D20Z i j ≠ 0)) ↔ S ∈ twelve) := by
  decide

theorem softL_D20 (i : Fin 6) (S : Finset (Fin 6)) :
    softL D20 i S = ((∏ j ∈ S, D20Z i j : ℤ) : ℝ) := by
  unfold softL D20
  push_cast
  rfl

theorem softR_D20 (S : Finset (Fin 6)) (j : Fin 6) :
    softR D20 S j = ((∏ i ∈ S, D20Z i j : ℤ) : ℝ) := by
  unfold softR D20
  push_cast
  rfl

/-- **The twelve supports** (`lem:l20-star-matrix`(a)): a set `S` with at least two elements is
the leaf set of a star of the soft L20 kernel with nonzero coefficient (`∏_{j∈S} D_ij ≠ 0` for
some centre `i`, or `∏_{i∈S} D_ij ≠ 0` for some centre `j`) if and only if it is one of the
twelve sets. -/
theorem D20_active_iff (S : Finset (Fin 6)) (hS : S ∈ supports (Fin 6)) :
    ((∃ i, softL D20 i S ≠ 0) ∨ (∃ j, softR D20 S j ≠ 0)) ↔ S ∈ twelve := by
  have h2 : 2 ≤ S.card := by
    unfold supports at hS
    exact (Finset.mem_filter.mp hS).2
  rw [← D20Z_active_iff S h2]
  simp only [softL_D20, softR_D20, ne_eq, Int.cast_eq_zero]

/-! ## The rank-four decomposition -/

/-- The index set `U ⊔ 𝒮` of S1's star matrix for `U = Fin 6`: the six singletons and the
supports (all sets with at least two elements). -/
abbrev Idx := Feat (Fin 6) (supports (Fin 6))

/-- A vector of `ℂ^{U ⊔ 𝒮}` with Gaussian-integer entries `xr_k + i xi_k` at the singletons and
integer entries `xs_S` at the supports. -/
noncomputable def mkVec (xr xi : Fin 6 → ℤ) (xs : Finset (Fin 6) → ℤ) : Idx → ℂ :=
  Sum.elim (fun i => (xr i : ℂ) + I * (xi i : ℂ)) (fun S => (xs S.1 : ℂ))

/-- `A = e₂ + e₃` (`= √2 v̂`). -/
noncomputable def vA : Idx → ℂ := mkVec aZ 0 0

/-- `Z = ∑_S σ_S e_S − 2i û` (`= √15 ẑ`): `i s_k` at the singleton `k`, `σ_S = ∏_{k∈S} s_k` at
the support `S` (zero unless `S ⊆ {0, 1, 4, 5}`). -/
noncomputable def vZ : Idx → ℂ := mkVec 0 sZ (fun S => ∏ k ∈ S, sZ k)

/-- `W = e₀ + e₁ + e₄ + e₅` (`= 2ŵ`). -/
noncomputable def vW : Idx → ℂ := mkVec wZ 0 0

/-- `E = e_{23}` (`= ê`). -/
noncomputable def vE : Idx → ℂ := mkVec 0 0 (fun S => if S = {2, 3} then 1 else 0)

theorem D20Z_left : ∀ (i : Fin 6) (S : Finset (Fin 6)), 2 ≤ S.card →
    (-1) ^ S.card * ∏ j ∈ S, D20Z i j =
      aZ i * ∏ k ∈ S, sZ k + wZ i * (if S = {2, 3} then 1 else 0) := by
  decide

theorem D20Z_right : ∀ (j : Fin 6) (S : Finset (Fin 6)), 2 ≤ S.card →
    ∏ i ∈ S, D20Z i j = (∏ k ∈ S, sZ k) * aZ j + (if S = {2, 3} then 1 else 0) * wZ j := by
  decide

theorem two_le_card_of_mem {S : Finset (Fin 6)} (hS : S ∈ supports (Fin 6)) : 2 ≤ S.card := by
  unfold supports at hS
  exact (Finset.mem_filter.mp hS).2

/-- **The rank-four decomposition of `M(i)`** (`lem:l20-star-matrix`(a), proof):
`M(i) = A Z^* + Z A^* + W E^* + E W^*`, i.e.
`M(i) = √30 (v̂ẑ^* + ẑv̂^*) + 2(ŵê^* + êŵ^*)`. -/
theorem softM_D20_eq (a b : Idx) :
    softM D20 a b = vA a * conj (vZ b) + vZ a * conj (vA b) + vW a * conj (vE b) +
      vE a * conj (vW b) := by
  rcases a with i | S <;> rcases b with j | T
  · have hc : (D20Z i j : ℂ) = (sZ i : ℂ) * aZ j - (aZ i : ℂ) * sZ j := by
      exact_mod_cast D20Z_eq i j
    simp only [softM, matI, starM0, starM1, vA, vZ, vW, vE, mkVec, Sum.elim_inl, D20,
      Complex.ofReal_intCast, Complex.ofReal_zero, map_mul, Complex.conj_I,
      map_intCast, Pi.zero_apply, Int.cast_zero, mul_zero, add_zero, zero_add, map_zero]
    linear_combination I * hc
  · have hc := congrArg (fun n : ℤ => (n : ℂ)) (D20Z_left i T.1 (two_le_card_of_mem T.2))
    simp only [softM, matI, starM0, starM1, vA, vZ, vW, vE, mkVec, Sum.elim_inl, Sum.elim_inr,
      softL_D20, map_intCast, Pi.zero_apply, Int.cast_zero,
      mul_zero, add_zero, zero_add, map_zero, Complex.ofReal_zero] at hc ⊢
    push_cast at hc ⊢
    linear_combination hc
  · have hc := congrArg (fun n : ℤ => (n : ℂ)) (D20Z_right j S.1 (two_le_card_of_mem S.2))
    simp only [softM, matI, starM0, starM1, vA, vZ, vW, vE, mkVec, Sum.elim_inl, Sum.elim_inr,
      softR_D20, map_mul, Complex.conj_I, map_intCast, Pi.zero_apply, Int.cast_zero,
      mul_zero, add_zero, zero_add, map_zero, zero_mul, Complex.ofReal_zero] at hc ⊢
    push_cast at hc ⊢
    linear_combination hc
  · simp [softM, matI, starM0, starM1, vA, vZ, vW, vE, mkVec]

/-! ## The bilinear form in rank-four form -/

/-- `⟨X, w⟩ = ∑_k \overline{X_k} w_k`. -/
noncomputable def cip {ι : Type*} [Fintype ι] (X w : ι → ℂ) : ℂ := ∑ k, conj (X k) * w k

theorem bform_rank_one {ι : Type*} [Fintype ι] (X Y w z : ι → ℂ) :
    ∑ k, ∑ l, conj (w k) * (X k * conj (Y l)) * z l = conj (cip X w) * cip Y z := by
  unfold cip
  rw [map_sum, Finset.sum_mul_sum]
  refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
  simp only [map_mul, Complex.conj_conj]
  ring

/-- The bilinear form of `M(i)`:
`w^* M(i) z = \overline{⟨A,w⟩}⟨Z,z⟩ + \overline{⟨Z,w⟩}⟨A,z⟩ + \overline{⟨W,w⟩}⟨E,z⟩ +
\overline{⟨E,w⟩}⟨W,z⟩`. -/
theorem bform_softM_D20 (w z : Idx → ℂ) :
    bform (softM D20) w z = conj (cip vA w) * cip vZ z + conj (cip vZ w) * cip vA z +
      conj (cip vW w) * cip vE z + conj (cip vE w) * cip vW z := by
  unfold bform
  simp_rw [softM_D20_eq]
  rw [← bform_rank_one vA vZ w z, ← bform_rank_one vZ vA w z, ← bform_rank_one vW vE w z,
    ← bform_rank_one vE vW w z]
  simp only [← sum_add_distrib]
  refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
  ring

/-! ## Bessel's inequality for an orthogonal family -/

/-- **Bessel's inequality** for a finite orthogonal family `X_i` in `ℂ^ι` with `|X_i|² = n_i > 0`:
`∑_i |⟨X_i, w⟩|²/n_i ≤ |w|²`. -/
theorem bessel_orth {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] (X : κ → ι → ℂ)
    (n : κ → ℝ) (hn : ∀ i, 0 < n i)
    (horth : ∀ i j, cip (X i) (X j) = if i = j then (n i : ℂ) else 0) (w : ι → ℂ) :
    ∑ i, ‖cip (X i) w‖ ^ 2 / n i ≤ ∑ k, ‖w k‖ ^ 2 := by
  set c : κ → ℝ := fun i => (Real.sqrt (n i))⁻¹ with hc
  have hc2 : ∀ i, c i * c i * n i = 1 := by
    intro i
    simp only [hc]
    have h0 : 0 < Real.sqrt (n i) := Real.sqrt_pos.mpr (hn i)
    have h1 : Real.sqrt (n i) * Real.sqrt (n i) = n i := Real.mul_self_sqrt (hn i).le
    field_simp
    linarith
  let v : κ → EuclideanSpace ℂ ι := fun i => WithLp.toLp 2 (fun k => (c i : ℂ) * X i k)
  have hinner : ∀ i (y : ι → ℂ), inner ℂ (v i) (WithLp.toLp 2 y) = (c i : ℂ) * cip (X i) y := by
    intro i y
    rw [PiLp.inner_apply]
    simp only [v, RCLike.inner_apply, cip, Finset.mul_sum]
    refine sum_congr rfl fun k _ => ?_
    simp only [map_mul, Complex.conj_ofReal]
    ring
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    have e : v j = WithLp.toLp 2 (fun k => (c j : ℂ) * X j k) := rfl
    rw [e, hinner]
    have hcip : cip (X i) (fun k => (c j : ℂ) * X j k) = (c j : ℂ) * cip (X i) (X j) := by
      unfold cip
      rw [Finset.mul_sum]
      exact sum_congr rfl fun k _ => by ring
    rw [hcip, horth]
    split_ifs with h
    · subst h
      have := hc2 i
      rw [← mul_assoc]
      exact_mod_cast this
    · simp
  have hb := hv.sum_inner_products_le (s := univ) (WithLp.toLp 2 w)
  rw [EuclideanSpace.norm_sq_eq] at hb
  calc ∑ i, ‖cip (X i) w‖ ^ 2 / n i = ∑ i, ‖inner ℂ (v i) (WithLp.toLp 2 w)‖ ^ 2 := by
        refine sum_congr rfl fun i _ => ?_
        rw [hinner, norm_mul, Complex.norm_real, mul_pow, Real.norm_eq_abs, sq_abs]
        have hni : n i ≠ 0 := (hn i).ne'
        have := hc2 i
        field_simp
        nlinarith [this]
    _ ≤ ∑ k, ‖w k‖ ^ 2 := hb

/-! ## The orthogonality of `A, Z, W, E` -/

/-- `⟨X, Y⟩` for two vectors with integer data:
`∑_k (xr_k yr_k + xi_k yi_k) + ∑_S xs_S ys_S + i ∑_k (xr_k yi_k − xi_k yr_k)`. -/
theorem cip_mkVec (xr xi : Fin 6 → ℤ) (xs : Finset (Fin 6) → ℤ) (yr yi : Fin 6 → ℤ)
    (ys : Finset (Fin 6) → ℤ) :
    cip (mkVec xr xi xs) (mkVec yr yi ys) =
      ((∑ i, (xr i * yr i + xi i * yi i) + ∑ S ∈ supports (Fin 6), xs S * ys S : ℤ) : ℂ) +
        I * ((∑ i, (xr i * yi i - xi i * yr i) : ℤ) : ℂ) := by
  unfold cip
  rw [Fintype.sum_sum_type]
  simp only [mkVec, Sum.elim_inl, Sum.elim_inr, map_add, map_mul, map_intCast, Complex.conj_I]
  have h1 : ∀ i, ((xr i : ℂ) + -I * (xi i : ℂ)) * ((yr i : ℂ) + I * (yi i : ℂ)) =
      ((xr i * yr i + xi i * yi i : ℤ) : ℂ) + I * ((xr i * yi i - xi i * yr i : ℤ) : ℂ) := by
    intro i
    push_cast
    linear_combination (-(xi i : ℂ) * (yi i : ℂ)) * Complex.I_sq
  have h2 : ∑ S : {S // S ∈ supports (Fin 6)}, (xs S.1 : ℂ) * (ys S.1 : ℂ) =
      ((∑ S ∈ supports (Fin 6), xs S * ys S : ℤ) : ℂ) := by
    push_cast
    exact Finset.sum_coe_sort (supports (Fin 6)) (fun S => (xs S : ℂ) * (ys S : ℂ))
  rw [sum_congr rfl fun i _ => h1 i, sum_add_distrib, ← Finset.mul_sum, h2]
  push_cast
  ring

/-- The four vectors `A, Z, W, E`. -/
noncomputable def vecs : Fin 4 → Idx → ℂ := ![vA, vZ, vW, vE]

/-- The singleton real parts of `A, Z, W, E`. -/
def vecR : Fin 4 → Fin 6 → ℤ := ![aZ, 0, wZ, 0]

/-- The singleton imaginary parts of `A, Z, W, E`. -/
def vecI : Fin 4 → Fin 6 → ℤ := ![0, sZ, 0, 0]

/-- The support parts of `A, Z, W, E`. -/
def vecS : Fin 4 → Finset (Fin 6) → ℤ :=
  ![0, fun S => ∏ k ∈ S, sZ k, 0, fun S => if S = {2, 3} then 1 else 0]

/-- The squared lengths `2, 15, 4, 1` of `A, Z, W, E`. -/
def lensZ : Fin 4 → ℤ := ![2, 15, 4, 1]

/-- The squared lengths as reals. -/
noncomputable def lens (a : Fin 4) : ℝ := (lensZ a : ℝ)

theorem vecs_eq (a : Fin 4) : vecs a = mkVec (vecR a) (vecI a) (vecS a) := by
  fin_cases a <;> rfl

theorem orth_int : ∀ a b : Fin 4,
    (∑ i, (vecR a i * vecR b i + vecI a i * vecI b i) +
        ∑ S ∈ supports (Fin 6), vecS a S * vecS b S = if a = b then lensZ a else 0) ∧
      ∑ i, (vecR a i * vecI b i - vecI a i * vecR b i) = 0 := by
  decide

theorem lens_pos (a : Fin 4) : 0 < lens a := by
  have h : 0 < lensZ a := by fin_cases a <;> decide
  unfold lens
  exact_mod_cast h

/-- **`A, Z, W, E` are pairwise orthogonal** with `|A|² = 2`, `|Z|² = 15`, `|W|² = 4`,
`|E|² = 1` (`lem:l20-star-matrix`(a), proof: `v̂, ẑ, ŵ, ê` are orthonormal). -/
theorem vecs_orth (a b : Fin 4) :
    cip (vecs a) (vecs b) = if a = b then (lens a : ℂ) else 0 := by
  rw [vecs_eq, vecs_eq, cip_mkVec, (orth_int a b).1, (orth_int a b).2]
  unfold lens
  split_ifs <;> simp

/-- **Bessel's inequality for `A, Z, W, E`**:
`|⟨A,w⟩|²/2 + |⟨Z,w⟩|²/15 + |⟨W,w⟩|²/4 + |⟨E,w⟩|² ≤ |w|²`. -/
theorem bessel_vecs (w : Idx → ℂ) :
    ‖cip vA w‖ ^ 2 / 2 + ‖cip vZ w‖ ^ 2 / 15 + ‖cip vW w‖ ^ 2 / 4 + ‖cip vE w‖ ^ 2 ≤
      ∑ k, ‖w k‖ ^ 2 := by
  have h := bessel_orth vecs lens lens_pos vecs_orth w
  have e0 : vecs 0 = vA := rfl
  have e1 : vecs 1 = vZ := rfl
  have e2 : vecs 2 = vW := rfl
  have e3 : vecs 3 = vE := rfl
  have l0 : lens 0 = 2 := by norm_num [lens, lensZ]
  have l1 : lens 1 = 15 := by norm_num [lens, lensZ]
  have l2 : lens 2 = 4 := by norm_num [lens, lensZ]
  have l3 : lens 3 = 1 := by norm_num [lens, lensZ]
  rw [Fin.sum_univ_four, e0, e1, e2, e3, l0, l1, l2, l3, div_one] at h
  exact h

/-! ## The norm bound -/

/-- The real inequality behind the norm:
`(α_A β_Z + α_Z β_A + α_W β_E + α_E β_W)² ≤
 (α_A²/2 + α_Z²/15 + α_W²/4 + α_E²) · 30 (β_A²/2 + β_Z²/15 + β_W²/4 + β_E²)`
(Cauchy–Schwarz, with `2 ≤ √30`); it holds for all real numbers. -/
theorem rank4_bound (aA aZ' aW aE bA bZ bW bE : ℝ) :
    (aA * bZ + aZ' * bA + aW * bE + aE * bW) ^ 2 ≤
      (aA ^ 2 / 2 + aZ' ^ 2 / 15 + aW ^ 2 / 4 + aE ^ 2) *
        (30 * (bA ^ 2 / 2 + bZ ^ 2 / 15 + bW ^ 2 / 4 + bE ^ 2)) := by
  -- Cauchy–Schwarz with the second factor `2 bZ² + 15 bA² + 4 bE² + bW²`
  have hCS : (aA * bZ + aZ' * bA + aW * bE + aE * bW) ^ 2 ≤
      (aA ^ 2 / 2 + aZ' ^ 2 / 15 + aW ^ 2 / 4 + aE ^ 2) *
        (2 * bZ ^ 2 + 15 * bA ^ 2 + 4 * bE ^ 2 + bW ^ 2) := by
    have e : (aA ^ 2 / 2 + aZ' ^ 2 / 15 + aW ^ 2 / 4 + aE ^ 2) *
        (2 * bZ ^ 2 + 15 * bA ^ 2 + 4 * bE ^ 2 + bW ^ 2) -
          (aA * bZ + aZ' * bA + aW * bE + aE * bW) ^ 2 =
        (15 * aA * bA - 2 * aZ' * bZ) ^ 2 / 30 + (2 * aA * bE - aW * bZ) ^ 2 / 2 +
          (aA * bW - 2 * aE * bZ) ^ 2 / 2 + (4 * aZ' * bE - 15 * aW * bA) ^ 2 / 60 +
          (aZ' * bW - 15 * aE * bA) ^ 2 / 15 + (aW * bW - 4 * aE * bE) ^ 2 / 4 := by
      ring
    nlinarith [sq_nonneg (15 * aA * bA - 2 * aZ' * bZ), sq_nonneg (2 * aA * bE - aW * bZ),
      sq_nonneg (aA * bW - 2 * aE * bZ), sq_nonneg (4 * aZ' * bE - 15 * aW * bA),
      sq_nonneg (aZ' * bW - 15 * aE * bA), sq_nonneg (aW * bW - 4 * aE * bE)]
  have hP : 0 ≤ aA ^ 2 / 2 + aZ' ^ 2 / 15 + aW ^ 2 / 4 + aE ^ 2 := by positivity
  have hQ : 2 * bZ ^ 2 + 15 * bA ^ 2 + 4 * bE ^ 2 + bW ^ 2 ≤
      30 * (bA ^ 2 / 2 + bZ ^ 2 / 15 + bW ^ 2 / 4 + bE ^ 2) := by
    nlinarith [sq_nonneg bW, sq_nonneg bE]
  calc _ ≤ _ := hCS
    _ ≤ _ := mul_le_mul_of_nonneg_left hQ hP

/-- **`‖M(i)‖ ≤ √30`** (`lem:l20-star-matrix`(a), "in particular `‖M(i)‖ = √30`", the upper
bound) for the star matrix of the soft L20 kernel, in WP-K's bilinear form `NormLe`: this is
the hypothesis `hM` of S1's `softStar_norm_le` for `D = D_20`. -/
theorem normLe_softM_D20 : NormLe (softM D20) (Real.sqrt 30) := by
  intro w z
  rw [bform_softM_D20]
  have e1 := norm_add_le (conj (cip vA w) * cip vZ z + conj (cip vZ w) * cip vA z +
    conj (cip vW w) * cip vE z) (conj (cip vE w) * cip vW z)
  have e2 := norm_add_le (conj (cip vA w) * cip vZ z + conj (cip vZ w) * cip vA z)
    (conj (cip vW w) * cip vE z)
  have e3 := norm_add_le (conj (cip vA w) * cip vZ z) (conj (cip vZ w) * cip vA z)
  simp only [norm_mul, Complex.norm_conj] at e1 e2 e3
  have hw := bessel_vecs w
  have hz := bessel_vecs z
  have h4 := rank4_bound ‖cip vA w‖ ‖cip vZ w‖ ‖cip vW w‖ ‖cip vE w‖ ‖cip vA z‖ ‖cip vZ z‖
    ‖cip vW z‖ ‖cip vE z‖
  have hW0 : 0 ≤ ∑ k, ‖w k‖ ^ 2 := sum_nonneg fun k _ => sq_nonneg _
  have hZ0 : 0 ≤ ∑ k, ‖z k‖ ^ 2 := sum_nonneg fun k _ => sq_nonneg _
  have hP0 : 0 ≤ ‖cip vA w‖ ^ 2 / 2 + ‖cip vZ w‖ ^ 2 / 15 + ‖cip vW w‖ ^ 2 / 4 +
      ‖cip vE w‖ ^ 2 := by positivity
  have hQ0 : 0 ≤ ‖cip vA z‖ ^ 2 / 2 + ‖cip vZ z‖ ^ 2 / 15 + ‖cip vW z‖ ^ 2 / 4 +
      ‖cip vE z‖ ^ 2 := by positivity
  set S := ‖cip vA w‖ * ‖cip vZ z‖ + ‖cip vZ w‖ * ‖cip vA z‖ + ‖cip vW w‖ * ‖cip vE z‖ +
    ‖cip vE w‖ * ‖cip vW z‖ with hS
  have hsq : S ^ 2 ≤ 30 * (∑ k, ‖w k‖ ^ 2) * (∑ k, ‖z k‖ ^ 2) := by
    calc S ^ 2 ≤ _ := h4
      _ ≤ (∑ k, ‖w k‖ ^ 2) * (30 * (∑ k, ‖z k‖ ^ 2)) :=
          mul_le_mul hw (by linarith) (by positivity) hW0
      _ = _ := by ring
  have hle := Real.abs_le_sqrt hsq
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num)] at hle
  have htri : ‖conj (cip vA w) * cip vZ z + conj (cip vZ w) * cip vA z +
      conj (cip vW w) * cip vE z + conj (cip vE w) * cip vW z‖ ≤ S := by
    rw [hS]
    linarith
  calc _ ≤ S := htri
    _ ≤ |S| := le_abs_self _
    _ ≤ _ := hle
    _ = Real.sqrt 30 * vnorm w * vnorm z := by unfold vnorm; ring

/-! ## The spectrum of `M(i)` -/

theorem cip_lin {ι : Type*} [Fintype ι] (X Y Y' : ι → ℂ) (c d : ℂ) :
    cip X (fun k => c * Y k + d * Y' k) = c * cip X Y + d * cip X Y' := by
  unfold cip
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact sum_congr rfl fun k _ => by ring

/-- The sixteen inner products of `A, Z, W, E`. -/
theorem cip_table :
    cip vA vA = 2 ∧ cip vA vZ = 0 ∧ cip vA vW = 0 ∧ cip vA vE = 0 ∧
    cip vZ vA = 0 ∧ cip vZ vZ = 15 ∧ cip vZ vW = 0 ∧ cip vZ vE = 0 ∧
    cip vW vA = 0 ∧ cip vW vZ = 0 ∧ cip vW vW = 4 ∧ cip vW vE = 0 ∧
    cip vE vA = 0 ∧ cip vE vZ = 0 ∧ cip vE vW = 0 ∧ cip vE vE = 1 := by
  have t : ∀ a b : Fin 4, cip (vecs a) (vecs b) = ((if a = b then lensZ a else 0 : ℤ) : ℂ) := by
    intro a b
    rw [vecs_orth]
    unfold lens
    split_ifs <;> simp
  refine ⟨(t 0 0).trans ?_, (t 0 1).trans ?_, (t 0 2).trans ?_, (t 0 3).trans ?_,
    (t 1 0).trans ?_, (t 1 1).trans ?_, (t 1 2).trans ?_, (t 1 3).trans ?_,
    (t 2 0).trans ?_, (t 2 1).trans ?_, (t 2 2).trans ?_, (t 2 3).trans ?_,
    (t 3 0).trans ?_, (t 3 1).trans ?_, (t 3 2).trans ?_, (t 3 3).trans ?_⟩ <;>
    norm_num [lensZ]

/-- **`M(i)` in rank-four form, acting on a vector**:
`M(i) x = A ⟨Z, x⟩ + Z ⟨A, x⟩ + W ⟨E, x⟩ + E ⟨W, x⟩`. -/
theorem mulVec_softM_D20 (x : Idx → ℂ) (k : Idx) :
    ∑ l, softM D20 k l * x l =
      vA k * cip vZ x + vZ k * cip vA x + vW k * cip vE x + vE k * cip vW x := by
  simp_rw [softM_D20_eq]
  unfold cip
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]

theorem sqrt30_eq : Real.sqrt 30 = Real.sqrt 2 * Real.sqrt 15 := by
  rw [← Real.sqrt_mul (by norm_num)]
  norm_num

/-- **The eigenvectors `√15 A ± √2 Z` of `M(i)`, eigenvalues `±√30`** (`lem:l20-star-matrix`(a):
`M(i)` has the eigenvalues `±√30` on the span of `v̂, ẑ`). Here `ε = ±1`. -/
theorem softM_D20_mulVec_vz (ε : ℂ) (hε : ε ^ 2 = 1) (k : Idx) :
    ∑ l, softM D20 k l * ((Real.sqrt 15 : ℂ) * vA l + (ε * (Real.sqrt 2 : ℂ)) * vZ l) =
      ε * (Real.sqrt 30 : ℂ) * ((Real.sqrt 15 : ℂ) * vA k + (ε * (Real.sqrt 2 : ℂ)) * vZ k) := by
  obtain ⟨hAA, -, -, -, hZA, hZZ, -, -, hWA, hWZ, -, -, hEA, hEZ, -, -⟩ := cip_table
  rw [mulVec_softM_D20, cip_lin, cip_lin, cip_lin, cip_lin, hAA, hZA, hZZ, hWA, hWZ, hEA, hEZ,
    cip_table.2.1]
  have h15 : (Real.sqrt 15 : ℂ) * (Real.sqrt 15 : ℂ) = 15 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have h2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have h30 : (Real.sqrt 30 : ℂ) = (Real.sqrt 2 : ℂ) * (Real.sqrt 15 : ℂ) := by
    rw [sqrt30_eq, Complex.ofReal_mul]
  rw [h30]
  linear_combination (-ε * (Real.sqrt 2 : ℂ) * vA k) * h15 +
    (-2 * (Real.sqrt 15 : ℂ) * vZ k) * hε + (-ε ^ 2 * (Real.sqrt 15 : ℂ) * vZ k) * h2

/-- **The eigenvectors `W ± 2E` of `M(i)`, eigenvalues `±2`** (`lem:l20-star-matrix`(a): `M(i)`
has the eigenvalues `±2` on the span of `ŵ, ê`). Here `ε = ±1`. -/
theorem softM_D20_mulVec_we (ε : ℂ) (hε : ε ^ 2 = 1) (k : Idx) :
    ∑ l, softM D20 k l * (1 * vW l + (2 * ε) * vE l) =
      2 * ε * (1 * vW k + (2 * ε) * vE k) := by
  obtain ⟨-, -, hAW, hAE, -, -, hZW, hZE, -, -, hWW, hWE, -, -, hEW, hEE⟩ := cip_table
  rw [mulVec_softM_D20, cip_lin, cip_lin, cip_lin, cip_lin, hAW, hAE, hZW, hZE, hWW, hWE, hEW,
    hEE]
  linear_combination (-4 * vE k) * hε

/-- **`M(i)` vanishes on the orthogonal complement of `A, Z, W, E`** (`lem:l20-star-matrix`(a):
the eigenvalue `0`, of multiplicity `14` on the eighteen relevant coordinates). -/
theorem softM_D20_mulVec_perp (x : Idx → ℂ) (hA : cip vA x = 0) (hZ : cip vZ x = 0)
    (hW : cip vW x = 0) (hE : cip vE x = 0) (k : Idx) : ∑ l, softM D20 k l * x l = 0 := by
  rw [mulVec_softM_D20, hA, hZ, hW, hE]
  ring

/-- `bform M w z = ∑_k \overline{w_k} (M z)_k`. -/
theorem bform_eq_sum_mulVec {ι : Type*} [Fintype ι] (M : ι → ι → ℂ) (w z : ι → ℂ) :
    bform M w z = ∑ k, conj (w k) * ∑ l, M k l * z l := by
  unfold bform
  refine sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  exact sum_congr rfl fun l _ => by ring

/-- **`‖M(i)‖ = √30`, the lower bound** (`lem:l20-star-matrix`(a), "in particular
`‖M(i)‖ = √30`"): no bound smaller than `√30` holds, since `x = √15 A + √2 Z` has
`x^* M(i) x = √30 |x|²`. With `normLe_softM_D20` this gives `‖M(i)‖ = √30`. -/
theorem sqrt30_le_of_normLe {lam : ℝ} (h : NormLe (softM D20) lam) : Real.sqrt 30 ≤ lam := by
  set x : Idx → ℂ := fun l => (Real.sqrt 15 : ℂ) * vA l + ((1 : ℂ) * (Real.sqrt 2 : ℂ)) * vZ l
    with hx
  have hMx : ∀ k, ∑ l, softM D20 k l * x l = 1 * (Real.sqrt 30 : ℂ) * x k :=
    softM_D20_mulVec_vz 1 (by norm_num)
  have hform : bform (softM D20) x x = (Real.sqrt 30 : ℂ) * cip x x := by
    rw [bform_eq_sum_mulVec]
    unfold cip
    rw [Finset.mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [hMx]
    ring
  obtain ⟨hAA, hAZ, -, -, hZA, hZZ, -, -⟩ := cip_table
  have hxx : cip x x = 60 := by
    have e : cip x x = conj (Real.sqrt 15 : ℂ) * (Real.sqrt 15 : ℂ) * cip vA vA +
        conj (Real.sqrt 15 : ℂ) * ((1 : ℂ) * (Real.sqrt 2 : ℂ)) * cip vA vZ +
        conj ((1 : ℂ) * (Real.sqrt 2 : ℂ)) * (Real.sqrt 15 : ℂ) * cip vZ vA +
        conj ((1 : ℂ) * (Real.sqrt 2 : ℂ)) * ((1 : ℂ) * (Real.sqrt 2 : ℂ)) * cip vZ vZ := by
      unfold cip
      simp only [hx, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine sum_congr rfl fun k _ => ?_
      simp only [map_add, map_mul]
      ring
    rw [e, hAA, hAZ, hZA, hZZ]
    simp only [Complex.conj_ofReal, one_mul]
    have h15 : (Real.sqrt 15 : ℂ) * (Real.sqrt 15 : ℂ) = 15 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
      norm_num
    have h2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
      norm_num
    linear_combination 2 * h15 + 15 * h2
  -- `|x|² = 60`
  have hsum : ∑ k, ‖x k‖ ^ 2 = 60 := by
    have e : ((∑ k, ‖x k‖ ^ 2 : ℝ) : ℂ) = cip x x := by
      unfold cip
      push_cast
      refine sum_congr rfl fun k _ => ?_
      rw [← Complex.mul_conj', mul_comm]
    rw [hxx] at e
    exact_mod_cast e
  have hv : vnorm x * vnorm x = 60 := by
    unfold vnorm
    rw [hsum, Real.mul_self_sqrt (by norm_num)]
  have hb := h x x
  rw [hform, hxx, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)] at hb
  have h60 : ‖(60 : ℂ)‖ = 60 := by norm_num
  rw [h60, mul_assoc, hv] at hb
  linarith

/-! ## The characteristic polynomial on the eighteen relevant coordinates -/

/-- The eighteen coordinates of `lem:l20-star-matrix`(a): the six singletons and the twelve
supports. -/
abbrev Idx18 := Fin 6 ⊕ {S : Finset (Fin 6) // S ∈ twelve}

/-- The inclusion of the eighteen coordinates into `U ⊔ 𝒮`. -/
def emb18 : Idx18 → Idx :=
  Sum.map id (fun S => ⟨S.1, twelve_subset_supports S.2⟩)

/-- **The `18 × 18` star matrix `M(i)` of the soft L20 kernel** (`lem:l20-star-matrix`(a)):
`softM D20` restricted to the six singletons and the twelve supports. -/
noncomputable def M18 : Matrix Idx18 Idx18 ℂ := Matrix.of fun a b => softM D20 (emb18 a) (emb18 b)

/-- The inner product over the eighteen coordinates. -/
noncomputable def cip18 (X Y : Idx → ℂ) : ℂ := ∑ k : Idx18, conj (X (emb18 k)) * Y (emb18 k)

theorem cip18_mkVec (xr xi : Fin 6 → ℤ) (xs : Finset (Fin 6) → ℤ) (yr yi : Fin 6 → ℤ)
    (ys : Finset (Fin 6) → ℤ) :
    cip18 (mkVec xr xi xs) (mkVec yr yi ys) =
      ((∑ i, (xr i * yr i + xi i * yi i) + ∑ S ∈ twelve, xs S * ys S : ℤ) : ℂ) +
        I * ((∑ i, (xr i * yi i - xi i * yr i) : ℤ) : ℂ) := by
  unfold cip18
  rw [Fintype.sum_sum_type]
  simp only [emb18, Sum.map_inl, Sum.map_inr, id, mkVec, Sum.elim_inl, Sum.elim_inr, map_add,
    map_mul, map_intCast, Complex.conj_I]
  have h1 : ∀ i, ((xr i : ℂ) + -I * (xi i : ℂ)) * ((yr i : ℂ) + I * (yi i : ℂ)) =
      ((xr i * yr i + xi i * yi i : ℤ) : ℂ) + I * ((xr i * yi i - xi i * yr i : ℤ) : ℂ) := by
    intro i
    push_cast
    linear_combination (-(xi i : ℂ) * (yi i : ℂ)) * Complex.I_sq
  have h2 : ∑ S : {S // S ∈ twelve}, (xs S.1 : ℂ) * (ys S.1 : ℂ) =
      ((∑ S ∈ twelve, xs S * ys S : ℤ) : ℂ) := by
    push_cast
    exact Finset.sum_coe_sort twelve (fun S => (xs S : ℂ) * (ys S : ℂ))
  rw [sum_congr rfl fun i _ => h1 i, sum_add_distrib, ← Finset.mul_sum, h2]
  push_cast
  ring

theorem orth_int18 : ∀ a b : Fin 4,
    (∑ i, (vecR a i * vecR b i + vecI a i * vecI b i) +
        ∑ S ∈ twelve, vecS a S * vecS b S = if a = b then lensZ a else 0) ∧
      ∑ i, (vecR a i * vecI b i - vecI a i * vecR b i) = 0 := by
  decide

theorem vecs_orth18 (a b : Fin 4) :
    cip18 (vecs a) (vecs b) = ((if a = b then lensZ a else 0 : ℤ) : ℂ) := by
  rw [vecs_eq, vecs_eq, cip18_mkVec, (orth_int18 a b).1, (orth_int18 a b).2]
  simp

/-- The left factor `P = [A, Z, W, E]` (columns indexed by `Fin 2 ⊕ Fin 2`). -/
noncomputable def P18 : Matrix Idx18 (Fin 2 ⊕ Fin 2) ℂ :=
  Matrix.of fun k i => Sum.elim ![vA, vZ] ![vW, vE] i (emb18 k)

/-- The right factor `Q = [Z^*; A^*; E^*; W^*]`. -/
noncomputable def Q18 : Matrix (Fin 2 ⊕ Fin 2) Idx18 ℂ :=
  Matrix.of fun i l => conj (Sum.elim ![vZ, vA] ![vE, vW] i (emb18 l))

theorem M18_eq : M18 = P18 * Q18 := by
  ext a b
  simp only [M18, P18, Q18, Matrix.of_apply, Matrix.mul_apply, Fintype.sum_sum_type,
    Fin.sum_univ_two, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
    softM_D20_eq]
  ring

/-- The `4 × 4` Gram matrix `Q P` of the rank-four factorisation. -/
theorem Q18_mul_P18 : Q18 * P18 = Matrix.fromBlocks !![0, 15; 2, 0] 0 0 !![0, 1; 4, 0] := by
  have t : ∀ a b : Fin 4, cip18 (vecs a) (vecs b) = ((if a = b then lensZ a else 0 : ℤ) : ℂ) :=
    vecs_orth18
  have e0 : vecs 0 = vA := rfl
  have e1 : vecs 1 = vZ := rfl
  have e2 : vecs 2 = vW := rfl
  have e3 : vecs 3 = vE := rfl
  have hc : ∀ i j, (Q18 * P18) i j =
      cip18 (Sum.elim ![vZ, vA] ![vE, vW] i) (Sum.elim ![vA, vZ] ![vW, vE] j) := by
    intro i j
    simp only [Q18, P18, Matrix.mul_apply, Matrix.of_apply, cip18]
  ext i j
  rw [hc]
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp only [Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Fin.zero_eta, Fin.mk_one,
      Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one] <;>
    first
    | (rw [← e0, ← e1, t]; norm_num [lensZ])
    | (rw [← e0, t]; norm_num [lensZ])
    | (rw [← e1, t]; norm_num [lensZ])
    | (rw [← e2, ← e3, t]; norm_num [lensZ])
    | (rw [← e2, t]; norm_num [lensZ])
    | (rw [← e3, t]; norm_num [lensZ])
    | (rw [← e0, ← e2, t]; norm_num [lensZ])
    | (rw [← e0, ← e3, t]; norm_num [lensZ])
    | (rw [← e1, ← e2, t]; norm_num [lensZ])
    | (rw [← e1, ← e3, t]; norm_num [lensZ])

open Polynomial in
theorem charpoly_block (a b : ℂ) :
    (!![0, a; b, 0] : Matrix (Fin 2) (Fin 2) ℂ).charpoly = X ^ 2 - C (a * b) := by
  rw [Matrix.charpoly_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, add_zero, map_zero, zero_mul,
    sub_zero, zero_sub, map_neg]
  ring

theorem card_Idx18 : Fintype.card Idx18 = 18 := by
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_coe, twelve_card]

open Polynomial in
/-- **The characteristic polynomial of the star matrix of L20** (`lem:l20-star-matrix`(a)): on
the six singletons and the twelve supports,
`det(λI − M(i)) = λ^{14}(λ² − 4)(λ² − 30)`. The proof is the paper's rank-four factorisation
`M(i) = P Q` with `P = [A, Z, W, E]`, `Q = [Z^*; A^*; E^*; W^*]` and the `4 × 4` Gram
`Q P = (0 15; 2 0) ⊕ (0 1; 4 0)`. -/
theorem charpoly_M18 : M18.charpoly = X ^ 14 * (X ^ 2 - C 4) * (X ^ 2 - C 30) := by
  have hle : Fintype.card (Fin 2 ⊕ Fin 2) ≤ Fintype.card Idx18 := by
    rw [card_Idx18]
    simp
  rw [M18_eq, Matrix.charpoly_mul_comm_of_le P18 Q18 hle, Q18_mul_P18,
    Matrix.charpoly_fromBlocks_zero₁₂, charpoly_block, charpoly_block, card_Idx18]
  have h4 : Fintype.card (Fin 2 ⊕ Fin 2) = 4 := by simp
  rw [h4]
  norm_num
  ring

/-! ## The supports outside the twelve, and the star part of the soft kernel -/

theorem inactive_int : ∀ S : Finset (Fin 6), 2 ≤ S.card → S ∉ twelve →
    ∏ k ∈ S, sZ k = 0 ∧ S ≠ {2, 3} := by
  decide

/-- **The rows and columns of the supports outside the twelve vanish**: `M(i)` is the `18 × 18`
matrix `M18` padded by zeros (`lem:l20-star-matrix`(a), first sentence). -/
theorem softM_D20_inactive (S : {S : Finset (Fin 6) // S ∈ supports (Fin 6)}) (hS : S.1 ∉ twelve)
    (b : Idx) : softM D20 (Sum.inr S) b = 0 ∧ softM D20 b (Sum.inr S) = 0 := by
  obtain ⟨h0, h1⟩ := inactive_int S.1 (two_le_card_of_mem S.2) hS
  have hZ : vZ (Sum.inr S) = 0 := by
    simp only [vZ, mkVec, Sum.elim_inr, h0, Int.cast_zero]
  have hE : vE (Sum.inr S) = 0 := by
    simp only [vE, mkVec, Sum.elim_inr, h1, ↓reduceIte, Int.cast_zero]
  have hA : vA (Sum.inr S) = 0 := by simp [vA, mkVec]
  have hW : vW (Sum.inr S) = 0 := by simp [vW, mkVec]
  constructor
  · rw [softM_D20_eq, hA, hZ, hW, hE]
    ring
  · rw [softM_D20_eq, hA, hZ, hW, hE]
    simp

/-- **The complete star part of the soft L20 kernel, `cor:star-matrix` with `‖M(i)‖ ≤ √30`**:
for a law `μ` on the halves with the hypotheses of `subsec:spec:actual-stars` and a synthesis
bound `‖𝓕‖² ≤ F` (`lem:l20-star-matrix`(b) provides `F = Γ_20`, not formalized here),
`|⟨P₀g, T_star P₀f⟩_μ| ≤ √30 F r ‖g‖_μ ‖f‖_μ`. This is the coefficient `√30 Γ_20` of `r` of the
remark after `lem:l20-star-matrix`. -/
theorem softStar_D20_norm_le {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p % 4 = 3)
    (μ : (Fin 6 → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : Fin 6 → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    {Fsq : ℝ} (hFsq : 0 ≤ Fsq)
    (hF : ∀ h : Idx → ZMod p → ℂ, (∀ a, meanC (h a) = 0) →
      ∑ x, μ x * ‖∑ a, kerMap (featKer (supports (Fin 6)) a) (h a) x‖ ^ 2 ≤
        Fsq * ∑ a, l2sq (h a))
    (g f : (Fin 6 → ZMod p) → ℂ) :
    ‖bil μ (cent μ g) (softStarPart D20) (cent μ f)‖ ≤
      rp p * Real.sqrt 30 * Fsq * √(∑ x, μ x * ‖g x‖ ^ 2) * √(∑ x, μ x * ‖f x‖ ^ 2) :=
  softStar_norm_le hp2 hp3 μ hμ0 hμ1 hinv D20 (Real.sqrt_nonneg 30) hFsq normLe_softM_D20 hF g f

end Sarkozy.L20Cap
