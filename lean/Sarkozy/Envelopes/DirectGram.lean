module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Sarkozy.Reflection.Bracket

@[expose] public section

/-!
# The leading Gram (`lem:record:direct-gram`)

`paper/sections/24_matching_mean.tex`, `lem:record:direct-gram` (in full), and part (a) of
`lem:record:asymmetric-gram`.

**The statement.** Let `V, A₁, A₂, A₃ : H₀ → 𝓗` be operators between real Hilbert spaces with
`‖(V, A₁/r, A₂/r, A₃/r)‖² ≤ Γ`, `r > 0`. Put `A_ξ = ∑ ξ_i A_i`, `e = (1, 0, 0)`,
`L_old = -(A_e V* + V A_e*)`, `L_{u,v} = A_u V* + V A_v*` and
`G(u, v) = [[L_old, L_{u,v}], [L_{u,v}*, L_old]]`. For `τ > 0` let
`Υ_τ(u, v) = [[-e/τ, u], [v, -τe]]` (a real `6 × 2` matrix) and `s(τ; u, v) = ‖Υ_τ(u, v)‖`. Then
`s² = λ_max [[τ⁻² + ‖v‖², -u₁/τ - τv₁], [-u₁/τ - τv₁, τ² + ‖u‖²]]` and
`G(u, v) ⪰ -rΓ s(τ; u, v) diag(τI, τ⁻¹I)`. At the signed point `a_t = (t, 1, 1 - t)`,
`u_t = a_t - e`, `v_t = -a_t - e`: `L_{u_t,v_t} = L_old + A_{a_t} V* - V A_{a_t}*` and
`G(u_t, v_t) ⪰ -rΓ s_t I` with `s_t = (4 - 2t + 2t² + 2√(1 + t²))^{1/2}`, `s₀ = √6`.

**Formalization.**
* `sSq τ u v` is the paper's `λ_max`, by the closed formula `lamMax` of the `2 × 2` eigenvalue,
  and `sSide = √sSq` is `s(τ; u, v)`. The columns of `Υ_τ(u, v)` are `upsCol1`, `upsCol2`
  (rows indexed by `Fin 3 ⊕ Fin 3`). `ups_norm_sq_le` (`‖Υw‖² ≤ s²‖w‖²` for all `w ∈ ℝ²`) and
  `ups_norm_sq_attained` (equality for some `w ≠ 0`) identify `s` with the operator norm `‖Υ‖`,
  i.e. they prove `s(τ; u, v)² = λ_max(ΥᵀΥ)` with the displayed matrix (`ups_norm_sq`).
* An operator inequality `G ⪰ -cD` on `𝓗 ⊕ 𝓗` is stated through its quadratic form at `(f, g)`:
  `gBlockForm V A u v f g ≥ -c(τ‖f‖² + τ⁻¹‖g‖²)`. `gramForm` is the same form written with the
  adjoints `W = V*`, `B_i = A_i*` (`gBlockForm_eq`).
* The frame hypothesis is the synthesis-map bound `‖V h₀ + ∑ A_i h_i/r‖² ≤ Γ(‖h₀‖² + ∑‖h_i‖²)`
  on `H₀⁴`, i.e. `‖Σ‖² ≤ Γ` for `Σ = (V, A₁/r, A₂/r, A₃/r)`; `frame_adjoint` turns it into
  `‖V* f‖² + ∑ ‖A_i* f‖²/r² ≤ Γ‖f‖²` (`‖Σ*‖² ≤ Γ`). `gramForm_lower` needs only the latter, for
  arbitrary linear maps `W, B_i` (no completeness).
* Headline theorems: `directGram` (the order for every `τ > 0`), `Luv_signed`, `sSq_signed`,
  `directGram_signed` (`G(u_t, v_t) ⪰ -rΓ s_t I`), `sT_zero` (`s₀ = √6`) and `sT_bounds`
  (`2.384227 < s_{127/500} < 2.384228`, the paper's `2.38422727…`).

**The proof** is the paper's: after the congruence by `diag(τI, τ⁻¹I)^{1/2}` the form is
`2r ∑_j ⟨(Υ ⊗ I)(x, x')_j, c_j⟩` over the six arm vectors `c_j` (`pairing_lower`), and
`|·| ≤ s` times the frame bound. The `2 × 2` eigenvalue bound is `quad_le_lamMax`.

**`lem:record:asymmetric-gram`(a)** (`bracket_enlarge_sides`): larger sides preserve the block
cut matrix `⪰_ι 0`, stated for the project's `ReflectionCut.Bracket` with the companion `D ⪰_c 0`
as a hypothesis (the paper's (E3)). Parts (b) and (c) of that lemma are not formalized.

No structures are introduced; all hypotheses are plain `Prop`s.
-/

namespace Sarkozy.Envelopes

open Finset

/-! ## The `2 × 2` eigenvalue -/

/-- The largest eigenvalue `(p + q)/2 + √(((p - q)/2)² + m²)` of the symmetric matrix
`[[p, m], [m, q]]`. -/
noncomputable def lamMax (p q m : ℝ) : ℝ := (p + q) / 2 + √(((p - q) / 2) ^ 2 + m ^ 2)

theorem lamMax_sub_left_nonneg (p q m : ℝ) : 0 ≤ lamMax p q m - p := by
  have h : |(p - q) / 2| ≤ √(((p - q) / 2) ^ 2 + m ^ 2) :=
    Real.abs_le_sqrt (by nlinarith [sq_nonneg m])
  have h2 := le_abs_self ((p - q) / 2)
  unfold lamMax
  linarith

theorem lamMax_sub_right_nonneg (p q m : ℝ) : 0 ≤ lamMax p q m - q := by
  have h : |(p - q) / 2| ≤ √(((p - q) / 2) ^ 2 + m ^ 2) :=
    Real.abs_le_sqrt (by nlinarith [sq_nonneg m])
  have h2 := neg_abs_le ((p - q) / 2)
  unfold lamMax
  linarith

theorem lamMax_mul_eq (p q m : ℝ) : (lamMax p q m - p) * (lamMax p q m - q) = m ^ 2 := by
  have hD : √(((p - q) / 2) ^ 2 + m ^ 2) ^ 2 = ((p - q) / 2) ^ 2 + m ^ 2 :=
    Real.sq_sqrt (by positivity)
  unfold lamMax
  linear_combination hD

/-- **The scalar step.** If `|t| ≤ XY`, then `pX² + 2mt + qY² ≤ λ_max (X² + Y²)`. -/
theorem quad_le_lamMax {p q m X Y t : ℝ} (ht : |t| ≤ X * Y) :
    p * X ^ 2 + 2 * m * t + q * Y ^ 2 ≤ lamMax p q m * (X ^ 2 + Y ^ 2) := by
  have hw := lamMax_sub_left_nonneg p q m
  have hw' := lamMax_sub_right_nonneg p q m
  have hprod := lamMax_mul_eq p q m
  set w := lamMax p q m - p with hw_def
  set w' := lamMax p q m - q with hw'_def
  have hmt : m * t ≤ |m| * (X * Y) := by
    calc m * t ≤ |m * t| := le_abs_self _
      _ = |m| * |t| := abs_mul m t
      _ ≤ |m| * (X * Y) := mul_le_mul_of_nonneg_left ht (abs_nonneg m)
  have hm2 : |m| ^ 2 = m ^ 2 := sq_abs m
  have key : 2 * (|m| * (X * Y)) ≤ w * X ^ 2 + w' * Y ^ 2 := by
    rcases hw.lt_or_eq with hwpos | hw0
    · have h1 : 0 ≤ (w * X - |m| * Y) ^ 2 := sq_nonneg _
      have h2 : w * (w * X ^ 2 + w' * Y ^ 2 - 2 * (|m| * (X * Y))) =
          (w * X - |m| * Y) ^ 2 := by
        have : w * w' = |m| ^ 2 := by rw [hm2]; exact hprod
        linear_combination Y ^ 2 * this
      have h3 : 0 ≤ w * (w * X ^ 2 + w' * Y ^ 2 - 2 * (|m| * (X * Y))) := h2 ▸ h1
      have h4 := nonneg_of_mul_nonneg_right h3 hwpos
      linarith
    · have hm0 : m ^ 2 = 0 := by rw [← hprod, ← hw0]; ring
      have : |m| = 0 := by
        have : m = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 hm0
        rw [this, abs_zero]
      rw [this, ← hw0]
      nlinarith [sq_nonneg Y]
  have e : lamMax p q m * (X ^ 2 + Y ^ 2) =
      p * X ^ 2 + q * Y ^ 2 + (w * X ^ 2 + w' * Y ^ 2) := by
    rw [hw_def, hw'_def]; ring
  rw [e]
  linarith

/-- **The eigenvalue is attained.** There is a nonzero `(X, Y)` with
`pX² + 2mXY + qY² = λ_max (X² + Y²)`. -/
theorem lamMax_attained (p q m : ℝ) :
    ∃ X Y : ℝ, (X ≠ 0 ∨ Y ≠ 0) ∧
      p * X ^ 2 + 2 * m * (X * Y) + q * Y ^ 2 = lamMax p q m * (X ^ 2 + Y ^ 2) := by
  have hprod := lamMax_mul_eq p q m
  by_cases hm : m = 0
  · subst hm
    have hD : √(((p - q) / 2) ^ 2 + 0 ^ 2) = |(p - q) / 2| := by
      rw [show ((p - q) / 2) ^ 2 + (0 : ℝ) ^ 2 = ((p - q) / 2) ^ 2 by ring]
      exact Real.sqrt_sq_eq_abs _
    rcases le_total q p with hqp | hpq
    · refine ⟨1, 0, Or.inl one_ne_zero, ?_⟩
      unfold lamMax
      rw [hD, abs_of_nonneg (by linarith)]
      ring
    · refine ⟨0, 1, Or.inr one_ne_zero, ?_⟩
      unfold lamMax
      rw [hD, abs_of_nonpos (by linarith)]
      ring
  · refine ⟨m, lamMax p q m - p, Or.inl hm, ?_⟩
    linear_combination (-(lamMax p q m - p)) * hprod

/-- `λ_max ≥ 0` when `p, q ≥ 0`. -/
theorem lamMax_nonneg {p q : ℝ} (hp : 0 ≤ p) (m : ℝ) : 0 ≤ lamMax p q m := by
  have := lamMax_sub_left_nonneg p q m
  linarith

/-! ## The pairing bound -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The pairing bound.** For real coefficient vectors `α, β` (the two columns of a real
matrix `Υ`) and vectors `x, x', c_j` of a real inner product space,
`2 ∑_j ⟪α_j x + β_j x', c_j⟫ ≥ -s (‖x‖² + ‖x'‖² + ∑_j ‖c_j‖²)`, where `s² = λ_max(ΥᵀΥ)`. -/
theorem pairing_lower {ι : Type*} [Fintype ι] (α β : ι → ℝ) (x x' : E) (c : ι → E) :
    -(√(lamMax (∑ j, α j ^ 2) (∑ j, β j ^ 2) (∑ j, α j * β j)) *
        (‖x‖ ^ 2 + ‖x'‖ ^ 2 + ∑ j, ‖c j‖ ^ 2)) ≤
      2 * ∑ j, inner ℝ (α j • x + β j • x') (c j) := by
  set p := ∑ j, α j ^ 2
  set q := ∑ j, β j ^ 2
  set m := ∑ j, α j * β j
  set lam := lamMax p q m with hlam
  have hp : 0 ≤ p := sum_nonneg (fun j _ => sq_nonneg (α j))
  have hlam0 : 0 ≤ lam := lamMax_nonneg hp m
  set s := √lam with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = lam := Real.sq_sqrt hlam0
  -- the norms of the `z_j = α_j x + β_j x'`
  have hz : ∑ j, ‖α j • x + β j • x'‖ ^ 2 =
      p * ‖x‖ ^ 2 + 2 * m * inner ℝ x x' + q * ‖x'‖ ^ 2 := by
    have : ∀ j, ‖α j • x + β j • x'‖ ^ 2 =
        α j ^ 2 * ‖x‖ ^ 2 + 2 * (α j * β j) * inner ℝ x x' + β j ^ 2 * ‖x'‖ ^ 2 := by
      intro j
      rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
        Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
      ring
    simp_rw [this]
    rw [sum_add_distrib, sum_add_distrib, ← sum_mul, ← sum_mul, ← sum_mul, ← mul_sum]
  have hzle : ∑ j, ‖α j • x + β j • x'‖ ^ 2 ≤ lam * (‖x‖ ^ 2 + ‖x'‖ ^ 2) := by
    rw [hz]
    exact quad_le_lamMax (abs_real_inner_le_norm x x')
  -- one pairing at a time
  have hj : ∀ j, -(‖α j • x + β j • x'‖ ^ 2 + s ^ 2 * ‖c j‖ ^ 2) ≤
      2 * s * inner ℝ (α j • x + β j • x') (c j) := by
    intro j
    have h0 := sq_nonneg ‖(α j • x + β j • x') + s • c j‖
    rw [norm_add_sq_real, norm_smul, real_inner_smul_right, Real.norm_eq_abs, mul_pow,
      sq_abs] at h0
    linarith
  have hsum : -(∑ j, ‖α j • x + β j • x'‖ ^ 2 + s ^ 2 * ∑ j, ‖c j‖ ^ 2) ≤
      2 * s * ∑ j, inner ℝ (α j • x + β j • x') (c j) := by
    have := sum_le_sum (fun j (_ : j ∈ (univ : Finset ι)) => hj j)
    rw [sum_neg_distrib, sum_add_distrib] at this
    rw [mul_sum, mul_sum]
    exact this
  rcases hs0.lt_or_eq with hspos | hs00
  · -- divide by `s > 0`
    have h1 : -(s * (s * (‖x‖ ^ 2 + ‖x'‖ ^ 2 + ∑ j, ‖c j‖ ^ 2))) ≤
        s * (2 * ∑ j, inner ℝ (α j • x + β j • x') (c j)) := by
      have : s * (s * (‖x‖ ^ 2 + ‖x'‖ ^ 2 + ∑ j, ‖c j‖ ^ 2)) =
          s ^ 2 * (‖x‖ ^ 2 + ‖x'‖ ^ 2) + s ^ 2 * ∑ j, ‖c j‖ ^ 2 := by ring
      rw [this, hs2]
      rw [hs2] at hsum
      have e2 : s * (2 * ∑ j, inner ℝ (α j • x + β j • x') (c j)) =
          2 * s * ∑ j, inner ℝ (α j • x + β j • x') (c j) := by ring
      rw [e2]
      have := mul_le_mul_of_nonneg_left hzle hlam0
      nlinarith
    have h2 : s * (-(s * (‖x‖ ^ 2 + ‖x'‖ ^ 2 + ∑ j, ‖c j‖ ^ 2))) ≤
        s * (2 * ∑ j, inner ℝ (α j • x + β j • x') (c j)) := by linarith
    exact le_of_mul_le_mul_left h2 hspos
  · -- `s = 0`: every `z_j` vanishes
    have hlam00 : lam = 0 := by rw [← hs2, ← hs00]; ring
    have hz0 : ∀ j, α j • x + β j • x' = 0 := by
      intro j
      have hle : ∑ j, ‖α j • x + β j • x'‖ ^ 2 ≤ 0 := by
        rw [hlam00, zero_mul] at hzle; exact hzle
      have hall := (sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖α j • x + β j • x'‖)).1
        (le_antisymm hle (sum_nonneg (fun j _ => sq_nonneg _))) j (mem_univ j)
      exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hall)
    simp only [hz0, inner_zero_left, sum_const_zero, mul_zero, ← hs00, zero_mul, neg_zero,
      le_refl]

/-! ## The matrix `Υ_τ(u, v)` and `s(τ; u, v)` -/

/-- `e = (1, 0, 0)`; the coordinates `0, 1, 2` of `Fin 3` are the paper's `1, 2, 3`. -/
def eVec : Fin 3 → ℝ := ![1, 0, 0]

/-- The squared Euclidean norm `‖ξ‖² = ∑ ξ_i²` on `ℝ³`. -/
def nsq (ξ : Fin 3 → ℝ) : ℝ := ∑ i, ξ i ^ 2

/-- The first column `(-e/τ; v)` of the real `6 × 2` matrix
`Υ_τ(u, v) = [[-e/τ, u], [v, -τe]]`, rows indexed by `Fin 3 ⊕ Fin 3`. -/
noncomputable def upsCol1 (τ : ℝ) (v : Fin 3 → ℝ) : Fin 3 ⊕ Fin 3 → ℝ
  | Sum.inl i => -eVec i / τ
  | Sum.inr i => v i

/-- The second column `(u; -τe)` of `Υ_τ(u, v)`. -/
noncomputable def upsCol2 (τ : ℝ) (u : Fin 3 → ℝ) : Fin 3 ⊕ Fin 3 → ℝ
  | Sum.inl i => u i
  | Sum.inr i => -τ * eVec i

/-- `s(τ; u, v)²`: the largest eigenvalue of the paper's matrix
`[[τ⁻² + ‖v‖², -u₁/τ - τv₁], [-u₁/τ - τv₁, τ² + ‖u‖²]]` (`lem:record:direct-gram`). -/
noncomputable def sSq (τ : ℝ) (u v : Fin 3 → ℝ) : ℝ :=
  lamMax (τ⁻¹ ^ 2 + nsq v) (τ ^ 2 + nsq u) (-u 0 / τ - τ * v 0)

/-- `s(τ; u, v) = ‖Υ_τ(u, v)‖` (`lem:record:direct-gram`); see `ups_norm_sq_le` and
`ups_norm_sq_attained` for the identification with the operator norm. -/
noncomputable def sSide (τ : ℝ) (u v : Fin 3 → ℝ) : ℝ := √(sSq τ u v)

theorem gram11 (τ : ℝ) (v : Fin 3 → ℝ) :
    ∑ j, upsCol1 τ v j ^ 2 = τ⁻¹ ^ 2 + nsq v := by
  simp only [Fintype.sum_sum_type, upsCol1, Fin.sum_univ_three, nsq, eVec]
  simp
  ring

theorem gram22 (τ : ℝ) (u : Fin 3 → ℝ) :
    ∑ j, upsCol2 τ u j ^ 2 = τ ^ 2 + nsq u := by
  simp only [Fintype.sum_sum_type, upsCol2, Fin.sum_univ_three, nsq, eVec]
  simp
  ring

theorem gram12 (τ : ℝ) (u v : Fin 3 → ℝ) :
    ∑ j, upsCol1 τ v j * upsCol2 τ u j = -u 0 / τ - τ * v 0 := by
  simp only [Fintype.sum_sum_type, upsCol1, upsCol2, Fin.sum_univ_three, eVec]
  simp
  ring

/-- `Υᵀ Υ` is the paper's displayed `2 × 2` matrix: for `w = (X, Y)`,
`‖Υ w‖² = (τ⁻² + ‖v‖²) X² + 2(-u₁/τ - τv₁) XY + (τ² + ‖u‖²) Y²`. -/
theorem ups_norm_sq (τ : ℝ) (u v : Fin 3 → ℝ) (X Y : ℝ) :
    ∑ j, (upsCol1 τ v j * X + upsCol2 τ u j * Y) ^ 2 =
      (τ⁻¹ ^ 2 + nsq v) * X ^ 2 + 2 * (-u 0 / τ - τ * v 0) * (X * Y) +
        (τ ^ 2 + nsq u) * Y ^ 2 := by
  rw [← gram11, ← gram22, ← gram12]
  have : ∀ j, (upsCol1 τ v j * X + upsCol2 τ u j * Y) ^ 2 =
      upsCol1 τ v j ^ 2 * X ^ 2 + 2 * (upsCol1 τ v j * upsCol2 τ u j) * (X * Y) +
        upsCol2 τ u j ^ 2 * Y ^ 2 := fun j => by ring
  simp_rw [this]
  rw [sum_add_distrib, sum_add_distrib, ← sum_mul, ← sum_mul, ← sum_mul, ← mul_sum]

/-- **`s(τ; u, v)` bounds `Υ_τ(u, v)`**: `‖Υ w‖² ≤ s² ‖w‖²` for every `w = (X, Y) ∈ ℝ²`. -/
theorem ups_norm_sq_le (τ : ℝ) (u v : Fin 3 → ℝ) (X Y : ℝ) :
    ∑ j, (upsCol1 τ v j * X + upsCol2 τ u j * Y) ^ 2 ≤ sSide τ u v ^ 2 * (X ^ 2 + Y ^ 2) := by
  have h0 : 0 ≤ sSq τ u v :=
    lamMax_nonneg (add_nonneg (sq_nonneg _) (sum_nonneg fun i _ => sq_nonneg (v i))) _
  rw [sSide, Real.sq_sqrt h0, ups_norm_sq, sSq]
  have := quad_le_lamMax (p := τ⁻¹ ^ 2 + nsq v) (q := τ ^ 2 + nsq u)
    (m := -u 0 / τ - τ * v 0) (X := |X|) (Y := |Y|) (t := X * Y) (by rw [abs_mul])
  rwa [sq_abs, sq_abs] at this

/-- **`s(τ; u, v)` is attained**: `‖Υ w‖² = s² ‖w‖²` for some `w ≠ 0`. With `ups_norm_sq_le`,
`s(τ; u, v)` is the operator norm `‖Υ_τ(u, v)‖` and `s² = λ_max(ΥᵀΥ)`, as the lemma states. -/
theorem ups_norm_sq_attained (τ : ℝ) (u v : Fin 3 → ℝ) :
    ∃ X Y : ℝ, (X ≠ 0 ∨ Y ≠ 0) ∧
      ∑ j, (upsCol1 τ v j * X + upsCol2 τ u j * Y) ^ 2 = sSide τ u v ^ 2 * (X ^ 2 + Y ^ 2) := by
  have h0 : 0 ≤ sSq τ u v :=
    lamMax_nonneg (add_nonneg (sq_nonneg _) (sum_nonneg fun i _ => sq_nonneg (v i))) _
  obtain ⟨X, Y, hne, h⟩ := lamMax_attained (τ⁻¹ ^ 2 + nsq v) (τ ^ 2 + nsq u)
    (-u 0 / τ - τ * v 0)
  exact ⟨X, Y, hne, by rw [sSide, Real.sq_sqrt h0, ups_norm_sq, sSq]; exact h⟩

theorem sSide_nonneg (τ : ℝ) (u v : Fin 3 → ℝ) : 0 ≤ sSide τ u v := Real.sqrt_nonneg _

/-! ## The bound on `G(u, v)`, through the adjoints -/

section Form

variable {H₀ 𝓗 : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]
  [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- The quadratic form of `G(u, v)` at `(f, g) ∈ 𝓗 ⊕ 𝓗`, written with the adjoints
`W = V*` and `B_i = A_i*`: with `L_old = -(A_e V* + V A_e*)` and `L_{u,v} = A_u V* + V A_v*`,
`⟨f, L_old f⟩ = -2⟨A₁* f, V* f⟩` and `⟨f, L_{u,v} g⟩ = ∑ u_i ⟨A_i* f, V* g⟩ + ∑ v_i ⟨V* f, A_i* g⟩`,
so `⟨(f, g), G(u, v)(f, g)⟩` is the expression below (`gBlockForm_eq` proves this for actual
adjoints). -/
def gramForm (W : 𝓗 →ₗ[ℝ] H₀) (B : Fin 3 → 𝓗 →ₗ[ℝ] H₀) (u v : Fin 3 → ℝ) (f g : 𝓗) : ℝ :=
  -2 * inner ℝ (B 0 f) (W f) - 2 * inner ℝ (B 0 g) (W g) +
    2 * (∑ i, u i * inner ℝ (B i f) (W g) + ∑ i, v i * inner ℝ (W f) (B i g))

/-- **`lem:record:direct-gram`, the order `G(u, v) ⪰ -rΓ s(τ; u, v) diag(τI, τ⁻¹I)`, in adjoint
form.** Let `W, B₁, B₂, B₃ : 𝓗 → H₀` (the adjoints `V*, A_i*`) satisfy the frame bound
`‖W f‖² + ∑ ‖B_i f‖²/r² ≤ Γ‖f‖²`, i.e. `‖(V, A₁/r, A₂/r, A₃/r)‖² ≤ Γ`. Then for `τ > 0`
the quadratic form of `G(u, v)` is at least `-rΓ s(τ; u, v)(τ‖f‖² + τ⁻¹‖g‖²)`. -/
theorem gramForm_lower (W : 𝓗 →ₗ[ℝ] H₀) (B : Fin 3 → 𝓗 →ₗ[ℝ] H₀) {r Γ τ : ℝ}
    (hr : 0 < r) (hτ : 0 < τ)
    (hframe : ∀ f, ‖W f‖ ^ 2 + (∑ i, ‖B i f‖ ^ 2) / r ^ 2 ≤ Γ * ‖f‖ ^ 2)
    (u v : Fin 3 → ℝ) (f g : 𝓗) :
    -(r * Γ * sSide τ u v * (τ * ‖f‖ ^ 2 + τ⁻¹ * ‖g‖ ^ 2)) ≤ gramForm W B u v f g := by
  set σ := √τ with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.2 hτ
  have hσ2 : σ ^ 2 = τ := Real.sq_sqrt hτ.le
  set x : H₀ := σ • W f
  set x' : H₀ := σ⁻¹ • W g
  set c : Fin 3 ⊕ Fin 3 → H₀ := fun j => match j with
    | Sum.inl i => (σ / r) • B i f
    | Sum.inr i => (σ⁻¹ / r) • B i g with hc
  have key := pairing_lower (upsCol1 τ v) (upsCol2 τ u) x x' c
  rw [gram11, gram22, gram12] at key
  change -(sSide τ u v * _) ≤ _ at key
  -- the norms
  have hn : ‖x‖ ^ 2 + ‖x'‖ ^ 2 + ∑ j, ‖c j‖ ^ 2 =
      τ * (‖W f‖ ^ 2 + (∑ i, ‖B i f‖ ^ 2) / r ^ 2) +
        τ⁻¹ * (‖W g‖ ^ 2 + (∑ i, ‖B i g‖ ^ 2) / r ^ 2) := by
    simp only [x, x', c, Fintype.sum_sum_type, Fin.sum_univ_three, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs]
    rw [← hσ2]
    field_simp
    ring
  -- the pairing
  have hp : r * (2 * ∑ j, inner ℝ (upsCol1 τ v j • x + upsCol2 τ u j • x') (c j)) =
      gramForm W B u v f g := by
    simp only [x, x', c, gramForm, Fintype.sum_sum_type, Fin.sum_univ_three, upsCol1, upsCol2,
      eVec, inner_add_left, real_inner_smul_left, real_inner_smul_right]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, neg_zero, zero_div, mul_zero, zero_mul, add_zero,
      zero_add]
    rw [real_inner_comm (W f) (B 0 f), real_inner_comm (W g) (B 0 g),
      real_inner_comm (W g) (B 0 f), real_inner_comm (W g) (B 1 f),
      real_inner_comm (W g) (B 2 f)]
    rw [← hσ2]
    field_simp
    ring
  have hframe' : τ * (‖W f‖ ^ 2 + (∑ i, ‖B i f‖ ^ 2) / r ^ 2) +
      τ⁻¹ * (‖W g‖ ^ 2 + (∑ i, ‖B i g‖ ^ 2) / r ^ 2) ≤
      Γ * (τ * ‖f‖ ^ 2 + τ⁻¹ * ‖g‖ ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_left (hframe f) hτ.le
    have h2 := mul_le_mul_of_nonneg_left (hframe g) (inv_nonneg.2 hτ.le)
    nlinarith
  rw [hn] at key
  rw [← hp]
  have hs := sSide_nonneg τ u v
  have h3 := mul_le_mul_of_nonneg_left hframe' (mul_nonneg hr.le hs)
  have h4 := mul_le_mul_of_nonneg_left key hr.le
  nlinarith

end Form

/-! ## The operator form, with actual adjoints -/

section Adjoint

open scoped InnerProduct

variable {H₀ 𝓗 : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

/-- `A_ξ = ∑_i ξ_i A_i` (`lem:record:direct-gram`). -/
noncomputable def armComb (A : Fin 3 → H₀ →L[ℝ] 𝓗) (ξ : Fin 3 → ℝ) : H₀ →L[ℝ] 𝓗 :=
  ∑ i, ξ i • A i

omit [CompleteSpace H₀] [CompleteSpace 𝓗] in
theorem armComb_apply (A : Fin 3 → H₀ →L[ℝ] 𝓗) (ξ : Fin 3 → ℝ) (x : H₀) :
    armComb A ξ x = ∑ i, ξ i • A i x := by
  simp [armComb]

/-- `L_old = -(A_e V* + V A_e*)` (`lem:record:direct-gram`). -/
noncomputable def Lold (V : H₀ →L[ℝ] 𝓗) (A : Fin 3 → H₀ →L[ℝ] 𝓗) : 𝓗 →L[ℝ] 𝓗 :=
  -(armComb A eVec ∘L V† + V ∘L (armComb A eVec)†)

/-- `L_{u,v} = A_u V* + V A_v*` (`lem:record:direct-gram`). -/
noncomputable def Luv (V : H₀ →L[ℝ] 𝓗) (A : Fin 3 → H₀ →L[ℝ] 𝓗) (u v : Fin 3 → ℝ) :
    𝓗 →L[ℝ] 𝓗 :=
  armComb A u ∘L V† + V ∘L (armComb A v)†

/-- The quadratic form of the block operator `G(u, v) = [[L_old, L_{u,v}], [L_{u,v}*, L_old]]`
on `𝓗 ⊕ 𝓗` at `(f, g)` (`lem:record:direct-gram`). -/
noncomputable def gBlockForm (V : H₀ →L[ℝ] 𝓗) (A : Fin 3 → H₀ →L[ℝ] 𝓗) (u v : Fin 3 → ℝ)
    (f g : 𝓗) : ℝ :=
  inner ℝ f (Lold V A f) + inner ℝ f (Luv V A u v g) + inner ℝ g (((Luv V A u v)†) f) +
    inner ℝ g (Lold V A g)

theorem inner_armComb (A : Fin 3 → H₀ →L[ℝ] 𝓗) (ξ : Fin 3 → ℝ) (f : 𝓗) (x : H₀) :
    inner ℝ f (armComb A ξ x) = ∑ i, ξ i * inner ℝ (((A i)†) f) x := by
  rw [armComb_apply, inner_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_right, ContinuousLinearMap.adjoint_inner_left]

theorem inner_armComb_adjoint (A : Fin 3 → H₀ →L[ℝ] 𝓗) (ξ : Fin 3 → ℝ) (x : H₀) (f : 𝓗) :
    inner ℝ x (((armComb A ξ)†) f) = ∑ i, ξ i * inner ℝ x (((A i)†) f) := by
  rw [ContinuousLinearMap.adjoint_inner_right, armComb_apply, sum_inner]
  refine sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_left, ContinuousLinearMap.adjoint_inner_right]

/-- The quadratic form of `G(u, v)` is `gramForm` at the adjoints `W = V*`, `B_i = A_i*`. -/
theorem gBlockForm_eq (V : H₀ →L[ℝ] 𝓗) (A : Fin 3 → H₀ →L[ℝ] 𝓗) (u v : Fin 3 → ℝ)
    (f g : 𝓗) :
    gBlockForm V A u v f g =
      gramForm (V†).toLinearMap (fun i => ((A i)†).toLinearMap) u v f g := by
  have hold : ∀ h : 𝓗, inner ℝ h (Lold V A h) = -2 * inner ℝ (((A 0)†) h) ((V†) h) := by
    intro h
    simp only [Lold, neg_apply, add_apply,
      ContinuousLinearMap.comp_apply, inner_neg_right, inner_add_right]
    rw [inner_armComb, ← ContinuousLinearMap.adjoint_inner_left V, inner_armComb_adjoint]
    simp only [eVec, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, one_mul, zero_mul, add_zero]
    rw [real_inner_comm (((A 0)†) h) ((V†) h)]
    ring
  have huv : inner ℝ f (Luv V A u v g) =
      ∑ i, u i * inner ℝ (((A i)†) f) ((V†) g) + ∑ i, v i * inner ℝ ((V†) f) (((A i)†) g) := by
    simp only [Luv, add_apply, ContinuousLinearMap.comp_apply,
      inner_add_right]
    rw [inner_armComb, ← ContinuousLinearMap.adjoint_inner_left V, inner_armComb_adjoint]
  have hadj : inner ℝ g (((Luv V A u v)†) f) = inner ℝ f (Luv V A u v g) := by
    rw [ContinuousLinearMap.adjoint_inner_right, real_inner_comm]
  rw [gBlockForm, hold, hold, hadj, huv, gramForm]
  simp only [ContinuousLinearMap.coe_coe]
  ring

/-- **The frame bound passes to the adjoints.** If the synthesis map
`Σ(h₀, h) = V h₀ + ∑ A_i h_i / r` of `H₀ ⊕ H₀³` has `‖Σ‖² ≤ Γ` (the hypothesis
`‖(V, A₁/r, A₂/r, A₃/r)‖² ≤ Γ`), then `‖V* f‖² + ∑ ‖A_i* f‖²/r² ≤ Γ‖f‖²`. -/
theorem frame_adjoint (V : H₀ →L[ℝ] 𝓗) (A : Fin 3 → H₀ →L[ℝ] 𝓗) {r Γ : ℝ} (hr : 0 < r)
    (hΓ : 0 ≤ Γ)
    (hframe : ∀ (h₀ : H₀) (h : Fin 3 → H₀),
      ‖V h₀ + ∑ i, r⁻¹ • A i (h i)‖ ^ 2 ≤ Γ * (‖h₀‖ ^ 2 + ∑ i, ‖h i‖ ^ 2))
    (f : 𝓗) :
    ‖(V†) f‖ ^ 2 + (∑ i, ‖((A i)†) f‖ ^ 2) / r ^ 2 ≤ Γ * ‖f‖ ^ 2 := by
  set h : Fin 3 → H₀ := fun i => r⁻¹ • ((A i)†) f with hh
  set S := V ((V†) f) + ∑ i, r⁻¹ • A i (h i) with hS
  set N := ‖(V†) f‖ ^ 2 + ∑ i, ‖h i‖ ^ 2 with hNdef
  have hN : N = ‖(V†) f‖ ^ 2 + (∑ i, ‖((A i)†) f‖ ^ 2) / r ^ 2 := by
    simp only [hNdef, hh, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, sum_div]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    field_simp
  have hinner : inner ℝ f S = N := by
    simp only [hS, hNdef, hh, inner_add_right, inner_sum, real_inner_smul_right]
    rw [← ContinuousLinearMap.adjoint_inner_left V, real_inner_self_eq_norm_sq]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [← ContinuousLinearMap.adjoint_inner_left (A i), real_inner_smul_right,
      real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hN0 : 0 ≤ N := add_nonneg (sq_nonneg _) (sum_nonneg fun i _ => sq_nonneg ‖h i‖)
  have hCS : N ≤ ‖f‖ * ‖S‖ := hinner ▸ real_inner_le_norm f S
  have hS2 := hframe ((V†) f) h
  rw [← hN]
  rcases hN0.lt_or_eq with hpos | h0
  · have : N ^ 2 ≤ ‖f‖ ^ 2 * (Γ * N) := by
      calc N ^ 2 ≤ (‖f‖ * ‖S‖) ^ 2 := pow_le_pow_left₀ hN0 hCS 2
        _ = ‖f‖ ^ 2 * ‖S‖ ^ 2 := by ring
        _ ≤ ‖f‖ ^ 2 * (Γ * N) := mul_le_mul_of_nonneg_left hS2 (sq_nonneg _)
    nlinarith
  · rw [← h0]; positivity

/-- **`lem:record:direct-gram`, the order `G(u, v) ⪰ -rΓ s(τ; u, v) diag(τI, τ⁻¹I)`.**
Let `V, A₁, A₂, A₃ : H₀ → 𝓗` be bounded operators between real Hilbert spaces with
`‖(V, A₁/r, A₂/r, A₃/r)‖² ≤ Γ`, `r > 0` (`hframe`, the synthesis-map form). Then for every
`τ > 0` and `u, v ∈ ℝ³` the quadratic form of `G(u, v)` on `𝓗 ⊕ 𝓗` satisfies
`⟨(f, g), G(u, v)(f, g)⟩ ≥ -rΓ s(τ; u, v)(τ‖f‖² + τ⁻¹‖g‖²)`. The adjoints are those of `𝓗`
and `H₀`; nothing is assumed about the operators beyond the frame bound. -/
theorem directGram (V : H₀ →L[ℝ] 𝓗) (A : Fin 3 → H₀ →L[ℝ] 𝓗) {r Γ τ : ℝ} (hr : 0 < r)
    (hΓ : 0 ≤ Γ) (hτ : 0 < τ)
    (hframe : ∀ (h₀ : H₀) (h : Fin 3 → H₀),
      ‖V h₀ + ∑ i, r⁻¹ • A i (h i)‖ ^ 2 ≤ Γ * (‖h₀‖ ^ 2 + ∑ i, ‖h i‖ ^ 2))
    (u v : Fin 3 → ℝ) (f g : 𝓗) :
    -(r * Γ * sSide τ u v * (τ * ‖f‖ ^ 2 + τ⁻¹ * ‖g‖ ^ 2)) ≤ gBlockForm V A u v f g := by
  rw [gBlockForm_eq]
  exact gramForm_lower _ _ hr hτ (fun f => by simpa using frame_adjoint V A hr hΓ hframe f)
    u v f g

/-! ### The signed point -/

/-- The signed arm vector `a_t = (t, 1, 1 - t)` (`lem:record:direct-gram`). -/
def aT (t : ℝ) : Fin 3 → ℝ := ![t, 1, 1 - t]

/-- `u_t = a_t - e`. -/
def uT (t : ℝ) : Fin 3 → ℝ := fun i => aT t i - eVec i

/-- `v_t = -a_t - e`. -/
def vT (t : ℝ) : Fin 3 → ℝ := fun i => -aT t i - eVec i

omit [CompleteSpace H₀] [CompleteSpace 𝓗] in
theorem armComb_sub (A : Fin 3 → H₀ →L[ℝ] 𝓗) (ξ η : Fin 3 → ℝ) :
    armComb A (fun i => ξ i - η i) = armComb A ξ - armComb A η := by
  simp [armComb, sub_smul, sum_sub_distrib]

omit [CompleteSpace H₀] [CompleteSpace 𝓗] in
theorem armComb_neg_sub (A : Fin 3 → H₀ →L[ℝ] 𝓗) (ξ η : Fin 3 → ℝ) :
    armComb A (fun i => -ξ i - η i) = -armComb A ξ - armComb A η := by
  simp [armComb, sub_smul, neg_smul, sum_sub_distrib, sum_neg_distrib]

/-- **`lem:record:direct-gram`, the signed identity**
`L_{u_t, v_t} = L_old + A_{a_t} V* - V A_{a_t}*`. -/
theorem Luv_signed (V : H₀ →L[ℝ] 𝓗) (A : Fin 3 → H₀ →L[ℝ] 𝓗) (t : ℝ) :
    Luv V A (uT t) (vT t) = Lold V A + armComb A (aT t) ∘L V† - V ∘L (armComb A (aT t))† := by
  unfold uT vT
  rw [Luv, Lold, armComb_sub, armComb_neg_sub, map_sub, map_neg,
    ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_neg]
  abel

/-- `s_t = (4 - 2t + 2t² + 2√(1 + t²))^{1/2}` (`lem:record:direct-gram`). -/
noncomputable def sT (t : ℝ) : ℝ := √(4 - 2 * t + 2 * t ^ 2 + 2 * √(1 + t ^ 2))

/-- At `τ = 1` and the signed point, the `2 × 2` matrix is `[[4 + 2t², 2], [2, 4 - 4t + 2t²]]`
with largest eigenvalue `4 - 2t + 2t² + 2√(1 + t²)`. -/
theorem sSq_signed (t : ℝ) : sSq 1 (uT t) (vT t) = 4 - 2 * t + 2 * t ^ 2 + 2 * √(1 + t ^ 2) := by
  have hv : nsq (vT t) = 3 + 2 * t ^ 2 := by
    simp [nsq, vT, aT, eVec, Fin.sum_univ_three]; ring
  have hu : nsq (uT t) = 3 - 4 * t + 2 * t ^ 2 := by
    simp [nsq, uT, aT, eVec, Fin.sum_univ_three]; ring
  have hu0 : uT t 0 = t - 1 := by simp [uT, aT, eVec]
  have hv0 : vT t 0 = -t - 1 := by simp [vT, aT, eVec]
  have h4 : √(4 * (1 + t ^ 2)) = 2 * √(1 + t ^ 2) := by
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [sSq, lamMax, hv, hu, hu0, hv0]
  have e : (((1 : ℝ)⁻¹ ^ 2 + (3 + 2 * t ^ 2) - (1 ^ 2 + (3 - 4 * t + 2 * t ^ 2))) / 2) ^ 2 +
      (-(t - 1) / 1 - 1 * (-t - 1)) ^ 2 = 4 * (1 + t ^ 2) := by ring
  rw [e, h4]
  ring

theorem sSide_signed (t : ℝ) : sSide 1 (uT t) (vT t) = sT t := by
  rw [sSide, sSq_signed, sT]

/-- `s_0 = √6`, the mirror point. -/
theorem sT_zero : sT 0 = √6 := by
  rw [sT]
  norm_num

/-- **`lem:record:direct-gram` at the signed point: `G(u_t, v_t) ⪰ -rΓ s_t I`.** -/
theorem directGram_signed (V : H₀ →L[ℝ] 𝓗) (A : Fin 3 → H₀ →L[ℝ] 𝓗) {r Γ : ℝ} (hr : 0 < r)
    (hΓ : 0 ≤ Γ)
    (hframe : ∀ (h₀ : H₀) (h : Fin 3 → H₀),
      ‖V h₀ + ∑ i, r⁻¹ • A i (h i)‖ ^ 2 ≤ Γ * (‖h₀‖ ^ 2 + ∑ i, ‖h i‖ ^ 2))
    (t : ℝ) (f g : 𝓗) :
    -(r * Γ * sT t * (‖f‖ ^ 2 + ‖g‖ ^ 2)) ≤ gBlockForm V A (uT t) (vT t) f g := by
  have := directGram V A hr hΓ one_pos hframe (uT t) (vT t) f g
  rwa [sSide_signed, one_mul, inv_one, one_mul] at this

end Adjoint

/-! ## `lem:record:asymmetric-gram`(a): larger sides -/

section Enlargement

variable {V X : Type*} [Fintype V] [DecidableEq V]

/-- **`lem:record:asymmetric-gram`(a), enlargement.** Only part (a) of that lemma is formalized
here; the block extension (b) and the reflected transpose (c) are not. Let `c` be a reflection
cut (the paper's `ι`), `Pold` and `Pnew` the cut-matrix measures of the reference record
`Π_{F₁,𝔅}` and of the comparison record `Π'_{F₁,𝔅}`, and `D` a measure with `D ⪰_c 0` (the
diagonal copy `D¹_𝔅`, which is `⪰_ι 0` by (E3); here a hypothesis). If the block cut matrix
`[[Pold + r d_L D, Pnew], [Pnew*, Pold + r d_R D]]` is `⪰_c 0` (a `ReflectionCut.Bracket`), so
is the one with any larger sides `d'_L ≥ d_L`, `d'_R ≥ d_R`, for `r ≥ 0`: the difference is the
diagonal `diag((d'_L - d_L) r D, (d'_R - d_R) r D) ⪰_c 0`. -/
theorem bracket_enlarge_sides {c : ReflectionCut V}
    {Pold Pnew D : ((V → X) → ℝ) →ₗ[ℝ] ℝ} {r dL dR dL' dR' : ℝ} (hr : 0 ≤ r)
    (hL : dL ≤ dL') (hR : dR ≤ dR') (hD : c.Positive D)
    (h : c.Bracket (Pold + (r * dL) • D) Pnew (Pold + (r * dR) • D)) :
    c.Bracket (Pold + (r * dL') • D) Pnew (Pold + (r * dR') • D) := by
  have eL : Pold + (r * dL') • D = (Pold + (r * dL) • D) + (r * (dL' - dL)) • D := by
    rw [add_assoc, ← add_smul]; congr 2; ring
  have eR : Pold + (r * dR') • D = (Pold + (r * dR) • D) + (r * (dR' - dR)) • D := by
    rw [add_assoc, ← add_smul]; congr 2; ring
  have hpL : 0 ≤ r * (dL' - dL) := mul_nonneg hr (by linarith)
  have hpR : 0 ≤ r * (dR' - dR) := mul_nonneg hr (by linarith)
  rw [eL, eR]
  refine ⟨h.left_positive.add (hD.smul hpL), h.right_positive.add (hD.smul hpR), ?_⟩
  intro F G
  have h0 := h.nonneg F G
  have h1 := mul_nonneg hpL (hD.nonneg F)
  have h2 := mul_nonneg hpR (hD.nonneg G)
  change 0 ≤ (c.form (Pold + (r * dL) • D) F F + (r * (dL' - dL)) * c.form D F F) +
    2 * c.form Pnew F G + (c.form (Pold + (r * dR) • D) G G + (r * (dR' - dR)) * c.form D G G)
  linarith

end Enlargement

/-! ## The value at `t = 127/500` -/

/-- **The signed coefficient at `t = 127/500`**: `2.384227 < s_t < 2.384228` (the paper's
`s_t = 2.38422727…`), by exact rational bounds for the two square roots. -/
theorem sT_bounds : (2384227 / 1000000 : ℝ) < sT (127 / 500) ∧
    sT (127 / 500) < 2384228 / 1000000 := by
  have hy1 : (10317538 / 10000000 : ℝ) < √(1 + (127 / 500 : ℝ) ^ 2) :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hy2 : √(1 + (127 / 500 : ℝ) ^ 2) < 10317539 / 10000000 :=
    (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  refine ⟨(Real.lt_sqrt (by norm_num)).2 ?_, (Real.sqrt_lt' (by norm_num)).2 ?_⟩
  · nlinarith
  · nlinarith

end Sarkozy.Envelopes
