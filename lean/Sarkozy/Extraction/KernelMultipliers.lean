module

public import Sarkozy.Extraction.WitnessKernel

/-!
# Inserted multipliers (`lem:matching:kernel`(d))

`paper/sections/16_extraction.tex`, `lem:matching:kernel` (d). Let `k = 2`,
`𝒦 = {(1,1), (2,2)}`, `ς₁, ς₂ = ±1`, and let `F_out(x₁, x₂)`, `F_mid(x₁, y₂)`, `F_in(y₁, y₂)` be
bounded functions. The operator on `L²(𝔽_p²)` (uniform probability) with kernel
`χ(ς₁(y₁ - x₁)) χ(ς₂(y₂ - x₂)) F_out(x₁, x₂) F_mid(x₁, y₂) F_in(y₁, y₂)`
has norm at most `r² ‖F_out‖_∞ ‖F_mid‖_∞ ‖F_in‖_∞`, and so has the operator with
`F_mid(y₁, x₂)` in place of `F_mid(x₁, y₂)`.

`OpBound` uses the counting-measure (`ℓ²`) normalization, in which the kernel matrix has norm at
most `√p² · c_out c_mid c_in` whenever `|F_out| ≤ c_out`, `|F_mid| ≤ c_mid`, `|F_in| ≤ c_in`;
the uniform-probability bound `r² = 1/p` corresponds to `√p² = p`.

* `insertedMultipliers_opBound`: as in the paper, the operator is
  `M_{F_out} (I ⊗ C_{ς₂}) M_{F_mid} (C_{ς₁} ⊗ I) M_{F_in}`, with `M_F` the multiplication by `F`
  and `C_ς` the Gauss operator with kernel `χ(ς(b - a))` (norm `√p`, `opBound_gauss`). The
  kernel identity sums out the intermediate point `(x₁, y₂)`.
* `insertedMultipliers_opBound'`: `F_mid(y₁, x₂)`; the two transforms in the other order,
  `M_{F_out} (C_{ς₁} ⊗ I) M_{F_mid} (I ⊗ C_{ς₂}) M_{F_in}`, through the point `(y₁, x₂)`.
* `threeEdgePath_opBound`, `threeEdgePath_opBound'` (`rem:extraction-kernels`): a third character
  `χ(ς₁₂(y₂ - x₁))`, resp. `χ(ς₂₁(y₁ - x₂))`, has modulus at most one and is absorbed into
  `F_mid`, so the three-edge paths are covered too (with any `ς₁₂`, `ς₂₁`).

Auxiliary operator bounds: `opBound_mul_diag` (a multiplication by a function of modulus at most
`c` has norm at most `c`, generalizing `opBound_diag`), `opBound_mul_left`, `opBound_mul_right`
(composition with such a multiplication on either side), `opBound_gauss`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.Extraction

open Sarkozy.Influence

section Operators

variable {U V : Type*} [Fintype U] [Fintype V]

/-- A multiplication by a function of modulus at most `c` has norm at most `c`. -/
theorem opBound_mul_diag [DecidableEq U] (m : U → ℝ) {c : ℝ} (hm : ∀ u, |m u| ≤ c) :
    OpBound univ univ (fun x y : U => if x = y then m x else 0) c := by
  intro g
  have hrow : ∀ x : U, ∑ y : U, (if x = y then m x else 0) * g y = m x * g x := by
    intro x
    rw [sum_eq_single x]
    · simp
    · intro y _ hy; simp [Ne.symm hy]
    · intro h'; exact absurd (mem_univ _) h'
  simp_rw [hrow]
  rw [mul_sum]
  refine sum_le_sum fun x _ => ?_
  have h1 : m x ^ 2 ≤ c ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hm x) 2
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)

/-- The composite `M_m A` of an operator `A` with a multiplication by a function of modulus at
most `c` has kernel `m(x) A(x, y)` and norm at most `c Λ`. -/
theorem opBound_mul_left [DecidableEq U] {A : U → V → ℝ} {Λ : ℝ} (h : OpBound univ univ A Λ)
    (m : U → ℝ) {c : ℝ} (hm : ∀ u, |m u| ≤ c) :
    OpBound univ univ (fun x y => m x * A x y) (c * Λ) := by
  refine Sarkozy.Extraction.OpBound.congr' ((opBound_mul_diag m hm).comp h) (fun x y => ?_) rfl
  rw [sum_eq_single x]
  · simp
  · intro u _ hu; simp [Ne.symm hu]
  · intro h'; exact absurd (mem_univ _) h'

/-- The composite `A M_m` of an operator `A` with a multiplication by a function of modulus at
most `c` has kernel `A(x, y) m(y)` and norm at most `Λ c`. -/
theorem opBound_mul_right [DecidableEq V] {A : U → V → ℝ} {Λ : ℝ} (h : OpBound univ univ A Λ)
    (m : V → ℝ) {c : ℝ} (hm : ∀ v, |m v| ≤ c) :
    OpBound univ univ (fun x y => A x y * m y) (Λ * c) := by
  refine Sarkozy.Extraction.OpBound.congr' (h.comp (opBound_mul_diag m hm)) (fun x y => ?_) rfl
  rw [sum_eq_single y]
  · simp
  · intro v _ hv; simp [hv]
  · intro h'; exact absurd (mem_univ _) h'

end Operators

variable {p : ℕ} [Fact p.Prime]

/-- The Gauss operator `C_ς` with kernel `χ(ς(y - x))`, `ς = ±1` (`lem:spec:gauss`), has `ℓ²`
norm at most `√p`; in the uniform normalization, norm `r`. -/
theorem opBound_gauss (hp2 : p ≠ 2) {ς : ZMod p} (hς : ς = 1 ∨ ς = -1) :
    OpBound univ univ (fun x y : ZMod p => chiR (ς * (y - x))) (Real.sqrt p) := by
  have hpal := (opBound_paley (p := p) hp2).smul (chiR ς)
  have habs : |chiR ς| = 1 := by
    rcases chiR_sign hς with h | h <;> rw [h] <;> simp
  rw [habs, one_mul] at hpal
  exact Sarkozy.Extraction.OpBound.congr' (A := fun x y : ZMod p => chiR ς * chiR (y - x)) hpal
    (fun x y => by rw [chiR_mul]) rfl

/-- **`lem:matching:kernel`(d), inserted multipliers**: for `ς₁, ς₂ = ±1` and functions with
`|F_out| ≤ c_out`, `|F_mid| ≤ c_mid`, `|F_in| ≤ c_in`, the kernel
`χ(ς₁(y₁ - x₁)) χ(ς₂(y₂ - x₂)) F_out(x₁, x₂) F_mid(x₁, y₂) F_in(y₁, y₂)` on `𝔽_p² × 𝔽_p²` has
`ℓ²` operator norm at most `√p² c_out c_mid c_in`; in the uniform normalization,
`r² ‖F_out‖_∞ ‖F_mid‖_∞ ‖F_in‖_∞`. The operator is
`M_{F_out} (I ⊗ C_{ς₂}) M_{F_mid} (C_{ς₁} ⊗ I) M_{F_in}`.

A third character `χ(ς₁₂(y₂ - x₁))` has modulus at most one and may be absorbed into `F_mid`
(`rem:extraction-kernels`): `threeEdgePath_opBound`. -/
theorem insertedMultipliers_opBound (hp2 : p ≠ 2) {ς₁ ς₂ : ZMod p} (h₁ : ς₁ = 1 ∨ ς₁ = -1)
    (h₂ : ς₂ = 1 ∨ ς₂ = -1) (Fout Fmid Fin : ZMod p → ZMod p → ℝ) {cout cmid cin : ℝ}
    (hout : ∀ a b, |Fout a b| ≤ cout) (hmid : ∀ a b, |Fmid a b| ≤ cmid)
    (hin : ∀ a b, |Fin a b| ≤ cin) :
    OpBound univ univ (fun (x y : ZMod p × ZMod p) => chiR (ς₁ * (y.1 - x.1)) *
      chiR (ς₂ * (y.2 - x.2)) * Fout x.1 x.2 * Fmid x.1 y.2 * Fin y.1 y.2)
      (Real.sqrt p ^ 2 * (cout * cmid * cin)) := by
  -- `C_{ς₁} ⊗ I` replaces `y₁` by `x₁`
  have hG₁ : OpBound univ univ (fun (x y : ZMod p × ZMod p) =>
      chiR (ς₁ * (y.1 - x.1)) * (if x.2 = y.2 then 1 else 0)) (Real.sqrt p) :=
    Sarkozy.Extraction.opBound_tensor_left (U := ZMod p) (V := ZMod p) (W := ZMod p)
      (A := fun x y : ZMod p => chiR (ς₁ * (y - x))) (opBound_gauss hp2 h₁)
  -- `I ⊗ C_{ς₂}` replaces `y₂` by `x₂`
  have hG₂ : OpBound univ univ (fun (x y : ZMod p × ZMod p) =>
      (if x.1 = y.1 then 1 else 0) * chiR (ς₂ * (y.2 - x.2))) (Real.sqrt p) :=
    Sarkozy.Extraction.opBound_tensor_right (U := ZMod p) (V := ZMod p) (W := ZMod p)
      (A := fun x y : ZMod p => chiR (ς₂ * (y - x))) (opBound_gauss hp2 h₂)
  -- `M_{F_mid} (C_{ς₁} ⊗ I)`
  have hM := Sarkozy.Extraction.opBound_mul_left (U := ZMod p × ZMod p) (V := ZMod p × ZMod p)
    hG₁ (fun v => Fmid v.1 v.2) (fun v => hmid v.1 v.2)
  -- `M_{F_out} (I ⊗ C_{ς₂}) M_{F_mid} (C_{ς₁} ⊗ I) M_{F_in}`
  have hT := Sarkozy.Extraction.opBound_mul_right (U := ZMod p × ZMod p) (V := ZMod p × ZMod p)
    (Sarkozy.Extraction.opBound_mul_left (U := ZMod p × ZMod p) (V := ZMod p × ZMod p)
      (hG₂.comp hM) (fun x => Fout x.1 x.2) (fun x => hout x.1 x.2))
    (fun y => Fin y.1 y.2) (fun y => hin y.1 y.2)
  refine Sarkozy.Extraction.OpBound.congr' hT (fun x y => ?_) (by ring)
  -- the kernel identity: the intermediate point is `(x₁, y₂)`
  rw [Fintype.sum_eq_single (x.1, y.2)]
  · simp only [↓reduceIte, mul_one, one_mul]
    ring
  · intro v hv
    by_cases h1 : x.1 = v.1
    · have h2 : v.2 ≠ y.2 := fun h2 => hv (Prod.ext h1.symm h2)
      simp only [h2, ↓reduceIte, mul_zero]
    · simp only [h1, ↓reduceIte, zero_mul]

/-- **`lem:matching:kernel`(d), inserted multipliers, other order**: the same bound with
`F_mid(y₁, x₂)` in place of `F_mid(x₁, y₂)`. The operator is
`M_{F_out} (C_{ς₁} ⊗ I) M_{F_mid} (I ⊗ C_{ς₂}) M_{F_in}`.

A third character `χ(ς₂₁(y₁ - x₂))` may be absorbed into `F_mid` (`rem:extraction-kernels`):
`threeEdgePath_opBound'`. -/
theorem insertedMultipliers_opBound' (hp2 : p ≠ 2) {ς₁ ς₂ : ZMod p} (h₁ : ς₁ = 1 ∨ ς₁ = -1)
    (h₂ : ς₂ = 1 ∨ ς₂ = -1) (Fout Fmid Fin : ZMod p → ZMod p → ℝ) {cout cmid cin : ℝ}
    (hout : ∀ a b, |Fout a b| ≤ cout) (hmid : ∀ a b, |Fmid a b| ≤ cmid)
    (hin : ∀ a b, |Fin a b| ≤ cin) :
    OpBound univ univ (fun (x y : ZMod p × ZMod p) => chiR (ς₁ * (y.1 - x.1)) *
      chiR (ς₂ * (y.2 - x.2)) * Fout x.1 x.2 * Fmid y.1 x.2 * Fin y.1 y.2)
      (Real.sqrt p ^ 2 * (cout * cmid * cin)) := by
  -- `C_{ς₁} ⊗ I` replaces `y₁` by `x₁`
  have hG₁ : OpBound univ univ (fun (x y : ZMod p × ZMod p) =>
      chiR (ς₁ * (y.1 - x.1)) * (if x.2 = y.2 then 1 else 0)) (Real.sqrt p) :=
    Sarkozy.Extraction.opBound_tensor_left (U := ZMod p) (V := ZMod p) (W := ZMod p)
      (A := fun x y : ZMod p => chiR (ς₁ * (y - x))) (opBound_gauss hp2 h₁)
  -- `I ⊗ C_{ς₂}` replaces `y₂` by `x₂`
  have hG₂ : OpBound univ univ (fun (x y : ZMod p × ZMod p) =>
      (if x.1 = y.1 then 1 else 0) * chiR (ς₂ * (y.2 - x.2))) (Real.sqrt p) :=
    Sarkozy.Extraction.opBound_tensor_right (U := ZMod p) (V := ZMod p) (W := ZMod p)
      (A := fun x y : ZMod p => chiR (ς₂ * (y - x))) (opBound_gauss hp2 h₂)
  -- `M_{F_mid} (I ⊗ C_{ς₂})`
  have hM := Sarkozy.Extraction.opBound_mul_left (U := ZMod p × ZMod p) (V := ZMod p × ZMod p)
    hG₂ (fun v => Fmid v.1 v.2) (fun v => hmid v.1 v.2)
  -- `M_{F_out} (C_{ς₁} ⊗ I) M_{F_mid} (I ⊗ C_{ς₂}) M_{F_in}`
  have hT := Sarkozy.Extraction.opBound_mul_right (U := ZMod p × ZMod p) (V := ZMod p × ZMod p)
    (Sarkozy.Extraction.opBound_mul_left (U := ZMod p × ZMod p) (V := ZMod p × ZMod p)
      (hG₁.comp hM) (fun x => Fout x.1 x.2) (fun x => hout x.1 x.2))
    (fun y => Fin y.1 y.2) (fun y => hin y.1 y.2)
  refine Sarkozy.Extraction.OpBound.congr' hT (fun x y => ?_) (by ring)
  -- the kernel identity: the intermediate point is `(y₁, x₂)`
  rw [Fintype.sum_eq_single (y.1, x.2)]
  · simp only [↓reduceIte, mul_one, one_mul]
    ring
  · intro v hv
    by_cases h2 : x.2 = v.2
    · have h1 : v.1 ≠ y.1 := fun h1 => hv (Prod.ext h1 h2.symm)
      simp only [h1, ↓reduceIte, mul_zero, zero_mul]
    · simp only [h2, ↓reduceIte, mul_zero, zero_mul]

/-- **Three-edge paths** (`rem:extraction-kernels`): the connector `χ(ς₁₂(y₂ - x₁))` has modulus
at most one and is absorbed into `F_mid(x₁, y₂)` in `insertedMultipliers_opBound`
(`lem:matching:kernel`(d)); any `ς₁₂` is allowed. -/
theorem threeEdgePath_opBound (hp2 : p ≠ 2) {ς₁ ς₂ : ZMod p} (h₁ : ς₁ = 1 ∨ ς₁ = -1)
    (h₂ : ς₂ = 1 ∨ ς₂ = -1) (ς₁₂ : ZMod p) (Fout Fmid Fin : ZMod p → ZMod p → ℝ)
    {cout cmid cin : ℝ} (hout : ∀ a b, |Fout a b| ≤ cout) (hmid : ∀ a b, |Fmid a b| ≤ cmid)
    (hin : ∀ a b, |Fin a b| ≤ cin) :
    OpBound univ univ (fun (x y : ZMod p × ZMod p) => chiR (ς₁ * (y.1 - x.1)) *
      chiR (ς₂ * (y.2 - x.2)) * chiR (ς₁₂ * (y.2 - x.1)) * Fout x.1 x.2 * Fmid x.1 y.2 *
        Fin y.1 y.2)
      (Real.sqrt p ^ 2 * (cout * cmid * cin)) := by
  have hmid' : ∀ a b, |chiR (ς₁₂ * (b - a)) * Fmid a b| ≤ cmid := fun a b => by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (chiR_sign_mul_abs_le _ _)).trans (hmid a b)
  refine Sarkozy.Extraction.OpBound.congr' (insertedMultipliers_opBound hp2 h₁ h₂ Fout
    (fun a b => chiR (ς₁₂ * (b - a)) * Fmid a b) Fin hout hmid' hin) (fun x y => ?_) rfl
  ring

/-- **Three-edge paths, other orientation** (`rem:extraction-kernels`): the connector
`χ(ς₂₁(y₁ - x₂))` has modulus at most one and is absorbed into `F_mid(y₁, x₂)` in
`insertedMultipliers_opBound'` (`lem:matching:kernel`(d)); any `ς₂₁` is allowed. -/
theorem threeEdgePath_opBound' (hp2 : p ≠ 2) {ς₁ ς₂ : ZMod p} (h₁ : ς₁ = 1 ∨ ς₁ = -1)
    (h₂ : ς₂ = 1 ∨ ς₂ = -1) (ς₂₁ : ZMod p) (Fout Fmid Fin : ZMod p → ZMod p → ℝ)
    {cout cmid cin : ℝ} (hout : ∀ a b, |Fout a b| ≤ cout) (hmid : ∀ a b, |Fmid a b| ≤ cmid)
    (hin : ∀ a b, |Fin a b| ≤ cin) :
    OpBound univ univ (fun (x y : ZMod p × ZMod p) => chiR (ς₁ * (y.1 - x.1)) *
      chiR (ς₂ * (y.2 - x.2)) * chiR (ς₂₁ * (y.1 - x.2)) * Fout x.1 x.2 * Fmid y.1 x.2 *
        Fin y.1 y.2)
      (Real.sqrt p ^ 2 * (cout * cmid * cin)) := by
  have hmid' : ∀ a b, |chiR (ς₂₁ * (a - b)) * Fmid a b| ≤ cmid := fun a b => by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (chiR_sign_mul_abs_le _ _)).trans (hmid a b)
  refine Sarkozy.Extraction.OpBound.congr' (insertedMultipliers_opBound' hp2 h₁ h₂ Fout
    (fun a b => chiR (ς₂₁ * (a - b)) * Fmid a b) Fin hout hmid' hin) (fun x y => ?_) rfl
  ring

end Sarkozy.Extraction
