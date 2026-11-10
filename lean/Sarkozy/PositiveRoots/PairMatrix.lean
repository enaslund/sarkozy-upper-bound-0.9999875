module

public import Sarkozy.L20Cap.StarMatrix

@[expose] public section

/-!
# The pair-feature matrix of a tilt (`lem:root-pair-matrix`)

`paper/sections/20b_positive_roots.tex`, `lem:root-pair-matrix`. In the coefficient space of
`lem:l20-star-matrix` (W3's index set `Idx = Fin 6 ⊕ supports`, on which the star matrix of the
soft L20 kernel at `Φ̂ = i` is `softM D20`), the linear part `2uH̄` of a tilt adds the pair
coupling
`P = e_{01}e_{45}^* + e_{45}e_{01}^* + e_{23}e_{23}^*` (`pairC`, the three couplings of
`eq:root-score-feature`), and
`M_λ = M + (λ/3) P` (`Mlam`).

Proved here, along the paper's proof:
* (1)–(3) the six vectors `A = √2 v̂`, `Z_⊥ = √13 ẑ_⊥`, `U₊ = √2 û₊`, `U₋ = √2 û₋`, `W = 2ŵ`,
  `E = ê` (unnormalized, with integer data) are pairwise orthogonal of squared lengths
  `2, 13, 2, 2, 4, 1` (`vecs6_orth`), `Z = Z_⊥ + U₊` (`vZ_eq`), `U₊ = e_{01} + e_{45}`,
  `U₋ = e_{01} − e_{45}`; hence Bessel's inequality (`bessel6`);
* (4) the bilinear form of `M_λ` in these coordinates (`bform_Mlam_eq`): with `a = ⟨A,x⟩`,
  `z = ⟨Z,x⟩`, `w = ⟨W,x⟩`, `e = ⟨E,x⟩`, `c₀₁ = x_{01}`, `c₄₅ = x_{45}`,
  `x^*M_λx = āz + z̄a + w̄e + ēw + (λ/3)(c̄₀₁c₄₅ + c̄₄₅c₀₁ + ēe)`, and
  `c̄₀₁c₄₅ + c̄₄₅c₀₁ = (|U₊x|² − |U₋x|²)/2` (`pair_polar`);
* (5) **the lower bound** (`Mlam_lower`): `M_λ ⪰ −g I` for every `g > 0` with
  `3g³ + λg² − 90g − 26λ ≥ 0` (that is, `g ≥ g(λ)` by `RootCubic`), when `0 ≤ λ ≤ 3√26`
  (stated as `λ² ≤ 234`). The proof completes the squares of the `3×3` block
  `[[0,2,√26],[2,λ/3,0],[√26,0,0]]` (`three_block`: the remainder is exactly
  `(3g³ + λg² − 90g − 26λ)/156` times `a²`), of the `2×2` block `[[0,2],[2,λ/3]]`
  (`two_block`) and uses `g ≥ λ/3` for the block `(−λ/3)`;
* **sharpness** (`Mlam_attains`): if `3g³ + λg² − 90g − 26λ = 0`, `g > 0`, the nonzero vector
  `x_g = A − (6/(3g+λ)) U₊ − (2/g) Z_⊥` (the eigenvector of the `3×3` block) has
  `x_g^* M_λ x_g = −g |x_g|²`; so with `Mlam_lower` the least eigenvalue of `M_λ` (the minimum of
  its Rayleigh quotient) is exactly `−g(λ)`;
* **the norm** (`normLe_Mlam`): `‖M_λ‖ ≤ √30 + λ/3` (bilinear form `NormLe`), from W3's
  `‖M‖ ≤ √30` and `‖P‖ ≤ 1`;
* `Mlam` is Hermitian (`Mlam_hermitian`).

The characteristic polynomial
`x^{12}(x + λ/3)(x² − (λ/3)x − 4)(x³ − (λ/3)x² − 30x + 26λ/3)` and the claim that the other
negative eigenvalues are `≥ −max(2, λ/3)` are in `PairCharpoly`; the properties of the root `g(λ)`
of `eq:root-cubic` (existence, uniqueness, `g ∈ (√26, √30]`, `g(0) = √30`, decreasing) are in
`RootCubic`. Downstream (`prop:root-chamber`) only `M_λ ⪰ −g I` and `‖M_λ‖ ≤ √30 + λ/3` are used.
The statement at `Φ̂ = −i` (the complex conjugate matrix, same spectrum) is not repeated.
-/

namespace Sarkozy.PositiveRoots

open Finset Complex Sarkozy.SpectralC Sarkozy.SpectralD.StarMatrix Sarkozy.L20Cap
open scoped BigOperators ComplexConjugate

/-! ## The pair coupling and `M_λ` -/

/-- Integer data of the coordinate vector of the support `T`. -/
def eSZ (T : Finset (Fin 6)) : Finset (Fin 6) → ℤ := fun S => if S = T then 1 else 0

/-- The coordinate vector `e_T` of the support `T` in `ℂ^{U ⊔ 𝒮}`. -/
noncomputable def eS (T : Finset (Fin 6)) : Idx → ℂ := mkVec 0 0 (eSZ T)

theorem vE_eq_eS : vE = eS {2, 3} := rfl

/-- **The pair coupling** `P = e_{01}e_{45}^* + e_{45}e_{01}^* + e_{23}e_{23}^*`
(`lem:root-pair-matrix`; the couplings `e_{01}e_{45}^*`, `e_{23}e_{23}^*`, `e_{45}e_{01}^*` of the
scores `H₀, H₁, H₂` in the coefficient space, `eq:root-score-feature`). -/
noncomputable def pairC (a b : Idx) : ℂ :=
  eS {0, 1} a * conj (eS {4, 5} b) + eS {4, 5} a * conj (eS {0, 1} b) + vE a * conj (vE b)

/-- **The tilted star matrix** `M_λ = M + (λ/3)(e_{01}e_{45}^* + e_{45}e_{01}^* + e_{23}e_{23}^*)`
(`lem:root-pair-matrix`), `M = M(i)` the star matrix of the soft L20 kernel
(`lem:l20-star-matrix`(a), W3's `softM D20`). -/
noncomputable def Mlam (lam : ℝ) (a b : Idx) : ℂ :=
  softM D20 a b + ((lam / 3 : ℝ) : ℂ) * pairC a b

theorem eS_conj (T : Finset (Fin 6)) (a : Idx) : conj (eS T a) = eS T a := by
  rcases a with i | S
  · simp [eS, mkVec]
  · simp only [eS, mkVec, Sum.elim_inr, map_intCast]

theorem pairC_hermitian (a b : Idx) : conj (pairC b a) = pairC a b := by
  unfold pairC
  simp only [map_add, map_mul, Complex.conj_conj]
  have h1 := eS_conj {0, 1}
  have h2 := eS_conj {4, 5}
  have h3 : ∀ a, conj (vE a) = vE a := by rw [vE_eq_eS]; exact eS_conj {2, 3}
  simp only [h1, h2, h3]
  ring

/-- **`M_λ` is Hermitian.** -/
theorem Mlam_hermitian (lam : ℝ) (a b : Idx) : conj (Mlam lam b a) = Mlam lam a b := by
  unfold Mlam
  rw [map_add, map_mul, Complex.conj_ofReal, softM_D20_hermitian, pairC_hermitian]

/-- The bilinear form of the pair coupling:
`w^* P z = \overline{w_{01}} z_{45} + \overline{w_{45}} z_{01} + \overline{w_{23}} z_{23}`. -/
theorem bform_pairC (w z : Idx → ℂ) :
    bform pairC w z = conj (cip (eS {0, 1}) w) * cip (eS {4, 5}) z +
      conj (cip (eS {4, 5}) w) * cip (eS {0, 1}) z + conj (cip vE w) * cip vE z := by
  unfold bform pairC
  rw [← bform_rank_one (eS {0, 1}) (eS {4, 5}) w z, ← bform_rank_one (eS {4, 5}) (eS {0, 1}) w z,
    ← bform_rank_one vE vE w z]
  simp only [← sum_add_distrib]
  refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
  ring

theorem bform_Mlam (lam : ℝ) (w z : Idx → ℂ) :
    bform (Mlam lam) w z = bform (softM D20) w z + ((lam / 3 : ℝ) : ℂ) * bform pairC w z := by
  have e : Mlam lam = fun k l => softM D20 k l + ((lam / 3 : ℝ) : ℂ) * pairC k l := rfl
  rw [e, bform_add, bform_smul]

/-! ## The six orthogonal vectors -/

/-- Support data of `Z_⊥ = Z − e_{01} − e_{45}` (`√13 ẑ_⊥`). -/
def zpS : Finset (Fin 6) → ℤ := fun S => if S = {0, 1} ∨ S = {4, 5} then 0 else ∏ k ∈ S, sZ k

/-- Support data of `U₊ = e_{01} + e_{45}` (`√2 û₊`). -/
def upS : Finset (Fin 6) → ℤ := fun S => if S = {0, 1} ∨ S = {4, 5} then 1 else 0

/-- Support data of `U₋ = e_{01} − e_{45}` (`√2 û₋`). -/
def umS : Finset (Fin 6) → ℤ := fun S => if S = {0, 1} then 1 else if S = {4, 5} then -1 else 0

/-- `Z_⊥ = Z − e_{01} − e_{45} = √13 ẑ_⊥` (step (2) of the proof). -/
noncomputable def vZp : Idx → ℂ := mkVec 0 sZ zpS

/-- `U₊ = e_{01} + e_{45} = √2 û₊`. -/
noncomputable def vUp : Idx → ℂ := mkVec 0 0 upS

/-- `U₋ = e_{01} − e_{45} = √2 û₋`. -/
noncomputable def vUm : Idx → ℂ := mkVec 0 0 umS

theorem zp_up_int : ∀ S : Finset (Fin 6), ∏ k ∈ S, sZ k = zpS S + upS S := by decide

theorem up_int : ∀ S : Finset (Fin 6), upS S = eSZ {0, 1} S + eSZ {4, 5} S := by decide

theorem um_int : ∀ S : Finset (Fin 6), umS S = eSZ {0, 1} S - eSZ {4, 5} S := by decide

/-- **`Z = Z_⊥ + U₊`**: `σ_{01} = σ_{45} = 1`, so `ẑ = √(2/15) û₊ + √(13/15) ẑ_⊥` (step (2)). -/
theorem vZ_eq (k : Idx) : vZ k = vZp k + vUp k := by
  rcases k with i | S
  · simp [vZ, vZp, vUp, mkVec]
  · simp only [vZ, vZp, vUp, mkVec, Sum.elim_inr]
    rw [zp_up_int S.1]
    push_cast
    ring

theorem vUp_eq (k : Idx) : vUp k = eS {0, 1} k + eS {4, 5} k := by
  rcases k with i | S
  · simp [vUp, eS, mkVec]
  · simp only [vUp, eS, mkVec, Sum.elim_inr]
    rw [up_int S.1]
    push_cast
    ring

theorem vUm_eq (k : Idx) : vUm k = eS {0, 1} k - eS {4, 5} k := by
  rcases k with i | S
  · simp [vUm, eS, mkVec]
  · simp only [vUm, eS, mkVec, Sum.elim_inr]
    rw [um_int S.1]
    push_cast
    ring

theorem cip_add_left {ι : Type*} [Fintype ι] {X Y Y' : ι → ℂ} (h : ∀ k, X k = Y k + Y' k)
    (w : ι → ℂ) : cip X w = cip Y w + cip Y' w := by
  unfold cip
  rw [← sum_add_distrib]
  exact sum_congr rfl fun k _ => by rw [h k, map_add]; ring

theorem cip_sub_left {ι : Type*} [Fintype ι] {X Y Y' : ι → ℂ} (h : ∀ k, X k = Y k - Y' k)
    (w : ι → ℂ) : cip X w = cip Y w - cip Y' w := by
  unfold cip
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun k _ => by rw [h k, map_sub]; ring

/-- The six vectors `A, Z_⊥, U₊, U₋, W, E`. -/
noncomputable def vecs6 : Fin 6 → Idx → ℂ := ![vA, vZp, vUp, vUm, vW, vE]

def vecR6 : Fin 6 → Fin 6 → ℤ := ![aZ, 0, 0, 0, wZ, 0]

def vecI6 : Fin 6 → Fin 6 → ℤ := ![0, sZ, 0, 0, 0, 0]

def vecS6 : Fin 6 → Finset (Fin 6) → ℤ := ![0, zpS, upS, umS, 0, eSZ {2, 3}]

/-- The squared lengths `2, 13, 2, 2, 4, 1`. -/
def lens6Z : Fin 6 → ℤ := ![2, 13, 2, 2, 4, 1]

noncomputable def lens6 (a : Fin 6) : ℝ := (lens6Z a : ℝ)

theorem vecs6_eq (a : Fin 6) : vecs6 a = mkVec (vecR6 a) (vecI6 a) (vecS6 a) := by
  fin_cases a <;> rfl

theorem orth_int6 : ∀ a b : Fin 6,
    (∑ i, (vecR6 a i * vecR6 b i + vecI6 a i * vecI6 b i) +
        ∑ S ∈ supports (Fin 6), vecS6 a S * vecS6 b S = if a = b then lens6Z a else 0) ∧
      ∑ i, (vecR6 a i * vecI6 b i - vecI6 a i * vecR6 b i) = 0 := by
  decide

theorem lens6_pos (a : Fin 6) : 0 < lens6 a := by
  have h : 0 < lens6Z a := by fin_cases a <;> decide
  unfold lens6
  exact_mod_cast h

/-- **`A, Z_⊥, U₊, U₋, W, E` are pairwise orthogonal**, of squared lengths `2, 13, 2, 2, 4, 1`
(steps (1)–(2): `v̂, û₊, ẑ_⊥, ŵ, ê, û₋` are orthonormal). -/
theorem vecs6_orth (a b : Fin 6) :
    cip (vecs6 a) (vecs6 b) = if a = b then (lens6 a : ℂ) else 0 := by
  rw [vecs6_eq, vecs6_eq, cip_mkVec, (orth_int6 a b).1, (orth_int6 a b).2]
  unfold lens6
  split_ifs <;> simp

/-- **Bessel's inequality for the six vectors**:
`|⟨A,x⟩|²/2 + |⟨Z_⊥,x⟩|²/13 + |⟨U₊,x⟩|²/2 + |⟨U₋,x⟩|²/2 + |⟨W,x⟩|²/4 + |⟨E,x⟩|² ≤ |x|²`. -/
theorem bessel6 (x : Idx → ℂ) :
    ‖cip vA x‖ ^ 2 / 2 + ‖cip vZp x‖ ^ 2 / 13 + ‖cip vUp x‖ ^ 2 / 2 + ‖cip vUm x‖ ^ 2 / 2 +
      ‖cip vW x‖ ^ 2 / 4 + ‖cip vE x‖ ^ 2 ≤ ∑ k, ‖x k‖ ^ 2 := by
  have h := bessel_orth vecs6 lens6 lens6_pos vecs6_orth x
  have l0 : lens6 0 = 2 := by norm_num [lens6, lens6Z]
  have l1 : lens6 1 = 13 := by norm_num [lens6, lens6Z]
  have l2 : lens6 2 = 2 := by norm_num [lens6, lens6Z]
  have l3 : lens6 3 = 2 := by norm_num [lens6, lens6Z]
  have l4 : lens6 4 = 4 := by norm_num [lens6, lens6Z]
  have l5 : lens6 5 = 1 := by norm_num [lens6, lens6Z]
  rw [Fin.sum_univ_six, l0, l1, l2, l3, l4, l5, div_one] at h
  exact h

/-! ## The form of `M_λ` in the six coordinates -/

/-- **The polarization of the core coupling** (step (3)):
`c̄₀₁c₄₅ + c̄₄₅c₀₁ = (|U₊x|² − |U₋x|²)/2`, i.e.
`e_{01}e_{45}^* + e_{45}e_{01}^* = û₊û₊^* − û₋û₋^*`. -/
theorem pair_polar (x : Idx → ℂ) :
    conj (cip (eS {0, 1}) x) * cip (eS {4, 5}) x + conj (cip (eS {4, 5}) x) * cip (eS {0, 1}) x =
      ((1 / 2 : ℝ) : ℂ) * (conj (cip vUp x) * cip vUp x - conj (cip vUm x) * cip vUm x) := by
  rw [cip_add_left vUp_eq, cip_sub_left vUm_eq]
  simp only [map_add, map_sub]
  push_cast
  ring

/-- **The form of `M_λ`** (step (4)): with `a = ⟨A,x⟩`, `z = ⟨Z,x⟩ = ⟨Z_⊥,x⟩ + ⟨U₊,x⟩`,
`w = ⟨W,x⟩`, `e = ⟨E,x⟩`,
`x^*M_λx = āz + z̄a + w̄e + ēw + (λ/3)((|U₊x|² − |U₋x|²)/2 + |e|²)`. -/
theorem bform_Mlam_eq (lam : ℝ) (x : Idx → ℂ) :
    bform (Mlam lam) x x =
      conj (cip vA x) * (cip vZp x + cip vUp x) + conj (cip vZp x + cip vUp x) * cip vA x +
        conj (cip vW x) * cip vE x + conj (cip vE x) * cip vW x +
        ((lam / 3 : ℝ) : ℂ) * (((1 / 2 : ℝ) : ℂ) *
          (conj (cip vUp x) * cip vUp x - conj (cip vUm x) * cip vUm x) +
          conj (cip vE x) * cip vE x) := by
  rw [bform_Mlam, bform_softM_D20, bform_pairC, pair_polar, cip_add_left vZ_eq]

/-- The real part of `z̄w`. -/
theorem re_conj_mul (z w : ℂ) : (conj z * w).re = z.re * w.re + z.im * w.im := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- **The real form of `M_λ`**: with `a, y, u, d, w, e` the coordinates along
`A, Z_⊥, U₊, U₋, W, E`,
`Re x^*M_λx = 2 Re(ā(y + u)) + 2 Re(w̄e) + (λ/3)((|u|² − |d|²)/2 + |e|²)`. -/
theorem re_bform_Mlam (lam : ℝ) (x : Idx → ℂ) :
    (bform (Mlam lam) x x).re =
      2 * ((cip vA x).re * ((cip vZp x).re + (cip vUp x).re) +
          (cip vA x).im * ((cip vZp x).im + (cip vUp x).im)) +
        2 * ((cip vW x).re * (cip vE x).re + (cip vW x).im * (cip vE x).im) +
        lam / 3 * (((cip vUp x).re ^ 2 + (cip vUp x).im ^ 2 - (cip vUm x).re ^ 2 -
            (cip vUm x).im ^ 2) / 2 + ((cip vE x).re ^ 2 + (cip vE x).im ^ 2)) := by
  rw [bform_Mlam_eq]
  simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.sub_re, re_conj_mul,
    Complex.add_im]
  ring

/-! ## The blocks -/

/-- **The `3×3` block** `[[0,2,√26],[2,λ/3,0],[√26,0,0]] + gI ⪰ 0` (step (5)), in the unnormalized
coordinates `a = ⟨A,x⟩ = √2 α`, `u = ⟨U₊,x⟩ = √2 β`, `y = ⟨Z_⊥,x⟩ = √13 γ`: if `g > 0`, `λ ≥ 0`
and `3g³ + λg² − 90g − 26λ ≥ 0`, then
`2a(y + u) + (λ/6)u² + g(a²/2 + y²/13 + u²/2) ≥ 0`. With `c₁ = (3g + λ)/6`, `c₂ = g/13` the
expression times `c₁c₂` is `c₂(c₁u + a)² + c₁(c₂y + a)² + a²(3g³ + λg² − 90g − 26λ)/156`. -/
theorem three_block {lam g : ℝ} (hlam : 0 ≤ lam) (hg : 0 < g)
    (hf : 0 ≤ 3 * g ^ 3 + lam * g ^ 2 - 90 * g - 26 * lam) (a u y : ℝ) :
    0 ≤ 2 * a * (y + u) + lam / 6 * u ^ 2 + g * (a ^ 2 / 2 + y ^ 2 / 13 + u ^ 2 / 2) := by
  set c₁ := (3 * g + lam) / 6 with hc₁
  set c₂ := g / 13 with hc₂
  have h1 : 0 < c₁ := by rw [hc₁]; positivity
  have h2 : 0 < c₂ := by rw [hc₂]; positivity
  have key : c₁ * c₂ * (2 * a * (y + u) + lam / 6 * u ^ 2 + g * (a ^ 2 / 2 + y ^ 2 / 13 +
      u ^ 2 / 2)) = c₂ * (c₁ * u + a) ^ 2 + c₁ * (c₂ * y + a) ^ 2 +
        a ^ 2 * (3 * g ^ 3 + lam * g ^ 2 - 90 * g - 26 * lam) / 156 := by
    rw [hc₁, hc₂]
    ring
  have hrhs : 0 ≤ c₂ * (c₁ * u + a) ^ 2 + c₁ * (c₂ * y + a) ^ 2 +
      a ^ 2 * (3 * g ^ 3 + lam * g ^ 2 - 90 * g - 26 * lam) / 156 := by positivity
  rw [← key] at hrhs
  exact (mul_nonneg_iff_of_pos_left (mul_pos h1 h2)).mp hrhs

/-- **The `2×2` block** `[[0,2],[2,λ/3]] + gI ⪰ 0`, in the coordinates `w = ⟨W,x⟩ = 2ω`,
`e = ⟨E,x⟩`: if `g > 0` and `g(g + λ/3) ≥ 4`, then `2we + (λ/3)e² + g(w²/4 + e²) ≥ 0`. -/
theorem two_block {lam g : ℝ} (hg : 0 < g) (h4 : 4 ≤ g * (g + lam / 3)) (w e : ℝ) :
    0 ≤ 2 * w * e + lam / 3 * e ^ 2 + g * (w ^ 2 / 4 + e ^ 2) := by
  have key : g / 4 * (2 * w * e + lam / 3 * e ^ 2 + g * (w ^ 2 / 4 + e ^ 2)) =
      (g / 4 * w + e) ^ 2 + (g * (g + lam / 3) - 4) / 4 * e ^ 2 := by ring
  have hrhs : 0 ≤ (g / 4 * w + e) ^ 2 + (g * (g + lam / 3) - 4) / 4 * e ^ 2 := by
    have : 0 ≤ (g * (g + lam / 3) - 4) / 4 := by linarith
    positivity
  rw [← key] at hrhs
  exact (mul_nonneg_iff_of_pos_left (by positivity)).mp hrhs

/-- A positive `g` with `3g³ + λg² − 90g − 26λ ≥ 0` (`λ ≥ 0`) has `g² ≥ 26`. -/
theorem sq_ge_26 {lam g : ℝ} (hlam : 0 ≤ lam) (hg : 0 < g)
    (hf : 0 ≤ 3 * g ^ 3 + lam * g ^ 2 - 90 * g - 26 * lam) : 26 ≤ g ^ 2 := by
  by_contra h
  push Not at h
  have h1 : 3 * g * (g ^ 2 - 30) < 0 := mul_neg_of_pos_of_neg (by positivity) (by linarith)
  have h2 : lam * (g ^ 2 - 26) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlam (by linarith)
  nlinarith

/-! ## The lower bound, its sharpness and the norm -/

/-- **`lem:root-pair-matrix`, the lower bound**: for `0 ≤ λ ≤ 3√26` (`λ² ≤ 234`) and every
`g > 0` with `3g³ + λg² − 90g − 26λ ≥ 0` (equivalently `g ≥ g(λ)`, the root of
`eq:root-cubic`; `RootCubic.cubic_nonneg_iff`), `M_λ ⪰ −g I`:
`Re x^*M_λx ≥ −g |x|²` for every `x`. -/
theorem Mlam_lower {lam g : ℝ} (hlam : 0 ≤ lam) (hlam2 : lam ^ 2 ≤ 234) (hg : 0 < g)
    (hf : 0 ≤ 3 * g ^ 3 + lam * g ^ 2 - 90 * g - 26 * lam) (x : Idx → ℂ) :
    -g * ∑ k, ‖x k‖ ^ 2 ≤ (bform (Mlam lam) x x).re := by
  have hB := bessel6 x
  rw [re_bform_Mlam]
  have h26 := sq_ge_26 hlam hg hf
  have hl3 : lam ≤ 3 * g := by nlinarith
  have h4 : 4 ≤ g * (g + lam / 3) := by nlinarith
  have hA := three_block hlam hg hf (cip vA x).re (cip vUp x).re (cip vZp x).re
  have hA' := three_block hlam hg hf (cip vA x).im (cip vUp x).im (cip vZp x).im
  have hW := two_block hg h4 (cip vW x).re (cip vE x).re
  have hW' := two_block hg h4 (cip vW x).im (cip vE x).im
  have hD : 0 ≤ (g / 2 - lam / 6) * ((cip vUm x).re ^ 2 + (cip vUm x).im ^ 2) :=
    mul_nonneg (by linarith) (by positivity)
  have hn : ∀ c : ℂ, ‖c‖ ^ 2 = c.re ^ 2 + c.im ^ 2 := fun c => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hn (cip vA x), hn (cip vZp x), hn (cip vUp x), hn (cip vUm x), hn (cip vW x),
    hn (cip vE x)] at hB
  have hgB := mul_le_mul_of_nonneg_left hB hg.le
  linarith

/-- `⟨X, c₁Y₁ + c₂Y₂ + c₃Y₃⟩ = c₁⟨X,Y₁⟩ + c₂⟨X,Y₂⟩ + c₃⟨X,Y₃⟩`. -/
theorem cip_lin3 {ι : Type*} [Fintype ι] (X Y₁ Y₂ Y₃ : ι → ℂ) (c₁ c₂ c₃ : ℂ) :
    cip X (fun k => c₁ * Y₁ k + c₂ * Y₂ k + c₃ * Y₃ k) =
      c₁ * cip X Y₁ + c₂ * cip X Y₂ + c₃ * cip X Y₃ := by
  unfold cip
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact sum_congr rfl fun k _ => by ring

/-- `⟨c₁Y₁ + c₂Y₂ + c₃Y₃, w⟩ = c̄₁⟨Y₁,w⟩ + c̄₂⟨Y₂,w⟩ + c̄₃⟨Y₃,w⟩`. -/
theorem cip_lin3_left {ι : Type*} [Fintype ι] {X : ι → ℂ} (Y₁ Y₂ Y₃ : ι → ℂ) (c₁ c₂ c₃ : ℂ)
    (h : ∀ k, X k = c₁ * Y₁ k + c₂ * Y₂ k + c₃ * Y₃ k) (w : ι → ℂ) :
    cip X w = conj c₁ * cip Y₁ w + conj c₂ * cip Y₂ w + conj c₃ * cip Y₃ w := by
  unfold cip
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact sum_congr rfl fun k _ => by rw [h k]; simp only [map_add, map_mul]; ring

/-- The eigenvector `x_g = A + βU₊ + γZ_⊥` (`β = −6/(3g+λ)`, `γ = −2/g`) of the `3×3` block. -/
noncomputable def xg (β γ : ℝ) : Idx → ℂ := fun k => 1 * vA k + (β : ℂ) * vUp k + (γ : ℂ) * vZp k

theorem cip_table6 :
    cip vA vA = 2 ∧ cip vA vUp = 0 ∧ cip vA vZp = 0 ∧
    cip vZp vA = 0 ∧ cip vZp vUp = 0 ∧ cip vZp vZp = 13 ∧
    cip vUp vA = 0 ∧ cip vUp vUp = 2 ∧ cip vUp vZp = 0 ∧
    cip vUm vA = 0 ∧ cip vUm vUp = 0 ∧ cip vUm vZp = 0 ∧
    cip vW vA = 0 ∧ cip vW vUp = 0 ∧ cip vW vZp = 0 ∧
    cip vE vA = 0 ∧ cip vE vUp = 0 ∧ cip vE vZp = 0 := by
  have t : ∀ a b : Fin 6, cip (vecs6 a) (vecs6 b) = ((if a = b then lens6Z a else 0 : ℤ) : ℂ) := by
    intro a b
    rw [vecs6_orth]
    unfold lens6
    split_ifs <;> simp
  refine ⟨(t 0 0).trans ?_, (t 0 2).trans ?_, (t 0 1).trans ?_, (t 1 0).trans ?_,
    (t 1 2).trans ?_, (t 1 1).trans ?_, (t 2 0).trans ?_, (t 2 2).trans ?_, (t 2 1).trans ?_,
    (t 3 0).trans ?_, (t 3 2).trans ?_, (t 3 1).trans ?_, (t 4 0).trans ?_, (t 4 2).trans ?_,
    (t 4 1).trans ?_, (t 5 0).trans ?_, (t 5 2).trans ?_, (t 5 1).trans ?_⟩ <;>
    norm_num [lens6Z]

/-- **`lem:root-pair-matrix`, sharpness**: if `g > 0` is a root of `eq:root-cubic`,
`3g³ + λg² − 90g − 26λ = 0` (`λ ≥ 0`), the nonzero vector
`x_g = A − (6/(3g+λ)) U₊ − (2/g) Z_⊥` has `x_g^*M_λx_g = −g|x_g|²`. With `Mlam_lower`, the least
eigenvalue of `M_λ` is exactly `−g(λ)`. -/
theorem Mlam_attains {lam g : ℝ} (hlam : 0 ≤ lam) (hg : 0 < g)
    (hf : 3 * g ^ 3 + lam * g ^ 2 - 90 * g - 26 * lam = 0) :
    (∑ k, ‖xg (-6 / (3 * g + lam)) (-2 / g) k‖ ^ 2 ≠ 0) ∧
    (bform (Mlam lam) (xg (-6 / (3 * g + lam)) (-2 / g)) (xg (-6 / (3 * g + lam)) (-2 / g))).re =
      -g * ∑ k, ‖xg (-6 / (3 * g + lam)) (-2 / g) k‖ ^ 2 := by
  set β : ℝ := -6 / (3 * g + lam) with hβ
  set γ : ℝ := -2 / g with hγ
  obtain ⟨hAA, hAU, hAZ, hZA, hZU, hZZ, hUA, hUU, hUZ, hMA, hMU, hMZ, hWA, hWU, hWZ, hEA, hEU,
    hEZ⟩ := cip_table6
  have hx : xg β γ = fun k => 1 * vA k + (β : ℂ) * vUp k + (γ : ℂ) * vZp k := rfl
  have ca : cip vA (xg β γ) = 2 := by
    rw [hx, cip_lin3, hAA, hAU, hAZ]; ring
  have cz : cip vZp (xg β γ) = 13 * (γ : ℂ) := by
    rw [hx, cip_lin3, hZA, hZU, hZZ]; ring
  have cu : cip vUp (xg β γ) = 2 * (β : ℂ) := by
    rw [hx, cip_lin3, hUA, hUU, hUZ]; ring
  have cm : cip vUm (xg β γ) = 0 := by
    rw [hx, cip_lin3, hMA, hMU, hMZ]; ring
  have cw : cip vW (xg β γ) = 0 := by
    rw [hx, cip_lin3, hWA, hWU, hWZ]; ring
  have ce : cip vE (xg β γ) = 0 := by
    rw [hx, cip_lin3, hEA, hEU, hEZ]; ring
  -- `|x_g|² = ⟨x_g, x_g⟩ = 2 + 2β² + 13γ²`
  have hnorm : ∑ k, ‖xg β γ k‖ ^ 2 = 2 + 2 * β ^ 2 + 13 * γ ^ 2 := by
    have e1 : ((∑ k, ‖xg β γ k‖ ^ 2 : ℝ) : ℂ) = cip (xg β γ) (xg β γ) := by
      unfold cip
      push_cast
      refine sum_congr rfl fun k _ => ?_
      rw [← Complex.mul_conj', mul_comm]
    have e2 : cip (xg β γ) (xg β γ) =
        conj (1 : ℂ) * cip vA (xg β γ) + conj (β : ℂ) * cip vUp (xg β γ) +
          conj (γ : ℂ) * cip vZp (xg β γ) :=
      cip_lin3_left vA vUp vZp 1 (β : ℂ) (γ : ℂ) (fun k => rfl) (xg β γ)
    rw [e2, ca, cu, cz, Complex.conj_ofReal, Complex.conj_ofReal, map_one] at e1
    have e3 : ((2 + 2 * β ^ 2 + 13 * γ ^ 2 : ℝ) : ℂ) = 1 * 2 + (β : ℂ) * (2 * β) +
        (γ : ℂ) * (13 * γ) := by push_cast; ring
    exact_mod_cast e1.trans e3.symm
  have h3 : 0 < 3 * g + lam := by positivity
  refine ⟨?_, ?_⟩
  · rw [hnorm]
    positivity
  rw [re_bform_Mlam, hnorm, ca, cz, cu, cm, cw, ce]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.zero_re, Complex.zero_im, Complex.re_ofNat, Complex.im_ofNat]
  rw [hβ, hγ]
  field_simp
  linear_combination (36 * g + 12 * lam) * hf

/-- `‖P‖ ≤ 1`: `|w^*Pz| ≤ |w||z|`. -/
theorem normLe_pairC : NormLe pairC 1 := by
  intro w z
  rw [bform_pairC]
  -- Bessel for the orthonormal `e_{01}, e_{45}, e_{23}`
  have horth : ∀ a b : Fin 3, cip (![eS {0, 1}, eS {4, 5}, vE] a) (![eS {0, 1}, eS {4, 5}, vE] b) =
      if a = b then ((1 : ℝ) : ℂ) else 0 := by
    have hint : ∀ a b : Fin 3,
        (∑ S ∈ supports (Fin 6), (![eSZ {0, 1}, eSZ {4, 5}, eSZ {2, 3}] a S) *
          (![eSZ {0, 1}, eSZ {4, 5}, eSZ {2, 3}] b S) = if a = b then 1 else 0) := by decide
    intro a b
    have ea : ![eS {0, 1}, eS {4, 5}, vE] a =
        mkVec 0 0 (![eSZ {0, 1}, eSZ {4, 5}, eSZ {2, 3}] a) := by
      fin_cases a <;> rfl
    have eb : ![eS {0, 1}, eS {4, 5}, vE] b =
        mkVec 0 0 (![eSZ {0, 1}, eSZ {4, 5}, eSZ {2, 3}] b) := by
      fin_cases b <;> rfl
    rw [ea, eb, cip_mkVec, hint a b]
    split_ifs <;> simp
  have hbw := bessel_orth ![eS {0, 1}, eS {4, 5}, vE] (fun _ => 1) (fun _ => one_pos) horth w
  have hbz := bessel_orth ![eS {0, 1}, eS {4, 5}, vE] (fun _ => 1) (fun _ => one_pos) horth z
  simp only [Fin.sum_univ_three, div_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hbw hbz
  set a₁ := ‖cip (eS {0, 1}) w‖
  set a₂ := ‖cip (eS {4, 5}) w‖
  set a₃ := ‖cip vE w‖
  set b₁ := ‖cip (eS {0, 1}) z‖
  set b₂ := ‖cip (eS {4, 5}) z‖
  set b₃ := ‖cip vE z‖
  have htri : ‖conj (cip (eS {0, 1}) w) * cip (eS {4, 5}) z +
      conj (cip (eS {4, 5}) w) * cip (eS {0, 1}) z + conj (cip vE w) * cip vE z‖ ≤
      a₁ * b₂ + a₂ * b₁ + a₃ * b₃ := by
    have e1 := norm_add_le (conj (cip (eS {0, 1}) w) * cip (eS {4, 5}) z +
      conj (cip (eS {4, 5}) w) * cip (eS {0, 1}) z) (conj (cip vE w) * cip vE z)
    have e2 := norm_add_le (conj (cip (eS {0, 1}) w) * cip (eS {4, 5}) z)
      (conj (cip (eS {4, 5}) w) * cip (eS {0, 1}) z)
    simp only [norm_mul, Complex.norm_conj] at e1 e2
    linarith
  have hW0 : 0 ≤ ∑ k, ‖w k‖ ^ 2 := sum_nonneg fun k _ => sq_nonneg _
  have hZ0 : 0 ≤ ∑ k, ‖z k‖ ^ 2 := sum_nonneg fun k _ => sq_nonneg _
  have hCS : (a₁ * b₂ + a₂ * b₁ + a₃ * b₃) ^ 2 ≤
      (a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2) * (b₁ ^ 2 + b₂ ^ 2 + b₃ ^ 2) := by
    nlinarith [sq_nonneg (a₁ * b₁ - a₂ * b₂), sq_nonneg (a₁ * b₃ - a₃ * b₂),
      sq_nonneg (a₂ * b₃ - a₃ * b₁)]
  have hsq : (a₁ * b₂ + a₂ * b₁ + a₃ * b₃) ^ 2 ≤ (∑ k, ‖w k‖ ^ 2) * (∑ k, ‖z k‖ ^ 2) :=
    hCS.trans (mul_le_mul hbw hbz (by positivity) hW0)
  have hle := Real.abs_le_sqrt hsq
  rw [Real.sqrt_mul hW0] at hle
  calc _ ≤ a₁ * b₂ + a₂ * b₁ + a₃ * b₃ := htri
    _ ≤ |a₁ * b₂ + a₂ * b₁ + a₃ * b₃| := le_abs_self _
    _ ≤ _ := hle
    _ = 1 * vnorm w * vnorm z := by unfold vnorm; ring

/-- **`lem:root-pair-matrix`, the norm**: `‖M_λ‖ ≤ √30 + λ/3` for `λ ≥ 0` (bilinear `NormLe`), from
`‖M‖ ≤ √30` (`lem:l20-star-matrix`(a), W3's `normLe_softM_D20`) and `‖P‖ ≤ 1`. -/
theorem normLe_Mlam {lam : ℝ} (hlam : 0 ≤ lam) : NormLe (Mlam lam) (Real.sqrt 30 + lam / 3) := by
  intro w z
  rw [bform_Mlam]
  have h1 := normLe_softM_D20 w z
  have h2 := normLe_pairC w z
  have hn : ‖((lam / 3 : ℝ) : ℂ) * bform pairC w z‖ = lam / 3 * ‖bform pairC w z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hw := vnorm_nonneg w
  have hz := vnorm_nonneg z
  calc _ ≤ ‖bform (softM D20) w z‖ + ‖((lam / 3 : ℝ) : ℂ) * bform pairC w z‖ := norm_add_le _ _
    _ ≤ Real.sqrt 30 * vnorm w * vnorm z + lam / 3 * (1 * vnorm w * vnorm z) := by
        rw [hn]
        exact add_le_add h1 (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ = _ := by ring

end Sarkozy.PositiveRoots
