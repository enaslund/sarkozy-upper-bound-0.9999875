module

public import Sarkozy.JointRows.PaleyCx
public import Sarkozy.ExtractionK.PinnedCollision

/-!
# The pinned collision bound as a form bound (`prop:pinned-collision`)

Sources: `paper/sections/16_extraction.tex`, the setting of the pinned subsection
(`μ` is the uniform law on `𝓘_pin`, and `μ = λ(· | 𝓘_pin)` for `λ = ⊗_i λ_i`, `λ_i` the uniform
law on the allowed set of `i`), `prop:pinned-collision`, and `lem:joint-rows` (the raw kernels
`K_•` and their collision parts); `lem:spec:expansion` for the split of the raw kernel.

X1's `ExtractionK.pinned_collision_opBound` bounds the matrix `K/|𝓘_pin|`, `K = pinKer ς`, in
`ℓ²(𝓘_pin)`. The joint-rows theorems use form bounds relative to `μ = λ(· | 𝓘)`
(`FiveType.FormBound`). Here:

* `condLaw_weight_of_const`: if `λ` is constant on a finset `s` and `𝓘 = s`, then `λ(· | 𝓘)` is
  the uniform law on `s`. The paper's `λ` is constant on `∏_i (allowed set of i) ⊇ 𝓘_pin`.
* `formBound_of_opBound`: for `μ` uniform on `s`, `OpBound s s (K/|s|) c` gives
  `FormBound μ K c` (Cauchy–Schwarz on `s`; `μ` vanishes off `s`).
* `formBound_pinKer`: **`prop:pinned-collision` as a form bound**. `‖T^pin_coll‖ ≤ (D_X D_Y)^{1/2}`
  on `L²(μ)` (`collBound`) for the concrete collision kernel `pinKer ς`, under X1's hypotheses
  (`Labellings.WeilBound` is Weil's theorem, `thm:weil`(a)).
* `rawKer`: the raw kernel `K_• = 1{x([n]) ∩ y([n]) = ∅} ∏_{(i,j)} (1 + χ_ij)` of
  `lem:joint-rows`, and `rawKer_add_pinKer`: `K_• + T_coll = ∏_{(i,j)} (1 + χ_ij)`, the
  collision split of `lem:spec:expansion`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows

open Sarkozy.FiveType

namespace Coll

/-- The pinned labellings `𝔽_p^{[n]}` of `n` coordinates. -/
abbrev Lab (p nv : ℕ) : Type := Fin nv → ZMod p

section Bridge

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- **`λ(· | 𝓘)` is uniform on `s`** when `𝓘 = s` and `λ` is constant on `s`. -/
theorem condLaw_weight_of_const (lam : FiniteLaw Ω) (I : Ω → Prop) (s : Finset Ω)
    (hI : ∀ x, I x ↔ x ∈ s) (hlam : ∀ x y, x ∈ s → y ∈ s → lam.weight x = lam.weight y)
    (hP : 0 < Peyre.prob lam I) (x : Ω) :
    (Peyre.condLaw lam I hP).weight x = if x ∈ s then ((s.card : ℝ))⁻¹ else 0 := by
  have hind : ∀ y, Peyre.ind I y = if y ∈ s then 1 else 0 := by
    intro y
    by_cases hy : y ∈ s
    · rw [Peyre.ind_of_pos ((hI y).mpr hy)]
      simp only [hy, ↓reduceIte]
    · rw [Peyre.ind_of_neg (fun h => hy ((hI y).mp h))]
      simp only [hy, ↓reduceIte]
  have hprob : Peyre.prob lam I = ∑ y ∈ s, lam.weight y := by
    unfold Peyre.prob FiniteLaw.expect
    simp only [hind, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [Peyre.cond_weight, hind]
  by_cases hx : x ∈ s
  · simp only [hx, ↓reduceIte, one_mul]
    rw [hprob, Finset.sum_congr rfl fun y hy => hlam y x hy hx, Finset.sum_const, nsmul_eq_mul]
    have hw : lam.weight x ≠ 0 := by
      intro h0
      have : Peyre.prob lam I = 0 := by
        rw [hprob, Finset.sum_congr rfl fun y hy => hlam y x hy hx, h0, Finset.sum_const_zero]
      linarith
    field_simp
  · simp only [hx, ↓reduceIte, zero_mul, zero_div]

/-- **Form bound from an `ℓ²(s)` operator bound**, for `μ` uniform on `s`. -/
theorem formBound_of_opBound (μ : FiniteLaw Ω) (s : Finset Ω)
    (hμ : ∀ x, μ.weight x = if x ∈ s then ((s.card : ℝ))⁻¹ else 0)
    (K : Ω → Ω → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hop : Influence.OpBound s s (fun x y => K x y / s.card) c) : FormBound μ K c := by
  intro Φ Ψ
  set N : ℝ := (s.card : ℝ) with hN
  have hN0 : 0 ≤ N⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hμs : ∀ x ∈ s, μ.weight x = N⁻¹ := fun x hx => by
    rw [hμ]
    simp only [hx, ↓reduceIte]
  have hμn : ∀ x, x ∉ s → μ.weight x = 0 := fun x hx => by
    rw [hμ]
    simp only [hx, ↓reduceIte]
  have hkf : kf μ K Φ Ψ = N⁻¹ * ∑ x ∈ s, Φ x * ∑ y ∈ s, K x y / N * Ψ y := by
    unfold kf
    rw [← Finset.sum_subset (Finset.subset_univ s), Finset.mul_sum]
    · refine Finset.sum_congr rfl fun x hx => ?_
      rw [← Finset.sum_subset (Finset.subset_univ s), Finset.mul_sum, Finset.mul_sum]
      · refine Finset.sum_congr rfl fun y hy => ?_
        rw [hμs x hx, hμs y hy, div_eq_mul_inv]
        ring
      · intro y _ hy
        rw [hμn y hy, mul_zero, zero_mul]
    · intro x _ hx
      simp only [hμn x hx, zero_mul, Finset.sum_const_zero]
  have hnrm : ∀ U : Ω → ℝ, nrm μ U = Real.sqrt N⁻¹ * Real.sqrt (∑ x ∈ s, U x ^ 2) := by
    intro U
    rw [← Real.sqrt_mul hN0]
    unfold nrm ip FiniteLaw.expect
    congr 1
    rw [← Finset.sum_subset (Finset.subset_univ s), Finset.mul_sum]
    · refine Finset.sum_congr rfl fun x hx => ?_
      rw [hμs x hx]
      ring
    · intro x _ hx
      rw [hμn x hx, zero_mul]
  -- Cauchy–Schwarz and the operator bound
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s Φ (fun x => ∑ y ∈ s, K x y / N * Ψ y)
  have hop' := hop Ψ
  have hsq : (∑ x ∈ s, Φ x * ∑ y ∈ s, K x y / N * Ψ y) ^ 2 ≤
      (c * Real.sqrt (∑ x ∈ s, Φ x ^ 2) * Real.sqrt (∑ y ∈ s, Ψ y ^ 2)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun x _ => sq_nonneg _),
      Real.sq_sqrt (Finset.sum_nonneg fun y _ => sq_nonneg _)]
    calc (∑ x ∈ s, Φ x * ∑ y ∈ s, K x y / N * Ψ y) ^ 2
        ≤ (∑ x ∈ s, Φ x ^ 2) * ∑ x ∈ s, (∑ y ∈ s, K x y / N * Ψ y) ^ 2 := hcs
      _ ≤ (∑ x ∈ s, Φ x ^ 2) * (c ^ 2 * ∑ y ∈ s, Ψ y ^ 2) :=
        mul_le_mul_of_nonneg_left hop' (Finset.sum_nonneg fun x _ => sq_nonneg _)
      _ = c ^ 2 * (∑ x ∈ s, Φ x ^ 2) * ∑ y ∈ s, Ψ y ^ 2 := by ring
  have habs : |∑ x ∈ s, Φ x * ∑ y ∈ s, K x y / N * Ψ y| ≤
      c * Real.sqrt (∑ x ∈ s, Φ x ^ 2) * Real.sqrt (∑ y ∈ s, Ψ y ^ 2) := by
    have h0 : 0 ≤ c * Real.sqrt (∑ x ∈ s, Φ x ^ 2) * Real.sqrt (∑ y ∈ s, Ψ y ^ 2) := by
      positivity
    exact abs_le_of_sq_le_sq' hsq h0 |> fun h => abs_le.mpr h
  rw [hkf, abs_mul, abs_of_nonneg hN0, hnrm, hnrm]
  have hsN : Real.sqrt N⁻¹ * Real.sqrt N⁻¹ = N⁻¹ := Real.mul_self_sqrt hN0
  calc N⁻¹ * |∑ x ∈ s, Φ x * ∑ y ∈ s, K x y / N * Ψ y|
      ≤ N⁻¹ * (c * Real.sqrt (∑ x ∈ s, Φ x ^ 2) * Real.sqrt (∑ y ∈ s, Ψ y ^ 2)) :=
        mul_le_mul_of_nonneg_left habs hN0
    _ = c * (Real.sqrt N⁻¹ * Real.sqrt (∑ x ∈ s, Φ x ^ 2)) *
        (Real.sqrt N⁻¹ * Real.sqrt (∑ x ∈ s, Ψ x ^ 2)) := by
        linear_combination
          (-(c * Real.sqrt (∑ x ∈ s, Φ x ^ 2) * Real.sqrt (∑ x ∈ s, Ψ x ^ 2))) * hsN

end Bridge

section Pinned

variable {p : ℕ} [Fact p.Prime] {nv : ℕ}

/-- `(D_X D_Y)^{1/2}` of `prop:pinned-collision`, for the sign data `ς` (`z = |𝓜|` fixed labels,
at most `ϖ` pins per coordinate). -/
noncomputable def collBound (p z ϖ : ℕ) {nv : ℕ} (ς : Fin nv → Fin nv → ℤ) : ℝ :=
  Real.sqrt (ExtractionK.pinD p z ϖ (ExtractionK.pinNX ς) * ExtractionK.pinD p z ϖ
    (ExtractionK.pinNY ς))

/-- **`prop:pinned-collision` as a form bound on `L²(μ)`**, `μ = λ(· | 𝓘_pin)`: the collision
kernel `pinKer ς` relative to `μ ⊗ μ` has `‖T^pin_coll‖ ≤ (D_X D_Y)^{1/2}`. The hypotheses are
X1's (`Labellings.WeilBound` is `thm:weil`(a)), with `λ` constant on `𝓘_pin` (`hlam`). -/
theorem formBound_pinKer (hW : Labellings.WeilBound (ZMod p)) (M : Finset (ZMod p))
    (pin : Fin nv → ZMod p → ℤ) (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ϖ : ℕ) (hϖ : ∀ j, ExtractionK.pinCount pin j ≤ ϖ)
    (he : ExtractionK.ePin p nv M.card ϖ < 1) (ς : Fin nv → Fin nv → ℤ)
    (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1)
    (lam : FiniteLaw (Lab p nv)) (I : Lab p nv → Prop)
    (hI : ∀ x, I x ↔ x ∈ ExtractionK.pinLab M pin)
    (hlam : ∀ x y, x ∈ ExtractionK.pinLab M pin → y ∈ ExtractionK.pinLab M pin →
      lam.weight x = lam.weight y)
    (hP : 0 < Peyre.prob lam I) :
    FormBound (Peyre.condLaw lam I hP) (ExtractionK.pinKer ς) (collBound p M.card ϖ ς) := by
  have hcard : ((Fintype.card (ZMod p) : ℕ) : ℝ) = p := by rw [ZMod.card]
  have he' : ExtractionK.ePin (Fintype.card (ZMod p)) nv M.card ϖ < 1 := by
    rw [hcard]
    exact he
  have hop := ExtractionK.pinned_collision_opBound hW M pin hpin hpinM ϖ hϖ he' ς hς
  rw [hcard] at hop
  exact formBound_of_opBound _ _ (condLaw_weight_of_const lam I _ hI hlam hP) _
    (Real.sqrt_nonneg _) hop

end Pinned

section Raw

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {nv : ℕ}

/-- **The raw kernel `K_•` of a pinned row** (`lem:joint-rows`): the indicator that
`x([n]) ∩ y([n]) = ∅`, times `∏_{(i,j)} (1 + χ_ij(x, y))`, `χ_ij(x, y) = χ(ς_ij(y_j - x_i))`. -/
noncomputable def rawKer (ς : Fin nv → Fin nv → ℤ) (x y : Fin nv → F) : ℝ :=
  (if ∃ i j, x i = y j then (0 : ℝ) else 1) * ∏ j, ExtractionK.pinOmega ς x j (y j)

/-- **The collision split** (`lem:spec:expansion`): `K_• + T_coll = ∏_{(i,j)} (1 + χ_ij)`. -/
theorem rawKer_add_pinKer (ς : Fin nv → Fin nv → ℤ) (x y : Fin nv → F) :
    rawKer ς x y + ExtractionK.pinKer ς x y = ∏ j, ExtractionK.pinOmega ς x j (y j) := by
  unfold rawKer ExtractionK.pinKer
  by_cases h : ∃ i j, x i = y j
  · simp only [h, ↓reduceIte]
    ring
  · simp only [h, ↓reduceIte]
    ring

end Raw

end Coll

end Sarkozy.JointRows
