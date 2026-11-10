module

public import Sarkozy.Variance.GainFlat
public import Sarkozy.Variance.RestorationBlocks

/-!
# Matching selections with each block its own factor (`lem:record:paired-e-joint`(b), (c),
`cor:var-classes`(ii))

`paper/sections/22_variance.tex`, `lem:record:paired-e-joint`(b), (c) and `cor:var-classes`(ii),
with the selected set `X` as a set of factors (`Xs`).

* `paired_e_joint_b_blocks`: **(b), the aligned bound**. The polarization order (a) in energy
  form, `Y[⊗_X Π_{F₁}] + Y[⊗_X Π_{F₂}] ≤ ∑_s Y[⊗_X (Π_{E_s} + ε G_s)]`, is the hypothesis `hord`.
  It is (E2) at `ϑ₀` applied to `lem:tr:polarization`(c), which `Bridge.paired_e_joint_a` proves
  for five-type data. (E1) bounds the merge part `Y[⊗(Π_{E_s} + ε G_s)] - Y[⊗Π_{E_s}]` by
  `(1 + z) ε_X C_X Y`. The restoration bounds for the two fold products are hypotheses. The
  conclusion is `½ ∑_s Y[E^X_s] ≥ (l₀ - C ε_X - z₁ - z ε_X C) Y`.
* `paired_e_joint_c_blocks`: **(c)**. The aligned embeddings are products of nonnegative weights
  coupling two copies of their actual half marginals at `ι`. The contraction (P1) for products
  gives `Y[E^X_s] ≤ Y[Diag_ι(m^X_s)]`, and so
  `Y[Diag_ι(m^X_0)] + Y[Diag_ι(m^X_1)] ≥ 2([l₀ - C ε_X]_+ - e) Y`.
* `energy_le_diag_blocks`: the contraction (P1) for products of couplings.
* `var_classes_aligned_matching_blocks`: **`cor:var-classes`(ii)**: (b), then
  `var_gain_a_blocks`.
* `paired_e_joint_b_all_blocks`, `var_classes_embeddings_blocks`: the second bound of (b), over
  the `2^k` embeddings, and **`cor:var-classes`(iii)**.
-/

@[expose] public section

open Finset
open scoped BigOperators
open Sarkozy.RecordExpansion

namespace Sarkozy.Variance

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]

/-- **`lem:record:paired-e-joint`(b), the aligned bound, blocks as factors** (energy form). -/
theorem paired_e_joint_b_blocks {YF1 YF2 YA0 YA1 YE0 YE1 Yμ CX C ε l₀ z₁ z : ℝ}
    (hY : 0 ≤ Yμ) (hCX : CX ≤ C) (hε : 0 ≤ ε) (hz : 0 ≤ z)
    (hord : YF1 + YF2 ≤ YA0 + YA1) (hF1 : (l₀ - z₁) * Yμ ≤ YF1) (hF2 : (l₀ - z₁) * Yμ ≤ YF2)
    (hMg0 : YA0 - YE0 ≤ (1 + z) * ε * CX * Yμ) (hMg1 : YA1 - YE1 ≤ (1 + z) * ε * CX * Yμ) :
    (l₀ - C * ε - z₁ - z * ε * C) * Yμ ≤ (YE0 + YE1) / 2 := by
  have hc : (1 + z) * ε * CX * Yμ ≤ (1 + z) * ε * C * Yμ := by
    have h1 : 0 ≤ (1 + z) * ε := mul_nonneg (by linarith) hε
    have := mul_le_mul_of_nonneg_left hCX h1
    nlinarith
  nlinarith

/-- **The contraction (P1) for products of couplings**: if on every block of `X` the weight
`w_𝔅 ≥ 0` has both half marginals `m_𝔅` at `c`, and the outside factors are positive, then
`Y[⊗_X w ⊗ O] ≤ Y[⊗_X Diag(m) ⊗ O]`. -/
theorem energy_le_diag_blocks (c : ReflectionCut V) (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (Xs : Finset J) (hO : ∀ j, j ∉ Xs → c.Positive (O j)) (F : (∀ b, X b) → ℝ)
    (w : ∀ j, (V → X j) → ℝ) (m : ∀ j, (c.Half → X j) → ℝ) (hw : ∀ j ∈ Xs, ∀ z, 0 ≤ w j z)
    (hp : ∀ j ∈ Xs, plusMarginal c (w j) = m j) (hn : ∀ j ∈ Xs, minusMarginal c (w j) = m j) :
    diagonalIntegral (tensorLaw (onBlocks Xs (fun j => signedIntegral (w j)) O)) F ≤
      diagonalIntegral (tensorLaw (onBlocks Xs (fun j => c.diagonalLaw (m j)) O)) F := by
  have hm0 : ∀ j ∈ Xs, ∀ x, 0 ≤ m j x := fun j hj x => hp j hj ▸ plusMarginal_nonneg c (hw j hj) x
  have hpos : ∀ j, c.Positive (onBlocks Xs (fun j => c.diagonalLaw (m j)) O j) := by
    intro j
    by_cases hj : j ∈ Xs
    · simp only [onBlocks, hj, ↓reduceIte]
      exact c.diagonalLaw_positive (hm0 j hj)
    · simp only [onBlocks, hj, ↓reduceIte]
      exact hO j hj
  have hbr := abs_energy_le_of_brackets (c := c)
    (κ := onBlocks Xs (fun j => c.diagonalLaw (m j)) O)
    (ζ := onBlocks Xs (fun j => signedIntegral (w j)) O)
    (κ' := onBlocks Xs (fun j => c.diagonalLaw (m j)) O) (fun j => by
      by_cases hj : j ∈ Xs
      · simp only [onBlocks, hj, ↓reduceIte]
        have hb := bracket_diagonal_marginals c (hw j hj)
        rw [hp j hj, hn j hj] at hb
        exact hb
      · simp only [onBlocks, hj, ↓reduceIte]
        exact (hO j hj).bracket_self) F
  have hnn := (ReflectionCut.Positive.tensor hpos).diagonal_nonneg F
  rw [Real.mul_self_sqrt hnn] at hbr
  exact (le_abs_self _).trans hbr

/-- **`lem:record:paired-e-joint`(c), blocks as factors**: with the first bound of (b) for the
aligned embeddings `E^X_s = ⊗_X e_s` (hypothesis `hb`), the diagonals of their actual half
marginals satisfy `Y[Diag(m^X_0)] + Y[Diag(m^X_1)] ≥ 2([l₀ - C ε_X]_+ - e) Y`. -/
theorem paired_e_joint_c_blocks (ι : ReflectionCut V) (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (Xs : Finset J) (hO : ∀ j, j ∉ Xs → ι.Positive (O j)) (F : (∀ b, X b) → ℝ)
    (e0 e1 : ∀ j, (V → X j) → ℝ) (m0 m1 : ∀ j, (ι.Half → X j) → ℝ)
    (hw0 : ∀ j ∈ Xs, ∀ z, 0 ≤ e0 j z) (hw1 : ∀ j ∈ Xs, ∀ z, 0 ≤ e1 j z)
    (hp0 : ∀ j ∈ Xs, plusMarginal ι (e0 j) = m0 j) (hn0 : ∀ j ∈ Xs, minusMarginal ι (e0 j) = m0 j)
    (hp1 : ∀ j ∈ Xs, plusMarginal ι (e1 j) = m1 j) (hn1 : ∀ j ∈ Xs, minusMarginal ι (e1 j) = m1 j)
    {Yμ C ε l₀ e : ℝ} (hY : 0 ≤ Yμ) (he : 0 ≤ e)
    (hb : (l₀ - C * ε - e) * Yμ ≤
      (diagonalIntegral (tensorLaw (onBlocks Xs (fun j => signedIntegral (e0 j)) O)) F +
        diagonalIntegral (tensorLaw (onBlocks Xs (fun j => signedIntegral (e1 j)) O)) F) / 2) :
    2 * (max 0 (l₀ - C * ε) - e) * Yμ ≤
      diagonalIntegral (tensorLaw (onBlocks Xs (fun j => ι.diagonalLaw (m0 j)) O)) F +
        diagonalIntegral (tensorLaw (onBlocks Xs (fun j => ι.diagonalLaw (m1 j)) O)) F := by
  have h0 := energy_le_diag_blocks ι O Xs hO F e0 m0 hw0 hp0 hn0
  have h1 := energy_le_diag_blocks ι O Xs hO F e1 m1 hw1 hp1 hn1
  have hD : ∀ (m : ∀ j, (ι.Half → X j) → ℝ) (w : ∀ j, (V → X j) → ℝ),
      (∀ j ∈ Xs, ∀ z, 0 ≤ w j z) → (∀ j ∈ Xs, plusMarginal ι (w j) = m j) →
      0 ≤ diagonalIntegral (tensorLaw (onBlocks Xs (fun j => ι.diagonalLaw (m j)) O)) F := by
    intro m w hw hp
    have hpos : ∀ j, ι.Positive (onBlocks Xs (fun j => ι.diagonalLaw (m j)) O j) := by
      intro j
      by_cases hj : j ∈ Xs
      · simp only [onBlocks, hj, ↓reduceIte]
        exact ι.diagonalLaw_positive fun x => hp j hj ▸ plusMarginal_nonneg ι (hw j hj) x
      · simp only [onBlocks, hj, ↓reduceIte]
        exact hO j hj
    exact (ReflectionCut.Positive.tensor hpos).diagonal_nonneg F
  have hD0 := hD m0 e0 hw0 hp0
  have hD1 := hD m1 e1 hw1 hp1
  rcases le_or_gt 0 (l₀ - C * ε) with hpos | hneg
  · rw [max_eq_right hpos]
    linarith
  · rw [max_eq_left hneg.le]
    have : 2 * (0 - e) * Yμ ≤ 0 := by nlinarith
    linarith

/-- **`cor:var-classes`(ii), blocks as factors**: (b) for the two aligned matching assignments
gives (Res) with `l₀ - C ε_X`, and `var_gain_a_blocks` gives
`½ ∑_s Y[⊗_X J(m_s) ⊗ O] ≥ (l̄_E^al - z) C_X Y`,
`l̄_E^al = (l₀/C - ε_X - κ_E)/(1 - κ_E)`. -/
theorem var_classes_aligned_matching_blocks (ι : ReflectionCut V)
    (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (Xs : Finset J) (hO : ∀ j, j ∉ Xs → ι.Positive (O j))
    (F : (∀ b, X b) → ℝ) (e0 e1 : ∀ j, (V → X j) → ℝ) (m0 m1 : ∀ j, (ι.Half → X j) → ℝ)
    (hw0 : ∀ j ∈ Xs, ∀ z, 0 ≤ e0 j z) (hw1 : ∀ j ∈ Xs, ∀ z, 0 ≤ e1 j z)
    (hp0 : ∀ j ∈ Xs, plusMarginal ι (e0 j) = m0 j) (hn0 : ∀ j ∈ Xs, minusMarginal ι (e0 j) = m0 j)
    (hp1 : ∀ j ∈ Xs, plusMarginal ι (e1 j) = m1 j) (hn1 : ∀ j ∈ Xs, minusMarginal ι (e1 j) = m1 j)
    (ht0 : ∀ j ∈ Xs, ∀ G H : (ι.Half → X j) → ℝ,
      ι.form (signedIntegral (e0 j)) G H = ι.form (signedIntegral (e0 j)) H G)
    (ht1 : ∀ j ∈ Xs, ∀ G H : (ι.Half → X j) → ℝ,
      ι.form (signedIntegral (e1 j)) G H = ι.form (signedIntegral (e1 j)) H G)
    (hmp0 : ∀ j ∈ Xs, 0 < ∑ x, m0 j x) (hmp1 : ∀ j ∈ Xs, 0 < ∑ x, m1 j x) (κj : J → ℝ)
    (hcen0 : ∀ j ∈ Xs, CentredNormLe ι (signedIntegral (e0 j)) (m0 j) (κj j))
    (hcen1 : ∀ j ∈ Xs, CentredNormLe ι (signedIntegral (e1 j)) (m1 j) (κj j))
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hκ : ∀ j ∈ Xs, κj j ≤ κ)
    {YF1 YF2 YA0 YA1 Yμ CX C ε l₀ z₁ z z₂ : ℝ} (hY : 0 ≤ Yμ) (hCX : 1 ≤ CX) (hC : CX ≤ C)
    (hε : 0 ≤ ε) (hz : 0 ≤ z) (hz₁ : 0 ≤ z₁) (hz₂ : 0 ≤ z₂)
    (hord : YF1 + YF2 ≤ YA0 + YA1) (hF1 : (l₀ - z₁) * Yμ ≤ YF1) (hF2 : (l₀ - z₁) * Yμ ≤ YF2)
    (hMg0 : YA0 - diagonalIntegral (tensorLaw (recFam ι O Xs Xs e0 m0)) F ≤
      (1 + z) * ε * CX * Yμ)
    (hMg1 : YA1 - diagonalIntegral (tensorLaw (recFam ι O Xs Xs e1 m1)) F ≤
      (1 + z) * ε * CX * Yμ)
    (hD0 : diagonalIntegral (tensorLaw (diagFam ι O Xs Xs m0)) F ≤ (1 + z₂) * CX * Yμ)
    (hD1 : diagonalIntegral (tensorLaw (diagFam ι O Xs Xs m1)) F ≤ (1 + z₂) * CX * Yμ) :
    ((l₀ / C - ε - κ) / (1 - κ) - (z₁ + z * ε * C + κ * z₂) / (1 - κ)) * CX * Yμ ≤
      (diagonalIntegral (tensorLaw (recFam ι O Xs ∅ e0 m0)) F +
        diagonalIntegral (tensorLaw (recFam ι O Xs ∅ e1 m1)) F) / 2 := by
  have hCpos : 0 < C := by linarith
  have hb := paired_e_joint_b_blocks hY hC hε hz hord hF1 hF2 hMg0 hMg1
  let w : Bool → ∀ j, (V → X j) → ℝ := fun s => if s then e1 else e0
  let m : Bool → ∀ j, (ι.Half → X j) → ℝ := fun s => if s then m1 else m0
  have ha := var_gain_a_blocks ι O Xs hO F univ univ_nonempty w m
    (fun s _ => by cases s <;> [exact hw0; exact hw1])
    (fun s _ => by cases s <;> [exact hp0; exact hp1])
    (fun s _ => by cases s <;> [exact hn0; exact hn1])
    (fun s _ => by cases s <;> [exact ht0; exact ht1])
    (fun s _ => by cases s <;> [exact hmp0; exact hmp1]) (fun _ => κj)
    (fun s _ => by cases s <;> [exact hcen0; exact hcen1]) hκ0 hκ1 (fun _ _ => hκ)
    (l₀ := l₀ - C * ε) (z₁ := z₁ + z * ε * C) hY hCX hC (by positivity) hz₂
    (by
      have e : (l₀ - C * ε - (z₁ + z * ε * C)) * Yμ = (l₀ - C * ε - z₁ - z * ε * C) * Yμ := by
        ring
      rw [e]
      simpa [w, m, add_comm] using hb)
    (fun s _ => by cases s <;> [exact hD0; exact hD1])
  rw [var_classes_aligned_gain hCpos.ne'] at ha
  simpa [w, m, add_comm] using ha

/-- **`lem:record:paired-e-joint`(b), the bound over all `2^k` matching embeddings, blocks as
factors** (energy form). The second polarization order with `μ` outside enters through its
energy form `hord` (C1's `polarization_c_second`). (E1) bounds the merge part, of total mass
`∏(2 + 2ε_𝔅) - 2^k ≤ 2^k ε_X`, by `(1 + z) 2^k ε_X C_X Y`. The conclusion is
`2^{-k} ∑_s Y[E_s] ≥ (2^{1-k} l₀ - C ε_X - 2^{1-k} z₁ - z ε_X C) Y`. -/
theorem paired_e_joint_b_all_blocks {σ : Type*} (S : Finset σ) (k : ℕ) (YE : σ → ℝ)
    {YF1 YF2 YA Yμ CX C ε l₀ z₁ z : ℝ} (hY : 0 ≤ Yμ) (hCX : CX ≤ C) (hε : 0 ≤ ε) (hz : 0 ≤ z)
    (hord : YF1 + YF2 ≤ YA) (hF1 : (l₀ - z₁) * Yμ ≤ YF1) (hF2 : (l₀ - z₁) * Yμ ≤ YF2)
    (hMg : YA - ∑ s ∈ S, YE s ≤ (1 + z) * (2 ^ k * ε) * CX * Yμ) :
    (2 * (2 : ℝ)⁻¹ ^ k * l₀ - C * ε - 2 * (2 : ℝ)⁻¹ ^ k * z₁ - z * ε * C) * Yμ ≤
      (∑ s ∈ S, YE s) / 2 ^ k := by
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  rw [le_div_iff₀ hk]
  have hinv : (2 : ℝ)⁻¹ ^ k * 2 ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  have hc : (1 + z) * (2 ^ k * ε) * CX * Yμ ≤ (1 + z) * (2 ^ k * ε) * C * Yμ := by
    have h1 : 0 ≤ (1 + z) * (2 ^ k * ε) := mul_nonneg (by linarith) (mul_nonneg hk.le hε)
    have := mul_le_mul_of_nonneg_left hCX h1
    nlinarith
  have e2 : (2 * (2 : ℝ)⁻¹ ^ k * l₀ - C * ε - 2 * (2 : ℝ)⁻¹ ^ k * z₁ - z * ε * C) * Yμ * 2 ^ k =
      2 * (l₀ - z₁) * Yμ - (1 + z) * (2 ^ k * ε) * C * Yμ := by
    linear_combination (2 * l₀ * Yμ - 2 * z₁ * Yμ) * hinv
  rw [e2]
  linarith

/-- **`cor:var-classes`(iii), blocks as factors**: the `2^k` matching embeddings `E_s`,
`s ∈ S` (each block `𝔅 ∈ X` carrying `e_{s,𝔅}`, with centred norm `≤ κ_E`). (Res) is the second
bound of (b) (`paired_e_joint_b_all_blocks`), and `var_gain_a_blocks` gives
`avg_s Y[⊗_X J(m_s) ⊗ O] ≥ (l̄_E - z) C_X Y` with
`l̄_E = (2^{1-k} l₀/C - ε_X - κ_E)/(1 - κ_E)`. -/
theorem var_classes_embeddings_blocks {σ : Type*} (ι : ReflectionCut V)
    (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (Xs : Finset J) (hO : ∀ j, j ∉ Xs → ι.Positive (O j))
    (F : (∀ b, X b) → ℝ) (S : Finset σ) (hSne : S.Nonempty) (k : ℕ) (hS : S.card = 2 ^ k)
    (e : σ → ∀ j, (V → X j) → ℝ) (m : σ → ∀ j, (ι.Half → X j) → ℝ)
    (hw : ∀ s ∈ S, ∀ j ∈ Xs, ∀ z, 0 ≤ e s j z)
    (hp : ∀ s ∈ S, ∀ j ∈ Xs, plusMarginal ι (e s j) = m s j)
    (hn : ∀ s ∈ S, ∀ j ∈ Xs, minusMarginal ι (e s j) = m s j)
    (ht : ∀ s ∈ S, ∀ j ∈ Xs, ∀ G H : (ι.Half → X j) → ℝ,
      ι.form (signedIntegral (e s j)) G H = ι.form (signedIntegral (e s j)) H G)
    (hmp : ∀ s ∈ S, ∀ j ∈ Xs, 0 < ∑ x, m s j x) (κj : σ → J → ℝ)
    (hcen : ∀ s ∈ S, ∀ j ∈ Xs, CentredNormLe ι (signedIntegral (e s j)) (m s j) (κj s j))
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hκ : ∀ s ∈ S, ∀ j ∈ Xs, κj s j ≤ κ)
    {YF1 YF2 YA Yμ CX C ε l₀ z₁ z z₂ : ℝ} (hY : 0 ≤ Yμ) (hCX : 1 ≤ CX) (hC : CX ≤ C)
    (hε : 0 ≤ ε) (hz : 0 ≤ z) (hz₁ : 0 ≤ z₁) (hz₂ : 0 ≤ z₂)
    (hord : YF1 + YF2 ≤ YA) (hF1 : (l₀ - z₁) * Yμ ≤ YF1) (hF2 : (l₀ - z₁) * Yμ ≤ YF2)
    (hMg : YA - ∑ s ∈ S, diagonalIntegral (tensorLaw (recFam ι O Xs Xs (e s) (m s))) F ≤
      (1 + z) * (2 ^ k * ε) * CX * Yμ)
    (hD : ∀ s ∈ S, diagonalIntegral (tensorLaw (diagFam ι O Xs Xs (m s))) F ≤
      (1 + z₂) * CX * Yμ) :
    ((2 * (2 : ℝ)⁻¹ ^ k * l₀ / C - ε - κ) / (1 - κ) -
        (2 * (2 : ℝ)⁻¹ ^ k * z₁ + z * ε * C + κ * z₂) / (1 - κ)) * CX * Yμ ≤
      (∑ s ∈ S, diagonalIntegral (tensorLaw (recFam ι O Xs ∅ (e s) (m s))) F) / S.card := by
  have hCpos : 0 < C := by linarith
  have hb := paired_e_joint_b_all_blocks S k
    (fun s => diagonalIntegral (tensorLaw (recFam ι O Xs Xs (e s) (m s))) F) hY hC hε hz hord hF1
    hF2 hMg
  have hcard : (S.card : ℝ) = 2 ^ k := by rw [hS]; push_cast; rfl
  have hz' : 0 ≤ 2 * (2 : ℝ)⁻¹ ^ k * z₁ + z * ε * C := by positivity
  have ha := var_gain_a_blocks ι O Xs hO F S hSne e m hw hp hn ht hmp κj hcen hκ0 hκ1 hκ
    (l₀ := 2 * (2 : ℝ)⁻¹ ^ k * l₀ - C * ε) (z₁ := 2 * (2 : ℝ)⁻¹ ^ k * z₁ + z * ε * C)
    hY hCX hC hz' hz₂ (by
      rw [hcard]
      have e1 : (2 * (2 : ℝ)⁻¹ ^ k * l₀ - C * ε - (2 * (2 : ℝ)⁻¹ ^ k * z₁ + z * ε * C)) * Yμ =
          (2 * (2 : ℝ)⁻¹ ^ k * l₀ - C * ε - 2 * (2 : ℝ)⁻¹ ^ k * z₁ - z * ε * C) * Yμ := by ring
      rw [e1]
      exact hb) hD
  rw [var_classes_aligned_gain hCpos.ne'] at ha
  exact ha

end Sarkozy.Variance
