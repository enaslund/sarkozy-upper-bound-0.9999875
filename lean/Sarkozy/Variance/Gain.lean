module

public import Sarkozy.Variance.Interpolation

/-!
# The variance gain (`lem:var-gain`, `cor:var-classes`)

`paper/sections/22_variance.tex`, Section 22.5. A class of selections whose records keep their
actual half marginals at the reserved cut `ι` has cost `B - g` in the sense of (CP5) when the
product of the actual half marginals carries energy at least `l̄ C_X Y`.

**Setting.** The selected set `X` of blocks is one factor `j₀` of a product law over the factors
`J` (as in `RecordExpansion/Variance.lean`); `c` is the reserved cut `ι`. The energies with `μ`
outside are `Y[κ] = energyAt O j₀ κ F` with outside laws `O` positive at `c` (`(R2)`), and those
with the bracket outside are `Y^Ñ[κ] = energyAt N j₀ κ F`. The records of an assignment
`φ ∈ 𝓡` are measures `P φ` at `j₀`, symmetric at `c`, with actual half marginal `m φ`; their
selected diagonals are `c.diagonalLaw (m φ)` and their products of actual half marginals are
`indepLaw c (m φ)` (`J_φ = J_ι(m_φ)`).

**The `o(1)`.** The paper's robust errors are explicit nonnegative numbers here: `z₁` in the
restoration hypothesis (Res), `z₂` in (E1) for the diagonals, `z₃`, `z₄` in the two bounds of
`lem:record:variance-interface`(ii). The conclusions carry the explicit error
`(z₁ + κ z₂)/(1 - κ)` (and `+ z₃ + z₄` in (b)), which tends to `0` with the inputs' errors.

**Main results.**
* `var_gain_a`: **`lem:var-gain`(a)**, in full, from (Res), (Cen), (P3) (proved here,
  `Interpolation.lean`), (E1) for the diagonals (hypothesis) and (E2) (proved).
* `var_gain_b`: **`lem:var-gain`(b)**, in full given `lem:record:variance-interface`(ii) as
  hypotheses; part (i) of that lemma is WP-R's `abs_energy_le_variance`, applied with the
  bilinear bound of each selected record difference (its hypothesis `hζ`).
* `var_gain_c`: **`lem:var-gain`(c)**: `l₀ ≤ C` gives `0 ≤ g ≤ 1 ≤ B` for
  `B = e^{U₀} + R_err`.
* `var_classes_aligned_gain`, `var_classes_embedding_gain`, `var_classes_compare`:
  **`cor:var-classes`**, the gain formulas of (ii), (iii) and the comparison
  `[l̄_E^al - R]_+ ≥ 2^{k-1}[l̄_E - R]_+`. The applications (i)–(iii) of `var_gain_a` take (Res)
  from `lem:record:restoration` (`Restoration.lean`) and `lem:record:paired-e-joint`(b)
  (`Matching.lean`), and (Cen) from `lem:record:old-f-marginal`(d) and
  `lem:record:paired-e-bridge`(b), which are not formalized here (hypotheses).
-/

@[expose] public section

open Finset
open scoped BigOperators
open Sarkozy.RecordExpansion

namespace Sarkozy.Variance

/-- The normalized gain `l̄ = (l₀/C - κ)/(1 - κ)` of `lem:var-gain`. -/
noncomputable def gainBar (l₀ C κ : ℝ) : ℝ := (l₀ / C - κ) / (1 - κ)

/-- The gain `g = [l̄ - R_err]_+` of `lem:var-gain`. -/
noncomputable def gainOf (l₀ C κ Rerr : ℝ) : ℝ := max 0 (gainBar l₀ C κ - Rerr)

section Gain

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)] {ι : Type*}

/-- **`lem:var-gain`(a)**. Let `𝓡` be a nonempty finite set of record assignments, each record
`P φ` symmetric at `ι` with actual half marginal `m φ` and centred norm `‖T_φ - 𝒥‖ ≤ κ < 1`
(Cen). If the average energy of the records is at least `(l₀ - z₁) Y` (Res), and the selected
diagonals satisfy (E1), `Y[Diag(m_φ)] ≤ (1 + z₂) C_X Y`, with `1 ≤ C_X ≤ C`, then the average
energy of the products of the actual half marginals is at least
`(l̄ - (z₁ + κ z₂)/(1 - κ)) C_X Y`, `l̄ = (l₀/C - κ)/(1 - κ)`. -/
theorem var_gain_a (c : ReflectionCut V) (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (j₀ : J)
    (hO : ∀ j, j ≠ j₀ → c.Positive (O j)) (F : (∀ b, X b) → ℝ)
    (R : Finset ι) (hR : R.Nonempty)
    (P : ι → ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ) (m : ι → (c.Half → X j₀) → ℝ)
    (hm : ∀ φ ∈ R, ∀ x, 0 ≤ m φ x) (hmpos : ∀ φ ∈ R, 0 < ∑ x, m φ x)
    (hsymm : ∀ φ ∈ R, ∀ G H : (c.Half → X j₀) → ℝ, c.form (P φ) G H = c.form (P φ) H G)
    (hplus : ∀ φ ∈ R, ∀ G : (c.Half → X j₀) → ℝ, c.form (P φ) G 1 = ∑ x, m φ x * G x)
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hcen : ∀ φ ∈ R, CentredNormLe c (P φ) (m φ) κ)
    {Yμ CX C l₀ z₁ z₂ : ℝ} (hY : 0 ≤ Yμ) (hCX : 1 ≤ CX) (hC : CX ≤ C)
    (hz₁ : 0 ≤ z₁) (hz₂ : 0 ≤ z₂)
    (hRes : (l₀ - z₁) * Yμ ≤ (∑ φ ∈ R, energyAt O j₀ (P φ) F) / R.card)
    (hE1 : ∀ φ ∈ R, energyAt O j₀ (c.diagonalLaw (m φ)) F ≤ (1 + z₂) * CX * Yμ) :
    (gainBar l₀ C κ - (z₁ + κ * z₂) / (1 - κ)) * CX * Yμ ≤
      (∑ φ ∈ R, energyAt O j₀ (indepLaw c (m φ)) F) / R.card := by
  have hn : (0 : ℝ) < R.card := by exact_mod_cast hR.card_pos
  have h1κ : 0 < 1 - κ := by linarith
  have hCpos : 0 < C := by linarith
  set n : ℝ := (R.card : ℝ) with hn_def
  set SJ := ∑ φ ∈ R, energyAt O j₀ (indepLaw c (m φ)) F with hSJ
  have hJnonneg : 0 ≤ SJ :=
    sum_nonneg fun φ hφ => energy_indepLaw_nonneg c O j₀ hO (hm φ hφ) F
  -- (P3) and (E1), summed
  have hsumP : ∑ φ ∈ R, energyAt O j₀ (P φ) F ≤ (1 - κ) * SJ + n * (κ * ((1 + z₂) * CX * Yμ)) := by
    have hle : ∀ φ ∈ R, energyAt O j₀ (P φ) F ≤
        (1 - κ) * energyAt O j₀ (indepLaw c (m φ)) F + κ * ((1 + z₂) * CX * Yμ) := by
      intro φ hφ
      have h3 := energy_le_centred_interpolation c O j₀ hO (hm φ hφ) (hmpos φ hφ) (hsymm φ hφ)
        (hplus φ hφ) (hcen φ hφ) F
      have h4 := hE1 φ hφ
      nlinarith
    have := sum_le_sum hle
    rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul] at this
    exact this
  have hRes' : (l₀ - z₁) * Yμ * n ≤ (1 - κ) * SJ + n * (κ * ((1 + z₂) * CX * Yμ)) := by
    have := (le_div_iff₀ hn).mp hRes
    linarith
  rw [le_div_iff₀ hn]
  unfold gainBar
  rw [div_sub_div_same, div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
    div_le_iff₀ h1κ]
  by_cases hl : 0 ≤ l₀
  · -- `l₀ ≥ 0`: `l₀ Y ≥ (l₀/C) C_X Y` and `z₁ Y ≤ z₁ C_X Y`
    have hA : l₀ / C * CX * Yμ ≤ l₀ * Yμ := by
      have : l₀ / C * CX ≤ l₀ := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hCpos]
        nlinarith
      nlinarith
    have hB : z₁ * Yμ ≤ z₁ * CX * Yμ := by
      have := mul_nonneg (mul_nonneg hz₁ hY) (sub_nonneg.mpr hCX)
      nlinarith
    nlinarith
  · -- `l₀ < 0`: the bound is negative
    push Not at hl
    have hneg : (l₀ / C - κ - (z₁ + κ * z₂)) * CX * Yμ ≤ 0 := by
      have : l₀ / C < 0 := div_neg_of_neg_of_pos hl hCpos
      have h5 : l₀ / C - κ - (z₁ + κ * z₂) ≤ 0 := by nlinarith
      have h6 : 0 ≤ CX * Yμ := by nlinarith
      nlinarith
    nlinarith

/-- **`lem:var-gain`(b)**. Under the hypotheses of (a), let `ζ φ` be the selected record
difference of the selection `ω_φ`, with the bilinear bound `γ` (common to all `φ ∈ 𝓡`, the
prices being common) relative to the centred norm of `m φ`, as in
`lem:record:variance-interface`(i), and assume the two bounds of
`lem:record:variance-interface`(ii): `Y^Ñ[Diag(m_φ)] ≤ (B + z₃) C_X Y` and
`Y^Ñ[J_φ] ≥ Y[J_φ] - (R_err + z₄) C_X Y`. Then, with the prices `π_φ = γ C_X`,
`∑_φ |I_φ| ≤ (B - g + z) ∑_φ π_φ Y`, where `g = [l̄ - R_err]_+` and
`z = z₃ + z₄ + (z₁ + κ z₂)/(1 - κ)`: the selections form a class of cost `B - g`. -/
theorem var_gain_b (c : ReflectionCut V) (O N lam : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (j₀ : J)
    (hO : ∀ j, j ≠ j₀ → c.Positive (O j)) (hN : ∀ j, j ≠ j₀ → c.Bracket (N j) (lam j) (N j))
    (F : (∀ b, X b) → ℝ) (R : Finset ι) (hR : R.Nonempty)
    (P : ι → ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ) (m : ι → (c.Half → X j₀) → ℝ)
    (hm : ∀ φ ∈ R, ∀ x, 0 ≤ m φ x) (hmpos : ∀ φ ∈ R, 0 < ∑ x, m φ x)
    (hsymm : ∀ φ ∈ R, ∀ G H : (c.Half → X j₀) → ℝ, c.form (P φ) G H = c.form (P φ) H G)
    (hplus : ∀ φ ∈ R, ∀ G : (c.Half → X j₀) → ℝ, c.form (P φ) G 1 = ∑ x, m φ x * G x)
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hcen : ∀ φ ∈ R, CentredNormLe c (P φ) (m φ) κ)
    {Yμ CX C l₀ z₁ z₂ z₃ z₄ Bf Rerr γ : ℝ} (hY : 0 ≤ Yμ) (hCX : 1 ≤ CX) (hC : CX ≤ C)
    (hz₁ : 0 ≤ z₁) (hz₂ : 0 ≤ z₂) (hz₄ : 0 ≤ z₄) (hγ : 0 ≤ γ)
    (hRes : (l₀ - z₁) * Yμ ≤ (∑ φ ∈ R, energyAt O j₀ (P φ) F) / R.card)
    (hE1 : ∀ φ ∈ R, energyAt O j₀ (c.diagonalLaw (m φ)) F ≤ (1 + z₂) * CX * Yμ)
    (ζ : ι → ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ)
    (hζ : ∀ φ ∈ R, ∀ G H : (c.Half → X j₀) → ℝ, |c.form (ζ φ) G H| ≤
      γ * Real.sqrt (c.form (c.diagonalLaw (m φ) - indepLaw c (m φ)) G G) *
        Real.sqrt (c.form (c.diagonalLaw (m φ) - indepLaw c (m φ)) H H))
    (hDiagN : ∀ φ ∈ R, energyAt N j₀ (c.diagonalLaw (m φ)) F ≤ (Bf + z₃) * CX * Yμ)
    (hJN : ∀ φ ∈ R, energyAt O j₀ (indepLaw c (m φ)) F - (Rerr + z₄) * CX * Yμ ≤
      energyAt N j₀ (indepLaw c (m φ)) F) :
    ∑ φ ∈ R, |energyAt lam j₀ (ζ φ) F| ≤
      (Bf - gainOf l₀ C κ Rerr + (z₃ + z₄ + (z₁ + κ * z₂) / (1 - κ))) *
        (∑ _φ ∈ R, γ * CX) * Yμ := by
  have hn : (0 : ℝ) < R.card := by exact_mod_cast hR.card_pos
  have h1κ : 0 < 1 - κ := by linarith
  set ea := (z₁ + κ * z₂) / (1 - κ) with hea
  have hea0 : 0 ≤ ea := div_nonneg (by nlinarith) h1κ.le
  have hNpos : ∀ j, j ≠ j₀ → c.Positive (N j) := fun j hj => (hN j hj).left_positive
  -- `lem:record:variance-interface`(i) for each selection
  have hI : ∀ φ ∈ R, |energyAt lam j₀ (ζ φ) F| ≤
      γ * (energyAt N j₀ (c.diagonalLaw (m φ)) F - energyAt N j₀ (indepLaw c (m φ)) F) :=
    fun φ hφ => abs_energy_le_variance c N lam j₀ hN (hm φ hφ) hγ (ζ φ) (hζ φ hφ) F
  have hsumγ : ∑ _φ ∈ R, γ * CX = R.card * (γ * CX) := by
    rw [sum_const, nsmul_eq_mul]
  rw [hsumγ]
  have hCXY : 0 ≤ CX * Yμ := by nlinarith
  by_cases hg : 0 ≤ gainBar l₀ C κ - Rerr
  · -- the gain is used
    have hgain : gainOf l₀ C κ Rerr = gainBar l₀ C κ - Rerr := max_eq_right hg
    rw [hgain]
    have ha := var_gain_a c O j₀ hO F R hR P m hm hmpos hsymm hplus hκ0 hκ1 hcen hY hCX hC
      hz₁ hz₂ hRes hE1
    rw [← hea] at ha
    have ha' : R.card * ((gainBar l₀ C κ - ea) * CX * Yμ) ≤
        ∑ φ ∈ R, energyAt O j₀ (indepLaw c (m φ)) F := by
      have := (le_div_iff₀ hn).mp ha
      linarith
    have hle : ∀ φ ∈ R, |energyAt lam j₀ (ζ φ) F| ≤
        γ * ((Bf + z₃) * CX * Yμ + (Rerr + z₄) * CX * Yμ -
          energyAt O j₀ (indepLaw c (m φ)) F) := by
      intro φ hφ
      refine (hI φ hφ).trans ?_
      apply mul_le_mul_of_nonneg_left _ hγ
      linarith [hDiagN φ hφ, hJN φ hφ]
    have hsum := sum_le_sum hle
    rw [← mul_sum, sum_sub_distrib, sum_const, nsmul_eq_mul] at hsum
    refine hsum.trans ?_
    have : γ * (R.card * ((Bf + z₃) * CX * Yμ + (Rerr + z₄) * CX * Yμ) -
        ∑ φ ∈ R, energyAt O j₀ (indepLaw c (m φ)) F) ≤
        γ * (R.card * ((Bf + z₃) * CX * Yμ + (Rerr + z₄) * CX * Yμ) -
          R.card * ((gainBar l₀ C κ - ea) * CX * Yμ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hγ
    refine this.trans (le_of_eq ?_)
    ring
  · -- no gain: `|I_φ| ≤ γ Y^Ñ[Diag(m_φ)]`
    push Not at hg
    have hgain : gainOf l₀ C κ Rerr = 0 := max_eq_left hg.le
    rw [hgain]
    have hle : ∀ φ ∈ R, |energyAt lam j₀ (ζ φ) F| ≤ γ * ((Bf + z₃) * CX * Yμ) := by
      intro φ hφ
      refine (hI φ hφ).trans ?_
      apply mul_le_mul_of_nonneg_left _ hγ
      have := energy_indepLaw_nonneg c N j₀ hNpos (hm φ hφ) F
      linarith [hDiagN φ hφ]
    have hsum := sum_le_sum hle
    rw [sum_const, nsmul_eq_mul] at hsum
    refine hsum.trans ?_
    have h0 : 0 ≤ R.card * (γ * CX) * Yμ := by
      have : 0 ≤ (R.card : ℝ) * γ := mul_nonneg hn.le hγ
      nlinarith
    have : R.card * (γ * ((Bf + z₃) * CX * Yμ)) = (Bf + z₃) * (R.card * (γ * CX) * Yμ) := by
      ring
    rw [this]
    have hz : Bf + z₃ ≤ Bf - 0 + (z₃ + z₄ + ea) := by linarith
    calc (Bf + z₃) * (R.card * (γ * CX) * Yμ)
        ≤ (Bf - 0 + (z₃ + z₄ + ea)) * (R.card * (γ * CX) * Yμ) :=
          mul_le_mul_of_nonneg_right hz h0
      _ = (Bf - 0 + (z₃ + z₄ + ea)) * (R.card * (γ * CX)) * Yμ := by ring

/-- **`lem:var-gain`(c)**: if `l₀ ≤ C` (with `C > 0`, `0 ≤ κ < 1`, `R_err ≥ 0`, `U₀ ≥ 0`),
then `0 ≤ g ≤ 1 ≤ B` for `B = e^{U₀} + R_err`. -/
theorem var_gain_c {l₀ C κ Rerr U₀ : ℝ} (hC : 0 < C) (hκ1 : κ < 1) (hR : 0 ≤ Rerr)
    (hU : 0 ≤ U₀) (hl : l₀ ≤ C) :
    0 ≤ gainOf l₀ C κ Rerr ∧ gainOf l₀ C κ Rerr ≤ 1 ∧ 1 ≤ Real.exp U₀ + Rerr := by
  have h1κ : 0 < 1 - κ := by linarith
  have hbar : gainBar l₀ C κ ≤ 1 := by
    unfold gainBar
    rw [div_le_one h1κ]
    have : l₀ / C ≤ 1 := (div_le_one hC).mpr hl
    linarith
  refine ⟨le_max_left _ _, max_le zero_le_one (by linarith), ?_⟩
  have := Real.add_one_le_exp U₀
  linarith

end Gain

/-! ### `cor:var-classes`: the gain formulas -/

/-- **`cor:var-classes`(ii)**: the aligned matching assignments, with `l₀ - C ε_X` in place of
`l₀`, have the normalized gain `l̄_E^al = (l₀/C - ε_X - κ_E)/(1 - κ_E)`. -/
theorem var_classes_aligned_gain {l₀ C ε κ : ℝ} (hC : C ≠ 0) :
    gainBar (l₀ - C * ε) C κ = (l₀ / C - ε - κ) / (1 - κ) := by
  unfold gainBar
  congr 1
  field_simp

/-- **`cor:var-classes`(iii)**: the `2^k` matching embeddings, with `2^{1-k} l₀ - C ε_X` in place
of `l₀`, have the normalized gain `l̄_E = (2^{1-k} l₀/C - ε_X - κ_E)/(1 - κ_E)`. -/
theorem var_classes_embedding_gain {l₀ C ε κ : ℝ} (k : ℕ) (hC : C ≠ 0) :
    gainBar ((2 : ℝ)⁻¹ ^ (k - 1) * l₀ - C * ε) C κ =
      ((2 : ℝ)⁻¹ ^ (k - 1) * l₀ / C - ε - κ) / (1 - κ) := by
  unfold gainBar
  congr 1
  field_simp

/-- **`cor:var-classes`, the last claim**: `[l̄_E^al - R_err]_+ ≥ 2^{k-1}[l̄_E - R_err]_+`, for
`ε_X, κ_E, R_err ≥ 0`, `κ_E < 1` (the paper's `k ≥ 1`; with truncated `k - 1` the case `k = 0`
is the case `k = 1`). For `k = 1` the two gains coincide. -/
theorem var_classes_compare {l₀ C ε κ Rerr : ℝ} (k : ℕ) (hε : 0 ≤ ε)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hR : 0 ≤ Rerr) :
    (2 : ℝ) ^ (k - 1) *
        max 0 (((2 : ℝ)⁻¹ ^ (k - 1) * l₀ / C - ε - κ) / (1 - κ) - Rerr) ≤
      max 0 ((l₀ / C - ε - κ) / (1 - κ) - Rerr) := by
  have h1κ : 0 < 1 - κ := by linarith
  set t : ℝ := (2 : ℝ) ^ (k - 1) with ht
  have ht1 : 1 ≤ t := one_le_pow₀ (by norm_num)
  have htinv : t * (2 : ℝ)⁻¹ ^ (k - 1) = 1 := by
    rw [ht, ← mul_pow]
    norm_num
  have hkey : t * (((2 : ℝ)⁻¹ ^ (k - 1) * l₀ / C - ε - κ) / (1 - κ) - Rerr) ≤
      (l₀ / C - ε - κ) / (1 - κ) - Rerr := by
    have e : t * (((2 : ℝ)⁻¹ ^ (k - 1) * l₀ / C - ε - κ) / (1 - κ)) =
        (l₀ / C - t * (ε + κ)) / (1 - κ) := by
      rw [mul_div_assoc']
      congr 1
      rw [mul_sub, mul_sub, mul_div_assoc', ← mul_assoc, htinv, one_mul]
      ring
    rw [mul_sub, e]
    have h2 : (l₀ / C - t * (ε + κ)) / (1 - κ) ≤ (l₀ / C - ε - κ) / (1 - κ) := by
      apply div_le_div_of_nonneg_right _ h1κ.le
      nlinarith
    nlinarith
  have ht0 : 0 ≤ t := by linarith
  rw [mul_max_of_nonneg _ _ ht0, mul_zero]
  exact max_le_max le_rfl hkey

end Sarkozy.Variance
