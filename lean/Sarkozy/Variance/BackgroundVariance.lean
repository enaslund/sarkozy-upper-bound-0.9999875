module

public import Sarkozy.Variance.Exterior

/-!
# `prop:background-variance`(a), the displayed bound, assembled

`paper/sections/22_variance.tex`, `prop:background-variance`(a): the composition of the steps of
its proof, at the measure level.

* the exterior expansion over the kept sets `Z` (`exterior_expansion_ge`, for `s = 0, 1`);
* the selected term `Z = ∅` (`background_selected`, by (P3));
* the background terms of the kept sets `Z ≠ ∅` (`background_term_set`, by (P3′) over `Z`);
* the sum with the choice weights (`background_assembly`).

**Conclusion.** `½ ∑_s Y^{Ñ₀}[J_s] ≥ (C_m [b_E(m) + ∑_r W_r p_E(m,r)] - z) Y`, with
`Ñ₀ = μ + R` off the selected factor and an explicit error `z`. The class cost `B - g_E(m)`
then follows by `class_cost_of_product_energy` with `O' = Ñ₀`.

**Inputs that remain hypotheses** (with the paper's labels):
* `(Ñ₀ - μ)_𝔅 ⪰ c_𝔅 D_{E_s,𝔅}` (`hR0`, `hR1`; `lem:record:gram`(i), `def:record:frame`(b));
* the centred norm `k_{E,m}` of the selected aligned embeddings (`lem:record:paired-e-bridge`(b));
* `lem:record:paired-e-joint`(b) for `X` and for every `X ∪ Z` (`hbsel`, `hbZ`; proved in
  `Matching.lean` from the polarization order and (E1));
* (E1) for the diagonals (`hDsel`, `hDZ`);
* the choice weights (`hW`; `lem:distinct-choice`(a)).
-/

@[expose] public section

open Finset
open scoped BigOperators
open Sarkozy.RecordExpansion

namespace Sarkozy.Variance

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]

/-- The coefficient `∏_{𝔅∈Z} c_𝔅` of a kept set `Z` (an indicator). -/
noncomputable def setCoeff (coef : J → ℝ) (g : J → Bool) : ℝ := ∏ b, (if g b then coef b else 1)

omit [DecidableEq J] in
theorem setCoeff_nonneg {coef : J → ℝ} (hcoef : ∀ j, 0 ≤ coef j) (g : J → Bool) :
    0 ≤ setCoeff coef g :=
  prod_nonneg fun b _ => by split_ifs <;> [exact hcoef b; exact zero_le_one]

/-- **`prop:background-variance`(a), the displayed bound**, assembled from the exterior
expansion, the selected term, the background terms of the kept sets and the choice weights. -/
theorem background_variance_a {π : Type*} [DecidableEq π] (ι : ReflectionCut V)
    (μ R : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (j₀ : J) (hμ : ∀ j, j ≠ j₀ → ι.Positive (μ j))
    (F : (∀ b, X b) → ℝ)
    -- the selected aligned embeddings on `X`
    {E0 E1 : ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ} {m0 m1 : (ι.Half → X j₀) → ℝ}
    (hm0 : ∀ x, 0 ≤ m0 x) (hm1 : ∀ x, 0 ≤ m1 x) (hm0p : 0 < ∑ x, m0 x) (hm1p : 0 < ∑ x, m1 x)
    (hs0 : ∀ G H : (ι.Half → X j₀) → ℝ, ι.form E0 G H = ι.form E0 H G)
    (hs1 : ∀ G H : (ι.Half → X j₀) → ℝ, ι.form E1 G H = ι.form E1 H G)
    (hp0 : ∀ G : (ι.Half → X j₀) → ℝ, ι.form E0 G 1 = ∑ x, m0 x * G x)
    (hp1 : ∀ G : (ι.Half → X j₀) → ℝ, ι.form E1 G 1 = ∑ x, m1 x * G x)
    {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hcen0 : CentredNormLe ι E0 m0 k) (hcen1 : CentredNormLe ι E1 m1 k)
    -- the matching records of the other blocks and their actual half marginals
    (w0 w1 : ∀ j, (V → X j) → ℝ) (hw0 : ∀ j, j ≠ j₀ → ∀ z, 0 ≤ w0 j z)
    (hw1 : ∀ j, j ≠ j₀ → ∀ z, 0 ≤ w1 j z) (ms0 ms1 : ∀ j, (ι.Half → X j) → ℝ)
    (hq0 : ∀ j, j ≠ j₀ → plusMarginal ι (w0 j) = ms0 j)
    (hr0 : ∀ j, j ≠ j₀ → minusMarginal ι (w0 j) = ms0 j)
    (hq1 : ∀ j, j ≠ j₀ → plusMarginal ι (w1 j) = ms1 j)
    (hr1 : ∀ j, j ≠ j₀ → minusMarginal ι (w1 j) = ms1 j)
    (ht0 : ∀ j, j ≠ j₀ → ∀ G H : (ι.Half → X j) → ℝ,
      ι.form (signedIntegral (w0 j)) G H = ι.form (signedIntegral (w0 j)) H G)
    (ht1 : ∀ j, j ≠ j₀ → ∀ G H : (ι.Half → X j) → ℝ,
      ι.form (signedIntegral (w1 j)) G H = ι.form (signedIntegral (w1 j)) H G)
    -- the exterior: `Ñ₀ - μ ⪰ c D_{E_s}`
    (coef : J → ℝ) (hcoef : ∀ j, 0 ≤ coef j)
    (hR0 : ∀ j, j ≠ j₀ → ι.Positive (R j - coef j • ι.diagonalLaw (ms0 j)))
    (hR1 : ∀ j, j ≠ j₀ → ι.Positive (R j - coef j • ι.diagonalLaw (ms1 j)))
    -- the kept nonempty sets and their patterns
    (Zs : Finset (J → Bool)) (hZs0 : ∀ g ∈ Zs, g j₀ = false)
    (hZsne : (fun _ => false) ∉ Zs) (pats : Finset π) (pat : (J → Bool) → π)
    (hpat : ∀ g ∈ Zs, pat g ∈ pats) (W : π → ℝ)
    (hW : ∀ r ∈ pats, W r ≤ ∑ g ∈ Zs.filter (fun g => pat g = r), setCoeff coef g)
    -- the numbers of the selected term and of the background terms
    {Yμ CX Cm ℓ η e z₂ : ℝ} (hY : 0 ≤ Yμ) (hCX : CX ≤ Cm) (hCm : 0 < Cm) (hz₂ : 0 ≤ z₂)
    (ℓr Cr ηr er CXZ : π → ℝ) (hCr : ∀ r, 0 ≤ Cr r) (her : ∀ r, 0 ≤ er r)
    (hCXZ : ∀ r, CXZ r ≤ Cm * Cr r)
    -- (E1) and `lem:record:paired-e-joint`(b) for `X` and for every `X ∪ Z`
    (hDsel0 : energyAt μ j₀ (ι.diagonalLaw m0) F ≤ (1 + z₂) * CX * Yμ)
    (hDsel1 : energyAt μ j₀ (ι.diagonalLaw m1) F ≤ (1 + z₂) * CX * Yμ)
    (hbsel : (ℓ - Cm * η - e) * Yμ ≤ (energyAt μ j₀ E0 F + energyAt μ j₀ E1 F) / 2)
    (hDZ0 : ∀ g ∈ Zs, energyAt (fun b => if g b then ι.diagonalLaw (ms0 b) else μ b) j₀
      (ι.diagonalLaw m0) F ≤ (1 + z₂) * CXZ (pat g) * Yμ)
    (hDZ1 : ∀ g ∈ Zs, energyAt (fun b => if g b then ι.diagonalLaw (ms1 b) else μ b) j₀
      (ι.diagonalLaw m1) F ≤ (1 + z₂) * CXZ (pat g) * Yμ)
    (hbZ : ∀ g ∈ Zs, (ℓr (pat g) - Cm * Cr (pat g) * ηr (pat g) - er (pat g)) * Yμ ≤
      (energyAt (fun b => if g b then signedIntegral (w0 b) else μ b) j₀ E0 F +
        energyAt (fun b => if g b then signedIntegral (w1 b) else μ b) j₀ E1 F) / 2) :
    (Cm * ((ℓ / Cm - η - k) / (1 - k) +
        ∑ r ∈ pats, W r * (max 0 (ℓr r / Cm - Cr r * (ηr r + k)) / (1 - k))) -
      (e + k * z₂ * Cm) / (1 - k) -
      ∑ g ∈ Zs, setCoeff coef g * ((er (pat g) + k * z₂ * Cm * Cr (pat g)) / (1 - k))) * Yμ ≤
      (energyAt (fun b => μ b + R b) j₀ (indepLaw ι m0) F +
        energyAt (fun b => μ b + R b) j₀ (indepLaw ι m1) F) / 2 := by
  have h1k : 0 < 1 - k := by linarith
  -- the selected term
  have hSel := background_selected ι μ j₀ hμ F hm0 hm1 hm0p hm1p hs0 hs1 hp0 hp1 hk0 hk1 hcen0
    hcen1 hY hCX hCm hz₂ hDsel0 hDsel1 hbsel
  -- the background terms
  have hT : ∀ g ∈ Zs,
      (Cm * (max 0 (ℓr (pat g) / Cm - Cr (pat g) * (ηr (pat g) + k)) / (1 - k)) -
        (er (pat g) + k * z₂ * Cm * Cr (pat g)) / (1 - k)) * Yμ ≤
      (energyAt (fun b => if g b then ι.diagonalLaw (ms0 b) else μ b) j₀ (indepLaw ι m0) F +
        energyAt (fun b => if g b then ι.diagonalLaw (ms1 b) else μ b) j₀
          (indepLaw ι m1) F) / 2 := by
    intro g hg
    have hg0 := hZs0 g hg
    have hne : ∀ j, g j = true → j ≠ j₀ := fun j hj h => by rw [h, hg0] at hj; cases hj
    exact background_term_set ι μ j₀ g hg0 (fun j hj _ => hμ j hj) F hm0 hm1 hm0p hm1p hs0 hs1
      hp0 hp1 hk0 hk1 hcen0 hcen1 w0 w1 (fun j hj => hw0 j (hne j hj))
      (fun j hj => hw1 j (hne j hj)) ms0 ms1 (fun j hj => hq0 j (hne j hj))
      (fun j hj => hr0 j (hne j hj)) (fun j hj => hq1 j (hne j hj))
      (fun j hj => hr1 j (hne j hj)) (fun j hj => ht0 j (hne j hj))
      (fun j hj => ht1 j (hne j hj)) hY hCm (hCr _) hz₂ (her _) (hCXZ _) (hDZ0 g hg)
      (hDZ1 g hg) (hbZ g hg)
  -- the exterior expansion, for `s = 0, 1`, over `Z = ∅` and the kept sets
  have hms0 : ∀ j, j ≠ j₀ → ∀ x, 0 ≤ ms0 j x := fun j hj x =>
    hq0 j hj ▸ plusMarginal_nonneg ι (hw0 j hj) x
  have hms1 : ∀ j, j ≠ j₀ → ∀ x, 0 ≤ ms1 j x := fun j hj x =>
    hq1 j hj ▸ plusMarginal_nonneg ι (hw1 j hj) x
  have hZs' : ∀ g ∈ insert (fun _ => false) Zs, g j₀ = false := by
    intro g hg
    rcases mem_insert.mp hg with h | h
    · rw [h]
    · exact hZs0 g h
  have hex : ∀ (ms : ∀ j, (ι.Half → X j) → ℝ) (m : (ι.Half → X j₀) → ℝ),
      (∀ x, 0 ≤ m x) → (∀ j, j ≠ j₀ → ∀ x, 0 ≤ ms j x) →
      (∀ j, j ≠ j₀ → ι.Positive (R j - coef j • ι.diagonalLaw (ms j))) →
      energyAt μ j₀ (indepLaw ι m) F + ∑ g ∈ Zs, setCoeff coef g *
          energyAt (fun b => if g b then ι.diagonalLaw (ms b) else μ b) j₀ (indepLaw ι m) F ≤
        energyAt (fun b => μ b + R b) j₀ (indepLaw ι m) F := by
    intro ms m hm hms hRs
    have h := exterior_expansion_ge ι μ R (fun b => ι.diagonalLaw (ms b)) j₀
      (positive_indepLaw ι hm) hμ (fun j hj => ι.diagonalLaw_positive (hms j hj)) coef hcoef
      hRs (insert (fun _ => false) Zs) hZs' F
    rw [sum_insert hZsne] at h
    have e0 : setCoeff coef (fun _ => false) *
        energyAt (fun b => if (fun _ => false : J → Bool) b then ι.diagonalLaw (ms b) else μ b)
          j₀ (indepLaw ι m) F = energyAt μ j₀ (indepLaw ι m) F := by
      simp [setCoeff]
    unfold setCoeff at e0 ⊢
    rw [e0] at h
    exact h
  have hex0 := hex ms0 m0 hm0 hms0 hR0
  have hex1 := hex ms1 m1 hm1 hms1 hR1
  -- assemble
  have hext : (energyAt μ j₀ (indepLaw ι m0) F + energyAt μ j₀ (indepLaw ι m1) F) / 2 +
      ∑ g ∈ Zs, setCoeff coef g *
        ((energyAt (fun b => if g b then ι.diagonalLaw (ms0 b) else μ b) j₀ (indepLaw ι m0) F +
          energyAt (fun b => if g b then ι.diagonalLaw (ms1 b) else μ b) j₀
            (indepLaw ι m1) F) / 2) ≤
      (energyAt (fun b => μ b + R b) j₀ (indepLaw ι m0) F +
        energyAt (fun b => μ b + R b) j₀ (indepLaw ι m1) F) / 2 := by
    have e : ∑ g ∈ Zs, setCoeff coef g *
        ((energyAt (fun b => if g b then ι.diagonalLaw (ms0 b) else μ b) j₀ (indepLaw ι m0) F +
          energyAt (fun b => if g b then ι.diagonalLaw (ms1 b) else μ b) j₀
            (indepLaw ι m1) F) / 2) =
        (∑ g ∈ Zs, setCoeff coef g *
          energyAt (fun b => if g b then ι.diagonalLaw (ms0 b) else μ b) j₀ (indepLaw ι m0) F +
        ∑ g ∈ Zs, setCoeff coef g *
          energyAt (fun b => if g b then ι.diagonalLaw (ms1 b) else μ b) j₀
            (indepLaw ι m1) F) / 2 := by
      rw [← sum_add_distrib, sum_div]
      exact sum_congr rfl fun g _ => by ring
    rw [e]
    linarith
  have hp : ∀ r ∈ pats, 0 ≤ max 0 (ℓr r / Cm - Cr r * (ηr r + k)) / (1 - k) :=
    fun r _ => div_nonneg (le_max_left _ _) h1k.le
  have := background_assembly Zs pats pat hpat (setCoeff coef)
    (fun g => (energyAt (fun b => if g b then ι.diagonalLaw (ms0 b) else μ b) j₀
        (indepLaw ι m0) F +
      energyAt (fun b => if g b then ι.diagonalLaw (ms1 b) else μ b) j₀ (indepLaw ι m1) F) / 2)
    (fun g => (er (pat g) + k * z₂ * Cm * Cr (pat g)) / (1 - k))
    (fun r => max 0 (ℓr r / Cm - Cr r * (ηr r + k)) / (1 - k)) W hY hCm.le
    (fun g _ => setCoeff_nonneg hcoef g) hp hSel hT hext hW
  exact this

end Sarkozy.Variance

namespace Sarkozy.Variance

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]

/-- **`prop:background-variance`(a), the class cost**: if the displayed bound
`½ ∑_s Y^{Ñ₀}[J_s] ≥ (C_m b̃ - z_b) Y` holds (`background_variance_a`), then the class of the two
aligned matching assignments, with selected differences `ζ_s` of bilinear bound `γ` relative to
the centred norms of `m_s`, prices `γ C_X`, and the two bounds of
`lem:record:variance-interface`(ii) relative to `Ñ₀` (hypotheses), has cost `B - g_E(m)`,
`g_E(m) = [b̃ - R_*]_+`, up to the explicit error `z₃ + z₄ + z_b`; the comparison of `Ñ` with `Ñ₀`
is made once. -/
theorem background_variance_class_cost (ι : ReflectionCut V)
    (N lam O' : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (j₀ : J)
    (hN : ∀ j, j ≠ j₀ → ι.Bracket (N j) (lam j) (N j)) (F : (∀ b, X b) → ℝ)
    {m0 m1 : (ι.Half → X j₀) → ℝ} (hm0 : ∀ x, 0 ≤ m0 x) (hm1 : ∀ x, 0 ≤ m1 x)
    (ζ0 ζ1 : ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ) {γ : ℝ} (hγ : 0 ≤ γ)
    (hζ0 : ∀ G H : (ι.Half → X j₀) → ℝ, |ι.form ζ0 G H| ≤
      γ * Real.sqrt (ι.form (ι.diagonalLaw m0 - indepLaw ι m0) G G) *
        Real.sqrt (ι.form (ι.diagonalLaw m0 - indepLaw ι m0) H H))
    (hζ1 : ∀ G H : (ι.Half → X j₀) → ℝ, |ι.form ζ1 G H| ≤
      γ * Real.sqrt (ι.form (ι.diagonalLaw m1 - indepLaw ι m1) G G) *
        Real.sqrt (ι.form (ι.diagonalLaw m1 - indepLaw ι m1) H H))
    {Yμ CX Cm bt zb z₃ z₄ Bf Rerr Rstar : ℝ} (hY : 0 ≤ Yμ) (hCX : 1 ≤ CX) (hCm : CX ≤ Cm)
    (hzb : 0 ≤ zb) (hz₄ : 0 ≤ z₄) (hR0 : 0 ≤ Rerr) (hRs : Rerr ≤ Rstar)
    (hbound : (Cm * bt - zb) * Yμ ≤
      (energyAt O' j₀ (indepLaw ι m0) F + energyAt O' j₀ (indepLaw ι m1) F) / 2)
    (hDiagN0 : energyAt N j₀ (ι.diagonalLaw m0) F ≤ (Bf + z₃) * CX * Yμ)
    (hDiagN1 : energyAt N j₀ (ι.diagonalLaw m1) F ≤ (Bf + z₃) * CX * Yμ)
    (hJN0 : energyAt O' j₀ (indepLaw ι m0) F - (Rerr + z₄) * CX * Yμ ≤
      energyAt N j₀ (indepLaw ι m0) F)
    (hJN1 : energyAt O' j₀ (indepLaw ι m1) F - (Rerr + z₄) * CX * Yμ ≤
      energyAt N j₀ (indepLaw ι m1) F) :
    |energyAt lam j₀ ζ0 F| + |energyAt lam j₀ ζ1 F| ≤
      (Bf - max 0 (bt - Rstar) + (z₃ + z₄ + zb)) * (γ * CX + γ * CX) * Yμ := by
  let m : Bool → (ι.Half → X j₀) → ℝ := fun s => if s then m1 else m0
  let ζ : Bool → ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ := fun s => if s then ζ1 else ζ0
  have h := class_cost_of_product_energy ι N lam O' j₀ hN F (univ : Finset Bool) univ_nonempty m
    (fun s _ => by cases s <;> simp [m, hm0, hm1]) ζ hγ
    (fun s _ => by cases s <;> simp [ζ, m, hζ0, hζ1])
    (Yμ := Yμ) (CX := CX) (Cm := Cm) (bt := bt) (zb := zb) (z₃ := z₃) (z₄ := z₄) (Bf := Bf)
    (Rerr := Rerr) (Rstar := Rstar) hY hCX hCm hzb hz₄ hR0 hRs
    (by
      have e : (∑ s ∈ (univ : Finset Bool), energyAt O' j₀ (indepLaw ι (m s)) F) /
          (univ : Finset Bool).card =
          (energyAt O' j₀ (indepLaw ι m0) F + energyAt O' j₀ (indepLaw ι m1) F) / 2 := by
        simp [m, add_comm]
      rw [e]
      exact hbound)
    (fun s _ => by cases s <;> [exact hDiagN0; exact hDiagN1])
    (fun s _ => by cases s <;> [exact hJN0; exact hJN1])
  rw [Fintype.sum_bool, Fintype.sum_bool] at h
  simp only [ζ, ↓reduceIte, Bool.false_eq_true] at h
  linarith

end Sarkozy.Variance
