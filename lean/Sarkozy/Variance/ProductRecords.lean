module

public import Sarkozy.Variance.ProductInterpolation

/-!
# Centred interpolation for products of records ((P4) with (P3) of `lem:energy-toolkit`)

`paper/sections/10_comparison_lemmas.tex`, `lem:energy-toolkit` (P4) and (P3), in the form used
by `lem:var-gain` (Section 22) for a selected set `X` of blocks, **each block its own factor** of
the product law (no regrouping of the factors is needed).

On every block `𝔅 ∈ X` let `π_𝔅` be a record: a nonnegative weight, symmetric at the cut `c`, with
both half marginals `m_𝔅` and centred norm `‖T_𝔅 - 𝒥‖ ≤ κ_𝔅 ≤ κ`. With positive outside factors,
`Y[⊗_X π ⊗ O] ≤ (1 - κ) Y[⊗_X J(m) ⊗ O] + κ Y[⊗_X Diag(m) ⊗ O]`
(`energy_le_product_records`). This is (P3) for the product record `⊗_X π_𝔅`, whose half marginal
is `⊗ m_𝔅` and whose centred norm is at most `max κ_𝔅` by (P4); since `J(⊗m) = ⊗J(m)` and
`Diag(⊗m) = ⊗Diag(m)`, it is the inequality that `lem:var-gain`(a) uses.

**Proof** (telescoping over the blocks, by induction on the set `S ⊆ X` of blocks carrying
`π`; the others carry `J(m)`): replacing `J(m_k)` by `π_k` at one block changes the energy by
`Y[⋯ ⊗ (π_k - J(m_k)) ⊗ ⋯]`. The `±` tensorization ((P5), WP-R's `abs_energy_le_of_add_sub`)
with `κ_k(Diag(m_k) - J(m_k)) ± (π_k - J(m_k)) ⪰ 0` (`centred_pm`) at `k` and
`Diag(m_𝔅) ± π_𝔅 ⪰ 0` (`diag_pm_of_weight`) on the blocks already replaced bounds it by
`κ_k` times the corresponding difference of the diagonal energies, which is nonnegative.
-/

@[expose] public section

open Finset
open scoped BigOperators
open Sarkozy.RecordExpansion

namespace Sarkozy.Variance

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]

/-- The family with the records `w` on `S`, the products `J(m)` on `X ∖ S` and `O` off `X`. -/
noncomputable def recFam (c : ReflectionCut V) (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (Xs S : Finset J) (w : ∀ j, (V → X j) → ℝ) (m : ∀ j, (c.Half → X j) → ℝ) :
    ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ :=
  fun j => if j ∈ S then signedIntegral (w j) else if j ∈ Xs then indepLaw c (m j) else O j

/-- The family with the diagonals `Diag(m)` on `S`, the products `J(m)` on `X ∖ S` and `O` off
`X`. -/
noncomputable def diagFam (c : ReflectionCut V) (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (Xs S : Finset J) (m : ∀ j, (c.Half → X j) → ℝ) : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ :=
  fun j => if j ∈ S then c.diagonalLaw (m j) else if j ∈ Xs then indepLaw c (m j) else O j

/-- **(P3) for a product of records**, the telescoping estimate: for `S ⊆ X`,
`|Y[recFam S] - Y[recFam ∅]| ≤ κ (Y[diagFam S] - Y[diagFam ∅])`. -/
theorem product_records_telescope (c : ReflectionCut V) (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (Xs : Finset J) (hO : ∀ j, j ∉ Xs → c.Positive (O j)) (F : (∀ b, X b) → ℝ)
    (w : ∀ j, (V → X j) → ℝ) (m : ∀ j, (c.Half → X j) → ℝ)
    (hw : ∀ j ∈ Xs, ∀ z, 0 ≤ w j z) (hp : ∀ j ∈ Xs, plusMarginal c (w j) = m j)
    (hn : ∀ j ∈ Xs, minusMarginal c (w j) = m j)
    (ht : ∀ j ∈ Xs, ∀ G H : (c.Half → X j) → ℝ,
      c.form (signedIntegral (w j)) G H = c.form (signedIntegral (w j)) H G)
    (hmpos : ∀ j ∈ Xs, 0 < ∑ x, m j x) (κj : J → ℝ)
    (hcen : ∀ j ∈ Xs, CentredNormLe c (signedIntegral (w j)) (m j) (κj j)) {κ : ℝ}
    (hκ : ∀ j ∈ Xs, κj j ≤ κ) :
    ∀ S : Finset J, S ⊆ Xs →
      |diagonalIntegral (tensorLaw (recFam c O Xs S w m)) F -
          diagonalIntegral (tensorLaw (recFam c O Xs ∅ w m)) F| ≤
        κ * (diagonalIntegral (tensorLaw (diagFam c O Xs S m)) F -
          diagonalIntegral (tensorLaw (diagFam c O Xs ∅ m)) F) := by
  have hm : ∀ j ∈ Xs, ∀ x, 0 ≤ m j x := fun j hj x => hp j hj ▸ plusMarginal_nonneg c (hw j hj) x
  intro S
  induction S using Finset.induction_on with
  | empty => intro _; simp
  | insert k S hk ih =>
    intro hsub
    have hkX : k ∈ Xs := hsub (mem_insert_self k S)
    have hSX : S ⊆ Xs := (subset_insert k S).trans hsub
    have ih' := ih hSX
    -- the families at `insert k S` are updates of those at `S`
    have eP : recFam c O Xs (insert k S) w m =
        Function.update (recFam c O Xs S w m) k (signedIntegral (w k)) := by
      funext j
      by_cases hj : j = k
      · subst hj
        simp [recFam]
      · simp [recFam, mem_insert, hj]
    have eP0 : recFam c O Xs S w m =
        Function.update (recFam c O Xs S w m) k (indepLaw c (m k)) := by
      funext j
      by_cases hj : j = k
      · subst hj
        simp [recFam, hk, hkX]
      · simp [Function.update_of_ne hj]
    have eD : diagFam c O Xs (insert k S) m =
        Function.update (diagFam c O Xs S m) k (c.diagonalLaw (m k)) := by
      funext j
      by_cases hj : j = k
      · subst hj
        simp [diagFam]
      · simp [diagFam, mem_insert, hj]
    have eD0 : diagFam c O Xs S m =
        Function.update (diagFam c O Xs S m) k (indepLaw c (m k)) := by
      funext j
      by_cases hj : j = k
      · subst hj
        simp [diagFam, hk, hkX]
      · simp [Function.update_of_ne hj]
    -- the step
    have hstepP : diagonalIntegral (tensorLaw (recFam c O Xs (insert k S) w m)) F -
        diagonalIntegral (tensorLaw (recFam c O Xs S w m)) F =
        energyAt (recFam c O Xs S w m) k (signedIntegral (w k) - indepLaw c (m k)) F := by
      rw [energyAt_sub]
      unfold energyAt
      rw [← eP, ← eP0]
    have hstepD : diagonalIntegral (tensorLaw (diagFam c O Xs (insert k S) m)) F -
        diagonalIntegral (tensorLaw (diagFam c O Xs S m)) F =
        energyAt (diagFam c O Xs S m) k (c.diagonalLaw (m k) - indepLaw c (m k)) F := by
      rw [energyAt_sub]
      unfold energyAt
      rw [← eD, ← eD0]
    -- the `±` tensorization at the step
    obtain ⟨hA1, hA2⟩ := centred_pm c (hm k hkX) (hmpos k hkX) (ht k hkX)
      (fun G => by rw [form_signedIntegral_one_right, hp k hkX]) (hcen k hkX)
    have hpm : |energyAt (recFam c O Xs S w m) k (signedIntegral (w k) - indepLaw c (m k)) F| ≤
        energyAt (diagFam c O Xs S m) k
          (κj k • (c.diagonalLaw (m k) - indepLaw c (m k))) F := by
      apply abs_energy_le_of_add_sub
      · intro j
        by_cases hj : j = k
        · subst hj
          simp only [Function.update_self]
          exact hA2
        · simp only [Function.update_of_ne hj, recFam, diagFam]
          by_cases hjS : j ∈ S
          · simp only [hjS, ↓reduceIte]
            exact (diag_pm_of_weight c (hw j (hSX hjS)) (hp j (hSX hjS)) (hn j (hSX hjS))
              (ht j (hSX hjS))).1
          · by_cases hjX : j ∈ Xs
            · simp only [hjS, hjX, ↓reduceIte]
              exact (positive_indepLaw c (hm j hjX)).add (positive_indepLaw c (hm j hjX))
            · simp only [hjS, hjX, ↓reduceIte]
              exact (hO j hjX).add (hO j hjX)
      · intro j
        by_cases hj : j = k
        · subst hj
          simp only [Function.update_self]
          exact hA1
        · simp only [Function.update_of_ne hj, recFam, diagFam]
          by_cases hjS : j ∈ S
          · simp only [hjS, ↓reduceIte]
            exact (diag_pm_of_weight c (hw j (hSX hjS)) (hp j (hSX hjS)) (hn j (hSX hjS))
              (ht j (hSX hjS))).2
          · by_cases hjX : j ∈ Xs
            · simp only [hjS, hjX, ↓reduceIte, sub_self]
              exact positive_zero c
            · simp only [hjS, hjX, ↓reduceIte, sub_self]
              exact positive_zero c
    -- the diagonal step is nonnegative
    have hDnn : 0 ≤ energyAt (diagFam c O Xs S m) k
        (c.diagonalLaw (m k) - indepLaw c (m k)) F := by
      apply energyAt_nonneg c _ k _ (positive_diagonal_sub_indep c (hm k hkX)) F
      intro j hj
      simp only [diagFam]
      by_cases hjS : j ∈ S
      · simp only [hjS, ↓reduceIte]
        exact c.diagonalLaw_positive (hm j (hSX hjS))
      · by_cases hjX : j ∈ Xs
        · simp only [hjS, hjX, ↓reduceIte]
          exact positive_indepLaw c (hm j hjX)
        · simp only [hjS, hjX, ↓reduceIte]
          exact hO j hjX
    rw [energyAt_smul] at hpm
    have hκk : κj k * energyAt (diagFam c O Xs S m) k
        (c.diagonalLaw (m k) - indepLaw c (m k)) F ≤
        κ * energyAt (diagFam c O Xs S m) k (c.diagonalLaw (m k) - indepLaw c (m k)) F :=
      mul_le_mul_of_nonneg_right (hκ k hkX) hDnn
    rw [← hstepP, ← hstepD] at hpm
    rw [← hstepD] at hκk
    have htri := abs_add_le
      (diagonalIntegral (tensorLaw (recFam c O Xs (insert k S) w m)) F -
        diagonalIntegral (tensorLaw (recFam c O Xs S w m)) F)
      (diagonalIntegral (tensorLaw (recFam c O Xs S w m)) F -
        diagonalIntegral (tensorLaw (recFam c O Xs ∅ w m)) F)
    rw [sub_add_sub_cancel] at htri
    have e3 : κ * (diagonalIntegral (tensorLaw (diagFam c O Xs (insert k S) m)) F -
        diagonalIntegral (tensorLaw (diagFam c O Xs ∅ m)) F) =
        κ * (diagonalIntegral (tensorLaw (diagFam c O Xs (insert k S) m)) F -
          diagonalIntegral (tensorLaw (diagFam c O Xs S m)) F) +
        κ * (diagonalIntegral (tensorLaw (diagFam c O Xs S m)) F -
          diagonalIntegral (tensorLaw (diagFam c O Xs ∅ m)) F) := by ring
    rw [e3]
    linarith

/-- **(P3) for a product of records, energy form**:
`Y[⊗_X π ⊗ O] ≤ (1 - κ) Y[⊗_X J(m) ⊗ O] + κ Y[⊗_X Diag(m) ⊗ O]` for `κ ≥ max_𝔅 κ_𝔅`. -/
theorem energy_le_product_records (c : ReflectionCut V) (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (Xs : Finset J) (hO : ∀ j, j ∉ Xs → c.Positive (O j)) (F : (∀ b, X b) → ℝ)
    (w : ∀ j, (V → X j) → ℝ) (m : ∀ j, (c.Half → X j) → ℝ)
    (hw : ∀ j ∈ Xs, ∀ z, 0 ≤ w j z) (hp : ∀ j ∈ Xs, plusMarginal c (w j) = m j)
    (hn : ∀ j ∈ Xs, minusMarginal c (w j) = m j)
    (ht : ∀ j ∈ Xs, ∀ G H : (c.Half → X j) → ℝ,
      c.form (signedIntegral (w j)) G H = c.form (signedIntegral (w j)) H G)
    (hmpos : ∀ j ∈ Xs, 0 < ∑ x, m j x) (κj : J → ℝ)
    (hcen : ∀ j ∈ Xs, CentredNormLe c (signedIntegral (w j)) (m j) (κj j)) {κ : ℝ}
    (hκ : ∀ j ∈ Xs, κj j ≤ κ) :
    diagonalIntegral (tensorLaw (recFam c O Xs Xs w m)) F ≤
      (1 - κ) * diagonalIntegral (tensorLaw (recFam c O Xs ∅ w m)) F +
        κ * diagonalIntegral (tensorLaw (diagFam c O Xs Xs m)) F := by
  have h := product_records_telescope c O Xs hO F w m hw hp hn ht hmpos κj hcen hκ Xs le_rfl
  have e : recFam c O Xs ∅ w m = diagFam c O Xs ∅ m := by
    funext j
    simp [recFam, diagFam]
  rw [e] at h ⊢
  have := le_abs_self (diagonalIntegral (tensorLaw (recFam c O Xs Xs w m)) F -
    diagonalIntegral (tensorLaw (diagFam c O Xs ∅ m)) F)
  nlinarith

end Sarkozy.Variance
