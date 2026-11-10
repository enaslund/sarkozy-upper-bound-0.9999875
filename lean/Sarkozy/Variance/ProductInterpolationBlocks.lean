module

public import Sarkozy.Variance.ProductRecords

/-!
# Product centred interpolation for products of records ((P3′) with (P4), blocks as factors)

`paper/sections/10_comparison_lemmas.tex`, `lem:energy-toolkit` (P3′) with (P4), for a selected set
`X` of blocks and a background set `Z` of blocks, disjoint, **each block its own factor**. On `X`
the records `π_𝔅` are nonnegative symmetric weights with half marginals `m_𝔅` and centred norms
`κ_𝔅 ≤ κ`; on `Z` the records `π'_𝔅` are nonnegative symmetric weights with half marginals `m'_𝔅`.
Then (`energy_le_product_interpolation_blocks`)
`Y[⊗_X π ⊗ ⊗_Z π' ⊗ O] ≤ (1 - κ) Y[⊗_X J(m) ⊗ ⊗_Z Diag(m') ⊗ O]
  + κ Y[⊗_X Diag(m) ⊗ ⊗_Z Diag(m') ⊗ O]`.

The proof is the telescoping of `ProductRecords.lean`, with the `±` condition
`Diag(m'_𝔅) ± π'_𝔅 ⪰ 0` (`diag_pm_of_weight`) at the blocks of `Z`, followed by
`Y[⊗_X J ⊗ ⊗_Z π'] ≤ Y[⊗_X J ⊗ ⊗_Z Diag(m')]` (the same `±` tensorization).
-/

@[expose] public section

open Finset
open scoped BigOperators
open Sarkozy.RecordExpansion

namespace Sarkozy.Variance

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]

/-- Records `w` on `S`, products `J(m)` on `X ∖ S`, records `w'` on `Z`, `O` elsewhere. -/
noncomputable def recFamZ (c : ReflectionCut V) (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (Xs Zs S : Finset J) (w : ∀ j, (V → X j) → ℝ) (m : ∀ j, (c.Half → X j) → ℝ)
    (w' : ∀ j, (V → X j) → ℝ) : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ :=
  fun j => if j ∈ S then signedIntegral (w j) else if j ∈ Xs then indepLaw c (m j)
    else if j ∈ Zs then signedIntegral (w' j) else O j

/-- Diagonals `Diag(m)` on `S`, products `J(m)` on `X ∖ S`, diagonals `Diag(m')` on `Z`, `O`
elsewhere. -/
noncomputable def diagFamZ (c : ReflectionCut V) (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (Xs Zs S : Finset J) (m m' : ∀ j, (c.Half → X j) → ℝ) : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ :=
  fun j => if j ∈ S then c.diagonalLaw (m j) else if j ∈ Xs then indepLaw c (m j)
    else if j ∈ Zs then c.diagonalLaw (m' j) else O j

/-- **(P3) for a product of records**, the telescoping estimate: for `S ⊆ X`,
`|Y[recFam S] - Y[recFam ∅]| ≤ κ (Y[diagFam S] - Y[diagFam ∅])`. -/
theorem product_records_telescope_Z (c : ReflectionCut V) (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (Xs : Finset J) (Zs : Finset J)
    (hO : ∀ j, j ∉ Xs → j ∉ Zs → c.Positive (O j)) (F : (∀ b, X b) → ℝ)
    (w : ∀ j, (V → X j) → ℝ) (m : ∀ j, (c.Half → X j) → ℝ)
    (hw : ∀ j ∈ Xs, ∀ z, 0 ≤ w j z) (hp : ∀ j ∈ Xs, plusMarginal c (w j) = m j)
    (hn : ∀ j ∈ Xs, minusMarginal c (w j) = m j)
    (ht : ∀ j ∈ Xs, ∀ G H : (c.Half → X j) → ℝ,
      c.form (signedIntegral (w j)) G H = c.form (signedIntegral (w j)) H G)
    (hmpos : ∀ j ∈ Xs, 0 < ∑ x, m j x) (κj : J → ℝ)
    (hcen : ∀ j ∈ Xs, CentredNormLe c (signedIntegral (w j)) (m j) (κj j)) {κ : ℝ}
    (hκ : ∀ j ∈ Xs, κj j ≤ κ)
    (w' : ∀ j, (V → X j) → ℝ) (m' : ∀ j, (c.Half → X j) → ℝ)
    (hw' : ∀ j ∈ Zs, ∀ z, 0 ≤ w' j z) (hp' : ∀ j ∈ Zs, plusMarginal c (w' j) = m' j)
    (hn' : ∀ j ∈ Zs, minusMarginal c (w' j) = m' j)
    (ht' : ∀ j ∈ Zs, ∀ G H : (c.Half → X j) → ℝ,
      c.form (signedIntegral (w' j)) G H = c.form (signedIntegral (w' j)) H G) :
    ∀ S : Finset J, S ⊆ Xs →
      |diagonalIntegral (tensorLaw (recFamZ c O Xs Zs S w m w')) F -
          diagonalIntegral (tensorLaw (recFamZ c O Xs Zs ∅ w m w')) F| ≤
        κ * (diagonalIntegral (tensorLaw (diagFamZ c O Xs Zs S m m')) F -
          diagonalIntegral (tensorLaw (diagFamZ c O Xs Zs ∅ m m')) F) := by
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
    have eP : recFamZ c O Xs Zs (insert k S) w m w' =
        Function.update (recFamZ c O Xs Zs S w m w') k (signedIntegral (w k)) := by
      funext j
      by_cases hj : j = k
      · subst hj
        simp [recFamZ]
      · simp [recFamZ, mem_insert, hj]
    have eP0 : recFamZ c O Xs Zs S w m w' =
        Function.update (recFamZ c O Xs Zs S w m w') k (indepLaw c (m k)) := by
      funext j
      by_cases hj : j = k
      · subst hj
        simp [recFamZ, hk, hkX]
      · simp [Function.update_of_ne hj]
    have eD : diagFamZ c O Xs Zs (insert k S) m m' =
        Function.update (diagFamZ c O Xs Zs S m m') k (c.diagonalLaw (m k)) := by
      funext j
      by_cases hj : j = k
      · subst hj
        simp [diagFamZ]
      · simp [diagFamZ, mem_insert, hj]
    have eD0 : diagFamZ c O Xs Zs S m m' =
        Function.update (diagFamZ c O Xs Zs S m m') k (indepLaw c (m k)) := by
      funext j
      by_cases hj : j = k
      · subst hj
        simp [diagFamZ, hk, hkX]
      · simp [Function.update_of_ne hj]
    -- the step
    have hstepP : diagonalIntegral (tensorLaw (recFamZ c O Xs Zs (insert k S) w m w')) F -
        diagonalIntegral (tensorLaw (recFamZ c O Xs Zs S w m w')) F =
        energyAt (recFamZ c O Xs Zs S w m w') k (signedIntegral (w k) - indepLaw c (m k)) F := by
      rw [energyAt_sub]
      unfold energyAt
      rw [← eP, ← eP0]
    have hstepD : diagonalIntegral (tensorLaw (diagFamZ c O Xs Zs (insert k S) m m')) F -
        diagonalIntegral (tensorLaw (diagFamZ c O Xs Zs S m m')) F =
        energyAt (diagFamZ c O Xs Zs S m m') k (c.diagonalLaw (m k) - indepLaw c (m k)) F := by
      rw [energyAt_sub]
      unfold energyAt
      rw [← eD, ← eD0]
    -- the `±` tensorization at the step
    obtain ⟨hA1, hA2⟩ := centred_pm c (hm k hkX) (hmpos k hkX) (ht k hkX)
      (fun G => by rw [form_signedIntegral_one_right, hp k hkX]) (hcen k hkX)
    have hpm : |energyAt (recFamZ c O Xs Zs S w m w') k
          (signedIntegral (w k) - indepLaw c (m k)) F| ≤
        energyAt (diagFamZ c O Xs Zs S m m') k
          (κj k • (c.diagonalLaw (m k) - indepLaw c (m k))) F := by
      apply abs_energy_le_of_add_sub
      · intro j
        by_cases hj : j = k
        · subst hj
          simp only [Function.update_self]
          exact hA2
        · simp only [Function.update_of_ne hj, recFamZ, diagFamZ]
          by_cases hjS : j ∈ S
          · simp only [hjS, ↓reduceIte]
            exact (diag_pm_of_weight c (hw j (hSX hjS)) (hp j (hSX hjS)) (hn j (hSX hjS))
              (ht j (hSX hjS))).1
          · by_cases hjX : j ∈ Xs
            · simp only [hjS, hjX, ↓reduceIte]
              exact (positive_indepLaw c (hm j hjX)).add (positive_indepLaw c (hm j hjX))
            · by_cases hjZ : j ∈ Zs
              · simp only [hjS, hjX, hjZ, ↓reduceIte]
                exact (diag_pm_of_weight c (hw' j hjZ) (hp' j hjZ) (hn' j hjZ) (ht' j hjZ)).1
              · simp only [hjS, hjX, hjZ, ↓reduceIte]
                exact (hO j hjX hjZ).add (hO j hjX hjZ)
      · intro j
        by_cases hj : j = k
        · subst hj
          simp only [Function.update_self]
          exact hA1
        · simp only [Function.update_of_ne hj, recFamZ, diagFamZ]
          by_cases hjS : j ∈ S
          · simp only [hjS, ↓reduceIte]
            exact (diag_pm_of_weight c (hw j (hSX hjS)) (hp j (hSX hjS)) (hn j (hSX hjS))
              (ht j (hSX hjS))).2
          · by_cases hjX : j ∈ Xs
            · simp only [hjS, hjX, ↓reduceIte, sub_self]
              exact positive_zero c
            · by_cases hjZ : j ∈ Zs
              · simp only [hjS, hjX, hjZ, ↓reduceIte]
                exact (diag_pm_of_weight c (hw' j hjZ) (hp' j hjZ) (hn' j hjZ) (ht' j hjZ)).2
              · simp only [hjS, hjX, hjZ, ↓reduceIte, sub_self]
                exact positive_zero c
    -- the diagonal step is nonnegative
    have hDnn : 0 ≤ energyAt (diagFamZ c O Xs Zs S m m') k
        (c.diagonalLaw (m k) - indepLaw c (m k)) F := by
      apply energyAt_nonneg c _ k _ (positive_diagonal_sub_indep c (hm k hkX)) F
      intro j hj
      simp only [diagFamZ]
      by_cases hjS : j ∈ S
      · simp only [hjS, ↓reduceIte]
        exact c.diagonalLaw_positive (hm j (hSX hjS))
      · by_cases hjX : j ∈ Xs
        · simp only [hjS, hjX, ↓reduceIte]
          exact positive_indepLaw c (hm j hjX)
        · by_cases hjZ : j ∈ Zs
          · simp only [hjS, hjX, hjZ, ↓reduceIte]
            exact c.diagonalLaw_positive fun x => hp' j hjZ ▸ plusMarginal_nonneg c (hw' j hjZ) x
          · simp only [hjS, hjX, hjZ, ↓reduceIte]
            exact hO j hjX hjZ
    rw [energyAt_smul] at hpm
    have hκk : κj k * energyAt (diagFamZ c O Xs Zs S m m') k
        (c.diagonalLaw (m k) - indepLaw c (m k)) F ≤
        κ * energyAt (diagFamZ c O Xs Zs S m m') k (c.diagonalLaw (m k) - indepLaw c (m k)) F :=
      mul_le_mul_of_nonneg_right (hκ k hkX) hDnn
    rw [← hstepP, ← hstepD] at hpm
    rw [← hstepD] at hκk
    have htri := abs_add_le
      (diagonalIntegral (tensorLaw (recFamZ c O Xs Zs (insert k S) w m w')) F -
        diagonalIntegral (tensorLaw (recFamZ c O Xs Zs S w m w')) F)
      (diagonalIntegral (tensorLaw (recFamZ c O Xs Zs S w m w')) F -
        diagonalIntegral (tensorLaw (recFamZ c O Xs Zs ∅ w m w')) F)
    rw [sub_add_sub_cancel] at htri
    have e3 : κ * (diagonalIntegral (tensorLaw (diagFamZ c O Xs Zs (insert k S) m m')) F -
        diagonalIntegral (tensorLaw (diagFamZ c O Xs Zs ∅ m m')) F) =
        κ * (diagonalIntegral (tensorLaw (diagFamZ c O Xs Zs (insert k S) m m')) F -
          diagonalIntegral (tensorLaw (diagFamZ c O Xs Zs S m m')) F) +
        κ * (diagonalIntegral (tensorLaw (diagFamZ c O Xs Zs S m m')) F -
          diagonalIntegral (tensorLaw (diagFamZ c O Xs Zs ∅ m m')) F) := by ring
    rw [e3]
    linarith

/-- **(P3′) with (P4), blocks as factors**, energy form:
`Y[⊗_X π ⊗ ⊗_Z π' ⊗ O] ≤ (1 - κ) Y[⊗_X J(m) ⊗ ⊗_Z Diag(m') ⊗ O] +
κ Y[⊗_X Diag(m) ⊗ ⊗_Z Diag(m') ⊗ O]`. -/
theorem energy_le_product_interpolation_blocks (c : ReflectionCut V)
    (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (Xs : Finset J) (Zs : Finset J)
    (hO : ∀ j, j ∉ Xs → j ∉ Zs → c.Positive (O j)) (F : (∀ b, X b) → ℝ)
    (w : ∀ j, (V → X j) → ℝ) (m : ∀ j, (c.Half → X j) → ℝ)
    (hw : ∀ j ∈ Xs, ∀ z, 0 ≤ w j z) (hp : ∀ j ∈ Xs, plusMarginal c (w j) = m j)
    (hn : ∀ j ∈ Xs, minusMarginal c (w j) = m j)
    (ht : ∀ j ∈ Xs, ∀ G H : (c.Half → X j) → ℝ,
      c.form (signedIntegral (w j)) G H = c.form (signedIntegral (w j)) H G)
    (hmpos : ∀ j ∈ Xs, 0 < ∑ x, m j x) (κj : J → ℝ)
    (hcen : ∀ j ∈ Xs, CentredNormLe c (signedIntegral (w j)) (m j) (κj j)) {κ : ℝ}
    (hκ : ∀ j ∈ Xs, κj j ≤ κ)
    (w' : ∀ j, (V → X j) → ℝ) (m' : ∀ j, (c.Half → X j) → ℝ)
    (hw' : ∀ j ∈ Zs, ∀ z, 0 ≤ w' j z) (hp' : ∀ j ∈ Zs, plusMarginal c (w' j) = m' j)
    (hn' : ∀ j ∈ Zs, minusMarginal c (w' j) = m' j)
    (ht' : ∀ j ∈ Zs, ∀ G H : (c.Half → X j) → ℝ,
      c.form (signedIntegral (w' j)) G H = c.form (signedIntegral (w' j)) H G) :
    diagonalIntegral (tensorLaw (recFamZ c O Xs Zs Xs w m w')) F ≤
      (1 - κ) * diagonalIntegral (tensorLaw (diagFamZ c O Xs Zs ∅ m m')) F +
        κ * diagonalIntegral (tensorLaw (diagFamZ c O Xs Zs Xs m m')) F := by
  have hm : ∀ j ∈ Xs, ∀ x, 0 ≤ m j x := fun j hj x => hp j hj ▸ plusMarginal_nonneg c (hw j hj) x
  have htel := product_records_telescope_Z c O Xs Zs hO F w m hw hp hn ht hmpos κj hcen hκ w' m'
    hw' hp' hn' ht' Xs le_rfl
  -- `Y[⊗_X J ⊗ ⊗_Z π'] ≤ Y[⊗_X J ⊗ ⊗_Z Diag(m')]`
  have h0 : |diagonalIntegral (tensorLaw (recFamZ c O Xs Zs ∅ w m w')) F| ≤
      diagonalIntegral (tensorLaw (diagFamZ c O Xs Zs ∅ m m')) F := by
    apply abs_energy_le_of_add_sub
    · intro j
      simp only [recFamZ, diagFamZ, notMem_empty, ↓reduceIte]
      by_cases hjX : j ∈ Xs
      · simp only [hjX, ↓reduceIte]
        exact (positive_indepLaw c (hm j hjX)).add (positive_indepLaw c (hm j hjX))
      · by_cases hjZ : j ∈ Zs
        · simp only [hjX, hjZ, ↓reduceIte]
          exact (diag_pm_of_weight c (hw' j hjZ) (hp' j hjZ) (hn' j hjZ) (ht' j hjZ)).1
        · simp only [hjX, hjZ, ↓reduceIte]
          exact (hO j hjX hjZ).add (hO j hjX hjZ)
    · intro j
      simp only [recFamZ, diagFamZ, notMem_empty, ↓reduceIte]
      by_cases hjX : j ∈ Xs
      · simp only [hjX, ↓reduceIte, sub_self]
        exact positive_zero c
      · by_cases hjZ : j ∈ Zs
        · simp only [hjX, hjZ, ↓reduceIte]
          exact (diag_pm_of_weight c (hw' j hjZ) (hp' j hjZ) (hn' j hjZ) (ht' j hjZ)).2
        · simp only [hjX, hjZ, ↓reduceIte, sub_self]
          exact positive_zero c
  have h1 := le_abs_self (diagonalIntegral (tensorLaw (recFamZ c O Xs Zs Xs w m w')) F -
    diagonalIntegral (tensorLaw (recFamZ c O Xs Zs ∅ w m w')) F)
  have h2 := le_abs_self (diagonalIntegral (tensorLaw (recFamZ c O Xs Zs ∅ w m w')) F)
  nlinarith

end Sarkozy.Variance
