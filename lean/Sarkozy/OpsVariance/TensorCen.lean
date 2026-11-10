module

public import Sarkozy.OpsVariance.Forms
public import Sarkozy.Variance.ProductInterpolation
public import Sarkozy.EnvelopeInputs.SharpTensor
public import Sarkozy.RecordExpansion.SubsetExpansion

@[expose] public section

/-!
# The centred norm of a tensor product (`lem:sector`(c), (P4) in operator form)

`paper/sections/22_variance.tex`, `lem:record:paired-e-bridge`(b), `lem:record:old-f-marginal`(d)
("`T_X` is the tensor product of the prime operators `T_old`, each with `‖T_old − 𝒥‖ ≤ κ_X`");
`paper/sections/10_comparison_lemmas.tex`, (P4): "If `π_𝔅` are as in (P3) with half marginals
`m_𝔅` and constants `κ_𝔅`, then `⊗π_𝔅` is as in (P3) with half marginal `⊗m_𝔅` and constant
`max κ_𝔅`."

W1 proved (P4) in the energy form that (P3) needs, with each factor its own atom
(`energy_le_product_records`), and listed the `CentredNormLe` form of a tensor product as not
proved. At the paper's data a block is one atom and its label is the product of the labels at its
primes, so the block's (Cen) is the `CentredNormLe` of a tensor over the primes. Proved here:

* `bracket_add`, `bracket_mono`: brackets add, and their diagonal entries may be enlarged by
  positive measures;
* `matrix_indepLaw`, **`tensorLaw_indepLaw`**: `⊗_j J_c(m_j) = J_c(∏_j m_j)` (with
  `tensorLaw_diagonalLaw`, `⊗_j Diag_c(m_j) = Diag_c(∏_j m_j)`);
* **`centredNormLe_tensor`**: if every factor `π_j` is symmetric at `c` with half marginal `m_j > 0`
  and `‖T_j − 𝒥‖ ≤ κ_j ≤ κ ≤ 1`, then `‖⊗T_j − 𝒥‖ ≤ κ` relative to `∏ m_j`. The proof expands
  `π_j = J_j + E_j` and `Diag_j = J_j + A_j` over the subsets `S ≠ ∅` of factors: the term of `S`
  is bracketed by `(∏_{j∈S} κ_j) ⊗_S A ⊗ J ≤ κ ⊗_S A ⊗ J` (`Bracket.tensor` of the factor brackets
  `κ_j A_j ± E_j ⪰ 0`, W1's `centred_pm`), and the brackets add. No order is tensored with an
  indefinite factor.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.OpsVariance

open Sarkozy.RecordExpansion Sarkozy.Variance

section Brackets

variable {V X : Type*} [Fintype V] [DecidableEq V] {c : ReflectionCut V}

theorem bracket_add {L K R L' K' R' : ((V → X) → ℝ) →ₗ[ℝ] ℝ} (h : c.Bracket L K R)
    (h' : c.Bracket L' K' R') : c.Bracket (L + L') (K + K') (R + R') := by
  refine ⟨h.left_positive.add h'.left_positive, h.right_positive.add h'.right_positive, ?_⟩
  intro F G
  have h1 := h.nonneg F G
  have h2 := h'.nonneg F G
  rw [form_add_law, form_add_law, form_add_law]
  linarith

theorem bracket_mono {L K L' : ((V → X) → ℝ) →ₗ[ℝ] ℝ} (h : c.Bracket L K L)
    (hL : c.Positive (L' - L)) : c.Bracket L' K L' := by
  have hL' : c.Positive L' := by
    have := hL.add h.left_positive
    rwa [sub_add_cancel] at this
  refine ⟨hL', hL', ?_⟩
  intro F G
  have h1 := h.nonneg F G
  have h2 := hL.nonneg F
  have h3 := hL.nonneg G
  rw [form_sub_law] at h2 h3
  linarith

theorem bracket_zero : c.Bracket (0 : ((V → X) → ℝ) →ₗ[ℝ] ℝ) 0 0 := by
  refine ⟨⟨fun F G => by simp [ReflectionCut.form], fun F => by simp [ReflectionCut.form]⟩,
    ⟨fun F G => by simp [ReflectionCut.form], fun F => by simp [ReflectionCut.form]⟩, ?_⟩
  intro F G
  simp [ReflectionCut.form]

theorem bracket_sum {ι : Type*} (s : Finset ι) (L K : ι → ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (h : ∀ i ∈ s, c.Bracket (L i) (K i) (L i)) :
    c.Bracket (∑ i ∈ s, L i) (∑ i ∈ s, K i) (∑ i ∈ s, L i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (bracket_zero (c := c) (X := X))
  | insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi]
    exact bracket_add (h i (mem_insert_self i s)) (ih fun j hj => h j (mem_insert_of_mem hj))

end Brackets

section Indep

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]

/-- The cut matrix of `J_c(m)`: `m(x) m(y)/∑ m`. -/
theorem matrix_indepLaw {Y : Type*} [Fintype Y] [DecidableEq Y] (c : ReflectionCut V)
    (m : (c.Half → Y) → ℝ) (x y : c.Half → Y) :
    c.matrix (indepLaw c m) x y = m x * m y / ∑ z, m z := by
  rw [c.matrix_eq_density_join]
  unfold lawDensity indepLaw
  change (1 / ∑ z, m z) * ∑ p : (c.Half → Y) × (c.Half → Y), m p.1 * m p.2 *
    (if c.join p.1 p.2 = c.join x y then 1 else 0) = _
  rw [sum_eq_single (x, y)]
  · simp only [↓reduceIte, mul_one]
    ring
  · intro p _ hp
    have : c.join p.1 p.2 ≠ c.join x y := by
      intro he
      apply hp
      have h1 := (c.halves_eq_iff (c.join x y) p.1 p.2).mpr he.symm
      have h2 := (c.halves_eq_iff (c.join x y) x y).mpr rfl
      exact Prod.ext (h1.1.symm.trans h2.1) (h1.2.symm.trans h2.2)
    simp [this]
  · intro h
    exact absurd (mem_univ _) h

omit [∀ j, DecidableEq (X j)] in
/-- `∑_x ∏_j m_j(x_j) = ∏_j ∑ m_j`. -/
theorem sum_prod_half (c : ReflectionCut V) (m : ∀ j, (c.Half → X j) → ℝ) :
    ∑ x : c.Half → ∀ j, X j, ∏ j, m j (fun u => x u j) = ∏ j, ∑ y, m j y := by
  rw [Finset.prod_univ_sum]
  exact (Fintype.sum_equiv (Equiv.piComm fun (_ : c.Half) (j : J) => X j) _ _
    fun x => rfl)

/-- **`⊗_j J_c(m_j) = J_c(∏_j m_j)`.** -/
theorem tensorLaw_indepLaw (c : ReflectionCut V) (m : ∀ j, (c.Half → X j) → ℝ) :
    tensorLaw (fun j => indepLaw c (m j)) =
      indepLaw c (fun x : c.Half → ∀ j, X j => ∏ j, m j (fun u => x u j)) := by
  apply c.matrix_injective
  funext x y
  rw [matrix_indepLaw c]
  change cutKernel (tensorLaw fun j => indepLaw c (m j)) (fun z (v : c.Half) => z v.1)
    (fun z (v : c.Half) => z (c.flip v.1)) x y = _
  rw [tensorLaw_cutKernel (fun j => indepLaw c (m j)) (fun v : c.Half => v.1)
    (fun v : c.Half => c.flip v.1) x y]
  change ∏ j, c.matrix (indepLaw c (m j)) (fun w => x w j) (fun w => y w j) = _
  simp only [matrix_indepLaw]
  rw [prod_div_distrib, prod_mul_distrib, sum_prod_half]

end Indep

section Tensor

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]

/-- **The centred norm of a tensor product** (`lem:sector`(c); (P4) in `CentredNormLe` form): if
every factor `π_j` is symmetric at `c`, with half marginal `m_j ≥ 0` of positive mass, and
`‖T_j − 𝒥‖ ≤ κ_j` with `0 ≤ κ_j ≤ κ ≤ 1`, then `‖⊗_j T_j − 𝒥‖ ≤ κ` relative to `∏_j m_j`. -/
theorem centredNormLe_tensor (c : ReflectionCut V) (π : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (m : ∀ j, (c.Half → X j) → ℝ) (hm : ∀ j x, 0 ≤ m j x) (hmpos : ∀ j, 0 < ∑ x, m j x)
    (hsymm : ∀ j (F G : (c.Half → X j) → ℝ), c.form (π j) F G = c.form (π j) G F)
    (hplus : ∀ j (F : (c.Half → X j) → ℝ), c.form (π j) F 1 = ∑ x, m j x * F x)
    (κj : J → ℝ) (hκj0 : ∀ j, 0 ≤ κj j) (hcen : ∀ j, CentredNormLe c (π j) (m j) (κj j))
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hκ : ∀ j, κj j ≤ κ) :
    CentredNormLe c (tensorLaw π) (fun x : c.Half → ∀ j, X j => ∏ j, m j (fun u => x u j)) κ := by
  classical
  set I : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ := fun j => indepLaw c (m j) with hI
  set Aj : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ := fun j => c.diagonalLaw (m j) - indepLaw c (m j)
    with hA
  set Ej : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ := fun j => π j - indepLaw c (m j) with hE
  set M : (c.Half → ∀ j, X j) → ℝ := fun x => ∏ j, m j (fun u => x u j) with hM
  -- the factor brackets
  have hbrE : ∀ j, c.Bracket (κj j • Aj j) (Ej j) (κj j • Aj j) := by
    intro j
    obtain ⟨hm1, hp1⟩ := centred_pm c (hm j) (hmpos j) (hsymm j) (hplus j) (hcen j)
    exact ReflectionCut.bracket_of_add_sub_positive hp1 hm1
  have hbrI : ∀ j, c.Bracket (I j) (I j) (I j) := fun j =>
    (positive_indepLaw c (hm j)).bracket_self
  have hApos : ∀ j, c.Positive (Aj j) := fun j => positive_diagonal_sub_indep c (hm j)
  -- the subset terms
  let TA : (J → Bool) → ((V → ∀ j, X j) → ℝ) →ₗ[ℝ] ℝ := fun f =>
    tensorLaw fun j => if f j then Aj j else I j
  let TE : (J → Bool) → ((V → ∀ j, X j) → ℝ) →ₗ[ℝ] ℝ := fun f =>
    tensorLaw fun j => if f j then Ej j else I j
  have hterm : ∀ f : J → Bool, f ≠ (fun _ => false) → c.Bracket (κ • TA f) (TE f) (κ • TA f) := by
    intro f hf
    have hb := ReflectionCut.Bracket.tensor (c := c)
      (L := fun j => if f j then κj j • Aj j else I j) (K := fun j => if f j then Ej j else I j)
      (R := fun j => if f j then κj j • Aj j else I j) (fun j => by
        by_cases hj : f j
        · simp only [hj, ↓reduceIte]
          exact hbrE j
        · simp only [hj, Bool.false_eq_true, ↓reduceIte]
          exact hbrI j)
    have hsm : tensorLaw (fun j => if f j then κj j • Aj j else I j) =
        (∏ j, if f j then κj j else 1) • TA f := by
      rw [← tensorLaw_smul]
      congr 1
      funext j
      by_cases hj : f j
      · simp [hj]
      · simp [hj]
    rw [hsm] at hb
    apply bracket_mono hb
    -- `κ TA ⪰ (∏_S κ_j) TA`
    have hTA : c.Positive (TA f) := ReflectionCut.Positive.tensor fun j => by
      by_cases hj : f j
      · simp only [hj, ↓reduceIte]
        exact hApos j
      · simp only [hj, Bool.false_eq_true, ↓reduceIte]
        exact positive_indepLaw c (hm j)
    have hprod : (∏ j, if f j then κj j else 1) ≤ κ := by
      obtain ⟨j₀, hj₀⟩ : ∃ j, f j = true := by
        by_contra hn
        push Not at hn
        exact hf (funext fun j => by simpa using hn j)
      have h1 : ∀ j, 0 ≤ (if f j then κj j else 1) := fun j => by
        split_ifs
        · exact hκj0 j
        · exact zero_le_one
      have h2 : ∀ j, (if f j then κj j else 1) ≤ 1 := fun j => by
        split_ifs
        · exact (hκ j).trans hκ1
        · exact le_refl 1
      calc (∏ j, if f j then κj j else 1)
          = (if f j₀ then κj j₀ else 1) * ∏ j ∈ univ.erase j₀, (if f j then κj j else 1) :=
            (Finset.mul_prod_erase univ (fun j => if f j then κj j else 1) (mem_univ j₀)).symm
        _ ≤ (if f j₀ then κj j₀ else 1) * 1 := by
            apply mul_le_mul_of_nonneg_left _ (h1 j₀)
            exact Finset.prod_le_one₀ (fun j _ => h1 j) (fun j _ => h2 j)
        _ = κj j₀ := by rw [hj₀]; simp
        _ ≤ κ := hκ j₀
    have e : κ • TA f - (∏ j, if f j then κj j else 1) • TA f =
        (κ - ∏ j, if f j then κj j else 1) • TA f :=
      (sub_smul κ (∏ j, if f j then κj j else 1) (TA f)).symm
    rw [e]
    exact hTA.smul (sub_nonneg.mpr hprod)
  -- sum over the nonempty subsets
  set S := univ.filter fun f : J → Bool => f ≠ fun _ => false with hS
  have hsum := bracket_sum (c := c) S (fun f => κ • TA f) TE
    (fun f hf => hterm f (mem_filter.mp hf).2)
  have hsplit : ∀ (A' : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ),
      tensorLaw (fun j => I j + A' j) - tensorLaw I =
        ∑ f ∈ S, tensorLaw (fun j => if f j then A' j else I j) := by
    intro A'
    rw [tensorLaw_add_eq_sum, ← add_sum_erase univ _ (mem_univ (fun _ => false))]
    have h0 : tensorLaw (fun j => if (fun _ : J => false) j then A' j else I j) = tensorLaw I := by
      congr 1
    rw [h0, add_sub_cancel_left]
    congr 1
    ext f
    simp [hS, mem_erase, and_comm]
  have hD : tensorLaw (fun j => I j + Aj j) = c.diagonalLaw M := by
    rw [← EnvelopeInputs.tensorLaw_diagonalLaw]
    congr 1
    funext j
    simp [hI, hA]
  have hP : tensorLaw (fun j => I j + Ej j) = tensorLaw π := by
    congr 1
    funext j
    simp [hI, hE]
  have hJ : tensorLaw I = indepLaw c M := tensorLaw_indepLaw c m
  have eA := hsplit Aj
  have eE := hsplit Ej
  rw [hD, hJ] at eA
  rw [hP, hJ] at eE
  rw [← smul_sum, ← eA, ← eE] at hsum
  -- the bracket gives the centred norm
  have hMnn : ∀ x, 0 ≤ M x := fun x => prod_nonneg fun j _ => hm j _
  intro F G
  have hb := hsum.abs_form_le F G
  rw [form_sub_law, form_indepLaw] at hb
  rw [form_smul_law, form_smul_law, form_diagonal_sub_indep, form_diagonal_sub_indep] at hb
  have hvar : ∀ H : (c.Half → ∀ j, X j) → ℝ,
      ∑ x, M x * (H x * H x) - (∑ x, M x * H x) * (∑ y, M y * H y) / ∑ x, M x ≤
        ∑ x, M x * H x ^ 2 := by
    intro H
    have h0 : 0 ≤ (∑ x, M x * H x) * (∑ y, M y * H y) / ∑ x, M x :=
      div_nonneg (mul_self_nonneg _) (sum_nonneg fun x _ => hMnn x)
    have e : ∑ x, M x * H x ^ 2 = ∑ x, M x * (H x * H x) :=
      sum_congr rfl fun x _ => by ring
    linarith
  have hvnn : ∀ H : (c.Half → ∀ j, X j) → ℝ,
      0 ≤ ∑ x, M x * (H x * H x) - (∑ x, M x * H x) * (∑ y, M y * H y) / ∑ x, M x := by
    intro H
    have := (positive_diagonal_sub_indep c hMnn).nonneg H
    rwa [form_diagonal_sub_indep] at this
  have hs1 := (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hvar F) hκ0)).trans_eq
    (Real.sqrt_mul hκ0 _)
  have hs2 := (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hvar G) hκ0)).trans_eq
    (Real.sqrt_mul hκ0 _)
  have hk := Real.mul_self_sqrt hκ0
  have hsF := Real.sqrt_nonneg (∑ x, M x * F x ^ 2)
  have hsG := Real.sqrt_nonneg (∑ x, M x * G x ^ 2)
  calc |c.form (tensorLaw π) F G - (∑ x, M x * F x) * (∑ y, M y * G y) / ∑ x, M x|
      ≤ Real.sqrt (κ * (∑ x, M x * (F x * F x) - (∑ x, M x * F x) * (∑ y, M y * F y) /
          ∑ x, M x)) * Real.sqrt (κ * (∑ x, M x * (G x * G x) - (∑ x, M x * G x) *
          (∑ y, M y * G y) / ∑ x, M x)) := hb
    _ ≤ (Real.sqrt κ * Real.sqrt (∑ x, M x * F x ^ 2)) *
        (Real.sqrt κ * Real.sqrt (∑ x, M x * G x ^ 2)) :=
        mul_le_mul hs1 hs2 (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hsF)
    _ = κ * Real.sqrt (∑ x, M x * F x ^ 2) * Real.sqrt (∑ x, M x * G x ^ 2) := by
        rw [show Real.sqrt κ * Real.sqrt (∑ x, M x * F x ^ 2) *
            (Real.sqrt κ * Real.sqrt (∑ x, M x * G x ^ 2)) =
          (Real.sqrt κ * Real.sqrt κ) * Real.sqrt (∑ x, M x * F x ^ 2) *
            Real.sqrt (∑ x, M x * G x ^ 2) by ring, hk]

end Tensor

end Sarkozy.OpsVariance
