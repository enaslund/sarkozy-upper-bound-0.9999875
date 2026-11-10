module

public import Sarkozy.OpsFeature.Compose
public import Sarkozy.Mixing.SectorLemma

@[expose] public section

/-!
# The tensor of the stars on a sector (`lem:oct24:mask-schur`(c), the sector structure)

`paper/sections/23_envelopes.tex`, `lem:oct24:mask-schur`(a), (c) and the star form (N1), (N3):
on a choice `s` of one singleton sector at every block, the tensor of the leading stars acts on
`Feat n k × Z_s` as the product of the per-block star matrices (`starTensor`): a fold star `StF`
on `Fin 4` labels (centre `0`, arms `1, 2, 3`), a matching star `StE` on `Fin 2` labels. From the
per-block facts of the paper:
* a star joins its centre to its arms only (`StF ((a,·),(a',·)) = 0` unless exactly one of `a, a'`
  is the centre);
* the block `(a, a')` has norm at most `mag a · mag a'` (`1` at the centre, the arm magnitudes
  `1, t, 1 - t` at the fold arms, `1` at the matching arm);
* the stars are antisymmetric,

the hypotheses `hsec`, `hnorm`, `hTs` of `hdom_of_table` follow (`starTensor_sec`,
`starTensor_norm`, `starTensor_hermitian`); the norm of a tensor product of blocks is the product
of the norms (`prodOp_norm_le`, Mixing's `general_exact_support_decay` with spectators only).
**`hdom_of_table_stars`** is then `hdom` for a checked diagonal envelope from per-block data only.
-/

open Finset Matrix
open scoped BigOperators Kronecker

namespace Sarkozy.OpsFeature

open Sarkozy.Mixing Sarkozy.IndexSupport Sarkozy.EnvelopeSteps Sarkozy.Envelopes

/-! ## The norm of a tensor product of matrices -/

section TensorNorm

variable {K : Type*} [Fintype K] [DecidableEq K] {Z : K → Type*} [∀ j, Fintype (Z j)]
  [∀ j, DecidableEq (Z j)] [∀ j, Nonempty (Z j)]

/-- **`‖⊗_j N_j‖ ≤ ∏_j δ_j`** for the Euclidean norms, from `‖N_j‖ ≤ δ_j`. -/
theorem prodOp_norm_le (N : ∀ j, Matrix (Z j) (Z j) ℝ) (δ : K → ℝ)
    (hN : ∀ j (y : Z j → ℝ), ∑ z, (N j *ᵥ y) z ^ 2 ≤ δ j ^ 2 * ∑ z, y z ^ 2)
    (y : (∀ j, Z j) → ℝ) :
    ∑ z, (prodOp N *ᵥ y) z ^ 2 ≤ (∏ j, δ j) ^ 2 * ∑ z, y z ^ 2 := by
  set u : ∀ j, Z j → ℝ := fun j _ => 1 / (Fintype.card (Z j) : ℝ) with hu
  have hc : ∀ j, (0 : ℝ) < Fintype.card (Z j) := fun j => by
    exact_mod_cast Fintype.card_pos
  have hu0 : ∀ j z, 0 ≤ u j z := fun j z => by have := hc j; simp only [hu]; positivity
  have hu1 : ∀ j, ∑ z, u j z = 1 := fun j => by
    have := (hc j).ne'
    simp only [hu, sum_const, card_univ, nsmul_eq_mul]; field_simp
  have h := (general_exact_support_decay u u N (fun _ => true) hu1 hu0
    (fun j hj => by simp at hj) δ (fun j hj => by simp at hj)
    (fun j _ f => by
      have hNj := hN j f
      have e1 : ∑ b, u j b * (N j *ᵥ f) b ^ 2 = 1 / (Fintype.card (Z j) : ℝ) *
          ∑ b, (N j *ᵥ f) b ^ 2 := by simp only [hu, mul_sum]
      have e2 : ∑ a, u j a * f a ^ 2 = 1 / (Fintype.card (Z j) : ℝ) * ∑ a, f a ^ 2 := by
        simp only [hu, mul_sum]
      rw [e1, e2]
      have hcj := hc j
      calc 1 / (Fintype.card (Z j) : ℝ) * ∑ b, (N j *ᵥ f) b ^ 2
          ≤ 1 / (Fintype.card (Z j) : ℝ) * (δ j ^ 2 * ∑ z, f z ^ 2) :=
            mul_le_mul_of_nonneg_left hNj (by positivity)
        _ = _ := by ring) y).2
  -- only the trivial sector survives, and the weights are constant
  have hP : ∀ l : K → Bool, wSectorProj u (fun _ => true) l *ᵥ y =
      if l = (fun _ => false) then y else 0 := by
    intro l
    split_ifs with hl
    · subst hl
      have : wSectorProj u (fun _ => true) (fun _ => false) = 1 := by
        simp only [wSectorProj, wProj, ite_true, Bool.false_eq_true, ite_false]
        exact piKron_one
      rw [this, one_mulVec]
    · obtain ⟨j, hj⟩ : ∃ j, l j = true := by
        by_contra hne
        apply hl
        funext j
        cases h : l j
        · rfl
        · exact absurd ⟨j, h⟩ hne
      have : wSectorProj u (fun _ => true) l = 0 :=
        piKron_eq_zero j (by simp [wProj, hj])
      rw [this, zero_mulVec]
  simp only [hP, ite_true] at h
  rw [Fintype.sum_eq_single (fun _ => false) (fun l hl => by simp [hl])] at h
  simp only [ite_true] at h
  have hw : ∀ a, prodW u a = ∏ j, 1 / (Fintype.card (Z j) : ℝ) := fun a => rfl
  simp only [hw, ← mul_sum] at h
  have hW : 0 < ∏ j, 1 / (Fintype.card (Z j) : ℝ) := prod_pos fun j _ => by
    have := hc j; positivity
  rw [← prod_pow]
  nlinarith [h, hW]

end TensorNorm

/-! ## The tensor of the stars -/

section StarTensor

variable {n k : ℕ} {Sb : Fin n ⊕ Fin k → Type*} [∀ b, Fintype (Sb b)] {Zb : ∀ b, Sb b → Type*}
  [∀ b p, Fintype (Zb b p)] [∀ b p, DecidableEq (Zb b p)]

/-- The magnitude of a fold label: `1` at the centre, `1, t, 1 - t` at the arms `1, 2, 3`. -/
noncomputable def magF (a : Fin 4) : ℝ := if a = 0 then 1 else (armMag (a : ℕ) : ℝ)

theorem featAlpha_eq (v : Feat n k) : (featAlpha v : ℝ) = ∏ i, magF (v.1 i) := by
  unfold featAlpha fArms
  push_cast
  rw [prod_filter]
  refine prod_congr rfl fun i _ => ?_
  unfold magF
  by_cases h : v.1 i = 0 <;> simp [h]

/-- **The tensor of the stars on a sector choice `s`**: the product of the fold star blocks and the
matching star blocks. -/
def starTensor
    (StF : ∀ (i : Fin n) (p : Sb (Sum.inl i)),
      Matrix (Fin 4 × Zb (Sum.inl i) p) (Fin 4 × Zb (Sum.inl i) p) ℝ)
    (StE : ∀ (j : Fin k) (p : Sb (Sum.inr j)),
      Matrix (Fin 2 × Zb (Sum.inr j) p) (Fin 2 × Zb (Sum.inr j) p) ℝ) (s : ∀ b, Sb b) :
    Matrix (Feat n k × (∀ b, Zb b (s b))) (Feat n k × (∀ b, Zb b (s b))) ℝ :=
  fun wz vz =>
    (∏ i : Fin n, StF i (s (Sum.inl i)) (wz.1.1 i, wz.2 (Sum.inl i))
      (vz.1.1 i, vz.2 (Sum.inl i))) *
      ∏ j : Fin k, StE j (s (Sum.inr j)) (wz.1.2 j, wz.2 (Sum.inr j))
        (vz.1.2 j, vz.2 (Sum.inr j))

variable
    (StF : ∀ (i : Fin n) (p : Sb (Sum.inl i)),
      Matrix (Fin 4 × Zb (Sum.inl i) p) (Fin 4 × Zb (Sum.inl i) p) ℝ)
    (StE : ∀ (j : Fin k) (p : Sb (Sum.inr j)),
      Matrix (Fin 2 × Zb (Sum.inr j) p) (Fin 2 × Zb (Sum.inr j) p) ℝ)

omit [∀ b, Fintype (Sb b)] [∀ b p, Fintype (Zb b p)] [∀ b p, DecidableEq (Zb b p)] in
/-- **The sector structure** (`hsec` of `hdom_of_table`): a star joins its centre to its arms
only, so the tensor maps the sector of a mask to the sector of the complementary mask. -/
theorem starTensor_sec
    (hF : ∀ i p (a a' : Fin 4) x x', (a = 0 ↔ a' = 0) → StF i p (a, x) (a', x') = 0)
    (hE : ∀ j p (a a' : Fin 2) x x', (a = 0 ↔ a' = 0) → StE j p (a, x) (a', x') = 0)
    (s : ∀ b, Sb b) (v w : Feat n k) (z z' : ∀ b, Zb b (s b))
    (h : featMask w ≠ maskCompl (featMask v)) : starTensor StF StE s (w, z) (v, z') = 0 := by
  by_contra hne
  apply h
  unfold starTensor at hne
  have hF' : ∀ i, ¬(w.1 i = 0 ↔ v.1 i = 0) := fun i hi =>
    hne (by rw [prod_eq_zero (mem_univ i) (hF i _ _ _ _ _ hi), zero_mul])
  have hE' : ∀ j, ¬(w.2 j = 0 ↔ v.2 j = 0) := fun j hj =>
    hne (by rw [prod_eq_zero (mem_univ j) (hE j _ _ _ _ _ hj), mul_zero])
  unfold featMask maskCompl
  congr 1
  · ext i
    simp only [fArms, mem_filter, mem_univ, true_and, mem_compl, not_not]
    have := hF' i
    tauto
  · ext j
    simp only [eArms, mem_filter, mem_univ, true_and, mem_compl, not_not]
    have := hE' j
    tauto

omit [∀ b, Fintype (Sb b)] in
/-- **The block norms** (`hnorm` of `hdom_of_table`): the block `(w, v)` of the tensor is the
tensor product of the star blocks, of norm at most `∏ mag · mag = α(v) α(w)`. -/
theorem starTensor_norm [∀ b p, Nonempty (Zb b p)]
    (hFn : ∀ i p (a a' : Fin 4) (y : Zb (Sum.inl i) p → ℝ),
      ∑ x, (∑ x', StF i p (a, x) (a', x') * y x') ^ 2 ≤
        (magF a * magF a') ^ 2 * ∑ x, y x ^ 2)
    (hEn : ∀ j p (a a' : Fin 2) (y : Zb (Sum.inr j) p → ℝ),
      ∑ x, (∑ x', StE j p (a, x) (a', x') * y x') ^ 2 ≤ 1 ^ 2 * ∑ x, y x ^ 2)
    (s : ∀ b, Sb b) (v w : Feat n k) (y : (∀ b, Zb b (s b)) → ℝ) :
    ∑ z, (∑ z', starTensor StF StE s (w, z) (v, z') * y z') ^ 2 ≤
      ((featAlpha v : ℝ) * featAlpha w) ^ 2 * ∑ z, y z ^ 2 := by
  let N : ∀ b, Matrix (Zb b (s b)) (Zb b (s b)) ℝ := fun b =>
    match b with
    | Sum.inl i => fun x x' => StF i (s (Sum.inl i)) (w.1 i, x) (v.1 i, x')
    | Sum.inr j => fun x x' => StE j (s (Sum.inr j)) (w.2 j, x) (v.2 j, x')
  let δ : Fin n ⊕ Fin k → ℝ := fun b =>
    match b with
    | Sum.inl i => magF (w.1 i) * magF (v.1 i)
    | Sum.inr _ => 1
  have hT : ∀ z z', starTensor StF StE s (w, z) (v, z') = prodOp N z z' := by
    intro z z'
    simp only [starTensor, prodOp, Fintype.prod_sum_type]
    rfl
  have hN : ∀ b (y : Zb b (s b) → ℝ), ∑ z, (N b *ᵥ y) z ^ 2 ≤ δ b ^ 2 * ∑ z, y z ^ 2 := by
    intro b y
    cases b with
    | inl i => exact hFn i (s (Sum.inl i)) (w.1 i) (v.1 i) y
    | inr j => exact hEn j (s (Sum.inr j)) (w.2 j) (v.2 j) y
  have h := prodOp_norm_le N δ hN y
  have hδ : ∏ b, δ b = (featAlpha v : ℝ) * featAlpha w := by
    rw [Fintype.prod_sum_type, featAlpha_eq, featAlpha_eq]
    simp only [δ, prod_const_one, mul_one, prod_mul_distrib]
    ring
  rw [hδ] at h
  refine le_of_eq_of_le ?_ h
  refine sum_congr rfl fun z _ => ?_
  congr 1
  simp only [mulVec, dotProduct, hT]

omit [∀ b, Fintype (Sb b)] [∀ b p, Fintype (Zb b p)] [∀ b p, DecidableEq (Zb b p)] in
/-- **The tensor of an even number of antisymmetric stars is symmetric** (`hTs`). -/
theorem starTensor_hermitian (hnk : Even (n + k))
    (hFa : ∀ i p x y, StF i p x y = -StF i p y x) (hEa : ∀ j p x y, StE j p x y = -StE j p y x)
    (s : ∀ b, Sb b) : (starTensor StF StE s).IsHermitian := by
  ext wz vz
  simp only [conjTranspose_apply, star_trivial, starTensor]
  have h1 : ∀ i, StF i (s (Sum.inl i)) (vz.1.1 i, vz.2 (Sum.inl i)) (wz.1.1 i, wz.2 (Sum.inl i))
      = -1 * StF i (s (Sum.inl i)) (wz.1.1 i, wz.2 (Sum.inl i)) (vz.1.1 i, vz.2 (Sum.inl i)) :=
    fun i => by rw [hFa]; ring
  have h2 : ∀ j, StE j (s (Sum.inr j)) (vz.1.2 j, vz.2 (Sum.inr j)) (wz.1.2 j, wz.2 (Sum.inr j))
      = -1 * StE j (s (Sum.inr j)) (wz.1.2 j, wz.2 (Sum.inr j)) (vz.1.2 j, vz.2 (Sum.inr j)) :=
    fun j => by rw [hEa]; ring
  set A := ∏ i, StF i (s (Sum.inl i)) (wz.1.1 i, wz.2 (Sum.inl i)) (vz.1.1 i, vz.2 (Sum.inl i))
    with hA
  set B := ∏ j, StE j (s (Sum.inr j)) (wz.1.2 j, wz.2 (Sum.inr j)) (vz.1.2 j, vz.2 (Sum.inr j))
    with hB
  have hF' : ∏ i, StF i (s (Sum.inl i)) (vz.1.1 i, vz.2 (Sum.inl i)) (wz.1.1 i, wz.2 (Sum.inl i))
      = (-1) ^ n * A := by
    rw [prod_congr rfl (fun i _ => h1 i), prod_mul_distrib, prod_const, card_univ,
      Fintype.card_fin]
  have hE' : ∏ j, StE j (s (Sum.inr j)) (vz.1.2 j, vz.2 (Sum.inr j)) (wz.1.2 j, wz.2 (Sum.inr j))
      = (-1) ^ k * B := by
    rw [prod_congr rfl (fun j _ => h2 j), prod_mul_distrib, prod_const, card_univ,
      Fintype.card_fin]
  have hpm : ((-1 : ℝ) ^ n) * (-1) ^ k = 1 := by rw [← pow_add]; exact hnk.neg_one_pow
  rw [hF', hE']
  linear_combination A * B * hpm

/-- **`hdom` for a checked diagonal envelope from per-block data only** (`lem:oct24:mask-schur`(a),
(c), `cert:envelopes`(b)): the input `hdom` of `EnvelopeSteps.DegreeOps`, given at every block and
sector the star matrices (centre–arm structure `hF`, `hE`; block norms `hFn`, `hEn`;
antisymmetry `hFa`, `hEa`), the sector maps `Ξb` and the unit tables `CU` with `hUY`, the
kernels `hL`, `hLop`, and `0 ≤ c_s ≤ 1`. -/
theorem hdom_of_table_stars {O : Fin n ⊕ Fin k → Type*} [∀ b, Fintype (O b)]
    [∀ b, DecidableEq (O b)] [∀ b p, Nonempty (Zb b p)] {Tb : EnvTable}
    (hT : tablePos Tb n k = true) (hC : maskCheck Tb n k = true) (hnk : Even (n + k))
    (Ξb : ∀ b (p : Sb b), Matrix (O b) (featLab n k b × Zb b p) ℝ)
    (CU : ∀ b, Matrix (featLab n k b × O b) (featLab n k b × O b) ℝ)
    (hUY : ∀ b, (maskT (fun b => (id : featLab n k b → featLab n k b)) CU b -
      maskT (fun b => (id : featLab n k b → featLab n k b)) (gramT Ξb) b).PosSemidef)
    (StF : ∀ (i : Fin n) (p : Sb (Sum.inl i)),
      Matrix (Fin 4 × Zb (Sum.inl i) p) (Fin 4 × Zb (Sum.inl i) p) ℝ)
    (StE : ∀ (j : Fin k) (p : Sb (Sum.inr j)),
      Matrix (Fin 2 × Zb (Sum.inr j) p) (Fin 2 × Zb (Sum.inr j) p) ℝ)
    (hF : ∀ i p (a a' : Fin 4) x x', (a = 0 ↔ a' = 0) → StF i p (a, x) (a', x') = 0)
    (hE : ∀ j p (a a' : Fin 2) x x', (a = 0 ↔ a' = 0) → StE j p (a, x) (a', x') = 0)
    (hFn : ∀ i p (a a' : Fin 4) (y : Zb (Sum.inl i) p → ℝ),
      ∑ x, (∑ x', StF i p (a, x) (a', x') * y x') ^ 2 ≤ (magF a * magF a') ^ 2 * ∑ x, y x ^ 2)
    (hEn : ∀ j p (a a' : Fin 2) (y : Zb (Sum.inr j) p → ℝ),
      ∑ x, (∑ x', StE j p (a, x) (a', x') * y x') ^ 2 ≤ 1 ^ 2 * ∑ x, y x ^ 2)
    (hFa : ∀ i p x y, StF i p x y = -StF i p y x) (hEa : ∀ j p x y, StE j p x y = -StE j p y x)
    (cs : (∀ b, Sb b) → ℝ) (hc0 : ∀ s, 0 ≤ cs s) (hc1 : ∀ s, cs s ≤ 1)
    {m : (∀ b, O b) → ℝ} {Lead Lop : ((∀ b, O b) → ℝ) →ₗ[ℝ] ((∀ b, O b) → ℝ)}
    (hL : ∀ x y, kern m Lead x y =
      (∑ s, cs s • (xiFeat Ξb s * starTensor StF StE s * (xiFeat Ξb s)ᴴ)) x y)
    (hLop : ∀ x y, kern m Lop x y =
      liftMap CU (diagonal ((fun v => (featWeight Tb v : ℝ)) ∘ (featEquiv n k).symm)) x y) :
    OpLE m Lead Lop ∧ OpLE m (-Lead) Lop :=
  hdom_of_table_blocks hT hC Ξb CU hUY (starTensor StF StE) cs hc0 hc1
    (starTensor_hermitian StF StE hnk hFa hEa)
    (fun s v w z z' h => starTensor_sec StF StE hF hE s v w z z' h)
    (fun s v w y => starTensor_norm StF StE hFn hEn s v w y) hL hLop

end StarTensor

end Sarkozy.OpsFeature
