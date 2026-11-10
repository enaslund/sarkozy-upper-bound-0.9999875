module

public import Sarkozy.Extraction.CollisionCorollaries

/-!
# Signed collision bounds with incident weights

Combine the vanishing in `lem:signed-collisions` with `cor:incident-weights`.
The retained pin weight is the actual incident weight when the signed constraints
are compatible, and zero otherwise. This is the input to the balanced L20 bound.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.Extraction

open Sarkozy Sarkozy.Labellings

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- Incident weight after removing impossible signed pins. -/
noncomputable def collisionAlphaTilde (G : OrientedGraph U) (ς : U → U → ℤ)
    (x : U → F) (i j : U) : ℝ :=
  if collisionGamma G ς i j then collisionAlpha G ς x i j else 0

/-- Row charge of the surviving incident weights. -/
noncomputable def collisionRhoTilde (G : OrientedGraph U) (ς : U → U → ℤ)
    (q : ℝ) (x : U → F) (i : U) : ℝ :=
  (Real.sqrt q)⁻¹ ^ 2 * ∑ j, collisionAlphaTilde G ς x i j

theorem collisionAlphaTilde_nonneg (G : OrientedGraph U) (ς : U → U → ℤ)
    (x : U → F) (i j : U) : 0 ≤ collisionAlphaTilde G ς x i j := by
  unfold collisionAlphaTilde collisionAlpha
  split_ifs
  · exact mul_nonneg (collisionW_nonneg ς x i _) (by positivity)
  · exact le_rfl

theorem collisionRhoTilde_nonneg (G : OrientedGraph U) (ς : U → U → ℤ)
    (q : ℝ) (x : U → F) (i : U) : 0 ≤ collisionRhoTilde G ς q x i :=
  mul_nonneg (sq_nonneg _) (sum_nonneg fun j _ => collisionAlphaTilde_nonneg G ς x i j)

/-- Signed single-collision bound with the actual incident weights. -/
noncomputable def collisionSignedIncident1 (G : OrientedGraph U) (ς : U → U → ℤ)
    (ord : U → U → U → ℕ) (q : ℝ) (n : ℕ) (x : U → F) : ℝ :=
  (collisionLint G q n)⁻¹ * ∑ i, ∑ j, (Real.sqrt q)⁻¹ ^ 2 * collisionAlphaTilde G ς x i j *
    ∏ ℓ ∈ univ.erase i, (1 + coarseError (collisionT G ς ord i j ℓ) q (2 * n))

/-- Signed multiple-collision bound retaining the internal-edge price `2^{e(I)}`. -/
noncomputable def collisionSignedIncident2 (G : OrientedGraph U) (ς : U → U → ℤ)
    (π : ℕ → U → ℕ) (q : ℝ) (n : ℕ) (x : U → F) : ℝ :=
  (collisionLint G q n)⁻¹ * ∑ k ∈ Icc 2 (Fintype.card U), collisionUpsK G ς π q n k *
    ∑ I ∈ (univ : Finset U).powersetCard k,
      (2 : ℝ) ^ collisionEdgesIn G I * ∏ i ∈ I, collisionRhoTilde G ς q x i

theorem collision_rowSum_signed_incident_le (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hm1 : quadraticChar F (-1) = -1)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (ord : U → U → U → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (x : U → F) (hx : x ∈ injLabellings F G) :
    (graphLaw G hne).expect (collisionKernel1 ς x) ≤
      collisionSignedIncident1 G ς ord (Fintype.card F) n x := by
  have hxinj : Function.Injective x := fun a b h => by
    simp only [injLabellings, mem_filter, mem_univ, true_and] at hx
    exact hx.1 a (mem_univ _) b (mem_univ _) h
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  rw [coverRow_expect_graphLaw]
  have hN : (0 : ℝ) < (injLabellings F G).card := by exact_mod_cast card_pos.mpr hne
  rw [div_le_iff₀ hN]
  have hstr : ∀ i j, ∑ y ∈ injLabellings F G,
      (if y i = x j ∧ ∀ ℓ, ℓ ≠ i → y ℓ ∉ univ.image x then collisionKernel ς x y else 0) ≤
        ((Fintype.card F : ℝ) * collisionLint G (Fintype.card F) n)⁻¹ *
          (collisionAlphaTilde G ς x i j * ∏ ℓ ∈ univ.erase i,
            (1 + coarseError (collisionT G ς ord i j ℓ) (Fintype.card F) (2 * n))) *
          (injLabellings F G).card := by
    intro i j
    by_cases hγ : collisionGamma G ς i j
    · have h := collision_stratum_ratio_incident hW G ς hς ord hord x hxinj hn hS1 i j
      unfold collisionAlphaTilde
      rw [ite_eq_left hγ]
      exact h
    · have h0 : ∑ y ∈ injLabellings F G,
          (if y i = x j ∧ ∀ ℓ, ℓ ≠ i → y ℓ ∉ univ.image x then collisionKernel ς x y else 0) =
            0 := sum_eq_zero fun y hy => by
        split_ifs with hc
        · exact collision_signed_vanish G ς hς hm1 hx hy hc.1 hγ
        · rfl
      rw [h0]
      unfold collisionAlphaTilde
      rw [ite_eq_right hγ]
      simp
  calc ∑ y ∈ injLabellings F G, collisionKernel1 ς x y
      ≤ ∑ y ∈ injLabellings F G, ∑ i, ∑ j,
          (if y i = x j ∧ ∀ ℓ, ℓ ≠ i → y ℓ ∉ univ.image x then collisionKernel ς x y else 0) := by
        refine sum_le_sum fun y hy => collisionKernel1_le_sum ς x y fun a b h => ?_
        simp only [injLabellings, mem_filter, mem_univ, true_and] at hy
        exact hy.1 a (mem_univ _) b (mem_univ _) h
    _ = ∑ i, ∑ j, ∑ y ∈ injLabellings F G,
          (if y i = x j ∧ ∀ ℓ, ℓ ≠ i → y ℓ ∉ univ.image x then collisionKernel ς x y else 0) := by
        rw [sum_comm]
        exact sum_congr rfl fun i _ => sum_comm
    _ ≤ ∑ i, ∑ j, ((Fintype.card F : ℝ) * collisionLint G (Fintype.card F) n)⁻¹ *
          (collisionAlphaTilde G ς x i j * ∏ ℓ ∈ univ.erase i,
            (1 + coarseError (collisionT G ς ord i j ℓ) (Fintype.card F) (2 * n))) *
          (injLabellings F G).card :=
        sum_le_sum fun i _ => sum_le_sum fun j _ => hstr i j
    _ = collisionSignedIncident1 G ς ord (Fintype.card F) n x * (injLabellings F G).card := by
        unfold collisionSignedIncident1
        rw [coverRow_r_sq hq0, mul_sum, sum_mul]
        refine sum_congr rfl fun i _ => ?_
        rw [mul_sum, sum_mul]
        refine sum_congr rfl fun j _ => ?_
        rw [mul_inv]
        ring

theorem collision_sum_maps_alphaTilde (G : OrientedGraph U) (ς : U → U → ℤ)
    (x : U → F) (I : Finset U) :
    ∑ ψ : (I → U), ∏ l ∈ I, collisionAlphaTilde G ς x l (collisionExt I ψ l) =
      ∏ l ∈ I, ∑ j, collisionAlphaTilde G ς x l j := by
  rw [← prod_coe_sort I (fun l => ∑ j, collisionAlphaTilde G ς x l j), Fintype.prod_sum]
  refine sum_congr rfl fun ψ _ => ?_
  rw [← prod_coe_sort I]
  refine prod_congr rfl fun l _ => ?_
  rw [collisionExt_coe]

theorem collision_prod_rhoTilde (G : OrientedGraph U) (ς : U → U → ℤ) {q : ℝ} (hq : 0 < q)
    (x : U → F) (I : Finset U) :
    q⁻¹ ^ I.card * ∏ l ∈ I, ∑ j, collisionAlphaTilde G ς x l j =
      ∏ l ∈ I, collisionRhoTilde G ς q x l := by
  unfold collisionRhoTilde
  rw [coverRow_r_sq hq, prod_mul_distrib, prod_const]

theorem collision_rowSum2_signed_incident_le (hW : WeilBound F) (G : OrientedGraph U)
    (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1)
    (hm1 : quadraticChar F (-1) = -1) (hne : (injLabellings F G).Nonempty)
    {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (π : ℕ → U → ℕ)
    (hπ : ∀ k, Function.Injective (π k)) (x : U → F) (hx : x ∈ injLabellings F G) :
    (graphLaw G hne).expect (collisionKernel2 ς x) ≤
      collisionSignedIncident2 G ς π (Fintype.card F) n x := by
  have hxinj : Function.Injective x := fun a b h => by
    simp only [injLabellings, mem_filter, mem_univ, true_and] at hx
    exact hx.1 a (mem_univ _) b (mem_univ _) h
  set q : ℝ := (Fintype.card F : ℝ) with hq
  have hq0 : (0 : ℝ) < q := by
    rw [hq]
    exact_mod_cast Fintype.card_pos
  set N : ℝ := ((injLabellings F G).card : ℝ) with hNdef
  rw [coverRow_expect_graphLaw]
  have hN : (0 : ℝ) < N := by
    rw [hNdef]
    exact_mod_cast card_pos.mpr hne
  rw [div_le_iff₀ hN]
  set c : ℕ → Finset U → ℝ := fun k I => (collisionLint G q n)⁻¹ * collisionUpsK G ς π q n k *
    (q⁻¹ ^ k * (2 : ℝ) ^ collisionEdgesIn G I) with hc
  have hstr : ∀ k ∈ Icc 2 (Fintype.card U), ∀ I ∈ (univ : Finset U).powersetCard k,
      ∀ ψ : (I → U), ∑ y ∈ injLabellings F G,
        (if (∀ l ∈ I, y l = x (collisionExt I ψ l)) ∧ (∀ v, v ∉ I → y v ∉ univ.image x) then
          collisionKernel ς x y else 0) ≤
        c k I * (∏ l ∈ I, collisionAlphaTilde G ς x l (collisionExt I ψ l)) * N := by
    intro k _ I hI ψ
    have hIk : I.card = k := (mem_powersetCard.mp hI).2
    by_cases hall : ∀ l ∈ I, collisionGamma G ς l (collisionExt I ψ l)
    · have hprod : ∏ l ∈ I, collisionAlphaTilde G ς x l (collisionExt I ψ l) =
          ∏ l ∈ I, collisionAlpha G ς x l (collisionExt I ψ l) :=
        prod_congr rfl fun l hl => by
          unfold collisionAlphaTilde
          rw [ite_eq_left (hall l hl)]
      have h := collision_stratumI_ratio_incident hW G ς hς π hπ x hxinj hn hS1 I (collisionExt I ψ)
      rw [hIk] at h
      rw [hprod]
      refine h.trans (le_of_eq ?_)
      simp only [hc]
      ring
    · push Not at hall
      obtain ⟨l, hl, hγl⟩ := hall
      have h0 : ∑ y ∈ injLabellings F G,
          (if (∀ l ∈ I, y l = x (collisionExt I ψ l)) ∧ (∀ v, v ∉ I → y v ∉ univ.image x) then
            collisionKernel ς x y else 0) = 0 := sum_eq_zero fun y hy => by
        split_ifs with hcond
        · exact collision_signed_vanish G ς hς hm1 hx hy (hcond.1 l hl) hγl
        · rfl
      have hp0 : ∏ l ∈ I, collisionAlphaTilde G ς x l (collisionExt I ψ l) = 0 :=
        prod_eq_zero hl (by unfold collisionAlphaTilde; rw [ite_eq_right hγl])
      rw [h0, hp0]
      simp
  calc ∑ y ∈ injLabellings F G, collisionKernel2 ς x y
      ≤ ∑ y ∈ injLabellings F G, ∑ k ∈ Icc 2 (Fintype.card U),
          ∑ I ∈ (univ : Finset U).powersetCard k, ∑ ψ : (I → U),
            (if (∀ l ∈ I, y l = x (collisionExt I ψ l)) ∧ (∀ v, v ∉ I → y v ∉ univ.image x) then
              collisionKernel ς x y else 0) := by
        refine sum_le_sum fun y hy => collisionKernel2_le_sum ς x y fun a b h => ?_
        simp only [injLabellings, mem_filter, mem_univ, true_and] at hy
        exact hy.1 a (mem_univ _) b (mem_univ _) h
    _ = ∑ k ∈ Icc 2 (Fintype.card U), ∑ I ∈ (univ : Finset U).powersetCard k, ∑ ψ : (I → U),
          ∑ y ∈ injLabellings F G,
            (if (∀ l ∈ I, y l = x (collisionExt I ψ l)) ∧ (∀ v, v ∉ I → y v ∉ univ.image x) then
              collisionKernel ς x y else 0) := by
        rw [sum_comm]
        refine sum_congr rfl fun k _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun I _ => ?_
        rw [sum_comm]
    _ ≤ ∑ k ∈ Icc 2 (Fintype.card U), ∑ I ∈ (univ : Finset U).powersetCard k, ∑ ψ : (I → U),
          c k I * (∏ l ∈ I, collisionAlphaTilde G ς x l (collisionExt I ψ l)) * N :=
        sum_le_sum fun k hk => sum_le_sum fun I hI => sum_le_sum fun ψ _ => hstr k hk I hI ψ
    _ = ∑ k ∈ Icc 2 (Fintype.card U), ∑ I ∈ (univ : Finset U).powersetCard k,
          (collisionLint G q n)⁻¹ * collisionUpsK G ς π q n k * (2 : ℝ) ^ collisionEdgesIn G I *
            (∏ i ∈ I, collisionRhoTilde G ς q x i) * N := by
        refine sum_congr rfl fun k _ => sum_congr rfl fun I hI => ?_
        have hIk : I.card = k := (mem_powersetCard.mp hI).2
        rw [← sum_mul, ← mul_sum, collision_sum_maps_alphaTilde,
          ← collision_prod_rhoTilde G ς hq0 x I, hIk]
        simp only [hc]
        ring
    _ = collisionSignedIncident2 G ς π q n x * N := by
        unfold collisionSignedIncident2
        rw [mul_sum, sum_mul]
        refine sum_congr rfl fun k _ => ?_
        rw [mul_sum, mul_sum, sum_mul]
        refine sum_congr rfl fun I _ => ?_
        ring

end Sarkozy.Extraction
