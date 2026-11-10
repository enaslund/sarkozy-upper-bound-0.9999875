module

public import Sarkozy.ExtractionK.SoftCore
public import Sarkozy.Extraction.CollisionBound

@[expose] public section

/-!
# Soft cross factors for the coincidences (`cor:soft-kernels`(b), `lem:oct24-collision`(a))

`paper/sections/16_extraction.tex`, `cor:soft-kernels`(b): the soft collision operator satisfies
the bound of `lem:oct24-collision`; here for the part with exactly one common label
(`lem:oct24-collision`(a), `collision_opBound` of `Extraction/CollisionBound.lean`).

* `skCollKer1`: `1{|x(U⁺) ∩ x'(U⁺)| = 1} ∏_{e ∈ E_×}(1 + D_e χ_e(x, x'))`;
  `sk_collKer1_expand`: a convex combination of the Boolean kernels `collisionKernel1` of the signs
  restricted to `T ⊆ E_×` (flipped to `-ς` where `D_e < 0`, using `χ(-1) = -1` there).
* `sk_collisionD1_mono`: `D_1` is nondecreasing in the support of the signs (`a_{ij}`, `t^{ij}_ℓ`
  are); `sk_coll_rowSum_le`: the row sums of the soft kernel are at most `D_1`;
  `sk_collKer1_swap`: the column sums are row sums of the transposed soft kernel (coefficients
  `D_{(k,j)}` at `(j,k)`, signs `ςᵀ`; its `D_1` is that of `ς` for antisymmetric signs).
* **`sk_soft_collision_opBound`**: `‖T^D_coll,1‖ ≤ D_1` for `|D_e| ≤ 1`, provided `χ(-1) = -1` if
  some `D_e < 0` (Schur's test with row and column sums; the soft kernel is not symmetric).

Not covered: the parts (b)–(e) of `lem:oct24-collision` for soft kernels (`T_coll` with at least
two common labels and the derived forms), and negative coefficients when `χ(-1) = 1`.
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

section SkColl

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]


theorem sk_pin_omega_factor_nonneg' (D : ℝ) (hD : |D| ≤ 1) (a : F) :
    0 ≤ 1 + D * (quadraticChar F a : ℝ) := by
  have h1 : |(quadraticChar F a : ℝ)| ≤ 1 := by
    rcases eq_or_ne a 0 with h | h
    · rw [h]; simp
    · rcases quadraticChar_dichotomy h with h' | h' <;> rw [h'] <;> norm_num
  have : |D * (quadraticChar F a : ℝ)| ≤ 1 := by
    rw [abs_mul]
    calc |D| * |(quadraticChar F a : ℝ)| ≤ 1 * 1 :=
          mul_le_mul hD h1 (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  linarith [neg_abs_le (D * (quadraticChar F a : ℝ))]

/-- The soft collision kernel with exactly one common label:
`1{|x(U⁺) ∩ x'(U⁺)| = 1} ∏_{e ∈ E_×} (1 + D_e χ_e(x, x'))`. -/
noncomputable def skCollKer1 (ς : U → U → ℤ) (D : U × U → ℝ) (x x' : U → F) : ℝ :=
  if collisionCommon x x' = 1 then
    ∏ e ∈ collisionCross ς, (1 + D e * (quadraticChar F ((ς e.1 e.2 : F) * (x' e.2 - x e.1)) : ℝ))
  else 0

/-- The signs restricted to `T` and flipped at the pairs with a negative coefficient. -/
noncomputable def skCollSgn (ς : U → U → ℤ) (D : U × U → ℝ) (T : Finset (U × U)) :
    U → U → ℤ :=
  fun j k => if (j, k) ∈ T then (if D (j, k) < 0 then -ς j k else ς j k) else 0

theorem sk_collCross_sgn (ς : U → U → ℤ) (D : U × U → ℝ) {T : Finset (U × U)}
    (hT : T ⊆ collisionCross ς) : collisionCross (skCollSgn ς D T) = T := by
  ext e
  unfold collisionCross skCollSgn
  simp only [mem_filter, mem_univ, true_and, Prod.mk.eta]
  constructor
  · intro h
    by_contra he
    simp [he] at h
  · intro he
    have hς : ς e.1 e.2 ≠ 0 := by
      have := hT he
      unfold collisionCross at this
      simpa using this
    simp only [he, ↓reduceIte]
    split_ifs <;> simpa using hς

omit [Fintype U] in
theorem sk_collSgn_values {ς : U → U → ℤ} (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1)
    (D : U × U → ℝ) (T : Finset (U × U)) (j k : U) :
    skCollSgn ς D T j k = 0 ∨ skCollSgn ς D T j k = 1 ∨ skCollSgn ς D T j k = -1 := by
  unfold skCollSgn
  split_ifs
  · rcases hς j k with h | h | h <;> simp [h]
  · exact hς j k
  · exact Or.inl rfl

theorem sk_rowsN_collSgn_subset (ς : U → U → ℤ) (D : U × U → ℝ) (T : Finset (U × U)) (i : U) :
    rowsN (skCollSgn ς D T) i ⊆ rowsN ς i := by
  intro j hj
  unfold rowsN skCollSgn at *
  simp only [mem_filter, mem_univ, true_and] at hj ⊢
  intro h0
  apply hj
  split_ifs <;> simp [h0]

omit [Fintype U] in
theorem sk_coll_flip_identity (ς : U → U → ℤ) (D : U × U → ℝ) {T : Finset (U × U)}
    {e : U × U} (he : e ∈ T) (hneg : D e < 0 → quadraticChar F (-1) = -1) (x x' : U → F) :
    1 + D e * (quadraticChar F ((ς e.1 e.2 : F) * (x' e.2 - x e.1)) : ℝ) =
      |D e| * (1 + (quadraticChar F ((skCollSgn ς D T e.1 e.2 : F) * (x' e.2 - x e.1)) : ℝ)) +
        (1 - |D e|) := by
  by_cases hD : D e < 0
  · have hm := hneg hD
    have hflip : (quadraticChar F ((skCollSgn ς D T e.1 e.2 : F) * (x' e.2 - x e.1)) : ℝ) =
        -(quadraticChar F ((ς e.1 e.2 : F) * (x' e.2 - x e.1)) : ℝ) := by
      unfold skCollSgn
      simp only [Prod.mk.eta, he, hD, ↓reduceIte, Int.cast_neg]
      have : (-(ς e.1 e.2 : F)) * (x' e.2 - x e.1) =
          (-1) * ((ς e.1 e.2 : F) * (x' e.2 - x e.1)) := by ring
      rw [this, map_mul, hm]
      push_cast
      ring
    rw [hflip, abs_of_neg hD]
    ring
  · push Not at hD
    have hflip : (quadraticChar F ((skCollSgn ς D T e.1 e.2 : F) * (x' e.2 - x e.1)) : ℝ) =
        (quadraticChar F ((ς e.1 e.2 : F) * (x' e.2 - x e.1)) : ℝ) := by
      unfold skCollSgn
      have : ¬ (D e < 0) := not_lt.mpr hD
      simp only [Prod.mk.eta, he, this, ↓reduceIte]
    rw [hflip, abs_of_nonneg hD]
    ring

/-- **The convex decomposition** of the soft collision kernel. -/
theorem sk_collKer1_expand (ς : U → U → ℤ) (D : U × U → ℝ)
    (hneg : ∀ e, D e < 0 → quadraticChar F (-1) = -1) (x x' : U → F) :
    skCollKer1 ς D x x' = ∑ T ∈ (collisionCross ς).powerset,
      skW D (collisionCross ς) T * collisionKernel1 (skCollSgn ς D T) x x' := by
  unfold skCollKer1 collisionKernel1
  split_ifs with h
  · have hF : ∏ e ∈ collisionCross ς,
        (1 + D e * (quadraticChar F ((ς e.1 e.2 : F) * (x' e.2 - x e.1)) : ℝ)) =
        ∏ e ∈ collisionCross ς, (|D e| * (1 + (quadraticChar F
          ((skCollSgn ς D (collisionCross ς) e.1 e.2 : F) * (x' e.2 - x e.1)) : ℝ)) +
            (1 - |D e|)) :=
      prod_congr rfl fun e he => sk_coll_flip_identity ς D he (hneg e) x x'
    rw [hF, prod_add]
    refine sum_congr rfl fun T hT => ?_
    rw [mem_powerset] at hT
    unfold collisionKernel skW
    rw [sk_collCross_sgn ς D hT, prod_mul_distrib]
    have hTe : ∏ e ∈ T, (1 + (quadraticChar F
        ((skCollSgn ς D (collisionCross ς) e.1 e.2 : F) * (x' e.2 - x e.1)) : ℝ)) =
        ∏ e ∈ T, (1 + (quadraticChar F ((skCollSgn ς D T e.1 e.2 : F) * (x' e.2 - x e.1)) : ℝ)) := by
      refine prod_congr rfl fun e he => ?_
      unfold skCollSgn
      simp only [Prod.mk.eta, he, hT he, ↓reduceIte]
    rw [hTe]
    ring
  · simp

/-- Monotonicity of the merge count `mg(j, i)` in the support of the signs. -/
theorem sk_rowsMg_mono (G : OrientedGraph U) {ς ς' : U → U → ℤ}
    (h : ∀ i, rowsN ς' i ⊆ rowsN ς i) (j i : U) : rowsMg G ς' j i ≤ rowsMg G ς j i := by
  unfold rowsMg
  refine card_le_card fun i' hi' => ?_
  rw [mem_filter] at hi' ⊢
  exact ⟨hi'.1, h i' hi'.2⟩

theorem sk_collisionA_mono (G : OrientedGraph U) {ς ς' : U → U → ℤ}
    (h : ∀ i, rowsN ς' i ⊆ rowsN ς i) (i j : U) :
    collisionA G ς' i j ≤ collisionA G ς i j := by
  unfold collisionA collisionR
  refine pow_le_pow_right₀ (by norm_num) ?_
  have hm := sk_rowsMg_mono G h j i
  have hc := card_le_card (h i)
  by_cases hj : j ∈ rowsN ς i
  · by_cases hj' : j ∈ rowsN ς' i
    · simp only [hj, hj', ↓reduceIte]
      omega
    · simp only [hj, hj', ↓reduceIte]
      have := card_lt_card ⟨h i, fun h' => hj' (h' hj)⟩
      omega
  · have hj' : j ∉ rowsN ς' i := fun h' => hj (h i h')
    simp only [hj, hj', ↓reduceIte]
    omega

theorem sk_collisionT_mono (G : OrientedGraph U) {ς ς' : U → U → ℤ}
    (h : ∀ i, rowsN ς' i ⊆ rowsN ς i) (ord : U → U → U → ℕ) (i j ℓ : U) :
    collisionT G ς' ord i j ℓ ≤ collisionT G ς ord i j ℓ := by
  unfold collisionT collisionR
  have hc := card_le_card (h ℓ)
  by_cases hi : i ∈ rowsAdj G ℓ
  · by_cases hj : j ∈ rowsN ς ℓ
    · by_cases hj' : j ∈ rowsN ς' ℓ
      · simp only [hi, hj, hj', and_self, ↓reduceIte]
        omega
      · simp only [hi, hj, hj', and_self, and_false, ↓reduceIte]
        have := card_lt_card ⟨h ℓ, fun h' => hj' (h' hj)⟩
        omega
    · have hj' : j ∉ rowsN ς' ℓ := fun h' => hj (h ℓ h')
      simp only [hi, hj, hj', and_false, ↓reduceIte]
      omega
  · simp only [hi, false_and, ↓reduceIte]
    omega

/-- `D_1` (`lem:oct24-collision`(a)) is nondecreasing in the support of the signs. -/
theorem sk_collisionD1_mono (G : OrientedGraph U) {ς ς' : U → U → ℤ}
    (h : ∀ i, rowsN ς' i ⊆ rowsN ς i) (ord : U → U → U → ℕ) {q : ℝ} (hq : 0 < q) {n : ℕ}
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) q n < 1) :
    collisionD1 G ς' ord q n ≤ collisionD1 G ς ord q n := by
  unfold collisionD1
  have hL : 0 < collisionLint G q n := prod_pos fun v _ => by linarith [hS1 v]
  have hn2 : (0 : ℝ) ≤ 2 * n := by positivity
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun i _ => sum_le_sum fun j _ => ?_)
    (inv_nonneg.mpr (mul_pos hq hL).le)
  refine mul_le_mul (sk_collisionA_mono G h i j) ?_ (prod_nonneg fun ℓ _ => ?_) (by
    unfold collisionA; positivity)
  · refine prod_le_prod₀ (fun ℓ _ => ?_) (fun ℓ _ => ?_)
    · linarith [coarseError_nonneg (q := q) hn2 (collisionT G ς' ord i j ℓ)]
    · linarith [coarseError_mono (q := q) hn2 (sk_collisionT_mono G h ord i j ℓ)]
  · linarith [coarseError_nonneg (q := q) hn2 (collisionT G ς' ord i j ℓ)]

theorem sk_collisionD1_congr (G : OrientedGraph U) {ς ς' : U → U → ℤ}
    (h : ∀ i, rowsN ς' i = rowsN ς i) (ord : U → U → U → ℕ) (q : ℝ) (n : ℕ) :
    collisionD1 G ς' ord q n = collisionD1 G ς ord q n := by
  have hN : rowsN ς' = rowsN ς := funext h
  unfold collisionD1 collisionA collisionT collisionR rowsMg
  rw [hN]

omit [DecidableEq U] in
theorem sk_collKer1_nonneg (ς : U → U → ℤ) (D : U × U → ℝ) (hD : ∀ e, |D e| ≤ 1)
    (x x' : U → F) : 0 ≤ skCollKer1 ς D x x' := by
  unfold skCollKer1
  split_ifs
  · exact prod_nonneg fun e _ => sk_pin_omega_factor_nonneg' (D e) (hD e) _
  · exact le_rfl

/-- Row sums of the soft collision kernel (`lem:oct24-collision`(a)): `E_{x'} K^D_1(x, x') ≤ D_1`. -/
theorem sk_coll_rowSum_le (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hne : (injLabellings F G).Nonempty)
    {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (ord : U → U → U → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (D : U × U → ℝ) (hD : ∀ e, |D e| ≤ 1) (hneg : ∀ e, D e < 0 → quadraticChar F (-1) = -1)
    (x : U → F) (hx : Function.Injective x) :
    ∑ x' ∈ injLabellings F G, skCollKer1 ς D x x' / (injLabellings F G).card ≤
      collisionD1 G ς ord (Fintype.card F) n := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hw0 : ∀ T ∈ (collisionCross ς).powerset, 0 ≤ skW D (collisionCross ς) T :=
    fun T _ => skW_nonneg (fun e _ => hD e) T
  have hT : ∀ T ∈ (collisionCross ς).powerset,
      ∑ x' ∈ injLabellings F G, collisionKernel1 (skCollSgn ς D T) x x' /
        (injLabellings F G).card ≤ collisionD1 G ς ord (Fintype.card F) n := by
    intro T _
    have h := collision_rowSum_le hW G (skCollSgn ς D T) (sk_collSgn_values hς D T) hne hn hS1 ord
      hord x hx
    rw [coverRow_expect_graphLaw] at h
    rw [← sum_div]
    exact h.trans (sk_collisionD1_mono G (sk_rowsN_collSgn_subset ς D T) ord hq hS1)
  simp only [sk_collKer1_expand ς D hneg x]
  calc ∑ x' ∈ injLabellings F G, (∑ T ∈ (collisionCross ς).powerset,
        skW D (collisionCross ς) T * collisionKernel1 (skCollSgn ς D T) x x') /
          (injLabellings F G).card
      = ∑ T ∈ (collisionCross ς).powerset, skW D (collisionCross ς) T *
          ∑ x' ∈ injLabellings F G, collisionKernel1 (skCollSgn ς D T) x x' /
            (injLabellings F G).card := by
        simp only [sum_div, mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun T _ => sum_congr rfl fun x' _ => by ring
    _ ≤ ∑ T ∈ (collisionCross ς).powerset, skW D (collisionCross ς) T *
          collisionD1 G ς ord (Fintype.card F) n :=
        sum_le_sum fun T hT' => mul_le_mul_of_nonneg_left (hT T hT') (hw0 T hT')
    _ = _ := by rw [← sum_mul, skW_sum, one_mul]

/-- Exchanging the two labellings in the soft collision kernel. -/
theorem sk_collKer1_swap (ς : U → U → ℤ) (D : U × U → ℝ) (x x' : U → F) :
    skCollKer1 ς D x x' = skCollKer1 (skT ς) (fun e => D e.swap) x' x := by
  unfold skCollKer1 collisionCommon
  rw [inter_comm]
  split_ifs
  · have hc : collisionCross (skT ς) = (collisionCross ς).image Prod.swap := by
      ext e
      unfold collisionCross skT
      simp only [mem_filter, mem_univ, true_and, mem_image, neg_ne_zero]
      constructor
      · intro h
        exact ⟨e.swap, h, Prod.swap_swap e⟩
      · rintro ⟨e', he', rfl⟩
        simpa using he'
    rw [hc, prod_image (fun a _ b _ h => Prod.swap_injective h)]
    refine prod_congr rfl fun e _ => ?_
    simp only [skT, Prod.fst_swap, Prod.snd_swap, Prod.swap_swap, Int.cast_neg]
    congr 3
    ring_nf
  · rfl

/-- **`cor:soft-kernels`(b) for `lem:oct24-collision`(a)**: with antisymmetric signs, coefficients
`|D_e| ≤ 1` and `χ(-1) = -1` if some `D_e < 0`, the soft collision operator with kernel
`1{exactly one common label} ∏_{e ∈ E_×}(1 + D_e χ_e)` has norm at most `D_1` on `L²(μ)`
(the bound of `collision_opBound`; Schur's test with the row sums and, for the column sums, the
transposed soft kernel). -/
theorem sk_soft_collision_opBound (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (ord : U → U → U → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (D : U × U → ℝ) (hD : ∀ e, |D e| ≤ 1) (hneg : ∀ e, D e < 0 → quadraticChar F (-1) = -1) :
    Sarkozy.Influence.OpBound (injLabellings F G) (injLabellings F G)
      (fun x x' => skCollKer1 ς D x x' / (injLabellings F G).card)
      (collisionD1 G ς ord (Fintype.card F) n) := by
  have hN : (0 : ℝ) < (injLabellings F G).card := by exact_mod_cast card_pos.mpr hne
  have hinj : ∀ x ∈ injLabellings F G, Function.Injective x := fun x hx a b h => by
    simp only [injLabellings, mem_filter, mem_univ, true_and] at hx
    exact hx.1 a (mem_univ _) b (mem_univ _) h
  have hrow : ∀ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G,
      skCollKer1 ς D x x' / (injLabellings F G).card ≤ collisionD1 G ς ord (Fintype.card F) n :=
    fun x hx => sk_coll_rowSum_le hW G ς hς hne hn hS1 ord hord D hD hneg x (hinj x hx)
  have hsupp : ∀ i, rowsN (skT ς) i = rowsN ς i := by
    intro i
    unfold rowsN skT
    exact filter_congr fun j _ => by rw [hanti i j]
  have hcol : ∀ x' ∈ injLabellings F G, ∑ x ∈ injLabellings F G,
      skCollKer1 ς D x x' / (injLabellings F G).card ≤ collisionD1 G ς ord (Fintype.card F) n := by
    intro x' hx'
    have h := sk_coll_rowSum_le hW G (skT ς) (skT_values ς hς) hne hn hS1 ord hord
      (fun e => D e.swap) (fun e => hD e.swap) (fun e he => hneg e.swap he) x' (hinj x' hx')
    rw [sk_collisionD1_congr G hsupp] at h
    calc ∑ x ∈ injLabellings F G, skCollKer1 ς D x x' / (injLabellings F G).card
        = ∑ x ∈ injLabellings F G, skCollKer1 (skT ς) (fun e => D e.swap) x' x /
            (injLabellings F G).card :=
          sum_congr rfl fun x _ => by rw [sk_collKer1_swap]
      _ ≤ _ := h
  obtain ⟨x0, hx0⟩ := hne
  have hD1 : 0 ≤ collisionD1 G ς ord (Fintype.card F) n :=
    le_trans (sum_nonneg fun x' _ => div_nonneg (sk_collKer1_nonneg ς D hD x0 x') hN.le)
      (hrow x0 hx0)
  have h := Sarkozy.Influence.opBound_schur (R := injLabellings F G) (C := injLabellings F G)
    (fun x x' => div_nonneg (sk_collKer1_nonneg ς D hD x x') hN.le) hD1 hD1 hrow hcol
  rwa [Real.sqrt_mul_self hD1] at h

end SkColl

end Sarkozy.ExtractionK
