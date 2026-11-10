module

public import Sarkozy.ExtractionK.OneSide

@[expose] public section

/-!
# Grouped extraction, III: the bound (`lem:matching:extractionk`)

`paper/sections/16_extraction.tex`, `lem:matching:extractionk` (Grouped extraction with a
witness of size `k`).

* `grouped_extraction_count`: the counting form of the theorem,
  `|∑ f K_𝒞 h| ≤ Λ (2^{f_V} M_{U_x} M_{C_z} ∑ f²)^{1/2} (2^{f_W} M_{U_z} M_{C_x} ∑ h²)^{1/2}`.
* `grouped_extraction_sum_le`: normalized by `|𝓘⁺|²`, with the lower counts
  `|𝓘⁺| ≥ ∏_v q 2^{-t_v} (1 - e_{t_v}(q, n))` along the orders of the two copies
  (`card_injLabellings_ge`, `lem:graphs:sequential`(a)); the witness vertices give
  `q^k 2^{-t_V} (1 - ê)^k`, the others their vertex factors.
* `grouped_extraction`: **`lem:matching:extractionk`** for a class `𝒞(P, A)` with a record
  (`IsWitness`, `IsCover`, orders), in the paper's normalization:
  `|∑_{S ∈ 𝒞} ⟨f, T_S h⟩_μ| ≤ c_ker r^k 2^{ex(𝒞)/2} ∏_v F_v^{1/2} (1 - ê)^{-k} ‖f‖_μ ‖h‖_μ`,
  which is sharper than the paper's statement by the factor `(R̃_{U_x} R̃_{U_z})^{1/2} ≥ 1`;
  `grouped_extraction_paper` is the paper's statement.

## Formal setting and conventions

* `F` is a finite field with `q` elements (`F = 𝔽_p`), `WeilBound F` is Weil's theorem
  (`thm:weil`(a), the literature input of `lem:extension`); the half graph `G⁺` is an oriented
  graph `G` on a finite type `U`, cross signs `ς ∈ {0, ±1}` with `ς_{kj} = -ς_{jk}`; `n ≥ |U⁺|`;
  (S1) enters only through `e_{d⁰_i}(q, n) ≤ ê < 1`.
* The record's orders are global orders `ordX`, `ordZ` of the two copies of `U⁺`, with the cover
  first and the integrated set last (the order of `V`, `W` in between is free). Then `t_v` is the
  number of earlier neighbours (`ordT`) for every vertex, and `t_V = ∑_{v ∈ V} t_v` is
  `e(V) + e(V, C_x)` (`cmp_sum_ordT`, `Compressed.lean`).
* The kernel hypothesis is an `OpBound` on injective tuples in the `ℓ²` counting normalization,
  `c_ker √q^k`, which is the paper's `c_ker r^k` for uniform probability.
* `T_S` is the operator with kernel `χ_S` relative to `μ ⊗ μ`, so
  `∑_{S ∈ 𝒞} ⟨f, T_S h⟩_μ = E_x[f(x) E_{x'}[∑_{S ∈ 𝒞} χ_S(x, x') h(x')]]` for real `f`, `h`.
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

/-! ## Part G: the counting bound and its normalization -/

section PartG

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

open Sarkozy.Influence

/-- **Steps 1–8, counting form**:
`|∑_{x, x' ∈ 𝓘⁺} f(x) K_𝒞(x, x') h(x')| ≤ Λ (2^{f_V} M_{U_x} M_{C_z} ∑ f²)^{1/2}
(2^{f_W} M_{U_z} M_{C_x} ∑ h²)^{1/2}`, where `M_Y` is the product over `Y` of `q 2^{-t_v}` times
the numerator of the vertex factor `F_v`. -/
theorem grouped_extraction_count (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k) (n : ℕ)
    (P Fr : Finset (U × U)) (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0)
    (V W Cx Cz : Finset U) (hVC : ∀ u ∈ V, u ∉ Cx) (hWC : ∀ u ∈ W, u ∉ Cz)
    (hP : ∀ e ∈ P, (e.1 ∈ V ∧ e.2 ∈ W) ∨ e.1 ∈ Cx ∨ e.2 ∈ Cz)
    (hFr : ∀ e ∈ Fr, e.1 ∈ Cx ∨ e.2 ∈ Cz)
    (ordX ordZ : U → ℕ) (hordX : Function.Injective ordX) (hordZ : Function.Injective ordZ)
    (hsegX : ∀ a, a ∉ univ \ (V ∪ Cx) → ∀ b ∈ univ \ (V ∪ Cx), ordX a < ordX b)
    (hsegZ : ∀ a, a ∉ univ \ (W ∪ Cz) → ∀ b ∈ univ \ (W ∪ Cz), ordZ a < ordZ b)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hker : OpBound (injTuples F V) (injTuples F W) (rectKer ς P V W) Λ)
    (f h : (U → F) → ℝ) :
    |∑ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G, f x * classKer ς P Fr x x' * h x'| ≤
      Λ * Real.sqrt (2 ^ (Fr.filter (fun e => e.1 ∈ V)).card *
          (∏ u ∈ univ \ (V ∪ Cx), intNumQ F G ς n ordX Fr Cz u) *
          (∏ b ∈ Cz, coverNumQ F G ς n Cz ordZ (Fr.filter (fun e => e.2 ∈ Cz)) b) *
          ∑ x ∈ injLabellings F G, f x ^ 2) *
        Real.sqrt (2 ^ (Fr.filter (fun e => e.2 ∈ W)).card *
          (∏ u ∈ univ \ (W ∪ Cz), intNumQ F G ς n ordZ (Fr.image Prod.swap) Cx u) *
          (∏ b ∈ Cx, coverNumQ F G ς n Cx ordX
            ((Fr.image Prod.swap).filter (fun e => e.2 ∈ Cx)) b) *
          ∑ x ∈ injLabellings F G, h x ^ 2) := by
  refine (bilinear_le G ς P Fr V W Cx Cz hVC hWC hP hFr hΛ hker f h).trans ?_
  have h1 := one_side_le hW G ς hς n P Fr hFrς V Cx Cz hVC
    (fun e he h1 => (hFr e he).resolve_left h1) ordX ordZ hordX hordZ.injOn hsegX f
  have h2 := other_side_le hW G ς hς hanti n P Fr hFrς W Cx Cz hWC
    (fun e he h2 => (hFr e he).resolve_right h2) ordX ordZ hordX.injOn hordZ hsegZ h
  exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h1) hΛ)
    (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _) (mul_nonneg hΛ (Real.sqrt_nonneg _))

/-- The normalization: from the counting bound to `L²(μ)`, with lower bounds `L_X, L_Z ≤ |𝓘⁺|`. -/
theorem normalize_le {Q N LX LZ A B Sf Sh Λ : ℝ} (hN : 0 < N) (hLX : 0 < LX) (hLZ : 0 < LZ)
    (hLXN : LX ≤ N) (hLZN : LZ ≤ N) (hA : 0 ≤ A) (hB : 0 ≤ B) (hSf : 0 ≤ Sf) (hSh : 0 ≤ Sh)
    (hΛ : 0 ≤ Λ) (hQ : |Q| ≤ Λ * Real.sqrt (A * Sf) * Real.sqrt (B * Sh)) :
    |Q / N ^ 2| ≤ Λ * Real.sqrt (A * B / (LX * LZ)) * Real.sqrt (Sf / N) *
      Real.sqrt (Sh / N) := by
  have e1 : Real.sqrt (A * Sf) * Real.sqrt (B * Sh) =
      Real.sqrt (A * B) * Real.sqrt (Sf * Sh) := by
    rw [← Real.sqrt_mul (mul_nonneg hA hSf), ← Real.sqrt_mul (mul_nonneg hA hB)]
    congr 1
    ring
  have e2 : Real.sqrt (A * B / (N * N)) = Real.sqrt (A * B) / N := by
    rw [Real.sqrt_div (mul_nonneg hA hB), Real.sqrt_mul_self hN.le]
  have e3 : Real.sqrt (Sf / N) * Real.sqrt (Sh / N) = Real.sqrt (Sf * Sh) / N := by
    rw [← Real.sqrt_mul (div_nonneg hSf hN.le)]
    have : Sf / N * (Sh / N) = Sf * Sh / (N * N) := by field_simp
    rw [this, Real.sqrt_div (mul_nonneg hSf hSh), Real.sqrt_mul_self hN.le]
  have hmono : Real.sqrt (A * B / (N * N)) ≤ Real.sqrt (A * B / (LX * LZ)) := by
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_left (mul_nonneg hA hB) (mul_pos hLX hLZ)
    exact mul_le_mul hLXN hLZN hLZ.le hN.le
  rw [abs_div, abs_of_pos (pow_pos hN 2)]
  calc |Q| / N ^ 2 ≤ Λ * Real.sqrt (A * Sf) * Real.sqrt (B * Sh) / N ^ 2 :=
        div_le_div_of_nonneg_right hQ (by positivity)
    _ = Λ * Real.sqrt (A * B / (N * N)) * (Real.sqrt (Sf / N) * Real.sqrt (Sh / N)) := by
        rw [e2, e3, mul_assoc Λ, e1]
        field_simp
    _ ≤ Λ * Real.sqrt (A * B / (LX * LZ)) * (Real.sqrt (Sf / N) * Real.sqrt (Sh / N)) := by
        gcongr
    _ = _ := by ring

end PartG

/-! ## Part H: the vertex factors and the statement of `lem:matching:extractionk` -/

section PartH

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

open Sarkozy.Influence

/-- The one-step lower count `ℓ_v = q 2^{-t_v} (1 - e_{t_v}(q, n))` of `lem:graphs:sequential`
along the order `ord`. -/
noncomputable def stepLow (G : OrientedGraph U) (q : ℝ) (n : ℕ) (ord : U → ℕ) (v : U) : ℝ :=
  q * (2 : ℝ)⁻¹ ^ ordT G ord v * (1 - coarseError (ordT G ord v) q n)

theorem ordT_le_deg (G : OrientedGraph U) (ord : U → ℕ) (v : U) :
    ordT G ord v ≤ rowsDeg0 G v := by
  unfold ordT coverRowT
  exact coverRow_nbrCount_le G _ v

theorem coarseError_ordT_le (G : OrientedGraph U) {q : ℝ} {n : ℕ} {ehat : ℝ}
    (hehat : ∀ i, coarseError (rowsDeg0 G i) q n ≤ ehat) (ord : U → ℕ) (v : U) :
    coarseError (ordT G ord v) q n ≤ ehat :=
  (coarseError_mono (Nat.cast_nonneg n) (ordT_le_deg G ord v)).trans (hehat v)

omit [DecidableEq F] in
/-- `F_u · ℓ_u = q 2^{-t_u} num_u` for an integrated vertex. -/
theorem intNumQ_eq (G : OrientedGraph U) (ς : U → U → ℤ) (n : ℕ) (ord : U → ℕ)
    (Fr : Finset (U × U)) (Cz : Finset U) (u : U)
    (he : coarseError (ordT G ord u) (Fintype.card F) n < 1) :
    intNumQ F G ς n ord Fr Cz u =
      intF G ς (Fintype.card F) n ord Fr Cz u * stepLow G (Fintype.card F) n ord u := by
  unfold intNumQ intF stepLow
  have h1 : 1 - coarseError (ordT G ord u) (Fintype.card F) n ≠ 0 := by linarith
  field_simp

/-- For an initial segment `C` of the order, `t_b` counted in `C` is `t_b` counted in the
whole order. -/
theorem coverRowT_eq_ordT (G : OrientedGraph U) (C : Finset U) (ord : U → ℕ)
    (hseg : ∀ a ∈ C, ∀ b, b ∉ C → ord a < ord b) {b : U} (hb : b ∈ C) :
    coverRowT G C ord b = ordT G ord b := by
  unfold ordT coverRowT
  congr 1
  unfold coverRowEarlier
  ext a
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    by_contra ha
    exact absurd (hseg b hb a ha) (by omega)

omit [DecidableEq F] in
/-- `F_b · ℓ_b = q 2^{-t_b} num_b` for a cover vertex. -/
theorem coverNumQ_eq (G : OrientedGraph U) (ς : U → U → ℤ) (n : ℕ) (C : Finset U)
    (ord : U → ℕ) (H : Finset (U × U)) (hseg : ∀ a ∈ C, ∀ b, b ∉ C → ord a < ord b)
    {b : U} (hb : b ∈ C) (he : coarseError (ordT G ord b) (Fintype.card F) n < 1) :
    coverNumQ F G ς n C ord H b =
      coverRowF G ς (Fintype.card F) n C ord H b * stepLow G (Fintype.card F) n ord b := by
  unfold coverNumQ coverRowF stepLow
  rw [coverRowT_eq_ordT G C ord hseg hb]
  have h1 : 1 - coarseError (ordT G ord b) (Fintype.card F) n ≠ 0 := by linarith
  field_simp

/-- The product over the vertices, split along `U = C ⊔ V ⊔ (U \ (V ∪ C))`. -/
theorem prod_univ_three (V C : Finset U) (hVC : ∀ u ∈ V, u ∉ C) (g : U → ℝ) :
    ∏ v, g v = (∏ v ∈ univ \ (V ∪ C), g v) * (∏ v ∈ V, g v) * ∏ v ∈ C, g v := by
  rw [← prod_sdiff (subset_univ (V ∪ C)), prod_union (disjoint_left.mpr hVC), mul_assoc]

theorem sqrt_pow_sq {q : ℝ} (hq : 0 ≤ q) (k : ℕ) : (Real.sqrt q ^ k) ^ 2 = q ^ k := by
  rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hq]

/-- **`lem:matching:extractionk` (grouped extraction), sum form.** For a class with present
pairs `P`, free pairs `Fr`, witness sets `V`, `W` (`|V| = |W| = k`), a cover `(C_x, C_z)`
(`hP`, `hFr`: (VC_k), with no free pair in `V × W` by (W_k)) and orders of the two copies in
which `C_x` (`C_z`) comes first and `U_x` (`U_z`) last, if the rectangle kernel `𝖶` has norm at
most `c_ker √q^k` on injective tuples (`ℓ²` counting normalization; `c_ker r^k` for uniform
probability), then
`|E_{x,x' ∼ μ} f(x) K_𝒞(x, x') h(x')| ≤ c_ker r^k (2^{ex} ∏_v F_v)^{1/2} (1 - ê)^{-k} ‖f‖_μ ‖h‖_μ`,
`ex = t_V + t_W + f_V + f_W`, the product over the `2(n - k)` non-witness vertices
`U_x ⊔ C_z ⊔ U_z ⊔ C_x`. This is the paper's bound without the factor
`(R̃_{U_x} R̃_{U_z})^{1/2} ≥ 1` (`grouped_extraction_sum_le_paper` adds it). Here `E_μ` is
written as `|𝓘⁺|⁻¹ ∑_{𝓘⁺}`; `ê ≥ e_{d⁰_i}(q, n)` for all `i`, `ê < 1` (from (S1)). -/
theorem grouped_extraction_sum_le (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k) {n : ℕ}
    (hn : Fintype.card U ≤ n) {ehat : ℝ}
    (hehat : ∀ i, coarseError (rowsDeg0 G i) (Fintype.card F) n ≤ ehat) (hehat1 : ehat < 1)
    (P Fr : Finset (U × U)) (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) {k : ℕ}
    (V W Cx Cz : Finset U) (hVk : V.card = k) (hWk : W.card = k)
    (hVC : ∀ u ∈ V, u ∉ Cx) (hWC : ∀ u ∈ W, u ∉ Cz)
    (hP : ∀ e ∈ P, (e.1 ∈ V ∧ e.2 ∈ W) ∨ e.1 ∈ Cx ∨ e.2 ∈ Cz)
    (hFr : ∀ e ∈ Fr, e.1 ∈ Cx ∨ e.2 ∈ Cz)
    (ordX ordZ : U → ℕ) (hordX : Function.Injective ordX) (hordZ : Function.Injective ordZ)
    (hX0 : ∀ a ∈ Cx, ∀ b, b ∉ Cx → ordX a < ordX b)
    (hZ0 : ∀ a ∈ Cz, ∀ b, b ∉ Cz → ordZ a < ordZ b)
    (hsegX : ∀ a, a ∉ univ \ (V ∪ Cx) → ∀ b ∈ univ \ (V ∪ Cx), ordX a < ordX b)
    (hsegZ : ∀ a, a ∉ univ \ (W ∪ Cz) → ∀ b ∈ univ \ (W ∪ Cz), ordZ a < ordZ b)
    {cker : ℝ} (hcker : 0 ≤ cker)
    (hker : OpBound (injTuples F V) (injTuples F W) (rectKer ς P V W)
      (cker * Real.sqrt (Fintype.card F) ^ k))
    (f h : (U → F) → ℝ) :
    |(∑ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G, f x * classKer ς P Fr x x' * h x') /
        ((injLabellings F G).card : ℝ) ^ 2| ≤
      cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        Real.sqrt (2 ^ ((Fr.filter (fun e => e.1 ∈ V)).card + (Fr.filter (fun e => e.2 ∈ W)).card +
            ∑ v ∈ V, ordT G ordX v + ∑ v ∈ W, ordT G ordZ v) *
          ((∏ u ∈ univ \ (V ∪ Cx), intF G ς (Fintype.card F) n ordX Fr Cz u) *
            (∏ b ∈ Cz, coverRowF G ς (Fintype.card F) n Cz ordZ (Fr.filter (fun e => e.2 ∈ Cz)) b) *
            (∏ u ∈ univ \ (W ∪ Cz), intF G ς (Fintype.card F) n ordZ (Fr.image Prod.swap) Cx u) *
            ∏ b ∈ Cx, coverRowF G ς (Fintype.card F) n Cx ordX
              ((Fr.image Prod.swap).filter (fun e => e.2 ∈ Cx)) b)) /
        (1 - ehat) ^ k *
        Real.sqrt ((∑ x ∈ injLabellings F G, f x ^ 2) / (injLabellings F G).card) *
        Real.sqrt ((∑ x ∈ injLabellings F G, h x ^ 2) / (injLabellings F G).card) := by
  set q : ℝ := (Fintype.card F : ℝ) with hq
  have hq0 : 0 < q := by rw [hq]; exact_mod_cast Fintype.card_pos
  set I := injLabellings F G
  set N : ℝ := (I.card : ℝ)
  set Ux := univ \ (V ∪ Cx)
  set Uz := univ \ (W ∪ Cz)
  set H := Fr.filter (fun e => e.2 ∈ Cz)
  set HT := (Fr.image Prod.swap).filter (fun e => e.2 ∈ Cx)
  set fV := (Fr.filter (fun e => e.1 ∈ V)).card
  set fW := (Fr.filter (fun e => e.2 ∈ W)).card
  set tV := ∑ v ∈ V, ordT G ordX v
  set tW := ∑ v ∈ W, ordT G ordZ v
  set ℓX := stepLow G q n ordX
  set ℓZ := stepLow G q n ordZ
  have he1 : ∀ ord v, coarseError (ordT G ord v) q n < 1 := fun ord v =>
    lt_of_le_of_lt (coarseError_ordT_le G hehat ord v) hehat1
  have hℓpos : ∀ ord v, 0 < stepLow G q n ord v := fun ord v => by
    unfold stepLow
    have := he1 ord v
    exact mul_pos (mul_pos hq0 (by positivity)) (by linarith)
  -- the counting bound
  have hΛ : 0 ≤ cker * Real.sqrt q ^ k := mul_nonneg hcker (by positivity)
  have hQ := grouped_extraction_count hW G ς hς hanti n P Fr hFrς V W Cx Cz hVC hWC hP hFr ordX
    ordZ hordX hordZ hsegX hsegZ hΛ hker f h
  -- the lower counts
  have hLX : ∏ v, ℓX v ≤ N := by
    have := card_injLabellings_ge hW G hn ordX hordX (fun v => (he1 ordX v).le)
    refine le_trans (le_of_eq ?_) this
    refine prod_congr rfl fun v _ => ?_
    simp only [ℓX, stepLow, div_eq_mul_inv, inv_pow, hq]
  have hLZ : ∏ v, ℓZ v ≤ N := by
    have := card_injLabellings_ge hW G hn ordZ hordZ (fun v => (he1 ordZ v).le)
    refine le_trans (le_of_eq ?_) this
    refine prod_congr rfl fun v _ => ?_
    simp only [ℓZ, stepLow, div_eq_mul_inv, inv_pow, hq]
  have hLX0 : 0 < ∏ v, ℓX v := prod_pos fun v _ => hℓpos ordX v
  have hLZ0 : 0 < ∏ v, ℓZ v := prod_pos fun v _ => hℓpos ordZ v
  have hN0 : 0 < N := lt_of_lt_of_le hLX0 hLX
  -- the factor identities
  set PUx := ∏ u ∈ Ux, intF G ς q n ordX Fr Cz u
  set PCz := ∏ b ∈ Cz, coverRowF G ς q n Cz ordZ H b
  set PUz := ∏ u ∈ Uz, intF G ς q n ordZ (Fr.image Prod.swap) Cx u
  set PCx := ∏ b ∈ Cx, coverRowF G ς q n Cx ordX HT b
  have hMUx : ∏ u ∈ Ux, intNumQ F G ς n ordX Fr Cz u = PUx * ∏ u ∈ Ux, ℓX u := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun u _ => intNumQ_eq G ς n ordX Fr Cz u (he1 ordX u)
  have hMUz : ∏ u ∈ Uz, intNumQ F G ς n ordZ (Fr.image Prod.swap) Cx u =
      PUz * ∏ u ∈ Uz, ℓZ u := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun u _ => intNumQ_eq G ς n ordZ _ Cx u (he1 ordZ u)
  have hMCz : ∏ b ∈ Cz, coverNumQ F G ς n Cz ordZ H b = PCz * ∏ b ∈ Cz, ℓZ b := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun b hb => coverNumQ_eq G ς n Cz ordZ H hZ0 hb (he1 ordZ b)
  have hMCx : ∏ b ∈ Cx, coverNumQ F G ς n Cx ordX HT b = PCx * ∏ b ∈ Cx, ℓX b := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun b hb => coverNumQ_eq G ς n Cx ordX HT hX0 hb (he1 ordX b)
  rw [hMUx, hMCz, hMUz, hMCx] at hQ
  set A := (2 : ℝ) ^ fV * (PUx * ∏ u ∈ Ux, ℓX u) * (PCz * ∏ b ∈ Cz, ℓZ b)
  set B := (2 : ℝ) ^ fW * (PUz * ∏ u ∈ Uz, ℓZ u) * (PCx * ∏ b ∈ Cx, ℓX b)
  have hPF0 : ∀ ord Fr' Cz' u, 0 ≤ intF G ς q n ord Fr' Cz' u := by
    intro ord Fr' Cz' u
    have h1 := intNumQ_nonneg (F := F) G ς n ord Fr' Cz' u
    rw [intNumQ_eq G ς n ord Fr' Cz' u (he1 ord u)] at h1
    exact nonneg_of_mul_nonneg_left h1 (hℓpos ord u)
  have hcF0 : ∀ (C : Finset U) (ord : U → ℕ) (H' : Finset (U × U)),
      (∀ a ∈ C, ∀ b, b ∉ C → ord a < ord b) → ∀ b ∈ C, 0 ≤ coverRowF G ς q n C ord H' b := by
    intro C ord H' hseg b hb
    have h1 := coverNumQ_nonneg (F := F) G ς n C ord H' b
    rw [coverNumQ_eq G ς n C ord H' hseg hb (he1 ord b)] at h1
    exact nonneg_of_mul_nonneg_left h1 (hℓpos ord b)
  have hPUx0 : 0 ≤ PUx := prod_nonneg fun u _ => hPF0 _ _ _ u
  have hPUz0 : 0 ≤ PUz := prod_nonneg fun u _ => hPF0 _ _ _ u
  have hPCz0 : 0 ≤ PCz := prod_nonneg fun b hb => hcF0 Cz ordZ H hZ0 b hb
  have hPCx0 : 0 ≤ PCx := prod_nonneg fun b hb => hcF0 Cx ordX HT hX0 b hb
  have hA0 : 0 ≤ A := mul_nonneg (mul_nonneg (by positivity)
    (mul_nonneg hPUx0 (prod_nonneg fun u _ => (hℓpos ordX u).le)))
    (mul_nonneg hPCz0 (prod_nonneg fun u _ => (hℓpos ordZ u).le))
  have hB0 : 0 ≤ B := mul_nonneg (mul_nonneg (by positivity)
    (mul_nonneg hPUz0 (prod_nonneg fun u _ => (hℓpos ordZ u).le)))
    (mul_nonneg hPCx0 (prod_nonneg fun u _ => (hℓpos ordX u).le))
  have hnorm := normalize_le hN0 hLX0 hLZ0 hLX hLZ hA0 hB0
    (sum_nonneg fun x _ => sq_nonneg (f x)) (sum_nonneg fun x _ => sq_nonneg (h x)) hΛ hQ
  refine hnorm.trans ?_
  -- the witness factors
  set DV := ∏ v ∈ V, ℓX v
  set DW := ∏ v ∈ W, ℓZ v
  have hDV : q ^ k * (2 : ℝ)⁻¹ ^ tV * (1 - ehat) ^ k ≤ DV := by
    have : ∏ v ∈ V, (q * (2 : ℝ)⁻¹ ^ ordT G ordX v * (1 - ehat)) ≤ DV := by
      refine prod_le_prod₀ (fun v _ => ?_) (fun v _ => ?_)
      · exact mul_nonneg (mul_nonneg hq0.le (by positivity)) (by linarith)
      · simp only [ℓX, stepLow]
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hq0.le (by positivity))
        linarith [coarseError_ordT_le G hehat ordX v]
    refine le_trans (le_of_eq ?_) this
    rw [prod_mul_distrib, prod_mul_distrib, prod_const, prod_const, hVk, prod_pow_eq_pow_sum]
  have hDW : q ^ k * (2 : ℝ)⁻¹ ^ tW * (1 - ehat) ^ k ≤ DW := by
    have : ∏ v ∈ W, (q * (2 : ℝ)⁻¹ ^ ordT G ordZ v * (1 - ehat)) ≤ DW := by
      refine prod_le_prod₀ (fun v _ => ?_) (fun v _ => ?_)
      · exact mul_nonneg (mul_nonneg hq0.le (by positivity)) (by linarith)
      · simp only [ℓZ, stepLow]
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hq0.le (by positivity))
        linarith [coarseError_ordT_le G hehat ordZ v]
    refine le_trans (le_of_eq ?_) this
    rw [prod_mul_distrib, prod_mul_distrib, prod_const, prod_const, hWk, prod_pow_eq_pow_sum]
  have h1e : 0 < 1 - ehat := by linarith
  have hdV0 : 0 < q ^ k * (2 : ℝ)⁻¹ ^ tV * (1 - ehat) ^ k := by positivity
  have hdW0 : 0 < q ^ k * (2 : ℝ)⁻¹ ^ tW * (1 - ehat) ^ k := by positivity
  -- `A B = 2^{f_V + f_W} ∏ F · L_X L_Z / (D_V D_W)`
  set PF := PUx * PCz * PUz * PCx
  have hPF0 : 0 ≤ PF := mul_nonneg (mul_nonneg (mul_nonneg hPUx0 hPCz0) hPUz0) hPCx0
  have hsplitX : ∏ v, ℓX v = (∏ v ∈ Ux, ℓX v) * DV * ∏ v ∈ Cx, ℓX v :=
    prod_univ_three V Cx hVC ℓX
  have hsplitZ : ∏ v, ℓZ v = (∏ v ∈ Uz, ℓZ v) * DW * ∏ v ∈ Cz, ℓZ v :=
    prod_univ_three W Cz hWC ℓZ
  have hAB : A * B / ((∏ v, ℓX v) * ∏ v, ℓZ v) = 2 ^ fV * 2 ^ fW * PF / (DV * DW) := by
    rw [hsplitX, hsplitZ]
    have h1 : (0 : ℝ) < ∏ v ∈ Ux, ℓX v := prod_pos fun v _ => hℓpos ordX v
    have h2 : (0 : ℝ) < ∏ v ∈ Cx, ℓX v := prod_pos fun v _ => hℓpos ordX v
    have h3 : (0 : ℝ) < ∏ v ∈ Uz, ℓZ v := prod_pos fun v _ => hℓpos ordZ v
    have h4 : (0 : ℝ) < ∏ v ∈ Cz, ℓZ v := prod_pos fun v _ => hℓpos ordZ v
    have h5 : (0 : ℝ) < DV := prod_pos fun v _ => hℓpos ordX v
    have h6 : (0 : ℝ) < DW := prod_pos fun v _ => hℓpos ordZ v
    simp only [A, B, PF]
    field_simp
  rw [hAB]
  have hbound : 2 ^ fV * 2 ^ fW * PF / (DV * DW) ≤
      2 ^ fV * 2 ^ fW * PF / ((q ^ k * (2 : ℝ)⁻¹ ^ tV * (1 - ehat) ^ k) *
        (q ^ k * (2 : ℝ)⁻¹ ^ tW * (1 - ehat) ^ k)) :=
    div_le_div_of_nonneg_left (by positivity) (mul_pos hdV0 hdW0)
      (mul_le_mul hDV hDW hdW0.le (lt_of_lt_of_le hdV0 hDV).le)
  have hinv : ((Real.sqrt q)⁻¹ ^ k) ^ 2 = (q ^ k)⁻¹ := by
    rw [inv_pow, inv_pow, sqrt_pow_sq hq0.le]
  have hsq : (cker * Real.sqrt q ^ k) ^ 2 *
      (2 ^ fV * 2 ^ fW * PF / ((q ^ k * (2 : ℝ)⁻¹ ^ tV * (1 - ehat) ^ k) *
        (q ^ k * (2 : ℝ)⁻¹ ^ tW * (1 - ehat) ^ k))) =
      (cker * (Real.sqrt q)⁻¹ ^ k / (1 - ehat) ^ k) ^ 2 * (2 ^ (fV + fW + tV + tW) * PF) := by
    have e1 : (cker * Real.sqrt q ^ k) ^ 2 = cker ^ 2 * q ^ k := by
      rw [mul_pow, sqrt_pow_sq hq0.le]
    have e2 : (cker * (Real.sqrt q)⁻¹ ^ k / (1 - ehat) ^ k) ^ 2 =
        cker ^ 2 * (q ^ k)⁻¹ / ((1 - ehat) ^ k) ^ 2 := by
      rw [div_pow, mul_pow, hinv]
    rw [e1, e2]
    simp only [pow_add, inv_pow]
    have hq' : (q ^ k) ≠ 0 := by positivity
    have he' : (1 - ehat) ^ k ≠ 0 := by positivity
    field_simp
  have hc' : 0 ≤ cker * (Real.sqrt q)⁻¹ ^ k / (1 - ehat) ^ k := by positivity
  have hkey : cker * Real.sqrt q ^ k * Real.sqrt (2 ^ fV * 2 ^ fW * PF / (DV * DW)) ≤
      cker * (Real.sqrt q)⁻¹ ^ k * Real.sqrt (2 ^ (fV + fW + tV + tW) * PF) / (1 - ehat) ^ k := by
    calc cker * Real.sqrt q ^ k * Real.sqrt (2 ^ fV * 2 ^ fW * PF / (DV * DW))
        ≤ cker * Real.sqrt q ^ k * Real.sqrt (2 ^ fV * 2 ^ fW * PF /
            ((q ^ k * (2 : ℝ)⁻¹ ^ tV * (1 - ehat) ^ k) *
              (q ^ k * (2 : ℝ)⁻¹ ^ tW * (1 - ehat) ^ k))) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hbound) hΛ
      _ = Real.sqrt ((cker * Real.sqrt q ^ k) ^ 2 * (2 ^ fV * 2 ^ fW * PF /
            ((q ^ k * (2 : ℝ)⁻¹ ^ tV * (1 - ehat) ^ k) *
              (q ^ k * (2 : ℝ)⁻¹ ^ tW * (1 - ehat) ^ k)))) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hΛ]
      _ = Real.sqrt ((cker * (Real.sqrt q)⁻¹ ^ k / (1 - ehat) ^ k) ^ 2 *
            (2 ^ (fV + fW + tV + tW) * PF)) := by rw [hsq]
      _ = cker * (Real.sqrt q)⁻¹ ^ k / (1 - ehat) ^ k *
            Real.sqrt (2 ^ (fV + fW + tV + tW) * PF) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc']
      _ = _ := by ring
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkey (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

end PartH

/-! ## Part I: the statement for a class with a record -/

section PartI

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

open Sarkozy.Influence

/-- The witness set `V = {j_1, …, j_k}` of a witness `w` (`def:extraction:witness`(a)). -/
def witV {k : ℕ} (w : Fin k → U × U) : Finset U := univ.image fun i => (w i).1

/-- The witness set `W = {k_1, …, k_k}`. -/
def witW {k : ℕ} (w : Fin k → U × U) : Finset U := univ.image fun i => (w i).2

/-- The exponent `ex(𝒞) = t_V + t_W + f_V + f_W` of a record (`def:extraction:records`), with
`t_V` (`t_W`) the number of `G⁺`-neighbours of the vertices of `V` (`W`) earlier in the order of
the copy (`C_x` before `V`); this is `e(V) + e(V, C_x)` when `V` follows `C_x` and precedes the
other vertices (`cmp_sum_ordT` in `Compressed.lean`). -/
noncomputable def recordExp (G : OrientedGraph U) (Fr : Finset (U × U)) (V W : Finset U)
    (ordX ordZ : U → ℕ) : ℕ :=
  (Fr.filter (fun e => e.1 ∈ V)).card + (Fr.filter (fun e => e.2 ∈ W)).card +
    ∑ v ∈ V, ordT G ordX v + ∑ v ∈ W, ordT G ordZ v

/-- The product `∏_v F_v` of the `2(n - k)` vertex factors of a record
(`def:extraction:records`): `F_u` over `U_x` and `U_z`, `F_b` over `C_z` and `C_x`. The factors of
`U_z` and `C_x` are those of the transposed record (Step 8), i.e. with `H_u = {a : (a, u) ∈ F}`
and `H_a = {b : (a, b) ∈ F}`. -/
noncomputable def recordFactor (G : OrientedGraph U) (ς : U → U → ℤ) (q : ℝ) (n : ℕ)
    (Fr : Finset (U × U)) (V W Cx Cz : Finset U) (ordX ordZ : U → ℕ) : ℝ :=
  (∏ u ∈ univ \ (V ∪ Cx), intF G ς q n ordX Fr Cz u) *
    (∏ b ∈ Cz, coverRowF G ς q n Cz ordZ (Fr.filter (fun e => e.2 ∈ Cz)) b) *
    (∏ u ∈ univ \ (W ∪ Cz), intF G ς q n ordZ (Fr.image Prod.swap) Cx u) *
    ∏ b ∈ Cx, coverRowF G ς q n Cx ordX ((Fr.image Prod.swap).filter (fun e => e.2 ∈ Cx)) b

/-- The completion ratio `R̃_U = ∏_{u ∈ U} (1 + e_{t_u}(q, n))/(1 - e_{t_u}(q, n))` of an
integrated set, `t_u` its actual insertion degree. -/
noncomputable def ratioTilde (G : OrientedGraph U) (q : ℝ) (n : ℕ) (ord : U → ℕ) (S : Finset U) :
    ℝ :=
  ∏ u ∈ S, (1 + coarseError (ordT G ord u) q n) / (1 - coarseError (ordT G ord u) q n)

theorem ratioTilde_ge_one (G : OrientedGraph U) {q : ℝ} {n : ℕ} (ord : U → ℕ) (S : Finset U)
    (he : ∀ u, coarseError (ordT G ord u) q n < 1) : 1 ≤ ratioTilde G q n ord S := by
  unfold ratioTilde
  refine one_le_prod₀ fun u _ => ?_
  have h0 := coarseError_nonneg (q := q) (Nat.cast_nonneg n) (ordT G ord u)
  have h1 := he u
  rw [one_le_div (by linarith)]
  linarith

/-- The bilinear form of `T_𝒞 = ∑_{S ∈ 𝒞} T_S` on `L²(μ)`, `μ = λ_p(G⁺)`:
`∑_{S ∈ 𝒞} ⟨f, T_S h⟩_μ = E_{x ∼ μ}[f(x) E_{x' ∼ μ}[(∑_{S ∈ 𝒞} χ_S(x, x')) h(x')]]`. -/
theorem classForm_eq (G : OrientedGraph U) (hne : (injLabellings F G).Nonempty)
    (ς : U → U → ℤ) (Ex P A : Finset (U × U)) (hP : P ⊆ Ex) (hPA : Disjoint P A)
    (f h : (U → F) → ℝ) :
    (graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
        (∑ S ∈ cls Ex P A, ∏ e ∈ S, chiPair ς e x x') * h x')) =
      (∑ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G,
        f x * classKer ς P (Ex \ (P ∪ A)) x x' * h x') / ((injLabellings F G).card : ℝ) ^ 2 := by
  have hN : ((injLabellings F G).card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hne).ne'
  rw [coverRow_expect_graphLaw]
  simp_rw [coverRow_expect_graphLaw, sum_cls_eq_classKer ς Ex P A hP hPA]
  rw [pow_two, ← div_div]
  congr 1
  rw [eq_div_iff hN, sum_mul]
  refine sum_congr rfl fun x _ => ?_
  have e : f x * ((∑ x' ∈ injLabellings F G, classKer ς P (Ex \ (P ∪ A)) x x' * h x') /
      ((injLabellings F G).card : ℝ)) * ((injLabellings F G).card : ℝ) =
      f x * ∑ x' ∈ injLabellings F G, classKer ς P (Ex \ (P ∪ A)) x x' * h x' := by
    field_simp
  rw [e, mul_sum]
  exact sum_congr rfl fun x' _ => by ring

/-- **`lem:matching:extractionk` (Grouped extraction with a witness of size `k`).** Assume
`e_{d⁰_i}(q, n) ≤ ê < 1` for every vertex (from (S1) at `p`; `n ≥ |U⁺|`). Let `𝒞 = 𝒞(P, A)` be a
class of the cross pairs `E_× ⊇ Ex` with a record: a witness `w` of size `k` (`IsWitness`,
(W_k)), a cover `(C_x, C_z)` (`IsCover`, (VC_k)), and orders `ordX`, `ordZ` of the two copies
in which the cover comes first and the integrated set `U_x` (`U_z`) last (any order of `V`, `W`
in between). Suppose the kernel `𝖶` of the present rectangle pairs, compressed to injective
tuples, has `ℓ²` norm at most `c_ker √q^k` (`c_ker r^k` for uniform probability; by
`lem:matching:kernel`, `c_ker = 2^{β(𝒞)}`, see `KernelBridge.lean`). Then for all `f, h`
`|∑_{S ∈ 𝒞} ⟨f, T_S h⟩_μ| ≤ c_ker r^k 2^{ex(𝒞)/2} (∏_v F_v)^{1/2} (1 - ê)^{-k} ‖f‖_μ ‖h‖_μ`.
This is the paper's bound without its factor `(R̃_{U_x} R̃_{U_z})^{1/2} ≥ 1`
(`grouped_extraction_paper` states it with that factor). The antisymmetry `ς_{kj} = -ς_{jk}`
(`lem:spec:elementary`) is used in Step 8 only. Literature input: `WeilBound F`. -/
theorem grouped_extraction (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n) {ehat : ℝ}
    (hehat : ∀ i, coarseError (rowsDeg0 G i) (Fintype.card F) n ≤ ehat) (hehat1 : ehat < 1)
    (Ex P A : Finset (U × U)) (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0) (hcls : IsClassDatum Ex (P, A))
    {k : ℕ} (w : Fin k → U × U) (hw : IsWitness Ex P A w) (Cx Cz : Finset U)
    (hcov : IsCover Ex P A w Cx Cz) (ordX ordZ : U → ℕ) (hordX : Function.Injective ordX)
    (hordZ : Function.Injective ordZ) (hX0 : ∀ a ∈ Cx, ∀ b, b ∉ Cx → ordX a < ordX b)
    (hZ0 : ∀ a ∈ Cz, ∀ b, b ∉ Cz → ordZ a < ordZ b)
    (hX1 : ∀ a, a ∉ univ \ (witV w ∪ Cx) → ∀ b ∈ univ \ (witV w ∪ Cx), ordX a < ordX b)
    (hZ1 : ∀ a, a ∉ univ \ (witW w ∪ Cz) → ∀ b ∈ univ \ (witW w ∪ Cz), ordZ a < ordZ b)
    {cker : ℝ} (hcker : 0 ≤ cker)
    (hker : OpBound (injTuples F (witV w)) (injTuples F (witW w)) (rectKer ς P (witV w) (witW w))
      (cker * Real.sqrt (Fintype.card F) ^ k))
    (f h : (U → F) → ℝ) :
    |(graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
        (∑ S ∈ cls Ex P A, ∏ e ∈ S, chiPair ς e x x') * h x'))| ≤
      cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        Real.sqrt (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
          recordFactor G ς (Fintype.card F) n (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) /
        (1 - ehat) ^ k *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by
  obtain ⟨hP, -, hPA⟩ := hcls
  rw [classForm_eq G hne ς Ex P A hP hPA, coverRow_expect_graphLaw, coverRow_expect_graphLaw]
  set Fr := Ex \ (P ∪ A) with hFr
  have hrect : ∀ e : U × U, e.1 ∈ witV w ∧ e.2 ∈ witW w ↔
      (∃ i, (w i).1 = e.1) ∧ ∃ l, (w l).2 = e.2 := by
    intro e
    simp [witV, witW]
  have hFrEx : ∀ e ∈ Fr, e ∈ Ex := fun e he => (mem_sdiff.mp he).1
  have hP' : ∀ e ∈ P, (e.1 ∈ witV w ∧ e.2 ∈ witW w) ∨ e.1 ∈ Cx ∨ e.2 ∈ Cz := by
    intro e he
    by_cases hr : e.1 ∈ witV w ∧ e.2 ∈ witW w
    · exact Or.inl hr
    · exact Or.inr (hcov.cover e (mem_union_left _ he) (by rwa [← hrect]))
  have hFr' : ∀ e ∈ Fr, e.1 ∈ Cx ∨ e.2 ∈ Cz := by
    intro e he
    refine hcov.cover e (mem_union_right _ he) fun hr => ?_
    have := hw.decided e (hFrEx e he) hr.1 hr.2
    exact (mem_sdiff.mp he).2 (mem_union.mpr this)
  have hVC : ∀ u ∈ witV w, u ∉ Cx := by
    intro u hu
    obtain ⟨i, -, rfl⟩ := mem_image.mp hu
    exact hcov.fst_not_mem i
  have hWC : ∀ u ∈ witW w, u ∉ Cz := by
    intro u hu
    obtain ⟨i, -, rfl⟩ := mem_image.mp hu
    exact hcov.snd_not_mem i
  have hVk : (witV w).card = k := by
    unfold witV
    rw [card_image_of_injective _ hw.injective_fst, card_univ, Fintype.card_fin]
  have hWk : (witW w).card = k := by
    unfold witW
    rw [card_image_of_injective _ hw.injective_snd, card_univ, Fintype.card_fin]
  exact grouped_extraction_sum_le hW G ς hς hanti hn hehat hehat1 P Fr
    (fun e he => hEx e (hFrEx e he)) (witV w) (witW w) Cx Cz hVk hWk hVC hWC hP' hFr' ordX ordZ
    hordX hordZ hX0 hZ0 hX1 hZ1 hcker hker f h

/-- **`lem:matching:extractionk`, the paper's form**: the bound of `grouped_extraction` with the
factor `(R̃_{U_x} R̃_{U_z})^{1/2}`, which is at least one. -/
theorem grouped_extraction_paper (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n) {ehat : ℝ}
    (hehat : ∀ i, coarseError (rowsDeg0 G i) (Fintype.card F) n ≤ ehat) (hehat1 : ehat < 1)
    (Ex P A : Finset (U × U)) (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0) (hcls : IsClassDatum Ex (P, A))
    {k : ℕ} (w : Fin k → U × U) (hw : IsWitness Ex P A w) (Cx Cz : Finset U)
    (hcov : IsCover Ex P A w Cx Cz) (ordX ordZ : U → ℕ) (hordX : Function.Injective ordX)
    (hordZ : Function.Injective ordZ) (hX0 : ∀ a ∈ Cx, ∀ b, b ∉ Cx → ordX a < ordX b)
    (hZ0 : ∀ a ∈ Cz, ∀ b, b ∉ Cz → ordZ a < ordZ b)
    (hX1 : ∀ a, a ∉ univ \ (witV w ∪ Cx) → ∀ b ∈ univ \ (witV w ∪ Cx), ordX a < ordX b)
    (hZ1 : ∀ a, a ∉ univ \ (witW w ∪ Cz) → ∀ b ∈ univ \ (witW w ∪ Cz), ordZ a < ordZ b)
    {cker : ℝ} (hcker : 0 ≤ cker)
    (hker : OpBound (injTuples F (witV w)) (injTuples F (witW w)) (rectKer ς P (witV w) (witW w))
      (cker * Real.sqrt (Fintype.card F) ^ k))
    (f h : (U → F) → ℝ) :
    |(graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
        (∑ S ∈ cls Ex P A, ∏ e ∈ S, chiPair ς e x x') * h x'))| ≤
      cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        Real.sqrt (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ) *
        Real.sqrt (ratioTilde G (Fintype.card F) n ordX (univ \ (witV w ∪ Cx)) *
          ratioTilde G (Fintype.card F) n ordZ (univ \ (witW w ∪ Cz))) / (1 - ehat) ^ k *
        Real.sqrt (recordFactor G ς (Fintype.card F) n (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz
          ordX ordZ) *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by
  refine (grouped_extraction hW G ς hς hanti hne hn hehat hehat1 Ex P A hEx hcls w hw Cx Cz hcov
    ordX ordZ hordX hordZ hX0 hZ0 hX1 hZ1 hcker hker f h).trans ?_
  have he : ∀ ord u, coarseError (ordT G ord u) (Fintype.card F) n < 1 := fun ord u =>
    lt_of_le_of_lt (coarseError_ordT_le G hehat ord u) hehat1
  have hR : 1 ≤ Real.sqrt (ratioTilde G (Fintype.card F) n ordX (univ \ (witV w ∪ Cx)) *
      ratioTilde G (Fintype.card F) n ordZ (univ \ (witW w ∪ Cz))) := by
    rw [Real.one_le_sqrt]
    exact one_le_mul_of_one_le_of_one_le (ratioTilde_ge_one G ordX _ (he ordX))
      (ratioTilde_ge_one G ordZ _ (he ordZ))
  have h1e : 0 < 1 - ehat := by linarith
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w)
    ordX ordZ)]
  set X := cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
      Real.sqrt (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ) *
      Real.sqrt (recordFactor G ς (Fintype.card F) n (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz
        ordX ordZ) / (1 - ehat) ^ k *
      Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
      Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) with hXdef
  have hX : 0 ≤ X := by positivity
  calc _ = X := by rw [hXdef]; ring
    _ ≤ X * Real.sqrt (ratioTilde G (Fintype.card F) n ordX (univ \ (witV w ∪ Cx)) *
          ratioTilde G (Fintype.card F) n ordZ (univ \ (witW w ∪ Cz))) :=
        le_mul_of_one_le_right hX hR
    _ = _ := by rw [hXdef]; ring

end PartI


end Sarkozy.ExtractionK
