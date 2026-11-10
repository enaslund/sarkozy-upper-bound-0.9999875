module

public import Sarkozy.PartVRecords.Mixture

@[expose] public section

/-!
# Merge records and their designated edges (`def:merge-records`)

`paper/sections/21_middle_records.tex`, `subsec:merge-repair`, `def:merge-records`,
`tab:merge-records`, and the first sentence of `lem:merge-repair`.

At a prime `p ≡ 3 (mod 4)`, the two-layer merge record `π_{sk}` reads only the objects `0, 1` of
the `E` law: a configuration is a four-label tuple `(x₀, x₁, y₀, y₁)`, `x_a`, `y_a` the labels of
object `a` in layers `0` and `1` (here `z : Fin 2 × Fin 2 → F`, `x_a = z(a, 0)`, `y_a = z(a, 1)`),
uniform on the injective tuples (`mergeRecordLaw`, the graph law of the edgeless graph
`emptyGraph4`). Through `G_{sk}` every query of `𝓔₆` reads the **designated pair**
`x_{G_{sk}(0)} → y_{G_{sk}(2)}` (`designated`, `mergeEmission_query`).

The replacements (`mergeRepLaw`):
* for `(s, k) ∈ {(0,0), (0,1), (1,0), (1,1)}`: the uniform injective four-label law satisfying the
  two mirror edges `x₁ → y₀` and `x₀ → y₁` (`mirrorLaw`, the graph law of `mirrorGraph`);
* for `(s, k) ∈ {(0,2), (1,2)}`: the law with density `2/(1 - 1/p) · 1[x₀ → y₀]` relative to
  `m_p ⊗ m_p`, `m_p` the uniform law on ordered distinct pairs (`firstLaw`); it allows
  coincidences between the two halves, each half being an ordered distinct pair.
Block replacements are products over the primes (`blockMergeRepLaw`).

**Proved:** the designated pairs of `tab:merge-records` (`designated_table`, by `decide`); the
first-coordinate law is a probability law (`firstLaw`, mass from the Paley out-degree
`(q - 1)/2`); its half marginals at `ι` are `m_p` (`firstLaw_half0`, `firstLaw_half1`); both
replacements are invariant under the maps `z ↦ αz + β`, `χ(α) = 1` (`mirrorLaw_affine`,
`firstLaw_affine`); and **the replacement records accept every query of `𝓔₆`**, at one prime and
on a block (`mergeRep_accepts`, `blockMergeRep_accepts`).

**Not proved here:** the half marginals of the mirror-edge law (`lem:merge-repair`: both actual
half marginals `m_p`, from the Paley counts), the uniformity of the queried pairs, and the norm
bounds of `lem:merge-repair`.
-/

namespace Sarkozy.PartVRecords

open Finset Sarkozy.Labellings Sarkozy.PartV Sarkozy.TraceMixing

/-! ## The graphs and the designated edges -/

/-- The edgeless graph on the four labels `(a, ℓ) ∈ {0, 1} × {0, 1}` (the merge record reads the
objects `0, 1` of the edgeless `E` graph). -/
def emptyGraph4 : OrientedGraph (Fin 2 × Fin 2) where
  E := ∅
  loopless _ := Finset.notMem_empty _
  oriented _ _ h := absurd h (Finset.notMem_empty _)

/-- The two mirror edges `x₁ → y₀` and `x₀ → y₁`: `(1, 0) → (0, 1)` and `(0, 0) → (1, 1)`. -/
def mirrorGraph : OrientedGraph (Fin 2 × Fin 2) where
  E := {((1, 0), (0, 1)), ((0, 0), (1, 1))}
  loopless u := by revert u; decide
  oriented u v := by revert u v; decide

/-- The emission of the merge `G_{sk}`: the slot `(u₀, u₁, ℓ)` reads the object `G_{sk}(u₀)` at the
layer `ℓ`. -/
def mergeEmission (s : Fin 2) (k : Fin 3) (v : Slot) : Fin 2 × Fin 2 :=
  (merge s k v.1, layerFin v.2.2)

/-- **The designated pair** `(x_{G_{sk}(0)}, y_{G_{sk}(2)})` of the merge `G_{sk}`. -/
def designated (s : Fin 2) (k : Fin 3) : (Fin 2 × Fin 2) × (Fin 2 × Fin 2) :=
  ((merge s k 0, 0), (merge s k 2, 1))

/-- Every query `(0, j, 0) → (2, rot j, 1)` of `𝓔₆` reads the designated pair. -/
theorem mergeEmission_query (s : Fin 2) (k : Fin 3) (j : Chamber) :
    (mergeEmission s k (querySource j), mergeEmission s k (queryTarget j)) = designated s k := by
  revert s k j
  decide

/-- **`tab:merge-records`**: `G₀₀`, `G₁₀` designate `x₁ → y₀`; `G₀₁`, `G₁₁` designate `x₀ → y₁`;
`G₀₂`, `G₁₂` designate `x₀ → y₀`. The first four are edges of `mirrorGraph`. -/
theorem designated_table :
    designated 0 0 = ((1, 0), (0, 1)) ∧ designated 1 0 = ((1, 0), (0, 1)) ∧
      designated 0 1 = ((0, 0), (1, 1)) ∧ designated 1 1 = ((0, 0), (1, 1)) ∧
      designated 0 2 = ((0, 0), (0, 1)) ∧ designated 1 2 = ((0, 0), (0, 1)) := by
  decide

/-- The mirror merges `(s, k)`, `k ≠ 2`, designate an edge of `mirrorGraph`. -/
theorem designated_mem_mirror (s : Fin 2) (k : Fin 3) (hk : k ≠ 2) :
    designated s k ∈ mirrorGraph.E := by
  revert s k
  decide

section OnePrime

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

/-- **The two-layer merge record** at one prime: uniform on the injective four-label tuples. -/
noncomputable def mergeRecordLaw (hne : (injLabellings F emptyGraph4).Nonempty) :
    FiniteLaw (Fin 2 × Fin 2 → F) :=
  graphLaw emptyGraph4 hne

/-- **The mirror-edge replacement**: uniform on the injective four-label tuples with `x₁ → y₀` and
`x₀ → y₁`. -/
noncomputable def mirrorLaw (hne : (injLabellings F mirrorGraph).Nonempty) :
    FiniteLaw (Fin 2 × Fin 2 → F) :=
  graphLaw mirrorGraph hne

/-- The configuration of a quadruple `(x₀, x₁, y₀, y₁)`. -/
def quadConfig (t : F × F × F × F) : Fin 2 × Fin 2 → F := fun o =>
  if o.2 = 0 then (if o.1 = 0 then t.1 else t.2.1) else (if o.1 = 0 then t.2.2.1 else t.2.2.2)

/-- The weight `2/(1 - 1/q) · [x₀ ≠ x₁] [y₀ ≠ y₁] [x₀ → y₀] / (q(q - 1))²` of the first-coordinate
replacement (density `2/(1 - 1/q) 1[x₀ → y₀]` relative to `m_q ⊗ m_q`). -/
noncomputable def firstWeight (t : F × F × F × F) : ℝ :=
  2 / (1 - 1 / (Fintype.card F : ℝ)) *
    ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1))⁻¹ ^ 2 *
    ((if t.1 = t.2.1 then 0 else 1) * (if t.2.2.1 = t.2.2.2 then 0 else 1) *
      (if χ (t.2.2.1 - t.1) = 1 then 1 else 0))

theorem sum_out_indicator (hF : ringChar F ≠ 2) (a : F) :
    ∑ b : F, (if χ (b - a) = 1 then (1 : ℝ) else 0) = ((Fintype.card F : ℝ) - 1) / 2 := by
  rw [sum_boole]
  have h := card_out hF a
  have : (2 : ℝ) * ((univ.filter fun b => χ (b - a) = 1).card : ℝ) = (Fintype.card F : ℝ) - 1 := by
    exact_mod_cast h
  linarith

variable (F) in
/-- **The first-coordinate replacement** at one prime, on quadruples `(x₀, x₁, y₀, y₁)`. -/
noncomputable def firstQuadLaw (hF : ringChar F ≠ 2) : FiniteLaw (F × F × F × F) where
  weight := firstWeight
  nonneg t := by
    unfold firstWeight
    have hq := card_gt_one_real (F := F)
    have h1 : 0 < 1 - 1 / (Fintype.card F : ℝ) := by
      rw [sub_pos, div_lt_one (by linarith)]
      exact hq
    refine mul_nonneg (mul_nonneg (div_nonneg (by norm_num) h1.le) (sq_nonneg _)) ?_
    refine mul_nonneg (mul_nonneg ?_ ?_) ?_ <;> split_ifs <;> norm_num
  total := by
    unfold firstWeight
    rw [← mul_sum]
    have hq := card_gt_one_real (F := F)
    have hsum : ∑ t : F × F × F × F, ((if t.1 = t.2.1 then (0 : ℝ) else 1) *
        (if t.2.2.1 = t.2.2.2 then 0 else 1) * (if χ (t.2.2.1 - t.1) = 1 then 1 else 0)) =
        (Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1) * (((Fintype.card F : ℝ) - 1) / 2) *
          ((Fintype.card F : ℝ) - 1) := by
      simp only [Fintype.sum_prod_type]
      have h1 : ∀ x₀ x₁ y₀ : F, ∑ y₁ : F, ((if x₀ = x₁ then (0 : ℝ) else 1) *
          (if y₀ = y₁ then 0 else 1) * (if χ (y₀ - x₀) = 1 then 1 else 0)) =
          (if x₀ = x₁ then (0 : ℝ) else 1) * (if χ (y₀ - x₀) = 1 then 1 else 0) *
            ((Fintype.card F : ℝ) - 1) := by
        intro x₀ x₁ y₀
        rw [← sum_ite_eq_zero_one y₀, mul_sum]
        exact sum_congr rfl fun y₁ _ => by ring
      simp only [h1]
      have h2 : ∀ x₀ x₁ : F, ∑ y₀ : F, ((if x₀ = x₁ then (0 : ℝ) else 1) *
          (if χ (y₀ - x₀) = 1 then 1 else 0) * ((Fintype.card F : ℝ) - 1)) =
          (if x₀ = x₁ then (0 : ℝ) else 1) * (((Fintype.card F : ℝ) - 1) / 2) *
            ((Fintype.card F : ℝ) - 1) := by
        intro x₀ x₁
        rw [← sum_out_indicator hF x₀, mul_sum, sum_mul]
      simp only [h2]
      have h3 : ∀ x₀ : F, ∑ x₁ : F, ((if x₀ = x₁ then (0 : ℝ) else 1) *
          (((Fintype.card F : ℝ) - 1) / 2) * ((Fintype.card F : ℝ) - 1)) =
          ((Fintype.card F : ℝ) - 1) * (((Fintype.card F : ℝ) - 1) / 2) *
            ((Fintype.card F : ℝ) - 1) := by
        intro x₀
        rw [← sum_ite_eq_zero_one x₀, sum_mul, sum_mul]
      simp only [h3, sum_const, card_univ, nsmul_eq_mul]
      ring
    rw [hsum]
    have hq0 : (Fintype.card F : ℝ) ≠ 0 := by linarith
    have hq1 : (Fintype.card F : ℝ) - 1 ≠ 0 := by linarith
    field_simp

variable (F) in
/-- **The first-coordinate replacement law** on the four labels. -/
noncomputable def firstLaw (hF : ringChar F ≠ 2) : FiniteLaw (Fin 2 × Fin 2 → F) :=
  (firstQuadLaw F hF).map quadConfig

omit [Field F] [Fintype F] [DecidableEq F] in
theorem quadConfig_apply (t : F × F × F × F) :
    quadConfig t (0, 0) = t.1 ∧ quadConfig t (1, 0) = t.2.1 ∧ quadConfig t (0, 1) = t.2.2.1 ∧
      quadConfig t (1, 1) = t.2.2.2 := by
  simp [quadConfig]

/-- **Support of the first-coordinate replacement**: `x₀ → y₀`, `x₀ ≠ x₁`, `y₀ ≠ y₁`. -/
theorem firstLaw_support (hF : ringChar F ≠ 2) {z : Fin 2 × Fin 2 → F}
    (hz : (firstLaw F hF).weight z ≠ 0) :
    χ (z (0, 1) - z (0, 0)) = 1 ∧ z (0, 0) ≠ z (1, 0) ∧ z (0, 1) ≠ z (1, 1) := by
  unfold firstLaw FiniteLaw.map at hz
  obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  split_ifs at ht with hzt
  · subst hzt
    change firstWeight t ≠ 0 at ht
    obtain ⟨e00, e10, e01, e11⟩ := quadConfig_apply t
    rw [e00, e10, e01, e11]
    unfold firstWeight at ht
    have hind := right_ne_zero_of_mul ht
    refine ⟨?_, ?_, ?_⟩
    · by_contra h
      apply hind
      simp only [h, ↓reduceIte, mul_zero]
    · intro h
      apply hind
      simp only [h, ↓reduceIte, zero_mul]
    · intro h
      apply hind
      simp only [h, ↓reduceIte, zero_mul, mul_zero]
  · exact absurd rfl ht

theorem expect_firstLaw (hF : ringChar F ≠ 2) (H : (Fin 2 × Fin 2 → F) → ℝ) :
    (firstLaw F hF).expect H = ∑ t, firstWeight t * H (quadConfig t) := by
  unfold firstLaw
  rw [FiniteLaw.expect_map]
  rfl

theorem firstWeight_split (t : F × F × F × F) :
    firstWeight t = 2 / (1 - 1 / (Fintype.card F : ℝ)) *
      ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1))⁻¹ ^ 2 *
      (if t.1 = t.2.1 then 0 else 1) * (if t.2.2.1 = t.2.2.2 then 0 else 1) *
      (if χ (t.2.2.1 - t.1) = 1 then 1 else 0) := by
  unfold firstWeight
  ring

/-- The weight of the layer-`0` pair `(x₀, x₁) = (a, a')`: `[a ≠ a']/(q(q - 1))`. -/
theorem firstWeight_sum_layer1 (hF : ringChar F ≠ 2) (a a' : F) :
    ∑ y₀ : F, ∑ y₁ : F, firstWeight (a, a', y₀, y₁) =
      ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1))⁻¹ * (if a = a' then 0 else 1) := by
  have hq := card_gt_one_real (F := F)
  have hq0 : (Fintype.card F : ℝ) ≠ 0 := by linarith
  have hq1 : (Fintype.card F : ℝ) - 1 ≠ 0 := by linarith
  set K := 2 / (1 - 1 / (Fintype.card F : ℝ)) *
    ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1))⁻¹ ^ 2 with hK
  have e1 : ∀ y₀ : F, ∑ y₁ : F, firstWeight (a, a', y₀, y₁) =
      K * (if a = a' then 0 else 1) * (if χ (y₀ - a) = 1 then 1 else 0) *
        ((Fintype.card F : ℝ) - 1) := by
    intro y₀
    have hB := sum_ite_eq_zero_one y₀
    calc ∑ y₁ : F, firstWeight (a, a', y₀, y₁)
        = ∑ y₁ : F, K * (if a = a' then 0 else 1) * (if χ (y₀ - a) = 1 then 1 else 0) *
            (if y₀ = y₁ then (0 : ℝ) else 1) := by
          refine sum_congr rfl fun y₁ _ => ?_
          rw [firstWeight_split]
          ring
      _ = _ := by rw [← mul_sum, hB]
  simp only [e1]
  rw [← sum_mul, ← mul_sum, sum_out_indicator hF a]
  rw [hK]
  split_ifs
  · ring
  · field_simp

/-- The weight of the layer-`1` pair `(y₀, y₁) = (c, c')`: `[c ≠ c']/(q(q - 1))` (the in-degree of
`c` is `(q - 1)/2`). -/
theorem firstWeight_sum_layer0 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (c c' : F) :
    ∑ x₀ : F, ∑ x₁ : F, firstWeight (x₀, x₁, c, c') =
      ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1))⁻¹ * (if c = c' then 0 else 1) := by
  have hq := card_gt_one_real (F := F)
  have hq0 : (Fintype.card F : ℝ) ≠ 0 := by linarith
  have hq1 : (Fintype.card F : ℝ) - 1 ≠ 0 := by linarith
  have hcol : ∑ x₀ : F, (if χ (c - x₀) = 1 then (1 : ℝ) else 0) =
      ((Fintype.card F : ℝ) - 1) / 2 := by
    rw [sum_boole]
    have h := card_in hF h3 c
    have : (2 : ℝ) * ((univ.filter fun b => χ (c - b) = 1).card : ℝ) =
        (Fintype.card F : ℝ) - 1 := by exact_mod_cast h
    linarith
  set K := 2 / (1 - 1 / (Fintype.card F : ℝ)) *
    ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1))⁻¹ ^ 2 with hK
  have e1 : ∀ x₀ : F, ∑ x₁ : F, firstWeight (x₀, x₁, c, c') =
      K * (if c = c' then 0 else 1) * (if χ (c - x₀) = 1 then 1 else 0) *
        ((Fintype.card F : ℝ) - 1) := by
    intro x₀
    have hB := sum_ite_eq_zero_one x₀
    calc ∑ x₁ : F, firstWeight (x₀, x₁, c, c')
        = ∑ x₁ : F, K * (if c = c' then 0 else 1) * (if χ (c - x₀) = 1 then 1 else 0) *
            (if x₀ = x₁ then (0 : ℝ) else 1) := by
          refine sum_congr rfl fun x₁ _ => ?_
          rw [firstWeight_split]
          ring
      _ = _ := by rw [← mul_sum, hB]
  simp only [e1]
  rw [← sum_mul, ← mul_sum, hcol]
  rw [hK]
  split_ifs
  · ring
  · field_simp

/-- **The half marginal on layer `0`** of the first-coordinate replacement is `m_q`:
`P(x₀ = a, x₁ = a') = [a ≠ a']/(q(q - 1))`. -/
theorem firstLaw_half0 (hF : ringChar F ≠ 2) (g : F → F → ℝ) :
    (firstLaw F hF).expect (fun z => g (z (0, 0)) (z (1, 0))) =
      ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1))⁻¹ *
        ∑ a, ∑ a', if a = a' then 0 else g a a' := by
  rw [expect_firstLaw]
  simp only [Fintype.sum_prod_type, (quadConfig_apply _).1, (quadConfig_apply _).2.1]
  rw [mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun a' _ => ?_
  have e : ∑ y₀ : F, ∑ y₁ : F, firstWeight (a, a', y₀, y₁) * g a a' =
      (∑ y₀ : F, ∑ y₁ : F, firstWeight (a, a', y₀, y₁)) * g a a' := by
    rw [sum_mul]
    exact sum_congr rfl fun y₀ _ => by rw [sum_mul]
  rw [e, firstWeight_sum_layer1 hF a a']
  split_ifs <;> ring

/-- **The half marginal on layer `1`** of the first-coordinate replacement is `m_q`:
`P(y₀ = c, y₁ = c') = [c ≠ c']/(q(q - 1))`. -/
theorem firstLaw_half1 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (g : F → F → ℝ) :
    (firstLaw F hF).expect (fun z => g (z (0, 1)) (z (1, 1))) =
      ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1))⁻¹ *
        ∑ c, ∑ c', if c = c' then 0 else g c c' := by
  rw [expect_firstLaw]
  simp only [Fintype.sum_prod_type, (quadConfig_apply _).2.2.1, (quadConfig_apply _).2.2.2]
  -- reorder `∑_{x₀} ∑_{x₁} ∑_c ∑_{c'}` to `∑_c ∑_{c'} ∑_{x₀} ∑_{x₁}`
  have r1 : ∀ x₀ : F, ∑ x₁ : F, ∑ c : F, ∑ c' : F, firstWeight (x₀, x₁, c, c') * g c c' =
      ∑ c : F, ∑ c' : F, ∑ x₁ : F, firstWeight (x₀, x₁, c, c') * g c c' := by
    intro x₀
    rw [sum_comm]
    exact sum_congr rfl fun c _ => sum_comm
  simp only [r1]
  rw [sum_comm]
  have r2 : ∀ c : F, ∑ x₀ : F, ∑ c' : F, ∑ x₁ : F, firstWeight (x₀, x₁, c, c') * g c c' =
      ∑ c' : F, ∑ x₀ : F, ∑ x₁ : F, firstWeight (x₀, x₁, c, c') * g c c' := fun c => sum_comm
  simp only [r2]
  rw [mul_sum]
  refine sum_congr rfl fun c _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun c' _ => ?_
  have e : ∑ x₀ : F, ∑ x₁ : F, firstWeight (x₀, x₁, c, c') * g c c' =
      (∑ x₀ : F, ∑ x₁ : F, firstWeight (x₀, x₁, c, c')) * g c c' := by
    rw [sum_mul]
    exact sum_congr rfl fun x₀ _ => by rw [sum_mul]
  rw [e, firstWeight_sum_layer0 hF h3 c c']
  split_ifs <;> ring

/-- **Invariance of the mirror-edge replacement** under `z ↦ αz + β`, `χ(α) = 1` (a graph law). -/
theorem mirrorLaw_affine (hne : (injLabellings F mirrorGraph).Nonempty) {α : F}
    (hα : χ α = 1) (β : F) (H : (Fin 2 × Fin 2 → F) → ℝ) :
    (mirrorLaw hne).expect (fun z => H (fun w => α * z w + β)) = (mirrorLaw hne).expect H :=
  graphLaw_expect_affine mirrorGraph hne hα β H

theorem firstWeight_affine {α : F} (hα : χ α = 1) (β : F) (t : F × F × F × F) :
    firstWeight (α * t.1 + β, α * t.2.1 + β, α * t.2.2.1 + β, α * t.2.2.2 + β) = firstWeight t := by
  have hα0 : α ≠ 0 := ne_zero_of_quadraticChar_eq_one hα
  have hχ : χ ((α * t.2.2.1 + β) - (α * t.1 + β)) = χ (t.2.2.1 - t.1) := by
    rw [show (α * t.2.2.1 + β) - (α * t.1 + β) = α * (t.2.2.1 - t.1) by ring, map_mul, hα,
      one_mul]
  have hne : ∀ x y : F, (α * x + β = α * y + β) ↔ x = y := fun x y =>
    ⟨fun e => mul_left_cancel₀ hα0 (add_right_cancel e), fun e => by rw [e]⟩
  unfold firstWeight
  simp only [hχ, hne]

/-- **Invariance of the first-coordinate replacement** under `z ↦ αz + β`, `χ(α) = 1`. -/
theorem firstLaw_affine (hF : ringChar F ≠ 2) {α : F} (hα : χ α = 1) (β : F)
    (H : (Fin 2 × Fin 2 → F) → ℝ) :
    (firstLaw F hF).expect (fun z => H (fun w => α * z w + β)) = (firstLaw F hF).expect H := by
  have hα0 : α ≠ 0 := ne_zero_of_quadraticChar_eq_one hα
  rw [expect_firstLaw, expect_firstLaw]
  let e : F ≃ F := ⟨fun x => α * x + β, fun x => α⁻¹ * (x - β), fun x => by
    simp only; field_simp; ring, fun x => by simp only; field_simp; ring⟩
  let E : F × F × F × F ≃ F × F × F × F :=
    Equiv.prodCongr e (Equiv.prodCongr e (Equiv.prodCongr e e))
  refine Fintype.sum_equiv E _ _ fun t => ?_
  have hc : (fun w => α * quadConfig t w + β) = quadConfig (E t) := by
    funext w
    obtain ⟨a, l⟩ := w
    fin_cases a <;> fin_cases l <;> rfl
  rw [hc]
  congr 1
  exact (firstWeight_affine hα β t).symm

/-- **The replacement law of the merge record `G_{sk}`** at one prime: the mirror-edge law for
`k ≠ 2`, the first-coordinate law for `k = 2`. -/
noncomputable def mergeRepLaw (hF : ringChar F ≠ 2) (hne : (injLabellings F mirrorGraph).Nonempty)
    (k : Fin 3) : FiniteLaw (Fin 2 × Fin 2 → F) :=
  if k = 2 then firstLaw F hF else mirrorLaw hne

/-- The designated edge holds on the support of the replacement of `G_{sk}`. -/
theorem mergeRepLaw_designated (hF : ringChar F ≠ 2)
    (hne : (injLabellings F mirrorGraph).Nonempty) (s : Fin 2) (k : Fin 3)
    {z : Fin 2 × Fin 2 → F} (hz : (mergeRepLaw hF hne k).weight z ≠ 0) :
    χ (z (designated s k).2 - z (designated s k).1) = 1 := by
  unfold mergeRepLaw at hz
  by_cases hk : k = 2
  · subst hk
    simp only [↓reduceIte] at hz
    have h := (firstLaw_support hF hz).1
    have hd : designated s 2 = ((0, 0), (0, 1)) := by revert s; decide
    rw [hd]
    exact h
  · simp only [hk, ↓reduceIte] at hz
    have hfeas := graphLaw_support mirrorGraph hne hz
    exact hfeas.2 _ (designated_mem_mirror s k hk) (mem_univ _) (mem_univ _)

/-- **The merge replacements accept every query of `𝓔₆`** (`lem:merge-repair`, at one prime). -/
theorem mergeRep_accepts (hF : ringChar F ≠ 2) (hne : (injLabellings F mirrorGraph).Nonempty)
    (s : Fin 2) (k : Fin 3) {z : Slot → F}
    (hz : (emit (mergeRepLaw hF hne k) (mergeEmission s k)).weight z ≠ 0) (j : Chamber) :
    χ (z (queryTarget j) - z (querySource j)) = 1 := by
  obtain ⟨y, hy, rfl⟩ := emit_support _ _ hz
  have hq := mergeEmission_query s k j
  have h1 : mergeEmission s k (querySource j) = (designated s k).1 := by rw [← hq]
  have h2 : mergeEmission s k (queryTarget j) = (designated s k).2 := by rw [← hq]
  simp only [Function.comp_apply, h1, h2]
  exact mergeRepLaw_designated hF hne s k hy

end OnePrime

/-! ## Block replacements -/

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- **The block replacement of `G_{sk}`**: the product over the primes of the block. -/
noncomputable def blockMergeRepLaw (hF : ∀ i, ringChar (ZMod (pr i)) ≠ 2)
    (hne : ∀ i, (injLabellings (ZMod (pr i)) mirrorGraph).Nonempty) (k : Fin 3) :
    FiniteLaw (Fin 2 × Fin 2 → BlockLabel pr) :=
  FiniteLaw.tensor fun i => mergeRepLaw (hF i) (hne i) k

/-- **The block merge replacements accept every query of `𝓔₆`**, at every prime of the block. -/
theorem blockMergeRep_accepts (hF : ∀ i, ringChar (ZMod (pr i)) ≠ 2)
    (hne : ∀ i, (injLabellings (ZMod (pr i)) mirrorGraph).Nonempty) (s : Fin 2) (k : Fin 3)
    {z : Slot → BlockLabel pr}
    (hz : (emit (blockMergeRepLaw pr hF hne k) (mergeEmission s k)).weight z ≠ 0) (j : Chamber)
    (i : ι) : quadraticChar (ZMod (pr i)) (z (queryTarget j) i - z (querySource j) i) = 1 := by
  obtain ⟨y, hy, rfl⟩ := emit_support _ _ hz
  unfold blockMergeRepLaw at hy
  rw [tensor_weight] at hy
  have hi := (Finset.prod_ne_zero_iff.mp hy) i (mem_univ _)
  have hq := mergeEmission_query s k j
  have h1 : mergeEmission s k (querySource j) = (designated s k).1 := by rw [← hq]
  have h2 : mergeEmission s k (queryTarget j) = (designated s k).2 := by rw [← hq]
  simp only [Function.comp_apply, h1, h2]
  exact mergeRepLaw_designated (hF i) (hne i) s k hi

end Block

end Sarkozy.PartVRecords
