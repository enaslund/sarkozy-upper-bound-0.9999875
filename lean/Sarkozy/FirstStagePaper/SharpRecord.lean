module

public import Sarkozy.FirstStagePaper.MiddleStage
public import Sarkozy.PartVRecords.OneStageMarginals

@[expose] public section

/-!
# The sharp bound of the one-stage replacement on the 72-slot records
(`lem:record:one-stage-folded-e`(e), from (d))

`paper/sections/20c_middle_frame.tex`, `lem:record:one-stage-folded-e`(e): "the record difference
is the coupling difference `Δ_c` of (d) conditional on the shared label, which gives the sharp
bound". The ingredients:

* **geometry** (`cert:record:middle-geometry`, by `decide`): at `tagCut s` (`ϑ₁` for `E₀`, `ϑ₂`
  for `E₁`) the plus half of the emitted record reads objects `1, 2` only and the minus half
  objects `0, 2` only (`emit_plus_half`, `emit_minus_half`);
* the cut form and the half-marginal norms of an emitted law are expectations
  (`form_emit`, `sum_halfPlus`, `sum_halfMinus`);
* a tensor of laws, read on three objects, is a sum over the three labels with the product of the
  per-prime triple laws (`tensor_triple`); at one prime the triple laws are
  `𝒦₊^{(c)}(a, a')/(q(q-1))`
  (`plusLaw_ind`) and `[a, a', c distinct]/(q(q-1)(q-2))` (`matchLaw_ind`).
-/

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.FirstStagePaper

open Sarkozy.TheoremC Sarkozy.PartVRecords Sarkozy.PartV Sarkozy.Labellings Sarkozy.Comparison

/-! ## Geometry -/

/-- At `tagCut s`, the plus half of the emission by `E_s` reads objects `1, 2`
(`cert:record:middle-geometry`). -/
theorem tagCut_plus (s : Fin 2) :
    ∀ v : Slot, v ∈ (tagCut s).half → (matching s v.1 = 1 ∨ matching s v.1 = 2) := by
  fin_cases s
  · exact (by decide : ∀ v : Slot, v ∈ (firstChamberCut 1).half →
      (matching 0 v.1 = 1 ∨ matching 0 v.1 = 2))
  · exact (by decide : ∀ v : Slot, v ∈ (firstChamberCut 2).half →
      (matching 1 v.1 = 1 ∨ matching 1 v.1 = 2))

/-- At `tagCut s`, the minus half of the emission by `E_s` reads objects `0, 2`. -/
theorem tagCut_minus (s : Fin 2) :
    ∀ v : Slot, v ∈ (tagCut s).half →
      (matching s ((tagCut s).flip v).1 = 0 ∨ matching s ((tagCut s).flip v).1 = 2) := by
  fin_cases s
  · exact (by decide : ∀ v : Slot, v ∈ (firstChamberCut 1).half →
      (matching 0 ((firstChamberCut 1).flip v).1 = 0 ∨
        matching 0 ((firstChamberCut 1).flip v).1 = 2))
  · exact (by decide : ∀ v : Slot, v ∈ (firstChamberCut 2).half →
      (matching 1 ((firstChamberCut 2).flip v).1 = 0 ∨
        matching 1 ((firstChamberCut 2).flip v).1 = 2))

section Half

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The plus-half assignment of the private label `a` (object `1`) and the shared label `c`. -/
def hpF (s : Fin 2) (a c : X) : (tagCut s).Half → X :=
  fun v => if matching s v.1.1 = 1 then a else c

/-- The minus-half assignment of the private label `a` (object `0`) and the shared label `c`. -/
def hmF (s : Fin 2) (a c : X) : (tagCut s).Half → X :=
  fun v => if matching s ((tagCut s).flip v.1).1 = 0 then a else c

omit [Fintype X] [DecidableEq X] in
theorem emit_plus_half (s : Fin 2) (y : Fin 3 × Fin 1 → X) :
    (fun v : (tagCut s).Half => y (midDiagEmission (matching s) v.1)) =
      hpF s (y (1, 0)) (y (2, 0)) := by
  funext v
  simp only [midDiagEmission, hpF]
  rcases tagCut_plus s v.1 v.2 with h | h
  · rw [h]
    rfl
  · rw [h]
    rfl

omit [Fintype X] [DecidableEq X] in
theorem emit_minus_half (s : Fin 2) (y : Fin 3 × Fin 1 → X) :
    (fun v : (tagCut s).Half => y (midDiagEmission (matching s) ((tagCut s).flip v.1))) =
      hmF s (y (0, 0)) (y (2, 0)) := by
  funext v
  simp only [midDiagEmission, hmF]
  rcases tagCut_minus s v.1 v.2 with h | h
  · rw [h]
    rfl
  · rw [h]
    rfl

/-! ## Forms and half-marginal norms of emitted laws -/

/-- The cut form of an emitted law is an expectation. -/
theorem form_emit (c : ReflectionCut Slot) (lam : FiniteLaw (Fin 3 × Fin 1 → X))
    (π : Slot → Fin 3 × Fin 1) (F G : (c.Half → X) → ℝ) :
    c.form (signedIntegral (emit lam π).weight) F G =
      lam.expect (fun y => F (fun v => y (π v.1)) * G (fun v => y (π (c.flip v.1)))) := by
  unfold ReflectionCut.form
  rw [← FiniteLaw.expect_eq_signedIntegral, expect_emit]
  rfl

/-- `∑_x m₊(x) F(x)² = K(F(z₊)²)`. -/
theorem sum_halfPlus (c : ReflectionCut Slot) (K : SlotMeasure X) (F : (c.Half → X) → ℝ) :
    ∑ x, halfMarginalPlus c K x * F x ^ 2 = K (fun z => F (fun v => z v.1) ^ 2) := by
  simp only [halfMarginalPlus]
  have e : ∀ x : c.Half → X, K (fun z => if (fun v : c.Half => z v.1) = x then 1 else 0) * F x ^ 2 =
      K (F x ^ 2 • fun z => if (fun v : c.Half => z v.1) = x then (1 : ℝ) else 0) := by
    intro x
    rw [LinearMap.map_smul, smul_eq_mul, mul_comm]
  simp only [e]
  rw [← map_sum]
  congr 1
  funext z
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    mem_univ, ↓reduceIte]

/-- `∑_y m₋(y) G(y)² = K(G(z₋)²)`. -/
theorem sum_halfMinus (c : ReflectionCut Slot) (K : SlotMeasure X) (G : (c.Half → X) → ℝ) :
    ∑ y, halfMarginalMinus c K y * G y ^ 2 = K (fun z => G (fun v => z (c.flip v.1)) ^ 2) := by
  simp only [halfMarginalMinus]
  have e : ∀ y : c.Half → X,
      K (fun z => if (fun v : c.Half => z (c.flip v.1)) = y then 1 else 0) * G y ^ 2 =
        K (G y ^ 2 • fun z => if (fun v : c.Half => z (c.flip v.1)) = y then (1 : ℝ) else 0) := by
    intro y
    rw [LinearMap.map_smul, smul_eq_mul, mul_comm]
  simp only [e]
  rw [← map_sum]
  congr 1
  funext z
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    mem_univ, ↓reduceIte]

end Half

/-! ## Tensors read on three objects -/

section Tensor

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]

/-- The indicator of the three values `a, b, c` at the slots `v₀, v₁, v₂`. -/
def ind3 {Y : Type*} [DecidableEq Y] (v₀ v₁ v₂ : V) (a b c : Y) (w : V → Y) : ℝ :=
  (if w v₀ = a then 1 else 0) * (if w v₁ = b then 1 else 0) * (if w v₂ = c then 1 else 0)

/-- **A tensor read on three slots** is the sum over the three values of the product of the
per-factor laws of the three slots. -/
theorem tensor_triple (μ : ∀ j, FiniteLaw (V → X j)) (v₀ v₁ v₂ : V)
    (g : (∀ j, X j) → (∀ j, X j) → (∀ j, X j) → ℝ) :
    (FiniteLaw.tensor μ).expect (fun z => g (z v₀) (z v₁) (z v₂)) =
      ∑ a : (∀ j, X j), ∑ b : (∀ j, X j), ∑ c : (∀ j, X j), g a b c *
        ∏ j, (μ j).expect (ind3 v₀ v₁ v₂ (a j) (b j) (c j)) := by
  rw [expect_tensor_eq_sum]
  have hpt : ∀ z : ∀ j, V → X j, g (fun j => z j v₀) (fun j => z j v₁) (fun j => z j v₂) =
      ∑ a : (∀ j, X j), ∑ b : (∀ j, X j), ∑ c : (∀ j, X j), g a b c *
        ∏ j, ind3 v₀ v₁ v₂ (a j) (b j) (c j) (z j) := by
    intro z
    have hz : ∀ (a b c : ∀ j, X j), (∏ j, ind3 v₀ v₁ v₂ (a j) (b j) (c j) (z j)) =
        if a = (fun j => z j v₀) ∧ b = (fun j => z j v₁) ∧ c = (fun j => z j v₂) then 1 else 0 := by
      intro a b c
      simp only [ind3]
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_boole, Finset.prod_boole,
        Finset.prod_boole]
      by_cases ha : a = (fun j => z j v₀)
      · by_cases hb : b = (fun j => z j v₁)
        · by_cases hc : c = (fun j => z j v₂)
          · subst ha hb hc
            simp
          · have : ¬ ∀ j ∈ univ, z j v₂ = c j :=
              fun h' => hc (funext fun j => (h' j (mem_univ j)).symm)
            simp only [this, ↓reduceIte, mul_zero, hc, and_false]
        · have : ¬ ∀ j ∈ univ, z j v₁ = b j :=
            fun h' => hb (funext fun j => (h' j (mem_univ j)).symm)
          simp only [this, ↓reduceIte, mul_zero, zero_mul, hb, false_and, and_false]
      · have : ¬ ∀ j ∈ univ, z j v₀ = a j := fun h' => ha (funext fun j => (h' j (mem_univ j)).symm)
        simp only [this, ↓reduceIte, zero_mul, ha, false_and]
    simp only [hz, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single (fun j => z j v₀)]
    · rw [Finset.sum_eq_single (fun j => z j v₁)]
      · rw [Finset.sum_eq_single (fun j => z j v₂)]
        · simp
        · intro c _ hc
          simp [hc]
        · intro h'
          exact absurd (mem_univ _) h'
      · intro b _ hb
        refine sum_eq_zero fun c _ => ?_
        simp [hb]
      · intro h'
        exact absurd (mem_univ _) h'
    · intro a _ ha
      refine sum_eq_zero fun b _ => sum_eq_zero fun c _ => ?_
      simp [ha]
    · intro h'
      exact absurd (mem_univ _) h'
  simp only [hpt, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun b _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun c _ => ?_
  have e : ∀ z : ∀ j, V → X j, (∏ j, (μ j).weight (z j)) * (g a b c *
      ∏ j, ind3 v₀ v₁ v₂ (a j) (b j) (c j) (z j)) =
      g a b c * ∏ j, ((μ j).weight (z j) * ind3 v₀ v₁ v₂ (a j) (b j) (c j) (z j)) := by
    intro z
    rw [Finset.prod_mul_distrib]
    ring
  simp only [e, ← mul_sum]
  congr 1
  unfold FiniteLaw.expect
  rw [Fintype.prod_sum]

end Tensor

/-! ## One prime: the triple laws -/

section OnePrime

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The triple law of the replacement: `𝒦₊^{(c)}(a, a')/(q(q-1))` (`tripleWeight`). -/
theorem plusLaw_ind (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F)
    (a b c : F) :
    (plusLaw F hF h3 hk).expect (ind3 (0, 0) (1, 0) (2, 0) a b c) = tripleWeight (a, b, c) := by
  rw [expect_plusLaw, Finset.sum_eq_single (a, b, c)]
  · simp only [ind3, (tripleConfig_apply _).1, (tripleConfig_apply _).2.1,
      (tripleConfig_apply _).2.2, ↓reduceIte, mul_one]
  · intro t _ ht
    simp only [ind3, (tripleConfig_apply _).1, (tripleConfig_apply _).2.1,
      (tripleConfig_apply _).2.2]
    by_cases h1 : t.1 = a
    · by_cases h2 : t.2.1 = b
      · have h3' : ¬ t.2.2 = c := fun h3' => ht (Prod.ext h1 (Prod.ext h2 h3'))
        simp only [h3', ↓reduceIte, mul_zero]
      · simp only [h2, ↓reduceIte, mul_zero, zero_mul]
    · simp only [h1, ↓reduceIte, mul_zero, zero_mul]
  · intro h'
    exact absurd (mem_univ _) h'

/-- The triple law of the replaced record: `[a, a', c distinct]/(q(q-1)(q-2))`. -/
theorem matchLaw_ind (hne : (injLabellings F (matchGraph (Fin 1))).Nonempty) (a b c : F) :
    (graphLaw (matchGraph (Fin 1)) hne).expect (ind3 (0, 0) (1, 0) (2, 0) a b c) =
      (if a ≠ b ∧ a ≠ c ∧ b ≠ c then 1 else 0) /
        (((Fintype.card F : ℝ) - 2) * ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1))) := by
  rw [matchLaw_expect, sum_distinct_one]
  congr 1
  rw [Finset.sum_eq_single (a, b, c)]
  · simp only [ind3, (tripleConfig_apply _).1, (tripleConfig_apply _).2.1,
      (tripleConfig_apply _).2.2, ↓reduceIte, mul_one]
  · intro t _ ht
    split_ifs with hd
    · simp only [ind3, (tripleConfig_apply _).1, (tripleConfig_apply _).2.1,
        (tripleConfig_apply _).2.2]
      by_cases h1 : t.1 = a
      · by_cases h2 : t.2.1 = b
        · have h3' : ¬ t.2.2 = c := fun h3' => ht (Prod.ext h1 (Prod.ext h2 h3'))
          simp only [h3', ↓reduceIte, mul_zero]
        · simp only [h2, ↓reduceIte, mul_zero, zero_mul]
      · simp only [h1, ↓reduceIte, zero_mul]
    · rfl
  · intro h'
    exact absurd (mem_univ _) h'

end OnePrime

/-! ## The block -/

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- `q_i`, the prime `p_i` as a real. -/
noncomputable abbrev qR (i : ι) : ℝ := (Fintype.card (ZMod (pr i)) : ℝ)

/-- The triple law of the replaced record at the prime `i`. -/
noncomputable def mwt (i : ι) (a b c : ZMod (pr i)) : ℝ :=
  (if a ≠ b ∧ a ≠ c ∧ b ≠ c then 1 else 0) / ((qR pr i - 2) * (qR pr i * (qR pr i - 1)))

/-- The common normalization `∏_p (p(p-1))⁻¹` of the conditional laws given the shared label. -/
noncomputable def kappaN : ℝ := ∏ i, (qR pr i * (qR pr i - 1))⁻¹

omit [DecidableEq ι] in
theorem kappaN_nonneg : 0 ≤ kappaN pr := by
  unfold kappaN
  refine prod_nonneg fun i _ => inv_nonneg.mpr ?_
  have : (1 : ℝ) ≤ qR pr i := by
    have := (Fact.out : (pr i).Prime).one_lt
    simp only [qR, ZMod.card]
    exact_mod_cast this.le
  nlinarith

/-- **The block replacement law read on the three objects.** -/
theorem blockPlus_expect (h : ClassThreeBlock pr)
    (g : BlockLabel pr → BlockLabel pr → BlockLabel pr → ℝ) :
    (blockPlusLaw pr h).expect (fun y => g (y (0, 0)) (y (1, 0)) (y (2, 0))) =
      ∑ a0, ∑ a1, ∑ c, g a0 a1 c * ∏ i, tripleWeight (a0 i, a1 i, c i) := by
  unfold blockPlusLaw
  rw [tensor_triple]
  simp only [plusLaw_ind]

/-- **The block matching law read on the three objects.** -/
theorem blockMatch_expect (hne : MiddleNonempty pr)
    (g : BlockLabel pr → BlockLabel pr → BlockLabel pr → ℝ) :
    (blockGraphLaw pr (matchGraph (Fin 1)) hne.E1).expect
        (fun y => g (y (0, 0)) (y (1, 0)) (y (2, 0))) =
      ∑ a0, ∑ a1, ∑ c, g a0 a1 c * ∏ i, mwt pr i (a0 i) (a1 i) (c i) := by
  unfold blockGraphLaw
  rw [tensor_triple]
  simp only [matchLaw_ind, mwt]

/-- **Sums over the labels that avoid the shared label at every prime.** -/
theorem sum_avoid (c : BlockLabel pr) (ψ : BlockLabel pr → ℝ)
    (hψ : ∀ a, (∃ i, a i = c i) → ψ a = 0) :
    ∑ a, ψ a = ∑ a : (∀ i, Vc (c i)), ψ (fun i => (a i).1) := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun a : BlockLabel pr => ∀ i, a i ≠ c i) ψ]
  have h0 : ∑ a : {a : BlockLabel pr // ¬ ∀ i, a i ≠ c i}, ψ a = 0 := by
    refine sum_eq_zero fun a _ => hψ a.1 ?_
    have := a.2
    push Not at this
    exact this
  rw [h0, add_zero]
  exact Fintype.sum_equiv (Equiv.subtypePiEquivPi (α := ι) (β := fun i => ZMod (pr i))
    (p := fun i x => x ≠ c i)) _ _ (fun a => rfl)

omit [DecidableEq ι] in
/-- The replacement's triple law, restricted to `∏_p V_{c_p}`, is `κ_N ⊗_p 𝒦₊^{(c_p)}`. -/
theorem prod_tripleWeight (c : BlockLabel pr) (a0 a1 : ∀ i, Vc (c i)) :
    ∏ i, tripleWeight ((a0 i).1, (a1 i).1, c i) = kappaN pr * blockKp pr c a0 a1 := by
  simp only [tripleWeight, kappaN, blockKp, Sarkozy.IndexSupport.piKron_apply, KpMat,
    Finset.prod_mul_distrib]

omit [DecidableEq ι] in
/-- The replaced record's triple law, restricted to `∏_p V_{c_p}`, is `κ_N ⊗_p 𝒦₀^{(c_p)}`. -/
theorem prod_mwt (c : BlockLabel pr) (a0 a1 : ∀ i, Vc (c i)) :
    ∏ i, mwt pr i (a0 i).1 (a1 i).1 (c i) = kappaN pr * blockK0 pr c a0 a1 := by
  simp only [kappaN, blockK0, Sarkozy.IndexSupport.piKron_apply, ← Finset.prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  simp only [mwt, K0Mat]
  have h0 : (a0 i).1 ≠ c i := (a0 i).2
  have h1 : (a1 i).1 ≠ c i := (a1 i).2
  by_cases he : a0 i = a1 i
  · simp only [he, ↓reduceIte, ne_eq, not_true_eq_false, false_and, zero_div, mul_zero]
  · have : (a0 i).1 ≠ (a1 i).1 := fun h' => he (Subtype.ext h')
    simp only [he, ↓reduceIte, ne_eq, this, not_false_eq_true, h0, h1, and_self, one_div]
    rw [mul_inv]
    ring

/-- Row sums of `⊗_p 𝒦₀^{(c_p)}`. -/
theorem blockK0_row_sum (h : ClassThreeBlock pr) (c : BlockLabel pr) (a0 : ∀ i, Vc (c i)) :
    ∑ a1, blockK0 pr c a0 a1 = 1 := by
  simp only [blockK0, Sarkozy.IndexSupport.piKron_apply]
  rw [← Fintype.prod_sum (fun i x => K0Mat (c i) (a0 i) x)]
  exact prod_eq_one fun i _ => K0Mat_row_sum (c i) (card_three_le (h.card_mod i)) (a0 i)

/-- Column sums of `⊗_p 𝒦₀^{(c_p)}`. -/
theorem blockK0_col_sum (h : ClassThreeBlock pr) (c : BlockLabel pr) (a1 : ∀ i, Vc (c i)) :
    ∑ a0, blockK0 pr c a0 a1 = 1 := by
  simp only [blockK0, Sarkozy.IndexSupport.piKron_apply]
  rw [← Fintype.prod_sum (fun i x => K0Mat (c i) x (a1 i))]
  refine prod_eq_one fun i _ => ?_
  rw [show ∑ x, K0Mat (c i) x (a1 i) = ∑ x, K0Mat (c i) (a1 i) x from
    sum_congr rfl fun x _ => K0Mat_symm (c i) x (a1 i)]
  exact K0Mat_row_sum (c i) (card_three_le (h.card_mod i)) (a1 i)

omit [DecidableEq ι] in
/-- The triple laws vanish when a private label equals the shared label at some prime. -/
theorem prod_triples_vanish (c a0 a1 : BlockLabel pr) (hc : (∃ i, a0 i = c i) ∨ ∃ i, a1 i = c i) :
    ∏ i, tripleWeight (a0 i, a1 i, c i) = 0 ∧ ∏ i, mwt pr i (a0 i) (a1 i) (c i) = 0 := by
  rcases hc with ⟨i, hi⟩ | ⟨i, hi⟩
  · refine ⟨prod_eq_zero (mem_univ i) ?_, prod_eq_zero (mem_univ i) ?_⟩
    · simp only [tripleWeight, hi, Kplus_left_eq, mul_zero]
    · simp only [mwt, hi, ne_eq, not_true_eq_false, false_and, and_false, ↓reduceIte, zero_div]
  · refine ⟨prod_eq_zero (mem_univ i) ?_, prod_eq_zero (mem_univ i) ?_⟩
    · simp only [tripleWeight, hi, Kplus_right_eq, mul_zero]
    · simp only [mwt, hi, ne_eq, not_true_eq_false, and_false, ↓reduceIte, zero_div]

/-- **The double sum over the private labels, for a fixed shared label**, restricted to
`∏_p V_{c_p}`. -/
theorem sum_private (c : BlockLabel pr) (Ψ : BlockLabel pr → BlockLabel pr → ℝ)
    (hΨ : ∀ a0 a1, ((∃ i, a0 i = c i) ∨ ∃ i, a1 i = c i) → Ψ a0 a1 = 0) :
    ∑ a0, ∑ a1, Ψ a0 a1 =
      ∑ a0 : (∀ i, Vc (c i)), ∑ a1 : (∀ i, Vc (c i)),
        Ψ (fun i => (a0 i).1) (fun i => (a1 i).1) := by
  rw [sum_avoid pr c (fun a0 => ∑ a1, Ψ a0 a1)
    (fun a0 ha0 => sum_eq_zero fun a1 _ => hΨ a0 a1 (Or.inl ha0))]
  refine sum_congr rfl fun a0 _ => ?_
  exact sum_avoid pr c _ (fun a1 ha1 => hΨ _ a1 (Or.inr ha1))

/-- Cauchy–Schwarz with square roots. -/
theorem sum_sqrt_mul_le {κ : Type*} (t : Finset κ) (a b : κ → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ i, 0 ≤ b i) :
    ∑ i ∈ t, Real.sqrt (a i) * Real.sqrt (b i) ≤
      Real.sqrt (∑ i ∈ t, a i) * Real.sqrt (∑ i ∈ t, b i) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq t (fun i => Real.sqrt (a i)) (fun i => Real.sqrt (b i))
  simp only [Real.sq_sqrt (ha _), Real.sq_sqrt (hb _)] at hcs
  rw [← Real.sqrt_mul (sum_nonneg fun i _ => ha i)]
  calc ∑ i ∈ t, Real.sqrt (a i) * Real.sqrt (b i)
      ≤ |∑ i ∈ t, Real.sqrt (a i) * Real.sqrt (b i)| := le_abs_self _
    _ = Real.sqrt ((∑ i ∈ t, Real.sqrt (a i) * Real.sqrt (b i)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((∑ i ∈ t, a i) * ∑ i ∈ t, b i) := Real.sqrt_le_sqrt hcs

theorem sum3_comm (T : BlockLabel pr → BlockLabel pr → BlockLabel pr → ℝ) :
    ∑ a0, ∑ a1, ∑ c, T a0 a1 c = ∑ c, ∑ a0, ∑ a1, T a0 a1 c :=
  calc ∑ a0, ∑ a1, ∑ c, T a0 a1 c = ∑ a0, ∑ c, ∑ a1, T a0 a1 c :=
        sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c, ∑ a0, ∑ a1, T a0 a1 c := Finset.sum_comm

/-- **For a fixed shared label**, the difference of the two triple laws, paired with `ψ(a₀) φ(a₁)`,
is `κ_N ⟨g, Δ_c f⟩` on `∏_p V_{c_p}`. -/
theorem sum_pair_diff (c : BlockLabel pr) (φ ψ : BlockLabel pr → ℝ) :
    ∑ a0, ∑ a1, φ a1 * ψ a0 *
        (∏ i, tripleWeight (a0 i, a1 i, c i) - ∏ i, mwt pr i (a0 i) (a1 i) (c i)) =
      kappaN pr * ((fun a : (∀ i, Vc (c i)) => ψ (fun i => (a i).1)) ⬝ᵥ
        ((blockKp pr c - blockK0 pr c) *ᵥ (fun a => φ (fun i => (a i).1)))) := by
  rw [sum_private pr c _ (fun a0 a1 hc => by
    obtain ⟨h1, h2⟩ := prod_triples_vanish pr c a0 a1 hc
    rw [h1, h2, sub_self, mul_zero])]
  simp only [prod_tripleWeight, prod_mwt, dotProduct, Matrix.mulVec, Matrix.sub_apply, mul_sum]
  refine sum_congr rfl fun a0 _ => sum_congr rfl fun a1 _ => ?_
  ring

/-- **For a fixed shared label**, the second moment of a function of `a₁` under the replaced
record. -/
theorem sum_sq_one (h : ClassThreeBlock pr) (c : BlockLabel pr) (φ : BlockLabel pr → ℝ) :
    ∑ a0 : BlockLabel pr, ∑ a1 : BlockLabel pr, φ a1 ^ 2 * ∏ i, mwt pr i (a0 i) (a1 i) (c i) =
      kappaN pr * ((fun a : (∀ i, Vc (c i)) => φ (fun i => (a i).1)) ⬝ᵥ
        (fun a : (∀ i, Vc (c i)) => φ (fun i => (a i).1))) := by
  rw [sum_private pr c _ (fun a0 a1 hc => by
    rw [(prod_triples_vanish pr c a0 a1 hc).2, mul_zero])]
  simp only [prod_mwt]
  rw [Finset.sum_comm]
  have e : ∀ a1 : (∀ i, Vc (c i)), ∑ a0 : (∀ i, Vc (c i)),
      φ (fun i => (a1 i).1) ^ 2 * (kappaN pr * blockK0 pr c a0 a1) =
        kappaN pr * (φ (fun i => (a1 i).1) * φ (fun i => (a1 i).1)) := by
    intro a1
    have e' : ∑ a0 : (∀ i, Vc (c i)),
        φ (fun i => (a1 i).1) ^ 2 * (kappaN pr * blockK0 pr c a0 a1) =
          φ (fun i => (a1 i).1) ^ 2 * kappaN pr * ∑ a0, blockK0 pr c a0 a1 := by
      rw [mul_sum]
      refine sum_congr rfl fun a0 _ => ?_
      ring
    rw [e', blockK0_col_sum pr h c a1]
    ring
  simp only [e]
  rw [dotProduct, mul_sum]

/-- **For a fixed shared label**, the second moment of a function of `a₀` under the replaced
record. -/
theorem sum_sq_zero (h : ClassThreeBlock pr) (c : BlockLabel pr) (ψ : BlockLabel pr → ℝ) :
    ∑ a0 : BlockLabel pr, ∑ a1 : BlockLabel pr, ψ a0 ^ 2 * ∏ i, mwt pr i (a0 i) (a1 i) (c i) =
      kappaN pr * ((fun a : (∀ i, Vc (c i)) => ψ (fun i => (a i).1)) ⬝ᵥ
        (fun a : (∀ i, Vc (c i)) => ψ (fun i => (a i).1))) := by
  rw [sum_private pr c _ (fun a0 a1 hc => by
    rw [(prod_triples_vanish pr c a0 a1 hc).2, mul_zero])]
  simp only [prod_mwt, dotProduct, mul_sum]
  refine sum_congr rfl fun a0 _ => ?_
  have e : ∑ a1 : (∀ i, Vc (c i)), ψ (fun i => (a0 i).1) ^ 2 * (kappaN pr * blockK0 pr c a0 a1) =
      ψ (fun i => (a0 i).1) ^ 2 * kappaN pr * ∑ a1, blockK0 pr c a0 a1 := by
    rw [mul_sum]
    refine sum_congr rfl fun a1 _ => ?_
    ring
  rw [e, blockK0_row_sum pr h c a0]
  ring

/-- **`lem:record:one-stage-folded-e`(e), the sharp bound on the 72-slot records, from (d).** For a
block of class-three primes `p ≥ b ≥ X ≥ 2^{24}` and `s = 0, 1`, the replacement `plusRec s` of the
folded matching record `matchRec s` (both normalized) differs from it with sharp bound
`k_new(X) b^{-1/2}` relative to it at its own first-coordinate cut `tagCut s` (`def:price`(b)).
Witness: the trivial label set (the shared label need not be conditioned on: by Cauchy–Schwarz over
it, the bound of each conditional difference `Δ_c`, `block_delta_form_le`, gives the bound of the
whole difference relative to the actual half marginals). The proof: the cut form of the difference
is `κ_N ∑_c ⟨g_c, Δ_c f_c⟩` (`sum_pair_diff`: the plus half reads `(a₁, c)` and the minus half
`(a₀, c)`, `emit_plus_half`, `emit_minus_half`), and the two half-marginal norms are
`κ_N ∑_c ‖f_c‖²` and `κ_N ∑_c ‖g_c‖²` (`sum_sq_one`, `sum_sq_zero`). -/
theorem blockSharp_of_block (h : ClassThreeBlock pr) (hne : MiddleNonempty pr) {X b : ℝ}
    (hX : 2 ^ 24 ≤ X) (hXb : X ≤ b) (hbp : ∀ i, b ≤ (pr i : ℝ)) :
    BlockSharp pr hne h (blockConst X b) := by
  intro s
  let π : FiniteLaw Unit := { weight := fun _ => 1, nonneg := fun _ => zero_le_one,
                              total := by simp }
  have hm1 : mass (matchRec pr hne s) = 1 := mass_law _
  refine ⟨Unit, inferInstance, π, fun _ => matchRec pr hne s,
    fun _ => plusRec pr h s - matchRec pr hne s, fun _ => ⟨isNonneg_law _, mass_law _⟩, ?_, ?_, ?_⟩
  · rw [hm1, Fintype.sum_unique]
    simp [π]
  · rw [hm1, Fintype.sum_unique]
    simp [π]
  intro _ F G
  set fC : ∀ c : BlockLabel pr, (∀ i, Vc (c i)) → ℝ :=
    fun c a => F (hpF s (fun i => (a i).1) c) with hfC
  set gC : ∀ c : BlockLabel pr, (∀ i, Vc (c i)) → ℝ :=
    fun c a => G (hmF s (fun i => (a i).1) c) with hgC
  have hform : (tagCut s).form (plusRec pr h s - matchRec pr hne s) F G =
      kappaN pr * ∑ c : BlockLabel pr, gC c ⬝ᵥ ((blockKp pr c - blockK0 pr c) *ᵥ fC c) := by
    have hsub : (tagCut s).form (plusRec pr h s - matchRec pr hne s) F G =
        (tagCut s).form (plusRec pr h s) F G - (tagCut s).form (matchRec pr hne s) F G := rfl
    rw [hsub, plusRec, matchRec, form_emit, form_emit]
    simp only [emit_plus_half, emit_minus_half]
    have e1 := blockPlus_expect pr h (fun a0 a1 c => F (hpF s a1 c) * G (hmF s a0 c))
    have e2 := blockMatch_expect pr hne (fun a0 a1 c => F (hpF s a1 c) * G (hmF s a0 c))
    rw [sum3_comm] at e1 e2
    rw [e1, e2, ← sum_sub_distrib, mul_sum]
    refine sum_congr rfl fun c _ => ?_
    rw [← sum_pair_diff pr c (fun a1 => F (hpF s a1 c)) (fun a0 => G (hmF s a0 c)),
      ← sum_sub_distrib]
    refine sum_congr rfl fun a0 _ => ?_
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun a1 _ => ?_
    ring
  have hmp : ∑ x, halfMarginalPlus (tagCut s) (matchRec pr hne s) x * F x ^ 2 =
      kappaN pr * ∑ c : BlockLabel pr, fC c ⬝ᵥ fC c := by
    rw [sum_halfPlus, matchRec, ← FiniteLaw.expect_eq_signedIntegral, expect_emit]
    simp only [Function.comp_apply, emit_plus_half]
    have e2 := blockMatch_expect pr hne (fun _ a1 c => F (hpF s a1 c) ^ 2)
    rw [e2, sum3_comm, mul_sum]
    exact sum_congr rfl fun c _ => sum_sq_one pr h c (fun a1 => F (hpF s a1 c))
  have hmm : ∑ y, halfMarginalMinus (tagCut s) (matchRec pr hne s) y * G y ^ 2 =
      kappaN pr * ∑ c : BlockLabel pr, gC c ⬝ᵥ gC c := by
    rw [sum_halfMinus, matchRec, ← FiniteLaw.expect_eq_signedIntegral, expect_emit]
    simp only [Function.comp_apply, emit_minus_half]
    have e2 := blockMatch_expect pr hne (fun a0 _ c => G (hmF s a0 c) ^ 2)
    rw [e2, sum3_comm, mul_sum]
    exact sum_congr rfl fun c _ => sum_sq_zero pr h c (fun a0 => G (hmF s a0 c))
  rw [hform, hmp, hmm]
  have hκ := kappaN_nonneg pr
  have hD : 0 ≤ blockConst X b := by
    have hX0 : 0 < X := by linarith
    unfold blockConst
    exact mul_nonneg (le_trans zero_le_one (one_le_knew (by positivity)
      (by rw [div_le_div_iff₀ hX0 (by norm_num)]; linarith) (by positivity))) (by positivity)
  have hterm : ∀ c, |gC c ⬝ᵥ ((blockKp pr c - blockK0 pr c) *ᵥ fC c)| ≤
      blockConst X b * Real.sqrt (gC c ⬝ᵥ gC c) * Real.sqrt (fC c ⬝ᵥ fC c) :=
    fun c => block_delta_form_le pr h hX hXb hbp c (gC c) (fC c)
  have hff : ∀ c, 0 ≤ fC c ⬝ᵥ fC c := fun c => Sarkozy.IndexSupport.dotProduct_self_nonneg _
  have hgg : ∀ c, 0 ≤ gC c ⬝ᵥ gC c := fun c => Sarkozy.IndexSupport.dotProduct_self_nonneg _
  calc |kappaN pr * ∑ c, gC c ⬝ᵥ ((blockKp pr c - blockK0 pr c) *ᵥ fC c)|
      = kappaN pr * |∑ c, gC c ⬝ᵥ ((blockKp pr c - blockK0 pr c) *ᵥ fC c)| := by
        rw [abs_mul, abs_of_nonneg hκ]
    _ ≤ kappaN pr * ∑ c, |gC c ⬝ᵥ ((blockKp pr c - blockK0 pr c) *ᵥ fC c)| :=
        mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) hκ
    _ ≤ kappaN pr * ∑ c, blockConst X b * Real.sqrt (gC c ⬝ᵥ gC c) *
          Real.sqrt (fC c ⬝ᵥ fC c) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun c _ => hterm c) hκ
    _ = blockConst X b * (kappaN pr * ∑ c, Real.sqrt (fC c ⬝ᵥ fC c) *
          Real.sqrt (gC c ⬝ᵥ gC c)) := by
        rw [mul_sum, mul_sum, mul_sum]
        refine sum_congr rfl fun c _ => ?_
        ring
    _ ≤ blockConst X b * (kappaN pr * (Real.sqrt (∑ c, fC c ⬝ᵥ fC c) *
          Real.sqrt (∑ c, gC c ⬝ᵥ gC c))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (sum_sqrt_mul_le univ _ _ hff hgg) hκ) hD
    _ = blockConst X b * Real.sqrt (kappaN pr * ∑ c, fC c ⬝ᵥ fC c) *
          Real.sqrt (kappaN pr * ∑ c, gC c ⬝ᵥ gC c) := by
        rw [Real.sqrt_mul hκ, Real.sqrt_mul hκ]
        have hs : Real.sqrt (kappaN pr) * Real.sqrt (kappaN pr) = kappaN pr :=
          Real.mul_self_sqrt hκ
        linear_combination (-(blockConst X b * Real.sqrt (∑ c, fC c ⬝ᵥ fC c) *
          Real.sqrt (∑ c, gC c ⬝ᵥ gC c))) * hs

end Block

end Sarkozy.FirstStagePaper
