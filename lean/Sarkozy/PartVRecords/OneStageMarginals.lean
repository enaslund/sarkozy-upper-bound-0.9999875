module

public import Sarkozy.PartVRecords.OneStageBlock

@[expose] public section

/-!
# The replacement keeps the actual conditional marginals, on the block
(`lem:record:one-stage-folded-e`(e))

`paper/sections/20c_middle_frame.tex`, `lem:record:one-stage-folded-e`(e): "at its own
first-coordinate cut each of its records has the same actual conditional marginals as the record
it replaces". At the cut `ϑ₁` (for `E₀`) or `ϑ₂` (for `E₁`) the two half marginals of a folded
matching record are the laws of `(c, a₀)` and `(c, a₁)` — the shared label (object `2`) with one
private label (object `0` or `1`).

**Proved:** these two pair laws of the block replacement `blockPlusLaw` equal those of the
record it replaces, the one-layer `E` block law `λ_𝔅(G_{E,1})` (`blockPlusLaw_pair02_eq`,
`blockPlusLaw_pair12_eq`). At one prime both are the uniform law on the ordered distinct pairs
(`plusLaw_pair02`, `plusLaw_pair12`; `matchLaw_pair02`, `matchLaw_pair12` for the `E` law, from
the count `|Inj_p(G_{E,1})| = p(p-1)(p-2)`), and a pair law of a tensor of laws is the tensor of the
pair laws (`tensor_pair_eq`).
-/

namespace Sarkozy.PartVRecords

open Finset Sarkozy.Labellings Sarkozy.PartV

/-! ## Pair laws of tensors -/

section Tensor

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]

/-- **A pair law of a tensor is determined by the pair laws of the factors**: if at every factor the
laws of `(z v₁, z v₂)` agree, they agree for the tensors. -/
theorem tensor_pair_eq (μ ν : ∀ j, FiniteLaw (V → X j)) (v₁ v₂ : V)
    (h : ∀ j (g : X j → X j → ℝ),
      (μ j).expect (fun z => g (z v₁) (z v₂)) = (ν j).expect (fun z => g (z v₁) (z v₂)))
    (g : (∀ j, X j) → (∀ j, X j) → ℝ) :
    (FiniteLaw.tensor μ).expect (fun z => g (z v₁) (z v₂)) =
      (FiniteLaw.tensor ν).expect (fun z => g (z v₁) (z v₂)) := by
  -- both sides, as sums over the pair values
  have key : ∀ ls : ∀ j, FiniteLaw (V → X j),
      (FiniteLaw.tensor ls).expect (fun z => g (z v₁) (z v₂)) =
        ∑ a : (∀ j, X j), ∑ b : (∀ j, X j), g a b *
          ∏ j, (ls j).expect (fun w => (if w v₁ = a j then (1 : ℝ) else 0) *
            (if w v₂ = b j then 1 else 0)) := by
    intro ls
    rw [expect_tensor_eq_sum]
    have hpt : ∀ z : ∀ j, V → X j, g (fun j => z j v₁) (fun j => z j v₂) =
        ∑ a : (∀ j, X j), ∑ b : (∀ j, X j), g a b *
          ∏ j, ((if z j v₁ = a j then (1 : ℝ) else 0) * (if z j v₂ = b j then 1 else 0)) := by
      intro z
      rw [Finset.sum_eq_single (fun j => z j v₁)]
      · rw [Finset.sum_eq_single (fun j => z j v₂)]
        · simp
        · intro b _ hb
          have : ∃ j, z j v₂ ≠ b j := by
            by_contra hc
            push Not at hc
            exact hb (funext fun j => (hc j).symm)
          obtain ⟨j, hj⟩ := this
          rw [Finset.prod_eq_zero (mem_univ j) (by simp [hj]), mul_zero]
        · intro h'
          exact absurd (mem_univ _) h'
      · intro a _ ha
        have : ∃ j, z j v₁ ≠ a j := by
          by_contra hc
          push Not at hc
          exact ha (funext fun j => (hc j).symm)
        obtain ⟨j, hj⟩ := this
        refine sum_eq_zero fun b _ => ?_
        rw [Finset.prod_eq_zero (mem_univ j) (by simp [hj]), mul_zero]
      · intro h'
        exact absurd (mem_univ _) h'
    simp only [hpt, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun a _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun b _ => ?_
    have e : ∀ z : ∀ j, V → X j, (∏ j, (ls j).weight (z j)) * (g a b *
        ∏ j, ((if z j v₁ = a j then (1 : ℝ) else 0) * (if z j v₂ = b j then 1 else 0))) =
        g a b * ∏ j, ((ls j).weight (z j) *
          ((if z j v₁ = a j then (1 : ℝ) else 0) * (if z j v₂ = b j then 1 else 0))) := by
      intro z
      simp only [Finset.prod_mul_distrib]
      ring
    simp only [e, ← mul_sum]
    congr 1
    unfold FiniteLaw.expect
    rw [Fintype.prod_sum]
  rw [key μ, key ν]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  congr 1
  exact prod_congr rfl fun j _ => h j (fun x y => (if x = a j then 1 else 0) *
    (if y = b j then 1 else 0))

end Tensor

/-! ## The one-layer `E` law at one prime -/

section OnePrime

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Triples and one-layer configurations of three objects. -/
def tripleEquiv : F × F × F ≃ (Fin 3 × Fin 1 → F) where
  toFun := tripleConfig
  invFun y := (y (0, 0), y (1, 0), y (2, 0))
  left_inv t := by
    obtain ⟨a, b, c⟩ := t
    rfl
  right_inv y := by
    funext o
    obtain ⟨o1, o2⟩ := o
    have : o2 = 0 := Subsingleton.elim _ _
    subst this
    fin_cases o1 <;> rfl

omit [Field F] [Fintype F] [DecidableEq F] in
/-- A configuration of three objects is injective iff its three labels are distinct. -/
theorem tripleConfig_injective_iff (t : F × F × F) :
    Function.Injective (tripleConfig t) ↔ t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 := by
  obtain ⟨a, b, c⟩ := t
  constructor
  · intro h
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
    · have := @h (0, 0) (1, 0) e
      simp at this
    · have := @h (0, 0) (2, 0) e
      simp at this
    · have := @h (1, 0) (2, 0) e
      simp at this
  · rintro ⟨h1, h2, h3⟩ ⟨o1, o2⟩ ⟨o1', o2'⟩ e
    have ho2 : o2 = 0 := Subsingleton.elim _ _
    have ho2' : o2' = 0 := Subsingleton.elim _ _
    subst ho2 ho2'
    fin_cases o1 <;> fin_cases o1' <;> simp_all [tripleConfig]

omit [Field F] in
/-- `∑_t [t distinct] g(t)` as a sum over the two labels `(c, a)` of objects `2, 0`. -/
theorem sum_distinct_02 (g : F → F → ℝ) :
    ∑ t : F × F × F, (if t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 then g t.2.2 t.1 else 0) =
      ((Fintype.card F : ℝ) - 2) * ∑ c, ∑ a, if a = c then 0 else g c a := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  have hinner : ∀ a : F, ∑ a' : F, ∑ c : F,
      (if a ≠ a' ∧ a ≠ c ∧ a' ≠ c then g c a else 0) =
      ∑ c : F, ((Fintype.card F : ℝ) - 2) * (if a = c then 0 else g c a) := by
    intro a
    rw [sum_comm]
    refine sum_congr rfl fun c _ => ?_
    by_cases hac : a = c
    · subst hac
      simp
    · rw [ite_eq_right hac]
      have e : ∀ a' : F, (if a ≠ a' ∧ a ≠ c ∧ a' ≠ c then g c a else 0) =
          g c a - (if a' = a then g c a else 0) - (if a' = c then g c a else 0) := by
        intro a'
        by_cases h1 : a' = a
        · subst h1
          simp [hac]
        · by_cases h2 : a' = c
          · subst h2
            simp [h1]
          · simp [h1, h2, hac, Ne.symm h1]
      simp only [e, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, Finset.sum_ite_eq',
        mem_univ, ↓reduceIte]
      ring
  simp only [hinner]
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun c _ => ?_
  rw [mul_sum]

omit [Field F] in
theorem sum_distinct_12 (g : F → F → ℝ) :
    ∑ t : F × F × F, (if t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 then g t.2.2 t.2.1 else 0) =
      ((Fintype.card F : ℝ) - 2) * ∑ c, ∑ a, if a = c then 0 else g c a := by
  -- swap the first two coordinates
  rw [← sum_distinct_02 g]
  let e : F × F × F ≃ F × F × F :=
    ⟨fun t => (t.2.1, t.1, t.2.2), fun t => (t.2.1, t.1, t.2.2), fun _ => rfl, fun _ => rfl⟩
  refine Fintype.sum_equiv e _ _ fun t => ?_
  obtain ⟨a, b, c⟩ := t
  change (if a ≠ b ∧ a ≠ c ∧ b ≠ c then g c b else 0) =
    (if b ≠ a ∧ b ≠ c ∧ a ≠ c then g c b else 0)
  by_cases h1 : a = b
  · subst h1
    simp
  · by_cases h2 : a = c
    · subst h2
      simp
    · by_cases h3 : b = c
      · subst h3
        simp
      · simp [h1, h2, h3, Ne.symm h1]

omit [Field F] in
theorem sum_ne_one (c : F) :
    ∑ a : F, (if a = c then (0 : ℝ) else 1) = (Fintype.card F : ℝ) - 1 := by
  have : ∀ a : F, (if a = c then (0 : ℝ) else 1) = 1 - (if a = c then 1 else 0) := by
    intro a
    split_ifs <;> norm_num
  simp only [this, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one,
    Finset.sum_ite_eq', mem_univ, ↓reduceIte]

omit [Field F] in
/-- The number of injective configurations of three objects: `q(q - 1)(q - 2)`. -/
theorem sum_distinct_one :
    ∑ t : F × F × F, (if t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 then (1 : ℝ) else 0) =
      ((Fintype.card F : ℝ) - 2) * ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1)) := by
  rw [sum_distinct_02 (fun _ _ => 1)]
  congr 1
  simp only [sum_ne_one, sum_const, card_univ, nsmul_eq_mul]

/-- Membership in `Inj_p(G_{E,1})` is injectivity (the graph has no edges). -/
theorem mem_inj_match_iff (y : Fin 3 × Fin 1 → F) :
    y ∈ injLabellings F (matchGraph (Fin 1)) ↔ Function.Injective y := by
  rw [mem_injLabellings_iff_feasible]
  constructor
  · rintro ⟨h, -⟩ a b hab
    exact h a (mem_univ _) b (mem_univ _) hab
  · intro h
    refine ⟨fun a _ b _ hab => h hab, fun e he => ?_⟩
    simp [matchGraph] at he

/-- **The one-layer `E` law at one prime** (uniform on the injective configurations), as a sum over
triples. -/
theorem matchLaw_expect (hne : (injLabellings F (matchGraph (Fin 1))).Nonempty)
    (H : (Fin 3 × Fin 1 → F) → ℝ) :
    (graphLaw (matchGraph (Fin 1)) hne).expect H =
      (∑ t : F × F × F, if t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 then H (tripleConfig t)
        else 0) /
      (∑ t : F × F × F, if t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 then (1 : ℝ) else 0) := by
  have hmem : ∀ t : F × F × F, tripleConfig t ∈ injLabellings F (matchGraph (Fin 1)) ↔
      (t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2) := fun t => by
    rw [mem_inj_match_iff, tripleConfig_injective_iff]
  have hcard : ((injLabellings F (matchGraph (Fin 1))).card : ℝ) =
      ∑ t : F × F × F, if t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 then (1 : ℝ) else 0 := by
    have h1 : ((injLabellings F (matchGraph (Fin 1))).card : ℝ) =
        ∑ y : Fin 3 × Fin 1 → F, if y ∈ injLabellings F (matchGraph (Fin 1)) then (1 : ℝ)
          else 0 := by
      rw [sum_boole]
      congr 2
      ext y
      simp
    rw [h1]
    refine (Fintype.sum_equiv tripleEquiv _ _ fun t => ?_).symm
    change _ = (if tripleConfig t ∈ injLabellings F (matchGraph (Fin 1)) then (1 : ℝ) else 0)
    by_cases hd : t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2
    · rw [ite_eq_left hd, ite_eq_left ((hmem t).mpr hd)]
    · rw [ite_eq_right hd, ite_eq_right (fun h' => hd ((hmem t).mp h'))]
  have hexp : (graphLaw (matchGraph (Fin 1)) hne).expect H =
      ∑ t : F × F × F, (graphLaw (matchGraph (Fin 1)) hne).weight (tripleConfig t) *
        H (tripleConfig t) := by
    unfold FiniteLaw.expect
    exact (Fintype.sum_equiv tripleEquiv _ (fun y => (graphLaw (matchGraph (Fin 1)) hne).weight y *
      H y) fun _ => rfl).symm
  rw [hexp, ← hcard, sum_div]
  refine sum_congr rfl fun t _ => ?_
  change (if tripleConfig t ∈ injLabellings F (matchGraph (Fin 1)) then
    1 / ((injLabellings F (matchGraph (Fin 1))).card : ℝ) else 0) * H (tripleConfig t) = _
  by_cases hd : t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2
  · rw [ite_eq_left ((hmem t).mpr hd), ite_eq_left hd]
    ring
  · rw [ite_eq_right (fun h' => hd ((hmem t).mp h')), ite_eq_right hd]
    ring

omit [Field F] [Fintype F] [DecidableEq F] in
theorem tripleConfig_apply (t : F × F × F) :
    tripleConfig t (0, 0) = t.1 ∧ tripleConfig t (1, 0) = t.2.1 ∧ tripleConfig t (2, 0) = t.2.2 :=
  ⟨rfl, rfl, rfl⟩

/-- **The `(c, a₀)` law of the one-layer `E` law** (objects `2`, `0`): uniform on the ordered
distinct pairs. -/
theorem matchLaw_pair02 (hne : (injLabellings F (matchGraph (Fin 1))).Nonempty)
    (h3 : 3 ≤ Fintype.card F) (g : F → F → ℝ) :
    (graphLaw (matchGraph (Fin 1)) hne).expect (fun y => g (y (2, 0)) (y (0, 0))) =
      ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1))⁻¹ *
        ∑ c, ∑ a, if a = c then 0 else g c a := by
  rw [matchLaw_expect, sum_distinct_one]
  simp only [(tripleConfig_apply _).1, (tripleConfig_apply _).2.2]
  rw [sum_distinct_02]
  have hq : (3 : ℝ) ≤ Fintype.card F := by exact_mod_cast h3
  have hq2 : (Fintype.card F : ℝ) - 2 ≠ 0 := by linarith
  have hq1 : (Fintype.card F : ℝ) - 1 ≠ 0 := by linarith
  have hq0 : (Fintype.card F : ℝ) ≠ 0 := by linarith
  field_simp

/-- **The `(c, a₁)` law of the one-layer `E` law** (objects `2`, `1`): uniform on the ordered
distinct pairs. -/
theorem matchLaw_pair12 (hne : (injLabellings F (matchGraph (Fin 1))).Nonempty)
    (h3 : 3 ≤ Fintype.card F) (g : F → F → ℝ) :
    (graphLaw (matchGraph (Fin 1)) hne).expect (fun y => g (y (2, 0)) (y (1, 0))) =
      ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1))⁻¹ *
        ∑ c, ∑ a, if a = c then 0 else g c a := by
  rw [matchLaw_expect, sum_distinct_one]
  simp only [(tripleConfig_apply _).2.1, (tripleConfig_apply _).2.2]
  rw [sum_distinct_12]
  have hq : (3 : ℝ) ≤ Fintype.card F := by exact_mod_cast h3
  have hq2 : (Fintype.card F : ℝ) - 2 ≠ 0 := by linarith
  have hq1 : (Fintype.card F : ℝ) - 1 ≠ 0 := by linarith
  have hq0 : (Fintype.card F : ℝ) ≠ 0 := by linarith
  field_simp

end OnePrime

/-! ## The block -/

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- **At the cut of `E₀`, the half law `(c, a₀)` of the replacement is that of the replaced record**
(`lem:record:one-stage-folded-e`(e)): the block replacement and the one-layer `E` block law have
the same law of the labels of objects `2, 0`. -/
theorem blockPlusLaw_pair02_eq (h : ClassThreeBlock pr) (hne : MiddleNonempty pr)
    (g : BlockLabel pr → BlockLabel pr → ℝ) :
    (blockPlusLaw pr h).expect (fun y => g (y (2, 0)) (y (0, 0))) =
      (blockGraphLaw pr (matchGraph (Fin 1)) hne.E1).expect (fun y => g (y (2, 0)) (y (0, 0))) := by
  refine tensor_pair_eq _ _ (2, 0) (0, 0) (fun i g' => ?_) g
  rw [plusLaw_pair02, matchLaw_pair02]
  rw [ZMod.card]
  have := h.ge7 i
  omega

/-- **At the cut of `E₁`, the half law `(c, a₁)` of the replacement is that of the replaced
record.** -/
theorem blockPlusLaw_pair12_eq (h : ClassThreeBlock pr) (hne : MiddleNonempty pr)
    (g : BlockLabel pr → BlockLabel pr → ℝ) :
    (blockPlusLaw pr h).expect (fun y => g (y (2, 0)) (y (1, 0))) =
      (blockGraphLaw pr (matchGraph (Fin 1)) hne.E1).expect (fun y => g (y (2, 0)) (y (1, 0))) := by
  refine tensor_pair_eq _ _ (2, 0) (1, 0) (fun i g' => ?_) g
  rw [plusLaw_pair12, matchLaw_pair12]
  rw [ZMod.card]
  have := h.ge7 i
  omega

/-- **The queried pair of the block replacement is uniform on the strict-square pairs**
(`lem:record:one-stage-folded-e`(e)): the law of `(y₀, y₁)` (objects `0, 1`) under
`blockPlusLaw` gives `(a, a')` the weight `∏_p [a_p → a'_p] · 2/(p(p - 1))`. -/
theorem blockPlusLaw_pair01 (h : ClassThreeBlock pr) (g : BlockLabel pr → BlockLabel pr → ℝ) :
    (blockPlusLaw pr h).expect (fun y => g (y (0, 0)) (y (1, 0))) =
      ∑ a : BlockLabel pr, ∑ a' : BlockLabel pr, g a a' *
        ∏ i, (if quadraticChar (ZMod (pr i)) (a' i - a i) = 1 then
          2 / ((pr i : ℝ) * ((pr i : ℝ) - 1)) else 0) := by
  unfold blockPlusLaw
  rw [expect_tensor_eq_sum]
  have hpt : ∀ z : ∀ i, Fin 3 × Fin 1 → ZMod (pr i), g (fun i => z i (0, 0)) (fun i => z i (1, 0)) =
      ∑ a : BlockLabel pr, ∑ b : BlockLabel pr, g a b *
        ∏ i, ((if z i (0, 0) = a i then (1 : ℝ) else 0) * (if z i (1, 0) = b i then 1 else 0)) := by
    intro z
    rw [Finset.sum_eq_single (fun i => z i (0, 0))]
    · rw [Finset.sum_eq_single (fun i => z i (1, 0))]
      · simp
      · intro b _ hb
        have : ∃ i, z i (1, 0) ≠ b i := by
          by_contra hc
          push Not at hc
          exact hb (funext fun i => (hc i).symm)
        obtain ⟨i, hi⟩ := this
        rw [Finset.prod_eq_zero (mem_univ i) (by simp [hi]), mul_zero]
      · intro h'
        exact absurd (mem_univ _) h'
    · intro a _ ha
      have : ∃ i, z i (0, 0) ≠ a i := by
        by_contra hc
        push Not at hc
        exact ha (funext fun i => (hc i).symm)
      obtain ⟨i, hi⟩ := this
      refine sum_eq_zero fun b _ => ?_
      rw [Finset.prod_eq_zero (mem_univ i) (by simp [hi]), mul_zero]
    · intro h'
      exact absurd (mem_univ _) h'
  simp only [hpt, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun b _ => ?_
  have e : ∀ z : ∀ i, Fin 3 × Fin 1 → ZMod (pr i),
      (∏ i, (plusLaw (ZMod (pr i)) (h.ringChar_ne i) (h.card_mod i) (h.kP_pos' i)).weight (z i)) *
        (g a b * ∏ i, ((if z i (0, 0) = a i then (1 : ℝ) else 0) *
          (if z i (1, 0) = b i then 1 else 0))) =
      g a b * ∏ i, ((plusLaw (ZMod (pr i)) (h.ringChar_ne i) (h.card_mod i)
        (h.kP_pos' i)).weight (z i) * ((if z i (0, 0) = a i then (1 : ℝ) else 0) *
          (if z i (1, 0) = b i then 1 else 0))) := by
    intro z
    simp only [Finset.prod_mul_distrib]
    ring
  simp only [e, ← mul_sum]
  congr 1
  have hfac : ∀ i, (if quadraticChar (ZMod (pr i)) (b i - a i) = 1 then
      2 / ((pr i : ℝ) * ((pr i : ℝ) - 1)) else 0) =
      ∑ w : Fin 3 × Fin 1 → ZMod (pr i), (plusLaw (ZMod (pr i)) (h.ringChar_ne i) (h.card_mod i)
        (h.kP_pos' i)).weight w * ((if w (0, 0) = a i then (1 : ℝ) else 0) *
          (if w (1, 0) = b i then 1 else 0)) := by
    intro i
    have hpl := plusLaw_pair01 (h.ringChar_ne i) (h.card_mod i) (h.kP_pos' i)
      (fun x y => (if x = a i then (1 : ℝ) else 0) * (if y = b i then 1 else 0))
    unfold FiniteLaw.expect at hpl
    rw [hpl, ZMod.card]
    symm
    rw [Finset.sum_eq_single (a i)]
    · rw [Finset.sum_eq_single (b i)]
      · simp only [↓reduceIte, mul_one]
      · intro b' _ hb'
        simp only [hb', ↓reduceIte, mul_zero, ite_self]
      · intro h'
        exact absurd (mem_univ _) h'
    · intro a' _ ha'
      refine sum_eq_zero fun b' _ => ?_
      simp only [ha', ↓reduceIte, zero_mul, mul_zero, ite_self]
    · intro h'
      exact absurd (mem_univ _) h'
  rw [prod_congr rfl fun i _ => hfac i, Fintype.prod_sum]

end Sarkozy.PartVRecords
