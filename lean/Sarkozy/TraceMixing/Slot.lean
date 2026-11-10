module

public import Sarkozy.TraceMixing.Kernel
public import Sarkozy.Labellings.GraphLaw

/-!
# One slot of a graph law (`lem:trace-mixing`(a))

`paper/sections/12_labellings.tex`, `lem:trace-mixing`(a). `F` is a finite field of odd
characteristic with `q` elements (`F = 𝔽_p`, `q = p`, in the paper), `G` an oriented graph on
`W` with `n = |W|` vertices, `λ = λ_q(G)` its graph law (`Sarkozy.Labellings.graphLaw`), `v` a
vertex of degree `d`, and `T` the conditional operator of `λ` from slot `v` to the other slots
(`condOp (slotJoint λ v)`, `def:mixing`).

* `feasible_affine`, `graphLaw_weight_affine`: the square-affine maps `x ↦ αx + β`
  (`χ(α) = 1`), acting coordinatewise, preserve `Inj_q(G)` and hence `λ`.
* `slotJoint_weight_comap`, `srcWeight_graphSlot`: the joint law of `(z_v, z_{W∖v})` is
  invariant, and the one-slot marginal is uniform.
* `gramSlot_translate`, `gramSlot_dilate`: `S = T^*T` commutes with translations and square
  dilations (step 1 of the proof).
* `trace_gramSlot_le`: `tr S = q E[1/|Φ_v|] ≤ 2^d/(1 - w)` (steps 3 and 4), from the one-step
  count `card_vertexAdmissible`.
* `trace_mixing_slot_graded` and `trace_mixing_slot` (the lemma, with the coarse error
  `e_d(q, n-1)` of the paper): for `E f = 0`,
  `‖T f‖² ≤ 2/(q-1) · (2^d/(1 - w) - 1) · ‖f‖²`. Step 2 (diagonalization in the additive
  characters) is replaced by `Sarkozy.TraceMixing.twin_bound`.
* `isMixing_graphLaw_slot`: the same bound as `(c, v)`-mixing in the sense of
  `Sarkozy.Mixing.IsMixing` (`def:mixing`).

Functions are real-valued; `T` is real, so the bound for complex `f` follows by applying it to
the real and imaginary parts.
-/

@[expose] public section

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.TraceMixing

open Sarkozy.Mixing Sarkozy.Labellings

/-! ## Error terms -/

/-- The graded lower count error `e^-_t(z) = (a_t √q + b_t + 2^t z)/q` (`eq:graphs:graded`,
`r = q^{-1/2}`: `e^-_t(z) = a_t r + b_t r² + z 2^t r²`). -/
noncomputable def lowerErr (q : ℝ) (t z : ℕ) : ℝ := (softError q t + 2 ^ t * z) / q

/-- The coarse count error `e_t(q, n) = 2^t (h_t r + n r²)`, `h_t = t/2 - 1 + 2^{-t}`,
`r = q^{-1/2}` (`eq:graphs:et`). -/
noncomputable def coarseErr (q : ℝ) (t n : ℕ) : ℝ :=
  2 ^ t * (((t : ℝ) / 2 - 1 + (1 / 2) ^ t) * (Real.sqrt q)⁻¹ + n / q)

/-- `a_t + b_t = 2^t h_t` (`it:et:compare`). -/
theorem gradedA_add_gradedB (t : ℕ) :
    gradedA t + gradedB t = 2 ^ t * ((t : ℝ) / 2 - 1 + (1 / 2) ^ t) := by
  unfold gradedA gradedB
  by_cases ht : t = 0
  · subst ht
    norm_num
  · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, (Nat.succ_pred_eq_of_ne_zero ht).symm⟩
    have hp : (2 : ℝ) ^ (s + 1) * (1 / 2) ^ (s + 1) = 1 := by
      rw [← mul_pow]
      norm_num
    rw [ite_eq_right ht, ite_eq_right ht, mul_add, hp, Nat.add_sub_cancel]
    push_cast
    ring

/-- **`it:et:compare`**: `e^-_t(z) ≤ e_t(q, z)` for `q ≥ 1`. -/
theorem lowerErr_le_coarseErr {q : ℝ} (hq : 1 ≤ q) (t z : ℕ) :
    lowerErr q t z ≤ coarseErr q t z := by
  have hq0 : 0 < q := by linarith
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hsq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq0.le
  have hs1 : 1 ≤ Real.sqrt q := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hq
  have hab := gradedA_add_gradedB t
  have hb := gradedB_nonneg t
  set H : ℝ := (t : ℝ) / 2 - 1 + (1 / 2) ^ t with hH
  unfold lowerErr coarseErr softError
  rw [div_le_iff₀ hq0]
  have key : gradedA t * Real.sqrt q + gradedB t ≤ 2 ^ t * H * Real.sqrt q := by
    rw [← hab]
    nlinarith
  have hinv : (Real.sqrt q)⁻¹ * q = Real.sqrt q := by
    calc (Real.sqrt q)⁻¹ * q = (Real.sqrt q)⁻¹ * (Real.sqrt q * Real.sqrt q) := by rw [hsq]
      _ = Real.sqrt q := by rw [← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
  have hz : (z : ℝ) / q * q = z := div_mul_cancel₀ _ hq0.ne'
  have hexp : 2 ^ t * (H * (Real.sqrt q)⁻¹ + (z : ℝ) / q) * q =
      2 ^ t * H * Real.sqrt q + 2 ^ t * z := by
    rw [mul_assoc, add_mul, mul_assoc H, hinv, hz]
    ring
  rw [hexp]
  linarith

/-- The degree `deg_G(v)`: the number of vertices joined to `v` by an edge (either
orientation). -/
noncomputable def degree {W : Type*} [Fintype W] [DecidableEq W] (G : OrientedGraph W) (v : W) :
    ℕ :=
  nbrCount G (univ.erase v) v

/-! ## Square-affine invariance -/

section Invariance

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {W : Type*} [Fintype W] [DecidableEq W]

omit [Fintype F] [DecidableEq F] in
theorem ne_zero_of_quadraticChar_eq_one [Fintype F] [DecidableEq F] {α : F}
    (hα : quadraticChar F α = 1) : α ≠ 0 := by
  intro h
  rw [h, quadraticChar_zero] at hα
  exact zero_ne_one hα

/-- The affine bijection `x ↦ αx + β`, `α ≠ 0`. -/
def affEquiv {α : F} (hα : α ≠ 0) (β : F) : F ≃ F where
  toFun x := α * x + β
  invFun y := α⁻¹ * (y - β)
  left_inv x := by
    simp only
    rw [add_sub_cancel_right, ← mul_assoc, inv_mul_cancel₀ hα, one_mul]
  right_inv y := by
    simp only
    rw [← mul_assoc, mul_inv_cancel₀ hα, one_mul, sub_add_cancel]

omit [Fintype F] [DecidableEq F] in
theorem affEquiv_apply {α : F} (hα : α ≠ 0) (β x : F) : affEquiv hα β x = α * x + β := rfl

omit [Fintype W] [DecidableEq W] in
/-- Square-affine maps preserve feasibility. -/
theorem feasible_affine (G : OrientedGraph W) {α : F} (hα : quadraticChar F α = 1) (β : F)
    (A : Finset W) (z : W → F) :
    Feasible F G A (fun w => α * z w + β) ↔ Feasible F G A z := by
  have hα0 := ne_zero_of_quadraticChar_eq_one hα
  have hdiff (a b : W) : α * z b + β - (α * z a + β) = α * (z b - z a) := by ring
  constructor
  · rintro ⟨hinj, hedge⟩
    refine ⟨fun a ha b hb hab => hinj a ha b hb (by simp only [hab]), fun e he h1 h2 => ?_⟩
    have := hedge e he h1 h2
    simp only [hdiff, map_mul, hα, one_mul] at this
    exact this
  · rintro ⟨hinj, hedge⟩
    refine ⟨fun a ha b hb hab => hinj a ha b hb ?_, fun e he h1 h2 => ?_⟩
    · exact mul_left_cancel₀ hα0 (add_right_cancel hab)
    · simp only [hdiff, map_mul, hα, one_mul]
      exact hedge e he h1 h2

theorem mem_injLabellings_iff (G : OrientedGraph W) (y : W → F) :
    y ∈ injLabellings F G ↔ Feasible F G univ y := by
  unfold injLabellings
  simp only [mem_filter, mem_univ, true_and]

/-- Square-affine maps preserve the graph law. -/
theorem graphLaw_weight_affine (G : OrientedGraph W) (hne : (injLabellings F G).Nonempty)
    {α : F} (hα : quadraticChar F α = 1) (β : F) (z : W → F) :
    (graphLaw G hne).weight (fun w => α * z w + β) = (graphLaw G hne).weight z := by
  have hiff : (fun w => α * z w + β) ∈ injLabellings F G ↔ z ∈ injLabellings F G := by
    rw [mem_injLabellings_iff, mem_injLabellings_iff, feasible_affine G hα β univ z]
  unfold graphLaw
  simp only []
  by_cases hz : z ∈ injLabellings F G
  · rw [ite_eq_left (hiff.mpr hz), ite_eq_left hz]
  · rw [ite_eq_right (fun h => hz (hiff.mp h)), ite_eq_right hz]

end Invariance

/-! ## The slot joint law -/

section SlotJoint

variable {V Y : Type*} [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y]

/-- A law invariant under a coordinatewise bijection `φ` has an invariant slot joint law. -/
theorem slotJoint_weight_comap (ρ : FiniteLaw (V → Y)) (v : V) (φ : Y ≃ Y)
    (hρ : ∀ z, ρ.weight (fun w => φ (z w)) = ρ.weight z) (x : Y)
    (r : {w // w ≠ v} → Y) :
    (slotJoint ρ v).weight (φ x, fun u => φ (r u)) = (slotJoint ρ v).weight (x, r) := by
  unfold slotJoint FiniteLaw.map
  simp only []
  rw [← Equiv.sum_comp (Equiv.piCongrRight (fun _ : V => φ))]
  apply sum_congr rfl
  intro z _
  have hiff : (Equiv.funSplitAt v Y) ((Equiv.piCongrRight fun _ : V => φ) z) =
      (φ x, fun u => φ (r u)) ↔ (Equiv.funSplitAt v Y) z = (x, r) := by
    simp only [Equiv.funSplitAt_apply, Equiv.piCongrRight_apply, Pi.map_apply, Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨φ.injective h1, funext fun u => φ.injective (congrFun h2 u)⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
  by_cases h : (Equiv.funSplitAt v Y) z = (x, r)
  · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
    exact hρ z
  · rw [ite_eq_right (fun h' => h (hiff.mp h')), ite_eq_right h]

end SlotJoint

section GraphSlot

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The slot joint law of a graph law is invariant under the square-affine maps. -/
theorem graphSlot_weight_affine (G : OrientedGraph W) (hne : (injLabellings F G).Nonempty)
    (v : W) {α : F} (hα : quadraticChar F α = 1) (β : F) (x : F) (r : {w // w ≠ v} → F) :
    (slotJoint (graphLaw G hne) v).weight
        (affEquiv (ne_zero_of_quadraticChar_eq_one hα) β x,
          (Equiv.piCongrRight fun _ => affEquiv (ne_zero_of_quadraticChar_eq_one hα) β) r) =
      (slotJoint (graphLaw G hne) v).weight (x, r) :=
  slotJoint_weight_comap (graphLaw G hne) v (affEquiv (ne_zero_of_quadraticChar_eq_one hα) β)
    (fun z => graphLaw_weight_affine G hne hα β z) x r

/-- **The one-slot marginal is uniform.** -/
theorem srcWeight_graphSlot (G : OrientedGraph W) (hne : (injLabellings F G).Nonempty) (v : W)
    (x : F) : srcWeight (slotJoint (graphLaw G hne) v) x = (Fintype.card F : ℝ)⁻¹ := by
  set κ := slotJoint (graphLaw G hne) v
  have hone : quadraticChar F 1 = 1 := map_one _
  have htr (x β : F) : srcWeight κ (x + β) = srcWeight κ x := by
    have h := srcWeight_equiv κ (affEquiv (ne_zero_of_quadraticChar_eq_one hone) β)
      (Equiv.piCongrRight fun _ => affEquiv (ne_zero_of_quadraticChar_eq_one hone) β)
      (fun a b => graphSlot_weight_affine G hne v hone β a b) x
    rwa [affEquiv_apply, one_mul] at h
  have hconst (x : F) : srcWeight κ x = srcWeight κ 0 := by
    have := htr 0 x
    rwa [zero_add] at this
  have hsum := sum_srcWeight κ
  simp only [hconst, sum_const, card_univ, nsmul_eq_mul] at hsum
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [hconst]
  field_simp
  linarith

/-- `S = T^*T` commutes with the translations. -/
theorem gramSlot_translate (G : OrientedGraph W) (hne : (injLabellings F G).Nonempty) (v : W)
    (x x' β : F) :
    gram (slotJoint (graphLaw G hne) v) (x + β) (x' + β) =
      gram (slotJoint (graphLaw G hne) v) x x' := by
  have hone : quadraticChar F 1 = 1 := map_one _
  have h := gram_equiv (slotJoint (graphLaw G hne) v)
    (affEquiv (ne_zero_of_quadraticChar_eq_one hone) β)
    (Equiv.piCongrRight fun _ => affEquiv (ne_zero_of_quadraticChar_eq_one hone) β)
    (fun a b => graphSlot_weight_affine G hne v hone β a b) x x'
  rwa [affEquiv_apply, affEquiv_apply, one_mul, one_mul] at h

/-- `S = T^*T` commutes with the square dilations. -/
theorem gramSlot_dilate (G : OrientedGraph W) (hne : (injLabellings F G).Nonempty) (v : W)
    {α : F} (hα : quadraticChar F α = 1) (x x' : F) :
    gram (slotJoint (graphLaw G hne) v) (α * x) (α * x') =
      gram (slotJoint (graphLaw G hne) v) x x' := by
  have h := gram_equiv (slotJoint (graphLaw G hne) v)
    (affEquiv (ne_zero_of_quadraticChar_eq_one hα) 0)
    (Equiv.piCongrRight fun _ => affEquiv (ne_zero_of_quadraticChar_eq_one hα) 0)
    (fun a b => graphSlot_weight_affine G hne v hα 0 a b) x x'
  rwa [affEquiv_apply, affEquiv_apply, add_zero, add_zero] at h

/-- The admissible labels of `v` given the other labels contain the one-step set
`vertexAdmissible`. -/
theorem card_admissible_slot_ge (hW : WeilBound F) (G : OrientedGraph W)
    (hne : (injLabellings F G).Nonempty) (v : W) (r : {w // w ≠ v} → F)
    (hr : tgtWeight (slotJoint (graphLaw G hne) v) r ≠ 0) :
    (Fintype.card F : ℝ) * (1 - lowerErr (Fintype.card F) (degree G v) (Fintype.card W - 1)) ≤
      2 ^ degree G v * ((univ.filter fun x => (Equiv.funSplitAt v F).symm (x, r) ∈
        injLabellings F G).card : ℝ) := by
  set e := Equiv.funSplitAt v F
  set κ := slotJoint (graphLaw G hne) v
  -- a completion of `r`
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, κ.weight (x₀, r) ≠ 0 := by
    by_contra h
    push Not at h
    apply hr
    unfold tgtWeight
    exact Finset.sum_eq_zero (fun x _ => h x)
  set y := e.symm (x₀, r) with hy
  have hyinj : y ∈ injLabellings F G := by
    by_contra hn
    apply hx₀
    rw [slotJoint_weight]
    unfold graphLaw
    simp only []
    rw [ite_eq_right hn]
  have hyfeas : Feasible F G univ y := (mem_injLabellings_iff G y).mp hyinj
  have hA : Feasible F G (univ.erase v) y :=
    ⟨fun a _ b _ hab => hyfeas.1 a (mem_univ _) b (mem_univ _) hab,
      fun e' he' _ _ => hyfeas.2 e' he' (mem_univ _) (mem_univ _)⟩
  have hvA : v ∉ univ.erase v := Finset.notMem_erase v univ
  -- the one-step set is contained in the admissible labels
  have hsub : vertexAdmissible G (univ.erase v) y v ⊆
      univ.filter fun x => e.symm (x, r) ∈ injLabellings F G := by
    intro c hc
    have hfeas := feasible_insert hA hvA hc
    rw [Finset.insert_erase (mem_univ v)] at hfeas
    have hupd : Function.update y v c = e.symm (c, r) := by
      rw [Equiv.eq_symm_apply]
      have hey : e y = (x₀, r) := e.apply_symm_apply (x₀, r)
      simp only [e, Equiv.funSplitAt_apply, Prod.mk.injEq] at hey ⊢
      refine ⟨Function.update_self v c y, ?_⟩
      rw [← hey.2]
      funext u
      exact Function.update_of_ne u.2 c y
    simp only [mem_filter, mem_univ, true_and]
    rw [← hupd, mem_injLabellings_iff]
    exact hfeas
  have hcard := card_le_card hsub
  have hcount := (card_vertexAdmissible hW G hA v).2
  have hAcard : ((univ.erase v).card : ℝ) = ((Fintype.card W - 1 : ℕ) : ℝ) := by
    rw [Finset.card_erase_of_mem (mem_univ v), card_univ]
  rw [hAcard] at hcount
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hexp : (Fintype.card F : ℝ) * (1 - lowerErr (Fintype.card F) (degree G v)
      (Fintype.card W - 1)) = (Fintype.card F : ℝ) - softError (Fintype.card F) (degree G v) -
        2 ^ degree G v * ((Fintype.card W - 1 : ℕ) : ℝ) := by
    unfold lowerErr
    field_simp
    ring
  rw [hexp]
  unfold degree
  have hpow : (0 : ℝ) ≤ 2 ^ nbrCount G (univ.erase v) v := by positivity
  calc (Fintype.card F : ℝ) - softError (Fintype.card F) (nbrCount G (univ.erase v) v) -
        2 ^ nbrCount G (univ.erase v) v * ((Fintype.card W - 1 : ℕ) : ℝ)
      ≤ 2 ^ nbrCount G (univ.erase v) v * ((vertexAdmissible G (univ.erase v) y v).card : ℝ) :=
        hcount
    _ ≤ 2 ^ nbrCount G (univ.erase v) v *
          ((univ.filter fun x => e.symm (x, r) ∈ injLabellings F G).card : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) hpow

/-- **The trace (steps 3 and 4).** If `w < 1` bounds the lower count error, then
`tr S = q ∑_x G(x, x) = q E[1/|Φ_v|] ≤ 2^d/(1 - w)`. -/
theorem trace_gramSlot_le (hW : WeilBound F) (G : OrientedGraph W)
    (hne : (injLabellings F G).Nonempty) (v : W) {w : ℝ} (hw1 : w < 1)
    (hw : lowerErr (Fintype.card F) (degree G v) (Fintype.card W - 1) ≤ w) :
    (Fintype.card F : ℝ) * Matrix.trace (gram (slotJoint (graphLaw G hne) v)) ≤
      2 ^ degree G v / (1 - w) := by
  set e := Equiv.funSplitAt v F
  set κ := slotJoint (graphLaw G hne) v
  set c : ℝ := 1 / ((injLabellings F G).card : ℝ) with hc
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hw0 : 0 < 1 - w := by linarith
  set B : ℝ := 2 ^ degree G v / ((Fintype.card F : ℝ) * (1 - w)) with hB
  -- the weights take the values `0` and `c`
  have hweight (x : F) (r : {w // w ≠ v} → F) :
      κ.weight (x, r) = if e.symm (x, r) ∈ injLabellings F G then c else 0 := by
    rw [slotJoint_weight]
    unfold graphLaw
    simp only []
    rfl
  have htgt (r : {w // w ≠ v} → F) : tgtWeight κ r =
      c * ((univ.filter fun x => e.symm (x, r) ∈ injLabellings F G).card : ℝ) := by
    unfold tgtWeight
    simp only [hweight]
    rw [← Finset.sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  have hc0 : 0 < c := by
    rw [hc]
    have : (0 : ℝ) < (injLabellings F G).card := by exact_mod_cast card_pos.mpr hne
    positivity
  -- each target point contributes at most `κ_B(r) B`
  have hterm (r : {w // w ≠ v} → F) :
      tgtWeight κ r * ∑ x, condMatrix κ r x ^ 2 ≤ tgtWeight κ r * B := by
    by_cases hr : tgtWeight κ r = 0
    · rw [hr, zero_mul, zero_mul]
    · have hK (x : F) : condMatrix κ r x = κ.weight (x, r) / tgtWeight κ r := by
        unfold condMatrix
        rw [ite_eq_right hr]
      have hsq (x : F) : κ.weight (x, r) ^ 2 = c * κ.weight (x, r) := by
        rw [hweight]
        split_ifs <;> ring
      have hsum : tgtWeight κ r * ∑ x, condMatrix κ r x ^ 2 = c := by
        simp only [hK, div_pow, hsq]
        rw [← Finset.sum_div, ← Finset.mul_sum]
        have : ∑ x, κ.weight (x, r) = tgtWeight κ r := rfl
        rw [this]
        field_simp
      rw [hsum]
      set N : ℝ := ((univ.filter fun x => e.symm (x, r) ∈ injLabellings F G).card : ℝ) with hN
      have hcount : (Fintype.card F : ℝ) *
          (1 - lowerErr (Fintype.card F) (degree G v) (Fintype.card W - 1)) ≤
          2 ^ degree G v * N := card_admissible_slot_ge hW G hne v r hr
      have hlow : (Fintype.card F : ℝ) * (1 - w) ≤ (Fintype.card F : ℝ) *
          (1 - lowerErr (Fintype.card F) (degree G v) (Fintype.card W - 1)) :=
        mul_le_mul_of_nonneg_left (by linarith) hq0.le
      have hpos : (0 : ℝ) < (Fintype.card F : ℝ) * (1 - w) := mul_pos hq0 hw0
      have key : (Fintype.card F : ℝ) * (1 - w) ≤ 2 ^ degree G v * N := hlow.trans hcount
      have h1 : 1 ≤ (2 ^ degree G v * N) / ((Fintype.card F : ℝ) * (1 - w)) := by
        rw [le_div_iff₀ hpos]
        linarith
      rw [htgt r, hB]
      calc c = c * 1 := (mul_one c).symm
        _ ≤ c * ((2 ^ degree G v * N) / ((Fintype.card F : ℝ) * (1 - w))) :=
            mul_le_mul_of_nonneg_left h1 hc0.le
        _ = c * N * (2 ^ degree G v / ((Fintype.card F : ℝ) * (1 - w))) := by ring
  have htr := gram_trace κ
  have hsum : Matrix.trace (gram κ) ≤ B := by
    rw [htr]
    calc ∑ r, tgtWeight κ r * ∑ x, condMatrix κ r x ^ 2 ≤ ∑ r, tgtWeight κ r * B :=
          Finset.sum_le_sum (fun r _ => hterm r)
      _ = B := by rw [← Finset.sum_mul, sum_tgtWeight, one_mul]
  calc (Fintype.card F : ℝ) * Matrix.trace (gram κ) ≤ (Fintype.card F : ℝ) * B :=
        mul_le_mul_of_nonneg_left hsum hq0.le
    _ = 2 ^ degree G v / (1 - w) := by
        rw [hB]
        field_simp

/-- **`lem:trace-mixing`(a), one slot, graded form.** For `f` with `E f = 0`,
`‖T f‖²_{L²(λ')} ≤ 2/(q-1) · (2^d/(1 - w) - 1) · ‖f‖²_{L²(Unif)}` whenever
`e^-_d(n - 1) ≤ w < 1`. -/
theorem trace_mixing_slot_graded (hW : WeilBound F) (hF : ringChar F ≠ 2)
    (G : OrientedGraph W) (hne : (injLabellings F G).Nonempty) (v : W) {w : ℝ} (hw1 : w < 1)
    (hw : lowerErr (Fintype.card F) (degree G v) (Fintype.card W - 1) ≤ w)
    (f : F → ℝ) (hf : ∑ x, f x = 0) :
    ∑ b, tgtWeight (slotJoint (graphLaw G hne) v) b *
        condOp (slotJoint (graphLaw G hne) v) f b ^ 2 ≤
      2 / ((Fintype.card F : ℝ) - 1) * (2 ^ degree G v / (1 - w) - 1) *
        (FiniteLaw.uniform F).expect (fun x => f x ^ 2) := by
  set κ := slotJoint (graphLaw G hne) v
  have hq2 : (2 : ℝ) ≤ Fintype.card F := card_field_ge_two
  have hq0 : (0 : ℝ) < Fintype.card F := by linarith
  have hbound := twin_bound hF (gram κ) (gram_quadratic_nonneg κ)
    (gramSlot_translate G hne v) (fun α hα => gramSlot_dilate G hne v hα) f hf
  rw [gram_total κ] at hbound
  have htr := trace_gramSlot_le hW G hne v hw1 hw
  have hf2 : 0 ≤ ∑ x, f x ^ 2 := Finset.sum_nonneg (fun x _ => sq_nonneg _)
  have hcoef : 0 ≤ 2 / ((Fintype.card F : ℝ) * (Fintype.card F - 1)) := by
    apply div_nonneg (by norm_num)
    exact mul_nonneg hq0.le (by linarith)
  have hstep : 2 / ((Fintype.card F : ℝ) * (Fintype.card F - 1)) *
      ((Fintype.card F : ℝ) * Matrix.trace (gram κ) - 1) * ∑ x, f x ^ 2 ≤
      2 / ((Fintype.card F : ℝ) * (Fintype.card F - 1)) * (2 ^ degree G v / (1 - w) - 1) *
        ∑ x, f x ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ hf2
    apply mul_le_mul_of_nonneg_left _ hcoef
    linarith
  rw [energy_eq_gram]
  refine (hbound.trans hstep).trans (le_of_eq ?_)
  rw [FiniteLaw.expect_uniform]
  have hq1 : (Fintype.card F : ℝ) - 1 ≠ 0 := by linarith
  field_simp

/-- **`lem:trace-mixing`(a), one slot**, with the paper's hypothesis `e_d(q, n - 1) ≤ w < 1`
on the coarse error. -/
theorem trace_mixing_slot (hW : WeilBound F) (hF : ringChar F ≠ 2) (G : OrientedGraph W)
    (hne : (injLabellings F G).Nonempty) (v : W) {w : ℝ} (hw1 : w < 1)
    (hw : coarseErr (Fintype.card F) (degree G v) (Fintype.card W - 1) ≤ w)
    (f : F → ℝ) (hf : ∑ x, f x = 0) :
    ∑ b, tgtWeight (slotJoint (graphLaw G hne) v) b *
        condOp (slotJoint (graphLaw G hne) v) f b ^ 2 ≤
      2 / ((Fintype.card F : ℝ) - 1) * (2 ^ degree G v / (1 - w) - 1) *
        (FiniteLaw.uniform F).expect (fun x => f x ^ 2) := by
  have hq1 : (1 : ℝ) ≤ Fintype.card F := by
    have := card_field_ge_two (F := F)
    linarith
  exact trace_mixing_slot_graded hW hF G hne v hw1
    ((lowerErr_le_coarseErr hq1 _ _).trans hw) f hf

/-- `lem:trace-mixing`(a) as a mixing bound (`def:mixing`): with
`c² = 2/(q-1) · (2^d/(1 - w) - 1)`, the graph law is `(c, v)`-mixing. -/
theorem isMixing_graphLaw_slot (hW : WeilBound F) (hF : ringChar F ≠ 2) (G : OrientedGraph W)
    (hne : (injLabellings F G).Nonempty) (v : W) {w : ℝ} (hw1 : w < 1)
    (hw : lowerErr (Fintype.card F) (degree G v) (Fintype.card W - 1) ≤ w) {c : ℝ}
    (hc : 2 / ((Fintype.card F : ℝ) - 1) * (2 ^ degree G v / (1 - w) - 1) ≤ c ^ 2) :
    IsMixing (graphLaw G hne) {v} c := by
  rw [isMixing_singleton_iff]
  intro f hf
  have hsrc := srcWeight_graphSlot G hne v
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hf' : ∑ x, f x = 0 := by
    simp only [hsrc] at hf
    rw [← Finset.mul_sum] at hf
    exact (mul_eq_zero.mp hf).resolve_left (inv_ne_zero hq0.ne')
  have h := trace_mixing_slot_graded hW hF G hne v hw1 hw f hf'
  have hnorm : (FiniteLaw.uniform F).expect (fun x => f x ^ 2) =
      ∑ x, srcWeight (slotJoint (graphLaw G hne) v) x * f x ^ 2 := by
    rw [FiniteLaw.expect_uniform]
    simp only [hsrc]
    rw [← Finset.mul_sum, div_eq_inv_mul]
  rw [hnorm] at h
  have hE : 0 ≤ ∑ x, srcWeight (slotJoint (graphLaw G hne) v) x * f x ^ 2 :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (srcWeight_nonneg _ _) (sq_nonneg _))
  exact h.trans (mul_le_mul_of_nonneg_right hc hE)

end GraphSlot

end Sarkozy.TraceMixing
