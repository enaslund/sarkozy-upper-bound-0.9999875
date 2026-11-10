module

public import Sarkozy.Influence.Pinned
public import Sarkozy.Influence.Monotone

/-!
# Pinned influence, XI: part (a) and the single-label form of part (b)

* `pinned_influence_a`: the chain of `prop:middle-negative` (a),
  `ρ(y_i; y_j | y_{S'} = s') ≤ [(I - 𝓔_{F'F'})^{-1}]_ij ≤ [(I - 𝓔)^{-1}]_ij ≤ ε_ij + e²/(1-e)`,
  from the first inequality. In the paper that inequality is `lem:mid:allpin`, which is not
  formalized here and is taken as the hypothesis `hallpin`.
* `single_label_maxCorr_le`: part (b) for the empty pinning, `X = {v}` and `Y = U \ {v}`.
  This bounds the correlation between one label and all the others, which is the input of
  the unit-constant argument (`slotForm_centeredL2_of_maxCorr`).
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Influence

open Sarkozy Sarkozy.Peyre

variable {U : Type*} [Fintype U] [DecidableEq U]

omit [Fintype U] in
/-- **`prop:middle-negative` (a)**, given its first inequality (`lem:mid:allpin`) as the
hypothesis `hallpin`. Here `Q` and `Q'` are `(I - E)^{-1}` on `F` and on `F' ⊆ F`. -/
theorem pinned_influence_a {F F' : Finset U} (hF : F' ⊆ F) (E Q Q' : U → U → ℝ)
    (hE0 : ∀ i j, 0 ≤ E i j) {e : ℝ} (he0 : 0 ≤ e) (he1 : e < 1) (hE : OpBound F F E e)
    (hQ : ∀ i ∈ F, ∀ j ∈ F, Q i j = (if i = j then 1 else 0) + ∑ l ∈ F, E i l * Q l j)
    (hQ' : ∀ i ∈ F', ∀ j ∈ F', Q' i j = (if i = j then 1 else 0) + ∑ l ∈ F', E i l * Q' l j)
    {i j : U} (hi : i ∈ F') (hj : j ∈ F') (hij : i ≠ j) {ρ : ℝ} (hallpin : ρ ≤ Q' i j) :
    ρ ≤ Q' i j ∧ Q' i j ≤ Q i j ∧ Q i j ≤ E i j + e ^ 2 / (1 - e) :=
  ⟨hallpin, inverse_restrict_le hF E Q Q' hE0 he0 he1 hE hQ hQ' hi hj,
    inverse_offdiag_le F E Q he0 he1 hE hQ (hF hi) (hF hj) hij⟩

omit [Fintype U] [DecidableEq U] in
theorem pinEvent_empty {p : ℕ} (s : U → ZMod p) :
    pinEvent (∅ : Finset U) s = fun _ => True := by
  funext ω
  simp [pinEvent]

theorem condLaw_true {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (h : 0 < prob μ (fun _ => True)) :
    condLaw μ (fun _ => True) h = μ := by
  have hp : prob μ (fun _ : Ω => True) = 1 := by
    unfold prob
    rw [show ind (fun _ : Ω => True) = fun _ => 1 from funext fun ω => ind_of_pos trivial,
      FiniteLaw.expect_const]
  apply law_ext
  intro ω
  rw [cond_weight, ind_of_pos trivial, hp, one_mul, div_one]

/-- **Single label against the others**: `prop:middle-negative` (b) for the empty pinning,
`X = {v}` and `Y = U \ {v}`. If the pairwise bounds of part (a) hold for every feasible
pinning, `‖E‖ ≤ e < 1`, and `Λ ≥ ‖E_{v, U \ {v}}‖`, then
`ρ(y_v; y_{U \ {v}}) ≤ min{1, Λ + e²/(1-e)}`. -/
theorem single_label_maxCorr_le {p : ℕ} [NeZero p] (μ : FiniteLaw (U → ZMod p))
    (E : U → U → ℝ) {e : ℝ} (he0 : 0 ≤ e) (he1 : e < 1) (hE : OpBound Finset.univ Finset.univ E e)
    (Q : U → U → ℝ)
    (hQ : ∀ i ∈ (Finset.univ : Finset U), ∀ j ∈ (Finset.univ : Finset U),
      Q i j = (if i = j then 1 else 0) + ∑ l ∈ Finset.univ, E i l * Q l j)
    (ha : ∀ (S'' : Finset U) (s'' : U → ZMod p),
      ∀ h : 0 < prob μ (pinEvent S'' s''), ∀ i ∈ free S'', ∀ j ∈ free S'', i ≠ j →
        maxCorr (condLaw μ (pinEvent S'' s'') h) (fun ω => ω i) (fun ω => ω j) ≤ Q i j)
    (v : U) {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : OpBound {v} (Finset.univ.erase v) E Λ) :
    maxCorr μ (fun z => z v) (fun z (u : {u // u ≠ v}) => z u) ≤ min 1 (Λ + e ^ 2 / (1 - e)) := by
  classical
  set s : U → ZMod p := fun _ => 0 with hs
  have hfree : free (∅ : Finset U) = Finset.univ := by simp [free]
  have hprob : 0 < prob μ (pinEvent (∅ : Finset U) s) := by
    rw [pinEvent_empty]
    unfold prob
    rw [show ind (fun _ : U → ZMod p => True) = fun _ => 1 from funext fun ω => ind_of_pos trivial,
      FiniteLaw.expect_const]
    exact one_pos
  have hE' : OpBound (free ∅) (free ∅) E e := by rw [hfree]; exact hE
  have hQ' : ∀ i ∈ free (∅ : Finset U), ∀ j ∈ free (∅ : Finset U),
      Q i j = (if i = j then 1 else 0) + ∑ l ∈ free ∅, E i l * Q l j := by
    rw [hfree]; exact hQ
  have hb := pinned_influence_b μ ∅ s E he0 he1 hE' Q hQ'
    (fun S'' s'' _ h i hi j hj hij => ha S'' s'' h i hi j hj hij) ∅ s
    ⟨Finset.Subset.refl _, fun w hw => absurd hw (Finset.notMem_empty w)⟩ hprob {v}
    (Finset.univ.erase v) (by rw [hfree]; exact Finset.subset_univ _)
    (by rw [hfree]; exact Finset.subset_univ _)
    (Finset.disjoint_singleton_left.mpr (Finset.notMem_erase v _)) hΛ0 hΛ
  have hcond : condLaw μ (pinEvent (∅ : Finset U) s) hprob = μ := by
    have h1 : 0 < prob μ (fun _ : U → ZMod p => True) := by
      rw [← pinEvent_empty s]; exact hprob
    rw [cond_congr μ (pinEvent_empty s) hprob h1, condLaw_true]
  rw [hcond] at hb
  have hc : maxCorr μ (fun z => z v) (fun z (u : {u // u ≠ v}) => z u) =
      maxCorr μ (fun ω (w : ({v} : Finset U)) => ω w)
        (fun ω (w : (Finset.univ.erase v : Finset U)) => ω w) := by
    apply maxCorr_congr
    · intro ω ω'
      constructor
      · intro h
        funext w
        have hw : (w : U) = v := Finset.mem_singleton.mp w.2
        simp only [hw, h]
      · intro h
        have := congrFun h ⟨v, Finset.mem_singleton_self v⟩
        simpa using this
    · intro ω ω'
      constructor
      · intro h
        funext w
        have hw : (w : U) ≠ v := Finset.ne_of_mem_erase w.2
        have := congrFun h ⟨w, hw⟩
        simpa using this
      · intro h
        funext u
        have := congrFun h ⟨u, Finset.mem_erase.mpr ⟨u.2, Finset.mem_univ _⟩⟩
        simpa using this
  rw [hc]
  exact hb

/-- A uniform bound for the influence entries: `ε_ij ≤ H_w · 2^{(d_i+d_j)/2} · (r + r²)`. -/
theorem influence_le (G : OrientedGraph U) (p : ℕ) {w : ℝ} (hw : -1 ≤ w) (i j : U) :
    influence G p w i j ≤ Hw w * √2 ^ (G.deg i + G.deg j) * (rp p + rp p ^ 2) := by
  classical
  have hH := Hw_nonneg hw
  have hr := rp_nonneg p
  have h2 : (1 : ℝ) ≤ √2 := by
    rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hpow : √2 ^ (G.deg i + G.deg j - 2) ≤ √2 ^ (G.deg i + G.deg j) :=
    pow_le_pow_right₀ h2 (Nat.sub_le _ _)
  have hbound : 0 ≤ Hw w * √2 ^ (G.deg i + G.deg j) * (rp p + rp p ^ 2) :=
    mul_nonneg (mul_nonneg hH (pow_nonneg (by positivity) _)) (add_nonneg hr (sq_nonneg _))
  unfold influence
  split_ifs
  · exact hbound
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hH)
      (add_nonneg hr (sq_nonneg _))
  · refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hH (pow_nonneg (by positivity) _))
    linarith

omit [DecidableEq U] in
/-- The influence matrix on `F` has norm at most `q` whenever every row sum over `F` is at
most `q` (Schur test; `𝓔` is symmetric and nonnegative). -/
theorem influence_opBound (G : OrientedGraph U) (p : ℕ) {w : ℝ} (hw : -1 ≤ w)
    (F : Finset U) {q : ℝ} (hq : 0 ≤ q) (hrow : ∀ i ∈ F, ∑ j ∈ F, influence G p w i j ≤ q) :
    OpBound F F (influence G p w) q := by
  have h := opBound_schur (R := F) (C := F) (influence_nonneg G p hw) hq hq hrow
    (fun j hj => by
      rw [Finset.sum_congr rfl (fun i _ => influence_symm G p w i j)]
      exact hrow j hj)
  rwa [Real.sqrt_mul_self hq] at h

theorem Hw_mono {w w' : ℝ} (hw : 0 ≤ w) (hww' : w ≤ w') (hw' : w' < 1) : Hw w ≤ Hw w' := by
  unfold Hw
  have h1 : 0 < 1 - w' := by linarith
  have h2 : 0 < 1 - w := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h3 : (1 - w') ^ 2 ≤ (1 - w) ^ 2 := by nlinarith
  nlinarith [mul_le_mul h3 (by linarith : 1 + w ≤ 1 + w') (by linarith) (sq_nonneg (1 - w))]

theorem rp_anti {p p₀ : ℕ} (hp₀ : 0 < p₀) (hp : p₀ ≤ p) : rp p ≤ rp p₀ := by
  unfold rp
  have h0 : (0 : ℝ) < p₀ := by exact_mod_cast hp₀
  apply one_div_le_one_div_of_le (Real.sqrt_pos.mpr h0)
  exact Real.sqrt_le_sqrt (by exact_mod_cast hp)

/-- **Monotonicity in `p`** (the remark that the influence data are admissible functions of
`r`): for `p ≥ p₀` and count errors `0 ≤ w ≤ w₀ < 1`, `ε_ij(p, w) ≤ ε_ij(p₀, w₀)`. -/
theorem influence_mono (G : OrientedGraph U) {p p₀ : ℕ} (hp₀ : 0 < p₀) (hp : p₀ ≤ p)
    {w w₀ : ℝ} (hw : 0 ≤ w) (hww₀ : w ≤ w₀) (hw₀ : w₀ < 1) (i j : U) :
    influence G p w i j ≤ influence G p₀ w₀ i j := by
  classical
  have hr := rp_anti hp₀ hp
  have hr0 := rp_nonneg p
  have hH := Hw_mono hw hww₀ hw₀
  have hH0 := Hw_nonneg (by linarith : -1 ≤ w)
  have hs : ∀ k : ℕ, (0 : ℝ) ≤ √2 ^ k := fun k => pow_nonneg (Real.sqrt_nonneg _) k
  have hr2 : rp p ^ 2 ≤ rp p₀ ^ 2 := pow_le_pow_left₀ hr0 hr 2
  unfold influence
  split_ifs
  · exact le_refl 0
  · exact mul_le_mul (mul_le_mul_of_nonneg_right hH (hs _)) (add_le_add hr hr2)
      (add_nonneg hr0 (sq_nonneg _)) (mul_nonneg (Hw_nonneg (by linarith)) (hs _))
  · exact mul_le_mul (mul_le_mul_of_nonneg_right hH (hs _)) hr2 (sq_nonneg _)
      (mul_nonneg (Hw_nonneg (by linarith)) (hs _))

end Sarkozy.Influence
