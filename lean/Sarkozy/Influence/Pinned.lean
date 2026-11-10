module

public import Sarkozy.Influence.Defs
public import Sarkozy.Influence.OpBound

/-!
# Pinned influence, IV: `prop:middle-negative` and `cor:influence-schur`

The pinned influence theorem `prop:middle-negative` (`13_cuts_correlations.tex`) and its
Schur-test form `cor:influence-schur`.

* `pinned_influence_a_bound`: the last inequality of (a),
  `[(I - 𝓔)^{-1}]_ij ≤ ε_ij + e²/(1-e)`, from `‖𝓔‖ ≤ e < 1` (`inverse_offdiag_le`).
* `pinned_influence_b`: part (b), from the conditional pairwise bounds of part (a). Those
  bounds are taken as the hypothesis `ha`:
  `ρ(y_i; y_j | y_{S''} = s'') ≤ [(I - 𝓔)^{-1}]_ij` for every feasible pinning `(S'', s'')`
  extending `(S, s)` and every pair of distinct free vertices. In the paper they come from
  `lem:mid:allpin` (Kassabov–Schur elimination), which is not formalized here.
* `influence_schur`: `cor:influence-schur`, from (b) and the Schur test.

The statements hold for an arbitrary finite law `μ` on labellings `U → ZMod p`, in
particular for the graph law `λ_p(G)`; only part (a) uses the graph structure. The
influence matrix enters as an arbitrary nonnegative `E` (for (b)); in the application
`E = influence G p w`. `(I - 𝓔)^{-1}` on the free set `F` is any `Q` with `Q = I + E Q` on
`F × F`. This determines `Q` on `F × F`, and `exists_inverse` provides one.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Influence

open Sarkozy Sarkozy.Peyre

variable {U : Type*} [Fintype U] [DecidableEq U]

omit [Fintype U] [DecidableEq U] in
theorem OpBound.congr {R C : Finset U} {A B : U → U → ℝ} {Λ : ℝ} (h : OpBound R C A Λ)
    (hAB : ∀ i ∈ R, ∀ j ∈ C, A i j = B i j) : OpBound R C B Λ := by
  intro x
  have e : ∀ i ∈ R, ∑ j ∈ C, B i j * x j = ∑ j ∈ C, A i j * x j := fun i hi =>
    Finset.sum_congr rfl (fun j hj => by rw [hAB i hi j hj])
  rw [Finset.sum_congr rfl (fun i hi => by rw [e i hi])]
  exact h x

theorem free_antitone {S S' : Finset U} (h : S ⊆ S') : free S' ⊆ free S := by
  intro v hv
  simp only [free, Finset.mem_sdiff, Finset.mem_univ, true_and] at hv ⊢
  exact fun hvS => hv (h hvS)

theorem mem_free {S : Finset U} {v : U} : v ∈ free S ↔ v ∉ S := by
  simp [free]

omit [Fintype U] in
/-- `prop:middle-negative` (a), last inequality: `[(I - 𝓔)^{-1}]_ij ≤ ε_ij + e²/(1-e)` for
distinct free `i, j`, when `‖𝓔‖ ≤ e < 1`. Together with `lem:mid:allpin`
(`ρ(y_i;y_j | y_{S'} = s') ≤ [(I - 𝓔)^{-1}]_ij`) this is part (a). -/
theorem pinned_influence_a_bound (F : Finset U) (E Q : U → U → ℝ) {e : ℝ} (he0 : 0 ≤ e)
    (he1 : e < 1) (hE : OpBound F F E e)
    (hQ : ∀ i ∈ F, ∀ j ∈ F, Q i j = (if i = j then 1 else 0) + ∑ l ∈ F, E i l * Q l j)
    {i j : U} (hi : i ∈ F) (hj : j ∈ F) (hij : i ≠ j) {ρ : ℝ} (hρ : ρ ≤ Q i j) :
    ρ ≤ E i j + e ^ 2 / (1 - e) :=
  hρ.trans (inverse_offdiag_le F E Q he0 he1 hE hQ hi hj hij)

/-- **`prop:middle-negative` (b).** Let `(S, s)` be a pinning with free set `F` and `E ≥ 0`
with `‖E_{FF}‖ ≤ e < 1`. Let `Q = (I - E)^{-1}` on `F`, and suppose the pairwise bounds of
part (a): `ρ(y_i; y_j | y_{S''} = s'') ≤ Q_ij` for every feasible pinning `(S'', s'')`
extending `(S, s)` and distinct free `i, j` of `S''`. Then, for every feasible pinning
`(S', s')` extending `(S, s)` and disjoint `X, Y ⊆ F'`,
`ρ(y_X; y_Y | y_{S'} = s') ≤ min{1, Λ + e²/(1-e)}` for every bound `Λ ≥ ‖E_{XY}‖`. -/
theorem pinned_influence_b {p : ℕ} [NeZero p] (μ : FiniteLaw (U → ZMod p)) (S : Finset U)
    (s : U → ZMod p) (E : U → U → ℝ) {e : ℝ} (he0 : 0 ≤ e) (he1 : e < 1)
    (hE : OpBound (free S) (free S) E e) (Q : U → U → ℝ)
    (hQ : ∀ i ∈ free S, ∀ j ∈ free S,
      Q i j = (if i = j then 1 else 0) + ∑ l ∈ free S, E i l * Q l j)
    (ha : ∀ (S'' : Finset U) (s'' : U → ZMod p), Extends S'' s'' S s →
      ∀ h : 0 < prob μ (pinEvent S'' s''), ∀ i ∈ free S'', ∀ j ∈ free S'', i ≠ j →
        maxCorr (condLaw μ (pinEvent S'' s'') h) (fun ω => ω i) (fun ω => ω j) ≤ Q i j)
    (S' : Finset U) (s' : U → ZMod p) (hext : Extends S' s' S s)
    (hS' : 0 < prob μ (pinEvent S' s')) (X Y : Finset U) (hX : X ⊆ free S')
    (hY : Y ⊆ free S') (hXY : Disjoint X Y) {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : OpBound X Y E Λ) :
    maxCorr (condLaw μ (pinEvent S' s') hS') (fun ω (v : X) => ω v) (fun ω (v : Y) => ω v) ≤
      min 1 (Λ + e ^ 2 / (1 - e)) := by
  have hF' : free S' ⊆ free S := free_antitone hext.1
  obtain ⟨hsplit, hR⟩ := inverse_split (free S) E Q he0 he1 hE hQ
  have hc0 : 0 ≤ e ^ 2 / (1 - e) := div_nonneg (sq_nonneg e) (by linarith)
  -- the block `Q_{XY}` is `E_{XY} + R_{XY}`
  have hQXY : OpBound X Y Q (Λ + e ^ 2 / (1 - e)) := by
    have h1 := hΛ.add (hR.subset (hX.trans hF') (hY.trans hF')) hΛ0 hc0
    refine h1.congr (fun i hi j hj => ?_)
    have hij : i ≠ j := fun h => Finset.disjoint_left.mp hXY hi (h ▸ hj)
    rw [hsplit i (hF' (hX hi)) j (hF' (hY hj)), ite_eq_right hij, zero_add]
  -- nonnegativity of `Q` on `X × Y`, from part (a) at `(S', s')` itself
  have hQ0 : ∀ i ∈ X, ∀ j ∈ Y, 0 ≤ Q i j := by
    intro i hi j hj
    have hij : i ≠ j := fun h => Finset.disjoint_left.mp hXY hi (h ▸ hj)
    exact (maxCorr_nonneg _ _ _).trans (ha S' s' hext hS' i (hX hi) j (hY hj) hij)
  refine peyre_finite_cond μ (fun v ω => ω v) X Y hXY (pinEvent S' s') hS' Q hQ0
    (add_nonneg hΛ0 hc0) hQXY.toSubtype ?_
  intro i hi j hj S'' hS'' hiS hjS t h
  -- the combined pinning of `S' ∪ S''`
  set t' : U → ZMod p := fun v => if v ∈ S' then s' v else t v with ht'
  have hdisj : ∀ v ∈ S'', v ∉ S' := by
    intro v hv hvS'
    rcases hS'' v hv with hvX | hvY
    · exact (mem_free.mp (hX hvX)) hvS'
    · exact (mem_free.mp (hY hvY)) hvS'
  have hev : (fun ω : U → ZMod p => (∀ v ∈ S'', ω v = t v) ∧ pinEvent S' s' ω) =
      pinEvent (S' ∪ S'') t' := by
    funext ω
    apply propext
    constructor
    · rintro ⟨h1, h2⟩ v hv
      by_cases hvS' : v ∈ S'
      · simp only [ht', hvS', ite_true]
        exact h2 v hvS'
      · simp only [ht', hvS', ite_false]
        exact h1 v ((Finset.mem_union.mp hv).resolve_left hvS')
    · intro h3
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩
      · have := h3 v (Finset.mem_union_right _ hv)
        simp only [ht', hdisj v hv, ite_false] at this
        exact this
      · have := h3 v (Finset.mem_union_left _ hv)
        simp only [ht', hv, ite_true] at this
        exact this
  have h' : 0 < prob μ (pinEvent (S' ∪ S'') t') := hev ▸ h
  rw [cond_congr μ hev h h']
  have hext' : Extends (S' ∪ S'') t' S s := by
    refine ⟨hext.1.trans Finset.subset_union_left, fun v hv => ?_⟩
    have hvS' : v ∈ S' := hext.1 hv
    simp only [ht', hvS', ite_true]
    exact hext.2 v hv
  have hiF : i ∈ free (S' ∪ S'') := by
    rw [mem_free, Finset.mem_union, not_or]
    exact ⟨mem_free.mp (hX hi), hiS⟩
  have hjF : j ∈ free (S' ∪ S'') := by
    rw [mem_free, Finset.mem_union, not_or]
    exact ⟨mem_free.mp (hY hj), hjS⟩
  have hij : i ≠ j := fun h => Finset.disjoint_left.mp hXY hi (h ▸ hj)
  exact ha (S' ∪ S'') t' hext' h' i hiF j hjF hij

/-- **`cor:influence-schur`.** In the setting of `pinned_influence_b`, let `E ≥ 0` be
symmetric, with `c_ij = ε_ij / r`, `q ≥ max_{i ∈ F} ∑_{j ∈ F} c_ij` and `r q < 1`, so that
`‖E‖ ≤ r q` by the Schur test. For disjoint nonempty `X, Y ⊆ F'`, with
`c_X ≥ max_{u ∈ X} ∑_{v ∈ Y} c_uv` and `c_Y ≥ max_{v ∈ Y} ∑_{u ∈ X} c_uv`,
`ρ(y_X; y_Y | y_{S'} = s') ≤ r (√(c_X c_Y) + √(|X| |Y|) · r q²/(1 - r q))`. The paper's
`c_×` is `√(c_X c_Y)` with `c_X`, `c_Y` the two maxima. -/
theorem influence_schur {p : ℕ} [NeZero p] (μ : FiniteLaw (U → ZMod p)) (S : Finset U)
    (s : U → ZMod p) (E : U → U → ℝ) (hE0 : ∀ i j, 0 ≤ E i j) (hEs : ∀ i j, E i j = E j i)
    {r q : ℝ} (hr : 0 < r) (hq : 0 ≤ q) (hrq : r * q < 1)
    (hrow : ∀ i ∈ free S, ∑ j ∈ free S, E i j / r ≤ q) (Q : U → U → ℝ)
    (hQ : ∀ i ∈ free S, ∀ j ∈ free S,
      Q i j = (if i = j then 1 else 0) + ∑ l ∈ free S, E i l * Q l j)
    (ha : ∀ (S'' : Finset U) (s'' : U → ZMod p), Extends S'' s'' S s →
      ∀ h : 0 < prob μ (pinEvent S'' s''), ∀ i ∈ free S'', ∀ j ∈ free S'', i ≠ j →
        maxCorr (condLaw μ (pinEvent S'' s'') h) (fun ω => ω i) (fun ω => ω j) ≤ Q i j)
    (S' : Finset U) (s' : U → ZMod p) (hext : Extends S' s' S s)
    (hS' : 0 < prob μ (pinEvent S' s')) (X Y : Finset U) (hX : X ⊆ free S')
    (hY : Y ⊆ free S') (hXY : Disjoint X Y) (hXne : X.Nonempty) (hYne : Y.Nonempty)
    {cX cY : ℝ} (hcX : ∀ u ∈ X, ∑ v ∈ Y, E u v / r ≤ cX)
    (hcY : ∀ v ∈ Y, ∑ u ∈ X, E u v / r ≤ cY) :
    maxCorr (condLaw μ (pinEvent S' s') hS') (fun ω (v : X) => ω v) (fun ω (v : Y) => ω v) ≤
      r * (√(cX * cY) + √((X.card : ℝ) * Y.card) * (r * q ^ 2 / (1 - r * q))) := by
  have hrq0 : 0 ≤ r * q := mul_nonneg hr.le hq
  have hsum_le : ∀ (A B : Finset U) (c : ℝ) (i : U),
      ∑ j ∈ B, E i j / r ≤ c → ∑ j ∈ B, E i j ≤ r * c := by
    intro A B c i h
    rw [← Finset.sum_div, div_le_iff₀ hr] at h
    linarith
  -- `‖E_{FF}‖ ≤ r q`
  have hEF : OpBound (free S) (free S) E (r * q) := by
    have h := opBound_schur (R := free S) (C := free S) hE0 hrq0 hrq0
      (fun i hi => hsum_le (free S) (free S) q i (hrow i hi))
      (fun j hj => by
        have := hsum_le (free S) (free S) q j (hrow j hj)
        rw [Finset.sum_congr rfl (fun i _ => hEs i j)]
        exact this)
    rwa [Real.sqrt_mul_self hrq0] at h
  -- `0 ≤ c_X`, `0 ≤ c_Y`
  obtain ⟨u0, hu0⟩ := hXne
  obtain ⟨v0, hv0⟩ := hYne
  have hcX0 : 0 ≤ cX := (Finset.sum_nonneg (fun v _ => div_nonneg (hE0 u0 v) hr.le)).trans
    (hcX u0 hu0)
  have hcY0 : 0 ≤ cY := (Finset.sum_nonneg (fun u _ => div_nonneg (hE0 u v0) hr.le)).trans
    (hcY v0 hv0)
  -- `‖E_{XY}‖ ≤ r √(c_X c_Y)` by the Schur test
  have hEXY : OpBound X Y E (r * √(cX * cY)) := by
    have h := opBound_schur (R := X) (C := Y) hE0 (mul_nonneg hr.le hcX0)
      (mul_nonneg hr.le hcY0) (fun i hi => hsum_le X Y cX i (hcX i hi))
      (fun j hj => by
        have h1 := hcY j hj
        rw [← Finset.sum_div, div_le_iff₀ hr] at h1
        linarith)
    have e : √(r * cX * (r * cY)) = r * √(cX * cY) := by
      rw [show r * cX * (r * cY) = r ^ 2 * (cX * cY) by ring, Real.sqrt_mul (sq_nonneg r),
        Real.sqrt_sq hr.le]
    rwa [e] at h
  have hb := pinned_influence_b μ S s E hrq0 hrq hEF Q hQ ha S' s' hext hS' X Y hX hY hXY
    (mul_nonneg hr.le (Real.sqrt_nonneg _)) hEXY
  refine (hb.trans (min_le_right _ _)).trans ?_
  have hcard : 1 ≤ √((X.card : ℝ) * Y.card) := by
    have hX1 : (1 : ℝ) ≤ X.card := by exact_mod_cast Finset.card_pos.mpr ⟨u0, hu0⟩
    have hY1 : (1 : ℝ) ≤ Y.card := by exact_mod_cast Finset.card_pos.mpr ⟨v0, hv0⟩
    rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have h1rq : 0 < 1 - r * q := by linarith
  have hterm : 0 ≤ r * q ^ 2 / (1 - r * q) := div_nonneg (mul_nonneg hr.le (sq_nonneg q)) h1rq.le
  have e2 : (r * q) ^ 2 / (1 - r * q) = r * (r * q ^ 2 / (1 - r * q)) := by
    field_simp
  rw [e2, mul_add]
  have : r * (r * q ^ 2 / (1 - r * q)) ≤ r * (√((X.card : ℝ) * Y.card) * (r * q ^ 2 / (1 - r * q))) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hterm hcard) hr.le
  linarith

end Sarkozy.Influence
