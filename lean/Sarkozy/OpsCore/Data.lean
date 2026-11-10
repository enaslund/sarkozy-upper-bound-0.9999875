module

public import Sarkozy.OpsCore.Mono
public import Sarkozy.ClassSlack.NoMean

@[expose] public section





open Filter Finset
open scoped Topology BigOperators

namespace Sarkozy.OpsCore

open Sarkozy.ClassInputsPaper Sarkozy.EnvelopeSteps Sarkozy.MainFinal2
open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.MeanCredit Sarkozy.Companion Sarkozy.ClassSlack Sarkozy.ClassData
open Sarkozy.CancellationSteps (PaperJ0)

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
  {D : CD blockOf} {cd : ClassData D.CL} {K : Type} [Fintype K] [DecidableEq K]

/-! ## The diagonal energies at their upper prices -/

/-- **The per-selection diagonal energies at their upper prices**: `Zs_ω = π_ω · max(Y, 0)`. -/
noncomputable def zsUp (D : CD blockOf) (L : ℕ) (A : Finset ℤ) (ω : Choice (D.CL.T L)) : ℝ :=
  monomial (D.CL.π L) ω * max (D.Y L A) 0

theorem zsUp_nonneg (cd : ClassData D.CL) (L : ℕ) (A : Finset ℤ) (ω : Choice (D.CL.T L)) :
    0 ≤ zsUp D L A ω :=
  mul_nonneg (monomial_nonneg (cd.π_nonneg L) ω) (le_max_right _ _)

omit [DecidableEq K] in
/-- **`hup` at `zsUp` is a theorem** (`SelUpper` with `ε₃ = 0`, `c₃ = 0` and no remainders). -/
theorem selUpper_zsUp (labS : ∀ L, Choice (D.CL.T L) → Option K) (wt : K → ℝ)
    (wc : ∀ L, cd.ι L → K → ℝ) : SelUpper D cd labS wt (zsUp D) wc := by
  refine ⟨fun _ => 0, fun _ => le_rfl, tendsto_const_nhds, 0, le_rfl, fun _ _ _ => 0,
    fun _ _ _ => le_rfl, ?_, ?_⟩
  · refine Eventually.of_forall fun L C hC _ A _ hcount ω _ _ => ?_
    have hY := (Param.counterexample_pos (Param.Params.ofDecay TargetLedger.targetDecay) hC
      hcount).le
    unfold zsUp
    rw [max_eq_left hY]
    linarith
  · refine Eventually.of_forall fun L _ _ _ A _ _ => ?_
    simp only [mul_zero, sum_const_zero]
    unfold Comparison.remainder
    simp

/-! ## The canonical split of the class weights -/

/-- The diagonal coefficient that `hcomp` charges a selection: `diagW` of its label's type, `0`
for an unlabelled selection. -/
noncomputable def delta (labS : ∀ L, Choice (D.CL.T L) → Option K) (labK : K → PaperDiag)
    (L : ℕ) (ω : Choice (D.CL.T L)) : ℝ :=
  (labS L ω).elim 0 fun k => (diagW (labK k) : ℝ)

theorem diagW_pos (d : PaperDiag) : 0 < (diagW d : ℝ) := by
  have h1 : ((diagB d + 2366 / 100 : ℚ) : ℝ) < ((63 * diagW d : ℚ) : ℝ) := by
    exact_mod_cast diag_resid d
  have h2 : (0 : ℝ) ≤ diagB d := by exact_mod_cast diagB_nonneg d
  push_cast at h1
  linarith

omit [Fintype K] [DecidableEq K] in
theorem delta_nonneg (labS : ∀ L, Choice (D.CL.T L) → Option K) (labK : K → PaperDiag) (L : ℕ)
    (ω : Choice (D.CL.T L)) : 0 ≤ delta labS labK L ω := by
  unfold delta
  rcases labS L ω with _ | k
  · exact le_rfl
  · exact (diagW_pos _).le

/-- `P_k`: the prices of all selections labelled `k`. -/
noncomputable def Pk (cd : ClassData D.CL) (labS : ∀ L, Choice (D.CL.T L) → Option K) (L : ℕ)
    (k : K) : ℝ :=
  ∑ ω ∈ (cd.sel L).filter (fun ω => labS L ω = some k), monomial (D.CL.π L) ω

/-- `P_{ik}`: the prices of the selections of class `i` labelled `k`. -/
noncomputable def Pik (cd : ClassData D.CL) (labS : ∀ L, Choice (D.CL.T L) → Option K) (L : ℕ)
    (i : cd.ι L) (k : K) : ℝ :=
  ∑ ω ∈ (cd.clsSel L i).filter (fun ω => labS L ω = some k), monomial (D.CL.π L) ω

omit [Fintype K] in
theorem Pik_nonneg (labS : ∀ L, Choice (D.CL.T L) → Option K) (L : ℕ) (i : cd.ι L) (k : K) :
    0 ≤ Pik cd labS L i k :=
  sum_nonneg fun ω _ => monomial_nonneg (cd.π_nonneg L) ω

omit [Fintype K] in
theorem Pk_nonneg (labS : ∀ L, Choice (D.CL.T L) → Option K) (L : ℕ) (k : K) :
    0 ≤ Pk cd labS L k :=
  sum_nonneg fun ω _ => monomial_nonneg (cd.π_nonneg L) ω

omit [Fintype K] in
/-- The classes split a part of each label: `∑_i P_{ik} ≤ P_k`. -/
theorem sum_Pik_le (labS : ∀ L, Choice (D.CL.T L) → Option K) (L : ℕ) (k : K) :
    ∑ i, Pik cd labS L i k ≤ Pk cd labS L k := by
  set S := (cd.sel L).filter (fun ω => labS L ω = some k) with hS
  set f : Choice (D.CL.T L) → ℝ := fun ω => monomial (D.CL.π L) ω
  have hf : ∀ ω, 0 ≤ f ω := fun ω => monomial_nonneg (cd.π_nonneg L) ω
  have hfib := sum_fiberwise S (cd.cls L) f
  rw [Fintype.sum_option] at hfib
  have e : ∀ i, Pik cd labS L i k = ∑ ω ∈ S with cd.cls L ω = some i, f ω := by
    intro i
    unfold Pik
    rw [hS, filter_filter, filter_filter]
    refine sum_congr ?_ fun _ _ => rfl
    ext ω
    simp only [mem_filter]
    tauto
  have h0 : 0 ≤ ∑ ω ∈ S with cd.cls L ω = none, f ω := sum_nonneg fun ω _ => hf ω
  rw [sum_congr rfl fun i _ => e i]
  unfold Pk
  rw [← hS]
  linarith

/-- The share of the classes in label `k`: `S_k = ∑_i P_{ik}/P_k ∈ [0, 1]`. -/
noncomputable def Sk (cd : ClassData D.CL) (labS : ∀ L, Choice (D.CL.T L) → Option K) (L : ℕ)
    (k : K) : ℝ :=
  ∑ i, Pik cd labS L i k / Pk cd labS L k

omit [Fintype K] in
theorem Sk_le_one (labS : ∀ L, Choice (D.CL.T L) → Option K) (L : ℕ) (k : K) :
    Sk cd labS L k ≤ 1 := by
  unfold Sk
  rw [← sum_div]
  exact div_le_one_of_le₀ (sum_Pik_le labS L k) (Pk_nonneg labS L k)

omit [Fintype K] in
theorem Sk_nonneg (labS : ∀ L, Choice (D.CL.T L) → Option K) (L : ℕ) (k : K) :
    0 ≤ Sk cd labS L k :=
  sum_nonneg fun i _ => div_nonneg (Pik_nonneg labS L i k) (Pk_nonneg labS L k)

/-- **The canonical class weights**: class `i` gets `2 diagW(labK k) · P_{ik}/P_k` of label `k`,
and the share `1 − S_k` of the selections in no class stays on the given `wc`. -/
noncomputable def wcCanon (cd : ClassData D.CL) (labS : ∀ L, Choice (D.CL.T L) → Option K)
    (labK : K → PaperDiag) (wc : ∀ L, cd.ι L → K → ℝ) (L : ℕ) (i : cd.ι L) (k : K) : ℝ :=
  2 * (diagW (labK k) : ℝ) * (Pik cd labS L i k / Pk cd labS L k) +
    (1 - Sk cd labS L k) * wc L i k

omit [Fintype K] in
theorem wcCanon_nonneg (labS : ∀ L, Choice (D.CL.T L) → Option K) (labK : K → PaperDiag)
    {wc : ∀ L, cd.ι L → K → ℝ} (hwc : ∀ L i k, 0 ≤ wc L i k) (L : ℕ) (i : cd.ι L) (k : K) :
    0 ≤ wcCanon cd labS labK wc L i k := by
  unfold wcCanon
  have h1 : 0 ≤ 1 - Sk cd labS L k := by linarith [Sk_le_one (cd := cd) labS L k]
  have h2 := div_nonneg (Pik_nonneg (cd := cd) labS L i k) (Pk_nonneg (cd := cd) labS L k)
  have h3 := (diagW_pos (labK k)).le
  exact add_nonneg (mul_nonneg (mul_nonneg two_pos.le h3) h2) (mul_nonneg h1 (hwc L i k))

omit [Fintype K] in
/-- **`hwHalf` is preserved by the canonical split.** -/
theorem weightsHalf_wcCanon (labS : ∀ L, Choice (D.CL.T L) → Option K) (labK : K → PaperDiag)
    {wc : ∀ L, cd.ι L → K → ℝ} (hw : WeightsHalf D cd labK wc) :
    WeightsHalf D cd labK (wcCanon cd labS labK wc) := by
  intro L k
  unfold wcCanon
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, hw L k]
  have : ∑ i, Pik cd labS L i k / Pk cd labS L k = Sk cd labS L k := rfl
  rw [this]
  ring

omit [Fintype K] in
/-- The aggregated upper-priced energy of a label: `agg_k(zsUp) = ½ P_k Y⁺`. -/
theorem agg_zsUp (labS : ∀ L, Choice (D.CL.T L) → Option K) (L : ℕ) (A : Finset ℤ) (k : K) :
    agg (cd.sel L) (labS L) (wtHalf K) (zsUp D L A) k =
      1 / 2 * Pk cd labS L k * max (D.Y L A) 0 := by
  unfold agg Pk zsUp wtHalf
  rw [mul_assoc, sum_mul, mul_sum]

/-- `∑_k δ_k P_{ik} = ∑_{ω ∈ 𝒞_i} δ_ω π_ω`. -/
theorem sum_diagW_Pik (labS : ∀ L, Choice (D.CL.T L) → Option K) (labK : K → PaperDiag)
    (L : ℕ) (i : cd.ι L) :
    ∑ k, (diagW (labK k) : ℝ) * Pik cd labS L i k =
      ∑ ω ∈ cd.clsSel L i, delta labS labK L ω * monomial (D.CL.π L) ω := by
  have hfib := sum_fiberwise (cd.clsSel L i) (labS L)
    (fun ω => delta labS labK L ω * monomial (D.CL.π L) ω)
  rw [Fintype.sum_option] at hfib
  have h0 : ∑ ω ∈ cd.clsSel L i with labS L ω = none,
      delta labS labK L ω * monomial (D.CL.π L) ω = 0 := by
    refine sum_eq_zero fun ω hω => ?_
    rw [delta, (mem_filter.mp hω).2]
    simp
  rw [h0, zero_add] at hfib
  rw [← hfib]
  refine sum_congr rfl fun k _ => ?_
  unfold Pik
  rw [mul_sum]
  refine sum_congr rfl fun ω hω => ?_
  rw [delta, (mem_filter.mp hω).2]
  simp

/-- **The diagonal budget of a class at the canonical data**: at `Zs = zsUp`, `wc = wcCanon`,
`∑_k wc_{ik} agg_k(Zs) ≥ (∑_{ω ∈ 𝒞_i} δ_ω π_ω) · Y⁺`. -/
theorem wz_canon_ge (labS : ∀ L, Choice (D.CL.T L) → Option K) (labK : K → PaperDiag)
    {wc : ∀ L, cd.ι L → K → ℝ} (hwc : ∀ L i k, 0 ≤ wc L i k) (L : ℕ) (A : Finset ℤ)
    (i : cd.ι L) :
    (∑ ω ∈ cd.clsSel L i, delta labS labK L ω * monomial (D.CL.π L) ω) * max (D.Y L A) 0 ≤
      ∑ k, wcCanon cd labS labK wc L i k *
        agg (cd.sel L) (labS L) (wtHalf K) (zsUp D L A) k := by
  rw [← sum_diagW_Pik, sum_mul]
  refine sum_le_sum fun k _ => ?_
  rw [agg_zsUp]
  set Y := max (D.Y L A) 0
  have hY : 0 ≤ Y := le_max_right _ _
  have hP := Pk_nonneg (cd := cd) labS L k
  have hPi := Pik_nonneg (cd := cd) labS L i k
  have h1 : 0 ≤ 1 - Sk cd labS L k := by linarith [Sk_le_one (cd := cd) labS L k]
  have hrest : 0 ≤ (1 - Sk cd labS L k) * wc L i k * (1 / 2 * Pk cd labS L k * Y) := by
    have := hwc L i k
    positivity
  unfold wcCanon
  rcases hP.eq_or_lt with h0 | hpos
  · -- `P_k = 0`, hence `P_{ik} = 0`
    have hle : Pik cd labS L i k ≤ Pk cd labS L k :=
      (single_le_sum (f := fun i => Pik cd labS L i k) (fun i _ => Pik_nonneg labS L i k)
        (mem_univ i)).trans (sum_Pik_le labS L k)
    have hz : Pik cd labS L i k = 0 := le_antisymm (h0 ▸ hle) hPi
    rw [hz, ← h0]
    simp
  · have e : 2 * (diagW (labK k) : ℝ) * (Pik cd labS L i k / Pk cd labS L k) *
        (1 / 2 * Pk cd labS L k * Y) = (diagW (labK k) : ℝ) * Pik cd labS L i k * Y := by
      field_simp
    rw [add_mul, e]
    linarith

end Sarkozy.OpsCore
