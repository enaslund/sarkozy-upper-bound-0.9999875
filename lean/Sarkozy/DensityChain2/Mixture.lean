module

public import Sarkozy.DensityChain2.Atoms

@[expose] public section

/-!
# Convex mixtures of unit mixed moments (`lem:density:packets`, "taking convex mixtures")

The proof of `lem:density:packets` ends: "Taking convex mixtures then gives it for their sum ...
and hence for the increment in (CP6)", and "Tensorization and convex mixing finish the proof".
Here is the mixing step for the normalized variation laws used by the density chain's `hatom`:

* `mixedLp_variationLaw_sum`: if `ρ = ∑ c_i ρ_i` with `c_i ≥ 0` and `ρ_i ≥ 0` pointwise, and every
  `ρ_i` of positive mass has unit (or `C`-) mixed `L^q` after normalization, then so does `ρ`;
* **`mixedLp_comb`**: the same for a nonnegative combination `∑ c_i κ_i` of nonnegative slot
  measures (e.g. the increments `envIncL/R = ∑ c κ`, the reserved records `∑ κu`, `wrapInc`);
* `hmixR_of_records`: the per-atom hypothesis `_hmixR` of `Fields` for `Ñ₀ − μ = ∑_i κu_i` from
  the same bound for every reserved record `κu_i`.
-/

namespace Sarkozy.DensityChain2

open Finset
open scoped BigOperators
open Sarkozy.BracketEnergy Sarkozy.Structured Sarkozy.TheoremC Sarkozy.BlockFrame

/-- **Convex mixing of mixed moments** for normalized variation laws of nonnegative densities. -/
theorem mixedLp_variationLaw_sum {X : Type} [Fintype X] [Nonempty X] {ι : Type} (s : Finset ι)
    (c : ι → ℝ) (ρ : ι → (Slot → X) → ℝ) (hc : ∀ i ∈ s, 0 ≤ c i)
    (hρ : ∀ i ∈ s, ∀ z, 0 ≤ ρ i z) {q C : ℝ}
    (h : ∀ i ∈ s, ∀ hb : 0 < totalVariation (ρ i), MixedLpBound (variationLaw (ρ i) hb) q C)
    (hb : 0 < totalVariation (fun z => ∑ i ∈ s, c i * ρ i z)) :
    MixedLpBound (variationLaw _ hb) q C := by
  intro f
  set N := ∏ v, (FiniteLaw.uniform X).lpNorm q (f v) with hN
  have hN0 : 0 ≤ N := prod_nonneg fun v _ => FiniteLaw.lpNorm_nonneg _ _ _
  set F : (Slot → X) → ℝ := fun z => ∏ v, f v (z v) with hF
  have hexp : ∀ (σ : (Slot → X) → ℝ) (hσ : 0 < totalVariation σ), (∀ z, 0 ≤ σ z) →
      (variationLaw σ hσ).expect F = (∑ z, σ z * F z) / totalVariation σ := by
    intro σ hσ hσ0
    unfold FiniteLaw.expect variationLaw
    simp only
    rw [sum_div]
    refine sum_congr rfl fun z _ => ?_
    rw [abs_of_nonneg (hσ0 z)]
    ring
  have key : ∀ i ∈ s, |∑ z, ρ i z * F z| ≤ C * N * totalVariation (ρ i) := by
    intro i hi
    by_cases ht : 0 < totalVariation (ρ i)
    · have h1 := h i hi ht f
      rw [hexp _ ht (hρ i hi), abs_div, abs_of_pos ht, div_le_iff₀ ht] at h1
      exact h1
    · have ht0 : totalVariation (ρ i) = 0 :=
        le_antisymm (not_lt.mp ht) (totalVariation_nonneg _)
      have hz : ∀ z, ρ i z = 0 := by
        intro z
        have hle : |ρ i z| ≤ totalVariation (ρ i) :=
          single_le_sum (f := fun z => |ρ i z|) (fun _ _ => abs_nonneg _) (mem_univ z)
        rw [ht0] at hle
        exact abs_nonpos_iff.mp hle
      simp only [hz, zero_mul, sum_const_zero, abs_zero, ht0, mul_zero, le_refl]
  have hρs : ∀ z, 0 ≤ ∑ i ∈ s, c i * ρ i z := fun z =>
    sum_nonneg fun i hi => mul_nonneg (hc i hi) (hρ i hi z)
  have htv : totalVariation (fun z => ∑ i ∈ s, c i * ρ i z) =
      ∑ i ∈ s, c i * totalVariation (ρ i) := by
    unfold totalVariation
    simp only [abs_of_nonneg (hρs _)]
    rw [sum_comm]
    refine sum_congr rfl fun i hi => ?_
    rw [mul_sum]
    exact sum_congr rfl fun z _ => by rw [abs_of_nonneg (hρ i hi z)]
  rw [hexp _ hb hρs, abs_div, abs_of_pos hb, div_le_iff₀ hb]
  have hsum : ∑ z, (∑ i ∈ s, c i * ρ i z) * F z = ∑ i ∈ s, c i * ∑ z, ρ i z * F z := by
    simp only [sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun z _ => by ring
  rw [hsum, htv]
  calc |∑ i ∈ s, c i * ∑ z, ρ i z * F z|
      ≤ ∑ i ∈ s, c i * |∑ z, ρ i z * F z| := by
        refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        exact sum_congr rfl fun i hi => by rw [abs_mul, abs_of_nonneg (hc i hi)]
    _ ≤ ∑ i ∈ s, c i * (C * N * totalVariation (ρ i)) :=
        sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (key i hi) (hc i hi)
    _ = C * N * ∑ i ∈ s, c i * totalVariation (ρ i) := by
        rw [mul_sum]
        exact sum_congr rfl fun i _ => by ring

/-- The density of a nonnegative slot measure is nonnegative. -/
theorem lawDensity_nonneg_of_isNonneg {X : Type} [Fintype X] [DecidableEq X]
    {κ : SlotMeasure X} (hκ : IsNonneg κ) (z : Slot → X) : 0 ≤ lawDensity κ z :=
  hκ _ fun y => by
    split_ifs
    · exact zero_le_one
    · exact le_refl 0

/-- **Convex mixing for nonnegative combinations of slot measures.** -/
theorem mixedLp_comb {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] {ι : Type}
    [Fintype ι] (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (κ : ι → SlotMeasure X)
    (hκ : ∀ i, IsNonneg (κ i)) {q C : ℝ}
    (h : ∀ i, ∀ hb : 0 < totalVariation (lawDensity (κ i)),
      MixedLpBound (variationLaw _ hb) q C)
    (hb : 0 < totalVariation (lawDensity (∑ i, c i • κ i))) :
    MixedLpBound (variationLaw _ hb) q C := by
  have he : lawDensity (∑ i, c i • κ i) = fun z => ∑ i ∈ univ, c i * lawDensity (κ i) z := by
    funext z
    rw [RecordExpansion.lawDensity_sum]
    exact sum_congr rfl fun i _ => RecordExpansion.lawDensity_smul _ _ _
  have hb' : 0 < totalVariation (fun z => ∑ i ∈ univ, c i * lawDensity (κ i) z) := he ▸ hb
  refine (mixedLp_variationLaw_congr he hb hb').mpr ?_
  exact mixedLp_variationLaw_sum univ c (fun i => lawDensity (κ i)) (fun i _ => hc i)
    (fun i _ z => lawDensity_nonneg_of_isNonneg (hκ i) z) (fun i _ => h i) hb'


variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

omit [DecidableEq P] in
/-- **`_hmixR` from the reserved records**: unit mixed `L^q` of `Ñ_{0,𝔟} − μ_𝔟 = ∑_i κu_{𝔟,i}`
(normalized) from the same bound for every record `κu_{𝔟,i}`. -/
theorem hmixR_of_records (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (b : BlockAtom Bk J L) {q : ℝ}
    (h : ∀ i, ∀ hb : 0 < totalVariation (lawDensity (D.GB.κu L b i)),
      MixedLpBound (variationLaw _ hb) q 1)
    (hb : 0 < totalVariation (lawDensity (recLaw D L b))) :
    MixedLpBound (variationLaw _ hb) q 1 := by
  have he : recLaw D L b = ∑ i, (1 : ℝ) • D.GB.κu L b i := by
    unfold recLaw
    simp only [one_smul]
  have hb' : 0 < totalVariation (lawDensity (∑ i, (1 : ℝ) • D.GB.κu L b i)) := he ▸ hb
  refine (mixedLp_variationLaw_congr (congrArg lawDensity he) hb hb').mpr ?_
  exact mixedLp_comb _ (fun _ => zero_le_one) _ (fun i => (D.GB.κu_pos L b i).1) h hb'

omit [DecidableEq P] in
/-- **`_hmixQ` for `envIncL` from its components**: `Q_{L,𝔟} = ∑_i c_i κ_{L,𝔟,i}`. -/
theorem hmixQL_of_components (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (b : BlockAtom Bk J L) {q : ℝ}
    (h : ∀ i, ∀ hb : 0 < totalVariation (lawDensity (D.ME.κL L b i)),
      MixedLpBound (variationLaw _ hb) q 1)
    (hb : 0 < totalVariation (lawDensity (TheoremCBlock.Structured.envIncL D L b))) :
    MixedLpBound (variationLaw _ hb) q 1 :=
  mixedLp_comb _ (D.ME.cL_nonneg L b) _ (fun i => (D.ME.κL_pos L b i).1) h hb

omit [DecidableEq P] in
/-- **`_hmixQ` for `envIncR` from its components**: `Q_{R,𝔟} = ∑_i c_i κ_{R,𝔟,i}`. -/
theorem hmixQR_of_components (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (b : BlockAtom Bk J L) {q : ℝ}
    (h : ∀ i, ∀ hb : 0 < totalVariation (lawDensity (D.ME.κR L b i)),
      MixedLpBound (variationLaw _ hb) q 1)
    (hb : 0 < totalVariation (lawDensity (TheoremCBlock.Structured.envIncR D L b))) :
    MixedLpBound (variationLaw _ hb) q 1 :=
  mixedLp_comb _ (D.ME.cR_nonneg L b) _ (fun i => (D.ME.κR_pos L b i).1) h hb

end Sarkozy.DensityChain2
