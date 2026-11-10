module

public import Sarkozy.Moments.Mixed
public import Sarkozy.Construction.CliqueLaw

/-!
# Invariant distinct pairs (`lem:density:invariant-pair`), from the square-pair moment

`paper/sections/30_density_moment_upgrade.tex`. A probability law on ordered distinct pairs in
`𝔽_p` that is invariant under the simultaneous square-affine maps `z ↦ s z + u` (`s` a nonzero
square) is a convex mixture of the uniform strict square pair law and the uniform nonsquare pair
law. These are the two orbits of the square-affine group on distinct pairs (`invariant_pair_eq`).
So it has unit mixed `L^r` whenever both pair laws do (`invariant_pair_mixedLpBound`).

`lem:density:edge-moment` supplies the unit mixed `L^{3/2}` norm of the two pair laws. Its gate
`eq:density:edge-integer-gate` at `j = 2` holds for `p ≥ 64` (`edge_gate_two`). That lemma
itself, which needs the bilinear interpolation, is not formalized here: its conclusion for the
two pair laws is the hypothesis of `invariant_pair_mixedLpBound`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.InvariantPair

variable {p : ℕ} [hp : Fact p.Prime]

/-- The ordered pairs with `χ(z₁ - z₀) = c`. -/
noncomputable def classSet (c : ℤ) : Finset (Fin 2 → ZMod p) :=
  univ.filter fun z => quadraticChar (ZMod p) (z 1 - z 0) = c

/-- **The two orbits**: if `χ(z₁ - z₀) = χ(z'₁ - z'₀) = ±1`, some square-affine map
`w ↦ s w + u` takes `z` to `z'`. -/
theorem exists_square_affine {z z' : Fin 2 → ZMod p} {c : ℤ} (hc : c ≠ 0)
    (hz : quadraticChar (ZMod p) (z 1 - z 0) = c) (hz' : quadraticChar (ZMod p) (z' 1 - z' 0) = c) :
    ∃ s u : ZMod p, s ≠ 0 ∧ IsSquare s ∧ ∀ k, s * z k + u = z' k := by
  have hd : z 1 - z 0 ≠ 0 := fun h => hc (by rw [← hz, h, quadraticChar_zero])
  have hd' : z' 1 - z' 0 ≠ 0 := fun h => hc (by rw [← hz', h, quadraticChar_zero])
  set s := (z' 1 - z' 0) / (z 1 - z 0) with hs
  have hs0 : s ≠ 0 := div_ne_zero hd' hd
  have hcc : c * c = 1 := by
    have : c = 1 ∨ c = -1 := by rw [← hz]; exact quadraticChar_dichotomy hd
    rcases this with rfl | rfl <;> norm_num
  have hχs : quadraticChar (ZMod p) s = 1 := by
    have e : s * (z 1 - z 0) ^ 2 = (z' 1 - z' 0) * (z 1 - z 0) := by
      rw [hs]; field_simp
    have h1 : quadraticChar (ZMod p) (s * (z 1 - z 0) ^ 2) = quadraticChar (ZMod p) s := by
      rw [map_mul, quadraticChar_sq_one' hd, mul_one]
    rw [← h1, e, map_mul, hz', hz, hcc]
  have hsq : IsSquare s := (quadraticChar_one_iff_isSquare hs0).mp hχs
  refine ⟨s, z' 0 - s * z 0, hs0, hsq, fun k => ?_⟩
  fin_cases k
  · simp
  · simp only [Fin.mk_one, Fin.isValue]
    rw [hs]
    field_simp
    ring

/-- An invariant law is constant on each class. -/
theorem weight_eq_of_class {μ : FiniteLaw (Fin 2 → ZMod p)}
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ z, μ.weight (fun k => s * z k + u) = μ.weight z)
    {z z' : Fin 2 → ZMod p} {c : ℤ} (hc : c ≠ 0) (hz : quadraticChar (ZMod p) (z 1 - z 0) = c)
    (hz' : quadraticChar (ZMod p) (z' 1 - z' 0) = c) : μ.weight z = μ.weight z' := by
  obtain ⟨s, u, hs0, hsq, hk⟩ := exists_square_affine hc hz hz'
  have : (fun k => s * z k + u) = z' := funext hk
  rw [← this, hinv s u hs0 hsq z]

theorem classSet_nonempty (hp2 : p ≠ 2) {c : ℤ} (hc : c = 1 ∨ c = -1) :
    (classSet (p := p) c).Nonempty := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  rcases hc with rfl | rfl
  · refine ⟨(![0, 1] : Fin 2 → ZMod p), mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
    simp
  · obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one hF
    refine ⟨(![0, a] : Fin 2 → ZMod p), mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
    simpa using ha

/-- **`lem:density:invariant-pair`, the orbit decomposition**: an invariant law on distinct pairs
is the mixture of the two class laws with weights the class masses. -/
theorem invariant_pair_eq (hp2 : p ≠ 2) (μ : FiniteLaw (Fin 2 → ZMod p))
    (hdist : ∀ z, z 0 = z 1 → μ.weight z = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ z, μ.weight (fun k => s * z k + u) = μ.weight z)
    (z : Fin 2 → ZMod p) :
    μ.weight z =
      (∑ w ∈ classSet (p := p) 1, μ.weight w) * (uniformOn (classSet (p := p) 1) (classSet_nonempty hp2 (Or.inl rfl))).weight z +
      (∑ w ∈ classSet (p := p) (-1), μ.weight w) *
        (uniformOn (classSet (p := p) (-1)) (classSet_nonempty hp2 (Or.inr rfl))).weight z := by
  have hconst : ∀ {c : ℤ}, c ≠ 0 → ∀ {z : Fin 2 → ZMod p}, z ∈ classSet (p := p) c →
      (∑ w ∈ classSet (p := p) c, μ.weight w) = (classSet (p := p) c).card * μ.weight z := by
    intro c hc z hz
    have hzc := (mem_filter.mp hz).2
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_congr rfl fun w hw => weight_eq_of_class hinv hc (mem_filter.mp hw).2 hzc
  have hne1 := classSet_nonempty (p := p) hp2 (Or.inl rfl)
  have hne2 := classSet_nonempty (p := p) hp2 (Or.inr rfl)
  have hc1 : ((classSet (p := p) 1).card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hne1).ne'
  have hc2 : ((classSet (p := p) (-1)).card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hne2).ne'
  simp only [uniformOn]
  rcases eq_or_ne (z 1 - z 0) 0 with h0 | h0
  · -- the diagonal: both sides vanish
    have hz0 : z 0 = z 1 := (sub_eq_zero.mp h0).symm
    have h1 : z ∉ classSet (p := p) 1 := by
      simp [classSet, h0]
    have h2 : z ∉ classSet (p := p) (-1) := by
      simp [classSet, h0]
    simp only [h1, h2, ↓reduceIte, mul_zero, add_zero, hdist z hz0]
  · rcases quadraticChar_dichotomy h0 with h | h
    · have h1 : z ∈ classSet (p := p) 1 := mem_filter.mpr ⟨mem_univ _, h⟩
      have h2 : z ∉ classSet (p := p) (-1) := by
        simp only [classSet, mem_filter, mem_univ, true_and, h]; decide
      simp only [h1, h2, ↓reduceIte, mul_zero, add_zero]
      rw [hconst one_ne_zero h1]
      field_simp
    · have h1 : z ∉ classSet (p := p) 1 := by
        simp only [classSet, mem_filter, mem_univ, true_and, h]; decide
      have h2 : z ∈ classSet (p := p) (-1) := mem_filter.mpr ⟨mem_univ _, h⟩
      simp only [h1, h2, ↓reduceIte, mul_zero, zero_add]
      rw [hconst (by decide) h2]
      field_simp

/-- **`lem:density:invariant-pair`**, given the square-pair moment: if the uniform strict square
pair law and the uniform nonsquare pair law have unit mixed `L^r`, so does every law on distinct
pairs that is invariant under the simultaneous square-affine maps. -/
theorem invariant_pair_mixedLpBound (hp2 : p ≠ 2) (μ : FiniteLaw (Fin 2 → ZMod p))
    (hdist : ∀ z, z 0 = z 1 → μ.weight z = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ z, μ.weight (fun k => s * z k + u) = μ.weight z)
    {r : ℝ}
    (hsq : MixedLpBound (uniformOn (classSet (p := p) 1) (classSet_nonempty hp2 (Or.inl rfl))) r 1)
    (hnsq : MixedLpBound (uniformOn (classSet (p := p) (-1)) (classSet_nonempty hp2 (Or.inr rfl)))
      r 1) :
    MixedLpBound μ r 1 := by
  -- the class masses form a law on `Bool`
  set m : Bool → ℝ := fun b => ∑ w ∈ classSet (p := p) (if b then 1 else -1), μ.weight w
  have hm0 : ∀ b, 0 ≤ m b := fun b => sum_nonneg fun w _ => μ.nonneg w
  have hm1 : ∑ b, m b = 1 := by
    have h := μ.total
    have hsplit : ∀ z, μ.weight z = (if z ∈ classSet (p := p) 1 then μ.weight z else 0) +
        (if z ∈ classSet (p := p) (-1) then μ.weight z else 0) := by
      intro z
      rcases eq_or_ne (z 1 - z 0) 0 with h0 | h0
      · have h1 : z ∉ classSet (p := p) 1 := by simp [classSet, h0]
        have h2 : z ∉ classSet (p := p) (-1) := by simp [classSet, h0]
        simp only [h1, h2, ↓reduceIte, add_zero]
        exact hdist z (sub_eq_zero.mp h0).symm
      · rcases quadraticChar_dichotomy h0 with hc | hc
        · have h1 : z ∈ classSet (p := p) 1 := mem_filter.mpr ⟨mem_univ _, hc⟩
          have h2 : z ∉ classSet (p := p) (-1) := by
            simp only [classSet, mem_filter, mem_univ, true_and, hc]; decide
          simp only [h1, h2, ↓reduceIte, add_zero]
        · have h1 : z ∉ classSet (p := p) 1 := by
            simp only [classSet, mem_filter, mem_univ, true_and, hc]; decide
          have h2 : z ∈ classSet (p := p) (-1) := mem_filter.mpr ⟨mem_univ _, hc⟩
          simp only [h1, h2, ↓reduceIte, zero_add]
    rw [sum_congr rfl fun z _ => hsplit z, sum_add_distrib, sum_ite_mem, sum_ite_mem,
      univ_inter, univ_inter] at h
    simp only [m, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
    linarith
  set wts : FiniteLaw Bool := ⟨m, hm0, hm1⟩
  set laws : Bool → FiniteLaw (Fin 2 → ZMod p) := fun b =>
    if b then uniformOn (classSet (p := p) 1) (classSet_nonempty hp2 (Or.inl rfl))
    else uniformOn (classSet (p := p) (-1)) (classSet_nonempty hp2 (Or.inr rfl))
  have hlaws : ∀ b, MixedLpBound (laws b) r 1 := by
    intro b
    cases b
    · simpa [laws] using hnsq
    · simpa [laws] using hsq
  have hmix := mixedLpBound_mixture wts laws r (fun _ => 1) hlaws
  have hexp : wts.expect (fun _ => (1 : ℝ)) = 1 := by
    simp only [FiniteLaw.expect, mul_one]
    exact hm1
  rw [hexp] at hmix
  have hw : ∀ z, μ.weight z = (FiniteLaw.mixture wts laws).weight z := by
    intro z
    rw [invariant_pair_eq hp2 μ hdist hinv z]
    simp only [FiniteLaw.mixture, Fintype.sum_bool, wts, laws, m, Bool.false_eq_true,
      ↓reduceIte]
  intro f
  have hE : μ.expect (fun z => ∏ v, f v (z v)) =
      (FiniteLaw.mixture wts laws).expect (fun z => ∏ v, f v (z v)) := by
    simp only [FiniteLaw.expect, hw]
  rw [hE]
  exact hmix f

/-- The gate `eq:density:edge-integer-gate` at `j = 2`: `8 (p+1)/((p-1)(√p - 1)²) ≤ 1` for `p ≥ 64`. -/
theorem edge_gate_two {x : ℝ} (hx : 64 ≤ x) :
    (2 : ℝ) ^ 3 * ((x + 1) / (x - 1)) ^ 1 * (1 / (Real.sqrt x - 1) ^ 2) ≤ 1 := by
  have hs : (8 : ℝ) ≤ Real.sqrt x := by
    rw [show (8 : ℝ) = Real.sqrt 64 by rw [show (64 : ℝ) = 8 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
  have h1 : (0 : ℝ) < x - 1 := by linarith
  have h2 : (0 : ℝ) < (Real.sqrt x - 1) ^ 2 := by nlinarith
  rw [show (2 : ℝ) ^ 3 * ((x + 1) / (x - 1)) ^ 1 * (1 / (Real.sqrt x - 1) ^ 2) =
      8 * (x + 1) / ((x - 1) * (Real.sqrt x - 1) ^ 2) by field_simp; ring,
    div_le_one (by positivity)]
  have h3 : (49 : ℝ) ≤ (Real.sqrt x - 1) ^ 2 := by nlinarith
  have h4 := mul_le_mul_of_nonneg_left h3 h1.le
  linarith

end Sarkozy.InvariantPair
