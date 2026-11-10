module

public import Sarkozy.Certificates.EdgeMoment
public import Sarkozy.Moments.InvariantPair
public import Sarkozy.TraceMixing.Paley

/-!
# The square-pair moment for the paper's two pair laws

Sources: `lem:density:edge-moment` and `lem:density:invariant-pair`;
`paper/sections/30_density_moment_upgrade.tex`.

For an odd prime `p`, the uniform law on the ordered pairs `(z₀, z₁)` with `χ(z₁ − z₀) = c`,
`c = ±1`, has uniform coordinates (`classSet_uniformCoords`). Each coordinate value has
`(p − 1)/2` partners.

So `EdgeGate.edge_moment_of_interpolation` applies to both pair laws (`square_pair_moment`).
Through `InvariantPair.invariant_pair_mixedLpBound` the bound then extends to every law on
distinct pairs invariant under the square-affine maps (`invariant_pair_edge`). The named input
is the interpolated centred bound of `lem:density:edge-moment`, for the two class laws.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.EdgeGate

open Sarkozy.InvariantPair

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [hp : Fact p.Prime]

local notation "χ" => quadraticChar (ZMod p)

/-- Each label has `(p − 1)/2` partners of either class: `2 · #{b : χ(b − a) = c} = p − 1`. -/
theorem card_class_partners (hp2 : p ≠ 2) {c : ℤ} (hc : c = 1 ∨ c = -1) (a : ZMod p) :
    2 * ((univ.filter fun b : ZMod p => χ (b - a) = c).card : ℤ) = p - 1 := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have h1 := TraceMixing.card_out hF a
  rw [ZMod.card] at h1
  rcases hc with rfl | rfl
  · exact h1
  · -- the three classes partition `ZMod p`
    have hpart : ((univ.filter fun b : ZMod p => χ (b - a) = 1).card : ℤ) +
        ((univ.filter fun b : ZMod p => χ (b - a) = -1).card : ℤ) + 1 = p := by
      have hsum : ∀ b : ZMod p, (if χ (b - a) = 1 then (1 : ℤ) else 0) +
          (if χ (b - a) = -1 then 1 else 0) + (if b = a then 1 else 0) = 1 := by
        intro b
        by_cases hb : b = a
        · subst hb
          simp
        · have hne : b - a ≠ 0 := sub_ne_zero.mpr hb
          rcases quadraticChar_dichotomy hne with h | h <;> simp [h, hb]
      have := congrArg (fun f : ZMod p → ℤ => ∑ b, f b) (funext hsum)
      simp only [sum_add_distrib, sum_boole, filter_eq', mem_univ, ↓reduceIte, card_singleton,
        sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_one] at this
      push_cast at this
      linarith
    linarith

/-- **The class laws have uniform coordinates.** -/
theorem classSet_uniformCoords (hp2 : p ≠ 2) {c : ℤ} (hc : c = 1 ∨ c = -1) :
    DensityUpgrade.conditioningUniformCoords
      (uniformOn (classSet (p := p) c) (classSet_nonempty hp2 hc)).weight := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  -- partners in the second coordinate, either orientation
  have hpart : ∀ (d : ℤ), (d = 1 ∨ d = -1) → ∀ a : ZMod p,
      2 * ((univ.filter fun b : ZMod p => χ (a - b) = d).card : ℤ) = p - 1 := by
    intro d hd a
    have hneg : χ (-1) = 1 ∨ χ (-1) = -1 := quadraticChar_dichotomy (neg_ne_zero.mpr one_ne_zero)
    have heq : (univ.filter fun b : ZMod p => χ (a - b) = d) =
        univ.filter fun b : ZMod p => χ (b - a) = d * χ (-1) := by
      ext b
      simp only [mem_filter, mem_univ, true_and]
      have hab : a - b = -1 * (b - a) := by ring
      rw [hab, map_mul]
      rcases hneg with h | h <;> rw [h] <;> constructor <;> intro h' <;> linarith
    rw [heq]
    exact card_class_partners hp2 (by rcases hd with rfl | rfl <;> rcases hneg with h | h <;>
      simp [h]) a
  intro v a
  set S := classSet (p := p) c with hSdef
  have hfib0 : ∀ a' : ZMod p, ((univ.filter (fun x : Fin 2 → ZMod p => x 0 = a')) ∩ S).card =
      (univ.filter fun b : ZMod p => χ (b - a') = c).card := by
    intro a'
    apply Finset.card_nbij' (fun x => x 1) (fun b => ![a', b])
    · intro x hx
      simp only [Finset.mem_coe, mem_inter, mem_filter, mem_univ, true_and, hSdef, classSet] at hx
      simp only [mem_filter, mem_univ, true_and, Finset.mem_coe]
      rw [← hx.1]
      exact hx.2
    · intro b hb
      simp only [mem_filter, mem_univ, true_and, Finset.mem_coe] at hb
      simp only [mem_inter, mem_filter, mem_univ, true_and, hSdef, classSet, Finset.mem_coe,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      first | exact ⟨rfl, hb⟩ | exact hb
    · intro x hx
      simp only [Finset.mem_coe, mem_inter, mem_filter, mem_univ, true_and] at hx
      funext k
      fin_cases k
      · simp [hx.1]
      · simp
    · intro b _
      simp
  have hfib1 : ((univ.filter (fun x : Fin 2 → ZMod p => x 1 = a)) ∩ S).card =
      (univ.filter fun b : ZMod p => χ (a - b) = c).card := by
    apply Finset.card_nbij' (fun x => x 0) (fun b => ![b, a])
    · intro x hx
      simp only [Finset.mem_coe, mem_inter, mem_filter, mem_univ, true_and, hSdef, classSet] at hx
      simp only [mem_filter, mem_univ, true_and, Finset.mem_coe]
      rw [← hx.1]
      exact hx.2
    · intro b hb
      simp only [mem_filter, mem_univ, true_and, Finset.mem_coe] at hb
      simp only [mem_inter, mem_filter, mem_univ, true_and, hSdef, classSet, Finset.mem_coe,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      first | exact ⟨rfl, hb⟩ | exact hb
    · intro x hx
      simp only [Finset.mem_coe, mem_inter, mem_filter, mem_univ, true_and] at hx
      funext k
      fin_cases k
      · simp
      · simp [hx.1]
    · intro b _
      simp
  -- the size of `S`
  have hScard : 2 * (S.card : ℤ) = p * (p - 1) := by
    have hsplit : S = (univ : Finset (ZMod p)).biUnion
        (fun a' => (univ.filter (fun x : Fin 2 → ZMod p => x 0 = a')) ∩ S) := by
      ext x
      simp
    rw [hsplit, card_biUnion]
    · push_cast
      rw [mul_sum]
      simp_rw [hfib0, card_class_partners hp2 hc]
      rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul]
    · intro a₁ _ a₂ _ hne
      rw [Function.onFun, disjoint_left]
      intro x hx1 hx2
      simp only [mem_inter, mem_filter, mem_univ, true_and] at hx1 hx2
      exact hne (hx1.1.symm.trans hx2.1)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hSpos : (0 : ℝ) < S.card := by
    have hpZ : (1 : ℤ) < p := by exact_mod_cast hp.out.one_lt
    have : (0 : ℤ) < S.card := by nlinarith
    exact_mod_cast this
  -- the fibre sum
  have hsum : ∑ x ∈ univ.filter (fun x : Fin 2 → ZMod p => x v = a),
      (uniformOn S (classSet_nonempty hp2 hc)).weight x =
        (((univ.filter (fun x : Fin 2 → ZMod p => x v = a)) ∩ S).card : ℝ) / S.card := by
    simp only [uniformOn]
    rw [sum_ite_mem, sum_const, nsmul_eq_mul]
    ring
  rw [hsum, ZMod.card]
  have hfib : 2 * ((((univ.filter (fun x : Fin 2 → ZMod p => x v = a)) ∩ S).card : ℤ)) =
      p - 1 := by
    have hv : v = 0 ∨ v = 1 := by
      fin_cases v
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hv with rfl | rfl
    · rw [hfib0]
      exact card_class_partners hp2 hc a
    · rw [hfib1]
      exact hpart c hc a
  have hfibR : (2 : ℝ) * ((((univ.filter (fun x : Fin 2 → ZMod p => x v = a)) ∩ S).card : ℝ)) =
      p - 1 := by exact_mod_cast hfib
  have hScardR : (2 : ℝ) * (S.card : ℝ) = p * (p - 1) := by exact_mod_cast hScard
  rw [div_eq_div_iff hSpos.ne' (by positivity)]
  nlinarith

/-- **`lem:density:edge-moment` for the paper's pair laws.** Assume the gate, and the
interpolated centred bound, for the uniform strict square pairs (`c = 1`) or nonsquare pairs
(`c = −1`). Then that law has unit mixed `L^{1+1/j}`. -/
theorem square_pair_moment (hp2 : p ≠ 2) {c : ℤ} (hc : c = 1 ∨ c = -1) {j : ℕ} (hj : 1 ≤ j)
    (hgate : (j : ℝ) ^ (j + 1) * (((p : ℝ) + 1) / ((p : ℝ) - 1)) ^ (j - 1) *
      (1 / (Real.sqrt p - 1)) ^ 2 ≤ 1)
    (hinterp : ∀ f g : ZMod p → ℝ, ∑ a, f a = 0 → ∑ a, g a = 0 →
      |∑ x, (uniformOn (classSet (p := p) c) (classSet_nonempty hp2 hc)).weight x *
          (f (x 0) * g (x 1))| ≤
        (((p : ℝ) + 1) / ((p : ℝ) - 1)) ^ (((j : ℝ) - 1) / ((j : ℝ) + 1)) *
          (1 / (Real.sqrt p - 1)) ^ ((2 : ℝ) / ((j : ℝ) + 1)) *
          DensityUpgrade.conditioningNorm (1 + 1 / (j : ℝ)) f *
          DensityUpgrade.conditioningNorm (1 + 1 / (j : ℝ)) g) :
    MixedLpBound (uniformOn (classSet (p := p) c) (classSet_nonempty hp2 hc)) (1 + 1 / (j : ℝ)) 1 := by
  rw [mixedLpBound_iff_conditioningUnitMixed]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hsq : 1 ≤ Real.sqrt p := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hp1.le
  exact edge_moment_of_interpolation _ (fun x => (uniformOn _ _).nonneg x)
    (classSet_uniformCoords hp2 hc) hj (div_nonneg (by linarith) (by linarith))
    (one_div_nonneg.mpr (by linarith)) hgate hinterp

/-- **`lem:density:invariant-pair` with the square-pair moment.** Assume the gate, and the
interpolated bounds for both class laws. Then every law on distinct pairs invariant under the
square-affine maps has unit mixed `L^{1+1/j}`. -/
theorem invariant_pair_edge (hp2 : p ≠ 2) (μ : FiniteLaw (Fin 2 → ZMod p))
    (hdist : ∀ z, z 0 = z 1 → μ.weight z = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ z,
      μ.weight (fun k => s * z k + u) = μ.weight z)
    {j : ℕ} (hj : 1 ≤ j)
    (hgate : (j : ℝ) ^ (j + 1) * (((p : ℝ) + 1) / ((p : ℝ) - 1)) ^ (j - 1) *
      (1 / (Real.sqrt p - 1)) ^ 2 ≤ 1)
    (hinterp : ∀ (c : ℤ) (hc : c = 1 ∨ c = -1), ∀ f g : ZMod p → ℝ, ∑ a, f a = 0 →
      ∑ a, g a = 0 →
      |∑ x, (uniformOn (classSet (p := p) c) (classSet_nonempty hp2 hc)).weight x *
          (f (x 0) * g (x 1))| ≤
        (((p : ℝ) + 1) / ((p : ℝ) - 1)) ^ (((j : ℝ) - 1) / ((j : ℝ) + 1)) *
          (1 / (Real.sqrt p - 1)) ^ ((2 : ℝ) / ((j : ℝ) + 1)) *
          DensityUpgrade.conditioningNorm (1 + 1 / (j : ℝ)) f *
          DensityUpgrade.conditioningNorm (1 + 1 / (j : ℝ)) g) :
    MixedLpBound μ (1 + 1 / (j : ℝ)) 1 :=
  invariant_pair_mixedLpBound hp2 μ hdist hinv
    (square_pair_moment hp2 (Or.inl rfl) hj hgate (hinterp 1 (Or.inl rfl)))
    (square_pair_moment hp2 (Or.inr rfl) hj hgate (hinterp (-1) (Or.inr rfl)))

end Sarkozy.EdgeGate
