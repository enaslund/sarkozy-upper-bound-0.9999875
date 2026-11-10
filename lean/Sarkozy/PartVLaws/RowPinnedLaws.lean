module

public import Sarkozy.PartVLaws.RowStarNumerics
public import Sarkozy.JointRows.PinnedCoordinateMeans

/-!
# Product reference laws for the ten tail rows

For an injectively labelled middle row, each free coordinate is uniform
on its actual allowed labels. The two free rows have the same pins.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.PartVLaws.FieldGraphs.RowCase

open Finset Sarkozy.Labellings Sarkozy.JointRows Sarkozy.JointRows.StarOps
  Sarkozy.FiveType Sarkozy.FiveType.Blocks

def pinNeighbours (c : RowCase) (i : c.Index) : Finset c.Index :=
  univ.filter fun j => c.pinSign i j ≠ 0

variable {p : ℕ} [Fact p.Prime]

def fixedLabels (c : RowCase) (b : c.Index → ZMod p) : Finset (ZMod p) := univ.image b

def roots (c : RowCase) (b : c.Index → ZMod p) (i : c.Index) :
    c.pinNeighbours i → ZMod p := fun j => b j.1

noncomputable def signs (c : RowCase) (i : c.Index) (j : c.pinNeighbours i) : ℤ :=
  quadraticChar (ZMod p) (c.pinSign i j.1 : ZMod p)

theorem signs_pm (c : RowCase) (i : c.Index) (j : c.pinNeighbours i) :
    c.signs (p := p) i j = 1 ∨ c.signs (p := p) i j = -1 := by
  apply ExtractionK.pin_char_pm
  rcases c.pinSign_cases i j.1 with h | h | h
  · exact False.elim ((mem_filter.mp j.2).2 h)
  · exact Or.inl h
  · exact Or.inr h

omit [Fact p.Prime] in
theorem roots_injective (c : RowCase) (b : c.Index → ZMod p)
    (hb : Function.Injective b) (i : c.Index) : Function.Injective (c.roots b i) := by
  intro j k h
  exact Subtype.ext (hb h)

omit [Fact p.Prime] in
theorem roots_mem (c : RowCase) (b : c.Index → ZMod p) (i : c.Index)
    (j : c.pinNeighbours i) : c.roots b i j ∈ c.fixedLabels b := mem_image_of_mem _ (mem_univ _)

theorem card_pins (c : RowCase) (i : c.Index) : Fintype.card (c.pinNeighbours i) ≤ c.pins := by
  unfold pinNeighbours
  rw [Fintype.card_coe]
  exact c.pin_degree i

omit [Fact p.Prime] in
theorem card_fixedLabels (c : RowCase) (b : c.Index → ZMod p) : (c.fixedLabels b).card ≤ 12 :=
  card_image_le.trans (card_univ.le.trans c.card_index)

noncomputable def allowed (c : RowCase) (b : c.Index → ZMod p) (i : c.Index) :
    Finset (ZMod p) := admissible (c.roots b i) (c.signs (p := p) i) (c.fixedLabels b)

theorem allowed_nonempty (c : RowCase) (hp : 2 ^ 512 ≤ p) (hW : WeilBound (ZMod p))
    (b : c.Index → ZMod p) (hb : Function.Injective b) (i : c.Index) :
    (c.allowed b i).Nonempty :=
  PinCoordinate.allowed_nonempty hp hW (c.roots b i) (c.roots_injective b hb i)
    (c.signs (p := p) i) (c.signs_pm i) (c.fixedLabels b) (c.roots_mem b i)
    ((c.card_pins i).trans c.pins_le) (c.card_fixedLabels b)

noncomputable def coordinateLaw (c : RowCase) (hp : 2 ^ 512 ≤ p)
    (hW : WeilBound (ZMod p)) (b : c.Index → ZMod p) (hb : Function.Injective b)
    (i : c.Index) : FiniteLaw (ZMod p) :=
  Coll.unifOn (c.allowed b i) (c.allowed_nonempty hp hW b hb i)

theorem coordinate_density (c : RowCase) (hp : 2 ^ 512 ≤ p) (hW : WeilBound (ZMod p))
    (b : c.Index → ZMod p) (hb : Function.Injective b) (i : c.Index) (a : ZMod p) :
    (c.coordinateLaw hp hW b hb i).weight a ≤
      (2 : ℝ) ^ c.pins * (1 + 1 / 100000) / p := by
  have h := PinCoordinate.density_bound hp hW (c.roots b i) (c.roots_injective b hb i)
    (c.signs (p := p) i) (c.signs_pm i) (c.fixedLabels b) (c.roots_mem b i)
    ((c.card_pins i).trans c.pins_le) (c.card_fixedLabels b)
    (c.allowed_nonempty hp hW b hb i) a
  apply h.trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg p)
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num) (c.card_pins i)) (by norm_num)

theorem charged_avoids (c : RowCase) (hp : 2 ^ 512 ≤ p) (hW : WeilBound (ZMod p))
    (b : c.Index → ZMod p) (hb : Function.Injective b) (i : c.Index) (a : ZMod p)
    (ha : (c.coordinateLaw hp hW b hb i).weight a ≠ 0) : a ∉ c.fixedLabels b := by
  have hmem : a ∈ c.allowed b i := by
    by_contra h
    exact ha (by simp [coordinateLaw, Coll.unifOn, h])
  exact (mem_filter.mp hmem).2.1

theorem coordinate_mean (c : RowCase) (hp : 2 ^ 512 ≤ p) (hW : WeilBound (ZMod p))
    (b : c.Index → ZMod p) (hb : Function.Injective b) (i : c.Index)
    (t : ZMod p) (ht : t ∉ c.fixedLabels b) :
    |mchi (c.coordinateLaw hp hW b hb i) t| ≤ (2 : ℝ)⁻¹ ^ 80 :=
  PinCoordinate.mean_tail hp hW (c.roots b i) (c.roots_injective b hb i)
    (c.signs (p := p) i) (c.signs_pm i) (c.fixedLabels b) (c.roots_mem b i)
    ((c.card_pins i).trans c.pins_le) (c.card_fixedLabels b)
    (c.allowed_nonempty hp hW b hb i) t ht

theorem product_star_bound (c : RowCase) (hp : 2 ^ 512 ≤ p) (hW : WeilBound (ZMod p))
    (b : c.Index → ZMod p) (hb : Function.Injective b)
    (f g : (c.Index → ZMod p) → ℝ)
    (hf : (blockLaw (c.coordinateLaw hp hW b hb)).expect f = 0)
    (hg : (blockLaw (c.coordinateLaw hp hW b hb)).expect g = 0) :
    |bform (c.coordinateLaw hp hW b hb) (c.coordinateLaw hp hW b hb)
      (starKernel (c.coefficients (p := p)) (sets2 c.Index)) f g| ≤
      ((c.cap : ℝ) - 1 / 25) * (Real.sqrt p)⁻¹ *
        nrm (blockLaw (c.coordinateLaw hp hW b hb)) f *
        nrm (blockLaw (c.coordinateLaw hp hW b hb)) g := by
  have hs := c.star_bound (by omega : p ≠ 2) (c.coordinateLaw hp hW b hb)
    (by positivity : (0 : ℝ) < 2 ^ c.pins * (1 + 1 / 100000))
    (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ 80) (by norm_num)
    (c.coordinate_density hp hW b hb)
    (fun i j t ht => c.coordinate_mean hp hW b hb j t (c.charged_avoids hp hW b hb i t ht))
    f g hf hg
  apply hs.trans
  have hc := c.star_coefficient_le (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ 80)
    le_rfl le_rfl
  have h := mul_le_mul_of_nonneg_right hc
    (mul_nonneg (mul_nonneg (by positivity : 0 ≤ (Real.sqrt p)⁻¹)
      (FiveType.nrm_nonneg (blockLaw (c.coordinateLaw hp hW b hb)) f))
      (FiveType.nrm_nonneg (blockLaw (c.coordinateLaw hp hW b hb)) g))
  convert h using 1 <;> ring

end Sarkozy.PartVLaws.FieldGraphs.RowCase
