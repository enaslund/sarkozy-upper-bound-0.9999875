module

public import Sarkozy.SpectralD.SmallNonstarOperator
public import Sarkozy.SpectralD.CollisionAtMost
public import Sarkozy.SecondOrder.StarAtMost

/-!
# Character-expansion allowances for the smaller cuts

Singleton extraction supplies a nonstar coefficient at most 2^(-50)r.
Together with the uniform collision and star estimates this fits the
normalizer and perpendicular budgets at every prime p ≥ 2^512.
-/

@[expose] public section

namespace Sarkozy.SpectralD.AtMost

open Finset Sarkozy.Labellings Sarkozy.SecondOrder Sarkozy.Extraction

theorem tail_normalizer_scalar {r z n d : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 2⁻¹ ^ 256)
    (hz : z ≤ 2 ^ 88 * r ^ 2) (hn : n ≤ 2⁻¹ ^ 50 * r)
    (hd : d ≤ 2⁻¹ ^ 50 * r) : 2 * z + n + d ≤ 1 / 100 := by
  have hr1 : r ≤ 1 := hr.trans (by norm_num)
  have hz' : z ≤ 2 ^ 88 * r := hz.trans
    (mul_le_mul_of_nonneg_left (by nlinarith : r ^ 2 ≤ r) (by positivity))
  calc 2 * z + n + d ≤ 2 * (2 ^ 88 * r) + 2⁻¹ ^ 50 * r + 2⁻¹ ^ 50 * r := by
        gcongr
    _ = (2 ^ 89 + 2⁻¹ ^ 49) * r := by ring
    _ ≤ (2 ^ 89 + 2⁻¹ ^ 49) * (2⁻¹ ^ 256) :=
        mul_le_mul_of_nonneg_left hr (by positivity)
    _ ≤ 1 / 100 := by norm_num

theorem tail_perpendicular_scalar {r m n d : ℝ} (hr0 : 0 ≤ r)
    (hr : r ≤ 2⁻¹ ^ 256) (hm0 : 0 ≤ m) (hn0 : 0 ≤ n) (hd0 : 0 ≤ d)
    (hm : m ≤ 2 ^ 84 * r) (hn : n ≤ 2⁻¹ ^ 50 * r) (hd : d ≤ 2⁻¹ ^ 50 * r) :
    (n + d) / (1 - 1 / 100) + ((m + n + d) / (1 - 1 / 100)) ^ 2 ≤ 1 / 4 * r := by
  have hnd : n + d ≤ 2⁻¹ ^ 49 * r := by
    calc _ ≤ 2⁻¹ ^ 50 * r + 2⁻¹ ^ 50 * r := add_le_add hn hd
      _ = _ := by ring
  have hn' : (n + d) / (1 - 1 / 100) ≤ 2⁻¹ ^ 48 * r := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1 - 1 / 100)).mpr
    calc n + d ≤ 2⁻¹ ^ 49 * r := hnd
      _ ≤ (2⁻¹ ^ 48 * (1 - 1 / 100)) * r :=
          mul_le_mul_of_nonneg_right (by norm_num) hr0
      _ = _ := by ring
  have hm' : (m + n + d) / (1 - 1 / 100) ≤ 2 ^ 86 * r := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1 - 1 / 100)).mpr
    calc m + n + d = m + (n + d) := by ring
      _ ≤ 2 ^ 84 * r + 2⁻¹ ^ 49 * r := add_le_add hm hnd
      _ = (2 ^ 84 + 2⁻¹ ^ 49) * r := by ring
      _ ≤ (2 ^ 86 * (1 - 1 / 100)) * r :=
          mul_le_mul_of_nonneg_right (by norm_num) hr0
      _ = _ := by ring
  have hs := pow_le_pow_left₀ (div_nonneg (by linarith : 0 ≤ m + n + d)
    (by norm_num : (0 : ℝ) ≤ 1 - 1 / 100)) hm' 2
  calc _ ≤ 2⁻¹ ^ 48 * r + (2 ^ 86 * r) ^ 2 := add_le_add hn' hs
    _ = (2⁻¹ ^ 48 + 2 ^ 172 * r) * r := by ring
    _ ≤ (2⁻¹ ^ 48 + 2 ^ 172 * (2⁻¹ ^ 256)) * r := by gcongr
    _ ≤ 1 / 4 * r := mul_le_mul_of_nonneg_right (by norm_num) hr0

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W]

theorem graphCountError_bound (G : OrientedGraph W) (hn : Fintype.card W ≤ 36)
    (hd : ∀ i, (graphNbrs G i).card ≤ 10) (hp : 2 ^ 64 ≤ p) (i : W) :
    graphCountError (p := p) G i ≤ 1 / 10000 := by
  have hnR : (Fintype.card W : ℝ) ≤ 36 := by exact_mod_cast hn
  have h := graphCountError_le_coarse (p := p) G i
  have hmono : coarseError (graphNbrs G i).card p (Fintype.card W) ≤
      coarseError (graphNbrs G i).card p 36 := by
    unfold coarseError
    gcongr
  exact h.trans (hmono.trans ((coarseError_mono (by norm_num) (hd i)).trans
    (collision_error10 (by exact_mod_cast hp))))

theorem small_tail_expansion_bounds (D : Cuts.SpecData W) [LinearOrder D.cut.Half]
    (hW : WeilBound (ZMod p)) (h4 : FourCycleBound p)
    (hp : 2 ^ 512 ≤ p) (hn : Fintype.card D.cut.Half ≤ 18)
    (hm : D.crossPairs.card ≤ 96)
    (hd : ∀ i, nbrCount D.halfGraph (univ.erase i) i ≤ 10)
    (hr : ∀ i, (D.Nset i).card ≤ 12)
    (hne : (injLabellings (ZMod p) D.G).Nonempty)
    (he : ∀ i, graphCountError (p := p) D.halfGraph i < 1) :
    let r := (Real.sqrt p)⁻¹
    let a := 2⁻¹ ^ 50 * r
    let L := graphPinned hW D.halfGraph (D.half_nonempty hne) he
    (∀ v, ‖Cx.nsOp D hne v‖ ≤ a * ‖v‖) ∧
    (∀ v, ‖Cx.collOp D hne v‖ ≤ a * ‖v‖) ∧
    2 * Spectral.starZstar L D.Nset (Spectral.starCoef (p := p) D) + a + a ≤ 1 / 100 ∧
    (a + a) / (1 - 1 / 100) +
      ((Spectral.starMstar L D.Nset (Spectral.starCoef (p := p) D) + a + a) /
        (1 - 1 / 100)) ^ 2 ≤ 1 / 4 * r := by
  have hn36 : Fintype.card D.cut.Half ≤ 36 := by omega
  have hd' : ∀ i, (graphNbrs D.halfGraph i).card ≤ 10 := fun i => by
    rw [← nbrCount_erase_self]
    exact hd i
  have he' : ∀ i, graphCountError (p := p) D.halfGraph i ≤ 1 / 2 := fun i =>
    (graphCountError_bound D.halfGraph hn36 hd' (by omega) i).trans (by norm_num)
  dsimp only
  refine ⟨small_nsOp_tail D hW h4 hp hn hm hne, ?_, ?_, ?_⟩
  · intro v
    have h := collOp_uniform D hW (by omega) hne hn36
      (fun i => by rw [rowsDeg0_eq_full_nbrCount]; exact hd i) hr v
    apply h.trans (mul_le_mul_of_nonneg_right _ (norm_nonneg _))
    exact (collision_tail_scalar hp).trans
      (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
  · apply tail_normalizer_scalar (by positivity) (tail_rp_le hp) _ le_rfl le_rfl
    simpa only [one_div] using SecondOrder.AtMost.starZstar_uniform
      (graphPinned hW D.halfGraph (D.half_nonempty hne) he) D.Nset
      (Spectral.starCoef (p := p) D) (Spectral.starCoef_abs_le D) hn36 hn36 hd' he'
  · apply tail_perpendicular_scalar (by positivity) (tail_rp_le hp)
      (Real.sqrt_nonneg _) (by positivity) (by positivity) _ le_rfl le_rfl
    simpa only [Spectral.starMstar, one_div] using SecondOrder.AtMost.starMstar_uniform
      (graphPinned hW D.halfGraph (D.half_nonempty hne) he) D.Nset
      (Spectral.starCoef (p := p) D) (Spectral.starCoef_abs_le D) hn36 hn36 hd' he'

end Sarkozy.SpectralD.AtMost
