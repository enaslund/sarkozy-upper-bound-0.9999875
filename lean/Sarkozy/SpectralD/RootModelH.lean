module

public import Sarkozy.SpectralD.RootChecks
public import Sarkozy.SpectralD.CouplingInputs

/-!
# The model matrix `𝐇` at the root cuts, `p ≡ 3 (mod 4)`

`paper/sections/14_spectral.tex`, `cor:spec2:coupling` (the matrix `𝐇` of `lem:spec2:gram`,
`Sarkozy.SpectralC.modelH`), and `paper/sections/25_upper_reference.tex`,
`subsec:record:upper_root` (route B: at `p ≡ 3 (mod 4)`, `𝐇⁺ = 𝐇`).

At `p ≡ 3 (mod 4)` we have `χ(−1) = −1`, so for cross signs `ς ∈ {−1, 0, 1}` the factor
`1 + χ(ς_{jk} ς_{jl})` is the integer `1 + ς_{jk} ς_{jl}`, and the factors with
`j ∉ N(k) ∩ N(l)` are `1`. Hence `𝐇` is the integer matrix
`hMat D k l = ∏_{j ∈ U⁺} (1 + ς_{jk} ς_{jl}) − 1`, for any spectral data `D` and every prime
`p ≡ 3 (mod 4)` (`modelH_eq`). It is symmetric (`hMat_symm`), with diagonal `2^{r_k} − 1`.

`lamH_of_rowsum`: `λ̄(𝐇) ≤ max_k ∑_l |𝐇_{kl}|` (Schur test, `PaleyB.qform_re_le_of_rowsum`), in
the form `hlam` of `Sarkozy.SpectralD.Cx.spectral_criterion_cut_S1`.

At the root cuts (checked by `decide +kernel` on the Boolean form `hB`):
* LL20: `∑_l |𝐇_{kl}| ≤ 8856` for every `k` (`LL20_rowsum`), so `λ̄(𝐇) = 8856` works
  (`LL20_lamH`);
* LL22: `∑_l |𝐇_{kl}| ≤ 1098` for every `k` (`LL22_rowsum`), so `λ̄(𝐇) = 1098` works
  (`LL22_lamH`).

These are the maximal absolute row sums `‖𝐇‖_row`, the value of `λ̄(𝐇)` that
`lem:record:frame-inputs` uses at the root cuts (in `ε_rem` and `ε_B`). By the explicit tables of
`Sarkozy.SpectralD.RootTables`, the row sums are `2140` and `8856` (LL20) and `1098` (LL22). The
diagonal entries are `2^{r_k} − 1 ∈ {1023, 4095}` (LL20) and `1023` (LL22). The off-diagonal entries
are `−1, 0, 3, 15, 255, 1023, 4095` (LL20) and `−1, 3, 15` (LL22). For comparison,
floating-point power iteration gives `λ_max(𝐇) ≈ 8820.01` (LL20) and `≈ 1050.56` (LL22); this is
not used.

New material for this paper.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.SpectralD.Root

open Sarkozy Sarkozy.SpectralC Sarkozy.SpectralD.Cx

section General

variable {W : Type*} [Fintype W] [DecidableEq W] (D : Cuts.SpecData W)

/-- The integer matrix `𝐇_{kl} = ∏_{j ∈ U⁺} (1 + ς_{jk} ς_{jl}) − 1`: the model matrix `𝐇` of
`lem:spec2:gram` at `p ≡ 3 (mod 4)` (`modelH_eq`). -/
def hMat (k l : D.cut.Half) : ℤ := ∏ j, (1 + D.sgn j k * D.sgn j l) - 1

theorem hMat_symm (k l : D.cut.Half) : hMat D k l = hMat D l k := by
  unfold hMat
  congr 1
  exact prod_congr rfl (fun j _ => by ring)

theorem sgn_cases (j k : D.cut.Half) : D.sgn j k = 1 ∨ D.sgn j k = -1 ∨ D.sgn j k = 0 := by
  unfold Cuts.SpecData.sgn
  split_ifs <;> simp

variable {p : ℕ} [Fact p.Prime]

/-- `χ(s) = s` for `s ∈ {1, −1, 0}` at `p ≡ 3 (mod 4)` (`χ(−1) = −1`). -/
theorem chi_int (hp3 : p % 4 = 3) (s : ℤ) (hs : s = 1 ∨ s = -1 ∨ s = 0) :
    ((quadraticChar (ZMod p) (s : ZMod p) : ℤ) : ℝ) = s := by
  have hp2 : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  rcases hs with rfl | rfl | rfl
  · rw [Int.cast_one, MulChar.map_one]
  · have h := quadraticChar_neg_one (F := ZMod p) hp2
    rw [ZMod.card, ZMod.χ₄_nat_three_mod_four hp3] at h
    have h' : quadraticChar (ZMod p) ((-1 : ℤ) : ZMod p) = -1 := by
      rw [Int.cast_neg, Int.cast_one]
      exact h
    rw [h']
  · rw [Int.cast_zero, MulChar.map_zero]

/-- The factor `1 + χ(ς_{jk} ς_{jl})` at `p ≡ 3 (mod 4)` is the integer `1 + ς_{jk} ς_{jl}`. -/
theorem chi_factor (hp3 : p % 4 = 3) (j k l : D.cut.Half) :
    (1 + (quadraticChar (ZMod p) (sgnZ (p := p) D j k * sgnZ (p := p) D j l) : ℝ)) =
      ((1 + D.sgn j k * D.sgn j l : ℤ) : ℝ) := by
  have hs : D.sgn j k * D.sgn j l = 1 ∨ D.sgn j k * D.sgn j l = -1 ∨
      D.sgn j k * D.sgn j l = 0 := by
    rcases sgn_cases D j k with h1 | h1 | h1 <;> rcases sgn_cases D j l with h2 | h2 | h2 <;>
      simp [h1, h2]
  have e : sgnZ (p := p) D j k * sgnZ (p := p) D j l =
      ((D.sgn j k * D.sgn j l : ℤ) : ZMod p) := by
    unfold sgnZ
    exact (Int.cast_mul _ _).symm
  rw [e, chi_int hp3 _ hs, Int.cast_add, Int.cast_one]

/-- **`𝐇` at `p ≡ 3 (mod 4)` is the integer matrix `hMat`.** -/
theorem modelH_eq (hp3 : p % 4 = 3) (k l : D.cut.Half) :
    modelH D.Nset (sgnZ (p := p) D) k l = (hMat D k l : ℝ) := by
  unfold modelH hMat
  rw [Int.cast_sub, Int.cast_prod, Int.cast_one]
  congr 1
  rw [prod_congr rfl (fun j _ => chi_factor D hp3 j k l)]
  refine prod_subset (subset_univ _) (fun j _ hj => ?_)
  simp only [mem_inter, Cuts.SpecData.Nset, mem_filter, mem_univ, true_and, not_and_or,
    not_not] at hj
  rcases hj with h | h <;> simp [h]

/-- **`λ̄(𝐇)` from the row sums of `|𝐇|`** at `p ≡ 3 (mod 4)` (Schur test): if
`∑_l |𝐇_{kl}| ≤ L` for every `k`, then `Re w^*𝐇w ≤ L |w|²`; the hypothesis `hlam` of
`Sarkozy.SpectralD.Cx.spectral_criterion_cut_S1` with `λ̄ = L`. -/
theorem lamH_of_rowsum (hp3 : p % 4 = 3) {L : ℤ} (hL : ∀ k, ∑ l, |hMat D k l| ≤ L)
    (w : D.cut.Half → ℂ) :
    (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) w).re ≤ L * ∑ j, ‖w j‖ ^ 2 := by
  refine PaleyB.qform_re_le_of_rowsum _ (fun k l => |(hMat D k l : ℝ)|)
    (fun k l => abs_nonneg _) (fun k l => by rw [hMat_symm]) (fun k l => ?_) (fun k => ?_) w
  · unfold PaleyB.modelHC
    rw [Complex.norm_real, Real.norm_eq_abs, modelH_eq D hp3]
  · have h : ∑ l, |(hMat D k l : ℝ)| = ((∑ l, |hMat D k l| : ℤ) : ℝ) := by
      push_cast
      rfl
    rw [h]
    exact_mod_cast hL k

end General

/-! ### The root cuts -/

/-- `𝐇` in Boolean form: `∏_{j ∈ U⁺} (1 + ς_{jk} ς_{jl}) − 1` with the signs `sgnB f`. -/
def hB (f : Slot → Slot) {c : ReflectionCut Slot} (k l : c.Half) : ℤ :=
  ∏ j : c.Half, (1 + sgnB f j.1 k.1 * sgnB f j.1 l.1) - 1

theorem hMat_eq_hB (D : Cuts.SpecData Slot) (hG : D.G = Labellings.rootGraph)
    (k l : D.cut.Half) : hMat D k l = hB D.cut.flip k l := by
  unfold hMat hB
  simp only [sgn_eq D hG]

theorem LL20_rowsum_bool :
    ∀ k : LL20.cut.Half, ∑ l : LL20.cut.Half, |hB LL20.cut.flip k l| ≤ 8856 := by
  decide +kernel

theorem LL22_rowsum_bool :
    ∀ k : LL22.cut.Half, ∑ l : LL22.cut.Half, |hB LL22.cut.flip k l| ≤ 1098 := by
  decide +kernel

/-- The absolute row sums of `𝐇` for LL20 are at most `8856`. -/
theorem LL20_rowsum : ∀ k : LL20.cut.Half, ∑ l, |hMat LL20 k l| ≤ 8856 := by
  intro k
  simp only [hMat_eq_hB LL20 LL20_G]
  exact LL20_rowsum_bool k

/-- The absolute row sums of `𝐇` for LL22 are at most `1098`. -/
theorem LL22_rowsum : ∀ k : LL22.cut.Half, ∑ l, |hMat LL22 k l| ≤ 1098 := by
  intro k
  simp only [hMat_eq_hB LL22 LL22_G]
  exact LL22_rowsum_bool k

/-- **`λ̄(𝐇) = 8856` for LL20** at every prime `p ≡ 3 (mod 4)` (row sums), the hypothesis `hlam`
of `Sarkozy.SpectralD.Cx.spectral_criterion_cut_S1`. -/
theorem LL20_lamH {p : ℕ} [Fact p.Prime] (hp3 : p % 4 = 3) (w : LL20.cut.Half → ℂ) :
    (qform (PaleyB.modelHC LL20.Nset (sgnZ (p := p) LL20)) w).re ≤ 8856 * ∑ j, ‖w j‖ ^ 2 := by
  have h := lamH_of_rowsum LL20 hp3 LL20_rowsum w
  exact_mod_cast h

/-- **`λ̄(𝐇) = 1098` for LL22** at every prime `p ≡ 3 (mod 4)` (row sums), the hypothesis `hlam`
of `Sarkozy.SpectralD.Cx.spectral_criterion_cut_S1`. -/
theorem LL22_lamH {p : ℕ} [Fact p.Prime] (hp3 : p % 4 = 3) (w : LL22.cut.Half → ℂ) :
    (qform (PaleyB.modelHC LL22.Nset (sgnZ (p := p) LL22)) w).re ≤ 1098 * ∑ j, ‖w j‖ ^ 2 := by
  have h := lamH_of_rowsum LL22 hp3 LL22_rowsum w
  exact_mod_cast h

end Sarkozy.SpectralD.Root
