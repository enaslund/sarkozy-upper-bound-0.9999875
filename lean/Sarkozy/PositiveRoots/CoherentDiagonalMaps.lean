module

public import Sarkozy.PositiveRoots.CoherentRectangle
public import Sarkozy.PositiveRoots.CoherentCubeFrame

/-! Raw core and private star maps, including the sharper core-singleton bound. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.SpectralC Sarkozy.SpectralC.TwoLabel Sarkozy.SpectralD
open Sarkozy.L20Cap Sarkozy.Cuts Sarkozy.Recentering
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

noncomputable def rawStarMap {ι : Type*} (S : Finset ι) (F : ZMod p → ℝ) (x : ι → ZMod p) : ℝ :=
  (fieldLaw p).expect (fun z => StarMatrix.psi S z x * F z)

theorem cube_rawStar_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hp3 : p % 4 = 3) (S : Finset ι) (hS : S.Nonempty) (F : ZMod p → ℝ) :
    (cube p ι).expect (fun x => rawStarMap S F x ^ 2) ≤
      (p : ℝ)⁻¹ * (fieldLaw p).expect (fun z => F z ^ 2) := by
  have hd (i : ι) (_ : i ∈ S) (a : ZMod p) :
      (FiniteLaw.uniform (ZMod p)).weight a ≤ (1 : ℝ) / p := by
    simp only [FiniteLaw.uniform, ZMod.card, one_div, le_refl]
  have h := JointRows.StarOps.wOp_norm_le_odd (by omega : p ≠ 2)
    (fun _ : ι => FiniteLaw.uniform (ZMod p)) S hS hd F
  have he : JointRows.StarOps.wOp (fun _ : ι => FiniteLaw.uniform (ZMod p)) S F =
      rawStarMap S F := by
    funext x
    unfold JointRows.StarOps.wOp rawStarMap fieldLaw StarMatrix.psi
    simp_rw [uniform_phi hp3]
    exact FiniteLaw.expect_congr _ fun z => mul_comm _ _
  rw [he] at h
  simpa only [FiveType.ip, ← pow_two, one_mul, cube, fieldLaw] using h

theorem core_coordinate_square (hp3 : p % 4 = 3) [Nonempty (CoreT (ZMod p))]
    (i : Fin 4) (h : ZMod p → ℝ) :
    coreLaw.expect (fun c : CoreT (ZMod p) => h (c.val i) ^ 2) =
      (fieldLaw p).expect (fun z => h z ^ 2) := by
  have hm1 := JointRows.PaleyGauss.chi_neg_one hp3
  have h01 := core_sq_same hm1 (i := 0) (j := 1) (by decide) wPair_swap01 h
  have h23 := core_sq_same hm1 (i := 2) (j := 3) (by decide) wPair_swap23 h
  simp only [← pow_two, ZMod.card] at h01 h23
  rw [fieldLaw, FiniteLaw.expect_uniform, ZMod.card]
  fin_cases i
  · exact h01.1
  · exact h01.2
  · exact h23.1
  · exact h23.2

theorem core_singleton_map_sq (hp3 : p % 4 = 3) [Nonempty (CoreT (ZMod p))]
    (i : Fin 4) (F : ZMod p → ℝ) :
    coreLaw.expect (fun c : CoreT (ZMod p) => rawStarMap {i} F c.val ^ 2) ≤
      (p : ℝ)⁻¹ * (fieldLaw p).expect (fun z => F z ^ 2) := by
  have he (x : Fin 4 → ZMod p) : rawStarMap {i} F x = characterMap F (x i) := by
    simp only [rawStarMap, StarMatrix.psi, prod_singleton, characterMap]
  simp_rw [he]
  rw [core_coordinate_square hp3]
  exact characterMap_sq (by omega) F

omit [Fact p.Prime] in
theorem coreCubeDensity_ge_sixteen (hp7 : 7 < p) : 16 ≤ coreCubeDensity p := by
  have hp : (7 : ℝ) < p := by exact_mod_cast hp7
  have h1 : 0 < 1 - 1 / (p : ℝ) := by rw [sub_pos, div_lt_one (by linarith)]; linarith
  have h3 : 0 < 1 - 3 / (p : ℝ) := by rw [sub_pos, div_lt_one (by linarith)]; linarith
  have h7 : 0 < 1 - 7 / (p : ℝ) := by rw [sub_pos, div_lt_one (by linarith)]; exact hp
  have hupper : (1 - 1 / (p : ℝ)) * (1 - 3 / p) * (1 - 7 / p) ≤ 1 := by
    have h13 : (1 - 1 / (p : ℝ)) * (1 - 3 / p) ≤ 1 := by
      exact (mul_le_mul (sub_le_self 1 (by positivity))
        (sub_le_self 1 (by positivity)) h3.le (by norm_num)).trans_eq (one_mul 1)
    exact (mul_le_mul h13 (sub_le_self 1 (by positivity))
      h7.le (by norm_num)).trans_eq (one_mul 1)
  unfold coreCubeDensity
  rw [le_div_iff₀ (mul_pos (mul_pos h1 h3) h7)]
  linarith

def coreStarFactor (S : Finset (Fin 4)) : ℝ := if S.card = 1 then 1 else 4

omit [Fact p.Prime] in
theorem coreStarFactor_nonneg (S : Finset (Fin 4)) : 0 ≤ coreStarFactor S := by
  unfold coreStarFactor
  split_ifs <;> norm_num

noncomputable def coreStarPrice (p : ℕ) (S : Finset (Fin 4)) : ℝ :=
  coreStarFactor S * Real.sqrt (coreCubeDensity p / 16) * Real.sqrt ((p : ℝ)⁻¹)

noncomputable def privateStarPrice (p : ℕ) : ℝ :=
  Real.sqrt ((p : ℝ) / (p - 1)) * Real.sqrt ((p : ℝ)⁻¹)

theorem core_rawStar_map_sq (hp3 : p % 4 = 3) (hp7 : 7 < p)
    [Nonempty (CoreT (ZMod p))] (S : Finset (Fin 4)) (hS : S.Nonempty) (F : ZMod p → ℝ) :
    coreLaw.expect (fun c : CoreT (ZMod p) => rawStarMap S F c.val ^ 2) ≤
      coreStarPrice p S ^ 2 * nrm (fieldLaw p) F ^ 2 := by
  have hD := (coreCubeDensity_pos hp7).le
  have hn := (fieldLaw p).second_moment_nonneg F
  rw [coreStarPrice, mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hD (by norm_num)),
    Real.sq_sqrt (by positivity : 0 ≤ (p : ℝ)⁻¹), nrm_sq_expect]
  by_cases hs : S.card = 1
  · obtain ⟨i, rfl⟩ := card_eq_one.mp hs
    have h := core_singleton_map_sq hp3 i F
    have hD16 := coreCubeDensity_ge_sixteen hp7
    have hf : (1 : ℝ) ≤ coreCubeDensity p / 16 := (le_div_iff₀ (by norm_num)).mpr (by simpa using hD16)
    have hq := mul_nonneg (by positivity : 0 ≤ (p : ℝ)⁻¹) hn
    simp only [coreStarFactor, card_singleton, ite_true, one_pow, one_mul]
    exact h.trans (by nlinarith [mul_le_mul_of_nonneg_right hf hq])
  · have h := coreLaw_cube_comparison hp3 hp7 (fun x => rawStarMap S F x ^ 2) (fun _ => sq_nonneg _)
    have hc := mul_le_mul_of_nonneg_left (cube_rawStar_sq hp3 S hS F) hD
    simp only [coreStarFactor, ite_eq_right hs]
    convert h.trans hc using 1
    ring

theorem private_rawStar_map_sq (hp3 : p % 4 = 3)
    [Nonempty (PairT (ZMod p))] (S : Finset (Fin 2)) (hS : S.Nonempty) (F : ZMod p → ℝ) :
    pairLaw.expect (fun b : PairT (ZMod p) => rawStarMap S F ![b.val.1, b.val.2] ^ 2) ≤
      privateStarPrice p ^ 2 * nrm (fieldLaw p) F ^ 2 := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hD : 0 ≤ (p : ℝ) / (p - 1) := by positivity
  have h := pairLaw_le_privateCube (fun x => rawStarMap S F x ^ 2) (fun _ => sq_nonneg _)
  have hc := mul_le_mul_of_nonneg_left (cube_rawStar_sq hp3 S hS F) hD
  rw [privateStarPrice, mul_pow, Real.sq_sqrt hD,
    Real.sq_sqrt (by positivity : 0 ≤ (p : ℝ)⁻¹), nrm_sq_expect]
  convert h.trans hc using 1
  ring

end Sarkozy.PositiveRoots.CoherentFrame
