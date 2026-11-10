module

public import Sarkozy.MiddleCertificates.Checks
public import Sarkozy.SpectralD.ComplexFiniteTest
public import Sarkozy.SpectralD.ClassThreeCharacters

/-!
# The class-three finite tests of L10 and L21 at every prime `p ≡ 3 (mod 4)` (`cert:layer12-grid`)

`paper/sections/14_spectral.tex`, `thm:spectral-criterion`, the test `eq:spectral-test` for the
class `𝔠 = 3`; `paper/sections/20_middle_reference.tex`, `cert:layer12-grid` (the class-three
tests of the cuts L10 and L21 at the 33 piece starts).

At `p ≡ 3 (mod 4)` the matrices of the test do not depend on `p`: `Δ^E = ς`
(`FiniteModel.deltaE_three`), `𝐇⁺ = 𝐇` (`FiniteModel.hplusM_three`), and the Fourier coefficient
`χ(ξ)ε_G` is one of `-i, 0, i` (`chi_eps_three`). So the kernel-checked certificates of
`Checks.lean` give, at the recorded `τ = τ^sp_{3,±}` and bars `c̄_⊥`, `η̄_Q`, `η̄_B` of the start of
piece `i`,

* **`finiteTest_three`**: the hypotheses `htp`, `htm` of `SpectralD.Cx.spectral_criterion_cut_full`
  (WP-A's `FiniteTest` for `𝐀₀(ξ)` and `𝐇⁺ - 𝐀₀(ξ)^*𝐀₀(ξ)`) for the actual spectral data of L10
  and L21, at every prime `p ≡ 3 (mod 4)` and every `ξ ∈ 𝔽_p` (including `ξ = 0`);
* **`finiteTest_mono`**: the test stays valid for a larger `c̄_⊥` and smaller `η̄_Q`, `η̄_B`;
* **`g_le_allpG`**: `(c̄_⊥ + τ)/(1 - ε̄_V) ≤ allpG i c` (the conditions `hgp`, `hgm` of the
  criterion at the ALLp constant of the cut).

The tests are those of the paper's records: the generator reads `τ` and the upper ends of
`c_⊥`, `η_Q`, `η_B`, `ε_V` from `middle12_grid.json` and `middle_grid_new.json`.
-/

@[expose] public section

namespace Sarkozy.MiddleCertificates

open Finset Sarkozy.SpectralC Sarkozy.SpectralD MidCut
open scoped Matrix

theorem test_matrix_eq (c : MidCut) (i : Fin 33) (e : Fin 3) :
    (fun a b => gaussian (testReal c i e a b) (testImag c i e a b)) =
      complexTest (modelD c) (modelH c) 100000000 (base c i) (linear c i) (char e) 1 := by
  funext a b
  have hs : (∑ k, ((modelD c k a : ℂ)) * (modelD c k b : ℂ)) =
      (((∑ k, modelD c k a * modelD c k b : ℤ)) : ℂ) := by push_cast; rfl
  have hc : ((char e : ℂ)) ^ 2 = (((char e) ^ 2 : ℤ) : ℂ) := by push_cast; ring
  have hp : phase (1 : Fin 2) = Complex.I := rfl
  unfold complexTest
  rw [hs, hc, hp]
  by_cases h : a = b
  · apply Complex.ext
    · simp only [gaussian, testReal, h, ↓reduceIte, Complex.add_re, Complex.sub_re,
        Complex.mul_re, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, Complex.I_re,
        Complex.I_im]
      push_cast
      ring
    · simp only [gaussian, testImag, h, ↓reduceIte, Complex.add_im, Complex.sub_im,
        Complex.mul_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.I_re,
        Complex.I_im]
      push_cast
      ring
  · apply Complex.ext
    · simp only [gaussian, testReal, h, ↓reduceIte, Complex.add_re, Complex.sub_re,
        Complex.mul_re, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, Complex.I_re,
        Complex.I_im, Complex.zero_re]
      push_cast
      ring
    · simp only [gaussian, testImag, h, ↓reduceIte, Complex.add_im, Complex.sub_im,
        Complex.mul_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.I_re,
        Complex.I_im, Complex.zero_im]
      push_cast
      ring

theorem test_nonneg (c : MidCut) (i : Fin 33) (e : Fin 3) (x : c.data.cut.Half → ℂ) :
    0 ≤ (qform (fun a b => gaussian (testReal c i e a b) (testImag c i e a b)) x).re :=
  qform_nonneg_of_gaussian_factor (testReal c i e) (testImag c i e)
    (factorReal c i e) (factorImag c i e) 1000000000000 (shift c i e)
    (by norm_num) ((residuals c i) e).1 ((residuals c i) e).2.1 ((residuals c i) e).2.2 x

theorem tau_pos (c : MidCut) (i : Fin 33) : (0 : ℝ) < tau c i := by
  exact_mod_cast (scalars c i).2.1

theorem linear_eq (c : MidCut) (i : Fin 33) : (linear c i : ℝ) = 100000000 * (tau c i : ℝ) := by
  have h := (scalars c i).1
  have h' : ((linear c i : ℚ) : ℝ) = ((100000000 * tau c i : ℚ) : ℝ) := by rw [h]
  push_cast at h'
  exact h'

theorem base_eq (c : MidCut) (i : Fin 33) :
    (base c i : ℝ) = 100000000 * ((tau c i : ℝ) * ((cbar c i : ℝ) + tau c i - etaQ c i) -
      etaB c i) := by
  unfold etaB
  push_cast
  ring

/-- **The class-three test at the model matrices**: `FiniteTest` for `𝐀 = (e - 1) i ς` and
`𝐇`, at the recorded `τ` and bars of piece `i`. -/
theorem finiteTest_model (c : MidCut) (i : Fin 33) (e : Fin 3) :
    Spectral.FiniteTest
      (fun x => (qform (fun a b => phaseMode (modelD c) (char e) 1 a b) x).re)
      (fun x => Spectral.qform (integerMatrix (modelH c)) x x -
        Spectral.sqn (phaseMode (modelD c) (char e) 1 *ᵥ x))
      (cbar c i) (tau c i) (etaQ c i) (etaB c i) := by
  apply finiteTest_of_scaled_matrix _ _
    (fun a b => gaussian (testReal c i e a b) (testImag c i e a b))
    (scale := 100000000) (tau_pos c i) (by norm_num)
  · rw [test_matrix_eq]
    exact complexTest_cast _ _ _ _ _ _ _ (linear_eq c i) (base_eq c i)
  · exact test_nonneg c i e

variable {p : ℕ} [Fact p.Prime]

/-- **`eq:spectral-test` at class three for the actual cut L10 or L21** (`cert:layer12-grid`):
for every prime `p ≡ 3 (mod 4)` and every `ξ ∈ 𝔽_p`, WP-A's finite test holds for the degree-one
matrix `𝐀₀(ξ) = χ(ξ)ε_GΔ^E` and the coupling form `x^*𝐇⁺x - |𝐀₀(ξ)x|²` of the spectral data, at
the recorded `τ` and the bars `c̄_⊥`, `η̄_Q`, `η̄_B` of the start of piece `i`. These are the
hypotheses `htp`, `htm` of `SpectralD.Cx.spectral_criterion_cut_full` with `Adj` the Boolean
adjacency. -/
theorem finiteTest_three (c : MidCut) (i : Fin 33) (hp3 : p % 4 = 3) (ξ : ZMod p) :
    Spectral.FiniteTest (fun x => (qform (azero (Cx.sgnZ c.data) ξ) x).re)
      (Cx.qXcx (FiniteModel.Adj c.edge c.data.cut) c.data.Nset (Cx.sgnZ c.data) ξ)
      (cbar c i) (tau c i) (etaQ c i) (etaB c i) := by
  obtain ⟨e, he⟩ := chi_eps_three hp3 ξ
  have hA : azero (Cx.sgnZ c.data) ξ = (fun a b => phaseMode (modelD c) (char e) 1 a b) := by
    funext a b
    unfold azero phaseMode
    rw [FiniteModel.deltaE_three c.data c.edge (mem_edge c) hp3, he, ((models c) a b).1]
    simp [phase, char]
  have hH : PaleyB.hplusM (FiniteModel.Adj c.edge c.data.cut) c.data.Nset
      (Cx.sgnZ (p := p) c.data) = (fun a b => integerMatrix (modelH c) a b) := by
    funext a b
    rw [FiniteModel.hplusM_three c.data c.edge (mem_edge c) hp3, ((models c) a b).2]
    rfl
  intro x
  simpa only [Cx.qXcx, hA, hH] using finiteTest_model c i e x

theorem char_rev (e : Fin 3) : char (Fin.rev e) = -char e := by
  fin_cases e <;> rfl

theorem phaseMode_neg {U : Type*} [Fintype U] (D : U → U → ℤ) (ε : ℤ) (a : Fin 2) :
    phaseMode D (-ε) a = -phaseMode D ε a := by
  funext i j
  simp only [phaseMode, Int.cast_neg, Matrix.neg_apply]
  ring

theorem qform_neg_re {U : Type*} [Fintype U] (M : Matrix U U ℂ) (x : U → ℂ) :
    (qform (fun i j => (-M) i j) x).re = -(qform (fun i j => M i j) x).re := by
  unfold qform
  simp only [Matrix.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib, Complex.neg_re]

theorem sqn_neg_mulVec {U : Type*} [Fintype U] (M : Matrix U U ℂ) (x : U → ℂ) :
    Spectral.sqn ((-M) *ᵥ x) = Spectral.sqn (M *ᵥ x) := by
  unfold Spectral.sqn
  simp only [Matrix.neg_mulVec, Pi.neg_apply, norm_neg]

/-- **The negated test** (the tests of `-𝐀₀(ξ)` used for `thm:spectral-criterion`(b)): at class
three it is the test at `-ξ`, i.e. at the conjugate coefficient. -/
theorem finiteTest_three_neg (c : MidCut) (i : Fin 33) (hp3 : p % 4 = 3) (ξ : ZMod p) :
    Spectral.FiniteTest (fun x => -(qform (azero (Cx.sgnZ c.data) ξ) x).re)
      (Cx.qXcx (FiniteModel.Adj c.edge c.data.cut) c.data.Nset (Cx.sgnZ c.data) ξ)
      (cbar c i) (tau c i) (etaQ c i) (etaB c i) := by
  obtain ⟨e, he⟩ := chi_eps_three hp3 ξ
  have hA : azero (Cx.sgnZ c.data) ξ = (fun a b => phaseMode (modelD c) (char e) 1 a b) := by
    funext a b
    unfold azero phaseMode
    rw [FiniteModel.deltaE_three c.data c.edge (mem_edge c) hp3, he, ((models c) a b).1]
    simp [phase, char]
  have hH : PaleyB.hplusM (FiniteModel.Adj c.edge c.data.cut) c.data.Nset
      (Cx.sgnZ (p := p) c.data) = (fun a b => integerMatrix (modelH c) a b) := by
    funext a b
    rw [FiniteModel.hplusM_three c.data c.edge (mem_edge c) hp3, ((models c) a b).2]
    rfl
  have hM : phaseMode (modelD c) (char e) 1 = -phaseMode (modelD c) (char (Fin.rev e)) 1 := by
    rw [char_rev, phaseMode_neg, neg_neg]
  intro x
  have h := finiteTest_model c i (Fin.rev e) x
  have h1 : -(qform (azero (Cx.sgnZ c.data) ξ) x).re =
      (qform (fun a b => phaseMode (modelD c) (char (Fin.rev e)) 1 a b) x).re := by
    rw [hA, hM, qform_neg_re, neg_neg]
  have h2 : Cx.qXcx (FiniteModel.Adj c.edge c.data.cut) c.data.Nset (Cx.sgnZ c.data) ξ x =
      Spectral.qform (integerMatrix (modelH c)) x x -
        Spectral.sqn (phaseMode (modelD c) (char (Fin.rev e)) 1 *ᵥ x) := by
    unfold Cx.qXcx
    rw [hH]
    have h3 : (azero (Cx.sgnZ c.data) ξ : Matrix _ _ ℂ) =
        -phaseMode (modelD c) (char (Fin.rev e)) 1 := by
      rw [hA, hM]
    rw [h3, sqn_neg_mulVec]
  change 0 ≤ -(qform (azero (Cx.sgnZ c.data) ξ) x).re -
      Cx.qXcx (FiniteModel.Adj c.edge c.data.cut) c.data.Nset (Cx.sgnZ c.data) ξ x / ↑(tau c i) +
      (↑(cbar c i) + ↑(tau c i) - ↑(etaQ c i) - ↑(etaB c i) / ↑(tau c i)) * Spectral.sqn x
  rw [h1, h2]
  exact h

/-- **Monotonicity of the finite test in its scalars**: a larger `c̄_⊥` and smaller `η̄_Q`, `η̄_B`
keep it valid (the bars of the criterion need only be upper bounds of the inputs at `p`). -/
theorem finiteTest_mono {n : Type*} [Fintype n] {qA qX : (n → ℂ) → ℝ} {c s ηQ ηB c' ηQ' ηB' : ℝ}
    (h : Spectral.FiniteTest qA qX c s ηQ ηB) (hs : 0 < s) (hc : c ≤ c') (hQ : ηQ' ≤ ηQ)
    (hB : ηB' ≤ ηB) : Spectral.FiniteTest qA qX c' s ηQ' ηB' := by
  intro x
  have h0 := h x
  have hn := Spectral.sqn_nonneg x
  have h1 : ηB' / s ≤ ηB / s := div_le_div_of_nonneg_right hB hs.le
  have h2 : (c + s - ηQ - ηB / s) * Spectral.sqn x ≤ (c' + s - ηQ' - ηB' / s) * Spectral.sqn x :=
    mul_le_mul_of_nonneg_right (by linarith) hn
  linarith

/-- **The choice of `g`** (`thm:spectral-criterion`: `g_𝔠 ≥ (c̄_⊥ + τ)/(1 - ε̄_V)`), at the ALLp
constant of the cut: `(c̄_⊥ + τ)/(1 - ε̄_V) ≤ allpG i c` (`allpG i 1` for L10, `allpG i 2` for
L21), with `0 ≤ ε̄_V < 1`. -/
theorem g_le_allpG (c : MidCut) (i : Fin 33) :
    ((cbar c i : ℝ) + tau c i) / (1 - epsV c i) ≤ BlockSpecPaper.AllpData.allpG i c.allpIdx ∧
      (0 : ℝ) ≤ epsV c i ∧ (epsV c i : ℝ) < 1 ∧ (0 : ℝ) ≤ cbar c i := by
  obtain ⟨-, -, hc0, hv0, hv1, hg, hg'⟩ := scalars c i
  refine ⟨?_, by exact_mod_cast hv0, by exact_mod_cast hv1, by exact_mod_cast hc0⟩
  have h := hg.trans hg'
  have h' : (((cbar c i + tau c i) / (1 - epsV c i) : ℚ) : ℝ) ≤
      ((BlockSpecPaper.AllpData.allpG i c.allpIdx : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  exact h'

end Sarkozy.MiddleCertificates
