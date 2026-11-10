module

public import Sarkozy.SpectralD.StarMatrixNorm

@[expose] public section

/-!
# Sanity checks for `cor:star-matrix` (non-vacuity)

The hypotheses of `Sarkozy.SpectralD.StarMatrix` are satisfiable:

* the uniform law on all labellings `x : U → 𝔽_p` (`unifLab`) is a probability law invariant
  under `Aff_p`, so `starPart_compress` and `starPart_factor` apply to it (`unifLab_compress`);
  for a single vertex it is also supported on injective labellings (`unifLab_inj`);
* at `p = 3`, `U = Fin 1` (one vertex, no supports) every hypothesis of
  `starPart_norm_le_rowsum` holds, with `N = 0`, `ρ = 0` and `‖M(i)‖ ≤ |d₀₀|`
  (`toy_normLe`, `toy_star_matrix_bound`): the kernel is the single pair `d₀₀ χ(y₀ − x₀)` and the
  conclusion is `|⟨P₀g, K P₀f⟩| ≤ r |d₀₀| ‖g‖ ‖f‖`.

New material for this paper.
-/

namespace Sarkozy.SpectralD.StarMatrix

open Finset Complex Sarkozy.SpectralC
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

/-- The uniform law on all labellings `x : U → 𝔽_p`. -/
noncomputable def unifLab (p : ℕ) (U : Type*) [Fintype U] (_x : U → ZMod p) : ℝ :=
  ((p : ℝ) ^ Fintype.card U)⁻¹

omit [Fact p.Prime] [DecidableEq U] in
lemma unifLab_nonneg (x : U → ZMod p) : 0 ≤ unifLab p U x := by
  unfold unifLab; positivity

lemma unifLab_total : ∑ x : U → ZMod p, unifLab p U x = 1 := by
  unfold unifLab
  rw [sum_const, card_univ, Fintype.card_fun, ZMod.card, nsmul_eq_mul]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  push_cast
  field_simp

omit [DecidableEq U] in
lemma unifLab_inv (s c : ZMod p) (x : U → ZMod p) (_hs : s ≠ 0) (_hsq : IsSquare s) :
    unifLab p U (affLab s c x) = unifLab p U x := rfl

omit [Fact p.Prime] [DecidableEq U] in
lemma unifLab_inj [Subsingleton U] (x : U → ZMod p) (k l : U) (_hx : unifLab p U x ≠ 0)
    (hkl : k ≠ l) : x k ≠ x l :=
  absurd (Subsingleton.elim k l) hkl

/-- **Non-vacuity of the factorisation**: `starPart_compress` applies to the uniform law. -/
theorem unifLab_compress (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (d : U → U → ℝ)
    (L : U → Finset U → ℝ) (R : Finset U → U → ℝ) (𝒮 : Finset (Finset U))
    (g f : (U → ZMod p) → ℂ) :
    bil (unifLab p U) (cent (unifLab p U) g) (starPart d L R 𝒮) (cent (unifLab p U) f) =
      ∑ i, ∑ j, (d i j : ℂ) * ip (vAdj (unifLab p U) i g) (gaussOp (vAdj (unifLab p U) j f)) +
        ∑ i, ∑ S ∈ 𝒮, (-1 : ℂ) ^ S.card * (L i S : ℂ) *
          ip (vAdj (unifLab p U) i g) (wAdj (unifLab p U) S f) +
        ∑ S ∈ 𝒮, ∑ j, (R S j : ℂ) * ip (wAdj (unifLab p U) S g) (vAdj (unifLab p U) j f) :=
  starPart_compress hp2 hp3 _ unifLab_total unifLab_inv d L R 𝒮 g f

/-! ## A toy instance of the norm bound: `p = 3`, one vertex -/

/-- One vertex has no supports. -/
lemma supports_fin_one : supports (Fin 1) = ∅ := by
  unfold supports
  ext S
  simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false, not_le]
  have := card_le_univ S
  simp only [Fintype.card_fin] at this
  omega

/-- The features of one vertex with no supports: only `V₀`. -/
abbrev ToyFeat : Type := Feat (Fin 1) (∅ : Finset (Finset (Fin 1)))

lemma toy_sum (F : ToyFeat → ℂ) : ∑ a, F a = F (Sum.inl 0) := by
  rw [Fintype.sum_sum_type, Fin.sum_univ_one]
  have h0 : ∑ S : {S : Finset (Fin 1) // S ∈ (∅ : Finset (Finset (Fin 1)))}, F (Sum.inr S) = 0 :=
    sum_eq_zero fun S _ => (notMem_empty S.1 S.2).elim
  rw [h0, add_zero]

lemma toy_sum_real (F : ToyFeat → ℝ) : ∑ a, F a = F (Sum.inl 0) := by
  rw [Fintype.sum_sum_type, Fin.sum_univ_one]
  have h0 : ∑ S : {S : Finset (Fin 1) // S ∈ (∅ : Finset (Finset (Fin 1)))}, F (Sum.inr S) = 0 :=
    sum_eq_zero fun S _ => (notMem_empty S.1 S.2).elim
  rw [h0, add_zero]

lemma toy_eq (a : ToyFeat) : a = Sum.inl 0 := by
  rcases a with i | S
  · rw [Subsingleton.elim i 0]
  · exact (notMem_empty S.1 S.2).elim

lemma toy_vnorm (w : ToyFeat → ℂ) : vnorm w = ‖w (Sum.inl 0)‖ := by
  unfold vnorm
  rw [toy_sum_real (fun a => ‖w a‖ ^ 2), Real.sqrt_sq (norm_nonneg _)]

/-- `‖M(i)‖ ≤ |d₀₀|` for one vertex: `M(i)` is the `1 × 1` matrix `i d₀₀`. -/
lemma toy_normLe (d : Fin 1 → Fin 1 → ℝ) (L : Fin 1 → Finset (Fin 1) → ℝ)
    (R : Finset (Fin 1) → Fin 1 → ℝ) :
    NormLe (matI (starM0 L R ∅) (starM1 d ∅)) |d 0 0| := by
  intro w z
  unfold bform
  rw [toy_sum, toy_sum, toy_vnorm, toy_vnorm]
  simp only [matI, starM0, starM1, Complex.ofReal_zero, zero_add, norm_mul, Complex.norm_conj,
    Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  ring_nf
  exact le_refl _

/-- **The toy instance** (`p = 3`, one vertex): every hypothesis of `starPart_norm_le_rowsum`
holds, and it gives `|⟨P₀g, d₀₀ χ(y₀ − x₀) P₀f⟩| ≤ r |d₀₀| ‖g‖ ‖f‖` (the kernel is the
single pair; `‖C‖ = r`). -/
theorem toy_star_matrix_bound (d : Fin 1 → Fin 1 → ℝ) (L : Fin 1 → Finset (Fin 1) → ℝ)
    (R : Finset (Fin 1) → Fin 1 → ℝ) (g f : (Fin 1 → ZMod 3) → ℂ) :
    ‖bil (unifLab 3 (Fin 1)) (cent (unifLab 3 (Fin 1)) g) (starPart d L R ∅)
        (cent (unifLab 3 (Fin 1)) f)‖ ≤
      rp 3 * |d 0 0| * (1 + 0) * √(∑ x, unifLab 3 (Fin 1) x * ‖g x‖ ^ 2) *
        √(∑ x, unifLab 3 (Fin 1) x * ‖f x‖ ^ 2) :=
  starPart_norm_le_rowsum (by norm_num) (by norm_num) _ unifLab_nonneg unifLab_total unifLab_inv
    unifLab_inj d L R ∅ (fun S hS => (notMem_empty S hS).elim) (abs_nonneg _) le_rfl
    (toy_normLe d L R) (fun _ _ => 0) (fun _ _ => le_rfl) (fun _ _ => rfl)
    (fun a => by rw [toy_sum_real]; simp)
    (fun a b hab => absurd ((toy_eq a).trans (toy_eq b).symm) hab) g f

end Sarkozy.SpectralD.StarMatrix
