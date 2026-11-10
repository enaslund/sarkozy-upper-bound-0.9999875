module

public import Sarkozy.ExtractionK.Grouped

@[expose] public section

/-!
# Grouped extraction, operator-norm form (`lem:matching:extractionk`)

`paper/sections/16_extraction.tex`, `lem:matching:extractionk`, as an operator bound. With
`T_𝒞 h(x) = E_{x' ∼ μ}[(∑_{S ∈ 𝒞} χ_S(x, x')) h(x')]` (`T_𝒞 = ∑_{S ∈ 𝒞} T_S` on `L²(μ)`,
`μ = λ_p(G⁺)`), the bilinear bound `|⟨f, T_𝒞 h⟩_μ| ≤ B ‖f‖_μ ‖h‖_μ` of `grouped_extraction`
for all `f`, `h` gives `‖T_𝒞 h‖_μ ≤ B ‖h‖_μ` (`grouped_extraction_norm`), i.e.
`‖T_𝒞‖ ≤ c_ker r^k 2^{ex(𝒞)/2} (∏_v F_v)^{1/2} (1 - ê)^{-k}`; this is the form in which
`cor:extraction-leaf`(a) states the class bound (`‖T_𝒞‖ ≤ …`).
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

/-- `a ≤ B √a √b` with `a, b ≥ 0` gives `a ≤ B² b`. -/
theorem le_sq_mul_of_le_sqrt {a b B : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ≤ B * Real.sqrt a * Real.sqrt b) : a ≤ B ^ 2 * b := by
  rcases eq_or_lt_of_le ha with h0 | hpos
  · rw [← h0]
    positivity
  · have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr hpos
    have h1 : Real.sqrt a ≤ B * Real.sqrt b := by
      have e : a = Real.sqrt a * Real.sqrt a := (Real.mul_self_sqrt ha).symm
      have h' : Real.sqrt a * Real.sqrt a ≤ (B * Real.sqrt b) * Real.sqrt a := by
        calc Real.sqrt a * Real.sqrt a = a := e.symm
          _ ≤ B * Real.sqrt a * Real.sqrt b := h
          _ = (B * Real.sqrt b) * Real.sqrt a := by ring
      exact le_of_mul_le_mul_right h' hsa
    have h2 := mul_self_le_mul_self (Real.sqrt_nonneg a) h1
    rw [Real.mul_self_sqrt ha] at h2
    calc a ≤ (B * Real.sqrt b) * (B * Real.sqrt b) := h2
      _ = B ^ 2 * (Real.sqrt b * Real.sqrt b) := by ring
      _ = B ^ 2 * b := by rw [Real.mul_self_sqrt hb]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- **`lem:matching:extractionk`, operator form**: under the hypotheses of `grouped_extraction`,
`‖T_𝒞 h‖²_μ ≤ B² ‖h‖²_μ` with `B = c_ker r^k 2^{ex(𝒞)/2} (∏_v F_v)^{1/2} (1 - ê)^{-k}`, where
`T_𝒞 h(x) = E_{x' ∼ μ}[(∑_{S ∈ 𝒞} χ_S(x, x')) h(x')]`. -/
theorem grouped_extraction_norm (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n) {ehat : ℝ}
    (hehat : ∀ i, coarseError (rowsDeg0 G i) (Fintype.card F) n ≤ ehat) (hehat1 : ehat < 1)
    (Ex P A : Finset (U × U)) (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0) (hcls : IsClassDatum Ex (P, A))
    {k : ℕ} (w : Fin k → U × U) (hw : IsWitness Ex P A w) (Cx Cz : Finset U)
    (hcov : IsCover Ex P A w Cx Cz) (ordX ordZ : U → ℕ) (hordX : Function.Injective ordX)
    (hordZ : Function.Injective ordZ) (hX0 : ∀ a ∈ Cx, ∀ b, b ∉ Cx → ordX a < ordX b)
    (hZ0 : ∀ a ∈ Cz, ∀ b, b ∉ Cz → ordZ a < ordZ b)
    (hX1 : ∀ a, a ∉ univ \ (witV w ∪ Cx) → ∀ b ∈ univ \ (witV w ∪ Cx), ordX a < ordX b)
    (hZ1 : ∀ a, a ∉ univ \ (witW w ∪ Cz) → ∀ b ∈ univ \ (witW w ∪ Cz), ordZ a < ordZ b)
    {cker : ℝ} (hcker : 0 ≤ cker)
    (hker : Sarkozy.Influence.OpBound (injTuples F (witV w)) (injTuples F (witW w))
      (rectKer ς P (witV w) (witW w)) (cker * Real.sqrt (Fintype.card F) ^ k))
    (h : (U → F) → ℝ) :
    (graphLaw G hne).expect (fun x => ((graphLaw G hne).expect (fun x' =>
        (∑ S ∈ cls Ex P A, ∏ e ∈ S, chiPair ς e x x') * h x')) ^ 2) ≤
      (cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        Real.sqrt (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
          recordFactor G ς (Fintype.card F) n (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz
            ordX ordZ) / (1 - ehat) ^ k) ^ 2 *
        (graphLaw G hne).expect (fun x => h x ^ 2) := by
  set g : (U → F) → ℝ := fun x => (graphLaw G hne).expect (fun x' =>
    (∑ S ∈ cls Ex P A, ∏ e ∈ S, chiPair ς e x x') * h x') with hg
  have hbil := grouped_extraction hW G ς hς hanti hne hn hehat hehat1 Ex P A hEx hcls w hw Cx Cz
    hcov ordX ordZ hordX hordZ hX0 hZ0 hX1 hZ1 hcker hker g h
  have hgg : (graphLaw G hne).expect (fun x => g x * g x) =
      (graphLaw G hne).expect (fun x => g x ^ 2) :=
    (graphLaw G hne).expect_congr fun x => (sq (g x)).symm
  rw [hgg] at hbil
  refine le_sq_mul_of_le_sqrt ((graphLaw G hne).second_moment_nonneg g)
    ((graphLaw G hne).second_moment_nonneg h) ?_
  exact (le_abs_self _).trans hbil

end Sarkozy.ExtractionK
