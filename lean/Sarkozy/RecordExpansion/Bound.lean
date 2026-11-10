module

public import Sarkozy.RecordExpansion.Monomials
public import Sarkozy.Reflection.BracketMatrix

/-!
# The reserved cost `|Y_ν - Y_λ| ≤ B (e^S cosh A - 1) Y`

This file assembles `lem:record:record-expansion` (i) and the class-free case
of (ii) of the paper (Section 10), up to the analytic energy estimate (E1) of
`lem:energy-toolkit`, which is taken as an explicit hypothesis.

## Results

* `abs_energy_sub_le_of_terms`: if every selection satisfies
  `|I_ω| ≤ (B + z) π_ω Y + r_ω`, then
  `|Y_ν - Y_λ| ≤ (B + z)(e^S cosh A - 1) Y + ∑_ω r_ω`. The parameter `z` is
  the uniform relative error of a robust bound (`def:robust`) and the `r_ω`
  are additive remainders; `abs_energy_sub_le` is the case `r = 0`, and
  `abs_energy_sub_le_poly` keeps the exact polynomial
  `½[∏(1 + s_b + a_b) + ∏(1 + s_b - a_b)] - 1` in place of `e^S cosh A - 1`.
* `abs_diagonal_le_of_bracket`: a bracket `(M K; K* M') ⪰_c 0` gives
  `|Y_K| ≤ Y_M^{1/2} Y_{M'}^{1/2}` (`lem:record:block-gram` (a) at the diagonal
  half-function, `eq:cc:bilinear`).
* `abs_term_le_envelope`: the bracket part of the proof of
  `lem:record:record-expansion` (i). With the brackets of (CP3),
  `(Ñ_b λ_b; λ_b Ñ_b) ⪰_c 0`, and of (CP4)(b),
  `(π̃^ε_{b,t} D^ε_{b,t}  ζ^ε_{b,t}; ζ^{ε*}_{b,t}  π̃^ε_{b,t} D^ε_{b,t}) ⪰_c 0`,
  every choice satisfies
  `|I_ω| ≤ (∏_{b ∈ X} π̃^{ε_b}_{b,t_b}) · Y_{(⊗_{b ∈ X} D^{ε_b}_{b,t_b}) ⊗ Ñ_{-X}}`
  (tensorization of brackets, `lem:record:block-gram` (b), and (P5)).
* `abs_energy_sub_le_of_envelopes`: the assembled reserved-cost bound. If in
  addition the envelope energies satisfy the instance of (E1)
  `Y_{(⊗_{b ∈ X} D^{ε_b}_{b,t_b}) ⊗ Ñ_{-X}} ≤ (B + z) C_X Y`,
  `C_X = ∏_{b ∈ X} q_b`, for every selection, then with the prices
  `π^ε_{b,t} = π̃^ε_{b,t} q_b` of (CP4)(b),
  `|Y_ν - Y_λ| ≤ (B + z)(e^S cosh A - 1) Y`.

In the paper `q_b = q_B^{2a}` is the selection factor and the envelopes
`D^ε_{b,t}` are probability laws, so `‖⊗_{b ∈ X} D^{ε_b}_{b,t_b}‖ = 1` in (E1).
Here `q_b ≥ 0`, `π̃ ≥ 0` and `B + z ≥ 0`, `Y ≥ 0` are the only numerical
assumptions; no normalization of the `D^ε_{b,t}` is needed, because (E1) enters
only through the stated hypothesis. The energy factor of (CP3) is written `B`
in the paper; in Lean it is `Bf`, since `b` names atoms.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.RecordExpansion

open Choice

/-! ### From per-selection bounds to the reserved cost -/

section Sum

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]
  {T : J → Type*} [∀ b, Fintype (T b)] [∀ b, DecidableEq (T b)]

/-- **Reserved cost with additive remainders.** Under the hypotheses of
`energy_sub_eq_sum_selections`, nonnegative prices, `Y ≥ 0` and `B + z ≥ 0`: if
`|I_ω| ≤ (B + z) π_ω Y + r_ω` for every selection, then
`|Y_ν - Y_λ| ≤ (B + z)(e^S cosh A - 1) Y + ∑_ω r_ω`. -/
theorem abs_energy_sub_le_of_terms (c : ReflectionCut V)
    {ν lam : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ}
    {ζ : ∀ b, T b → ChangeType → ((V → X b) → ℝ) →ₗ[ℝ] ℝ}
    (hν : ∀ b, ν b = lam b + ∑ t, (ζ b t .sym + ζ b t .skew))
    (hlam : ∀ b, IsSymmetricAt c (lam b)) (hs : ∀ b t, IsSymmetricAt c (ζ b t .sym))
    (ha : ∀ b t, IsSkewAt c (ζ b t .skew)) (F : (∀ b, X b) → ℝ)
    {π : ∀ b, T b → ChangeType → ℝ} (hπ : ∀ b t e, 0 ≤ π b t e)
    {Bf z Y : ℝ} (hY : 0 ≤ Y) (hBz : 0 ≤ Bf + z) (r : Choice T → ℝ)
    (hterm : ∀ ω : Choice T, IsSelection ω →
      |term lam ζ F ω| ≤ (Bf + z) * monomial π ω * Y + r ω) :
    |diagonalIntegral (tensorLaw ν) F - diagonalIntegral (tensorLaw lam) F| ≤
      (Bf + z) * (Real.exp (∑ b, symTotal π b) * Real.cosh (∑ b, skewTotal π b) - 1) * Y +
        ∑ ω ∈ univ.filter (fun ω : Choice T => IsSelection ω), r ω := by
  rw [energy_sub_eq_sum_selections c hν hlam hs ha F]
  set sel := univ.filter (fun ω : Choice T => IsSelection ω)
  have hmono := sum_monomial_selections_le (T := T) hπ
  calc |∑ ω ∈ sel, term lam ζ F ω| ≤ ∑ ω ∈ sel, |term lam ζ F ω| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ω ∈ sel, ((Bf + z) * monomial π ω * Y + r ω) := by
        apply Finset.sum_le_sum
        intro ω hω
        exact hterm ω (mem_filter.mp hω).2
    _ = (Bf + z) * (∑ ω ∈ sel, monomial π ω) * Y + ∑ ω ∈ sel, r ω := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    _ ≤ (Bf + z) * (Real.exp (∑ b, symTotal π b) * Real.cosh (∑ b, skewTotal π b) - 1) * Y +
          ∑ ω ∈ sel, r ω := by
        have h1 := mul_le_mul_of_nonneg_left hmono hBz
        have h2 := mul_le_mul_of_nonneg_right h1 hY
        linarith

/-- **Reserved cost** (`lem:record:record-expansion` (ii) without classes, from
the per-selection bounds of (i)): if `|I_ω| ≤ (B + z) π_ω Y` for every
selection, then `|Y_ν - Y_λ| ≤ (B + z)(e^S cosh A - 1) Y`. -/
theorem abs_energy_sub_le (c : ReflectionCut V)
    {ν lam : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ}
    {ζ : ∀ b, T b → ChangeType → ((V → X b) → ℝ) →ₗ[ℝ] ℝ}
    (hν : ∀ b, ν b = lam b + ∑ t, (ζ b t .sym + ζ b t .skew))
    (hlam : ∀ b, IsSymmetricAt c (lam b)) (hs : ∀ b t, IsSymmetricAt c (ζ b t .sym))
    (ha : ∀ b t, IsSkewAt c (ζ b t .skew)) (F : (∀ b, X b) → ℝ)
    {π : ∀ b, T b → ChangeType → ℝ} (hπ : ∀ b t e, 0 ≤ π b t e)
    {Bf z Y : ℝ} (hY : 0 ≤ Y) (hBz : 0 ≤ Bf + z)
    (hterm : ∀ ω : Choice T, IsSelection ω → |term lam ζ F ω| ≤ (Bf + z) * monomial π ω * Y) :
    |diagonalIntegral (tensorLaw ν) F - diagonalIntegral (tensorLaw lam) F| ≤
      (Bf + z) * (Real.exp (∑ b, symTotal π b) * Real.cosh (∑ b, skewTotal π b) - 1) * Y := by
  have h := abs_energy_sub_le_of_terms c hν hlam hs ha F hπ hY hBz (fun _ => 0)
    (fun ω hω => by rw [add_zero]; exact hterm ω hω)
  rwa [Finset.sum_const_zero, add_zero] at h

/-- The reserved cost with the exact polynomial of the selections,
`½[∏_b (1 + s_b + a_b) + ∏_b (1 + s_b - a_b)] - 1`, in place of `e^S cosh A - 1`. -/
theorem abs_energy_sub_le_poly (c : ReflectionCut V)
    {ν lam : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ}
    {ζ : ∀ b, T b → ChangeType → ((V → X b) → ℝ) →ₗ[ℝ] ℝ}
    (hν : ∀ b, ν b = lam b + ∑ t, (ζ b t .sym + ζ b t .skew))
    (hlam : ∀ b, IsSymmetricAt c (lam b)) (hs : ∀ b t, IsSymmetricAt c (ζ b t .sym))
    (ha : ∀ b t, IsSkewAt c (ζ b t .skew)) (F : (∀ b, X b) → ℝ)
    {π : ∀ b, T b → ChangeType → ℝ} {Bf z Y : ℝ}
    (hterm : ∀ ω : Choice T, IsSelection ω → |term lam ζ F ω| ≤ (Bf + z) * monomial π ω * Y) :
    |diagonalIntegral (tensorLaw ν) F - diagonalIntegral (tensorLaw lam) F| ≤
      (Bf + z) * (((∏ b, (1 + symTotal π b + skewTotal π b)) +
        ∏ b, (1 + symTotal π b - skewTotal π b)) / 2 - 1) * Y := by
  rw [energy_sub_eq_sum_selections c hν hlam hs ha F, ← sum_monomial_selections]
  set sel := univ.filter (fun ω : Choice T => IsSelection ω)
  calc |∑ ω ∈ sel, term lam ζ F ω| ≤ ∑ ω ∈ sel, |term lam ζ F ω| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ω ∈ sel, (Bf + z) * monomial π ω * Y := by
        apply Finset.sum_le_sum
        intro ω hω
        exact hterm ω (mem_filter.mp hω).2
    _ = (Bf + z) * (∑ ω ∈ sel, monomial π ω) * Y := by
        rw [Finset.mul_sum, Finset.sum_mul]

end Sum

/-! ### Brackets at the diagonal -/

section Brackets

variable {W Y : Type*} [Fintype W] [DecidableEq W]

theorem diagonalIntegral_eq_form (c : ReflectionCut W) (L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ)
    (f : Y → ℝ) :
    diagonalIntegral L f = c.form L (c.halfProduct fun _ => f) (c.halfProduct fun _ => f) :=
  c.multilinear_eq_form L (fun _ => f)

/-- `Y_κ = Q_κ(X̄, X̄)` with the half-function `X̄(x) = ∏_{v ∈ V_+} f(x_v)` carrying `f`
at every slot of the plus half (`eq:cc:bilinear`), at any cut. -/
theorem diagonalIntegral_eq_form_prod (c : ReflectionCut W) (L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ)
    (f : Y → ℝ) :
    diagonalIntegral L f = c.form L (fun x => ∏ v, f (x v)) (fun x => ∏ v, f (x v)) :=
  c.multilinear_eq_form L (fun _ => f)

/-- **Brackets at the diagonal** (`lem:record:block-gram` (a), evaluated at the
half-function carrying `f` at every slot): `|Y_K| ≤ Y_M^{1/2} Y_{M'}^{1/2}`. -/
theorem abs_diagonal_le_of_bracket {c : ReflectionCut W} {L K R : ((W → Y) → ℝ) →ₗ[ℝ] ℝ}
    (h : c.Bracket L K R) (f : Y → ℝ) :
    |diagonalIntegral K f| ≤
      Real.sqrt (diagonalIntegral L f) * Real.sqrt (diagonalIntegral R f) := by
  rw [diagonalIntegral_eq_form c K, diagonalIntegral_eq_form c L, diagonalIntegral_eq_form c R]
  exact h.abs_form_le _ _

/-- For a bracket with equal diagonal blocks, `|Y_K| ≤ Y_M`. -/
theorem abs_diagonal_le_self_of_bracket {c : ReflectionCut W} {L K : ((W → Y) → ℝ) →ₗ[ℝ] ℝ}
    (h : c.Bracket L K L) (f : Y → ℝ) : |diagonalIntegral K f| ≤ diagonalIntegral L f := by
  have h1 := abs_diagonal_le_of_bracket h f
  rwa [Real.mul_self_sqrt (h.left_positive.diagonal_nonneg f)] at h1

/-- A bracket can be scaled: `(aM aK; aK* aM') ⪰ 0` for `a ≥ 0`. -/
theorem bracket_smul {c : ReflectionCut W} {L K R : ((W → Y) → ℝ) →ₗ[ℝ] ℝ}
    (h : c.Bracket L K R) {a : ℝ} (ha : 0 ≤ a) : c.Bracket (a • L) (a • K) (a • R) := by
  refine ⟨h.left_positive.smul ha, h.right_positive.smul ha, ?_⟩
  intro F G
  have h1 := h.nonneg F G
  have he : c.form (a • L) F F + 2 * c.form (a • K) F G + c.form (a • R) G G =
      a * (c.form L F F + 2 * c.form K F G + c.form R G G) := by
    change a * c.form L F F + 2 * (a * c.form K F G) + a * c.form R G G = _
    ring
  rw [he]
  exact mul_nonneg ha h1

end Brackets

/-! ### The bracket bound for a selection -/

section Envelope

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]
  {T : J → Type*}

/-- The envelope law `(⊗_{b ∈ X} D^{ε_b}_{b,t_b}) ⊗ Ñ_{-X}` of a choice: the norm
envelopes `D^ε_{b,t}` of (CP4)(b) on the selected atoms and the bracket `Ñ_b` of
(CP3) elsewhere. -/
noncomputable def envelopeLaw (N : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ)
    (D : ∀ b, T b → ChangeType → ((V → X b) → ℝ) →ₗ[ℝ] ℝ) (ω : Choice T) :
    ((V → ∀ b, X b) → ℝ) →ₗ[ℝ] ℝ :=
  tensorLaw fun b => entryFactor (N b) (D b) (ω b)

theorem entryFactor_scaled {α Ω : Type*} (Nb : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (Db : α → ChangeType → (Ω → ℝ) →ₗ[ℝ] ℝ) (πb : α → ChangeType → ℝ)
    (o : Option (α × ChangeType)) :
    entryFactor Nb (fun t e => πb t e • Db t e) o = entryPrice πb o • entryFactor Nb Db o := by
  rcases o with _ | ⟨t, e⟩
  · exact (one_smul_functional Nb).symm
  · rfl

/-- **The bracket bound for a selection** (proof of `lem:record:record-expansion`
(i), via `lem:record:block-gram` (b) and (P5) of `lem:energy-toolkit`): with the
brackets `(Ñ_b λ_b; λ_b Ñ_b) ⪰_c 0` of (CP3) at every atom and
`(π̃ D  ζ; ζ*  π̃ D) ⪰_c 0` of (CP4)(b) for every record and type,
`|I_ω| ≤ (∏_{b ∈ X} π̃^{ε_b}_{b,t_b}) · Y_{(⊗_{b ∈ X} D^{ε_b}_{b,t_b}) ⊗ Ñ_{-X}}`
for every choice `ω`, at the common input `F`. -/
theorem abs_term_le_envelope {c : ReflectionCut V} {lam N : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ}
    {ζ D : ∀ b, T b → ChangeType → ((V → X b) → ℝ) →ₗ[ℝ] ℝ}
    {πt : ∀ b, T b → ChangeType → ℝ}
    (hN : ∀ b, c.Bracket (N b) (lam b) (N b))
    (hζ : ∀ b t e, c.Bracket (πt b t e • D b t e) (ζ b t e) (πt b t e • D b t e))
    (F : (∀ b, X b) → ℝ) (ω : Choice T) :
    |term lam ζ F ω| ≤ monomial πt ω * diagonalIntegral (envelopeLaw N D ω) F := by
  have hb : ∀ b, c.Bracket (entryFactor (N b) (fun t e => πt b t e • D b t e) (ω b))
      (entryFactor (lam b) (ζ b) (ω b))
      (entryFactor (N b) (fun t e => πt b t e • D b t e) (ω b)) := by
    intro b
    rcases hωb : ω b with _ | ⟨t, e⟩
    · exact hN b
    · exact hζ b t e
  have htensor := ReflectionCut.Bracket.tensor hb
  have h1 := abs_diagonal_le_self_of_bracket htensor F
  have he : tensorLaw (fun b => entryFactor (N b) (fun t e => πt b t e • D b t e) (ω b)) =
      monomial πt ω • envelopeLaw N D ω := by
    simp_rw [entryFactor_scaled]
    exact tensorLaw_smul _ _
  rw [he] at h1
  exact h1

end Envelope

/-! ### The assembled reserved cost -/

section Assembly

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]
  {T : J → Type*} [∀ b, Fintype (T b)] [∀ b, DecidableEq (T b)]

omit [Fintype J] [DecidableEq J] [∀ b, Fintype (T b)] [∀ b, DecidableEq (T b)] in
theorem entryPrice_mul {α : Type*} (πb : α → ChangeType → ℝ) (q : ℝ)
    (o : Option (α × ChangeType)) :
    entryPrice (fun t e => πb t e * q) o = entryPrice πb o * (if o.isSome then q else 1) := by
  rcases o with _ | ⟨t, e⟩
  · simp [entryPrice]
  · simp [entryPrice]

omit [DecidableEq J] [∀ b, Fintype (T b)] [∀ b, DecidableEq (T b)] in
/-- `π_ω = (∏_{b ∈ X} π̃^{ε_b}_{b,t_b}) C_X` for the prices `π^ε_{b,t} = π̃^ε_{b,t} q_b`. -/
theorem monomial_mul_selectionFactor (πt : ∀ b, T b → ChangeType → ℝ) (q : J → ℝ)
    (ω : Choice T) :
    monomial (fun b t e => πt b t e * q b) ω = monomial πt ω * ∏ b ∈ support ω, q b := by
  unfold monomial support
  rw [Finset.prod_filter]
  simp only [entryPrice_mul, Finset.prod_mul_distrib]

/-- **Reserved cost, assembled** (`lem:record:record-expansion` (i) and (ii)
without classes, with (E1) as hypothesis). Assume at the cut `c`:

* (CP4)(b): `ν_b = λ_b + ∑_t (ζ^s_{b,t} + ζ^a_{b,t})`, with `ζ^s_{b,t}` symmetric,
  `ζ^a_{b,t}` skew, and brackets `(π̃^ε_{b,t} D^ε_{b,t}  ζ^ε_{b,t}; ζ^{ε*}_{b,t}
  π̃^ε_{b,t} D^ε_{b,t}) ⪰_c 0` with `π̃^ε_{b,t} ≥ 0`;
* (CP3): `λ_b` symmetric and `(Ñ_b λ_b; λ_b Ñ_b) ⪰_c 0` at every atom;
* (E1) for the envelopes of the selections: for every selection `ω` with
  support `X`, `Y_{(⊗_{b ∈ X} D^{ε_b}_{b,t_b}) ⊗ Ñ_{-X}} ≤ (B + z) C_X Y` with
  `C_X = ∏_{b ∈ X} q_b`, `q_b ≥ 0`, `B + z ≥ 0`, `Y ≥ 0`.

Then, with the prices `π^ε_{b,t} = π̃^ε_{b,t} q_b` and their totals `S`, `A`,
`|Y_ν - Y_λ| ≤ (B + z)(e^S cosh A - 1) Y`. -/
theorem abs_energy_sub_le_of_envelopes (c : ReflectionCut V)
    {ν lam N : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ}
    {ζ D : ∀ b, T b → ChangeType → ((V → X b) → ℝ) →ₗ[ℝ] ℝ}
    (hν : ∀ b, ν b = lam b + ∑ t, (ζ b t .sym + ζ b t .skew))
    (hlam : ∀ b, IsSymmetricAt c (lam b)) (hs : ∀ b t, IsSymmetricAt c (ζ b t .sym))
    (ha : ∀ b t, IsSkewAt c (ζ b t .skew))
    {πt : ∀ b, T b → ChangeType → ℝ} (hπt : ∀ b t e, 0 ≤ πt b t e)
    (hN : ∀ b, c.Bracket (N b) (lam b) (N b))
    (hζ : ∀ b t e, c.Bracket (πt b t e • D b t e) (ζ b t e) (πt b t e • D b t e))
    {q : J → ℝ} (hq : ∀ b, 0 ≤ q b) (F : (∀ b, X b) → ℝ)
    {Bf z Y : ℝ} (hY : 0 ≤ Y) (hBz : 0 ≤ Bf + z)
    (hE1 : ∀ ω : Choice T, IsSelection ω →
      diagonalIntegral (envelopeLaw N D ω) F ≤ (Bf + z) * (∏ b ∈ support ω, q b) * Y) :
    |diagonalIntegral (tensorLaw ν) F - diagonalIntegral (tensorLaw lam) F| ≤
      (Bf + z) * (Real.exp (∑ b, symTotal (fun b t e => πt b t e * q b) b) *
        Real.cosh (∑ b, skewTotal (fun b t e => πt b t e * q b) b) - 1) * Y := by
  apply abs_energy_sub_le c hν hlam hs ha F
    (fun b t e => mul_nonneg (hπt b t e) (hq b)) hY hBz
  intro ω hω
  rw [monomial_mul_selectionFactor]
  have h1 := abs_term_le_envelope hN hζ F ω
  have hm : 0 ≤ monomial πt ω := monomial_nonneg hπt ω
  have h2 := mul_le_mul_of_nonneg_left (hE1 ω hω) hm
  calc |term lam ζ F ω| ≤ monomial πt ω * diagonalIntegral (envelopeLaw N D ω) F := h1
    _ ≤ monomial πt ω * ((Bf + z) * (∏ b ∈ support ω, q b) * Y) := h2
    _ = (Bf + z) * (monomial πt ω * ∏ b ∈ support ω, q b) * Y := by ring

end Assembly

end Sarkozy.RecordExpansion
