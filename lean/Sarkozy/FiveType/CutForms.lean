module

public import Sarkozy.FiveType.Datum

/-!
# The cut forms of the components (`lem:five-type`(a), cut forms)

Source: `paper/sections/17_completion_repair.tex`, `lem:five-type`(a) and its proof, which
reads the cut forms off `tab:corner` (`lem:record:fold-identification`(f)).

At the chamber cut `ϑ₀` (`chamberCut 0`: plus half `H₀ = {0, 1, 2}`, reflection `u ↦ 5 - u`)
a half-function is a real function `G` of the half-configurations `x : H₀ → 𝔛`; `hp x₀ x₁ x₂`
is the half-configuration `(x₀, x₁, x₂)`. The paper's
`U_b(y) = g(b, y, y)`, `V_b(y) = g(y, y, b)`, `z_b = g(b, b, b)` are `Uf G b`, `Vf G b`, `zf G b`,
and `u_b = E_{ν^b} U_b`, `v_b = E_{ν^b} V_b`. The diagonal cut form of a measure `κ` at `G` is
`(chamberCut 0).form κ G G`.

Proved (each identity separately; `cut_forms` collects them):
* `form_F0`: `Q_{Π_{F_0}}(g) = E_{π_F} g(ω)²`;
* `form_F1`, `form_F2`: `Q_{Π_{F_1}}(g) = Q_{Π_{F_2}}(g) = E_b ⟨U_b, T_F^b V_b⟩`;
* `form_E0`, `form_E1`: `Q_{Π_{E_0}}(g) = E_b ⟨U_b, T_E^b U_b⟩`,
  `Q_{Π_{E_1}}(g) = E_b ⟨V_b, T_E^b V_b⟩`
  (the first by exchangeability of `π_E`, as in the paper);
* `form_G00`, `form_G11`: `Q_{Π_{G_e}}(g) = E_b ‖U_b‖²`, `Q_{Π_{G_o}}(g) = E_b ‖V_b‖²`;
* `form_G01`, `form_G02`, `form_G10`, `form_G12`: `E_b[z_b u_b]` and `E_b[z_b v_b]` (by the
  symmetry of `Γ`);
* `form_C`: `Q_{Π_{C_k}}(g) = E_b z_b²`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.FiveType

open Sarkozy.Labellings

/-- A sum over the five types. -/
theorem sum_Ty {M : Type*} [AddCommMonoid M] (f : Ty → M) :
    ∑ t, f t = f .L + f .D + f .S + f .R + f .C := by
  change ∑ t ∈ ({.L, .D, .S, .R, .C} : Finset Ty), f t = _
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [add_assoc]

/-! ## Half-configurations at `ϑ₀` -/

/-- The plus half `H₀ = {0, 1, 2}` of `ϑ₀`. -/
abbrev Half0 := (chamberCut 0).Half

section Halves

variable {𝔛 : Type*}

/-- The half-configuration `(x₀, x₁, x₂)` on `H₀`. -/
def hp (x0 x1 x2 : 𝔛) : Half0 → 𝔛 :=
  fun v => if v.1 = 0 then x0 else if v.1 = 1 then x1 else x2

theorem half_mem (v : Half0) : v.1 = 0 ∨ v.1 = 1 ∨ v.1 = 2 := by
  obtain ⟨v, hv⟩ := v
  revert v
  decide

/-- The plus half of a configuration `Ψ` at `ϑ₀` is `(Ψ₀, Ψ₁, Ψ₂)`. -/
theorem plus_half (Ψ : ZMod 6 → 𝔛) : (fun v : Half0 => Ψ v.1) = hp (Ψ 0) (Ψ 1) (Ψ 2) := by
  have h10 : (1 : ZMod 6) ≠ 0 := by decide
  have h20 : (2 : ZMod 6) ≠ 0 := by decide
  have h21 : (2 : ZMod 6) ≠ 1 := by decide
  funext v
  rcases half_mem v with h | h | h <;> simp only [hp, h, h10, h20, h21, ↓reduceIte]

/-- The reflected half of a configuration `Ψ` at `ϑ₀` is `(Ψ₅, Ψ₄, Ψ₃)`. -/
theorem refl_half (Ψ : ZMod 6 → 𝔛) :
    (fun v : Half0 => Ψ ((chamberCut 0).flip v.1)) = hp (Ψ 5) (Ψ 4) (Ψ 3) := by
  have h10 : (1 : ZMod 6) ≠ 0 := by decide
  have h20 : (2 : ZMod 6) ≠ 0 := by decide
  have h21 : (2 : ZMod 6) ≠ 1 := by decide
  have f0 : (chamberCut 0).flip 0 = 5 := by decide
  have f1 : (chamberCut 0).flip 1 = 4 := by decide
  have f2 : (chamberCut 0).flip 2 = 3 := by decide
  funext v
  rcases half_mem v with h | h | h <;>
    simp only [hp, h, f0, f1, f2, h10, h20, h21, ↓reduceIte]

/-- `U_b(y) = g(b, y, y)`. -/
def Uf (G : (Half0 → 𝔛) → ℝ) (b y : 𝔛) : ℝ := G (hp b y y)

/-- `V_b(y) = g(y, y, b)`. -/
def Vf (G : (Half0 → 𝔛) → ℝ) (b y : 𝔛) : ℝ := G (hp y y b)

/-- `z_b = g(b, b, b)`. -/
def zf (G : (Half0 → 𝔛) → ℝ) (b : 𝔛) : ℝ := G (hp b b b)

end Halves

/-! ## Linear algebra of cut forms -/

section FormAlgebra

variable {V X : Type*} [Fintype V] [DecidableEq V] (c : ReflectionCut V)

theorem form_add (L M : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (F G : (c.Half → X) → ℝ) :
    c.form (L + M) F G = c.form L F G + c.form M F G := rfl

theorem form_sub (L M : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (F G : (c.Half → X) → ℝ) :
    c.form (L - M) F G = c.form L F G - c.form M F G := rfl

theorem form_smul (a : ℝ) (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (F G : (c.Half → X) → ℝ) :
    c.form (a • L) F G = a * c.form L F G := rfl

theorem form_sum {I : Type*} (s : Finset I) (L : I → ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (F G : (c.Half → X) → ℝ) : c.form (∑ i ∈ s, L i) F G = ∑ i ∈ s, c.form (L i) F G := by
  simp only [ReflectionCut.form, LinearMap.sum_apply]

end FormAlgebra

/-! ## Expectations of the laws of the datum -/

section Sums

variable {𝔛 : Type*} [Fintype 𝔛]

/-- `ω ↦ (ω₁, ω₀, ω₂)`. -/
def e3 : (Fin 3 → 𝔛) ≃ 𝔛 × 𝔛 × 𝔛 where
  toFun ω := (ω 1, ω 0, ω 2)
  invFun t := ![t.2.1, t.1, t.2.2]
  left_inv ω := by funext i; fin_cases i <;> rfl
  right_inv _ := rfl

/-- `ω ↦ (ω₁, ω₀)`. -/
def e2 : (Fin 2 → 𝔛) ≃ 𝔛 × 𝔛 where
  toFun ω := (ω 1, ω 0)
  invFun t := ![t.2, t.1]
  left_inv ω := by funext i; fin_cases i <;> rfl
  right_inv _ := rfl

theorem sum_triple (g : (Fin 3 → 𝔛) → ℝ) : ∑ ω, g ω = ∑ b, ∑ x, ∑ y, g ![x, b, y] := by
  rw [(Fintype.sum_equiv e3.symm (fun t => g (e3.symm t)) g (fun _ => rfl)).symm,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Fintype.sum_prod_type]
  rfl

theorem sum_pair (g : (Fin 2 → 𝔛) → ℝ) : ∑ ω, g ω = ∑ b, ∑ x, g ![x, b] := by
  rw [(Fintype.sum_equiv e2.symm (fun t => g (e2.symm t)) g (fun _ => rfl)).symm,
    Fintype.sum_prod_type]
  rfl

/-- **An exchangeable law is invariant under relabelling the objects**:
if `μ(ω ∘ σ) = μ(ω)` for all `ω`, then `E_μ f = E_μ f(· ∘ σ)`. -/
theorem expect_perm {O : Type*} [Fintype O] [DecidableEq O] (μ : FiniteLaw (O → 𝔛))
    (σ : Equiv.Perm O) (hσ : ∀ ω, μ.weight (ω ∘ σ) = μ.weight ω) (f : (O → 𝔛) → ℝ) :
    μ.expect f = μ.expect (fun ω => f (ω ∘ σ)) := by
  unfold FiniteLaw.expect
  rw [← Fintype.sum_equiv (Equiv.arrowCongr σ.symm (Equiv.refl 𝔛))
    (fun ω => μ.weight (ω ∘ σ) * f (ω ∘ σ)) (fun ω => μ.weight ω * f ω) (fun _ => rfl)]
  exact Finset.sum_congr rfl fun ω _ => by rw [hσ]

end Sums

/-- The integral against `Π_φ(λ)`. -/
theorem lawL_pattern {O 𝔛 : Type*} [Fintype O] [DecidableEq O] [Fintype 𝔛] [DecidableEq 𝔛]
    (φ : ZMod 6 → O) (lam : FiniteLaw (O → 𝔛)) (f : (ZMod 6 → 𝔛) → ℝ) :
    lawL (patternLaw φ lam) f = lam.expect (fun ω => f (fun u => ω (φ u))) := by
  rw [lawL_apply]
  unfold patternLaw
  rw [FiniteLaw.expect_map]
  rfl

/-- **The cut form of a law at `ϑ₀`**: `∫ g(Ψ₀, Ψ₁, Ψ₂) g'(Ψ₅, Ψ₄, Ψ₃) dκ(Ψ)`. -/
theorem form_lawL {𝔛 : Type*} [Fintype 𝔛] (μ : FiniteLaw (ZMod 6 → 𝔛))
    (F G : (Half0 → 𝔛) → ℝ) :
    (chamberCut 0).form (lawL μ) F G =
      μ.expect (fun Ψ => F (hp (Ψ 0) (Ψ 1) (Ψ 2)) * G (hp (Ψ 5) (Ψ 4) (Ψ 3))) := by
  change μ.expect (fun Ψ => F (fun v => Ψ v.1) * G (fun v => Ψ ((chamberCut 0).flip v.1))) = _
  apply FiniteLaw.expect_congr
  intro Ψ
  rw [plus_half, refl_half]

/-- **The cut form of `Π_φ(λ)` at `ϑ₀`** (`tab:corner`): the halves of `ω ∘ φ` are
`(ω_{φ(0)}, ω_{φ(1)}, ω_{φ(2)})` and `(ω_{φ(5)}, ω_{φ(4)}, ω_{φ(3)})`. -/
theorem form_pattern {O 𝔛 : Type*} [Fintype O] [DecidableEq O] [Fintype 𝔛] [DecidableEq 𝔛]
    (φ : ZMod 6 → O) (lam : FiniteLaw (O → 𝔛)) (F G : (Half0 → 𝔛) → ℝ) :
    (chamberCut 0).form (lawL (patternLaw φ lam)) F G =
      lam.expect (fun ω => F (hp (ω (φ 0)) (ω (φ 1)) (ω (φ 2))) *
        G (hp (ω (φ 5)) (ω (φ 4)) (ω (φ 3)))) := by
  rw [form_lawL]
  unfold patternLaw
  rw [FiniteLaw.expect_map]
  rfl

namespace Datum

variable {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛] (D : Datum 𝔛)

/-- Expectation under the fold law, by its factorization (iv). -/
theorem expect_piF (f : (Fin 3 → 𝔛) → ℝ) :
    D.piF.expect f = ∑ b, ∑ x, ∑ y, D.nu.weight b * (D.nub b).weight x *
      (D.nub b).weight y * D.TF b x y * f ![x, b, y] := by
  unfold FiniteLaw.expect
  rw [sum_triple]
  simp only [D.piF_weight]
  rfl

/-- Expectation under the matching law, by its factorization (iii). -/
theorem expect_piE (f : (Fin 3 → 𝔛) → ℝ) :
    D.piE.expect f = ∑ b, ∑ x, ∑ y, D.nu.weight b * (D.nub b).weight x *
      (D.nub b).weight y * D.TE b x y * f ![x, b, y] := by
  unfold FiniteLaw.expect
  rw [sum_triple]
  simp only [D.piE_weight]
  rfl

/-- Expectation under the merge law, by (ii). -/
theorem expect_Gam (f : (Fin 2 → 𝔛) → ℝ) :
    D.Gam.expect f = ∑ b, ∑ x, D.nu.weight b * (D.nub b).weight x * f ![x, b] := by
  unfold FiniteLaw.expect
  rw [sum_pair]
  simp only [D.Gam_weight]
  rfl

/-- A triple sum against a kernel is `E_b ⟨U_b, T^b V_b⟩`. -/
theorem triple_kf (T : 𝔛 → 𝔛 → 𝔛 → ℝ) (U V : 𝔛 → 𝔛 → ℝ) :
    ∑ b, ∑ x, ∑ y, D.nu.weight b * (D.nub b).weight x * (D.nub b).weight y * T b x y *
      (U b x * V b y) = D.nu.expect (fun b => kf (D.nub b) (T b) (U b) (V b)) := by
  unfold FiniteLaw.expect kf
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

/-- A pair sum is `E_b E_{ν^b}[h_b]`. -/
theorem pair_expect (h : 𝔛 → 𝔛 → ℝ) :
    ∑ b, ∑ x, D.nu.weight b * (D.nub b).weight x * h b x =
      D.nu.expect (fun b => (D.nub b).expect (h b)) := by
  unfold FiniteLaw.expect
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-! ## The cut forms -/

variable (G : (Half0 → 𝔛) → ℝ)

/-- **`Q_{Π_{F_0}}(g) = E_{π_F} g(ω)²`**: the halves of `F_0` coincide. -/
theorem form_F0 :
    (chamberCut 0).form (D.compF 0) G G = D.piF.expect (fun ω => G (hp (ω 0) (ω 1) (ω 2)) ^ 2) := by
  unfold compF
  rw [form_pattern]
  obtain ⟨h0, h1, h2, h5, h4, h3⟩ : fold 0 0 = 0 ∧ fold 0 1 = 1 ∧ fold 0 2 = 2 ∧ fold 0 5 = 0 ∧
      fold 0 4 = 1 ∧ fold 0 3 = 2 := by decide
  simp only [h0, h1, h2, h3, h4, h5, sq]

/-- **`Q_{Π_{F_1}}(g) = E_b ⟨U_b, T_F^b V_b⟩`**: the halves of `F_1` are `(ω₁, ω₀, ω₀)` and
`(ω₂, ω₂, ω₁)`. -/
theorem form_F1 :
    (chamberCut 0).form (D.compF 1) G G =
      D.nu.expect (fun b => kf (D.nub b) (D.TF b) (Uf G b) (Vf G b)) := by
  unfold compF
  rw [form_pattern, expect_piF, ← triple_kf]
  obtain ⟨h0, h1, h2, h5, h4, h3⟩ : fold 1 0 = 1 ∧ fold 1 1 = 0 ∧ fold 1 2 = 0 ∧ fold 1 5 = 2 ∧
      fold 1 4 = 2 ∧ fold 1 3 = 1 := by decide
  simp only [h0, h1, h2, h3, h4, h5]
  rfl

/-- **`Q_{Π_{F_2}}(g) = E_b ⟨U_b, T_F^b V_b⟩`**: `F_2` exchanges the two halves of `F_1`. -/
theorem form_F2 :
    (chamberCut 0).form (D.compF 2) G G =
      D.nu.expect (fun b => kf (D.nub b) (D.TF b) (Uf G b) (Vf G b)) := by
  unfold compF
  rw [form_pattern, expect_piF, ← triple_kf]
  obtain ⟨h0, h1, h2, h5, h4, h3⟩ : fold 2 0 = 2 ∧ fold 2 1 = 2 ∧ fold 2 2 = 1 ∧ fold 2 5 = 1 ∧
      fold 2 4 = 0 ∧ fold 2 3 = 0 := by decide
  simp only [h0, h1, h2, h3, h4, h5]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun x _ =>
    Finset.sum_congr rfl fun y _ => ?_
  simp only [Uf, Vf, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

/-- **`Q_{Π_{E_0}}(g) = E_b ⟨U_b, T_E^b U_b⟩`**: the object on both halves is `ω₀`, and
`(ω₁, ω₀, ω₂)` again has the law `π_E`. -/
theorem form_E0 :
    (chamberCut 0).form (D.compE 0) G G =
      D.nu.expect (fun b => kf (D.nub b) (D.TE b) (Uf G b) (Uf G b)) := by
  unfold compE
  rw [form_pattern, expect_perm D.piE (Equiv.swap 0 1) (D.piE_exch _), expect_piE,
    ← triple_kf]
  obtain ⟨h0, h1, h2, h5, h4, h3⟩ : matching 0 0 = 0 ∧ matching 0 1 = 1 ∧ matching 0 2 = 1 ∧
      matching 0 5 = 0 ∧ matching 0 4 = 2 ∧ matching 0 3 = 2 := by decide
  simp only [h0, h1, h2, h3, h4, h5]
  rfl

/-- **`Q_{Π_{E_1}}(g) = E_b ⟨V_b, T_E^b V_b⟩`**: the halves of `E_1` are `(ω₀, ω₀, ω₁)` and
`(ω₂, ω₂, ω₁)`. -/
theorem form_E1 :
    (chamberCut 0).form (D.compE 1) G G =
      D.nu.expect (fun b => kf (D.nub b) (D.TE b) (Vf G b) (Vf G b)) := by
  unfold compE
  rw [form_pattern, expect_piE, ← triple_kf]
  obtain ⟨h0, h1, h2, h5, h4, h3⟩ : matching 1 0 = 0 ∧ matching 1 1 = 0 ∧ matching 1 2 = 1 ∧
      matching 1 5 = 2 ∧ matching 1 4 = 2 ∧ matching 1 3 = 1 := by decide
  simp only [h0, h1, h2, h3, h4, h5]
  rfl

/-- **`Q_{Π_{G_e}}(g) = E_b ‖U_b‖²`**. -/
theorem form_G00 :
    (chamberCut 0).form (D.compG 0 0) G G =
      D.nu.expect (fun b => ip (D.nub b) (Uf G b) (Uf G b)) := by
  unfold compG
  rw [form_pattern, expect_Gam]
  obtain ⟨h0, h1, h2, h5, h4, h3⟩ : merge 0 0 0 = 1 ∧ merge 0 0 1 = 0 ∧ merge 0 0 2 = 0 ∧
      merge 0 0 5 = 1 ∧ merge 0 0 4 = 0 ∧ merge 0 0 3 = 0 := by decide
  simp only [h0, h1, h2, h3, h4, h5]
  exact D.pair_expect (fun b x => Uf G b x * Uf G b x)

/-- **`Q_{Π_{G_o}}(g) = E_b ‖V_b‖²`**. -/
theorem form_G11 :
    (chamberCut 0).form (D.compG 1 1) G G =
      D.nu.expect (fun b => ip (D.nub b) (Vf G b) (Vf G b)) := by
  unfold compG
  rw [form_pattern, expect_Gam]
  obtain ⟨h0, h1, h2, h5, h4, h3⟩ : merge 1 1 0 = 0 ∧ merge 1 1 1 = 0 ∧ merge 1 1 2 = 1 ∧
      merge 1 1 5 = 0 ∧ merge 1 1 4 = 0 ∧ merge 1 1 3 = 1 := by decide
  simp only [h0, h1, h2, h3, h4, h5]
  exact D.pair_expect (fun b x => Vf G b x * Vf G b x)

/-- **`Q_{Π_{G_{01}}}(g) = E_b[z_b u_b]`**, by the symmetry of `Γ`. -/
theorem form_G01 :
    (chamberCut 0).form (D.compG 0 1) G G =
      D.nu.expect (fun b => zf G b * (D.nub b).expect (Uf G b)) := by
  unfold compG
  rw [form_pattern, expect_perm D.Gam (Equiv.swap 0 1) D.Gam_symm, expect_Gam]
  obtain ⟨h0, h1, h2, h5, h4, h3⟩ : merge 0 1 0 = 0 ∧ merge 0 1 1 = 1 ∧ merge 0 1 2 = 1 ∧
      merge 0 1 5 = 0 ∧ merge 0 1 4 = 0 ∧ merge 0 1 3 = 0 := by decide
  simp only [h0, h1, h2, h3, h4, h5]
  rw [show D.nu.expect (fun b => zf G b * (D.nub b).expect (Uf G b)) =
    D.nu.expect (fun b => (D.nub b).expect (fun x => Uf G b x * zf G b)) from
    D.nu.expect_congr fun b => by rw [FiniteLaw.expect_mul_const, mul_comm]]
  exact D.pair_expect (fun b x => Uf G b x * zf G b)

/-- **`Q_{Π_{G_{02}}}(g) = E_b[z_b u_b]`**, by the symmetry of `Γ`. -/
theorem form_G02 :
    (chamberCut 0).form (D.compG 0 2) G G =
      D.nu.expect (fun b => zf G b * (D.nub b).expect (Uf G b)) := by
  unfold compG
  rw [form_pattern, expect_perm D.Gam (Equiv.swap 0 1) D.Gam_symm, expect_Gam]
  obtain ⟨h0, h1, h2, h5, h4, h3⟩ : merge 0 2 0 = 0 ∧ merge 0 2 1 = 0 ∧ merge 0 2 2 = 0 ∧
      merge 0 2 5 = 0 ∧ merge 0 2 4 = 1 ∧ merge 0 2 3 = 1 := by decide
  simp only [h0, h1, h2, h3, h4, h5]
  rw [show D.nu.expect (fun b => zf G b * (D.nub b).expect (Uf G b)) =
    D.nu.expect (fun b => (D.nub b).expect (fun x => zf G b * Uf G b x)) from
    D.nu.expect_congr fun b => by rw [FiniteLaw.expect_const_mul]]
  exact D.pair_expect (fun b x => zf G b * Uf G b x)

/-- **`Q_{Π_{G_{10}}}(g) = E_b[z_b v_b]`**, by the symmetry of `Γ`. -/
theorem form_G10 :
    (chamberCut 0).form (D.compG 1 0) G G =
      D.nu.expect (fun b => zf G b * (D.nub b).expect (Vf G b)) := by
  unfold compG
  rw [form_pattern, expect_perm D.Gam (Equiv.swap 0 1) D.Gam_symm, expect_Gam]
  obtain ⟨h0, h1, h2, h5, h4, h3⟩ : merge 1 0 0 = 1 ∧ merge 1 0 1 = 1 ∧ merge 1 0 2 = 0 ∧
      merge 1 0 5 = 0 ∧ merge 1 0 4 = 0 ∧ merge 1 0 3 = 0 := by decide
  simp only [h0, h1, h2, h3, h4, h5]
  rw [show D.nu.expect (fun b => zf G b * (D.nub b).expect (Vf G b)) =
    D.nu.expect (fun b => (D.nub b).expect (fun x => Vf G b x * zf G b)) from
    D.nu.expect_congr fun b => by rw [FiniteLaw.expect_mul_const, mul_comm]]
  exact D.pair_expect (fun b x => Vf G b x * zf G b)

/-- **`Q_{Π_{G_{12}}}(g) = E_b[z_b v_b]`**, by the symmetry of `Γ`. -/
theorem form_G12 :
    (chamberCut 0).form (D.compG 1 2) G G =
      D.nu.expect (fun b => zf G b * (D.nub b).expect (Vf G b)) := by
  unfold compG
  rw [form_pattern, expect_perm D.Gam (Equiv.swap 0 1) D.Gam_symm, expect_Gam]
  obtain ⟨h0, h1, h2, h5, h4, h3⟩ : merge 1 2 0 = 0 ∧ merge 1 2 1 = 0 ∧ merge 1 2 2 = 0 ∧
      merge 1 2 5 = 1 ∧ merge 1 2 4 = 1 ∧ merge 1 2 3 = 0 := by decide
  simp only [h0, h1, h2, h3, h4, h5]
  rw [show D.nu.expect (fun b => zf G b * (D.nub b).expect (Vf G b)) =
    D.nu.expect (fun b => (D.nub b).expect (fun x => zf G b * Vf G b x)) from
    D.nu.expect_congr fun b => by rw [FiniteLaw.expect_const_mul]]
  exact D.pair_expect (fun b x => zf G b * Vf G b x)

/-- **`Q_{Π_{C_k}}(g) = E_b z_b²`**. -/
theorem form_C :
    (chamberCut 0).form D.compC G G = D.nu.expect (fun b => zf G b ^ 2) := by
  unfold compC nu1
  rw [form_pattern, FiniteLaw.expect_map]
  apply FiniteLaw.expect_congr
  intro b
  simp only [constPat, Function.comp_apply, zf, sq]

/-- **`lem:five-type`(a), the cut forms**, collected: at `ϑ₀` and a half-function `g`,
* `Q_{Π_{F_0}}(g) = E_{π_F} g(ω)²`,
* `Q_{Π_{F_1}}(g) = Q_{Π_{F_2}}(g) = E_b ⟨U_b, T_F^b V_b⟩`,
* `Q_{Π_{E_0}}(g) = E_b ⟨U_b, T_E^b U_b⟩`, `Q_{Π_{E_1}}(g) = E_b ⟨V_b, T_E^b V_b⟩`,
* `Q_{Π_{G_e}}(g) = E_b ‖U_b‖²`, `Q_{Π_{G_o}}(g) = E_b ‖V_b‖²`,
* `Q_{Π_{G_{01}}}(g) = Q_{Π_{G_{02}}}(g) = E_b[z_b u_b]`,
  `Q_{Π_{G_{10}}}(g) = Q_{Π_{G_{12}}}(g) = E_b[z_b v_b]`,
* `Q_{Π_{C_k}}(g) = E_b z_b²`. -/
theorem cut_forms :
    (chamberCut 0).form (D.compF 0) G G = D.piF.expect (fun ω => G (hp (ω 0) (ω 1) (ω 2)) ^ 2) ∧
    (chamberCut 0).form (D.compF 1) G G =
      D.nu.expect (fun b => kf (D.nub b) (D.TF b) (Uf G b) (Vf G b)) ∧
    (chamberCut 0).form (D.compF 2) G G =
      D.nu.expect (fun b => kf (D.nub b) (D.TF b) (Uf G b) (Vf G b)) ∧
    (chamberCut 0).form (D.compE 0) G G =
      D.nu.expect (fun b => kf (D.nub b) (D.TE b) (Uf G b) (Uf G b)) ∧
    (chamberCut 0).form (D.compE 1) G G =
      D.nu.expect (fun b => kf (D.nub b) (D.TE b) (Vf G b) (Vf G b)) ∧
    (chamberCut 0).form (D.compG 0 0) G G =
      D.nu.expect (fun b => ip (D.nub b) (Uf G b) (Uf G b)) ∧
    (chamberCut 0).form (D.compG 1 1) G G =
      D.nu.expect (fun b => ip (D.nub b) (Vf G b) (Vf G b)) ∧
    (chamberCut 0).form (D.compG 0 1) G G =
      D.nu.expect (fun b => zf G b * (D.nub b).expect (Uf G b)) ∧
    (chamberCut 0).form (D.compG 0 2) G G =
      D.nu.expect (fun b => zf G b * (D.nub b).expect (Uf G b)) ∧
    (chamberCut 0).form (D.compG 1 0) G G =
      D.nu.expect (fun b => zf G b * (D.nub b).expect (Vf G b)) ∧
    (chamberCut 0).form (D.compG 1 2) G G =
      D.nu.expect (fun b => zf G b * (D.nub b).expect (Vf G b)) ∧
    (chamberCut 0).form D.compC G G = D.nu.expect (fun b => zf G b ^ 2) :=
  ⟨D.form_F0 G, D.form_F1 G, D.form_F2 G, D.form_E0 G, D.form_E1 G, D.form_G00 G, D.form_G11 G,
    D.form_G01 G, D.form_G02 G, D.form_G10 G, D.form_G12 G, D.form_C G⟩

end Datum

end Sarkozy.FiveType
