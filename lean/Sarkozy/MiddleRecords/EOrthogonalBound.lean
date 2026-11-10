module

public import Sarkozy.MiddleRecords.EOrthogonal

/-!
# The bound `‖𝖢𝖣 H‖ ≤ e_E` (`lem:record:e-orthogonal`(b), last claim)

`paper/sections/21_middle_records.tex`, `lem:record:e-orthogonal`(b): if `H` is the orthogonal
projection onto `V(H₀³)`, `V = (V₀, V₁, V₂)` the coordinate embeddings into `L²(ν_E)`, then
`‖𝖢𝖣 H‖ ≤ e_E = qr ((1 - q)(1 - 3q))^{-1/2} (2 + 4q²/(1 - 2q)²)^{1/2}`.

Since `‖𝖢𝖣 H f‖ = ‖𝖢𝖣 (H f)‖` and `‖H f‖ ≤ ‖f‖`, this is the bound on the range of `V`:
`‖𝖢𝖣 (V c)‖_{ν_E} ≤ e_E ‖V c‖_{ν_E}` for every triple `c` of mean-zero functions
(`CD_V_bound`, in squared form, with `e_E² = q³(2 + 4q²/(1 - 2q)²)/((1 - q)(1 - 3q))`).

The proof is the paper's: `𝖢𝖣 (V c) = 𝒯_E(-u c₀ - u c₁ + 2c₂/((p - 1)(p - 2)))` on halves
(`CD_V_eq`, from `CD_V0`, `CD_V1`, `CD_V2`), `‖𝒯_E g‖² ≤ q ‖g‖²` (`TE_norm_le`), Cauchy–Schwarz,
and the Gram of `V`, `‖V c‖² ≥ (1 - 2u) ∑ ‖cᵢ‖²` (`norm_V_sq_ge`, from
`⟨Vᵢ cᵢ, Vⱼ cⱼ⟩ = -u ⟨cᵢ, cⱼ⟩` for `i ≠ j`).
-/

@[expose] public section

namespace Sarkozy.MiddleRecords

open Finset Sarkozy.TraceMixing

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `χ` as an integer-valued character. -/
local notation "χ" => quadraticChar F

/-- `p = |F|` as a real number. -/
local notation "qF" => (Fintype.card F : ℝ)

/-! ## Symmetries and congruence of `E_{ν_E}` -/

omit [Field F] in
theorem nuE_congr {G G' : F → F → F → ℝ}
    (h : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → G a b c = G' a b c) : nuE G = nuE G' := by
  unfold nuE
  congr 1
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ => ?_
  by_cases hc : a ≠ b ∧ a ≠ c ∧ b ≠ c
  · rw [ite_eq_left hc, ite_eq_left hc, h a b c hc.1 hc.2.1 hc.2.2]
  · rw [ite_eq_right hc, ite_eq_right hc]

omit [Field F] in
theorem nuE_swap23 (G : F → F → F → ℝ) : nuE G = nuE (fun a b c => G a c b) := by
  unfold nuE
  congr 1
  refine sum_congr rfl fun a _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun b _ => sum_congr rfl fun c _ => ?_
  by_cases hc : a ≠ c ∧ a ≠ b ∧ c ≠ b
  · rw [ite_eq_left hc, ite_eq_left (show a ≠ b ∧ a ≠ c ∧ b ≠ c from
      ⟨hc.2.1, hc.1, Ne.symm hc.2.2⟩)]
  · rw [ite_eq_right hc, ite_eq_right (fun h => hc ⟨h.2.1, h.1, Ne.symm h.2.2⟩)]

omit [Field F] in
theorem nuE_swap12 (G : F → F → F → ℝ) : nuE G = nuE (fun a b c => G b a c) := by
  unfold nuE
  congr 1
  rw [sum_comm]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ => ?_
  by_cases hc : b ≠ a ∧ b ≠ c ∧ a ≠ c
  · rw [ite_eq_left hc, ite_eq_left (show a ≠ b ∧ a ≠ c ∧ b ≠ c from
      ⟨Ne.symm hc.1, hc.2.2, hc.2.1⟩)]
  · rw [ite_eq_right hc, ite_eq_right (fun h => hc ⟨Ne.symm h.1, h.2.2, h.2.1⟩)]

omit [Field F] in
theorem nuE_add (G G' : F → F → F → ℝ) :
    nuE (fun a b c => G a b c + G' a b c) = nuE G + nuE G' := by
  unfold nuE
  rw [← mul_add, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun a _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun b _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun c _ => ?_
  split_ifs <;> ring

omit [Field F] in
theorem nuE_smul (k : ℝ) (G : F → F → F → ℝ) :
    nuE (fun a b c => k * G a b c) = k * nuE G := by
  unfold nuE
  rw [mul_left_comm]
  congr 1
  rw [mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun c _ => ?_
  split_ifs <;> ring

theorem nuE_mono {G G' : F → F → F → ℝ} (hp : 3 ≤ qF)
    (h : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → G a b c ≤ G' a b c) : nuE G ≤ nuE G' := by
  unfold nuE
  have h0 : 0 ≤ (qF * (qF - 1) * (qF - 2))⁻¹ := by
    have : 0 < qF - 2 := by linarith
    have : 0 < qF - 1 := by linarith
    have : 0 < qF := by linarith
    positivity
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun a _ => sum_le_sum fun b _ =>
    sum_le_sum fun c _ => ?_) h0
  by_cases hc : a ≠ b ∧ a ≠ c ∧ b ≠ c
  · rw [ite_eq_left hc, ite_eq_left hc]; exact h a b c hc.1 hc.2.1 hc.2.2
  · rw [ite_eq_right hc, ite_eq_right hc]

/-! ## The Gram of `V = (V₀, V₁, V₂)` -/

omit [Field F] in
/-- `⟨V₀ f, V₁ g⟩_{ν_E} = -(p(p - 1))⁻¹ ∑ f g` for mean-zero `f`. -/
theorem nuE_cross01 (hp : 3 ≤ qF) (f g : F → ℝ) (hf : ∑ a, f a = 0) :
    nuE (fun a b _ => f a * g b) = -((qF * (qF - 1))⁻¹ * ∑ a, f a * g a) := by
  rw [nuE_pair _ hp]
  have e : ∀ a, ∑ b, (if a ≠ b then f a * g b else 0) = f a * ∑ b, g b - f a * g a := by
    intro a
    have : ∀ b, (if a ≠ b then f a * g b else 0) =
        f a * g b - (if a = b then f a * g b else 0) := by
      intro b; by_cases hb : a = b
      · subst hb; simp
      · rw [ite_eq_left hb, ite_eq_right hb, sub_zero]
    simp only [this, sum_sub_distrib, ← mul_sum, sum_ite_eq, mem_univ, ↓reduceIte]
  simp only [e, sum_sub_distrib, ← sum_mul, hf, zero_mul, zero_sub, mul_neg]

omit [Field F] in
/-- `⟨V₀ f, V₀ g⟩_{ν_E} = p⁻¹ ∑ f g` (the coordinate is uniform). -/
theorem nuE_diag0 (hp : 3 ≤ qF) (f : F → ℝ) :
    nuE (fun a _ _ => f a) = qF⁻¹ * ∑ a, f a := by
  rw [nuE_pair (fun a _ => f a) hp]
  have e : ∀ a, ∑ b, (if a ≠ b then f a else 0) = (qF - 1) * f a := by
    intro a
    have : ∀ b, (if a ≠ b then f a else 0) = f a - (if a = b then f a else 0) := by
      intro b; by_cases hb : a = b
      · subst hb; simp
      · rw [ite_eq_left hb, ite_eq_right hb, sub_zero]
    simp only [this, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, sum_ite_eq, mem_univ,
      ↓reduceIte]
    ring
  simp only [e, ← mul_sum]
  have h1 : qF - 1 ≠ 0 := by intro h; linarith
  have h0 : qF ≠ 0 := by intro h; linarith
  field_simp

/-- **The Gram of `V`**: `‖V c‖²_{ν_E} ≥ (1 - 2u) p⁻¹ ∑ᵢ ∑ cᵢ²`, `u = 1/(p - 1)` (only `c₀`, `c₁`
need mean zero). -/
theorem norm_V_sq_ge (hp : 3 ≤ qF) (c₀ c₁ c₂ : F → ℝ) (h₀ : ∑ a, c₀ a = 0)
    (h₁ : ∑ a, c₁ a = 0) :
    (1 - 2 / (qF - 1)) * (qF⁻¹ * ∑ a, (c₀ a ^ 2 + c₁ a ^ 2 + c₂ a ^ 2)) ≤
      nuE (fun a b c => (c₀ a + c₁ b + c₂ c) ^ 2) := by
  have hexp : nuE (fun a b c => (c₀ a + c₁ b + c₂ c) ^ 2) =
      nuE (fun a _ _ => c₀ a ^ 2) + nuE (fun _ b _ => c₁ b ^ 2) + nuE (fun _ _ c => c₂ c ^ 2) +
        2 * nuE (fun a b _ => c₀ a * c₁ b) + 2 * nuE (fun a _ c => c₀ a * c₂ c) +
        2 * nuE (fun _ b c => c₁ b * c₂ c) := by
    rw [← nuE_smul, ← nuE_smul, ← nuE_smul, ← nuE_add, ← nuE_add, ← nuE_add, ← nuE_add,
      ← nuE_add]
    congr 1
    funext a b c
    ring
  -- reduce every term to the first coordinates
  have t1 : nuE (fun _ b _ => c₁ b ^ 2) = qF⁻¹ * ∑ a, c₁ a ^ 2 := by
    rw [nuE_swap12]; exact nuE_diag0 hp _
  have t2 : nuE (fun _ _ c => c₂ c ^ 2) = qF⁻¹ * ∑ a, c₂ a ^ 2 := by
    rw [nuE_swap23, nuE_swap12]; exact nuE_diag0 hp _
  have t02 : nuE (fun a _ c => c₀ a * c₂ c) = -((qF * (qF - 1))⁻¹ * ∑ a, c₀ a * c₂ a) := by
    rw [nuE_swap23]; exact nuE_cross01 hp _ _ h₀
  have t12 : nuE (fun _ b c => c₁ b * c₂ c) = -((qF * (qF - 1))⁻¹ * ∑ a, c₁ a * c₂ a) := by
    rw [nuE_swap12, nuE_swap23]; exact nuE_cross01 hp _ _ h₁
  have t0 : nuE (fun a _ _ => c₀ a ^ 2) = qF⁻¹ * ∑ a, c₀ a ^ 2 := nuE_diag0 hp _
  have t01 : nuE (fun a b _ => c₀ a * c₁ b) = -((qF * (qF - 1))⁻¹ * ∑ a, c₀ a * c₁ a) :=
    nuE_cross01 hp c₀ c₁ h₀
  rw [hexp, t0, t1, t2, t01, t02, t12]
  -- `2∑ cᵢcⱼ ≤ ∑ cᵢ² + ∑ cⱼ²`
  have k01 : 2 * ∑ a, c₀ a * c₁ a ≤ ∑ a, c₀ a ^ 2 + ∑ a, c₁ a ^ 2 := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_le_sum fun a _ => by nlinarith [sq_nonneg (c₀ a - c₁ a)]
  have k02 : 2 * ∑ a, c₀ a * c₂ a ≤ ∑ a, c₀ a ^ 2 + ∑ a, c₂ a ^ 2 := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_le_sum fun a _ => by nlinarith [sq_nonneg (c₀ a - c₂ a)]
  have k12 : 2 * ∑ a, c₁ a * c₂ a ≤ ∑ a, c₁ a ^ 2 + ∑ a, c₂ a ^ 2 := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_le_sum fun a _ => by nlinarith [sq_nonneg (c₁ a - c₂ a)]
  have hsplit : ∑ a, (c₀ a ^ 2 + c₁ a ^ 2 + c₂ a ^ 2) =
      ∑ a, c₀ a ^ 2 + ∑ a, c₁ a ^ 2 + ∑ a, c₂ a ^ 2 := by
    rw [sum_add_distrib, sum_add_distrib]
  rw [hsplit]
  have h0 : 0 < qF := by linarith
  have h1 : 0 < qF - 1 := by linarith
  have hinv : (qF * (qF - 1))⁻¹ = qF⁻¹ * (1 / (qF - 1)) := by
    rw [mul_inv, one_div]
  rw [hinv]
  have hq : 0 < qF⁻¹ * (1 / (qF - 1)) := by positivity
  have e2 : 2 / (qF - 1) = 2 * (1 / (qF - 1)) := by ring
  rw [e2]
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add (add_le_add k01 k02) k12) hq.le]

/-! ## `𝖢𝖣 (V c)` and the bound -/

/-- `𝖢𝖣 (V c)` at the half `x`: `E_{y ∼ ν_E}[χ(y₀ - x₁) χ(y₁ - x₀) (c₀(y₀) + c₁(y₁) + c₂(y₂))]`. -/
noncomputable def CDV (c₀ c₁ c₂ : F → ℝ) (x₀ x₁ : F) : ℝ :=
  nuE (fun a b c => (χ (a - x₁) : ℝ) * (χ (b - x₀) : ℝ) * (c₀ a + c₁ b + c₂ c))

theorem TE_add (g g' : F → ℝ) (x₀ x₁ : F) :
    TE (fun t => g t + g' t) x₀ x₁ = TE g x₀ x₁ + TE g' x₀ x₁ := by
  unfold TE
  rw [← mul_add, ← sum_add_distrib]
  congr 1
  exact sum_congr rfl fun t _ => by ring

theorem TE_smul (k : ℝ) (g : F → ℝ) (x₀ x₁ : F) : TE (fun t => k * g t) x₀ x₁ = k * TE g x₀ x₁ := by
  simp only [TE, mul_sum]
  exact sum_congr rfl fun t _ => by ring

/-- **`𝖢𝖣 (V c) = 𝒯_E(-u c₀ - u c₁ + 2c₂/((p - 1)(p - 2)))`** on halves (`x₀ ≠ x₁`). -/
theorem CD_V_eq (hF : ringChar F ≠ 2) (hp : 3 ≤ qF) (c₀ c₁ c₂ : F → ℝ) (h₂ : ∑ a, c₂ a = 0)
    {x₀ x₁ : F} (hx : x₀ ≠ x₁) :
    CDV c₀ c₁ c₂ x₀ x₁ = TE (fun t => -(1 / (qF - 1)) * c₀ t + -(1 / (qF - 1)) * c₁ t +
      2 / ((qF - 1) * (qF - 2)) * c₂ t) x₀ x₁ := by
  unfold CDV
  have e : (fun a b c => (χ (a - x₁) : ℝ) * (χ (b - x₀) : ℝ) * (c₀ a + c₁ b + c₂ c)) =
      fun a b c => ((χ (a - x₁) : ℝ) * (χ (b - x₀) : ℝ) * c₀ a +
        (χ (a - x₁) : ℝ) * (χ (b - x₀) : ℝ) * c₁ b) +
          (χ (a - x₁) : ℝ) * (χ (b - x₀) : ℝ) * c₂ c := by
    funext a b c; ring
  rw [e, nuE_add, nuE_add, CD_V0 hF hp, CD_V1 hF hp, CD_V2 hF hp c₂ h₂ hx, TE_add, TE_add,
    TE_smul, TE_smul, TE_smul]
  ring

/-- **`lem:record:e-orthogonal`(b): `‖𝖢𝖣 H‖ ≤ e_E`**, on the range of `V`, squared:
`‖𝖢𝖣 (V c)‖²_{ν_E} ≤ q³ (2 + 4q²/(1 - 2q)²)/((1 - q)(1 - 3q)) · ‖V c‖²_{ν_E}`, `q = 1/p`, for every
triple of mean-zero functions (`p ≥ 7`). -/
theorem CD_V_bound (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (c₀ c₁ c₂ : F → ℝ) (h₀ : ∑ a, c₀ a = 0) (h₁ : ∑ a, c₁ a = 0) (h₂ : ∑ a, c₂ a = 0) :
    nuE (fun a b _ => CDV c₀ c₁ c₂ a b ^ 2) ≤
      (1 / qF) ^ 3 * (2 + 4 * (1 / qF) ^ 2 / (1 - 2 * (1 / qF)) ^ 2) /
        ((1 - 1 / qF) * (1 - 3 * (1 / qF))) * nuE (fun a b c => (c₀ a + c₁ b + c₂ c) ^ 2) := by
  have hp : 3 ≤ qF := by linarith
  have h0 : 0 < qF := by linarith
  have h1 : 0 < qF - 1 := by linarith
  have h2 : 0 < qF - 2 := by linarith
  have h3' : 0 < qF - 3 := by linarith
  set g : F → ℝ := fun t => -(1 / (qF - 1)) * c₀ t + -(1 / (qF - 1)) * c₁ t +
    2 / ((qF - 1) * (qF - 2)) * c₂ t with hg
  have hgz : ∑ t, g t = 0 := by
    simp only [hg, sum_add_distrib, ← mul_sum, h₀, h₁, h₂, mul_zero, add_zero]
  -- `‖𝖢𝖣 (V c)‖² = ‖𝒯_E g‖² ≤ q · ‖g‖²`
  have hTE : nuE (fun a b _ => CDV c₀ c₁ c₂ a b ^ 2) ≤ qF⁻¹ * unifNormSq g := by
    rw [nuE_congr (G' := fun a b _ => TE g a b ^ 2) (fun a b _ hab _ _ => by
      rw [CD_V_eq hF hp c₀ c₁ c₂ h₂ hab])]
    refine (TE_norm_le hF h3 hp g hgz).trans ?_
    have hu : 0 ≤ unifNormSq g := by unfold unifNormSq; positivity
    have hq : qF⁻¹ * (1 - 2 * qF⁻¹) / (1 - qF⁻¹) ≤ qF⁻¹ := by
      apply TE_const_le (by positivity)
      rw [inv_lt_one₀ h0]; linarith
    exact mul_le_mul_of_nonneg_right hq hu
  -- Cauchy–Schwarz: `g² ≤ (2u² + w²)(c₀² + c₁² + c₂²)`
  set u : ℝ := 1 / (qF - 1) with hu
  set w : ℝ := 2 / ((qF - 1) * (qF - 2)) with hw
  have hpt : ∀ a, g a ^ 2 ≤ (2 * u ^ 2 + w ^ 2) * (c₀ a ^ 2 + c₁ a ^ 2 + c₂ a ^ 2) := by
    intro a
    simp only [hg]
    nlinarith [sq_nonneg (u * c₀ a - u * c₁ a), sq_nonneg (u * c₂ a + w * c₀ a),
      sq_nonneg (u * c₂ a + w * c₁ a)]
  have hcs : unifNormSq g ≤ (2 * u ^ 2 + w ^ 2) *
      (qF⁻¹ * ∑ a, (c₀ a ^ 2 + c₁ a ^ 2 + c₂ a ^ 2)) := by
    calc unifNormSq g = qF⁻¹ * ∑ a, g a ^ 2 := rfl
      _ ≤ qF⁻¹ * ∑ a, (2 * u ^ 2 + w ^ 2) * (c₀ a ^ 2 + c₁ a ^ 2 + c₂ a ^ 2) :=
          mul_le_mul_of_nonneg_left (sum_le_sum fun a _ => hpt a) (by positivity)
      _ = (2 * u ^ 2 + w ^ 2) * (qF⁻¹ * ∑ a, (c₀ a ^ 2 + c₁ a ^ 2 + c₂ a ^ 2)) := by
          rw [← mul_sum]; ring
  have hV := norm_V_sq_ge hp c₀ c₁ c₂ h₀ h₁
  -- assemble
  have hS : 0 ≤ qF⁻¹ * ∑ a, (c₀ a ^ 2 + c₁ a ^ 2 + c₂ a ^ 2) := by positivity
  have h12u : 0 < 1 - 2 / (qF - 1) := by
    rw [sub_pos, div_lt_one h1]; linarith
  have hS' : qF⁻¹ * ∑ a, (c₀ a ^ 2 + c₁ a ^ 2 + c₂ a ^ 2) ≤
      nuE (fun a b c => (c₀ a + c₁ b + c₂ c) ^ 2) / (1 - 2 / (qF - 1)) := by
    rw [le_div_iff₀ h12u]; linarith
  have hconst : qF⁻¹ * (2 * u ^ 2 + w ^ 2) / (1 - 2 / (qF - 1)) =
      (1 / qF) ^ 3 * (2 + 4 * (1 / qF) ^ 2 / (1 - 2 * (1 / qF)) ^ 2) /
        ((1 - 1 / qF) * (1 - 3 * (1 / qF))) := by
    rw [hu, hw]
    have e1 : (1 - 1 / qF) = (qF - 1) / qF := by field_simp
    have e2 : (1 - 2 * (1 / qF)) = (qF - 2) / qF := by field_simp
    have e3 : (1 - 3 * (1 / qF)) = (qF - 3) / qF := by field_simp
    have e4 : (1 - 2 / (qF - 1)) = (qF - 3) / (qF - 1) := by
      field_simp; ring
    rw [e1, e2, e3, e4]
    field_simp
    ring
  calc nuE (fun a b _ => CDV c₀ c₁ c₂ a b ^ 2) ≤ qF⁻¹ * unifNormSq g := hTE
    _ ≤ qF⁻¹ * ((2 * u ^ 2 + w ^ 2) * (qF⁻¹ * ∑ a, (c₀ a ^ 2 + c₁ a ^ 2 + c₂ a ^ 2))) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ ≤ qF⁻¹ * ((2 * u ^ 2 + w ^ 2) *
          (nuE (fun a b c => (c₀ a + c₁ b + c₂ c) ^ 2) / (1 - 2 / (qF - 1)))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hS' (by positivity)
    _ = qF⁻¹ * (2 * u ^ 2 + w ^ 2) / (1 - 2 / (qF - 1)) *
          nuE (fun a b c => (c₀ a + c₁ b + c₂ c) ^ 2) := by ring
    _ = _ := by rw [hconst]

end Sarkozy.MiddleRecords
