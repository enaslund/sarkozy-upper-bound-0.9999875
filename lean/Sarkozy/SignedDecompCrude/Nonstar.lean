module

public import Sarkozy.SignedDecompCrude.Removed
public import Sarkozy.PrimeGram.OldAB

@[expose] public section

/-!
# The nine nonstars of the signed record as one tensor product (ND)

`paper/sections/21_middle_records.tex`, `lem:record:projected-nonstar`(a),(b) and
`prop:signed-bounds`(c), Step 2 ("The nonstars of `Ψ^soft_t` are those of the products of
`{𝖢, (1 - t)𝖡, (1 - t)𝖡𝖢}` with `{𝖣, (1 + t)𝖠, (1 - t)𝖠𝖣}` ... each of norm at most `(2/Z)q`").

The nonstar kernel factors: `K_ns(x, y) = G₁(y₀; x₁, x₂) G₂(x₀; y₁, y₂)` (`knon_factor`), with
`G₁ = 𝖢 + (1 - t)𝖡 + (1 - t)𝖡𝖢` a function of `(y₀, x₁, x₂)` and
`G₂ = 𝖣 + (1 + t)𝖠 + (1 - t)𝖠𝖣` a function of `(x₀, y₁, y₂)`, on disjoint labels. Hence its
norm is the product of the norms of the two rectangular stars.

* **`gen_sq_le`**: for `Gen(s; u, w) = Aχ(u - s) + Bχ(w - s) + Cχ(u - s)χ(w - s)`,
  `∑_{u,w} (∑_s Gen(s; u, w) h(s))² ≤ (A² + B² + C²) p² ∑ h²` (the three parts are orthogonal;
  Paley `paley_sq_le'` for each).
* **`tensor_bound`**: `|∑ G(x) G₁(y₀, x₁, x₂) G₂(x₀, y₁, y₂) H(y)| ≤ √λ₁ √λ₂ ‖G‖ ‖H‖` from the two
  row bounds (Cauchy–Schwarz in `(x₁, x₂, y₁, y₂)`).
* **`nonstarBound_tensor`**: **`NonstarBound t (2 |𝐚| |𝐛| / Z)`**,
  `|𝐚|² = 1 + 2(1 - t)²`, `|𝐛|² = 1 + (1 + t)² + (1 - t)²`, `Z = (1 - q)(1 - 2q)`. At
  `t = 127/500`, `2|𝐚||𝐛| = 5.1428...`, against the paper's sum `2(9 - 6t) = 14.952` of the nine
  monomial bounds `(2/Z)q`.
-/

open Finset Matrix

namespace Sarkozy.SignedDecompCrude

open Sarkozy.PrimeGram Sarkozy.SignedEstimates Sarkozy.SignedComponents Sarkozy.SignedDecomp

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

local notation "qF" => (Fintype.card F : ℝ)

/-- A rectangular star `Gen(s; u, w) = Aχ(u - s) + Bχ(w - s) + Cχ(u - s)χ(w - s)`. -/
noncomputable def gen (A B C : ℝ) (s u w : F) : ℝ :=
  A * (χ (u - s) : ℝ) + B * (χ (w - s) : ℝ) + C * ((χ (u - s) : ℝ) * χ (w - s))

section Gen

variable (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3)

include hR h3 in
/-- **The norm of a rectangular star**: `‖Gen‖² ≤ (A² + B² + C²) p²` (`ℓ²(𝔽_p) → ℓ²(𝔽_p²)`). -/
theorem gen_sq_le (A B C : ℝ) (h : F → ℝ) :
    ∑ u, ∑ w, (∑ s, gen A B C s u w * h s) ^ 2 ≤
      (A ^ 2 + B ^ 2 + C ^ 2) * qF ^ 2 * ∑ s, h s ^ 2 := by
  set P : F → ℝ := fun u => ∑ s, (χ (u - s) : ℝ) * h s with hPdef
  set Q : F → F → ℝ := fun u w => ∑ s, (χ (w - s) : ℝ) * ((χ (u - s) : ℝ) * h s) with hQdef
  have hin : ∀ u w, ∑ s, gen A B C s u w * h s = A * P u + B * P w + C * Q u w := by
    intro u w
    simp only [hPdef, hQdef, gen, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun s _ => by ring
  have hP0 : ∑ u, P u = 0 := by
    simp only [hPdef]
    rw [sum_comm]
    refine sum_eq_zero fun s _ => ?_
    rw [← sum_mul, sumR_chi hR s, zero_mul]
  have hQ0 : ∀ u, ∑ w, Q u w = 0 := by
    intro u
    simp only [hQdef]
    rw [sum_comm]
    refine sum_eq_zero fun s _ => ?_
    rw [← sum_mul, sumR_chi hR s, zero_mul]
  have hQ0' : ∀ w, ∑ u, Q u w = 0 := by
    intro w
    simp only [hQdef]
    rw [sum_comm]
    refine sum_eq_zero fun s _ => ?_
    have e : ∀ u, (χ (w - s) : ℝ) * ((χ (u - s) : ℝ) * h s) =
        (χ (u - s) : ℝ) * ((χ (w - s) : ℝ) * h s) := fun u => by ring
    simp only [e]
    rw [← sum_mul, sumR_chi hR s, zero_mul]
  have hH0 : 0 ≤ ∑ s, h s ^ 2 := sum_nonneg fun s _ => sq_nonneg _
  have hPsq : ∑ u, P u ^ 2 ≤ qF * ∑ s, h s ^ 2 := Sarkozy.PrimeGram.paley_sq_le' hR h3 h
  have hQsq : ∀ u, ∑ w, Q u w ^ 2 ≤ qF * ∑ s, h s ^ 2 := by
    intro u
    have h1 := Sarkozy.PrimeGram.paley_sq_le' hR h3 (fun s => (χ (u - s) : ℝ) * h s)
    refine h1.trans ?_
    have hq : (0 : ℝ) ≤ qF := Nat.cast_nonneg _
    refine mul_le_mul_of_nonneg_left (sum_le_sum fun s _ => ?_) hq
    have hc := abs_le.mp (chi_abs_le (u - s))
    rw [mul_pow]
    have : (χ (u - s) : ℝ) ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (h s)]
  have hexp : ∑ u, ∑ w, (A * P u + B * P w + C * Q u w) ^ 2 =
      ∑ u, ∑ _w : F, A ^ 2 * P u ^ 2 + ∑ _u : F, ∑ w, B ^ 2 * P w ^ 2 +
        ∑ u, ∑ w, C ^ 2 * Q u w ^ 2 +
        ∑ u, ∑ w, 2 * A * B * P u * P w + ∑ u, ∑ w, 2 * A * C * P u * Q u w +
        ∑ u, ∑ w, 2 * B * C * P w * Q u w := by
    simp only [← sum_add_distrib]
    exact sum_congr rfl fun u _ => sum_congr rfl fun w _ => by ring
  have s1 : ∑ u, ∑ _w : F, A ^ 2 * P u ^ 2 = qF * (A ^ 2 * ∑ u, P u ^ 2) := by
    simp only [sum_const, card_univ, nsmul_eq_mul, mul_sum]
  have s2 : ∑ _u : F, ∑ w, B ^ 2 * P w ^ 2 = qF * (B ^ 2 * ∑ w, P w ^ 2) := by
    simp only [sum_const, card_univ, nsmul_eq_mul, mul_sum]
  have s3 : ∑ u, ∑ w, C ^ 2 * Q u w ^ 2 ≤ C ^ 2 * (qF * (qF * ∑ s, h s ^ 2)) := by
    have e : ∑ u, ∑ w, C ^ 2 * Q u w ^ 2 = C ^ 2 * ∑ u, ∑ w, Q u w ^ 2 := by
      simp only [mul_sum]
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg C)
    calc ∑ u, ∑ w, Q u w ^ 2 ≤ ∑ _u : F, qF * ∑ s, h s ^ 2 := sum_le_sum fun u _ => hQsq u
      _ = qF * (qF * ∑ s, h s ^ 2) := by rw [sum_const, card_univ, nsmul_eq_mul]
  have s4 : ∑ u, ∑ w, 2 * A * B * P u * P w = 0 := by
    simp only [← mul_sum, hP0, mul_zero, sum_const_zero]
  have s5 : ∑ u, ∑ w, 2 * A * C * P u * Q u w = 0 := by
    simp only [← mul_sum, hQ0, mul_zero, sum_const_zero]
  have s6 : ∑ u, ∑ w, 2 * B * C * P w * Q u w = 0 := by
    rw [sum_comm]
    simp only [← mul_sum, hQ0', mul_zero, sum_const_zero]
  simp only [hin]
  rw [hexp, s1, s2, s4, s5, s6]
  have hq : (0 : ℝ) ≤ qF := Nat.cast_nonneg _
  have t1 : qF * (A ^ 2 * ∑ u, P u ^ 2) ≤ qF * (A ^ 2 * (qF * ∑ s, h s ^ 2)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPsq (sq_nonneg A)) hq
  have t2 : qF * (B ^ 2 * ∑ w, P w ^ 2) ≤ qF * (B ^ 2 * (qF * ∑ s, h s ^ 2)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPsq (sq_nonneg B)) hq
  nlinarith

end Gen

/-! ## The tensor bound -/

omit [Field F] [DecidableEq F] in
theorem sum4_comm (f : F → F → F → F → ℝ) :
    ∑ b, ∑ c, ∑ u, ∑ w, f b c u w = ∑ u, ∑ w, ∑ b, ∑ c, f b c u w := by
  calc ∑ b, ∑ c, ∑ u, ∑ w, f b c u w = ∑ b, ∑ u, ∑ c, ∑ w, f b c u w :=
        sum_congr rfl fun b _ => sum_comm
    _ = ∑ b, ∑ u, ∑ w, ∑ c, f b c u w :=
        sum_congr rfl fun b _ => sum_congr rfl fun u _ => sum_comm
    _ = ∑ u, ∑ b, ∑ w, ∑ c, f b c u w := sum_comm
    _ = ∑ u, ∑ w, ∑ b, ∑ c, f b c u w := sum_congr rfl fun u _ => sum_comm

omit [Field F] [DecidableEq F] in
theorem sum3_rot (f : F → F → F → ℝ) : ∑ a, ∑ b, ∑ c, f a b c = ∑ b, ∑ c, ∑ a, f a b c := by
  calc ∑ a, ∑ b, ∑ c, f a b c = ∑ b, ∑ a, ∑ c, f a b c := sum_comm
    _ = ∑ b, ∑ c, ∑ a, f a b c := sum_congr rfl fun b _ => sum_comm

omit [Field F] [DecidableEq F] in
theorem cs4 (φ ψ : F → F → F → F → ℝ) :
    |∑ b, ∑ c, ∑ u, ∑ w, φ b c u w * ψ b c u w| ≤
      √(∑ b, ∑ c, ∑ u, ∑ w, φ b c u w ^ 2) * √(∑ b, ∑ c, ∑ u, ∑ w, ψ b c u w ^ 2) := by
  have e : ∀ g : F → F → F → F → ℝ, ∑ b, ∑ c, ∑ u, ∑ w, g b c u w =
      ∑ z : F × F × F × F, g z.1 z.2.1 z.2.2.1 z.2.2.2 := fun g => by
    simp only [Fintype.sum_prod_type]
  rw [e (fun b c u w => φ b c u w * ψ b c u w), e (fun b c u w => φ b c u w ^ 2),
    e (fun b c u w => ψ b c u w ^ 2)]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ (fun z : F × F × F × F =>
    φ z.1 z.2.1 z.2.2.1 z.2.2.2) (fun z => ψ z.1 z.2.1 z.2.2.1 z.2.2.2)
  rw [← Real.sqrt_mul (sum_nonneg fun z _ => sq_nonneg _)]
  exact Real.abs_le_sqrt hcs

omit [Field F] [DecidableEq F] in
/-- **The tensor bound**: a kernel `G₁(y₀; x₁, x₂) G₂(x₀; y₁, y₂)` on disjoint labels has norm at
most `√λ₁ √λ₂` on `ℓ²(𝔽_p³)` when the two rectangular stars have norms `√λ₁`, `√λ₂`. -/
theorem tensor_bound (G1 G2 : F → F → F → ℝ) {l1 l2 : ℝ} (hl1 : 0 ≤ l1) (hl2 : 0 ≤ l2)
    (h1 : ∀ h : F → ℝ, ∑ u, ∑ w, (∑ s, G1 s u w * h s) ^ 2 ≤ l1 * ∑ s, h s ^ 2)
    (h2 : ∀ h : F → ℝ, ∑ u, ∑ w, (∑ s, G2 s u w * h s) ^ 2 ≤ l2 * ∑ s, h s ^ 2)
    (G H : (Fin 3 → F) → ℝ) :
    |∑ x, ∑ y, G x * (G1 (y 0) (x 1) (x 2) * G2 (x 0) (y 1) (y 2)) * H y| ≤
      √l1 * √l2 * (√(∑ x, G x ^ 2) * √(∑ y, H y ^ 2)) := by
  set Φ : F → F → F → F → ℝ := fun b c u w => ∑ a, G2 a u w * G ![a, b, c] with hΦ
  set Ψ : F → F → F → F → ℝ := fun b c u w => ∑ s, G1 s b c * H ![s, u, w] with hΨ
  -- the reindexing
  have hA : ∑ x, ∑ y, G x * (G1 (y 0) (x 1) (x 2) * G2 (x 0) (y 1) (y 2)) * H y =
      ∑ b, ∑ c, ∑ u, ∑ w, Φ b c u w * Ψ b c u w := by
    have e1 : ∑ x, ∑ y, G x * (G1 (y 0) (x 1) (x 2) * G2 (x 0) (y 1) (y 2)) * H y =
        ∑ a, ∑ b, ∑ c, ∑ s, ∑ u, ∑ w,
          G ![a, b, c] * (G1 s b c * G2 a u w) * H ![s, u, w] := by
      rw [sum_triple]
      refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ => ?_
      rw [sum_triple]
      rfl
    rw [e1, sum3_rot]
    refine sum_congr rfl fun b _ => sum_congr rfl fun c _ => ?_
    rw [sum4_comm]
    refine sum_congr rfl fun u _ => sum_congr rfl fun w _ => ?_
    simp only [hΦ, hΨ, sum_mul_sum]
    exact sum_congr rfl fun a _ => sum_congr rfl fun s _ => by ring
  have hC : ∑ b, ∑ c, ∑ u, ∑ w, Φ b c u w ^ 2 ≤ l2 * ∑ x, G x ^ 2 := by
    calc ∑ b, ∑ c, ∑ u, ∑ w, Φ b c u w ^ 2 ≤ ∑ b, ∑ c, l2 * ∑ a, G ![a, b, c] ^ 2 :=
          sum_le_sum fun b _ => sum_le_sum fun c _ => h2 (fun a => G ![a, b, c])
      _ = l2 * ∑ x, G x ^ 2 := by
          rw [sum_triple (fun x => G x ^ 2), sum3_rot, mul_sum]
          refine sum_congr rfl fun b _ => ?_
          rw [mul_sum]
  have hD : ∑ b, ∑ c, ∑ u, ∑ w, Ψ b c u w ^ 2 ≤ l1 * ∑ y, H y ^ 2 := by
    rw [sum4_comm]
    calc ∑ u, ∑ w, ∑ b, ∑ c, Ψ b c u w ^ 2 ≤ ∑ u, ∑ w, l1 * ∑ s, H ![s, u, w] ^ 2 :=
          sum_le_sum fun u _ => sum_le_sum fun w _ => h1 (fun s => H ![s, u, w])
      _ = l1 * ∑ y, H y ^ 2 := by
          rw [sum_triple (fun y => H y ^ 2), sum3_rot, mul_sum]
          refine sum_congr rfl fun u _ => ?_
          rw [mul_sum]
  rw [hA]
  refine (cs4 Φ Ψ).trans ?_
  have hG0 : 0 ≤ ∑ x, G x ^ 2 := sum_nonneg fun x _ => sq_nonneg _
  have hH0 : 0 ≤ ∑ y, H y ^ 2 := sum_nonneg fun y _ => sq_nonneg _
  calc √(∑ b, ∑ c, ∑ u, ∑ w, Φ b c u w ^ 2) * √(∑ b, ∑ c, ∑ u, ∑ w, Ψ b c u w ^ 2)
      ≤ √(l2 * ∑ x, G x ^ 2) * √(l1 * ∑ y, H y ^ 2) :=
        mul_le_mul (Real.sqrt_le_sqrt hC) (Real.sqrt_le_sqrt hD) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = √l1 * √l2 * (√(∑ x, G x ^ 2) * √(∑ y, H y ^ 2)) := by
        rw [Real.sqrt_mul hl2, Real.sqrt_mul hl1]
        ring

/-! ## The nonstar bound -/

section Nonstar

variable (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3)

include h3 in
/-- **`K_ns = G₁(y₀; x₁, x₂) G₂(x₀; y₁, y₂)`**, `G₁ = Gen(-1, 1 - t, -(1 - t))`,
`G₂ = Gen(1, 1 + t, 1 - t)` (at `p ≡ 3 (mod 4)`, `𝖢 = χ(y₀ - x₁) = -χ(x₁ - y₀)`). -/
theorem knon_factor (t : ℝ) (x y : Fin 3 → F) :
    Knon t x y = gen (-1) (1 - t) (-(1 - t)) (y 0) (x 1) (x 2) *
      gen 1 (1 + t) (1 - t) (x 0) (y 1) (y 2) := by
  unfold Knon gen chC chD PrimeGram.chA PrimeGram.chB
  rw [chiR_swap h3 (y 0) (x 1)]
  ring

include hR h3 in
/-- **`lem:record:projected-nonstar` for the nine nonstars of the signed record, as a tensor
product**: `NonstarBound t (2|𝐚||𝐛|/((1 - q)(1 - 2q)))`, `|𝐚|² = 1 + 2(1 - t)²`,
`|𝐛|² = 1 + (1 + t)² + (1 - t)²`. -/
theorem nonstarBound_tensor (h19 : 19 ≤ Fintype.card F) (t : ℝ) :
    NonstarBound (F := F) t (2 * (√(1 + 2 * (1 - t) ^ 2) * √(1 + (1 + t) ^ 2 + (1 - t) ^ 2)) /
      ((1 - qF⁻¹) * (1 - 2 * qF⁻¹))) := by
  intro f g
  have ha : 0 ≤ 1 + 2 * (1 - t) ^ 2 := by positivity
  have hb : 0 ≤ 1 + (1 + t) ^ 2 + (1 - t) ^ 2 := by positivity
  refine E2_of_l2 hR h19 (Knon t) ?_ f g
  intro G H
  have hq : (0 : ℝ) ≤ qF := Nat.cast_nonneg _
  have e1 : (-1 : ℝ) ^ 2 + (1 - t) ^ 2 + (-(1 - t)) ^ 2 = 1 + 2 * (1 - t) ^ 2 := by ring
  have e2 : (1 : ℝ) ^ 2 + (1 + t) ^ 2 + (1 - t) ^ 2 = 1 + (1 + t) ^ 2 + (1 - t) ^ 2 := by ring
  have h1 : ∀ h : F → ℝ, ∑ u, ∑ w, (∑ s, gen (-1) (1 - t) (-(1 - t)) s u w * h s) ^ 2 ≤
      ((1 + 2 * (1 - t) ^ 2) * qF ^ 2) * ∑ s, h s ^ 2 := by
    intro h; have := gen_sq_le hR h3 (-1) (1 - t) (-(1 - t)) h; rwa [e1] at this
  have h2 : ∀ h : F → ℝ, ∑ u, ∑ w, (∑ s, gen 1 (1 + t) (1 - t) s u w * h s) ^ 2 ≤
      ((1 + (1 + t) ^ 2 + (1 - t) ^ 2) * qF ^ 2) * ∑ s, h s ^ 2 := by
    intro h; have := gen_sq_le hR h3 1 (1 + t) (1 - t) h; rwa [e2] at this
  have hT := tensor_bound _ _ (by positivity) (by positivity) h1 h2 G H
  have e : ∑ x, ∑ y, G x * Knon t x y * H y = ∑ x, ∑ y, G x *
      (gen (-1) (1 - t) (-(1 - t)) (y 0) (x 1) (x 2) * gen 1 (1 + t) (1 - t) (x 0) (y 1) (y 2)) *
        H y := by
    simp only [knon_factor h3]
  rw [e]
  refine hT.trans (le_of_eq ?_)
  rw [Real.sqrt_mul ha, Real.sqrt_mul hb, Real.sqrt_sq hq]
  ring

end Nonstar

end Sarkozy.SignedDecompCrude
