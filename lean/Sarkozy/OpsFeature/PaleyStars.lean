module

public import Sarkozy.OpsFeature.Stars
public import Sarkozy.OpsFeature.Edge34Prime

@[expose] public section

/-!
# The signed stars `𝖥(Φ̂)`, `𝖤(Φ̂)` at a prime (`eq:signed-star`)

`paper/sections/23_envelopes.tex`, `eq:signed-star`: on `(L²)^5` (fold labels `0, …, 4`) and
`(L²)^3` (matching labels), with the normalized Paley operator `Φ̂ = P/r`,
`(Φ̂ f)(z) = p^{-1/2} ∑_{z'} χ(z' - z) f(z')` (`phiHat`),
* `𝖥(Φ̂)` has the blocks `Φ̂`, `t Φ̂`, `t - 1` from the centre `0` to the arms `1, 2, 3` and `Φ̂`,
  `t Φ̂`, `1 - t` back (`foldStar`, `t = 127/500`, on the labels `0..3` of the tensor features; the
  label `4` carries no block);
* `𝖤(Φ̂)` has the blocks `Φ̂` between the centre `0` and the arm `1` (`matchStar`).

**Proved:** the star facts that `hdom_of_table_stars` asks of them: they join the centre to the arms
only (`foldStar_sec`, `matchStar_sec`), the block `(a, a')` has norm at most `mag a · mag a'`
(`foldStar_norm`, `matchStar_norm`, from `‖Φ̂ f‖² = ‖f‖² - (∑ f)²/p ≤ ‖f‖²`, `phiHat_norm`), and
they are antisymmetric (`foldStar_antisymm`, `matchStar_antisymm`, from `χ(-1) = -1`).
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.OpsFeature

open Sarkozy.TraceMixing Sarkozy.Envelopes Sarkozy.EnvelopeSteps

section Paley

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

local notation "qF" => (Fintype.card F : ℝ)

/-- The normalized Paley operator `Φ̂ = P/r` as a matrix. -/
noncomputable def phiHat : Matrix F F ℝ := fun z z' => (χ (z' - z) : ℝ) / Real.sqrt qF

theorem phiHat_antisymm (h3 : Fintype.card F % 4 = 3) (z z' : F) :
    phiHat z z' = -phiHat z' z := by
  simp only [phiHat, chi_swap h3 z' z, Int.cast_neg, neg_div]

/-- The Paley identity `∑_z (∑_{z'} χ(z' - z) y(z'))² = p ∑ y² - (∑ y)²`. -/
theorem paley_identity (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (y : F → ℝ) :
    ∑ z, (∑ z', (χ (z' - z) : ℝ) * y z') ^ 2 = qF * ∑ z, y z ^ 2 - (∑ z, y z) ^ 2 := by
  have e3 : ∀ z, (∑ z', (χ (z' - z) : ℝ) * y z') ^ 2 =
      ∑ w, ∑ w', y w * y w' * ((χ (w - z) : ℝ) * (χ (w' - z) : ℝ)) := by
    intro z
    simp only [sq, sum_mul_sum]
    exact sum_congr rfl fun w _ => sum_congr rfl fun w' _ => by ring
  simp only [e3]
  rw [sum_comm]
  have e4 : ∀ w, ∑ z, ∑ w', y w * y w' * ((χ (w - z) : ℝ) * (χ (w' - z) : ℝ)) =
      ∑ w', y w * y w' * ((if w = w' then qF else 0) - 1) := by
    intro w
    rw [sum_comm]
    refine sum_congr rfl fun w' _ => ?_
    rw [← mul_sum, sum_chi_mul_chi_R hF h3]
  rw [sum_congr rfl fun w _ => e4 w]
  have e5 : ∀ w, ∑ w', y w * y w' * ((if w = w' then qF else 0) - 1) =
      qF * y w ^ 2 - y w * ∑ w', y w' := by
    intro w
    have h1 : ∑ w', y w * y w' * ((if w = w' then qF else 0) - 1) =
        ∑ w', (if w = w' then qF * y w * y w' else 0) - y w * ∑ w', y w' := by
      rw [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun w' _ => by split_ifs <;> ring
    rw [h1, sum_ite_eq]
    simp only [mem_univ, ↓reduceIte]
    ring
  rw [sum_congr rfl fun w _ => e5 w, sum_sub_distrib, ← mul_sum, ← sum_mul, sq]

/-- `‖Φ̂ f‖² ≤ ‖f‖²`. -/
theorem phiHat_norm (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (y : F → ℝ) :
    ∑ z, (phiHat *ᵥ y) z ^ 2 ≤ ∑ z, y z ^ 2 := by
  have hq : 0 < qF := by exact_mod_cast Fintype.card_pos
  have e : ∀ z, (phiHat *ᵥ y) z ^ 2 = (1 / qF) * (∑ z', (χ (z' - z) : ℝ) * y z') ^ 2 := by
    intro z
    simp only [mulVec, dotProduct, phiHat, div_mul_eq_mul_div, ← sum_div, div_pow,
      Real.sq_sqrt hq.le]
    ring
  simp only [e, ← mul_sum, paley_identity hF h3 y]
  have : 0 ≤ (∑ z, y z) ^ 2 := sq_nonneg _
  rw [mul_sub, ← mul_assoc, one_div_mul_cancel hq.ne', one_mul]
  have : 0 ≤ 1 / qF * (∑ z, y z) ^ 2 := by positivity
  linarith

/-- The parameter `t = 127/500` of the signed fold record. -/
noncomputable def tlaw : ℝ := 127 / 500

/-- **The fold star `𝖥(Φ̂)`** on the labels `0..3` (centre and three arms). -/
noncomputable def foldStar : Matrix (Fin 4 × F) (Fin 4 × F) ℝ := fun x x' =>
  if x.1 = 0 ∧ x'.1 = 1 then phiHat x.2 x'.2
  else if x.1 = 1 ∧ x'.1 = 0 then phiHat x.2 x'.2
  else if x.1 = 0 ∧ x'.1 = 2 then tlaw * phiHat x.2 x'.2
  else if x.1 = 2 ∧ x'.1 = 0 then tlaw * phiHat x.2 x'.2
  else if x.1 = 0 ∧ x'.1 = 3 then (tlaw - 1) * (if x.2 = x'.2 then 1 else 0)
  else if x.1 = 3 ∧ x'.1 = 0 then (1 - tlaw) * (if x.2 = x'.2 then 1 else 0)
  else 0

/-- **The matching star `𝖤(Φ̂)`** on the labels `0, 1` (centre and arm). -/
noncomputable def matchStar : Matrix (Fin 2 × F) (Fin 2 × F) ℝ := fun x x' =>
  if x.1 ≠ x'.1 then phiHat x.2 x'.2 else 0

theorem foldStar_sec (a a' : Fin 4) (x x' : F) (h : a = 0 ↔ a' = 0) :
    foldStar (a, x) (a', x') = 0 := by
  unfold foldStar
  fin_cases a <;> fin_cases a' <;> simp_all

theorem matchStar_sec (a a' : Fin 2) (x x' : F) (h : a = 0 ↔ a' = 0) :
    matchStar (a, x) (a', x') = 0 := by
  unfold matchStar
  fin_cases a <;> fin_cases a' <;> simp_all

theorem foldStar_antisymm (h3 : Fintype.card F % 4 = 3) (x x' : Fin 4 × F) :
    foldStar x x' = -foldStar x' x := by
  obtain ⟨a, z⟩ := x
  obtain ⟨a', z'⟩ := x'
  unfold foldStar
  have hp := phiHat_antisymm h3 z z'
  fin_cases a <;> fin_cases a' <;> simp [hp, eq_comm] <;> split_ifs <;> simp_all

theorem matchStar_antisymm (h3 : Fintype.card F % 4 = 3) (x x' : Fin 2 × F) :
    matchStar x x' = -matchStar x' x := by
  obtain ⟨a, z⟩ := x
  obtain ⟨a', z'⟩ := x'
  unfold matchStar
  have hp := phiHat_antisymm h3 z z'
  fin_cases a <;> fin_cases a' <;> simp [hp]

/-- A scaled `Φ̂` block. -/
theorem scaled_norm (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (c : ℝ) (y : F → ℝ) :
    ∑ x, (∑ x', c * phiHat x x' * y x') ^ 2 ≤ c ^ 2 * ∑ x, y x ^ 2 := by
  have h := phiHat_norm hF h3 y
  have e : ∀ x, (∑ x', c * phiHat x x' * y x') ^ 2 = c ^ 2 * (phiHat *ᵥ y) x ^ 2 := by
    intro x
    simp only [mulVec, dotProduct, mul_assoc, ← mul_sum]
    ring
  simp only [e, ← mul_sum]
  exact mul_le_mul_of_nonneg_left h (sq_nonneg c)

omit [Field F] in
/-- A scaled identity block. -/
theorem diag_norm (c : ℝ) (y : F → ℝ) :
    ∑ x, (∑ x', c * (if x = x' then 1 else 0) * y x') ^ 2 = c ^ 2 * ∑ x, y x ^ 2 := by
  have e : ∀ x, ∑ x', c * (if x = x' then (1 : ℝ) else 0) * y x' = c * y x := by
    intro x
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, sum_ite_eq, mem_univ, ↓reduceIte]
  simp only [e, mul_pow, ← mul_sum]

theorem foldStar_norm (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (a a' : Fin 4)
    (y : F → ℝ) :
    ∑ x, (∑ x', foldStar (a, x) (a', x') * y x') ^ 2 ≤ (magF a * magF a') ^ 2 * ∑ x, y x ^ 2 := by
  have hy : 0 ≤ ∑ x, y x ^ 2 := sum_nonneg fun x _ => sq_nonneg _
  have h1 := scaled_norm hF h3 1 y
  have ht := scaled_norm hF h3 tlaw y
  have hd1 := diag_norm (F := F) (tlaw - 1) y
  have hd2 := diag_norm (F := F) (1 - tlaw) y
  simp only [one_mul, one_pow] at h1
  have m0 : magF 0 = 1 := by simp [magF]
  have m1 : magF 1 = 1 := by simp [magF, armMag]
  have m2 : magF 2 = tlaw := by simp [magF, armMag, tlaw]
  have m3 : magF 3 = 1 - tlaw := by
    simp only [magF, armMag, tlaw]; norm_num
  have hz : ∑ x : F, (∑ x' : F, (0 : ℝ) * y x') ^ 2 = 0 := by simp
  unfold foldStar
  fin_cases a <;> fin_cases a' <;> simp only [Fin.isValue,
    Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.reduceEq, and_self, and_true, and_false,
    ↓reduceIte, m0, m1, m2, m3, one_mul, mul_one, one_pow] <;>
    first
      | exact h1
      | exact ht
      | (rw [hd1]; nlinarith [sq_nonneg (tlaw - 1)])
      | (rw [hd2])
      | (rw [hz]; positivity)

theorem matchStar_norm (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (a a' : Fin 2)
    (y : F → ℝ) :
    ∑ x, (∑ x', matchStar (a, x) (a', x') * y x') ^ 2 ≤ 1 ^ 2 * ∑ x, y x ^ 2 := by
  have h1 := scaled_norm hF h3 1 y
  simp only [one_mul, one_pow] at h1 ⊢
  have hy : 0 ≤ ∑ x, y x ^ 2 := sum_nonneg fun x _ => sq_nonneg _
  unfold matchStar
  fin_cases a <;> fin_cases a' <;> simp <;> first | exact h1 | positivity

end Paley

/-! ## `hdom` with the paper's stars -/

section Paper

variable {n k : ℕ} {Sb : Fin n ⊕ Fin k → Type*} [∀ b, Fintype (Sb b)]
  {Fld : ∀ b, Sb b → Type*} [∀ b p, Field (Fld b p)] [∀ b p, Fintype (Fld b p)]
  [∀ b p, DecidableEq (Fld b p)]

/-- **`hdom` for a checked diagonal envelope with the paper's signed stars** `𝖥(Φ̂_p)`, `𝖤(Φ̂_p)` on
the singleton sectors (`eq:signed-star`, (N1), (N3)): the star facts are theorems
(`foldStar_*`, `matchStar_*`); the remaining inputs are the sector maps `Ξb` with the unit tables
`CU` (`hUY`) and the kernels `hL`, `hLop` of `L_ω` and `D_ω`. -/
theorem hdom_of_table_paley {O : Fin n ⊕ Fin k → Type*} [∀ b, Fintype (O b)]
    [∀ b, DecidableEq (O b)] (hF : ∀ b p, ringChar (Fld b p) ≠ 2)
    (h3 : ∀ b p, Fintype.card (Fld b p) % 4 = 3) {Tb : EnvTable}
    (hT : tablePos Tb n k = true) (hC : maskCheck Tb n k = true) (hnk : Even (n + k))
    (Ξb : ∀ b (p : Sb b), Matrix (O b) (featLab n k b × Fld b p) ℝ)
    (CU : ∀ b, Matrix (featLab n k b × O b) (featLab n k b × O b) ℝ)
    (hUY : ∀ b, (maskT (fun b => (id : featLab n k b → featLab n k b)) CU b -
      maskT (fun b => (id : featLab n k b → featLab n k b)) (gramT Ξb) b).PosSemidef)
    (cs : (∀ b, Sb b) → ℝ) (hc0 : ∀ s, 0 ≤ cs s) (hc1 : ∀ s, cs s ≤ 1)
    {m : (∀ b, O b) → ℝ} {Lead Lop : ((∀ b, O b) → ℝ) →ₗ[ℝ] ((∀ b, O b) → ℝ)}
    (hL : ∀ x y, kern m Lead x y = (∑ s, cs s • (xiFeat Ξb s *
      starTensor (fun i p => foldStar (F := Fld (Sum.inl i) p))
        (fun j p => matchStar (F := Fld (Sum.inr j) p)) s * (xiFeat Ξb s)ᴴ)) x y)
    (hLop : ∀ x y, kern m Lop x y =
      liftMap CU (diagonal ((fun v => (featWeight Tb v : ℝ)) ∘ (featEquiv n k).symm)) x y) :
    OpLE m Lead Lop ∧ OpLE m (-Lead) Lop :=
  hdom_of_table_stars hT hC hnk Ξb CU hUY _ _
    (fun _ _ a a' x x' h => foldStar_sec a a' x x' h)
    (fun _ _ a a' x x' h => matchStar_sec a a' x x' h)
    (fun _ p a a' y => foldStar_norm (hF _ p) (h3 _ p) a a' y)
    (fun _ p a a' y => matchStar_norm (hF _ p) (h3 _ p) a a' y)
    (fun _ p x y => foldStar_antisymm (h3 _ p) x y)
    (fun _ p x y => matchStar_antisymm (h3 _ p) x y) cs hc0 hc1 hL hLop

end Paper

end Sarkozy.OpsFeature
