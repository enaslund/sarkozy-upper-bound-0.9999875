module

public import Sarkozy.NormBoundsPaper4.ECounts

@[expose] public section

/-!
# The decomposition of `Sym(K₁ − K^E_0)` on mean-zero functions (FD)

`paper/sections/21_middle_records.tex`, `lem:record:e-law`(c),(d): "`z₁ Sym K₁ = 1 + 𝖢𝖣 − δ_𝖢 −
δ_𝖣 + δ_𝖢 δ_𝖣` … Write `1 − I_× = ∑_{i,j} δ_{ij} − ε_E` … `Π_⊥ Sym(K₁ − K^E_0) Π_⊥ = 𝒮 +
(Π_⊥𝖢𝖣Π_⊥ + Π_⊥δ_𝖢δ_𝖣Π_⊥)/z₁ − Π_⊥ε_EΠ_⊥/z^E_0`, where `𝒮 = qV[J₃/z^E_0 − (E₁₀ + E₀₁)/z₁]V^*`
on mean-zero functions".

Unnormalized, for `u, v` with `∑_x [x inj] u(x) = ∑_y [y inj] v(y) = 0`
(`Nk = |eSet| = M² z₁/4`, `NL = M² z^E_0`, `M = p(p − 1)(p − 2)`):

  `chg1 K₁ K^E_0 (½, ½, 1) u v = Sraw/NL − Sc/(4 Nk) + (CHf + ZZf)/(4 Nk) − Ef/NL`,

with `Sraw = ∑_{i,j} ⟨U_i, V_j⟩` (the `δ_{ij}` of `K^E_0`), `Sc = ⟨U₁, V₀⟩ + ⟨U₀, V₁⟩` (`δ_𝖢`,
`δ_𝖣`), `CHf` the form of `𝖢𝖣`, `ZZf` that of `δ_𝖢δ_𝖣` (through NB3's pair reduction `red`),
and `Ef` that of `ε_E = I_× − (1 − ∑ δ_{ij})` (`epsE`). This is **`chg1_decomp`**.
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.NormBoundsPaper4

open Sarkozy.NormBoundsPaper3
open Sarkozy.PartV Sarkozy.Labellings Sarkozy.PartVRecords Sarkozy.MiddleComparison
open Sarkozy.NormBoundsPaper2 (off chg1 chC chH OffDiag)

variable {p : ℕ} [Fact p.Prime]

local notation "T3" => (ZMod p × ZMod p) × ZMod p

/-- `⟨f, g⟩ = ∑_t f(t) g(t)`. -/
noncomputable def ip1 (f g : ZMod p → ℝ) : ℝ := ∑ t, f t * g t

/-- `ε_E = I_× − (1 − ∑ δ_{ij})` on injective halves. -/
noncomputable def epsE (x y : T3) : ℝ := ind6 x y - ind3 x * ind3 y * (1 - coinc x y)

/-- `∑_{i,j} ⟨U_i, V_j⟩`. -/
noncomputable def Sraw (u v : T3 → ℝ) : ℝ := ∑ i, ∑ j, ip1 (Uc u i) (Uc v j)

/-- `⟨U₁, V₀⟩ + ⟨U₀, V₁⟩`. -/
noncomputable def Sc (u v : T3 → ℝ) : ℝ := ip1 (Uc u 1) (Uc v 0) + ip1 (Uc u 0) (Uc v 1)

/-- The form of `𝖢𝖣` through the pairs. -/
noncomputable def CHf (u v : T3 → ℝ) : ℝ :=
  ∑ a, ∑ b, red u a * red v b * (chC a b * chH a b)

/-- The form of `δ_𝖢 δ_𝖣` through the pairs. -/
noncomputable def ZZf (u v : T3 → ℝ) : ℝ :=
  ∑ a, ∑ b, red u a * red v b * (z0 (b.1 - a.2) * z0 (b.2 - a.1))

/-- The form of `ε_E`. -/
noncomputable def Ef (u v : T3 → ℝ) : ℝ := ∑ x, ∑ y, epsE x y * u x * v y

/-! ## Reading sums through the features -/

omit [Fact p.Prime] in
theorem crd0 (x : T3) : crd 0 x = x.1.1 := rfl
omit [Fact p.Prime] in
theorem crd1 (x : T3) : crd 1 x = x.1.2 := rfl
omit [Fact p.Prime] in
theorem crd2 (x : T3) : crd 2 x = x.2 := rfl

theorem red_pair (u : T3 → ℝ) (F : ZMod p × ZMod p → ℝ) :
    ∑ a, red u a * F a = ∑ x, ind3 x * u x * F x.1 := by
  unfold red
  rw [Fintype.sum_prod_type (f := fun x : T3 => ind3 x * u x * F x.1)]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_mul]

theorem z0_dl (a b : ZMod p) : z0 (a - b) = dl a b := by
  unfold z0 dl
  simp only [sub_eq_zero]

/-- `∑_b v̄(b) [b₀ = s] = V₀(s)`. -/
theorem red_z0_fst (v : T3 → ℝ) (s : ZMod p) :
    ∑ b, red v b * z0 (b.1 - s) = Uc v 0 s := by
  rw [red_pair v (fun b => z0 (b.1 - s))]
  unfold Uc
  refine sum_congr rfl fun y _ => ?_
  rw [z0_dl, crd0]
  ring

/-- `∑_b v̄(b) [b₁ = s] = V₁(s)`. -/
theorem red_z0_snd (v : T3 → ℝ) (s : ZMod p) :
    ∑ b, red v b * z0 (b.2 - s) = Uc v 1 s := by
  rw [red_pair v (fun b => z0 (b.2 - s))]
  unfold Uc
  refine sum_congr rfl fun y _ => ?_
  rw [z0_dl, crd1]
  ring

theorem zC_eq (u v : T3 → ℝ) :
    ∑ a, ∑ b, red u a * red v b * z0 (b.1 - a.2) = ip1 (Uc u 1) (Uc v 0) := by
  have e : ∀ a, ∑ b, red u a * red v b * z0 (b.1 - a.2) = red u a * Uc v 0 a.2 := fun a => by
    rw [← red_z0_fst v a.2, mul_sum]
    exact sum_congr rfl fun b _ => by ring
  rw [sum_congr rfl fun a _ => e a, red_pair u (fun a => Uc v 0 a.2)]
  unfold ip1
  rw [show ∑ t, Uc u 1 t * Uc v 0 t = ∑ t, Uc v 0 t * Uc u 1 t from
    sum_congr rfl fun t _ => mul_comm _ _, Uc_pair u 1 (Uc v 0)]
  exact sum_congr rfl fun x _ => by rw [crd1]; ring

theorem zD_eq (u v : T3 → ℝ) :
    ∑ a, ∑ b, red u a * red v b * z0 (b.2 - a.1) = ip1 (Uc u 0) (Uc v 1) := by
  have e : ∀ a, ∑ b, red u a * red v b * z0 (b.2 - a.1) = red u a * Uc v 1 a.1 := fun a => by
    rw [← red_z0_snd v a.1, mul_sum]
    exact sum_congr rfl fun b _ => by ring
  rw [sum_congr rfl fun a _ => e a, red_pair u (fun a => Uc v 1 a.1)]
  unfold ip1
  rw [show ∑ t, Uc u 0 t * Uc v 1 t = ∑ t, Uc v 1 t * Uc u 0 t from
    sum_congr rfl fun t _ => mul_comm _ _, Uc_pair u 0 (Uc v 1)]
  exact sum_congr rfl fun x _ => by rw [crd0]; ring

omit [Fact p.Prime] in
theorem dE_dl (a b : ZMod p) : dE a b = dl a b := by
  unfold dE dl
  by_cases h : a = b
  · simp [h]
  · simp [h]

omit [Fact p.Prime] in
theorem coinc_eq (x y : T3) : coinc x y = ∑ i, ∑ j, dl (crd i x) (crd j y) := by
  unfold coinc
  simp only [dE_dl, Fin.sum_univ_three, crd0, crd1, crd2]
  ring

theorem coinc_form (u v : T3 → ℝ) :
    ∑ x, ∑ y, ind3 x * ind3 y * coinc x y * u x * v y = Sraw u v := by
  unfold Sraw
  have e : ∀ x y, ind3 x * ind3 y * coinc x y * u x * v y =
      ∑ i, ∑ j, ind3 x * u x * (ind3 y * dl (crd j y) (crd i x) * v y) := fun x y => by
    rw [coinc_eq]
    simp only [mul_sum, sum_mul]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    have : dl (crd i x) (crd j y) = dl (crd j y) (crd i x) := by
      unfold dl; split_ifs <;> simp_all
    rw [this]
    ring
  simp only [e]
  rw [sum_comm]
  have e2 : ∀ y, ∑ x, ∑ i, ∑ j, ind3 x * u x * (ind3 y * dl (crd j y) (crd i x) * v y) =
      ∑ i, ∑ j, ∑ x, ind3 x * u x * (ind3 y * dl (crd j y) (crd i x) * v y) := fun y => by
    rw [sum_comm]
    exact sum_congr rfl fun i _ => sum_comm
  rw [sum_congr rfl fun y _ => e2 y, sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_comm]
  have e3 : ∀ x, ∑ y, ind3 x * u x * (ind3 y * dl (crd j y) (crd i x) * v y) =
      ind3 x * u x * Uc v j (crd i x) := fun x => by
    unfold Uc; rw [mul_sum]
  rw [sum_congr rfl fun x _ => e3 x]
  unfold ip1
  rw [show ∑ t, Uc u i t * Uc v j t = ∑ t, Uc v j t * Uc u i t from
    sum_congr rfl fun t _ => mul_comm _ _, Uc_pair u i (Uc v j)]
  exact sum_congr rfl fun x _ => by ring

/-! ## The decomposition -/

/-- **`lem:record:e-law`(c),(d) on mean-zero functions**, unnormalized. -/
theorem chg1_decomp (hE : (eSet (F := ZMod p)).Nonempty)
    (hne : (injLabellings (ZMod p) (matchGraph (Fin 2))).Nonempty) (h3 : p % 4 = 3)
    (u v : T3 → ℝ) (hu : ∑ x, ind3 x * u x = 0) (hv : ∑ x, ind3 x * v x = 0) :
    chg1 (P3 hE) (C0 hne) (1 / 2) (1 / 2) 1 u v =
      Sraw u v / NL (p := p) - Sc u v / (4 * Nk (p := p)) +
        (CHf u v + ZZf u v) / (4 * Nk (p := p)) - Ef u v / NL (p := p) := by
  have hNk := Nk_pos (p := p) hE
  have hNL := NL_pos hne
  -- the `K₁` part
  have hsu : ∑ a, red u a = 0 := by rw [red_sum, hu]
  have hsv : ∑ a, red v a = 0 := by rw [red_sum, hv]
  have hP : 1 / 2 * (u ⬝ᵥ (P3 hE *ᵥ v)) + 1 / 2 * (v ⬝ᵥ (P3 hE *ᵥ u)) =
      (CHf u v + ZZf u v - Sc u v) / (4 * Nk (p := p)) := by
    rw [form_red, form_red]
    have hswap : ∑ a, ∑ b, red v a * g2 a b * red u b = ∑ a, ∑ b, red u a * red v b * g2 b a := by
      rw [sum_comm]
      exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
    have hsym : ∑ a, ∑ b, red u a * g2 a b * red v b + ∑ a, ∑ b, red u a * red v b * g2 b a =
        ∑ a, ∑ b, red u a * red v b * ((1 - z0 (b.1 - a.2) - z0 (b.2 - a.1) +
          z0 (b.1 - a.2) * z0 (b.2 - a.1) + chC a b * chH a b) / 2) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun a _ => ?_
      rw [← sum_add_distrib]
      refine sum_congr rfl fun b _ => ?_
      rw [← g2_sym h3]
      ring
    have hone : ∑ a, ∑ b, red u a * red v b = 0 := by
      simp only [← mul_sum, hsv, mul_zero, sum_const_zero]
    have hexp : ∑ a, ∑ b, red u a * red v b * ((1 - z0 (b.1 - a.2) - z0 (b.2 - a.1) +
          z0 (b.1 - a.2) * z0 (b.2 - a.1) + chC a b * chH a b) / 2) =
        (∑ a, ∑ b, red u a * red v b -
          ∑ a, ∑ b, red u a * red v b * z0 (b.1 - a.2) -
          ∑ a, ∑ b, red u a * red v b * z0 (b.2 - a.1) + ZZf u v + CHf u v) / 2 := by
      unfold ZZf CHf
      simp only [← sum_sub_distrib, ← sum_add_distrib, sum_div]
      refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
      ring
    rw [hswap]
    have : 1 / 2 * (1 / Nk (p := p) * ∑ a, ∑ b, red u a * g2 a b * red v b) +
        1 / 2 * (1 / Nk (p := p) * ∑ a, ∑ b, red u a * red v b * g2 b a) =
        1 / (2 * Nk (p := p)) * (∑ a, ∑ b, red u a * g2 a b * red v b +
          ∑ a, ∑ b, red u a * red v b * g2 b a) := by
      field_simp
    rw [this, hsym, hexp, hone, zC_eq, zD_eq]
    unfold Sc
    field_simp
    ring
  -- the `K^E_0` part
  have hC : u ⬝ᵥ (C0 hne *ᵥ v) = (Ef u v - Sraw u v) / NL (p := p) := by
    have e1 : u ⬝ᵥ (C0 hne *ᵥ v) = (∑ x, ∑ y, ind6 x y * u x * v y) / NL (p := p) := by
      simp only [dotProduct, Matrix.mulVec, C0_eq, mul_sum, sum_div]
      exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring
    have e2 : ∑ x, ∑ y, ind6 x y * u x * v y = Ef u v +
        ∑ x, ∑ y, ind3 x * ind3 y * u x * v y -
          ∑ x, ∑ y, ind3 x * ind3 y * coinc x y * u x * v y := by
      unfold Ef epsE
      simp only [← sum_add_distrib, ← sum_sub_distrib]
      refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
      ring
    have e3 : ∑ x, ∑ y, ind3 x * ind3 y * u x * v y = 0 := by
      have : ∀ x, ∑ y, ind3 x * ind3 y * u x * v y = ind3 x * u x * ∑ y, ind3 y * v y := fun x => by
        rw [mul_sum]; exact sum_congr rfl fun y _ => by ring
      simp only [this, hv, mul_zero, sum_const_zero]
    rw [e1, e2, e3, coinc_form]
    ring
  unfold chg1
  rw [hP, hC]
  ring

end Sarkozy.NormBoundsPaper4
