module

public import Sarkozy.Comparison.Recentering
public import Sarkozy.Labellings.Extension
public import Sarkozy.PartV.BlockLaw
public import Mathlib.Data.Fintype.Powerset

/-!
# `lem:upper-stars`: star terms in the one-way replacements (partial)

`paper/sections/26_upper_comparison.tex`, `lem:upper-stars`. The new law `π^new = λ_p(G^new)`
of a one-way replacement has the density `K₀/Z₀` relative to `λ_H ⊗ λ_H`, where
`K₀ = 1{distinct} ∏_{(u,v) ∈ 𝐃} (1 + 𝐃_{uv} χ(y_v - x_u))` is expanded over the subsets of the
cross graph `𝐃`.

**Proved here.**
* **Step 1, the supports** (`pairwise_meeting`, `exists_disjoint_edges`, `rectangle_edge`): if
  every vertex has cross degree at most two, a nonempty set of cross edges any two of which meet
  is a single edge or a two-star (two edges with a common vertex); every other nonempty set
  contains two disjoint edges `(u, v), (u', v')`, and if `𝐃` has no `4`-cycle at most one of
  `(u, v')`, `(u', v)` is an edge.
* **The two cross graphs of the ten records** (`twoPaths`, `sixStars`, as abstract models: two
  disjoint three-edge paths, and six disjoint two-edge stars with all centres in `X`):
  `(N₁, N₂, N_*) = (6, 4, 53)`, `N_X = N_Y = 2` (`twoPaths_counts`), and
  `N₁ = 12`, `N_X = 6`, `N_Y = 0`, `N_* = 2¹² - 1 - 12 - 6 = 4077` (`sixStars_counts`), with the
  numbers of pairwise meeting subsets counted directly; `twoPaths_gram`, `sixStars_gram`: the
  Gram matrices `𝐃ᵀ𝐃` satisfy `G² - 3G + I = 0` on each path (eigenvalues `φ^{±2}`, so
  `‖𝐃‖ = (1 + √5)/2`) and `𝐃𝐃ᵀ = 2I` (`‖𝐃‖ = √2`).
* **Step 6, the normalizer** (`upper_stars_Z`): `|Z₀ - 1| ≤ (N₂ + N_*κ_pr + C_col) q = 1 - Z_-`
  from the means of the pieces.
* **Step 6, the correlation** (`upper_stars_correlation`, and `upper_stars_a`,
  `upper_stars_b`): from `lem:recentering`(b) (`Recentering.recentering_bound`) and the density
  conversion (`Recentering.norm_le_of_density_ge`), a centred bound `c` and constant couplings
  `M` of the kernel give the maximal correlation `e^ℓ(c/Z_- + (M/Z_-)²)` of `π^new`; with
  `c = M = b_raw` this is (a), `e^ℓ(ξ₀ + ξ₀²)`, and with `c = b + 𝓡`, `M = 𝓡` it is (b),
  `e^ℓ(ξ + ξ₁²)`.
* **(d), the targets, in full** (`upper_stars_d`): `‖u‖²_{L²(π_X)} ≤ e^ℓ(ε_old + ξ₁)²`.
* **Step 2 on the uniform law** (`paley_norm`): `‖𝒫‖ ≤ r` for the Paley operator
  `𝒫h(a) = E_b χ(b - a)h(b)` (`𝒫𝒫^* = q(I - J)`, two-root identity).
* **Step 0, the pair density** (`graphLaw_pair_le`, `graphLaw_pair_density`, with
  `card_squares`): two distinct coordinates of a graph law have pair density at most
  `2/(1 - q)` against the uniform law, by the square-affine invariance.
* **Step 3, the two-stars** (`sum_chi_chi`, `twoStar_gram`, `twoStar_adjoint_norm`,
  `twoStar_norm`, `twoStar_norm_density`): by the two-root identity, the pair Gram of a two-star
  kernel `χ(b - a)χ(b' - a)` is `(1{a = a'} - q)²`, so `‖𝒦_u‖² ≤ q(1 - q) ≤ q`; on a leaf law
  with density at most `c` (Step 0: `c = 2/(1 - q)`), `‖𝒦‖² ≤ c q`.
* **Step 5, the coincidences, in full** (`coincidence_bound`, with Schur's test `schur_kernel`;
  `coincidence_bound_graphLaw` for the half laws `λ_H`, whose coordinates are uniform by V1's
  `graphLaw_vertex_uniform`): from `0 ≤ K_col ≤ 2^{m_×} ∑_{i,j} 1{x_i = y_j}`,
  `‖K_col‖ ≤ C_col q` and `0 ≤ E K_col ≤ C_col q`, `C_col = n² 2^{m_×}`.

**Not formalized** (hypotheses of the assembly theorems): Step 2 beyond the uniform law (the
identity `𝒮_e = Φ(𝐃 ⊗ 𝒫)Φ*` and `‖𝒮_e‖ ≤ Γ‖𝐃‖r`); Step 0 beyond the pair density and the
uniform coordinates (the embedding bound `γ ⪯ Φ*Φ ⪯ Γ` of `prop:middle-negative` that gives
`b_all`); Step 4 (the other supports `≤ κ_pr q`, from `lem:extension`(c) and
`lem:matching:kernel`(a)); the passage from the two-star kernels on the leaf pairs to the
operators on the half labellings (the conditional expectations `Φ*_{ww'}`); part (c) (Step 7,
`lem:general-star`(a),(d)). The two cross graphs are models; identifying them with the new
cross edges of the LR and RL records is not done here.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.UpperReference.UpperStars

open Sarkozy Sarkozy.Recentering

/-! ## Step 1: the supports -/

section Supports

variable {X Y : Type*} [DecidableEq X] [DecidableEq Y]

/-- **Step 1**: if every vertex has cross degree at most two, a nonempty set `S` of cross edges
in which any two edges meet is a single edge or a two-star (two edges with a common vertex). -/
theorem pairwise_meeting (Dset : Finset (X × Y))
    (hdegX : ∀ x, (Dset.filter fun e => e.1 = x).card ≤ 2)
    (hdegY : ∀ y, (Dset.filter fun e => e.2 = y).card ≤ 2) (S : Finset (X × Y))
    (hS : S ⊆ Dset) (hne : S.Nonempty) (hmeet : ∀ e ∈ S, ∀ e' ∈ S, e.1 = e'.1 ∨ e.2 = e'.2) :
    S.card = 1 ∨
      (S.card = 2 ∧ ((∃ x, ∀ e ∈ S, e.1 = x) ∨ ∃ y, ∀ e ∈ S, e.2 = y)) := by
  obtain ⟨e₀, he₀⟩ := hne
  -- all edges share the first or the second vertex of `e₀`
  have hcommon : (∀ e ∈ S, e.1 = e₀.1) ∨ ∀ e ∈ S, e.2 = e₀.2 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨e₁, he₁, h₁⟩, ⟨e₂, he₂, h₂⟩⟩ := hcon
    have h₁' : e₁.2 = e₀.2 := by
      rcases hmeet e₁ he₁ e₀ he₀ with h | h
      · exact absurd h h₁
      · exact h
    have h₂' : e₂.1 = e₀.1 := by
      rcases hmeet e₂ he₂ e₀ he₀ with h | h
      · exact h
      · exact absurd h h₂
    rcases hmeet e₁ he₁ e₂ he₂ with h | h
    · exact h₁ (h.trans h₂')
    · exact h₂ (h₁'.symm.trans h).symm
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨e₀, he₀⟩
  rcases hcommon with h | h
  · have hle : S.card ≤ 2 := by
      refine le_trans (Finset.card_le_card fun e he => ?_) (hdegX e₀.1)
      rw [Finset.mem_filter]
      exact ⟨hS he, h e he⟩
    rcases (by omega : S.card = 1 ∨ S.card = 2) with h1 | h2
    · exact Or.inl h1
    · exact Or.inr ⟨h2, Or.inl ⟨e₀.1, h⟩⟩
  · have hle : S.card ≤ 2 := by
      refine le_trans (Finset.card_le_card fun e he => ?_) (hdegY e₀.2)
      rw [Finset.mem_filter]
      exact ⟨hS he, h e he⟩
    rcases (by omega : S.card = 1 ∨ S.card = 2) with h1 | h2
    · exact Or.inl h1
    · exact Or.inr ⟨h2, Or.inr ⟨e₀.2, h⟩⟩

omit [DecidableEq X] [DecidableEq Y] in
/-- **Step 1**: a set of cross edges that is not pairwise meeting contains two disjoint edges. -/
theorem exists_disjoint_edges (S : Finset (X × Y))
    (h : ¬ ∀ e ∈ S, ∀ e' ∈ S, e.1 = e'.1 ∨ e.2 = e'.2) :
    ∃ e ∈ S, ∃ e' ∈ S, e.1 ≠ e'.1 ∧ e.2 ≠ e'.2 := by
  push Not at h
  exact h

/-- **Step 1**: for two disjoint edges `(u, v), (u', v')` of a cross graph without `4`-cycles, at
most one of the rectangle pairs `(u, v')`, `(u', v)` is an edge. -/
theorem rectangle_edge (Dset : Finset (X × Y))
    (hC4 : ∀ u u' v v', u ≠ u' → v ≠ v' → (u, v) ∈ Dset → (u', v') ∈ Dset → (u, v') ∈ Dset →
      (u', v) ∈ Dset → False)
    {u u' : X} {v v' : Y} (hu : u ≠ u') (hv : v ≠ v') (h1 : (u, v) ∈ Dset)
    (h2 : (u', v') ∈ Dset) : (u, v') ∉ Dset ∨ (u', v) ∉ Dset := by
  by_contra hcon
  push Not at hcon
  exact hC4 u u' v v' hu hv h1 h2 hcon.1 hcon.2

end Supports

/-! ## The two cross graphs of the ten records -/

/-- Pairwise meeting, as a Boolean test on a finite set of cross edges. -/
def meets {X Y : Type*} [DecidableEq X] [DecidableEq Y] (S : Finset (X × Y)) : Prop :=
  ∀ e ∈ S, ∀ e' ∈ S, e.1 = e'.1 ∨ e.2 = e'.2

instance {X Y : Type*} [DecidableEq X] [DecidableEq Y] (S : Finset (X × Y)) :
    Decidable (meets S) := by
  unfold meets
  infer_instance

/-- **The cross graph of the six LR records** (model): two disjoint three-edge paths
`x₀ - y₀ - x₁ - y₁` and `x₂ - y₂ - x₃ - y₃`, all edges from `X` to `Y`. -/
def twoPaths : Finset (Fin 4 × Fin 4) := {(0, 0), (1, 0), (1, 1), (2, 2), (3, 2), (3, 3)}

/-- **The counts of the LR cross graph**: `N₁ = m_× = 6`, `N_X = N_Y = 2` vertices of cross
degree two, `N₂ = N_X + N_Y = 4` nonempty pairwise meeting sets of two edges, and
`N_* = 2⁶ - 1 - N₁ - N₂ = 53` nonempty sets that are not pairwise meeting. -/
theorem twoPaths_counts :
    twoPaths.card = 6 ∧
    (univ.filter fun x : Fin 4 => (twoPaths.filter fun e => e.1 = x).card = 2).card = 2 ∧
    (univ.filter fun y : Fin 4 => (twoPaths.filter fun e => e.2 = y).card = 2).card = 2 ∧
    (twoPaths.powerset.filter fun S => S.Nonempty ∧ meets S).card = 6 + 4 ∧
    (twoPaths.powerset.filter fun S => S.Nonempty ∧ ¬ meets S).card = 53 ∧
    2 ^ 6 - 1 - 6 - 4 = 53 := by
  decide +kernel

/-- **The cross graph of the four nonaccepting RL records** (model): six disjoint two-edge
stars with all centres in `X`. -/
def sixStars : Finset (Fin 6 × Fin 12) :=
  univ.biUnion fun i : Fin 6 => {(i, ⟨2 * i.1, by omega⟩), (i, ⟨2 * i.1 + 1, by omega⟩)}

/-- **The counts of the RL cross graph**: `N₁ = 12`, `N_X = 6`, `N_Y = 0`, `N₂ = 6`, and
`N_* = 2¹² - 1 - 12 - 6 = 4077`. -/
theorem sixStars_counts :
    sixStars.card = 12 ∧
    (univ.filter fun x : Fin 6 => (sixStars.filter fun e => e.1 = x).card = 2).card = 6 ∧
    (univ.filter fun y : Fin 12 => (sixStars.filter fun e => e.2 = y).card = 2).card = 0 ∧
    (∀ x, (sixStars.filter fun e => e.1 = x).card ≤ 2) ∧
    (∀ y, (sixStars.filter fun e => e.2 = y).card ≤ 2) ∧
    2 ^ 12 - 1 - 12 - 6 = 4077 := by
  decide +kernel

/-- The degrees of the LR cross graph are at most two, and it has no `4`-cycle. -/
theorem twoPaths_hyp :
    (∀ x, (twoPaths.filter fun e => e.1 = x).card ≤ 2) ∧
    (∀ y, (twoPaths.filter fun e => e.2 = y).card ≤ 2) ∧
    (∀ u u' v v', u ≠ u' → v ≠ v' → (u, v) ∈ twoPaths → (u', v') ∈ twoPaths →
      (u, v') ∈ twoPaths → (u', v) ∈ twoPaths → False) := by
  decide +kernel

/-- The incidence matrix of one three-edge path `x₀ - y₀ - x₁ - y₁`. -/
def pathD : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 1, 1]

/-- **`‖𝐃‖ = (1 + √5)/2` for the LR records**: on each path `G = 𝐃ᵀ𝐃` satisfies
`G² - 3G + I = 0`, so its eigenvalues are `(3 ± √5)/2 = φ^{±2}` and `‖𝐃‖ = φ = (1 + √5)/2`. -/
theorem twoPaths_gram :
    (pathD.transpose * pathD) * (pathD.transpose * pathD) - 3 • (pathD.transpose * pathD) + 1 =
      0 := by
  decide +kernel

/-- **`‖𝐃‖ = √2` for the RL records**: on each two-edge star `𝐃𝐃ᵀ = 2`. -/
theorem sixStars_gram :
    (!![1, 1] : Matrix (Fin 1) (Fin 2) ℤ) * (!![1, 1] : Matrix (Fin 1) (Fin 2) ℤ).transpose =
      !![2] := by
  decide +kernel

/-! ## Step 6: the normalizer and the correlation -/

/-- **Step 6, the normalizer**: `Z₀ = 1 - q ∑_S 𝐃_S + E(𝓡_* - K_col)` with `|∑_S 𝐃_S| ≤ N₂` (the
signs have modulus one), `|E 𝓡_*| ≤ N_* κ_pr q` and `0 ≤ E K_col ≤ C_col q` gives
`|Z₀ - 1| ≤ (N₂ + N_* κ_pr + C_col) q = 1 - Z_-`. -/
theorem upper_stars_Z {Z₀ q sD eR eC N₂ Nst κ Ccol : ℝ} (hq : 0 ≤ q)
    (hZ : Z₀ = 1 - q * sD + (eR - eC)) (hsD : |sD| ≤ N₂) (heR : |eR| ≤ Nst * κ * q)
    (heC0 : 0 ≤ eC) (heC : eC ≤ Ccol * q) :
    |Z₀ - 1| ≤ (N₂ + Nst * κ + Ccol) * q := by
  rw [hZ]
  have h1 : |q * sD| ≤ N₂ * q := by
    rw [abs_mul, abs_of_nonneg hq, mul_comm]
    exact mul_le_mul_of_nonneg_right hsD hq
  have e : 1 - q * sD + (eR - eC) - 1 = -(q * sD) + eR - eC := by ring
  rw [e]
  have h2 := abs_add_three (-(q * sD)) eR (-eC)
  rw [abs_neg, abs_neg, abs_of_nonneg heC0] at h2
  have e2 : -(q * sD) + eR - eC = -(q * sD) + eR + -eC := by ring
  rw [e2]
  nlinarith

variable {Ω : Type*} [Fintype Ω]

/-- **Step 6, the correlation of `π^new`** (`lem:recentering`(b)). Let `𝔟(f, h) = ⟨f, K₀ h⟩/Z₀`
be the form of `π^new` relative to `λ_H ⊗ λ_H` (`𝔟(1, 1) = 1`), with marginal densities `ρ_L`,
`ρ_R` (`𝔟(f, 1) = ⟨f, ρ_L⟩`, `𝔟(1, h) = ⟨ρ_R, h⟩`), and suppose `Z₀ ≥ Z_- > 0`,
`‖P₀K₀P₀‖ ≤ c`, `‖ρ_L - 1‖, ‖ρ_R - 1‖ ≤ M/Z₀` (that is `‖P₀K₀1‖, ‖P₀K₀*1‖ ≤ M`) and
`ρ_L, ρ_R ≥ e^{-ℓ}`. Then for `f`, `h` centred under the marginals of `π^new`,
`|𝔟(f, h)| ≤ e^ℓ (c/Z_- + (M/Z_-)²) ‖f‖_{π_X} ‖h‖_{π_Y}`. -/
theorem upper_stars_correlation (μ : FiniteLaw Ω) (𝔟 : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) →ₗ[ℝ] ℝ)
    (ρL ρR : Ω → ℝ) (h11 : 𝔟 (fun _ => 1) (fun _ => 1) = 1)
    (hL : ∀ f, 𝔟 f (fun _ => 1) = ip μ f ρL) (hR : ∀ h, 𝔟 (fun _ => 1) h = ip μ ρR h)
    {Z₀ Zm c M ℓ : ℝ} (hZm : 0 < Zm) (hZ : Zm ≤ Z₀) (hc : 0 ≤ c) (hM : 0 ≤ M)
    (hcen : ∀ f h, |𝔟 (center μ f) (center μ h)| ≤
      c / Z₀ * nrm μ (center μ f) * nrm μ (center μ h))
    (hmL : nrm μ (fun x => ρL x - 1) ≤ M / Z₀) (hmR : nrm μ (fun y => ρR y - 1) ≤ M / Z₀)
    (hρL : ∀ x, Real.exp (-ℓ) ≤ ρL x) (hρR : ∀ y, Real.exp (-ℓ) ≤ ρR y)
    {f h : Ω → ℝ} (hf : ip μ f ρL = 0) (hh : ip μ ρR h = 0) :
    |𝔟 f h| ≤ Real.exp ℓ * (c / Zm + (M / Zm) ^ 2) *
      √(μ.expect (fun x => ρL x * f x ^ 2)) * √(μ.expect (fun y => ρR y * h y ^ 2)) := by
  have hZ0 : 0 < Z₀ := lt_of_lt_of_le hZm hZ
  have hb := recentering_bound μ μ 𝔟 ρL ρR h11 hL hR (div_nonneg hc hZ0.le) hcen hmL hmR hf hh
  have hcZ : c / Z₀ ≤ c / Zm := div_le_div_of_nonneg_left hc hZm hZ
  have hMZ : M / Z₀ ≤ M / Zm := div_le_div_of_nonneg_left hM hZm hZ
  have hconst : c / Z₀ + M / Z₀ * (M / Z₀) ≤ c / Zm + (M / Zm) ^ 2 := by
    have := mul_le_mul hMZ hMZ (div_nonneg hM hZ0.le) (div_nonneg hM hZm.le)
    nlinarith
  have hnf := norm_le_of_density_ge μ ρL hρL f
  have hnh := norm_le_of_density_ge μ ρR hρR h
  have hnf0 : 0 ≤ nrm μ f := Real.sqrt_nonneg _
  have hnh0 : 0 ≤ nrm μ h := Real.sqrt_nonneg _
  have hK : 0 ≤ c / Zm + (M / Zm) ^ 2 := by positivity
  calc |𝔟 f h| ≤ (c / Z₀ + M / Z₀ * (M / Z₀)) * nrm μ f * nrm μ h := hb
    _ ≤ (c / Zm + (M / Zm) ^ 2) * nrm μ f * nrm μ h := by
        have := mul_le_mul_of_nonneg_right hconst hnf0
        exact mul_le_mul_of_nonneg_right this hnh0
    _ ≤ (c / Zm + (M / Zm) ^ 2) *
          (Real.exp (ℓ / 2) * √(μ.expect (fun x => ρL x * f x ^ 2))) *
          (Real.exp (ℓ / 2) * √(μ.expect (fun y => ρR y * h y ^ 2))) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hnf hK) hnh hnh0
        exact mul_nonneg hK (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))
    _ = Real.exp ℓ * (c / Zm + (M / Zm) ^ 2) *
          √(μ.expect (fun x => ρL x * f x ^ 2)) * √(μ.expect (fun y => ρR y * h y ^ 2)) := by
        have : Real.exp ℓ = Real.exp (ℓ / 2) * Real.exp (ℓ / 2) := by
          rw [← Real.exp_add]
          ring_nf
        rw [this]
        ring

/-- **`lem:upper-stars`(a), forest stars**: with `‖K₀ - 1 ⊗ 1‖ ≤ b_raw` (so `c = M = b_raw`), the
centred conditional operator of `π^new` has norm at most `e^ℓ(ξ₀ + ξ₀²)`, `ξ₀ = b_raw/Z_-`. -/
theorem upper_stars_a (μ : FiniteLaw Ω) (𝔟 : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) →ₗ[ℝ] ℝ)
    (ρL ρR : Ω → ℝ) (h11 : 𝔟 (fun _ => 1) (fun _ => 1) = 1)
    (hL : ∀ f, 𝔟 f (fun _ => 1) = ip μ f ρL) (hR : ∀ h, 𝔟 (fun _ => 1) h = ip μ ρR h)
    {Z₀ Zm braw ℓ : ℝ} (hZm : 0 < Zm) (hZ : Zm ≤ Z₀) (hb : 0 ≤ braw)
    (hcen : ∀ f h, |𝔟 (center μ f) (center μ h)| ≤
      braw / Z₀ * nrm μ (center μ f) * nrm μ (center μ h))
    (hmL : nrm μ (fun x => ρL x - 1) ≤ braw / Z₀) (hmR : nrm μ (fun y => ρR y - 1) ≤ braw / Z₀)
    (hρL : ∀ x, Real.exp (-ℓ) ≤ ρL x) (hρR : ∀ y, Real.exp (-ℓ) ≤ ρR y)
    {f h : Ω → ℝ} (hf : ip μ f ρL = 0) (hh : ip μ ρR h = 0) :
    |𝔟 f h| ≤ Real.exp ℓ * (braw / Zm + (braw / Zm) ^ 2) *
      √(μ.expect (fun x => ρL x * f x ^ 2)) * √(μ.expect (fun y => ρR y * h y ^ 2)) :=
  upper_stars_correlation μ 𝔟 ρL ρR h11 hL hR hZm hZ hb hb hcen hmL hmR hρL hρR hf hh

/-- **`lem:upper-stars`(b), joint stars**: with `‖P₀K₀P₀‖ ≤ b + 𝓡` (`b` a bound for the centred
star operator `𝒮^c`, e.g. `b_all`) and `‖P₀K₀1‖, ‖P₀K₀*1‖ ≤ 𝓡`, the centred conditional operator
of `π^new` has norm at most `e^ℓ(ξ + ξ₁²)`, `ξ = (b + 𝓡)/Z_-`, `ξ₁ = 𝓡/Z_-`. -/
theorem upper_stars_b (μ : FiniteLaw Ω) (𝔟 : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) →ₗ[ℝ] ℝ)
    (ρL ρR : Ω → ℝ) (h11 : 𝔟 (fun _ => 1) (fun _ => 1) = 1)
    (hL : ∀ f, 𝔟 f (fun _ => 1) = ip μ f ρL) (hR : ∀ h, 𝔟 (fun _ => 1) h = ip μ ρR h)
    {Z₀ Zm b RR ℓ : ℝ} (hZm : 0 < Zm) (hZ : Zm ≤ Z₀) (hb : 0 ≤ b) (hRR : 0 ≤ RR)
    (hcen : ∀ f h, |𝔟 (center μ f) (center μ h)| ≤
      (b + RR) / Z₀ * nrm μ (center μ f) * nrm μ (center μ h))
    (hmL : nrm μ (fun x => ρL x - 1) ≤ RR / Z₀) (hmR : nrm μ (fun y => ρR y - 1) ≤ RR / Z₀)
    (hρL : ∀ x, Real.exp (-ℓ) ≤ ρL x) (hρR : ∀ y, Real.exp (-ℓ) ≤ ρR y)
    {f h : Ω → ℝ} (hf : ip μ f ρL = 0) (hh : ip μ ρR h = 0) :
    |𝔟 f h| ≤ Real.exp ℓ * ((b + RR) / Zm + (RR / Zm) ^ 2) *
      √(μ.expect (fun x => ρL x * f x ^ 2)) * √(μ.expect (fun y => ρR y * h y ^ 2)) :=
  upper_stars_correlation μ 𝔟 ρL ρR h11 hL hR hZm hZ (add_nonneg hb hRR) hRR hcen hmL hmR hρL
    hρR hf hh

/-! ## (d): the targets -/

/-- `‖f - g‖ ≤ ‖f‖ + ‖g‖` in `L²(μ)`. -/
theorem nrm_sub_le (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    nrm μ (fun x => f x - g x) ≤ nrm μ f + nrm μ g := by
  have hf0 : 0 ≤ nrm μ f := Real.sqrt_nonneg _
  have hg0 : 0 ≤ nrm μ g := Real.sqrt_nonneg _
  have hsq : ip μ (fun x => f x - g x) (fun x => f x - g x) ≤ (nrm μ f + nrm μ g) ^ 2 := by
    have e : ip μ (fun x => f x - g x) (fun x => f x - g x) =
        ip μ f f - 2 * ip μ f g + ip μ g g := by
      unfold ip
      rw [← μ.expect_const_mul, ← μ.expect_sub, ← μ.expect_add]
      exact μ.expect_congr fun x => by ring
    have hff : ip μ f f = nrm μ f ^ 2 := by
      unfold nrm
      rw [Real.sq_sqrt]
      unfold ip
      exact μ.expect_nonneg fun x => mul_self_nonneg _
    have hgg : ip μ g g = nrm μ g ^ 2 := by
      unfold nrm
      rw [Real.sq_sqrt]
      unfold ip
      exact μ.expect_nonneg fun x => mul_self_nonneg _
    have hfg := abs_ip_le μ f g
    rw [e, hff, hgg]
    nlinarith [neg_abs_le (ip μ f g)]
  unfold nrm
  calc √(ip μ (fun x => f x - g x) (fun x => f x - g x)) ≤ √((nrm μ f + nrm μ g) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = nrm μ f + nrm μ g := Real.sqrt_sq (add_nonneg hf0 hg0)

/-- **`lem:upper-stars`(d), the targets.** Let `dμ^old/dλ_H = 1 + w_old` with
`‖w_old‖_{L²(λ_H)} ≤ ε_old`, and `dπ^new_X/dλ_H = 1 + w_new` with `‖w_new‖ ≤ ξ₁` (Step 6) and
`1 + w_new ≥ e^{-ℓ}`. Then `u = dμ^old/dπ^new_X - 1` satisfies
`‖u‖²_{L²(π^new_X)} = E_λ[(1 + w_new) u²] ≤ e^ℓ (ε_old + ξ₁)²`; no change of reference and no
normalizer is involved. (The same holds for `v` and `π^new_Y`.) -/
theorem upper_stars_d (μ : FiniteLaw Ω) (wold wnew : Ω → ℝ) {εold ξ₁ ℓ : ℝ}
    (hold : nrm μ wold ≤ εold) (hnew : nrm μ wnew ≤ ξ₁)
    (hdens : ∀ x, Real.exp (-ℓ) ≤ 1 + wnew x) :
    μ.expect (fun x => (1 + wnew x) * ((1 + wold x) / (1 + wnew x) - 1) ^ 2) ≤
      Real.exp ℓ * (εold + ξ₁) ^ 2 := by
  have hpos : ∀ x, 0 < 1 + wnew x := fun x => lt_of_lt_of_le (Real.exp_pos _) (hdens x)
  -- pointwise: `(1 + w_new) u² = (w_old - w_new)²/(1 + w_new) ≤ e^ℓ (w_old - w_new)²`
  have hpt : ∀ x, (1 + wnew x) * ((1 + wold x) / (1 + wnew x) - 1) ^ 2 ≤
      Real.exp ℓ * ((wold x - wnew x) * (wold x - wnew x)) := by
    intro x
    have hp := hpos x
    have e : (1 + wnew x) * ((1 + wold x) / (1 + wnew x) - 1) ^ 2 =
        (wold x - wnew x) ^ 2 / (1 + wnew x) := by
      field_simp
      ring
    rw [e]
    have h1 : 1 ≤ Real.exp ℓ * (1 + wnew x) := by
      have := mul_le_mul_of_nonneg_left (hdens x) (Real.exp_pos ℓ).le
      rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at this
    rw [div_le_iff₀ hp]
    nlinarith [sq_nonneg (wold x - wnew x)]
  have hsum := μ.expect_mono hpt
  rw [μ.expect_const_mul] at hsum
  have hn := nrm_sub_le μ wold wnew
  have hip : ip μ (fun x => wold x - wnew x) (fun x => wold x - wnew x) ≤ (εold + ξ₁) ^ 2 := by
    have h0 : 0 ≤ nrm μ (fun x => wold x - wnew x) := Real.sqrt_nonneg _
    have hsq : nrm μ (fun x => wold x - wnew x) ^ 2 =
        ip μ (fun x => wold x - wnew x) (fun x => wold x - wnew x) := by
      unfold nrm
      rw [Real.sq_sqrt]
      unfold ip
      exact μ.expect_nonneg fun x => mul_self_nonneg _
    rw [← hsq]
    exact pow_le_pow_left₀ h0 (hn.trans (add_le_add hold hnew)) 2
  calc μ.expect (fun x => (1 + wnew x) * ((1 + wold x) / (1 + wnew x) - 1) ^ 2) ≤
        Real.exp ℓ * μ.expect (fun x => (wold x - wnew x) * (wold x - wnew x)) := hsum
    _ ≤ Real.exp ℓ * (εold + ξ₁) ^ 2 := mul_le_mul_of_nonneg_left hip (Real.exp_pos ℓ).le

/-! ## Step 5: the coincidences -/

section Coincidences

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- **Schur's test for a kernel on two finite laws**: if `K ≥ 0`, `E_y K(x, y) ≤ ρ` for every `x`
and `E_x K(x, y) ≤ γ` for every `y`, then `|E_{x,y} f(x)K(x, y)g(y)| ≤ √(ργ) ‖f‖_μ ‖g‖_ν`. -/
theorem schur_kernel (μ : FiniteLaw X) (ν : FiniteLaw Y) (K : X → Y → ℝ)
    (hK : ∀ x y, 0 ≤ K x y) {ρ γ : ℝ} (hρ : ∀ x, ν.expect (K x) ≤ ρ)
    (hγ : ∀ y, μ.expect (fun x => K x y) ≤ γ) (f : X → ℝ) (g : Y → ℝ) :
    |μ.expect (fun x => ν.expect (fun y => f x * K x y * g y))| ≤
      √(ρ * γ) * nrm μ f * nrm ν g := by
  set w : X × Y → ℝ := fun z => μ.weight z.1 * ν.weight z.2 * K z.1 z.2 with hw
  have hw0 : ∀ z, 0 ≤ w z := fun z =>
    mul_nonneg (mul_nonneg (μ.nonneg _) (ν.nonneg _)) (hK _ _)
  have hdouble : ∀ F : X → Y → ℝ, μ.expect (fun x => ν.expect (fun y => F x y)) =
      ∑ z : X × Y, μ.weight z.1 * ν.weight z.2 * F z.1 z.2 := by
    intro F
    simp only [FiniteLaw.expect, Finset.mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  -- Cauchy–Schwarz with the weights `w`
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun z : X × Y => √(w z) * f z.1) (fun z : X × Y => √(w z) * g z.2)
  have e1 : ∀ z : X × Y, √(w z) * f z.1 * (√(w z) * g z.2) =
      μ.weight z.1 * ν.weight z.2 * (f z.1 * K z.1 z.2 * g z.2) := by
    intro z
    have := Real.mul_self_sqrt (hw0 z)
    calc √(w z) * f z.1 * (√(w z) * g z.2) = (√(w z) * √(w z)) * (f z.1 * g z.2) := by ring
      _ = _ := by rw [this, hw]; ring
  have e2 : ∀ z : X × Y, (√(w z) * f z.1) ^ 2 = μ.weight z.1 * ν.weight z.2 * (K z.1 z.2 *
      f z.1 ^ 2) := by
    intro z
    rw [mul_pow, Real.sq_sqrt (hw0 z), hw]
    ring
  have e3 : ∀ z : X × Y, (√(w z) * g z.2) ^ 2 = μ.weight z.1 * ν.weight z.2 * (K z.1 z.2 *
      g z.2 ^ 2) := by
    intro z
    rw [mul_pow, Real.sq_sqrt (hw0 z), hw]
    ring
  simp only [e1, e2, e3] at hcs
  have d1 : μ.expect (fun x => ν.expect (fun y => f x * K x y * g y)) =
      ∑ z : X × Y, μ.weight z.1 * ν.weight z.2 * (f z.1 * K z.1 z.2 * g z.2) := hdouble _
  have d2 : μ.expect (fun x => ν.expect (fun y => K x y * f x ^ 2)) =
      ∑ z : X × Y, μ.weight z.1 * ν.weight z.2 * (K z.1 z.2 * f z.1 ^ 2) := hdouble _
  have d3 : μ.expect (fun x => ν.expect (fun y => K x y * g y ^ 2)) =
      ∑ z : X × Y, μ.weight z.1 * ν.weight z.2 * (K z.1 z.2 * g z.2 ^ 2) := hdouble _
  rw [← d1, ← d2, ← d3] at hcs
  -- the two marginal sums
  have hf : μ.expect (fun x => ν.expect (fun y => K x y * f x ^ 2)) ≤ ρ * nrm μ f ^ 2 := by
    have hn : nrm μ f ^ 2 = μ.expect (fun x => f x ^ 2) := by
      unfold nrm ip
      rw [Real.sq_sqrt (μ.expect_nonneg fun x => mul_self_nonneg _)]
      exact μ.expect_congr fun x => by ring
    rw [hn, ← μ.expect_const_mul]
    refine μ.expect_mono fun x => ?_
    rw [show (fun y => K x y * f x ^ 2) = fun y => K x y * f x ^ 2 from rfl, ν.expect_mul_const]
    exact mul_le_mul_of_nonneg_right (hρ x) (sq_nonneg _)
  have hg : μ.expect (fun x => ν.expect (fun y => K x y * g y ^ 2)) ≤ γ * nrm ν g ^ 2 := by
    have hn : nrm ν g ^ 2 = ν.expect (fun y => g y ^ 2) := by
      unfold nrm ip
      rw [Real.sq_sqrt (ν.expect_nonneg fun y => mul_self_nonneg _)]
      exact ν.expect_congr fun y => by ring
    have hswap : μ.expect (fun x => ν.expect (fun y => K x y * g y ^ 2)) =
        ν.expect (fun y => μ.expect (fun x => K x y) * g y ^ 2) := by
      simp only [FiniteLaw.expect, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
      ring
    rw [hswap, hn, ← ν.expect_const_mul]
    exact ν.expect_mono fun y => mul_le_mul_of_nonneg_right (hγ y) (sq_nonneg _)
  have hA0 : 0 ≤ μ.expect (fun x => ν.expect (fun y => K x y * f x ^ 2)) :=
    μ.expect_nonneg fun x => ν.expect_nonneg fun y => mul_nonneg (hK x y) (sq_nonneg _)
  have hB0 : 0 ≤ μ.expect (fun x => ν.expect (fun y => K x y * g y ^ 2)) :=
    μ.expect_nonneg fun x => ν.expect_nonneg fun y => mul_nonneg (hK x y) (sq_nonneg _)
  have hρ0 : 0 ≤ ρ * nrm μ f ^ 2 := hA0.trans hf
  have hγ0 : 0 ≤ γ * nrm ν g ^ 2 := hB0.trans hg
  have hsq : (μ.expect (fun x => ν.expect (fun y => f x * K x y * g y))) ^ 2 ≤
      (√(ρ * γ) * nrm μ f * nrm ν g) ^ 2 := by
    have h1 := hcs.trans (mul_le_mul hf hg hB0 hρ0)
    have hρnn : 0 ≤ ρ := by
      obtain ⟨x₀⟩ : Nonempty X := by
        by_contra hX
        rw [not_nonempty_iff] at hX
        have := μ.total
        simp [Finset.univ_eq_empty] at this
      exact (ν.expect_nonneg (hK x₀)).trans (hρ x₀)
    have hγnn : 0 ≤ γ := by
      obtain ⟨y₀⟩ : Nonempty Y := by
        by_contra hY
        rw [not_nonempty_iff] at hY
        have := ν.total
        simp [Finset.univ_eq_empty] at this
      exact (μ.expect_nonneg fun x => hK x y₀).trans (hγ y₀)
    have hρg : 0 ≤ ρ * γ := mul_nonneg hρnn hγnn
    calc _ ≤ ρ * nrm μ f ^ 2 * (γ * nrm ν g ^ 2) := h1
      _ = (√(ρ * γ) * nrm μ f * nrm ν g) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt hρg]
          ring
  have hpos : 0 ≤ √(ρ * γ) * nrm μ f * nrm ν g :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  exact abs_le_of_sq_le_sq' hsq hpos |> fun h => abs_le.mpr h

/-- **`lem:upper-stars`, Step 5, the coincidences.** Let every coordinate of the labellings be
uniform under both laws (`P(x_i = t) = q`; Step 0, `lem:marginals`), and
`0 ≤ K_col ≤ C ∑_{i,j} 1{x_i = y_j}` (`C = 2^{m_×}`). Then every row and column integral of
`K_col` is at most `C n² q`, so `‖K_col‖ ≤ C_col q` with `C_col = n² 2^{m_×}` (Schur's test), and
`0 ≤ E K_col ≤ C_col q`. -/
theorem coincidence_bound {U F : Type*} [Fintype U] [DecidableEq U] [Fintype F] [DecidableEq F]
    (μ ν : FiniteLaw (U → F)) {q : ℝ}
    (hμ : ∀ i t, μ.expect (fun x => if x i = t then 1 else 0) = q)
    (hν : ∀ j t, ν.expect (fun y => if y j = t then 1 else 0) = q)
    (K : (U → F) → (U → F) → ℝ) (hK0 : ∀ x y, 0 ≤ K x y) {C : ℝ} (hC : 0 ≤ C)
    (hK : ∀ x y, K x y ≤ C * ∑ i, ∑ j, (if x i = y j then (1 : ℝ) else 0)) (hq : 0 ≤ q)
    (f g : (U → F) → ℝ) :
    |μ.expect (fun x => ν.expect (fun y => f x * K x y * g y))| ≤
        C * (Fintype.card U : ℝ) ^ 2 * q * nrm μ f * nrm ν g ∧
      0 ≤ μ.expect (fun x => ν.expect (K x)) ∧
      μ.expect (fun x => ν.expect (K x)) ≤ C * (Fintype.card U : ℝ) ^ 2 * q := by
  have hcard : ∑ _i : U, ∑ _j : U, q = (Fintype.card U : ℝ) ^ 2 * q := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have hrow : ∀ x, ν.expect (K x) ≤ C * (Fintype.card U : ℝ) ^ 2 * q := by
    intro x
    calc ν.expect (K x) ≤ ν.expect (fun y => C * ∑ i, ∑ j, (if x i = y j then (1 : ℝ) else 0)) :=
          ν.expect_mono (hK x)
      _ = C * ∑ i, ∑ j, ν.expect (fun y => if y j = x i then (1 : ℝ) else 0) := by
          rw [ν.expect_const_mul]
          congr 1
          simp only [FiniteLaw.expect, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun y _ => ?_
          by_cases h : x i = y j
          · simp [h]
          · simp [h, Ne.symm h]
      _ = C * ((Fintype.card U : ℝ) ^ 2 * q) := by
          simp only [hν]
          rw [hcard]
      _ = C * (Fintype.card U : ℝ) ^ 2 * q := by ring
  have hcol : ∀ y, μ.expect (fun x => K x y) ≤ C * (Fintype.card U : ℝ) ^ 2 * q := by
    intro y
    calc μ.expect (fun x => K x y) ≤
          μ.expect (fun x => C * ∑ i, ∑ j, (if x i = y j then (1 : ℝ) else 0)) :=
          μ.expect_mono fun x => hK x y
      _ = C * ∑ i, ∑ j, μ.expect (fun x => if x i = y j then (1 : ℝ) else 0) := by
          rw [μ.expect_const_mul]
          congr 1
          simp only [FiniteLaw.expect, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
      _ = C * ((Fintype.card U : ℝ) ^ 2 * q) := by
          simp only [hμ]
          rw [hcard]
      _ = C * (Fintype.card U : ℝ) ^ 2 * q := by ring
  have hb : 0 ≤ C * (Fintype.card U : ℝ) ^ 2 * q := by positivity
  refine ⟨?_, μ.expect_nonneg fun x => ν.expect_nonneg (hK0 x), ?_⟩
  · have h := schur_kernel μ ν K hK0 hrow hcol f g
    rwa [Real.sqrt_mul_self hb] at h
  · exact μ.expect_le_const fun x => hrow x

/-- **The coordinates of a graph law are uniform** (`lem:marginals`, V1's
`PartV.graphLaw_vertex_uniform`): `P(x_i = t) = 1/|F|`. -/
theorem graphLaw_coord_uniform {W F : Type*} [Fintype W] [DecidableEq W] [Field F] [Fintype F]
    [DecidableEq F] (G : Labellings.OrientedGraph W)
    (hne : (Labellings.injLabellings F G).Nonempty) (i : W) (t : F) :
    (Labellings.graphLaw G hne).expect (fun x => if x i = t then (1 : ℝ) else 0) =
      1 / (Fintype.card F : ℝ) := by
  rw [PartV.graphLaw_vertex_uniform G hne i (fun z => if z = t then (1 : ℝ) else 0),
    FiniteLaw.expect_uniform, Finset.sum_ite_eq' Finset.univ t]
  simp

/-- **Step 5 for the half laws `λ_H`** (`lem:upper-stars`): with `μ = ν = λ_p(H)`, the uniform
coordinates hold (`graphLaw_coord_uniform`), so `0 ≤ K_col ≤ 2^{m_×} ∑_{i,j} 1{x_i = y_j}` gives
`‖K_col‖ ≤ n² 2^{m_×} q = C_col q` and `0 ≤ E K_col ≤ C_col q`, `q = 1/p`. -/
theorem coincidence_bound_graphLaw {U F : Type*} [Fintype U] [DecidableEq U] [Field F]
    [Fintype F] [DecidableEq F] (H : Labellings.OrientedGraph U)
    (hne : (Labellings.injLabellings F H).Nonempty) (K : (U → F) → (U → F) → ℝ)
    (hK0 : ∀ x y, 0 ≤ K x y) {m : ℕ}
    (hK : ∀ x y, K x y ≤ (2 : ℝ) ^ m * ∑ i, ∑ j, (if x i = y j then (1 : ℝ) else 0))
    (f g : (U → F) → ℝ) :
    |(Labellings.graphLaw H hne).expect (fun x => (Labellings.graphLaw H hne).expect
        (fun y => f x * K x y * g y))| ≤
        (2 : ℝ) ^ m * (Fintype.card U : ℝ) ^ 2 * (1 / (Fintype.card F : ℝ)) *
          nrm (Labellings.graphLaw H hne) f * nrm (Labellings.graphLaw H hne) g ∧
      0 ≤ (Labellings.graphLaw H hne).expect (fun x => (Labellings.graphLaw H hne).expect (K x)) ∧
      (Labellings.graphLaw H hne).expect (fun x => (Labellings.graphLaw H hne).expect (K x)) ≤
        (2 : ℝ) ^ m * (Fintype.card U : ℝ) ^ 2 * (1 / (Fintype.card F : ℝ)) :=
  coincidence_bound _ _ (graphLaw_coord_uniform H hne) (graphLaw_coord_uniform H hne) K hK0
    (by positivity) hK (by positivity) f g

end Coincidences

/-! ## Step 3: the two-stars on the uniform law -/

section TwoStars

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]


/-- **The two-root identity in correlation form** (`eq:two-root`): `∑_b χ(b - a)χ(b - a')` is
`|F| - 1` if `a = a'` and `-1` otherwise. -/
theorem sum_chi_chi (hF : ringChar F ≠ 2) (a a' : F) :
    (∑ b : F, (quadraticChar F (b - a) : ℝ) * (quadraticChar F (b - a') : ℝ)) =
      if a = a' then (Fintype.card F : ℝ) - 1 else -1 := by
  split_ifs with h
  · subst h
    have hpt : ∀ b : F, (quadraticChar F (b - a) : ℝ) * (quadraticChar F (b - a) : ℝ) =
        1 - if b = a then 1 else 0 := by
      intro b
      by_cases hb : b = a
      · simp [hb]
      · have hne : b - a ≠ 0 := sub_ne_zero.mpr hb
        have h1 := quadraticChar_sq_one hne
        simp only [hb, ↓reduceIte, sub_zero]
        rw [← Int.cast_mul, ← sq, h1, Int.cast_one]
    rw [Finset.sum_congr rfl fun b _ => hpt b, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.sum_ite_eq' univ a]
    simp only [mem_univ, ↓reduceIte, Finset.card_univ, nsmul_eq_mul, mul_one]
  · have h2 := Sarkozy.Labellings.two_root hF h
    unfold Sarkozy.Labellings.rootSum at h2
    simp only [Finset.prod_pair h] at h2
    have hpt : ∀ b : F, (quadraticChar F (b - a) : ℝ) * (quadraticChar F (b - a') : ℝ) =
        (quadraticChar F ((b - a) * (b - a')) : ℝ) := by
      intro b
      rw [map_mul, Int.cast_mul]
    rw [Finset.sum_congr rfl fun b _ => hpt b]
    exact_mod_cast h2

/-- **Step 3, the pair Gram** (`lem:upper-stars`): for `𝒦_u` with kernel `χ(b - a)χ(b' - a)`
(centre `a`, leaves `(b, b')`) on the uniform laws, the kernel of `𝒦_u𝒦_u^*` is
`E_{b,b'} χ(b-a)χ(b'-a)χ(b-a')χ(b'-a') = (1{a = a'} - q)²`, i.e. `𝒦_u𝒦_u^* = q(1 - 2q)I + q²J`. -/
theorem twoStar_gram (hF : ringChar F ≠ 2) (a a' : F) :
    (1 / (Fintype.card F : ℝ)) ^ 2 * ∑ b : F, ∑ b' : F,
      ((quadraticChar F (b - a) : ℝ) * (quadraticChar F (b' - a) : ℝ)) *
        ((quadraticChar F (b - a') : ℝ) * (quadraticChar F (b' - a') : ℝ)) =
      ((if a = a' then 1 else 0) - 1 / (Fintype.card F : ℝ)) ^ 2 := by
  have hcard : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hfac : ∑ b : F, ∑ b' : F,
      ((quadraticChar F (b - a) : ℝ) * (quadraticChar F (b' - a) : ℝ)) *
        ((quadraticChar F (b - a') : ℝ) * (quadraticChar F (b' - a') : ℝ)) =
      (∑ b : F, (quadraticChar F (b - a) : ℝ) * (quadraticChar F (b - a') : ℝ)) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    ring
  rw [hfac, sum_chi_chi hF]
  split_ifs
  · field_simp
  · field_simp
    ring

omit [Field F] [DecidableEq F] in
/-- Interchange of four finite sums. -/
theorem sum4_comm (X : F → F → F → F → ℝ) :
    ∑ b : F, ∑ b' : F, ∑ a : F, ∑ a' : F, X b b' a a' =
      ∑ a : F, ∑ a' : F, ∑ b : F, ∑ b' : F, X b b' a a' := by
  calc ∑ b : F, ∑ b' : F, ∑ a : F, ∑ a' : F, X b b' a a'
      = ∑ b : F, ∑ a : F, ∑ b' : F, ∑ a' : F, X b b' a a' :=
        Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ b : F, ∑ a : F, ∑ a' : F, ∑ b' : F, X b b' a a' :=
        Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a : F, ∑ b : F, ∑ a' : F, ∑ b' : F, X b b' a a' := Finset.sum_comm
    _ = ∑ a : F, ∑ a' : F, ∑ b : F, ∑ b' : F, X b b' a a' :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm

/-- **Step 3, the norm** (`lem:upper-stars`): `‖𝒦_u^* f‖² ≤ q(1 - q)‖f‖²` on the uniform laws,
so `‖𝒦_u‖ ≤ (q(1 - q))^{1/2} ≤ r`, the norm `q(1 - q)` of `q(1 - 2q)I + q²J`. -/
theorem twoStar_adjoint_norm (hF : ringChar F ≠ 2) (f : F → ℝ) :
    (1 / (Fintype.card F : ℝ)) ^ 2 * ∑ b : F, ∑ b' : F,
      ((1 / (Fintype.card F : ℝ)) * ∑ a : F,
        ((quadraticChar F (b - a) : ℝ) * (quadraticChar F (b' - a) : ℝ)) * f a) ^ 2 ≤
      (1 / (Fintype.card F : ℝ)) * (1 - 1 / (Fintype.card F : ℝ)) *
        ((1 / (Fintype.card F : ℝ)) * ∑ a : F, f a ^ 2) := by
  set q : ℝ := 1 / (Fintype.card F : ℝ) with hq
  have hcard : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hq0 : 0 < q := by rw [hq]; positivity
  set k : F → F → F → ℝ := fun a b b' =>
    (quadraticChar F (b - a) : ℝ) * (quadraticChar F (b' - a) : ℝ) with hk
  have hsq : ∀ b b' : F, (q * ∑ a : F, k a b b' * f a) ^ 2 =
      q ^ 2 * ∑ a : F, ∑ a' : F, f a * f a' * (k a b b' * k a' b b') := by
    intro b b'
    rw [mul_pow, sq (∑ a : F, k a b b' * f a), Finset.sum_mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
    ring
  have hgram : ∀ a a' : F, ∑ b : F, ∑ b' : F, k a b b' * k a' b b' =
      ((if a = a' then 1 else 0) - q) ^ 2 / q ^ 2 := by
    intro a a'
    have h := twoStar_gram hF a a'
    rw [← hq] at h
    rw [eq_div_iff (by positivity), ← h, mul_comm]
  have hS : ∑ b : F, ∑ b' : F, (q * ∑ a : F, k a b b' * f a) ^ 2 =
      ∑ a : F, ∑ a' : F, f a * f a' * ((if a = a' then 1 else 0) - q) ^ 2 := by
    simp only [hsq, ← Finset.mul_sum]
    rw [sum4_comm (fun b b' a a' => f a * f a' * (k a b b' * k a' b b'))]
    simp only [← Finset.mul_sum, hgram]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a' _ => ?_
    field_simp
  have hsplit : ∑ a : F, ∑ a' : F, f a * f a' * ((if a = a' then 1 else 0) - q) ^ 2 =
      (1 - 2 * q) * ∑ a : F, f a ^ 2 + q ^ 2 * (∑ a : F, f a) ^ 2 := by
    have hpt : ∀ a a' : F, f a * f a' * ((if a = a' then 1 else 0) - q) ^ 2 =
        (if a = a' then (1 - 2 * q) * f a ^ 2 else 0) + q ^ 2 * (f a * f a') := by
      intro a a'
      by_cases h : a = a'
      · subst h
        simp only [↓reduceIte]
        ring
      · simp only [h, ↓reduceIte]
        ring
    simp only [hpt, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    rw [sq (∑ a : F, f a), Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
  have hcs : (∑ a : F, f a) ^ 2 ≤ (Fintype.card F : ℝ) * ∑ a : F, f a ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq univ (fun _ => (1 : ℝ)) f
    simpa [Finset.card_univ] using this
  have hcardq : (Fintype.card F : ℝ) = 1 / q := by rw [hq, one_div_one_div]
  have h4 : q ^ 4 * (∑ a : F, f a) ^ 2 ≤ q ^ 3 * ∑ a : F, f a ^ 2 := by
    have := mul_le_mul_of_nonneg_left hcs (pow_nonneg hq0.le 4)
    calc q ^ 4 * (∑ a : F, f a) ^ 2 ≤ q ^ 4 * ((Fintype.card F : ℝ) * ∑ a : F, f a ^ 2) := this
      _ = q ^ 3 * ∑ a : F, f a ^ 2 := by
          rw [hcardq]
          field_simp
  rw [hS, hsplit]
  nlinarith [h4]

/-- **Step 3, the forward norm on the uniform law**: for `h` on the leaf pairs,
`E_a (E_{b,b'} χ(b-a)χ(b'-a) h(b,b'))² ≤ q(1 - q) E_{b,b'} h²` (duality from
`twoStar_adjoint_norm`). -/
theorem twoStar_norm (hF : ringChar F ≠ 2) (h : F → F → ℝ) :
    (1 / (Fintype.card F : ℝ)) * ∑ a : F, ((1 / (Fintype.card F : ℝ)) ^ 2 * ∑ b : F, ∑ b' : F,
      ((quadraticChar F (b - a) : ℝ) * (quadraticChar F (b' - a) : ℝ)) * h b b') ^ 2 ≤
      (1 / (Fintype.card F : ℝ)) * (1 - 1 / (Fintype.card F : ℝ)) *
        ((1 / (Fintype.card F : ℝ)) ^ 2 * ∑ b : F, ∑ b' : F, h b b' ^ 2) := by
  set q : ℝ := 1 / (Fintype.card F : ℝ) with hq
  have hcard : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hq0 : 0 < q := by rw [hq]; positivity
  have hq1 : q ≤ 1 := by
    rw [hq, div_le_one hcard]
    exact_mod_cast Fintype.card_pos
  set k : F → F → F → ℝ := fun a b b' =>
    (quadraticChar F (b - a) : ℝ) * (quadraticChar F (b' - a) : ℝ) with hk
  -- `g = 𝒦_u h`, and the duality `E_a g(a)² = E_{b,b'} h (𝒦_u^* g)`
  set g : F → ℝ := fun a => q ^ 2 * ∑ b : F, ∑ b' : F, k a b b' * h b b' with hg
  set G : F → F → ℝ := fun b b' => q * ∑ a : F, k a b b' * g a with hG
  have hswap : ∀ X : F → F → F → ℝ,
      ∑ a : F, ∑ b : F, ∑ b' : F, X a b b' = ∑ b : F, ∑ b' : F, ∑ a : F, X a b b' := by
    intro X
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_comm
  have hdual : q * ∑ a : F, g a ^ 2 = q ^ 2 * ∑ b : F, ∑ b' : F, h b b' * G b b' := by
    have e1 : q * ∑ a : F, g a ^ 2 =
        q ^ 3 * ∑ a : F, ∑ b : F, ∑ b' : F, k a b b' * h b b' * g a := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      have : g a ^ 2 = (q ^ 2 * ∑ b : F, ∑ b' : F, k a b b' * h b b') * g a := by
        rw [sq]
      have e3 : (∑ b : F, ∑ b' : F, k a b b' * h b b') * g a =
          ∑ b : F, ∑ b' : F, k a b b' * h b b' * g a := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun b _ => by rw [Finset.sum_mul]
      rw [this, mul_assoc (q ^ 2), e3]
      ring
    have e2 : q ^ 2 * ∑ b : F, ∑ b' : F, h b b' * G b b' =
        q ^ 3 * ∑ b : F, ∑ b' : F, ∑ a : F, k a b b' * h b b' * g a := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b' _ => ?_
      rw [hG]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    rw [e1, e2, hswap]
  -- Cauchy–Schwarz on the leaf pairs, and the adjoint bound for `G`
  have hadj := twoStar_adjoint_norm hF g
  rw [← hq] at hadj
  have hGsq : q ^ 2 * ∑ b : F, ∑ b' : F, G b b' ^ 2 ≤ q * (1 - q) * (q * ∑ a : F, g a ^ 2) :=
    hadj
  have hcs : (q ^ 2 * ∑ b : F, ∑ b' : F, h b b' * G b b') ^ 2 ≤
      (q ^ 2 * ∑ b : F, ∑ b' : F, h b b' ^ 2) * (q ^ 2 * ∑ b : F, ∑ b' : F, G b b' ^ 2) := by
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq (univ ×ˢ univ) (fun z : F × F => h z.1 z.2)
      (fun z : F × F => G z.1 z.2)
    simp only [Finset.sum_product] at h1
    have e : (q ^ 2 * ∑ b : F, ∑ b' : F, h b b' * G b b') ^ 2 =
        q ^ 4 * (∑ b : F, ∑ b' : F, h b b' * G b b') ^ 2 := by ring
    rw [e]
    calc q ^ 4 * (∑ b : F, ∑ b' : F, h b b' * G b b') ^ 2 ≤
        q ^ 4 * ((∑ b : F, ∑ b' : F, h b b' ^ 2) * ∑ b : F, ∑ b' : F, G b b' ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
  -- conclude
  set A := q * ∑ a : F, g a ^ 2 with hA
  set Hn := q ^ 2 * ∑ b : F, ∑ b' : F, h b b' ^ 2 with hHn
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact mul_nonneg hq0.le (Finset.sum_nonneg fun a _ => sq_nonneg _)
  have hH0 : 0 ≤ Hn := by
    rw [hHn]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun b _ =>
      Finset.sum_nonneg fun b' _ => sq_nonneg _)
  have hc0 : 0 ≤ q * (1 - q) := mul_nonneg hq0.le (by linarith)
  -- `A² ≤ Hn · q(1 - q) A`, hence `A ≤ q(1 - q) Hn`
  have hAA : A ^ 2 ≤ Hn * (q * (1 - q) * A) := by
    rw [hdual]
    calc (q ^ 2 * ∑ b : F, ∑ b' : F, h b b' * G b b') ^ 2 ≤
        Hn * (q ^ 2 * ∑ b : F, ∑ b' : F, G b b' ^ 2) := hcs
      _ ≤ Hn * (q * (1 - q) * (q ^ 2 * ∑ b : F, ∑ b' : F, h b b' * G b b')) := by
          rw [← hdual]
          exact mul_le_mul_of_nonneg_left hGsq hH0
  have hfin : A ≤ q * (1 - q) * Hn := by
    rcases hA0.lt_or_eq with hpos | hzero
    · have := hAA
      nlinarith
    · rw [← hzero]
      exact mul_nonneg hc0 hH0
  exact hfin

/-- **Step 3, the two-star kernel on the pair law** (`lem:upper-stars`): if the law `ϱ` of the
leaves has density `ρ ≤ c` relative to the uniform law on `F × F` (Step 0: `c = 2/(1 - q)`), then
`h ↦ E_ϱ[χ(b - a)χ(b' - a) h(b, b')]` has `E_a (·)² ≤ c q(1 - q) ‖h‖²_ϱ`, i.e. norm at most
`(c q)^{1/2} ≤ (2/(1 - q))^{1/2} r`. -/
theorem twoStar_norm_density (hF : ringChar F ≠ 2) (ρ : F → F → ℝ) {c : ℝ}
    (hρ0 : ∀ b b', 0 ≤ ρ b b') (hρc : ∀ b b', ρ b b' ≤ c) (h : F → F → ℝ) :
    (1 / (Fintype.card F : ℝ)) * ∑ a : F, ((1 / (Fintype.card F : ℝ)) ^ 2 * ∑ b : F, ∑ b' : F,
      ((quadraticChar F (b - a) : ℝ) * (quadraticChar F (b' - a) : ℝ)) * (ρ b b' * h b b')) ^ 2 ≤
      c * ((1 / (Fintype.card F : ℝ)) * (1 - 1 / (Fintype.card F : ℝ))) *
        ((1 / (Fintype.card F : ℝ)) ^ 2 * ∑ b : F, ∑ b' : F, ρ b b' * h b b' ^ 2) := by
  have h1 := twoStar_norm hF (fun b b' => ρ b b' * h b b')
  have hcard : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hq1 : 1 / (Fintype.card F : ℝ) ≤ 1 := by
    rw [div_le_one hcard]
    exact_mod_cast Fintype.card_pos
  have hc : 0 ≤ (1 / (Fintype.card F : ℝ)) * (1 - 1 / (Fintype.card F : ℝ)) :=
    mul_nonneg (by positivity) (by linarith)
  have hsq : (1 / (Fintype.card F : ℝ)) ^ 2 * ∑ b : F, ∑ b' : F, (ρ b b' * h b b') ^ 2 ≤
      c * ((1 / (Fintype.card F : ℝ)) ^ 2 * ∑ b : F, ∑ b' : F, ρ b b' * h b b' ^ 2) := by
    rw [← mul_assoc, mul_comm c, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b' _ => ?_
    have := mul_le_mul_of_nonneg_right (hρc b b') (mul_nonneg (hρ0 b b') (sq_nonneg (h b b')))
    nlinarith [this]
  calc _ ≤ (1 / (Fintype.card F : ℝ)) * (1 - 1 / (Fintype.card F : ℝ)) *
        ((1 / (Fintype.card F : ℝ)) ^ 2 * ∑ b : F, ∑ b' : F, (ρ b b' * h b b') ^ 2) := h1
    _ ≤ (1 / (Fintype.card F : ℝ)) * (1 - 1 / (Fintype.card F : ℝ)) *
        (c * ((1 / (Fintype.card F : ℝ)) ^ 2 * ∑ b : F, ∑ b' : F, ρ b b' * h b b' ^ 2)) :=
        mul_le_mul_of_nonneg_left hsq hc
    _ = _ := by ring

/-- **Step 2, the single edges on the uniform law**: the Paley operator
`𝒫h(a) = E_b χ(b - a) h(b)` satisfies `E_a (𝒫h)² ≤ q E_b h²`, i.e. `‖𝒫‖ ≤ r` (`𝒫𝒫^* = q(I - J)` by
the two-root identity; `lem:square-shift`(c)). -/
theorem paley_norm (hF : ringChar F ≠ 2) (h : F → ℝ) :
    (1 / (Fintype.card F : ℝ)) * ∑ a : F, ((1 / (Fintype.card F : ℝ)) *
      ∑ b : F, (quadraticChar F (b - a) : ℝ) * h b) ^ 2 ≤
      (1 / (Fintype.card F : ℝ)) * ((1 / (Fintype.card F : ℝ)) * ∑ b : F, h b ^ 2) := by
  set q : ℝ := 1 / (Fintype.card F : ℝ) with hq
  have hcard : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hq0 : 0 < q := by rw [hq]; positivity
  -- `∑_a (∑_b χ(b-a)h(b))² = ∑_{b,b'} h(b)h(b') ∑_a χ(b-a)χ(b'-a) = |F| ∑ h² - (∑ h)²`
  have hexp : ∑ a : F, (∑ b : F, (quadraticChar F (b - a) : ℝ) * h b) ^ 2 =
      ∑ b : F, ∑ b' : F, h b * h b' *
        ∑ a : F, (quadraticChar F (b - a) : ℝ) * (quadraticChar F (b' - a) : ℝ) := by
    have e : ∀ a : F, (∑ b : F, (quadraticChar F (b - a) : ℝ) * h b) ^ 2 =
        ∑ b : F, ∑ b' : F, h b * h b' *
          ((quadraticChar F (b - a) : ℝ) * (quadraticChar F (b' - a) : ℝ)) := by
      intro a
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
      ring
    simp only [e, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_comm
  have hchi : ∀ b b' : F, ∑ a : F, (quadraticChar F (b - a) : ℝ) * (quadraticChar F (b' - a) : ℝ) =
      if b = b' then (Fintype.card F : ℝ) - 1 else -1 := by
    intro b b'
    have h1 := sum_chi_chi hF b b'
    rw [← h1]
    -- `χ(b - a) = χ(-1) χ(a - b)` for both factors, and `χ(-1)² = 1`
    have hsq : ∀ a : F, (quadraticChar F (b - a) : ℝ) * (quadraticChar F (b' - a) : ℝ) =
        (quadraticChar F (a - b) : ℝ) * (quadraticChar F (a - b') : ℝ) := by
      intro a
      have e1 : b - a = -1 * (a - b) := by ring
      have e2 : b' - a = -1 * (a - b') := by ring
      rw [e1, e2, map_mul, map_mul, Int.cast_mul, Int.cast_mul]
      have hm1 : (quadraticChar F (-1) : ℝ) * (quadraticChar F (-1) : ℝ) = 1 := by
        rw [← Int.cast_mul, ← sq, quadraticChar_sq_one (neg_ne_zero.mpr one_ne_zero),
          Int.cast_one]
      calc (quadraticChar F (-1) : ℝ) * (quadraticChar F (a - b) : ℝ) *
            ((quadraticChar F (-1) : ℝ) * (quadraticChar F (a - b') : ℝ)) =
          ((quadraticChar F (-1) : ℝ) * (quadraticChar F (-1) : ℝ)) *
            ((quadraticChar F (a - b) : ℝ) * (quadraticChar F (a - b') : ℝ)) := by ring
        _ = _ := by rw [hm1, one_mul]
    exact Finset.sum_congr rfl fun a _ => hsq a
  have hval : ∑ b : F, ∑ b' : F, h b * h b' *
      ∑ a : F, (quadraticChar F (b - a) : ℝ) * (quadraticChar F (b' - a) : ℝ) =
      (Fintype.card F : ℝ) * ∑ b : F, h b ^ 2 - (∑ b : F, h b) ^ 2 := by
    simp only [hchi]
    have hpt : ∀ b b' : F, h b * h b' * (if b = b' then (Fintype.card F : ℝ) - 1 else -1) =
        (if b = b' then (Fintype.card F : ℝ) * h b ^ 2 else 0) - h b * h b' := by
      intro b b'
      by_cases hb : b = b'
      · subst hb
        simp only [↓reduceIte]
        ring
      · simp only [hb, ↓reduceIte]
        ring
    simp only [hpt, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    rw [sq (∑ b : F, h b), Finset.sum_mul_sum, Finset.mul_sum]
  have hlhs : q * ∑ a : F, (q * ∑ b : F, (quadraticChar F (b - a) : ℝ) * h b) ^ 2 =
      q ^ 3 * ((Fintype.card F : ℝ) * ∑ b : F, h b ^ 2 - (∑ b : F, h b) ^ 2) := by
    rw [← hval, ← hexp]
    simp only [mul_pow, ← Finset.mul_sum]
    ring
  rw [hlhs]
  have hcardq : (Fintype.card F : ℝ) = 1 / q := by rw [hq, one_div_one_div]
  rw [hcardq]
  have hsq0 : 0 ≤ (∑ b : F, h b) ^ 2 := sq_nonneg _
  have e : q ^ 3 * (1 / q * ∑ b : F, h b ^ 2 - (∑ b : F, h b) ^ 2) =
      q * (q * ∑ b : F, h b ^ 2) - q ^ 3 * (∑ b : F, h b) ^ 2 := by
    field_simp
  rw [e]
  have := mul_nonneg (pow_nonneg hq0.le 3) hsq0
  linarith

end TwoStars

/-! ## Step 0: the pair law of two coordinates -/

section PairDensity

open Sarkozy.Labellings

variable {W F : Type*} [Fintype W] [DecidableEq W] [Field F] [Fintype F] [DecidableEq F]


/-- The number of nonzero squares of `F` is `(|F| - 1)/2` (`∑ χ = 0`, `∑ χ² = |F| - 1`). -/
theorem card_squares (hF : ringChar F ≠ 2) :
    ((univ.filter fun α : F => quadraticChar F α = 1).card : ℝ) =
      ((Fintype.card F : ℝ) - 1) / 2 := by
  have hind : ∀ α : F, (if quadraticChar F α = 1 then (1 : ℝ) else 0) =
      ((quadraticChar F α : ℝ) + (quadraticChar F α : ℝ) * (quadraticChar F α : ℝ)) * (1 / 2) := by
    intro α
    by_cases h0 : α = 0
    · subst h0
      simp
    · have h2 := quadraticChar_sq_one h0
      rcases quadraticChar_dichotomy h0 with h | h
      · rw [h]; norm_num
      · rw [h]; norm_num
  rw [Finset.card_filter, Nat.cast_sum]
  have : ∑ α : F, ((if quadraticChar F α = 1 then 1 else 0 : ℕ) : ℝ) =
      ∑ α : F, (if quadraticChar F α = 1 then (1 : ℝ) else 0) := by
    refine Finset.sum_congr rfl fun α _ => ?_
    split_ifs <;> simp
  rw [this, Finset.sum_congr rfl fun α _ => hind α, ← Finset.sum_mul, Finset.sum_add_distrib]
  have hs0 : ∑ α : F, (quadraticChar F α : ℝ) = 0 := by
    exact_mod_cast quadraticChar_sum_zero hF
  have hs2 := sum_chi_chi hF (0 : F) 0
  simp only [sub_zero, ↓reduceIte] at hs2
  rw [hs0, hs2]
  ring


/-- **Step 0, the pair law of two coordinates** (`lem:upper-stars`, proof): for distinct vertices
`i ≠ j` of a graph law, `P(x_i = a, x_j = b) ≤ 2/(|F|(|F| - 1))`. The square-affine maps
`z ↦ αz + β` (`χ(α) = 1`) preserve the law (V1's `PartV.graphLaw_expect_affine`, `lem:marginals`)
and move `(a, b)`, `a ≠ b`, along `|F|(|F| - 1)/2` distinct pairs; for `a = b` the probability is
zero (the labellings are injective). -/
theorem graphLaw_pair_le (hF : ringChar F ≠ 2) (G : OrientedGraph W)
    (hne : (injLabellings F G).Nonempty) {i j : W} (hij : i ≠ j) (a b : F) :
    (graphLaw G hne).expect (fun z => if z i = a ∧ z j = b then (1 : ℝ) else 0) ≤
      2 / ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1)) := by
  have hcard1 : (1 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.one_lt_card
  have hden : 0 < (Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1) := by
    have : (0 : ℝ) < Fintype.card F := by linarith
    nlinarith
  set P : F → F → ℝ := fun c d =>
    (graphLaw G hne).expect (fun z => if z i = c ∧ z j = d then (1 : ℝ) else 0) with hP
  by_cases hab : a = b
  · -- injectivity: `P(a, a) = 0`
    subst hab
    have h0 : P a a = 0 := by
      rw [hP]
      simp only [FiniteLaw.expect, graphLaw]
      refine Finset.sum_eq_zero fun z _ => ?_
      by_cases hz : z ∈ injLabellings F G
      · have hinj := ((mem_injLabellings_iff_feasible G z).mp hz).1
        have hne' : ¬ (z i = a ∧ z j = a) := by
          rintro ⟨h1, h2⟩
          exact hij (hinj i (mem_univ i) j (mem_univ j) (h1.trans h2.symm))
        simp [hne']
      · simp [hz]
    show P a a ≤ _
    rw [h0]
    positivity
  · -- the square-affine maps preserve `P`
    have hinv : ∀ α : F, quadraticChar F α = 1 → ∀ β : F, P (α * a + β) (α * b + β) = P a b := by
      intro α hα β
      have hα0 : α ≠ 0 := PartV.ne_zero_of_quadraticChar_eq_one hα
      have h := PartV.graphLaw_expect_affine G hne hα β
        (fun z => if z i = α * a + β ∧ z j = α * b + β then (1 : ℝ) else 0)
      have e : ∀ z : W → F, (α * z i + β = α * a + β ∧ α * z j + β = α * b + β) ↔
          (z i = a ∧ z j = b) := by
        intro z
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨mul_left_cancel₀ hα0 (add_right_cancel h1),
            mul_left_cancel₀ hα0 (add_right_cancel h2)⟩
        · rintro ⟨h1, h2⟩
          exact ⟨by rw [h1], by rw [h2]⟩
      simp only [e] at h
      rw [hP]
      exact h.symm
    -- summing over the `|F|(|F| - 1)/2` maps
    set T := univ.filter fun α : F => quadraticChar F α = 1 with hT
    have hsum : ∑ α ∈ T, ∑ β : F, P (α * a + β) (α * b + β) =
        (T.card : ℝ) * (Fintype.card F : ℝ) * P a b := by
      rw [Finset.sum_congr rfl fun α hα => Finset.sum_congr rfl fun β _ =>
        hinv α (Finset.mem_filter.mp hα).2 β]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    have hle : ∑ α ∈ T, ∑ β : F, P (α * a + β) (α * b + β) ≤ 1 := by
      have hswap : ∑ α ∈ T, ∑ β : F, P (α * a + β) (α * b + β) =
          (graphLaw G hne).expect (fun z => ∑ α ∈ T, ∑ β : F,
            if z i = α * a + β ∧ z j = α * b + β then (1 : ℝ) else 0) := by
        rw [hP]
        simp only [FiniteLaw.expect, Finset.mul_sum]
        exact (Finset.sum_congr rfl fun α _ => Finset.sum_comm).trans Finset.sum_comm
      rw [hswap]
      refine (graphLaw G hne).expect_le_const fun z => ?_
      -- at most one `(α, β)` maps `(a, b)` to `(z_i, z_j)`
      have hone : ∀ α ∈ T, ∀ β : F, ∀ α' ∈ T, ∀ β' : F,
          (z i = α * a + β ∧ z j = α * b + β) → (z i = α' * a + β' ∧ z j = α' * b + β') →
            α = α' ∧ β = β' := by
        intro α _ β α' _ β' ⟨h1, h2⟩ ⟨h1', h2'⟩
        have hd : α * (a - b) = α' * (a - b) := by linear_combination h1.symm - h2.symm + h1' - h2'
        have hsub : a - b ≠ 0 := sub_ne_zero.mpr hab
        have hαα : α = α' := mul_right_cancel₀ hsub hd
        refine ⟨hαα, ?_⟩
        rw [hαα] at h1
        linear_combination h1' - h1
      by_cases hex : ∃ α ∈ T, ∃ β : F, z i = α * a + β ∧ z j = α * b + β
      · obtain ⟨α₀, hα₀, β₀, hz⟩ := hex
        have : ∑ α ∈ T, ∑ β : F, (if z i = α * a + β ∧ z j = α * b + β then (1 : ℝ) else 0) =
            ∑ α ∈ T, ∑ β : F, (if α = α₀ ∧ β = β₀ then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl fun α hα => Finset.sum_congr rfl fun β _ => ?_
          by_cases hc : z i = α * a + β ∧ z j = α * b + β
          · obtain ⟨e1, e2⟩ := hone α hα β α₀ hα₀ β₀ hc hz
            simp [hc, e1, e2]
          · have : ¬ (α = α₀ ∧ β = β₀) := by
              rintro ⟨e1, e2⟩
              exact hc (by rw [e1, e2]; exact hz)
            simp [hc, this]
        rw [this]
        have h1 : ∀ α : F, ∑ β : F, (if α = α₀ ∧ β = β₀ then (1 : ℝ) else 0) =
            if α = α₀ then 1 else 0 := by
          intro α
          by_cases hα : α = α₀
          · simp [hα]
          · simp [hα]
        simp only [h1]
        rw [Finset.sum_ite_eq' T α₀]
        simp [hα₀]
      · push Not at hex
        have : ∑ α ∈ T, ∑ β : F, (if z i = α * a + β ∧ z j = α * b + β then (1 : ℝ) else 0) = 0 :=
          Finset.sum_eq_zero fun α hα => Finset.sum_eq_zero fun β _ => by
            have := hex α hα β
            simp only [ite_eq_right_iff, one_ne_zero, imp_false, not_and]
            exact this
        rw [this]
        norm_num
    have hT2 : (T.card : ℝ) = ((Fintype.card F : ℝ) - 1) / 2 := card_squares hF
    have hP0 : 0 ≤ P a b := (graphLaw G hne).expect_nonneg fun z => by split_ifs <;> norm_num
    show P a b ≤ _
    rw [hsum, hT2] at hle
    rw [le_div_iff₀ hden]
    nlinarith

/-- **Step 0, the pair density** (`lem:upper-stars`, proof): the pair law of two distinct
coordinates of a graph law has density at most `2|F|/(|F| - 1) = 2/(1 - q)` against the uniform
law of `F × F`; with `twoStar_norm_density` this gives Step 3's `‖𝒦‖ ≤ (2/(1 - q))^{1/2} r`. -/
theorem graphLaw_pair_density (hF : ringChar F ≠ 2) (G : OrientedGraph W)
    (hne : (injLabellings F G).Nonempty) {i j : W} (hij : i ≠ j) (a b : F) :
    (Fintype.card F : ℝ) ^ 2 *
        (graphLaw G hne).expect (fun z => if z i = a ∧ z j = b then (1 : ℝ) else 0) ≤
      2 / (1 - 1 / (Fintype.card F : ℝ)) := by
  have hcard1 : (1 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.one_lt_card
  have h := graphLaw_pair_le hF G hne hij a b
  have hc0 : (0 : ℝ) < Fintype.card F := by linarith
  have e : 2 / (1 - 1 / (Fintype.card F : ℝ)) =
      (Fintype.card F : ℝ) ^ 2 * (2 / ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1))) := by
    have : (Fintype.card F : ℝ) - 1 ≠ 0 := by linarith
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left h (by positivity)

end PairDensity

end Sarkozy.UpperReference.UpperStars
