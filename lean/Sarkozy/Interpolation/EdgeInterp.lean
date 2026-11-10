module

public import Sarkozy.Interpolation.RealEndpoints
public import Sarkozy.Certificates.EdgeMoment

/-!
# The centred pair form: interpolation at `r = 1 + 1/j` (`lem:density:edge-moment`)

`paper/sections/30_density_moment_upgrade.tex`, `lem:density:edge-moment`, step 2. For a weight
`π` on `Fin 2 → X` (a pair law) the centred bilinear form is
`B(f, g) = E_π f(x₀) g(x₁) − E f · E g` (`centredForm`), with uniform expectations on `X`. If
`|B(f,g)| ≤ L ‖f‖₁ ‖g‖₁` and `|B(f,g)| ≤ ρ ‖f‖₂ ‖g‖₂` for all real `f, g`, interpolation at
`1/r = (1 − t)/1 + t/2`, `t = 2/(j + 1)`, i.e. `r = 1 + 1/j`, gives
`|B(f,g)| ≤ L^{(j−1)/(j+1)} ρ^{2/(j+1)} ‖f‖_r ‖g‖_r`.

Main results:
* `centredForm_eq_rbil`: `B` is the bilinear form of the kernel `π(a,b) − 1/|X|²`;
* `centred_interp`: the interpolated bound for every `t ∈ [0,1]`;
* `centred_interp_edge`: the case `t = 2/(j+1)`, restricted to mean-zero `f, g`. This is
  exactly the hypothesis `hinterp` of `EdgeGate.edge_moment_of_interpolation` and of
  `EdgeGate.square_pair_moment`;
* `edge_moment_of_endpoints`: `lem:density:edge-moment` from the two endpoint bounds and the
  gate (the interpolation hypothesis discharged);
* `interp_L1_L2_lpNorm`: the real `L¹`/`L²` interpolation with `FiniteLaw.lpNorm` norms of
  arbitrary finite laws.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Interpolation

section FiniteLawNorms

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The weighted norm of a `FiniteLaw` weight is `FiniteLaw.lpNorm`. -/
theorem rNorm_eq_lpNorm (μ : FiniteLaw X) (r : ℝ) (f : X → ℝ) :
    rNorm μ.weight r f = μ.lpNorm r f := by
  unfold rNorm FiniteLaw.lpNorm FiniteLaw.moment FiniteLaw.expect
  rw [one_div]

/-- **Bilinear interpolation between `L¹ × L¹` and `L² × L²` for finite laws** (the
interpolation step of `lem:density:edge-moment`, with the norms `FiniteLaw.lpNorm` of arbitrary
finite probability laws `μ` on `X` and `ν` on `Y`). -/
theorem interp_L1_L2_lpNorm (μ : FiniteLaw X) (ν : FiniteLaw Y) (k : X → Y → ℝ) {L ρ t r : ℝ}
    (hL : 0 ≤ L) (hρ : 0 ≤ ρ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hr : 1 / r = (1 - t) / 1 + t / 2)
    (h1 : ∀ f g, |rbil k f g| ≤ L * μ.lpNorm 1 f * ν.lpNorm 1 g)
    (h2 : ∀ f g, |rbil k f g| ≤ ρ * μ.lpNorm 2 f * ν.lpNorm 2 g) (f : X → ℝ) (g : Y → ℝ) :
    |rbil k f g| ≤ L ^ (1 - t) * ρ ^ t * μ.lpNorm r f * ν.lpNorm r g := by
  simp only [← rNorm_eq_lpNorm] at h1 h2 ⊢
  exact interp_L1_L2 μ.weight ν.weight μ.nonneg ν.nonneg k hL hρ ht0 ht1 hr h1 h2 f g

end FiniteLawNorms

variable {X : Type*} [Fintype X]

/-- The centred bilinear form `E_π f(x₀) g(x₁) − E f · E g` of a weight `π` on `Fin 2 → X`. The
expectations `E f`, `E g` are uniform on `X`. -/
noncomputable def centredForm (π : (Fin 2 → X) → ℝ) (f g : X → ℝ) : ℝ :=
  ∑ x, π x * (f (x 0) * g (x 1)) -
    (∑ a, f a) / Fintype.card X * ((∑ b, g b) / Fintype.card X)

/-- The kernel `π(a, b) − 1/|X|²` of the centred form. -/
noncomputable def centredKernel (π : (Fin 2 → X) → ℝ) : X → X → ℝ :=
  fun a b => π ![a, b] - (Fintype.card X : ℝ)⁻¹ * (Fintype.card X : ℝ)⁻¹

/-- Sums over `Fin 2 → X` as double sums. -/
theorem sum_pair (π : (Fin 2 → X) → ℝ) (f g : X → ℝ) :
    ∑ x, π x * (f (x 0) * g (x 1)) = ∑ a, ∑ b, π ![a, b] * f a * g b := by
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (piFinTwoEquiv fun _ => X) _ _ fun x => ?_
  have hx : ![x 0, x 1] = x := by
    funext i
    fin_cases i <;> rfl
  simp only [piFinTwoEquiv_apply, hx]
  ring

theorem centredForm_eq_rbil (π : (Fin 2 → X) → ℝ) (f g : X → ℝ) :
    centredForm π f g = rbil (centredKernel π) f g := by
  unfold centredForm rbil centredKernel
  rw [sum_pair]
  simp only [sub_mul, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_div, Finset.sum_div, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem centredForm_of_mean_zero (π : (Fin 2 → X) → ℝ) {f : X → ℝ} (g : X → ℝ)
    (hf : ∑ a, f a = 0) : centredForm π f g = ∑ x, π x * (f (x 0) * g (x 1)) := by
  simp [centredForm, hf]

/-- **Interpolation for the centred pair form** (`lem:density:edge-moment`, step 2, every
`t`). From `|B(f,g)| ≤ L ‖f‖₁ ‖g‖₁` and `|B(f,g)| ≤ ρ ‖f‖₂ ‖g‖₂` (all real `f, g`, uniform
norms on `X`), for `0 ≤ t ≤ 1` and `1/r = (1 − t) + t/2`:
`|B(f,g)| ≤ L^{1−t} ρ^t ‖f‖_r ‖g‖_r`. -/
theorem centred_interp (π : (Fin 2 → X) → ℝ) {L ρ t r : ℝ} (hL : 0 ≤ L) (hρ : 0 ≤ ρ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hr : 1 / r = (1 - t) / 1 + t / 2)
    (h1 : ∀ f g : X → ℝ, |centredForm π f g| ≤
      L * DensityUpgrade.conditioningNorm 1 f * DensityUpgrade.conditioningNorm 1 g)
    (h2 : ∀ f g : X → ℝ, |centredForm π f g| ≤
      ρ * DensityUpgrade.conditioningNorm 2 f * DensityUpgrade.conditioningNorm 2 g)
    (f g : X → ℝ) :
    |centredForm π f g| ≤ L ^ (1 - t) * ρ ^ t * DensityUpgrade.conditioningNorm r f *
      DensityUpgrade.conditioningNorm r g := by
  simp only [centredForm_eq_rbil] at h1 h2 ⊢
  exact interp_L1_L2_uniform _ hL hρ ht0 ht1 hr h1 h2 f g

/-- **`lem:density:edge-moment`, step 2** (`r = 1 + 1/j`, `t = 2/(j+1)`). From the `L¹ × L¹` and
`L² × L²` bounds `L`, `ρ` of the centred form, every mean-zero `f, g` satisfy
`|E_π f(x₀) g(x₁)| ≤ L^{(j−1)/(j+1)} ρ^{2/(j+1)} ‖f‖_{1+1/j} ‖g‖_{1+1/j}`. This is the hypothesis
`hinterp` of `EdgeGate.edge_moment_of_interpolation` and `EdgeGate.square_pair_moment`. -/
theorem centred_interp_edge (π : (Fin 2 → X) → ℝ) {L ρ : ℝ} (hL : 0 ≤ L) (hρ : 0 ≤ ρ)
    {j : ℕ} (hj : 1 ≤ j)
    (h1 : ∀ f g : X → ℝ, |centredForm π f g| ≤
      L * DensityUpgrade.conditioningNorm 1 f * DensityUpgrade.conditioningNorm 1 g)
    (h2 : ∀ f g : X → ℝ, |centredForm π f g| ≤
      ρ * DensityUpgrade.conditioningNorm 2 f * DensityUpgrade.conditioningNorm 2 g) :
    ∀ f g : X → ℝ, ∑ a, f a = 0 → ∑ a, g a = 0 →
      |∑ x, π x * (f (x 0) * g (x 1))| ≤
        L ^ (((j : ℝ) - 1) / ((j : ℝ) + 1)) * ρ ^ ((2 : ℝ) / ((j : ℝ) + 1)) *
          DensityUpgrade.conditioningNorm (1 + 1 / (j : ℝ)) f *
          DensityUpgrade.conditioningNorm (1 + 1 / (j : ℝ)) g := by
  intro f g hf _
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have ht0 : (0 : ℝ) ≤ 2 / ((j : ℝ) + 1) := by positivity
  have ht1 : 2 / ((j : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hr : 1 / (1 + 1 / (j : ℝ)) = (1 - 2 / ((j : ℝ) + 1)) / 1 + 2 / ((j : ℝ) + 1) / 2 := by
    field_simp
    ring
  have key := centred_interp π hL hρ ht0 ht1 hr h1 h2 f g
  have he : 1 - 2 / ((j : ℝ) + 1) = ((j : ℝ) - 1) / ((j : ℝ) + 1) := by
    field_simp
    ring
  rwa [he, centredForm_of_mean_zero π g hf] at key

/-- **`lem:density:edge-moment` from the endpoint bounds.** A pair law with uniform coordinates
whose centred form has `L¹ × L¹` norm at most `L` and `L² × L²` norm at most `ρ`, under the gate
`j^{j+1} L^{j−1} ρ² ≤ 1`, has unit mixed `L^{1+1/j}`. The interpolation hypothesis of
`EdgeGate.edge_moment_of_interpolation` is discharged by `centred_interp_edge`. -/
theorem edge_moment_of_endpoints [DecidableEq X] [Nonempty X] (π : (Fin 2 → X) → ℝ)
    (hπ : ∀ x, 0 ≤ π x) (hπu : DensityUpgrade.conditioningUniformCoords π) {j : ℕ} (hj : 1 ≤ j)
    {L ρ : ℝ} (hL : 0 ≤ L) (hρ : 0 ≤ ρ) (hgate : (j : ℝ) ^ (j + 1) * L ^ (j - 1) * ρ ^ 2 ≤ 1)
    (h1 : ∀ f g : X → ℝ, |centredForm π f g| ≤
      L * DensityUpgrade.conditioningNorm 1 f * DensityUpgrade.conditioningNorm 1 g)
    (h2 : ∀ f g : X → ℝ, |centredForm π f g| ≤
      ρ * DensityUpgrade.conditioningNorm 2 f * DensityUpgrade.conditioningNorm 2 g) :
    DensityUpgrade.conditioningUnitMixed π (1 + 1 / (j : ℝ)) :=
  EdgeGate.edge_moment_of_interpolation π hπ hπu hj hL hρ hgate
    (centred_interp_edge π hL hρ hj h1 h2)

end Sarkozy.Interpolation
