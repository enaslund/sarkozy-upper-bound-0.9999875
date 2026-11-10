module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.BigOperators.Field
public import Sarkozy.Comparison.FoldedEnergy

/-!
# Coupled spectator estimate (`lem:density:coupled`)

`lem:density:coupled` (`paper/sections/31_density_induction_upgrade.tex`) bounds a signed
change in the sharp form `eq:record:sharp` in the presence of a positive spectator law `κ`
coupled to it through an outside reference `O`.

## Representation

* `d` slots `Fin d`; selected labels `x : Fin d → X`, spectator labels `z : Fin d → Y`, with
  `X`, `Y` finite slot alphabets; the outside alphabet is an arbitrary type `W`.
* The outside reference enters only through its multilinear functional
  `Λ : (Fin d → W → ℝ) → ℝ` (the paper's `Λ_O`) and its energy
  `coupledEnergy Λ g = Λ (fun _ => g)` (the paper's `Z_O(g)`, all slots carrying `g`).
  No linearity of `Λ` is used.
* Laws are finite weights: the selected sharp signed law `K`, its two full actual folded laws
  `λ₊ = lp`, `λ₋ = lm` on `Fin d → X`, and the spectator law `κ` on `Fin d → Y`. Integration is
  `∑ x, K x * F x`; the coupled law is `K ⊗ κ`, with integral `∑ x, ∑ z, K x * κ z * F x z`.
* The folds `f₊ = fp`, `f₋ = fm : Fin d → Fin d` (`φ^c_±` of `def:sorting` at the balanced cut)
  enter only through the copying property `#f₊⁻¹(v) + #f₋⁻¹(v) = 2` (`coupledCopying`,
  `lem:record:folded-energy` (e)).
* The inputs are `h v x y : W → ℝ` (the paper's `h_v(x, z, ·)`), the numbers `a v x y ≥ 0`
  and the constants `b v ≥ 0`.

## Named analytic inputs

* `coupledSharpBracket` — the sharp bracket of `K` with constant `δ`, in its folded-energy
  form (`lem:record:folded-energy` (a), applied to `K ⊗ O`, shared labels integrated in the
  full folded laws): for all slot inputs `g`, `|∫ Λ_O((g_v(x_v,·))_v) dK| ≤ δ E₊^{1/2} E₋^{1/2}`
  with `E± = ∫ Λ_O((g_{f±(u)}(x_u,·))_u) dλ±`.
* `coupledOutsideHolder` — the outside signed Hölder inequality (`lem:record:holder` (a)):
  `Z_O(g) ≥ 0` and `|Λ_O((g_v)_v)| ≤ ∏_v Z_O(g_v)^{1/d}`.
* `coupledUnitMixed` — unit mixed `L^r` norm (`def:density:mixed-moment`), here with
  `r = d/θ`, for `λ₊`, `λ₋` and `κ`.

## Main result

* `coupled_spectator_estimate` — `lem:density:coupled`:
  `|∫ Λ_O((h_v)_v) d(K ⊗ κ)| ≤ δ ∏_v b_v ∏_v (E_{x,z} a_v(x,z))^{θ/d}`.
* `coupled_conditional_bound` — the bound at a fixed spectator tuple `z` (the first part of the
  proof): `|∫ Λ_O((h_v(x_v,z_v,·))_v) dK(x)| ≤ δ ∏_v b_v (E_x a_v(x,z_v))^{θ/d}`.

## Connection to the project's folded energies

* `coupledCopying_cut` — the folds `ReflectionCut.foldPlus`, `ReflectionCut.foldMinus` of a cut
  have the copying property (from `Sarkozy.Comparison.sum_folds`).
* `coupledSharpBracket_of_sharp` — `coupledSharpBracket` holds when `K` is
  `Sarkozy.Comparison.Sharp` at the cut and `O` is reflection positive there; the folded laws
  are the diagonal laws of the half marginals (a single shared label). It is
  `Sarkozy.Comparison.folded_energy` with two atoms, via the Fubini identity
  `coupled_two_atom`.
* `coupled_spectator_estimate_cut` — the lemma in those terms; only the outside Hölder
  inequality and the three unit mixed moments remain hypotheses.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.DensityUpgrade

section Means

variable {X : Type*} [Fintype X]

/-- The uniform expectation `E_x f(x)` on a finite slot alphabet. -/
noncomputable def coupledMean (f : X → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card X

/-- The norm `‖f‖_{L^r(X)}` for the uniform probability measure on the finite alphabet `X`
(`def:density:mixed-moment`). -/
noncomputable def coupledLpNorm (r : ℝ) (f : X → ℝ) : ℝ :=
  coupledMean (fun x => |f x| ^ r) ^ (1 / r)

theorem coupledMean_nonneg {f : X → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ coupledMean f :=
  div_nonneg (Finset.sum_nonneg fun x _ => hf x) (Nat.cast_nonneg _)

/-- For `a ≥ 0`, `‖a^{θ/d}‖_{L^{d/θ}} = (E a)^{θ/d}`. -/
theorem coupledLpNorm_rpow {d θ : ℝ} (hd : d ≠ 0) (hθ : θ ≠ 0) {f : X → ℝ}
    (hf : ∀ x, 0 ≤ f x) :
    coupledLpNorm (d / θ) (fun x => f x ^ (θ / d)) = coupledMean f ^ (θ / d) := by
  unfold coupledLpNorm
  have hinv : 1 / (d / θ) = θ / d := one_div_div d θ
  have hone : θ / d * (d / θ) = 1 := by field_simp
  have hpt : (fun x => |f x ^ (θ / d)| ^ (d / θ)) = f := by
    funext x
    rw [abs_of_nonneg (Real.rpow_nonneg (hf x) _), ← Real.rpow_mul (hf x), hone,
      Real.rpow_one]
  rw [hpt, hinv]

variable {Y : Type*} [Fintype Y]

/-- Iterated uniform expectations are the joint uniform expectation:
`E_y E_x f(x,y) = E_{x,y} f(x,y)`. -/
theorem coupledMean_iterate (f : X → Y → ℝ) :
    coupledMean (fun y => coupledMean fun x => f x y) =
      coupledMean (fun p : X × Y => f p.1 p.2) := by
  simp only [coupledMean, Fintype.card_prod, Fintype.sum_prod_type_right, Nat.cast_mul]
  rw [← Finset.sum_div, div_div]

end Means

section Definitions

variable {d : ℕ} {X W : Type*} [Fintype X]

/-- **Unit mixed `L^r` norm** (`def:density:mixed-moment`): the weights `π` on `X^d` satisfy
`|∫ ∏_v f_v(x_v) dπ(x)| ≤ ∏_v ‖f_v‖_{L^r(X)}` for all real functions `f_v`, norms for the
uniform probability measure on `X`. (The paper's standing requirements that `π` be a
probability measure with uniform coordinates are not part of this predicate; they are not
used below.) -/
def coupledUnitMixed (r : ℝ) (π : (Fin d → X) → ℝ) : Prop :=
  ∀ f : Fin d → X → ℝ, |∑ x, π x * ∏ v, f v (x v)| ≤ ∏ v, coupledLpNorm r (f v)

/-- The outside energy `Z_O(g) = Λ_O((g)_v)`: every slot carries the same input. -/
def coupledEnergy (Λ : (Fin d → W → ℝ) → ℝ) (g : W → ℝ) : ℝ :=
  Λ fun _ => g

/-- **Outside signed Hölder inequality** (`lem:record:holder` (a), for the outside reference
`O`; the paper requires it separately in `lem:density:coupled`, supplied by the current
outside reference): energies are nonnegative and `|Λ_O((g_v)_v)| ≤ ∏_v Z_O(g_v)^{1/d}`. -/
def coupledOutsideHolder (Λ : (Fin d → W → ℝ) → ℝ) : Prop :=
  (∀ g : W → ℝ, 0 ≤ coupledEnergy Λ g) ∧
    ∀ g : Fin d → W → ℝ, |Λ g| ≤ ∏ v, coupledEnergy Λ (g v) ^ (1 / (d : ℝ))

/-- **Sharp bracket of `K` in its folded-energy form** (`lem:record:folded-energy` (a), applied
to `K ⊗ O` at the balanced cut, with folds `fp = φ₊`, `fm = φ₋`, bracket constant `δ`, and
full actual folded laws `lp = λ₊`, `lm = λ₋` in which the shared labels are already
integrated): for all slot inputs `g v x : W → ℝ`,
`|∫ Λ_O((g_v(x_v,·))_v) dK(x)| ≤ δ E₊^{1/2} E₋^{1/2}`, where
`E± = ∫ Λ_O((g_{f±(u)}(x_u,·))_u) dλ±(x)` are the two folded energies. (The nonnegativity
of `E±`, also part of (a), is not needed.) -/
def coupledSharpBracket (Λ : (Fin d → W → ℝ) → ℝ) (K lp lm : (Fin d → X) → ℝ)
    (fp fm : Fin d → Fin d) (δ : ℝ) : Prop :=
  ∀ g : Fin d → X → W → ℝ,
    |∑ x, K x * Λ (fun v => g v (x v))| ≤
      δ * Real.sqrt (∑ x, lp x * Λ (fun u => g (fp u) (x u))) *
        Real.sqrt (∑ x, lm x * Λ (fun u => g (fm u) (x u)))

end Definitions

section Copying

variable {d : ℕ}

/-- **Copying of the folds** (`lem:record:folded-energy` (e)): every slot `v` has
`#f₊⁻¹(v) + #f₋⁻¹(v) = 2` preimages in total. -/
def coupledCopying (fp fm : Fin d → Fin d) : Prop :=
  ∀ v, (Finset.univ.filter fun u => fp u = v).card +
    (Finset.univ.filter fun u => fm u = v).card = 2

/-- The multiplicative copying identity `∏_u c(f₊ u) ∏_u c(f₋ u) = ∏_v c(v)^2`. -/
theorem coupled_prod_folds {fp fm : Fin d → Fin d} (hcopy : coupledCopying fp fm)
    (c : Fin d → ℝ) : (∏ u, c (fp u)) * ∏ u, c (fm u) = ∏ v, c v ^ 2 := by
  rw [← Finset.prod_fiberwise' Finset.univ fp c, ← Finset.prod_fiberwise' Finset.univ fm c,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Finset.prod_const, Finset.prod_const, ← pow_add, hcopy v]

/-- The folds `φ^c_±` of a reflection cut `c` of the slots (`def:sorting`, the project's
`ReflectionCut.foldPlus`, `ReflectionCut.foldMinus`) have the copying property; this is the
additive copying identity `Sarkozy.Comparison.sum_folds` (`lem:record:folded-energy` (e))
applied to the indicator of a slot. -/
theorem coupledCopying_cut (c : ReflectionCut (Fin d)) :
    coupledCopying c.foldPlus c.foldMinus := by
  intro v
  have h := Sarkozy.Comparison.sum_folds c (fun w => if w = v then (1 : ℝ) else 0)
  simp only [Finset.sum_boole] at h
  have h1 : (Finset.univ.filter fun w : Fin d => w = v).card = 1 := by
    rw [Finset.filter_eq' Finset.univ v]
    simp
  rw [h1, Nat.cast_one, mul_one] at h
  have h2 : (((Finset.univ.filter fun u => c.foldPlus u = v).card +
      (Finset.univ.filter fun u => c.foldMinus u = v).card : ℕ) : ℝ) = ((2 : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast h2

end Copying

section Estimate

variable {d : ℕ} {X Y W : Type*} [Fintype X] [Fintype Y]

/-- **One folded energy** (the plus or minus step of the proof): outside signed Hölder on each
term, the pointwise hypothesis `Z_O(g_v(x,·))^{1/d} ≤ b_v α_v(x)^{θ/d}`, and the unit mixed
`L^{d/θ}` moment of the nonnegative folded law `λ` give
`E = ∫ Λ_O((g_{f(u)}(x_u,·))_u) dλ ≤ ∏_u b_{f(u)} (E_x α_{f(u)}(x))^{θ/d}`. -/
theorem coupled_folded_energy_le {Λ : (Fin d → W → ℝ) → ℝ} (hhol : coupledOutsideHolder Λ)
    {θ : ℝ} (hθ : θ ≠ 0) {lam : (Fin d → X) → ℝ} (hlam : ∀ x, 0 ≤ lam x)
    (hmix : coupledUnitMixed ((d : ℝ) / θ) lam) (f : Fin d → Fin d)
    (g : Fin d → X → W → ℝ) {α : Fin d → X → ℝ} {b : Fin d → ℝ} (hα : ∀ v x, 0 ≤ α v x)
    (hb : ∀ v, 0 ≤ b v)
    (hZ : ∀ v x, coupledEnergy Λ (g v x) ^ (1 / (d : ℝ)) ≤ b v * α v x ^ (θ / d)) :
    ∑ x, lam x * Λ (fun u => g (f u) (x u)) ≤
      ∏ u, (b (f u) * coupledMean (α (f u)) ^ (θ / d)) := by
  -- pointwise: outside signed Hölder and the hypothesis on the inputs
  have hpt : ∀ x : Fin d → X, Λ (fun u => g (f u) (x u)) ≤
      ∏ u, (b (f u) * α (f u) (x u) ^ (θ / d)) := by
    intro x
    calc Λ (fun u => g (f u) (x u)) ≤ |Λ (fun u => g (f u) (x u))| := le_abs_self _
      _ ≤ ∏ u, coupledEnergy Λ (g (f u) (x u)) ^ (1 / (d : ℝ)) := hhol.2 _
      _ ≤ ∏ u, (b (f u) * α (f u) (x u) ^ (θ / d)) :=
          Finset.prod_le_prod₀ (fun u _ => Real.rpow_nonneg (hhol.1 _) _)
            (fun u _ => hZ (f u) (x u))
  -- the unit mixed moment of the folded law
  have hmom := hmix (fun u y => α (f u) y ^ (θ / d))
  have hnorm : ∀ u : Fin d, coupledLpNorm ((d : ℝ) / θ) (fun y => α (f u) y ^ (θ / d)) =
      coupledMean (α (f u)) ^ (θ / d) := by
    intro u
    have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fin.pos u).ne'
    exact coupledLpNorm_rpow hd hθ (hα (f u))
  simp only [hnorm] at hmom
  have hB : 0 ≤ ∏ u, b (f u) := Finset.prod_nonneg fun u _ => hb (f u)
  calc ∑ x, lam x * Λ (fun u => g (f u) (x u))
      ≤ ∑ x, lam x * ∏ u, (b (f u) * α (f u) (x u) ^ (θ / d)) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpt x) (hlam x)
    _ = (∏ u, b (f u)) * ∑ x, lam x * ∏ u, α (f u) (x u) ^ (θ / d) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.prod_mul_distrib]
        ring
    _ ≤ (∏ u, b (f u)) * |∑ x, lam x * ∏ u, α (f u) (x u) ^ (θ / d)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hB
    _ ≤ (∏ u, b (f u)) * ∏ u, coupledMean (α (f u)) ^ (θ / d) :=
        mul_le_mul_of_nonneg_left hmom hB
    _ = ∏ u, (b (f u) * coupledMean (α (f u)) ^ (θ / d)) :=
        (Finset.prod_mul_distrib).symm

omit [Fintype Y] in
/-- **The conditional bound at a fixed spectator tuple `z`** (first part of the proof of
`lem:density:coupled`): the sharp bracket, outside Hölder on each folded energy, the unit
mixed moments of `λ±`, and the copying of the folds give
`|∫ Λ_O((h_v(x_v,z_v,·))_v) dK(x)| ≤ δ ∏_v b_v (E_x a_v(x,z_v))^{θ/d}`. -/
theorem coupled_conditional_bound {Λ : (Fin d → W → ℝ) → ℝ} {K lp lm : (Fin d → X) → ℝ}
    {fp fm : Fin d → Fin d} {δ θ : ℝ} (hδ : 0 ≤ δ) (hθ : θ ≠ 0)
    (hcopy : coupledCopying fp fm) (hbr : coupledSharpBracket Λ K lp lm fp fm δ)
    (hhol : coupledOutsideHolder Λ) (hlp : ∀ x, 0 ≤ lp x) (hlm : ∀ x, 0 ≤ lm x)
    (hmp : coupledUnitMixed ((d : ℝ) / θ) lp) (hmm : coupledUnitMixed ((d : ℝ) / θ) lm)
    {h : Fin d → X → Y → W → ℝ} {a : Fin d → X → Y → ℝ} {b : Fin d → ℝ}
    (ha : ∀ v x y, 0 ≤ a v x y) (hb : ∀ v, 0 ≤ b v)
    (hZ : ∀ v x y, coupledEnergy Λ (h v x y) ^ (1 / (d : ℝ)) ≤ b v * a v x y ^ (θ / d))
    (z : Fin d → Y) :
    |∑ x, K x * Λ (fun v => h v (x v) (z v))| ≤
      δ * ∏ v, (b v * coupledMean (fun x => a v x (z v)) ^ (θ / d)) := by
  set g : Fin d → X → W → ℝ := fun v x => h v x (z v) with hg
  set α : Fin d → X → ℝ := fun v x => a v x (z v) with hαdef
  set c : Fin d → ℝ := fun v => b v * coupledMean (α v) ^ (θ / d) with hc
  have hα : ∀ v x, 0 ≤ α v x := fun v x => ha v x (z v)
  have hZ' : ∀ v x, coupledEnergy Λ (g v x) ^ (1 / (d : ℝ)) ≤ b v * α v x ^ (θ / d) :=
    fun v x => hZ v x (z v)
  have hcn : ∀ v, 0 ≤ c v := fun v =>
    mul_nonneg (hb v) (Real.rpow_nonneg (coupledMean_nonneg (hα v)) _)
  have hEp := coupled_folded_energy_le hhol hθ hlp hmp fp g hα hb hZ'
  have hEm := coupled_folded_energy_le hhol hθ hlm hmm fm g hα hb hZ'
  have hPp : 0 ≤ ∏ u, c (fp u) := Finset.prod_nonneg fun u _ => hcn (fp u)
  have hP : 0 ≤ ∏ v, c v := Finset.prod_nonneg fun v _ => hcn v
  have hsq : Real.sqrt (∏ u, c (fp u)) * Real.sqrt (∏ u, c (fm u)) = ∏ v, c v := by
    rw [← Real.sqrt_mul hPp, coupled_prod_folds hcopy c, Finset.prod_pow, Real.sqrt_sq hP]
  calc |∑ x, K x * Λ (fun v => h v (x v) (z v))|
      ≤ δ * Real.sqrt (∑ x, lp x * Λ (fun u => g (fp u) (x u))) *
          Real.sqrt (∑ x, lm x * Λ (fun u => g (fm u) (x u))) := hbr g
    _ ≤ δ * Real.sqrt (∏ u, c (fp u)) * Real.sqrt (∏ u, c (fm u)) := by
        gcongr
    _ = δ * ∏ v, c v := by rw [mul_assoc, hsq]

/-- **`lem:density:coupled` (Coupled spectator estimate).** Let `Λ` be the multilinear
functional of an outside reference `O` satisfying the outside signed Hölder inequality, `K` a
selected sharp signed law with bracket constant `δ ≥ 0` relative to its two full actual folded
laws `λ₊ = lp`, `λ₋ = lm` (nonnegative, folds `fp`, `fm` with the copying property), and `κ`
a positive spectator law. Suppose `λ₊`, `λ₋`, `κ` have unit mixed `L^{d/θ}`. If
`Z_O(h_v(x,z,·))^{1/d} ≤ b_v a_v(x,z)^{θ/d}` with `a_v ≥ 0` and `b_v ≥ 0` independent of the
labels, then `|∫ Λ_O((h_v)_v) d(K ⊗ κ)| ≤ δ ∏_v b_v ∏_v (E_{x,z} a_v(x,z))^{θ/d}`, the
expectations uniform in each slot alphabet. No moment hypothesis is used for a fold of `κ`. -/
theorem coupled_spectator_estimate {Λ : (Fin d → W → ℝ) → ℝ} {K lp lm : (Fin d → X) → ℝ}
    {κ : (Fin d → Y) → ℝ} {fp fm : Fin d → Fin d} {δ θ : ℝ} (hδ : 0 ≤ δ) (hθ : θ ≠ 0)
    (hcopy : coupledCopying fp fm) (hbr : coupledSharpBracket Λ K lp lm fp fm δ)
    (hhol : coupledOutsideHolder Λ) (hlp : ∀ x, 0 ≤ lp x) (hlm : ∀ x, 0 ≤ lm x)
    (hκ : ∀ z, 0 ≤ κ z) (hmp : coupledUnitMixed ((d : ℝ) / θ) lp)
    (hmm : coupledUnitMixed ((d : ℝ) / θ) lm) (hmκ : coupledUnitMixed ((d : ℝ) / θ) κ)
    {h : Fin d → X → Y → W → ℝ} {a : Fin d → X → Y → ℝ} {b : Fin d → ℝ}
    (ha : ∀ v x y, 0 ≤ a v x y) (hb : ∀ v, 0 ≤ b v)
    (hZ : ∀ v x y, coupledEnergy Λ (h v x y) ^ (1 / (d : ℝ)) ≤ b v * a v x y ^ (θ / d)) :
    |∑ x, ∑ z, K x * κ z * Λ (fun v => h v (x v) (z v))| ≤
      δ * (∏ v, b v) * ∏ v, coupledMean (fun p : X × Y => a v p.1 p.2) ^ (θ / d) := by
  set T : (Fin d → Y) → ℝ := fun z => ∑ x, K x * Λ (fun v => h v (x v) (z v)) with hT
  set G : Fin d → Y → ℝ := fun v y => coupledMean (fun x => a v x y) ^ (θ / d) with hG
  have hswap : ∑ x, ∑ z, K x * κ z * Λ (fun v => h v (x v) (z v)) = ∑ z, κ z * T z := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [hT, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hcond : ∀ z, |T z| ≤ δ * (∏ v, b v) * ∏ v, G v (z v) := by
    intro z
    have h1 := coupled_conditional_bound hδ hθ hcopy hbr hhol hlp hlm hmp hmm ha hb hZ z
    rw [Finset.prod_mul_distrib, ← mul_assoc] at h1
    exact h1
  have hDB : 0 ≤ δ * ∏ v, b v := mul_nonneg hδ (Finset.prod_nonneg fun v _ => hb v)
  -- the unit mixed moment of `κ`
  have hmom := hmκ G
  have hnorm : ∀ v : Fin d, coupledLpNorm ((d : ℝ) / θ) (G v) =
      coupledMean (fun p : X × Y => a v p.1 p.2) ^ (θ / d) := by
    intro v
    have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fin.pos v).ne'
    rw [hG, coupledLpNorm_rpow hd hθ (fun y => coupledMean_nonneg fun x => ha v x y),
      coupledMean_iterate]
  simp only [hnorm] at hmom
  rw [hswap]
  calc |∑ z, κ z * T z| ≤ ∑ z, |κ z * T z| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ z, κ z * |T z| := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [abs_mul, abs_of_nonneg (hκ z)]
    _ ≤ ∑ z, κ z * (δ * (∏ v, b v) * ∏ v, G v (z v)) :=
        Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hcond z) (hκ z)
    _ = δ * (∏ v, b v) * ∑ z, κ z * ∏ v, G v (z v) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun z _ => by ring
    _ ≤ δ * (∏ v, b v) * |∑ z, κ z * ∏ v, G v (z v)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hDB
    _ ≤ δ * (∏ v, b v) * ∏ v, coupledMean (fun p : X × Y => a v p.1 p.2) ^ (θ / d) :=
        mul_le_mul_of_nonneg_left hmom hDB

end Estimate

section FoldedEnergyBridge

universe u

/-- The label types of the two atoms of `K ⊗ O`: `true` the selected atom, `false` the
outside reference. -/
abbrev coupledAtom (X W : Type u) : Bool → Type u := fun b => cond b X W

instance coupledAtom.instFintype {X W : Type u} [Fintype X] [Fintype W] :
    ∀ b, Fintype (coupledAtom X W b)
  | true => inferInstanceAs (Fintype X)
  | false => inferInstanceAs (Fintype W)

instance coupledAtom.instDecidableEq {X W : Type u} [DecidableEq X] [DecidableEq W] :
    ∀ b, DecidableEq (coupledAtom X W b)
  | true => inferInstanceAs (DecidableEq X)
  | false => inferInstanceAs (DecidableEq W)

variable {d : ℕ} {X W : Type u} [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]

/-- The configurations of the two atoms are pairs. -/
def coupledSplit : (∀ b, Fin d → coupledAtom X W b) ≃ (Fin d → X) × (Fin d → W) where
  toFun z := (z true, z false)
  invFun p := fun b => match b with
    | true => p.1
    | false => p.2
  left_inv z := by funext b; cases b <;> rfl
  right_inv _ := rfl

/-- Fubini for the two atoms. -/
theorem coupled_two_atom (L : ∀ b, ((Fin d → coupledAtom X W b) → ℝ) →ₗ[ℝ] ℝ)
    (G : Fin d → X → W → ℝ) :
    multilinearIntegral (tensorLaw L) (fun v p => G v (p true) (p false)) =
      ∑ x : Fin d → X, lawDensity (L true) x * L false (fun w => ∏ v, G v (x v) (w v)) := by
  rw [multilinearIntegral, RecordExpansion.tensorLaw_apply]
  rw [Fintype.sum_equiv (coupledSplit (d := d) (X := X) (W := W)) _
    (fun p => lawDensity (L true) p.1 * lawDensity (L false) p.2 *
      ∏ v, G v (p.1 v) (p.2 v)) (fun z => by rw [Fintype.prod_bool]; rfl)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [linearFunctional_density (L false), Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [lawDensity]
  ring

/-- The two laws `(L₁, L₂)` as a family over the two atoms. -/
def coupledPair (L₁ : ((Fin d → X) → ℝ) →ₗ[ℝ] ℝ) (L₂ : ((Fin d → W) → ℝ) →ₗ[ℝ] ℝ) :
    ∀ b, ((Fin d → coupledAtom X W b) → ℝ) →ₗ[ℝ] ℝ
  | true => L₁
  | false => L₂

/-- Half marginals on the selected atom; the outside atom (positive) carries none. -/
def coupledHalf (c : ReflectionCut (Fin d)) (m : (c.Half → X) → ℝ) :
    ∀ b, (c.Half → coupledAtom X W b) → ℝ
  | true => m
  | false => fun _ => 0

/-- **`coupledSharpBracket` from the project's folded-energy lemma.** For a selected law `K`
(a linear functional on `(Fin d → X) → ℝ`) that is `Sharp` at the cut `c` with constant `δ`
relative to the half marginals `mp`, `mm` (`eq:record:sharp`), and an outside law `O` reflection
positive at `c`, `Sarkozy.Comparison.folded_energy` (`lem:record:folded-energy` (a), two
atoms, the sharp block `{true}`) gives `coupledSharpBracket` for `Λ = multilinearIntegral O`,
the weights of `K`, the weights of the diagonal laws of `mp`, `mm` as `λ₊`, `λ₋`, and the folds
of `c`. (Shared labels are not included here: this is the case of a single shared label.) -/
theorem coupledSharpBracket_of_sharp (c : ReflectionCut (Fin d))
    (K : ((Fin d → X) → ℝ) →ₗ[ℝ] ℝ) (O : ((Fin d → W) → ℝ) →ₗ[ℝ] ℝ)
    {mp mm : (c.Half → X) → ℝ} (hmp : ∀ x, 0 ≤ mp x) (hmm : ∀ x, 0 ≤ mm x) {δ : ℝ}
    (hδ : 0 ≤ δ) (hsharp : Comparison.Sharp c K mp mm δ) (hO : c.Positive O) :
    coupledSharpBracket (multilinearIntegral O) (lawDensity K)
      (lawDensity (c.diagonalLaw mp)) (lawDensity (c.diagonalLaw mm)) c.foldPlus c.foldMinus
      δ := by
  intro g
  have hE : ∀ j ∈ ({true} : Finset Bool), j = true := fun j hj => Finset.mem_singleton.mp hj
  have h3 := (Comparison.folded_energy c {true} (coupledPair (W := W) K O)
    (coupledHalf (W := W) c mp) (coupledHalf (W := W) c mm) (fun _ => δ) (fun _ _ => hδ)
    (fun j hj x => by obtain rfl := hE j hj; exact hmp x)
    (fun j hj x => by obtain rfl := hE j hj; exact hmm x)
    (fun j hj => by obtain rfl := hE j hj; exact hsharp)
    (fun j hj => by
      cases j
      · exact hO
      · exact absurd (Finset.mem_singleton_self _) hj)
    (fun v p => g v (p true) (p false))).2.2
  rw [Finset.prod_singleton] at h3
  have eT : multilinearIntegral (tensorLaw (coupledPair (W := W) K O))
      (fun v p => g v (p true) (p false)) =
      ∑ x, lawDensity K x * multilinearIntegral O (fun v => g v (x v)) :=
    coupled_two_atom _ g
  have eP : multilinearIntegral (tensorLaw fun j => if j ∈ ({true} : Finset Bool) then
      c.diagonalLaw (coupledHalf (W := W) c mp j) else coupledPair (W := W) K O j)
      (fun u p => g (c.foldPlus u) (p true) (p false)) =
      ∑ x, lawDensity (c.diagonalLaw mp) x *
        multilinearIntegral O (fun u => g (c.foldPlus u) (x u)) := by
    refine (coupled_two_atom _ (fun u => g (c.foldPlus u))).trans ?_
    rw [ite_eq_left (Finset.mem_singleton_self true), ite_eq_right (by simp)]
    rfl
  have eM : multilinearIntegral (tensorLaw fun j => if j ∈ ({true} : Finset Bool) then
      c.diagonalLaw (coupledHalf (W := W) c mm j) else coupledPair (W := W) K O j)
      (fun u p => g (c.foldMinus u) (p true) (p false)) =
      ∑ x, lawDensity (c.diagonalLaw mm) x *
        multilinearIntegral O (fun u => g (c.foldMinus u) (x u)) := by
    refine (coupled_two_atom _ (fun u => g (c.foldMinus u))).trans ?_
    rw [ite_eq_left (Finset.mem_singleton_self true), ite_eq_right (by simp)]
    rfl
  calc |∑ x, lawDensity K x * multilinearIntegral O (fun v => g v (x v))|
      = |multilinearIntegral (tensorLaw (coupledPair (W := W) K O))
          (fun v p => g v (p true) (p false))| := by rw [eT]
    _ ≤ δ * Real.sqrt (multilinearIntegral (tensorLaw fun j => if j ∈ ({true} : Finset Bool) then
          c.diagonalLaw (coupledHalf (W := W) c mp j) else coupledPair (W := W) K O j)
          (fun u p => g (c.foldPlus u) (p true) (p false))) *
        Real.sqrt (multilinearIntegral (tensorLaw fun j => if j ∈ ({true} : Finset Bool) then
          c.diagonalLaw (coupledHalf (W := W) c mm j) else coupledPair (W := W) K O j)
          (fun u p => g (c.foldMinus u) (p true) (p false))) := h3
    _ = _ := by rw [eP, eM]

omit [Fintype W] [DecidableEq W] in
/-- The weights of a diagonal law with nonnegative half marginal are nonnegative. -/
theorem coupled_diagonalLaw_nonneg (c : ReflectionCut (Fin d)) {m : (c.Half → X) → ℝ}
    (hm : ∀ x, 0 ≤ m x) (y : Fin d → X) : 0 ≤ lawDensity (c.diagonalLaw m) y := by
  show 0 ≤ ∑ x, m x * (if c.join x x = y then (1 : ℝ) else 0)
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hm x) (by split_ifs <;> norm_num)

/-- **`lem:density:coupled` for the project's sharp law and outside reference.** The selected
law `K` is `Sharp` at the cut `c` of the slots with constant `δ` relative to nonnegative half
marginals `mp`, `mm`; its full actual folded laws are the diagonal laws `c.diagonalLaw mp`,
`c.diagonalLaw mm` (one shared label); the outside reference `O` is reflection positive at
`c`, and its multilinear functional satisfies the outside signed Hölder inequality. The sharp
bracket (`coupledSharpBracket_of_sharp`) and the copying (`coupledCopying_cut`) are then
proved, and `coupled_spectator_estimate` applies. -/
theorem coupled_spectator_estimate_cut {Y : Type*} [Fintype Y] (c : ReflectionCut (Fin d))
    (K : ((Fin d → X) → ℝ) →ₗ[ℝ] ℝ) (O : ((Fin d → W) → ℝ) →ₗ[ℝ] ℝ) {κ : (Fin d → Y) → ℝ}
    {mp mm : (c.Half → X) → ℝ} (hmp : ∀ x, 0 ≤ mp x) (hmm : ∀ x, 0 ≤ mm x) {δ θ : ℝ}
    (hδ : 0 ≤ δ) (hθ : θ ≠ 0) (hsharp : Comparison.Sharp c K mp mm δ) (hO : c.Positive O)
    (hhol : coupledOutsideHolder (multilinearIntegral O)) (hκ : ∀ z, 0 ≤ κ z)
    (hmp' : coupledUnitMixed ((d : ℝ) / θ) (lawDensity (c.diagonalLaw mp)))
    (hmm' : coupledUnitMixed ((d : ℝ) / θ) (lawDensity (c.diagonalLaw mm)))
    (hmκ : coupledUnitMixed ((d : ℝ) / θ) κ)
    {h : Fin d → X → Y → W → ℝ} {a : Fin d → X → Y → ℝ} {b : Fin d → ℝ}
    (ha : ∀ v x y, 0 ≤ a v x y) (hb : ∀ v, 0 ≤ b v)
    (hZ : ∀ v x y, coupledEnergy (multilinearIntegral O) (h v x y) ^ (1 / (d : ℝ)) ≤
      b v * a v x y ^ (θ / d)) :
    |∑ x, ∑ z, lawDensity K x * κ z * multilinearIntegral O (fun v => h v (x v) (z v))| ≤
      δ * (∏ v, b v) * ∏ v, coupledMean (fun p : X × Y => a v p.1 p.2) ^ (θ / d) :=
  coupled_spectator_estimate hδ hθ (coupledCopying_cut c)
    (coupledSharpBracket_of_sharp c K O hmp hmm hδ hsharp hO) hhol
    (coupled_diagonalLaw_nonneg c hmp) (coupled_diagonalLaw_nonneg c hmm) hκ hmp' hmm' hmκ
    ha hb hZ

end FoldedEnergyBridge

end Sarkozy.DensityUpgrade
