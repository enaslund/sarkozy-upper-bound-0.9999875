module

public import Sarkozy.DensityUpgrade.Coupled
public import Sarkozy.TheoremC.Defs

/-!
# `lem:density:coupled` on the 72 slots, for the sharp decompositions of `HasSharpBound`

`paper/sections/31_density_induction_upgrade.tex`, `lem:density:coupled`, with the sharp bound
of `def:price`(b) (`TheoremC.HasSharpBound`). WP-FI's `Sarkozy/DensityUpgrade/Coupled.lean`
proves the lemma for slots `Fin d` and one shared label. Here:

* **General slots.** The definitions and the estimate are restated for an arbitrary finite slot
  type `V` (`coupledUnitMixedV`, `coupledOutsideHolderV`, `coupledSharpBracketV`,
  `coupledCopyingV`, `coupled_spectator_estimateV`), with `d = |V|`; the proofs are WP-FI's.
* **Shared labels.** `coupledSharpBracket_mixtureV`: the bracket passes to mixtures over the
  values of the shared labels, by Cauchy–Schwarz over `s`; `coupled_folded_energy_of_sharpV`:
  the folded energies of one sharp component are nonnegative and bound it
  (`Comparison.folded_energy` with two atoms).
* **`HasSharpBound`.** `coupled_spectator_estimate_sharpDecomp`: for a sharp decomposition
  `ζ = w ∑_s π_s K_s`, `κ = w ∑_s π_s κ_s` (`w = mass κ ≥ 0`, `κ_s` probability measures, `K_s`
  sharp with constant `d ≥ 0` relative to the half marginals of `κ_s`), an outside reference `O`
  positive at the cut with the outside signed Hölder inequality, a nonnegative spectator `κ'`, and
  unit mixed `L^{72/θ}` of the normalized full folded laws
  `λ̂± = ∑_s π_s Diag(m±(κ_s))` and of `κ'`:
  `|∫ Λ_O((h_v)_v) d(ζ ⊗ κ')| ≤ w d ∏_v b_v ∏_v (E_{x,z} a_v(x,z))^{θ/72}`.
  `coupled_spectator_estimate_hasSharpBound` takes `HasSharpBound c κ ζ d` itself, with the
  moment hypothesis for every decomposition witness.

Hypotheses (as in the paper's statement): the outside signed Hölder inequality, reflection
positivity of `O` at the cut, and the unit mixed moments of the folded laws and of the
spectator. Positive records (uniform one-slot marginals of the `κ_s`) are **not** needed here:
only nonnegativity of the half marginals, which follows from `IsProbability`. Uniform
marginals would enter only through the unit mixed hypotheses on `λ̂±`, which the caller supplies.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.DensityMoments

open Sarkozy.DensityUpgrade Sarkozy.ReflectionCut

section Definitions

variable {V : Type*} [Fintype V] [DecidableEq V] {X W : Type*} [Fintype X]

/-- **Unit mixed `L^r` norm** on the slots `V` (`def:density:mixed-moment`), for weights `π`. -/
def coupledUnitMixedV (r : ℝ) (π : (V → X) → ℝ) : Prop :=
  ∀ f : V → X → ℝ, |∑ x, π x * ∏ v, f v (x v)| ≤ ∏ v, coupledLpNorm r (f v)

/-- The outside energy `Z_O(g) = Λ_O((g)_v)`. -/
def coupledEnergyV (Λ : (V → W → ℝ) → ℝ) (g : W → ℝ) : ℝ := Λ fun _ => g

/-- **Outside signed Hölder inequality** on `V`, with `d = |V|`. -/
def coupledOutsideHolderV (Λ : (V → W → ℝ) → ℝ) : Prop :=
  (∀ g : W → ℝ, 0 ≤ coupledEnergyV Λ g) ∧
    ∀ g : V → W → ℝ, |Λ g| ≤ ∏ v, coupledEnergyV Λ (g v) ^ (1 / (Fintype.card V : ℝ))

/-- **The sharp bracket in folded-energy form** on `V`. -/
def coupledSharpBracketV (Λ : (V → W → ℝ) → ℝ) (K lp lm : (V → X) → ℝ) (fp fm : V → V)
    (δ : ℝ) : Prop :=
  ∀ g : V → X → W → ℝ,
    |∑ x, K x * Λ (fun v => g v (x v))| ≤
      δ * Real.sqrt (∑ x, lp x * Λ (fun u => g (fp u) (x u))) *
        Real.sqrt (∑ x, lm x * Λ (fun u => g (fm u) (x u)))

end Definitions

section Copying

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Copying of the folds** on `V`: `#f₊⁻¹(v) + #f₋⁻¹(v) = 2`. -/
def coupledCopyingV (fp fm : V → V) : Prop :=
  ∀ v, (Finset.univ.filter fun u => fp u = v).card +
    (Finset.univ.filter fun u => fm u = v).card = 2

theorem coupled_prod_foldsV {fp fm : V → V} (hcopy : coupledCopyingV fp fm) (c : V → ℝ) :
    (∏ u, c (fp u)) * ∏ u, c (fm u) = ∏ v, c v ^ 2 := by
  rw [← Finset.prod_fiberwise' Finset.univ fp c, ← Finset.prod_fiberwise' Finset.univ fm c,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Finset.prod_const, Finset.prod_const, ← pow_add, hcopy v]

/-- The folds of a reflection cut have the copying property (`Comparison.sum_folds`). -/
theorem coupledCopying_cutV (c : ReflectionCut V) : coupledCopyingV c.foldPlus c.foldMinus := by
  intro v
  have h := Sarkozy.Comparison.sum_folds c (fun w => if w = v then (1 : ℝ) else 0)
  simp only [Finset.sum_boole] at h
  have h1 : (Finset.univ.filter fun w : V => w = v).card = 1 := by
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

variable {V : Type*} [Fintype V] [DecidableEq V] {X Y W : Type*} [Fintype X] [Fintype Y]

omit [DecidableEq V] in
theorem card_ne_zero_of_elem (u : V) : (Fintype.card V : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Fintype.card_pos_iff.mpr ⟨u⟩).ne'

/-- **One folded energy**, on `V`. -/
theorem coupled_folded_energy_leV {Λ : (V → W → ℝ) → ℝ} (hhol : coupledOutsideHolderV Λ)
    {θ : ℝ} (hθ : θ ≠ 0) {lam : (V → X) → ℝ} (hlam : ∀ x, 0 ≤ lam x)
    (hmix : coupledUnitMixedV ((Fintype.card V : ℝ) / θ) lam) (f : V → V)
    (g : V → X → W → ℝ) {α : V → X → ℝ} {b : V → ℝ} (hα : ∀ v x, 0 ≤ α v x)
    (hb : ∀ v, 0 ≤ b v)
    (hZ : ∀ v x, coupledEnergyV Λ (g v x) ^ (1 / (Fintype.card V : ℝ)) ≤
      b v * α v x ^ (θ / Fintype.card V)) :
    ∑ x, lam x * Λ (fun u => g (f u) (x u)) ≤
      ∏ u, (b (f u) * coupledMean (α (f u)) ^ (θ / Fintype.card V)) := by
  have hpt : ∀ x : V → X, Λ (fun u => g (f u) (x u)) ≤
      ∏ u, (b (f u) * α (f u) (x u) ^ (θ / Fintype.card V)) := by
    intro x
    calc Λ (fun u => g (f u) (x u)) ≤ |Λ (fun u => g (f u) (x u))| := le_abs_self _
      _ ≤ ∏ u, coupledEnergyV Λ (g (f u) (x u)) ^ (1 / (Fintype.card V : ℝ)) := hhol.2 _
      _ ≤ ∏ u, (b (f u) * α (f u) (x u) ^ (θ / Fintype.card V)) :=
          Finset.prod_le_prod₀ (fun u _ => Real.rpow_nonneg (hhol.1 _) _)
            (fun u _ => hZ (f u) (x u))
  have hmom := hmix (fun u y => α (f u) y ^ (θ / Fintype.card V))
  have hnorm : ∀ u : V, coupledLpNorm ((Fintype.card V : ℝ) / θ)
      (fun y => α (f u) y ^ (θ / Fintype.card V)) =
      coupledMean (α (f u)) ^ (θ / Fintype.card V) := fun u =>
    coupledLpNorm_rpow (card_ne_zero_of_elem u) hθ (hα (f u))
  simp only [hnorm] at hmom
  have hB : 0 ≤ ∏ u, b (f u) := Finset.prod_nonneg fun u _ => hb (f u)
  calc ∑ x, lam x * Λ (fun u => g (f u) (x u))
      ≤ ∑ x, lam x * ∏ u, (b (f u) * α (f u) (x u) ^ (θ / Fintype.card V)) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpt x) (hlam x)
    _ = (∏ u, b (f u)) * ∑ x, lam x * ∏ u, α (f u) (x u) ^ (θ / Fintype.card V) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.prod_mul_distrib]
        ring
    _ ≤ (∏ u, b (f u)) * |∑ x, lam x * ∏ u, α (f u) (x u) ^ (θ / Fintype.card V)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hB
    _ ≤ (∏ u, b (f u)) * ∏ u, coupledMean (α (f u)) ^ (θ / Fintype.card V) :=
        mul_le_mul_of_nonneg_left hmom hB
    _ = ∏ u, (b (f u) * coupledMean (α (f u)) ^ (θ / Fintype.card V)) :=
        (Finset.prod_mul_distrib).symm

omit [Fintype Y] in
/-- **The conditional bound at a fixed spectator tuple**, on `V`. -/
theorem coupled_conditional_boundV {Λ : (V → W → ℝ) → ℝ} {K lp lm : (V → X) → ℝ}
    {fp fm : V → V} {δ θ : ℝ} (hδ : 0 ≤ δ) (hθ : θ ≠ 0)
    (hcopy : coupledCopyingV fp fm) (hbr : coupledSharpBracketV Λ K lp lm fp fm δ)
    (hhol : coupledOutsideHolderV Λ) (hlp : ∀ x, 0 ≤ lp x) (hlm : ∀ x, 0 ≤ lm x)
    (hmp : coupledUnitMixedV ((Fintype.card V : ℝ) / θ) lp)
    (hmm : coupledUnitMixedV ((Fintype.card V : ℝ) / θ) lm)
    {h : V → X → Y → W → ℝ} {a : V → X → Y → ℝ} {b : V → ℝ}
    (ha : ∀ v x y, 0 ≤ a v x y) (hb : ∀ v, 0 ≤ b v)
    (hZ : ∀ v x y, coupledEnergyV Λ (h v x y) ^ (1 / (Fintype.card V : ℝ)) ≤
      b v * a v x y ^ (θ / Fintype.card V))
    (z : V → Y) :
    |∑ x, K x * Λ (fun v => h v (x v) (z v))| ≤
      δ * ∏ v, (b v * coupledMean (fun x => a v x (z v)) ^ (θ / Fintype.card V)) := by
  set g : V → X → W → ℝ := fun v x => h v x (z v) with hg
  set α : V → X → ℝ := fun v x => a v x (z v) with hαdef
  set c : V → ℝ := fun v => b v * coupledMean (α v) ^ (θ / Fintype.card V) with hc
  have hα : ∀ v x, 0 ≤ α v x := fun v x => ha v x (z v)
  have hZ' : ∀ v x, coupledEnergyV Λ (g v x) ^ (1 / (Fintype.card V : ℝ)) ≤
      b v * α v x ^ (θ / Fintype.card V) := fun v x => hZ v x (z v)
  have hcn : ∀ v, 0 ≤ c v := fun v =>
    mul_nonneg (hb v) (Real.rpow_nonneg (coupledMean_nonneg (hα v)) _)
  have hEp := coupled_folded_energy_leV hhol hθ hlp hmp fp g hα hb hZ'
  have hEm := coupled_folded_energy_leV hhol hθ hlm hmm fm g hα hb hZ'
  have hPp : 0 ≤ ∏ u, c (fp u) := Finset.prod_nonneg fun u _ => hcn (fp u)
  have hP : 0 ≤ ∏ v, c v := Finset.prod_nonneg fun v _ => hcn v
  have hsq : Real.sqrt (∏ u, c (fp u)) * Real.sqrt (∏ u, c (fm u)) = ∏ v, c v := by
    rw [← Real.sqrt_mul hPp, coupled_prod_foldsV hcopy c, Finset.prod_pow, Real.sqrt_sq hP]
  calc |∑ x, K x * Λ (fun v => h v (x v) (z v))|
      ≤ δ * Real.sqrt (∑ x, lp x * Λ (fun u => g (fp u) (x u))) *
          Real.sqrt (∑ x, lm x * Λ (fun u => g (fm u) (x u))) := hbr g
    _ ≤ δ * Real.sqrt (∏ u, c (fp u)) * Real.sqrt (∏ u, c (fm u)) := by
        gcongr
    _ = δ * ∏ v, c v := by rw [mul_assoc, hsq]

/-- **`lem:density:coupled` on the slots `V`** (WP-FI's `coupled_spectator_estimate`, `d = |V|`). -/
theorem coupled_spectator_estimateV {Λ : (V → W → ℝ) → ℝ} {K lp lm : (V → X) → ℝ}
    {κ : (V → Y) → ℝ} {fp fm : V → V} {δ θ : ℝ} (hδ : 0 ≤ δ) (hθ : θ ≠ 0)
    (hcopy : coupledCopyingV fp fm) (hbr : coupledSharpBracketV Λ K lp lm fp fm δ)
    (hhol : coupledOutsideHolderV Λ) (hlp : ∀ x, 0 ≤ lp x) (hlm : ∀ x, 0 ≤ lm x)
    (hκ : ∀ z, 0 ≤ κ z) (hmp : coupledUnitMixedV ((Fintype.card V : ℝ) / θ) lp)
    (hmm : coupledUnitMixedV ((Fintype.card V : ℝ) / θ) lm)
    (hmκ : coupledUnitMixedV ((Fintype.card V : ℝ) / θ) κ)
    {h : V → X → Y → W → ℝ} {a : V → X → Y → ℝ} {b : V → ℝ}
    (ha : ∀ v x y, 0 ≤ a v x y) (hb : ∀ v, 0 ≤ b v)
    (hZ : ∀ v x y, coupledEnergyV Λ (h v x y) ^ (1 / (Fintype.card V : ℝ)) ≤
      b v * a v x y ^ (θ / Fintype.card V)) :
    |∑ x, ∑ z, K x * κ z * Λ (fun v => h v (x v) (z v))| ≤
      δ * (∏ v, b v) * ∏ v, coupledMean (fun p : X × Y => a v p.1 p.2) ^
        (θ / Fintype.card V) := by
  set T : (V → Y) → ℝ := fun z => ∑ x, K x * Λ (fun v => h v (x v) (z v)) with hT
  set G : V → Y → ℝ := fun v y => coupledMean (fun x => a v x y) ^ (θ / Fintype.card V)
    with hG
  have hswap : ∑ x, ∑ z, K x * κ z * Λ (fun v => h v (x v) (z v)) = ∑ z, κ z * T z := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [hT, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hcond : ∀ z, |T z| ≤ δ * (∏ v, b v) * ∏ v, G v (z v) := by
    intro z
    have h1 := coupled_conditional_boundV hδ hθ hcopy hbr hhol hlp hlm hmp hmm ha hb hZ z
    rw [Finset.prod_mul_distrib, ← mul_assoc] at h1
    exact h1
  have hDB : 0 ≤ δ * ∏ v, b v := mul_nonneg hδ (Finset.prod_nonneg fun v _ => hb v)
  have hmom := hmκ G
  have hnorm : ∀ v : V, coupledLpNorm ((Fintype.card V : ℝ) / θ) (G v) =
      coupledMean (fun p : X × Y => a v p.1 p.2) ^ (θ / Fintype.card V) := by
    intro v
    rw [hG, coupledLpNorm_rpow (card_ne_zero_of_elem v) hθ
      (fun y => coupledMean_nonneg fun x => ha v x y), coupledMean_iterate]
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
    _ ≤ δ * (∏ v, b v) * ∏ v, coupledMean (fun p : X × Y => a v p.1 p.2) ^
          (θ / Fintype.card V) :=
        mul_le_mul_of_nonneg_left hmom hDB

end Estimate

section Mixture

variable {V : Type*} [Fintype V] [DecidableEq V] {X W : Type*} [Fintype X]

/-- **The bracket passes to mixtures over the shared labels** (Cauchy–Schwarz over `s`). -/
theorem coupledSharpBracket_mixtureV {S : Type*} [Fintype S] {Λ : (V → W → ℝ) → ℝ}
    {fp fm : V → V} {δ : ℝ} (hδ : 0 ≤ δ) (π : S → ℝ) (hπ : ∀ s, 0 ≤ π s)
    (K lp lm : S → (V → X) → ℝ)
    (hEp : ∀ s (g : V → X → W → ℝ), 0 ≤ ∑ x, lp s x * Λ (fun u => g (fp u) (x u)))
    (hEm : ∀ s (g : V → X → W → ℝ), 0 ≤ ∑ x, lm s x * Λ (fun u => g (fm u) (x u)))
    (hK : ∀ s, coupledSharpBracketV Λ (K s) (lp s) (lm s) fp fm δ) :
    coupledSharpBracketV Λ (fun x => ∑ s, π s * K s x) (fun x => ∑ s, π s * lp s x)
      (fun x => ∑ s, π s * lm s x) fp fm δ := by
  intro g
  set Ep : S → ℝ := fun s => ∑ x, lp s x * Λ (fun u => g (fp u) (x u)) with hEpdef
  set Em : S → ℝ := fun s => ∑ x, lm s x * Λ (fun u => g (fm u) (x u)) with hEmdef
  have hswap : ∀ (F : S → (V → X) → ℝ) (G : (V → X) → ℝ),
      ∑ x, (∑ s, π s * F s x) * G x = ∑ s, π s * ∑ x, F s x * G x := by
    intro F G
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [hswap, hswap lp, hswap lm]
  calc |∑ s, π s * ∑ x, K s x * Λ (fun v => g v (x v))|
      ≤ ∑ s, π s * |∑ x, K s x * Λ (fun v => g v (x v))| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [abs_mul, abs_of_nonneg (hπ s)]
    _ ≤ ∑ s, π s * (δ * Real.sqrt (Ep s) * Real.sqrt (Em s)) :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hK s g) (hπ s)
    _ = δ * ∑ s, Real.sqrt (π s * Ep s) * Real.sqrt (π s * Em s) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Real.sqrt_mul (hπ s), Real.sqrt_mul (hπ s)]
        have hss : Real.sqrt (π s) * Real.sqrt (π s) = π s := Real.mul_self_sqrt (hπ s)
        calc π s * (δ * Real.sqrt (Ep s) * Real.sqrt (Em s))
            = δ * ((Real.sqrt (π s) * Real.sqrt (π s)) * Real.sqrt (Ep s) *
                Real.sqrt (Em s)) := by rw [hss]; ring
          _ = _ := by ring
    _ ≤ δ * (Real.sqrt (∑ s, π s * Ep s) * Real.sqrt (∑ s, π s * Em s)) := by
        apply mul_le_mul_of_nonneg_left _ hδ
        exact Real.sum_sqrt_mul_sqrt_le _ (fun s => mul_nonneg (hπ s) (hEp s g))
          (fun s => mul_nonneg (hπ s) (hEm s g))
    _ = δ * Real.sqrt (∑ s, π s * Ep s) * Real.sqrt (∑ s, π s * Em s) := by ring

end Mixture

section FoldedEnergyBridge

universe u

variable {V : Type*} [Fintype V] [DecidableEq V] {X W : Type u} [Fintype X] [DecidableEq X]
  [Fintype W] [DecidableEq W]

/-- The configurations of the two atoms are pairs (slots `V`). -/
def coupledSplitV : (∀ b, V → coupledAtom X W b) ≃ (V → X) × (V → W) where
  toFun z := (z true, z false)
  invFun p := fun b => match b with
    | true => p.1
    | false => p.2
  left_inv z := by funext b; cases b <;> rfl
  right_inv _ := rfl

/-- Fubini for the two atoms (slots `V`). -/
theorem coupled_two_atomV (L : ∀ b, ((V → coupledAtom X W b) → ℝ) →ₗ[ℝ] ℝ)
    (G : V → X → W → ℝ) :
    multilinearIntegral (tensorLaw L) (fun v p => G v (p true) (p false)) =
      ∑ x : V → X, lawDensity (L true) x * L false (fun w => ∏ v, G v (x v) (w v)) := by
  rw [multilinearIntegral, RecordExpansion.tensorLaw_apply]
  rw [Fintype.sum_equiv (coupledSplitV (V := V) (X := X) (W := W)) _
    (fun p => lawDensity (L true) p.1 * lawDensity (L false) p.2 *
      ∏ v, G v (p.1 v) (p.2 v)) (fun z => by rw [Fintype.prod_bool]; rfl)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [linearFunctional_density (L false), Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [lawDensity]
  ring

/-- The two laws `(L₁, L₂)` as a family over the two atoms (slots `V`). -/
def coupledPairV (L₁ : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (L₂ : ((V → W) → ℝ) →ₗ[ℝ] ℝ) :
    ∀ b, ((V → coupledAtom X W b) → ℝ) →ₗ[ℝ] ℝ
  | true => L₁
  | false => L₂

/-- Half marginals on the selected atom; the outside atom carries none (slots `V`). -/
def coupledHalfV (c : ReflectionCut V) (m : (c.Half → X) → ℝ) :
    ∀ b, (c.Half → coupledAtom X W b) → ℝ
  | true => m
  | false => fun _ => 0

/-- **The folded energies of one sharp law** (slots `V`): nonnegative, and they bound the
coupled integral (`Comparison.folded_energy` with two atoms). -/
theorem coupled_folded_energy_of_sharpV (c : ReflectionCut V)
    (K : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (O : ((V → W) → ℝ) →ₗ[ℝ] ℝ)
    {mp mm : (c.Half → X) → ℝ} (hmp : ∀ x, 0 ≤ mp x) (hmm : ∀ x, 0 ≤ mm x) {δ : ℝ}
    (hδ : 0 ≤ δ) (hsharp : Comparison.Sharp c K mp mm δ) (hO : c.Positive O)
    (g : V → X → W → ℝ) :
    0 ≤ ∑ x, lawDensity (c.diagonalLaw mp) x *
        multilinearIntegral O (fun u => g (c.foldPlus u) (x u)) ∧
      0 ≤ ∑ x, lawDensity (c.diagonalLaw mm) x *
        multilinearIntegral O (fun u => g (c.foldMinus u) (x u)) ∧
      |∑ x, lawDensity K x * multilinearIntegral O (fun v => g v (x v))| ≤
        δ * Real.sqrt (∑ x, lawDensity (c.diagonalLaw mp) x *
          multilinearIntegral O (fun u => g (c.foldPlus u) (x u))) *
        Real.sqrt (∑ x, lawDensity (c.diagonalLaw mm) x *
          multilinearIntegral O (fun u => g (c.foldMinus u) (x u))) := by
  have hE : ∀ j ∈ ({true} : Finset Bool), j = true := fun j hj => Finset.mem_singleton.mp hj
  have h3 := Comparison.folded_energy c {true} (coupledPairV (W := W) K O)
    (coupledHalfV (W := W) c mp) (coupledHalfV (W := W) c mm) (fun _ => δ) (fun _ _ => hδ)
    (fun j hj x => by obtain rfl := hE j hj; exact hmp x)
    (fun j hj x => by obtain rfl := hE j hj; exact hmm x)
    (fun j hj => by obtain rfl := hE j hj; exact hsharp)
    (fun j hj => by
      cases j
      · exact hO
      · exact absurd (Finset.mem_singleton_self _) hj)
    (fun v p => g v (p true) (p false))
  rw [Finset.prod_singleton] at h3
  have eT : multilinearIntegral (tensorLaw (coupledPairV (W := W) K O))
      (fun v p => g v (p true) (p false)) =
      ∑ x, lawDensity K x * multilinearIntegral O (fun v => g v (x v)) :=
    coupled_two_atomV _ g
  have eP : multilinearIntegral (tensorLaw fun j => if j ∈ ({true} : Finset Bool) then
      c.diagonalLaw (coupledHalfV (W := W) c mp j) else coupledPairV (W := W) K O j)
      (fun u p => g (c.foldPlus u) (p true) (p false)) =
      ∑ x, lawDensity (c.diagonalLaw mp) x *
        multilinearIntegral O (fun u => g (c.foldPlus u) (x u)) := by
    refine (coupled_two_atomV _ (fun u => g (c.foldPlus u))).trans ?_
    rw [ite_eq_left (Finset.mem_singleton_self true), ite_eq_right (by simp)]
    rfl
  have eM : multilinearIntegral (tensorLaw fun j => if j ∈ ({true} : Finset Bool) then
      c.diagonalLaw (coupledHalfV (W := W) c mm j) else coupledPairV (W := W) K O j)
      (fun u p => g (c.foldMinus u) (p true) (p false)) =
      ∑ x, lawDensity (c.diagonalLaw mm) x *
        multilinearIntegral O (fun u => g (c.foldMinus u) (x u)) := by
    refine (coupled_two_atomV _ (fun u => g (c.foldMinus u))).trans ?_
    rw [ite_eq_left (Finset.mem_singleton_self true), ite_eq_right (by simp)]
    rfl
  obtain ⟨hp, hm, hb⟩ := h3
  refine ⟨?_, ?_, ?_⟩
  · have := hp
    simp only [Function.comp_def] at this
    rw [← eP]
    exact this
  · have := hm
    simp only [Function.comp_def] at this
    rw [← eM]
    exact this
  · rw [← eT, ← eP, ← eM]
    simpa only [Function.comp_def] using hb

omit [Fintype W] [DecidableEq W] in
/-- The weights of a diagonal law with nonnegative half marginal are nonnegative. -/
theorem coupled_diagonalLaw_nonnegV (c : ReflectionCut V) {m : (c.Half → X) → ℝ}
    (hm : ∀ x, 0 ≤ m x) (y : V → X) : 0 ≤ lawDensity (c.diagonalLaw m) y := by
  show 0 ≤ ∑ x, m x * (if c.join x x = y then (1 : ℝ) else 0)
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hm x) (by split_ifs <;> norm_num)

/-- **`lem:density:coupled` for a mixture over shared labels**, on the slots `V`: the selected
law is `∑_s π_s K_s` with every `K_s` `Sharp` at the cut `c` with constant `δ` relative to
nonnegative half marginals `m±_s`; the folded laws are `λ± = ∑_s π_s Diag(m±_s)`. -/
theorem coupled_spectator_estimate_mixtureV {Y : Type*} [Fintype Y] {S : Type*} [Fintype S]
    (c : ReflectionCut V) (π : S → ℝ) (hπ : ∀ s, 0 ≤ π s)
    (K : S → ((V → X) → ℝ) →ₗ[ℝ] ℝ) (O : ((V → W) → ℝ) →ₗ[ℝ] ℝ)
    {κ : (V → Y) → ℝ} {mp mm : S → (c.Half → X) → ℝ} (hmp : ∀ s x, 0 ≤ mp s x)
    (hmm : ∀ s x, 0 ≤ mm s x) {δ θ : ℝ} (hδ : 0 ≤ δ) (hθ : θ ≠ 0)
    (hsharp : ∀ s, Comparison.Sharp c (K s) (mp s) (mm s) δ) (hO : c.Positive O)
    (hhol : coupledOutsideHolderV (multilinearIntegral O)) (hκ : ∀ z, 0 ≤ κ z)
    (hmp' : coupledUnitMixedV ((Fintype.card V : ℝ) / θ)
      (fun x => ∑ s, π s * lawDensity (c.diagonalLaw (mp s)) x))
    (hmm' : coupledUnitMixedV ((Fintype.card V : ℝ) / θ)
      (fun x => ∑ s, π s * lawDensity (c.diagonalLaw (mm s)) x))
    (hmκ : coupledUnitMixedV ((Fintype.card V : ℝ) / θ) κ)
    {h : V → X → Y → W → ℝ} {a : V → X → Y → ℝ} {b : V → ℝ}
    (ha : ∀ v x y, 0 ≤ a v x y) (hb : ∀ v, 0 ≤ b v)
    (hZ : ∀ v x y, coupledEnergyV (multilinearIntegral O) (h v x y) ^
      (1 / (Fintype.card V : ℝ)) ≤ b v * a v x y ^ (θ / Fintype.card V)) :
    |∑ x, ∑ z, (∑ s, π s * lawDensity (K s) x) * κ z *
        multilinearIntegral O (fun v => h v (x v) (z v))| ≤
      δ * (∏ v, b v) * ∏ v, coupledMean (fun p : X × Y => a v p.1 p.2) ^
        (θ / Fintype.card V) := by
  have hbr := coupledSharpBracket_mixtureV hδ π hπ (fun s => lawDensity (K s))
    (fun s => lawDensity (c.diagonalLaw (mp s))) (fun s => lawDensity (c.diagonalLaw (mm s)))
    (fun s g => (coupled_folded_energy_of_sharpV c (K s) O (hmp s) (hmm s) hδ (hsharp s) hO g).1)
    (fun s g =>
      (coupled_folded_energy_of_sharpV c (K s) O (hmp s) (hmm s) hδ (hsharp s) hO g).2.1)
    (fun s g =>
      (coupled_folded_energy_of_sharpV c (K s) O (hmp s) (hmm s) hδ (hsharp s) hO g).2.2)
  exact coupled_spectator_estimateV hδ hθ (coupledCopying_cutV c) hbr hhol
    (fun x => Finset.sum_nonneg fun s _ =>
      mul_nonneg (hπ s) (coupled_diagonalLaw_nonnegV c (hmp s) x))
    (fun x => Finset.sum_nonneg fun s _ =>
      mul_nonneg (hπ s) (coupled_diagonalLaw_nonnegV c (hmm s) x))
    hκ hmp' hmm' hmκ ha hb hZ

end FoldedEnergyBridge

section SharpBound

open Sarkozy.TheoremC Sarkozy.Comparison

variable {X : Type} [Fintype X] [DecidableEq X] {W : Type} [Fintype W] [DecidableEq W]

/-- **The normalized plus full folded law** of a sharp decomposition (`lem:density:coupled`,
"including integration of shared labels"): `λ̂₊ = ∑_s π_s Diag(m₊(κ_s))`. -/
noncomputable def foldedLawPlus (c : ReflectionCut Slot) {S : Type} [Fintype S]
    (π : FiniteLaw S) (κs : S → SlotMeasure X) : (Slot → X) → ℝ :=
  fun x => ∑ s, π.weight s * lawDensity (c.diagonalLaw (halfMarginalPlus c (κs s))) x

/-- The normalized minus full folded law `λ̂₋ = ∑_s π_s Diag(m₋(κ_s))`. -/
noncomputable def foldedLawMinus (c : ReflectionCut Slot) {S : Type} [Fintype S]
    (π : FiniteLaw S) (κs : S → SlotMeasure X) : (Slot → X) → ℝ :=
  fun x => ∑ s, π.weight s * lawDensity (c.diagonalLaw (halfMarginalMinus c (κs s))) x

/-- The half marginals of a nonnegative measure are nonnegative. -/
theorem halfMarginalPlus_nonneg' {κ : SlotMeasure X} (hκ : IsNonneg κ) (c : ReflectionCut Slot)
    (x : c.Half → X) : 0 ≤ halfMarginalPlus c κ x :=
  hκ _ (fun _ => by split_ifs <;> norm_num)

theorem halfMarginalMinus_nonneg' {κ : SlotMeasure X} (hκ : IsNonneg κ)
    (c : ReflectionCut Slot) (x : c.Half → X) : 0 ≤ halfMarginalMinus c κ x :=
  hκ _ (fun _ => by split_ifs <;> norm_num)

/-- The weights of a decomposed sharp difference. -/
theorem lawDensity_sharpDecomp {κ ζ : SlotMeasure X} {S : Type} [Fintype S] (π : FiniteLaw S)
    (Ks : S → SlotMeasure X) (hζ : ζ = mass κ • ∑ s, π.weight s • Ks s) (x : Slot → X) :
    lawDensity ζ x = mass κ * ∑ s, π.weight s * lawDensity (Ks s) x := by
  rw [hζ, RecordExpansion.lawDensity_smul, RecordExpansion.lawDensity_sum]
  simp only [RecordExpansion.lawDensity_smul]

theorem card_slot_real : (Fintype.card Slot : ℝ) = 72 := by
  rw [card_slot]
  norm_num

/-- **`lem:density:coupled` for a sharp decomposition** (`def:price`(b), the witness of
`TheoremC.HasSharpBound`). Data: `ζ = w ∑_s π_s K_s` with `w = mass κ ≥ 0`, probability
components `κ_s`, and `K_s` sharp at the cut `c` with constant `d ≥ 0` relative to the half
marginals of `κ_s`. Hypotheses (named analytic inputs, as in the paper's statement): `O`
reflection positive at `c` with the outside signed Hölder inequality, a nonnegative spectator
`κ'`, unit mixed `L^{72/θ}` of the normalized full folded laws `λ̂±` and of `κ'`, and
`Z_O(h_v(x,z,·))^{1/72} ≤ b_v a_v(x,z)^{θ/72}`. Conclusion:
`|∫ Λ_O((h_v)_v) d(ζ ⊗ κ')| ≤ w d ∏_v b_v ∏_v (E_{x,z} a_v(x,z))^{θ/72}`. -/
theorem coupled_spectator_estimate_sharpDecomp {Y : Type*} [Fintype Y] (c : ReflectionCut Slot)
    (O : SlotMeasure W) {κ ζ : SlotMeasure X} {d θ : ℝ} {S : Type} [Fintype S]
    (π : FiniteLaw S) (κs Ks : S → SlotMeasure X) (hprob : ∀ s, IsProbability (κs s))
    (hζ : ζ = mass κ • ∑ s, π.weight s • Ks s)
    (hsharp : ∀ s, Sharp c (Ks s) (halfMarginalPlus c (κs s)) (halfMarginalMinus c (κs s)) d)
    (hmass : 0 ≤ mass κ) (hd : 0 ≤ d) (hθ : θ ≠ 0) (hO : c.Positive O)
    (hhol : coupledOutsideHolderV (multilinearIntegral O)) {κ' : (Slot → Y) → ℝ}
    (hκ' : ∀ z, 0 ≤ κ' z) (hmp : coupledUnitMixedV (72 / θ) (foldedLawPlus c π κs))
    (hmm : coupledUnitMixedV (72 / θ) (foldedLawMinus c π κs))
    (hmκ : coupledUnitMixedV (72 / θ) κ')
    {h : Slot → X → Y → W → ℝ} {a : Slot → X → Y → ℝ} {b : Slot → ℝ}
    (ha : ∀ v x y, 0 ≤ a v x y) (hb : ∀ v, 0 ≤ b v)
    (hZ : ∀ v x y, coupledEnergyV (multilinearIntegral O) (h v x y) ^ (1 / (72 : ℝ)) ≤
      b v * a v x y ^ (θ / 72)) :
    |∑ x, ∑ z, lawDensity ζ x * κ' z * multilinearIntegral O (fun v => h v (x v) (z v))| ≤
      mass κ * d * (∏ v, b v) * ∏ v, coupledMean (fun p : X × Y => a v p.1 p.2) ^ (θ / 72) := by
  have hcard := card_slot_real
  have hmix := coupled_spectator_estimate_mixtureV (Y := Y) c (fun s => π.weight s) π.nonneg Ks
    O (mp := fun s => halfMarginalPlus c (κs s)) (mm := fun s => halfMarginalMinus c (κs s))
    (fun s x => halfMarginalPlus_nonneg' (hprob s).1 c x)
    (fun s x => halfMarginalMinus_nonneg' (hprob s).1 c x) hd hθ hsharp hO hhol hκ'
    (by rw [hcard]; exact hmp) (by rw [hcard]; exact hmm) (by rw [hcard]; exact hmκ) ha hb
    (by rw [hcard]; exact hZ)
  rw [hcard] at hmix
  have hrw : ∑ x, ∑ z, lawDensity ζ x * κ' z * multilinearIntegral O (fun v => h v (x v) (z v)) =
      mass κ * ∑ x, ∑ z, (∑ s, π.weight s * lawDensity (Ks s) x) * κ' z *
        multilinearIntegral O (fun v => h v (x v) (z v)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [lawDensity_sharpDecomp π Ks hζ x]
    ring
  rw [hrw, abs_mul, abs_of_nonneg hmass]
  calc mass κ * |∑ x, ∑ z, (∑ s, π.weight s * lawDensity (Ks s) x) * κ' z *
        multilinearIntegral O (fun v => h v (x v) (z v))|
      ≤ mass κ * (d * (∏ v, b v) * ∏ v, coupledMean (fun p : X × Y => a v p.1 p.2) ^
          (θ / 72)) := mul_le_mul_of_nonneg_left hmix hmass
    _ = mass κ * d * (∏ v, b v) * ∏ v, coupledMean (fun p : X × Y => a v p.1 p.2) ^
          (θ / 72) := by ring

/-- **`lem:density:coupled` from `TheoremC.HasSharpBound`.** The moment hypothesis on the
normalized folded laws is required for every decomposition witness of the sharp bound. -/
theorem coupled_spectator_estimate_hasSharpBound {Y : Type*} [Fintype Y]
    (c : ReflectionCut Slot) (O : SlotMeasure W) {κ ζ : SlotMeasure X} {d θ : ℝ}
    (hsb : HasSharpBound c κ ζ d) (hmass : 0 ≤ mass κ) (hd : 0 ≤ d) (hθ : θ ≠ 0)
    (hO : c.Positive O) (hhol : coupledOutsideHolderV (multilinearIntegral O))
    (hfold : ∀ (S : Type) [Fintype S] (π : FiniteLaw S) (κs Ks : S → SlotMeasure X),
      (∀ s, IsProbability (κs s)) → κ = mass κ • ∑ s, π.weight s • κs s →
      ζ = mass κ • ∑ s, π.weight s • Ks s →
      (∀ s, Sharp c (Ks s) (halfMarginalPlus c (κs s)) (halfMarginalMinus c (κs s)) d) →
      coupledUnitMixedV (72 / θ) (foldedLawPlus c π κs) ∧
        coupledUnitMixedV (72 / θ) (foldedLawMinus c π κs))
    {κ' : (Slot → Y) → ℝ} (hκ' : ∀ z, 0 ≤ κ' z) (hmκ : coupledUnitMixedV (72 / θ) κ')
    {h : Slot → X → Y → W → ℝ} {a : Slot → X → Y → ℝ} {b : Slot → ℝ}
    (ha : ∀ v x y, 0 ≤ a v x y) (hb : ∀ v, 0 ≤ b v)
    (hZ : ∀ v x y, coupledEnergyV (multilinearIntegral O) (h v x y) ^ (1 / (72 : ℝ)) ≤
      b v * a v x y ^ (θ / 72)) :
    |∑ x, ∑ z, lawDensity ζ x * κ' z * multilinearIntegral O (fun v => h v (x v) (z v))| ≤
      mass κ * d * (∏ v, b v) * ∏ v, coupledMean (fun p : X × Y => a v p.1 p.2) ^ (θ / 72) := by
  obtain ⟨S, hS, π, κs, Ks, hprob, hκ, hζ, hsharp⟩ := hsb
  obtain ⟨hmp, hmm⟩ := hfold S π κs Ks hprob hκ hζ hsharp
  exact coupled_spectator_estimate_sharpDecomp c O π κs Ks hprob hζ hsharp hmass hd hθ hO hhol
    hκ' hmp hmm hmκ ha hb hZ

end SharpBound

end Sarkozy.DensityMoments
