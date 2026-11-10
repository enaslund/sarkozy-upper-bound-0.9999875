module

public import Sarkozy.OpsFeature.GlueA3
public import Sarkozy.OpsFeature.Frame

@[expose] public section

/-!
# The block edge `12` in the half-triple encoding (`hcor` of `hUa_fold_A3`)

`paper/sections/21_middle_records.tex`, `lem:oct24:feature-block`(a) (edge `12`), read in the
encoding `∀ p, Fin 3 → ℤ/p` of OPS-L's blocks (`mB = ∏ mP`). The edge is `Frame.edge12` (B11's
correlation in the encoding `Tri F = ∀ p, F p × F p × F p`, law `m0B`), transported along
`triE` and PG's `m0_eq_oldW` (`mB_eq_m0B`); the centring of the block coordinates under `mB` is the
uniform one (`sum_mB_coordFun`).

* **`hcor_block`**: at a middle block (`MiddleBlock`, least prime `b ≥ Q₃`), the centred functions
  of `x₁` and of `x₂` have correlation at most `ρ_pair` under `m_{0,𝔅}`;
* **`hUa_fold_block`**: `hUa` of `hdom_of_units` at a fold block, all four labels, for the chart's
  sector maps, with `ρ = ρ_pair`: the only remaining input is the identification of OPS-S's unit
  lifts with the conditional expectations of `m_{0,𝔅}`.
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.OpsFeature

open Sarkozy.OpsCore Sarkozy.SignedGram Sarkozy.PrimeGram Sarkozy.MiddleRecords
  Sarkozy.Envelopes Sarkozy.PartV Sarkozy.EnvelopeSteps Sarkozy.Mixing

section Cor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ} [∀ i, Fact (pr i).Prime]

/-- The two encodings of a block point. -/
def triE : (∀ i, Ai pr i) ≃ (∀ i, ZMod (pr i) × ZMod (pr i) × ZMod (pr i)) where
  toFun x i := (x i 0, x i 1, x i 2)
  invFun t i := ![(t i).1, (t i).2.1, (t i).2.2]
  left_inv x := by
    funext i k
    fin_cases k <;> rfl
  right_inv t := by
    funext i
    rfl

omit [DecidableEq ι] in
theorem mB_eq_m0B (hne : MiddleNonempty pr) (h3 : ∀ i, pr i % 4 = 3) (h19 : ∀ i, 19 ≤ pr i)
    (x : ∀ i, Ai pr i) : mB hne x = m0B (F := fun i => ZMod (pr i)) (triE x) := by
  unfold mB m0B
  refine prod_congr rfl fun i _ => ?_
  obtain ⟨hR, h3', h19'⟩ := primeHyps h3 h19 i
  unfold mP
  rw [m0_eq_oldW (hne.F2 i) hR h3' h19']
  rfl

/-- The block coordinate `x_k` is uniform under `m_{0,𝔅}`. -/
theorem sum_mB_coordFun (hne : MiddleNonempty pr) (k : Fin 3) (u : (∀ i, ZMod (pr i)) → ℝ) :
    ∑ x, mB hne x * u (piA k x) =
      ∑ w, prodW (unifB (F := fun i => ZMod (pr i))) w * u w := by
  have hdec : ∀ x : ∀ i, Ai pr i, u (piA k x) =
      ∑ w : (∀ i, ZMod (pr i)), u w * ∏ i, (if x i k = w i then (1 : ℝ) else 0) := by
    intro x
    rw [Finset.sum_eq_single (piA k x)]
    · simp [piA]
    · intro w _ hw
      have : ∃ i, x i k ≠ w i := by
        by_contra hc
        simp only [not_exists, not_not] at hc
        exact hw (funext fun i => (hc i).symm)
      obtain ⟨i, hi⟩ := this
      rw [Finset.prod_eq_zero (mem_univ i) (by simp [hi]), mul_zero]
    · simp
  simp only [hdec, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun w _ => ?_
  have e : ∀ x : ∀ i, Ai pr i, mB hne x * (u w * ∏ i, (if x i k = w i then (1 : ℝ) else 0)) =
      u w * ∏ i, (mP hne i (x i) * if x i k = w i then (1 : ℝ) else 0) := by
    intro x
    unfold mB
    rw [prod_mul_distrib]
    ring
  simp only [e, ← mul_sum]
  rw [show (∑ x : ∀ i, Ai pr i, ∏ i, (mP hne i (x i) * if x i k = w i then (1 : ℝ) else 0)) =
      ∏ i, ∑ c : Ai pr i, (mP hne i c * if c k = w i then (1 : ℝ) else 0) from
    sum_prod_coords (fun i (c : Ai pr i) => mP hne i c * if c k = w i then (1 : ℝ) else 0)]
  have hc : ∀ i, ∑ c : Ai pr i, mP hne i c * (if c k = w i then (1 : ℝ) else 0) =
      unifB (F := fun i => ZMod (pr i)) i (w i) := by
    intro i
    have := mP_coord hne i k (fun a => if a = w i then (1 : ℝ) else 0)
    simp only [sum_ite_eq', mem_univ, ↓reduceIte] at this
    rw [this, unifB]
  simp only [hc, prodW]
  ring

/-- **The block edge `12`** in the half-triple encoding: at a middle block, the centred functions
of `x₁` and of `x₂` have correlation at most `ρ_pair` under `m_{0,𝔅}` (`hcor`). -/
theorem hcor_block (hne : MiddleNonempty pr) (h3 : ∀ i, pr i % 4 = 3) (h19 : ∀ i, 19 ≤ pr i)
    {b : ℝ} (hB : MiddleBlock (fun i => ZMod (pr i)) b) (u v : (∀ i, ZMod (pr i)) → ℝ)
    (hu : EnvelopeSteps.ip (mB hne) (fun x => u (piA 1 x)) (fun _ => 1) = 0)
    (hv : EnvelopeSteps.ip (mB hne) (fun x => v (piA 2 x)) (fun _ => 1) = 0) :
    |EnvelopeSteps.ip (mB hne) (fun x => u (piA 1 x)) (fun x => v (piA 2 x))| ≤
      (rhoPair : ℝ) * Real.sqrt (EnvelopeSteps.ip (mB hne) (fun x => u (piA 1 x))
        (fun x => u (piA 1 x))) *
        Real.sqrt (EnvelopeSteps.ip (mB hne) (fun x => v (piA 2 x)) (fun x => v (piA 2 x))) := by
  have tr : ∀ h k : Tri (fun i => ZMod (pr i)) → ℝ,
      EnvelopeSteps.ip (mB hne) (fun x => h (triE x)) (fun x => k (triE x)) = ipm h k := by
    intro h k
    unfold EnvelopeSteps.ip ipm
    exact Fintype.sum_equiv triE _ _ fun x => by rw [mB_eq_m0B hne h3 h19]; ring
  have hmean : ∀ (f : (∀ i, ZMod (pr i)) → ℝ) (k : Fin 3),
      EnvelopeSteps.ip (mB hne) (fun x => f (piA k x)) (fun _ => 1) = 0 →
      ∑ w, prodW (unifB (F := fun i => ZMod (pr i))) w * f w = 0 := by
    intro f k h
    rw [← sum_mB_coordFun hne k f, ← h]
    unfold EnvelopeSteps.ip
    exact sum_congr rfl fun x _ => by ring
  have hh : IsH c1 (fun t : Tri (fun i => ZMod (pr i)) => u (c1 t)) :=
    ⟨u, hmean u 1 hu, fun _ => rfl⟩
  have hk : IsH c2 (fun t : Tri (fun i => ZMod (pr i)) => v (c2 t)) :=
    ⟨v, hmean v 2 hv, fun _ => rfl⟩
  have he := edge12 hB _ _ hh hk
  have hρ := (feature_table hB.hb).2.2.2.2
  have t1 : EnvelopeSteps.ip (mB hne) (fun x => u (piA 1 x)) (fun x => v (piA 2 x)) =
      ipm (fun t : Tri (fun i => ZMod (pr i)) => u (c1 t)) (fun t => v (c2 t)) :=
    tr (fun t => u (c1 t)) (fun t => v (c2 t))
  have t2 : EnvelopeSteps.ip (mB hne) (fun x => u (piA 1 x)) (fun x => u (piA 1 x)) =
      ipm (fun t : Tri (fun i => ZMod (pr i)) => u (c1 t)) (fun t => u (c1 t)) :=
    tr (fun t => u (c1 t)) (fun t => u (c1 t))
  have t3 : EnvelopeSteps.ip (mB hne) (fun x => v (piA 2 x)) (fun x => v (piA 2 x)) =
      ipm (fun t : Tri (fun i => ZMod (pr i)) => v (c2 t)) (fun t => v (c2 t)) :=
    tr (fun t => v (c2 t)) (fun t => v (c2 t))
  rw [t1, t2, t3]
  have hs : 0 ≤ Real.sqrt (ipm (fun t : Tri (fun i => ZMod (pr i)) => u (c1 t))
      (fun t => u (c1 t))) * Real.sqrt (ipm (fun t : Tri (fun i => ZMod (pr i)) => v (c2 t))
      (fun t => v (c2 t))) := by positivity
  calc _ ≤ _ := he
    _ ≤ (rhoPair : ℝ) * (Real.sqrt (ipm (fun t : Tri (fun i => ZMod (pr i)) => u (c1 t))
      (fun t => u (c1 t))) * Real.sqrt (ipm (fun t : Tri (fun i => ZMod (pr i)) => v (c2 t))
      (fun t => v (c2 t)))) := mul_le_mul_of_nonneg_right hρ hs
    _ = _ := by ring

/-- **`hUa` of `hdom_of_units` at a fold block of a middle block, all four labels**, for the
chart's sector maps of `chart_lead` (third arm `A₃°`), at `ρ = ρ_pair`: every arm fact and the edge
`12` are proved; the only input is the identification of OPS-S's unit lifts of the fold factor with
the conditional expectations of `m_{0,𝔅}` (`hU`: `M_aa − 𝒥`, `hU3`: `Q₁₂`). -/
theorem hUa_fold_block (hne : MiddleNonempty pr) (h3 : ∀ i, pr i % 4 = 3)
    (h19 : ∀ i, 19 ≤ pr i) {b : ℝ} (hB : MiddleBlock (fun i => ZMod (pr i)) b)
    (x₀ : ∀ i, Ai pr i)
    (U : Fin 5 → Fin 5 → ((∀ i, Ai pr i) → ℝ) →ₗ[ℝ] ((∀ i, Ai pr i) → ℝ))
    (hU : ∀ a : Fin 3, U (Fin.castSucc (Fin.castSucc a)) (Fin.castSucc (Fin.castSucc a)) =
      uOp (mB hne) (piA a))
    (hU3 : U 3 3 = qOp (mB hne) (fun x => (piA 1 x, piA 2 x)) (rhoPair : ℝ)) (a : Fin 4) :
    (Matrix.of fun x x' : (∀ i, Ai pr i) =>
      EnvelopeSteps.kern (mB hne) (U (Fin.castSucc a) (Fin.castSucc a)) x x' -
      ∑ j, ∑ z, ((Real.sqrt (Fintype.card (ZMod (pr j))))⁻¹ •
          (CXi hne x₀ j * XiM (mP hne j) A3c)) x (a, z) *
        ((Real.sqrt (Fintype.card (ZMod (pr j))))⁻¹ • (CXi hne x₀ j * XiM (mP hne j) A3c))
          x' (a, z)).PosSemidef :=
  hUa_fold_A3 hne h3 h19 x₀ (by norm_num [rhoPair]) (by norm_num [rhoPair]) U hU hU3
    (hcor_block hne h3 h19 hB) a

end Cor

end Sarkozy.OpsFeature
