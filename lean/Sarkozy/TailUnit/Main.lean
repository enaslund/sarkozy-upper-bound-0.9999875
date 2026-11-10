module

public import Sarkozy.TailUnit.Emission
public import Sarkozy.PartV.NonVacuity
public import Sarkozy.TailMoment.SingleLabel
public import Sarkozy.Moments.TypedMixture
public import Sarkozy.DensityMoments.ExactTypedMixture

/-!
# Unit mixed `L³⁶` of the paper's tail laws (`hunit`)

`paper/sections/31_density_induction_upgrade.tex`, proof of `lem:density:global-moment`, second
paragraph ("Hence the full tail reference has unit mixed `L^{36}` eventually"), with
`lem:density:typed-mixture` (`paper/sections/30_density_moment_upgrade.tex`).

**`tailLawFamily_unit`**: under `Target.Weil`, V1's tail laws `PartV.tailLawFamily q` have unit
mixed `L³⁶` at every prime `q` above a threshold. This is the field `hunit` of
`MainAnchor.PartVObligations` for `μp = PartV.tailLawFamily`.

The proof is the paper's.
* **Components.** The tail law is V1's upper reference at one prime, a mixture of the 392
  components `upComponent j` (`weightedCompletion` = `FiniteLaw.mixture`), each the image of one
  of the eighteen field graph laws `λ_p(G_{φ₀φ₁,j})` under an emission. WP-P's
  `TailMoment.labellings_unit_mixed_of_weil` gives each field graph law unit mixed `L^{9/8}` for
  large `p`, from `Target.Weil`. `upComponent_mixedLpBound` (`Emission.lean`) then gives each
  component unit mixed `L^{(9/8)m}`, `m = compFib j` its multiplicity bound.
* **Three classes** (`compExp`). Components with `m ≤ 32` have exponent `(9/8)m ≤ 36`; the root
  `π_{LL,2}` has exponent `9/8 ≤ 18`. The components with `m > 32` (multiplicities `36, 48, 72`)
  are charged at exponent `72`, from uniform marginals alone (`mixedLpBound_of_uniform_marginals`).
* **Balance** (`tail_balance`). A bad component has degree `≥ 6` (`degOf_ge_of_fibOf`), so its
  weight is at most `upCoeff(1) · p^{-3}`; its charge is `C_72(p) ≤ 4p` (`exactCoeff_le`); the
  root has weight `1/P_μ(r)`. So the charges are at most `4K/p²` times the root's weight,
  `K = ∑_j upCoeff_j(1)`.
* **Mixture.** `mixedLpBound_typed_mixture` (`Moments/TypedMixture.lean`) with the one-coordinate
  deficit `DensityMoments.exact_deficit` concludes.

The exponent `9/8` replaces the paper's `11/10`; any `r ∈ (1, 9/8]` works.
-/

@[expose] public section

namespace Sarkozy.TailUnit

open Finset Sarkozy.PartV Sarkozy.Labellings

/-! ## The exponents and coefficients of the components -/

/-- The exponent of a component: `(9/8) m` for multiplicity bound `m = compFib j ≤ 32`, and `72`
(uniform marginals alone) for `m > 32`. -/
noncomputable def compExp (j : UpIdx) : ℝ := if 32 < compFib j then 72 else 9 / 8 * compFib j

theorem compExp_pos (j : UpIdx) : 0 < compExp j := by
  unfold compExp
  split_ifs
  · norm_num
  · have h : (1 : ℝ) ≤ compFib j := by exact_mod_cast one_le_compFib j
    linarith

theorem bad_of_compExp {j : UpIdx} (h : 36 < compExp j) : 32 < compFib j := by
  by_contra hj
  unfold compExp at h
  simp only [hj, ↓reduceIte] at h
  have : (compFib j : ℝ) ≤ 32 := by exact_mod_cast not_lt.mp hj
  linarith

/-- The root component `π_{LL,2}`: the two-layer copy of the state `(L, L)`. -/
def rootIdx : UpIdx := (true, ⟨(.L, .L), ((), ())⟩)

theorem compExp_root : compExp rootIdx = 9 / 8 := by
  have h : compFib rootIdx = 1 := rfl
  unfold compExp
  rw [h]
  norm_num

/-- The coefficient of a component at `r` is its coefficient at `1` times `r^{deg}`. -/
theorem upCoeff_eq (W : UpperWeights) (r : ℝ) (j : UpIdx) :
    upCoeff W r j = upCoeff W 1 j * r ^ compDeg j := by
  rcases j with ⟨b, ⟨t₀, t₁⟩, φ⟩
  cases b <;> simp [upCoeff, compDeg, degOf]

/-- The root has coefficient `w_LL = 1`. -/
theorem upCoeff_root (W : UpperWeights) (r : ℝ) : upCoeff W r rootIdx = 1 := by
  simp [upCoeff, rootIdx, W.w_LL, PType.deg]

/-- The charge of the bad components: the coefficient `C_72(Q)` of `lem:density:typed-mixture`
(`DensityMoments.exactCoeff` at `θ = 72/36`, `κ = 18/36`). -/
noncomputable def badCoeff (Q : ℝ) (j : UpIdx) : ℝ :=
  if 32 < compFib j then DensityMoments.exactCoeff (((72 : ℕ) : ℝ) / 36) (18 / 36) Q else 0

/-- **`C_72(Q) ≤ 4Q`** for `Q ≥ 16`: `φ(Q) = (Q-1)² ≤ Q²` and `ψ(Q) = Q/2 + 1/2 - √Q ≥ Q/4`. -/
theorem exactCoeff_le {Q : ℝ} (hQ : 16 ≤ Q) :
    DensityMoments.exactCoeff (((72 : ℕ) : ℝ) / 36) (18 / 36) Q ≤ 4 * Q := by
  have h1 : (((72 : ℕ) : ℝ) / 36) = 2 := by norm_num
  have h2 : ((18 : ℝ) / 36) = 1 / 2 := by norm_num
  rw [h1, h2]
  unfold DensityMoments.exactCoeff DensityUpgrade.blockGatePhi DensityUpgrade.blockGatePsi
  have hQ0 : 0 ≤ Q := by linarith
  rw [Real.rpow_two, ← Real.sqrt_eq_rpow]
  have hs : Real.sqrt Q ≤ Q / 4 := by
    rw [show Q / 4 = Real.sqrt ((Q / 4) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hψ : Q / 4 ≤ 1 / 2 * Q + 1 - 1 / 2 - Real.sqrt Q := by linarith
  have hψpos : 0 < 1 / 2 * Q + 1 - 1 / 2 - Real.sqrt Q := by linarith
  apply max_le
  · rw [div_le_iff₀ hψpos]
    nlinarith [mul_le_mul_of_nonneg_left hψ (by linarith : (0 : ℝ) ≤ 4 * Q)]
  · norm_num
    linarith

/-- **The balance of `lem:density:typed-mixture`** for an upper reference: if
`K r⁶ C ≤ 1`, `K = ∑_j upCoeff_j(1)`, the charges of the components of exponent `> 36` are at
most the weight of the components of exponent `≤ 18`. -/
theorem tail_balance (W : UpperWeights) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {Cq : ℝ}
    (hCq : 0 ≤ Cq) (hK : (∑ j, upCoeff W 1 j) * r ^ 6 * Cq ≤ 1) :
    (∑ j ∈ univ.filter (fun j => 36 < compExp j),
        (normWeights (upCoeff W r) (upCoeff_nonneg W hr0) (upPoly_pos W hr0)).weight j *
          (if 32 < compFib j then Cq else 0)) ≤
      ∑ j ∈ univ.filter (fun j => compExp j ≤ 18),
        (normWeights (upCoeff W r) (upCoeff_nonneg W hr0) (upPoly_pos W hr0)).weight j := by
  have hSpos : 0 < ∑ i, upCoeff W r i := upPoly_pos W hr0
  simp only [normWeights]
  have hterm : ∀ j ∈ univ.filter (fun j => 36 < compExp j),
      upCoeff W r j / (∑ i, upCoeff W r i) * (if 32 < compFib j then Cq else 0) ≤
        upCoeff W 1 j * r ^ 6 * Cq / (∑ i, upCoeff W r i) := by
    intro j hj
    have hbad : 32 < compFib j := bad_of_compExp (mem_filter.mp hj).2
    have hdeg : 6 ≤ compDeg j := degOf_ge_of_fibOf _ _ _ hbad
    simp only [hbad, ↓reduceIte]
    rw [upCoeff_eq W r j, div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hSpos.le
    have hc1 : 0 ≤ upCoeff W 1 j := upCoeff_nonneg W zero_le_one j
    have hpow : r ^ compDeg j ≤ r ^ 6 := pow_le_pow_of_le_one hr0 hr1 hdeg
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hc1) hCq
  have hroot : rootIdx ∈ univ.filter (fun j => compExp j ≤ 18) :=
    mem_filter.mpr ⟨mem_univ _, by rw [compExp_root]; norm_num⟩
  calc (∑ j ∈ univ.filter (fun j => 36 < compExp j),
          upCoeff W r j / (∑ i, upCoeff W r i) * (if 32 < compFib j then Cq else 0))
      ≤ ∑ j ∈ univ.filter (fun j => 36 < compExp j),
          upCoeff W 1 j * r ^ 6 * Cq / (∑ i, upCoeff W r i) := sum_le_sum hterm
    _ ≤ ∑ j, upCoeff W 1 j * r ^ 6 * Cq / (∑ i, upCoeff W r i) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun j _ _ =>
          div_nonneg (mul_nonneg (mul_nonneg (upCoeff_nonneg W zero_le_one j) (pow_nonneg hr0 6))
            hCq) hSpos.le
    _ = (∑ j, upCoeff W 1 j) * r ^ 6 * Cq / (∑ i, upCoeff W r i) := by
        rw [← sum_div, ← sum_mul, ← sum_mul]
    _ ≤ 1 / (∑ i, upCoeff W r i) := div_le_div_of_nonneg_right hK hSpos.le
    _ = upCoeff W r rootIdx / (∑ i, upCoeff W r i) := by rw [upCoeff_root]
    _ ≤ ∑ j ∈ univ.filter (fun j => compExp j ≤ 18), upCoeff W r j / (∑ i, upCoeff W r i) :=
        single_le_sum (fun j _ => div_nonneg (upCoeff_nonneg W hr0 j) hSpos.le) hroot

/-- **The one-coordinate deficit** for the bad components (`DensityMoments.exact_deficit` with
`d = 72`, `s = 18`, `R = 36`). -/
theorem bad_scalar {X : Type*} [Fintype X] [Nonempty X] (hQ : 1 < (Fintype.card X : ℝ))
    (f : X → ℝ) (hn : (FiniteLaw.uniform X).lpNorm 36 f = 1) (j : UpIdx)
    (hj : 36 < compExp j) :
    (FiniteLaw.uniform X).lpNorm (compExp j) f ^ Fintype.card Slot - 1 ≤
      badCoeff (Fintype.card X) j *
        (1 - (FiniteLaw.uniform X).lpNorm 18 f ^ Fintype.card Slot) := by
  have hbad := bad_of_compExp hj
  have hexp : compExp j = ((72 : ℕ) : ℝ) := by
    unfold compExp
    simp only [hbad, ↓reduceIte]
    norm_num
  rw [hexp, card_slot]
  unfold badCoeff
  simp only [hbad, ↓reduceIte]
  exact DensityMoments.exact_deficit (d := 72) (by norm_num) (by norm_num) (by norm_num) hQ hn

/-- The components inherit uniform one-slot marginals from the field laws. -/
theorem upComponent_uniform {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (F : UpperFieldLaws X)
    (h2 : ∀ f₀ f₁ (i : f₀.Obj × f₁.Obj × Fin 2) (g : X → ℝ),
      (F.two f₀ f₁).expect (fun y => g (y i)) = (FiniteLaw.uniform X).expect g)
    (h1 : ∀ f₀ f₁ (i : f₀.Obj × f₁.Obj × Fin 1) (g : X → ℝ),
      (F.one f₀ f₁).expect (fun y => g (y i)) = (FiniteLaw.uniform X).expect g)
    (j : UpIdx) : HasUniformMarginals (upComponent F j) := by
  rcases j with ⟨b, ⟨t₀, t₁⟩, φ⟩
  cases b
  · exact emit_uniform _ _ (h1 _ _)
  · exact emit_uniform _ _ (h2 _ _)

/-- The object sets of the field types are nonempty. -/
instance instNonemptyObj (f : FType) : Nonempty f.Obj := by
  cases f
  · exact ⟨(0 : ZMod 6)⟩
  · exact ⟨(0 : Fin 3)⟩
  · exact ⟨(0 : Fin 3)⟩

/-- `r⁶ = p^{-3}` for `r = p^{-1/2}`. -/
theorem tailR_pow_six {q : ℕ} (hq : 0 < q) : tailR q ^ 6 = 1 / (q : ℝ) ^ 3 := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have h2 : tailR q ^ 2 = (q : ℝ)⁻¹ := by
    unfold tailR
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0]
    norm_num
    exact Real.rpow_neg_one _
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  calc tailR q ^ 6 = (tailR q ^ 2) ^ 3 := by ring
    _ = 1 / (q : ℝ) ^ 3 := by rw [h2, inv_pow, one_div]

/-! ## `hunit` for the paper's tail laws -/

/-- **`hunit` for the paper's tail laws** (`lem:density:global-moment`, tail part): under
`Target.Weil`, V1's tail laws `PartV.tailLawFamily q` have unit mixed `L³⁶` at every prime `q`
above a threshold. This is the field `hunit` of `MainAnchor.PartVObligations` for
`μp = PartV.tailLawFamily`. -/
theorem tailLawFamily_unit (hW : Target.Weil) :
    ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q →
      MixedLpBound (tailLawFamily q) 36 1 := by
  choose P2 hP2 using fun f₀ f₁ : FType =>
    TailMoment.labellings_unit_mixed_of_weil (fieldGraph f₀ f₁ (Fin 2)) hW (r := 9 / 8)
      (by norm_num)
  choose P1 hP1 using fun f₀ f₁ : FType =>
    TailMoment.labellings_unit_mixed_of_weil (fieldGraph f₀ f₁ (Fin 1)) hW (r := 9 / 8)
      (by norm_num)
  set K : ℝ := ∑ j, upCoeff tailWeights 1 j with hKdef
  refine ⟨∑ t : FType × FType, (P2 t.1 t.2 + P1 t.1 t.2) + ⌈4 * K⌉₊ + 16,
    fun q _ hq hle => ?_⟩
  have : Fact q.Prime := ⟨hq⟩
  have hPle : ∀ f₀ f₁ : FType, P2 f₀ f₁ ≤ q ∧ P1 f₀ f₁ ≤ q := by
    intro f₀ f₁
    have hle' : P2 f₀ f₁ + P1 f₀ f₁ ≤ ∑ t : FType × FType, (P2 t.1 t.2 + P1 t.1 t.2) :=
      single_le_sum (f := fun t : FType × FType => P2 t.1 t.2 + P1 t.1 t.2)
        (fun _ _ => Nat.zero_le _) (mem_univ (f₀, f₁))
    constructor <;> omega
  have hT : TailNonempty q :=
    ⟨fun f₀ f₁ => (hP2 f₀ f₁ q (hPle f₀ f₁).1).1, fun f₀ f₁ => (hP1 f₀ f₁ q (hPle f₀ f₁).2).1⟩
  have h2 : ∀ f₀ f₁, MixedLpBound ((tailFieldLaws q hT).two f₀ f₁) (9 / 8) 1 :=
    fun f₀ f₁ => (hP2 f₀ f₁ q (hPle f₀ f₁).1).2
  have h1 : ∀ f₀ f₁, MixedLpBound ((tailFieldLaws q hT).one f₀ f₁) (9 / 8) 1 :=
    fun f₀ f₁ => (hP1 f₀ f₁ q (hPle f₀ f₁).2).2
  have hcomp : ∀ j, MixedLpBound (upComponent (tailFieldLaws q hT) j) (compExp j) 1 := by
    intro j
    by_cases hb : 32 < compFib j
    · have hu : HasUniformMarginals (upComponent (tailFieldLaws q hT) j) :=
        upComponent_uniform (tailFieldLaws q hT)
          (fun f₀ f₁ => graphLaw_vertex_uniform (fieldGraph f₀ f₁ (Fin 2)) (hT.two f₀ f₁))
          (fun f₀ f₁ => graphLaw_vertex_uniform (fieldGraph f₀ f₁ (Fin 1)) (hT.one f₀ f₁)) j
      have h72 := mixedLpBound_of_uniform_marginals _ hu
      rw [card_slot] at h72
      unfold compExp
      simp only [hb, ↓reduceIte]
      exact_mod_cast h72
    · unfold compExp
      simp only [hb, ↓reduceIte]
      exact upComponent_mixedLpBound (tailFieldLaws q hT) (by norm_num) h2 h1 j
  -- the numbers
  have hq16 : (16 : ℝ) ≤ q := by exact_mod_cast (by omega : 16 ≤ q)
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hcard : (Fintype.card (ZMod q) : ℝ) = q := by rw [ZMod.card]
  have hr0 : 0 ≤ tailR q := tailR_nonneg q
  have hr1 : tailR q ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq1 (by norm_num)
  have hCq : DensityMoments.exactCoeff (((72 : ℕ) : ℝ) / 36) (18 / 36)
      (Fintype.card (ZMod q)) ≤ 4 * q := by
    rw [hcard]
    exact exactCoeff_le hq16
  have hCq0 : 0 ≤ DensityMoments.exactCoeff (((72 : ℕ) : ℝ) / 36) (18 / 36)
      (Fintype.card (ZMod q)) :=
    DensityMoments.exactCoeff_nonneg (by norm_num) (by norm_num) (by norm_num)
  have hK0 : 0 ≤ K := sum_nonneg fun j _ => upCoeff_nonneg tailWeights zero_le_one j
  have hKq : 4 * K ≤ q := by
    have hc := Nat.le_ceil (4 * K)
    have hc' : (⌈4 * K⌉₊ : ℝ) ≤ q := by exact_mod_cast (by omega : ⌈4 * K⌉₊ ≤ q)
    linarith
  have hfin : K * tailR q ^ 6 * DensityMoments.exactCoeff (((72 : ℕ) : ℝ) / 36) (18 / 36)
      (Fintype.card (ZMod q)) ≤ 1 := by
    rw [tailR_pow_six (by omega)]
    have hqpos : (0 : ℝ) < q := by linarith
    calc K * (1 / (q : ℝ) ^ 3) * DensityMoments.exactCoeff (((72 : ℕ) : ℝ) / 36) (18 / 36)
          (Fintype.card (ZMod q)) ≤ K * (1 / (q : ℝ) ^ 3) * (4 * q) :=
          mul_le_mul_of_nonneg_left hCq (by positivity)
      _ = 4 * K / (q : ℝ) ^ 2 := by
          field_simp
      _ ≤ 1 := by
          rw [div_le_one (by positivity)]
          nlinarith
  rw [tailLawFamily_eq q hT]
  unfold tailLaw upperReference weightedCompletion
  exact mixedLpBound_typed_mixture
    (normWeights (upCoeff tailWeights (tailR q)) (upCoeff_nonneg tailWeights (tailR_nonneg q))
      (upPoly_pos tailWeights (tailR_nonneg q)))
    (upComponent (tailFieldLaws q hT)) compExp (badCoeff (Fintype.card (ZMod q)))
    (s := 18) (R := 36) (by norm_num) (by norm_num) compExp_pos hcomp
    (tail_balance tailWeights hr0 hr1 hCq0 hfin)
    (fun f _ hn j hj => bad_scalar (by rw [hcard]; linarith) f hn j hj)

end Sarkozy.TailUnit
