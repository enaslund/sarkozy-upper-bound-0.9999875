module

public import Sarkozy.OpsSteps.SymBlock
public import Sarkozy.FirstStagePaper.SharpRecord
public import Sarkozy.EnvelopeSteps.PaperAveraging
public import Sarkozy.OpsSteps.SymBridge

@[expose] public section

/-!
# `lem:record:one-stage-folded-e`(e), the symmetric part, on the 72-slot records (OPS-S)

`paper/sections/20c_middle_frame.tex`, `lem:record:one-stage-folded-e`(e): "the record difference
is the coupling difference `Δ_c` of (d) conditional on the shared label, which gives the sharp
bound and the bound of its symmetric part". FirstStagePaper proved the sharp bound
(`blockSharp_of_block`); here the symmetric part:

* **geometry** (`tagCut_swap`, by `decide`, as `cert:record:middle-geometry`): the reflection of
  `tagCut s` exchanges the two private objects `0`, `1` of the record and fixes the shared object
  `2`, so the two halves read the private label in the same way (`hpF_eq_hmF`): "the reflection
  fixes the shared label of the folded record and transposes its conditional kernel";
* `form_symPart`: the cut form of `Sym ζ = ½(ζ + ϑ_* ζ)` is `½(form ζ F G + form ζ G F)`;
* `form_diff_eq`: the cut form of the record difference is `κ_N ∑_c ⟨g_c, Δ_c f_c⟩`
  (FirstStagePaper's computation);
* **`blockSymSharp_of_block`**: the symmetric part of `plusRec s - matchRec s` at `tagCut s` has
  sharp bound `s_crude(b)` relative to `matchRec s` (`SymBlock.block_sym_form_le` and the
  Cauchy–Schwarz step of `blockSharp_of_block`).

The constant is `s_crude(b)` instead of the paper's `s_fold(X)/b` (see `SymBlock`).
-/

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.OpsSteps

open Sarkozy.FirstStagePaper Sarkozy.TheoremC Sarkozy.PartVRecords Sarkozy.PartV
  Sarkozy.Labellings Sarkozy.Comparison Sarkozy.RecordExpansion

/-- **The reflection of `tagCut s` exchanges the private objects of the record `E_s`**: on the half,
the plus side reads object `1` exactly where the minus side reads object `0`. -/
theorem tagCut_swap (s : Fin 2) :
    ∀ v : Slot, v ∈ (tagCut s).half →
      (matching s v.1 = 1 ↔ matching s ((tagCut s).flip v).1 = 0) := by
  fin_cases s
  · exact (by decide : ∀ v : Slot, v ∈ (firstChamberCut 1).half →
      (matching 0 v.1 = 1 ↔ matching 0 ((firstChamberCut 1).flip v).1 = 0))
  · exact (by decide : ∀ v : Slot, v ∈ (firstChamberCut 2).half →
      (matching 1 v.1 = 1 ↔ matching 1 ((firstChamberCut 2).flip v).1 = 0))

/-- **The two halves read the private label in the same way.** -/
theorem hpF_eq_hmF {X : Type} (s : Fin 2) (a c : X) : hpF s a c = hmF s a c := by
  funext v
  exact if_congr (tagCut_swap s v.1 v.2) rfl rfl

/-- The cut form of the symmetric part. -/
theorem form_symPart {X : Type} [Fintype X] [DecidableEq X] (cc : ReflectionCut Slot)
    (ζ : SlotMeasure X) (F G : (cc.Half → X) → ℝ) :
    cc.form (symPart cc ζ) F G = (1 / 2 : ℝ) * (cc.form ζ F G + cc.form ζ G F) := by
  rw [← form_reflect cc ζ F G]
  rfl

/-- The reflection `R_h` whose cut is `tagCut s` (`def:record:frame`(e)): `h = 1` for the tag `0`,
`h = 3` for the tag `1` (`s = (h - 1)/2`). -/
def tagR : Fin 2 → ZMod 6 := ![1, 3]

/-- **`R_h` is the reflection of the cut `ϑ_{0,1+s}`** (`def:record:frame`(e), by `decide`). -/
theorem slotR_eq_flip (s : Fin 2) :
    ∀ v : Slot, EnvelopeSteps.slotREquiv (tagR s) v = (tagCut s).flip v := by
  fin_cases s
  · exact (by decide : ∀ v : Slot,
      EnvelopeSteps.slotREquiv (1 : ZMod 6) v = (firstChamberCut 1).flip v)
  · exact (by decide : ∀ v : Slot,
      EnvelopeSteps.slotREquiv (3 : ZMod 6) v = (firstChamberCut 2).flip v)

/-- `R_{h*} = ϑ_*` on measures, so `½(δ + R_{h*}δ)` is the symmetric part `Sym δ` at the cut. -/
theorem avg_slotPush_eq_symPart {X : Type} [Fintype X] [DecidableEq X] (s : Fin 2)
    (ζ : SlotMeasure X) :
    (1 / 2 : ℝ) • (ζ + Envelopes.slotPush (EnvelopeSteps.slotREquiv (tagR s)) ζ) =
      symPart (tagCut s) ζ := by
  have h : Envelopes.slotPush (EnvelopeSteps.slotREquiv (tagR s)) ζ = reflect (tagCut s) ζ := by
    apply LinearMap.ext
    intro F
    rw [Envelopes.slotPush_apply, reflect_apply]
    congr 1
    funext z
    congr 1
    funext v
    simp only [Function.comp_apply, slotR_eq_flip s v]
  rw [h]
  rfl

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- **The cut form of the record difference** (FirstStagePaper's computation in
`blockSharp_of_block`, for any pair of half-functions). -/
theorem form_diff_eq (h : ClassThreeBlock pr) (hne : MiddleNonempty pr) (s : Fin 2)
    (F G : ((tagCut s).Half → BlockLabel pr) → ℝ) :
    (tagCut s).form (plusRec pr h s - matchRec pr hne s) F G =
      kappaN pr * ∑ c : BlockLabel pr,
        (fun a : (∀ i, Vc (c i)) => G (hmF s (fun i => (a i).1) c)) ⬝ᵥ
          ((blockKp pr c - blockK0 pr c) *ᵥ
            (fun a : (∀ i, Vc (c i)) => F (hpF s (fun i => (a i).1) c))) := by
  set fC : ∀ c : BlockLabel pr, (∀ i, Vc (c i)) → ℝ :=
    fun c a => F (hpF s (fun i => (a i).1) c) with hfC
  set gC : ∀ c : BlockLabel pr, (∀ i, Vc (c i)) → ℝ :=
    fun c a => G (hmF s (fun i => (a i).1) c) with hgC
  have hsub : (tagCut s).form (plusRec pr h s - matchRec pr hne s) F G =
      (tagCut s).form (plusRec pr h s) F G - (tagCut s).form (matchRec pr hne s) F G := rfl
  rw [hsub, plusRec, matchRec, form_emit, form_emit]
  simp only [emit_plus_half, emit_minus_half]
  have e1 := blockPlus_expect pr h (fun a0 a1 c => F (hpF s a1 c) * G (hmF s a0 c))
  have e2 := blockMatch_expect pr hne (fun a0 a1 c => F (hpF s a1 c) * G (hmF s a0 c))
  rw [sum3_comm] at e1 e2
  rw [e1, e2, ← sum_sub_distrib, mul_sum]
  refine sum_congr rfl fun c _ => ?_
  rw [← sum_pair_diff pr c (fun a1 => F (hpF s a1 c)) (fun a0 => G (hmF s a0 c)),
    ← sum_sub_distrib]
  refine sum_congr rfl fun a0 _ => ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun a1 _ => ?_
  ring

/-- **`lem:record:one-stage-folded-e`(e), the bound of the symmetric part, on the 72-slot records**
(constant `s_crude(b)`): for a block of class-three primes `p ≥ b ≥ X ≥ 2^{24}` and `s = 0, 1`, the
symmetric part at `tagCut s` of `plusRec s - matchRec s` has sharp bound `s_crude(b)` relative to
`matchRec s`. -/
theorem blockSymSharp_of_block (h : ClassThreeBlock pr) (hne : MiddleNonempty pr) {X b : ℝ}
    (hX : 2 ^ 24 ≤ X) (hXb : X ≤ b) (hbp : ∀ i, b ≤ (pr i : ℝ)) (s : Fin 2) :
    HasSharpBound (tagCut s) (matchRec pr hne s)
      (symPart (tagCut s) (plusRec pr h s - matchRec pr hne s)) (sCrude b) := by
  let π : FiniteLaw Unit := { weight := fun _ => 1, nonneg := fun _ => zero_le_one,
                              total := by simp }
  have hm1 : mass (matchRec pr hne s) = 1 := mass_law _
  refine ⟨Unit, inferInstance, π, fun _ => matchRec pr hne s,
    fun _ => symPart (tagCut s) (plusRec pr h s - matchRec pr hne s),
    fun _ => ⟨isNonneg_law _, mass_law _⟩, ?_, ?_, ?_⟩
  · rw [hm1, Fintype.sum_unique]
    simp [π]
  · rw [hm1, Fintype.sum_unique]
    simp [π]
  intro _ F G
  set fC : ∀ c : BlockLabel pr, (∀ i, Vc (c i)) → ℝ :=
    fun c a => F (hpF s (fun i => (a i).1) c) with hfC
  set gC : ∀ c : BlockLabel pr, (∀ i, Vc (c i)) → ℝ :=
    fun c a => G (hmF s (fun i => (a i).1) c) with hgC
  have hform : (tagCut s).form (symPart (tagCut s) (plusRec pr h s - matchRec pr hne s)) F G =
      kappaN pr * ∑ c : BlockLabel pr, gC c ⬝ᵥ (blockSymD pr c *ᵥ fC c) := by
    rw [form_symPart, form_diff_eq pr h hne s F G, form_diff_eq pr h hne s G F]
    have hsw : ∀ c : BlockLabel pr,
        (fun a : (∀ i, Vc (c i)) => F (hmF s (fun i => (a i).1) c)) = fC c := by
      intro c
      funext a
      simp only [hfC, hpF_eq_hmF]
    have hsw' : ∀ c : BlockLabel pr,
        (fun a : (∀ i, Vc (c i)) => G (hpF s (fun i => (a i).1) c)) = gC c := by
      intro c
      funext a
      simp only [hgC, hpF_eq_hmF]
    simp only [hsw, hsw']
    rw [← mul_add, ← sum_add_distrib, mul_sum, mul_sum, mul_sum]
    refine sum_congr rfl fun c _ => ?_
    have ht : fC c ⬝ᵥ ((blockKp pr c - blockK0 pr c) *ᵥ gC c) =
        gC c ⬝ᵥ ((blockKp pr c - blockK0 pr c)ᵀ *ᵥ fC c) := by
      rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec, dotProduct_comm]
    rw [ht]
    unfold blockSymD
    rw [Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul, dotProduct_add, smul_eq_mul]
    ring
  have hmp : ∑ x, halfMarginalPlus (tagCut s) (matchRec pr hne s) x * F x ^ 2 =
      kappaN pr * ∑ c : BlockLabel pr, fC c ⬝ᵥ fC c := by
    rw [sum_halfPlus, matchRec, ← FiniteLaw.expect_eq_signedIntegral, expect_emit]
    simp only [Function.comp_apply, emit_plus_half]
    have e2 := blockMatch_expect pr hne (fun _ a1 c => F (hpF s a1 c) ^ 2)
    rw [e2, sum3_comm, mul_sum]
    exact sum_congr rfl fun c _ => sum_sq_one pr h c (fun a1 => F (hpF s a1 c))
  have hmm : ∑ y, halfMarginalMinus (tagCut s) (matchRec pr hne s) y * G y ^ 2 =
      kappaN pr * ∑ c : BlockLabel pr, gC c ⬝ᵥ gC c := by
    rw [sum_halfMinus, matchRec, ← FiniteLaw.expect_eq_signedIntegral, expect_emit]
    simp only [Function.comp_apply, emit_minus_half]
    have e2 := blockMatch_expect pr hne (fun a0 _ c => G (hmF s a0 c) ^ 2)
    rw [e2, sum3_comm, mul_sum]
    exact sum_congr rfl fun c _ => sum_sq_zero pr h c (fun a0 => G (hmF s a0 c))
  rw [hform, hmp, hmm]
  have hκ := kappaN_nonneg pr
  have hD : 0 ≤ sCrude b := by unfold sCrude; positivity
  have hterm : ∀ c, |gC c ⬝ᵥ (blockSymD pr c *ᵥ fC c)| ≤
      sCrude b * Real.sqrt (gC c ⬝ᵥ gC c) * Real.sqrt (fC c ⬝ᵥ fC c) :=
    fun c => block_sym_form_le pr h hX hXb hbp c (gC c) (fC c)
  have hff : ∀ c, 0 ≤ fC c ⬝ᵥ fC c := fun c => Sarkozy.IndexSupport.dotProduct_self_nonneg _
  have hgg : ∀ c, 0 ≤ gC c ⬝ᵥ gC c := fun c => Sarkozy.IndexSupport.dotProduct_self_nonneg _
  calc |kappaN pr * ∑ c, gC c ⬝ᵥ (blockSymD pr c *ᵥ fC c)|
      = kappaN pr * |∑ c, gC c ⬝ᵥ (blockSymD pr c *ᵥ fC c)| := by
        rw [abs_mul, abs_of_nonneg hκ]
    _ ≤ kappaN pr * ∑ c, |gC c ⬝ᵥ (blockSymD pr c *ᵥ fC c)| :=
        mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) hκ
    _ ≤ kappaN pr * ∑ c, sCrude b * Real.sqrt (gC c ⬝ᵥ gC c) *
          Real.sqrt (fC c ⬝ᵥ fC c) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun c _ => hterm c) hκ
    _ = sCrude b * (kappaN pr * ∑ c, Real.sqrt (fC c ⬝ᵥ fC c) *
          Real.sqrt (gC c ⬝ᵥ gC c)) := by
        rw [mul_sum, mul_sum, mul_sum]
        refine sum_congr rfl fun c _ => ?_
        ring
    _ ≤ sCrude b * (kappaN pr * (Real.sqrt (∑ c, fC c ⬝ᵥ fC c) *
          Real.sqrt (∑ c, gC c ⬝ᵥ gC c))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (sum_sqrt_mul_le univ _ _ hff hgg) hκ) hD
    _ = sCrude b * Real.sqrt (kappaN pr * ∑ c, fC c ⬝ᵥ fC c) *
          Real.sqrt (kappaN pr * ∑ c, gC c ⬝ᵥ gC c) := by
        rw [Real.sqrt_mul hκ, Real.sqrt_mul hκ]
        have hs : Real.sqrt (kappaN pr) * Real.sqrt (kappaN pr) = kappaN pr :=
          Real.mul_self_sqrt hκ
        linear_combination (-(sCrude b * Real.sqrt (∑ c, fC c ⬝ᵥ fC c) *
          Real.sqrt (∑ c, gC c ⬝ᵥ gC c))) * hs


/-- **The symmetric sharp bound of the frame's tagged differences** (the scaled block statement, as
`FirstStagePaper.middle_sharp`): at a middle block, the symmetric part at `tagCut s` of
`newRecN s - oldRec s` has sharp bound `s_crude(b)` relative to `oldRec s`. These are the records
`κ`, `κ'` of `FirstStagePaper.middleStage` (tag `s`, cut `tagCut s`). -/
theorem middle_symSharp (hne : MiddleNonempty pr)
    (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr))
    (W : MiddleWeights) (I : MiddleInputs) {r : ℝ} (hr : 0 ≤ r) (bmin : ℝ)
    (h : ClassThreeBlock pr) {X b : ℝ} (hX : 2 ^ 24 ≤ X) (hXb : X ≤ b)
    (hbp : ∀ i, b ≤ (pr i : ℝ)) (s : Fin 2) :
    HasSharpBound (tagCut s) ((middleFrame pr hne root W I hr bmin h).oldRec s)
      (symPart (tagCut s) ((middleFrame pr hne root W I hr bmin h).newRecN s -
        (middleFrame pr hne root W I hr bmin h).oldRec s)) (sCrude b) := by
  set w := (middleFrame pr hne root W I hr bmin h).P⁻¹ * ((W.v .S + W.v .D) * r ^ 2) with hw
  have hb := hasSharpBound_smul (blockSymSharp_of_block pr h hne hX hXb hbp s) w
  rw [middle_oldRec, middle_newRecN, ← hw,
    show w • plusRec pr h s - w • matchRec pr hne s = w • (plusRec pr h s - matchRec pr hne s)
      from (smul_sub w _ _).symm]
  have e : symPart (tagCut s) (w • (plusRec pr h s - matchRec pr hne s)) =
      w • symPart (tagCut s) (plusRec pr h s - matchRec pr hne s) := by
    unfold symPart
    rw [reflect_smul, ← smul_add, smul_comm]
  rw [e]
  exact hb

end Block

section Bridge

open Sarkozy.BlockFrame Sarkozy.EnvelopeSteps Sarkozy.Envelopes Sarkozy.RecordExpansion.Choice

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

omit [DecidableEq P] in
/-- **`hsymT` from the symmetric part at the cut** (`hsymT_of_sym` with `R_h = R_{tagR t}`, whose
average `½(δ + R_{h*}δ)` is `Sym δ` at `tagCut t`): the remaining input of `hsym` is a bound on the
energy `Y_{κ̄ ⊗ Sym δ ⊗ O}`, `Sym δ` the symmetric part whose sharp bound is
`blockSymSharp_of_block` / `middle_symSharp`. -/
theorem hsymT_of_symPart (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (A : Finset ℤ) (isG : ∀ b : BlockAtom Bk J L, D.GB.Iu L b → Bool)
    (S : Finset (BlockAtom Bk J L)) (Q₁ Q₂ : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (s : D.FS.Tag) (t : Fin 2)
    (hκ : slotPush (slotREquiv (tagR t)) (orbitBar L S Q₁ Q₂) = orbitBar L S Q₁ Q₂)
    (hinvN : ∀ j : {b // b ∉ S},
      slotPush (slotREquiv (tagR t)) (ninvP D L isG j.1) = ninvP D L isG j.1)
    (B r : (∀ b, Option (D.FS.Ib L b)) → ℝ) (hBr : ∀ σ, 0 ≤ B σ + r σ)
    (hS : ∀ σ ∈ (univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)).filter
        (fun σ => countVec (D.FS.tag L) σ = Pi.single s 1),
      ∀ b' : {b // b ∉ S}, (σ b'.1).isSome →
      |jointEnergy (orbitBar L S Q₁ Q₂)
          (tensorLaw (Function.update (catOut D L isG S σ) b'
            (symPart (tagCut t) (catOut D L isG S σ b'))))
          (fun z => blockLift m₀ blk p L A (merge S z))| ≤ B σ + r σ) :
    ∀ σ ∈ (univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)).filter
        (fun σ => countVec (D.FS.tag L) σ = Pi.single s 1),
      |catT D L A isG S Q₁ Q₂ σ (fun _ => false)| ≤ B σ + r σ :=
  hsymT_of_sym D L A isG S Q₁ Q₂ s (tagR t) hκ hinvN B r hBr (fun σ hσ b' hb' => by
    rw [avg_slotPush_eq_symPart]
    exact hS σ hσ b' hb')

end Bridge

end Sarkozy.OpsSteps
