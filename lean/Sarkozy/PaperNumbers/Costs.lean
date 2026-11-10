module

public import Sarkozy.PaperNumbers.FirstStage
public import Sarkozy.PaperNumbers.ChargeData
public import Sarkozy.RecordExpansion.TwoTags

@[expose] public section

/-!
# The two cost inequalities at the recorded charges (`hB`, `hL₀`)

`main_target_paper_joint_N1_numbers` reduces `hB` and `hL₀` to bounds `pieceBound a_T d i ≤ c_d(i)`
and two cost inequalities in the numbers `c_d(i)`. Here the numbers are fixed to `chargeC2`,
`chargeC3` (`ChargeData.lean`: the recorded degree charges of `final_L570_source.json`, repriced to
`a_T` by R1's factor `t`, with a slack `1 + 4·10⁻⁴`), and both cost inequalities are proved:

* the coefficients `U₂`, `U₃`, `4 v_D`, `2 |f₁ + h₁| v_D`, `2 (v_S + v_D)` are the rationals of the
  ALLp records (`chargeU2_eq`, …); `(v_S + v_D) k_new(X_i)` is bounded by its value at
  `r = 1/⌊√X_i⌋` (`fsD3_le`);
* the four totals are bounded by decimals (`costU`, `costP`, `costD`, `costV`), kernel-checked;
* the tag series over the two tags is bounded by `cor:two-cut-series` (`tagSeries_two_le`, `n = 3`),
  after relabelling `Fin 2` as `Bool` (`tagSeries_fin_two`);
* the exponentials by the rational Taylor witnesses of `Certificates.ExpWitness`.

**`costB_le`**: `e^{∑ (U₂ c₂ + U₃ c₃)} (1 + 𝔗(D, V)) ≤ B^{ledger} = 2.016052216152`;
**`costL_le`**: `e^P 𝔗(D, V) ≤ L₀^{ledger} = 0.000271970853` (RB's package R at `a_G = 71/10⁵`;
the `a_T` below is the ledger's exponent `TargetLedger.targetDecay`, now `a_G`; RG).

**`main_target_paper_joint_N1_final`**: the main statement with `hB` and `hL₀` discharged except for
the 66 per-piece hypotheses `pieceBound a_T d i ≤ c_d(i)`, `d = 2, 3`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.PaperNumbers

open Sarkozy.PartV Sarkozy.BlockSpecPaper Sarkozy.RecordExpansion Sarkozy.Certificates
  Sarkozy.MiddleRecords
open Sarkozy.TargetLedger (targetDecay targetLedger)

/-! ## The tag series over `Fin 2` is the one over `Bool` -/

theorem tagTerm_comp_equiv {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (σ : α ≃ β) (d v : ℝ) (k : β → ℕ) (j : α) :
    tagTerm (fun _ : α => d) (fun _ => v) (k ∘ σ) j =
      tagTerm (fun _ : β => d) (fun _ => v) k (σ j) := by
  unfold tagTerm
  congr 1
  · rw [← Equiv.prod_comp σ.symm]
    refine Finset.prod_congr rfl fun b _ => ?_
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
    by_cases h : b = σ j
    · subst h
      simp
    · have h' : σ.symm b ≠ j := fun e => h (by rw [← e, Equiv.apply_symm_apply])
      simp [h, h']
  · rw [← Equiv.prod_comp σ.symm]
    simp only [Function.comp_apply, Equiv.apply_symm_apply]

theorem tagMin_comp_equiv {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (σ : α ≃ β) (d v : ℝ) (k : β → ℕ) :
    tagMin (fun _ : α => d) (fun _ => v) (k ∘ σ) = tagMin (fun _ : β => d) (fun _ => v) k := by
  have hset : tagsOf (k ∘ σ) = (tagsOf k).map σ.symm.toEmbedding := by
    ext j
    simp only [tagsOf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Equiv.coe_toEmbedding, Function.comp_apply]
    constructor
    · intro h
      exact ⟨σ j, h, by simp⟩
    · rintro ⟨b, hb, rfl⟩
      simpa using hb
  unfold tagMin
  by_cases hne : (tagsOf k).Nonempty
  · have hne' : (tagsOf (k ∘ σ)).Nonempty := by
      rw [hset]
      exact hne.map
    simp only [hne', hne, ↓reduceDIte]
    simp only [hset]
    rw [Finset.inf'_map]
    refine le_antisymm ?_ ?_ <;>
    · apply Finset.le_inf'
      intro b hb
      simp only [Function.comp_apply, Equiv.coe_toEmbedding, tagTerm_comp_equiv,
        Equiv.apply_symm_apply]
      exact Finset.inf'_le _ hb
  · have hne' : ¬ (tagsOf (k ∘ σ)).Nonempty := by
      rw [hset, Finset.map_nonempty]
      exact hne
    simp only [hne', hne, ↓reduceDIte]

/-- **Relabelling the two tags**: `𝔗` over `Fin 2` at constant totals is `𝔗` over `Bool`. -/
theorem tagSeries_fin_two (d v : ℝ) :
    tagSeries (fun _ : Fin 2 => d) (fun _ => v) = tagSeries (fun _ : Bool => d) (fun _ => v) := by
  unfold tagSeries
  let e : (Bool → ℕ) ≃ (Fin 2 → ℕ) := Equiv.arrowCongr finTwoEquiv.symm (Equiv.refl ℕ)
  rw [← e.tsum_eq]
  congr 1
  funext k
  have hk : e k = k ∘ finTwoEquiv := by
    funext j
    rfl
  rw [hk, tagMin_comp_equiv]

/-! ## The coefficients as rationals -/

/-- `U₂ = 2 v_D`. -/
def U2Q (i : Fin 33) : ℚ := 2 * (AllpData.allpRecord i).vD

/-- `U₃ = 2 v_D (f₁ + h₁) + 12 w_S/(1 - 3/X_i)`. -/
def U3Q (i : Fin 33) : ℚ :=
  2 * (AllpData.allpRecord i).vD * ((AllpData.allpRecord i).f₁ + (AllpData.allpRecord i).h₁) +
    12 * (AllpData.allpRecord i).wD / (1 - 3 / (pieceStart i : ℚ))

/-- `4 v_D`. -/
def P2Q (i : Fin 33) : ℚ := 4 * (AllpData.allpRecord i).vD

/-- `2 |f₁ + h₁| v_D`. -/
def P3Q (i : Fin 33) : ℚ :=
  2 * |(AllpData.allpRecord i).f₁ + (AllpData.allpRecord i).h₁| * (AllpData.allpRecord i).vD

/-- `2 (v_S + v_D)`. -/
def V2Q (i : Fin 33) : ℚ := 2 * ((AllpData.allpRecord i).vD + (AllpData.allpRecord i).vD)

/-- `k_new(X)` at `q' = 1/X` and `r = 1/⌊√X⌋ ≥ X^{-1/2}`. -/
def knewQ (X : ℕ) : ℚ :=
  (1 + 5 * (1 / (X : ℚ))) / ((1 - 3 * (1 / (X : ℚ))) * (1 + 1 / (X : ℚ))) +
    1 / (X : ℚ) * (1 / (Nat.sqrt X : ℚ)) / ((1 - 3 * (1 / (X : ℚ))) * (1 - 2 * (1 / (X : ℚ))))

/-- `(v_S + v_D) k_new(X_i)` with `r = 1/⌊√X_i⌋`. -/
def D3Q (i : Fin 33) : ℚ :=
  ((AllpData.allpRecord i).vD + (AllpData.allpRecord i).vD) * knewQ (pieceStart i)

theorem chargeU2_eq (i : Fin 33) : chargeU2 i = (U2Q i : ℝ) := by
  unfold chargeU2 U2Q
  push_cast
  rfl

theorem chargeU3_eq (i : Fin 33) : chargeU3 i = (U3Q i : ℝ) := by
  unfold chargeU3 U3Q
  push_cast
  rfl

theorem fsP2_eq (i : Fin 33) : fsP2 i = (P2Q i : ℝ) := by
  unfold fsP2 P2Q
  push_cast
  rfl

theorem fsP3_eq (i : Fin 33) : fsP3 i = (P3Q i : ℝ) := by
  unfold fsP3 P3Q
  push_cast
  rfl

theorem fsV2_eq (i : Fin 33) : fsV2 i = (V2Q i : ℝ) := by
  unfold fsV2 V2Q
  push_cast
  rfl

theorem knew_le_knewQ {X : ℕ} (hX : 4 ≤ X) :
    PartVRecords.knew (1 / (X : ℝ)) (1 / Real.sqrt (X : ℝ)) ≤ (knewQ X : ℝ) := by
  have hX' : (4 : ℝ) ≤ X := by exact_mod_cast hX
  have hs1 : 1 ≤ Nat.sqrt X := Nat.le_sqrt.mpr (by omega)
  have hs1' : (1 : ℝ) ≤ (Nat.sqrt X : ℝ) := by exact_mod_cast hs1
  have hsle : (Nat.sqrt X : ℝ) ≤ Real.sqrt X := Real.nat_sqrt_le_real_sqrt
  have hr : 1 / Real.sqrt (X : ℝ) ≤ 1 / (Nat.sqrt X : ℝ) :=
    one_div_le_one_div_of_le (by linarith) hsle
  have hq : 0 < 1 / (X : ℝ) := by positivity
  have hq3 : 1 / (X : ℝ) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hX'
  have h1 : 0 < 1 - 3 * (1 / (X : ℝ)) := by linarith
  have h2 : 0 < 1 - 2 * (1 / (X : ℝ)) := by linarith
  unfold PartVRecords.knew knewQ
  push_cast
  gcongr

theorem fsD3_le (i : Fin 33) : fsD3 i ≤ (D3Q i : ℝ) := by
  unfold fsD3 D3Q
  have hX : 4 ≤ pieceStart i := le_trans (by norm_num [Q3]) (pieceStart_ge_Q3 i)
  have h := knew_le_knewQ hX
  have hv : (0 : ℝ) ≤ (allpWeights i).v .S + (allpWeights i).v .D :=
    add_nonneg ((allpWeights i).v_nonneg _) ((allpWeights i).v_nonneg _)
  push_cast
  exact mul_le_mul_of_nonneg_left h hv

/-! ## The totals (kernel-checked) -/

theorem sumU_le : ∑ i, (U2Q i * chargeC2 i + U3Q i * chargeC3 i) ≤ costU := by decide +kernel

theorem sumP_le : ∑ i, (P2Q i * chargeC2 i + P3Q i * chargeC3 i) ≤ costP := by decide +kernel

theorem sumD_le : ∑ i, D3Q i * chargeC3 i ≤ costD := by decide +kernel

theorem sumV_le : ∑ i, V2Q i * chargeC2 i ≤ costV := by decide +kernel

theorem chargeC_nonneg : ∀ i, 0 ≤ chargeC2 i ∧ 0 ≤ chargeC3 i := by decide +kernel

/-! ## The exponentials and the tag series -/

/-- The upper end `upper^k` of an exponential witness. -/
def expUpper (w : ExpWitness) : ℚ := w.upper ^ w.divisions

theorem costU_valid : costUWitness.Valid costU ⟨0, expUpper costUWitness⟩ := by
  unfold ExpWitness.Valid
  decide +kernel

theorem costP_valid : costPWitness.Valid costP ⟨0, expUpper costPWitness⟩ := by
  unfold ExpWitness.Valid
  decide +kernel

theorem costV_valid : costVWitness.Valid costV ⟨0, expUpper costVWitness⟩ := by
  unfold ExpWitness.Valid
  decide +kernel

theorem costD_nonneg : (0 : ℝ) ≤ (costD : ℝ) := by
  have : (0 : ℚ) ≤ costD := by decide +kernel
  exact_mod_cast this

theorem costV_nonneg : (0 : ℝ) ≤ (costV : ℝ) := by
  have : (0 : ℚ) ≤ costV := by decide +kernel
  exact_mod_cast this

/-- **`cor:two-cut-series` at the recorded totals**: `𝔗⁺₃(costD, costV) ≤ costT`. -/
theorem twoTagUpper_le : twoTagUpper 3 (costD : ℝ) (costV : ℝ) ≤ (costT : ℝ) := by
  have hE : Real.exp (costV : ℝ) ≤ (expUpper costVWitness : ℝ) := (ExpWitness.sound costV_valid).2
  unfold twoTagUpper twoGroup
  generalize Real.exp (costV : ℝ) = y at hE ⊢
  norm_num [Finset.sum_range_succ, Nat.factorial, costD, costV, costT, expUpper, costVWitness]
    at hE ⊢
  linarith

/-- **The tag series at the recorded charges**: `𝔗(D, V) ≤ costT` for tag totals `≤ costD`,
`costV`. -/
theorem tagSeries_le_costT {d v : Fin 2 → ℝ} (hd0 : ∀ j, 0 ≤ d j) (hv0 : ∀ j, 0 ≤ v j)
    (hd : ∀ j, d j ≤ costD) (hv : ∀ j, v j ≤ costV) : tagSeries d v ≤ (costT : ℝ) := by
  have h1 := tagSeries_mono (d' := fun _ => (costD : ℝ)) (v' := fun _ => (costV : ℝ)) hd0 hv0 hd hv
  rw [tagSeries_fin_two] at h1
  have hgate1 : (costD : ℝ) < (3 : ℕ) + 2 := by norm_num [costD]
  have hgate2 : (costD : ℝ) * costV < (((3 : ℕ) : ℝ) + 2) ^ 2 := by norm_num [costD, costV]
  exact h1.trans ((tagSeries_two_le costD_nonneg costV_nonneg 3 hgate1 hgate2).trans
    twoTagUpper_le)

/-! ## The two cost inequalities -/

/-- The tag totals at the recorded charges. -/
noncomputable def chargeD : Fin 2 → ℝ := fun _ =>
  ∑ i, (0 * (chargeC2 i : ℝ) + fsD3 i * (chargeC3 i : ℝ))

/-- The variation tag totals at the recorded charges. -/
noncomputable def chargeV : Fin 2 → ℝ := fun _ =>
  ∑ i, (fsV2 i * (chargeC2 i : ℝ) + 0 * (chargeC3 i : ℝ))

theorem chargeD_le (j : Fin 2) : chargeD j ≤ costD := by
  unfold chargeD
  have h : ∑ i, (0 * (chargeC2 i : ℝ) + fsD3 i * (chargeC3 i : ℝ)) ≤
      ∑ i, ((D3Q i * chargeC3 i : ℚ) : ℝ) :=
    sum_le_sum fun i _ => by
      push_cast
      rw [zero_mul, zero_add]
      exact mul_le_mul_of_nonneg_right (fsD3_le i) (by exact_mod_cast (chargeC_nonneg i).2)
  refine h.trans ?_
  rw [← Rat.cast_sum]
  exact_mod_cast sumD_le

theorem chargeV_le (j : Fin 2) : chargeV j ≤ costV := by
  unfold chargeV
  have h : ∑ i, (fsV2 i * (chargeC2 i : ℝ) + 0 * (chargeC3 i : ℝ)) =
      ∑ i, ((V2Q i * chargeC2 i : ℚ) : ℝ) :=
    sum_congr rfl fun i _ => by
      push_cast
      rw [fsV2_eq, zero_mul, add_zero]
  rw [h, ← Rat.cast_sum]
  exact_mod_cast sumV_le

theorem chargeD_nonneg (j : Fin 2) : 0 ≤ chargeD j :=
  sum_nonneg fun i _ => by
    rw [zero_mul, zero_add]
    exact mul_nonneg (fsD3_nonneg i) (by exact_mod_cast (chargeC_nonneg i).2)

theorem chargeV_nonneg (j : Fin 2) : 0 ≤ chargeV j :=
  sum_nonneg fun i _ => by
    rw [zero_mul, add_zero]
    exact mul_nonneg (fsV2_nonneg i) (by exact_mod_cast (chargeC_nonneg i).1)

/-- **The cost inequality of `hB` at the recorded charges** (kernel-checked rational arithmetic and
Taylor witnesses): `e^{∑ (U₂ c₂ + U₃ c₃)} (1 + 𝔗(D, V)) ≤ B^{ledger}`. -/
theorem costB_le :
    Real.exp (∑ i : Fin 33, (chargeU2 i * (chargeC2 i : ℝ) + chargeU3 i * (chargeC3 i : ℝ))) *
      (1 + tagSeries chargeD chargeV) ≤ targetLedger.B := by
  have hsum : ∑ i : Fin 33, (chargeU2 i * (chargeC2 i : ℝ) + chargeU3 i * (chargeC3 i : ℝ)) =
      ((∑ i, (U2Q i * chargeC2 i + U3Q i * chargeC3 i) : ℚ) : ℝ) := by
    rw [Rat.cast_sum]
    exact sum_congr rfl fun i _ => by
      push_cast
      rw [chargeU2_eq, chargeU3_eq]
  have hU : Real.exp (∑ i : Fin 33, (chargeU2 i * (chargeC2 i : ℝ) +
      chargeU3 i * (chargeC3 i : ℝ))) ≤ (expUpper costUWitness : ℝ) := by
    rw [hsum]
    refine (Real.exp_le_exp.mpr ?_).trans (ExpWitness.sound costU_valid).2
    exact_mod_cast sumU_le
  have hT := tagSeries_le_costT chargeD_nonneg chargeV_nonneg chargeD_le chargeV_le
  have hT0 : 0 ≤ tagSeries chargeD chargeV := tagSeries_nonneg chargeD_nonneg chargeV_nonneg
  have hE0 : (0 : ℝ) ≤ (expUpper costUWitness : ℝ) := (Real.exp_pos _).le.trans hU
  calc Real.exp (∑ i : Fin 33, (chargeU2 i * (chargeC2 i : ℝ) + chargeU3 i * (chargeC3 i : ℝ))) *
        (1 + tagSeries chargeD chargeV)
      ≤ (expUpper costUWitness : ℝ) * (1 + (costT : ℝ)) :=
        mul_le_mul hU (by linarith) (by linarith) hE0
    _ ≤ targetLedger.B := by
        norm_num [targetLedger, expUpper, costUWitness, costT]

/-- **The cost inequality of `hL₀` at the recorded charges**: `e^P 𝔗(D, V) ≤ L₀^{ledger}`. -/
theorem costL_le :
    TheoremC.firstStageCost (∑ i, (fsP2 i * (chargeC2 i : ℝ) + fsP3 i * (chargeC3 i : ℝ)))
      chargeD chargeV ≤ targetLedger.L₀ := by
  have hsum : ∑ i, (fsP2 i * (chargeC2 i : ℝ) + fsP3 i * (chargeC3 i : ℝ)) =
      ((∑ i, (P2Q i * chargeC2 i + P3Q i * chargeC3 i) : ℚ) : ℝ) := by
    rw [Rat.cast_sum]
    exact sum_congr rfl fun i _ => by
      push_cast
      rw [fsP2_eq, fsP3_eq]
  have hP : Real.exp (∑ i, (fsP2 i * (chargeC2 i : ℝ) + fsP3 i * (chargeC3 i : ℝ))) ≤
      (expUpper costPWitness : ℝ) := by
    rw [hsum]
    refine (Real.exp_le_exp.mpr ?_).trans (ExpWitness.sound costP_valid).2
    exact_mod_cast sumP_le
  have hT := tagSeries_le_costT chargeD_nonneg chargeV_nonneg chargeD_le chargeV_le
  have hT0 : 0 ≤ tagSeries chargeD chargeV := tagSeries_nonneg chargeD_nonneg chargeV_nonneg
  have hE0 : (0 : ℝ) ≤ (expUpper costPWitness : ℝ) := (Real.exp_pos _).le.trans hP
  unfold TheoremC.firstStageCost
  calc Real.exp (∑ i, (fsP2 i * (chargeC2 i : ℝ) + fsP3 i * (chargeC3 i : ℝ))) *
        tagSeries chargeD chargeV
      ≤ (expUpper costPWitness : ℝ) * (costT : ℝ) := mul_le_mul hP hT hT0 hE0
    _ ≤ targetLedger.L₀ := by
        norm_num [targetLedger, expUpper, costPWitness, costT]

/-! ## The main statement -/

open Sarkozy.JointClosing Sarkozy.FirstStagePaper Sarkozy.PartVLaws in
/-- **The main statement at `ε = a_T/71` at the paper's partition, with `hB` and `hL₀` reduced to
66 per-piece charge bounds** (`thm:main` at `ε = a_T/71`, `cor:joint-closing`,
`def:construction`(b), `lem:record:block-charge`, `lem:record:middle-prices`,
`def:closing-quantities`(2), (3), `cor:two-cut-series`): from the hypotheses H1 (`Weil`), H2
(`BMOR`), H5 (`MovingRoot`), `thm:dl:K` (`FourCycle`), H2″ (`ThetaSmallRR`), the
lemma families `hU`, `hM`, `hI` (`lem:upper-reference-rp`(ii), `lem:front12:reference`(i),(ii)),
* the **66 charge bounds** `pieceBound a_T d i ≤ c_d(i)`, `d = 2, 3`, `i < 33`, at the recorded
  numbers `c_d(i) = chargeC2 i`, `chargeC3 i` (*hypotheses*, numerical: M2's explicit bound of the
  paper's blocks, i.e. the price buckets of the greedy blocks below `X_Ch` and the cell integrals
  above it, at `a_T`, against `1.0004 t I_d(i)`; `cert:record:middle-price`,
  `lem:record:repricing`);
* and the 9 fields `Dv` (`CL`, `ME`, `SM`), `hT`, `hSA`, `JB`, `SF`, `fix`, `env`.

The cost inequalities of `hB` and `hL₀` are proved (`costB_le`, `costL_le`). -/
theorem main_target_paper_joint_N1_final (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (hU : ∀ k, UpperBandLemma k) (hM : ∀ i, allpIndividual i = none → MiddleUniformLemma i)
    (hI : ∀ i u, allpIndividual i = some u → MiddleIndividualLemma i u)
    (Dv : N1JointBlockData hWeil hMovingRoot hFourCycle hU hM hI)
    (h₂ : ∀ i, pieceBound targetDecay 2 i ≤ chargeC2 i)
    (h₃ : ∀ i, pieceBound targetDecay 3 i ≤ chargeC3 i)
    (hT : Dv.toJoint.data.ME.T ≤ targetLedger.T)
    (hSA : Dv.toJoint.data.CL.S + Dv.toJoint.data.CL.A ≤ targetLedger.S + targetLedger.A)
    (JB : JointBound Dv.toJoint.data targetLedger.jointConstant)
    (SF : EnvelopeInputsBlock.SharpFirstInputs Dv.toJoint.data)
    (fix : EnvelopeInputsBlock.FixedIntervalInputs
      (BlockAnchor.index_coprime_block Dv.toJoint.data) Dv.toJoint.data)
    (env : EnvelopeInputsBlock.EnvelopeEnergyInputs
      (BlockAnchor.index_coprime_block Dv.toJoint.data) Dv.toJoint.data) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_joint_N1_numbers hWeil hBMOR hMovingRoot hFourCycle
    hThetaSmallRR hU hM hI Dv (c₂ := fun i => (chargeC2 i : ℝ)) (c₃ := fun i => (chargeC3 i : ℝ))
    h₂ h₃ costB_le costL_le hT hSA JB SF fix env

end Sarkozy.PaperNumbers
