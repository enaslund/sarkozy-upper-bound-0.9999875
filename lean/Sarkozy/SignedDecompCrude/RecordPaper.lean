module

public import Sarkozy.SignedDecompCrude.Paper
public import Sarkozy.SignedDecompCrude.Record
public import Sarkozy.MainFinalF1.K3

@[expose] public section

/-!
# (K) at the paper's fold records: `NewDecomp` at the explicit `e_sg′ = esgND` (ND)

`paper/sections/21_middle_records.tex`, `prop:signed-bounds`(c), last claim, at every prime of
every middle block of the F1 data.

The components of a middle block are `paperComponents E.toDC` for the block's middle estimates
`E : MiddleEstimates b hne` (K2), whose repair constants are `M_c = M_c(η_p, e_p)`
(`DefectConstants.ofEstimates`) and whose `SignedEstimates.z` gives `|z_{uv} - 1| ≤ η_p`. With
**`η_p ≤ 10/p` and `e_p ≤ e₀(p)`** (the paper's values; E1's `paperMiddleEstimates` has them with
equality, `paperMiddleEstimates_est`), (K) holds at

* **`κRec p = (1 + t) (δ(10/p, M̄) X₁(p) + 4 M̄ X₂(p)) p`**, `M̄ = M_c(10/p, e₀(p))`
  (`recordForm_block`).

So, with the nonstars and the removed query proved, `NewDecomp` holds at every prime with
**`e_sg′(p) = esgCrude κRec nT p`**
`= κRec p + c_g/q + 6 (D_g/q) Γ_A r + (nT p + kRQ p)/(1 - e₀)`, explicit in `p`. At `Q₃` it is
about `19.62` (an untrusted float evaluation: `κRec ≈ 0.504`, `nT ≈ 5.143`, `kRQ ≈ 13.968`,
the transport term `≈ 0.0054`), against the paper's `e_sg < 17.254638`.

* **`EstInputs C`** (1 field: `η_p ≤ 10/p`, `e_p ≤ e₀(p)` for the estimates of `C` at every middle
  block), **`EstInputs.toSD`**: with the gates `PieceGate (esgCrude κRec nT) 38 k`, PG's
  `SignedDecompInputsC C`.
-/

open Finset Matrix

namespace Sarkozy.SignedDecompCrude

open Sarkozy.PrimeGram Sarkozy.SignedGram Sarkozy.SignedComponents Sarkozy.Labellings
open Sarkozy.SignedDecomp
open Sarkozy.MiddleComparison (signedCoef)
open Sarkozy.PartV (MiddleNonempty)
open Sarkozy.MainFinal2 (tPaper tPaper_nonneg tPaper_le_one)
open Sarkozy.PartVLaws (PaperBlockSpec blockPrimes)
open Sarkozy.MainFinalF1 (bOf Blk SignedSpec specF analyticInputs MiddleEstimates)
open Sarkozy.MainFinalF1c (ComparisonPartsTC)
open Sarkozy.BlockSpecPaper
open Sarkozy.AnalyticCells (f1Cell)

theorem Mc_mono {η η' e e' : ℝ} (hη0 : 0 ≤ η) (hηη : η ≤ η') (hη1 : η' < 1) (he0 : 0 ≤ e)
    (hee : e ≤ e') (he1 : e' < 1) : Mc η e ≤ Mc η' e' := by
  unfold Mc
  have h1 : 0 < 1 - η' := by linarith
  have h2 : 0 < 1 - e' := by linarith
  have hden : (1 - η') * (1 - e') ≤ (1 - η) * (1 - e) :=
    mul_le_mul (by linarith) (by linarith) h2.le (by linarith)
  have hnum : 2 * η + (1 + η) * e ≤ 2 * η' + (1 + η') * e' :=
    by nlinarith [mul_le_mul (by linarith : 1 + η ≤ 1 + η') hee he0 (by linarith)]
  exact div_le_div₀ (by nlinarith) hnum (mul_pos h1 h2) hden

theorem deltaC_mono2 {η η' M M' : ℝ} (hη0 : 0 ≤ η) (hηη : η ≤ η') (hη1 : η' < 1) (hM0 : 0 ≤ M)
    (hMM : M ≤ M') : deltaC η M ≤ deltaC η' M' := by
  unfold deltaC
  have h1 : 0 < 1 - η' := by linarith
  have hnum : η + 2 * M * (1 + η) ≤ η' + 2 * M' * (1 + η') := by
    nlinarith [mul_le_mul (by linarith : 2 * M ≤ 2 * M') (by linarith : 1 + η ≤ 1 + η')
      (by linarith) (by linarith)]
  exact div_le_div₀ (by nlinarith) hnum h1 (by linarith)

theorem recordForm_mono {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {hF : (injLabellings F (foldGraph (Fin 2))).Nonempty} {N : Matrix (Fin 3 → F) (Fin 3 → F) ℝ}
    {t κ κ' : ℝ} (h : RecordForm hF N t κ) (hκ : κ ≤ κ') : RecordForm hF N t κ' := by
  intro f g hf hg
  refine (h f g hf hg).trans ?_
  have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hκ hq)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- `|H_F| = p(p - 1)(p - 2)/2`. -/
noncomputable def Hp (p : ℕ) : ℝ := (p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2) / 2

/-- `M̄(p) = M_c(10/p, e₀(p))`. -/
noncomputable def Mbar (p : ℕ) : ℝ := Mc (10 / (p : ℝ)) (Sarkozy.SignedEstimates.e0 (p : ℝ))

/-- **The constant of (K)** at the paper's estimates:
`κRec p = (1 + t)(δ(10/p, M̄) X₁(p) + 4 M̄ X₂(p)) p`. -/
noncomputable def κRec (p : ℕ) : ℝ :=
  (1 + tPaper) * (deltaC (10 / (p : ℝ)) (Mbar p) *
      X1C (p : ℝ) (Sarkozy.SignedEstimates.e0 (p : ℝ)) (Hp p) +
    4 * Mbar p * X2C (p : ℝ) (Sarkozy.SignedEstimates.e0 (p : ℝ)) (Hp p)) * (p : ℝ)

/-- **(K) at a prime of a middle block**, for components built from middle estimates with
`η_p ≤ 10/p` and `e_p ≤ e₀(p)` (`prop:signed-bounds`(c), Step 1 for the three components). -/
theorem recordForm_block {b : Blk} (hne : MiddleNonempty (blockPrimes bOf b))
    (E : MiddleEstimates b hne) (i)
    (hη : E.η i ≤ 10 / (blockPrimes bOf b i : ℝ))
    (he : E.e i ≤ Sarkozy.SignedEstimates.e0 (blockPrimes bOf b i : ℝ)) :
    RecordForm (hne.F2 i) (∑ c, signedCoef tPaper c • compP hne (paperComponents E.toDC) c i)
      tPaper (κRec (blockPrimes bOf b i)) := by
  set p := blockPrimes bOf b i with hpdef
  have h3 : p % 4 = 3 := (Sarkozy.FirstStagePaper.blockPrimes_mod_ge b i).1
  have h19 : 19 ≤ p := blockPrimes_ge19 b i
  have h24 : (16777216 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast Sarkozy.MainFinalF1.blockPrime_ge b i
  have hR' := ringChar_zmod_ne_two h3
  have h3' := card_zmod_mod h3
  have h19' := card_zmod_ge h19
  have hN : ∀ a a', (∑ c, signedCoef tPaper c • compP hne (paperComponents E.toDC) c i) a a' =
      ∑ c, signedCoef tPaper c * (repairInput hR' h3' h19' (hne.F2 i) tPaper_nonneg tPaper_le_one
        c).repair (E.toDC.M i c) (a, a') := by
    intro a a'
    rw [Matrix.sum_apply]
    refine sum_congr rfl fun c _ => ?_
    rw [Matrix.smul_apply, smul_eq_mul]
    congr 1
    exact congrFun (congrFun (Sarkozy.CompSharp.compP_blockComponents
      (fun j => (Sarkozy.FirstStagePaper.blockPrimes_mod_ge b j).1) (blockPrimes_ge19 b) hne
      tPaper_nonneg tPaper_le_one E.toDC.M E.toDC.nonneg E.toDC.bound c i) a) a'
  have key := recordForm_of hR' h3' h19' (hne.F2 i) tPaper_nonneg tPaper_le_one
    (fun c => E.toDC.M i c) (fun c => E.toDC.nonneg i c) (fun c => E.toDC.bound i c)
    (E.hη i) (E.hη1 i) (fun c => (E.E i c).z) (Mb := Mc (E.η i) (E.e i)) (fun _ => le_refl _) hN
  refine recordForm_mono key ?_
  -- the constants
  rw [ZMod.card, Sarkozy.SignedEstimates.Hcard_eq hR', ZMod.card]
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hη1' : 10 / (p : ℝ) < 1 := by rw [div_lt_one hp0]; linarith
  have he1' : Sarkozy.SignedEstimates.e0 (p : ℝ) < 1 :=
    Sarkozy.SignedEstimates.e0_lt_one (by linarith)
  have he0' : 0 ≤ Sarkozy.SignedEstimates.e0 (p : ℝ) :=
    Sarkozy.SignedEstimates.e0_nonneg (by linarith)
  have hM := Mc_mono (E.hη i) hη hη1' (E.he i) he he1'
  have hMc0 : 0 ≤ Mc (E.η i) (E.e i) := Mc_nonneg (E.hη i) (E.hη1 i) (E.he i) (E.he1 i)
  have hd := deltaC_mono2 (E.hη i) hη hη1' hMc0 hM
  have hH : 0 < Hp p := by
    unfold Hp
    have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have : (0 : ℝ) < (p : ℝ) - 2 := by linarith
    positivity
  have hX1 : 0 ≤ X1C (p : ℝ) (Sarkozy.SignedEstimates.e0 (p : ℝ)) (Hp p) := by
    unfold X1C; have : 0 < 1 - Sarkozy.SignedEstimates.e0 (p : ℝ) := by linarith
    positivity
  have hX2 : 0 ≤ X2C (p : ℝ) (Sarkozy.SignedEstimates.e0 (p : ℝ)) (Hp p) := by
    unfold X2C; have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  unfold κRec Mbar
  have ht : 0 ≤ 1 + tPaper := by linarith [tPaper_nonneg]
  have hHp : (p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2) / 2 = Hp p := rfl
  rw [hHp]
  have h1 := mul_le_mul_of_nonneg_right hd hX1
  have h2 : 4 * Mc (E.η i) (E.e i) * X2C (p : ℝ) (Sarkozy.SignedEstimates.e0 (p : ℝ)) (Hp p) ≤
      4 * Mc (10 / (p : ℝ)) (Sarkozy.SignedEstimates.e0 (p : ℝ)) *
        X2C (p : ℝ) (Sarkozy.SignedEstimates.e0 (p : ℝ)) (Hp p) :=
    mul_le_mul_of_nonneg_right (by linarith) hX2
  have h12 := add_le_add h1 h2
  have h3'' := mul_le_mul_of_nonneg_left h12 ht
  exact mul_le_mul_of_nonneg_right h3'' hp0.le

variable (hW : Target.Weil)

/-- **The estimates of a class-three block are the paper's** (`η_p ≤ 10/p`, `e_p ≤ e₀(p)`), by
specification. `True` on an upper block. -/
def SpecEst {b : Blk} : (S : PaperBlockSpec bOf b) → SignedSpec hW S → Prop
  | .upper _, _ => True
  | .middleUniform _, E => ∀ i, E.down.η i ≤ 10 / (blockPrimes bOf b i : ℝ) ∧
      E.down.e i ≤ Sarkozy.SignedEstimates.e0 (blockPrimes bOf b i : ℝ)
  | .middleIndividual _, E => ∀ i, E.down.η i ≤ 10 / (blockPrimes bOf b i : ℝ) ∧
      E.down.e i ≤ Sarkozy.SignedEstimates.e0 (blockPrimes bOf b i : ℝ)
  | .middleCoherent _, E => ∀ i, E.down.η i ≤ 10 / (blockPrimes bOf b i : ℝ) ∧
      E.down.e i ≤ Sarkozy.SignedEstimates.e0 (blockPrimes bOf b i : ℝ)

/-- **E1's estimates are the paper's**: `paperMiddleEstimates` has `η_p = 10/p`, `e_p = e₀(p)`. -/
theorem paperMiddleEstimates_est (b : Blk) (hne : MiddleNonempty (blockPrimes bOf b)) (i) :
    (Sarkozy.MainFinalF1.paperMiddleEstimates hW b hne).η i ≤
        10 / (blockPrimes bOf b i : ℝ) ∧
      (Sarkozy.MainFinalF1.paperMiddleEstimates hW b hne).e i ≤
        Sarkozy.SignedEstimates.e0 (blockPrimes bOf b i : ℝ) :=
  ⟨le_refl _, le_refl _⟩

theorem specK_of_est {b : Blk} :
    (S : PaperBlockSpec bOf b) → (E : SignedSpec hW S) → SpecEst hW S E → SpecK hW κRec S E
  | .upper _, _, _ => trivial
  | .middleUniform M, E, H => fun i => recordForm_block M.hne E.down i (H i).1 (H i).2
  | .middleIndividual M, E, H => fun i => recordForm_block M.hne E.down i (H i).1 (H i).2
  | .middleCoherent M, E, H => fun i => recordForm_block M.hne E.down i (H i).1 (H i).2

theorem κRec_nonneg (p : ℕ) (hp : 19 ≤ p) : 0 ≤ κRec p := by
  have h19r : (19 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hη0 : 0 ≤ 10 / (p : ℝ) := by positivity
  have hη1 : 10 / (p : ℝ) < 1 := by rw [div_lt_one hp0]; linarith
  have he1 : Sarkozy.SignedEstimates.e0 (p : ℝ) < 1 :=
    Sarkozy.SignedEstimates.e0_lt_one (by linarith)
  have he0 : 0 ≤ Sarkozy.SignedEstimates.e0 (p : ℝ) :=
    Sarkozy.SignedEstimates.e0_nonneg (by linarith)
  have hM : 0 ≤ Mbar p := Mc_nonneg hη0 hη1 he0 he1
  have hd : 0 ≤ deltaC (10 / (p : ℝ)) (Mbar p) := by
    unfold deltaC; have : 0 < 1 - 10 / (p : ℝ) := by linarith
    positivity
  have hH : 0 < Hp p := by
    unfold Hp
    have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have : (0 : ℝ) < (p : ℝ) - 2 := by linarith
    positivity
  have hX1 : 0 ≤ X1C (p : ℝ) (Sarkozy.SignedEstimates.e0 (p : ℝ)) (Hp p) := by
    unfold X1C; have : 0 < 1 - Sarkozy.SignedEstimates.e0 (p : ℝ) := by linarith
    positivity
  have hX2 : 0 ≤ X2C (p : ℝ) (Sarkozy.SignedEstimates.e0 (p : ℝ)) (Hp p) := by
    unfold X2C; have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  have ht : 0 ≤ 1 + tPaper := by linarith [tPaper_nonneg]
  unfold κRec
  positivity

variable {hW} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {A : PaperAnalyticInputs f1Cell}

/-- **The estimates of `C` are the paper's** (*hypothesis*, 1 field, not analytic): at every
middle block of the F1 data, the middle estimates inside `C` have `η_p ≤ 10/p` and
`e_p ≤ e₀(p)`. True with equality for E1's `paperMiddleEstimates`
(`paperMiddleEstimates_est`). -/
structure EstInputs (C : ComparisonPartsTC hW hMR hFour A) : Prop where
  est : ∀ b i, blockSite b = .inl i → SpecEst hW (specF hW A b) (C.blk b)

/-- `EstInputs` gives (K) at `κRec`. -/
theorem EstInputs.toRecordInputs {C : ComparisonPartsTC hW hMR hFour A} (H : EstInputs C) :
    RecordInputs κRec C where
  κ_nonneg := κRec_nonneg
  form b i hb := specK_of_est hW (specF hW A b) (C.blk b) (H.est b i hb)

/-- **A constructor of PG's `SignedDecompInputsC` with `prop:signed-bounds`(c) proved at
`e_sg′ = esgCrude κRec nT`**: from the paper's estimates (`EstInputs`) and the gates
`PieceGate (esgCrude κRec nT) 38 k`. `c_col = 73` (`collisionBound_73`) and `c_+ = 38`
(`comp38_paper`) are proved. -/
theorem EstInputs.toSD {C : ComparisonPartsTC hW hMR hFour A} (H : EstInputs C)
    (G : ∀ k, PieceGate (esgCrude κRec nT) 38 k) : SignedDecompInputsC C :=
  H.toRecordInputs.toSD G

/-! ## The estimates of every `ComparisonPartsTC` are the paper's -/

variable (hW) in
/-- On a middle block, `UpperSpec.toSigned` is E1's `paperMiddleEstimates`; so `SpecEst` holds. -/
theorem specEst_toSigned {b : Blk} :
    (S : PaperBlockSpec bOf b) → (U : Sarkozy.MainFinalF1.UpperSpec hW S) →
      SpecEst hW S (Sarkozy.MainFinalF1.UpperSpec.toSigned hW S U)
  | .upper _, _ => trivial
  | .middleUniform M, _ => fun i => paperMiddleEstimates_est hW b M.hne i
  | .middleIndividual M, _ => fun i => paperMiddleEstimates_est hW b M.hne i
  | .middleCoherent M, _ => fun i => paperMiddleEstimates_est hW b M.hne i

/-- **`EstInputs` holds for every `ComparisonPartsTC`** (its middle blocks carry E1's
`paperMiddleEstimates`, `ComparisonPartsTC.blk`). -/
theorem estInputs (C : ComparisonPartsTC hW hMR hFour A) : EstInputs C :=
  ⟨fun b _ _ => specEst_toSigned hW (specF hW A b) (C.blkU b)⟩

/-- **PG's `SD` from the gates alone**: for every `C`, `prop:signed-bounds`(c) for the signed
record (at `e_sg′ = esgCrude κRec nT`), `lem:record:conditional-collision`(d) (at `c_col = 73`)
and the component norms (at `c_+ = 38`) are proved at every prime of every middle block; the only
hypothesis is the numerical gate `PieceGate (esgCrude κRec nT) 38 k` at the 33 pieces. -/
theorem signedDecompInputs_of_gates (C : ComparisonPartsTC hW hMR hFour A)
    (G : ∀ k, PieceGate (esgCrude κRec nT) 38 k) : SignedDecompInputsC C :=
  (estInputs C).toSD G

end Sarkozy.SignedDecompCrude
