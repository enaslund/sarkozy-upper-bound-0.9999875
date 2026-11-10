module

public import Sarkozy.BracketEnergy.SlotCount
public import Sarkozy.BracketEnergy.DensityMean
public import Sarkozy.BracketEnergy.EnvFirst

@[expose] public section

/-!
# The main price of the revealed-input chain at the envelope energies

The chain bound of `EnvFirst` carries the main price of `def:record:structured-energy`,
`Π_main = ∏_v ξ_v^{a/72} ∏_v (ᾱ_v/α)^{θ/72}` (all slots changed). For the slot data of `envC`
this file evaluates it:

* `prod_slotDatum`: a product over the slots of a function of the datum is
  `H(F_A)^{72 − 2|E|} ∏_e H(datum_e)^2`;
* `mainPrice_slotDatum`: `Π_main` in these terms;
* **`envMainPrice_eq`**: for the data of `envC`, with `D_{𝒥_e}` coprime to `D_E`,
  `Π_main = sq(D_E)^a · Π_𝒥 · ∏_e (ᾱ_e/α)^{2θ/72}`, where `Π_𝒥 = ∏_e (K sq(D_{𝒥_e}))^{2a/72}` is
  the conductor price of `lem:hyb:moment` (`conductorPrice`) and `ᾱ_e` the local density of the
  revealed input (`queryLocalDensity`).

With `env_localDensity_mean_le` (`E_ω ∏_e (ᾱ_e/α)^{2θ/72} ≤ 1`) this is the paper's
`Π_Z = C_Z ∏_e (K sq(D_{𝒥_e}))^{2a/d}` of `lem:envelope-energy` after the average over the
residues: the per-index chain bound exceeds `sq(D_E)^a Π_𝒥 Y` only by a factor of mean at most one.
-/

open Finset Function
open scoped BigOperators

namespace Sarkozy.BracketEnergy

open Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper Sarkozy.Structured Sarkozy.Functional
  Sarkozy.FourierArithmetic Sarkozy.PaperFrame Sarkozy.BlockFrame Sarkozy.IndexSupport
  Sarkozy.TheoremC

section Generic

variable {E : Type} [Fintype E] [DecidableEq E]

/-- The datum of a slot as a function of its query. -/
def optDatum (qdat : E → SlotDatum) (fdat : SlotDatum) : Option E → SlotDatum
  | some e => qdat e
  | none => fdat

omit [DecidableEq E] in
theorem slotDatum_eq_optDatum (u : E → reservedCut.Half) (qdat : E → SlotDatum)
    (fdat : SlotDatum) (v : Slot) :
    slotDatum u qdat fdat v = optDatum qdat fdat (slotQuery u v) := by
  unfold slotDatum
  rcases slotQuery u v with _ | e <;> rfl

/-- **A product over the slots of a function of the datum.** -/
theorem prod_slotDatum {M : Type*} [CommMonoid M] (u : E → reservedCut.Half) (hu : Injective u)
    (qdat : E → SlotDatum) (fdat : SlotDatum) (H : SlotDatum → M) :
    ∏ v : Slot, H (slotDatum u qdat fdat v) =
      H fdat ^ (72 - 2 * Fintype.card E) * ∏ e, H (qdat e) ^ 2 := by
  simp_rw [slotDatum_eq_optDatum]
  exact prod_slotQuery u hu (fun o => H (optDatum qdat fdat o))

variable {J : Type} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)]

/-- The slot price `ξ = (N/M) sq(D₀ D_E)` of a datum. -/
noncomputable def datumPrice (Es : Finset J) (L : ℕ) (d : SlotDatum) : ℝ :=
  ((blockScale * L : ℕ) : ℝ) / d.2.2.1 * (stepR m Es d.1 : ℕ)

/-- The mean density `ᾱ = (D₀/M) #(A ∩ I ∩ {x ≡ s (mod D₀)})` of a datum. -/
noncomputable def datumDensity (A : Finset ℤ) (d : SlotDatum) : ℝ :=
  (d.1 : ℝ) / d.2.2.1 *
    (((A ∩ Icc (d.2.2.2 + 1) (d.2.2.2 + d.2.2.1)).filter
      fun x : ℤ => (x : ZMod d.1) = d.2.1).card : ℝ)

omit [Fintype J] [DecidableEq J] [∀ j, NeZero (m j)] in
/-- **The main price with structured slot data**, all slots changed. -/
theorem mainPrice_slotDatum (u : E → reservedCut.Half) (hu : Injective u) (qdat : E → SlotDatum)
    (fdat : SlotDatum) (Es : Finset J) (L : ℕ) (A : Finset ℤ) (a θ α : ℝ) :
    mainPrice (paperPrice m Es (fun v => (slotDatum u qdat fdat v).1)
        (fun v => (slotDatum u qdat fdat v).2.2.1) L)
      (paperMeanDensity (FiniteLaw.uniform Unit) A (fun v => (slotDatum u qdat fdat v).1)
        (fun v => (slotDatum u qdat fdat v).2.2.1) (fun _ v => (slotDatum u qdat fdat v).2.2.2)
        (fun _ v => (slotDatum u qdat fdat v).2.1)) (fun _ => True) a θ α =
      (((datumPrice m Es L fdat) ^ (a / 72)) ^ (72 - 2 * Fintype.card E) *
          ∏ e, ((datumPrice m Es L (qdat e)) ^ (a / 72)) ^ 2) *
        (((datumDensity A fdat / α) ^ (θ / 72)) ^ (72 - 2 * Fintype.card E) *
          ∏ e, ((datumDensity A (qdat e) / α) ^ (θ / 72)) ^ 2) := by
  unfold mainPrice
  have hd : ∀ v, paperMeanDensity (FiniteLaw.uniform Unit) A
      (fun v => (slotDatum u qdat fdat v).1) (fun v => (slotDatum u qdat fdat v).2.2.1)
      (fun _ v => (slotDatum u qdat fdat v).2.2.2) (fun _ v => (slotDatum u qdat fdat v).2.1) v =
      datumDensity A (slotDatum u qdat fdat v) := by
    intro v
    unfold paperMeanDensity datumDensity
    rw [FiniteLaw.expect_const]
  have hp : ∀ v, paperPrice m Es (fun v => (slotDatum u qdat fdat v).1)
      (fun v => (slotDatum u qdat fdat v).2.2.1) L v =
        datumPrice m Es L (slotDatum u qdat fdat v) :=
    fun v => rfl
  have hfil : (univ.filter fun _ : Slot => True) = univ := filter_true_of_mem fun _ _ => trivial
  rw [hfil]
  simp_rw [hd, hp]
  rw [prod_slotDatum u hu qdat fdat (fun d => (datumPrice m Es L d) ^ (a / 72)),
    prod_slotDatum u hu qdat fdat (fun d => (datumDensity A d / α) ^ (θ / 72))]

end Generic

section Env

variable {E : Type} [Fintype E] [DecidableEq E]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))
  {J : Type} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)]

omit [DecidableEq P] [Fintype J] [DecidableEq J] [∀ j, NeZero (m j)] in
/-- **The main price of the revealed-input chain at the data of `envC`**: with `D_{𝒥_e}` coprime
to `D_E` and `A ⊆ [1, N]` of positive density,
`Π_main = sq(D_E)^a · Π_𝒥 · ∏_e (ᾱ_e/α)^{2θ/72}`, `Π_𝒥 = ∏_e (K sq(D_{𝒥_e}))^{2a/72}`. -/
theorem envMainPrice_eq {L : ℕ} (hL : 1 ≤ L) (u : E → reservedCut.Half) (hu : Injective u)
    (Es : Finset J) (A : Finset ℤ) (hA : A ⊆ Icc 1 ((blockScale * L : ℕ) : ℤ))
    (hα : 0 < density (blockScale * L) A) (a θ : ℝ)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j)
    (hcopJ : ∀ e, (revealedModulus blockScale pr h (Jq e)).Coprime (∏ j ∈ Es, m j)) :
    mainPrice (paperPrice m Es (fun v => (envSlots hcop u L Jq ω v).1)
        (fun v => (envSlots hcop u L Jq ω v).2.2.1) L)
      (paperMeanDensity (FiniteLaw.uniform Unit) A (fun v => (envSlots hcop u L Jq ω v).1)
        (fun v => (envSlots hcop u L Jq ω v).2.2.1)
        (fun _ v => (envSlots hcop u L Jq ω v).2.2.2)
        (fun _ v => (envSlots hcop u L Jq ω v).2.1)) (fun _ => True) a θ
        (density (blockScale * L) A) =
      ((stepR m Es 1 : ℕ) : ℝ) ^ a * conductorPrice pr h (2 * a / 72) Jq *
        ∏ e, (queryLocalDensity hcop L A (Jq e) (ω e) / density (blockScale * L) A) ^
          (2 * θ / 72) := by
  have hmp := mainPrice_slotDatum m u hu (fun e => envDatum hcop L Jq e (ω e)) (wholeDatum L) Es
    L A a θ (density (blockScale * L) A)
  unfold envSlots
  rw [hmp]
  set α := density (blockScale * L) A
  set x : ℝ := ((leastSquare (∏ j ∈ Es, m j) : ℕ) : ℝ)
  have hx : 0 < x := Nat.cast_pos.mpr (leastSquare_pos _)
  have hK : (0 : ℝ) < blockScale := by norm_num [blockScale]
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
  have hN : ((blockScale * L : ℕ) : ℝ) ≠ 0 := by
    have : 0 < blockScale * L := Nat.mul_pos (by norm_num [blockScale]) (by omega)
    exact_mod_cast this.ne'
  have hk : 2 * Fintype.card E ≤ 72 := by
    have := card_slotQuery_none u hu
    omega
  -- the outside slots
  have hw1 : datumPrice m Es L (wholeDatum L) = x := by
    unfold datumPrice wholeDatum stepR
    simp only [one_mul]
    rw [div_self hN, one_mul]
  have hw2 : datumDensity A (wholeDatum L) = α := by
    unfold datumDensity wholeDatum
    have hfilter : ((A ∩ Icc (0 + 1) (0 + ((blockScale * L : ℕ) : ℤ))).filter
        fun x : ℤ => (x : ZMod 1) = 0) = A := by
      rw [filter_true_of_mem (fun x _ => Subsingleton.elim _ _), zero_add, zero_add]
      exact inter_eq_left.mpr hA
    simp only at hfilter ⊢
    rw [hfilter]
    unfold α density
    push_cast
    ring
  -- the query slots
  have hq1 : ∀ e, datumPrice m Es L (envDatum hcop L Jq e (ω e)) =
      (blockScale * (leastSquare (revealedModulus blockScale pr h (Jq e)) : ℝ)) * x := by
    intro e
    unfold datumPrice envDatum stepR
    simp only
    rw [leastSquare_mul (hcopJ e)]
    push_cast
    field_simp
    ring
  have hq2 : ∀ e, datumDensity A (envDatum hcop L Jq e (ω e)) =
      queryLocalDensity hcop L A (Jq e) (ω e) := by
    intro e
    unfold datumDensity envDatum queryLocalDensity localDensity
    simp only
    rw [blockInterval_eq_Icc]
  simp only [hw1, hw2, hq1, hq2, div_self hα.ne', Real.one_rpow, one_pow]
  -- exponent algebra
  have hpow : ∀ (y : ℝ) (hy : 0 ≤ y) (c : ℝ) (n : ℕ), (y ^ c) ^ n = y ^ (c * n) := by
    intro y hy c n
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy]
  have hquery : ∀ e, ((blockScale * (leastSquare (revealedModulus blockScale pr h (Jq e)) : ℝ) *
      x) ^ (a / 72)) ^ 2 =
      queryPrice pr h (2 * a / 72) (Jq e) * x ^ (2 * a / 72) := by
    intro e
    have hy : 0 ≤ (blockScale : ℝ) * (leastSquare (revealedModulus blockScale pr h (Jq e)) : ℝ) :=
      mul_nonneg hK.le (Nat.cast_nonneg _)
    rw [hpow _ (mul_nonneg hy hx.le), Real.mul_rpow hy hx.le]
    unfold queryPrice queryConductor
    congr 2 <;> push_cast <;> ring
  have hdens : ∀ e, ((queryLocalDensity hcop L A (Jq e) (ω e) / α) ^ (θ / 72)) ^ 2 =
      (queryLocalDensity hcop L A (Jq e) (ω e) / α) ^ (2 * θ / 72) := by
    intro e
    rw [hpow (queryLocalDensity hcop L A (Jq e) (ω e) / α)
      (div_nonneg (localDensity_nonneg _ _ _ _ _ _) hα.le)]
    congr 1
    push_cast
    ring
  simp only [hquery, hdens, prod_mul_distrib, prod_const, card_univ]
  unfold conductorPrice
  rw [hpow _ hx.le, hpow _ hx.le]
  have hxx : x ^ (2 * a / 72 * (Fintype.card E : ℝ)) *
      x ^ (a / 72 * ((72 - 2 * Fintype.card E : ℕ) : ℝ)) = x ^ a := by
    rw [← Real.rpow_add hx]
    congr 1
    rw [Nat.cast_sub hk]
    push_cast
    ring
  have hst : ((stepR m Es 1 : ℕ) : ℝ) = x := by
    unfold x stepR
    rw [one_mul]
  rw [hst, ← hxx]
  ring

end Env

end Sarkozy.BracketEnergy
