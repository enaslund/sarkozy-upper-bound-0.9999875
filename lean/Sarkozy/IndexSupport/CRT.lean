module

public import Sarkozy.IndexSupport.CoupledIndex
public import Sarkozy.IndexSupport.Reindex
public import Sarkozy.IndexSupport.GeneralIndex
public import Sarkozy.IndexSupport.HalfFunctions
public import Mathlib.Data.ZMod.QuotientRing

/-!
# The unsplit coupled index `ℤ/Kℤ × ℤ/M_0ℤ`

`def:hyb:coupled`(a): the index of one query is `Ω_e = ℤ/Kℤ × ℤ/M_0ℤ`,
`M_0 = ∏_p p^{h_p}`, and by the Chinese remainder theorem it is the product of the
interval coordinate and the prime-power residues. This file transports the
exact-conductor sectors, the depth revelations and the sector bounds of
`Sarkozy/IndexSupport/CoupledIndex.lean` along the CRT relabelling
`crtEquiv : ℤ/Kℤ × ℤ/M_0ℤ ≃ ∏_j Ω_j` (built from `ZMod.prodEquivPi`; the moduli `p^{h_p}`
are only assumed pairwise coprime).

* `unsplitTransition μ`: the transition `T_e f(b, s) = E_r f(b + 1, s + r)` of
  `def:hyb:coupled`(c), where the increment `r ∈ ℤ/M_0ℤ` combines independent
  `r_p ∼ μ_p` by the CRT; `unsplitTransition_eq` identifies it with the transported tensor
  product of the coordinate transitions.
* `unsplit_sectorOperator`: `cor:index-support-frame`(i) on the unsplit index:
  `𝒯 = ⊗_e (2P_e - T_e)` and `𝒯ᵀ` preserve the (transported) exact-conductor sectors, are
  the identity on the constants, and have norm at most `δ_S` there.
* `unsplit_bounds`, `unsplit_cut_mean_step`: `cor:index-support-frame`(iii) and
  `eq:cp:mean-step` on the unsplit index.
* `unsplitRevelation_reveal_mod`: the transported revealed projection at the depth vector
  `𝒥` is the conditional expectation given `b` (when revealed) and `s mod D_𝒥`,
  `D_𝒥 = ∏_p p^{𝒥_p}`.
-/

@[expose] public section

open Finset Function
open scoped BigOperators Matrix

namespace Sarkozy.IndexSupport

section CRT

variable (Kint : ℕ) [NeZero Kint] {P : Type*} [Fintype P] [DecidableEq P] (pr h : P → ℕ)
  [∀ p, NeZero (pr p ^ h p)]

/-- The paper's modulus `M_0 = ∏_p p^{h_p}`. -/
abbrev modulus : ℕ := ∏ p, pr p ^ h p

instance modulus_neZero : NeZero (modulus pr h) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun _ _ => NeZero.ne _)⟩

variable (hcop : Pairwise (Nat.Coprime on fun p => pr p ^ h p))

/-- The CRT residues of `s ∈ ℤ/M_0ℤ`. -/
noncomputable def crtResidues (s : ZMod (modulus pr h)) : ∀ p, ZMod (pr p ^ h p) :=
  ZMod.prodEquivPi (fun p => pr p ^ h p) hcop s

/-- The CRT relabelling of one query index: `(b, s) ↦ (b, (s mod p^{h_p})_p)`. -/
noncomputable def crtEquiv : (ZMod Kint × ZMod (modulus pr h)) ≃ (∀ j, CoordSpace Kint pr h j) where
  toFun x j := match j with
    | none => x.1
    | some p => crtResidues pr h hcop x.2 p
  invFun y := (y none, (ZMod.prodEquivPi (fun p => pr p ^ h p) hcop).symm (fun p => y (some p)))
  left_inv x := by
    ext
    · rfl
    · change (ZMod.prodEquivPi (fun p => pr p ^ h p) hcop).symm
        (ZMod.prodEquivPi (fun p => pr p ^ h p) hcop x.2) = x.2
      exact RingEquiv.symm_apply_apply _ _
  right_inv y := by
    funext j
    match j with
    | none => rfl
    | some p =>
      change ZMod.prodEquivPi (fun p => pr p ^ h p) hcop
        ((ZMod.prodEquivPi (fun p => pr p ^ h p) hcop).symm (fun p => y (some p))) p = y (some p)
      rw [RingEquiv.apply_symm_apply]

/-- The transition of `def:hyb:coupled`(c) on the unsplit index:
`T((b, s), (b', s')) = [b' = b + 1] · ∏_p μ_p((s' - s) mod p^{h_p})`, i.e. the interval shift
tensored with the convolution by the CRT combination of independent increments `r_p ∼ μ_p`. -/
noncomputable def unsplitTransition (μ : ∀ p, ZMod (pr p ^ h p) → ℝ) :
    Matrix (ZMod Kint × ZMod (modulus pr h)) (ZMod Kint × ZMod (modulus pr h)) ℝ :=
  fun x y => (if y.1 = x.1 + 1 then 1 else 0) * ∏ p, μ p (crtResidues pr h hcop (y.2 - x.2) p)

omit [NeZero Kint] [DecidableEq P] [∀ p, NeZero (pr p ^ h p)] in
/-- The unsplit transition is the CRT-transport of `⊗_j T_j` (shift ⊗ coordinate
convolutions). -/
theorem unsplitTransition_eq (μ : ∀ p, ZMod (pr p ^ h p) → ℝ) :
    (piKron (coordTransition Kint pr h μ)).submatrix (crtEquiv Kint pr h hcop)
      (crtEquiv Kint pr h hcop) = unsplitTransition Kint pr h hcop μ := by
  ext x y
  simp only [Matrix.submatrix_apply, piKron_apply, Fintype.prod_option]
  unfold unsplitTransition
  congr 1
  · change convMatrix (fun r : ZMod Kint => if r = 1 then (1 : ℝ) else 0) x.1 y.1 = _
    simp only [convMatrix]
    by_cases hb : y.1 = x.1 + 1
    · rw [ite_eq_left (by rw [hb]; ring), ite_eq_left hb]
    · rw [ite_eq_right (fun h' => hb (by rw [← h']; ring)), ite_eq_right hb]
  · apply prod_congr rfl
    intro p _
    change convMatrix (μ p) (crtResidues pr h hcop x.2 p) (crtResidues pr h hcop y.2 p) = _
    simp only [convMatrix, crtResidues, map_sub, Pi.sub_apply]

end CRT

section Queries

variable (Kint : ℕ) [NeZero Kint] {P : Type*} [Fintype P] [DecidableEq P] (pr h : P → ℕ)
  [∀ p, NeZero (pr p ^ h p)] (hcop : Pairwise (Nat.Coprime on fun p => pr p ^ h p))
  {E : Type*} [Fintype E] [DecidableEq E]

/-- The exact-conductor sectors of one unsplit query index (transported from the product
coordinates). -/
noncomputable def unsplitSectors :
    SectorSystem (ZMod Kint × ZMod (modulus pr h)) (∀ j, Fin ((coordChain Kint pr h j).depth + 1)) :=
  (productSectors (coordChain Kint pr h)).reindex (crtEquiv Kint pr h hcop)

/-- **`cor:index-support-frame`(i) on the unsplit index `ℤ/Kℤ × ℤ/M_0ℤ`.** -/
theorem unsplit_sectorOperator (μ : E → ∀ p, ZMod (pr p ^ h p) → ℝ)
    (hμ : ∀ e p r, 0 ≤ μ e p r) (hμ1 : ∀ e p, ∑ r, μ e p r = 1)
    (t : E → ∀ p, Tails (Chain.residues (pr p) (h p)).depth)
    (hnorm : ∀ e p (l : Fin ((Chain.residues (pr p) (h p)).depth + 1)) f,
      (Chain.residues (pr p) (h p)).diff l *ᵥ f = f →
      (convMatrix (μ e p) *ᵥ f) ⬝ᵥ (convMatrix (μ e p) *ᵥ f) ≤ (t e p).tail l ^ 2 * (f ⬝ᵥ f)) :
    SectorOperator (SectorSystem.pi (fun _ : E => unsplitSectors Kint pr h hcop))
        (signedOp (fun e => unsplitTransition Kint pr h hcop (μ e)))
        (fun s => ∏ e, sectorWeight (coordChain Kint pr h) (coordTails Kint pr h (t e)) (s e)) ∧
      SectorOperator (SectorSystem.pi (fun _ : E => unsplitSectors Kint pr h hcop))
        (signedOp (fun e => unsplitTransition Kint pr h hcop (μ e)))ᵀ
        (fun s => ∏ e, sectorWeight (coordChain Kint pr h) (coordTails Kint pr h (t e)) (s e)) := by
  have hT (e : E) : SectorOperator (unsplitSectors Kint pr h hcop)
      (unsplitTransition Kint pr h hcop (μ e))
      (sectorWeight (coordChain Kint pr h) (coordTails Kint pr h (t e))) := by
    have h1 := SectorOperator.chain (coordChain Kint pr h) (coordTails Kint pr h (t e))
      (fun j => (coordTransition_hypotheses Kint pr h (μ e) (hμ e) (hμ1 e) (t e) (hnorm e) j).1)
      (fun j => (coordTransition_hypotheses Kint pr h (μ e) (hμ e) (hμ1 e) (t e) (hnorm e) j).2)
    have h2 := h1.reindex (crtEquiv Kint pr h hcop)
    rwa [unsplitTransition_eq] at h2
  exact signedOp_sectorOperator (fun _ => unsplitSectors Kint pr h hcop) hT
    (fun e => sectorWeight_zero (coordChain Kint pr h) (coordTails Kint pr h (t e)))

/-- The depth revelation of one unsplit query index (transported). -/
noncomputable def unsplitRevelation (t : ∀ p, Tails (Chain.residues (pr p) (h p)).depth) :
    Revelation (unsplitSectors Kint pr h hcop) (∀ j, Fin ((coordChain Kint pr h j).depth + 1)) :=
  (depthRevelation (coordChain Kint pr h) (coordTails Kint pr h t)).reindex
    (crtEquiv Kint pr h hcop)

/-- **`cor:index-support-frame`(iii) on the unsplit index**, matrix form, with independent
depths across queries (`Revelation.pi` of the transported depth revelations). -/
theorem unsplit_bounds (μ : E → ∀ p, ZMod (pr p ^ h p) → ℝ)
    (hμ : ∀ e p r, 0 ≤ μ e p r) (hμ1 : ∀ e p, ∑ r, μ e p r = 1)
    (t : E → ∀ p, Tails (Chain.residues (pr p) (h p)).depth)
    (hnorm : ∀ e p (l : Fin ((Chain.residues (pr p) (h p)).depth + 1)) f,
      (Chain.residues (pr p) (h p)).diff l *ᵥ f = f →
      (convMatrix (μ e p) *ᵥ f) ⬝ᵥ (convMatrix (μ e p) *ᵥ f) ≤ (t e p).tail l ^ 2 * (f ⬝ᵥ f))
    {ι : Type*} [Fintype ι] {ML Γ MR : Matrix ι ι ℝ}
    (hG : (Matrix.fromBlocks ML Γ Γᵀ MR).PosSemidef)
    (X Y : (E → ZMod Kint × ZMod (modulus pr h)) → ι → ℝ) (Xbar : ι → ℝ)
    (hX : vmean X = Xbar) (hY : vmean Y = Xbar) :
    let V := Revelation.pi (fun e => unsplitRevelation Kint pr h hcop (t e))
    let 𝒯 := signedOp (fun e => unsplitTransition Kint pr h hcop (μ e))
    Xbar ⬝ᵥ (ML *ᵥ Xbar) ≤ V.energy ML X ∧ 0 ≤ Xbar ⬝ᵥ (ML *ᵥ Xbar) ∧
    Xbar ⬝ᵥ (MR *ᵥ Xbar) ≤ V.energy MR Y ∧ 0 ≤ Xbar ⬝ᵥ (MR *ᵥ Xbar) ∧
    |pairing Γ X (act 𝒯 Y) - Xbar ⬝ᵥ (Γ *ᵥ Xbar)| ≤
      (1 / 2) * ((V.energy ML X - Xbar ⬝ᵥ (ML *ᵥ Xbar)) +
        (V.energy MR Y - Xbar ⬝ᵥ (MR *ᵥ Xbar))) ∧
    |pairing Γ X (act 𝒯 Y)| ≤ Real.sqrt (V.energy ML X) * Real.sqrt (V.energy MR Y) := by
  intro V 𝒯
  have hT (e : E) : SectorOperator (unsplitSectors Kint pr h hcop)
      (unsplitTransition Kint pr h hcop (μ e))
      (sectorWeight (coordChain Kint pr h) (coordTails Kint pr h (t e))) := by
    have h1 := SectorOperator.chain (coordChain Kint pr h) (coordTails Kint pr h (t e))
      (fun j => (coordTransition_hypotheses Kint pr h (μ e) (hμ e) (hμ1 e) (t e) (hnorm e) j).1)
      (fun j => (coordTransition_hypotheses Kint pr h (μ e) (hμ e) (hμ1 e) (t e) (hnorm e) j).2)
    have h2 := h1.reindex (crtEquiv Kint pr h hcop)
    rwa [unsplitTransition_eq] at h2
  exact signedOp_bounds (fun _ => unsplitSectors Kint pr h hcop)
    (fun e => unsplitRevelation Kint pr h hcop (t e)) hT
    (fun e => sectorWeight_zero (coordChain Kint pr h) (coordTails Kint pr h (t e)))
    (fun e s => by
      rw [← depthRevelation_prob]
      exact Revelation.prob_nonneg _ s)
    (fun e s => (depthRevelation_prob (coordChain Kint pr h) (coordTails Kint pr h (t e)) s).symm.le)
    hG X Y Xbar hX hY

end Queries

section Conditional

/-- Conditional expectations transport along relabellings: `E_π ∘ σ = E_{π ∘ σ}`. -/
theorem condExpMatrix_submatrix {Ω Ω' γ : Type*} [Fintype Ω] [Fintype Ω'] [DecidableEq γ]
    (π : Ω → γ) (σ : Ω' ≃ Ω) :
    (condExpMatrix π).submatrix σ σ = condExpMatrix (π ∘ σ) := by
  ext x y
  have hfib : (fibre (π ∘ σ) x).card = (fibre π (σ x)).card := by
    apply Finset.card_bij (fun z _ => σ z)
    · intro z hz
      simpa [fibre] using hz
    · intro a _ b _ hab
      exact σ.injective hab
    · intro z hz
      refine ⟨σ.symm z, ?_, by simp⟩
      simpa [fibre] using hz
  simp only [Matrix.submatrix_apply, condExpMatrix, Function.comp_apply, hfib]

variable (Kint : ℕ) [NeZero Kint] {P : Type*} [Fintype P] [DecidableEq P] (pr h : P → ℕ)
  [∀ p, NeZero (pr p ^ h p)]

/-- Common natural-number labels for the coordinate chains: the interval coordinate is
unlabelled at depth `0` and fully labelled at depth `1`; a residue is labelled by its residue
modulo `p^l`. -/
def coordLabel : ∀ j, ℕ → CoordSpace Kint pr h j → ℕ
  | none => fun l b => if l = 0 then 0 else (b : ZMod Kint).val + 1
  | some p => fun l s => residueLabel (pr p) (h p) l s

omit [Fintype P] [DecidableEq P] in
theorem coordChain_cond_eq (j : Option P) {l : ℕ} (hl : l ≤ (coordChain Kint pr h j).depth) :
    (coordChain Kint pr h j).cond l = condExpMatrix (coordLabel Kint pr h j l) := by
  match j with
  | none =>
    change (Chain.whole (ZMod Kint)).cond l = condExpMatrix (fun b : ZMod Kint =>
      if l = 0 then 0 else b.val + 1)
    have hl1 : l ≤ 1 := hl
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hl1 with rfl | rfl
    · rw [condExpMatrix_const (fun x y => by simp)]
      rfl
    · rw [condExpMatrix_injective (fun x y hxy => ZMod.val_injective _ (by simpa using hxy))]
      rfl
  | some p => rfl

/-- In the product coordinates of the coupled index, `Z^𝒥` is the conditional expectation
given the revealed labels: the interval coordinate when revealed, and each residue modulo
`p^{𝒥_p}`. -/
theorem coupled_depthReveal_eq {ι : Type*} (J : ∀ j, Fin ((coordChain Kint pr h j).depth + 1))
    (Z : (∀ j, CoordSpace Kint pr h j) → ι → ℝ) :
    depthReveal (coordChain Kint pr h) J Z =
      act (condExpMatrix (fun ω : (∀ j, CoordSpace Kint pr h j) =>
        fun j => coordLabel Kint pr h j (J j) (ω j))) Z := by
  unfold depthReveal
  rw [← piKron_condExpMatrix (fun j => coordLabel Kint pr h j (J j))]
  congr 2
  funext j
  exact coordChain_cond_eq Kint pr h j (by omega)

variable (hcop : Pairwise (Nat.Coprime on fun p => pr p ^ h p))

omit [DecidableEq P] in
/-- The CRT residue of `s` modulo `p^l` is `s mod p^l`. -/
theorem crtResidues_val_mod (s : ZMod (modulus pr h)) (p : P) {l : ℕ} (hl : l ≤ h p) :
    (crtResidues pr h hcop s p).val % pr p ^ l = s.val % pr p ^ l := by
  rw [crtResidues, ZMod.prodEquivPi_apply, ZMod.castHom_apply, ZMod.cast_eq_val,
    ZMod.val_natCast, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow _ hl)]

/-- On the unsplit index `ℤ/Kℤ × ℤ/M_0ℤ`, the transported revealed projection at the depth
vector `𝒥` is the conditional expectation given the labels `coordLabel j (𝒥_j)` of the CRT
coordinates: `b` if the interval is revealed, and `s mod p^{𝒥_p}` for every `p`
(`crtResidues_val_mod`). -/
theorem unsplitRevelation_reveal {ι : Type*} (t : ∀ p, Tails (Chain.residues (pr p) (h p)).depth)
    (J : ∀ j, Fin ((coordChain Kint pr h j).depth + 1))
    (Z : (ZMod Kint × ZMod (modulus pr h)) → ι → ℝ) :
    (unsplitRevelation Kint pr h hcop t).reveal J Z =
      act (condExpMatrix (fun x : ZMod Kint × ZMod (modulus pr h) =>
        fun j => coordLabel Kint pr h j (J j) (crtEquiv Kint pr h hcop x j))) Z := by
  unfold Revelation.reveal
  change act (∑ s ∈ (depthRevelation (coordChain Kint pr h) (coordTails Kint pr h t)).retained J,
    ((productSectors (coordChain Kint pr h)).proj s).submatrix (crtEquiv Kint pr h hcop)
      (crtEquiv Kint pr h hcop)) Z = _
  rw [← submatrix_sum_equiv, depthRevelation_sum_proj]
  have h1 : piKron (fun j => (coordChain Kint pr h j).cond (J j)) =
      condExpMatrix (fun ω : (∀ j, CoordSpace Kint pr h j) =>
        fun j => coordLabel Kint pr h j (J j) (ω j)) := by
    rw [← piKron_condExpMatrix (fun j => coordLabel Kint pr h j (J j))]
    congr 1
    funext j
    exact coordChain_cond_eq Kint pr h j (by omega)
  rw [h1, condExpMatrix_submatrix]
  rfl

/-- Two labelings with the same fibres give the same conditional expectation. -/
theorem condExpMatrix_congr {Ω γ γ' : Type*} [Fintype Ω] [DecidableEq γ] [DecidableEq γ']
    {π : Ω → γ} {ρ : Ω → γ'} (h : ∀ x y, π x = π y ↔ ρ x = ρ y) :
    condExpMatrix π = condExpMatrix ρ := by
  ext x y
  have hfib : fibre π x = fibre ρ x := by
    ext z
    simp only [fibre, Finset.mem_filter, Finset.mem_univ, true_and, h z x]
  simp only [condExpMatrix, h x y, hfib]

/-- The Chinese remainder theorem for congruences: modulo a product of pairwise coprime
moduli, congruence is congruence modulo every factor. -/
theorem modEq_prod_iff {Q : Type*} [DecidableEq Q] (s : Finset Q) (m : Q → ℕ)
    (hcop : ∀ p ∈ s, ∀ q ∈ s, p ≠ q → Nat.Coprime (m p) (m q)) (a b : ℕ) :
    a ≡ b [MOD ∏ p ∈ s, m p] ↔ ∀ p ∈ s, a ≡ b [MOD m p] := by
  induction s using Finset.induction_on with
  | empty => simp [Nat.modEq_one]
  | @insert q s hq ih =>
    have hq' : Nat.Coprime (m q) (∏ p ∈ s, m p) := Nat.Coprime.prod_right (fun p hp =>
      hcop q (Finset.mem_insert_self _ _) p (Finset.mem_insert_of_mem hp)
        (fun hqp => hq (hqp ▸ hp)))
    rw [Finset.prod_insert hq, ← Nat.modEq_and_modEq_iff_modEq_mul hq',
      ih (fun p hp r hr hpr => hcop p (Finset.mem_insert_of_mem hp) r
        (Finset.mem_insert_of_mem hr) hpr), Finset.forall_mem_insert]

/-- The product of the revealed prime powers, `D_𝒥 = ∏_p p^{𝒥_p}`. -/
def revealedModulus (J : ∀ j, Fin ((coordChain Kint pr h j).depth + 1)) : ℕ :=
  ∏ p, pr p ^ (J (some p) : ℕ)

/-- **The revealed projection on the unsplit index is `E[Z | b, s mod D_𝒥]`** (the
interval label `b` when revealed): the conditioning of `cor:index-support-frame`(ii), "a
uniform residue conditioned on its revealed depths `𝒥_e`", with `D_𝒥` the product of the
revealed prime powers. -/
theorem unsplitRevelation_reveal_mod {ι : Type*}
    (t : ∀ p, Tails (Chain.residues (pr p) (h p)).depth)
    (J : ∀ j, Fin ((coordChain Kint pr h j).depth + 1))
    (Z : (ZMod Kint × ZMod (modulus pr h)) → ι → ℝ) :
    (unsplitRevelation Kint pr h hcop t).reveal J Z =
      act (condExpMatrix (fun x : ZMod Kint × ZMod (modulus pr h) =>
        (coordLabel Kint pr h none (J none) x.1, x.2.val % revealedModulus Kint pr h J))) Z := by
  rw [unsplitRevelation_reveal]
  congr 1
  apply condExpMatrix_congr
  intro x y
  have hJ (p : P) : (J (some p) : ℕ) ≤ h p := by
    have := (J (some p)).isLt
    change (J (some p) : ℕ) < h p + 1 at this
    omega
  have hcopJ : ∀ p ∈ (Finset.univ : Finset P), ∀ q ∈ (Finset.univ : Finset P), p ≠ q →
      Nat.Coprime (pr p ^ (J (some p) : ℕ)) (pr q ^ (J (some q) : ℕ)) := by
    intro p _ q _ hpq
    exact ((hcop hpq).coprime_dvd_left (Nat.pow_dvd_pow _ (hJ p))).coprime_dvd_right
      (Nat.pow_dvd_pow _ (hJ q))
  constructor
  · intro hxy
    refine Prod.ext (congrFun hxy none) ?_
    change x.2.val ≡ y.2.val [MOD revealedModulus Kint pr h J]
    rw [revealedModulus, modEq_prod_iff _ _ hcopJ]
    intro p _
    have h1 := congrFun hxy (some p)
    change residueLabel (pr p) (h p) (J (some p)) (crtResidues pr h hcop x.2 p) =
      residueLabel (pr p) (h p) (J (some p)) (crtResidues pr h hcop y.2 p) at h1
    unfold residueLabel at h1
    rw [crtResidues_val_mod pr h hcop _ p (hJ p), crtResidues_val_mod pr h hcop _ p (hJ p)] at h1
    exact h1
  · intro hxy
    have h1 : coordLabel Kint pr h none (J none) x.1 = coordLabel Kint pr h none (J none) y.1 :=
      congrArg Prod.fst hxy
    have h2 : x.2.val ≡ y.2.val [MOD revealedModulus Kint pr h J] := congrArg Prod.snd hxy
    rw [revealedModulus, modEq_prod_iff _ _ hcopJ] at h2
    funext j
    match j with
    | none => exact h1
    | some p =>
      change residueLabel (pr p) (h p) (J (some p)) (crtResidues pr h hcop x.2 p) =
        residueLabel (pr p) (h p) (J (some p)) (crtResidues pr h hcop y.2 p)
      unfold residueLabel
      rw [crtResidues_val_mod pr h hcop _ p (hJ p), crtResidues_val_mod pr h hcop _ p (hJ p)]
      exact h2 p (Finset.mem_univ p)

end Conditional

section CutForm

variable (Kint : ℕ) [NeZero Kint] {P : Type*} [Fintype P] [DecidableEq P] (pr h : P → ℕ)
  [∀ p, NeZero (pr p ^ h p)] (hcop : Pairwise (Nat.Coprime on fun p => pr p ^ h p))
  {E : Type*} [Fintype E] [DecidableEq E]
  {V : Type*} [Fintype V] [DecidableEq V]
  {𝔅 : Type*} [Fintype 𝔅] [DecidableEq 𝔅] {Xb : 𝔅 → Type*} [∀ b, Fintype (Xb b)]
  [∀ b, DecidableEq (Xb b)]

/-- **`cor:index-support-frame`(ii)+(iii) and `eq:cp:mean-step` on the unsplit coupled index**
`ω_e = (b_e, s_e) ∈ ℤ/Kℤ × ℤ/M_0ℤ`, cut form. The half-functions carry slot functions
`φ_e(ω_e)` at the distinct sources `u_e` and `ψ_e(ω_e)` at the distinct reflected targets
`ι v_e`, and `F` elsewhere; every slot function averages to `F` over the uniform index
(`E_{b,s} g^{I_b,M_0,s} = F_A` in the paper). The energies use independent conductor depths
across queries; their revealed projections are the conditional expectations of
`unsplitRevelation_reveal`. -/
theorem unsplit_cut_mean_step (μ : E → ∀ p, ZMod (pr p ^ h p) → ℝ)
    (hμ : ∀ e p r, 0 ≤ μ e p r) (hμ1 : ∀ e p, ∑ r, μ e p r = 1)
    (t : E → ∀ p, Tails (Chain.residues (pr p) (h p)).depth)
    (hnorm : ∀ e p (l : Fin ((Chain.residues (pr p) (h p)).depth + 1)) f,
      (Chain.residues (pr p) (h p)).diff l *ᵥ f = f →
      (convMatrix (μ e p) *ᵥ f) ⬝ᵥ (convMatrix (μ e p) *ᵥ f) ≤ (t e p).tail l ^ 2 * (f ⬝ᵥ f))
    (c : ReflectionCut V) (ML ν MR : ∀ b, ((V → Xb b) → ℝ) →ₗ[ℝ] ℝ)
    (hbr : ∀ b, c.Bracket (ML b) (ν b) (MR b))
    {u w : E → c.Half} (hu : Function.Injective u) (hw : Function.Injective w)
    (φ ψ : E → (ZMod Kint × ZMod (modulus pr h)) → (∀ b, Xb b) → ℝ) (F : (∀ b, Xb b) → ℝ)
    (hφ : ∀ e y, (FiniteLaw.uniform (ZMod Kint × ZMod (modulus pr h))).expect
      (fun η => φ e η y) = F y)
    (hψ : ∀ e y, (FiniteLaw.uniform (ZMod Kint × ZMod (modulus pr h))).expect
      (fun η => ψ e η y) = F y) :
    let X := productHalf u φ F
    let Y := productHalf w ψ F
    let Xbar : (c.Half → ∀ b, Xb b) → ℝ := fun x => ∏ v, F (x v)
    let unif := FiniteLaw.uniform (E → ZMod Kint × ZMod (modulus pr h))
    let 𝒯 := signedOp (fun e => unsplitTransition Kint pr h hcop (μ e))
    let Rv := Revelation.pi (fun e => unsplitRevelation Kint pr h hcop (t e))
    let Jν := unif.expect (fun ω => c.form (tensorLaw ν) (X ω) (act 𝒯 Y ω))
    let Yν := c.form (tensorLaw ν) Xbar Xbar
    let eL := c.form (tensorLaw ML) Xbar Xbar
    let eR := c.form (tensorLaw MR) Xbar Xbar
    let VL := Rv.law.expect (fun J => unif.expect (fun ω =>
      c.form (tensorLaw ML) (Rv.reveal J X ω) (Rv.reveal J X ω)))
    let VR := Rv.law.expect (fun J => unif.expect (fun ω =>
      c.form (tensorLaw MR) (Rv.reveal J Y ω) (Rv.reveal J Y ω)))
    eL ≤ VL ∧ 0 ≤ eL ∧ eR ≤ VR ∧ 0 ≤ eR ∧
      |Jν - Yν| ≤ (1 / 2) * ((VL - eL) + (VR - eR)) ∧
      |Jν| ≤ Real.sqrt VL * Real.sqrt VR ∧
      Jν ≤ Yν + (1 / 2) * ((VL - eL) + (VR - eR)) := by
  intro X Y Xbar unif 𝒯 Rv Jν Yν eL eR VL VR
  have hG : (Matrix.fromBlocks (c.matrix (tensorLaw ML)) (c.matrix (tensorLaw ν))
      (c.matrix (tensorLaw ν))ᵀ (c.matrix (tensorLaw MR))).PosSemidef :=
    (c.bracket_iff_blockMatrix_posSemidef _ _ _).mp (ReflectionCut.Bracket.tensor hbr)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := unsplit_bounds Kint pr h hcop μ hμ hμ1 t hnorm hG X Y Xbar
    (vmean_productHalf_of_mean hu hφ) (vmean_productHalf_of_mean hw hψ)
  have hform (κ : ((V → ∀ b, Xb b) → ℝ) →ₗ[ℝ] ℝ)
      (A B : (E → ZMod Kint × ZMod (modulus pr h)) → (c.Half → ∀ b, Xb b) → ℝ) :
      unif.expect (fun ω => c.form κ (A ω) (B ω)) = pairing (c.matrix κ) A B := by
    rw [pairing_eq_expect]
    apply FiniteLaw.expect_congr
    intro ω
    exact c.form_eq_dotProduct κ (A ω) (B ω)
  have hJ : Jν = pairing (c.matrix (tensorLaw ν)) X (act 𝒯 Y) := hform _ _ _
  have hVL : VL = Rv.energy (c.matrix (tensorLaw ML)) X := by
    change Rv.law.expect _ = Rv.law.expect _
    apply FiniteLaw.expect_congr
    intro J
    exact hform _ _ _
  have hVR : VR = Rv.energy (c.matrix (tensorLaw MR)) Y := by
    change Rv.law.expect _ = Rv.law.expect _
    apply FiniteLaw.expect_congr
    intro J
    exact hform _ _ _
  have hY' : Yν = Xbar ⬝ᵥ (c.matrix (tensorLaw ν) *ᵥ Xbar) := c.form_eq_dotProduct _ _ _
  have heL : eL = Xbar ⬝ᵥ (c.matrix (tensorLaw ML) *ᵥ Xbar) := c.form_eq_dotProduct _ _ _
  have heR : eR = Xbar ⬝ᵥ (c.matrix (tensorLaw MR) *ᵥ Xbar) := c.form_eq_dotProduct _ _ _
  rw [hJ, hVL, hVR, hY', heL, heR]
  refine ⟨h1, h2, h3, h4, h5, h6, ?_⟩
  have := (abs_le.mp h5).2
  linarith

end CutForm

end Sarkozy.IndexSupport
