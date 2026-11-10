module

public import Sarkozy.BlockAdapter.Final

@[expose] public section

/-!
# The upper layer caps (V3) of the non-`E × E` states from per-prime certificates

`paper/sections/25_upper_reference.tex`, (V3) of `subsec:upper-reference-rp`,
`lem:upper-reference-rp`(ii), `subsec:upper-nonroot` (the layer cuts FL22, EL22, FF22, FE22),
formula (F6) of `def:record:upper-bands` with its block form, the root cut LL22
(`cert:upper-root-caps`, `lem:upper-completed-root`), `prop:observed-caps`.

B6's field `UpperBandRowsNonEE k` has three parts: the rows `rows20`, `rows10` (V2) and the layer
caps of the 16 states `𝔱 = (𝔱₀, 𝔱₁)` other than `E × E` (V3). The layer cap of a state is the
block-cap form of the layer cut of its field pair `G_{𝔣(𝔱₀)𝔣(𝔱₁),2}`, *except* for the four
observed states `LR`, `RL`, `LC`, `CL`, whose recorded caps are the smaller observed caps of
`prop:observed-caps` (compressions of the EL22 cut operator to the observed labels; for band 1
the recorded caps are `2.26882` and `0.07976` against `5.65087` for the full EL22 cut).

* `fieldGraph_upSwap`, `fieldGraph_upRestricts`: the edge rule of `G_{φ₀φ₁}` does not read the
  layer, so every field graph is invariant under the layer swap and `G_{φ₀φ₁,1}` is its layer-`0`
  restriction (`lem:upper-geometry`(c));
* `UpLayerCutCap f₀ f₁ g B p`: the per-prime bounds `-g p^{-1/2} ⪯ A_p ⪯ 1 + B/p` of the cut
  operator of the layer swap of `G_{f₀f₁,2}` at `p` (the paper's (F6) at one prime);
* `UpperBandLayerCap k f₀ f₁ d`: constants `(g, B, X)` with `1 < X ≤ X_k`, `g X^{-1/2} < 1`,
  `g e^{B L_k/(X log X)} ≤ d` and `UpLayerCutCap` at every class-three prime of band `k`
  (the shape of B6's `UpperBandRootCap`);
* **`upperStateLayerCap_of_band`**: the layer cap (V3) of a state on a block of band `k` from the
  band certificate of its field pair (B6's adapter `upLayerCap_of_cutCaps`);
* `IsObserved`, `UpperLayerCerts k` (the band certificates of the 12 states that are neither
  `E × E` nor observed), `UpperObservedCaps k` (the block-level caps of the 4 observed states),
  `UpperBandRowsV2 k` (the rows alone);
* **`upperBandRowsNonEE_of_certs`**: B6's `UpperBandRowsNonEE k` from these three.
-/

open scoped InnerProductSpace
open Finset

namespace Sarkozy.BlockInputs

open Sarkozy Sarkozy.Labellings Sarkozy.PartV Sarkozy.FiveType Sarkozy.FiveType.TwoCoord
  Sarkozy.PartVLaws Sarkozy.BlockSpecPaper Sarkozy.Cuts Sarkozy.BlockAdapter

/-! ## The layer geometry of the field graphs -/

/-- Every two-layer field graph is invariant under the layer swap: the edge rule of `G_{φ₀φ₁}`
does not read the layer. -/
theorem fieldGraph_upSwap (f₀ f₁ : FType) :
    UpSwapInvariant f₀.Obj f₁.Obj (fieldGraph f₀ f₁ (Fin 2)) := by
  intro u w
  simp only [fieldGraph, mem_twoLayerGraph, twoLayerEdge]

/-- `G_{φ₀φ₁,1}` is the layer-`0` restriction of `G_{φ₀φ₁,2}`. -/
theorem fieldGraph_upRestricts (f₀ f₁ : FType) :
    UpLayerRestricts f₀.Obj f₁.Obj (fieldGraph f₀ f₁ (Fin 2)) (fieldGraph f₀ f₁ (Fin 1)) := by
  intro a a' b b'
  simp only [fieldGraph, mem_twoLayerGraph, twoLayerEdge]

/-- The spectral data of the layer cut of `G_{f₀f₁,2}` (the paper's `f₀f₁22`). -/
noncomputable abbrev upFieldLayer (f₀ f₁ : FType) : SpecData (f₀.Obj × f₁.Obj × Fin 2) :=
  upLayerData f₀.Obj f₁.Obj (fieldGraph f₀ f₁ (Fin 2)) (fieldGraph_upSwap f₀ f₁)

/-! ## The per-prime and per-band certificates -/

/-- **The per-prime cap of the layer cut of `G_{f₀f₁,2}`** at `p`: the cut operator `A_p` of the
layer swap satisfies `-g p^{-1/2} ⪯ A_p ⪯ 1 + B/p` ((F6) at one prime; for `f₀ = f₁ = L` the
root cut LL22). -/
def UpLayerCutCap (f₀ f₁ : FType) (g B : ℝ) (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (hne : (injLabellings (ZMod p) (fieldGraph f₀ f₁ (Fin 2))).Nonempty)
    (v : EuclideanSpace ℝ ((upFieldLayer f₀ f₁).cut.Half → ZMod p)),
    -(g * (√(p : ℝ))⁻¹) * ‖v‖ ^ 2 ≤ ⟪v, Spectral.cutOp (upFieldLayer f₀ f₁) hne v⟫_ℝ ∧
      ⟪v, Spectral.cutOp (upFieldLayer f₀ f₁) hne v⟫_ℝ ≤ (1 + B / p) * ‖v‖ ^ 2

/-- **The layer-cap certificate of band `k` at the field pair `(f₀, f₁)`** for the cap `d`:
per-prime constants `(g, B)` and a threshold `X ≤ X_k` whose block cap `g e^{B L_k/(X log X)}` is
at most `d`, with the per-prime bounds at every class-three prime of the band. *Hypothesis*
(`cert:upper-band-inputs`(a), (F6) and its block form; for LL22 `cert:upper-root-caps`,
`lem:upper-completed-root`). -/
def UpperBandLayerCap (k : Fin 310) (f₀ f₁ : FType) (d : ℝ) : Prop :=
  ∃ g B X : ℝ, 0 ≤ g ∧ 0 ≤ B ∧ 1 < X ∧ X ≤ (bandOf k).1 ∧ g * (√X)⁻¹ < 1 ∧
    g * Real.exp (B * (UpperRecords.CompletionData.record k).budget / (X * Real.log X)) ≤ d ∧
    ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 → (bandOf k).1 ≤ p → p < (bandOf k).2 →
      UpLayerCutCap f₀ f₁ g B p

/-! ## The layer cap of a state from the band certificate -/

/-- **The layer cap (V3) of a state on a block of band `k`** from the band certificate of its
field pair: `Π_{𝔱,φ} ⪰_ι -d b^{-1/2} Diag_ι(Π⁽¹⁾_{𝔱,φ})` for every pattern pair `φ`. -/
theorem upperStateLayerCap_of_band (k : Fin 310) {ι : Type} [Fintype ι] [DecidableEq ι]
    (pr : ι → ℕ) [∀ j, Fact (pr j).Prime] (b : ℕ) (h3 : ∀ j, pr j % 4 = 3)
    (hband : ∀ j, (bandOf k).1 ≤ pr j ∧ pr j < (bandOf k).2)
    (hbud : ∑ j, Real.log (pr j) ≤ (UpperRecords.CompletionData.record k).budget)
    (hb : ∀ j, b ≤ pr j) (hb' : ∃ j, pr j = b) (hne : UpperNonempty pr)
    (t : PType × PType) (d : ℝ) (hcert : UpperBandLayerCap k t.1.field t.2.field d)
    (φ : t.1.Pat × t.2.Pat) :
    reservedCut.Below
      (-(d * (b : ℝ) ^ (-(1 / 2 : ℝ))) •
        signedIntegral (upComponent (upperBlockFieldLaws pr hne) (false, ⟨t, φ⟩)).weight)
      (signedIntegral (upComponent (upperBlockFieldLaws pr hne) (true, ⟨t, φ⟩)).weight) := by
  obtain ⟨g, B, X, hg, hB, hX, hXk, hgX, hinf, hp⟩ := hcert
  have hXp : ∀ j, X ≤ pr j := fun j => hXk.trans (by exact_mod_cast (hband j).1)
  have hXb : X ≤ b := by
    obtain ⟨j₀, hj₀⟩ := hb'
    rw [← hj₀]
    exact hXp j₀
  have hgp : ∀ j, g * (√(pr j : ℝ))⁻¹ < 1 := by
    intro j
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left ?_ hg) hgX
    exact inv_anti₀ (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_le_sqrt (hXp j))
  have hcap := fun j => hp (pr j) (h3 j) (hband j).1 (hband j).2
  have h := upLayerCap_of_cutCaps t.1.field.Obj t.2.field.Obj pr (fieldGraph t.1.field t.2.field
    (Fin 2)) (fieldGraph_upSwap _ _) (fieldGraph t.1.field t.2.field (Fin 1))
    (fieldGraph_upRestricts _ _) (hne.two t.1.field t.2.field) (hne.one t.1.field t.2.field)
    (t.1.pat φ.1) (t.2.pat φ.2) hg hB hX hXb (fun j => by exact_mod_cast hb j) hbud hgp
    (fun j v => (hcap j (hne.two t.1.field t.2.field j) v).1)
    (fun j v => (hcap j (hne.two t.1.field t.2.field j) v).2)
  have hdiag := emit_positive (blockGraphLaw pr (fieldGraph t.1.field t.2.field (Fin 1))
    (hne.one t.1.field t.2.field)) (upDiagEmission (t.1.pat φ.1) (t.2.pat φ.2)) reservedCut
    (upDiagEmission_reserved _ _)
  have hr : 0 ≤ (√(b : ℝ))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  rw [rpow_neg_half_eq]
  exact Reserved.below_mono_coeff reservedCut hdiag (mul_le_mul_of_nonneg_right hinf hr) h

/-! ## The split of B6's field -/

/-- The four observed states `LR`, `RL`, `LC`, `CL` (`prop:observed-caps`), whose recorded caps
are caps of compressions of the EL22 cut operator, not of the full layer cut. -/
def IsObserved (t : PType × PType) : Prop :=
  t = (.L, .R) ∨ t = (.R, .L) ∨ t = (.L, .C) ∨ t = (.C, .L)

/-- **The band layer certificates of band `k`**: for each of the 12 states that are neither
`E × E` nor observed, the certificate of its field pair at the recorded cap of the state (the
field pairs LL, LF, FL, FF, LE, EL, FE, EF; the paper's LL22, FL22, EL22, FF22, FE22 and their
coordinate exchanges). *Hypothesis* (per-prime analytic statements with per-band constants). -/
def UpperLayerCerts (k : Fin 310) : Prop :=
  ∀ t : PType × PType, ¬ IsEE t → ¬ IsObserved t →
    UpperBandLayerCap k t.1.field t.2.field (UpperRecords.bandCap k t.1 t.2)

/-- **The layer caps of the four observed states** on every block of band `k`, at the recorded
caps (`prop:observed-caps` with its block form). *Hypothesis* (block level, spectral). -/
def UpperObservedCaps (k : Fin 310) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ j, Fact (pr j).Prime] (b : ℕ),
    Function.Injective pr → (∀ j, pr j % 4 = 3) →
    (∀ j, (bandOf k).1 ≤ pr j ∧ pr j < (bandOf k).2) →
    (∑ j, Real.log (pr j) ≤ (UpperRecords.CompletionData.record k).budget) →
    (∀ j, b ≤ pr j) → (∃ j, pr j = b) →
    ∀ (hne : UpperNonempty pr) (_hW' : ∀ i, WeilBound (ZMod (pr i)))
      (_hp' : ∀ i, (2 : ℝ) ^ 20 ≤ pr i) (t : PType × PType) (φ : t.1.Pat × t.2.Pat),
      IsObserved t → reservedCut.Below
        (-(UpperRecords.bandCap k t.1 t.2 * (b : ℝ) ^ (-(1 / 2 : ℝ))) •
          signedIntegral (upComponent (upperBlockFieldLaws pr hne) (false, ⟨t, φ⟩)).weight)
        (signedIntegral (upComponent (upperBlockFieldLaws pr hne) (true, ⟨t, φ⟩)).weight)

/-- **The coordinate-`0` rows of band `k`** (V2; `rows20`, `rows10` of B6's
`UpperBandRowsNonEE`). *Hypothesis* (block level, spectral; `lem:upper-reference-rp`(ii), (F5)). -/
def UpperBandRowsV2 (k : Fin 310) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ j, Fact (pr j).Prime] (b : ℕ),
    Function.Injective pr → (∀ j, pr j % 4 = 3) →
    (∀ j, (bandOf k).1 ≤ pr j ∧ pr j < (bandOf k).2) →
    (∑ j, Real.log (pr j) ≤ (UpperRecords.CompletionData.record k).budget) →
    (∀ j, b ≤ pr j) → (∃ j, pr j = b) →
    ∀ (hne : UpperNonempty pr) (hW' : ∀ i, WeilBound (ZMod (pr i)))
      (hp' : ∀ i, (2 : ℝ) ^ 20 ≤ pr i),
      (∀ f', ValidRows (rowD0 (lam2 (upperBlockFieldLaws pr hne)) f'
        ((block_upperDatumHyp pr hW' hp' hne).two0 f')) ((b : ℝ) ^ (-(1 / 2 : ℝ)))
          (UpperRecords.bandOrd k f').f (UpperRecords.bandOrd k f').h
          (UpperRecords.bandOrd k f').M) ∧
      (∀ f', ValidRows (rowD0 (lam1 (upperBlockFieldLaws pr hne)) f'
        ((block_upperDatumHyp pr hW' hp' hne).one0 f')) ((b : ℝ) ^ (-(1 / 2 : ℝ)))
          (UpperRecords.bandRes k f').f (UpperRecords.bandRes k f').h
          (UpperRecords.bandRes k f').M)

/-- **B6's `UpperBandRowsNonEE k` from the rows, the band layer certificates and the observed
caps.** -/
theorem upperBandRowsNonEE_of_certs {k : Fin 310} (hR : UpperBandRowsV2 k)
    (hC : UpperLayerCerts k) (hO : UpperObservedCaps k) : UpperBandRowsNonEE k := by
  intro ι _ _ pr _ b hinj h3 hband hbud hb hb' hne hW' hp'
  obtain ⟨w20, w10⟩ := hR ι pr b hinj h3 hband hbud hb hb' hne hW' hp'
  refine ⟨w20, w10, fun t φ hEE => ?_⟩
  by_cases hob : IsObserved t
  · exact hO ι pr b hinj h3 hband hbud hb hb' hne hW' hp' t φ hob
  · exact upperStateLayerCap_of_band k pr b h3 hband hbud hb hb' hne t _ (hC t hEE hob) φ

/-- Conversely, `UpperBandRowsNonEE k` gives the rows (non-vacuity of the split). -/
theorem upperBandRowsV2_of_nonEE {k : Fin 310} (h : UpperBandRowsNonEE k) : UpperBandRowsV2 k := by
  intro ι _ _ pr _ b hinj h3 hband hbud hb hb' hne hW' hp'
  obtain ⟨w20, w10, -⟩ := h ι pr b hinj h3 hband hbud hb hb' hne hW' hp'
  exact ⟨w20, w10⟩

/-- Conversely, `UpperBandRowsNonEE k` gives the observed caps (non-vacuity of the split). -/
theorem upperObservedCaps_of_nonEE {k : Fin 310} (h : UpperBandRowsNonEE k) :
    UpperObservedCaps k := by
  intro ι _ _ pr _ b hinj h3 hband hbud hb hb' hne hW' hp' t φ hob
  have hEE : ¬ IsEE t := by
    rcases hob with rfl | rfl | rfl | rfl <;> simp [IsEE]
  exact (h ι pr b hinj h3 hband hbud hb hb' hne hW' hp').2.2 t φ hEE

end Sarkozy.BlockInputs
