module

public import Sarkozy.BlockInputs.Observed
public import Sarkozy.MiddleCertificates.L20Bridge

@[expose] public section

/-!
# The coordinate exchange of the upper layer cuts (`lem:upper-geometry`)

`paper/sections/25_upper_reference.tex`, `subsec:upper-nonroot` (the layer cuts are certified in
one orientation: FL22, EL22, FF22, FE22, and LL22), `prop:observed-caps` (EL22), the coordinate
exchange of `lem:upper-geometry`; `13_cuts_correlations.tex`, `lem:cut-transport`.

`UpperLayerCerts` and `UpperObservedCerts` ask for the per-prime certificate of every state's
field pair in the state's own orientation, so for the mixed pairs in both orders. The exchange
`(a, b, ℓ) ↦ (b, a, ℓ)` is an isomorphism of the layer-cut spectral data
`G_{f₀f₁,2} → G_{f₁f₀,2}` (`coordSwap_transport`), and the cut operators correspond
(`lem:cut-transport`). Here:

* **`upLayerCutCap_swap`**, `upperBandLayerCap_swap`: a certificate of `(f₀, f₁)` is one of
  `(f₁, f₀)`; **`obsCutCap_swap`**, `upperBandObsCap_swap`: the same for compressions;
* `UpperLayerCertsP k`, `UpperObservedCertsP k`: the certificates in the paper's orientations only
  (LL, FL, FF, EL, FE; the observed EL compressions), at the minimum of the two recorded state caps
  (equal in the records);
* **`upperLayerCerts_of_paper`**, **`upperObservedCerts_of_paper`**.
-/

open scoped InnerProductSpace
open Finset

namespace Sarkozy.BlockInputs

open Sarkozy Sarkozy.Labellings Sarkozy.PartV Sarkozy.FiveType Sarkozy.FiveType.TwoCoord
  Sarkozy.PartVLaws Sarkozy.BlockSpecPaper Sarkozy.Cuts Sarkozy.Cuts.SpecData Sarkozy.BlockAdapter

/-- The coordinate exchange `(a, b, ℓ) ↦ (b, a, ℓ)`. -/
def coordSwap3 (A B : Type) : A × B × Fin 2 ≃ B × A × Fin 2 where
  toFun v := (v.2.1, v.1, v.2.2)
  invFun v := (v.2.1, v.1, v.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The exchange is an isomorphism of the layer-cut spectral data** (`lem:upper-geometry`). -/
theorem coordSwap_transport (f₀ f₁ : FType) :
    (upFieldLayer f₀ f₁).Transport (upFieldLayer f₁ f₀) (coordSwap3 f₀.Obj f₁.Obj) where
  edges u w := by
    change (u, w) ∈ (fieldGraph f₀ f₁ (Fin 2)).E ↔
      (coordSwap3 f₀.Obj f₁.Obj u, coordSwap3 f₀.Obj f₁.Obj w) ∈ (fieldGraph f₁ f₀ (Fin 2)).E
    simp only [fieldGraph, mem_twoLayerGraph, twoLayerEdge, coordSwap3, Equiv.coe_fn_mk,
      Bool.and_eq_true, Bool.or_eq_true]
    tauto
  half u := by
    change u ∈ (upCut f₀.Obj f₁.Obj).half ↔ coordSwap3 f₀.Obj f₁.Obj u ∈ (upCut f₁.Obj f₀.Obj).half
    rw [mem_upHalf, mem_upHalf]
    rfl
  flip _ := rfl

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The inverse transport. -/
theorem coordSwap_transport_symm (f₀ f₁ : FType) :
    (upFieldLayer f₁ f₀).Transport (upFieldLayer f₀ f₁) (coordSwap3 f₀.Obj f₁.Obj).symm where
  edges u w := by
    have h := (coordSwap_transport f₀ f₁).edges ((coordSwap3 f₀.Obj f₁.Obj).symm u)
      ((coordSwap3 f₀.Obj f₁.Obj).symm w)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    exact h.symm
  half u := by
    have h := (coordSwap_transport f₀ f₁).half ((coordSwap3 f₀.Obj f₁.Obj).symm u)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  flip _ := rfl

/-- **Form bounds transport**: `-c ‖F‖² ≤ ⟨F, A F⟩ ≤ C ‖F‖²` for all `F` on the `(f₀, f₁)` side
gives the same for every function on the `(f₁, f₀)` side of the form `F ∘ Φ⁻¹`. -/
theorem cutForm_bounds_swap (f₀ f₁ : FType) {c C : ℝ}
    (hne' : (injLabellings F (upFieldLayer f₁ f₀).G).Nonempty)
    (Fn : ((upFieldLayer f₀ f₁).cut.Half → F) → ℝ)
    (h : ∀ hne : (injLabellings F (upFieldLayer f₀ f₁).G).Nonempty,
      -c * Recentering.nrm ((upFieldLayer f₀ f₁).halfLaw hne) Fn ^ 2 ≤
          (upFieldLayer f₀ f₁).cutForm hne Fn Fn ∧
        (upFieldLayer f₀ f₁).cutForm hne Fn Fn ≤
          C * Recentering.nrm ((upFieldLayer f₀ f₁).halfLaw hne) Fn ^ 2) :
    -c * Recentering.nrm ((upFieldLayer f₁ f₀).halfLaw hne')
          (transportFun (coordSwap_transport f₀ f₁) Fn) ^ 2 ≤
        (upFieldLayer f₁ f₀).cutForm hne' (transportFun (coordSwap_transport f₀ f₁) Fn)
          (transportFun (coordSwap_transport f₀ f₁) Fn) ∧
      (upFieldLayer f₁ f₀).cutForm hne' (transportFun (coordSwap_transport f₀ f₁) Fn)
          (transportFun (coordSwap_transport f₀ f₁) Fn) ≤
        C * Recentering.nrm ((upFieldLayer f₁ f₀).halfLaw hne')
          (transportFun (coordSwap_transport f₀ f₁) Fn) ^ 2 := by
  have hne := nonempty_transport (coordSwap_transport_symm f₀ f₁) hne'
  have hform := transport_cutForm (coordSwap_transport f₀ f₁) hne Fn Fn
  have hnrm := transport_unitary (coordSwap_transport f₀ f₁) hne Fn Fn
  have hn : Recentering.nrm ((upFieldLayer f₁ f₀).halfLaw hne')
      (transportFun (coordSwap_transport f₀ f₁) Fn) =
      Recentering.nrm ((upFieldLayer f₀ f₁).halfLaw hne) Fn := by
    unfold Recentering.nrm
    exact congrArg Real.sqrt hnrm
  rw [hn, hform]
  exact h hne

omit [Field F] [Fintype F] [DecidableEq F] in
/-- Every function on the `(f₁, f₀)` side is a transport. -/
theorem transportFun_surj (f₀ f₁ : FType) (G : ((upFieldLayer f₁ f₀).cut.Half → F) → ℝ) :
    transportFun (coordSwap_transport f₀ f₁)
      (fun x => G (fun k' => x ((halfEquiv (coordSwap_transport f₀ f₁)).symm k'))) = G := by
  funext ξ
  simp only [transportFun, Equiv.apply_symm_apply]

/-- **The per-prime layer cap is invariant under the coordinate exchange.** -/
theorem upLayerCutCap_swap (f₀ f₁ : FType) {g B : ℝ} (hg : 0 ≤ g) (hB : 0 ≤ B) {p : ℕ}
    [Fact p.Prime] (h : UpLayerCutCap f₀ f₁ g B p) : UpLayerCutCap f₁ f₀ g B p := by
  intro hne' v
  have hr : 0 ≤ (√(p : ℝ))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  refine MiddleCertificates.kernelOp_bounds_of_form ((upFieldLayer f₁ f₀).halfLaw hne')
    (fun x x' => (upFieldLayer f₁ f₀).cutK x x' / (upFieldLayer f₁ f₀).cutZ hne')
    (mul_nonneg hg hr) (by positivity) (fun G => ?_) v
  set Fn : ((upFieldLayer f₀ f₁).cut.Half → ZMod p) → ℝ :=
    fun x => G (fun k' => x ((halfEquiv (coordSwap_transport f₀ f₁)).symm k'))
  have hb := cutForm_bounds_swap f₀ f₁ hne' Fn
    (fun hne => Spectral.cutForm_bounds_of_op (upFieldLayer f₀ f₁) hne
      (fun v => (h hne v).1) (fun v => (h hne v).2) Fn)
  rw [transportFun_surj f₀ f₁ G] at hb
  have hn : Recentering.nrm ((upFieldLayer f₁ f₀).halfLaw hne') G ^ 2 =
      ((upFieldLayer f₁ f₀).halfLaw hne').expect (fun x => G x ^ 2) := by
    unfold Recentering.nrm Recentering.ip
    rw [Real.sq_sqrt (((upFieldLayer f₁ f₀).halfLaw hne').expect_nonneg
      fun x => mul_self_nonneg _)]
    exact ((upFieldLayer f₁ f₀).halfLaw hne').expect_congr fun x => (sq (G x)).symm
  rw [hn] at hb
  exact hb

/-- The band certificate is invariant under the coordinate exchange. -/
theorem upperBandLayerCap_swap {k : Fin 310} {f₀ f₁ : FType} {d : ℝ}
    (h : UpperBandLayerCap k f₀ f₁ d) : UpperBandLayerCap k f₁ f₀ d := by
  obtain ⟨g, B, X, hg, hB, hX, hXk, hgX, hinf, hp⟩ := h
  exact ⟨g, B, X, hg, hB, hX, hXk, hgX, hinf,
    fun p _ h3 h1 h2 => upLayerCutCap_swap f₀ f₁ hg hB (hp p h3 h1 h2)⟩

theorem upperBandLayerCap_mono {k : Fin 310} {f₀ f₁ : FType} {d d' : ℝ}
    (h : UpperBandLayerCap k f₀ f₁ d) (hd : d ≤ d') : UpperBandLayerCap k f₀ f₁ d' := by
  obtain ⟨g, B, X, hg, hB, hX, hXk, hgX, hinf, hp⟩ := h
  exact ⟨g, B, X, hg, hB, hX, hXk, hgX, hinf.trans hd, hp⟩

/-! ## The observed compressions -/

/-- **The per-prime observed cap is invariant under the coordinate exchange**, for observed label
maps `ι_O`, `ι_O'` related by the exchange (`(Φ⁺)⁻¹ ∘ ι_O' = ι_O ∘ e`). -/
theorem obsCutCap_swap (f₀ f₁ : FType) {O O' : Type} [Fintype O] [DecidableEq O] [Fintype O']
    [DecidableEq O'] (ιO : O → (upFieldLayer f₀ f₁).cut.Half)
    (ιO' : O' → (upFieldLayer f₁ f₀).cut.Half) (e : O' → O)
    (he : ∀ o', (halfEquiv (coordSwap_transport f₀ f₁)).symm (ιO' o') = ιO (e o'))
    {g B : ℝ} {p : ℕ} [Fact p.Prime] (h : ObsCutCap f₀ f₁ ιO g B p) :
    ObsCutCap f₁ f₀ ιO' g B p := by
  intro hne' f
  set f'' : (O → ZMod p) → ℝ := fun y => f (fun o' => y (e o'))
  have hG : (f ∘ fun x => x ∘ ιO') = transportFun (coordSwap_transport f₀ f₁)
      (f'' ∘ fun x => x ∘ ιO) := by
    rw [← transportFun_surj f₀ f₁ (f ∘ fun x => x ∘ ιO')]
    congr 1
    funext x
    simp only [Function.comp_apply, f'']
    congr 1
    funext o'
    exact congrArg x (he o')
  rw [hG]
  exact cutForm_bounds_swap f₀ f₁ hne' _ (fun hne => h hne f'')

theorem upperBandObsCap_swap {k : Fin 310} {f₀ f₁ : FType} {O O' : Type} [Fintype O]
    [DecidableEq O] [Fintype O'] [DecidableEq O'] {ιO : O → (upFieldLayer f₀ f₁).cut.Half}
    {ιO' : O' → (upFieldLayer f₁ f₀).cut.Half} (e : O' → O)
    (he : ∀ o', (halfEquiv (coordSwap_transport f₀ f₁)).symm (ιO' o') = ιO (e o')) {d : ℝ}
    (h : UpperBandObsCap k f₀ f₁ ιO d) : UpperBandObsCap k f₁ f₀ ιO' d := by
  obtain ⟨g, B, X, hg, hB, hX, hXk, hgX, hinf, hp⟩ := h
  exact ⟨g, B, X, hg, hB, hX, hXk, hgX, hinf,
    fun p _ h3 h1 h2 => obsCutCap_swap f₀ f₁ ιO ιO' e he (hp p h3 h1 h2)⟩

theorem upperBandObsCap_mono {k : Fin 310} {f₀ f₁ : FType} {O : Type} [Fintype O]
    [DecidableEq O] {ιO : O → (upFieldLayer f₀ f₁).cut.Half} {d d' : ℝ}
    (h : UpperBandObsCap k f₀ f₁ ιO d) (hd : d ≤ d') : UpperBandObsCap k f₀ f₁ ιO d' := by
  obtain ⟨g, B, X, hg, hB, hX, hXk, hgX, hinf, hp⟩ := h
  exact ⟨g, B, X, hg, hB, hX, hXk, hgX, hinf.trans hd, hp⟩

/-! ## The certificates in the paper's orientations -/

open UpperRecords in
/-- The certificate of one canonical state `(t₀, t₁)`, at the smaller of the two recorded caps of
`(t₀, t₁)` and `(t₁, t₀)` (equal in the records: the caps are those of the field pair). -/
def CanonCert (k : Fin 310) (t₀ t₁ : PType) : Prop :=
  UpperBandLayerCap k t₀.field t₁.field (min (bandCap k t₀ t₁) (bandCap k t₁ t₀))

/-- **The layer-cut certificates of band `k` in the paper's orientations**: LL22 (state `LL`),
FL22 (`DL`), FF22 (`DD`), EL22 (`SL`) and FE22 (`DS`, `DR`, `DC`). *Hypothesis* (per prime, with
per-band constants; `cert:upper-band-inputs`(a), `cert:upper-root-caps`,
`lem:upper-completed-root`). -/
def UpperLayerCertsP (k : Fin 310) : Prop :=
  CanonCert k .L .L ∧ CanonCert k .D .L ∧ CanonCert k .D .D ∧ CanonCert k .S .L ∧
    CanonCert k .D .S ∧ CanonCert k .D .R ∧ CanonCert k .D .C

/-- **`UpperLayerCerts k` from the paper's orientations**, through the coordinate exchange. -/
theorem upperLayerCerts_of_paper {k : Fin 310} (h : UpperLayerCertsP k) : UpperLayerCerts k := by
  obtain ⟨hLL, hDL, hDD, hSL, hDS, hDR, hDC⟩ := h
  intro t hEE hob
  have dir : ∀ {t₀ t₁ : PType}, CanonCert k t₀ t₁ →
      UpperBandLayerCap k t₀.field t₁.field (UpperRecords.bandCap k t₀ t₁) :=
    fun hc => upperBandLayerCap_mono hc (min_le_left _ _)
  have rev : ∀ {t₀ t₁ : PType}, CanonCert k t₀ t₁ →
      UpperBandLayerCap k t₁.field t₀.field (UpperRecords.bandCap k t₁ t₀) :=
    fun hc => upperBandLayerCap_swap (upperBandLayerCap_mono hc (min_le_right _ _))
  rcases t with ⟨t₀, t₁⟩
  cases t₀ <;> cases t₁ <;> simp only [IsEE, IsObserved, Prod.mk.injEq] at hEE hob <;>
    first
    | exact dir hLL | exact dir hDL | exact dir hDD | exact dir hSL | exact dir hDS
    | exact dir hDR | exact dir hDC | exact rev hDL | exact rev hSL | exact rev hDS
    | exact rev hDR | exact rev hDC | simp at hEE hob

/-- The exchange of the merge labels: `(Φ⁺)⁻¹ ∘ obsLR = obsRL ∘ swap`. -/
theorem obsRL_LR (o : FType.L.Obj × Fin 2) :
    (halfEquiv (coordSwap_transport .E .L)).symm (obsLR o) = obsRL (o.2, o.1) := rfl

/-- The exchange of the constant labels: `(Φ⁺)⁻¹ ∘ obsLC = obsCL`. -/
theorem obsCL_LC (o : FType.L.Obj) :
    (halfEquiv (coordSwap_transport .E .L)).symm (obsLC o) = obsCL o := rfl

open UpperRecords in
/-- **The observed-cap certificates of band `k` in the paper's orientation** (EL22,
`prop:observed-caps`): the compressions of the layer cut of `G_{EL,2}` to the merge and the
constant labels, at the smaller of the two recorded caps (`RL`/`LR`, `CL`/`LC`). *Hypothesis* (per
prime, with per-band constants). -/
def UpperObservedCertsP (k : Fin 310) : Prop :=
  UpperBandObsCap k .E .L obsRL (min (bandCap k .R .L) (bandCap k .L .R)) ∧
    UpperBandObsCap k .E .L obsCL (min (bandCap k .C .L) (bandCap k .L .C))

/-- **`UpperObservedCerts k` from the paper's orientation**, through the coordinate exchange. -/
theorem upperObservedCerts_of_paper {k : Fin 310} (h : UpperObservedCertsP k) :
    UpperObservedCerts k := by
  obtain ⟨hRL, hCL⟩ := h
  refine ⟨?_, upperBandObsCap_mono hRL (min_le_left _ _), ?_,
    upperBandObsCap_mono hCL (min_le_left _ _)⟩
  · exact upperBandObsCap_swap (fun o => (o.2, o.1)) obsRL_LR
      (upperBandObsCap_mono hRL (min_le_right _ _))
  · exact upperBandObsCap_swap id obsCL_LC (upperBandObsCap_mono hCL (min_le_right _ _))

end Sarkozy.BlockInputs
