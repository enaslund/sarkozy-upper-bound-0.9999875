module

public import Sarkozy.BlockInputs.UpperLayer

@[expose] public section

/-!
# The observed merge and constant caps from per-prime certificates (`prop:observed-caps`)

`paper/sections/25_upper_reference.tex`, `prop:observed-caps` (the compression
`Op^O = Π_O Op Π_O` of the EL22 cut operator to the functions of the observed labels `x_O`:
`-g r ⪯ Op^O ⪯ 1 + B_top/p`, and the block caps), (V3) second assertion, `lem:five-type`(e);
`cert:upper-band-inputs`(b).

The four observed states `LR`, `RL`, `LC`, `CL` read only some labels of the `E` coordinate (the
rows `0, 1` for a merge, the row `0` for a constant), so their cut form at `ι` is that of the
field law on the functions of these labels. Here:

* `fibMass`, `margKer`: for a law `μ`, a kernel `K` and a map `r : X → O`, the compressed kernel
  `K^O = (r × r)_*(μ ⊗ μ · K)/(μ^O ⊗ μ^O)` relative to `μ^O = r_* μ`; `kernelForm_comp_eq`,
  `kernelForm_marg_eq`: `⟨f ∘ r, K (g ∘ r)⟩_μ = ⟨f, K^O g⟩_{μ^O}`;
* `pi_fibMass`, `pi_map_expect`, **`pi_kernelForm_comp`**: on a product, the compression of the
  tensor kernel is the tensor of the compressions;
* **`obs_block_lower`**: per-prime bounds `-g p^{-1/2} ⪯ A_p^O ⪯ 1 + B/p` on the functions of the
  observed labels give `(⊗ A_p)^O ⪰ -g e^{BL/(X log X)} b^{-1/2}` (`lem:spec:tensorcomp`(b) for
  the compressions);
* `ObsCutCap`, `UpperBandObsCap`, the observed label maps `obsLR`, `obsLC`, `obsRL`, `obsCL`,
  `UpperObservedCerts k`; **`upperObservedCaps_of_certs`**: `UpperObservedCaps k` from them.
-/

open scoped InnerProductSpace
open Finset

namespace Sarkozy.BlockInputs

open Sarkozy Sarkozy.Labellings Sarkozy.PartV Sarkozy.FiveType Sarkozy.FiveType.TwoCoord
  Sarkozy.PartVLaws Sarkozy.BlockSpecPaper Sarkozy.Cuts Sarkozy.BlockAdapter

/-! ## Compression to the functions of a map -/

section Marginal

variable {X O : Type} [Fintype X] [Fintype O] [DecidableEq O] (μ : FiniteLaw X)
  (K : X → X → ℝ) (r : X → O)

/-- The `μ ⊗ μ · K` mass of a pair of fibres of `r`. -/
noncomputable def fibMass (a b : O) : ℝ :=
  ∑ x ∈ univ.filter (fun x => r x = a), ∑ y ∈ univ.filter (fun y => r y = b),
    μ.weight x * μ.weight y * K x y

theorem map_weight_eq (a : O) :
    (μ.map r).weight a = ∑ x ∈ univ.filter (fun x => r x = a), μ.weight x := by
  rw [Finset.sum_filter]
  rfl

/-- **The compressed kernel** `K^O = (r × r)_*(μ ⊗ μ · K)/(μ^O ⊗ μ^O)` (`0` off the support). -/
noncomputable def margKer (a b : O) : ℝ :=
  if (μ.map r).weight a * (μ.map r).weight b = 0 then 0
  else fibMass μ K r a b / ((μ.map r).weight a * (μ.map r).weight b)

theorem fibMass_eq_zero {a b : O} (h : (μ.map r).weight a * (μ.map r).weight b = 0) :
    fibMass μ K r a b = 0 := by
  rcases mul_eq_zero.mp h with ha | hb
  · rw [map_weight_eq] at ha
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun x _ => μ.nonneg x).mp ha
    unfold fibMass
    refine Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y _ => ?_
    rw [h0 x hx]
    ring
  · rw [map_weight_eq] at hb
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun x _ => μ.nonneg x).mp hb
    unfold fibMass
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y hy => ?_
    rw [h0 y hy]
    ring

theorem marg_weight_mul (a b : O) :
    (μ.map r).weight a * (μ.map r).weight b * margKer μ K r a b = fibMass μ K r a b := by
  unfold margKer
  split_ifs with h
  · rw [mul_zero, fibMass_eq_zero μ K r h]
  · rw [mul_div_cancel₀ _ h]

theorem margKer_symm (hK : ∀ x y, K x y = K y x) (a b : O) :
    margKer μ K r a b = margKer μ K r b a := by
  have hf : fibMass μ K r a b = fibMass μ K r b a := by
    unfold fibMass
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by rw [hK]; ring
  unfold margKer
  rw [hf, mul_comm ((μ.map r).weight a)]

/-- **Regrouping by fibres**: `⟨f ∘ r, K (g ∘ r)⟩_μ = ∑_{a, b} f(a) g(b) M(a, b)`. -/
theorem kernelForm_comp_eq (f g : O → ℝ) :
    kernelForm μ μ K (f ∘ r) (g ∘ r) = ∑ a, ∑ b, f a * g b * fibMass μ K r a b := by
  have h1 : kernelForm μ μ K (f ∘ r) (g ∘ r) =
      ∑ a, ∑ x ∈ univ.filter (fun x => r x = a), ∑ b, ∑ y ∈ univ.filter (fun y => r y = b),
        μ.weight x * μ.weight y * f (r x) * K x y * g (r y) := by
    calc kernelForm μ μ K (f ∘ r) (g ∘ r)
        = ∑ x, ∑ y, μ.weight x * μ.weight y * f (r x) * K x y * g (r y) := by
          simp only [kernelForm, LinearMap.mk₂_apply, Function.comp_apply]
      _ = ∑ a, ∑ x ∈ univ.filter (fun x => r x = a),
            ∑ y, μ.weight x * μ.weight y * f (r x) * K x y * g (r y) :=
          (Finset.sum_fiberwise univ r _).symm
      _ = _ := Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ =>
          (Finset.sum_fiberwise univ r _).symm
  rw [h1]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  unfold fibMass
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  have hx' : r x = a := (Finset.mem_filter.mp hx).2
  have hy' : r y = b := (Finset.mem_filter.mp hy).2
  rw [hx', hy']
  ring

/-- The form of the compressed kernel: `⟨f, K^O g⟩_{μ^O} = ∑_{a, b} f(a) g(b) M(a, b)`. -/
theorem kernelForm_marg_eq (f g : O → ℝ) :
    kernelForm (μ.map r) (μ.map r) (margKer μ K r) f g =
      ∑ a, ∑ b, f a * g b * fibMass μ K r a b := by
  simp only [kernelForm, LinearMap.mk₂_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← marg_weight_mul μ K r a b]
  ring

/-- **`⟨f ∘ r, K (f ∘ r)⟩_μ = ⟨f, K^O f⟩_{μ^O}`** (the compression to the functions of `r`). -/
theorem kernelForm_comp_marg (f g : O → ℝ) :
    kernelForm μ μ K (f ∘ r) (g ∘ r) = kernelForm (μ.map r) (μ.map r) (margKer μ K r) f g := by
  rw [kernelForm_comp_eq, kernelForm_marg_eq]

theorem nrm_comp_map (f : O → ℝ) : Recentering.nrm μ (f ∘ r) = Recentering.nrm (μ.map r) f := by
  unfold Recentering.nrm Recentering.ip
  rw [FiniteLaw.expect_map]
  rfl

end Marginal

/-! ## Products -/

section PiMarginal

variable {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} [∀ i, Fintype (X i)]
  {O : ι → Type} [∀ i, Fintype (O i)] [∀ i, DecidableEq (O i)]
  (μ : ∀ i, FiniteLaw (X i)) (K : ∀ i, X i → X i → ℝ) (r : ∀ i, X i → O i)

/-- The coordinatewise map on a product. -/
def piRes (ξ : ∀ i, X i) : ∀ i, O i := fun i => r i (ξ i)

omit [∀ i, Fintype (O i)] in
theorem filter_piRes (a : ∀ i, O i) :
    univ.filter (fun ξ => piRes r ξ = a) =
      Fintype.piFinset (fun i => univ.filter (fun x => r i x = a i)) := by
  ext ξ
  simp [Fintype.mem_piFinset, piRes, funext_iff]

omit [∀ i, Fintype (O i)] in
/-- The fibre masses of a tensor kernel factor. -/
theorem pi_fibMass (a b : ∀ i, O i) :
    fibMass (FiniteLaw.pi μ) (fun x y => ∏ i, K i (x i) (y i)) (piRes r) a b =
      ∏ i, fibMass (μ i) (K i) (r i) (a i) (b i) := by
  unfold fibMass
  rw [filter_piRes, filter_piRes, Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun η _ => ?_
  change (∏ i, (μ i).weight (ξ i)) * (∏ i, (μ i).weight (η i)) * ∏ i, K i (ξ i) (η i) =
    ∏ i, ((μ i).weight (ξ i) * (μ i).weight (η i) * K i (ξ i) (η i))
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]

/-- The image of a product law under a coordinatewise map is the product of the images. -/
theorem pi_map_expect (h : (∀ i, O i) → ℝ) :
    (FiniteLaw.pi μ).expect (h ∘ piRes r) =
      (FiniteLaw.pi fun i => (μ i).map (r i)).expect h := by
  unfold FiniteLaw.expect
  rw [← Finset.sum_fiberwise univ (piRes r)]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hfib : ∀ ξ ∈ univ.filter (fun ξ => piRes r ξ = a),
      (FiniteLaw.pi μ).weight ξ * (h ∘ piRes r) ξ = (FiniteLaw.pi μ).weight ξ * h a := by
    intro ξ hξ
    rw [Function.comp_apply, (Finset.mem_filter.mp hξ).2]
  rw [Finset.sum_congr rfl hfib, ← Finset.sum_mul]
  congr 1
  change _ = ∏ i, ((μ i).map (r i)).weight (a i)
  simp only [map_weight_eq]
  rw [Finset.prod_univ_sum, filter_piRes]
  rfl

/-- **The compression of a tensor kernel is the tensor of the compressions.** -/
theorem pi_kernelForm_comp (Ψ : (∀ i, O i) → ℝ) :
    kernelForm (FiniteLaw.pi μ) (FiniteLaw.pi μ) (fun x y => ∏ i, K i (x i) (y i))
        (Ψ ∘ piRes r) (Ψ ∘ piRes r) =
      kernelForm (FiniteLaw.pi fun i => (μ i).map (r i)) (FiniteLaw.pi fun i => (μ i).map (r i))
        (fun a b => ∏ i, margKer (μ i) (K i) (r i) (a i) (b i)) Ψ Ψ := by
  rw [kernelForm_comp_eq]
  simp only [kernelForm, LinearMap.mk₂_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [pi_fibMass]
  change Ψ a * Ψ b * ∏ i, fibMass (μ i) (K i) (r i) (a i) (b i) =
    (∏ i, ((μ i).map (r i)).weight (a i)) * (∏ i, ((μ i).map (r i)).weight (b i)) * Ψ a *
      (∏ i, margKer (μ i) (K i) (r i) (a i) (b i)) * Ψ b
  rw [← Finset.prod_congr rfl fun i _ => marg_weight_mul (μ i) (K i) (r i) (a i) (b i),
    Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

end PiMarginal

/-! ## The block cap of a compression -/

section Block

variable {U : Type} [Fintype U] [DecidableEq U] (D : SpecData U) {ι : Type} [Fintype ι]
  [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (hL : ∀ i, (injLabellings (ZMod (pr i)) D.G).Nonempty)

/-- **The block cap of the compression to observed labels** (`prop:observed-caps`, block form;
`lem:spec:tensorcomp`(b) for the compressed operators): if at every prime the cut operator
satisfies `-g p^{-1/2} ⪯ A_p ⪯ 1 + B/p` on the functions of the labels `x ∘ ι_O`, then
`⊗ A_p ⪰ -g e^{BL/(X log X)} b^{-1/2}` on the functions of the block labels `(ξ_p ∘ ι_O)_p`. -/
theorem obs_block_lower {O : Type} [Fintype O] [DecidableEq O] (ιO : O → D.cut.Half)
    {g B X L b : ℝ} (hg : 0 ≤ g) (hB : 0 ≤ B) (hX : 1 < X) (hXb : X ≤ b)
    (hbp : ∀ i, b ≤ pr i) (hLs : ∑ i, Real.log (pr i) ≤ L) (hgp : ∀ i, g * (√(pr i : ℝ))⁻¹ < 1)
    (hlow : ∀ i (f : (O → ZMod (pr i)) → ℝ),
      -(g * (√(pr i : ℝ))⁻¹) * Recentering.nrm (D.halfLaw (hL i)) (f ∘ fun x => x ∘ ιO) ^ 2 ≤
        kernelForm (D.halfLaw (hL i)) (D.halfLaw (hL i))
          (fun x y => D.cutK x y / D.cutZ (hL i)) (f ∘ fun x => x ∘ ιO) (f ∘ fun x => x ∘ ιO))
    (hup : ∀ i (f : (O → ZMod (pr i)) → ℝ),
      kernelForm (D.halfLaw (hL i)) (D.halfLaw (hL i))
          (fun x y => D.cutK x y / D.cutZ (hL i)) (f ∘ fun x => x ∘ ιO) (f ∘ fun x => x ∘ ιO) ≤
        (1 + B / pr i) * Recentering.nrm (D.halfLaw (hL i)) (f ∘ fun x => x ∘ ιO) ^ 2)
    (Ψ : (∀ i, O → ZMod (pr i)) → ℝ) :
    -(g * Real.exp (B * L / (X * Real.log X)) * (√b)⁻¹) *
        Recentering.nrm (FiniteLaw.pi fun i => D.halfLaw (hL i))
          (Ψ ∘ piRes (fun i (x : D.cut.Half → ZMod (pr i)) => x ∘ ιO)) ^ 2 ≤
      kernelForm (FiniteLaw.pi fun i => D.halfLaw (hL i)) (FiniteLaw.pi fun i => D.halfLaw (hL i))
        (fun x y => ∏ i, D.cutK (x i) (y i) / D.cutZ (hL i))
        (Ψ ∘ piRes (fun i (x : D.cut.Half → ZMod (pr i)) => x ∘ ιO))
        (Ψ ∘ piRes (fun i (x : D.cut.Half → ZMod (pr i)) => x ∘ ιO)) := by
  set r : ∀ i, (D.cut.Half → ZMod (pr i)) → (O → ZMod (pr i)) := fun i x => x ∘ ιO
  set μ' := fun i => (D.halfLaw (hL i)).map (r i)
  set K' := fun i => margKer (D.halfLaw (hL i)) (fun x y => D.cutK x y / D.cutZ (hL i)) (r i)
  have hb : 0 < b := by linarith
  have hlow' : ∀ i (f : (O → ZMod (pr i)) → ℝ),
      -(g * (√(pr i : ℝ))⁻¹) * Recentering.nrm (μ' i) f ^ 2 ≤
        kernelForm (μ' i) (μ' i) (K' i) f f := by
    intro i f
    rw [← nrm_comp_map, ← kernelForm_comp_marg]
    exact hlow i f
  have hup' : ∀ i (f : (O → ZMod (pr i)) → ℝ),
      kernelForm (μ' i) (μ' i) (K' i) f f ≤ (1 + B / pr i) * Recentering.nrm (μ' i) f ^ 2 := by
    intro i f
    rw [← nrm_comp_map, ← kernelForm_comp_marg]
    exact hup i f
  have hsym : ∀ i a c, K' i a c = K' i c a := fun i a c =>
    margKer_symm _ _ _ (fun x y => by rw [D.cutK_symm]) a c
  have h := Spectral.tensorcomp_block_supp μ' K' hsym (fun i => (pr i : ℝ)) hg hB hb hbp hgp
    hlow' hup' Ψ
  have hform := pi_kernelForm_comp (fun i => D.halfLaw (hL i))
    (fun i x y => D.cutK x y / D.cutZ (hL i)) r Ψ
  have hn : Recentering.nrm (FiniteLaw.pi fun i => D.halfLaw (hL i)) (Ψ ∘ piRes r) =
      Recentering.nrm (FiniteLaw.pi μ') Ψ := by
    unfold Recentering.nrm Recentering.ip
    exact congrArg Real.sqrt (pi_map_expect (fun i => D.halfLaw (hL i)) r (fun a => Ψ a * Ψ a))
  rw [hform, hn]
  have hprod := UpperReference.prod_one_add_le_exp (fun i => (pr i : ℝ)) hB hX
    (fun i => hXb.trans (hbp i)) hLs
  have hnn : 0 ≤ Recentering.nrm (FiniteLaw.pi μ') Ψ ^ 2 := sq_nonneg _
  have hsb : 0 ≤ (√b)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hcmp : g * (√b)⁻¹ * ∏ i, (1 + B / (pr i : ℝ)) ≤
      g * Real.exp (B * L / (X * Real.log X)) * (√b)⁻¹ := by
    calc g * (√b)⁻¹ * ∏ i, (1 + B / (pr i : ℝ)) ≤
          g * (√b)⁻¹ * Real.exp (B * L / (X * Real.log X)) :=
          mul_le_mul_of_nonneg_left hprod (mul_nonneg hg hsb)
      _ = g * Real.exp (B * L / (X * Real.log X)) * (√b)⁻¹ := by ring
  calc -(g * Real.exp (B * L / (X * Real.log X)) * (√b)⁻¹) *
        Recentering.nrm (FiniteLaw.pi μ') Ψ ^ 2 ≤
      -(g * (√b)⁻¹ * ∏ i, (1 + B / (pr i : ℝ))) * Recentering.nrm (FiniteLaw.pi μ') Ψ ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) hnn
    _ ≤ _ := h

end Block

/-! ## The observed states of the upper bands -/

section States

/-- **The per-prime observed cap** (`prop:observed-caps` at one prime): the cut operator `A_p` of
the layer swap of `G_{f₀f₁,2}`, compressed to the functions of the observed labels `x ∘ ι_O`,
satisfies `-g p^{-1/2} ⪯ A_p^O ⪯ 1 + B/p`. -/
def ObsCutCap (f₀ f₁ : FType) {O : Type} [Fintype O] [DecidableEq O]
    (ιO : O → (upFieldLayer f₀ f₁).cut.Half) (g B : ℝ) (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (hne : (injLabellings (ZMod p) (fieldGraph f₀ f₁ (Fin 2))).Nonempty) (f : (O → ZMod p) → ℝ),
    -(g * (√(p : ℝ))⁻¹) *
        Recentering.nrm ((upFieldLayer f₀ f₁).halfLaw hne) (f ∘ fun x => x ∘ ιO) ^ 2 ≤
        kernelForm ((upFieldLayer f₀ f₁).halfLaw hne) ((upFieldLayer f₀ f₁).halfLaw hne)
          (fun x y => (upFieldLayer f₀ f₁).cutK x y / (upFieldLayer f₀ f₁).cutZ hne)
          (f ∘ fun x => x ∘ ιO) (f ∘ fun x => x ∘ ιO) ∧
      kernelForm ((upFieldLayer f₀ f₁).halfLaw hne) ((upFieldLayer f₀ f₁).halfLaw hne)
          (fun x y => (upFieldLayer f₀ f₁).cutK x y / (upFieldLayer f₀ f₁).cutZ hne)
          (f ∘ fun x => x ∘ ιO) (f ∘ fun x => x ∘ ιO) ≤
        (1 + B / p) * Recentering.nrm ((upFieldLayer f₀ f₁).halfLaw hne) (f ∘ fun x => x ∘ ιO) ^ 2

/-- **The observed-cap certificate of band `k`** for the observed labels `ι_O` of the field pair
`(f₀, f₁)` at the cap `d` (the shape of `UpperBandLayerCap`). *Hypothesis*
(`cert:upper-band-inputs`(b)). -/
def UpperBandObsCap (k : Fin 310) (f₀ f₁ : FType) {O : Type} [Fintype O] [DecidableEq O]
    (ιO : O → (upFieldLayer f₀ f₁).cut.Half) (d : ℝ) : Prop :=
  ∃ g B X : ℝ, 0 ≤ g ∧ 0 ≤ B ∧ 1 < X ∧ X ≤ (bandOf k).1 ∧ g * (√X)⁻¹ < 1 ∧
    g * Real.exp (B * (UpperRecords.CompletionData.record k).budget / (X * Real.log X)) ≤ d ∧
    ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 → (bandOf k).1 ≤ p → p < (bandOf k).2 →
      ObsCutCap f₀ f₁ ιO g B p

/-- **The layer cap of a component that reads only observed labels**, from the band certificate
of the compression: if the slots of the plus half of `ι` read the labels `ι_O ∘ o`, then
`Π ⪰_ι -d b^{-1/2} Diag_ι(Π⁽¹⁾)`. -/
theorem upObsLayerCap (k : Fin 310) {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ)
    [∀ j, Fact (pr j).Prime] (b : ℕ) (h3 : ∀ j, pr j % 4 = 3)
    (hband : ∀ j, (bandOf k).1 ≤ pr j ∧ pr j < (bandOf k).2)
    (hbud : ∑ j, Real.log (pr j) ≤ (UpperRecords.CompletionData.record k).budget)
    (hb : ∀ j, b ≤ pr j) (hb' : ∃ j, pr j = b) (hne : UpperNonempty pr) (f₀ f₁ : FType)
    {O : Type} [Fintype O] [DecidableEq O] (ιO : O → (upFieldLayer f₀ f₁).cut.Half)
    (φ₀ : ZMod 6 → f₀.Obj) (φ₁ : ZMod 6 → f₁.Obj) (o : reservedCut.Half → O)
    (hfac : ∀ v : reservedCut.Half,
      (⟨(φ₀ v.1.1, φ₁ v.1.2.1, 0), (mem_upHalf f₀.Obj f₁.Obj _).mpr rfl⟩ :
        (upFieldLayer f₀ f₁).cut.Half) = ιO (o v))
    (d : ℝ) (hcert : UpperBandObsCap k f₀ f₁ ιO d) :
    reservedCut.Below
      (-(d * (b : ℝ) ^ (-(1 / 2 : ℝ))) •
        signedIntegral (emit (blockGraphLaw pr (fieldGraph f₀ f₁ (Fin 1)) (hne.one f₀ f₁))
          (upDiagEmission φ₀ φ₁)).weight)
      (signedIntegral (emit (blockGraphLaw pr (fieldGraph f₀ f₁ (Fin 2)) (hne.two f₀ f₁))
        (upEmission φ₀ φ₁)).weight) := by
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
  have hbp : ∀ j, (b : ℝ) ≤ pr j := fun j => by exact_mod_cast hb j
  have hcap := fun j => hp (pr j) (h3 j) (hband j).1 (hband j).2 (hne.two f₀ f₁ j)
  set μ := FiniteLaw.pi fun i => (upFieldLayer f₀ f₁).halfLaw (hne.two f₀ f₁ i)
  set K := fun x y : (∀ i, (upFieldLayer f₀ f₁).cut.Half → ZMod (pr i)) =>
    ∏ i, (upFieldLayer f₀ f₁).cutK (x i) (y i) / (upFieldLayer f₀ f₁).cutZ (hne.two f₀ f₁ i)
  set L : ℝ := ((UpperRecords.CompletionData.record k).budget : ℝ)
  set c := g * Real.exp (B * L / (X * Real.log X)) * (√(b : ℝ))⁻¹
  have htwo : ∀ F G : (reservedCut.Half → BlockLabel pr) → ℝ,
      reservedCut.form (signedIntegral (emit (blockGraphLaw pr (fieldGraph f₀ f₁ (Fin 2))
        (hne.two f₀ f₁)) (upEmission φ₀ φ₁)).weight) F G =
        kernelForm μ μ K
          ((F ∘ upSlotRows f₀.Obj f₁.Obj φ₀ φ₁) ∘ blockHalfRows pr (upFieldLayer f₀ f₁))
          ((G ∘ upSlotRows f₀.Obj f₁.Obj φ₀ φ₁) ∘ blockHalfRows pr (upFieldLayer f₀ f₁)) := by
    intro F G
    rw [reservedForm_up_two]
    exact block_cut_expect pr (upFieldLayer f₀ f₁) (hne.two f₀ f₁)
      (F ∘ upSlotRows f₀.Obj f₁.Obj φ₀ φ₁)
      (G ∘ upSlotRows f₀.Obj f₁.Obj φ₀ φ₁)
  have hdiagPos := emit_positive (blockGraphLaw pr (fieldGraph f₀ f₁ (Fin 1)) (hne.one f₀ f₁))
    (upDiagEmission φ₀ φ₁) reservedCut (upDiagEmission_reserved φ₀ φ₁)
  have hK : ∀ x y, K y x = K x y := by
    intro x y
    simp only [K]
    exact Finset.prod_congr rfl fun i _ => by rw [(upFieldLayer f₀ f₁).cutK_symm]
  have hfacF : ∀ F : (reservedCut.Half → BlockLabel pr) → ℝ,
      (F ∘ upSlotRows f₀.Obj f₁.Obj φ₀ φ₁) ∘ blockHalfRows pr (upFieldLayer f₀ f₁) =
        (fun a : (∀ i, O → ZMod (pr i)) => F (fun v i => a i (o v))) ∘
          piRes (fun i (x : (upFieldLayer f₀ f₁).cut.Half → ZMod (pr i)) => x ∘ ιO) := by
    intro F
    funext ξ
    change F (upSlotRows f₀.Obj f₁.Obj φ₀ φ₁ (blockHalfRows pr (upFieldLayer f₀ f₁) ξ)) =
      F (fun v i => ξ i (ιO (o v)))
    congr 1
    funext v i
    change ξ i ⟨(φ₀ v.1.1, φ₁ v.1.2.1, 0), _⟩ = ξ i (ιO (o v))
    rw [hfac v]
  have hc : reservedCut.Below
      (-c • signedIntegral (emit (blockGraphLaw pr (fieldGraph f₀ f₁ (Fin 1)) (hne.one f₀ f₁))
          (upDiagEmission φ₀ φ₁)).weight)
      (signedIntegral (emit (blockGraphLaw pr (fieldGraph f₀ f₁ (Fin 2)) (hne.two f₀ f₁))
        (upEmission φ₀ φ₁)).weight) := by
    constructor
    · intro F G
      change reservedCut.form (signedIntegral (emit (blockGraphLaw pr (fieldGraph f₀ f₁ (Fin 2))
            (hne.two f₀ f₁)) (upEmission φ₀ φ₁)).weight) F G - -c *
            reservedCut.form (signedIntegral (emit (blockGraphLaw pr (fieldGraph f₀ f₁ (Fin 1))
              (hne.one f₀ f₁)) (upDiagEmission φ₀ φ₁)).weight) F G =
        reservedCut.form (signedIntegral (emit (blockGraphLaw pr (fieldGraph f₀ f₁ (Fin 2))
            (hne.two f₀ f₁)) (upEmission φ₀ φ₁)).weight) G F - -c *
            reservedCut.form (signedIntegral (emit (blockGraphLaw pr (fieldGraph f₀ f₁ (Fin 1))
              (hne.one f₀ f₁)) (upDiagEmission φ₀ φ₁)).weight) G F
      rw [htwo, htwo, kernelForm_symm μ K hK, hdiagPos.symmetric F G]
    · intro F
      change 0 ≤ reservedCut.form (signedIntegral (emit (blockGraphLaw pr (fieldGraph f₀ f₁ (Fin 2))
            (hne.two f₀ f₁)) (upEmission φ₀ φ₁)).weight) F F - -c *
            reservedCut.form (signedIntegral (emit (blockGraphLaw pr (fieldGraph f₀ f₁ (Fin 1))
              (hne.one f₀ f₁)) (upDiagEmission φ₀ φ₁)).weight) F F
      have hdiag : reservedCut.form (signedIntegral (emit (blockGraphLaw pr
          (fieldGraph f₀ f₁ (Fin 1)) (hne.one f₀ f₁)) (upDiagEmission φ₀ φ₁)).weight) F F =
          μ.expect (fun ξ =>
            ((F ∘ upSlotRows f₀.Obj f₁.Obj φ₀ φ₁) ∘ blockHalfRows pr (upFieldLayer f₀ f₁)) ξ *
            ((F ∘ upSlotRows f₀.Obj f₁.Obj φ₀ φ₁) ∘ blockHalfRows pr (upFieldLayer f₀ f₁)) ξ) := by
        rw [reservedForm_up_diag,
          pi_expect_equiv (fun i => (upFieldLayer f₀ f₁).halfLaw (hne.two f₀ f₁ i))
          (fun i => graphLaw (fieldGraph f₀ f₁ (Fin 1)) (hne.one f₀ f₁ i))
          (fun i => precomp (upHalfEquiv f₀.Obj f₁.Obj (fieldGraph f₀ f₁ (Fin 2))
            (fieldGraph_upSwap f₀ f₁)) _)
          (fun i y => upHalfLaw_weight f₀.Obj f₁.Obj (fieldGraph f₀ f₁ (Fin 2))
            (fieldGraph_upSwap f₀ f₁) (fieldGraph f₀ f₁ (Fin 1)) (fieldGraph_upRestricts f₀ f₁)
            (hne.two f₀ f₁ i) (hne.one f₀ f₁ i) y)]
        unfold blockGraphLaw
        rw [expect_tensor_eq_sum]
        rfl
      rw [htwo, hdiag]
      have h := obs_block_lower (upFieldLayer f₀ f₁) pr (hne.two f₀ f₁) ιO hg hB hX hXb hbp hbud hgp
        (fun j f => (hcap j f).1) (fun j f => (hcap j f).2)
        (fun a : (∀ i, O → ZMod (pr i)) => F (fun v i => a i (o v)))
      rw [← hfacF F] at h
      have hn : Recentering.nrm μ
            ((F ∘ upSlotRows f₀.Obj f₁.Obj φ₀ φ₁) ∘ blockHalfRows pr (upFieldLayer f₀ f₁)) ^ 2 =
          μ.expect (fun ξ =>
            ((F ∘ upSlotRows f₀.Obj f₁.Obj φ₀ φ₁) ∘ blockHalfRows pr (upFieldLayer f₀ f₁)) ξ *
            ((F ∘ upSlotRows f₀.Obj f₁.Obj φ₀ φ₁) ∘ blockHalfRows pr (upFieldLayer f₀ f₁)) ξ) := by
        unfold Recentering.nrm Recentering.ip
        exact Real.sq_sqrt (μ.expect_nonneg fun ξ => mul_self_nonneg _)
      rw [hn] at h
      linarith
  have hr : 0 ≤ (√(b : ℝ))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  rw [rpow_neg_half_eq]
  exact Reserved.below_mono_coeff reservedCut hdiagPos (mul_le_mul_of_nonneg_right hinf hr) hc

/-- The observed labels of the merge state `LR`: the rows `0, 1` of the `E` coordinate. -/
def obsLR : FType.L.Obj × Fin 2 → (upFieldLayer .L .E).cut.Half :=
  fun a => ⟨(a.1, a.2.castSucc, 0), (mem_upHalf _ _ _).mpr rfl⟩

/-- The observed labels of the constant state `LC`: the row `0` of the `E` coordinate. -/
def obsLC : FType.L.Obj → (upFieldLayer .L .E).cut.Half :=
  fun a => ⟨(a, 0, 0), (mem_upHalf _ _ _).mpr rfl⟩

/-- The observed labels of the merge state `RL` (the `E` coordinate first). -/
def obsRL : Fin 2 × FType.L.Obj → (upFieldLayer .E .L).cut.Half :=
  fun a => ⟨(a.1.castSucc, a.2, 0), (mem_upHalf _ _ _).mpr rfl⟩

/-- The observed labels of the constant state `CL`. -/
def obsCL : FType.L.Obj → (upFieldLayer .E .L).cut.Half :=
  fun a => ⟨(0, a, 0), (mem_upHalf _ _ _).mpr rfl⟩

/-- **The observed-cap certificates of band `k`** (`prop:observed-caps`,
`cert:upper-band-inputs`(b)):
the compressions of the layer cut of `G_{LE,2}` (states `LR`, `LC`) and `G_{EL,2}` (states `RL`,
`CL`, the coordinate exchange) to the merge and the constant labels, at the recorded caps.
*Hypothesis* (per prime, with per-band constants). -/
def UpperObservedCerts (k : Fin 310) : Prop :=
  UpperBandObsCap k .L .E obsLR (UpperRecords.bandCap k .L .R) ∧
    UpperBandObsCap k .E .L obsRL (UpperRecords.bandCap k .R .L) ∧
    UpperBandObsCap k .L .E obsLC (UpperRecords.bandCap k .L .C) ∧
    UpperBandObsCap k .E .L obsCL (UpperRecords.bandCap k .C .L)

/-- **`UpperObservedCaps k` from the observed-cap certificates.** -/
theorem upperObservedCaps_of_certs {k : Fin 310} (h : UpperObservedCerts k) :
    UpperObservedCaps k := by
  intro ι _ _ pr _ b _hinj h3 hband hbud hb hb' hne _ _ t φ hob
  obtain ⟨hLR, hRL, hLC, hCL⟩ := h
  rcases hob with rfl | rfl | rfl | rfl
  · exact upObsLayerCap k pr b h3 hband hbud hb hb' hne .L .E obsLR (PType.L.pat φ.1)
      (PType.R.pat φ.2) (fun v => (v.1.1, merge φ.2.1 φ.2.2 v.1.2.1)) (fun v => rfl) _ hLR
  · exact upObsLayerCap k pr b h3 hband hbud hb hb' hne .E .L obsRL (PType.R.pat φ.1)
      (PType.L.pat φ.2) (fun v => (merge φ.1.1 φ.1.2 v.1.1, v.1.2.1)) (fun v => rfl) _ hRL
  · exact upObsLayerCap k pr b h3 hband hbud hb hb' hne .L .E obsLC (PType.L.pat φ.1)
      (PType.C.pat φ.2) (fun v => v.1.1) (fun v => rfl) _ hLC
  · exact upObsLayerCap k pr b h3 hband hbud hb hb' hne .E .L obsCL (PType.C.pat φ.1)
      (PType.L.pat φ.2) (fun v => v.1.2.1) (fun v => rfl) _ hCL

end States

end Sarkozy.BlockInputs
