module

public import Sarkozy.PartV.MiddleReference
public import Mathlib.NumberTheory.Real.Irrational

@[expose] public section

/-!
# The positive roots (`def:positive-root`, `lem:positive-root-properties`)

`paper/sections/20b_positive_roots.tex`, `def:positive-root`, `lem:positive-root-properties`;
`paper/sections/20b_selected_refinements.tex`, `lem:imp:coherent39-law`.

On the seven middle pieces from `2³⁰` the two-layer root is a positive reweighting of the uniform
twelve-label law `λ_p(G_{L,2})`:
* **individual squares** (six pieces): `Γ_{p,u} = (w_u / E w_u) λ_p(G_{L,2})`,
  `w_u = (1/3) ∑_{j=0}^{2} (1 + u H_j)²`,
  `H_j(x) = r ∑_{z ∈ 𝔽_p} χ(∏_{u ∈ {j, j+3}} ∏_ℓ (z - x_{u,ℓ}))`
  the normalized trace score of the opposite base pair `{j, j+3}` (`individualRoot`);
* **coherent** (the piece `[2⁴⁵, P₃)`): `Γ_{p,u} ∝ (η + (1 + u H_𝒟)²) λ_p(G_{L,2})`, `η = 1/100`,
  `H_𝒟 = (1/r) ∑_{D ∈ 𝒟} c_D E_s ∏_{i ∈ D} χ(s - x_i)` (`eq:merge-local-I-21`), for a dictionary
  `𝒟` of supports with coefficients (`coherentRoot`). The paper's dictionary `𝒟₃₉` is produced
  by the procedure of `imp:local:filtered-coherent` and is **not** entered here: `coherentRoot`
  takes the dictionary as a parameter.

On a block, `Γ_{𝔅,u} = ⊗_{p ∈ 𝔅} Γ_{p,u}` (`individualBlockRoot`).

Proved:
* `w_u > 0` everywhere for rational `u` (`individualWeight_pos`, the argument of
  `lem:positive-root-properties`(a): `1 + u H_j = 0` with `H_j ∈ r ℤ` would make `√p`
  rational), so `Γ_{p,u}` is a probability law with exactly the support of `λ_p(G_{L,2})`
  (`tiltLaw_weight_ne_zero_iff`); the coherent weight is `≥ η > 0`;
* the scores are invariant under translation of all labels (`rootTrace_translate`), hence
  `Γ_{p,u}` and `Γ_{𝔅,u}` have uniform vertex marginals (`individualRoot_vertex_uniform`,
  `individualBlockRoot_vertex_uniform`: the "every slot is uniform" of (b)); so the middle
  reference with a positive root has uniform one-slot marginals
  (`middleBlockReference_individual_uniform`).

The invariance under `𝒢₆` (the chamber reflections and the translation `u ↦ u + 2`), the layer
swap and the full square-affine maps of (b) are proved in `PositiveRootRP`, `LayerSwap` and
`RootAffine`. Not proved: the chamber pairing (c), and every cap of the positive roots (the
chamber and layer propositions and the certificate of section 20b).

Convention: `r = 1/√p`, which is the paper's `p^{-1/2}`.
-/

namespace Sarkozy.PartV

open Finset Sarkozy.Labellings

/-! ## Tilted laws -/

section Tilt

variable {Ω : Type*} [Fintype Ω]

/-- **A tilted law** `(w / E_λ w) λ` for a nonnegative weight `w` with `E_λ w > 0`. -/
noncomputable def tiltLaw (lam : FiniteLaw Ω) (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hpos : 0 < lam.expect w) : FiniteLaw Ω where
  weight ω := lam.weight ω * w ω / lam.expect w
  nonneg ω := div_nonneg (mul_nonneg (lam.nonneg ω) (hw ω)) hpos.le
  total := by
    rw [← sum_div]
    exact div_self hpos.ne'

/-- **The tilted law has the support of `λ`** when the weight is positive everywhere. -/
theorem tiltLaw_weight_ne_zero_iff (lam : FiniteLaw Ω) (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hpos : 0 < lam.expect w) (hw' : ∀ ω, 0 < w ω) (ω : Ω) :
    (tiltLaw lam w hw hpos).weight ω ≠ 0 ↔ lam.weight ω ≠ 0 := by
  change lam.weight ω * w ω / lam.expect w ≠ 0 ↔ _
  rw [div_ne_zero_iff, mul_ne_zero_iff]
  exact ⟨fun h => h.1.1, fun h => ⟨⟨h, (hw' ω).ne'⟩, hpos.ne'⟩⟩

/-- A positive weight has positive mean under a probability law. -/
theorem expect_pos_of_pos (lam : FiniteLaw Ω) {w : Ω → ℝ} (hw : ∀ ω, 0 < w ω) :
    0 < lam.expect w := by
  have h1 : ∑ ω : Ω, (0 : ℝ) < ∑ ω, lam.weight ω := by rw [lam.total]; simp
  obtain ⟨ω, -, hω⟩ := Finset.exists_lt_of_sum_lt h1
  unfold FiniteLaw.expect
  exact Finset.sum_pos' (fun x _ => mul_nonneg (lam.nonneg x) (hw x).le)
    ⟨ω, mem_univ _, mul_pos hω (hw ω)⟩

end Tilt

/-! ## Uniform vertex marginals from translation invariance -/

section Translation

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
/-- **A law on labellings whose weight is invariant under every translation of all labels has
uniform vertex marginals** (`lem:marginals`). -/
theorem vertex_uniform_of_translation (lam : FiniteLaw (W → F))
    (htr : ∀ (c : F) (z : W → F), lam.weight (fun w => z w + c) = lam.weight z) (w : W)
    (f : F → ℝ) : lam.expect (fun z => f (z w)) = (FiniteLaw.uniform F).expect f := by
  have hshift : ∀ c : F, lam.expect (fun z => f (z w + c)) = lam.expect (fun z => f (z w)) := by
    intro c
    let T : (W → F) ≃ (W → F) := Equiv.piCongrRight fun _ => Equiv.addRight c
    unfold FiniteLaw.expect
    calc ∑ z, lam.weight z * f (z w + c) = ∑ z, lam.weight (T z) * f (T z w) :=
          sum_congr rfl fun z _ => by rw [show lam.weight (T z) = lam.weight z from htr c z]; rfl
      _ = ∑ z, lam.weight z * f (z w) := Fintype.sum_equiv T _ (fun z => lam.weight z * f (z w))
          fun _ => rfl
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hsum : ∑ c : F, lam.expect (fun z => f (z w + c)) =
      lam.expect (fun _ => ∑ y : F, f y) := by
    unfold FiniteLaw.expect
    rw [sum_comm]
    refine sum_congr rfl fun z _ => ?_
    rw [← mul_sum]
    congr 1
    exact Fintype.sum_equiv (Equiv.addLeft (z w)) _ _ fun _ => rfl
  rw [sum_congr rfl fun c _ => hshift c, sum_const, card_univ, nsmul_eq_mul,
    FiniteLaw.expect_const] at hsum
  rw [FiniteLaw.expect_uniform]
  field_simp
  linarith [hsum]

/-- The graph law's weight is invariant under translations. -/
theorem graphLaw_weight_translate (G : OrientedGraph W) (hne : (injLabellings F G).Nonempty)
    (c : F) (z : W → F) :
    (graphLaw G hne).weight (fun w => z w + c) = (graphLaw G hne).weight z := by
  have hmem : (fun w => z w + c) ∈ injLabellings F G ↔ z ∈ injLabellings F G := by
    rw [mem_injLabellings_iff_feasible, mem_injLabellings_iff_feasible]
    have h := feasible_affine_iff G (α := 1) (by simp) c z
    simpa only [one_mul] using h
  simp only [graphLaw, hmem]

end Translation

/-! ## Tensor products with translation-invariant factors -/

section TensorTranslation

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- **A tensor of translation-invariant laws has uniform vertex marginals on `X_𝔅`.** -/
theorem tensor_vertex_uniform_of_translation (μ : ∀ i, FiniteLaw (W → ZMod (pr i)))
    (htr : ∀ i (c : ZMod (pr i)) (z : W → ZMod (pr i)),
      (μ i).weight (fun w => z w + c) = (μ i).weight z) (w : W) (f : BlockLabel pr → ℝ) :
    (FiniteLaw.tensor μ).expect (fun z => f (z w)) =
      (FiniteLaw.uniform (BlockLabel pr)).expect f := by
  have hshift : ∀ c : BlockLabel pr, (FiniteLaw.tensor μ).expect (fun z => f (z w + c)) =
      (FiniteLaw.tensor μ).expect (fun z => f (z w)) := by
    intro c
    let T : ∀ i, (W → ZMod (pr i)) ≃ (W → ZMod (pr i)) := fun i =>
      Equiv.piCongrRight fun _ => Equiv.addRight (c i)
    exact expect_tensor_comp μ T (fun i y => htr i (c i) y) (fun z => f (z w))
  have hq : (0 : ℝ) < Fintype.card (BlockLabel pr) := by exact_mod_cast Fintype.card_pos
  have hsum : ∑ c : BlockLabel pr, (FiniteLaw.tensor μ).expect (fun z => f (z w + c)) =
      (FiniteLaw.tensor μ).expect (fun _ => ∑ y : BlockLabel pr, f y) := by
    unfold FiniteLaw.expect
    rw [sum_comm]
    refine sum_congr rfl fun z _ => ?_
    rw [← mul_sum]
    congr 1
    exact Fintype.sum_equiv (Equiv.addLeft (z w)) _ _ fun _ => rfl
  rw [sum_congr rfl fun c _ => hshift c, sum_const, card_univ, nsmul_eq_mul,
    FiniteLaw.expect_const] at hsum
  rw [FiniteLaw.expect_uniform]
  field_simp
  linarith [hsum]

end TensorTranslation

/-! ## The individual-square positive root (`eq:positive-root`) -/

section Individual

variable (p : ℕ) [Fact p.Prime]

/-- The four labels of the opposite base pair `{j, j+3}` in the two layers. -/
def basePair (j : Fin 3) : Finset (ZMod 6 × Fin 2) :=
  {((j.val : ZMod 6), 0), ((j.val : ZMod 6), 1), ((j.val : ZMod 6) + 3, 0),
    ((j.val : ZMod 6) + 3, 1)}

/-- The integer trace `∑_{z ∈ 𝔽_p} χ(∏_{v ∈ {j, j+3} × {0,1}} (z - x_v))`. -/
noncomputable def rootTrace (j : Fin 3) (x : ZMod 6 × Fin 2 → ZMod p) : ℤ :=
  ∑ z : ZMod p, quadraticChar (ZMod p) (∏ v ∈ basePair j, (z - x v))

/-- **The normalized trace score** `H_j(x) = r · rootTrace`, `r = 1/√p`. -/
noncomputable def rootScore (j : Fin 3) (x : ZMod 6 × Fin 2 → ZMod p) : ℝ :=
  (rootTrace p j x : ℝ) / Real.sqrt p

/-- **The individual-square weight** `w_u = (1/3) ∑_j (1 + u H_j)²`. -/
noncomputable def individualWeight (u : ℚ) (x : ZMod 6 × Fin 2 → ZMod p) : ℝ :=
  (1 / 3) * ∑ j : Fin 3, (1 + (u : ℝ) * rootScore p j x) ^ 2

/-- **The scores are invariant under translation of all labels** (substitute `z ↦ z + c`). -/
theorem rootTrace_translate (j : Fin 3) (x : ZMod 6 × Fin 2 → ZMod p) (c : ZMod p) :
    rootTrace p j (fun v => x v + c) = rootTrace p j x := by
  unfold rootTrace
  refine Fintype.sum_equiv (Equiv.subRight c) _ _ fun z => ?_
  congr 1
  refine prod_congr rfl fun v _ => ?_
  simp only [Equiv.subRight_apply]
  ring

/-- `1 + u n / √p ≠ 0` for rational `u` and integer `n`: otherwise `√p` would be rational. -/
theorem one_add_ne_zero (u : ℚ) (n : ℤ) : (1 : ℝ) + (u : ℝ) * ((n : ℝ) / Real.sqrt p) ≠ 0 := by
  intro h
  have hp : (p.Prime) := Fact.out
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)
  have h' : Real.sqrt p = ((-(u * n) : ℚ) : ℝ) := by
    push_cast
    field_simp at h
    linarith
  exact hp.irrational_sqrt ⟨-(u * n), h'.symm⟩

/-- **`w_u > 0` everywhere** (`lem:positive-root-properties`(a)). -/
theorem individualWeight_pos (u : ℚ) (x : ZMod 6 × Fin 2 → ZMod p) :
    0 < individualWeight p u x := by
  unfold individualWeight
  refine mul_pos (by norm_num) (Finset.sum_pos (fun j _ => ?_) univ_nonempty)
  have h : (1 : ℝ) + (u : ℝ) * rootScore p j x ≠ 0 := by
    unfold rootScore
    exact one_add_ne_zero p u _
  exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h))

/-- **The individual-square positive root** `Γ_{p,u}` (`eq:positive-root`), for rational `u`,
over the uniform twelve-label law `λ_p(G_{L,2})`. -/
noncomputable def individualRoot (u : ℚ)
    (hne : (injLabellings (ZMod p) (recordGraph (Fin 2))).Nonempty) :
    FiniteLaw (ZMod 6 × Fin 2 → ZMod p) :=
  tiltLaw (graphLaw (recordGraph (Fin 2)) hne) (individualWeight p u)
    (fun x => (individualWeight_pos p u x).le)
    (expect_pos_of_pos _ (individualWeight_pos p u))

/-- `Γ_{p,u}` has the support of `λ_p(G_{L,2})`; in particular it accepts the six queries. -/
theorem individualRoot_support (u : ℚ)
    (hne : (injLabellings (ZMod p) (recordGraph (Fin 2))).Nonempty)
    (x : ZMod 6 × Fin 2 → ZMod p) :
    (individualRoot p u hne).weight x ≠ 0 ↔ (graphLaw (recordGraph (Fin 2)) hne).weight x ≠ 0 :=
  tiltLaw_weight_ne_zero_iff _ _ _ _ (individualWeight_pos p u) x

theorem individualWeight_translate (u : ℚ) (x : ZMod 6 × Fin 2 → ZMod p) (c : ZMod p) :
    individualWeight p u (fun v => x v + c) = individualWeight p u x := by
  unfold individualWeight rootScore
  simp only [rootTrace_translate]

theorem individualRoot_weight_translate (u : ℚ)
    (hne : (injLabellings (ZMod p) (recordGraph (Fin 2))).Nonempty) (c : ZMod p)
    (x : ZMod 6 × Fin 2 → ZMod p) :
    (individualRoot p u hne).weight (fun v => x v + c) = (individualRoot p u hne).weight x := by
  change (graphLaw _ hne).weight (fun v => x v + c) * individualWeight p u (fun v => x v + c) /
      _ = (graphLaw _ hne).weight x * individualWeight p u x / _
  rw [graphLaw_weight_translate, individualWeight_translate]

/-- **Every vertex marginal of `Γ_{p,u}` is uniform** (`lem:positive-root-properties`(b)). -/
theorem individualRoot_vertex_uniform (u : ℚ)
    (hne : (injLabellings (ZMod p) (recordGraph (Fin 2))).Nonempty) (o : ZMod 6 × Fin 2)
    (f : ZMod p → ℝ) :
    (individualRoot p u hne).expect (fun z => f (z o)) = (FiniteLaw.uniform (ZMod p)).expect f :=
  vertex_uniform_of_translation _ (fun c z => individualRoot_weight_translate p u hne c z) o f

end Individual

/-! ## The coherent root (`lem:imp:coherent39-law`), for a given dictionary -/

section Coherent

variable (p : ℕ) [Fact p.Prime]

/-- A dictionary: a finite list of supports `D ⊆ ℤ/6ℤ × {0, 1}` with rational coefficients `c_D`. -/
abbrev Dictionary : Type := List (Finset (ZMod 6 × Fin 2) × ℚ)

/-- **The coherent score** `H_𝒟 = (1/r) ∑_D c_D E_s ∏_{i ∈ D} χ(s - x_i)` (`eq:merge-local-I-21`),
`r = 1/√p`, `E_s` the average over `s ∈ 𝔽_p`. -/
noncomputable def coherentScore (D : Dictionary) (x : ZMod 6 × Fin 2 → ZMod p) : ℝ :=
  Real.sqrt p * (D.map fun Sc => (Sc.2 : ℝ) *
    ((∑ s : ZMod p, ∏ i ∈ Sc.1, (quadraticChar (ZMod p) (s - x i) : ℝ)) / p)).sum

/-- **The coherent weight** `η + (1 + u H_𝒟)²`. -/
noncomputable def coherentWeight (D : Dictionary) (u η : ℚ) (x : ZMod 6 × Fin 2 → ZMod p) : ℝ :=
  (η : ℝ) + (1 + (u : ℝ) * coherentScore p D x) ^ 2

theorem coherentWeight_pos (D : Dictionary) (u : ℚ) {η : ℚ} (hη : 0 < η)
    (x : ZMod 6 × Fin 2 → ZMod p) : 0 < coherentWeight p D u η x := by
  unfold coherentWeight
  have : (0 : ℝ) < η := by exact_mod_cast hη
  positivity

/-- **The coherent root** for a dictionary `𝒟`, parameter `u` and floor `η > 0`: the uniform
twelve-label law reweighted by `η + (1 + u H_𝒟)²` and normalized. The paper uses
`𝒟 = 𝒟₃₉` (not entered here), `u = 67/40`, `η = 1/100`. -/
noncomputable def coherentRoot (D : Dictionary) (u : ℚ) {η : ℚ} (hη : 0 < η)
    (hne : (injLabellings (ZMod p) (recordGraph (Fin 2))).Nonempty) :
    FiniteLaw (ZMod 6 × Fin 2 → ZMod p) :=
  tiltLaw (graphLaw (recordGraph (Fin 2)) hne) (coherentWeight p D u η)
    (fun x => (coherentWeight_pos p D u hη x).le)
    (expect_pos_of_pos _ (coherentWeight_pos p D u hη))

/-- The coherent score is invariant under translation of all labels (`lem:imp:coherent39-law`). -/
theorem coherentScore_translate (D : Dictionary) (x : ZMod 6 × Fin 2 → ZMod p) (c : ZMod p) :
    coherentScore p D (fun v => x v + c) = coherentScore p D x := by
  unfold coherentScore
  congr 2
  refine List.map_congr_left fun Sc _ => ?_
  congr 2
  refine Fintype.sum_equiv (Equiv.subRight c) _ _ fun s => ?_
  refine prod_congr rfl fun i _ => ?_
  simp only [Equiv.subRight_apply]
  congr 2
  ring

theorem coherentRoot_weight_translate (D : Dictionary) (u : ℚ) {η : ℚ} (hη : 0 < η)
    (hne : (injLabellings (ZMod p) (recordGraph (Fin 2))).Nonempty) (c : ZMod p)
    (x : ZMod 6 × Fin 2 → ZMod p) :
    (coherentRoot p D u hη hne).weight (fun v => x v + c) =
      (coherentRoot p D u hη hne).weight x := by
  change (graphLaw _ hne).weight (fun v => x v + c) * coherentWeight p D u η (fun v => x v + c) /
      _ = (graphLaw _ hne).weight x * coherentWeight p D u η x / _
  rw [graphLaw_weight_translate]
  unfold coherentWeight
  rw [coherentScore_translate]

/-- **Every vertex marginal of the coherent root is uniform** (`lem:imp:coherent39-law`: "every
slot is uniform"). -/
theorem coherentRoot_vertex_uniform (D : Dictionary) (u : ℚ) {η : ℚ} (hη : 0 < η)
    (hne : (injLabellings (ZMod p) (recordGraph (Fin 2))).Nonempty) (o : ZMod 6 × Fin 2)
    (f : ZMod p → ℝ) :
    (coherentRoot p D u hη hne).expect (fun z => f (z o)) = (FiniteLaw.uniform (ZMod p)).expect f :=
  vertex_uniform_of_translation _ (fun c z => coherentRoot_weight_translate p D u hη hne c z) o f

/-- The coherent root has the support of the uniform root. -/
theorem coherentRoot_support (D : Dictionary) (u : ℚ) {η : ℚ} (hη : 0 < η)
    (hne : (injLabellings (ZMod p) (recordGraph (Fin 2))).Nonempty)
    (x : ZMod 6 × Fin 2 → ZMod p) :
    (coherentRoot p D u hη hne).weight x ≠ 0 ↔ (graphLaw (recordGraph (Fin 2)) hne).weight x ≠ 0 :=
  tiltLaw_weight_ne_zero_iff _ _ _ _ (coherentWeight_pos p D u hη) x

end Coherent

/-! ## Block roots and the middle reference with a positive root -/

section Block

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- **The block positive root** `Γ_{𝔅,u} = ⊗_{p ∈ 𝔅} Γ_{p,u}`. -/
noncomputable def individualBlockRoot (u : ℚ)
    (hne : ∀ i, (injLabellings (ZMod (pr i)) (recordGraph (Fin 2))).Nonempty) :
    FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr) :=
  FiniteLaw.tensor fun i => individualRoot (pr i) u (hne i)

theorem individualBlockRoot_vertex_uniform (u : ℚ)
    (hne : ∀ i, (injLabellings (ZMod (pr i)) (recordGraph (Fin 2))).Nonempty)
    (o : ZMod 6 × Fin 2) (f : BlockLabel pr → ℝ) :
    (individualBlockRoot pr u hne).expect (fun z => f (z o)) =
      (FiniteLaw.uniform (BlockLabel pr)).expect f :=
  tensor_vertex_uniform_of_translation pr _
    (fun i c z => individualRoot_weight_translate (pr i) u (hne i) c z) o f

/-- **The block coherent root** `⊗_{p ∈ 𝔅} Γ_{p,u}` for a dictionary `𝒟`. -/
noncomputable def coherentBlockRoot (D : Dictionary) (u : ℚ) {η : ℚ} (hη : 0 < η)
    (hne : ∀ i, (injLabellings (ZMod (pr i)) (recordGraph (Fin 2))).Nonempty) :
    FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr) :=
  FiniteLaw.tensor fun i => coherentRoot (pr i) D u hη (hne i)

theorem coherentBlockRoot_vertex_uniform (D : Dictionary) (u : ℚ) {η : ℚ} (hη : 0 < η)
    (hne : ∀ i, (injLabellings (ZMod (pr i)) (recordGraph (Fin 2))).Nonempty)
    (o : ZMod 6 × Fin 2) (f : BlockLabel pr → ℝ) :
    (coherentBlockRoot pr D u hη hne).expect (fun z => f (z o)) =
      (FiniteLaw.uniform (BlockLabel pr)).expect f :=
  tensor_vertex_uniform_of_translation pr _
    (fun i c z => coherentRoot_weight_translate (pr i) D u hη (hne i) c z) o f

/-- **The middle reference with the individual-square root has uniform one-slot marginals**
(`lem:front12:reference`(iii) on the six pieces from `2³⁰` to `2⁴⁰`). -/
theorem middleBlockReference_individual_uniform (hne : MiddleNonempty pr) (u : ℚ)
    (W : MiddleWeights) {r : ℝ} (hr : 0 ≤ r) :
    HasUniformMarginals (middleBlockReference pr hne (individualBlockRoot pr u hne.L2) W hr) :=
  middleBlockReference_uniform pr hne _ (individualBlockRoot_vertex_uniform pr u hne.L2) W hr

end Block

end Sarkozy.PartV
