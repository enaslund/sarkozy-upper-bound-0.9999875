module

public import Sarkozy.PartV.UpperReference
public import Sarkozy.PartV.MiddleInvariance
public import Sarkozy.PartV.Construction

@[expose] public section

/-!
# The upper reference and the tail laws are invariant under `R_1, R_3, R_5`

`lem:oct24:invariant-background`(ii) and (iii).

`paper/sections/23_envelopes.tex`, `lem:oct24:invariant-background`(ii), with the slot reflections
`R_h(u₀, u₁, ℓ) = (h − u₀, u₁, ℓ)`, `h ∈ {1, 3, 5}`, of `lem:reflection-averaging`
(`slotR`; `R_1, R_3, R_5 = slotG 3, 4, 5` of V1's `MiddleInvariance.lean`, `slotR_eq_slotG`).

**The statement.** For every choice of the state weights `(w_𝔱, v_𝔱)`, the upper reference of
`def:upper-reference` is `R_h`-invariant, and so is every tail law (`def:tail-law`).

**The proof here.** It is direct, component by component, rather than through the slice
principle of the paper's proof; the two arguments use the same facts. `R_h` acts on the first
coordinate only, so the component `Π_{𝔱,φ}` (the image of `λ_{𝔣(𝔱₀)𝔣(𝔱₁)}` under
`e_φ`, `φ = (φ₀, φ₁)`) is carried to the image under `e_{(φ₀ ∘ R_h, φ₁)}` (`emit_slotR`). Then,
type by type of the first coordinate (`typeSum_slotR`, the rows of `tab:reflection` /
`lem:record:fold-identification`(e)):
* `L`: `id ∘ R_h = R_h ∘ id`, and the `L` field laws are invariant under the chamber reflection
  of their first object coordinate (`R_h` is an automorphism of every `G_{L𝔣₁}`,
  `lem:upper-geometry`(b));
* `D`: `R_h` permutes the three folds (`fold_slotR_perm`), so the sum over the folds is unchanged;
* `S`: `E_s ∘ R_h = ψ ∘ E_s` with `ψ` a permutation of `{0, 1, 2}`, and the `E` field laws are
  exchangeable in their first object coordinate (`lem:upper-geometry`(b));
* `R`: `G_{sk} ∘ R_h = G_{s,ψ⁻¹(k)}` (`merge_relabel`), a permutation of the merges of each
  partition;
* `C`: the constants are fixed.
The second coordinate and the layer are untouched, and the two-layer and the one-layer
(diagonal) components are treated alike (`genEmission`). The weights depend only on the state,
so `μ̃` (`upperTilde_slotR_inv`) and `μ` (`upperReference_slotR_inv`) are invariant.

**Hypotheses.** The field-law invariances are a named bundle, `LawsInvariant`, discharged for the
paper's laws from the automorphisms of the graphs `G_{𝔣₀𝔣₁,j}` (`lawsInvariant_of_auto`): the
block laws (`upperBlockReference_slotR_inv`) and the tail laws (`tailLaw_slotR_inv`). As `R_1` and
`R_3` generate `𝒢₆` on the first coordinate, these laws are also `𝒢₆`-invariant there
(`upperReference_slotG_inv`, `tailLaw_slotG_inv`).

**(iii), the prefix laws.** "Every prefix law (`def:clique-law`) is invariant under all
permutations of the first coordinate": given the shared data, the six first-coordinate labels are
independent and identically distributed (`chamberIidLaw_perm_inv`), so the square-clique law
`def:clique-law` is (`baselinePrefixLaw_perm_inv`); the replacement prefix of
`thm:density:iid-prefix` (one independent label per slot) is invariant under every permutation of
the 72 slots (`slotIidLaw_perm_inv`), and the prefix law of the upgraded route is invariant under
every permutation of the first coordinate (`prefixLaw_perm_inv`).

Not formalized here: (iv), the frame records `E_add`, `H`, `G` (V3's `PartVRecords.Frame`), and
(v), the assigned prices.
-/

namespace Sarkozy.PartVLaws

open Finset Sarkozy.Labellings Sarkozy.PartV

/-! ## The slot reflections -/

/-- **The slot reflection** `R_h(u₀, u₁, ℓ) = (h − u₀, u₁, ℓ)` (`lem:reflection-averaging`). -/
def slotR (h : ZMod 6) (v : Slot) : Slot := (chamberRefl h v.1, v.2.1, v.2.2)

/-- `R_1, R_3, R_5` are `slotG 3, 4, 5` of `PartV.MiddleInvariance`. -/
theorem slotR_eq_slotG (v : Slot) :
    slotR 1 v = slotG 3 v ∧ slotR 3 v = slotG 4 v ∧ slotR 5 v = slotG 5 v := by
  obtain ⟨h1, h3, h5⟩ := slotG_reflections v
  refine ⟨?_, ?_, ?_⟩
  · rw [h1]; rfl
  · rw [h3]; rfl
  · rw [h5]; rfl

/-! ## Emissions with a general layer map -/

section Emission

variable {X : Type} [Fintype X] [DecidableEq X] {Λ : Type} [Fintype Λ] [DecidableEq Λ]

/-- The emission `(u₀, u₁, ℓ) ↦ (φ₀(u₀), φ₁(u₁), λ(ℓ))`. With `λ = layerFin` it is the upper
emission `e_φ`, with `λ = 0` its one-layer diagonal copy. -/
def genEmission {O₀ O₁ : Type*} (φ₀ : ZMod 6 → O₀) (φ₁ : ZMod 6 → O₁) (lay : Layer → Λ)
    (v : Slot) : O₀ × O₁ × Λ :=
  (φ₀ v.1, φ₁ v.2.1, lay v.2.2)

theorem upEmission_eq {O₀ O₁ : Type*} (φ₀ : ZMod 6 → O₀) (φ₁ : ZMod 6 → O₁) :
    upEmission φ₀ φ₁ = genEmission φ₀ φ₁ layerFin := rfl

theorem upDiagEmission_eq {O₀ O₁ : Type*} (φ₀ : ZMod 6 → O₀) (φ₁ : ZMod 6 → O₁) :
    upDiagEmission φ₀ φ₁ = genEmission φ₀ φ₁ (fun _ => (0 : Fin 1)) := rfl

/-- **`R_h` acts on the placed laws through the first pattern**: the image under `e_φ` composed
with `R_h` is the image under `e_{(φ₀ ∘ R_h, φ₁)}`. -/
theorem emit_slotR {O₀ O₁ : Type} [Fintype O₀] [DecidableEq O₀] [Fintype O₁] [DecidableEq O₁]
    (μ : FiniteLaw (O₀ × O₁ × Λ → X)) (φ₀ : ZMod 6 → O₀) (φ₁ : ZMod 6 → O₁) (lay : Layer → Λ)
    (h : ZMod 6) (f : (Slot → X) → ℝ) :
    (emit μ (genEmission φ₀ φ₁ lay)).expect (fun z => f (z ∘ slotR h)) =
      (emit μ (genEmission (fun u => φ₀ (chamberRefl h u)) φ₁ lay)).expect f := by
  rw [expect_emit, expect_emit]
  rfl

/-- **An object automorphism of the first coordinate does not change the placed law**: if `μ` is
invariant under `σ` acting on the first object coordinate, then the images under
`e_{(σ ∘ φ₀, φ₁)}` and `e_{(φ₀, φ₁)}` agree. -/
theorem emit_relabel {O₀ O₁ : Type} [Fintype O₀] [DecidableEq O₀] [Fintype O₁] [DecidableEq O₁]
    (μ : FiniteLaw (O₀ × O₁ × Λ → X)) (σ : O₀ → O₀)
    (hμ : ∀ g : (O₀ × O₁ × Λ → X) → ℝ, μ.expect (fun y => g (fun o => y (σ o.1, o.2))) = μ.expect g)
    (φ₀ : ZMod 6 → O₀) (φ₁ : ZMod 6 → O₁) (lay : Layer → Λ) (f : (Slot → X) → ℝ) :
    (emit μ (genEmission (fun u => σ (φ₀ u)) φ₁ lay)).expect f =
      (emit μ (genEmission φ₀ φ₁ lay)).expect f := by
  rw [expect_emit, expect_emit]
  exact hμ (fun y => f (y ∘ genEmission φ₀ φ₁ lay))

end Emission

/-! ## The patterns under `R_h` (`tab:reflection`) -/

/-- The permutation of the folds by `R_h`: `F_j ∘ R_h = F_{π_h(j)}`. -/
def foldPerm (h : ZMod 6) : Equiv.Perm (Fin 3) :=
  if h = 5 then Equiv.swap 1 2 else if h = 3 then Equiv.swap 0 2 else Equiv.swap 0 1

/-- **`R_h` permutes the folds** (`lem:record:fold-identification`(e)): `R_5` fixes `F_0` and
exchanges `F_1, F_2`; `R_3` fixes `F_1`; `R_1` fixes `F_2`. -/
theorem fold_slotR_perm (h : ZMod 6) (hh : h = 1 ∨ h = 3 ∨ h = 5) (j : Fin 3) (u : ZMod 6) :
    Labellings.fold j (chamberRefl h u) = Labellings.fold (foldPerm h j) u := by
  rcases hh with rfl | rfl | rfl <;> revert j u <;> decide

/-! ## Invariance of the field laws, and the type sums -/

section TypeSums

variable {X : Type} [Fintype X] [DecidableEq X] {Λ : Type} [Fintype Λ] [DecidableEq Λ]

/-- **The field-law invariances used by `lem:oct24:invariant-background`(ii)**
(`lem:upper-geometry`(b)), for a family of field laws `μ_{𝔣₀𝔣₁}` on `O_{𝔣₀} × O_{𝔣₁} × Λ`:
* `L`: the laws `μ_{L𝔣₁}` are invariant under the chamber reflections `u ↦ h − u`
  (`h = 1, 3, 5`) of the first object coordinate;
* `E`: the laws `μ_{E𝔣₁}` are invariant under every permutation of the first object coordinate.
For the paper's laws these come from graph automorphisms (`lawsInvariant_of_auto`). -/
structure LawsInvariant (μ : (f₀ f₁ : FType) → FiniteLaw (f₀.Obj × f₁.Obj × Λ → X)) : Prop where
  L : ∀ h : ZMod 6, (h = 1 ∨ h = 3 ∨ h = 5) → ∀ (f₁ : FType)
    (g : (FType.L.Obj × f₁.Obj × Λ → X) → ℝ),
    (μ .L f₁).expect (fun y => g (fun o => y (chamberRefl h o.1, o.2))) = (μ .L f₁).expect g
  E : ∀ (σ : Equiv.Perm (Fin 3)) (f₁ : FType) (g : (FType.E.Obj × f₁.Obj × Λ → X) → ℝ),
    (μ .E f₁).expect (fun y => g (fun o => y (σ o.1, o.2))) = (μ .E f₁).expect g

/-- **The type sums are `R_h`-invariant** (`lem:five-type`(a), `tab:reflection`): for each type
`𝔱₀` of the first coordinate and each pattern `φ₁` of the second, the sum over the patterns
`φ₀ ∈ P_{𝔱₀}` of the placed laws is unchanged by `R_h`. -/
theorem typeSum_slotR (μ : (f₀ f₁ : FType) → FiniteLaw (f₀.Obj × f₁.Obj × Λ → X))
    (hμ : LawsInvariant μ) (lay : Layer → Λ) (h : ZMod 6) (hh : h = 1 ∨ h = 3 ∨ h = 5)
    (t₀ t₁ : PType) (φ₁ : t₁.Pat) (f : (Slot → X) → ℝ) :
    ∑ φ₀ : t₀.Pat, (emit (μ t₀.field t₁.field) (genEmission (t₀.pat φ₀) (t₁.pat φ₁) lay)).expect
        (fun z => f (z ∘ slotR h)) =
      ∑ φ₀ : t₀.Pat,
        (emit (μ t₀.field t₁.field) (genEmission (t₀.pat φ₀) (t₁.pat φ₁) lay)).expect f := by
  simp only [emit_slotR]
  cases t₀ with
  | L =>
    refine Finset.sum_congr rfl fun φ₀ _ => ?_
    exact emit_relabel (μ .L t₁.field) (chamberRefl h) (hμ.L h hh t₁.field) (fun u => u)
      (t₁.pat φ₁) lay f
  | D =>
    change ∑ j : Fin 3, (emit (μ .F t₁.field)
        (genEmission (fun u => Labellings.fold j (chamberRefl h u)) (t₁.pat φ₁) lay)).expect f =
      ∑ j : Fin 3, (emit (μ .F t₁.field)
        (genEmission (Labellings.fold j) (t₁.pat φ₁) lay)).expect f
    have hfun : ∀ j : Fin 3, (fun u => Labellings.fold j (chamberRefl h u)) =
        Labellings.fold (foldPerm h j) :=
      fun j => funext fun u => fold_slotR_perm h hh j u
    simp only [hfun]
    exact Equiv.sum_comp (foldPerm h) (fun j => (emit (μ .F t₁.field)
      (genEmission (Labellings.fold j) (t₁.pat φ₁) lay)).expect f)
  | S =>
    refine Finset.sum_congr rfl fun s _ => ?_
    change (emit (μ .E t₁.field)
        (genEmission (fun u => matching s (chamberRefl h u)) (t₁.pat φ₁) lay)).expect f =
      (emit (μ .E t₁.field) (genEmission (matching s) (t₁.pat φ₁) lay)).expect f
    obtain ⟨ψ, hψ⟩ := (matching_generators s).2 h hh
    have hfun : (fun u => matching s (chamberRefl h u)) = fun u => ψ (matching s u) :=
      funext hψ
    rw [hfun]
    exact emit_relabel (μ .E t₁.field) ψ (hμ.E ψ t₁.field) (matching s) (t₁.pat φ₁) lay f
  | R =>
    change ∑ sk : Fin 2 × Fin 3, (emit (μ .E t₁.field) (genEmission
        (fun u => (merge sk.1 sk.2 (chamberRefl h u)).castSucc) (t₁.pat φ₁) lay)).expect f =
      ∑ sk : Fin 2 × Fin 3, (emit (μ .E t₁.field)
        (genEmission (fun u => (merge sk.1 sk.2 u).castSucc) (t₁.pat φ₁) lay)).expect f
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun s _ => ?_
    obtain ⟨ψ, hψ⟩ := (matching_generators s).2 h hh
    have hfun : ∀ k : Fin 3, (fun u => (merge s k (chamberRefl h u)).castSucc) =
        fun u => (merge s (ψ.symm k) u).castSucc :=
      fun k => funext fun u => by rw [merge_relabel s (chamberRefl h) ψ hψ k u]
    simp only [hfun]
    exact Equiv.sum_comp ψ.symm (fun k => (emit (μ .E t₁.field)
      (genEmission (fun u => (merge s k u).castSucc) (t₁.pat φ₁) lay)).expect f)
  | C =>
    rfl

end TypeSums

/-! ## The upper reference -/

section Upper

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The two-layer field laws of an upper field-law family. -/
def UpperFieldLaws.twoFam (F : UpperFieldLaws X) :
    (f₀ f₁ : FType) → FiniteLaw (f₀.Obj × f₁.Obj × Fin 2 → X) := F.two

/-- The one-layer field laws of an upper field-law family. -/
def UpperFieldLaws.oneFam (F : UpperFieldLaws X) :
    (f₀ f₁ : FType) → FiniteLaw (f₀.Obj × f₁.Obj × Fin 1 → X) := F.one

/-- A sum `∑ c_a E_a` with a constant coefficient depends only on `∑ E_a`. -/
theorem sum_const_mul_congr {α : Type*} [Fintype α] (c E E' : α → ℝ) (hc : ∀ a a', c a = c a')
    (hE : ∑ a, E a = ∑ a, E' a) : ∑ a, c a * E a = ∑ a, c a * E' a := by
  rcases isEmpty_or_nonempty α with hα | ⟨⟨a₀⟩⟩
  · simp
  · have h1 : ∑ a, c a * E a = c a₀ * ∑ a, E a := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by rw [hc a a₀]
    have h2 : ∑ a, c a * E' a = c a₀ * ∑ a, E' a := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by rw [hc a a₀]
    rw [h1, h2, hE]

/-- **The sum over the patterns of the first coordinate, at a fixed state and second pattern, is
`R_h`-invariant**, for the two-layer (`b = true`) and the one-layer (`b = false`) components. -/
theorem upComponent_sum_slotR (F : UpperFieldLaws X) (h2 : LawsInvariant F.two)
    (h1 : LawsInvariant F.one) (h : ZMod 6) (hh : h = 1 ∨ h = 3 ∨ h = 5) (b : Bool)
    (t : PType × PType) (φ₁ : t.2.Pat) (f : (Slot → X) → ℝ) :
    ∑ φ₀ : t.1.Pat, (upComponent F (b, ⟨t, (φ₀, φ₁)⟩)).expect (fun z => f (z ∘ slotR h)) =
      ∑ φ₀ : t.1.Pat, (upComponent F (b, ⟨t, (φ₀, φ₁)⟩)).expect f := by
  cases b
  · exact typeSum_slotR F.one h1 (fun _ => (0 : Fin 1)) h hh t.1 t.2 φ₁ f
  · exact typeSum_slotR F.two h2 layerFin h hh t.1 t.2 φ₁ f

/-- **`lem:oct24:invariant-background`(ii), unnormalized**: for every choice of the state weights,
`μ̃_𝔅` is `R_h`-invariant (`h = 1, 3, 5`), given the field-law invariances. -/
theorem upperTilde_slotR_inv (F : UpperFieldLaws X) (h2 : LawsInvariant F.two)
    (h1 : LawsInvariant F.one) (W : UpperWeights) (r : ℝ) (h : ZMod 6)
    (hh : h = 1 ∨ h = 3 ∨ h = 5) (f : (Slot → X) → ℝ) :
    upperTilde F W r (fun z => f (z ∘ slotR h)) = upperTilde F W r f := by
  unfold upperTilde tildeMeasure
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    ← FiniteLaw.expect_eq_signedIntegral]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Fintype.sum_sigma, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Fintype.sum_prod_type_right, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun φ₁ _ => ?_
  exact sum_const_mul_congr _ _ _ (fun _ _ => by cases b <;> rfl)
    (upComponent_sum_slotR F h2 h1 h hh b t φ₁ f)

/-- **`lem:oct24:invariant-background`(ii)**: for every choice of the state weights, the upper
reference `μ_𝔅 = μ̃_𝔅 / P_μ(r)` is `R_h`-invariant (`h = 1, 3, 5`), given the field-law
invariances `LawsInvariant` (proved for the paper's laws below). -/
theorem upperReference_slotR_inv (F : UpperFieldLaws X) (h2 : LawsInvariant F.two)
    (h1 : LawsInvariant F.one) (W : UpperWeights) {r : ℝ} (hr : 0 ≤ r) (h : ZMod 6)
    (hh : h = 1 ∨ h = 3 ∨ h = 5) (f : (Slot → X) → ℝ) :
    (upperReference F W hr).expect (fun z => f (z ∘ slotR h)) =
      (upperReference F W hr).expect f := by
  rw [FiniteLaw.expect_eq_signedIntegral, FiniteLaw.expect_eq_signedIntegral, upperReference_eq,
    LinearMap.smul_apply, LinearMap.smul_apply, upperTilde_slotR_inv F h2 h1 W r h hh]

/-- `slotG k` as a composition of the reflections `R_1, R_3, R_5`. -/
theorem slotG_eq_comp (k : Fin 6) :
    (∃ h, (h = 1 ∨ h = 3 ∨ h = 5) ∧ ∀ v, slotG k v = slotR h v) ∨
      (∃ h h', (h = 1 ∨ h = 3 ∨ h = 5) ∧ (h' = 1 ∨ h' = 3 ∨ h' = 5) ∧
        ∀ v, slotG k v = slotR h (slotR h' v)) := by
  have key : ∀ k : Fin 6,
      (∃ h : ZMod 6, (h = 1 ∨ h = 3 ∨ h = 5) ∧ ∀ u, FiveType.g6 k u = chamberRefl h u) ∨
      (∃ h h' : ZMod 6, (h = 1 ∨ h = 3 ∨ h = 5) ∧ (h' = 1 ∨ h' = 3 ∨ h' = 5) ∧
        ∀ u, FiveType.g6 k u = chamberRefl h (chamberRefl h' u)) := by
    decide
  rcases key k with ⟨h, hh, hu⟩ | ⟨h, h', hh, hh', hu⟩
  · exact Or.inl ⟨h, hh, fun v => by simp only [slotG, slotR, hu]⟩
  · exact Or.inr ⟨h, h', hh, hh', fun v => by simp only [slotG, slotR, hu]⟩

omit [DecidableEq X] in
/-- **Invariance under `𝒢₆` on the first coordinate** follows from the reflections. -/
theorem slotG_inv_of_slotR {L : FiniteLaw (Slot → X)}
    (hR : ∀ h : ZMod 6, (h = 1 ∨ h = 3 ∨ h = 5) →
      ∀ f : (Slot → X) → ℝ, L.expect (fun z => f (z ∘ slotR h)) = L.expect f)
    (k : Fin 6) (f : (Slot → X) → ℝ) : L.expect (fun z => f (z ∘ slotG k)) = L.expect f := by
  rcases slotG_eq_comp k with ⟨h, hh, hv⟩ | ⟨h, h', hh, hh', hv⟩
  · have : (fun z : Slot → X => f (z ∘ slotG k)) = fun z => f (z ∘ slotR h) := by
      funext z
      congr 1
      funext v
      simp only [Function.comp_apply, hv]
    rw [this, hR h hh f]
  · have : (fun z : Slot → X => f (z ∘ slotG k)) =
        fun z => (fun z' : Slot → X => f (z' ∘ slotR h')) (z ∘ slotR h) := by
      funext z
      congr 1
      funext v
      simp only [Function.comp_apply, hv]
    rw [this, hR h hh (fun z' => f (z' ∘ slotR h')), hR h' hh' f]

/-- **The upper reference is `𝒢₆`-invariant on the first coordinate**, for every choice of the
state weights. -/
theorem upperReference_slotG_inv (F : UpperFieldLaws X) (h2 : LawsInvariant F.two)
    (h1 : LawsInvariant F.one) (W : UpperWeights) {r : ℝ} (hr : 0 ≤ r) (k : Fin 6)
    (f : (Slot → X) → ℝ) :
    (upperReference F W hr).expect (fun z => f (z ∘ slotG k)) =
      (upperReference F W hr).expect f :=
  slotG_inv_of_slotR (fun h hh f' => upperReference_slotR_inv F h2 h1 W hr h hh f') k f

end Upper

/-! ## The paper's laws -/

section Paper

variable {X : Type} [Fintype X] [DecidableEq X] {Λ : Type} [Fintype Λ] [DecidableEq Λ]

omit [DecidableEq X] in
/-- **The field-law invariances from graph automorphisms** (`lem:upper-geometry`(b)): if each
law `μ_{𝔣₀𝔣₁}` is invariant under the automorphisms of `G_{𝔣₀𝔣₁}` on `Λ` layers, then the
chamber reflections of an `L` coordinate and the permutations of an `E` coordinate (both
automorphisms, by `twoLayer_auto`) give `LawsInvariant`. -/
theorem lawsInvariant_of_auto (μ : (f₀ f₁ : FType) → FiniteLaw (f₀.Obj × f₁.Obj × Λ → X))
    (hauto : ∀ (f₀ f₁ : FType) (π : f₀.Obj × f₁.Obj × Λ ≃ f₀.Obj × f₁.Obj × Λ),
      IsAutomorphism (fieldGraph f₀ f₁ Λ) π →
        ∀ g : (f₀.Obj × f₁.Obj × Λ → X) → ℝ, (μ f₀ f₁).expect (fun y => g (y ∘ π)) =
          (μ f₀ f₁).expect g) :
    LawsInvariant μ := by
  refine ⟨fun h hh f₁ g => ?_, fun σ f₁ g => ?_⟩
  · have hπ := twoLayer_auto typeL f₁.rel typeL_proper f₁.rel_proper (chamberReflEquiv h)
      (Equiv.refl f₁.Obj) (Equiv.refl Λ) (typeL_preserves_reflection h hh)
      (fun _ _ => ⟨rfl, rfl⟩)
    exact hauto .L f₁ _ hπ g
  · have hπ := twoLayer_auto typeE f₁.rel typeE_proper f₁.rel_proper σ
      (Equiv.refl f₁.Obj) (Equiv.refl Λ) (typeE_preserves σ) (fun _ _ => ⟨rfl, rfl⟩)
    exact hauto .E f₁ _ hπ g

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- The block field laws satisfy the invariances (two layers). -/
theorem upperBlockFieldLaws_two_inv (hne : UpperNonempty pr) :
    LawsInvariant (upperBlockFieldLaws pr hne).two :=
  lawsInvariant_of_auto _ fun f₀ f₁ π hπ g =>
    blockGraphLaw_expect_auto pr (fieldGraph f₀ f₁ (Fin 2)) (hne.two f₀ f₁) π hπ g

/-- The block field laws satisfy the invariances (one layer). -/
theorem upperBlockFieldLaws_one_inv (hne : UpperNonempty pr) :
    LawsInvariant (upperBlockFieldLaws pr hne).one :=
  lawsInvariant_of_auto _ fun f₀ f₁ π hπ g =>
    blockGraphLaw_expect_auto pr (fieldGraph f₀ f₁ (Fin 1)) (hne.one f₀ f₁) π hπ g

/-- **`lem:oct24:invariant-background`(ii) for the upper blocks**: for every choice of the state
weights, the reference law of an upper block is invariant under `R_1, R_3, R_5`. -/
theorem upperBlockReference_slotR_inv (hne : UpperNonempty pr) (W : UpperWeights) {r : ℝ}
    (hr : 0 ≤ r) (h : ZMod 6) (hh : h = 1 ∨ h = 3 ∨ h = 5) (f : (Slot → BlockLabel pr) → ℝ) :
    (upperBlockReference pr hne W hr).expect (fun z => f (z ∘ slotR h)) =
      (upperBlockReference pr hne W hr).expect f :=
  upperReference_slotR_inv _ (upperBlockFieldLaws_two_inv pr hne)
    (upperBlockFieldLaws_one_inv pr hne) W hr h hh f

/-- The upper block law is `𝒢₆`-invariant on the first coordinate. -/
theorem upperBlockReference_slotG_inv (hne : UpperNonempty pr) (W : UpperWeights) {r : ℝ}
    (hr : 0 ≤ r) (k : Fin 6) (f : (Slot → BlockLabel pr) → ℝ) :
    (upperBlockReference pr hne W hr).expect (fun z => f (z ∘ slotG k)) =
      (upperBlockReference pr hne W hr).expect f :=
  upperReference_slotG_inv _ (upperBlockFieldLaws_two_inv pr hne)
    (upperBlockFieldLaws_one_inv pr hne) W hr k f

end Paper

section Tail

variable (p : ℕ) [Fact p.Prime]

/-- The tail field laws satisfy the invariances (two layers). -/
theorem tailFieldLaws_two_inv (hne : TailNonempty p) : LawsInvariant (tailFieldLaws p hne).two :=
  lawsInvariant_of_auto _ fun f₀ f₁ π hπ g =>
    graphLaw_expect_comp (fieldGraph f₀ f₁ (Fin 2)) (hne.two f₀ f₁) π hπ g

/-- The tail field laws satisfy the invariances (one layer). -/
theorem tailFieldLaws_one_inv (hne : TailNonempty p) : LawsInvariant (tailFieldLaws p hne).one :=
  lawsInvariant_of_auto _ fun f₀ f₁ π hπ g =>
    graphLaw_expect_comp (fieldGraph f₀ f₁ (Fin 1)) (hne.one f₀ f₁) π hπ g

/-- **`lem:oct24:invariant-background`(ii) for the tail laws**: every tail law is invariant under
`R_1, R_3, R_5`. -/
theorem tailLaw_slotR_inv (hne : TailNonempty p) (h : ZMod 6) (hh : h = 1 ∨ h = 3 ∨ h = 5)
    (f : (Slot → ZMod p) → ℝ) :
    (tailLaw p hne).expect (fun z => f (z ∘ slotR h)) = (tailLaw p hne).expect f :=
  upperReference_slotR_inv _ (tailFieldLaws_two_inv p hne) (tailFieldLaws_one_inv p hne)
    tailWeights (tailR_nonneg p) h hh f

/-- Every tail law is `𝒢₆`-invariant on the first coordinate. -/
theorem tailLaw_slotG_inv (hne : TailNonempty p) (k : Fin 6) (f : (Slot → ZMod p) → ℝ) :
    (tailLaw p hne).expect (fun z => f (z ∘ slotG k)) = (tailLaw p hne).expect f :=
  upperReference_slotG_inv _ (tailFieldLaws_two_inv p hne) (tailFieldLaws_one_inv p hne)
    tailWeights (tailR_nonneg p) k f

end Tail

/-! ## (iii): the prefix laws -/

section Prefix

variable {Ω X : Type*} [Fintype Ω] [Fintype X] [DecidableEq X]

/-- The action of a permutation `σ` of the first chamber coordinate on the slots. -/
def slotPerm (σ : Equiv.Perm Chamber) (v : Slot) : Slot := (σ v.1, v.2.1, v.2.2)

/-- Precomposition with a bijection, as a bijection of labellings. -/
def precompEquiv {A : Type*} (σ : Equiv.Perm A) : (A → X) ≃ (A → X) where
  toFun y := y ∘ σ
  invFun y := y ∘ σ.symm
  left_inv y := by funext a; simp
  right_inv y := by funext a; simp

/-- **Independent labels per first chamber, given shared data, are invariant under every
permutation of the first coordinate.** -/
theorem chamberIidLaw_perm_inv (w : FiniteLaw Ω) (ν : Ω → FiniteLaw X) (σ : Equiv.Perm Chamber)
    (f : (Slot → X) → ℝ) :
    (chamberIidLaw w ν).expect (fun z => f (z ∘ slotPerm σ)) = (chamberIidLaw w ν).expect f := by
  rw [expect_chamberIidLaw, expect_chamberIidLaw]
  refine sum_congr rfl fun ω _ => ?_
  congr 1
  refine Fintype.sum_equiv (precompEquiv σ) _ _ fun y => ?_
  change (∏ i, (ν ω).weight (y i)) * f (y ∘ firstChamber ∘ slotPerm σ) =
    (∏ i, (ν ω).weight (y (σ i))) * f ((y ∘ σ) ∘ firstChamber)
  rw [Equiv.prod_comp σ (fun i => (ν ω).weight (y i))]
  rfl

/-- **Independent labels per slot, given shared data, are invariant under every permutation of
the slots.** -/
theorem slotIidLaw_perm_inv (w : FiniteLaw Ω) (ν : Ω → FiniteLaw X) (π : Equiv.Perm Slot)
    (f : (Slot → X) → ℝ) :
    (slotIidLaw w ν).expect (fun z => f (z ∘ π)) = (slotIidLaw w ν).expect f := by
  rw [expect_slotIidLaw, expect_slotIidLaw]
  refine sum_congr rfl fun ω _ => ?_
  congr 1
  refine Fintype.sum_equiv (precompEquiv π) _ _ fun y => ?_
  change (∏ v, (ν ω).weight (y v)) * f (y ∘ π) = (∏ v, (ν ω).weight (y (π v))) * f (y ∘ π)
  rw [Equiv.prod_comp π (fun v => (ν ω).weight (y v))]

/-- The first-coordinate permutation of the slots, as a bijection. -/
def slotPermEquiv (σ : Equiv.Perm Chamber) : Equiv.Perm Slot :=
  σ.prodCongr (Equiv.refl _)

end Prefix

section PrefixPaper

variable (p : ℕ) [Fact p.Prime]

/-- **`lem:oct24:invariant-background`(iii) for the square-clique law** (`def:clique-law`): it is
invariant under every permutation of the first coordinate. -/
theorem baselinePrefixLaw_perm_inv (σ : Equiv.Perm Chamber)
    (f : (Slot → ZMod (p ^ (2 * digitPairs))) → ℝ) :
    (baselinePrefixLaw p).expect (fun z => f (z ∘ slotPerm σ)) =
      (baselinePrefixLaw p).expect f := by
  unfold baselinePrefixLaw cliqueLaw affineChamberLaw
  exact chamberIidLaw_perm_inv _ _ σ f

/-- **The replacement prefix law of `thm:density:iid-prefix` is invariant under every
permutation of the 72 slots.** -/
theorem cliqueIidLaw_perm_inv (ℓ : ℕ) (π : Equiv.Perm Slot) (f : (Slot → ZMod (p ^ (2 * ℓ))) → ℝ) :
    (cliqueIidLaw p ℓ).expect (fun z => f (z ∘ π)) = (cliqueIidLaw p ℓ).expect f := by
  unfold cliqueIidLaw affineSlotLaw
  exact slotIidLaw_perm_inv _ _ π f

/-- **`lem:oct24:invariant-background`(iii) for the prefix law of the upgraded route**
(`thm:density:iid-prefix`): invariant under every permutation of the first coordinate. -/
theorem prefixLaw_perm_inv (σ : Equiv.Perm Chamber)
    (f : (Slot → ZMod (p ^ (2 * digitPairs))) → ℝ) :
    (prefixLaw p).expect (fun z => f (z ∘ slotPerm σ)) = (prefixLaw p).expect f := by
  unfold prefixLaw
  split_ifs
  · exact cliqueIidLaw_perm_inv p digitPairs (slotPermEquiv σ) f
  · exact baselinePrefixLaw_perm_inv p σ f

end PrefixPaper

end Sarkozy.PartVLaws
