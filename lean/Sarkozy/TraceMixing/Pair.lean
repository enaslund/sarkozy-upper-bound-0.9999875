module

public import Sarkozy.TraceMixing.PairTrace
public import Sarkozy.TraceMixing.Slot

/-!
# A pair of a graph law (`lem:trace-mixing`(b))

`paper/sections/12_labellings.tex`, `lem:trace-mixing`(b), for the graph law `λ = λ_p(G)` and
an edge `(u, v)`. `pairJoint λ u v` is the joint law of `((z_u, z_v), z_{W'})`,
`W' = W ∖ {u, v}`; its conditional operator is `T_{uv}` of the paper.

* `pairJoint_weight`: the weight of `((x, x'), r)` is `λ(z)` for the labelling `z` with
  `z_u = x`, `z_v = x'`, `z|_{W'} = r` (`pairCombine`).
* `pairJoint_supp`, `pairJoint_translate`, `pairJoint_dilate`: the pair is a strict-square
  pair, and the law is invariant under the square-affine maps.
* `condMatrix_pairJoint`: on the support, `T_{uv}` averages over the admissible pairs
  `Φ(z')` (`pairAdmissible`): `T(z'; ω) = [ω ∈ Φ(z')]/|Φ(z')|`. So `phiPair` is the paper's
  `φ_y = (p-1)/2 · c_y/|Φ| - 1` and the trace term is `E[1/|Φ|]` (`trace_pairJoint_eq`).
* `trace_mixing_pair`: the bound of (b).
* `isMixing_graphLaw_pair`: the same as `(c, (u, v))`-mixing in the sense of `def:mixing`
  (`IsMixing λ {u, v} c`).
-/

@[expose] public section

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.TraceMixing

open Sarkozy.Mixing Sarkozy.Labellings

variable {p : ℕ} [Fact p.Prime]
variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The joint law of `((z_u, z_v), z_{W ∖ {u, v}})`. -/
noncomputable def pairJoint (ρ : FiniteLaw (W → ZMod p)) (u v : W) :
    FiniteLaw ((ZMod p × ZMod p) × ({w // w ∉ ({u, v} : Finset W)} → ZMod p)) :=
  ρ.map (fun z => ((z u, z v), fun w => z w))

/-- The labelling with `z_u = x`, `z_v = x'` and `z|_{W'} = r`. -/
def pairCombine {u v : W} (x x' : ZMod p) (r : {w // w ∉ ({u, v} : Finset W)} → ZMod p) :
    W → ZMod p :=
  fun w => if hu : w = u then x else if hv : w = v then x' else r ⟨w, by simp [hu, hv]⟩

omit [Fact p.Prime] [Fintype W] in
theorem pairCombine_u {u v : W} (x x' : ZMod p) (r : {w // w ∉ ({u, v} : Finset W)} → ZMod p) :
    pairCombine x x' r u = x := by
  simp [pairCombine]

omit [Fact p.Prime] [Fintype W] in
theorem pairCombine_v {u v : W} (huv : u ≠ v) (x x' : ZMod p)
    (r : {w // w ∉ ({u, v} : Finset W)} → ZMod p) : pairCombine x x' r v = x' := by
  simp [pairCombine, Ne.symm huv]

omit [Fact p.Prime] [Fintype W] in
theorem pairCombine_rest {u v : W} (x x' : ZMod p) (r : {w // w ∉ ({u, v} : Finset W)} → ZMod p)
    (w : {w // w ∉ ({u, v} : Finset W)}) : pairCombine x x' r w = r w := by
  have hw := w.2
  simp only [mem_insert, mem_singleton, not_or] at hw
  simp [pairCombine, hw.1, hw.2]

/-- The weights of the pair joint law. -/
theorem pairJoint_weight (ρ : FiniteLaw (W → ZMod p)) {u v : W} (huv : u ≠ v) (x x' : ZMod p)
    (r : {w // w ∉ ({u, v} : Finset W)} → ZMod p) :
    (pairJoint ρ u v).weight ((x, x'), r) = ρ.weight (pairCombine x x' r) := by
  unfold pairJoint FiniteLaw.map
  simp only []
  rw [Finset.sum_eq_single (pairCombine x x' r)]
  · have h : ((pairCombine x x' r u, pairCombine x x' r v),
        fun w : {w // w ∉ ({u, v} : Finset W)} => pairCombine x x' r w) = ((x, x'), r) := by
      rw [pairCombine_u, pairCombine_v huv]
      congr 1
      funext w
      exact pairCombine_rest x x' r w
    rw [ite_eq_left h]
  · intro z _ hz
    apply ite_eq_right
    intro h
    apply hz
    simp only [Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    funext w
    by_cases hu : w = u
    · subst hu
      rw [pairCombine_u, h1]
    · by_cases hv : w = v
      · subst hv
        rw [pairCombine_v huv, h2]
      · have hw : w ∉ ({u, v} : Finset W) := by simp [hu, hv]
        have := congrFun h3 ⟨w, hw⟩
        rw [show w = ((⟨w, hw⟩ : {w // w ∉ ({u, v} : Finset W)}) : W) from rfl,
          pairCombine_rest x x' r ⟨w, hw⟩]
        exact this
  · intro h
    exact absurd (mem_univ _) h

omit [Fact p.Prime] [Fintype W] in
/-- A coordinatewise bijection commutes with `pairCombine`. -/
theorem pairCombine_map {u v : W} (φ : ZMod p → ZMod p) (x x' : ZMod p)
    (r : {w // w ∉ ({u, v} : Finset W)} → ZMod p) :
    pairCombine (φ x) (φ x') (fun w => φ (r w)) = fun w => φ (pairCombine x x' r w) := by
  funext w
  unfold pairCombine
  split_ifs <;> rfl

section Graph

variable (G : OrientedGraph W) (hne : (injLabellings (ZMod p) G).Nonempty)

/-- The pair of an edge is a strict-square pair. -/
theorem pairJoint_supp {u v : W} (huv : (u, v) ∈ G.E) (x x' : ZMod p)
    (r : {w // w ∉ ({u, v} : Finset W)} → ZMod p)
    (h : quadraticChar (ZMod p) (x' - x) ≠ 1) :
    (pairJoint (graphLaw G hne) u v).weight ((x, x'), r) = 0 := by
  have huv' : u ≠ v := fun h' => G.loopless u (h' ▸ huv)
  rw [pairJoint_weight _ huv']
  unfold graphLaw
  simp only []
  apply ite_eq_right
  intro hz
  apply h
  have hfeas := (mem_injLabellings_iff G _).mp hz
  have := hfeas.2 (u, v) huv (mem_univ _) (mem_univ _)
  rwa [pairCombine_u, pairCombine_v huv'] at this

/-- Translations. -/
theorem pairJoint_translate {u v : W} (huv : u ≠ v) (β x x' : ZMod p)
    (r : {w // w ∉ ({u, v} : Finset W)} → ZMod p) :
    (pairJoint (graphLaw G hne) u v).weight ((x + β, x' + β), fun w => r w + β) =
      (pairJoint (graphLaw G hne) u v).weight ((x, x'), r) := by
  rw [pairJoint_weight _ huv, pairJoint_weight _ huv]
  have h := pairCombine_map (u := u) (v := v) (fun c => c + β) x x' r
  rw [h]
  have hone : quadraticChar (ZMod p) (1 : ZMod p) = 1 := map_one _
  have := graphLaw_weight_affine G hne hone β (pairCombine x x' r)
  simp only [one_mul] at this
  exact this

/-- Square dilations. -/
theorem pairJoint_dilate {u v : W} (huv : u ≠ v) {α : ZMod p}
    (hα : quadraticChar (ZMod p) α = 1) (x x' : ZMod p)
    (r : {w // w ∉ ({u, v} : Finset W)} → ZMod p) :
    (pairJoint (graphLaw G hne) u v).weight ((α * x, α * x'), fun w => α * r w) =
      (pairJoint (graphLaw G hne) u v).weight ((x, x'), r) := by
  rw [pairJoint_weight _ huv, pairJoint_weight _ huv]
  have h := pairCombine_map (u := u) (v := v) (fun c => α * c) x x' r
  rw [h]
  have := graphLaw_weight_affine G hne hα 0 (pairCombine x x' r)
  simp only [add_zero] at this
  exact this

/-- The translation of the other labels. -/
def restTr {u v : W} (β : ZMod p) :
    ({w // w ∉ ({u, v} : Finset W)} → ZMod p) ≃ ({w // w ∉ ({u, v} : Finset W)} → ZMod p) where
  toFun r w := r w + β
  invFun r w := r w - β
  left_inv r := by funext w; simp
  right_inv r := by funext w; simp

/-- The dilation of the other labels (by `α`, or the identity if `α = 0`). -/
noncomputable def restDil {u v : W} (α : ZMod p) :
    ({w // w ∉ ({u, v} : Finset W)} → ZMod p) ≃ ({w // w ∉ ({u, v} : Finset W)} → ZMod p) :=
  if hα : α = 0 then Equiv.refl _ else
  { toFun := fun r w => α * r w
    invFun := fun r w => α⁻¹ * r w
    left_inv := fun r => by funext w; simp only; rw [← mul_assoc, inv_mul_cancel₀ hα, one_mul]
    right_inv := fun r => by funext w; simp only; rw [← mul_assoc, mul_inv_cancel₀ hα, one_mul] }

omit [Fintype W] in
theorem restDil_apply {u v : W} {α : ZMod p} (hα : α ≠ 0)
    (r : {w // w ∉ ({u, v} : Finset W)} → ZMod p) : restDil α r = fun w => α * r w := by
  unfold restDil
  rw [dite_eq_right hα]
  rfl

/-- **`lem:trace-mixing`(b), pair trace form**, for the graph law and an edge `(u, v)`. -/
theorem trace_mixing_pair (hp2 : p ≠ 2) {u v : W} (huv : (u, v) ∈ G.E)
    (f : ZMod p × ZMod p → ℝ)
    (hf : ∑ ω, srcWeight (pairJoint (graphLaw G hne) u v) ω * f ω = 0) :
    ∑ r, tgtWeight (pairJoint (graphLaw G hne) u v) r *
        condOp (pairJoint (graphLaw G hne) u v) f r ^ 2 ≤
      max (∑ r, tgtWeight (pairJoint (graphLaw G hne) u v) r * (2 / ((p : ℝ) - 1) *
            ∑ y ∈ univ.filter (fun y => quadraticChar (ZMod p) y = 1),
              phiPair (pairJoint (graphLaw G hne) u v) r y ^ 2))
          ((p : ℝ) * ∑ r, tgtWeight (pairJoint (graphLaw G hne) u v) r *
            ∑ ω, condMatrix (pairJoint (graphLaw G hne) u v) r ω ^ 2) *
        ∑ ω, srcWeight (pairJoint (graphLaw G hne) u v) ω * f ω ^ 2 := by
  have huv' : u ≠ v := fun h' => G.loopless u (h' ▸ huv)
  refine pair_trace_bound hp2 (pairJoint (graphLaw G hne) u v)
    (fun x x' r h => pairJoint_supp G hne huv x x' r h) (fun β => restTr β)
    (fun β x x' r => pairJoint_translate G hne huv' β x x' r) (fun α => restDil α)
    (fun α hα x x' r => ?_) f hf
  have hα0 : α ≠ 0 := ne_zero_of_quadraticChar_eq_one hα
  rw [restDil_apply hα0]
  exact pairJoint_dilate G hne huv' hα x x' r

/-- The relabelling of the source of `blockJoint λ {u, v}` as pairs. -/
def pairEquiv {u v : W} (huv : u ≠ v) :
    ({w // w ∈ ({u, v} : Finset W)} → ZMod p) ≃ ZMod p × ZMod p where
  toFun g := (g ⟨u, by simp⟩, g ⟨v, by simp⟩)
  invFun ω w := if w.1 = u then ω.1 else ω.2
  left_inv g := by
    funext w
    obtain ⟨w, hw⟩ := w
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl
    · simp
    · simp [Ne.symm huv]
  right_inv ω := by
    simp [Ne.symm huv]

theorem pairJoint_eq_blockJoint {u v : W} (huv : u ≠ v) (ρ : FiniteLaw (W → ZMod p))
    (a : {w // w ∈ ({u, v} : Finset W)} → ZMod p) (b : {w // w ∉ ({u, v} : Finset W)} → ZMod p) :
    (pairJoint ρ u v).weight (pairEquiv huv a, (Equiv.refl _) b) =
      (blockJoint ρ {u, v}).weight (a, b) := by
  rw [blockJoint_weight]
  change (pairJoint ρ u v).weight ((a ⟨u, by simp⟩, a ⟨v, by simp⟩), b) = _
  rw [pairJoint_weight ρ huv]
  congr 1
  funext w
  simp only [pairCombine, Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_symm_mk]
  by_cases hu : w = u
  · subst hu
    simp
  · by_cases hv : w = v
    · subst hv
      simp [hu]
    · have hw : w ∉ ({u, v} : Finset W) := by simp [hu, hv]
      simp [hu, hv, hw]

/-- `lem:trace-mixing`(b) as a mixing bound (`def:mixing`): if `c²` bounds the maximum of the
two terms, the graph law is `(c, (u, v))`-mixing. -/
theorem isMixing_graphLaw_pair (hp2 : p ≠ 2) {u v : W} (huv : (u, v) ∈ G.E) {c : ℝ}
    (hc : max (∑ r, tgtWeight (pairJoint (graphLaw G hne) u v) r * (2 / ((p : ℝ) - 1) *
            ∑ y ∈ univ.filter (fun y => quadraticChar (ZMod p) y = 1),
              phiPair (pairJoint (graphLaw G hne) u v) r y ^ 2))
          ((p : ℝ) * ∑ r, tgtWeight (pairJoint (graphLaw G hne) u v) r *
            ∑ ω, condMatrix (pairJoint (graphLaw G hne) u v) r ω ^ 2) ≤ c ^ 2) :
    IsMixing (graphLaw G hne) {u, v} c := by
  have huv' : u ≠ v := fun h' => G.loopless u (h' ▸ huv)
  unfold IsMixing
  rw [contractsMeanZero_congr (pairEquiv huv') (Equiv.refl _)
    (fun a b => pairJoint_eq_blockJoint huv' (graphLaw G hne) a b) c]
  intro f hf
  have h := trace_mixing_pair G hne hp2 huv f hf
  have hE : 0 ≤ ∑ ω, srcWeight (pairJoint (graphLaw G hne) u v) ω * f ω ^ 2 :=
    Finset.sum_nonneg (fun ω _ => mul_nonneg (srcWeight_nonneg _ _) (sq_nonneg _))
  exact h.trans (mul_le_mul_of_nonneg_right hc hE)

/-- **`lem:trace-mixing`(b): the pair `(z_u, z_v)` has law `Unif(Ω)`.** -/
theorem srcWeight_pairJoint (hp2 : p ≠ 2) {u v : W} (huv : (u, v) ∈ G.E) (x x' : ZMod p) :
    srcWeight (pairJoint (graphLaw G hne) u v) (x, x') =
      if quadraticChar (ZMod p) (x' - x) = 1 then 2 / ((p : ℝ) * ((p : ℝ) - 1)) else 0 := by
  have huv' : u ≠ v := fun h' => G.loopless u (h' ▸ huv)
  refine srcWeight_pair_uniform hp2 (pairJoint (graphLaw G hne) u v)
    (fun x x' r h => pairJoint_supp G hne huv x x' r h) (fun β => restTr β)
    (fun β x x' r => pairJoint_translate G hne huv' β x x' r) (fun α => restDil α)
    (fun α hα x x' r => ?_) x x'
  rw [restDil_apply (ne_zero_of_quadraticChar_eq_one hα)]
  exact pairJoint_dilate G hne huv' hα x x' r

/-- The admissible pairs `Φ(z')`: the `(x, x')` such that `z'` with `z_u = x`, `z_v = x'` lies
in `Inj_p(G)`. -/
noncomputable def pairAdmissible {u v : W} (r : {w // w ∉ ({u, v} : Finset W)} → ZMod p) :
    Finset (ZMod p × ZMod p) :=
  univ.filter (fun ω => pairCombine ω.1 ω.2 r ∈ injLabellings (ZMod p) G)

theorem pairJoint_weight_eq {u v : W} (huv : u ≠ v) (ω : ZMod p × ZMod p)
    (r : {w // w ∉ ({u, v} : Finset W)} → ZMod p) :
    (pairJoint (graphLaw G hne) u v).weight (ω, r) =
      if ω ∈ pairAdmissible G r then 1 / ((injLabellings (ZMod p) G).card : ℝ) else 0 := by
  obtain ⟨x, x'⟩ := ω
  rw [pairJoint_weight _ huv]
  unfold graphLaw pairAdmissible
  simp only [mem_filter, mem_univ, true_and]

/-- **On the support, `T_{uv}` averages over `Φ(z')`**: `T(z'; ω) = [ω ∈ Φ(z')]/|Φ(z')|`. -/
theorem condMatrix_pairJoint {u v : W} (huv : u ≠ v)
    (r : {w // w ∉ ({u, v} : Finset W)} → ZMod p)
    (hr : tgtWeight (pairJoint (graphLaw G hne) u v) r ≠ 0) (ω : ZMod p × ZMod p) :
    condMatrix (pairJoint (graphLaw G hne) u v) r ω =
      (if ω ∈ pairAdmissible G r then 1 else 0) / ((pairAdmissible G r).card : ℝ) := by
  set c : ℝ := 1 / ((injLabellings (ZMod p) G).card : ℝ) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    have : (0 : ℝ) < (injLabellings (ZMod p) G).card := by exact_mod_cast card_pos.mpr hne
    positivity
  have hfilt : univ.filter (fun ω => ω ∈ pairAdmissible G r) = pairAdmissible G r := by
    ext ω
    simp
  have htgt : tgtWeight (pairJoint (graphLaw G hne) u v) r =
      c * ((pairAdmissible G r).card : ℝ) := by
    unfold tgtWeight
    simp only [pairJoint_weight_eq G hne huv]
    rw [← Finset.sum_filter, hfilt, sum_const, nsmul_eq_mul, mul_comm]
  unfold condMatrix
  rw [ite_eq_right hr, pairJoint_weight_eq G hne huv, htgt]
  split_ifs
  · rw [div_mul_eq_div_div, div_self hc0]
  · simp

/-- `φ_y = (p-1)/2 · c_y/|Φ| - 1` on the support, `c_y = #{x : (x, x + y) ∈ Φ(z')}`. -/
theorem phiPair_pairJoint {u v : W} (huv : u ≠ v)
    (r : {w // w ∉ ({u, v} : Finset W)} → ZMod p)
    (hr : tgtWeight (pairJoint (graphLaw G hne) u v) r ≠ 0) (y : ZMod p) :
    phiPair (pairJoint (graphLaw G hne) u v) r y =
      ((p : ℝ) - 1) / 2 * (((univ.filter fun x => (x, x + y) ∈ pairAdmissible G r).card : ℝ) /
        ((pairAdmissible G r).card : ℝ)) - 1 := by
  unfold phiPair
  simp only [condMatrix_pairJoint G hne huv r hr]
  rw [← Finset.sum_div, Finset.sum_boole]

/-- The trace term: `∑_ω T(z'; ω)² = 1/|Φ(z')|` on the support, so
`∑_{z'} λ(z') ∑_ω T(z'; ω)² = E_λ[1/|Φ|]`. -/
theorem sum_sq_condMatrix_pairJoint {u v : W} (huv : u ≠ v)
    (r : {w // w ∉ ({u, v} : Finset W)} → ZMod p)
    (hr : tgtWeight (pairJoint (graphLaw G hne) u v) r ≠ 0) :
    ∑ ω, condMatrix (pairJoint (graphLaw G hne) u v) r ω ^ 2 =
      1 / ((pairAdmissible G r).card : ℝ) := by
  simp only [condMatrix_pairJoint G hne huv r hr, div_pow, ite_pow, one_pow,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  rw [← Finset.sum_div, Finset.sum_boole]
  have hpos : (0 : ℝ) < (pairAdmissible G r).card := by
    by_contra h
    push Not at h
    have h0 : ((pairAdmissible G r).card : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg _)
    apply hr
    unfold tgtWeight
    apply Finset.sum_eq_zero
    intro ω _
    rw [pairJoint_weight_eq G hne huv]
    have : (pairAdmissible G r) = ∅ := by
      rw [← Finset.card_eq_zero]
      exact_mod_cast h0
    simp [this]
  have hfilt : ((univ.filter fun ω => ω ∈ pairAdmissible G r).card : ℝ) =
      (pairAdmissible G r).card := by
    congr 2
    ext ω
    simp
  rw [hfilt]
  field_simp

end Graph

end Sarkozy.TraceMixing
