module

public import Sarkozy.TraceMixing.R4

/-!
# Mixing of the tail laws (`lem:record:tail-mixing`(a), (b); (R4) for the tail laws)

`paper/sections/27_tail_index.tex`, `lem:record:tail-mixing`. At a tail prime the tail law and
its normalized accepted part are two-component mixtures
`μ = ϖ π + (1 - ϖ) ρ`, where `π = λ_p(G)` is the root (the graph law of a graph with `72`
vertices and degrees at most `20`) and `ρ` is any law with the same marginal on the queried
slot or pair (`lem:tail-law`(iii), `lem:tail-prices`). By `lem:mixture`
(`Sarkozy.Mixing.mixture_mixing`) the root contributes its `lem:trace-mixing`(d) bound and the
other component is a contraction:

* `tail_slot_bound`: the squared norm from slot `v` is at most `ϖ 2^22/p + (1 - ϖ)`;
* `tail_pair_bound`: if the query `(u, v)` is an edge of the root graph and the `(u, v)`-marginal
  of `ρ` is `Unif(Ω)`, then so is that of `μ` (`srcWeight_pairJoint_tail`), and the squared norm
  from the pair is at most `ϖ 2^92/p + (1 - ϖ)`;
* `tail_mixing_S`: with `1 - ϖ ≤ h` and `2^92/p + h ≤ S`, both squared norms are at most `S`
  (`lem:record:tail-mixing`(a), (b), with `S = S_72(p)`);
* `tail_R4`: if moreover `S ≤ p^{-2γ}`, `γ = 255/1024` (`lem:record:tail-mixing`(c), which the
  paper checks with the explicit `S_72(p)` and the certificate (S7)), then `μ` is
  `(γ, v)`-mixing at every slot and `(γ, (u, v))`-mixing at the query, with `Unif(Ω)` marginal:
  the clauses of (R4) for `μ_p` and `ν̄_p`.

The decomposition of `μ_p` and `ν̄_p` (`lem:tail-law`, `lem:tail-prices`) and the explicit
`S_72(p)` are inputs here (hypotheses `hμ`, `hρ…`, `h`, `S`).
-/

@[expose] public section

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.TraceMixing

open Sarkozy.Mixing Sarkozy.Labellings

variable {p : ℕ} [Fact p.Prime]
variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The slot joint law of a mixture is the mixture of the slot joint laws. -/
theorem slotJoint_mix {μ π ρ : FiniteLaw (W → ZMod p)} {ϖ : ℝ}
    (hμ : ∀ z, μ.weight z = ϖ * π.weight z + (1 - ϖ) * ρ.weight z) (v : W)
    (x : ZMod p × ({w // w ≠ v} → ZMod p)) :
    (slotJoint μ v).weight x = ϖ * (slotJoint π v).weight x + (1 - ϖ) * (slotJoint ρ v).weight x := by
  rw [slotJoint_weight, slotJoint_weight, slotJoint_weight, hμ]

/-- The pair joint law of a mixture is the mixture of the pair joint laws. -/
theorem pairJoint_mix {μ π ρ : FiniteLaw (W → ZMod p)} {ϖ : ℝ}
    (hμ : ∀ z, μ.weight z = ϖ * π.weight z + (1 - ϖ) * ρ.weight z) {u v : W} (huv : u ≠ v)
    (x : (ZMod p × ZMod p) × ({w // w ∉ ({u, v} : Finset W)} → ZMod p)) :
    (pairJoint μ u v).weight x =
      ϖ * (pairJoint π u v).weight x + (1 - ϖ) * (pairJoint ρ u v).weight x := by
  obtain ⟨⟨a, b⟩, r⟩ := x
  rw [pairJoint_weight _ huv, pairJoint_weight _ huv, pairJoint_weight _ huv, hμ]

/-- `ContractsMeanZero` for the root at a slot, from `lem:trace-mixing`(d). -/
theorem contractsMeanZero_root_slot (hW : WeilBound (ZMod p)) (hp2 : p ≠ 2) (G : OrientedGraph W)
    (hne : (injLabellings (ZMod p) G).Nonempty) (hn : Fintype.card W = 72)
    (hdeg : ∀ w, degree G w ≤ 20) (hp : (2 : ℝ) ^ 512 ≤ p) (v : W) :
    ContractsMeanZero (slotJoint (graphLaw G hne) v) (Real.sqrt (2 ^ 22 / p)) := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have hcard : (Fintype.card (ZMod p) : ℝ) = p := by rw [ZMod.card]
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (by positivity) hp
  intro f hf
  have hsrc := srcWeight_graphSlot G hne v
  have hq0 : (0 : ℝ) < Fintype.card (ZMod p) := by rw [hcard]; exact hp0
  have hf' : ∑ x, f x = 0 := by
    simp only [hsrc] at hf
    rw [← Finset.mul_sum] at hf
    exact (mul_eq_zero.mp hf).resolve_left (inv_ne_zero hq0.ne')
  have h := trace_mixing_slot_72 hW hF G hne hn v (hdeg v) (by rw [hcard]; exact hp) f hf'
  have hnorm : (FiniteLaw.uniform (ZMod p)).expect (fun x => f x ^ 2) =
      ∑ x, srcWeight (slotJoint (graphLaw G hne) v) x * f x ^ 2 := by
    rw [FiniteLaw.expect_uniform]
    simp only [hsrc]
    rw [← Finset.mul_sum, div_eq_inv_mul]
  rw [hnorm, hcard] at h
  rw [Real.sq_sqrt (by positivity)]
  exact h

/-- `ContractsMeanZero` for the root at an edge, from `lem:trace-mixing`(d). -/
theorem contractsMeanZero_root_pair (hW : WeilBound (ZMod p)) (hp2 : p ≠ 2) (G : OrientedGraph W)
    (hne : (injLabellings (ZMod p) G).Nonempty) (hn : Fintype.card W = 72)
    (hdeg : ∀ w, degree G w ≤ 20) (hp : (2 : ℝ) ^ 512 ≤ p) {u v : W} (huv : (u, v) ∈ G.E) :
    ContractsMeanZero (pairJoint (graphLaw G hne) u v) (Real.sqrt (2 ^ 92 / p)) := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (by positivity) hp
  intro f hf
  rw [Real.sq_sqrt (by positivity)]
  exact trace_mixing_pair_72 hW hp2 G hne hn hdeg hp huv f hf

/-- **`lem:record:tail-mixing`(a), the bound from one slot**: for `μ = ϖ π + (1 - ϖ) ρ` with
`π` the root and `ρ` any law with uniform marginal at `v`, the squared norm of the conditional
operator from slot `v` on the mean-zero functions is at most `ϖ 2^22/p + (1 - ϖ)`. -/
theorem tail_slot_bound (hW : WeilBound (ZMod p)) (hp2 : p ≠ 2) (G : OrientedGraph W)
    (hne : (injLabellings (ZMod p) G).Nonempty) (hn : Fintype.card W = 72)
    (hdeg : ∀ w, degree G w ≤ 20) (hp : (2 : ℝ) ^ 512 ≤ p) {μ ρ : FiniteLaw (W → ZMod p)}
    {ϖ : ℝ} (hϖ0 : 0 ≤ ϖ) (hϖ1 : ϖ ≤ 1)
    (hμ : ∀ z, μ.weight z = ϖ * (graphLaw G hne).weight z + (1 - ϖ) * ρ.weight z) (v : W)
    (hρ : ∀ x, srcWeight (slotJoint ρ v) x = (Fintype.card (ZMod p) : ℝ)⁻¹)
    (f : ZMod p → ℝ) (hf : ∑ x, srcWeight (slotJoint μ v) x * f x = 0) :
    ∑ b, tgtWeight (slotJoint μ v) b * condOp (slotJoint μ v) f b ^ 2 ≤
      (ϖ * (2 ^ 22 / p) + (1 - ϖ)) * ∑ x, srcWeight (slotJoint μ v) x * f x ^ 2 := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (by positivity) hp
  set κs : Fin 2 → FiniteLaw (ZMod p × ({w // w ≠ v} → ZMod p)) :=
    ![slotJoint (graphLaw G hne) v, slotJoint ρ v] with hκs
  set ϖs : Fin 2 → ℝ := ![ϖ, 1 - ϖ] with hϖs
  set cs : Fin 2 → ℝ := ![Real.sqrt (2 ^ 22 / p), 1] with hcs
  have hsrcπ := srcWeight_graphSlot G hne v
  have hmix : ∀ x, (slotJoint μ v).weight x = ∑ i, ϖs i * (κs i).weight x := by
    intro x
    rw [Fin.sum_univ_two, slotJoint_mix hμ v x]
    simp [hκs, hϖs]
  have hsrcμ (a : ZMod p) : srcWeight (slotJoint μ v) a = (Fintype.card (ZMod p) : ℝ)⁻¹ := by
    unfold srcWeight
    simp only [slotJoint_mix hμ v, Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 := hsrcπ a
    have h2 := hρ a
    unfold srcWeight at h1 h2
    rw [h1, h2]
    ring
  have hsrc : ∀ i a, srcWeight (κs i) a = srcWeight (slotJoint μ v) a := by
    intro i a
    rw [hsrcμ]
    fin_cases i
    · exact hsrcπ a
    · exact hρ a
  have hc : ∀ i, ContractsMeanZero (κs i) (cs i) := by
    intro i
    fin_cases i
    · exact contractsMeanZero_root_slot hW hp2 G hne hn hdeg hp v
    · exact contractsMeanZero_one _
  have h := mixture_mixing (fun i => by fin_cases i <;> simp [hϖs, hϖ0, hϖ1]) hmix hsrc hc f hf
  have hsum : ∑ i, ϖs i * cs i ^ 2 = ϖ * (2 ^ 22 / p) + (1 - ϖ) := by
    rw [Fin.sum_univ_two]
    simp only [hϖs, hcs, Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, mul_one]
    rw [Real.sq_sqrt (by positivity)]
  rwa [hsum] at h

/-- The `(u, v)`-marginal of the mixture is `Unif(Ω)` when that of `ρ` is. -/
theorem srcWeight_pairJoint_tail (hp2 : p ≠ 2) (G : OrientedGraph W)
    (hne : (injLabellings (ZMod p) G).Nonempty) {μ ρ : FiniteLaw (W → ZMod p)} {ϖ : ℝ}
    (hμ : ∀ z, μ.weight z = ϖ * (graphLaw G hne).weight z + (1 - ϖ) * ρ.weight z)
    {u v : W} (huv : (u, v) ∈ G.E)
    (hρ : ∀ x x', srcWeight (pairJoint ρ u v) (x, x') =
      if quadraticChar (ZMod p) (x' - x) = 1 then 2 / ((p : ℝ) * ((p : ℝ) - 1)) else 0)
    (x x' : ZMod p) :
    srcWeight (pairJoint μ u v) (x, x') =
      if quadraticChar (ZMod p) (x' - x) = 1 then 2 / ((p : ℝ) * ((p : ℝ) - 1)) else 0 := by
  have huv' : u ≠ v := fun h' => G.loopless u (h' ▸ huv)
  have h1 := srcWeight_pairJoint G hne hp2 huv x x'
  have h2 := hρ x x'
  unfold srcWeight at h1 h2 ⊢
  simp only [pairJoint_mix hμ huv', Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h1, h2]
  ring

/-- **`lem:record:tail-mixing`(b), the bound from a query pair**: if `(u, v)` is an edge of the
root graph and the `(u, v)`-marginal of `ρ` is `Unif(Ω)`, the squared norm of the conditional
operator of `μ = ϖ π + (1 - ϖ) ρ` from the pair on the mean-zero functions is at most
`ϖ 2^92/p + (1 - ϖ)`. -/
theorem tail_pair_bound (hW : WeilBound (ZMod p)) (hp2 : p ≠ 2) (G : OrientedGraph W)
    (hne : (injLabellings (ZMod p) G).Nonempty) (hn : Fintype.card W = 72)
    (hdeg : ∀ w, degree G w ≤ 20) (hp : (2 : ℝ) ^ 512 ≤ p) {μ ρ : FiniteLaw (W → ZMod p)}
    {ϖ : ℝ} (hϖ0 : 0 ≤ ϖ) (hϖ1 : ϖ ≤ 1)
    (hμ : ∀ z, μ.weight z = ϖ * (graphLaw G hne).weight z + (1 - ϖ) * ρ.weight z)
    {u v : W} (huv : (u, v) ∈ G.E)
    (hρ : ∀ x x', srcWeight (pairJoint ρ u v) (x, x') =
      if quadraticChar (ZMod p) (x' - x) = 1 then 2 / ((p : ℝ) * ((p : ℝ) - 1)) else 0)
    (f : ZMod p × ZMod p → ℝ) (hf : ∑ ω, srcWeight (pairJoint μ u v) ω * f ω = 0) :
    ∑ r, tgtWeight (pairJoint μ u v) r * condOp (pairJoint μ u v) f r ^ 2 ≤
      (ϖ * (2 ^ 92 / p) + (1 - ϖ)) * ∑ ω, srcWeight (pairJoint μ u v) ω * f ω ^ 2 := by
  have huv' : u ≠ v := fun h' => G.loopless u (h' ▸ huv)
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (by positivity) hp
  set κs : Fin 2 → FiniteLaw ((ZMod p × ZMod p) × ({w // w ∉ ({u, v} : Finset W)} → ZMod p)) :=
    ![pairJoint (graphLaw G hne) u v, pairJoint ρ u v] with hκs
  set ϖs : Fin 2 → ℝ := ![ϖ, 1 - ϖ] with hϖs
  set cs : Fin 2 → ℝ := ![Real.sqrt (2 ^ 92 / p), 1] with hcs
  have hmix : ∀ x, (pairJoint μ u v).weight x = ∑ i, ϖs i * (κs i).weight x := by
    intro x
    rw [Fin.sum_univ_two, pairJoint_mix hμ huv' x]
    simp [hκs, hϖs]
  have hsrc : ∀ i a, srcWeight (κs i) a = srcWeight (pairJoint μ u v) a := by
    intro i a
    obtain ⟨x, x'⟩ := a
    rw [srcWeight_pairJoint_tail hp2 G hne hμ huv hρ x x']
    fin_cases i
    · exact srcWeight_pairJoint G hne hp2 huv x x'
    · exact hρ x x'
  have hc : ∀ i, ContractsMeanZero (κs i) (cs i) := by
    intro i
    fin_cases i
    · exact contractsMeanZero_root_pair hW hp2 G hne hn hdeg hp huv
    · exact contractsMeanZero_one _
  have h := mixture_mixing (fun i => by fin_cases i <;> simp [hϖs, hϖ0, hϖ1]) hmix hsrc hc f hf
  have hsum : ∑ i, ϖs i * cs i ^ 2 = ϖ * (2 ^ 92 / p) + (1 - ϖ) := by
    rw [Fin.sum_univ_two]
    simp only [hϖs, hcs, Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, mul_one]
    rw [Real.sq_sqrt (by positivity)]
  rwa [hsum] at h

/-- `ϖ X + (1 - ϖ) ≤ B + h` for `0 ≤ X ≤ B`, `ϖ ≤ 1`, `1 - ϖ ≤ h`. -/
theorem mix_coef_le {ϖ X h B : ℝ} (hϖ1 : ϖ ≤ 1) (hX0 : 0 ≤ X) (hX : X ≤ B)
    (hh : 1 - ϖ ≤ h) : ϖ * X + (1 - ϖ) ≤ B + h := by
  have : ϖ * X ≤ X := by nlinarith
  linarith

/-- **`lem:record:tail-mixing`(a), (b)**: with `1 - ϖ ≤ h` and `2^92/p + h ≤ S`, the squared
norms of the conditional operators of `μ` from every slot, and from the query pair, are at most
`S` on the mean-zero functions; the pair marginal is `Unif(Ω)`. -/
theorem tail_mixing_S (hW : WeilBound (ZMod p)) (hp2 : p ≠ 2) (G : OrientedGraph W)
    (hne : (injLabellings (ZMod p) G).Nonempty) (hn : Fintype.card W = 72)
    (hdeg : ∀ w, degree G w ≤ 20) (hp : (2 : ℝ) ^ 512 ≤ p) {μ ρ : FiniteLaw (W → ZMod p)}
    {ϖ h S : ℝ} (hϖ0 : 0 ≤ ϖ) (hϖ1 : ϖ ≤ 1) (hh : 1 - ϖ ≤ h) (hS : 2 ^ 92 / p + h ≤ S)
    (hμ : ∀ z, μ.weight z = ϖ * (graphLaw G hne).weight z + (1 - ϖ) * ρ.weight z) :
    (∀ v, (∀ x, srcWeight (slotJoint ρ v) x = (Fintype.card (ZMod p) : ℝ)⁻¹) →
      ∀ f : ZMod p → ℝ, ∑ x, srcWeight (slotJoint μ v) x * f x = 0 →
        ∑ b, tgtWeight (slotJoint μ v) b * condOp (slotJoint μ v) f b ^ 2 ≤
          S * ∑ x, srcWeight (slotJoint μ v) x * f x ^ 2) ∧
    (∀ u v, (u, v) ∈ G.E →
      (∀ x x', srcWeight (pairJoint ρ u v) (x, x') =
        if quadraticChar (ZMod p) (x' - x) = 1 then 2 / ((p : ℝ) * ((p : ℝ) - 1)) else 0) →
      ∀ f : ZMod p × ZMod p → ℝ, ∑ ω, srcWeight (pairJoint μ u v) ω * f ω = 0 →
        ∑ r, tgtWeight (pairJoint μ u v) r * condOp (pairJoint μ u v) f r ^ 2 ≤
          S * ∑ ω, srcWeight (pairJoint μ u v) ω * f ω ^ 2) := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (by positivity) hp
  have h2292 : (2 : ℝ) ^ 22 / p ≤ 2 ^ 92 / p :=
    div_le_div_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by norm_num)) hp0.le
  refine ⟨fun v hρ f hf => ?_, fun u v huv hρ f hf => ?_⟩
  · have hb := tail_slot_bound hW hp2 G hne hn hdeg hp hϖ0 hϖ1 hμ v hρ f hf
    have hE : 0 ≤ ∑ x, srcWeight (slotJoint μ v) x * f x ^ 2 :=
      Finset.sum_nonneg (fun x _ => mul_nonneg (srcWeight_nonneg _ _) (sq_nonneg _))
    refine hb.trans (mul_le_mul_of_nonneg_right ?_ hE)
    exact (mix_coef_le hϖ1 (by positivity) h2292 hh).trans hS
  · have hb := tail_pair_bound hW hp2 G hne hn hdeg hp hϖ0 hϖ1 hμ huv hρ f hf
    have hE : 0 ≤ ∑ ω, srcWeight (pairJoint μ u v) ω * f ω ^ 2 :=
      Finset.sum_nonneg (fun ω _ => mul_nonneg (srcWeight_nonneg _ _) (sq_nonneg _))
    refine hb.trans (mul_le_mul_of_nonneg_right ?_ hE)
    exact (mix_coef_le hϖ1 (by positivity) le_rfl hh).trans hS

/-- **(R4) for the tail laws** (`lem:record:tail-mixing`(c) given `S ≤ p^{-2γ}`): with
`γ = 255/1024`, the mixture `μ = ϖ π + (1 - ϖ) ρ` of the root `π = λ_p(G)` and a law `ρ` with
uniform one-slot marginals is `(γ, v)`-mixing at every slot; at every query `(u, v)` that is an
edge of the root graph and at which `ρ` has `Unif(Ω)` marginal, the `(u, v)`-marginal of `μ` is
`Unif(Ω)` and `μ` is `(γ, (u, v))`-mixing (`def:mixing`). Assumes Weil's bound
(`Sarkozy.Target.Weil`). -/
theorem tail_R4 (hWeil : Target.Weil) (hp : (2 : ℝ) ^ 512 ≤ p) (G : OrientedGraph W)
    (hne : (injLabellings (ZMod p) G).Nonempty) (hn : Fintype.card W = 72)
    (hdeg : ∀ w, degree G w ≤ 20) {μ ρ : FiniteLaw (W → ZMod p)}
    {ϖ h S : ℝ} (hϖ0 : 0 ≤ ϖ) (hϖ1 : ϖ ≤ 1) (hh : 1 - ϖ ≤ h) (hS : 2 ^ 92 / p + h ≤ S)
    (hSγ : S ≤ (p : ℝ) ^ (-(255 / 512 : ℝ)))
    (hμ : ∀ z, μ.weight z = ϖ * (graphLaw G hne).weight z + (1 - ϖ) * ρ.weight z)
    (hρ1 : ∀ v x, srcWeight (slotJoint ρ v) x = (Fintype.card (ZMod p) : ℝ)⁻¹) :
    (∀ v, IsGammaMixing p (255 / 1024) μ {v}) ∧
      ∀ u v, (u, v) ∈ G.E →
        (∀ x x', srcWeight (pairJoint ρ u v) (x, x') =
          if quadraticChar (ZMod p) (x' - x) = 1 then 2 / ((p : ℝ) * ((p : ℝ) - 1)) else 0) →
        (∀ x x', srcWeight (pairJoint μ u v) (x, x') =
          if quadraticChar (ZMod p) (x' - x) = 1 then 2 / ((p : ℝ) * ((p : ℝ) - 1)) else 0) ∧
        IsGammaMixing p (255 / 1024) μ {u, v} := by
  have h2512 : (2 : ℝ) < 2 ^ 512 := lt_self_pow₀ (by norm_num) (by norm_num)
  have hp2R : (2 : ℝ) < p := lt_of_lt_of_le h2512 hp
  have hp2 : p ≠ 2 := by
    intro h'
    rw [h'] at hp2R
    push_cast at hp2R
    exact lt_irrefl _ hp2R
  have hW := weilBound_of_target hWeil p hp2
  have hp0 : (0 : ℝ) < p := by linarith only [hp2R]
  have hsq : ((p : ℝ) ^ (-(255 / 1024 : ℝ))) ^ 2 = (p : ℝ) ^ (-(255 / 512 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    norm_num
  obtain ⟨hslot, hpair⟩ := tail_mixing_S hW hp2 G hne hn hdeg hp hϖ0 hϖ1 hh hS hμ
  refine ⟨fun v => ?_, fun u v huv hρ => ⟨srcWeight_pairJoint_tail hp2 G hne hμ huv hρ, ?_⟩⟩
  · unfold IsGammaMixing
    rw [isMixing_singleton_iff]
    intro f hf
    have hb := hslot v (hρ1 v) f hf
    have hE : 0 ≤ ∑ x, srcWeight (slotJoint μ v) x * f x ^ 2 :=
      Finset.sum_nonneg (fun x _ => mul_nonneg (srcWeight_nonneg _ _) (sq_nonneg _))
    rw [hsq]
    exact hb.trans (mul_le_mul_of_nonneg_right hSγ hE)
  · have huv' : u ≠ v := fun h' => G.loopless u (h' ▸ huv)
    unfold IsGammaMixing IsMixing
    rw [contractsMeanZero_congr (pairEquiv huv') (Equiv.refl _)
      (fun a b => pairJoint_eq_blockJoint huv' μ a b)]
    intro f hf
    have hb := hpair u v huv hρ f hf
    have hE : 0 ≤ ∑ ω, srcWeight (pairJoint μ u v) ω * f ω ^ 2 :=
      Finset.sum_nonneg (fun ω _ => mul_nonneg (srcWeight_nonneg _ _) (sq_nonneg _))
    rw [hsq]
    exact hb.trans (mul_le_mul_of_nonneg_right hSγ hE)

end Sarkozy.TraceMixing
