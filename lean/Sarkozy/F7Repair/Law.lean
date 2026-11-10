module

public import Sarkozy.F7Repair.OneWay
public import Sarkozy.ProbabilityConstructions

@[expose] public section

/-!
# The repaired law on the labelling space (`lem:tr:repair`(a)–(c),(f), (F7))

`paper/sections/26_upper_comparison.tex`, (F7) and its proof: the one-way repair is the law
`π^rep = (1 + f(x) + g(y)) π^new` on the labellings of the repaired graph, with `x`, `y` its two
halves. Here `π^new` is any law `lam` on a finite space `Ω` with two maps `a : Ω → X`,
`b : Ω → Y` (the halves), and `(f, g)` is the solution of `OneWayData` for the pair law of
`(a, b)`.

* `pairLaw lam a b`: the law of `(a, b)`;
* **`repLaw D`**: the repaired law on `Ω`; `repLaw_support` (it lives on the support of `lam`, so
  it satisfies every constraint that holds `lam`-almost surely, `lem:tr:repair`(c)),
  `repLaw_fst`, `repLaw_snd` (its half marginals are `μX`, `μY`), `repLaw_centred` (its centred
  norm is at most `ρ'`, `lem:tr:repair`(f));
* **`repLaw_invariant`**: invariance under every symmetry of the data (`lem:tr:repair`(a));
* `pairForm`, **`coupling_change`**: two laws with the same half marginals and centred norms
  `r`, `s` differ, as a form on all of `L²(μX) × L²(μY)`, by at most `r + s`
  (`lem:tr:repair`(f), last claim);
* `map_weight_ne_zero_of_support`, `map_weight_equivariant`: support and invariance pass to images
  (used for the emission).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.F7Repair

open Sarkozy.Recentering Sarkozy.Structured

variable {Ω X Y : Type*} [Fintype Ω] [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- The law of the pair of halves `(a, b)` under `lam`. -/
noncomputable def pairLaw (lam : FiniteLaw Ω) (a : Ω → X) (b : Ω → Y) : FiniteLaw (X × Y) :=
  lam.map (fun ω => (a ω, b ω))

theorem pairLaw_expect (lam : FiniteLaw Ω) (a : Ω → X) (b : Ω → Y) (G : X × Y → ℝ) :
    (pairLaw lam a b).expect G = lam.expect (fun ω => G (a ω, b ω)) := by
  unfold pairLaw
  rw [FiniteLaw.expect_map]
  rfl

variable {lam : FiniteLaw Ω} {a : Ω → X} {b : Ω → Y} {μX : FiniteLaw X} {μY : FiniteLaw Y}

/-- **The repaired law** `π^rep = (1 + f(a) + g(b)) lam` (`lem:tr:repair`(a),(c); (F7)). -/
noncomputable def repLaw (D : OneWayData (pairLaw lam a b) μX μY) : FiniteLaw Ω where
  weight ω := (1 + D.f (a ω) + D.g (b ω)) * lam.weight ω
  nonneg ω := mul_nonneg (D.one_add_pos _ _).le (lam.nonneg ω)
  total := by
    have h := D.marg_fst (fun _ => 1)
    rw [pairLaw_expect] at h
    simp only [mul_one, FiniteLaw.expect_const] at h
    unfold FiniteLaw.expect at h
    refine Eq.trans ?_ h
    exact sum_congr rfl fun ω _ => mul_comm _ _

variable (D : OneWayData (pairLaw lam a b) μX μY)

theorem repLaw_weight (ω : Ω) :
    (repLaw D).weight ω = (1 + D.f (a ω) + D.g (b ω)) * lam.weight ω := rfl

theorem repLaw_expect (G : Ω → ℝ) :
    (repLaw D).expect G = lam.expect (fun ω => (1 + D.f (a ω) + D.g (b ω)) * G ω) := by
  unfold FiniteLaw.expect
  exact sum_congr rfl fun ω _ => by rw [repLaw_weight]; ring

/-- **The repaired law lives on the support of `lam`** (`lem:tr:repair`(c)). -/
theorem repLaw_support {ω : Ω} (h : (repLaw D).weight ω ≠ 0) : lam.weight ω ≠ 0 := by
  intro h0
  apply h
  rw [repLaw_weight, h0, mul_zero]

/-- **The first half marginal of the repair is `μX`.** -/
theorem repLaw_fst (φ : X → ℝ) : (repLaw D).expect (fun ω => φ (a ω)) = μX.expect φ := by
  rw [repLaw_expect, ← D.marg_fst φ, pairLaw_expect]

/-- **The second half marginal of the repair is `μY`.** -/
theorem repLaw_snd (ψ : Y → ℝ) : (repLaw D).expect (fun ω => ψ (b ω)) = μY.expect ψ := by
  rw [repLaw_expect, ← D.marg_snd ψ, pairLaw_expect]

/-- **The centred norm of the repair is at most `ρ'`** (`lem:tr:repair`(f), case (d)). -/
theorem repLaw_centred (h : X → ℝ) (k : Y → ℝ) (hh : μX.expect h = 0) (hk : μY.expect k = 0) :
    |(repLaw D).expect (fun ω => h (a ω) * k (b ω))| ≤ D.ρ' * nrm μX h * nrm μY k := by
  have := D.centred h k hh hk
  rw [pairLaw_expect] at this
  rw [repLaw_expect]
  exact this

omit [DecidableEq X] [DecidableEq Y] in
/-- A law `lam'` supported where `lam` is has images supported where the image of `lam` is. -/
theorem map_weight_ne_zero_of_support {Ξ : Type*} [Fintype Ξ] [DecidableEq Ξ]
    {lam' lam₀ : FiniteLaw Ω} (hs : ∀ ω, lam'.weight ω ≠ 0 → lam₀.weight ω ≠ 0) (φ : Ω → Ξ)
    {z : Ξ} (hz : (lam'.map φ).weight z ≠ 0) : (lam₀.map φ).weight z ≠ 0 := by
  change (∑ ω, if φ ω = z then lam'.weight ω else 0) ≠ 0 at hz
  obtain ⟨ω, _, hω⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  have hφ : φ ω = z := by
    by_contra hne
    simp only [hne, ↓reduceIte] at hω
    exact hω rfl
  simp only [hφ, ↓reduceIte] at hω
  have hpos : 0 < lam₀.weight ω := lt_of_le_of_ne (lam₀.nonneg ω) (Ne.symm (hs ω hω))
  change (∑ ω', if φ ω' = z then lam₀.weight ω' else 0) ≠ 0
  apply ne_of_gt
  refine Finset.sum_pos' (fun ω' _ => ?_) ⟨ω, mem_univ _, ?_⟩
  · split_ifs
    · exact lam₀.nonneg ω'
    · exact le_rfl
  · simp only [hφ, ↓reduceIte]
    exact hpos

omit [DecidableEq X] [DecidableEq Y] in
/-- **Images of invariant laws are invariant**: if `σ` preserves `lam` and `φ ∘ σ = τ ∘ φ`, then
the image law is `τ`-invariant. -/
theorem map_weight_equivariant {Ξ : Type*} [Fintype Ξ] [DecidableEq Ξ] (lam₀ : FiniteLaw Ω)
    (φ : Ω → Ξ) (σ : Ω ≃ Ω) (τ : Ξ ≃ Ξ) (hσ : ∀ ω, lam₀.weight (σ ω) = lam₀.weight ω)
    (hφ : ∀ ω, φ (σ ω) = τ (φ ω)) (z : Ξ) : (lam₀.map φ).weight (τ z) = (lam₀.map φ).weight z := by
  change (∑ ω, if φ ω = τ z then lam₀.weight ω else 0) =
    ∑ ω, if φ ω = z then lam₀.weight ω else 0
  rw [← Equiv.sum_comp σ (fun ω => if φ ω = τ z then lam₀.weight ω else 0)]
  refine sum_congr rfl fun ω _ => ?_
  simp only [hφ, hσ, τ.apply_eq_iff_eq]

/-- **Invariance of the repair** (`lem:tr:repair`(a), last claim): if `σ` preserves `lam` and
acts on the halves by `τX`, `τY`, which preserve `μX`, `μY`, then `σ` preserves the repair. -/
theorem repLaw_invariant (σ : Ω ≃ Ω) (τX : X ≃ X) (τY : Y ≃ Y)
    (hσ : ∀ ω, lam.weight (σ ω) = lam.weight ω) (ha : ∀ ω, a (σ ω) = τX (a ω))
    (hb : ∀ ω, b (σ ω) = τY (b ω)) (hμX : ∀ x, μX.weight (τX x) = μX.weight x)
    (hμY : ∀ y, μY.weight (τY y) = μY.weight y) (ω : Ω) :
    (repLaw D).weight (σ ω) = (repLaw D).weight ω := by
  have hν : ∀ x y, (pairLaw lam a b).weight (τX x, τY y) = (pairLaw lam a b).weight (x, y) := by
    intro x y
    exact map_weight_equivariant lam (fun ω => (a ω, b ω)) σ (τX.prodCongr τY) hσ
      (fun ω => by rw [ha, hb]; rfl) (x, y)
  obtain ⟨hf, hg⟩ := D.invariant τX τY hν hμX hμY
  rw [repLaw_weight, repLaw_weight, ha, hb, hf, hg, hσ]

/-! ### The change against a coupling with the same marginals (`lem:tr:repair`(f)) -/

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
/-- The pair form `(h, k) ↦ E_lam[h(a) k(b)]`. -/
noncomputable def pairForm (lam : FiniteLaw Ω) (a : Ω → X) (b : Ω → Y) :
    (X → ℝ) →ₗ[ℝ] (Y → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun h k => lam.expect (fun ω => h (a ω) * k (b ω)))
    (fun h h' k => by
      rw [← lam.expect_add]
      exact lam.expect_congr fun ω => by simp only [Pi.add_apply]; ring)
    (fun c h k => by
      simp only [smul_eq_mul]
      rw [← lam.expect_const_mul]
      exact lam.expect_congr fun ω => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun h k k' => by
      rw [← lam.expect_add]
      exact lam.expect_congr fun ω => by simp only [Pi.add_apply]; ring)
    (fun c h k => by
      simp only [smul_eq_mul]
      rw [← lam.expect_const_mul]
      exact lam.expect_congr fun ω => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
theorem pairForm_apply (lam : FiniteLaw Ω) (a : Ω → X) (b : Ω → Y) (h : X → ℝ) (k : Y → ℝ) :
    pairForm lam a b h k = lam.expect (fun ω => h (a ω) * k (b ω)) := rfl

omit [DecidableEq X] [DecidableEq Y] in
/-- **Two laws with the same half marginals differ by at most `r + s`** (`lem:tr:repair`(f), last
claim): if `P`, `Q` (on spaces `Ω₁`, `Ω₂`, with halves `a₁, b₁` and `a₂, b₂`) both have the half
marginals `μX`, `μY`, with centred norms at most `r` and `s`, then
`|E_P[φ(a₁)ψ(b₁)] − E_Q[φ(a₂)ψ(b₂)]| ≤ (r + s)‖φ‖_{μX}‖ψ‖_{μY}` for all `φ`, `ψ`. -/
theorem coupling_change {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂] (P : FiniteLaw Ω₁)
    (Q : FiniteLaw Ω₂) (a₁ : Ω₁ → X) (b₁ : Ω₁ → Y) (a₂ : Ω₂ → X) (b₂ : Ω₂ → Y)
    (hP1 : ∀ φ, P.expect (fun ω => φ (a₁ ω)) = μX.expect φ)
    (hP2 : ∀ ψ, P.expect (fun ω => ψ (b₁ ω)) = μY.expect ψ)
    (hQ1 : ∀ φ, Q.expect (fun ω => φ (a₂ ω)) = μX.expect φ)
    (hQ2 : ∀ ψ, Q.expect (fun ω => ψ (b₂ ω)) = μY.expect ψ) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hPr : ∀ h k, μX.expect h = 0 → μY.expect k = 0 →
      |P.expect (fun ω => h (a₁ ω) * k (b₁ ω))| ≤ r * nrm μX h * nrm μY k)
    (hQs : ∀ h k, μX.expect h = 0 → μY.expect k = 0 →
      |Q.expect (fun ω => h (a₂ ω) * k (b₂ ω))| ≤ s * nrm μX h * nrm μY k) (φ : X → ℝ)
    (ψ : Y → ℝ) :
    |P.expect (fun ω => φ (a₁ ω) * ψ (b₁ ω)) - Q.expect (fun ω => φ (a₂ ω) * ψ (b₂ ω))| ≤
      (r + s) * nrm μX φ * nrm μY ψ := by
  have h := (coupling_difference μX μY (pairForm P a₁ b₁) (pairForm Q a₂ b₂)
    (fun φ => by rw [pairForm_apply, ← hP1 φ]; exact P.expect_congr fun ω => mul_one _)
    (fun ψ => by rw [pairForm_apply, ← hP2 ψ]; exact P.expect_congr fun ω => one_mul _)
    (fun φ => by rw [pairForm_apply, ← hQ1 φ]; exact Q.expect_congr fun ω => mul_one _)
    (fun ψ => by rw [pairForm_apply, ← hQ2 ψ]; exact Q.expect_congr fun ω => one_mul _)
    hr hs hPr hQs).2.2 φ ψ
  simp only [LinearMap.sub_apply, pairForm_apply] at h
  exact h

end Sarkozy.F7Repair
