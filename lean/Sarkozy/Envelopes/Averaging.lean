module

public import Sarkozy.Labellings.Patterns
public import Sarkozy.Reflection.Tensor
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Averaging a dominating matrix over reflections (`lem:reflection-averaging`)

`paper/sections/23_envelopes.tex`, `lem:reflection-averaging`.

**Proved here.**
* (a) **Placements**, the reflection rows of `tab:reflection`, exactly: for `h ∈ {1, 3, 5}` the
  folds `F_j ∘ R_h` (`fold_reflection_table`), the matchings `E_s ∘ R_h = ψ_{h,s} ∘ E_s` with the
  paper's `ψ_{h,s}` (`matching_reflection_table`), the merges `G_{sk} ∘ R_h = G_{s,ψ_{h,s}(k)}`
  (`merge_reflection_table`), and the fact that `F_0 ∘ R_5 = F_0`, `F_1 ∘ R_3 = F_1`,
  `F_2 ∘ R_1 = F_2` are the only fixed cases (`fold_fixed_iff`). `R_h` acts on the first slot
  coordinate as `chamberRefl h` of `Sarkozy.Labellings`.
* (c) **Energy invariance**, for the project's energies `Y_ρ = diagonalIntegral ρ F_A`
  (`∫ ∏_v F_A(z_v) dρ`): the push-forward `α_*ρ` by a slot permutation (`slotPush`) has the same
  energy (`diagonalIntegral_slotPush`), the push-forward commutes with tensor products over the
  atoms (`slotPush_tensorLaw`), so `α_*(κ ⊗ O) = α_*κ ⊗ O` when every outside factor is invariant
  (`slotPush_tensor_invariant`), and `Y_{α_*κ ⊗ O} = Y_{κ ⊗ O}` (`energy_slotPush_outside`).
  The order statement `κ ⪰_ι κ' ⇒ α_*κ ⪰_ι α_*κ'` holds for every slot permutation preserving the
  half and commuting with the flip (`slotPush_positive`, `slotPush_mono`).
* (d) **Averaging**, in abstract form (`reflection_average`): over a finite set of assignments with
  an involution `ω ↦ ω̄` and weights `π_ω̄ = π_ω`, if the energies satisfy the transport
  `Y_ω̄(K) = Y_ω(P_ω K)` (from (a) and (c)) and the operators satisfy `K_ω̄ = T_ω K_ω`, then
  `∑ π_ω Y_ω(K_ω) = ∑ π_ω Y_ω(½(K_ω + g_ω K_ω))` with `g_ω = P_ω T_ω`.
* (e)–(g) **the permutation identities** used in the charts (`chart_identities`): the chart
  reflection `P_{(01)} P_{(02)} P_{(01)} = P_{(12)}`, the extra-reflection charts
  `(01)(12)(01) = (02)`, the conjugacy by `(12)`, `(01)c = c⁻¹(01) = ε`, `ψ_{1,α} = c ψ_{0,α} c⁻¹`
  on the generators, and the surjectivity of `α ↦ ψ_{0,α}` (`psi0_generates`).
* (g) **the numbers**: the group weights `(1/8, 1/2, 3/8)` and `(1/32, 3/16, 15/32, 5/16)`
  (`matching_group_weights`), and the crossed-pair caps `(1 + √3)/6` and the aligned bound
  `(a + d)/3 ≥ 2/3` (`crossed_pair_cap`, `aligned_pair_bound`).

**Not formalized:** (b) (the arithmetic transport `𝒰` on `L²(m₀)`), which needs the actual fold
marginal (the old fold law), and the placement map `K ↦ [K]_ω` itself; (d) is stated for abstract
energies `Y_ω`.
-/

namespace Sarkozy.Envelopes

open Sarkozy.Labellings

/-! ### (a) The reflection rows of `tab:reflection` -/

/-- **`lem:reflection-averaging`(a), folds.** `(F_0, F_1, F_2) ∘ R_1 = (F_1, F_0, F_2)`,
`∘ R_3 = (F_2, F_1, F_0)`, `∘ R_5 = (F_0, F_2, F_1)`. -/
theorem fold_reflection_table (u : ZMod 6) :
    (fold 0 (chamberRefl 1 u) = fold 1 u ∧ fold 1 (chamberRefl 1 u) = fold 0 u ∧
      fold 2 (chamberRefl 1 u) = fold 2 u) ∧
    (fold 0 (chamberRefl 3 u) = fold 2 u ∧ fold 1 (chamberRefl 3 u) = fold 1 u ∧
      fold 2 (chamberRefl 3 u) = fold 0 u) ∧
    (fold 0 (chamberRefl 5 u) = fold 0 u ∧ fold 1 (chamberRefl 5 u) = fold 2 u ∧
      fold 2 (chamberRefl 5 u) = fold 1 u) := by
  revert u; decide

/-- The permutations `ψ_{h,s}` of `lem:reflection-averaging`(a):
`ψ_{1,0} = (0 1)`, `ψ_{1,1} = (1 2)`, `ψ_{3,0} = (0 2)`, `ψ_{3,1} = (0 1)`, `ψ_{5,0} = (1 2)`,
`ψ_{5,1} = (0 2)`. -/
def psiRefl (h : ZMod 6) (s : Fin 2) : Equiv.Perm (Fin 3) :=
  if h = 1 then (if s = 0 then Equiv.swap 0 1 else Equiv.swap 1 2)
  else if h = 3 then (if s = 0 then Equiv.swap 0 2 else Equiv.swap 0 1)
  else (if s = 0 then Equiv.swap 1 2 else Equiv.swap 0 2)

/-- **`lem:reflection-averaging`(a), matchings.** `E_s ∘ R_h = ψ_{h,s} ∘ E_s`. -/
theorem matching_reflection_table (h : ZMod 6) (hh : h = 1 ∨ h = 3 ∨ h = 5) (s : Fin 2)
    (u : ZMod 6) : matching s (chamberRefl h u) = psiRefl h s (matching s u) := by
  rcases hh with rfl | rfl | rfl <;> revert s u <;> decide

/-- **`lem:reflection-averaging`(a), merges.** `G_{sk} ∘ R_h = G_{s,ψ_{h,s}(k)}` (each
`ψ_{h,s}` is an involution). -/
theorem merge_reflection_table (h : ZMod 6) (hh : h = 1 ∨ h = 3 ∨ h = 5) (s : Fin 2) (k : Fin 3)
    (u : ZMod 6) : merge s k (chamberRefl h u) = merge s (psiRefl h s k) u := by
  rcases hh with rfl | rfl | rfl <;> revert s k u <;> decide

/-- **`lem:reflection-averaging`(a), fixed folds.** For `h ∈ {1, 3, 5}`, `F_j ∘ R_h = F_j` only for
`F_0 ∘ R_5`, `F_1 ∘ R_3` and `F_2 ∘ R_1`. -/
theorem fold_fixed_iff (j : Fin 3) (h : ZMod 6) (hh : h = 1 ∨ h = 3 ∨ h = 5) :
    (∀ u, fold j (chamberRefl h u) = fold j u) ↔
      (j = 0 ∧ h = 5) ∨ (j = 1 ∧ h = 3) ∨ (j = 2 ∧ h = 1) := by
  rcases hh with rfl | rfl | rfl <;> revert j <;> decide

/-! ### (c) Energy invariance under slot permutations -/

section EnergyInvariance

variable {V X : Type*}

/-- The push-forward `α_*ρ` of a finite signed measure on labellings `V → X` by a slot
permutation: the law of `z ∘ α` (`R_{h*}κ` of `lem:reflection-averaging`). -/
noncomputable def slotPush (α : V ≃ V) (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) :
    ((V → X) → ℝ) →ₗ[ℝ] ℝ :=
  L.comp (LinearMap.funLeft ℝ ℝ (fun z : V → X => z ∘ α))

theorem slotPush_apply (α : V ≃ V) (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (F : (V → X) → ℝ) :
    slotPush α L F = L (fun z => F (z ∘ α)) := rfl

/-- **`lem:reflection-averaging`(c), the change of variables.** `Y_{α_*ρ} = Y_ρ` for every finite
signed measure `ρ` on labellings, the same input at every slot. -/
theorem diagonalIntegral_slotPush [Fintype V] (α : V ≃ V) (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (g : X → ℝ) :
    diagonalIntegral (slotPush α L) g = diagonalIntegral L g := by
  unfold diagonalIntegral multilinearIntegral
  rw [slotPush_apply]
  congr 1
  funext z
  exact Equiv.prod_comp α (fun v => g (z v))

end EnergyInvariance

section Order

variable {V X : Type*} [Fintype V] [DecidableEq V]

/-- **`lem:reflection-averaging`(c), the order.** If the slot permutation `α` maps the half `V_+`
onto itself and commutes with the flip of the cut (as `R_h` does at `ι`: it fixes the layer), then
the cut form of `α_*L` is the cut form of `L` at the transported half-functions; so
`L ⪰_ι 0` implies `α_*L ⪰_ι 0`. -/
theorem slotPush_positive {c : ReflectionCut V} (α : V ≃ V)
    (hhalf : ∀ v, α v ∈ c.half ↔ v ∈ c.half) (hflip : ∀ v, α (c.flip v) = c.flip (α v))
    {L : ((V → X) → ℝ) →ₗ[ℝ] ℝ} (hL : c.Positive L) : c.Positive (slotPush α L) := by
  let αh : c.Half → c.Half := fun v => ⟨α v.1, (hhalf v.1).2 v.2⟩
  let tr : ((c.Half → X) → ℝ) → ((c.Half → X) → ℝ) := fun F x => F (fun v => x (αh v))
  have hform : ∀ F G, c.form (slotPush α L) F G = c.form L (tr F) (tr G) := by
    intro F G
    unfold ReflectionCut.form
    rw [slotPush_apply]
    congr 1
    funext z
    simp only [Function.comp_apply, tr, αh, hflip]
  exact ⟨fun F G => by rw [hform, hform, hL.symmetric], fun F => by rw [hform]; exact hL.nonneg _⟩

/-- **`lem:reflection-averaging`(c), the order between measures.** Under the same conditions,
`κ ⪰_ι κ'` (i.e. `κ - κ' ⪰_ι 0`) implies `α_*κ ⪰_ι α_*κ'`. -/
theorem slotPush_mono {c : ReflectionCut V} (α : V ≃ V)
    (hhalf : ∀ v, α v ∈ c.half ↔ v ∈ c.half) (hflip : ∀ v, α (c.flip v) = c.flip (α v))
    {L L' : ((V → X) → ℝ) →ₗ[ℝ] ℝ} (h : c.Positive (L - L')) :
    c.Positive (slotPush α L - slotPush α L') := by
  have e : slotPush α L - slotPush α L' = slotPush α (L - L') := by
    unfold slotPush; rw [LinearMap.sub_comp]
  rw [e]
  exact slotPush_positive α hhalf hflip h

end Order

section Tensor

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]

omit [Fintype J] [DecidableEq J] [DecidableEq V] in
theorem lawDensity_slotPush {Y : Type*} [Fintype Y] [DecidableEq Y] (α : V ≃ V)
    (L : ((V → Y) → ℝ) →ₗ[ℝ] ℝ) (y : V → Y) :
    lawDensity (slotPush α L) y = lawDensity L (y ∘ α.symm) := by
  unfold lawDensity
  rw [slotPush_apply]
  congr 1
  funext x
  have : (x ∘ α = y) ↔ (x = y ∘ α.symm) := by
    constructor
    · rintro rfl; funext v; simp
    · rintro rfl; funext v; simp
  exact if_congr this rfl rfl

/-- **`lem:reflection-averaging`(c), the product.** The push-forward by a slot permutation (acting
at every atom) commutes with the tensor product over the atoms. -/
theorem slotPush_tensorLaw (α : V ≃ V) (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) :
    slotPush α (tensorLaw L) = tensorLaw (fun j => slotPush α (L j)) := by
  apply LinearMap.ext
  intro F
  rw [slotPush_apply]
  change (∑ z : ∀ j, V → X j, (∏ j, lawDensity (L j) (z j)) *
      F ((fun v j => z j v) ∘ α)) =
    ∑ z : ∀ j, V → X j, (∏ j, lawDensity (slotPush α (L j)) (z j)) * F (fun v j => z j v)
  simp only [lawDensity_slotPush]
  let e : (∀ j, V → X j) ≃ (∀ j, V → X j) :=
    Equiv.piCongrRight (fun j => Equiv.arrowCongr α.symm (Equiv.refl (X j)))
  conv_rhs => rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun z _ => ?_
  have h1 : ∀ j, (e z) j ∘ α.symm = z j := by
    intro j; funext v
    simp [e, Equiv.arrowCongr_apply]
  have h2 : (fun v j => (e z) j v) = (fun v j => z j v) ∘ α := by
    funext v j
    simp [e, Equiv.arrowCongr_apply]
  rw [h2]
  simp only [h1]

/-- **`lem:reflection-averaging`(c), invariant outside laws.** If every outside factor is
invariant under the slot permutation, `α_*(κ ⊗ O) = α_*κ ⊗ O`: the push-forward acts on the
selected atoms only. -/
theorem slotPush_tensor_invariant (α : V ≃ V) (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (S : Finset J) (hO : ∀ j ∉ S, slotPush α (L j) = L j) :
    slotPush α (tensorLaw L) =
      tensorLaw (fun j => if j ∈ S then slotPush α (L j) else L j) := by
  rw [slotPush_tensorLaw]
  congr 1
  funext j
  by_cases hj : j ∈ S
  · simp only [hj, ↓reduceIte]
  · simp only [hj, ↓reduceIte, hO j hj]

/-- **`lem:reflection-averaging`(c).** With an invariant outside law, transporting the selected
factors by a slot permutation does not change the energy:
`Y_{α_*κ ⊗ O} = Y_{κ ⊗ O}`. -/
theorem energy_slotPush_outside (α : V ≃ V) (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (S : Finset J) (hO : ∀ j ∉ S, slotPush α (L j) = L j) (g : (∀ j, X j) → ℝ) :
    diagonalIntegral (tensorLaw (fun j => if j ∈ S then slotPush α (L j) else L j)) g =
      diagonalIntegral (tensorLaw L) g := by
  rw [← slotPush_tensor_invariant α L S hO, diagonalIntegral_slotPush]

end Tensor

/-! ### (d) Averaging over the partner involution -/

/-- **`lem:reflection-averaging`(d), abstract form.** `Ω` is a finite set of record assignments with
an involution `ω ↦ ω̄` and weights `π_ω̄ = π_ω`. Each assignment has an energy `Y_ω` (linear in the
operator, `Y_ω(K) = Y_{[K]_ω ⊗ O}`), and the reflection transports the placements:
`Y_ω̄(K) = Y_ω(P_ω K)` (`P_ω K = 𝒫_ω K 𝒫_ω^*`, from (a) and (c)). If `K_ω̄ = T_ω K_ω`
(`T_ω K = 𝒯_ω K 𝒯_ω^*`), then with `g_ω = P_ω T_ω`,
`∑ π_ω Y_ω(K_ω) = ∑ π_ω Y_ω(½(K_ω + g_ω K_ω))`. -/
theorem reflection_average {Ω Op : Type*} [Fintype Ω] [AddCommGroup Op] [Module ℝ Op]
    (bar : Ω → Ω) (hbar : ∀ ω, bar (bar ω) = ω) (π : Ω → ℝ) (hπ : ∀ ω, π (bar ω) = π ω)
    (Y : Ω → Op →ₗ[ℝ] ℝ) (P T : Ω → Op →ₗ[ℝ] Op) (K : Ω → Op)
    (htrans : ∀ ω A, Y (bar ω) A = Y ω (P ω A)) (hK : ∀ ω, K (bar ω) = T ω (K ω)) :
    ∑ ω, π ω * Y ω (K ω) = ∑ ω, π ω * Y ω ((1 / 2 : ℝ) • (K ω + P ω (T ω (K ω)))) := by
  have hinv : Function.Involutive bar := hbar
  have hswap : ∑ ω, π ω * Y ω (K ω) = ∑ ω, π ω * Y ω (P ω (T ω (K ω))) := by
    rw [← Equiv.sum_comp (hinv.toPerm bar) (fun ω => π ω * Y ω (K ω))]
    refine Finset.sum_congr rfl fun ω _ => ?_
    simp only [Function.Involutive.coe_toPerm, hπ, htrans, hK]
  have e : ∀ ω, π ω * Y ω ((1 / 2 : ℝ) • (K ω + P ω (T ω (K ω)))) =
      (1 / 2 : ℝ) * (π ω * Y ω (K ω)) + (1 / 2 : ℝ) * (π ω * Y ω (P ω (T ω (K ω)))) := by
    intro ω
    rw [map_smul, map_add, smul_eq_mul]
    ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, ← hswap]
  ring

/-! ### (e)–(g) The permutation identities of the charts -/

/-- **`lem:reflection-averaging`(e)–(g), the chart identities** in `Sym({0, 1, 2})`
(`(σ * τ) x = σ (τ x)`), with `c = (0 1 2) = finRotate 3` and `ε = (1 2)`:
* (e) `(01)(02)(01) = (12)`: the chart reflection at an `E_1` factor;
* (f) `(01)(12)(01) = (02)`, and conjugation by `(12)` exchanges `(01)` and `(02)`;
* (g) `(01)c = c⁻¹(01) = ε`, and `ψ_{1,h} = c ψ_{0,h} c⁻¹` for the generators `h = 1, 3, 5`. -/
theorem chart_identities :
    Equiv.swap (0 : Fin 3) 1 * Equiv.swap 0 2 * Equiv.swap 0 1 = Equiv.swap 1 2 ∧
    Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 * Equiv.swap 0 1 = Equiv.swap 0 2 ∧
    Equiv.swap (1 : Fin 3) 2 * Equiv.swap 0 1 * Equiv.swap 1 2 = Equiv.swap 0 2 ∧
    Equiv.swap (0 : Fin 3) 1 * finRotate 3 = Equiv.swap 1 2 ∧
    (finRotate 3)⁻¹ * Equiv.swap (0 : Fin 3) 1 = Equiv.swap 1 2 ∧
    (∀ h : ZMod 6, h = 1 ∨ h = 3 ∨ h = 5 →
      psiRefl h 1 = finRotate 3 * psiRefl h 0 * (finRotate 3)⁻¹) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
  rintro h (rfl | rfl | rfl) <;> decide

/-- **`lem:reflection-averaging`(f), the aligned assignments.** On `n ≥ 1` fold blocks (a fold
record `F₁`/`F₂` coded by a Boolean at each block), exactly two assignments have all fold records
equal; with the `2^m` choices at the matching blocks they form the fraction
`2 · 2^m / 2^{n+m} = 2^{1-n}` of the class. -/
theorem aligned_count (n : ℕ) (hn : 0 < n) :
    (Finset.univ.filter (fun f : Fin n → Bool => (∀ i, f i = true) ∨ (∀ i, f i = false))).card
      = 2 ∧ ∀ m : ℕ, ((2 * 2 ^ m : ℕ) : ℝ) / ((2 ^ (n + m) : ℕ) : ℝ) = 2 / 2 ^ n := by
  refine ⟨?_, fun m => ?_⟩
  · have e : Finset.univ.filter (fun f : Fin n → Bool => (∀ i, f i = true) ∨ (∀ i, f i = false))
        = {fun _ => true, fun _ => false} := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, funext_iff]
    rw [e, Finset.card_pair]
    intro h
    have := congrFun h ⟨0, hn⟩
    simp at this
  · push_cast
    rw [pow_add]
    field_simp

/-- **`lem:reflection-averaging`(g), surjectivity.** The images `ψ_{0,1} = (01)` and
`ψ_{0,3} = (02)` generate `Sym({0, 1, 2})`: every permutation is a word of length at most three
in them, so `α ↦ ψ_{0,α}` is onto. -/
theorem psi0_generates (σ : Equiv.Perm (Fin 3)) :
    σ = 1 ∨ σ = psiRefl 1 0 ∨ σ = psiRefl 3 0 ∨ σ = psiRefl 1 0 * psiRefl 3 0 ∨
      σ = psiRefl 3 0 * psiRefl 1 0 ∨ σ = psiRefl 1 0 * psiRefl 3 0 * psiRefl 1 0 := by
  revert σ; decide

/-- **`lem:reflection-averaging`(g), the group weights.** A word with `k` coordinates `E_1` among
`m` has weight `C(m, k) 2^{-m}`; the groups `{k, m - k}` have the weights `(1/8, 1/2, 3/8)` for
`m = 4` and `(1/32, 3/16, 15/32, 5/16)` for `m = 6`. -/
theorem matching_group_weights :
    ((Nat.choose 4 0 + Nat.choose 4 4 : ℚ) / 2 ^ 4 = 1 / 8 ∧
      (Nat.choose 4 1 + Nat.choose 4 3 : ℚ) / 2 ^ 4 = 1 / 2 ∧
      (Nat.choose 4 2 : ℚ) / 2 ^ 4 = 3 / 8) ∧
    ((Nat.choose 6 0 + Nat.choose 6 6 : ℚ) / 2 ^ 6 = 1 / 32 ∧
      (Nat.choose 6 1 + Nat.choose 6 5 : ℚ) / 2 ^ 6 = 3 / 16 ∧
      (Nat.choose 6 2 + Nat.choose 6 4 : ℚ) / 2 ^ 6 = 15 / 32 ∧
      (Nat.choose 6 3 : ℚ) / 2 ^ 6 = 5 / 16) := by
  simp only [Nat.choose_zero_right, Nat.choose_self, Nat.choose_one_right]
  norm_num [Nat.choose]

/-- **`lem:reflection-averaging`(g), the crossed pair.** With `a = (1 + √3)/2`, `b = c = 1`,
`d = 1/a`, the mask conditions `ad ≥ 1`, `bc ≥ 1` hold, and both averages `a/3` (diagonal orbit)
and `(b + c + d)/6` (off it) equal `(1 + √3)/6`. -/
theorem crossed_pair_cap :
    let a : ℝ := (1 + Real.sqrt 3) / 2
    let d : ℝ := 1 / a
    1 ≤ a * d ∧ (1 : ℝ) ≤ 1 * 1 ∧ a / 3 = (1 + Real.sqrt 3) / 6 ∧
      (1 + 1 + d) / 6 = (1 + Real.sqrt 3) / 6 := by
  intro a d
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have ha : 0 < a := by positivity
  refine ⟨?_, by norm_num, ?_, ?_⟩
  · simp only [d]; rw [mul_one_div_cancel ha.ne']
  · simp only [a]; ring
  · simp only [d, a]
    field_simp
    nlinarith

/-- **`lem:reflection-averaging`(g), the aligned pair.** For two factors of one type, the diagonal
orbit receives `(a + d)/3 ≥ 2√(ad)/3 ≥ 2/3` whenever `a, d > 0` and `ad ≥ 1`. -/
theorem aligned_pair_bound {a d : ℝ} (ha : 0 < a) (hd : 0 < d) (had : 1 ≤ a * d) :
    2 / 3 ≤ (a + d) / 3 := by
  nlinarith [sq_nonneg (a - d)]

end Sarkozy.Envelopes
