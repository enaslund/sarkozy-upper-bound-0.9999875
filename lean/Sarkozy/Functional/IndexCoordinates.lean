module

public import Sarkozy.Functional.SignedIndex
public import Mathlib.Data.ZMod.QuotientRing

@[expose] public section

/-!
# The coordinates of the index space (`def:hyb:coupled`(a))

`def:hyb:coupled`(a): "By the Chinese remainder theorem `Ω = ∏_{j ∈ 𝒦} Ω_j` is a
product of cyclic groups indexed by the coordinates `𝒦 = ⨆_e 𝒦_e`: the interval
coordinate `b_e` and the prime-power residues `s_e mod p^{h_p}` for `p ∣ M₀`."

`queryCRT` is the isomorphism `ℤ/Kℤ × ℤ/M₀ℤ ≃ ℤ/Kℤ × ∏_{p ∣ M₀} ℤ/p^{h_p}ℤ`,
`h_p = v_p(M₀)`, from mathlib's `ZMod.equivPi`. `uniform_map_queryCRT` shows that
it carries the uniform law of a query index to the product of the uniform laws of
its coordinates. With `uniform_pi_eq_pi_uniform` (product over the queries), the
uniform law on `Ω` is therefore the product of the uniform laws on all the
coordinates `𝒦`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.Functional

/-- The prime-power coordinate moduli `p^{h_p}`, `p ∣ M₀`. -/
def residueCoordinate (M0 : ℕ) (p : M0.primeFactors) : ℕ := (p : ℕ) ^ M0.factorization p

instance residueCoordinate_neZero (M0 : ℕ) (p : M0.primeFactors) :
    NeZero (residueCoordinate M0 p) :=
  ⟨pow_ne_zero _ (Nat.prime_of_mem_primeFactors p.2).ne_zero⟩

/-- A bijection carries the uniform law to the uniform law. -/
theorem uniform_map_equiv {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    [DecidableEq β] (e : α ≃ β) : (FiniteLaw.uniform α).map e = FiniteLaw.uniform β := by
  apply finiteLaw_ext
  intro b
  simp only [FiniteLaw.map, FiniteLaw.uniform]
  rw [Fintype.sum_equiv e _ (fun b' => if b' = b then (Fintype.card α : ℝ)⁻¹ else 0)
    (fun ω => rfl), Finset.sum_ite_eq' univ b, ite_eq_left (mem_univ b), Fintype.card_congr e]

/-- `ℤ/M₀ℤ ≅ ∏_{p ∣ M₀} ℤ/p^{h_p}ℤ` (mathlib's Chinese remainder theorem). -/
noncomputable def residueCRT (M0 : ℕ) (hM0 : M0 ≠ 0) :
    ZMod M0 ≃+* ∀ p : M0.primeFactors, ZMod (residueCoordinate M0 p) :=
  ZMod.equivPi M0 hM0

/-- `def:hyb:coupled`(a): the CRT carries the uniform law on `ℤ/M₀ℤ` to the
product of the uniform laws on the prime-power coordinates. -/
theorem uniform_map_residueCRT (M0 : ℕ) [NeZero M0] :
    (FiniteLaw.uniform (ZMod M0)).map (residueCRT M0 (NeZero.ne M0)).toEquiv =
      FiniteLaw.pi (fun p : M0.primeFactors => FiniteLaw.uniform (ZMod (residueCoordinate M0 p))) := by
  rw [uniform_map_equiv]
  exact uniform_pi_eq_pi_uniform

/-- The coordinates of one query index `ω_e = (b_e, s_e)`: the interval coordinate
and the prime-power residues. -/
noncomputable def queryCRT (K M0 : ℕ) (hM0 : M0 ≠ 0) :
    ZMod K × ZMod M0 ≃ ZMod K × ∀ p : M0.primeFactors, ZMod (residueCoordinate M0 p) :=
  Equiv.prodCongr (Equiv.refl _) (residueCRT M0 hM0).toEquiv

/-- `def:hyb:coupled`(a): the uniform law of a query index is the product of the
uniform laws of its coordinates. -/
theorem uniform_map_queryCRT (K M0 : ℕ) [NeZero K] [NeZero M0] :
    (FiniteLaw.uniform (ZMod K × ZMod M0)).map (queryCRT K M0 (NeZero.ne M0)) =
      (FiniteLaw.uniform (ZMod K)).product
        (FiniteLaw.pi (fun p : M0.primeFactors => FiniteLaw.uniform (ZMod (residueCoordinate M0 p)))) := by
  rw [uniform_map_equiv]
  apply finiteLaw_ext
  intro ω
  rw [← uniform_pi_eq_pi_uniform]
  simp [FiniteLaw.uniform, FiniteLaw.product, Fintype.card_prod]
  ring

end Sarkozy.Functional
