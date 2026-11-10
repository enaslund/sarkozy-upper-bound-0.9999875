module

public import Sarkozy.JointRows.StarMeanBound

/-! The full star estimate used for the conditional rows in the tail. -/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows.StarOps

open Finset Sarkozy.FiveType Sarkozy.FiveType.Blocks

variable {p : ℕ} [Fact p.Prime]
variable {X : Type*} [Fintype X] [DecidableEq X]

theorem starKernel_bound_odd (hp : p ≠ 2) (νp : X → FiniteLaw (ZMod p))
    (D : X → X → ℝ) (𝒮 : Finset (Finset X))
    {κ β d G : ℝ} (hκ : 0 < κ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hd : 0 ≤ d) (hG : 0 ≤ G) (hD1 : ∀ i j, |D i j| ≤ 1)
    (hdens : ∀ i t, (νp i).weight t ≤ κ / p)
    (hm : ∀ i j t, (νp i).weight t ≠ 0 → |mchi (νp j) t| ≤ β)
    (h𝒮 : ∀ S ∈ 𝒮, 2 ≤ S.card)
    (hD : Influence.OpBound univ univ (fun i j => |D i j|) d)
    (hA : ∀ i, ∑ i', ∑ T ∈ 𝒮,
      |rowParityCoef (p := p) D i T| * |rowParityCoef (p := p) D i' T| ≤ G)
    (hB : ∀ j, ∑ j', ∑ S ∈ 𝒮, |coefB D j S| * |coefB D j' S| ≤ G)
    (f g : (X → ZMod p) → ℝ)
    (hf : (blockLaw νp).expect f = 0) (hg : (blockLaw νp).expect g = 0) :
    |bform νp νp (starKernel D 𝒮) f g| ≤
      κ * (Real.sqrt p)⁻¹ *
        (Star.eStar d (Real.sqrt G) +
          2 * Fintype.card X * 𝒮.card * 2 ^ Fintype.card X * β) *
        nrm (blockLaw νp) f * nrm (blockLaw νp) g := by
  rw [show starKernel D 𝒮 = fun x y =>
    pureKernel νp νp D 𝒮 (rowParityCoef (p := p) D) 𝒮 (coefB D) x y +
      meanKernelPrime νp D 𝒮 x y from
        funext fun x => funext fun y => starKernel_eq_prime νp D 𝒮 x y, bform_add]
  have hpure := pureKernel_bound_odd hp νp νp D 𝒮 (rowParityCoef (p := p) D) 𝒮
    (coefB D) hκ hd hG hdens hdens h𝒮 h𝒮 hD hA hB f g hf hg
  have hmean := meanKernelPrime_bound hp νp D 𝒮 hκ.le hβ0 hβ1 hD1 hdens hm f g hf hg
  exact ((abs_add_le _ _).trans (add_le_add hpure hmean)).trans_eq (by ring)

end Sarkozy.JointRows.StarOps
