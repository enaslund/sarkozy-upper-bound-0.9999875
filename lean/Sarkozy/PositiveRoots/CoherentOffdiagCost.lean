module

public import Sarkozy.PositiveRoots.CoherentOffdiagKeys

/-! Exact rational accounting of the 1,521 off-diagonal covariance pairs. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Sarkozy.PartV.CoherentDictionary Sarkozy.L20Cap

def coreCostMass (st : (Support × ℚ) × (Support × ℚ)) : ℚ :=
  if (covarianceCase st.1.1 st.2.1).1 then 0
  else |st.1.2 * st.2.2| * (corePairCost st.1.1 st.2.1 : ℚ)

def privateCostMass (st : (Support × ℚ) × (Support × ℚ)) : ℚ :=
  if (covarianceCase st.1.1 st.2.1).1 then
    |st.1.2 * st.2.2| * (privatePairCost st.1.1 st.2.1 : ℚ)
  else 0

theorem core_cost_mass : ((dictionary39.product dictionary39).map coreCostMass).sum =
    17280 / 225 := core_cost_keys

theorem private_cost_mass : ((dictionary39.product dictionary39).map privateCostMass).sum =
    1448 / 225 := private_cost_keys

noncomputable def coherentOffdiagPrice (p : ℕ) : ℝ :=
  (p : ℝ)⁻¹ * ((17280 / 225 : ℝ) / 16 * coreCubeDensity p +
    (1448 / 225 : ℝ) * ((p : ℝ) / (p - 1)))

theorem offdiag_price_sum (p : ℕ) :
    ((dictionary39.product dictionary39).map fun st =>
      |((st.1.2 * st.2.2 : ℚ) : ℝ)| * offdiagPairPrice p st.1.1 st.2.1).sum =
      coherentOffdiagPrice p := by
  have he (st : (Support × ℚ) × (Support × ℚ)) :
      |((st.1.2 * st.2.2 : ℚ) : ℝ)| * offdiagPairPrice p st.1.1 st.2.1 =
        (coreCostMass st : ℝ) * (coreCubeDensity p / 16 * (p : ℝ)⁻¹) +
          (privateCostMass st : ℝ) * (((p : ℝ) / (p - 1)) * (p : ℝ)⁻¹) := by
    unfold offdiagPairPrice coreCostMass privateCostMass
    split_ifs <;> push_cast <;> ring
  simp_rw [he]
  rw [List.sum_map_add, List.sum_map_mul_right, List.sum_map_mul_right]
  have hcore := congrArg (fun q : ℚ => (q : ℝ)) core_cost_mass
  have hprivate := congrArg (fun q : ℚ => (q : ℝ)) private_cost_mass
  simp only [Rat.cast_list_sum, List.map_map, Function.comp_def, Rat.cast_div,
    Rat.cast_ofNat] at hcore hprivate
  rw [hcore, hprivate]
  unfold coherentOffdiagPrice
  ring

theorem coherentOffdiagPrice_paper (p : ℕ) (hp : 1 < p) :
    coherentOffdiagPrice p = (1 / (p : ℝ)) *
      (17280 / (225 * ((1 - 1 / p) * (1 - 3 / p) * (1 - 7 / p))) +
        1448 / (225 * (1 - 1 / p))) := by
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp
  have he : (p : ℝ) / (p - 1) = 1 / (1 - 1 / p) := by field_simp
  unfold coherentOffdiagPrice coreCubeDensity
  rw [he]
  simp only [div_eq_mul_inv, mul_inv]
  ring

end Sarkozy.PositiveRoots.CoherentFrame
