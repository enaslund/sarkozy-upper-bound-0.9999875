module

public import Sarkozy.Param.PaperMain
public import Sarkozy.Param.Compat
public import Sarkozy.TheoremC.MainTheta
public import Sarkozy.TheoremC.Energy

@[expose] public section

/-!
# Compatibility with WP-FI's closing-number forms in `Sarkozy.TheoremC`

`Sarkozy/TheoremC/MainTheta.lean` and `Sarkozy/TheoremC/Energy.lean` state the conditional main
theorem and its energy form for an arbitrary closing number below one, at the hard-coded
exponents. These are the entry points through which `Sarkozy.TheoremC.ComparisonData.theoremC`
and `theoremC_energy` reach the endgame. Each theorem below has, by construction
(`type_of% @…`), exactly the statement of the `Sarkozy.TheoremC` theorem it names, and proves
it from the parametrized version in `Sarkozy.Param` at the record exponent.

So a generalization of `Sarkozy.TheoremC` to a free price exponent can call the parametrized
versions (`Sarkozy.Param.paperMain_powerSavingBound_theta` and the others) in place of these six,
and recover the present statements at `a = decay`.
-/

open Filter
open scoped Topology

namespace Sarkozy.Param

theorem scaledEnergyEstimate_transfer_viaParam :
    type_of% @Sarkozy.TheoremC.ScaledEnergyEstimate.transfer := by
  intro Y Y' h hY
  exact ScaledEnergyEstimate.transfer (P := Params.paper) h hY

theorem prefixedResidueModel_scaledEnergyEstimate_theta_viaParam :
    type_of% @Sarkozy.TheoremC.prefixedResidueModel_scaledEnergyEstimate_theta := by
  intro J _ _ p _ X₀ _ _ model ha hprefix hzero hm hp C hC hmixed k L₀ Jn W H hθ e
  exact PrefixedResidueModel.scaledEnergyEstimate_of_closingEstimates_theta (a := Sarkozy.decay)
    Params.paper_valid model ha hprefix hzero hm hp hC hmixed hθ e.toParam

theorem paperMain_scaledEnergyEstimate_theta_viaParam :
    type_of% @Sarkozy.TheoremC.paperMain_scaledEnergyEstimate_theta := by
  intro J₀ _ _ m₀ _ J _ _ p _ hp hinj μ₀ μp hm₀ hp₀ hmp hpp hunit k L₀ Jn W H hθ e
  exact paperMain_scaledEnergyEstimate_theta (a := Sarkozy.decay) m₀ p Params.paper_valid hp
    hinj μ₀ μp hm₀ hp₀ hmp hpp hunit hθ e.toParam

theorem prefixedResidueModel_powerSavingBound_theta_viaParam :
    type_of% @Sarkozy.TheoremC.prefixedResidueModel_powerSavingBound_theta := by
  intro J _ _ p _ X₀ _ _ model ha hprefix hzero hm hp C hC hmixed k L₀ Jn W H hθ e
  exact powerSavingBound_paper.mp
    (PrefixedResidueModel.powerSavingBound_of_closingEstimates_theta (a := Sarkozy.decay)
      Params.paper_valid model ha hprefix hzero hm hp hC hmixed hθ e.toParam)

theorem paperMain_powerSavingBound_theta_viaParam :
    type_of% @Sarkozy.TheoremC.paperMain_powerSavingBound_theta := by
  intro J₀ _ _ m₀ _ J _ _ p _ hp hinj μ₀ μp hm₀ hp₀ hmp hpp hunit k L₀ Jn W H hθ e
  exact powerSavingBound_paper.mp
    (paperMain_powerSavingBound_theta (a := Sarkozy.decay) m₀ p Params.paper_valid hp hinj μ₀
      μp hm₀ hp₀ hmp hpp hunit hθ e.toParam)

theorem paperMain_powerSavingBound_theta_ref_viaParam :
    type_of% @Sarkozy.TheoremC.paperMain_powerSavingBound_theta_ref := by
  intro J₀ _ _ m₀ _ J _ _ p _ hp hinj μ₀ μp hm₀ hp₀ hmp hpp hunit k L₀ Jn W H hθ e
  exact powerSavingBound_paper.mp
    (paperMain_powerSavingBound_theta_ref (a := Sarkozy.decay) m₀ p Params.paper_valid hp hinj
      μ₀ μp hm₀ hp₀ hmp hpp hunit hθ e.toParam)

end Sarkozy.Param
