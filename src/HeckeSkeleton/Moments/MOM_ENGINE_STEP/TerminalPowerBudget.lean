import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondTailBudget

/-!
# The elementary common-cutoff tail budget

The original power bound is multiplied by the common physical cutoff.
All constants and the original amplitude remain explicit. This public
entry is used by the actual finite-source terminal estimates.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStep

theorem terminal_tail_power_bound
    (mass Cnum Amp Z L Lmax N Ctail decay : ℝ)
    (hZ : 1 ≤ Z) (hdecay : 1 < decay) (hL : L ≤ Lmax)
    (hCtail : 0 ≤ Ctail) (hCnum : 0 ≤ Cnum) (hAmp : 0 ≤ Amp)
    (hmass : mass ≤ Cnum * Amp * Z ^ L) :
    Ctail * (Z ^ firstTailCutoffExponent Lmax N decay) ^ (1 - decay) * mass ≤
      (Ctail * Cnum) * Amp * Z ^ (-N) := by
  have hZ0 : 0 ≤ Z := zero_le_one.trans hZ
  calc
    _ ≤ Ctail * (Z ^ firstTailCutoffExponent Lmax N decay) ^ (1 - decay) *
        (Cnum * Amp * Z ^ L) :=
      mul_le_mul_of_nonneg_left hmass
        (mul_nonneg hCtail (Real.rpow_nonneg (Real.rpow_nonneg hZ0 _) _))
    _ = (Ctail * Cnum) * Amp *
        ((Z ^ firstTailCutoffExponent Lmax N decay) ^ (1 - decay) * Z ^ L) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (first_tail_cutoff_power_of_le Z L Lmax N decay hZ hdecay hL)
      (mul_nonneg (mul_nonneg hCtail hCnum) hAmp)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.terminal_tail_power_bound
