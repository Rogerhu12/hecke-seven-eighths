import HeckeSkeleton.Moments.MOM_INV_STEP.InverseSpectralEnergy
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstMellinEnergy
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstCenteredMellinEnergy
import Mathlib.Util.PrintSorries

/-!
# Independent audit of the intermediate spectral estimates

This target is independent of the final source assembly, so its recursive
axiom checks remain available while a downstream module is being repaired.
-/

#print axioms HeckeSkeleton.Moments.MOM_INV_STEP.InverseSpectralEnergy.amplitude_continuous
#print axioms HeckeSkeleton.Moments.MOM_INV_STEP.InverseSpectralEnergy.amplitude_bound
#print axioms HeckeSkeleton.Moments.MOM_INV_STEP.InverseSpectralEnergy.summable_fixedProfile
#print axioms HeckeSkeleton.Moments.MOM_INV_STEP.InverseSpectralEnergy.spectral_term_bound
#print axioms HeckeSkeleton.Moments.MOM_INV_STEP.InverseSpectralEnergy.energy_continuous
#print axioms HeckeSkeleton.Moments.MOM_INV_STEP.InverseSpectralEnergy.energy_bound
#print axioms HeckeSkeleton.Moments.MOM_INV_STEP.InverseSpectralEnergy.weighted_energy_integrable
#print axioms HeckeSkeleton.Moments.MOM_INV_STEP.InverseSpectralEnergy.finite_rows_continuous
#print axioms HeckeSkeleton.Moments.MOM_INV_STEP.InverseSpectralEnergy.weighted_finite_rows_integrable
#print axioms HeckeSkeleton.Moments.MOM_INV_STEP.InverseSpectralEnergy.integral_finite_rows_le_energy
#print axioms HeckeSkeleton.Moments.MOM_INV_STEP.FirstMellinEnergy.free_energy_integrable
#print axioms HeckeSkeleton.Moments.MOM_INV_STEP.FirstMellinEnergy.residual_rows_le_free_energy
#print axioms HeckeSkeleton.Moments.MOM_INV_STEP.FirstCenteredMellinEnergy.free_energy_integrable
#print axioms HeckeSkeleton.Moments.MOM_INV_STEP.FirstCenteredMellinEnergy.residual_rows_le_free_energy

#print sorries HeckeSkeleton.Moments.MOM_INV_STEP.InverseSpectralEnergy.amplitude_continuous
#print sorries HeckeSkeleton.Moments.MOM_INV_STEP.InverseSpectralEnergy.amplitude_bound
#print sorries HeckeSkeleton.Moments.MOM_INV_STEP.FirstMellinEnergy.residual_rows_le_free_energy
#print sorries HeckeSkeleton.Moments.MOM_INV_STEP.FirstCenteredMellinEnergy.residual_rows_le_free_energy

set_option pp.all true in
#print HeckeSkeleton.Moments.MOM_INV_STEP.InverseSpectralEnergy.amplitude_continuous

set_option pp.all true in
#print HeckeSkeleton.Moments.MOM_INV_STEP.InverseSpectralEnergy.amplitude_bound

noncomputable section

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SpectralAudit

/-- An explicit-binder check of the smallest spectral continuity proof. -/
theorem amplitude_continuous_explicit
    (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
    (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
    (N : Finset (ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K)))))
    (a : ℝ → ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K))) → ℂ)
    (ha : ∀ n ∈ N, Continuous (fun t => a t n))
    (q : SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ) :
    Continuous (fun t => InverseRowMajorant.amplitude K S Γ D N (a t) q) := by
  exact continuous_finsetSum N (fun n hn => (ha n hn).mul continuous_const)

/-- An explicit-binder check of the smallest spectral coefficient bound. -/
theorem amplitude_bound_explicit
    (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
    (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
    (N : Finset (ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K)))))
    (a : ℝ → ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K))) → ℂ)
    (B : ℝ) (hbound : ∀ t, (∑ n ∈ N, ‖a t n‖) ≤ B)
    (t : ℝ) (q : SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ) :
    ‖InverseRowMajorant.amplitude K S Γ D N (a t) q‖ ≤ B :=
  (InverseRowMajorant.amplitude_norm_le K S Γ D N (a t) q).trans (hbound t)

end HeckeSkeleton.Moments.MOM_INV_STEP.SpectralAudit

end

#print axioms HeckeSkeleton.Moments.MOM_INV_STEP.SpectralAudit.amplitude_continuous_explicit
#print axioms HeckeSkeleton.Moments.MOM_INV_STEP.SpectralAudit.amplitude_bound_explicit
#print sorries HeckeSkeleton.Moments.MOM_INV_STEP.SpectralAudit.amplitude_continuous_explicit
#print sorries HeckeSkeleton.Moments.MOM_INV_STEP.SpectralAudit.amplitude_bound_explicit
