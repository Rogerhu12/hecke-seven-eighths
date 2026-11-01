import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFullKappaNormalization

/-!
# The actual right frame uses the right original common ideal

The right Fourier source and its calibrated data are unchanged. Its
raw degree contains the right second-common ideal, so the original
prime-power capacity dictionary is read in the corresponding order.
The complete sixth root, gcd and pattern unit ideal are the same ones;
there is no new frequency, row, profile or capacity choice.

This complements the original left-oriented pattern constructor. The
same actual right frame enters the normalized family and its existing
mass calculation, whose right length dictionary already uses the
swapped original common ideals.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain
open DedekindZetaZeroFree (SArithmeticData)
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable [IsPrincipalIdealRing A.R]
variable {U E H : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ω ψ : HeckeCharacter K} {k : ℕ}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]

namespace SecondSideNormalization

variable (f : SecondSideFrame (V := WithLp 2 (U × E)) C R Ray .right k)
variable (D : f.source.Calibration (σ := σ) ω ψ)
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {rowInput : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable (Q : CompleteMovingRowRecipe A P rowInput D.data)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {seminorms : Finset (ℕ × ℕ)}
variable {B δ lengthBound analyticHeight width : ℝ} {J₁ J₂ : ℕ}
variable (profiles : D.FullKappaProfileInput Q rowDomain heightDomain window seminorms
  B J₁ J₂ δ lengthBound analyticHeight width)
variable (parent : MomentData K ω ψ) (a : RealParameters) (step : ℝ)
variable (G : OriginalNominalGeometry (K := K) a f.source.base step)
variable (binding : D.OriginalSixthLengthBinding parent a step G
  (idealLogLength f.source.base
    (secondSixthRootIdeal R.primes R.rightMultiplicity R.leftMultiplicity).val))
variable (hm : ∀ i, 0 < R.leftMultiplicity i) (hn : ∀ i, 0 < R.rightMultiplicity i)
variable (pattern : ι → Bool)
variable (hsecond : G.ideals.second.val = (primePowerProduct R.primes R.rightMultiplicity).val)
variable (hopposite : G.ideals.secondOpposite.val =
  (primePowerProduct R.primes R.leftMultiplicity).val)
variable (hunit : G.ideals.unitPart.val =
  (secondPatternUnitIdeal R.primes R.rightMultiplicity R.leftMultiplicity pattern).val)
variable (hstep : 0 < step) (mesh : ℝ) (hmesh : 0 ≤ mesh)
variable (hfit : parent.geometry.fitsMesh mesh)

/-- The original right source uses the same actual profile windows,
but the right original common ideal in its capacity ledger. -/
def ofFullKappaOriginalRightPattern :
    SecondSideNormalization f ω ψ rowDomain heightDomain window seminorms where
  calibration := D
  capacity := binding.capacityInputOfPattern R.primes_injective hn hm pattern
    hsecond hopposite hunit hstep mesh hmesh hfit profiles.atoms
  amplitude := profiles.amplitude
  amplitude_pos := profiles.amplitude_pos
  bounds := fun _ => 1
  bounds_nonneg := fun _ => zero_le_one
  factor := profiles.atoms_primeBound
  profile := profiles.clippedWindow

@[simp] theorem ofFullKappaOriginalRightPattern_calibration :
    (ofFullKappaOriginalRightPattern f D Q profiles parent a step G binding hm hn pattern
      hsecond hopposite hunit hstep mesh hmesh hfit).calibration = D := rfl

@[simp] theorem ofFullKappaOriginalRightPattern_radius (z : U × E) :
    (ofFullKappaOriginalRightPattern f D Q profiles parent a step G binding hm hn pattern
      hsecond hopposite hunit hstep mesh hmesh hfit).normalizedCapacityData.radius
        (WithLp.toLp 2 z) = polynomialProfileRadius profiles.coefficient J₁ J₂ z := rfl

@[simp] theorem ofFullKappaOriginalRightPattern_primeBound
    (i : Fin f.source.allocation.keep.card) :
    (ofFullKappaOriginalRightPattern f D Q profiles parent a step G binding hm hn pattern
      hsecond hopposite hunit hstep mesh hmesh hfit).normalizedCapacityData.primeBound i = 1 := rfl

/-- This equality exposes the exact already selected capacity input
for the existing same-child right-side mass theorem. -/
@[simp] theorem ofFullKappaOriginalRightPattern_capacity :
    (ofFullKappaOriginalRightPattern f D Q profiles parent a step G binding hm hn pattern
      hsecond hopposite hunit hstep mesh hmesh hfit).capacity =
      binding.capacityInputOfPattern R.primes_injective hn hm pattern
        hsecond hopposite hunit hstep mesh hmesh hfit profiles.atoms := rfl

end SecondSideNormalization
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideNormalization.ofFullKappaOriginalRightPattern
#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideNormalization.ofFullKappaOriginalRightPattern_capacity
