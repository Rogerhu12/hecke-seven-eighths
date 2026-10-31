import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualChildMassBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondHybridAllocation

/-!
# Move the actual common scalars before any row Cauchy estimate

Scalar extraction is an exact identity of the coupled complex form.
Only individual coefficient identities are used, so a complete centered
difference may be retained. The resulting actual row structure has its
literal new weight; the canonical arithmetic mass record is constructed
for this same structure, with no additional common denominator inserted.
-/

noncomputable section
open scoped Classical BigOperators NumberField FourierTransform SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters
open HeckePort.Moments

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- This equality precedes Fourier Cauchy. The right scalar is
conjugated exactly once by the original coupled pairing. -/
theorem joint_kernel_common_scalar_reweight {H I J : Type*}
    (Fker : 𝓢(V, ℂ)) (rows : Finset H) (left : Finset I) (right : Finset J)
    (q scalarLeft scalarRight : H → ℂ)
    (originalLeft residualLeft : H → I → ℂ)
    (originalRight residualRight : H → J → ℂ)
    (x : H → I → V) (y : H → J → V)
    (hleft : ∀ h ∈ rows, ∀ i ∈ left,
      originalLeft h i = scalarLeft h * residualLeft h i)
    (hright : ∀ h ∈ rows, ∀ j ∈ right,
      originalRight h j = scalarRight h * residualRight h j) :
    jointKernelPairing Fker rows left right q originalLeft originalRight x y =
      jointKernelPairing Fker rows left right
        (fun h => q h * scalarLeft h * star (scalarRight h)) residualLeft residualRight x y := by
  unfold jointKernelPairing
  apply Finset.sum_congr rfl
  intro h hh
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hleft h hh i hi, hright h hh j hj, star_mul']
  ring

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]

namespace ActualSecondCorrelationRows

variable (R : ActualSecondCorrelationRows A σ H ι)
variable {kLeft kRight : ℕ}

/-- The common atoms are moved from both columns into this actual row
weight. Arithmetic frequencies, generators and complete correlations
are inherited without replacement. -/
def withCommonAtoms
    (left : FrozenSourceAtoms A σ H R.rows kLeft)
    (right : FrozenSourceAtoms A σ H R.rows kRight) :
    ActualSecondCorrelationRows A σ H ι :=
  { R with weight := fun h => R.weight h * left.value h * star (right.value h) }

@[simp] theorem withCommonAtoms_correlation
    (left : FrozenSourceAtoms A σ H R.rows kLeft)
    (right : FrozenSourceAtoms A σ H R.rows kRight) (h : H) :
    (R.withCommonAtoms left right).correlation h = R.correlation h := rfl

/-- Each original per-column extraction is used inside the real complex
sum. Hence the following hybrid cost belongs to the same reweighted
actual rows used by the canonical mass and capacity calibration. -/
theorem common_atoms_hybrid_bound
    (Fker : 𝓢(V, ℂ))
    (leftAtoms : FrozenSourceAtoms A σ H R.rows kLeft)
    (rightAtoms : FrozenSourceAtoms A σ H R.rows kRight)
    {I J : Type*} (left : Finset I) (right : Finset J)
    (originalLeft residualLeft : H → I → ℂ)
    (originalRight residualRight : H → J → ℂ)
    (x : H → I → V) (y : H → J → V)
    (hleft : ∀ h ∈ R.rows, ∀ i ∈ left,
      originalLeft h i = leftAtoms.value h * residualLeft h i)
    (hright : ∀ h ∈ R.rows, ∀ j ∈ right,
      originalRight h j = rightAtoms.value h * residualRight h j)
    (exceptional : H → Prop) :
    ‖jointKernelPairing Fker R.rows left right
      (fun h => R.weight h * R.correlation h) originalLeft originalRight x y‖ ≤
      jointHybridKernelCost Fker R.rows left right
        (fun h => (R.withCommonAtoms leftAtoms rightAtoms).weight h *
          (R.withCommonAtoms leftAtoms rightAtoms).correlation h)
        residualLeft residualRight x y exceptional := by
  rw [joint_kernel_common_scalar_reweight Fker R.rows left right
    (fun h => R.weight h * R.correlation h) leftAtoms.value rightAtoms.value
    originalLeft residualLeft originalRight residualRight x y hleft hright]
  have hq : (fun h => (R.weight h * R.correlation h) * leftAtoms.value h *
      star (rightAtoms.value h)) =
      (fun h => (R.withCommonAtoms leftAtoms rightAtoms).weight h *
        (R.withCommonAtoms leftAtoms rightAtoms).correlation h) := by
    funext h
    dsimp only [withCommonAtoms, withCommonAtoms_correlation]
    ring
  rw [hq]
  exact joint_kernel_exceptional_split Fker R.rows left right _ residualLeft residualRight x y exceptional

end ActualSecondCorrelationRows

variable [IsPrincipalIdealRing A.R]

namespace ActualSecondRowMass

/-- Construct the canonical mass input from the original profile row
factor and the proved common-atom extraction. The complete correlation
stays internal to the actual row structure. -/
def ofCommonAtoms (R : ActualSecondCorrelationRows A σ H ι)
    (C : A.GeneralArithmeticContext σ η hS) {kLeft kRight : ℕ}
    (left : FrozenSourceAtoms A σ H R.rows kLeft)
    (right : FrozenSourceAtoms A σ H R.rows kRight)
    (hleft : left.ideal = (primePowerProduct R.primes R.leftMultiplicity).val)
    (hright : right.ideal = (primePowerProduct R.primes R.rightMultiplicity).val)
    (radius : {r : ℝ // 0 < r}) (mask : Finset (HeightOneSpectrum A.R))
    (profile : H → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hprofile : ∀ h ∈ R.rows, ‖profile h‖ ≤ B)
    (hweight : ∀ h ∈ R.rows,
      R.weight h = secondOrbitalScalar (K := K) (S := A.Sf) radius mask * profile h)
    (unitIdeal nonunitIdeal : A.Exterior)
    (hunit : ∀ h ∈ R.rows,
      unitFrequencyRadical C R.primes R.leftMultiplicity R.rightMultiplicity (R.frequency h) = unitIdeal)
    (hnonunit : ∀ h ∈ R.rows,
      nonunitFrequencyRadical C R.primes R.leftMultiplicity R.rightMultiplicity (R.frequency h) =
        nonunitIdeal)
    (hpositive : ∀ i, 0 < R.leftMultiplicity i)
    (fiber : ℕ) (hfiber : ∀ I : Ideal (𝓞 K),
      (R.rows.filter (fun h => (R.originalIdeal h).val = I)).card ≤ fiber) :
    ActualSecondRowMass (R.withCommonAtoms left right) C kLeft kRight where
  leftAtoms := left
  rightAtoms := right
  left_ideal := hleft
  right_ideal := hright
  radius := radius
  mask := mask
  rowProfile := profile
  profileBound := B
  profileBound_nonneg := hB
  profile_bound := hprofile
  weight_eq h hh := by
    change R.weight h * left.value h * star (right.value h) = _
    rw [hweight h hh]
  unitIdeal := unitIdeal
  unit_ideal := hunit
  nonunitIdeal := nonunitIdeal
  nonunit_ideal := hnonunit
  left_positive := hpositive
  originalFiber := fiber
  original_fibers := hfiber

end ActualSecondRowMass

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.joint_kernel_common_scalar_reweight
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondCorrelationRows.common_atoms_hybrid_bound
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondRowMass.ofCommonAtoms

