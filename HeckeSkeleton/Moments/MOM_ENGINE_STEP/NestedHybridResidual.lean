import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NestedHybridKernel
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondHybridSource

/-!
# Integrability of every actual hybrid residual branch

The genuine complete correlation, divisor pool, fixed ray phases and
whole occurrence allocations remain in the expression.  Their finite
sums use the proved product-kernel integrability, with the first phase
attached to each original whole coefficient before conjugation.
-/

noncomputable section
open scoped Classical BigOperators NumberField FourierTransform SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckePort.Moments HeckePort.Moments.MobiusRegroup HeckePort.IdealMobiusDivisorSum
open WholeAllocation

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable (Ray : Type*) [CommGroup Ray] [Fintype Ray]
local instance : Fintype ((Ray × Ray) →* Circle) := Fintype.ofFinite _

/-- The actual two-transform hybrid residual cost is integrable in its
first Fourier variable.  The exceptional predicate may depend on every
finite divisor, phase and allocation label, but precedes that variable. -/
theorem actual_second_hybrid_first_phase_integrable {H : Type*} {k l : ℕ}
    (F₁ : 𝓢(U, ℂ)) (F₂ : 𝓢(V, ℂ)) (rows : Finset H) (frequency : H → A.R)
    (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (T₁ T₂ : Finset (Ideal (𝓞 K))) (T : Fin l → Finset (HeightOneSpectrum (𝓞 K)))
    (ID IE : A.Exterior) (IA : AllocationColumn K k → A.Exterior)
    (IB : AllocationColumn K l → A.Exterior)
    (d e : A.R) (hd : A.Generates ID d) (he : A.Generates IE e)
    (rayLeft : AllocationColumn K k → Ray) (rayRight : AllocationColumn K l → Ray)
    (phaseTable : Ray × Ray → Circle) (q : H → ℂ)
    (c : AllocationColumn K k → ℂ) (f : AllocationColumn K l → ℂ)
    (x₁ : AllocationColumn K k → U) (y₁ : AllocationColumn K l → U)
    (x₂ : H → AllocationColumn K k → V) (y₂ : H → AllocationColumn K l → V)
    (exceptional : ∀ D : Ideal (𝓞 K), ((Ray × Ray) →* Circle) →
      (primeSupport D → Finset (Fin (k + 2))) →
      (primeSupport D → Finset (Fin (l + 2))) → H → Prop) :
    Integrable (fun ξ =>
      secondResidualHybridCost Ray F₂ rows frequency S₁ S₂ S T₁ T₂ T
        ID IE IA IB d e hd he rayLeft rayRight phaseTable q
        (fun i => c i * jointPhase ξ (x₁ i)) (fun j => f j * jointPhase ξ (y₁ j))
        x₂ y₂ exceptional) (actualFourierMeasure F₁) := by
  unfold secondResidualHybridCost fullCorrelationHybridCost
  apply integrable_finsetSum
  intro D _
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro χ _
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro a _
  apply integrable_finsetSum
  intro b _
  have hi := iterated_joint_hybrid_integrable rows
    (pairedAllocatedColumns D a S₁ S₂ S id id HeightOneSpectrum.asIdeal)
    (pairedAllocatedColumns D b T₁ T₂ T id id HeightOneSpectrum.asIdeal)
    (fun h => q h * generatedIdealCorrelation (σ := σ) ID IE d e hd he (frequency h))
    (fun h i => c i * (fixedLeftPhase Ray χ (rayLeft i) : ℂ) *
      σ (A.sexticResidue (IA i) (frequency h)))
    (fun h j => f j * (fixedRightPhase Ray χ (rayRight j) : ℂ) *
      σ (A.sexticResidue (IB j) (-frequency h)))
    (fun _ i => x₁ i) x₂ (fun _ j => y₁ j) y₂ (exceptional D χ a b) F₁ F₂
  convert hi using 1
  funext ξ
  congr 1 <;> funext h i <;> ring

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_second_hybrid_first_phase_integrable
