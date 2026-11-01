import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralRectangles

/-!
# The absent ordinary comparison rectangle on the same source

The literal table sets only its comparison left weight to zero when
the original moment is uncentered. That field remains zero in the
actual allocated frame, on both Fourier orientations. Its source
energy is therefore identically zero before any calibration or child
is selected. In particular no comparison-scale product identity is
needed to exclude this rectangle from the actual active carrier.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum
open WholeAllocation

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}

namespace ActualAllocatedSource

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {k : ℕ}

/-- A zero individual original weight proves zero source energy;
there is no polynomial or whole-energy equality among the inputs. -/
theorem energy_zero_of_leftWeight (source : ActualAllocatedSource A V H k)
    (hzero : ∀ h ∈ source.rows, ∀ I, source.leftWeight h I = 0) (ξ : V) :
    source.energy (σ := σ) ξ = 0 := by
  unfold energy jointColumnEnergy
  apply Finset.sum_eq_zero
  intro h hh
  simp only [jointFourierColumn, rawSourceCoefficient, FixedChildCharacters.coefficient,
    childCartesianCoefficient, sourcePlainTerm, hzero h hh, mul_zero, zero_mul,
    Finset.sum_const_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]

end ActualAllocatedSource

namespace CanonicalLiteralRectangles.Atoms

variable {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable (C : A.GeneralArithmeticContext σ η hS)
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (rows : ActualSecondCorrelationRows A σ H ι)
variable (side : SecondColumnSide) (χ : (PUnit.{1} × PUnit.{1}) →* Circle)
variable (ideal : AllocationColumn K k → A.Exterior)
variable (hideal : ∀ i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots,
  (ideal i).val = allocationColumnIdeal i)
variable (firstSign : ℝ) (L : Ideal (𝓞 K))
variable (selection : primeSupport L → Finset (Fin (k + 2)))
variable (hne : (pairedAllocatedColumns L selection d.plain₁ d.plain₂ d.slots
  id id HeightOneSpectrum.asIdeal).Nonempty)

/-- The negative Fourier orientation changes locations and frequency,
and retains this same original individual weight. -/
theorem factors_source_leftWeight (r : Bool) (h : rows.live)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    ((d.factors rows side χ ideal hideal firstSign r).frame C L selection hne)
        .source.leftWeight h I = d.rectangleLeftWeight r I := by
  cases side <;> rfl

theorem comparison_source_energy_zero (hordinary : d.centered = false)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    ((d.factors rows side χ ideal hideal firstSign true).frame C L selection hne)
      .source.energy (σ := σ) ξ = 0 := by
  apply ActualAllocatedSource.energy_zero_of_leftWeight
  intro h _ I
  rw [d.factors_source_leftWeight C rows side χ ideal hideal firstSign L selection hne]
  simp [rectangleLeftWeight, hordinary]

/-- Exactly the ordinary zero rectangle is excluded by the original
activity test. All other labels and both original sources remain. -/
theorem active_rectangle (r : Bool)
    (hactive : ¬ ∀ ξ,
      ((d.factors rows side χ ideal hideal firstSign r).frame C L selection hne)
        .source.energy (σ := σ) ξ = 0) :
    r = false ∨ d.centered = true := by
  cases r with
  | false => exact Or.inl rfl
  | true =>
    cases hc : d.centered with
    | false =>
      exfalso
      apply hactive
      intro ξ
      exact d.comparison_source_energy_zero C rows side χ ideal hideal firstSign
        L selection hne hc ξ
    | true => exact Or.inr (by simp only [hc])

end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.energy_zero_of_leftWeight
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.comparison_source_energy_zero
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.active_rectangle
