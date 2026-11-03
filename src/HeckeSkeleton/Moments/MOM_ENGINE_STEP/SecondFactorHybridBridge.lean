import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondFactorIdentification
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridOrdinaryProduction

/-!
# Original factor dictionaries feed the actual hybrid child producer

The shared original atoms and ray labels are identified one factor at a
time.  Their additional Gauss normalizers are the explicit positive
original scales.  This constructs the rectangle input of the actual
ordinary branch; no whole-polynomial or energy identity is assumed.
The same construction works after any genuine pre-Cauchy row restriction.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters
open HeckePort.Moments WholeAllocation

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {H ι V : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {k : ℕ} {side : SecondColumnSide}
variable {S₁ S₂ : Finset (Ideal (𝓞 K))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 K))}
variable {T : FixedChildCharacters K k} {χ : (Ray × Ray) →* Circle}
variable {D : SecondCoefficientTermDictionary T (side.phase Ray χ) S₁ S₂ S}
variable {P : SecondColumnFactors K Ray k}

namespace SecondCoefficientTermDictionary.FactorIdentification

/-- The incoming single-factor identification gives the existing real
ordinary rectangle, including its actual central normalizer.  The
original ray and coefficient are kept verbatim on every retained column. -/
def rectangularFactors
    (h : D.FactorIdentification P)
    (R : ActualSecondCorrelationRows A σ H ι)
    (ideal : AllocationColumn K k → A.Exterior)
    (hideal : ∀ i ∈ childCartesianColumns S₁ S₂ S,
      (ideal i).val = allocationColumnIdeal i)
    (hS₁ : ∀ I ∈ S₁, I ≠ 0) (hS₂ : ∀ I ∈ S₂, I ≠ 0)
    (hbase : 1 < D.base) (hlength : ∀ i, 0 < D.length i)
    (N₁ N₂ : ℝ) (Nslot : Fin k → ℝ)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hNslot : ∀ i, 0 < Nslot i)
    (hnormalizer₁ : P.leftNormalizer = (Real.sqrt N₁ : ℂ)⁻¹)
    (hnormalizer₂ : P.rightNormalizer = (Real.sqrt N₂ : ℂ)⁻¹)
    (hnormalizerSlot : P.slotNormalizer = fun i => (Real.sqrt (Nslot i) : ℂ)⁻¹)
    (x₁ x₂ : H → HeckeGeneral.Analysis.NonzeroIdeal K → V)
    (x : H → Fin k → HeightOneSpectrum (𝓞 K) → V) :
    SecondRectangularFactors R Ray side S₁ S₂ S ideal P.ray P.coefficient
      (fun h => rawSourceLocation (x₁ h) (x₂ h) (x h)) χ where
  characters := T
  dictionary := D
  base_gt_one := hbase
  length_pos := hlength
  plain₁_nonzero := hS₁
  plain₂_nonzero := hS₂
  ideal_product := hideal
  gaussScale₁ := N₁
  gaussScale₂ := N₂
  gaussSlotScale := Nslot
  gaussScale₁_pos := hN₁
  gaussScale₂_pos := hN₂
  gaussSlotScale_pos := hNslot
  coefficient_factor i hi := by
    simpa only [hnormalizer₁, hnormalizer₂, hnormalizerSlot] using
      (h.coefficient_eq i hi).symm
  ray_factor i hi := (h.ray_eq i hi).symm
  leftLocation := x₁
  rightLocation := x₂
  slotLocation := x
  point_factor _ _ _ _ := rfl

end SecondCoefficientTermDictionary.FactorIdentification

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondCoefficientTermDictionary.FactorIdentification.rectangularFactors

