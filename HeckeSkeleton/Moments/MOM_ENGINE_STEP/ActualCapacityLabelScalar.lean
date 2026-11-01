import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCapacityScalarMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.TwoDivisorLabelMass

/-!
# The actual child scalar is bounded by its original full label

The first Gauss scalar, both original Möbius coefficients and finite
characters multiply the actual normalized-capacity kernel scalar.  The
pointwise bound below derives its canonical `AtomicLabel.weight` from
the original radius window and individual arithmetic/profile costs.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree UniqueFactorizationMonoid
open HeckeGeneral.Characters HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open CommonSupportMass LocalFiniteSums

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ} {ω ψ : HeckeCharacter F}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]
variable {V HL HR : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {k l : ℕ}
variable {sL : ActualAllocatedSource A V HL k} {sR : ActualAllocatedSource A V HR l}
variable {DL : sL.Calibration (σ := σ) ω ψ} {DR : sR.Calibration (σ := σ) ω ψ}
variable {«GL» : DL.NormalizedCapacityData} {GR : DR.NormalizedCapacityData}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {branch : TwoDivisorCommonBranch (K := F)}
variable (z : branch.AtomicLabel Ray)
variable {α β : Type*} {fullI : α → A.Exterior} {fullJ : β → A.Exterior}

theorem actual_capacity_same_label_scalar_le
    (first : FirstCommonCharacterBlock fullI fullJ z.firstLabel.1)
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent F v = 0)
    (firstResidue firstFrequency : A.R)
    (phase₁ phase₂ : branch.AtomicLabel Ray → Ray × Ray → Circle)
    (left : «GL».Child) (right : GR.Child) (originalLeft originalRight : ℂ)
    (Z : ℝ) (hZ : 1 < Z)
    (parentWidth a₀ q wo w boundary krow g ell NL NR δ ε : ℝ)
    (r : {r : ℝ // 0 < r}) (mask : Finset (HeightOneSpectrum A.R))
    (T R : Ideal (𝓞 F))
    (hD : z.secondLabel.1.1 ≠ 0) (hE : z.secondLabel.1.2 ≠ 0)
    (hT : T ≠ 0) (hL : z.secondDivisor ≠ 0)
    (hrow : Z ^ (-krow - g) ≤
      r.val * (sIntegerElementNorm F (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
        (sIntegerMaskGenerator F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) mask)).val)
    (hcentral : Z ^ a₀ ≤ Real.sqrt NL * Real.sqrt NR)
    (hnormalizers : ‖originalLeft‖ * ‖originalRight‖ =
      1 / (Real.sqrt NL * Real.sqrt NR))
    (frozenCost fiberCost primeCost : ℝ) (cap : ℕ) (hfrozen : 1 ≤ frozenCost)
    (hbaseL : sL.base = Z) (hbaseR : sR.base = Z)
    (hrowL : DL.rowBound ≤ secondCommonRowCost (A := A) r mask
      z.secondLabel.1.1 z.secondLabel.1.2 T)
    (hrowR : DR.rowBound ≤ secondCommonRowCost (A := A) r mask
      z.secondLabel.1.1 z.secondLabel.1.2 T)
    (hscalarL : DL.scalarBound ≤ frozenCost ^ cap / (Ideal.absNorm z.secondDivisor : ℝ))
    (hscalarR : DR.scalarBound ≤ frozenCost ^ cap / (Ideal.absNorm z.secondDivisor : ℝ))
    (hfiberL : (DL.fiberBound : ℝ) ≤ fiberCost) (hfiberR : (DR.fiberBound : ℝ) ≤ fiberCost)
    (hprimeL : ∀ i, «GL».primeBound i ≤ primeCost)
    (hprimeR : ∀ i, GR.primeBound i ≤ primeCost) (hprime : 1 ≤ primeCost)
    (hcapL : sL.allocation.keep.card ≤ cap) (hcapR : sR.allocation.keep.card ≤ cap)
    (hbudgetL : DL.parameters.m + DL.parameters.q + «GL».exponent ≤
      secondCommonChildWidth Z a₀ q wo krow g z.secondLabel.1.1 z.secondLabel.1.2 T R +
        secondCommonChildAllowance Z w boundary ell z.secondLabel.1.1 z.secondLabel.1.2 + δ)
    (hbudgetR : DR.parameters.m + DR.parameters.q + GR.exponent ≤
      secondCommonChildWidth Z a₀ q wo krow g z.secondLabel.1.1 z.secondLabel.1.2 T R +
        secondCommonChildAllowance Z w boundary ell z.secondLabel.1.1 z.secondLabel.1.2 + δ)
    (hparent : parentWidth = a₀ + q) (hreserve : w + boundary + δ ≤ ε) :
    (first.normalizedActiveGauss C hDiff Z firstResidue firstFrequency *
      ‖(moebius z.firstDivisor : ℂ)‖ *
      ‖fixedPhaseCoefficient Ray (phase₁ z) z.firstPhase‖ *
      ‖(moebius z.secondDivisor : ℂ)‖ *
      ‖fixedPhaseCoefficient Ray (phase₂ z) z.secondPhase‖) *
      normalizedCapacityPairWeight left right originalLeft originalRight Z parentWidth ≤
      (frozenCost ^ cap * fiberCost * primeCost ^ cap * orbitalFieldFactor F) *
        Z ^ (ε + wo + ell) * z.weight phase₁ phase₂ := by
  have hfirst := first.normalizedActiveGauss_le_radical C hDiff Z hZ firstResidue firstFrequency
  have hsecond := normalizedCapacityPairWeight_second_harmonic left right originalLeft originalRight
    Z hZ parentWidth a₀ q wo w boundary krow g ell NL NR δ ε r mask
    z.secondLabel.1.1 z.secondLabel.1.2 T R z.secondDivisor hD hE hT hL hrow hcentral
    hnormalizers frozenCost fiberCost primeCost cap hfrozen hbaseL hbaseR hrowL hrowR
    hscalarL hscalarR hfiberL hfiberR hprimeL hprimeR hprime hcapL hcapR
    hbudgetL hbudgetR hparent hreserve
  have hp := mul_le_mul hfirst hsecond
    (normalizedCapacityPairWeight_nonneg left right originalLeft originalRight Z parentWidth
      (zero_lt_one.trans hZ))
    (one_div_nonneg.mpr (Nat.cast_nonneg _))
  have hc : 0 ≤ ‖(moebius z.firstDivisor : ℂ)‖ *
      ‖fixedPhaseCoefficient Ray (phase₁ z) z.firstPhase‖ *
      ‖(moebius z.secondDivisor : ℂ)‖ *
      ‖fixedPhaseCoefficient Ray (phase₂ z) z.secondPhase‖ := by positivity
  convert mul_le_mul_of_nonneg_right hp hc using 1 <;>
    (try simp only [TwoDivisorCommonBranch.AtomicLabel.weight,
      TwoDivisorCommonBranch.AtomicLabel.harmonicWeight]) <;> ring

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_capacity_same_label_scalar_le
