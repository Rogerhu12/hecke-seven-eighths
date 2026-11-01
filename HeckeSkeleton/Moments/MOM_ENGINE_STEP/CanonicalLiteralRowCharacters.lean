import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralAllocatedData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralRowSectors

/-!
# The actual common row character before either rectangle is normalized

The character is computed from the original correction, the complete
moving list and the original residual sector. It is independent of the
two plain profiles, their comparison scales, the slot allocation and
both Fourier variables. Thus the two actual rectangles and both sides
use exactly the same exceptional predicate on the original row carrier.

The predicate is fixed before its ordinary restriction. On a row with
zero complete correlation its chosen value is immaterial, since the
original row coefficient is zero. No ordinary-row witness or previously
constructed normalized family is used in this definition.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}

namespace CanonicalLiteralAllocatedData

variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (oldMoving : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
variable (leftMultiplicity rightMultiplicity : ι → ℕ) (pattern : ι → Bool)
variable (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))

/-- The complete original character, including all fixed phases and
the active second factor, before any profile or capacity choice. -/
def rowCharacter (u : HeckeGeneral.Analysis.NonzeroIdeal K) : HeckeCharacter K :=
  correction *
    ((F.moving P R oldMoving).appendSecondFactor C p leftMultiplicity rightMultiplicity
      pattern).character *
    completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R ν u

variable {ω ψ : HeckeCharacter K} {k : ℕ}
variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (B : ActualColumnAllocation K k)
variable (parent : MomentData K ω ψ) (hcorr : correction ∈ parent.theta)
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K) (m q : ℝ)
variable (inverse : IdealTest K) (index : Fin k → Fin parent.geometry.slotCount)
variable (rectangle : Bool) (firstSign : ℝ) (negative : Bool)

@[simp] theorem data_rowCharacter (ξ : WithLp 2 (ℝ × ℝ))
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (data P R W B F parent oldMoving correction hcorr C p leftMultiplicity rightMultiplicity
      pattern ν remaining extra m q inverse index rectangle firstSign negative ξ).rowCharacter u =
        rowCharacter P R F oldMoving correction C p leftMultiplicity rightMultiplicity
          pattern ν u := rfl

@[simp] theorem data_theta (ξ : WithLp 2 (ℝ × ℝ)) :
    (data P R W B F parent oldMoving correction hcorr C p leftMultiplicity rightMultiplicity
      pattern ν remaining extra m q inverse index rectangle firstSign negative ξ).theta =
        parent.theta := rfl

end CanonicalLiteralAllocatedData

namespace PairedFiniteCharacters

/-- Equal actual row characters need only the identity correction.
The original finite theta set is not enlarged or assumed to be a group. -/
def diagonal {H : Type*} (theta : Finset (HeckeCharacter K))
    (character : H → HeckeCharacter K) : PairedFiniteCharacters theta H where
  subgroup := ⊥
  action χ hχ := by
    have h : χ = 1 := Subgroup.mem_bot.mp hχ
    subst χ
    exact ActualThetaAction.one (theta := theta)
  left := character
  right := character
  ratio_mem h := by simp only [div_self, Subgroup.one_mem]

end PairedFiniteCharacters

variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]

namespace ActualSecondCorrelationRows

variable (S : ActualSecondCorrelationRows A σ H ι)
variable (C : A.GeneralArithmeticContext σ η hS)
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (oldMoving : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
variable (pattern : ι → Bool)
variable (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))

/-- Only the original complete-correlation carrier is inspected. -/
def literalCharacter (h : H) : HeckeCharacter K :=
  if hh : h ∈ S.live then
    CanonicalLiteralAllocatedData.rowCharacter P R F oldMoving correction C S.primes
      S.leftMultiplicity S.rightMultiplicity pattern ν (S.extractedRow C ⟨h, hh⟩).momentIdeal
  else 1

def literalFiniteCharacters (theta : Finset (HeckeCharacter K)) :
    PairedFiniteCharacters theta H :=
  PairedFiniteCharacters.diagonal theta
    (S.literalCharacter C P R F oldMoving correction pattern ν)

/-- Reweighting and two exact row restrictions leave the arithmetic
ideal and the character used in the original predicate unchanged. -/
theorem literalCharacter_reweighted
    (weight : H → ℂ) (keep₁ keep₂ : H → Prop)
    (h : ((({ S with weight := weight }).restrictRows keep₁).restrictRows keep₂).live) :
    let T := (({ S with weight := weight }).restrictRows keep₁).restrictRows keep₂
    CanonicalLiteralAllocatedData.rowCharacter P R F oldMoving correction C T.primes
      T.leftMultiplicity T.rightMultiplicity pattern ν (T.extractedRow C h).momentIdeal =
      S.literalCharacter C P R F oldMoving correction pattern ν h.val := by
  let T₁ := { S with weight := weight }
  let T₂ := T₁.restrictRows keep₁
  let h₁ : T₂.live := T₂.liveInclusion keep₂ h
  let h₀ : S.live := T₁.liveInclusion keep₁ h₁
  rw [literalCharacter, dif_pos h₀.property]
  rfl

end ActualSecondCorrelationRows
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllocatedData.data_rowCharacter
#print axioms HeckeSkeleton.Moments.EngineStep.PairedFiniteCharacters.diagonal
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondCorrelationRows.literalCharacter_reweighted
