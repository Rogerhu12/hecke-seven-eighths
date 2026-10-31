import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SupportCartesianReindex
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondCoefficientBinding

/-!
# Whole source coefficients on actual support-extraction branches

The residual Cartesian support is the actual support from
SupportCartesianReindex.  The original whole coefficient is reindexed,
then the already proved single-ideal multiplicativity extracts its
literal frozen scalar.  Both rectangles of a centered coefficient use
that same scalar and the same Fourier translation.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {k : ℕ}
variable {S₁ S₂ : Finset (Ideal (𝓞 K))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 K))}
variable {P : Finset (Ideal (𝓞 K))}

namespace SupportCartesianBranch

variable (b : SupportCartesianBranch S₁ S₂ S P)

theorem plainExtract₁_ne_zero : b.plainExtract₁ ≠ 0 := by
  have he := (Finset.mem_filter.mp
    (Finset.mem_product.mp (Finset.mem_product.mp b.witness_mem).1).1).2
  rw [← he]
  exact supportExtract_ne_zero b.witness.1.1 P

theorem plainExtract₂_ne_zero : b.plainExtract₂ ≠ 0 := by
  have he := (Finset.mem_filter.mp
    (Finset.mem_product.mp (Finset.mem_product.mp b.witness_mem).1).2).2
  rw [← he]
  exact supportExtract_ne_zero b.witness.1.2 P

def plainDivisor₁ : HeckeGeneral.Analysis.NonzeroIdeal K :=
  ⟨b.plainExtract₁, mem_nonZeroDivisors_of_ne_zero b.plainExtract₁_ne_zero⟩

def plainDivisor₂ : HeckeGeneral.Analysis.NonzeroIdeal K :=
  ⟨b.plainExtract₂, mem_nonZeroDivisors_of_ne_zero b.plainExtract₂_ne_zero⟩

def childPlain₁ : Finset (HeckeGeneral.Analysis.NonzeroIdeal K) :=
  nonzeroMomentSupport (SupportCartesian.plainResidual S₁ P b.plainExtract₁)

def childPlain₂ : Finset (HeckeGeneral.Analysis.NonzeroIdeal K) :=
  nonzeroMomentSupport (SupportCartesian.plainResidual S₂ P b.plainExtract₂)

def childSlots (j : Fin b.keep.card) : Finset (HeightOneSpectrum (𝓞 K)) :=
  SupportCartesian.primeLive (S (SlotRestriction.index b.keep j)) P

def childMomentColumns : Finset
    ((HeckeGeneral.Analysis.NonzeroIdeal K × HeckeGeneral.Analysis.NonzeroIdeal K) ×
      (Fin b.keep.card → HeightOneSpectrum (𝓞 K))) :=
  childCartesianColumns b.childPlain₁ b.childPlain₂ b.childSlots

private theorem plainResidual_ne_zero (T : Finset (Ideal (𝓞 K))) (D J : Ideal (𝓞 K))
    (hJ : J ∈ SupportCartesian.plainResidual T P D) : J ≠ 0 := by
  obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hJ
  exact supportResidual_ne_zero I P

def scalar (T : FixedChildCharacters K k) (g h' : A.R)
    (Z : ℝ) (length : Fin k → ℝ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ) : ℂ :=
  T.frozenScalar (σ := σ) g h' b.plainDivisor₁ b.plainDivisor₂
    Z length b.keep b.witness.2 w

def childCoefficient (T : FixedChildCharacters K k) (g h' : A.R)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ) :
    ((HeckeGeneral.Analysis.NonzeroIdeal K × HeckeGeneral.Analysis.NonzeroIdeal K) ×
      (Fin b.keep.card → HeightOneSpectrum (𝓞 K))) → ℂ :=
  (T.restrictSlots b.keep).coefficient (σ := σ) g h'
    (N₁ / idealNorm K b.plainDivisor₁) (N₂ / idealNorm K b.plainDivisor₂) Z
    (fun j => length (SlotRestriction.index b.keep j))
    (fun I => w₁ (b.plainDivisor₁ * I)) (fun J => w₂ (b.plainDivisor₂ * J))
    (fun j => w (SlotRestriction.index b.keep j))

section Fourier

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def childLocation
    (x₁ x₂ : HeckeGeneral.Analysis.NonzeroIdeal K → V)
    (x : Fin k → HeightOneSpectrum (𝓞 K) → V) :
    ((HeckeGeneral.Analysis.NonzeroIdeal K × HeckeGeneral.Analysis.NonzeroIdeal K) ×
      (Fin b.keep.card → HeightOneSpectrum (𝓞 K))) → V :=
  childCartesianLocation
    (fun I => x₁ (b.plainDivisor₁ * I)) (fun J => x₂ (b.plainDivisor₂ * J))
    (fun j => x (SlotRestriction.index b.keep j))

theorem joint_polynomial
    (T : FixedChildCharacters K k) (g h' : A.R)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (x₁ x₂ : HeckeGeneral.Analysis.NonzeroIdeal K → V)
    (x : Fin k → HeightOneSpectrum (𝓞 K) → V) (ξ : V) :
    jointFourierColumn b.originalColumns
      (rawSourceCoefficient (σ := σ) T g h' N₁ N₂ Z length w₁ w₂ w)
      (rawSourceLocation x₁ x₂ x) ξ =
      b.scalar (σ := σ) T g h' Z length w *
        jointPhase ξ (frozenSourceLocation b.keep b.witness.2 x) *
          jointFourierColumn b.childMomentColumns
            (b.childCoefficient (σ := σ) T g h' N₁ N₂ Z length w₁ w₂ w)
            (b.childLocation x₁ x₂ x) ξ := by
  unfold jointFourierColumn
  rw [b.sum_reindex]
  rw [show b.residualColumns = childCartesianColumns
    (SupportCartesian.plainResidual S₁ P b.plainExtract₁)
    (SupportCartesian.plainResidual S₂ P b.plainExtract₂) b.childSlots from rfl]
  rw [sum_cartesian_nonzeroMomentSupport
    (SupportCartesian.plainResidual S₁ P b.plainExtract₁)
    (SupportCartesian.plainResidual S₂ P b.plainExtract₂) b.childSlots
    (fun I hI => plainResidual_ne_zero _ _ I hI)
    (fun J hJ => plainResidual_ne_zero _ _ J hJ)]
  have hlift₁ (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
      sourceMomentIdeal (b.plainExtract₁ * I.val) = b.plainDivisor₁ * I :=
    sourceMomentIdeal_mul_val b.plainDivisor₁ I
  have hlift₂ (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
      sourceMomentIdeal (b.plainExtract₂ * I.val) = b.plainDivisor₂ * I :=
    sourceMomentIdeal_mul_val b.plainDivisor₂ I
  simp only [reconstruct, rawSourceCoefficient, rawSourceLocation, hlift₁, hlift₂]
  exact extracted_source_joint_polynomial T g h' b.plainDivisor₁ b.plainDivisor₂
    N₁ N₂ Z length b.keep b.witness.2 b.childPlain₁ b.childPlain₂ b.childSlots
    w₁ w₂ w x₁ x₂ x ξ

/-- The complete centered coefficient has the same extracted scalar. -/
theorem centered_joint_polynomial
    (T : FixedChildCharacters K k) (g h' : A.R)
    (X₁ X₂ Y₁ Y₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ v₁ v₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (x₁ x₂ : HeckeGeneral.Analysis.NonzeroIdeal K → V)
    (x : Fin k → HeightOneSpectrum (𝓞 K) → V) (ξ : V) :
    jointFourierColumn b.originalColumns
      (fun y => rawSourceCoefficient (σ := σ) T g h' X₁ X₂ Z length w₁ w₂ w y -
        rawSourceCoefficient (σ := σ) T g h' Y₁ Y₂ Z length v₁ v₂ w y)
      (rawSourceLocation x₁ x₂ x) ξ =
      b.scalar (σ := σ) T g h' Z length w *
        jointPhase ξ (frozenSourceLocation b.keep b.witness.2 x) *
          jointFourierColumn b.childMomentColumns
            (fun y => b.childCoefficient (σ := σ) T g h' X₁ X₂ Z length w₁ w₂ w y -
              b.childCoefficient (σ := σ) T g h' Y₁ Y₂ Z length v₁ v₂ w y)
            (b.childLocation x₁ x₂ x) ξ := by
  have hsub {J : Type*} (U : Finset J) (c d : J → ℂ) (u : J → V) :
      jointFourierColumn U (fun y => c y - d y) u ξ =
        jointFourierColumn U c u ξ - jointFourierColumn U d u ξ := by
    simp only [jointFourierColumn, sub_mul, Finset.sum_sub_distrib]
  rw [hsub, b.joint_polynomial, b.joint_polynomial, hsub, mul_sub]

/-- The exact common extraction scalar is absorbed into the original
row measure once.  The common Fourier translation has norm one. -/
theorem joint_energy {H : Type*}
    (rows : Finset H) (T : H → FixedChildCharacters K k) (g h' : H → A.R)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : H → HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : H → Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (x₁ x₂ : H → HeckeGeneral.Analysis.NonzeroIdeal K → V)
    (x : H → Fin k → HeightOneSpectrum (𝓞 K) → V) (q : H → ℂ) (ξ : V) :
    jointColumnEnergy rows b.originalColumns q
      (fun h => rawSourceCoefficient (σ := σ) (T h) (g h) (h' h)
        N₁ N₂ Z length (w₁ h) (w₂ h) (w h))
      (fun h => rawSourceLocation (x₁ h) (x₂ h) (x h)) ξ =
      jointColumnEnergy rows b.childMomentColumns
        (fun h => q h * b.scalar (σ := σ) (T h) (g h) (h' h) Z length (w h) *
          star (b.scalar (σ := σ) (T h) (g h) (h' h) Z length (w h)))
        (fun h => b.childCoefficient (σ := σ) (T h) (g h) (h' h)
          N₁ N₂ Z length (w₁ h) (w₂ h) (w h))
        (fun h => b.childLocation (x₁ h) (x₂ h) (x h)) ξ := by
  unfold jointColumnEnergy
  apply Finset.sum_congr rfl
  intro h _
  rw [b.joint_polynomial]
  simp only [norm_mul, norm_star, norm_jointPhase, mul_one, mul_pow]
  ring

end Fourier
end SupportCartesianBranch

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SupportCartesianBranch.joint_polynomial
#print axioms HeckeSkeleton.Moments.EngineStep.SupportCartesianBranch.centered_joint_polynomial
#print axioms HeckeSkeleton.Moments.EngineStep.SupportCartesianBranch.joint_energy

