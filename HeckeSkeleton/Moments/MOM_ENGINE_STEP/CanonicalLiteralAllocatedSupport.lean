import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralAllocatedData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralSupport

/-!
# Effective support of the actual allocated literal child

The original support table starts outside the fixed set S, and its two
actual common-ideal extractions add their prime supports.  The first
complete deletion is present in the remaining ideal.  At the second
extraction the active factor and the complete sixth root together remove
every common prime, including those with zero active exponent.

Consequently the nonzero mask of the child constructed in
`CanonicalLiteralAllocatedData` implies precisely the avoidance needed
by the original finite support table.  The three effective-support
conclusions below retain that same child, its smooth Fourier profiles,
the actual allocation and its occurrence indices.  No final support or
whole-mask implication is supplied as an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllocatedSupport

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum
open CanonicalLiteralSupport CanonicalLiteralMaskSupport
open CanonicalLiteralAllocatedData

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Each first deleted prime divides the literal complete deletion,
independently of whether it occurs in an active reciprocity factor. -/
theorem dvd_literalDeletionIdeal (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ p ∈ S, Prime p) (p : Ideal (𝓞 K)) (hp : p ∈ S) :
    p ∣ (literalDeletionIdeal S hS).val :=
  Finset.dvd_prod_of_mem (fun J : Ideal (𝓞 K) => J) hp

section PrimitiveAvoidance

variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {oldMoving : OriginalMovingFactors A P R}
variable {remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K}
variable {p : ι → ExteriorPrime A} {l r : ι → ℕ} {pattern : ι → Bool}
variable {u I : HeckeGeneral.Analysis.NonzeroIdeal K}

/-- Only the original individual prime inclusions occur as inputs.
All coprimality statements are obtained from the actual child mask. -/
theorem avoids_of_maskConsequences
    (H : MaskConsequences oldMoving (remaining * extra) p l r pattern u I)
    (firstSupport secondSupport : Finset (Ideal (𝓞 K)))
    (hfirst : ∀ q ∈ firstSupport, q ∣ extra.val)
    (hsecond : secondSupport ⊆ primeSupport (primePowerProduct p l).val)
    (hl : ∀ i, 0 < l i) (hr : ∀ i, 0 < r i) :
    Avoids I.val ((primeSupport A.cS ∪ firstSupport) ∪ secondSupport) := by
  have hextra : IsCoprime I.val extra.val := H.old_remaining.of_mul_right_right
  intro q hq
  rcases Finset.mem_union.mp hq with hq | hq
  · rcases Finset.mem_union.mp hq with hfixed | hfirstmem
    · exact (coprime_support_iff I.val A.cS A.cS_ne_zero).mp H.fixed q hfixed
    · exact hextra.of_isCoprime_of_dvd_right (hfirst q hfirstmem)
  · exact H.second_left_prime hl hr q (hsecond hq)

end PrimitiveAvoidance

section ActualData

variable {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {ω ψ : HeckeCharacter K} {k : ℕ}
variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (B : ActualColumnAllocation K k)
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
variable (leftMultiplicity rightMultiplicity : ι → ℕ) (pattern : ι → Bool)
variable (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K) (m q : ℝ)
variable (inverse : IdealTest K) (index : Fin k → Fin parent.geometry.slotCount)
variable (rectangle : Bool) (firstSign : ℝ) (negative : Bool)

local notation "child" => data P R W B F parent oldMoving correction hcorr C p
  leftMultiplicity rightMultiplicity pattern ν remaining extra m q inverse index
  rectangle firstSign negative

/-- Restricting the allocated slots does not alter the complete mask.
The output records the old moving factors, the entire first deletion,
and the complete new active/root factors. -/
theorem mask_consequences (ξ : WithLp 2 (ℝ × ℝ))
    (u I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hmask : maskValue (child ξ) u I.val ≠ 0) :
    MaskConsequences (F.moving P R oldMoving) (remaining * extra) p
      leftMultiplicity rightMultiplicity pattern u I :=
  childData_mask_nonzero P R parent (F.moving P R oldMoving) correction hcorr C p
    leftMultiplicity rightMultiplicity pattern ν (remaining * extra) (d.base ^ (m + q))
    inverse (W.fourierLeft rectangle firstSign negative ξ)
    (W.fourierRight rectangle firstSign negative ξ) (preGeometry W firstSign negative ξ)
    index u I hmask

/-- The source may use its original finite support presentation, with
its prime-by-prime inclusion in the actual two deletions. -/
theorem mask_nonzero_avoids
    (firstSupport secondSupport : Finset (Ideal (𝓞 K)))
    (hfirst : ∀ v ∈ firstSupport, v ∣ extra.val)
    (hsecond : secondSupport ⊆ primeSupport (primePowerProduct p leftMultiplicity).val)
    (hl : ∀ i, 0 < leftMultiplicity i) (hr : ∀ i, 0 < rightMultiplicity i)
    (ξ : WithLp 2 (ℝ × ℝ)) (u I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hmask : maskValue (child ξ) u I.val ≠ 0) :
    Avoids I.val ((primeSupport A.cS ∪ firstSupport) ∪ secondSupport) :=
  avoids_of_maskConsequences
    (mask_consequences P R W B F parent oldMoving correction hcorr C p
      leftMultiplicity rightMultiplicity pattern ν remaining extra m q inverse index
      rectangle firstSign negative ξ u I hmask)
    firstSupport secondSupport hfirst hsecond hl hr

/-- All three support fields of the actual calibration follow from
the original atom support table and individual prime inclusions.
The profile functions themselves retain their original smooth values. -/
theorem effectiveSupports
    (firstSupport secondSupport : Finset (Ideal (𝓞 K)))
    (hfirst : ∀ v ∈ firstSupport, v ∣ extra.val)
    (hsecond : secondSupport ⊆ primeSupport (primePowerProduct p leftMultiplicity).val)
    (hl : ∀ i, 0 < leftMultiplicity i) (hr : ∀ i, 0 < rightMultiplicity i)
    (support : d.SupportData ((primeSupport A.cS ∪ firstSupport) ∪ secondSupport))
    (hplain₁ : B.plain₁ = d.plain₁) (hplain₂ : B.plain₂ = d.plain₂)
    (hslots : B.slots = d.slots) (κ : ℝ)
    (ξ : WithLp 2 (ℝ × ℝ)) (u : HeckeGeneral.Analysis.NonzeroIdeal K) :
    EffectivePlainSupport (child ξ) (child ξ).plainTest₁ u
        (d.base ^ (parameters d B rectangle m q κ).n₁) (height ξ) B.childPlain₁ ∧
      EffectivePlainSupport (child ξ) (child ξ).plainTest₂ u
        (d.base ^ (parameters d B rectangle m q κ).n₂) (height ξ) B.childPlain₂ ∧
      ∀ i : Fin (child ξ).geometry.slotCount,
        EffectivePrimeSupport (child ξ) i u d.base (height ξ)
          (B.childSlots (Fin.cast
            (data_count P R W B F parent oldMoving correction hcorr C p
              leftMultiplicity rightMultiplicity pattern ν remaining extra m q inverse index
              rectangle firstSign negative ξ) i)) := by
  have hm : ∀ I : HeckeGeneral.Analysis.NonzeroIdeal K,
      maskValue (child ξ) u I.val ≠ 0 →
        Avoids I.val ((primeSupport A.cS ∪ firstSupport) ∪ secondSupport) :=
    fun I hI => mask_nonzero_avoids P R W B F parent oldMoving correction hcorr C p
      leftMultiplicity rightMultiplicity pattern ν remaining extra m q inverse index
      rectangle firstSign negative firstSupport secondSupport hfirst hsecond hl hr ξ u I hI
  refine ⟨?_, ?_, ?_⟩
  · change EffectivePlainSupport (child ξ) (W.fourierLeft rectangle firstSign negative ξ) u
      (d.base ^ (parameters d B rectangle m q κ).n₁) (height ξ) B.childPlain₁
    rw [left_scale d B rectangle m q κ]
    exact support.fourierLeft_effectiveSupport W B hplain₁ (child ξ) u
      rectangle firstSign negative ξ (height ξ) hm
  · change EffectivePlainSupport (child ξ) (W.fourierRight rectangle firstSign negative ξ) u
      (d.base ^ (parameters d B rectangle m q κ).n₂) (height ξ) B.childPlain₂
    rw [right_scale d B rectangle m q κ]
    exact support.fourierRight_effectiveSupport W B hplain₂ (child ξ) u
      rectangle firstSign negative ξ (height ξ) hm
  · intro i
    exact support.fourierSlot_effectiveSupport W B hslots (child ξ) u rfl
      firstSign negative ξ (height ξ) (fun _ => rfl) hm i

/-- Actual main/direct and pool tables delete their complete original
first support with `literalDeletionIdeal`; their second extraction uses
the displayed common support.  For those computed tables even the
individual prime-inclusion inputs of `effectiveSupports` are proved
internally. `hextra` is the literal recipe identity (normally `rfl`). -/
theorem effectiveSupports_of_original_deletions
    (firstSupport : Finset (Ideal (𝓞 K))) (hfirst : ∀ v ∈ firstSupport, Prime v)
    (hextra : extra = literalDeletionIdeal firstSupport hfirst)
    (hl : ∀ i, 0 < leftMultiplicity i) (hr : ∀ i, 0 < rightMultiplicity i)
    (support : d.SupportData ((primeSupport A.cS ∪ firstSupport) ∪
      primeSupport (primePowerProduct p leftMultiplicity).val))
    (hplain₁ : B.plain₁ = d.plain₁) (hplain₂ : B.plain₂ = d.plain₂)
    (hslots : B.slots = d.slots) (κ : ℝ)
    (ξ : WithLp 2 (ℝ × ℝ)) (u : HeckeGeneral.Analysis.NonzeroIdeal K) :
    EffectivePlainSupport (child ξ) (child ξ).plainTest₁ u
        (d.base ^ (parameters d B rectangle m q κ).n₁) (height ξ) B.childPlain₁ ∧
      EffectivePlainSupport (child ξ) (child ξ).plainTest₂ u
        (d.base ^ (parameters d B rectangle m q κ).n₂) (height ξ) B.childPlain₂ ∧
      ∀ i : Fin (child ξ).geometry.slotCount,
        EffectivePrimeSupport (child ξ) i u d.base (height ξ)
          (B.childSlots (Fin.cast
            (data_count P R W B F parent oldMoving correction hcorr C p
              leftMultiplicity rightMultiplicity pattern ν remaining extra m q inverse index
              rectangle firstSign negative ξ) i)) := by
  apply effectiveSupports P R W B F parent oldMoving correction hcorr C p
    leftMultiplicity rightMultiplicity pattern ν remaining extra m q inverse index
    rectangle firstSign negative firstSupport
    (primeSupport (primePowerProduct p leftMultiplicity).val) _ (fun _ h => h)
    hl hr support hplain₁ hplain₂ hslots κ ξ u
  intro v hv
  rw [hextra]
  exact dvd_literalDeletionIdeal firstSupport hfirst v hv

/-- The slot characters are the same original characters selected by
the actual occurrence embedding, including when no slot is retained. -/
theorem slot_in_theta (hslot : ∀ i, parent.slotCoefficient i ∈ parent.theta)
    (ξ : WithLp 2 (ℝ × ℝ)) (i : Fin (child ξ).geometry.slotCount) :
    (child ξ).slotCoefficient i ∈ (child ξ).theta :=
  hslot (index (SlotRestriction.index B.keep i))

/-- A condition on the original background alone supplies the
principal-row implication.  The finite set theta is not assumed to be
a subgroup, and its membership is not enlarged for the child. -/
theorem principal_in_theta
    (hbackground : parent.plainBackground⁻¹ ∈ parent.theta ∨
      ¬ FiniteOrder parent.plainBackground)
    (ξ : WithLp 2 (ℝ × ℝ)) (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hprincipal : (child ξ).plainBackground * (child ξ).rowCharacter u = 1) :
    (child ξ).rowCharacter u ∈ (child ξ).theta := by
  change parent.plainBackground * (child ξ).rowCharacter u = 1 at hprincipal
  have hrow : (child ξ).rowCharacter u = parent.plainBackground⁻¹ :=
    eq_inv_of_mul_eq_one_right hprincipal
  change (child ξ).rowCharacter u ∈ parent.theta
  rcases hbackground with hmem | hinfinite
  · rw [hrow]
    exact hmem
  · have hfinite : FiniteOrder (parent.plainBackground⁻¹) := by
      rw [← hrow]
      exact (child ξ).rowCharacter_finite u
    exact False.elim (hinfinite (isOfFinOrder_inv_iff.mp hfinite))

end ActualData

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllocatedSupport

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllocatedSupport.dvd_literalDeletionIdeal
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllocatedSupport.avoids_of_maskConsequences
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllocatedSupport.mask_consequences
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllocatedSupport.effectiveSupports
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllocatedSupport.effectiveSupports_of_original_deletions
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllocatedSupport.slot_in_theta
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllocatedSupport.principal_in_theta
