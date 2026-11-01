import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveSource

/-!
# Effective support of each actual passive quotient

The paid table uses the complete smooth carrier, filtered only by the
fixed exterior condition. Its support certificate is constructed from
the original profiles. An allocated plain divisor divides its actual
witness and is therefore coprime to the fixed modulus as well.

For the new child, a nonzero mask supplies that same fixed coprimality.
The quotient-profile identity then puts the product of the actual plain
divisor and the residual ideal into the full smooth carrier. The two
plain supports and the retained prime support follow on the stored
allocation, without a passive avoidance or support-norm assumption.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveSupport

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum
open CanonicalLiteralSupport CanonicalLiteralProfileCarrier
open CanonicalLiteralPassiveSource CanonicalLiteralAllocatedData

variable {K : Type} [Field K] [NumberField K] {k : ℕ}
variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (B : ActualColumnAllocation K k) (A : SArithmeticData K)

/-- This support record is an output of the actual frozen profiles;
the passive primes have not been filtered out of its carrier. -/
def tableSupport (paid : FixedChildCharacters K B.keep.card) :
    (table W B A paid).SupportData (primeSupport A.cS) where
  left_avoids I hI := by
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    exact (coprime_support_iff J.val A.cS A.cS_ne_zero).mp
      (W.exteriorSmoothPlain₁_coprime B A J hJ)
  right_avoids I hI := by
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    exact (coprime_support_iff J.val A.cS A.cS_ne_zero).mp
      (W.exteriorSmoothPlain₂_coprime B A J hJ)
  slot_avoids j p hp :=
    (coprime_support_iff p.asIdeal A.cS A.cS_ne_zero).mp
      (W.exteriorSmoothSlots_coprime B A j p hp)
  left_mem r I hI havoid := by
    refine Finset.mem_image.mpr ⟨I, Finset.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
    · apply W.left_support_subset_smooth B r 1 0
      apply ((W.left r).support_spec 1 0 _ I).mpr
      change ((profiles W B A paid).left r).profile 1 0
        (idealNorm K I / (table W B A paid).scale₁ r) ≠ 0
      rw [(profiles W B A paid).left_eval]
      exact hI
    · exact (coprime_support_iff I.val A.cS A.cS_ne_zero).mpr havoid
  right_mem r I hI havoid := by
    refine Finset.mem_image.mpr ⟨I, Finset.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
    · apply W.right_support_subset_smooth B r 1 0
      apply ((W.right r).support_spec 1 0 _ I).mpr
      change ((profiles W B A paid).right r).profile 1 0
        (idealNorm K I / (table W B A paid).scale₂ r) ≠ 0
      rw [(profiles W B A paid).right_eval]
      exact hI
    · exact (coprime_support_iff I.val A.cS A.cS_ne_zero).mpr havoid
  slot_mem j p hp havoid := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · apply ((W.slot (SlotRestriction.index B.keep j)).support_spec 0 _ p).mpr
      change ((profiles W B A paid).slot j).profile 0
        ((Ideal.absNorm p.asIdeal : ℝ) /
          (table W B A paid).base ^ (table W B A paid).length j) ≠ 0
      rw [(profiles W B A paid).slot_eval]
      exact hp
    · exact (coprime_support_iff p.asIdeal A.cS A.cS_ne_zero).mpr havoid

variable (M : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (a : { a // a ∈ CanonicalLiteralPassiveSource.labels W B A M })

/-- The divisor is the actual occurrence divisor of the stored
witness, so no new coprimality premise is needed for the quotient. -/
theorem leftDivisor_coprime :
    IsCoprime ((branch W B A M a).plainDivisor 0).val A.cS := by
  have hm := Finset.mem_filter.mp
    (Finset.mem_product.mp (Finset.mem_product.mp (branch W B A M a).witness_mem).1).1
  have hmem : (branch W B A M a).witness.1.1 ∈
      idealCarrier (W.exteriorSmoothPlain₁ B A) := hm.1
  obtain ⟨I, hI, hval⟩ := Finset.mem_image.mp hmem
  have hc : IsCoprime (branch W B A M a).witness.1.1 A.cS := by
    rw [← hval]
    exact W.exteriorSmoothPlain₁_coprime B A I hI
  exact hc.of_isCoprime_of_dvd_left hm.2

theorem rightDivisor_coprime :
    IsCoprime ((branch W B A M a).plainDivisor (Fin.succ 0)).val A.cS := by
  have hm := Finset.mem_filter.mp
    (Finset.mem_product.mp (Finset.mem_product.mp (branch W B A M a).witness_mem).1).2
  have hmem : (branch W B A M a).witness.1.2 ∈
      idealCarrier (W.exteriorSmoothPlain₂ B A) := hm.1
  obtain ⟨I, hI, hval⟩ := Finset.mem_image.mp hmem
  have hc : IsCoprime (branch W B A M a).witness.1.2 A.cS := by
    rw [← hval]
    exact W.exteriorSmoothPlain₂_coprime B A I hI
  exact hc.of_isCoprime_of_dvd_left hm.2

section ActualData

variable {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {ω ψ : HeckeCharacter K}
variable (paid : FixedChildCharacters K B.keep.card)
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
variable (leftMultiplicity rightMultiplicity : ι → ℕ) (pattern : ι → Bool)
variable (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) (m q : ℝ)
variable (inverse : IdealTest K) (index : Fin k → Fin parent.geometry.slotCount)
variable (rectangle : Bool) (firstSign : ℝ) (negative : Bool)

local notation "child" => data P R (profiles W B A paid) (branch W B A M a) F parent
  oldMoving correction hcorr C p leftMultiplicity rightMultiplicity pattern ν remaining 1 m q
  inverse (fun j => index (SlotRestriction.index B.keep j)) rectangle firstSign negative

/-- The actual appended child already contains the fixed exterior
mask; no passive-prime avoidance is assumed or inferred here. -/
theorem mask_nonzero_coprime (ξ : WithLp 2 (ℝ × ℝ))
    (u I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hmask : maskValue (child ξ) u I.val ≠ 0) : IsCoprime I.val A.cS :=
  (CanonicalLiteralAllocatedSupport.mask_consequences P R
    (profiles W B A paid) (branch W B A M a) F parent oldMoving correction hcorr C p
    leftMultiplicity rightMultiplicity pattern ν remaining 1 m q inverse
    (fun j => index (SlotRestriction.index B.keep j)) rectangle firstSign negative
    ξ u I hmask).fixed

/-- Both plain quotient supports and the twice-retained prime support
belong to the stored passive allocation. All support certificates are
constructed internally from the original profiles and the actual mask. -/
theorem effectiveSupports (κ : ℝ) (ξ : WithLp 2 (ℝ × ℝ))
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) :
    EffectivePlainSupport (child ξ) (child ξ).plainTest₁ u
        (d.base ^ (parameters (table W B A paid) (branch W B A M a)
          rectangle m q κ).n₁) (height ξ) (branch W B A M a).childPlain₁ ∧
      EffectivePlainSupport (child ξ) (child ξ).plainTest₂ u
        (d.base ^ (parameters (table W B A paid) (branch W B A M a)
          rectangle m q κ).n₂) (height ξ) (branch W B A M a).childPlain₂ ∧
      ∀ i : Fin (child ξ).geometry.slotCount,
        EffectivePrimeSupport (child ξ) i u d.base (height ξ)
          ((branch W B A M a).childSlots (Fin.cast
            (data_count P R (profiles W B A paid) (branch W B A M a) F parent oldMoving
              correction hcorr C p leftMultiplicity rightMultiplicity pattern ν remaining 1
              m q inverse (fun j => index (SlotRestriction.index B.keep j))
              rectangle firstSign negative ξ) i)) := by
  have hm : ∀ I : HeckeGeneral.Analysis.NonzeroIdeal K,
      maskValue (child ξ) u I.val ≠ 0 → Avoids I.val (primeSupport A.cS) := by
    intro I hI
    exact (coprime_support_iff I.val A.cS A.cS_ne_zero).mp
      (mask_nonzero_coprime W B A M a P R paid F parent oldMoving correction hcorr C p
        leftMultiplicity rightMultiplicity pattern ν remaining m q inverse index
        rectangle firstSign negative ξ u I hI)
  refine ⟨?_, ?_, ?_⟩
  · change EffectivePlainSupport (child ξ)
      ((profiles W B A paid).fourierLeft rectangle firstSign negative ξ) u
      ((table W B A paid).base ^ (parameters (table W B A paid) (branch W B A M a)
        rectangle m q κ).n₁) (height ξ) (branch W B A M a).childPlain₁
    rw [left_scale]
    exact (tableSupport W B A paid).fourierLeft_effectiveSupport
      (profiles W B A paid) (branch W B A M a) rfl (child ξ) u rectangle
      firstSign negative ξ (height ξ) hm
  · change EffectivePlainSupport (child ξ)
      ((profiles W B A paid).fourierRight rectangle firstSign negative ξ) u
      ((table W B A paid).base ^ (parameters (table W B A paid) (branch W B A M a)
        rectangle m q κ).n₂) (height ξ) (branch W B A M a).childPlain₂
    rw [right_scale]
    exact (tableSupport W B A paid).fourierRight_effectiveSupport
      (profiles W B A paid) (branch W B A M a) rfl (child ξ) u rectangle
      firstSign negative ξ (height ξ) hm
  · intro i
    exact (tableSupport W B A paid).fourierSlot_effectiveSupport
      (profiles W B A paid) (branch W B A M a) rfl (child ξ) u rfl
      firstSign negative ξ (height ξ) (fun _ => rfl) hm i

end ActualData

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveSupport

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveSupport.tableSupport
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveSupport.leftDivisor_coprime
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveSupport.rightDivisor_coprime
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveSupport.mask_nonzero_coprime
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveSupport.effectiveSupports
