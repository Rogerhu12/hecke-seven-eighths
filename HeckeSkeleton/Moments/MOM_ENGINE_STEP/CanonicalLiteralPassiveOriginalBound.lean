import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralOriginalEnergy
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralOriginalFrozenCost
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveNormalizedFamily

/-!
# The original allocated energy reaches its passive frames

The original complete coefficient is first evaluated on its actual
frequency row. Its old frozen scalar is estimated inside the same
finite row norm. The actual single-occurrence dictionaries then expand
the remaining complete centered polynomial over its passive labels.
Finite Minkowski reaches the frames already stored at those labels.

The original second divisor appears only in `originalFrozenCost`.
Every new passive divisor retains its own label. No source-energy
inequality or whole-polynomial identity is supplied to this theorem.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckePort.Moments
open HeckeGeneral.ThetaSkeleton.Physical (ProbeData RowCharacterInput)
open HeckePort.IdealMobiusDivisorSum

namespace CanonicalLiteralPassiveOriginalBound

open CanonicalLiteralPassiveSource CanonicalLiteralPassiveEnergy
open CanonicalLiteralPassiveFrames CanonicalLiteralPassiveFrameEnergy
open CanonicalLiteralPassiveNonzero

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {k : ℕ}
variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (B : ActualColumnAllocation K k)
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (Rchar : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {ω ψ : HeckeCharacter K}
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P Rchar)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C : A.GeneralArithmeticContext σ η hS)
variable (S : ActualSecondCorrelationRows A σ H ι)
variable (pattern : ι → Bool)
variable (sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (index : Fin k → Fin parent.geometry.slotCount)
variable (choice : PhaseChoice F C)
variable (hone : (1 : HeckeCharacter K) ∈ parent.theta)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
variable (hcharacters : d.characters = CanonicalLiteralPhaseCalibration.sourceCharacters
  P Rchar F parent oldMoving correction remaining extra index)
variable (firstSupport : Finset (Ideal (𝓞 K)))
variable (hfirst : ∀ p ∈ firstSupport, Prime p)
variable (hextra : extra = literalDeletionIdeal firstSupport hfirst)
variable (hl : ∀ i, 0 < S.leftMultiplicity i) (hr : ∀ i, 0 < S.rightMultiplicity i)
variable (support : d.SupportData ((primeSupport A.cS ∪ firstSupport) ∪
  primeSupport (primePowerProduct S.primes S.leftMultiplicity).val))
variable (hplain₁ : B.plain₁ = d.plain₁) (hplain₂ : B.plain₂ = d.plain₂)
variable (hslots : B.slots = d.slots)
variable (patternRows : S.live → CanonicalOriginalPhaseCalibration.PatternSector
  P S C pattern sector)
variable (patternRows_val : ∀ h, (patternRows h).val.val = h)

local notation "paid" => (CanonicalLiteralPaidCharacters.paidSourceCharacters P Rchar
  choice.phases parent oldMoving correction remaining index).restrictSlots B.keep

include hcorr hone hroot hemb hcharacters hfirst hextra hl hr support
  hplain₁ hplain₂ hslots patternRows patternRows_val in
/-- The auxiliary arithmetic dictionary is constructed from the
original atoms. Its row budget is irrelevant to this finite identity. -/
theorem centered_eq_passive (h : S.live) (firstSign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    centeredColumn (σ := σ) (d := d) B (d.characters.restrictSlots B.keep)
      (if negative then -(S.factor C h.val) else S.factor C h.val)
      (S.extractedRow C h).element firstSign negative ξ =
    passiveColumn (σ := σ) W B paid (choice.mask extra)
      (if negative then -(S.factor C h.val) else S.factor C h.val)
      (S.extractedRow C h).element firstSign negative ξ := by
  have he := actual_centered_allocations
    (W := W) (B := B) (P := P) (R := Rchar) (F := F) (parent := parent)
    (oldMoving := oldMoving) (correction := correction) (hcorr := hcorr)
    (C := C) (S := S) (pattern := pattern) (ν := sector)
    (remaining := remaining) (extra := extra) (m := 0) (q := 0)
    (inverse := parent.inverseTest) (index := index) (firstSign := firstSign)
    (negative := negative) (hone := hone) (hroot := hroot) (hemb := hemb)
    (row := patternRows h) choice hcharacters firstSupport hfirst hextra hl hr
    support hplain₁ hplain₂ hslots ξ
  simpa only [patternRows_val h] using he

include hcorr hone hroot hemb hcharacters hfirst hextra hl hr support
  hplain₁ hplain₂ hslots patternRows patternRows_val in
/-- The old frozen allocation is charged inside the original row
square norm, before the passive expansion is estimated. -/
theorem sqrt_frequency_le_passive
    (hsquarefree : Squarefree B.divisor)
    (hselection : B.selection ∈ AllocationMass.idealAllocations B.divisor (k + 2))
    (firstSign : ℝ) (negative : Bool) (ξ : WithLp 2 (ℝ × ℝ)) :
    Real.sqrt (jointColumnEnergy (Finset.univ : Finset S.live) B.columns
      (fun h => S.weight h.val * S.correlation h.val)
      (fun h => d.frequencyWhole (σ := σ)
        (if negative then -(S.factor C h.val) else S.factor C h.val)
        (S.extractedRow C h).element)
      (fun _ => canonicalPoint firstSign negative) ξ) ≤
    Real.sqrt (d.originalFrozenCost B) *
      Real.sqrt (∑ h : S.live, ‖S.weight h.val * S.correlation h.val‖ *
        ‖passiveColumn (σ := σ) W B paid (choice.mask extra)
          (if negative then -(S.factor C h.val) else S.factor C h.val)
          (S.extractedRow C h).element firstSign negative ξ‖ ^ 2) := by
  have hmask : d.characters.MaskIndicator := by
    rw [hcharacters]
    exact CanonicalLiteralPhaseCalibration.sourceCharacters_maskIndicator P Rchar F
      parent oldMoving correction remaining extra index
  have he := original_sqrt_le_actualCost
    (d := d) (B := B) (C := C) (rows := (Finset.univ : Finset S.live))
    (weight := fun h => S.weight h.val * S.correlation h.val)
    (g := fun h => if negative then -(S.factor C h.val) else S.factor C h.val)
    (h := fun h => (S.extractedRow C h).element)
    (firstSign := firstSign) (negative := negative)
    hmask hsquarefree hselection ξ
  have hsum :
      (∑ h : S.live, ‖S.weight h.val * S.correlation h.val‖ *
        ‖centeredColumn (σ := σ) (d := d) B (d.characters.restrictSlots B.keep)
          (if negative then -(S.factor C h.val) else S.factor C h.val)
          (S.extractedRow C h).element firstSign negative ξ‖ ^ 2) =
      ∑ h : S.live, ‖S.weight h.val * S.correlation h.val‖ *
        ‖passiveColumn (σ := σ) W B paid (choice.mask extra)
          (if negative then -(S.factor C h.val) else S.factor C h.val)
          (S.extractedRow C h).element firstSign negative ξ‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro h _
    rw [centered_eq_passive W B P Rchar F parent oldMoving correction hcorr C S
      pattern sector remaining extra index choice hone hroot hemb hcharacters
      firstSupport hfirst hextra hl hr support hplain₁ hplain₂ hslots
      patternRows patternRows_val h firstSign negative ξ]
  simpa only [hsum] using he

include hcorr hone hroot hemb hcharacters hfirst hextra hl hr support
  hplain₁ hplain₂ hslots patternRows patternRows_val in
/-- Every frame in this bound has the original stored passive label.
The common continuous Fourier parameter is unchanged. -/
theorem sqrt_frequency_le_frames
    (hsquarefree : Squarefree B.divisor)
    (hselection : B.selection ∈ AllocationMass.idealAllocations B.divisor (k + 2))
    (firstSign : ℝ) (negative : Bool) (ξ : WithLp 2 (ℝ × ℝ)) :
    Real.sqrt (jointColumnEnergy (Finset.univ : Finset S.live) B.columns
      (fun h => S.weight h.val * S.correlation h.val)
      (fun h => d.frequencyWhole (σ := σ)
        (if negative then -(S.factor C h.val) else S.factor C h.val)
        (S.extractedRow C h).element)
      (fun _ => canonicalPoint firstSign negative) ξ) ≤
    Real.sqrt (d.originalFrozenCost B) *
      ∑ a ∈ nonzeroLabels W B A (choice.mask extra),
        (Real.sqrt ((frame W B A paid C S (if negative then .right else .left)
          (choice.mask extra) a firstSign false).energy ξ) +
          Real.sqrt ((frame W B A paid C S (if negative then .right else .left)
            (choice.mask extra) a firstSign true).energy ξ)) := by
  exact (sqrt_frequency_le_passive W B P Rchar F parent oldMoving correction hcorr C S
    pattern sector remaining extra index choice hone hroot hemb hcharacters
    firstSupport hfirst hextra hl hr support hplain₁ hplain₂ hslots
    patternRows patternRows_val hsquarefree hselection firstSign negative ξ).trans
      (mul_le_mul_of_nonneg_left
        (sqrt_passiveColumn_le_frames B W paid C S (choice.mask extra) firstSign negative ξ)
        (Real.sqrt_nonneg _))

end CanonicalLiteralPassiveOriginalBound
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveOriginalBound.centered_eq_passive
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveOriginalBound.sqrt_frequency_le_passive
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveOriginalBound.sqrt_frequency_le_frames
