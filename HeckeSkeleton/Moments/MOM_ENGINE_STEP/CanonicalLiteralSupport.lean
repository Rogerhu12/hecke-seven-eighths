import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralProfileData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.EffectiveChildSupport

/-!
# Actual finite supports after occurrence extraction

The smooth profiles are not masked. At a retained ideal their actual
nonzero value gives membership in the original support once the deleted
primes are avoided. The first and second occurrence extractions preserve
this assertion, using their original witnesses and exact reconstruction.

An allocation divisor is coprime to every already deleted prime because
it divides an actual original occurrence. Consequently the child mask,
the computed Fourier profile and the literal quotient support give the
effective-support fields of the actual calibration. There is no assumed
polynomial equality or final energy bound.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum
open WholeAllocation

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralSupport

def Avoids (I : Ideal (𝓞 K)) (S : Finset (Ideal (𝓞 K))) : Prop :=
  ∀ p ∈ S, IsCoprime I p

theorem avoids_union (I : Ideal (𝓞 K)) (S T : Finset (Ideal (𝓞 K))) :
    Avoids I (S ∪ T) ↔ Avoids I S ∧ Avoids I T := by
  simp only [Avoids, Finset.mem_union, or_imp, forall_and]

theorem residual_avoids (I : Ideal (𝓞 K)) (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ p ∈ S, Prime p) : Avoids (supportResidual I S) S :=
  (outside_iff_coprime S hS ⟨_, supportResidual_ne_zero I S⟩).mp
    (residual_outside S hS I)

theorem residual_dvd (I : Ideal (𝓞 K)) (hI : I ≠ 0) (S : Finset (Ideal (𝓞 K))) :
    supportResidual I S ∣ I := by
  refine ⟨supportExtract I S, ?_⟩
  rw [mul_comm, support_reconstruct I hI S]

theorem extract_dvd (I : Ideal (𝓞 K)) (hI : I ≠ 0) (S : Finset (Ideal (𝓞 K))) :
    supportExtract I S ∣ I :=
  ⟨supportResidual I S, (support_reconstruct I hI S).symm⟩

theorem plain_residual_mem (T S : Finset (Ideal (𝓞 K)))
    (hS : ∀ p ∈ S, Prime p) (D I : Ideal (𝓞 K)) (hD : D ≠ 0) (hI : I ≠ 0)
    (hsmooth : primeSupport D ⊆ S) (havoid : Avoids I S) (hmem : D * I ∈ T) :
    I ∈ SupportCartesian.plainResidual T S D := by
  have hp := split_product S hS ⟨⟨D, hD⟩, hsmooth⟩
    ⟨⟨I, hI⟩, (outside_iff_coprime S hS ⟨I, hI⟩).mpr havoid⟩
  exact Finset.mem_image.mpr
    ⟨D * I, Finset.mem_filter.mpr ⟨hmem, hp.1⟩, hp.2⟩

end CanonicalLiteralSupport

namespace CanonicalLiteralRectangles.Atoms

open CanonicalLiteralSupport

variable {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)

/-- Exact one-occurrence support, with its finite deletion condition.
The actual constructors below derive this from the original profiles. -/
structure SupportData (excluded : Finset (Ideal (𝓞 K))) : Prop where
  left_avoids : ∀ I ∈ d.plain₁, Avoids I excluded
  right_avoids : ∀ I ∈ d.plain₂, Avoids I excluded
  slot_avoids : ∀ j p, p ∈ d.slots j → Avoids p.asIdeal excluded
  left_mem : ∀ r I, d.rectangleLeftWeight r I ≠ 0 → Avoids I.val excluded → I.val ∈ d.plain₁
  right_mem : ∀ r I, d.rightWeight r I ≠ 0 → Avoids I.val excluded → I.val ∈ d.plain₂
  slot_mem : ∀ j p, d.slotWeight j p ≠ 0 → Avoids p.asIdeal excluded → p ∈ d.slots j

namespace SupportData

variable {d} {excluded : Finset (Ideal (𝓞 K))}

def scale (W : d.SupportData excluded) (c : ℂ) : (d.scale c).SupportData excluded where
  left_avoids := W.left_avoids
  right_avoids := W.right_avoids
  slot_avoids := W.slot_avoids
  left_mem r I hI havoid := by
    rw [d.scale_rectangleLeftWeight c r I] at hI
    exact W.left_mem r I (right_ne_zero_of_mul hI) havoid
  right_mem := W.right_mem
  slot_mem := W.slot_mem

def addGauss (W : d.SupportData excluded) (G₁ G₂ : ℝ) (G : Fin k → ℝ)
    (h₁ : 0 < G₁) (h₂ : 0 < G₂) (hG : ∀ i, 0 < G i) :
    (d.addGauss G₁ G₂ G h₁ h₂ hG).SupportData excluded where
  left_avoids := W.left_avoids
  right_avoids := W.right_avoids
  slot_avoids := W.slot_avoids
  left_mem r I hI havoid := by
    rw [d.addGauss_rectangleLeftWeight G₁ G₂ G h₁ h₂ hG r I] at hI
    exact W.left_mem r I (left_ne_zero_of_mul hI) havoid
  right_mem r I hI havoid := W.right_mem r I (left_ne_zero_of_mul hI) havoid
  slot_mem j p hp havoid := W.slot_mem j p (left_ne_zero_of_mul hp) havoid

def normPower (W : d.SupportData excluded) (δ : ℝ) :
    (d.normPower δ).SupportData excluded where
  left_avoids := W.left_avoids
  right_avoids := W.right_avoids
  slot_avoids := W.slot_avoids
  left_mem r I hI havoid := by
    rw [d.normPower_rectangleLeftWeight δ r I] at hI
    exact W.left_mem r I (left_ne_zero_of_mul hI) havoid
  right_mem r I hI havoid := W.right_mem r I (left_ne_zero_of_mul hI) havoid
  slot_mem j p hp havoid := W.slot_mem j p (left_ne_zero_of_mul hp) havoid

variable {S : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots S)

private theorem extract_left_avoids (W : d.SupportData excluded) :
    Avoids b.plainExtract₁ excluded := by
  have hm := Finset.mem_filter.mp
    (Finset.mem_product.mp (Finset.mem_product.mp b.witness_mem).1).1
  intro p hp
  rw [← hm.2]
  exact (W.left_avoids b.witness.1.1 hm.1 p hp).of_isCoprime_of_dvd_left
    (extract_dvd b.witness.1.1 (d.plain₁_nonzero _ hm.1) S)

private theorem extract_right_avoids (W : d.SupportData excluded) :
    Avoids b.plainExtract₂ excluded := by
  have hm := Finset.mem_filter.mp
    (Finset.mem_product.mp (Finset.mem_product.mp b.witness_mem).1).2
  intro p hp
  rw [← hm.2]
  exact (W.right_avoids b.witness.1.2 hm.1 p hp).of_isCoprime_of_dvd_left
    (extract_dvd b.witness.1.2 (d.plain₂_nonzero _ hm.1) S)

/-- The retained profile is unchanged. Only the actual extraction's
prime exclusion is added, with both directions of support proved. -/
def extract (W : d.SupportData excluded) (hS : ∀ p ∈ S, Prime p) :
    (d.extract b).SupportData (excluded ∪ S) where
  left_avoids I hI := by
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    apply (avoids_union _ excluded S).mpr
    refine ⟨?_, residual_avoids J S hS⟩
    intro p hp
    exact (W.left_avoids J (Finset.mem_filter.mp hJ).1 p hp).of_isCoprime_of_dvd_left
      (residual_dvd J (d.plain₁_nonzero J (Finset.mem_filter.mp hJ).1) S)
  right_avoids I hI := by
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    apply (avoids_union _ excluded S).mpr
    refine ⟨?_, residual_avoids J S hS⟩
    intro p hp
    exact (W.right_avoids J (Finset.mem_filter.mp hJ).1 p hp).of_isCoprime_of_dvd_left
      (residual_dvd J (d.plain₂_nonzero J (Finset.mem_filter.mp hJ).1) S)
  slot_avoids j p hp := by
    have hm := Finset.mem_filter.mp hp
    apply (avoids_union _ excluded S).mpr
    refine ⟨W.slot_avoids _ p hm.1, ?_⟩
    have ha := residual_avoids p.asIdeal S hS
    rwa [supportResidual_prime p.asIdeal p.prime S, if_neg hm.2] at ha
  left_mem r I hI havoid := by
    rw [d.extract_rectangleLeftWeight b r I] at hI
    have ha := (avoids_union I.val excluded S).mp havoid
    have hm := W.left_mem r (b.plainDivisor₁ * I) hI (fun p hp =>
      (extract_left_avoids b W p hp).mul_left (ha.1 p hp))
    have hs := (Finset.mem_filter.mp
      (Finset.mem_product.mp (Finset.mem_product.mp b.witness_mem).1).1).2
    apply plain_residual_mem d.plain₁ S hS b.plainExtract₁ I.val
      b.plainExtract₁_ne_zero (nonZeroDivisors.coe_ne_zero I) _ ha.2 hm
    rw [← hs, supportExtract_support]
    exact Finset.inter_subset_right
  right_mem r I hI havoid := by
    have ha := (avoids_union I.val excluded S).mp havoid
    have hm := W.right_mem r (b.plainDivisor₂ * I) hI (fun p hp =>
      (extract_right_avoids b W p hp).mul_left (ha.1 p hp))
    have hs := (Finset.mem_filter.mp
      (Finset.mem_product.mp (Finset.mem_product.mp b.witness_mem).1).2).2
    apply plain_residual_mem d.plain₂ S hS b.plainExtract₂ I.val
      b.plainExtract₂_ne_zero (nonZeroDivisors.coe_ne_zero I) _ ha.2 hm
    rw [← hs, supportExtract_support]
    exact Finset.inter_subset_right
  slot_mem j p hp havoid := by
    have ha := (avoids_union p.asIdeal excluded S).mp havoid
    apply Finset.mem_filter.mpr
    refine ⟨W.slot_mem _ p hp ha.1, ?_⟩
    intro hmem
    exact p.prime.not_unit ((ha.2 p.asIdeal hmem).isUnit_of_dvd (dvd_refl _))

def firstExtracted (W : d.SupportData excluded) (hS : ∀ p ∈ S, Prime p) :
    (d.firstExtracted b).SupportData (excluded ∪ S) :=
  (W.extract b hS).scale (d.commonScalar b)

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)

def movingSingleton (W : d.SupportData excluded) (I : A.Exterior) (a : A.R)
    (ha : A.Generates I a) :
    (d.movingSingleton P R I a ha).SupportData excluded where
  left_avoids := W.left_avoids
  right_avoids := W.right_avoids
  slot_avoids := W.slot_avoids
  left_mem := W.left_mem
  right_mem := W.right_mem
  slot_mem := W.slot_mem

def secondInput (W : d.SupportData excluded) (hS : ∀ p ∈ S, Prime p)
    (power firstFixed poolFixed unitFixed : A.Exterior)
    (firstElement poolElement unitElement : A.R)
    (hfirst : A.Generates firstFixed firstElement)
    (hpool : A.Generates poolFixed poolElement)
    (hunit : A.Generates unitFixed unitElement) (δ₁ δ₂ : ℝ) :
    (d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).SupportData
        (excluded ∪ S) := by
  let e := d.firstExtracted b
  let w := W.firstExtracted b hS
  let v := (((w.addGauss (e.scale₁ false) (e.scale₂ false)
    (fun j => e.base ^ e.length j) (e.scale₁_pos false) (e.scale₂_pos false)
    (fun _ => Real.rpow_pos_of_pos (zero_lt_one.trans e.base_gt_one) _)).normPower (-1))
      .normPower δ₁).normPower δ₂
  exact (((v.movingSingleton P R firstFixed firstElement hfirst)
    .movingSingleton P R poolFixed poolElement hpool)
    .movingSingleton P R unitFixed unitElement hunit).scale
      (((A.exteriorNorm power ^ δ₁ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ) power.val firstElement)

end SupportData
end CanonicalLiteralRectangles.Atoms

namespace CompleteMovingRowRecipe

open CanonicalLiteralSupport

variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {X : Type*}
variable {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data)

/-- The original atom table supplies its support data from an original
paired row. No later ordinary row or normalized child is consulted. -/
def literalOriginalSupportData (ξ : X)
    (W : NormProfileRecipe (fun _ : PUnit => data ξ))
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
    (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (reference : HeckeGeneral.Analysis.NonzeroIdeal K)
    (href : reference ∈ pairedRows (data ξ) a Z) :
    (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).SupportData
      (primeSupport A.cS) where
  left_avoids I hI := by
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    exact (coprime_support_iff J.val A.cS A.cS_ne_zero).mp (Finset.mem_filter.mp hJ).2
  right_avoids I hI := by
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    exact (coprime_support_iff J.val A.cS A.cS_ne_zero).mp (Finset.mem_filter.mp hJ).2
  slot_avoids j p hp :=
    (coprime_support_iff p.asIdeal A.cS A.cS_ne_zero).mp (Finset.mem_filter.mp hp).2
  left_mem r I hI havoid :=
    Q.literalOriginalAtoms_left_weight_mem ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      reference href r I ((coprime_support_iff I.val A.cS A.cS_ne_zero).mpr havoid)
      (CanonicalLiteralRectangles.Atoms.rectangleLeftWeight_ne_zero _ r I hI)
  right_mem r I hI havoid :=
    Q.literalOriginalAtoms_right_weight_mem ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      reference href r I ((coprime_support_iff I.val A.cS A.cS_ne_zero).mpr havoid) hI
  slot_mem j p hp havoid :=
    Q.literalOriginalAtoms_slot_weight_mem ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ j p
      ((coprime_support_iff p.asIdeal A.cS A.cS_ne_zero).mpr havoid) hp

end CompleteMovingRowRecipe

namespace CanonicalLiteralRectangles.Atoms.SupportData

open CanonicalLiteralSupport

variable {k : ℕ} {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable {excluded : Finset (Ideal (𝓞 K))}

/-- Every allocated divisor divides the actual original witness at
that occurrence, so it introduces no already excluded prime. -/
theorem leftDivisor_avoids (W : d.SupportData excluded) (B : ActualColumnAllocation K k)
    (hplain : B.plain₁ = d.plain₁) : Avoids (B.plainDivisor 0).val excluded := by
  have hm := Finset.mem_filter.mp
    (Finset.mem_product.mp (Finset.mem_product.mp B.witness_mem).1).1
  have hmem : B.witness.1.1 ∈ d.plain₁ := hplain ▸ hm.1
  intro p hp
  exact (W.left_avoids B.witness.1.1 hmem p hp).of_isCoprime_of_dvd_left hm.2

theorem rightDivisor_avoids (W : d.SupportData excluded) (B : ActualColumnAllocation K k)
    (hplain : B.plain₂ = d.plain₂) :
    Avoids (B.plainDivisor (Fin.succ 0)).val excluded := by
  have hm := Finset.mem_filter.mp
    (Finset.mem_product.mp (Finset.mem_product.mp B.witness_mem).1).2
  have hmem : B.witness.1.2 ∈ d.plain₂ := hplain ▸ hm.1
  intro p hp
  exact (W.right_avoids B.witness.1.2 hmem p hp).of_isCoprime_of_dvd_left hm.2

variable {ω ψ : HeckeCharacter K}

/-- The actual Fourier profile at the quotient scale has the full
allocated atom's support. Only its genuine mask supplies avoidance. -/
theorem fourierLeft_effectiveSupport (W : d.SupportData excluded) (profiles : d.ProfileData)
    (B : ActualColumnAllocation K k) (hplain : B.plain₁ = d.plain₁)
    (child : MomentData K ω ψ) (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (r : Bool) (firstSign : ℝ) (negative : Bool) (ξ : WithLp 2 (ℝ × ℝ)) (time : ℝ)
    (hmask : ∀ I : HeckeGeneral.Analysis.NonzeroIdeal K,
      maskValue child u I.val ≠ 0 → Avoids I.val excluded) :
    EffectivePlainSupport child (profiles.fourierLeft r firstSign negative ξ) u
      (d.scale₁ r / idealNorm K (B.plainDivisor 0)) time B.childPlain₁ := by
  intro I hI
  have ha := hmask I (right_ne_zero_of_mul hI)
  have hw := right_ne_zero_of_mul (left_ne_zero_of_mul hI)
  rw [profiles.fourierLeft_allocated r firstSign negative ξ u time
    (B.plainDivisor 0) I] at hw
  change I ∈ nonzeroQuotientMomentSupport (B.plainDivisor 0).val B.plain₁
  apply (mem_nonzeroQuotientMomentSupport _
    (nonZeroDivisors.coe_ne_zero (B.plainDivisor 0)) _ I).mpr
  rw [hplain]
  exact W.left_mem r (B.plainDivisor 0 * I) (left_ne_zero_of_mul hw)
    (fun p hp => (W.leftDivisor_avoids B hplain p hp).mul_left (ha p hp))

theorem fourierRight_effectiveSupport (W : d.SupportData excluded) (profiles : d.ProfileData)
    (B : ActualColumnAllocation K k) (hplain : B.plain₂ = d.plain₂)
    (child : MomentData K ω ψ) (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (r : Bool) (firstSign : ℝ) (negative : Bool) (ξ : WithLp 2 (ℝ × ℝ)) (time : ℝ)
    (hmask : ∀ I : HeckeGeneral.Analysis.NonzeroIdeal K,
      maskValue child u I.val ≠ 0 → Avoids I.val excluded) :
    EffectivePlainSupport child (profiles.fourierRight r firstSign negative ξ) u
      (d.scale₂ r / idealNorm K (B.plainDivisor (Fin.succ 0))) time B.childPlain₂ := by
  intro I hI
  have ha := hmask I (right_ne_zero_of_mul hI)
  have hw := right_ne_zero_of_mul (left_ne_zero_of_mul hI)
  rw [profiles.fourierRight_allocated r firstSign negative ξ u time
    (B.plainDivisor (Fin.succ 0)) I] at hw
  change I ∈ nonzeroQuotientMomentSupport (B.plainDivisor (Fin.succ 0)).val B.plain₂
  apply (mem_nonzeroQuotientMomentSupport _
    (nonZeroDivisors.coe_ne_zero (B.plainDivisor (Fin.succ 0))) _ I).mpr
  rw [hplain]
  exact W.right_mem r (B.plainDivisor (Fin.succ 0) * I) (left_ne_zero_of_mul hw)
    (fun p hp => (W.rightDivisor_avoids B hplain p hp).mul_left (ha p hp))

/-- Only the original retained slot is used. Its complete arithmetic
mask removes the excluded primes without altering its smooth window. -/
theorem fourierSlot_effectiveSupport (W : d.SupportData excluded) (profiles : d.ProfileData)
    (B : ActualColumnAllocation K k) (hslots : B.slots = d.slots)
    (child : MomentData K ω ψ) (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (count : child.geometry.slotCount = B.keep.card)
    (firstSign : ℝ) (negative : Bool) (ξ : WithLp 2 (ℝ × ℝ)) (time : ℝ)
    (hslot : ∀ i, child.geometry.slots i =
      profiles.fourierSlot (SlotRestriction.index B.keep (Fin.cast count i))
        firstSign negative ξ)
    (hmask : ∀ I : HeckeGeneral.Analysis.NonzeroIdeal K,
      maskValue child u I.val ≠ 0 → Avoids I.val excluded)
    (i : Fin child.geometry.slotCount) :
    EffectivePrimeSupport child i u d.base time (B.childSlots (Fin.cast count i)) := by
  intro p hp
  have ha := hmask
    (⟨p.asIdeal, mem_nonZeroDivisors_of_ne_zero p.ne_bot⟩ : HeckeGeneral.Analysis.NonzeroIdeal K)
    (right_ne_zero_of_mul hp)
  have hw := right_ne_zero_of_mul (left_ne_zero_of_mul hp)
  simp only [hslot i, profiles.fourierSlot_length] at hw
  rw [profiles.fourierSlot_eval] at hw
  change p ∈ B.slots (SlotRestriction.index B.keep (Fin.cast count i))
  rw [hslots]
  exact W.slot_mem _ p (left_ne_zero_of_mul hw) ha

end CanonicalLiteralRectangles.Atoms.SupportData

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalOriginalSupportData
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.SupportData.extract
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.SupportData.secondInput
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.SupportData.fourierLeft_effectiveSupport
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.SupportData.fourierSlot_effectiveSupport
