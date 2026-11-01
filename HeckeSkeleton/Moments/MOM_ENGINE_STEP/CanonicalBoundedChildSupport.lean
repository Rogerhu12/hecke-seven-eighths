import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalBoundedChildData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalEffectiveChildSupport

/-!
# Effective supports of the same bounded original child

The two original common-support branches and the final allocation keep
their own witnesses. These witnesses prove all extraction and divisor
conditions used below. No inclusion of a completed child support is an
input. The only profile support is the original parent support at its
actual anchor and height.

The bounded signed multipliers preserve those finite supports. Their
complete arithmetic mask excludes both original common-prime sets:
the first is in the literal remaining ideal, and the second is in the
actual active frequency together with its full sixth-root remainder.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.CanonicalBoundedChildSupport

open NumberField IsDedekindDomain DedekindZetaZeroFree UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical HeckePort.Moments HeckePort.Moments.Support
open HeckePort.IdealMobiusDivisorSum WholeAllocation
open CanonicalEffectiveChildSupport CanonicalBoundedChildData

variable {K : Type} [Field K] [NumberField K]

section FiniteSupports

private theorem extract_dvd (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (P : Finset (Ideal (𝓞 K))) : supportExtract I P ∣ I := by
  exact ⟨supportResidual I P, (support_reconstruct I hI P).symm⟩

private theorem residual_dvd (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (P : Finset (Ideal (𝓞 K))) : supportResidual I P ∣ I := by
  exact ⟨supportExtract I P, by
    simpa only [mul_comm] using (support_reconstruct I hI P).symm⟩

theorem plainResidual_ne_zero (S P : Finset (Ideal (𝓞 K))) (D I : Ideal (𝓞 K))
    (hI : I ∈ SupportCartesian.plainResidual S P D) : I ≠ 0 := by
  obtain ⟨J, _, rfl⟩ := Finset.mem_image.mp hI
  exact supportResidual_ne_zero J P

/-- Every actual divisor of a residual occurrence avoids its original
common-prime set. The divisor condition comes from the allocation. -/
theorem extract_one_of_dvd_plainResidual (S P : Finset (Ideal (𝓞 K)))
    (D I E : Ideal (𝓞 K)) (hE : E ≠ 0)
    (hI : I ∈ SupportCartesian.plainResidual S P D) (hd : E ∣ I) :
    supportExtract E P = 1 := by
  obtain ⟨J, _, rfl⟩ := Finset.mem_image.mp hI
  exact supportExtract_eq_one_of_dvd_residual J E hE P hd

/-- A divisor of a twice-residual occurrence avoids both extracted
sets. This includes the literal allocated occurrence divisor. -/
theorem extract_one_of_dvd_twice_plainResidual
    (S P Q : Finset (Ideal (𝓞 K))) (D₁ D₂ I E : Ideal (𝓞 K)) (hE : E ≠ 0)
    (hI : I ∈ SupportCartesian.plainResidual
      (SupportCartesian.plainResidual S P D₁) Q D₂) (hd : E ∣ I) :
    supportExtract E P = 1 ∧ supportExtract E Q = 1 := by
  have hQ := extract_one_of_dvd_plainResidual
    (SupportCartesian.plainResidual S P D₁) Q D₂ I E hE hI hd
  obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
  have hJmem : J ∈ SupportCartesian.plainResidual S P D₁ :=
    (Finset.mem_filter.mp hJ).1
  have hJ0 := plainResidual_ne_zero S P D₁ J hJmem
  exact ⟨extract_one_of_dvd_plainResidual S P D₁ J E hE hJmem
    (hd.trans (residual_dvd J hJ0 Q)), hQ⟩

/-- Both original extracted parts are read from genuine nonempty
fibres. The second extracted part is itself prime to the first set. -/
private theorem extraction_parts
    (S P Q : Finset (Ideal (𝓞 K))) (D₁ D₂ W₁ W₂ : Ideal (𝓞 K))
    (hD₂ : D₂ ≠ 0)
    (hW₁ : W₁ ∈ SupportCartesian.plainFibre S P D₁)
    (hW₂ : W₂ ∈ SupportCartesian.plainFibre
      (SupportCartesian.plainResidual S P D₁) Q D₂) :
    supportExtract D₁ P = D₁ ∧
      supportExtract D₂ Q = D₂ ∧ supportExtract D₂ P = 1 := by
  have h₁ := (Finset.mem_filter.mp hW₁).2
  have h₂ := (Finset.mem_filter.mp hW₂).2
  have hmem := (Finset.mem_filter.mp hW₂).1
  have hW₂0 := plainResidual_ne_zero S P D₁ W₂ hmem
  refine ⟨?_, ?_, ?_⟩
  · rw [← h₁]
    exact supportExtract_idempotent W₁ P
  · rw [← h₂]
    exact supportExtract_idempotent W₂ Q
  · exact extract_one_of_dvd_plainResidual S P D₁ W₂ D₂ hD₂ hmem
      (h₂ ▸ extract_dvd W₂ hW₂0 Q)

/-- The literal threefold reconstruction gives the final allocated
quotient of the two original residual supports. All extraction facts
are derived from the three original witnesses. -/
theorem mem_twice_allocated_of_original
    (S P Q : Finset (Ideal (𝓞 K))) (D₁ D₂ E I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (W₁ W₂ W₃ : Ideal (𝓞 K))
    (hW₁ : W₁ ∈ SupportCartesian.plainFibre S P D₁.val)
    (hW₂ : W₂ ∈ SupportCartesian.plainFibre
      (SupportCartesian.plainResidual S P D₁.val) Q D₂.val)
    (hW₃ : W₃ ∈ SupportCartesian.plainResidual
      (SupportCartesian.plainResidual S P D₁.val) Q D₂.val)
    (hE : E.val ∣ W₃)
    (hI₁ : supportExtract I.val P = 1) (hI₂ : supportExtract I.val Q = 1)
    (hmem : (D₁ * (D₂ * (E * I))).val ∈ S) :
    I ∈ nonzeroQuotientMomentSupport E.val
      (SupportCartesian.plainResidual
        (SupportCartesian.plainResidual S P D₁.val) Q D₂.val) := by
  have hparts := extraction_parts S P Q D₁.val D₂.val W₁ W₂
    (nonZeroDivisors.coe_ne_zero D₂) hW₁ hW₂
  have hEparts := extract_one_of_dvd_twice_plainResidual S P Q D₁.val D₂.val W₃ E.val
    (nonZeroDivisors.coe_ne_zero E) hW₃ hE
  have hEI₁ : supportExtract (E.val * I.val) P = 1 := by
    rw [supportExtract_mul E.val I.val (nonZeroDivisors.coe_ne_zero E)
      (nonZeroDivisors.coe_ne_zero I), hEparts.1, hI₁, one_mul]
  have hEI₂ : supportExtract (E.val * I.val) Q = 1 := by
    rw [supportExtract_mul E.val I.val (nonZeroDivisors.coe_ne_zero E)
      (nonZeroDivisors.coe_ne_zero I), hEparts.2, hI₂, one_mul]
  have hD₂EI : supportExtract (D₂.val * (E.val * I.val)) P = 1 := by
    rw [supportExtract_mul D₂.val (E.val * I.val) (nonZeroDivisors.coe_ne_zero D₂)
      (mul_ne_zero (nonZeroDivisors.coe_ne_zero E) (nonZeroDivisors.coe_ne_zero I)),
      hparts.2.2, hEI₁, one_mul]
  rw [mem_nonzeroQuotientMomentSupport E.val (nonZeroDivisors.coe_ne_zero E)]
  apply mem_plainResidual_of_reconstruct _ Q D₂.val (E.val * I.val)
    (nonZeroDivisors.coe_ne_zero D₂)
    (mul_ne_zero (nonZeroDivisors.coe_ne_zero E) (nonZeroDivisors.coe_ne_zero I))
    hparts.2.1 hEI₂
  exact mem_plainResidual_of_reconstruct S P D₁.val (D₂.val * (E.val * I.val))
    (nonZeroDivisors.coe_ne_zero D₁)
    (mul_ne_zero (nonZeroDivisors.coe_ne_zero D₂)
      (mul_ne_zero (nonZeroDivisors.coe_ne_zero E) (nonZeroDivisors.coe_ne_zero I)))
    hparts.1 hD₂EI hmem

variable {k : ℕ} {S₁ S₂ : Finset (Ideal (𝓞 K))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 K))}
variable {P Q : Finset (Ideal (𝓞 K))}
variable (b₁ : SupportCartesianBranch S₁ S₂ S P)
local notation "T₁" => SupportCartesian.plainResidual S₁ P b₁.plainExtract₁
local notation "T₂" => SupportCartesian.plainResidual S₂ P b₁.plainExtract₂
local notation "T" => fun j => SupportCartesian.primeLive
  (S (SlotRestriction.index b₁.keep j)) P
variable (b₂ : SupportCartesianBranch T₁ T₂ T Q)
local notation "U₁" => SupportCartesian.plainResidual T₁ Q b₂.plainExtract₁
local notation "U₂" => SupportCartesian.plainResidual T₂ Q b₂.plainExtract₂
local notation "U" => fun j => SupportCartesian.primeLive
  (T (SlotRestriction.index b₂.keep j)) Q
variable (B : ActualColumnAllocation K b₂.keep.card)

/-- The actual left allocation witness supplies its own divisor and
both preceding extraction witnesses. The carrier equality is literal
source data, rather than a completed support bound. -/
theorem left_mem_child_of_original (hB : B.plain₁ = U₁) (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hI₁ : supportExtract I.val P = 1) (hI₂ : supportExtract I.val Q = 1)
    (hmem : (b₁.plainDivisor₁ *
      (b₂.plainDivisor₁ * (B.plainDivisor 0 * I))).val ∈ S₁) :
    I ∈ B.childPlain₁ := by
  have hw := Finset.mem_filter.mp
    (Finset.mem_product.mp (Finset.mem_product.mp B.witness_mem).1).1
  change B.witness.1.1 ∈ B.plain₁ ∧ (B.plainDivisor 0).val ∣ B.witness.1.1 at hw
  change I ∈ nonzeroQuotientMomentSupport (B.plainDivisor 0).val B.plain₁
  rw [hB]
  exact mem_twice_allocated_of_original S₁ P Q b₁.plainDivisor₁ b₂.plainDivisor₁
    (B.plainDivisor 0) I b₁.witness.1.1 b₂.witness.1.1 B.witness.1.1
    (Finset.mem_product.mp (Finset.mem_product.mp b₁.witness_mem).1).1
    (Finset.mem_product.mp (Finset.mem_product.mp b₂.witness_mem).1).1
    (hB ▸ hw.1) hw.2 hI₁ hI₂ hmem

theorem right_mem_child_of_original (hB : B.plain₂ = U₂) (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hI₁ : supportExtract I.val P = 1) (hI₂ : supportExtract I.val Q = 1)
    (hmem : (b₁.plainDivisor₂ *
      (b₂.plainDivisor₂ * (B.plainDivisor (Fin.succ 0) * I))).val ∈ S₂) :
    I ∈ B.childPlain₂ := by
  have hw := Finset.mem_filter.mp
    (Finset.mem_product.mp (Finset.mem_product.mp B.witness_mem).1).2
  change B.witness.1.2 ∈ B.plain₂ ∧
    (B.plainDivisor (Fin.succ 0)).val ∣ B.witness.1.2 at hw
  change I ∈ nonzeroQuotientMomentSupport (B.plainDivisor (Fin.succ 0)).val B.plain₂
  rw [hB]
  exact mem_twice_allocated_of_original S₂ P Q b₁.plainDivisor₂ b₂.plainDivisor₂
    (B.plainDivisor (Fin.succ 0)) I b₁.witness.1.2 b₂.witness.1.2 B.witness.1.2
    (Finset.mem_product.mp (Finset.mem_product.mp b₁.witness_mem).1).2
    (Finset.mem_product.mp (Finset.mem_product.mp b₂.witness_mem).1).2
    (hB ▸ hw.1) hw.2 hI₁ hI₂ hmem

/-- A retained original prime occurrence avoids both common sets.
All three index maps are the actual successive slot restrictions. -/
theorem prime_mem_child_of_original (hB : B.slots = U)
    (j : Fin B.keep.card) (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∈ S (SlotRestriction.index b₁.keep
      (SlotRestriction.index b₂.keep (SlotRestriction.index B.keep j))))
    (hp₁ : p.asIdeal ∉ P) (hp₂ : p.asIdeal ∉ Q) : p ∈ B.childSlots j := by
  change p ∈ B.slots (SlotRestriction.index B.keep j)
  rw [hB]
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hp, hp₁⟩, hp₂⟩

end FiniteSupports

section ActualMasks

variable {A : SArithmeticData K} {σ : K →+* ℂ} {ω ψ : HeckeCharacter K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}

/-- Positive original multiplicities give the same displayed common
support on the two sides, before the sixth/active splitting. -/
theorem positive_common_support_eq (p : ι → ExteriorPrime A)
    (hp : Function.Injective p) (m n : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) :
    primeSupport (primePowerProduct p m).val = primeSupport (primePowerProduct p n).val := by
  rw [primePowerProduct_support_nonzero p hp m, primePowerProduct_support_nonzero p hp n]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact iff_of_true (Nat.ne_of_gt (hm i)) (Nat.ne_of_gt (hn i))

variable (parent : MomentData K ω ψ) (prefix : OriginalMovingFactors A P R)
variable (correction : HeckeCharacter K) (hcorr : correction = 1 ∨ correction ∈ parent.theta)
variable (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
variable (hp : Function.Injective p) (m n : ι → ℕ)
variable (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (pattern : ι → Bool)
variable (sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) (firstCommon : A.Exterior) (budget : ℝ)
variable (inverse left right : IdealTest K) (geometry : SlotGeometry K)
variable (index : Fin geometry.slotCount → Fin parent.geometry.slotCount)

local notation "moving" => prefix.append (secondOriginalMovingFactors P R C p m n pattern)
local notation "rest" => (remaining * exteriorMomentIdeal firstCommon) *
  exteriorMomentIdeal (secondSixthRootIdeal p m n)
local notation "child" => CanonicalMovingPhaseCalibration.childData P R parent prefix correction
  hcorr C p m n pattern sector (remaining * exteriorMomentIdeal firstCommon) budget
  inverse left right geometry index

/-- The two common-prime exclusions are read from the same complete
child mask. No separate support certificate is supplied. -/
include hp hm hn in
theorem child_common_parts (secondRight : Bool) (u I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hmask : child.commonMask u I.val = true) :
    IsCoprime I.val A.cS ∧
      supportExtract I.val (primeSupport firstCommon.val) = 1 ∧
      supportExtract I.val
        (primeSupport (primePowerProduct p (if secondRight then n else m)).val) = 1 := by
  have h := (child_commonMask_iff parent moving correction hcorr (fun _ => sector) rest budget
    inverse left right geometry index u I).mp hmask
  have hout := (CanonicalOriginalPhaseCalibration.outside_iff_coprime I).mp h.1
  have hrest : IsCoprime I.val
      ((remaining.val * firstCommon.val) * (secondSixthRootIdeal p m n).val) := h.2.2.2
  have hfirst : IsCoprime I.val firstCommon.val :=
    (IsCoprime.mul_right_iff.mp (IsCoprime.mul_right_iff.mp hrest).1).2
  have hfull : IsCoprime I.val (moving.support.val * rest.val) :=
    h.2.2.1.mul_right h.2.2.2
  have hsecond := supportExtract_eq_one_of_coprime I.val (moving.support.val * rest.val)
    (nonZeroDivisors.coe_ne_zero I)
    (mul_ne_zero moving.support.property.1 (nonZeroDivisors.coe_ne_zero rest))
    (primeSupport (primePowerProduct p m).val)
    (second_common_subset_full_mask prefix (remaining * exteriorMomentIdeal firstCommon)
      C p hp m n hm hn pattern) hfull
  refine ⟨hout, supportExtract_eq_one_of_coprime I.val firstCommon.val
    (nonZeroDivisors.coe_ne_zero I) firstCommon.property.1
    (primeSupport firstCommon.val) (Finset.Subset.refl _) hfirst, ?_⟩
  cases secondRight with
  | false => exact hsecond
  | true =>
    change supportExtract I.val (primeSupport (primePowerProduct p n).val) = 1
    rw [← positive_common_support_eq p hp m n hm hn]
    exact hsecond

end ActualMasks

section OriginalProfileSupport

private theorem extract_dvd_any (I : Ideal (𝓞 K)) (P : Finset (Ideal (𝓞 K))) :
    supportExtract I P ∣ I := by
  by_cases hI : I = 0
  · rw [hI]
    exact dvd_zero _
  · exact extract_dvd I hI P

private theorem residual_dvd_any (I : Ideal (𝓞 K)) (P : Finset (Ideal (𝓞 K))) :
    supportResidual I P ∣ I := by
  by_cases hI : I = 0
  · rw [hI]
    exact dvd_zero _
  · exact residual_dvd I hI P

theorem plainResidual_coprime_of_original
    (S P : Finset (Ideal (𝓞 K))) (D M I : Ideal (𝓞 K))
    (hS : ∀ J ∈ S, IsCoprime J M)
    (hI : I ∈ SupportCartesian.plainResidual S P D) : IsCoprime I M := by
  obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
  exact (hS J (Finset.mem_filter.mp hJ).1).of_isCoprime_of_dvd_left
    (residual_dvd_any J P)

private theorem reconstructed_coprime
    (S P Q : Finset (Ideal (𝓞 K))) (M : Ideal (𝓞 K))
    (D₁ D₂ E I : HeckeGeneral.Analysis.NonzeroIdeal K) (W₁ W₂ W₃ : Ideal (𝓞 K))
    (hS : ∀ J ∈ S, IsCoprime J M)
    (hW₁ : W₁ ∈ SupportCartesian.plainFibre S P D₁.val)
    (hW₂ : W₂ ∈ SupportCartesian.plainFibre
      (SupportCartesian.plainResidual S P D₁.val) Q D₂.val)
    (hW₃ : W₃ ∈ SupportCartesian.plainResidual
      (SupportCartesian.plainResidual S P D₁.val) Q D₂.val)
    (hE : E.val ∣ W₃) (hI : IsCoprime I.val M) :
    IsCoprime (D₁ * (D₂ * (E * I))).val M := by
  have hD₁ : IsCoprime D₁.val M :=
    (hS W₁ (Finset.mem_filter.mp hW₁).1).of_isCoprime_of_dvd_left
      ((Finset.mem_filter.mp hW₁).2 ▸ extract_dvd_any W₁ P)
  have hT : ∀ J ∈ SupportCartesian.plainResidual S P D₁.val, IsCoprime J M :=
    fun J hJ => plainResidual_coprime_of_original S P D₁.val M J hS hJ
  have hD₂ : IsCoprime D₂.val M :=
    (hT W₂ (Finset.mem_filter.mp hW₂).1).of_isCoprime_of_dvd_left
      ((Finset.mem_filter.mp hW₂).2 ▸ extract_dvd_any W₂ Q)
  have hEcop := (plainResidual_coprime_of_original
    (SupportCartesian.plainResidual S P D₁.val) Q D₂.val M W₃ hT hW₃).
      of_isCoprime_of_dvd_left hE
  exact hD₁.mul_left (hD₂.mul_left (hEcop.mul_left hI))

/-- Three divisions of the original physical scale reconstruct the
same original ideal, with the full extracted and allocated powers. -/
theorem original_profile_reconstruct (W : IdealTest K) (anchor D₁ D₂ E I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (N height : ℝ)
    (hI : I ∈ W.support anchor height
      (((N / idealNorm K D₁) / idealNorm K D₂) / idealNorm K E)) :
    D₁ * (D₂ * (E * I)) ∈ W.support anchor height N := by
  have h := (W.support_spec anchor height _ I).mp hI
  rw [quotient_norm_ratio E I ((N / idealNorm K D₁) / idealNorm K D₂),
    quotient_norm_ratio D₂ (E * I) (N / idealNorm K D₁),
    quotient_norm_ratio D₁ (D₂ * (E * I)) N] at h
  exact (W.support_spec anchor height N (D₁ * (D₂ * (E * I)))).mpr h

variable {A : SArithmeticData K}

/-- The original exterior carrier supplies its own coprimality facts. -/
theorem exteriorPlainSupport_coprime (W : IdealTest K) (anchor : HeckeGeneral.Analysis.NonzeroIdeal K)
    (N height : ℝ) (I : Ideal (𝓞 K))
    (hI : I ∈ exteriorPlainSupport (A := A) W anchor N height) : IsCoprime I A.cS := by
  obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
  exact (Finset.mem_filter.mp hJ).2

/-- In particular, the shared original main/comparison carrier is
exterior without any assumption about which comparison is nonzero. -/
theorem exteriorPlainSupport_union_coprime (W₁ W₂ : IdealTest K)
    (anchor : HeckeGeneral.Analysis.NonzeroIdeal K) (N₁ N₂ height : ℝ) (I : Ideal (𝓞 K))
    (hI : I ∈ exteriorPlainSupport (A := A) W₁ anchor N₁ height ∪
      exteriorPlainSupport (A := A) W₂ anchor N₂ height) : IsCoprime I A.cS := by
  rcases Finset.mem_union.mp hI with hI | hI
  · exact exteriorPlainSupport_coprime W₁ anchor N₁ height I hI
  · exact exteriorPlainSupport_coprime W₂ anchor N₂ height I hI

/-- This version starts with the original profile support itself.
Exterior coprimality of every extracted divisor follows from the
original branch witnesses, rather than a new exterior-carrier bound. -/
theorem mem_twice_allocated_of_profile
    (W : IdealTest K) (anchor : HeckeGeneral.Analysis.NonzeroIdeal K) (N height : ℝ)
    (P Q : Finset (Ideal (𝓞 K))) (D₁ D₂ E I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (W₁ W₂ W₃ : Ideal (𝓞 K))
    (hW₁ : W₁ ∈ SupportCartesian.plainFibre
      (exteriorPlainSupport (A := A) W anchor N height) P D₁.val)
    (hW₂ : W₂ ∈ SupportCartesian.plainFibre
      (SupportCartesian.plainResidual (exteriorPlainSupport (A := A) W anchor N height)
        P D₁.val) Q D₂.val)
    (hW₃ : W₃ ∈ SupportCartesian.plainResidual
      (SupportCartesian.plainResidual (exteriorPlainSupport (A := A) W anchor N height)
        P D₁.val) Q D₂.val)
    (hE : E.val ∣ W₃) (hout : IsCoprime I.val A.cS)
    (hI₁ : supportExtract I.val P = 1) (hI₂ : supportExtract I.val Q = 1)
    (hprofile : I ∈ W.support anchor height
      (((N / idealNorm K D₁) / idealNorm K D₂) / idealNorm K E)) :
    I ∈ nonzeroQuotientMomentSupport E.val
      (SupportCartesian.plainResidual
        (SupportCartesian.plainResidual (exteriorPlainSupport (A := A) W anchor N height)
          P D₁.val) Q D₂.val) := by
  apply mem_twice_allocated_of_original _ P Q D₁ D₂ E I W₁ W₂ W₃
    hW₁ hW₂ hW₃ hE hI₁ hI₂
  apply (mem_exteriorPlainSupport W anchor (D₁ * (D₂ * (E * I))) N height).mpr
  refine ⟨original_profile_reconstruct W anchor D₁ D₂ E I N height hprofile, ?_⟩
  apply reconstructed_coprime _ P Q A.cS D₁ D₂ E I W₁ W₂ W₃ _
    hW₁ hW₂ hW₃ hE hout
  exact exteriorPlainSupport_coprime W anchor N height

/-- The same proof on a shared original carrier, such as the union of
the main and comparison supports. Its witnesses need not belong to the
particular comparison profile under consideration. -/
theorem mem_twice_allocated_of_carrier
    (W : IdealTest K) (anchor : HeckeGeneral.Analysis.NonzeroIdeal K) (N height : ℝ)
    (S P Q : Finset (Ideal (𝓞 K))) (D₁ D₂ E I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (W₁ W₂ W₃ : Ideal (𝓞 K))
    (hS : exteriorPlainSupport (A := A) W anchor N height ⊆ S)
    (hExterior : ∀ J ∈ S, IsCoprime J A.cS)
    (hW₁ : W₁ ∈ SupportCartesian.plainFibre S P D₁.val)
    (hW₂ : W₂ ∈ SupportCartesian.plainFibre
      (SupportCartesian.plainResidual S P D₁.val) Q D₂.val)
    (hW₃ : W₃ ∈ SupportCartesian.plainResidual
      (SupportCartesian.plainResidual S P D₁.val) Q D₂.val)
    (hE : E.val ∣ W₃) (hout : IsCoprime I.val A.cS)
    (hI₁ : supportExtract I.val P = 1) (hI₂ : supportExtract I.val Q = 1)
    (hprofile : I ∈ W.support anchor height
      (((N / idealNorm K D₁) / idealNorm K D₂) / idealNorm K E)) :
    I ∈ nonzeroQuotientMomentSupport E.val
      (SupportCartesian.plainResidual (SupportCartesian.plainResidual S P D₁.val) Q D₂.val) := by
  apply mem_twice_allocated_of_original S P Q D₁ D₂ E I W₁ W₂ W₃
    hW₁ hW₂ hW₃ hE hI₁ hI₂
  apply hS
  apply (mem_exteriorPlainSupport W anchor (D₁ * (D₂ * (E * I))) N height).mpr
  exact ⟨original_profile_reconstruct W anchor D₁ D₂ E I N height hprofile,
    reconstructed_coprime S P Q A.cS D₁ D₂ E I W₁ W₂ W₃ hExterior
      hW₁ hW₂ hW₃ hE hout⟩

end OriginalProfileSupport

section BoundedData

variable {A : SArithmeticData K} {σ : K →+* ℂ} {ω ψ : HeckeCharacter K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable (parent : MomentData K ω ψ) (prefix : OriginalMovingFactors A P R)
variable (correction : HeckeCharacter K) (hcorr : correction = 1 ∨ correction ∈ parent.theta)
variable (C : A.GeneralArithmeticContext σ η hS) (primes : ι → ExteriorPrime A)
variable (m n : ι → ℕ) (pattern : ι → Bool)
variable (sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) (firstCommon : A.Exterior) (budget : ℝ)
variable (anchor : HeckeGeneral.Analysis.NonzeroIdeal K) (height : ℝ) {k : ℕ}
variable (index : Fin k → Fin parent.geometry.slotCount)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain window : Set ℝ}
variable {orders : Finset (ℕ × ℕ)} {P₀ : ℝ}
variable (raw : RawProfileWindow rowDomain heightDomain window orders parent P₀)
variable (hanchor : anchor ∈ rowDomain) (hheight : height ∈ heightDomain)
variable (hpositive : window ⊆ Set.Ioi 0)
variable (G₁ G₂ : ℝ) (G : Fin k → ℝ) (D₁ D₂ : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (annulus δ₁ δ₂ : ℝ) (hG₁ : 0 < G₁) (hG₂ : 0 < G₂)
variable (hG : ∀ i, 0 < G i) (hAnnulus : 1 ≤ annulus)
variable (firstDirection secondDirection : V)

local notation "bounded" => CanonicalBoundedChildData.boundedData parent prefix correction hcorr
  C primes m n pattern sector (remaining * exteriorMomentIdeal firstCommon) budget
  anchor height index raw hanchor hheight hpositive G₁ G₂ G D₁ D₂ annulus δ₁ δ₂
  hG₁ hG₂ hG hAnnulus firstDirection secondDirection

/-- The bounded scalar and signed multiplier preserve the literal
original finite supports, for every residual row and evaluation time. -/
@[simp] theorem left_support (ξ : V) (u : HeckeGeneral.Analysis.NonzeroIdeal K) (N t : ℝ) :
    (bounded ξ).plainTest₁.support u t N = parent.plainTest₁.support anchor height N := rfl

@[simp] theorem right_support (ξ : V) (u : HeckeGeneral.Analysis.NonzeroIdeal K) (N t : ℝ) :
    (bounded ξ).plainTest₂.support u t N = parent.plainTest₂.support anchor height N := rfl

@[simp] theorem prime_support (ξ : V) (i : Fin k) (N t : ℝ) :
    ((bounded ξ).geometry.slots i).support t N =
      (parent.geometry.slots (index i)).support height N := rfl

variable (hp : Function.Injective primes) (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i)
variable (secondRight : Bool)
local notation "common₁" => primeSupport firstCommon.val
local notation "common₂" => primeSupport
  (primePowerProduct primes (if secondRight then n else m)).val

include hp hm hn in
theorem bounded_mask_parts (ξ : V) (u I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hmask : (bounded ξ).commonMask u I.val = true) :
    IsCoprime I.val A.cS ∧
      supportExtract I.val common₁ = 1 ∧ supportExtract I.val common₂ = 1 :=
  child_common_parts parent prefix correction hcorr C primes hp m n hm hn pattern sector
    remaining firstCommon budget (bounded ξ).inverseTest (bounded ξ).plainTest₁
    (bounded ξ).plainTest₂ (bounded ξ).geometry index secondRight u I hmask

variable {S₁ S₂ : Finset (Ideal (𝓞 K))}
variable {S : Fin parent.geometry.slotCount → Finset (HeightOneSpectrum (𝓞 K))}
variable (b₁ : SupportCartesianBranch S₁ S₂ S common₁)
local notation "T₁" => SupportCartesian.plainResidual S₁ common₁ b₁.plainExtract₁
local notation "T₂" => SupportCartesian.plainResidual S₂ common₁ b₁.plainExtract₂
local notation "T" => fun j => SupportCartesian.primeLive
  (S (SlotRestriction.index b₁.keep j)) common₁
variable (b₂ : SupportCartesianBranch T₁ T₂ T common₂)
local notation "U₁" => SupportCartesian.plainResidual T₁ common₂ b₂.plainExtract₁
local notation "U₂" => SupportCartesian.plainResidual T₂ common₂ b₂.plainExtract₂
local notation "U" => fun j => SupportCartesian.primeLive
  (T (SlotRestriction.index b₂.keep j)) common₂
variable (B : ActualColumnAllocation K b₂.keep.card)

/-- The true bounded left profile is supported on the actual allocated
child carrier. The original carrier may include both comparisons;
all effective-support and extraction facts are outputs. -/
include hp hm hn in
theorem effective_left_support (N : ℝ)
    (hS₁ : exteriorPlainSupport (A := A) parent.plainTest₁ anchor N height ⊆ S₁)
    (hExterior : ∀ J ∈ S₁, IsCoprime J A.cS)
    (hB : B.plain₁ = U₁) (ξ : V) (u : HeckeGeneral.Analysis.NonzeroIdeal K) (t : ℝ) :
    effectivePlainSupport (bounded ξ) (bounded ξ).plainTest₁ u
        (((N / idealNorm K b₁.plainDivisor₁) / idealNorm K b₂.plainDivisor₁) /
          idealNorm K (B.plainDivisor 0)) t ⊆ B.childPlain₁ := by
  intro I hI
  have hparts := bounded_mask_parts parent prefix correction hcorr C primes m n pattern sector
    remaining firstCommon budget anchor height index raw hanchor hheight hpositive
    G₁ G₂ G D₁ D₂ annulus δ₁ δ₂ hG₁ hG₂ hG hAnnulus firstDirection secondDirection
    hp hm hn secondRight ξ u I (effectivePlainSupport_commonMask _ _ _ _ _ _ hI)
  have hprofile := effectivePlainSupport_subset_profile _ _ _ _ _ hI
  change I ∈ parent.plainTest₁.support anchor height
    (((N / idealNorm K b₁.plainDivisor₁) / idealNorm K b₂.plainDivisor₁) /
      idealNorm K (B.plainDivisor 0)) at hprofile
  have hw := Finset.mem_filter.mp
    (Finset.mem_product.mp (Finset.mem_product.mp B.witness_mem).1).1
  change B.witness.1.1 ∈ B.plain₁ ∧ (B.plainDivisor 0).val ∣ B.witness.1.1 at hw
  have hmem := mem_twice_allocated_of_carrier (A := A) parent.plainTest₁ anchor N height
    S₁ common₁ common₂ b₁.plainDivisor₁ b₂.plainDivisor₁ (B.plainDivisor 0) I
    b₁.witness.1.1 b₂.witness.1.1 B.witness.1.1
    hS₁ hExterior
    (Finset.mem_product.mp (Finset.mem_product.mp b₁.witness_mem).1).1
    (Finset.mem_product.mp (Finset.mem_product.mp b₂.witness_mem).1).1
    (hB ▸ hw.1)
    hw.2 hparts.1 hparts.2.1 hparts.2.2 hprofile
  change I ∈ nonzeroQuotientMomentSupport (B.plainDivisor 0).val B.plain₁
  simpa only [hB] using hmem

include hp hm hn in
theorem effective_right_support (N : ℝ)
    (hS₂ : exteriorPlainSupport (A := A) parent.plainTest₂ anchor N height ⊆ S₂)
    (hExterior : ∀ J ∈ S₂, IsCoprime J A.cS)
    (hB : B.plain₂ = U₂) (ξ : V) (u : HeckeGeneral.Analysis.NonzeroIdeal K) (t : ℝ) :
    effectivePlainSupport (bounded ξ) (bounded ξ).plainTest₂ u
        (((N / idealNorm K b₁.plainDivisor₂) / idealNorm K b₂.plainDivisor₂) /
          idealNorm K (B.plainDivisor (Fin.succ 0))) t ⊆ B.childPlain₂ := by
  intro I hI
  have hparts := bounded_mask_parts parent prefix correction hcorr C primes m n pattern sector
    remaining firstCommon budget anchor height index raw hanchor hheight hpositive
    G₁ G₂ G D₁ D₂ annulus δ₁ δ₂ hG₁ hG₂ hG hAnnulus firstDirection secondDirection
    hp hm hn secondRight ξ u I (effectivePlainSupport_commonMask _ _ _ _ _ _ hI)
  have hprofile := effectivePlainSupport_subset_profile _ _ _ _ _ hI
  change I ∈ parent.plainTest₂.support anchor height
    (((N / idealNorm K b₁.plainDivisor₂) / idealNorm K b₂.plainDivisor₂) /
      idealNorm K (B.plainDivisor (Fin.succ 0))) at hprofile
  have hw := Finset.mem_filter.mp
    (Finset.mem_product.mp (Finset.mem_product.mp B.witness_mem).1).2
  change B.witness.1.2 ∈ B.plain₂ ∧
    (B.plainDivisor (Fin.succ 0)).val ∣ B.witness.1.2 at hw
  have hmem := mem_twice_allocated_of_carrier (A := A) parent.plainTest₂ anchor N height
    S₂ common₁ common₂ b₁.plainDivisor₂ b₂.plainDivisor₂ (B.plainDivisor (Fin.succ 0)) I
    b₁.witness.1.2 b₂.witness.1.2 B.witness.1.2
    hS₂ hExterior
    (Finset.mem_product.mp (Finset.mem_product.mp b₁.witness_mem).1).2
    (Finset.mem_product.mp (Finset.mem_product.mp b₂.witness_mem).1).2
    (hB ▸ hw.1)
    hw.2 hparts.1 hparts.2.1 hparts.2.2 hprofile
  change I ∈ nonzeroQuotientMomentSupport (B.plainDivisor (Fin.succ 0)).val B.plain₂
  simpa only [hB] using hmem

/-- The same literal three-stage slot index gives the live child
support. The whole arithmetic mask excludes both deleted prime sets. -/
include hp hm hn in
theorem effective_prime_support (Z : ℝ)
    (hSlots : ∀ i, exteriorPrimeSupport (A := A) (parent.geometry.slots i) Z height ⊆ S i)
    (hB : B.slots = U) (i : Fin k) (j : Fin B.keep.card)
    (hindex : index i = SlotRestriction.index b₁.keep
      (SlotRestriction.index b₂.keep (SlotRestriction.index B.keep j)))
    (ξ : V) (u : HeckeGeneral.Analysis.NonzeroIdeal K) (t : ℝ) :
    effectivePrimeSupport (bounded ξ) i u Z t ⊆ B.childSlots j := by
  intro p hmem
  let I := CanonicalOriginalPhaseCalibration.primeIdeal p
  have hparts := bounded_mask_parts parent prefix correction hcorr C primes m n pattern sector
    remaining firstCommon budget anchor height index raw hanchor hheight hpositive
    G₁ G₂ G D₁ D₂ annulus δ₁ δ₂ hG₁ hG₂ hG hAnnulus firstDirection secondDirection
    hp hm hn secondRight ξ u I (effectivePrimeSupport_commonMask _ i u Z t p hmem)
  have hprofile := effectivePrimeSupport_subset_profile _ i u Z t hmem
  change p ∈ (parent.geometry.slots (index i)).support height
    (Z ^ (parent.geometry.slots (index i)).length) at hprofile
  have horiginal : p ∈ exteriorPrimeSupport (A := A)
      (parent.geometry.slots (index i)) Z height :=
    Finset.mem_filter.mpr ⟨hprofile, hparts.1⟩
  apply prime_mem_child_of_original b₁ b₂ B hB j p
  · simpa only [hindex] using hSlots (index i) horiginal
  · exact (SupportCartesian.prime_extract_eq_one p common₁).mp hparts.2.1
  · exact (SupportCartesian.prime_extract_eq_one p common₂).mp hparts.2.2

end BoundedData

end HeckeSkeleton.Moments.EngineStep.CanonicalBoundedChildSupport

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalBoundedChildSupport.mem_twice_allocated_of_original
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalBoundedChildSupport.left_mem_child_of_original
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalBoundedChildSupport.right_mem_child_of_original
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalBoundedChildSupport.prime_mem_child_of_original
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalBoundedChildSupport.child_common_parts
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalBoundedChildSupport.mem_twice_allocated_of_profile
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalBoundedChildSupport.mem_twice_allocated_of_carrier
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalBoundedChildSupport.effective_left_support
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalBoundedChildSupport.effective_right_support
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalBoundedChildSupport.effective_prime_support
