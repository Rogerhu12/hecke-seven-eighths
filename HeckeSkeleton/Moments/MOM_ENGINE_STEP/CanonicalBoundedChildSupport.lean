import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalBoundedChildData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalEffectiveChildSupport

set_option linter.unusedSectionVars false
set_option quotPrecheck false

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
open DedekindZetaZeroFree.LocalFiniteSums (ExteriorPrime)
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
  sorry

private theorem residual_dvd (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (P : Finset (Ideal (𝓞 K))) : supportResidual I P ∣ I := by
  sorry

theorem plainResidual_ne_zero (S P : Finset (Ideal (𝓞 K))) (D I : Ideal (𝓞 K))
    (hI : I ∈ SupportCartesian.plainResidual S P D) : I ≠ 0 := by
  sorry

/-- Every actual divisor of a residual occurrence avoids its original
common-prime set. The divisor condition comes from the allocation. -/
theorem extract_one_of_dvd_plainResidual (S P : Finset (Ideal (𝓞 K)))
    (D I E : Ideal (𝓞 K)) (hE : E ≠ 0)
    (hI : I ∈ SupportCartesian.plainResidual S P D) (hd : E ∣ I) :
    supportExtract E P = 1 := by
  sorry

/-- A divisor of a twice-residual occurrence avoids both extracted
sets. This includes the literal allocated occurrence divisor. -/
theorem extract_one_of_dvd_twice_plainResidual
    (S P Q : Finset (Ideal (𝓞 K))) (D₁ D₂ I E : Ideal (𝓞 K)) (hE : E ≠ 0)
    (hI : I ∈ SupportCartesian.plainResidual
      (SupportCartesian.plainResidual S P D₁) Q D₂) (hd : E ∣ I) :
    supportExtract E P = 1 ∧ supportExtract E Q = 1 := by
  sorry

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
  sorry

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
  sorry

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
  sorry

theorem right_mem_child_of_original (hB : B.plain₂ = U₂) (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hI₁ : supportExtract I.val P = 1) (hI₂ : supportExtract I.val Q = 1)
    (hmem : (b₁.plainDivisor₂ *
      (b₂.plainDivisor₂ * (B.plainDivisor (Fin.succ 0) * I))).val ∈ S₂) :
    I ∈ B.childPlain₂ := by
  sorry

/-- A retained original prime occurrence avoids both common sets.
All three index maps are the actual successive slot restrictions. -/
theorem prime_mem_child_of_original (hB : B.slots = U)
    (j : Fin B.keep.card) (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∈ S (SlotRestriction.index b₁.keep
      (SlotRestriction.index b₂.keep (SlotRestriction.index B.keep j))))
    (hp₁ : p.asIdeal ∉ P) (hp₂ : p.asIdeal ∉ Q) : p ∈ B.childSlots j := by
  sorry

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
  sorry

variable (parent : MomentData K ω ψ) («prefix» : OriginalMovingFactors A P R)
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
local notation "child" => CanonicalMovingPhaseCalibration.childData P R parent «prefix» correction
  hcorr C p m n pattern sector (remaining * exteriorMomentIdeal firstCommon) budget
  inverse left right geometry index

include hp hm hn in
/-- The two common-prime exclusions are read from the same complete
child mask. No separate support certificate is supplied. -/
theorem child_common_parts (secondRight : Bool) (u I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hmask : (child).commonMask u I.val = true) :
    IsCoprime I.val A.cS ∧
      supportExtract I.val (primeSupport firstCommon.val) = 1 ∧
      supportExtract I.val
        (primeSupport (primePowerProduct p (if secondRight then n else m)).val) = 1 := by
  sorry

end ActualMasks

section OriginalProfileSupport

private theorem extract_dvd_any (I : Ideal (𝓞 K)) (P : Finset (Ideal (𝓞 K))) :
    supportExtract I P ∣ I := by
  sorry

private theorem residual_dvd_any (I : Ideal (𝓞 K)) (P : Finset (Ideal (𝓞 K))) :
    supportResidual I P ∣ I := by
  sorry

theorem plainResidual_coprime_of_original
    (S P : Finset (Ideal (𝓞 K))) (D M I : Ideal (𝓞 K))
    (hS : ∀ J ∈ S, IsCoprime J M)
    (hI : I ∈ SupportCartesian.plainResidual S P D) : IsCoprime I M := by
  sorry

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
  sorry

/-- Three divisions of the original physical scale reconstruct the
same original ideal, with the full extracted and allocated powers. -/
theorem original_profile_reconstruct (W : IdealTest K) (anchor D₁ D₂ E I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (N height : ℝ)
    (hI : I ∈ W.support anchor height
      (((N / idealNorm K D₁) / idealNorm K D₂) / idealNorm K E)) :
    D₁ * (D₂ * (E * I)) ∈ W.support anchor height N := by
  sorry

variable {A : SArithmeticData K}

/-- The original exterior carrier supplies its own coprimality facts. -/
theorem exteriorPlainSupport_coprime (W : IdealTest K) (anchor : HeckeGeneral.Analysis.NonzeroIdeal K)
    (N height : ℝ) (I : Ideal (𝓞 K))
    (hI : I ∈ exteriorPlainSupport (A := A) W anchor N height) : IsCoprime I A.cS := by
  sorry

/-- In particular, the shared original main/comparison carrier is
exterior without any assumption about which comparison is nonzero. -/
theorem exteriorPlainSupport_union_coprime (W₁ W₂ : IdealTest K)
    (anchor : HeckeGeneral.Analysis.NonzeroIdeal K) (N₁ N₂ height : ℝ) (I : Ideal (𝓞 K))
    (hI : I ∈ exteriorPlainSupport (A := A) W₁ anchor N₁ height ∪
      exteriorPlainSupport (A := A) W₂ anchor N₂ height) : IsCoprime I A.cS := by
  sorry

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
  sorry

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
  sorry

end OriginalProfileSupport

section BoundedData

variable {A : SArithmeticData K} {σ : K →+* ℂ} {ω ψ : HeckeCharacter K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable (parent : MomentData K ω ψ) («prefix» : OriginalMovingFactors A P R)
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

local notation "bounded" => CanonicalBoundedChildData.boundedData parent «prefix» correction hcorr
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
      supportExtract I.val common₁ = 1 ∧ supportExtract I.val common₂ = 1 := by
  sorry

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

include hp hm hn in
/-- The true bounded left profile is supported on the actual allocated
child carrier. The original carrier may include both comparisons;
all effective-support and extraction facts are outputs. -/
theorem effective_left_support (N : ℝ)
    (hS₁ : exteriorPlainSupport (A := A) parent.plainTest₁ anchor N height ⊆ S₁)
    (hExterior : ∀ J ∈ S₁, IsCoprime J A.cS)
    (hB : B.plain₁ = U₁) (ξ : V) (u : HeckeGeneral.Analysis.NonzeroIdeal K) (t : ℝ) :
    effectivePlainSupport (bounded ξ) (bounded ξ).plainTest₁ u
        (((N / idealNorm K b₁.plainDivisor₁) / idealNorm K b₂.plainDivisor₁) /
          idealNorm K (B.plainDivisor 0)) t ⊆ B.childPlain₁ := by
  sorry

include hp hm hn in
theorem effective_right_support (N : ℝ)
    (hS₂ : exteriorPlainSupport (A := A) parent.plainTest₂ anchor N height ⊆ S₂)
    (hExterior : ∀ J ∈ S₂, IsCoprime J A.cS)
    (hB : B.plain₂ = U₂) (ξ : V) (u : HeckeGeneral.Analysis.NonzeroIdeal K) (t : ℝ) :
    effectivePlainSupport (bounded ξ) (bounded ξ).plainTest₂ u
        (((N / idealNorm K b₁.plainDivisor₂) / idealNorm K b₂.plainDivisor₂) /
          idealNorm K (B.plainDivisor (Fin.succ 0))) t ⊆ B.childPlain₂ := by
  sorry

include hp hm hn in
/-- The same literal three-stage slot index gives the live child
support. The whole arithmetic mask excludes both deleted prime sets. -/
theorem effective_prime_support (Z : ℝ)
    (hSlots : ∀ i, exteriorPrimeSupport (A := A) (parent.geometry.slots i) Z height ⊆ S i)
    (hB : B.slots = U) (i : Fin k) (j : Fin B.keep.card)
    (hindex : index i = SlotRestriction.index b₁.keep
      (SlotRestriction.index b₂.keep (SlotRestriction.index B.keep j)))
    (ξ : V) (u : HeckeGeneral.Analysis.NonzeroIdeal K) (t : ℝ) :
    effectivePrimeSupport (bounded ξ) i u Z t ⊆ B.childSlots j := by
  sorry

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
