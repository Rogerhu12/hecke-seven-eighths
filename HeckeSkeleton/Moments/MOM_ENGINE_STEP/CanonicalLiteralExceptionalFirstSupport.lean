import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPaidSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveLabelMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCommonLabelConditions

/-!
# The original first deletion in the complete exceptional mask

The exceptional source keeps its original first deletion, including
primes whose phase is a sixth power.  Those primes need not belong to
the active first radical.  Their actual norm is bounded from the
original common-label witness and the original column window.

The pool case also keeps the original exponent `2 * n`.  Its displayed
support costs at most one copy of the actual pool prime, independently
of the exponent.  A second copy pays the original union deletion.
These costs enlarge only the fixed box used by the single-character
volume estimate; they do not change any child parameter or row count.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open UniqueFactorizationMonoid HeckePort.IdealMobiusDivisorSum CommonSupportMass
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical (ProbeData RowCharacterInput)
open HeckePort.Moments HeckePort.Moments.Support
open CanonicalLiteralPhaseCalibration CanonicalLiteralActualCharacters

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}

private theorem exceptional_primeSupport_mul (I J : Ideal (𝓞 K))
    (hI : I ≠ 0) (hJ : J ≠ 0) :
    primeSupport (I * J) = primeSupport I ∪ primeSupport J := by
  simp only [primeSupport, normalizedFactors_mul hI hJ, Multiset.toFinset_add]

namespace OriginalMovingFactors

/-- The full old support remains present when the original deletion
is multiplied into the remaining ideal.  Overlap needs no assumption. -/
theorem effectiveFullSupport_mul_dvd (D : OriginalMovingFactors A P R)
    (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (D.effectiveFullSupport (remaining * extra)).val ∣
      (D.effectiveFullSupport remaining).val * extra.val := by
  rw [← squarefree_support_product_self
    (D.effectiveFullSupport_squarefree (remaining * extra))]
  apply support_product_dvd
    (mul_ne_zero (D.effectiveFullSupport remaining).property.1
      (nonZeroDivisors.coe_ne_zero extra))
  intro p hp
  rw [D.effectiveFullSupport_primes,
    show (remaining * extra).val = remaining.val * extra.val from rfl,
    exceptional_primeSupport_mul _ _ (nonZeroDivisors.coe_ne_zero remaining)
      (nonZeroDivisors.coe_ne_zero extra)] at hp
  rw [exceptional_primeSupport_mul _ _ (D.effectiveFullSupport remaining).property.1
    (nonZeroDivisors.coe_ne_zero extra), D.effectiveFullSupport_primes]
  simp only [Finset.mem_union, Finset.mem_sdiff] at hp ⊢
  tauto

theorem effectiveFullSupport_mul_norm_le (D : OriginalMovingFactors A P R)
    (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K) :
    A.exteriorNorm (D.effectiveFullSupport (remaining * extra)) ≤
      A.exteriorNorm (D.effectiveFullSupport remaining) * idealNorm K extra := by
  have h := HeckePort.Moments.norm_le_of_dvd
    (mul_ne_zero (D.effectiveFullSupport remaining).property.1
      (nonZeroDivisors.coe_ne_zero extra))
    (D.effectiveFullSupport_mul_dvd remaining extra)
  simpa only [map_mul, Nat.cast_mul] using h

end OriginalMovingFactors

namespace CanonicalLiteralExceptionalFirstSupport

open CanonicalLiteralPassiveLabelMass

variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)

/-- A genuine common label supplies its original column witness. -/
theorem firstMask_window {α β : Type*}
    (left : Finset α) (right : Finset β)
    (I : α → A.Exterior) (J : β → A.Exterior)
    (DE : Ideal (𝓞 K) × Ideal (𝓞 K))
    (hDE : DE ∈ commonSupportPool left right (fun i => (I i).val) (fun j => (J j).val))
    (Y : ℝ) (hI : ∀ i ∈ left, A.exteriorNorm (I i) ≤ Y) :
    idealNorm K (firstMask DE.1) ≤ Y := by
  obtain ⟨ij, hij, he⟩ := Finset.mem_image.mp hDE
  have hi := (Finset.mem_product.mp hij).1
  have hnorm := (actual_common_label_norm_le (I ij.1).val (J ij.2).val
    (I ij.1).property.1 (J ij.2).property.1).1
  have hnonzero := (actual_common_label_nonzero (I ij.1).val (J ij.2).val).1
  rw [he] at hnorm hnonzero
  exact (HeckePort.Moments.norm_le_of_dvd hnonzero
    (firstMask_dvd DE.1 hnonzero)).trans (hnorm.trans (hI ij.1 hi))

theorem poolExtra_norm_le (D : Ideal (𝓞 K)) (p : ExteriorPrime A) :
    idealNorm K (poolExtra D p) ≤
      idealNorm K (firstMask D) * (Ideal.absNorm p.val.asIdeal : ℝ) := by
  have h := HeckePort.Moments.norm_le_of_dvd
    (mul_ne_zero (nonZeroDivisors.coe_ne_zero (firstMask D)) p.val.ne_bot)
    (poolExtra_dvd D p)
  simpa only [map_mul, Nat.cast_mul] using h

variable [IsPrincipalIdealRing A.R]
variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {hS : A.ContainsTraceBadPlaces}
variable (C : A.GeneralArithmeticContext σ η hS)

/-- This bounds the literal displayed support of the original
amplifier generator, including exponent twelve. -/
theorem amplified_pool_support_dvd (first : A.Exterior) (a : A.R)
    (ha : A.Generates first a) (p : ExteriorPrime A) (n : ℕ) :
    ((amplifiedPhases C first a ha p n).poolMoving P R).support.val ∣ p.val.asIdeal := by
  change (OriginalMovingFactors.singleton (P := P) (R := R)
    ⟨generator C p ^ (2 * n), (generator_power_generates C p (2 * n)).1⟩ 1).support.val ∣ _
  rw [OriginalMovingFactors.singleton_support _ _
    (generator_power_generates C p (2 * n)) 1]
  unfold commonRadical
  rw [Finset.inter_self]
  apply support_product_dvd p.val.ne_bot
  intro v hv
  have hp := support_prime hv
  have hd := (prime_mem_support_iff_dvd v _ hp (powerIdeal p (2 * n)).property.1).mp hv
  change v ∣ p.val.asIdeal ^ (2 * n) at hd
  exact (prime_mem_support_iff_dvd v _ hp p.val.ne_bot).mpr (hp.dvd_of_dvd_pow hd)

theorem amplified_pool_norm_le (first : A.Exterior) (a : A.R)
    (ha : A.Generates first a) (p : ExteriorPrime A) (n : ℕ) :
    A.exteriorNorm ((amplifiedPhases C first a ha p n).poolMoving P R).support ≤
      (Ideal.absNorm p.val.asIdeal : ℝ) :=
  HeckePort.Moments.norm_le_of_dvd p.val.ne_bot
    (amplified_pool_support_dvd P R C first a ha p n)

private theorem amplified_unit_norm (first : A.Exterior) (a : A.R)
    (ha : A.Generates first a) (p : ExteriorPrime A) (n : ℕ) :
    A.exteriorNorm ((amplifiedPhases C first a ha p n).unitMoving P R).support = 1 := by
  change (Ideal.absNorm (CanonicalLiteralFixedPhases.emptyDivisorMoving P R).support.val : ℝ) = 1
  rw [CanonicalLiteralFixedPhases.emptyDivisorMoving_support P R, map_one, Nat.cast_one]

section ActualBlocks

variable {α β : Type*} {I : α → A.Exterior} {J : β → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable (b : FirstCommonCharacterBlock I J DE)
variable (D : Finset (HeightOneSpectrum A.R))
variable (old : OriginalMovingFactors A P R)
variable (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (left : Finset α) (right : Finset β)
variable (hDE : DE ∈ commonSupportPool left right (fun i => (I i).val) (fun j => (J j).val))
variable (Z q columnBound : ℝ) (hZ : 1 < Z)
variable (hcolumns : ∀ i ∈ left, A.exteriorNorm (I i) ≤ Z ^ columnBound)
variable (hold : A.exteriorNorm (old.effectiveFullSupport remaining) ≤ Z ^ q)

local notation "firstCost" => idealLogLength Z (firstActiveRadical DE.1 DE.2) +
  idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D).val
local notation "leftElement" => CanonicalLiteralFirstPhase.leftElement C b.primes
  b.leftMultiplicity b.rightMultiplicity
  (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val
local notation "rightElement" => CanonicalLiteralFirstPhase.rightElement C b.primes
  b.leftMultiplicity b.rightMultiplicity
  (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val

include hDE hcolumns hold hZ in
private theorem old_firstMask_window :
    A.exteriorNorm (old.effectiveFullSupport (remaining * firstMask DE.1)) ≤
      Z ^ (q + columnBound) := by
  have hm := firstMask_window left right I J DE hDE _ hcolumns
  apply (old.effectiveFullSupport_mul_norm_le remaining (firstMask DE.1)).trans
  rw [Real.rpow_add (zero_lt_one.trans hZ)]
  exact mul_le_mul hold hm (by positivity) (by positivity)

include hDE hcolumns hold hZ in
/-- Direct and main retain their full first deletion.  Its cost is
the actual original column window, separate from the active radical. -/
theorem unamplified_left (first : A.Exterior)
    (hfirst : A.Generates first leftElement) :
    A.exteriorNorm (((unamplifiedPhases first leftElement hfirst).moving P R old)
      .effectiveFullSupport (remaining * firstMask DE.1)) ≤
      Z ^ ((q + firstCost) + columnBound) := by
  have hm := old_firstMask_window P R old remaining left right hDE Z q columnBound hZ hcolumns hold
  have h := CanonicalLiteralPaidSupport.unamplified_left P R C b D old
    (remaining * firstMask DE.1) first hfirst Z (q + columnBound) hZ hm
  have he : (q + columnBound) + idealLogLength Z (firstActiveRadical DE.1 DE.2) +
      idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D).val =
        (q + firstCost) + columnBound := by ring
  simpa only [he] using h

include hDE hcolumns hold hZ in
theorem unamplified_right (first : A.Exterior)
    (hfirst : A.Generates first rightElement) :
    A.exteriorNorm (((unamplifiedPhases first rightElement hfirst).moving P R old)
      .effectiveFullSupport (remaining * firstMask DE.1)) ≤
      Z ^ ((q + firstCost) + columnBound) := by
  have hm := old_firstMask_window P R old remaining left right hDE Z q columnBound hZ hcolumns hold
  have h := CanonicalLiteralPaidSupport.unamplified_right P R C b D old
    (remaining * firstMask DE.1) first hfirst Z (q + columnBound) hZ hm
  have he : (q + columnBound) + idealLogLength Z (firstActiveRadical DE.1 DE.2) +
      idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D).val =
        (q + firstCost) + columnBound := by ring
  simpa only [he] using h

include hDE hcolumns hold hZ in
private theorem amplified_window (first : A.Exterior) (a : A.R)
    (ha : A.Generates first a) (p : ExteriorPrime A) (n : ℕ) (ell : ℝ)
    (hp : (Ideal.absNorm p.val.asIdeal : ℝ) ≤ Z ^ ell)
    (hfirst : A.exteriorNorm
      (OriginalMovingFactors.singleton (P := P) (R := R) ⟨a, ha.1⟩ 1).support ≤ Z ^ firstCost) :
    A.exteriorNorm (((amplifiedPhases C first a ha p n).moving P R old)
      .effectiveFullSupport (remaining * poolExtra DE.1 p)) ≤
      Z ^ ((q + firstCost) + (columnBound + 2 * ell)) := by
  have hm : idealNorm K (poolExtra DE.1 p) ≤ Z ^ (columnBound + ell) := by
    apply (poolExtra_norm_le DE.1 p).trans
    rw [Real.rpow_add (zero_lt_one.trans hZ)]
    exact mul_le_mul (firstMask_window left right I J DE hDE _ hcolumns) hp
      (by positivity) (by positivity)
  have ho : A.exteriorNorm (old.effectiveFullSupport (remaining * poolExtra DE.1 p)) ≤
      Z ^ (q + columnBound + ell) := by
    apply (old.effectiveFullSupport_mul_norm_le remaining (poolExtra DE.1 p)).trans
    calc
      _ ≤ Z ^ q * Z ^ (columnBound + ell) :=
        mul_le_mul hold hm (by positivity) (by positivity)
      _ = _ := by rw [← Real.rpow_add (zero_lt_one.trans hZ)]; congr 1; ring
  have h := CanonicalLiteralPaidSupport.moving_norm_le P R
    (amplifiedPhases C first a ha p n) old (remaining * poolExtra DE.1 p)
  rw [amplified_unit_norm P R C first a ha p n, mul_one] at h
  apply h.trans
  calc
    _ ≤ (Z ^ (q + columnBound + ell) * Z ^ firstCost) * Z ^ ell :=
      mul_le_mul (mul_le_mul ho hfirst (by positivity) (by positivity))
        ((amplified_pool_norm_le P R C first a ha p n).trans hp)
        (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.rpow_add (zero_lt_one.trans hZ), ← Real.rpow_add (zero_lt_one.trans hZ)]
      congr 1
      ring

include hDE hcolumns hold hZ in
/-- All three literal amplifier valuations satisfy this same window.
The original twelfth-power support is charged, not erased. -/
theorem amplified_left (first : A.Exterior)
    (hfirst : A.Generates first leftElement) (p : ExteriorPrime A) (n : ℕ) (ell : ℝ)
    (hp : (Ideal.absNorm p.val.asIdeal : ℝ) ≤ Z ^ ell) :
    A.exteriorNorm (((amplifiedPhases C first leftElement hfirst p n).moving P R old)
      .effectiveFullSupport (remaining * poolExtra DE.1 p)) ≤
      Z ^ ((q + firstCost) + (columnBound + 2 * ell)) :=
  amplified_window P R C D old remaining left right hDE Z q columnBound hZ hcolumns hold
    first leftElement hfirst p n ell hp (CanonicalLiteralPaidSupport.left_first_window P R C b D Z hZ)

include hDE hcolumns hold hZ in
theorem amplified_right (first : A.Exterior)
    (hfirst : A.Generates first rightElement) (p : ExteriorPrime A) (n : ℕ) (ell : ℝ)
    (hp : (Ideal.absNorm p.val.asIdeal : ℝ) ≤ Z ^ ell) :
    A.exteriorNorm (((amplifiedPhases C first rightElement hfirst p n).moving P R old)
      .effectiveFullSupport (remaining * poolExtra DE.1 p)) ≤
      Z ^ ((q + firstCost) + (columnBound + 2 * ell)) :=
  amplified_window P R C D old remaining left right hDE Z q columnBound hZ hcolumns hold
    first rightElement hfirst p n ell hp (CanonicalLiteralPaidSupport.right_first_window P R C b D Z hZ)

end ActualBlocks
end CanonicalLiteralExceptionalFirstSupport
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.OriginalMovingFactors.effectiveFullSupport_mul_dvd
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalFirstSupport.firstMask_window
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalFirstSupport.unamplified_left
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalFirstSupport.unamplified_right
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalFirstSupport.amplified_left
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalFirstSupport.amplified_right
