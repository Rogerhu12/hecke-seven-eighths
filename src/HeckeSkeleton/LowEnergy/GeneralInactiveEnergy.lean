import HeckeSkeleton.LowEnergy.GeneralAggregation
import HeckeSkeleton.LowEnergy.GeneralInactiveMass

/-!
# General inactive sums use their actual reciprocal-prime mass

The inactive prefactor is extracted from each genuine reflected row
before finite Minkowski.  The coefficient inside the resulting L1 mass
is the original outer coefficient times that exact prefactor.  Thus a
tuple with repeated primes is never assigned an extra reciprocal norm.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.GeneralInactiveEnergy

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckePort.CenteredMomentGenerator
open HeckeSkeleton.LowEnergy.ActualReflection
open HeckeSkeleton.LowEnergy.ActualReflectionReindex
open HeckeSkeleton.LowEnergy.ActualSeparatedBlock
open HeckeSkeleton.LowEnergy.ActualSieveDictionary
open HeckeSkeleton.LowEnergy.GeneralMarkedEnergy
open HeckeSkeleton.LowEnergy.GeneralAggregation
open scoped Classical BigOperators NumberField nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

theorem inactiveWeight_ne_zero (f : FixedData K S) : inactiveWeight K S f ≠ 0 := by
  unfold inactiveWeight
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  have hn : p.val.asIdeal.absNorm ≠ 0 :=
    (Ideal.absNorm_pos_of_nonZeroDivisors (exteriorPrimeIdeal K S p).val).ne'
  exact inv_ne_zero (Nat.cast_ne_zero.mpr hn)

/-- The outer finite sum remains a linear row vector.  Every energy
estimate inside this statement is proved from the original sieves and
kernel; the displayed inactive L1 mass is its literal finite sum. -/
theorem general_frozen_weighted_energy [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ : HeckeCharacter K) (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D)
    (W Fmax eps : ℝ) (hW : 0 ≤ W) (hFmax : 0 ≤ Fmax) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z A E : ℝ), 1 < Z → 0 < A →
      ∀ (V : SmoothAnnularTest) {ι : Type*} (I : Finset ι)
        (blocks : ι → FrozenBlock K S) (a : ι → ℂ) (rows : Finset (Ideal (𝓞 K))),
      (∀ i ∈ I, (blocks i).Admissible Z W A E Fmax) →
      (∀ i ∈ I, (blocks i).rows ⊆ rows) →
      (∑ k ∈ rows, ‖∑ i ∈ I, a i * (blocks i).restrictedRow D F θ V k‖ ^ 2) ≤
        C * A ^ 2 * testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
          (∑ i ∈ I, ‖a i * inactiveWeight K S (blocks i).fixed‖) ^ 2 * Z ^ (E + eps) := by
  obtain ⟨C, hC, hb⟩ := general_frozen_block_energy K S D F hF θ hKernel hθ hD
    hquadratic hcubic W Fmax eps hW hFmax heps
  refine ⟨C, hC, ?_⟩
  intro Z A E hZ hA V ι I blocks a rows hadm hrows
  let L := C * A ^ 2 * testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2
  let E0 := L * Z ^ (E + eps)
  let v := fun i k => (inactiveWeight K S (blocks i).fixed)⁻¹ *
    (blocks i).restrictedRow D F θ V k
  have hinner (i : ι) (hi : i ∈ I) : (∑ k ∈ rows, ‖v i k‖ ^ 2) ≤ E0 := by
    have hblock := hb Z A E hZ hA V (blocks i) (hadm i hi)
    have hcancel : ‖(inactiveWeight K S (blocks i).fixed)⁻¹‖ ^ 2 *
        ‖inactiveWeight K S (blocks i).fixed‖ ^ 2 = 1 := by
      rw [← mul_pow, ← norm_mul, inv_mul_cancel₀ (inactiveWeight_ne_zero K S _),
        norm_one, one_pow]
    calc
      _ = ‖(inactiveWeight K S (blocks i).fixed)⁻¹‖ ^ 2 * (blocks i).energy D F θ V := by
        simp only [v, norm_mul, mul_pow, ← Finset.mul_sum]
        rw [FrozenBlock.restrictedRow_energy D (blocks i) F θ V rows (hrows i hi)]
      _ ≤ ‖(inactiveWeight K S (blocks i).fixed)⁻¹‖ ^ 2 *
          (L * ‖inactiveWeight K S (blocks i).fixed‖ ^ 2 * Z ^ (E + eps)) :=
        mul_le_mul_of_nonneg_left hblock (sq_nonneg _)
      _ = L * (‖(inactiveWeight K S (blocks i).fixed)⁻¹‖ ^ 2 *
          ‖inactiveWeight K S (blocks i).fixed‖ ^ 2) * Z ^ (E + eps) := by ring
      _ = E0 := by rw [hcancel, mul_one]
  have hfinite := InactiveCore.finite_weighted_energy_le I rows
    (fun i => a i * inactiveWeight K S (blocks i).fixed) v hinner
  have hrow (k : Ideal (𝓞 K)) :
      (∑ i ∈ I, (a i * inactiveWeight K S (blocks i).fixed) * v i k) =
      ∑ i ∈ I, a i * (blocks i).restrictedRow D F θ V k := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [v]
    calc
      _ = a i * (inactiveWeight K S (blocks i).fixed *
          (inactiveWeight K S (blocks i).fixed)⁻¹) * (blocks i).restrictedRow D F θ V k := by ring
      _ = _ := by rw [mul_inv_cancel₀ (inactiveWeight_ne_zero K S _), mul_one]
  simp_rw [hrow] at hfinite
  apply hfinite.trans_eq
  dsimp [E0, L]
  ring

/-- Literal data of the inactive tuple sum for a fixed activity pattern. -/
structure InactiveFamily where
  slots : ℕ
  windows : Fin slots → Finset (ExteriorPrime K S)
  scales : Fin slots → ℝ
  slotCoefficient : Fin slots → ExteriorPrime K S → ℂ
  tuples : Finset (Fin slots → ExteriorPrime K S)
  phase : (Fin slots → ExteriorPrime K S) → ℂ
  blocks : (Fin slots → ExteriorPrime K S) → FrozenBlock K S
  rows : Finset (Ideal (𝓞 K))

namespace InactiveFamily

variable {K S}

def coefficient (b : InactiveFamily K S) (p : Fin b.slots → ExteriorPrime K S) : ℂ :=
  GeneralInactiveMass.slotProduct b.slotCoefficient p * b.phase p

def row (b : InactiveFamily K S) (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (V : SmoothAnnularTest) (k : Ideal (𝓞 K)) : ℂ :=
  ∑ p ∈ b.tuples, b.coefficient p * (b.blocks p).restrictedRow D F θ V k

def energy (b : InactiveFamily K S) (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (V : SmoothAnnularTest) : ℝ := ∑ k ∈ b.rows, ‖b.row D F θ V k‖ ^ 2

def restrictedRow (b : InactiveFamily K S) (F : FiniteMellinData K S)
    (θ : HeckeCharacter K) (V : SmoothAnnularTest) (k : Ideal (𝓞 K)) : ℂ :=
  if k ∈ b.rows then b.row D F θ V k else 0

theorem restrictedRow_energy (b : InactiveFamily K S) (F : FiniteMellinData K S)
    (θ : HeckeCharacter K) (V : SmoothAnnularTest) (rows : Finset (Ideal (𝓞 K)))
    (hrows : b.rows ⊆ rows) :
    (∑ k ∈ rows, ‖b.restrictedRow D F θ V k‖ ^ 2) = b.energy D F θ V := by
  have he := Finset.sum_subset hrows
    (f := fun k => ‖b.restrictedRow D F θ V k‖ ^ 2)
    (fun k _ hk => by simp only [restrictedRow, if_neg hk, norm_zero, zero_pow (by decide : 2 ≠ 0)])
  rw [← he]
  unfold energy
  apply Finset.sum_congr rfl
  intro k hk
  simp only [restrictedRow, if_pos hk]

/-- These are precisely finite-support, coefficient and length conditions.
The equality of the inactive set keeps repeated primes from being counted
twice in the reciprocal prefactor. -/
structure Admissible (b : InactiveFamily K S) (Z W A B E Fmax : ℝ) (rmax : ℕ) : Prop where
  slots_le : b.slots ≤ rmax
  scale_ge : ∀ i, 1 ≤ b.scales i
  window_norm : ∀ i p, p ∈ b.windows i →
    b.scales i ≤ (p.val.asIdeal.absNorm : ℝ) ∧ (p.val.asIdeal.absNorm : ℝ) ≤ 2 * b.scales i
  tuple_subset : b.tuples ⊆ Fintype.piFinset b.windows
  coefficient_bound : ∀ i p, p ∈ b.windows i → ‖b.slotCoefficient i p‖ ≤ B
  phase_bound : ∀ p ∈ b.tuples, ‖b.phase p‖ ≤ 1
  block_admissible : ∀ p ∈ b.tuples, (b.blocks p).Admissible Z W A E Fmax
  row_subset : ∀ p ∈ b.tuples, (b.blocks p).rows ⊆ b.rows
  inactive_eq : ∀ p ∈ b.tuples, (b.blocks p).fixed.inactive = Finset.univ.image p

end InactiveFamily

/-- Full inactive assembly for arbitrary, possibly overlapping windows
and arbitrary bounded slot coefficients.  Its constant uses the proved
actual ideal count, including all tuple collisions. -/
theorem general_inactive_block_energy [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ : HeckeCharacter K) (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D)
    (W Fmax : ℝ) (rmax : ℕ) (eps : ℝ)
    (hW : 0 ≤ W) (hFmax : 0 ≤ Fmax) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z A B E : ℝ), 1 < Z → 0 < A → 1 ≤ B →
      ∀ (V : SmoothAnnularTest) (b : InactiveFamily K S),
      b.Admissible Z W A B E Fmax rmax →
      b.energy D F θ V ≤
        C * A ^ 2 * (B ^ rmax) ^ 2 *
          testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 * Z ^ (E + eps) := by
  obtain ⟨Cb, hCb, hb⟩ := general_frozen_weighted_energy K S D F hF θ hKernel hθ hD
    hquadratic hcubic W Fmax eps hW hFmax heps
  obtain ⟨M, hM, hm⟩ := GeneralInactiveMass.exists_uniform_contracted_mass_constant K rmax
  refine ⟨Cb * M ^ 2, mul_pos hCb (sq_pos_of_pos (zero_lt_one.trans_le hM)), ?_⟩
  intro Z A B E hZ hA hB V b hadm
  have he := hb Z A E hZ hA V b.tuples b.blocks b.coefficient b.rows
    hadm.block_admissible hadm.row_subset
  have hslots : Fintype.card (Fin b.slots) ≤ rmax := by
    simpa only [Fintype.card_fin] using hadm.slots_le
  have hmass0 := hm S hslots b.windows b.scales hadm.scale_ge hadm.window_norm B hB
    b.slotCoefficient hadm.coefficient_bound b.tuples hadm.tuple_subset b.phase hadm.phase_bound
  have heq : (∑ p ∈ b.tuples, ‖b.coefficient p * inactiveWeight K S (b.blocks p).fixed‖) =
      ∑ p ∈ b.tuples,
        ‖GeneralInactiveMass.inactiveCoefficient K S b.slotCoefficient p * b.phase p‖ := by
    apply Finset.sum_congr rfl
    intro p hp
    congr 1
    unfold InactiveFamily.coefficient GeneralInactiveMass.inactiveCoefficient
      GeneralInactiveMass.distinctPrefactor GeneralInactiveMass.tupleSupport inactiveWeight
    rw [hadm.inactive_eq p hp]
    ring
  have hmass : (∑ p ∈ b.tuples, ‖b.coefficient p * inactiveWeight K S (b.blocks p).fixed‖) ≤
      M * B ^ rmax := by rw [heq]; exact hmass0
  have hmass2 := pow_le_pow_left₀
    (Finset.sum_nonneg (fun p _ => norm_nonneg _)) hmass 2
  apply he.trans
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmass2
      (by positivity : 0 ≤ Cb * A ^ 2 *
        testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2))
    (by positivity : 0 ≤ Z ^ (E + eps))
  apply h.trans_eq
  rw [mul_pow]
  ring

/-- All activity patterns of the original finite slot collection. -/
structure MarkedFamily (rmax : ℕ) where
  patterns : Finset (Finset (Fin rmax))
  components : Finset (Fin rmax) → InactiveFamily K S
  rows : Finset (Ideal (𝓞 K))

namespace MarkedFamily

variable {K S} {rmax : ℕ}

def row (b : MarkedFamily K S rmax) (F : FiniteMellinData K S)
    (θ : HeckeCharacter K) (V : SmoothAnnularTest) (k : Ideal (𝓞 K)) : ℂ :=
  ∑ A ∈ b.patterns, (b.components A).restrictedRow D F θ V k

def energy (b : MarkedFamily K S rmax) (F : FiniteMellinData K S)
    (θ : HeckeCharacter K) (V : SmoothAnnularTest) : ℝ :=
  ∑ k ∈ b.rows, ‖b.row D F θ V k‖ ^ 2

structure Admissible (b : MarkedFamily K S rmax) (Z W A B E Fmax : ℝ) : Prop where
  component_admissible : ∀ a ∈ b.patterns, (b.components a).Admissible Z W A B E Fmax rmax
  row_subset : ∀ a ∈ b.patterns, (b.components a).rows ⊆ b.rows

end MarkedFamily

/-- All active choices, all inactive tuples, all frozen local states and
all local classes now occur in one genuine linear row vector. -/
theorem general_marked_family_energy [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ : HeckeCharacter K) (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D)
    (W Fmax : ℝ) (rmax : ℕ) (eps : ℝ)
    (hW : 0 ≤ W) (hFmax : 0 ≤ Fmax) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z A B E : ℝ), 1 < Z → 0 < A → 1 ≤ B →
      ∀ (V : SmoothAnnularTest) (b : MarkedFamily K S rmax),
      b.Admissible Z W A B E Fmax →
      b.energy D F θ V ≤
        C * A ^ 2 * (B ^ rmax) ^ 2 *
          testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 * Z ^ (E + eps) := by
  obtain ⟨Cb, hCb, hb⟩ := general_inactive_block_energy K S D F hF θ hKernel hθ hD
    hquadratic hcubic W Fmax rmax eps hW hFmax heps
  refine ⟨(2 ^ rmax : ℝ) ^ 2 * Cb, by positivity, ?_⟩
  intro Z A B E hZ hA hB V b hadm
  let E0 := Cb * A ^ 2 * (B ^ rmax) ^ 2 *
    testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 * Z ^ (E + eps)
  have hE0 : 0 ≤ E0 := by dsimp [E0]; positivity
  have hpart (a : Finset (Fin rmax)) (ha : a ∈ b.patterns) :
      (∑ k ∈ b.rows, ‖(b.components a).restrictedRow D F θ V k‖ ^ 2) ≤ E0 := by
    rw [InactiveFamily.restrictedRow_energy D (b.components a) F θ V b.rows
      (hadm.row_subset a ha)]
    exact hb Z A B E hZ hA hB V (b.components a) (hadm.component_admissible a ha)
  have hfinite := InactiveCore.finite_weighted_energy_le b.patterns b.rows (fun _ => (1 : ℂ))
    (fun a k => (b.components a).restrictedRow D F θ V k) hpart
  have hcomb : b.energy D F θ V ≤ (b.patterns.card : ℝ) ^ 2 * E0 := by
    simpa only [MarkedFamily.energy, MarkedFamily.row, one_mul, norm_one,
      Finset.sum_const, nsmul_eq_mul, mul_one] using hfinite
  have hcard : (b.patterns.card : ℝ) ≤ (2 ^ rmax : ℝ) := by
    have h := Finset.card_le_univ b.patterns
    simp only [Fintype.card_finset, Fintype.card_fin] at h
    exact_mod_cast h
  have hcard2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
  apply hcomb.trans
  apply (mul_le_mul_of_nonneg_right hcard2 hE0).trans_eq
  dsimp [E0]
  ring

/-- The complete general reflected block energy.  Every activity pattern,
inactive tuple, frozen state, local class, supported row part, row-unit
class and actual powerful part is present in this one conclusion. -/
theorem general_complete_family_energy [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ : HeckeCharacter K) (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D)
    (W Fmax Omax Lmax : ℝ) (rmax : ℕ) (eps : ℝ)
    (hW : 0 ≤ W) (hFmax : 0 ≤ Fmax) (hOmax : 0 ≤ Omax)
    (hLmax : 0 ≤ Lmax) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z O A B E : ℝ),
      1 < Z → 0 ≤ O → O ≤ Omax → 0 < A → 1 ≤ B →
      ∀ (V : SmoothAnnularTest) (label puncture : ExteriorIdeal K S)
        (R : Finset (IdealRankin.PowerfulIdeal K))
        (families : IdealRankin.PowerfulIdeal K → Finset (ExteriorPrime K S) →
          SixthUnitClasses K S → MarkedFamily K S rmax),
      ((label.val * puncture.val).val.absNorm : ℝ) ≤ Z ^ Lmax →
      (∀ I ∈ R, IdealRankin.powerfulNorm K I ≤ Z ^ O) →
      (∀ I ∈ R, ∀ T ∈ (ActualFrozenStateCount.fixedSupport K S label puncture).powerset,
        ∀ u, (families I T u).Admissible Z W A B E Fmax) →
      (∑ I ∈ R, ∑ T ∈ (ActualFrozenStateCount.fixedSupport K S label puncture).powerset,
        ∑' u : SixthUnitClasses K S, (families I T u).energy D F θ V) ≤
        C * A ^ 2 * (B ^ rmax) ^ 2 *
          testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
          Z ^ (O / 2 + E + eps) := by
  letI : Fintype (SixthUnitClasses K S) := Fintype.ofFinite _
  obtain ⟨Cb, hCb, hb⟩ := general_marked_family_energy K S D F hF θ hKernel hθ hD
    hquadratic hcubic W Fmax rmax (eps / 2) hW hFmax (by linarith)
  obtain ⟨Cp, hCp, hc⟩ := powerful_supported_count K S Omax Lmax (eps / 2)
    hOmax hLmax (by linarith)
  refine ⟨Cb * Cp, mul_pos hCb hCp, ?_⟩
  intro Z O A B E hZ hO hO' hA hB V label puncture R families hnorm hR hadm
  let E0 := Cb * A ^ 2 * (B ^ rmax) ^ 2 *
    testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 * Z ^ (E + eps / 2)
  have hE0 : 0 ≤ E0 := by dsimp [E0]; positivity
  have hlocal (I : IdealRankin.PowerfulIdeal K) (hI : I ∈ R)
      (T : Finset (ExteriorPrime K S))
      (hT : T ∈ (ActualFrozenStateCount.fixedSupport K S label puncture).powerset)
      (u : SixthUnitClasses K S) : (families I T u).energy D F θ V ≤ E0 :=
    hb Z A B E hZ hA hB V (families I T u) (hadm I hI T hT u)
  have hcomb :
      (∑ I ∈ R, ∑ T ∈ (ActualFrozenStateCount.fixedSupport K S label puncture).powerset,
        ∑' u : SixthUnitClasses K S, (families I T u).energy D F θ V) ≤
      ((R.card : ℝ) * ((ActualFrozenStateCount.fixedSupport K S label puncture).powerset.card : ℝ) *
        (Nat.card (SixthUnitClasses K S) : ℝ)) * E0 := by
    simp_rw [tsum_fintype]
    calc
      _ ≤ ∑ _I ∈ R, ∑ _T ∈ (ActualFrozenStateCount.fixedSupport K S label puncture).powerset,
          ∑ _u : SixthUnitClasses K S, E0 := by
        apply Finset.sum_le_sum
        intro I hI
        apply Finset.sum_le_sum
        intro T hT
        exact Finset.sum_le_sum (fun u _ => hlocal I hI T hT u)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
        ring
  apply hcomb.trans
  apply (mul_le_mul_of_nonneg_right (hc Z O hZ hO hO' label puncture R hnorm hR) hE0).trans_eq
  have hpow : Z ^ (O / 2 + eps / 2) * Z ^ (E + eps / 2) = Z ^ (O / 2 + E + eps) := by
    rw [← Real.rpow_add (zero_lt_one.trans hZ)]
    congr 1
    ring
  dsimp [E0]
  calc
    _ = (Cb * Cp) * A ^ 2 * (B ^ rmax) ^ 2 *
        testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
        (Z ^ (O / 2 + eps / 2) * Z ^ (E + eps / 2)) := by ring
    _ = _ := by rw [hpow]

#print axioms general_frozen_weighted_energy
#print axioms general_inactive_block_energy
#print axioms general_marked_family_energy
#print axioms general_complete_family_energy

end HeckeSkeleton.LowEnergy.GeneralInactiveEnergy
