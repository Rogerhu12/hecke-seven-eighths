import HeckeSkeleton.LowEnergy.GeneralCanonicalBlock
import HeckeSkeleton.LowEnergy.GeneralKernelTail
import HeckeSkeleton.LowEnergy.GeneralAnnuli
import HeckeSkeleton.LowEnergy.GeneralProductReconstruction

/-!
# Public general marked reflected energy

The interface follows Lemma 4.8: arbitrary arithmetic calibration and
unramified background, squarefree labels and punctures, product-form
marks, independent completed scale, actual residual row annuli and
powerful row parts.  All finite coefficients and supports remain data;
the energy, tail, reconstruction and conductor assertions are conclusions.

The exponent in `block_energy` is the exact `paperExponent` recorded in
`ReflectedBlock.exponent`, including the common kernel saving.  A common
upper bound E is a scalar comparison of those explicit exponents.  The
constant is selected before every profile, row, label, puncture, completed
scale and tuple family.  Test dependence is displayed as a finite seminorm.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.GeneralCompletedEnergy

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckePort.CenteredMomentGenerator
open HeckeSkeleton.LowEnergy.ActualReflection
open HeckeSkeleton.LowEnergy.ActualReflectionReindex
open HeckeSkeleton.LowEnergy.ActualFrozenCharges
open HeckeSkeleton.LowEnergy.ActualSourceReindex
open HeckeSkeleton.LowEnergy.ActualSieveDictionary
open HeckeSkeleton.LowEnergy.GeneralRows
open HeckeSkeleton.LowEnergy.GeneralReconstruction
open HeckeSkeleton.LowEnergy.GeneralProductReconstruction
open HeckeSkeleton.LowEnergy.GeneralCanonicalBlock
open HeckeSkeleton.LowEnergy.GeneralInactiveEnergy
open HeckeSkeleton.LowEnergy.GeneralKernelTail
open HeckeSkeleton.LowEnergy.GeneralTailNumerics
open HeckeSkeleton.LowEnergy.LogGeometry
open HeckeSkeleton.Moments.MOM_BASE
open scoped Classical BigOperators NumberField nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

def tailBudget (Cmax Wmax Hmax Pmax Amax Nmax : ℝ) : ℝ :=
  Cmax + Wmax + 2 * Hmax + 2 * Pmax + 2 * Amax + Nmax

/-- Every input is an ordinary bounded length, finite cardinality or
coefficient norm.  In particular the total reflected tail estimate and
its polynomial prefactor are not assumptions. -/
def ArbitraryPowerTails (F : FiniteMellinData K S) (θ : HeckeCharacter K) : Prop :=
  ∀ Cmax Wmax Hmax Pmax Amax Nmax tau L : ℝ,
    0 ≤ Cmax → 0 ≤ Wmax → 0 ≤ Hmax → 0 ≤ Pmax → 0 ≤ Amax → 0 ≤ Nmax →
    0 < tau → 0 < L →
    ∃ (J : ℕ) (C Z0 : ℝ), 0 ≤ C ∧ 1 < Z0 ∧
      ∀ Z : ℝ, Z0 ≤ Z → 16 ≤ Z ^ (tau / 2) ∧
      ∀ (V : SmoothAnnularTest) {ι : Type*} (I : Finset ι) (p : ι → TailPiece K S),
      (I.card : ℝ) ≤ Z ^ Cmax →
      (∀ i ∈ I, 0 < (p i).X) →
      (∀ i ∈ I, ‖(p i).weight‖ ≤ Z ^ Wmax) →
      (∀ i ∈ I, exteriorNorm K S (p i).row ≤ Z ^ Hmax) →
      (∀ i ∈ I, exteriorNorm K S (p i).mark ≤ Z ^ Pmax) →
      (∀ i ∈ I, exteriorNorm K S (primeSetIdeal K S (p i).state.active) ≤ Z ^ Amax) →
      (∀ i ∈ I, Z ^ (-Nmax) ≤ (p i).X) →
      (∀ i ∈ I, Summable (fun cb => ‖(p i).weight *
        tailColumnAtom K S D (p i).fixed (p i).state F θ (p i).classes V.toFun (p i).X
          (Z ^ (tau / 2)) (p i).row (p i).mark cb‖)) ∧
      (∑ i ∈ I, (p i).tailMass D F θ V (Z ^ (tau / 2))) ≤
        C * testSeminorm V.toFun J (tailOrder (tailBudget Cmax Wmax Hmax Pmax Amax Nmax) tau L) *
          Z ^ (-L)

theorem arbitraryPowerTails (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ) :
    ArbitraryPowerTails K S D F θ := by
  intro Cmax Wmax Hmax Pmax Amax Nmax tau L hC hW hH hP hA hN htau hL
  have hbudget : 0 ≤ tailBudget Cmax Wmax Hmax Pmax Amax Nmax := by
    unfold tailBudget
    positivity
  obtain ⟨J, C, Z0, hC0, hZ0, hb⟩ := actual_total_power_tail K S D F θ
    hreflection.kernel hreflection.exterior_unramified hreflection.allowed_generators
    (tailBudget Cmax Wmax Hmax Pmax Amax Nmax) tau L hbudget htau hL
  refine ⟨J, C, Z0, hC0, hZ0, ?_⟩
  intro Z hZ
  refine ⟨(hb Z hZ).1, ?_⟩
  intro V ι I p hcard hX hw hk hp ha hs
  exact (hb Z hZ).2 V I p hX
    (total_prefactor_le_from_lengths K S I p (zero_lt_one.trans (hZ0.trans_le hZ))
      hcard hX hw hk hp ha hs)

/-- The complete reusable terminal for canonical inverse induction.
This record contains conclusions only, proved below from the original
reflection input and the two original exterior sieves. -/
structure CompletedMarkedEnergy (F : FiniteMellinData K S) (θ : HeckeCharacter K) : Prop where
  block_energy :
    ∀ (W Fmax Omax Lmax : ℝ) (rmax : ℕ) (eps : ℝ),
      0 ≤ W → 0 ≤ Fmax → 0 ≤ Omax → 0 ≤ Lmax → 0 < eps →
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
        (∀ I ∈ R, ∀ T ∈ (ActualFrozenStateCount.fixedSupport K S label puncture).powerset,
          ∀ u, FamilySourceSupported K S (families I T u)) →
        (∑ I ∈ R, ∑ T ∈ (ActualFrozenStateCount.fixedSupport K S label puncture).powerset,
          ∑' u : SixthUnitClasses K S, sourceMarkedEnergy K S D (families I T u) F θ V) ≤
          C * A ^ 2 * (B ^ rmax) ^ 2 *
            testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
            Z ^ (O / 2 + E + eps)
  reconstruct :
    ∀ (d : MarkedDatum K S) (V : SmoothAnnularTest) (X : ℝ), 0 < X →
      canonicalCompletedSum (exteriorGamma K S D)
        (canonicalTau K S D θ (rowElement K S D d) d.puncture.val.val)
        (wholeMarkWeight K S d.marks) V.toFun X =
        ∑' s : FrozenState K S d.frozen d.puncture,
          ∑' A : MarkChoice K S d,
            ∑' cb : ExteriorIdeal K S × ExteriorIdeal K S,
              generalAtom K S D (splitFixed K S d A) s F θ (fun _ => 1) V.toFun X
                d.moving (primeSetIdeal K S A.val) cb.1 cb.2
  reconstruct_product :
    ∀ (r : ℕ) (k label puncture : ExteriorIdeal K S)
      (hpuncture : Squarefree puncture.val.val) (u : S.unit K)
      (tuples : Finset (Fin r → ExteriorPrime K S))
      (a : Fin r → ExteriorPrime K S → ℂ)
      (V : SmoothAnnularTest) (X : ℝ), 0 < X →
      canonicalCompletedSum (exteriorGamma K S D)
        (canonicalTau K S D θ (canonicalRowElement K S D k label u) puncture.val.val)
        (productMark K S tuples a) V.toFun X =
        ∑ p ∈ (tuples.filter (TupleAdmissible K S k label puncture)).attach,
          GeneralInactiveMass.slotProduct a p.val *
            reflectedTuple K S D F θ k label puncture hpuncture u p.val
              (Finset.mem_filter.mp p.property).2 V.toFun X
  power_tails : ArbitraryPowerTails K S D F θ
  annular_conductors :
    ∀ (k label puncture : ExteriorIdeal K S),
      Squarefree label.val.val → Squarefree puncture.val.val →
      ∀ (s : FrozenState K S (reflectedFrozen K S k label puncture) puncture)
        (Z X Klo Plo M O V Ck Cp Cf : ℝ),
      1 < Z → 0 < Klo → 0 < Ck → 0 < Cp → 0 < Cf →
      Klo ≤ exteriorNorm K S (movingRow K S k label puncture) →
      exteriorNorm K S k ≤ Ck * Z ^ M →
      Z ^ O ≤ Cp * exteriorNorm K S (exteriorPowerfulPart K S k) →
      exteriorNorm K S label ≤ Cf * Z ^ V →
      scale Z Klo ≤ M - O + (Real.log Ck + Real.log Cp) / Real.log Z ∧
        GeneralBlockPolynomial.threshold Z X
            (exteriorNorm K S (primeSetIdeal K S s.active))
            (exteriorNorm K S (minimumLinearIdeal K S s))
            (exteriorNorm K S (minimumCubeIdeal K S s)) Klo Plo -
          scale Z (exteriorNorm K S (minimumSmallIdeal K S s)) -
          scale Z (exteriorNorm K S (minimumCubeIdeal K S s)) ≤
        2 * M - O + scale Z (exteriorNorm K S puncture) + V - scale Z X +
          2 * scale Z Plo +
          (2 * Real.log Ck + Real.log Cp + Real.log Cf) / Real.log Z

/-- General marked reflected energy from the original reflection and the
two original sieves.  No energy, tail or conductor bound is an input. -/
theorem completedMarkedEnergy [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D) :
    CompletedMarkedEnergy K S D F θ where
  block_energy := canonical_complete_family_energy K S D F hreflection.kernel.finite_admissible θ
    hreflection.kernel hreflection.exterior_unramified hreflection.allowed_generators
    hquadratic hcubic
  reconstruct := canonicalCompletedSum_eq_general_atoms K S D
    hreflection.allowed_generators F θ hreflection
  reconstruct_product := by
    intro r k label puncture hpuncture u tuples a V X hX
    exact canonicalCompletedSum_productMark_eq_reflectedTuples K S D
      hreflection.allowed_generators F θ hreflection k label puncture hpuncture u
      tuples a V X hX
  power_tails := arbitraryPowerTails K S D F θ hreflection
  annular_conductors := by
    intro k label puncture hlabel hpuncture s Z X Klo Plo M O V Ck Cp Cf
      hZ hKlo hCk hCp hCf hmove hrow hp hf
    exact GeneralAnnuli.actual_annular_comparisons K S k label puncture hlabel hpuncture s
      hZ hKlo hCk hCp hCf hmove hrow hp hf

#print axioms arbitraryPowerTails
#print axioms completedMarkedEnergy

end HeckeSkeleton.LowEnergy.GeneralCompletedEnergy
