import HeckeSkeleton.LowEnergy.ActualRows
import HeckeSkeleton.LowEnergy.IdealRows
import HeckeGeneral.Analysis.MarkedThetaReflection

/-!
# Applying the supplied reflection to every actual row

The powerful and residual ideals are constructed from the actual prime
exponents.  All marking collisions are removed using the literal whole-index
symbol zeros.  What remains is exactly a `MarkedDatum`, so the supplied
coefficient reflection applies without assuming a row-factorization input.

This is a project adapter.  It does not supply the common Fourier profile or
an estimate for the reflected row vector.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.LowEnergy.ActualReflection

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeSkeleton.LowEnergy.ActualRows HeckeSkeleton.LowEnergy.IdealRows
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Positivity belongs to the actual ideal dictionary, before reflection
states or cube columns are introduced. -/
theorem exteriorNorm_pos (A : ExteriorIdeal K S) : 0 < exteriorNorm K S A := by
  exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors A.val

@[simp] theorem emptyPrimeIdeal_val :
    (primeSetIdeal K S ∅).val.val = (1 : Ideal (𝓞 K)) := by
  simp [primeSetIdeal, squarefreeIdeal, HeckeGeneral.Arithmetic.IdealMobiusMask.primeProduct]

/-- The exterior support is exactly ordinary prime divisibility. -/
theorem mem_exteriorSupport_iff (I : ExteriorIdeal K S) (p : ExteriorPrime K S) :
    p ∈ exteriorSupport K S I ↔ p.val.asIdeal ∣ I.val.val := by
  constructor
  · intro hp
    obtain ⟨q, _hq, hqp⟩ := Finset.mem_image.mp hp
    have he : q.val = p.val := congrArg Subtype.val hqp
    have hd := (mem_idealPrimeSupport_iff K I.val q.val).mp q.property
    simpa only [he] using hd
  · intro hp
    let q : {q : HeightOneSpectrum (𝓞 K) // q ∈ idealPrimeSupport K I.val} :=
      ⟨p.val, (mem_idealPrimeSupport_iff K I.val p.val).mpr hp⟩
    exact Finset.mem_image.mpr ⟨q, Finset.mem_attach _ _, Subtype.ext rfl⟩

/-- The squarefree product contains exactly the primes in its finite set. -/
theorem prime_dvd_primeSetIdeal_iff (Q : Finset (ExteriorPrime K S))
    (p : ExteriorPrime K S) :
    p.val.asIdeal ∣ (primeSetIdeal K S Q).val.val ↔ p ∈ Q := by
  rw [← mem_idealPrimeSupport_iff K (primeSetIdeal K S Q).val p.val]
  change p.val ∈ idealPrimeSupport K (squarefreeIdeal K (Q.image Subtype.val)) ↔ p ∈ Q
  rw [idealPrimeSupport_squarefreeIdeal]
  constructor
  · intro hp
    obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hp
    have he : q = p := Subtype.ext hqp
    exact he ▸ hq
  · intro hp
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩

@[simp] theorem exteriorSupport_emptyPrimeIdeal :
    exteriorSupport K S (primeSetIdeal K S ∅) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hd := (mem_exteriorSupport_iff K S _ p).mp hp
  rw [emptyPrimeIdeal_val] at hd
  exact p.val.prime.not_dvd_one hd

/-- Actual complete prime powers remain outside S because they divide I. -/
def exteriorPowerfulPart (I : ExteriorIdeal K S) : ExteriorIdeal K S :=
  ⟨powerfulPart I.val, fun p hp => I.property p (dvd_trans hp (powerfulPart_dvd I.val))⟩

/-- The residual valuation-one ideal remains outside S for the same reason. -/
def exteriorResidualPart (I : ExteriorIdeal K S) : ExteriorIdeal K S :=
  ⟨residualPart I.val, fun p hp => I.property p (dvd_trans hp (residualPart_dvd I.val))⟩

theorem exterior_residual_powerful_decomposition (I : ExteriorIdeal K S) :
    exteriorMul K S (exteriorResidualPart K S I) (exteriorPowerfulPart K S I) = I := by
  apply Subtype.ext
  change residualPart I.val * powerfulPart I.val = I.val
  rw [mul_comm]
  exact powerful_residual_decomposition I.val

/-- The actual datum used by the low estimate (empty fixed puncture). -/
def actualMarkedDatum (x : ExteriorIdeal K S × SixthUnitClasses K S)
    (Q : Finset (ExteriorPrime K S))
    (hQ : ∀ p ∈ Q, ¬p.val.asIdeal ∣ x.1.val.val) : MarkedDatum K S where
  moving := exteriorResidualPart K S x.1
  frozen := exteriorPowerfulPart K S x.1
  puncture := primeSetIdeal K S ∅
  moving_squarefree := residualPart_squarefree x.1.val
  puncture_squarefree := by rw [emptyPrimeIdeal_val]; exact squarefree_one
  moving_frozen_coprime := (powerful_residual_coprime x.1.val).symm
  moving_puncture_coprime := by rw [emptyPrimeIdeal_val]; exact isCoprime_one_right
  rowUnit := Quotient.out x.2
  marks := Q
  marks_coprime := by
    intro p hp
    refine ⟨?_, ?_, ?_⟩
    · exact fun h => hQ p hp (dvd_trans h (residualPart_dvd x.1.val))
    · exact fun h => hQ p hp (dvd_trans h (powerfulPart_dvd x.1.val))
    · rw [emptyPrimeIdeal_val]
      exact p.val.prime.not_dvd_one

/-- The reconstructed marked datum gives the exact canonical row element. -/
theorem actualMarkedDatum_rowElement (D : ThetaArithmeticData K S)
    (x : ExteriorIdeal K S × SixthUnitClasses K S)
    (Q : Finset (ExteriorPrime K S))
    (hQ : ∀ p ∈ Q, ¬p.val.asIdeal ∣ x.1.val.val) :
    rowElement K S D (actualMarkedDatum K S x Q hQ) =
      (idealSectorElement K S D x).val := by
  change (S.unitEquivUnitsInteger K (Quotient.out x.2)).val *
      D.generator (exteriorMul K S (exteriorResidualPart K S x.1)
        (exteriorPowerfulPart K S x.1)) = _
  rw [exterior_residual_powerful_decomposition]
  rfl

/-- The supplied reflection applies to every noncolliding actual row/tuple. -/
theorem completedThetaSum_actual_reflection (D : ThetaArithmeticData K S)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (x : ExteriorIdeal K S × SixthUnitClasses K S)
    (Q : Finset (ExteriorPrime K S))
    (hQ : ∀ p ∈ Q, ¬p.val.asIdeal ∣ x.1.val.val)
    (V : SmoothAnnularTest) (X : ℝ) (hX : 0 < X) :
    completedThetaSum K S D θ (idealSectorElement K S D x).val
        (primeSetIdeal K S ∅) Q V.toFun X =
      ∑' i : ReflectionIndex K S (actualMarkedDatum K S x Q hQ),
        reflectedTerm K S D (actualMarkedDatum K S x Q hQ) i F θ V.toFun X := by
  have h := hreflection.reflection (actualMarkedDatum K S x Q hQ) V X hX
  rw [actualMarkedDatum_rowElement] at h
  exact h

/-- The concrete reflected row after the exact primal collision deletion. -/
def actualReflectedRow (D : ThetaArithmeticData K S) (F : FiniteMellinData K S)
    (θ : HeckeCharacter K) (x : ExteriorIdeal K S × SixthUnitClasses K S)
    (Q : Finset (ExteriorPrime K S)) (V : ℝ → ℂ) (X : ℝ) : ℂ :=
  if hQ : ∀ p ∈ Q, ¬p.val.asIdeal ∣ x.1.val.val then
    ∑' i : ReflectionIndex K S (actualMarkedDatum K S x Q hQ),
      reflectedTerm K S D (actualMarkedDatum K S x Q hQ) i F θ V X
  else 0

/-- Every actual row is covered: either genuine reflection or a proved zero. -/
theorem completedThetaSum_eq_actualReflectedRow (D : ThetaArithmeticData K S)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (x : ExteriorIdeal K S × SixthUnitClasses K S)
    (Q : Finset (ExteriorPrime K S)) (V : SmoothAnnularTest) (X : ℝ) (hX : 0 < X) :
    completedThetaSum K S D θ (idealSectorElement K S D x).val
        (primeSetIdeal K S ∅) Q V.toFun X =
      actualReflectedRow K S D F θ x Q V.toFun X := by
  by_cases hQ : ∀ p ∈ Q, ¬p.val.asIdeal ∣ x.1.val.val
  · rw [actualReflectedRow, dif_pos hQ]
    exact completedThetaSum_actual_reflection K S D F θ hreflection x Q hQ V X hX
  · rw [actualReflectedRow, dif_neg hQ]
    push_neg at hQ
    obtain ⟨p, hpQ, hpI⟩ := hQ
    apply completedThetaSum_eq_zero_of_mark_overlap K S D θ
      (idealSectorElement K S D x).val (primeSetIdeal K S ∅) Q V.toFun X p hpQ
    have hcontr : sIntegerModulusContraction K S (idealSectorElement K S D x).val =
        x.1.val.val := idealSectorOrbit_contraction K S D x
    rw [hcontr]
    exact hpI

/-- Every active ordinary prime really divides the powerful row part;
the fixed puncture of this application is the unit ideal. -/
theorem actual_active_prime_dvd_powerful
    (x : ExteriorIdeal K S × SixthUnitClasses K S)
    (Q : Finset (ExteriorPrime K S))
    (hQ : ∀ p ∈ Q, ¬p.val.asIdeal ∣ x.1.val.val)
    (i : ReflectionIndex K S (actualMarkedDatum K S x Q hQ))
    (p : HeightOneSpectrum (𝓞 K))
    (hp : p.asIdeal ∣ (activeFrozenIdeal K S (actualMarkedDatum K S x Q hQ) i).val.val) :
    p.asIdeal ∣ (exteriorPowerfulPart K S x.1).val.val := by
  let pe : ExteriorPrime K S :=
    ⟨p, (activeFrozenIdeal K S (actualMarkedDatum K S x Q hQ) i).property p hp⟩
  have hpe : pe ∈ i.activeFrozen :=
    (prime_dvd_primeSetIdeal_iff K S i.activeFrozen pe).mp hp
  have hmem := i.frozen_subset hpe
  change pe ∈ exteriorSupport K S (exteriorPowerfulPart K S x.1) ∪
    exteriorSupport K S (primeSetIdeal K S ∅) at hmem
  rw [exteriorSupport_emptyPrimeIdeal, Finset.union_empty] at hmem
  exact (mem_exteriorSupport_iff K S _ pe).mp hmem

/-- The actual active frozen radical has square bounded by the powerful row
norm. This is the exact arithmetic source of the low conductor inequality;
it has no extra conductor premise. -/
theorem actual_active_radical_sq_norm_le
    (x : ExteriorIdeal K S × SixthUnitClasses K S)
    (Q : Finset (ExteriorPrime K S))
    (hQ : ∀ p ∈ Q, ¬p.val.asIdeal ∣ x.1.val.val)
    (i : ReflectionIndex K S (actualMarkedDatum K S x Q hQ)) :
    exteriorNorm K S (activeFrozenIdeal K S (actualMarkedDatum K S x Q hQ) i) ^ 2 ≤
      exteriorNorm K S (exteriorPowerfulPart K S x.1) := by
  apply norm_radical_sq_le_powerful
  · exact HeckeGeneral.Arithmetic.IdealMobiusMask.squarefree_primeProduct _
  · exact powerfulPart_powerful x.1.val
  · exact actual_active_prime_dvd_powerful K S x Q hQ i

end HeckeSkeleton.LowEnergy.ActualReflection
