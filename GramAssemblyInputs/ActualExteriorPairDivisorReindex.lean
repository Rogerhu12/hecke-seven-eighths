import ActualIdealPairMobius
import HeckeGeneral.Analysis.GlobalThetaData
import Mathlib.Data.Finset.Preimage

/-!
UNCOMPILED / native 0. The same actual exterior divisor is removed from
both columns of a finite ideal-pair sum. Its residual support is exactly
the preimage of the ORIGINAL support under (M1,M2) -> (D*M1,D*M2).
The final identity combines this reindexing with the genuine ideal Mobius
expansion. No principal generator, ray condition or analytic bound enters.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Global.ActualPairDivisorDraft

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Arithmetic.IdealMobiusMask
open HeckeGeneral.Arithmetic.ActualIdealPairMobiusDraft
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local notation "E" => ExteriorIdeal K S

/-- A divisor of a nonzero exterior ideal has an actual exterior quotient. -/
theorem exists_exterior_quotient (D I : E) (h : D.val.val ∣ I.val.val) :
    ∃ N : E, exteriorMul K S D N = I := by
  obtain ⟨J, hJ⟩ := h
  have hJ0 : J ≠ 0 := by
    intro hz
    apply nonZeroDivisors.coe_ne_zero I.val
    simpa only [hz, mul_zero] using hJ
  have houtside : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ J → p ∉ S := by
    intro p hp
    apply I.property p
    rw [hJ]
    exact hp.trans (dvd_mul_left J D.val.val)
  refine ⟨⟨⟨J, mem_nonZeroDivisors_of_ne_zero hJ0⟩, houtside⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hJ.symm

theorem exteriorMul_left_injective (D : E) :
    Function.Injective (exteriorMul K S D) := by
  intro I J h
  apply Subtype.ext
  apply Subtype.ext
  exact mul_left_cancel₀ (nonZeroDivisors.coe_ne_zero D.val)
    (congrArg (fun A : E => A.val.val) h)

def exteriorPairDilation (D : E) (ij : E × E) : E × E :=
  (exteriorMul K S D ij.1, exteriorMul K S D ij.2)

theorem exteriorPairDilation_injective (D : E) :
    Function.Injective (exteriorPairDilation K S D) := by
  intro ij kl h
  apply Prod.ext
  · exact exteriorMul_left_injective K S D (congrArg Prod.fst h)
  · exact exteriorMul_left_injective K S D (congrArg Prod.snd h)

/-- Both original cutoffs remain on D*M_i; the residual set is finite by
injectivity and introduces no new estimate or enlarged support. -/
def divisorResidualPairs (D : E) (A : Finset (E × E)) : Finset (E × E) :=
  A.preimage (exteriorPairDilation K S D)
    (exteriorPairDilation_injective K S D).injOn

@[simp] theorem mem_divisorResidualPairs (D : E) (A : Finset (E × E))
    (ij : E × E) :
    ij ∈ divisorResidualPairs K S D A ↔ exteriorPairDilation K S D ij ∈ A :=
  Finset.mem_preimage

theorem sum_divisible_pair_eq_sum_residual {M : Type*} [AddCommMonoid M]
    (D : E) (A : Finset (E × E)) (F : E × E → M) :
    (∑ ij ∈ A with D.val.val ∣ ij.1.val.val ∧ D.val.val ∣ ij.2.val.val, F ij) =
      ∑ mn ∈ divisorResidualPairs K S D A, F (exteriorPairDilation K S D mn) := by
  symm
  refine Finset.sum_bij (fun mn _ => exteriorPairDilation K S D mn) ?_ ?_ ?_ ?_
  · intro mn hmn
    exact Finset.mem_filter.mpr
      ⟨(mem_divisorResidualPairs K S D A mn).mp hmn,
        ⟨⟨mn.1.val.val, rfl⟩, ⟨mn.2.val.val, rfl⟩⟩⟩
  · intro mn _ pq _ h
    exact exteriorPairDilation_injective K S D h
  · intro ij hij
    obtain ⟨hijA, hD1, hD2⟩ := Finset.mem_filter.mp hij
    obtain ⟨N1, hN1⟩ := exists_exterior_quotient K S D ij.1 hD1
    obtain ⟨N2, hN2⟩ := exists_exterior_quotient K S D ij.2 hD2
    have heq : exteriorPairDilation K S D (N1, N2) = ij := Prod.ext hN1 hN2
    refine ⟨(N1, N2), (mem_divisorResidualPairs K S D A _).mpr ?_, heq⟩
    rw [heq]
    exact hijA
  · intro mn _
    rfl

/-- Every prime in the actual finite first-column envelope is outside S. -/
theorem finite_pair_prime_envelope_outside (A : Finset (E × E))
    (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∈ finiteIdealPrimeEnvelope A (fun ij => ij.1.val)) : p ∉ S := by
  obtain ⟨ij, _hij, hpI⟩ := Finset.mem_biUnion.mp hp
  exact ij.1.property p ((mem_primeExponentSupport_iff ij.1.val p).mp hpI)

/-- Package the genuine squarefree prime product as an exterior ideal. -/
def exteriorPrimeProduct (T : Finset (HeightOneSpectrum (𝓞 K)))
    (houtside : ∀ p ∈ T, p ∉ S) : E :=
  ⟨⟨primeProduct T, mem_nonZeroDivisors_of_ne_zero (primeProduct_ne_bot T)⟩, by
    intro p hp
    have hmem : p.asIdeal ∈ normalizedFactors (primeProduct T) :=
      (mem_normalizedFactors_iff (primeProduct_ne_bot T)).mpr ⟨p.prime, hp⟩
    rw [normalizedFactors_primeProduct] at hmem
    obtain ⟨q, hq, hqp⟩ := Multiset.mem_map.mp hmem
    have heq : q = p := HeightOneSpectrum.asIdeal_injective hqp
    subst q
    exact houtside p hq⟩

def pairMobiusDivisor (A : Finset (E × E))
    (T : {T : Finset (HeightOneSpectrum (𝓞 K)) //
      T ∈ (finiteIdealPrimeEnvelope A (fun ij => ij.1.val)).powerset}) : E :=
  exteriorPrimeProduct K S T.val (fun p hp =>
    finite_pair_prime_envelope_outside K S A p ((Finset.mem_powerset.mp T.property) hp))

/-- Exact Mobius insertion followed by simultaneous removal of the SAME
divisor from both actual exterior columns. The finite support and coefficient
are evaluated on the original reconstructed ideals D*M1 and D*M2. -/
theorem finite_coprime_exterior_pair_sum_mobius_reindexed
    (A : Finset (E × E)) (F : E × E → ℂ) :
    (∑ ij ∈ A, F ij * (if IsCoprime ij.1.val.val ij.2.val.val then 1 else 0)) =
      ∑ T ∈ (finiteIdealPrimeEnvelope A (fun ij => ij.1.val)).powerset.attach,
        (moebius (primeProduct T.val) : ℂ) *
          ∑ mn ∈ divisorResidualPairs K S (pairMobiusDivisor K S A T) A,
            F (exteriorPairDilation K S (pairMobiusDivisor K S A T) mn) := by
  calc
    _ = ∑ T ∈ (finiteIdealPrimeEnvelope A (fun ij => ij.1.val)).powerset.attach,
        (moebius (primeProduct T.val) : ℂ) *
          ∑ ij ∈ A with primeProduct T.val ∣ ij.1.val.val ∧
              primeProduct T.val ∣ ij.2.val.val, F ij := by
      have hAttach := Finset.sum_attach
        (finiteIdealPrimeEnvelope A (fun ij => ij.1.val)).powerset
        (fun T : Finset (HeightOneSpectrum (𝓞 K)) =>
          (moebius (primeProduct T) : ℂ) *
            ∑ ij ∈ A with primeProduct T ∣ ij.1.val.val ∧
                primeProduct T ∣ ij.2.val.val, F ij)
      exact (finite_coprime_pair_sum_mobius A
        (fun ij => ij.1.val) (fun ij => ij.2.val) F).trans hAttach.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro T _hT
      congr 1
      exact sum_divisible_pair_eq_sum_residual K S (pairMobiusDivisor K S A T) A F

end HeckeGeneral.ThetaSkeleton.Global.ActualPairDivisorDraft
