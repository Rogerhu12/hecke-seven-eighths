import ActualProbeGaussOriginalFourier
import HeckeGeneral.Arithmetic.SIntegerPeriodicFourier
import HeckeGeneral.Arithmetic.SIntegerModulusNorm

/-!
SOURCE CANDIDATE / not compiled. The actual negative-frequency Gauss pair
in (3.33) descends to the principal quotient by the SAME two generators.
Its full positive finite transform is cardinality times the original
correlation, including zero and nonunit frequencies. The cardinality is
then cancelled against the actual Poisson modulus norm. No infinite sum
interchange, orbital invariance, or Gram estimate is asserted here.
-/

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualProbePairFourierDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Arithmetic.PeriodicFourier
open HeckeGeneral.Arithmetic.ResidueTraceCharacters
open ActualProbeGaussFourierDraft
open scoped Classical BigOperators ComplexConjugate

private theorem fourier_negative_fourier {A : Type*} [CommRing A] [Fintype A]
    (ψ : AddChar A ℂ) (hψ : ψ.IsPrimitive) (f : A → ℂ) (h : A) :
    HeckeGeneral.Arithmetic.PeriodicFourier.fourier ψ (fun a => HeckeGeneral.Arithmetic.PeriodicFourier.fourier ψ f (-a)) h = (Fintype.card A : ℂ) * f h := by
  change (∑ a : A, HeckeGeneral.Arithmetic.PeriodicFourier.fourier ψ f (-a) * ψ (h * a)) = _
  calc
    _ = ∑ a : A, HeckeGeneral.Arithmetic.PeriodicFourier.fourier ψ f a * ψ (-(a * h)) := by
      refine Fintype.sum_bijective (fun a : A => -a) (Equiv.neg A).bijective _ _ ?_
      intro a
      simp only [neg_mul, mul_neg, neg_neg, mul_comm]
    _ = _ := inversion_sum ψ hψ f h

private theorem fourier_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    [Fintype A] [Fintype B] (e : A ≃+* B) (ψ : AddChar B ℂ) (f : A → ℂ) (h : B) :
    HeckeGeneral.Arithmetic.PeriodicFourier.fourier ψ (fun b => f (e.symm b)) h =
      HeckeGeneral.Arithmetic.PeriodicFourier.fourier (transportCharacter e ψ) f (e.symm h) := by
  unfold HeckeGeneral.Arithmetic.PeriodicFourier.fourier
  symm
  apply Fintype.sum_equiv e.toEquiv
  intro a
  change f a * (transportCharacter e ψ) (e.symm h * a) =
    f (e.symm (e a)) * ψ (h * e a)
  simp only [transportCharacter_apply, map_mul, e.apply_symm_apply, e.symm_apply_apply]

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local notation "R" => S.integer K
local notation "N" => NonzeroRingElements R
local notation "Total" => (fun u v : N => R ⧸ commonFactorTotalIdeal (⊤ : Ideal R) (Subtype.val u) (Subtype.val v))
local notation "Principal" => (fun u v : N => R ⧸ Ideal.span ({(Subtype.val u) * (Subtype.val v)} : Set R))

local instance pair_totalFinite (u v : N) : Finite (Total u v) := by
  letI : Finite (R ⧸ Ideal.span ({(Subtype.val u) * (Subtype.val v)} : Set R)) :=
    finite_sIntegerPrincipalResidue K S _ (mul_ne_zero (Subtype.property u) (Subtype.property v))
  exact Finite.of_equiv _ (originalFullTotalPrincipalEquiv K S u v).symm.toEquiv

local instance pair_totalFintype (u v : N) : Fintype (Total u v) := Fintype.ofFinite _

local instance pair_principalFinite (u v : N) : Finite (Principal u v) :=
  finite_sIntegerPrincipalResidue K S _ (mul_ne_zero (Subtype.property u) (Subtype.property v))

local instance pair_principalFintype (u v : N) : Fintype (Principal u v) := Fintype.ofFinite _

variable (P : ProbeData K S) (I J : ExteriorIdeal K S)
local notation "u" => probeGenerator K S P.arithmetic I
local notation "v" => probeGenerator K S P.arithmetic J

/-- Quotient coefficient identified below with the literal pair of probe
Gauss sums at -m. It is independent of the representative by construction. -/
def probeNegativeGaussPairResidue (a : Principal u v) : ℂ :=
  HeckeGeneral.Arithmetic.PeriodicFourier.fourier (originalFullPositiveTraceCharacter K S P.arithmetic.different_outside u v)
    (sIntegerSexticOriginalFullQuotientCorrelation K S
      P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding
      (probeArithmetic_six_support K S P.arithmetic) u v)
    (-(originalFullTotalPrincipalEquiv K S u v).symm a)

/-- Every actual row, including m=0, has exactly its original negative sign. -/
theorem probeNegativeGaussPairResidue_mk (m : R) :
    probeNegativeGaussPairResidue K S P I J (Ideal.Quotient.mk _ m) =
      probeGauss K S P I (-m) * conj (probeGauss K S P J (-m)) := by
  rw [probeGauss_mul_conj_eq_originalFull_fourier]
  unfold probeNegativeGaussPairResidue
  congr 1

/-- The periodic Poisson transform of the actual row coefficient is the
FULL original correlation times the genuine finite quotient cardinality. -/
theorem probeNegativeGaussPairResidue_divisorFourier (h : Principal u v) :
    sIntegerPeriodicDivisorFourier K S P.arithmetic.different_outside
        ((Subtype.val u) * (Subtype.val v)) (mul_ne_zero (Subtype.property u) (Subtype.property v))
        (probeNegativeGaussPairResidue K S P I J) 1 h =
      (Fintype.card (Total u v) : ℂ) *
        sIntegerSexticOriginalFullQuotientCorrelation K S
          P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding
          (probeArithmetic_six_support K S P.arithmetic) u v
          ((originalFullTotalPrincipalEquiv K S u v).symm h) := by
  unfold sIntegerPeriodicDivisorFourier divisorTransform dilate
  simp only [map_one, one_mul]
  unfold probeNegativeGaussPairResidue
  rw [fourier_ringEquiv (originalFullTotalPrincipalEquiv K S u v)
    (sIntegerActualModulusAddCharacter K S P.arithmetic.different_outside
      ((Subtype.val u) * (Subtype.val v))
      (mul_ne_zero (Subtype.property u) (Subtype.property v)))
    (fun a => HeckeGeneral.Arithmetic.PeriodicFourier.fourier
      (originalFullPositiveTraceCharacter K S P.arithmetic.different_outside u v)
      (sIntegerSexticOriginalFullQuotientCorrelation K S
        P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding
        (probeArithmetic_six_support K S P.arithmetic) u v) (-a)) h]
  exact fourier_negative_fourier _
    (originalFullPositiveTraceCharacter_isPrimitive K S
      P.arithmetic.different_outside u v) _ _

/-- On S-integer representatives the output is literally F(u,v;h). -/
theorem probeNegativeGaussPairResidue_divisorFourier_mk (h : R) :
    sIntegerPeriodicDivisorFourier K S P.arithmetic.different_outside
        ((Subtype.val u) * (Subtype.val v)) (mul_ne_zero (Subtype.property u) (Subtype.property v))
        (probeNegativeGaussPairResidue K S P I J) 1 (Ideal.Quotient.mk _ h) =
      (Fintype.card (Total u v) : ℂ) *
        sIntegerSexticOriginalFullCorrelation K S
          P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding
          (probeArithmetic_six_support K S P.arithmetic) u v h := by
  rw [probeNegativeGaussPairResidue_divisorFourier]
  have he : (originalFullTotalPrincipalEquiv K S u v).symm (Ideal.Quotient.mk _ h) =
      Ideal.Quotient.mk _ h := by
    apply (originalFullTotalPrincipalEquiv K S u v).injective
    simp only [RingEquiv.apply_symm_apply, originalFullTotalPrincipalEquiv,
      Ideal.quotEquivOfEq_mk]
  rw [he, sIntegerSexticOriginalFullQuotientCorrelation_mk]

/-- Cardinality uses the actual S-local product norm; no normalization is
assumed for Haar measure or for the generator. -/
theorem probePair_card_eq_modulusNorm :
    (Fintype.card (Total u v) : ℂ) =
      ((sIntegerElementNorm K S
        ⟨(Subtype.val u) * (Subtype.val v), mul_ne_zero (Subtype.property u) (Subtype.property v)⟩).val : ℂ) := by
  have hcard : (Fintype.card (Total u v) : ℝ) =
      (sIntegerElementNorm K S
        ⟨(Subtype.val u) * (Subtype.val v), mul_ne_zero (Subtype.property u) (Subtype.property v)⟩).val := by
    rw [Fintype.card_congr (originalFullTotalPrincipalEquiv K S u v).toEquiv,
      ← Nat.card_eq_fintype_card]
    exact natCard_sIntegerPrincipalResidue_eq_productNorm K S _ _
  exact_mod_cast hcard

/-- Cancelling the finite Fourier cardinality against the Poisson modulus
factor leaves Q, with the field/discriminant factor D still explicit. This
identity does not perform or assume the infinite Poisson interchange. -/
theorem probePair_poisson_prefactor (Q D : ℂ) :
    (Q * D * ((sIntegerElementNorm K S
        ⟨(Subtype.val u) * (Subtype.val v), mul_ne_zero (Subtype.property u) (Subtype.property v)⟩).val : ℂ)⁻¹) *
        (Fintype.card (Total u v) : ℂ) = Q * D := by
  rw [probePair_card_eq_modulusNorm]
  have hnorm : ((sIntegerElementNorm K S
      ⟨(Subtype.val u) * (Subtype.val v), mul_ne_zero (Subtype.property u) (Subtype.property v)⟩).val : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (sIntegerElementNorm K S
      ⟨(Subtype.val u) * (Subtype.val v), mul_ne_zero (Subtype.property u) (Subtype.property v)⟩).property
  rw [mul_assoc, inv_mul_cancel₀ hnorm, mul_one]

end HeckeGeneral.ThetaSkeleton.Physical.ActualProbePairFourierDraft
