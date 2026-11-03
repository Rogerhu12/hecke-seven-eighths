import HeckeGeneral.Analysis.SixthPowerFreeDecomposition
import HeckeGeneral.Analysis.FrequencyRowOrbit
import HeckeGeneral.Analysis.ActualSIntegerAmplifierMask

/-!
Every actual S-integer orbit has a unique complete exterior ideal and unit
sector when the preferred generator is gen(base(I))*gen(amplifier(I))^6.
All sixth-power descendants and every original unit sector are retained.
This arithmetic reindexing does not supply source moment admissibility.
-/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.ActualSIntegerMoments HeckeGeneral.ThetaSkeleton.Global
open scoped Classical nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S)

/-- The actual contraction is exterior, for every original unit sector. -/
def actualOrbitExteriorIdeal (q : ActualSIntegerOrbit K S) : ExteriorIdeal K S :=
  ⟨actualSIntegerOrbitIdeal K S q, by
    refine Quotient.inductionOn q ?_
    intro a p hp hpin
    have hcop := sIntegerModulusContraction_coprime K S a.val a.property p hpin
    have hle := Ideal.dvd_iff_le.mp hp
    exact p.isPrime.ne_top ((sup_of_le_right hle).symm.trans hcop)⟩

/-- For a fixed sector, all complete ideals are indexed, including descendants. -/
def decomposedFrequencyRow (I : ExteriorIdeal K S) (ξ : SixthUnitClasses K S) :
    FrequencyRow K S where
  ideal := exteriorSixthPowerFreePart S I
  sixthPowerFree := (sixthPowerFreeIdeal_iff_primeExponents_lt _).mp
    (sixthPowerFreePart_isSixthPowerFree I.val)
  sector := ξ

def decomposedIdealSectorOrbit (x : ExteriorIdeal K S × SixthUnitClasses K S) :
    ActualSIntegerOrbit K S :=
  actualSimultaneousAmplifier K S P.arithmetic
    (frequencyRowOrbit K S P (decomposedFrequencyRow K S x.1 x.2))
    (exteriorSixthPowerAmplifierPart S x.1)

theorem decomposedIdealSectorOrbit_ideal (x : ExteriorIdeal K S × SixthUnitClasses K S) :
    actualSIntegerOrbitIdeal K S (decomposedIdealSectorOrbit K S P x) = x.1.val := by
  rw [decomposedIdealSectorOrbit, actualSimultaneousAmplifier_ideal,
    frequencyRowOrbit_ideal]
  exact exteriorSixthPowerFree_decomposition S x.1

theorem decomposedIdealSectorOrbit_norm (x : ExteriorIdeal K S × SixthUnitClasses K S) :
    actualSIntegerOrbitNorm K S (decomposedIdealSectorOrbit K S P x) =
      idealNorm K x.1.val := by
  rw [actualSIntegerOrbitNorm_eq_absNorm_contraction]
  change ((actualSIntegerOrbitIdeal K S (decomposedIdealSectorOrbit K S P x)).val.absNorm : ℝ) = _
  rw [decomposedIdealSectorOrbit_ideal]
  rfl

theorem decomposedIdealSectorOrbit_injective :
    Function.Injective (decomposedIdealSectorOrbit K S P) := by
  intro x y h
  have hI : x.1 = y.1 := by
    apply Subtype.ext
    have hi := congrArg (actualSIntegerOrbitIdeal K S) h
    simpa only [decomposedIdealSectorOrbit_ideal] using hi
  have hp := (frequencyRowAmplifierEmbedding K S P).injective
    (a₁ := (decomposedFrequencyRow K S x.1 x.2, exteriorSixthPowerAmplifierPart S x.1))
    (a₂ := (decomposedFrequencyRow K S y.1 y.2, exteriorSixthPowerAmplifierPart S y.1)) h
  have hξ : x.2 = y.2 := congrArg (fun z => z.1.sector) hp
  exact Prod.ext hI hξ

theorem decomposedIdealSectorOrbit_surjective :
    Function.Surjective (decomposedIdealSectorOrbit K S P) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro a
  let I := actualOrbitExteriorIdeal K S (Quotient.mk _ a)
  let B := exteriorSixthPowerFreePart S I
  let A := exteriorSixthPowerAmplifierPart S I
  let b : S.integer K := P.arithmetic.generator B * P.arithmetic.generator A ^ 6
  have hspan : Ideal.span ({b} : Set (S.integer K)) =
      Ideal.span ({a.val} : Set (S.integer K)) := by
    change Ideal.span ({P.arithmetic.generator B * P.arithmetic.generator A ^ 6} :
      Set (S.integer K)) = _
    rw [← Ideal.span_singleton_mul_span_singleton,
      ← Ideal.span_singleton_pow, P.arithmetic.generator_span,
      P.arithmetic.generator_span, ← Ideal.map_pow, ← Ideal.map_mul]
    have hI := congrArg (fun J : NonzeroIdeal K => J.val)
      (exteriorSixthPowerFree_decomposition S I)
    change B.val.val * A.val.val ^ 6 = sIntegerModulusContraction K S a.val at hI
    rw [hI, map_sIntegerModulusContraction]
  obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  let u : S.unit K := (S.unitEquivUnitsInteger K).symm v
  let ξ : SixthUnitClasses K S := QuotientGroup.mk' (sixthPowerSUnitSubgroup K S) u
  have hξ : QuotientGroup.mk' (sixthPowerSUnitSubgroup K S) (Quotient.out ξ) =
      QuotientGroup.mk' (sixthPowerSUnitSubgroup K S) u := Quotient.out_eq ξ
  obtain ⟨γ, hγ, hγu⟩ :=
    (QuotientGroup.mk'_eq_mk' (sixthPowerSUnitSubgroup K S)).mp hξ
  refine ⟨(I, ξ), ?_⟩
  symm
  apply Quotient.sound
  apply (sIntegerOrbitRelation_iff K S (sixthPowerSUnitSubgroup K S) _ _).mpr
  refine ⟨⟨γ, hγ⟩, ?_⟩
  have huv : S.unitEquivUnitsInteger K u = v :=
    (S.unitEquivUnitsInteger K).apply_symm_apply v
  have hfield : (b : K) * (((u : Kˣ) : K)) = (a.val : K) := by
    have h := congrArg (fun c : S.integer K => (c : K)) hv
    rw [← huv] at h
    exact h
  have hγfield : (((Quotient.out ξ : S.unit K) : Kˣ) : K) *
      ((γ : Kˣ) : K) = ((u : Kˣ) : K) :=
    congrArg (fun c : S.unit K => ((c : Kˣ) : K)) hγu
  change ((γ : Kˣ) : K) *
      ((P.arithmetic.generator A : K) ^ 6 *
        ((((Quotient.out ξ : S.unit K) : Kˣ) : K) *
          (P.arithmetic.generator B : K))) = (a.val : K)
  calc
    _ = (b : K) * ((((Quotient.out ξ : S.unit K) : Kˣ) : K) * ((γ : Kˣ) : K)) := by
      change _ = ((P.arithmetic.generator B : K) * (P.arithmetic.generator A : K) ^ 6) * _
      ring
    _ = (b : K) * ((u : Kˣ) : K) := by rw [hγfield]
    _ = _ := hfield

/-- Exact reindexing, rather than a bound that discards unit sectors. -/
def exteriorIdealSectorsEquivActualOrbits :
    (ExteriorIdeal K S × SixthUnitClasses K S) ≃ ActualSIntegerOrbit K S :=
  Equiv.ofBijective (decomposedIdealSectorOrbit K S P)
    ⟨decomposedIdealSectorOrbit_injective K S P,
      decomposedIdealSectorOrbit_surjective K S P⟩

/-- The descendant's original deletion is retained in the literal symbol. -/
theorem actualOrbitSexticEvaluation_decomposedIdealSector
    (I : NonzeroIdeal K) (x : ExteriorIdeal K S × SixthUnitClasses K S) :
    actualOrbitSexticEvaluation K S P.arithmetic.root6 P.arithmetic.primitive6
        P.arithmetic.embedding I (decomposedIdealSectorOrbit K S P x) =
      actualOrbitSexticEvaluation K S P.arithmetic.root6 P.arithmetic.primitive6
        P.arithmetic.embedding I
        (frequencyRowOrbit K S P (decomposedFrequencyRow K S x.1 x.2)) *
      (if IsCoprime I.val (sixthPowerAmplifierPart x.1.val).val then 1 else 0) := by
  exact actualOrbitSexticEvaluation_simultaneousAmplifier_product K S
    P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding P.arithmetic I _ _

end HeckeGeneral.ThetaSkeleton.Physical
