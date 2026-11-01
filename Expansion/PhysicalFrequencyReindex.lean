import Expansion.PhysicalFinitePoisson
import HeckeGeneral.Analysis.SIntegerSixthPowerDecomposition
import HeckeGeneral.Characters.UnramifiedPrimeCoefficientAlgebra
import RowCharacterNormTwistExclusion

/-!
# Every actual Fourier orbit, and the unique principal row

The existing sixth-power decomposition makes the physical row/amplifier
embedding a genuine equivalence.  Thus no sector or sixth-power descendant
is omitted.  The later interchange of its two infinite indices is justified
by the actual Schwartz Fourier tensor's proved summability.

The canonical principal row has unit ideal and trivial original unit sector.
Its actual arithmetic character is proved trivial from the allowed generator
and global finite-order character uniqueness, rather than supplied as data.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Project

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Bridge
open HeckeGeneral.Characters.ArithmeticKummerDraft
open HeckeGeneral.Characters.RowUniquenessDraft
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualAbsolute
open Expansion.PhysicalFourierNormalization Expansion.PhysicalFinitePoisson
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

section Arithmetic

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The one principal physical row; the original sector is literally one. -/
def physicalPrincipalRow : FrequencyRow K S where
  ideal := ⟨1, by
    intro p hp
    change p.asIdeal ∣ (1 : Ideal (𝓞 K)) at hp
    rw [Ideal.one_eq_top] at hp
    exact False.elim (p.isPrime.ne_top
      (eq_top_iff.mpr (Ideal.dvd_iff_le.mp hp)))⟩
  sixthPowerFree := by
    intro p
    simp only [primeExponents_one, Finsupp.zero_apply]
    norm_num
  sector := 1

@[simp] theorem physicalPrincipalRow_principal :
    principalFrequencyRow K S (physicalPrincipalRow K S) := ⟨rfl, rfl⟩

theorem principalFrequencyRow_iff_eq_physicalPrincipalRow (u : FrequencyRow K S) :
    principalFrequencyRow K S u ↔ u = physicalPrincipalRow K S := by
  constructor
  · intro hu
    rcases u with ⟨⟨I, hI⟩, hfree, ξ⟩
    change I = 1 ∧ ξ = 1 at hu
    rcases hu with ⟨rfl, rfl⟩
    rfl
  · rintro rfl
    exact physicalPrincipalRow_principal K S

theorem existsUnique_principalFrequencyRow :
    ∃! u : FrequencyRow K S, principalFrequencyRow K S u := by
  refine ⟨physicalPrincipalRow K S, physicalPrincipalRow_principal K S, ?_⟩
  intro u hu
  exact (principalFrequencyRow_iff_eq_physicalPrincipalRow K S u).mp hu

@[simp] theorem physicalPrincipalRow_norm :
    frequencyRowNorm K S (physicalPrincipalRow K S) = 1 := by
  simp [frequencyRowNorm, exteriorNorm, physicalPrincipalRow]

@[simp] theorem physicalPrincipalRow_support :
    exteriorSupport K S (physicalPrincipalRow K S).ideal = ∅ := by
  simp [exteriorSupport, idealPrimeSupport, physicalPrincipalRow]

theorem frequencyRowNorm_eq_one_of_principal (u : FrequencyRow K S)
    (hu : principalFrequencyRow K S u) : frequencyRowNorm K S u = 1 := by
  rw [(principalFrequencyRow_iff_eq_physicalPrincipalRow K S u).mp hu]
  exact physicalPrincipalRow_norm K S

theorem exteriorSupport_eq_empty_of_principal (u : FrequencyRow K S)
    (hu : principalFrequencyRow K S u) : exteriorSupport K S u.ideal = ∅ := by
  rw [(principalFrequencyRow_iff_eq_physicalPrincipalRow K S u).mp hu]
  exact physicalPrincipalRow_support K S

/-- An arbitrary chosen representative of the principal sector is a sixth
power of an original S-unit, as is the allowed unit-ideal generator. -/
theorem frequencyRowElement_eq_sixth_power_of_principal (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic) (u : FrequencyRow K S)
    (hu : principalFrequencyRow K S u) :
    ∃ v : S.unit K,
      frequencyRowElement K S P u = (S.unitEquivUnitsInteger K v).val ^ 6 := by
  obtain ⟨δ, hδ⟩ := AllowedGeneratorInput.generator_eq_sixth_power_of_ideal_eq_one
    K S P.arithmetic hP u.ideal hu.1
  have hmk : QuotientGroup.mk' (sixthPowerSUnitSubgroup K S)
      (Quotient.out u.sector) = 1 := (Quotient.out_eq u.sector).trans hu.2
  have hmem := (QuotientGroup.eq_one_iff (Quotient.out u.sector)).mp hmk
  obtain ⟨ε, hε⟩ := hmem
  change ε ^ 6 = Quotient.out u.sector at hε
  refine ⟨ε * δ, ?_⟩
  simp only [frequencyRowElement, hδ, ← hε, map_pow, map_mul,
    Units.val_pow_eq_pow_val, Units.val_mul, mul_pow]

/-- Forward principal-row detection for the original arithmetic constructor.
The finite exceptional set in global uniqueness is precisely the fixed S. -/
theorem arithmeticRowCharacter_eq_one_of_principal (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic) (u : FrequencyRow K S)
    (hu : principalFrequencyRow K S u) : arithmeticRowCharacter K S P u = 1 := by
  let hS : S.Finite := Set.toFinite S
  apply finiteOrder_heckeCharacter_eq_of_primeCoefficient_eq_away K
    (arithmeticRowCharacter K S P u) 1
    (arithmeticRowCharacter_finiteOrder K S P u) IsOfFinOrder.one hS.toFinset
  intro p hp
  have hpS : p ∉ S := fun h => hp (hS.mem_toFinset.mpr h)
  let b := arithmeticRowIntegralRepresentative K S P u
  obtain ⟨γ, hrep⟩ := b.property.2
  have hpa : ¬p.asIdeal ∣ sIntegerModulusContraction K S
      (frequencyRowElement K S P u) := by
    rw [frequencyRowElement_contraction]
    intro hd
    rw [hu.1] at hd
    change p.asIdeal ∣ (1 : Ideal (𝓞 K)) at hd
    rw [Ideal.one_eq_top] at hd
    exact p.isPrime.ne_top (eq_top_iff.mpr (Ideal.dvd_iff_le.mp hd))
  have hcal := arithmeticSexticKummerCharacter_primeCoefficient_sInteger K S
    P.arithmetic (frequencyRowElement K S P u) (frequencyRowElement_ne_zero K S P u)
    b.val b.property.1 γ hrep p hpS hpa
  change primeCoefficient K (arithmeticRowCharacter K S P u) p = _ at hcal
  rw [hcal, primeCoefficient_one]
  obtain ⟨v, hv⟩ := frequencyRowElement_eq_sixth_power_of_principal K S P hP u hu
  rw [hv]
  exact sIntegerSexticEvaluation_sixth_power_unit K S p hpS P.arithmetic.root6
    P.arithmetic.primitive6 P.arithmetic.embedding (P.arithmetic.away_six p hpS) v

@[simp] theorem physicalPrincipalRow_character (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic) :
    arithmeticRowCharacter K S P (physicalPrincipalRow K S) = 1 :=
  arithmeticRowCharacter_eq_one_of_principal K S P hP _
    (physicalPrincipalRow_principal K S)

theorem rowCharacterInput_eq_one_of_principal (P : ProbeData K S)
    (R : RowCharacterInput K S P) (hP : AllowedGeneratorInput K S P.arithmetic)
    (u : FrequencyRow K S) (hu : principalFrequencyRow K S u) : R.character u = 1 := by
  rw [rowCharacterInput_character_eq_arithmetic]
  exact arithmeticRowCharacter_eq_one_of_principal K S P hP u hu

theorem frequencyRowAmplifierEmbedding_surjective (P : ProbeData K S) :
    Function.Surjective (frequencyRowAmplifierEmbedding K S P) := by
  intro q
  obtain ⟨x, hx⟩ := decomposedIdealSectorOrbit_surjective K S P q
  exact ⟨(decomposedFrequencyRow K S x.1 x.2,
    exteriorSixthPowerAmplifierPart S x.1), hx⟩

/-- All original nonzero frequencies, with unique base row and amplifier. -/
def physicalFrequencyEquiv (P : ProbeData K S) :
    (FrequencyRow K S × ExteriorIdeal K S) ≃ ActualSIntegerOrbit K S :=
  Equiv.ofBijective (frequencyRowAmplifierEmbedding K S P)
    ⟨(frequencyRowAmplifierEmbedding K S P).injective,
      frequencyRowAmplifierEmbedding_surjective K S P⟩

theorem poissonFrequency_ne_zero (P : ProbeData K S)
    (u : FrequencyRow K S) (r : ExteriorIdeal K S) : poissonFrequency K S P u r ≠ 0 :=
  mul_ne_zero (frequencyRowElement_ne_zero K S P u)
    (pow_ne_zero 6 (P.arithmetic.generator_ne_zero r))

theorem physicalFrequencyEquiv_eq_mk (P : ProbeData K S)
    (u : FrequencyRow K S) (r : ExteriorIdeal K S) :
    physicalFrequencyEquiv K S P (u, r) =
      Quotient.mk _ ⟨poissonFrequency K S P u r, poissonFrequency_ne_zero K S P u r⟩ := by
  change Quotient.mk _
    (sIntegerNonzeroMul K S (actualAmplifierElement K S P.arithmetic r)
      ⟨frequencyRowElement K S P u, frequencyRowElement_ne_zero K S P u⟩) = _
  apply congrArg (Quotient.mk _)
  apply Subtype.ext
  exact mul_comm _ _

theorem physicalFrequencyEquiv_norm (P : ProbeData K S)
    (u : FrequencyRow K S) (r : ExteriorIdeal K S) :
    actualSIntegerOrbitNorm K S (physicalFrequencyEquiv K S P (u, r)) =
      frequencyRowNorm K S u * exteriorNorm K S r ^ 6 := by
  change actualSIntegerOrbitNorm K S
    (actualSimultaneousAmplifier K S P.arithmetic (frequencyRowOrbit K S P u) r) = _
  rw [actualSimultaneousAmplifier_norm, frequencyRowOrbit_norm]
  rfl

theorem gaussSymbolOrbitWeight_mk (P : ProbeData K S) (den A : ExteriorIdeal K S)
    (m : NonzeroRingElements (S.integer K)) :
    gaussSymbolOrbitWeight K S P den A (Quotient.mk _ m) =
      probeGauss K S P den (-m.val) * idealSymbol K S P.arithmetic A m.val := by
  have h := congrFun (periodicOrbitWeight_eq K S P den A) (Quotient.mk _ m)
  rw [sIntegerPeriodicOrbitWeight_mk, principalPoissonCoefficient_mk] at h
  exact h.symm

theorem finitePoissonOrbitWeight_mk (P : ProbeData K S) (den A : ExteriorIdeal K S)
    (m : NonzeroRingElements (S.integer K)) :
    finitePoissonOrbitWeight K S P den A (Quotient.mk _ m) =
      finitePoissonFactor K S P den A m.val := by
  have h := congrFun (periodicFourierOrbitWeight_eq K S P den A) (Quotient.mk _ m)
  rw [sIntegerPeriodicFourierOrbitWeight_mk, principalDivisorFourier_eq_norm_mul] at h
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (idealNorm_pos K den.val).ne') h.symm

theorem finitePoissonOrbitWeight_frequency (P : ProbeData K S)
    (den A : ExteriorIdeal K S) (u : FrequencyRow K S) (r : ExteriorIdeal K S) :
    finitePoissonOrbitWeight K S P den A (physicalFrequencyEquiv K S P (u, r)) =
      finitePoissonFactor K S P den A (poissonFrequency K S P u r) := by
  rw [physicalFrequencyEquiv_eq_mk]
  exact finitePoissonOrbitWeight_mk K S P den A
    ⟨poissonFrequency K S P u r, poissonFrequency_ne_zero K S P u r⟩

end Arithmetic

section FourierSeries

variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Γ" => sixthPowerUnits K Sset

local instance : (Γ).FiniteIndex := sUnit_power_range_finiteIndex K Sset 6 (by decide)

variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
  [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]

/-- The literal Fourier coefficient and genuine common radial profile,
with both physical indices visible. -/
def physicalFrequencyProfileTerm (P : ProbeData K Sset) (den A : ExteriorIdeal K Sset)
    (ρ : {r : ℝ // 0 < r}) (u : FrequencyRow K Sset) (r : ExteriorIdeal K Sset) : ℂ :=
  finitePoissonFactor K Sset P den A (poissonFrequency K Sset P u r) *
    sUnitOrbitalProfile K Sset (additiveFourier K Sset (fun v => μv v.val) P.additive)
      ⟨ρ.val * (frequencyRowNorm K Sset u * exteriorNorm K Sset r ^ 6),
        mul_pos ρ.property (mul_pos (idealNorm_pos K u.ideal.val)
          (pow_pos (idealNorm_pos K r.val) 6))⟩

theorem physicalFrequencyProfileTerm_eq_orbit (P : ProbeData K Sset)
    (den A : ExteriorIdeal K Sset) (ρ : {r : ℝ // 0 < r})
    (u : FrequencyRow K Sset) (r : ExteriorIdeal K Sset) :
    physicalFrequencyProfileTerm K S μv P den A ρ u r =
      finitePoissonOrbitWeight K Sset P den A (physicalFrequencyEquiv K Sset P (u, r)) *
        sUnitOrbitalProfile K Sset
          (additiveFourier K Sset (fun v => μv v.val) P.additive)
          ⟨ρ.val * (sIntegerOrbitNorm K Sset Γ (physicalFrequencyEquiv K Sset P (u, r))).val,
            mul_pos ρ.property (sIntegerOrbitNorm K Sset Γ _).property⟩ := by
  rw [finitePoissonOrbitWeight_frequency]
  unfold physicalFrequencyProfileTerm
  have hn : (sIntegerOrbitNorm K Sset Γ (physicalFrequencyEquiv K Sset P (u, r))).val =
      frequencyRowNorm K Sset u * exteriorNorm K Sset r ^ 6 :=
    physicalFrequencyEquiv_norm K Sset P u r
  simp only [hn]

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]

include ν in
/-- Actual absolute convergence follows from Fourier closure and the
finite Gauss-symbol bound.  It is not an added convergence hypothesis. -/
theorem summable_physicalFourierOrbitSeries (P : ProbeData K Sset)
    (den A : ExteriorIdeal K Sset) (ρ : {r : ℝ // 0 < r}) :
    Summable (fun q : ActualSIntegerOrbit K Sset =>
      finitePoissonOrbitWeight K Sset P den A q *
        sUnitOrbitalProfile K Sset
          (additiveFourier K Sset (fun v => μv v.val) P.additive)
          ⟨ρ.val * (sIntegerOrbitNorm K Sset Γ q).val,
            mul_pos ρ.property (sIntegerOrbitNorm K Sset Γ q).property⟩) := by
  have hft := sIntegerFiniteFourierTestFunction_locallyConstant_compactSupport K S ν μv
    (finiteExtension K S P.additive)
    (finiteExtension_locallyConstant K S P.additive)
    (finiteExtension_compactSupport K S P.additive)
  rw [additiveFourier_eq_tensor]
  exact (hasSum_sIntegerOrbitalProfile_weighted K Sset Γ
    (traceSchwartzFourier K P.additive.infiniteTest)
    (sIntegerFiniteFourierTestFunction K S μv (finiteExtension K S P.additive))
    hft.1.continuous hft.2 ρ (finitePoissonOrbitWeight K Sset P den A)
    (exteriorNorm K Sset den * exteriorNorm K Sset A)
    (fun q => norm_finitePoissonFactor_le K Sset P den A q.out.val)).summable

include ν in
theorem summable_physicalFrequencyProfileTerm (P : ProbeData K Sset)
    (den A : ExteriorIdeal K Sset) (ρ : {r : ℝ // 0 < r}) :
    Summable (fun x : FrequencyRow K Sset × ExteriorIdeal K Sset =>
      physicalFrequencyProfileTerm K S μv P den A ρ x.1 x.2) := by
  have h := (physicalFrequencyEquiv K Sset P).summable_iff.mpr
    (summable_physicalFourierOrbitSeries K S μv ν P den A ρ)
  exact h.congr (fun x => (physicalFrequencyProfileTerm_eq_orbit K S μv P den A ρ x.1 x.2).symm)

include ν in
/-- Exact reindexing to rows and all amplifier ideals, after proving
summability of the double series. -/
theorem physicalFourierOrbitSeries_eq_rows (P : ProbeData K Sset)
    (den A : ExteriorIdeal K Sset) (ρ : {r : ℝ // 0 < r}) :
    weightedPhysicalOrbitalSeries K S Γ
        (additiveFourier K Sset (fun v => μv v.val) P.additive) ρ
        (finitePoissonOrbitWeight K Sset P den A) =
      ∑' u : FrequencyRow K Sset, ∑' r : ExteriorIdeal K Sset,
        physicalFrequencyProfileTerm K S μv P den A ρ u r := by
  have hsum := summable_physicalFrequencyProfileTerm K S μv ν P den A ρ
  rw [← hsum.tsum_prod]
  unfold weightedPhysicalOrbitalSeries
  calc
    _ = ∑' x : FrequencyRow K Sset × ExteriorIdeal K Sset,
        finitePoissonOrbitWeight K Sset P den A (physicalFrequencyEquiv K Sset P x) *
          sUnitOrbitalProfile K Sset
            (additiveFourier K Sset (fun v => μv v.val) P.additive)
            ⟨ρ.val * (sIntegerOrbitNorm K Sset Γ (physicalFrequencyEquiv K Sset P x)).val,
              mul_pos ρ.property (sIntegerOrbitNorm K Sset Γ _).property⟩ :=
      ((physicalFrequencyEquiv K Sset P).tsum_eq _).symm
    _ = _ := tsum_congr (fun x =>
      (physicalFrequencyProfileTerm_eq_orbit K S μv P den A ρ x.1 x.2).symm)

end FourierSeries

end Expansion.Project

#print axioms Expansion.Project.arithmeticRowCharacter_eq_one_of_principal
#print axioms Expansion.Project.physicalFourierOrbitSeries_eq_rows
