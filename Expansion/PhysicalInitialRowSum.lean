import Expansion.PhysicalCompensatedInitial

/-!
# Absolute initial row integrals and the unique principal row

The full physical identity is now a genuinely summable sum of individual
row integrals.  Absolute norm-integral convergence survives every original
finite compensation and division by the original normalizers.  This lets
the actual unique principal row be split off before finite contour moves.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.PhysicalInitialMellin

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualAbsolute HeckeSkeleton.HighBinActualEuler
open HeckeSkeleton.Expansion.LargeRows Expansion.Project
open scoped Classical BigOperators

private theorem summable_integral_norm_finiteSum {ι κ : Type*} (s : Finset ι)
    (F : ι → κ → (Fin 3 → ℝ) → ℂ)
    (hF : ∀ i ∈ s, ∀ k, Integrable (F i k))
    (hs : ∀ i ∈ s, Summable (fun k => ∫ t : Fin 3 → ℝ, ‖F i k t‖)) :
    Summable (fun k => ∫ t : Fin 3 → ℝ, ‖∑ i ∈ s, F i k t‖) := by
  apply (summable_sum hs).of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _)
  intro k
  calc
    _ ≤ ∫ t : Fin 3 → ℝ, ∑ i ∈ s, ‖F i k t‖ :=
      integral_mono (integrable_finsetSum s (fun i hi => hF i hi k)).norm
        (integrable_finsetSum s (fun i hi => (hF i hi k).norm))
        (fun t => norm_sum_le _ _)
    _ = _ := integral_finsetSum s (fun i hi => (hF i hi k).norm)

private theorem summable_integral_norm_const_mul {κ : Type*}
    (F : κ → (Fin 3 → ℝ) → ℂ)
    (hs : Summable (fun k => ∫ t : Fin 3 → ℝ, ‖F k t‖)) (c : ℂ) :
    Summable (fun k => ∫ t : Fin 3 → ℝ, ‖c * F k t‖) := by
  simpa only [norm_mul, integral_const_mul] using hs.mul_left ‖c‖

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "FIdx" => FourIdealIndex K Sset

def physicalInitialRowMajorant (u : FrequencyRow K Sset) : ℝ :=
  frequencyRowNorm K Sset u ^ (-3 : ℝ) * ∑' I : FIdx, initialMajorant K Sset 5 5 3 I

theorem summable_physicalInitialRowMajorant : Summable (physicalInitialRowMajorant K S) :=
  (summable_frequencyRowNorm_rpow K Sset (p := -3) (by norm_num)).mul_right _

variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
  [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]

def physicalInitialRowAt (P : ProbeData K Sset) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K Sset)) (X Y Z : ℝ)
    (u : FrequencyRow K Sset) (t : Fin 3 → ℝ) : ℂ :=
  physicalInitialRowKernel K S μv P ψ Q X Y Z u
    (idealVerticalPoint 5 (t 0)) (idealVerticalPoint 5 (t 1)) (idealVerticalPoint 3 (t 2))

theorem norm_physicalInitialRowAt_le (P : ProbeData K Sset) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K Sset)) (X Y Z : ℝ)
    (u : FrequencyRow K Sset) (t : Fin 3 → ℝ) :
    ‖physicalInitialRowAt K S μv P ψ Q X Y Z u t‖ ≤
      ‖physicalInitialScalarAt K S μv P X Y Z t‖ * physicalInitialRowMajorant K S u := by
  have hn := (summable_norm_physicalInitialMellinTerm K S μv P ψ Q X Y Z t).prod_factor u
  have hb : Summable (fun I : FIdx =>
      ‖physicalInitialScalarAt K S μv P X Y Z t‖ * physicalInitialMajorant K S (u, I)) := by
    simpa only [physicalInitialMajorant, mul_assoc] using
      (summable_initialMajorant K Sset 5 5 3 (by norm_num) (by norm_num) (by norm_num)).mul_left
        (‖physicalInitialScalarAt K S μv P X Y Z t‖ * frequencyRowNorm K Sset u ^ (-3 : ℝ))
  unfold physicalInitialRowAt
  rw [physicalInitialRowKernel_eq_tsum]
  apply (norm_tsum_le_tsum_norm hn).trans
  have hh := hn.tsum_le_tsum
    (fun I => norm_physicalInitialMellinTerm_le K S μv P ψ Q X Y Z (u, I) t) hb
  simpa only [physicalInitialMajorant, physicalInitialRowMajorant, tsum_mul_left, mul_assoc] using hh

def compensatedInitialRowAt (P : ProbeData K Sset) (ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) (Z : ℝ)
    (u : FrequencyRow K Sset) (t : Fin 3 → ℝ) : ℂ :=
  compensatedInitialKernel K S μv P ψ g T Z u
    (idealVerticalPoint 5 (t 0)) (idealVerticalPoint 5 (t 1)) (idealVerticalPoint 3 (t 2))

def actualInitialRowAt (P : ProbeData K Sset) (ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) (Z : ℝ)
    (u : FrequencyRow K Sset) (t : Fin 3 → ℝ) : ℂ :=
  compensatedRowMellinKernel K Sset (fun v => μv v.val) P ψ
    (arithmeticHighEulerData K Sset P ψ) g T u Z
    (idealVerticalPoint 5 (t 0)) (idealVerticalPoint 5 (t 1)) (idealVerticalPoint 3 (t 2))

def actualInitialRowIntegral (P : ProbeData K Sset) (ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) (Z : ℝ)
    (u : FrequencyRow K Sset) : ℂ :=
  tripleMellinConstant * ∫ t : Fin 3 → ℝ, actualInitialRowAt K S μv P ψ g T Z u t

variable [IsTotallyComplex K]
  [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]

include ν in
theorem integrable_physicalInitialRowAt (P : ProbeData K Sset) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K Sset)) (X Y Z : ℝ)
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) (u : FrequencyRow K Sset) :
    Integrable (physicalInitialRowAt K S μv P ψ Q X Y Z u) := by
  have hm : AEStronglyMeasurable (physicalInitialRowAt K S μv P ψ Q X Y Z u) := by
    unfold physicalInitialRowAt
    simp_rw [physicalInitialRowKernel_eq_tsum]
    exact AEStronglyMeasurable.tsum (fun I =>
      (integrable_physicalInitialMellinTerm K S μv ν P ψ Q X Y Z hX hY hZ u I).aestronglyMeasurable)
  exact ((integrable_physicalInitialScalarAt K S μv ν P X Y Z hX hY hZ).norm.mul_const
    (physicalInitialRowMajorant K S u)).mono' hm
      (Filter.Eventually.of_forall (norm_physicalInitialRowAt_le K S μv P ψ Q X Y Z u))

include ν in
theorem summable_integral_norm_physicalInitialRowAt (P : ProbeData K Sset)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K Sset)) (X Y Z : ℝ)
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    Summable (fun u : FrequencyRow K Sset =>
      ∫ t : Fin 3 → ℝ, ‖physicalInitialRowAt K S μv P ψ Q X Y Z u t‖) := by
  apply ((summable_physicalInitialRowMajorant K S).mul_left
    (∫ t : Fin 3 → ℝ, ‖physicalInitialScalarAt K S μv P X Y Z t‖)).of_nonneg_of_le
      (fun _ => integral_nonneg fun _ => norm_nonneg _)
  intro u
  rw [← integral_mul_const]
  exact integral_mono
    (integrable_physicalInitialRowAt K S μv ν P ψ Q X Y Z hX hY hZ u).norm
    ((integrable_physicalInitialScalarAt K S μv ν P X Y Z hX hY hZ).norm.mul_const _)
    (norm_physicalInitialRowAt_le K S μv P ψ Q X Y Z u)

include ν in
theorem compensatedInitialRowAt_absolute (P : ProbeData K Sset) (ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) {Z : ℝ} (hZ : 0 < Z) :
    (∀ u : FrequencyRow K Sset, Integrable (compensatedInitialRowAt K S μv P ψ g T Z u)) ∧
    Summable (fun u : FrequencyRow K Sset =>
      ∫ t : Fin 3 → ℝ, ‖compensatedInitialRowAt K S μv P ψ g T Z u t‖) := by
  let Jset := (Finset.univ : Finset (Fin g.slots)).powerset
  let Pset := Fintype.piFinset (fun i => primeWindow K Sset g T Z i)
  let row (p : Fin g.slots → ExteriorPrime K Sset) (J : Finset (Fin g.slots))
      (u : FrequencyRow K Sset) := physicalInitialRowAt K S μv P ψ ((Finset.univ \ J).image p)
    (physicalCompensationX K S g Z p J) (physicalCompensationY K S g Z p J)
    (physicalCompensationZ K S g Z p J) u
  have hrow p J u : Integrable (row p J u) :=
    integrable_physicalInitialRowAt K S μv ν P ψ _ _ _ _
      (physicalCompensationX_pos K S g hZ p J) (physicalCompensationY_pos K S g hZ p J)
      (physicalCompensationZ_pos K S g hZ p J) u
  have hrows p J : Summable (fun u => ∫ t : Fin 3 → ℝ, ‖row p J u t‖) :=
    summable_integral_norm_physicalInitialRowAt K S μv ν P ψ _ _ _ _
      (physicalCompensationX_pos K S g hZ p J) (physicalCompensationY_pos K S g hZ p J)
      (physicalCompensationZ_pos K S g hZ p J)
  let inner p u t := ∑ J ∈ Jset, physicalCompensationCoefficient K S ψ g p J * row p J u t
  have hi p u : Integrable (inner p u) :=
    integrable_finsetSum Jset (fun J _ => (hrow p J u).const_mul _)
  have his p : Summable (fun u => ∫ t : Fin 3 → ℝ, ‖inner p u t‖) :=
    summable_integral_norm_finiteSum Jset
      (fun J u t => physicalCompensationCoefficient K S ψ g p J * row p J u t)
      (fun J _ u => (hrow p J u).const_mul _)
      (fun J _ => summable_integral_norm_const_mul (row p J) (hrows p J) _)
  let outer u t := ∑ p ∈ Pset,
    (∏ i : Fin g.slots, windowWeight K Sset g Z i (p i)) * inner p u t
  have ho u : Integrable (outer u) :=
    integrable_finsetSum Pset (fun p _ => (hi p u).const_mul _)
  have hos : Summable (fun u => ∫ t : Fin 3 → ℝ, ‖outer u t‖) :=
    summable_integral_norm_finiteSum Pset
      (fun p u t => (∏ i : Fin g.slots, windowWeight K Sset g Z i (p i)) * inner p u t)
      (fun p _ u => (hi p u).const_mul _)
      (fun p _ => summable_integral_norm_const_mul (inner p) (his p) _)
  let D : ℂ := physicalResidueNormalizer K Sset (fun v => μv v.val) P * primeNormalizer K Sset g T Z
  have he u t : compensatedInitialRowAt K S μv P ψ g T Z u t = outer u t / D := rfl
  constructor
  · intro u
    rw [funext (he u)]
    exact (ho u).div_const D
  · simp_rw [he, div_eq_mul_inv, norm_mul, integral_mul_const]
    exact hos.mul_right ‖D⁻¹‖

theorem actualInitialRowAt_eq_compensated (P : ProbeData K Sset)
    (hP : AllowedGeneratorInput K Sset P.arithmetic) (ψ : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hψ : ∀ p : ExteriorPrime K Sset, UnramifiedAt K ψ p.val)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) (Z : ℝ)
    (u : FrequencyRow K Sset) (t : Fin 3 → ℝ) :
    actualInitialRowAt K S μv P ψ g T Z u t = compensatedInitialRowAt K S μv P ψ g T Z u t :=
  (compensatedInitialKernel_eq_actual K S μv P hP ψ hcal hψ g T Z u
    (idealVerticalPoint 5 (t 0)) (idealVerticalPoint 5 (t 1)) (idealVerticalPoint 3 (t 2))
    (by norm_num) (by norm_num) (by norm_num)).symm

include ν in
theorem actualInitialRows_absolute (P : ProbeData K Sset)
    (hP : AllowedGeneratorInput K Sset P.arithmetic) (ψ : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hψ : ∀ p : ExteriorPrime K Sset, UnramifiedAt K ψ p.val)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) {Z : ℝ} (hZ : 0 < Z) :
    (∀ u : FrequencyRow K Sset, Integrable (actualInitialRowAt K S μv P ψ g T Z u)) ∧
    Summable (fun u : FrequencyRow K Sset =>
      ∫ t : Fin 3 → ℝ, ‖actualInitialRowAt K S μv P ψ g T Z u t‖) := by
  have he (u : FrequencyRow K Sset) :
      actualInitialRowAt K S μv P ψ g T Z u = compensatedInitialRowAt K S μv P ψ g T Z u :=
    funext (actualInitialRowAt_eq_compensated K S μv P hP ψ hcal hψ g T Z u)
  simp_rw [he]
  exact compensatedInitialRowAt_absolute K S μv ν P ψ g T hZ

include ν in
theorem summable_actualInitialRowIntegral (P : ProbeData K Sset)
    (hP : AllowedGeneratorInput K Sset P.arithmetic) (ψ : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hψ : ∀ p : ExteriorPrime K Sset, UnramifiedAt K ψ p.val)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) {Z : ℝ} (hZ : 0 < Z) :
    Summable (actualInitialRowIntegral K S μv P ψ g T Z) := by
  have hs := (actualInitialRows_absolute K S μv ν P hP ψ hcal hψ g T hZ).2
  exact (hs.of_norm_bounded (fun u => norm_integral_le_integral_norm _)).mul_left tripleMellinConstant

variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
theorem normalizedProbe_eq_sum_actualInitialRowIntegral (P : ProbeData K Sset)
    (hzero : additiveFourierAtZero K Sset (fun v => μv v.val) P.additive = 0)
    (hP : AllowedGeneratorInput K Sset P.arithmetic) (ψ : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hψ : ∀ p : ExteriorPrime K Sset, UnramifiedAt K ψ p.val)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) {Z : ℝ} (hZ : 0 < Z) :
    normalizedProbe K Sset (fun v => μv v.val) P ψ g T Z =
      ∑' u : FrequencyRow K Sset, actualInitialRowIntegral K S μv P ψ g T Z u := by
  obtain ⟨hi, hs⟩ := actualInitialRows_absolute K S μv ν P hP ψ hcal hψ g T hZ
  have he := integral_tsum_of_summable_integral_norm hi hs
  rw [normalizedProbe_eq_actual_initial_rows K S μv ν μ P hzero hP ψ hcal hψ g T hZ]
  change tripleMellinConstant * (∫ t : Fin 3 → ℝ, ∑' u : FrequencyRow K Sset,
    actualInitialRowAt K S μv P ψ g T Z u t) = _
  rw [← he]
  exact tsum_mul_left.symm

include ν μ in
/-- The principal contribution is the unique actual unit ideal/unit sector
row; every nonprincipal frequency is retained in the summable complement. -/
theorem normalizedProbe_eq_principal_add_nonprincipal (P : ProbeData K Sset)
    (hzero : additiveFourierAtZero K Sset (fun v => μv v.val) P.additive = 0)
    (hP : AllowedGeneratorInput K Sset P.arithmetic) (ψ : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hψ : ∀ p : ExteriorPrime K Sset, UnramifiedAt K ψ p.val)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) {Z : ℝ} (hZ : 0 < Z) :
    normalizedProbe K Sset (fun v => μv v.val) P ψ g T Z =
      actualInitialRowIntegral K S μv P ψ g T Z (physicalPrincipalRow K Sset) +
        ∑' u : FrequencyRow K Sset,
          if principalFrequencyRow K Sset u then 0 else actualInitialRowIntegral K S μv P ψ g T Z u := by
  rw [normalizedProbe_eq_sum_actualInitialRowIntegral K S μv ν μ P hzero hP ψ hcal hψ g T hZ]
  simpa only [principalFrequencyRow_iff_eq_physicalPrincipalRow] using
    (summable_actualInitialRowIntegral K S μv ν P hP ψ hcal hψ g T hZ).tsum_eq_add_tsum_ite
      (physicalPrincipalRow K Sset)

end Expansion.PhysicalInitialMellin

#print axioms Expansion.PhysicalInitialMellin.actualInitialRows_absolute
#print axioms Expansion.PhysicalInitialMellin.normalizedProbe_eq_principal_add_nonprincipal
