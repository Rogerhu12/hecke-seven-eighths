import Expansion.PhysicalRecipePresentation
import Expansion.ActualShiftedRecipeIntegrability

/-!
# Actual integrability and label identities for the same physical recipe

The original zero detector supplies the finite rectangle needed for the
selected line.  Thus each original row kernel and each transported label
integrand is absolutely integrable, including at scales where the recipe
uses its default witnesses.  The identities below apply to the unchanged
scheduled block data and have no integrability or target estimate inputs.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ExpansionRecipe
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.HighBinActualEuler ExpansionInterfaces
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))

variable [∀ p : HeightOneSpectrum (𝓞 K), MeasurableSpace (p.adicCompletion K)]
variable [∀ p : HeightOneSpectrum (𝓞 K), BorelSpace (p.adicCompletion K)]
variable (mu : ∀ p : HeightOneSpectrum (𝓞 K), Measure (p.adicCompletion K))
variable [∀ p, (mu p).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
variable [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (nu : Measure (FiniteAdeleRing (𝓞 K) K)) [nu.IsAddHaarMeasure]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
local notation "muS" => (fun p : Sset => mu p.val)

variable (P : ProbeData K (S : Set (HeightOneSpectrum (𝓞 K)))) (omega psi : HeckeCharacter K)
variable (hAllowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) P.arithmetic)
variable (g : PrimeWindowGeometry) (ray : Finset (HeckeCharacter K))
variable {B e : ℝ} (hpsi : psi ∈ HeckePacket K omega)
variable (hB0 : 51 / 100 ≤ B) (hB : B ≤ 1) (he : 0 < e) (he1 : e ≤ 1 / 10000)
variable (hbound : ∀ chi r, r ∈ heckePacketZeros K omega chi →
  1 / 2 ≤ r → r ≤ 1 → r ≤ B)
local notation "E" => arithmeticHighEulerData K Sset P psi

include nu hAllowed he1 in
/-- The selected original row is integrable on its actual final box.
Its finite-height zero predicate is already part of the fixed selector. -/
theorem integrable_actual_physicalRecipeRow (zeta Z T : ℝ)
    (hZ : 1 < Z) (hT : 0 ≤ T)
    (j : Fin (shellCount Z (1 / 16) (13 / 16 + zeta)))
    (c : PhysicalRecipeChoice K Sset B e) (u : FrequencyRow K Sset)
    (hu : u ∈ physicalRecipeRows K Sset P E omega psi hpsi hB0 hB he hbound zeta Z T j c) :
    IntegrableOn (rowVerticalKernel K Sset muS P psi E g ray u Z
      (c.1.center + 16 * e) (1 - c.1.center - 6 * e) (17 / 50))
      (rowRetainedHeightBox T) rowHeightVolume := by
  have hr := physicalRecipeRows_spec K Sset P E omega psi hpsi hB0 hB he hbound
    zeta Z T hZ j c u hu
  have ha := rowBufferIndex_center_range hB0 he c.1
  have hTH : T ≤ upperHeight (c.1.1.val + 1) T := by
    unfold upperHeight
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg c.1.1.val : (0 : ℝ) ≤ c.1.1.val) hT]
  exact integrableOn_actual_shifted_rowVerticalKernel_box K S mu nu P psi hAllowed
    g ray u
    (physicalRecipeRows_nonprincipal K Sset P E omega psi hpsi hB0 hB he hbound
      zeta Z T j c u hu)
    (zero_lt_one.trans hZ) ha.1 (ha.2.trans hB) he he1 hTH hr.2.2.2.2

include nu hAllowed he1 in
/-- Each actual moving-label integrand is Bochner integrable.  Its
receiving rows and sample are read from the same scheduled block. -/
theorem integrable_actual_physicalRecipeLabel (lam zeta width k : ℝ) (hw : 0 < width)
    (Z T : ℝ) (hZ : 1 < Z) (hT : 0 ≤ T)
    (j : Fin (shellCount Z (1 / 16) (13 / 16 + zeta)))
    (c : PhysicalRecipeChoice K Sset B e)
    (label : AmplitudeLabels g.slots width ((2 * c.1.center - 1) / 2))
    (u : FrequencyRow K Sset) :
    IntegrableOn
      (physicalBlockLabelIntegrand (P := P) (R := E.rows) (ω := omega)
        width ((2 * c.1.center - 1) / 2) Z
        (physicalRecipeRows K Sset P E omega psi hpsi hB0 hB he hbound zeta Z T j c)
        (physicalRecipeScheduledBlock K Sset P omega psi g E hpsi hB0 hB he hbound
          muS ray lam zeta width k hw Z T j c)
        (amplitudeLabels_card_le_fixed g.slots hw (physicalRecipeChoice_cap K Sset hB0 hB he c))
        (physicalContourKernel K Sset muS P psi E g ray Z
          (c.1.center + 16 * e) (1 - c.1.center - 6 * e) (17 / 50)) label u)
      {p : Fin 3 → ℝ | ‖p‖ ≤ T} physicalHeightVolume := by
  apply physicalBlockLabelIntegrand_integrable (measurable_physicalRecipeSlotPower K psi g)
    width ((2 * c.1.center - 1) / 2) Z T _ _ _ physicalHeightVolume _
  intro v hv
  exact physicalContourKernel_integrable K Sset muS P psi E g ray Z T
    (c.1.center + 16 * e) (1 - c.1.center - 6 * e) (17 / 50) hT v
    (integrable_actual_physicalRecipeRow K S mu nu P omega psi hAllowed g ray
      hpsi hB0 hB he he1 hbound zeta Z T hZ hT j c v hv)

include nu hAllowed he1 in
/-- Every retained label is an actual transported contribution, and their
sum is exactly the original fixed-row contour value at every active scale. -/
theorem actual_physicalRecipeShiftedPiece_sum (lam zeta width k : ℝ) (hw : 0 < width)
    (Z T : ℝ) (hZ : 1 < Z) (hT : 0 ≤ T)
    (j : Fin (shellCount Z (1 / 16) (13 / 16 + zeta)))
    (c : PhysicalRecipeChoice K Sset B e) :
    (∑ l ∈ physicalRecipeRetainedLabels K Sset hB0 hB he g width hw c,
      ∑ u ∈ ((physicalRecipeScheduledBlock K Sset P omega psi g E hpsi hB0 hB he hbound
        muS ray lam zeta width k hw Z T j c).amplitude l).rows
          (Z ^ shellExponent Z (1 / 16) j.val),
        physicalRecipeShiftedPiece K Sset P E omega psi hpsi hB0 hB he hbound g
          muS ray lam zeta width k hw Z T j c l u) =
      physicalRecipeBlockValue K Sset P E omega psi hpsi hB0 hB he hbound
        muS g ray zeta Z T j c := by
  apply physicalRecipeShiftedPiece_sum K Sset P E omega psi hpsi hB0 hB he hbound
    g muS ray lam zeta width k hw Z T hZ hT j c
  exact integrable_actual_physicalRecipeRow K S mu nu P omega psi hAllowed g ray
    hpsi hB0 hB he he1 hbound zeta Z T hZ hT j c

include nu hAllowed he1 in
/-- The unchanged value field of the same actual source block is its
retained-label integral sum.  Default witnesses require no exception. -/
theorem actual_physicalRecipeScheduledBlock_identification
    (lam zeta width k : ℝ) (hw : 0 < width)
    (Z T : ℝ) (hZ : 1 < Z) (hT : 0 ≤ T)
    (j : Fin (shellCount Z (1 / 16) (13 / 16 + zeta)))
    (c : PhysicalRecipeChoice K Sset B e) :
    (physicalRecipeScheduledBlock K Sset P omega psi g E hpsi hB0 hB he hbound
      muS ray lam zeta width k hw Z T j c).value =
      ∑ l ∈ physicalRecipeRetainedLabels K Sset hB0 hB he g width hw c,
        ∑ u ∈ ((physicalRecipeScheduledBlock K Sset P omega psi g E hpsi hB0 hB he hbound
          muS ray lam zeta width k hw Z T j c).amplitude l).rows
            (Z ^ shellExponent Z (1 / 16) j.val),
          physicalRecipeShiftedPiece K Sset P E omega psi hpsi hB0 hB he hbound g
            muS ray lam zeta width k hw Z T j c l u := by
  apply physicalRecipeScheduledBlock_identification K Sset P E omega psi hpsi hB0 hB he hbound
    g muS ray lam zeta width k hw Z T hZ hT j c
  exact integrable_actual_physicalRecipeRow K S mu nu P omega psi hAllowed g ray
    hpsi hB0 hB he he1 hbound zeta Z T hZ hT j c

end Expansion.Project

#print axioms Expansion.Project.integrable_actual_physicalRecipeRow
#print axioms Expansion.Project.integrable_actual_physicalRecipeLabel
#print axioms Expansion.Project.actual_physicalRecipeShiftedPiece_sum
#print axioms Expansion.Project.actual_physicalRecipeScheduledBlock_identification
