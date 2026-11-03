import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TailsOriginalBounds
import HeckeGeneral.Arithmetic.SIntegerOrbitCounting

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Actual first frequency windows and finite row counts

The physical cutoff is the maximum over the nonzero original pair
profiles. Its bound therefore uses the proved active whole-ideal
windows even when the public Cartesian source contains zero columns.
The original subgroup orbit count retains every unit sector.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

theorem maskGenerator_norm_mono (S : Finset (HeightOneSpectrum (𝓞 K)))
    [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
    (D M : Finset (HeightOneSpectrum
      (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K))) (hDM : D ⊆ M) :
    (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val ≤
    (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) M)).val := by
  have hdiv :
      (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D).val ∣
        (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) M).val := by
    change IdealMobiusMask.maskGenerator D ∣ IdealMobiusMask.maskGenerator M
    rw [IdealMobiusMask.maskGenerator_dvd_iff, IdealMobiusMask.mem_primeProduct]
    have hmem := (IdealMobiusMask.maskGenerator_dvd_iff M
      (IdealMobiusMask.maskGenerator M)).mp (dvd_refl _)
    rw [IdealMobiusMask.mem_primeProduct] at hmem
    exact fun p hp => hmem p (hDM hp)
  exact tailsV2_sIntegerElementNorm_le_of_dvd S _ _ _ _ hdiv

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable (F : FirstPresentation call p) (hF : F.Realizes)

include hF in
/-- The actual squarefree divisor count is paid by its mask norm. -/
theorem first_mask_powerset_card (input : ProfileInput call)
    (hlarge : originalThreshold c call.frame ≤ call.base)
    (v : F.source.CommonLabel) (i : F.source.Column)
    (hi : i ∈ (F.source.source v).leftColumns) (hci : F.coefficient i ≠ 0) :
    (((F.source.source v).mask.powerset).card : ℝ) ≤
      call.base ^ originalColumnExponent c :=
  (mask_powerset_card_le_generator_norm (K := K) (S := (Arithmetic.data c).Sf)
    (F.source.source v).mask).trans
      (first_mask_norm_le F hF input hlarge v i hi hci)

include hF in
theorem first_pair_inverse_dual_radius_le (input : ProfileInput call)
    (hlarge : originalThreshold c call.frame ≤ call.base)
    (v : F.source.CommonLabel) (i : F.source.Column)
    (hi : i ∈ (F.source.source v).leftColumns) (j : F.source.Column)
    (hj : j ∈ (F.source.source v).rightColumns)
    (hprofile : ((F.source.source v).pairs i j).profile ≠ 0)
    (D : Finset (HeightOneSpectrum (Arithmetic.data c).R))
    (hD : D ∈ (F.source.source v).mask.powerset) :
    (((F.source.source v).pairs i j).dualRadius (F.source.source v).radius D).val⁻¹ ≤
      call.base ^ (3 * originalColumnExponent c) := by
  have hc := first_profile_nonzero_coefficients F hF i j hprofile
  have hmask := (maskGenerator_norm_mono (K := K) (Arithmetic.data c).Sf
    D (F.source.source v).mask (Finset.mem_powerset.mp hD)).trans
      (first_mask_norm_le F hF input hlarge v i hi hc.1)
  have hmod := first_modulus_norm_le F hF input hlarge v i hi j hj hc.1 hc.2
  simp only [ParentPeriodicPair.dualRadius, sIntegerMaskDualRadius,
    sIntegerMaskDilationRadius, inv_inv]
  calc
    _ ≤ (1 * call.base ^ originalColumnExponent c) *
        call.base ^ (2 * originalColumnExponent c) :=
      mul_le_mul
        (mul_le_mul (first_radius_le_one F hF) hmask
          (sIntegerElementNorm K _ (sIntegerMaskGenerator K _ D)).property.le zero_le_one)
        hmod
        (sIntegerElementNorm K _
          ⟨((F.source.source v).pairs i j).modulus,
            ((F.source.source v).pairs i j).modulus_ne_zero⟩).property.le
        (mul_nonneg zero_le_one (Real.rpow_nonneg call.base_pos.le _))
    _ = _ := by
      rw [one_mul, ← Real.rpow_add call.base_pos]
      congr 1
      ring

include hF in
theorem first_inverseRadiusBound_le (input : ProfileInput call)
    (hlarge : originalThreshold c call.frame ≤ call.base)
    (v : F.source.CommonLabel) :
    (F.source.source v).inverseRadiusBound ≤
      call.base ^ (3 * originalColumnExponent c) := by
  apply Finset.sup'_le
  intro r hr
  rcases Finset.mem_insert.mp hr with hr | hr
  · simpa only [id_eq, hr] using Real.rpow_nonneg call.base_pos.le
      (3 * originalColumnExponent c)
  · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨hem, hep⟩ := Finset.mem_filter.mp he
    obtain ⟨hij, hD⟩ := Finset.mem_product.mp hem
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hij
    exact first_pair_inverse_dual_radius_le F hF input hlarge v
      e.1.1 hi e.1.2 hj hep e.2 hD

include hF in
theorem first_divisorInverseRadiusBound_le (input : ProfileInput call)
    (hlarge : originalThreshold c call.frame ≤ call.base)
    (v : F.source.CommonLabel)
    (D : Finset (HeightOneSpectrum (Arithmetic.data c).R))
    (hD : D ∈ (F.source.source v).mask.powerset) :
    (F.source.source v).divisorInverseRadiusBound D ≤
      call.base ^ (3 * originalColumnExponent c) := by
  apply Finset.sup'_le
  intro r hr
  rcases Finset.mem_insert.mp hr with hr | hr
  · simpa only [id_eq, hr] using Real.rpow_nonneg call.base_pos.le
      (3 * originalColumnExponent c)
  · obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨hmem, hprofile⟩ := Finset.mem_filter.mp hij
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hmem
    exact first_pair_inverse_dual_radius_le F hF input hlarge v
      ij.1 hi ij.2 hj hprofile D hD

def firstRowExponent (c : TargetContext K) (p : SourceParameters c) : ℝ :=
  p.firstCutoffExponent + 3 * originalColumnExponent c

theorem firstRowExponent_nonneg (c : TargetContext K) (p : SourceParameters c) :
    0 ≤ firstRowExponent c p :=
  add_nonneg p.firstCutoff_pos.le
    (mul_nonneg (by norm_num) (originalColumnExponent_nonneg c))

include hF in
theorem first_physicalCutoff_le (input : ProfileInput call)
    (hlarge : originalThreshold c call.frame ≤ call.base) (v : F.source.CommonLabel) :
    (F.source.source v).physicalCutoff ≤ call.base ^ firstRowExponent c p := by
  calc
    _ ≤ p.firstCutoff call * call.base ^ (3 * originalColumnExponent c) :=
      mul_le_mul_of_nonneg_left (first_inverseRadiusBound_le F hF input hlarge v)
        (zero_le_one.trans (p.firstCutoff_one call))
    _ = _ := by
      change call.base ^ p.firstCutoffExponent * call.base ^
        (3 * originalColumnExponent c) = _
      rw [← Real.rpow_add call.base_pos]
      rfl

include hF in
theorem first_divisorPhysicalCutoff_le (input : ProfileInput call)
    (hlarge : originalThreshold c call.frame ≤ call.base) (v : F.source.CommonLabel)
    (D : Finset (HeightOneSpectrum (Arithmetic.data c).R))
    (hD : D ∈ (F.source.source v).mask.powerset) :
    (F.source.source v).divisorPhysicalCutoff D ≤ call.base ^ firstRowExponent c p := by
  calc
    _ ≤ p.firstCutoff call * call.base ^ (3 * originalColumnExponent c) :=
      mul_le_mul_of_nonneg_left
        (first_divisorInverseRadiusBound_le F hF input hlarge v D hD)
        (zero_le_one.trans (p.firstCutoff_one call))
    _ = _ := by
      change call.base ^ p.firstCutoffExponent * call.base ^
        (3 * originalColumnExponent c) = _
      rw [← Real.rpow_add call.base_pos]
      rfl

/-- This constant belongs to the fixed field and subgroup. -/
def orbitRowConstant (c : TargetContext K) : ℝ :=
  Classical.choose (exists_card_boundedSIntegerOrbits_le K
    ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
    (Arithmetic.unitSubgroup c))

theorem orbitRowConstant_pos (c : TargetContext K) : 0 < orbitRowConstant c :=
  (Classical.choose_spec (exists_card_boundedSIntegerOrbits_le K
    ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
    (Arithmetic.unitSubgroup c))).1

theorem finite_orbit_rows_card (c : TargetContext K)
    (rows : Finset (SIntegerOrbits K
      ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
      (Arithmetic.unitSubgroup c))) (H : ℝ) (hH : 0 ≤ H)
    (hrows : ∀ q ∈ rows,
      (sIntegerOrbitNorm K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
        (Arithmetic.unitSubgroup c) q).val ≤ H) :
    (rows.card : ℝ) ≤ orbitRowConstant c * (1 + H) := by
  let embed : rows → BoundedSIntegerOrbits K
      ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
      (Arithmetic.unitSubgroup c) H :=
    fun q => ⟨q.val, hrows q.val q.property⟩
  have hinj : Function.Injective embed := by
    intro q q' hq
    apply Subtype.ext
    exact congrArg
      (fun z : BoundedSIntegerOrbits K
        ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
        (Arithmetic.unitSubgroup c) H => z.val) hq
  have hn := Nat.card_le_card_of_injective embed hinj
  have hn' : rows.card ≤ Nat.card (BoundedSIntegerOrbits K
      ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
      (Arithmetic.unitSubgroup c) H) := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hn
  have hc := (Classical.choose_spec (exists_card_boundedSIntegerOrbits_le K
    ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
    (Arithmetic.unitSubgroup c))).2 H hH
  exact (Nat.cast_le.mpr hn').trans hc

include hF in
theorem first_divisorRows_card (input : ProfileInput call)
    (hlarge : originalThreshold c call.frame ≤ call.base) (v : F.source.CommonLabel)
    (D : Finset (HeightOneSpectrum (Arithmetic.data c).R))
    (hD : D ∈ (F.source.source v).mask.powerset) :
    (((F.source.source v).divisorRows D).card : ℝ) ≤
      (2 * orbitRowConstant c) * call.base ^ firstRowExponent c p := by
  have hcut := first_divisorPhysicalCutoff_le F hF input hlarge v D hD
  have hrows := finite_orbit_rows_card c ((F.source.source v).divisorRows D)
    (call.base ^ firstRowExponent c p) (Real.rpow_nonneg call.base_pos.le _)
    (fun q hq => (((F.source.source v).mem_divisorRows D q).mp hq).trans hcut)
  have hp : 1 ≤ call.base ^ firstRowExponent c p :=
    Real.one_le_rpow call.domain.scale.le (firstRowExponent_nonneg c p)
  calc
    _ ≤ orbitRowConstant c * (1 + call.base ^ firstRowExponent c p) := hrows
    _ ≤ orbitRowConstant c * (2 * call.base ^ firstRowExponent c p) :=
      mul_le_mul_of_nonneg_left (by linarith) (orbitRowConstant_pos c).le
    _ = _ := by ring

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.first_pair_inverse_dual_radius_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.first_divisorPhysicalCutoff_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.first_divisorRows_card

