import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.S3PoolData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondData

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# First-row exponents from the physical windows

The finite supremum includes the unit bound, so an empty first row set
has exponent zero.  A nonempty row set uses its actual retained cutoff.
The original joint row/mask budget also shows that charging the full
old support leaves a nonnegative working row exponent.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.S3

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

theorem rowExponent_le_of_rows (source : PhysicalSource call p)
    {B : ℝ} (hB : 0 ≤ B)
    (hrows : ∀ h ∈ source.source.rows,
      (Arithmetic.data c).exteriorNorm (originalFrequencyIdeal h) ≤ call.base ^ B) :
    source.rowExponent ≤ B := by
  apply (Real.rpow_le_rpow_left_iff call.domain.scale).mp
  rw [rpow_rowExponent]
  apply max_le (Real.one_le_rpow call.domain.scale.le hB)
  let bound : NNReal := ⟨call.base ^ B, Real.rpow_nonneg call.base_pos.le B⟩
  have hsup : source.source.rows.sup (fun h =>
      (⟨(Arithmetic.data c).exteriorNorm (originalFrequencyIdeal h),
        ((Arithmetic.data c).exteriorNorm_pos (originalFrequencyIdeal h)).le⟩ : NNReal)) ≤
      bound := by
    apply Finset.sup_le
    intro h hh
    exact hrows h hh
  exact_mod_cast hsup

theorem rowExponent_le_window (source : PhysicalSource call p)
    (windows : source.Windows) :
    source.rowExponent ≤ max 0
      (source.firstFrequency + 4 * p.loss +
        source.first.tag.padding (recipeInductionSigma c)) := by
  apply rowExponent_le_of_rows source (le_max_left _ _)
  intro h hh
  have hret := windows.retained_upper ⟨h, hh⟩
  change source.first.retainedScale ≤
    call.base ^ (source.firstFrequency + 4 * p.loss) at hret
  calc
    _ ≤ source.first.retainedScale *
        call.base ^ source.first.tag.padding (recipeInductionSigma c) :=
      windows.row_upper h hh
    _ ≤ call.base ^ (source.firstFrequency + 4 * p.loss) *
        call.base ^ source.first.tag.padding (recipeInductionSigma c) :=
      mul_le_mul_of_nonneg_right hret (Real.rpow_nonneg call.base_pos.le _)
    _ = call.base ^ (source.firstFrequency + 4 * p.loss +
        source.first.tag.padding (recipeInductionSigma c)) :=
      (Real.rpow_add call.base_pos _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le call.domain.scale.le (le_max_right _ _)

theorem supportLength_le_width (active : call.Active) :
    call.supportLength ≤ call.node.parameters.m + call.node.parameters.q := by
  obtain ⟨u, hu⟩ := active
  have hbudget := call.source.pairedJointBudget u hu
  have hsupport := call.localizedSource.source.recipe.moving.effectiveFullSupport_norm_le
    call.localizedSource.source.recipe.remaining
  change (Arithmetic.data c).exteriorNorm call.oldSupport ≤
    idealNorm K (call.source.source.recipe.moving.fullMaskSupport
      call.source.source.recipe.remaining) at hsupport
  have hnorm : (Arithmetic.data c).exteriorNorm call.oldSupport ≤
      call.base ^ (call.node.parameters.m + call.node.parameters.q) :=
    hsupport.trans ((le_mul_of_one_le_left (idealNorm_pos K _).le
      (one_le_idealNorm K u)).trans hbudget)
  apply (Real.rpow_le_rpow_left_iff call.domain.scale).mp
  have hlog : call.base ^ call.supportLength =
      (Arithmetic.data c).exteriorNorm call.oldSupport :=
    rpow_idealLogLength call.base call.domain.scale _ call.oldSupport.property.1
  rw [hlog]
  exact hnorm

theorem working_m_nonneg (active : call.Active) :
    0 ≤ call.workingParameters.m := by
  change 0 ≤ call.node.parameters.m + call.node.parameters.q - call.supportLength
  exact sub_nonneg.mpr (supportLength_le_width active)

theorem working_totalLength_le :
    call.workingParameters.n₁ + call.workingParameters.n₂ + call.workingParameters.z ≤
      2 + recipeInductionSigma c / 16 := by
  have hcore := call.domain.padded_core
  have hwidth := call.width_le
  change call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z ≤ _
  linarith

theorem firstFrequency_le_of_common_lengths (source : PhysicalSource call p)
    (active : call.Active)
    (hcommon : idealLogLength call.base
        (firstActiveRadical source.first.selected.val source.first.opposite.val) +
        idealLogLength call.base source.first.complementary.val ≤
      idealLogLength call.base source.first.selected.val +
        idealLogLength call.base source.first.opposite.val) :
    source.firstFrequency ≤ 4 + recipeInductionSigma c / 8 := by
  have hm := working_m_nonneg active
  have hlength := working_totalLength_le (call := call)
  unfold PhysicalSource.firstFrequency
  linarith

theorem cauchy_rowExponent_le_of_common_lengths {F : FirstPresentation call p}
    {family : FirstCauchyFamily F} (realized : family.Realizes)
    (active : call.Active) (i : Fin family.count)
    (windows : (family.source i).Windows)
    (hcommon : idealLogLength call.base
        (firstActiveRadical (family.source i).first.selected.val
          (family.source i).first.opposite.val) +
        idealLogLength call.base (family.source i).first.complementary.val ≤
      idealLogLength call.base (family.source i).first.selected.val +
        idealLogLength call.base (family.source i).first.opposite.val) :
    (family.source i).rowExponent ≤
      4 + recipeInductionSigma c / 8 + 4 * p.loss + recipeInductionSigma c := by
  have hrow := rowExponent_le_window (family.source i) windows
  rw [realized.tag i] at hrow
  change (family.source i).rowExponent ≤
    max 0 ((family.source i).firstFrequency + 4 * p.loss + recipeInductionSigma c) at hrow
  apply hrow.trans
  apply max_le
  · have hs := (recipeInduction_budget (c := c)).1
    have hloss := p.loss_pos
    linarith
  · have hf := firstFrequency_le_of_common_lengths (family.source i) active hcommon
    linarith

theorem firstPhysicalDivisorIdeal_eq_under {A : SArithmeticData K}
    [IsPrincipalIdealRing A.R] (D : Finset (HeightOneSpectrum A.R)) :
    (firstPhysicalDivisorIdeal (A := A) D).val =
      (IdealMobiusMask.primeProduct D).under (𝓞 K) := by
  let delta := sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D
  have hspan : A.extendIdeal (firstPhysicalDivisorIdeal (A := A) D) =
      IdealMobiusMask.primeProduct D := by
    change A.extendIdeal (originalFrequencyIdeal (A := A) delta.val) = _
    exact (originalFrequencyIdeal_generates (A := A) delta.val delta.property).2.symm.trans
      (Ideal.span_singleton_generator _)
  calc
    _ = (A.extendIdeal (firstPhysicalDivisorIdeal (A := A) D)).under (𝓞 K) :=
      (SIntegerLocalization.under_map_exterior A.Sf _
        (firstPhysicalDivisorIdeal (A := A) D).property.2).symm
    _ = _ := congrArg (fun I : Ideal A.R => I.under (𝓞 K)) hspan

theorem firstPhysicalDivisorIdeal_dvd_product {A : SArithmeticData K}
    [IsPrincipalIdealRing A.R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (primes : ι → ExteriorPrime A) (multiplicity : ι → ℕ)
    (positive : ∀ i, 0 < multiplicity i) (D : Finset (HeightOneSpectrum A.R))
    (hD : D ⊆ Finset.univ.image (fun i => actualExteriorSPrime (primes i))) :
    (firstPhysicalDivisorIdeal (A := A) D).val ∣ (primePowerProduct primes multiplicity).val := by
  apply Ideal.dvd_iff_le.mpr
  rw [firstPhysicalDivisorIdeal_eq_under]
  intro a ha
  change algebraMap (𝓞 K) A.R a ∈ IdealMobiusMask.primeProduct D
  rw [IdealMobiusMask.mem_primeProduct]
  intro q hq
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (hD hq)
  change algebraMap (𝓞 K) A.R a ∈
    (primes i).val.asIdeal.map (algebraMap (𝓞 K) A.R)
  apply Ideal.mem_map_of_mem
  have hd : (primes i).val.asIdeal ∣ (primePowerProduct primes multiplicity).val := by
    change (primes i).val.asIdeal ∣ ∏ j, (primes j).val.asIdeal ^ multiplicity j
    exact (dvd_pow_self _ (Nat.ne_of_gt (positive i))).trans
      (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  exact (Ideal.dvd_iff_le.mp hd) ha

theorem idealLogLength_le_of_dvd {I J : Ideal (𝓞 K)}
    (hI : I ≠ 0) (hJ : J ≠ 0) (hIJ : I ∣ J) :
    idealLogLength call.base I ≤ idealLogLength call.base J := by
  apply (Real.rpow_le_rpow_left_iff call.domain.scale).mp
  rw [rpow_idealLogLength call.base call.domain.scale I hI,
    rpow_idealLogLength call.base call.domain.scale J hJ]
  exact HeckePort.Moments.norm_le_of_dvd hJ hIJ

theorem cauchy_complementary_dvd_opposite {F : FirstPresentation call p}
    (hF : F.Realizes) {family : FirstCauchyFamily F}
    (realized : family.Realizes) (i : Fin family.count) :
    (family.source i).first.complementary.val ∣ (family.source i).first.opposite.val := by
  let key := family.index i
  let b := FirstCauchyKey.block key
  have hD : key.2.1.val ⊆
      Finset.univ.image (fun j => actualExteriorSPrime (b.primes j)) := by
    have hsub := Finset.mem_powerset.mp key.2.1.property
    change key.2.1.val ⊆ F.source.mask ∪
      firstPrincipalPrimeMask b.primes b.leftMultiplicity b.rightMultiplicity at hsub
    have hprincipal : key.2.1.val ⊆
        firstPrincipalPrimeMask b.primes b.leftMultiplicity b.rightMultiplicity := by
      intro q hq
      rcases Finset.mem_union.mp (hsub hq) with hq | hq
      · have hempty : q ∈ (∅ : Finset (HeightOneSpectrum (Arithmetic.data c).R)) :=
          hF.mask ▸ hq
        exact (Finset.notMem_empty q hempty).elim
      · exact hq
    exact hprincipal.trans
      (Finset.image_mono (fun j => actualExteriorSPrime (b.primes j))
        (Finset.subset_univ _))
  have hleft := firstPhysicalDivisorIdeal_dvd_product b.primes b.leftMultiplicity
    b.left_positive key.2.1.val hD
  have hright := firstPhysicalDivisorIdeal_dvd_product b.primes b.rightMultiplicity
    b.right_positive key.2.1.val hD
  rw [b.common_left] at hleft
  rw [b.common_right] at hright
  rw [realized.complementary i, realized.opposite i]
  split_ifs
  · exact hleft
  · exact hright

theorem cauchy_common_lengths {F : FirstPresentation call p}
    (hF : F.Realizes) {family : FirstCauchyFamily F}
    (realized : family.Realizes) (i : Fin family.count) :
    idealLogLength call.base
        (firstActiveRadical (family.source i).first.selected.val
          (family.source i).first.opposite.val) +
        idealLogLength call.base (family.source i).first.complementary.val ≤
      idealLogLength call.base (family.source i).first.selected.val +
        idealLogLength call.base (family.source i).first.opposite.val := by
  apply add_le_add
  · apply idealLogLength_le_of_dvd
      (firstActiveRadical_ne_zero _ _)
      (nonZeroDivisors.coe_ne_zero (family.source i).first.selected)
    unfold firstActiveRadical
    exact support_product_dvd
      (nonZeroDivisors.coe_ne_zero (family.source i).first.selected)
      (Finset.filter_subset _ _)
  · exact idealLogLength_le_of_dvd
      (nonZeroDivisors.coe_ne_zero (family.source i).first.complementary)
      (nonZeroDivisors.coe_ne_zero (family.source i).first.opposite)
      (cauchy_complementary_dvd_opposite hF realized i)

theorem cauchy_rowExponent_le {F : FirstPresentation call p}
    (hF : F.Realizes) {family : FirstCauchyFamily F}
    (realized : family.Realizes) (i : Fin family.count)
    (windows : (family.source i).Windows) :
    (family.source i).rowExponent ≤
      4 + recipeInductionSigma c / 8 + 4 * p.loss + recipeInductionSigma c :=
  cauchy_rowExponent_le_of_common_lengths realized hF.active i windows
    (cauchy_common_lengths hF realized i)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.S3

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.S3.rowExponent_le_window
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.S3.working_m_nonneg
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.S3.cauchy_rowExponent_le_of_common_lengths
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.S3.cauchy_rowExponent_le
