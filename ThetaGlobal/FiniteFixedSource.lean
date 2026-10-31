import ThetaGlobal.FiniteProjectedFullSource
import DedekindZetaZeroFree.Theta.Profiles.CanonicalSphericalRealization
import DedekindZetaZeroFree.Theta.Periods.SphericalRealizationAndCommonGerms
import DedekindZetaZeroFree.Theta.Whittaker.FirstRootNondegeneracy
import DedekindZetaZeroFree.RepresentationTheory.Jacquet.ComplexWhittakerLine
import DedekindZetaZeroFree.HarmonicAnalysis.Haar.TraceCharactersAndGaussShifts

/-!
# The fixed actual projected source, retaining the full matrix product

The spherical normalization and finite projection keep the original core
map and local models.  This strengthens those constructive proofs by
retaining the full arbitrary-vector archimedean product.  The public
`source` is obtained by those proofs; its existence is not an input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section

namespace ThetaGlobal.FiniteFixedSource

open NumberField MeasureTheory DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources DedekindZetaZeroFree.ThetaExpansion
open DedekindZetaZeroFree.RootDerivatives
open DedekindZetaZeroFree.FourierContinuation.LiteralSource
open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

private theorem spherical_word_smul
    (R : PrincipalMellin.ActualRecipe S η) (c : ℂ) (f : Functions R)
    (w : List (Fin (KPContActualSphericalRightFieldIdentification.groupDimension F))) :
    KPContActualSphericalRightFieldIdentification.actualRightWord F R.A.zeta12 R.A.primitive_zeta12 w (c • f) =
      c • KPContActualSphericalRightFieldIdentification.actualRightWord F R.A.zeta12 R.A.primitive_zeta12 w f := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [KPContActualSphericalRightFieldIdentification.actualRightWord, ih]
    funext g
    simp only [KPContActualSphericalRightFieldIdentification.actualRight, Pi.smul_apply, smul_eq_mul]
    exact deriv_const_mul_field c

theorem normalized_spherical_factorization_full
    (R : PrincipalMellin.ActualRecipe S η) {N : TraceHaarTransport R}
    (A : JointExteriorCoefficientSources R N) (D : SphericalTransportData R A)
    (P : NormalizedSphericalTensor R A D) (L : SphericalFlatPreimages R A D P)
    (hNative : SourceNativeLie R A.factorization)
    (hFull : FiniteFullProduct.FullArchProduct R A.factorization)
    (hLocal : FiniteFullProduct.LocalArchRatio R A.factorization) :
    ∃ B : JointExteriorCoefficientSources R N, SourceNativeLie R B.factorization ∧
      FiniteFullProduct.FullArchProduct R B.factorization ∧
      FiniteFullProduct.LocalArchRatio R B.factorization ∧
      FiniteFullProduct.LocalWhittakerForms R B.factorization ∧ B.sources.dq = A.sources.dq ∧
      (∀ v, B.realization.theta v = tensorFunction R A.factorization D.tensor.stage P.entries) ∧
      (∀ v, (B.sources.flat v).val 0 ≠ 0) ∧
      (∀ v, B.realization.theta v ≠ 0) ∧
      (∀ v, fourier R B.sources.dq (B.realization.theta v) 1 ≠ 0) := by
  let B5 : JointRootAlignedSources R N := ⟨A.aligned, N, rfl, L.sources⟩
  obtain ⟨C, ⟨H⟩⟩ := selected_scalar_source_exists  R B5
  choose G hG using fun v => selected_source_smooth_germ_of_scalar_germ  R B5 C v (H v)
  let T := EisensteinSmoothGerms.assemble C G
  have hpin (v) : T.theta v = tensorFunction R A.factorization D.tensor.stage P.entries :=
    (funext (fun g => FlatScalarResidue.value_unique (realizationScalarResidue T v) (L.residue v) g)).trans
      (L.residue_exact v)
  have hscaled : T.theta 1 = P.scalar • D.tensor.value := (hpin 1).trans P.realization_exact
  have hspan : sphericalHCSpan R D.tensor.value ≤ hcHeckeSpan T := by
    apply Submodule.span_le.mpr
    rintro f ⟨a, w, rfl⟩
    have hm : KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12 a
        (KPContActualSphericalRightFieldIdentification.actualRightWord
          F R.A.zeta12 R.A.primitive_zeta12 w (T.theta 1)) ∈ hcHeckeSpan T :=
      Submodule.subset_span ⟨1, a, w, by
        have h : KPContActualSphericalRightFieldIdentification.actualRightWord
            F R.A.zeta12 R.A.primitive_zeta12 w (T.theta 1) =
            AdelicRightLieWords.actualRightWord
              F R.A.zeta12 R.A.primitive_zeta12 w (T.theta 1) := by
          induction w with
          | nil => rfl
          | cons b w ih =>
            simp only [KPContActualSphericalRightFieldIdentification.actualRightWord,
              AdelicRightLieWords.actualRightWord]
            rw [ih]
            rfl
        rw [h]⟩
    rw [hscaled, spherical_word_smul, map_smul] at hm
    have hi := Submodule.smul_mem (hcHeckeSpan T) P.scalar⁻¹ hm
    exact (by simpa only [smul_smul, inv_mul_cancel₀ P.scalar_nonzero, one_smul] using hi :
      KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12 a
        (KPContActualSphericalRightFieldIdentification.actualRightWord
          F R.A.zeta12 R.A.primitive_zeta12 w D.tensor.value) ∈ hcHeckeSpan T)
  let core := RestrictedTensorSimple.stageInclusion _ A.factorization.references A.factorization.bad
    D.tensor.stage (PiTensorProduct.tprod ℂ P.entries)
  let E : SourceFactorization R L.sources T := {
    finiteData := A.factorization.finiteData
    references := A.factorization.references
    bad := A.factorization.bad
    bad_exact := A.factorization.bad_exact
    ell := A.factorization.ell
    reference_value := A.factorization.reference_value
    scalarSlot := A.factorization.scalarSlot
    coreMap := A.factorization.coreMap
    selected := fun _ => core
    selected_eq := fun v => (hpin v).symm
    selected_frozen_stage := fun _ => ⟨D.tensor.stage, P.entries, D.tensor.stage_exact, rfl⟩
    core_injective := A.factorization.core_injective
    core_same_residue := fun x => ⟨hspan (D.core_generated x), (A.factorization.core_same_residue x).2⟩
    finite_intertwining := A.factorization.finite_intertwining
    complex_intertwining := A.factorization.complex_intertwining
    product_integrable := by rw [L.dq_exact]; exact A.factorization.product_integrable
    product_exact := by rw [L.dq_exact]; exact A.factorization.product_exact
    spherical_reference := A.factorization.spherical_reference
    detected_tensor := by rw [L.dq_exact]; exact A.factorization.detected_tensor
    period_integrable := fun v g => FourierContinuation.theta_period_integrable T v g
    detected := ⟨1, by rw [L.dq_exact, hpin]; exact P.period_nonzero⟩ }
  have hEfull : FiniteFullProduct.FullArchProduct R E := by
    simpa only [FiniteFullProduct.FullArchProduct, FiniteFullProduct.archRatio,
      FiniteCoreProduct.stageCoefficient, FiniteCoreProduct.stageFunction, E, L.dq_exact] using hFull
  have hElocal : FiniteFullProduct.LocalArchRatio R E := by
    simpa only [FiniteFullProduct.LocalArchRatio, FiniteFullProduct.archRatio,
      FiniteCoreProduct.stageCoefficient, FiniteCoreProduct.stageFunction, E, L.dq_exact] using hLocal
  have hEforms : FiniteFullProduct.LocalWhittakerForms R E := by
    intro w
    refine ⟨D.localForm w, ?_, D.restriction w⟩
    intro t v
    have hx := D.whittaker w (Multiplicative.ofAdd
      ((KPReferenceChange.StandardComplexImage.coordinate R.A w).symm t)) v
    change D.localForm w
        (KPActualReflectionData.StandardLocalSource.complexRootAction R.A w
          (Multiplicative.ofAdd
            ((KPReferenceChange.StandardComplexImage.coordinate R.A w).symm t)) v) =
      (KPActualReflectionData.StandardLocalSource.complexRawPsi w).toAddChar
        ((KPReferenceChange.StandardComplexImage.coordinate R.A w).symm t) *
          D.localForm w v at hx
    rw [KPActualReflectionData.StandardLocalSource.complexRootAction_apply,
      KPActualReflectionData.StandardLocalSource.complexRawPsi_trace,
      KPReferenceChange.StandardComplexImage.trace_character R.A w,
      (KPReferenceChange.StandardComplexImage.coordinate R.A w).apply_symm_apply t] at hx
    exact hx
  let B : JointExteriorCoefficientSources R N := {
    toJointRootAlignedSources := B5
    realization := T
    factorization := E
    localHaarTransport := ?_
    exterior := ⟨A.exterior.rational_exact, A.exterior.crt_product, A.exterior.local_exact⟩ }
  · refine ⟨B, hNative, hEfull, hElocal, hEforms, L.dq_exact, hpin, L.source_nonzero, ?_, ?_⟩
    · intro v
      rw [hpin]
      exact P.realization_nonzero
    · intro v
      rw [L.dq_exact, hpin]
      exact P.period_nonzero
  · intro q
    change N.finiteHaar q = ENNReal.ofReal (PoissonS.integerVolume F q) •
      (A.factorization.finiteData q).haar
    exact (congrArg (fun M : TraceHaarTransport R => M.finiteHaar q) A.transport_exact).symm.trans
      (A.localHaarTransport q)


theorem spherical_seed_full
    (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
    (A : JointExteriorCoefficientSources R N) (D : SphericalTransportData R A)
    (hNative : SourceNativeLie R A.factorization)
    (hFull : FiniteFullProduct.FullArchProduct R A.factorization)
    (hLocal : FiniteFullProduct.LocalArchRatio R A.factorization) :
    ∃ B : FirstRootSphericalSeed R N,
      SourceNativeLie R B.base.factorization ∧
      FiniteFullProduct.FullArchProduct R B.base.factorization ∧
      FiniteFullProduct.LocalArchRatio R B.base.factorization ∧
      FiniteFullProduct.LocalWhittakerForms R B.base.factorization := by
  obtain ⟨P⟩ := normalizedSphericalTensor_nonempty R A D
  obtain ⟨L⟩ := sphericalFlatPreimages_nonempty R A D P
  obtain ⟨B, hB, hF, hL, hForms, hdq, hpin, _, _, _⟩ :=
    normalized_spherical_factorization_full R A D P L hNative hFull hLocal
  let B' : FirstRootSphericalSeed R N := {
    base := B
    neighborhood := D.tensor.neighborhood
    open_neighborhood := D.tensor.open_neighborhood
    one_neighborhood := D.tensor.one_neighborhood
    spherical_near := by
      intro v y hy
      rw [hdq, hpin v]
      exact P.spherical_near y hy }
  exact ⟨B', hB, hF, hL, hForms⟩

theorem canonical_transport_full
    (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R)
    (N : TraceHaarTransport R) :
    ∃ A : JointExteriorCoefficientSources R N,
      SourceNativeLie R A.factorization ∧
      FiniteFullProduct.FullArchProduct R A.factorization ∧
      FiniteFullProduct.LocalArchRatio R A.factorization ∧
      Nonempty (SphericalTransportData R A) := by
  let B : FiniteCanonicalSource.Seed R :=
    Classical.choice (FiniteCanonicalSource.seed_nonempty R N)
  let μ := FiniteCanonicalSource.localHaar (F := F)
  letI : ∀ q, (μ q).IsAddHaarMeasure := fun q => by
    dsimp [μ, FiniteCanonicalSource.localHaar]
    infer_instance
  have hμ := FiniteCanonicalSource.localHaar_integer (F := F)
  have hs := coreFlatInsertion_initial_exterior_spherical R B.model B.fibers
    B.exceptional_eq (PiTensorProduct.tprod ℂ B.initial)
  let A := canonicalStage08 R B.model B.fibers μ hμ hR N B.exceptional_eq
    B.initial hs B.initial_nonzero
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · exact canonicalStage08_native R B.model B.fibers μ hμ hR N B.exceptional_eq
      B.initial hs B.initial_nonzero
  · exact FiniteFullProduct.canonical_fullArchProduct R N B hR
  · exact FiniteFullProduct.canonical_localArchRatio R N B hR
  · exact canonical_spherical_transport R B.model B.fibers μ hμ hR N B.exceptional_eq
      B.initial hs B.initial_nonzero

structure Source (R : PrincipalMellin.ActualRecipe S η)
    (θ : HeckeGeneral.Characters.HeckeCharacter F) where
  transport : TraceHaarTransport R
  spherical : FirstRootSphericalSeed R transport
  initialCutoffs : FirstRootCutoffs R
  projected : FirstRootProjected R transport spherical initialCutoffs
  target_kernel : ∀ p z, z ∈ projected.cutoffs.cutoff p →
    HeckeGeneral.Characters.localComponent F p.val θ z = 1
  native : SourceNativeLie R projected.base.factorization
  fullArchProduct : FiniteFullProduct.FullArchProduct R projected.base.factorization
  localArchRatio : FiniteFullProduct.LocalArchRatio R projected.base.factorization
  localWhittakerForms : FiniteFullProduct.LocalWhittakerForms R projected.base.factorization

theorem source_nonempty (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R)
    (θ : HeckeGeneral.Characters.HeckeCharacter F) : Nonempty (Source R θ) := by
  obtain ⟨N⟩ := trace_haar_transport_exists R hR
  obtain ⟨A, hNative, hFull, hLocal, ⟨D⟩⟩ := canonical_transport_full R hR N
  obtain ⟨A', hNative', hFull', hLocal', hForms'⟩ := spherical_seed_full R N A D hNative hFull hLocal
  obtain ⟨B⟩ := first_root_cutoffs_exist R
  obtain ⟨B', J, hker, hNative'', hFull'', hLocal'', hForms''⟩ :=
    FiniteProjectedFullSource.target_projector_full R hR N A' B hNative' hFull' hLocal' hForms' θ
  exact ⟨⟨N, A', B', J, hker, hNative'', hFull'', hLocal'', hForms''⟩⟩

def source (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R)
    (θ : HeckeGeneral.Characters.HeckeCharacter F) : Source R θ :=
  Classical.choice (source_nonempty R hR θ)

theorem Source.period_nonzero (R : PrincipalMellin.ActualRecipe S η)
    (θ : HeckeGeneral.Characters.HeckeCharacter F) (C : Source R θ)
    (u : R.A.UnitQuotient) :
    fourier R C.projected.base.sources.dq (C.projected.base.realization.theta u) 1 ≠ 0 := by
  rw [← ThetaExpansion.diagonal_one R, C.projected.radial]
  exact FiniteWhittakerProjectors.radialProfile_one_ne_zero R C.projected.cutoffs

/-- A high K-type core vector detected by any actual Whittaker functional
is also detected by this fixed source's stored archimedean functional. -/
theorem Source.archimedean_nonzero (R : PrincipalMellin.ActualRecipe S η)
    (θ : HeckeGeneral.Characters.HeckeCharacter F) (C : Source R θ)
    (w : InfinitePlace F)
    (M : KPCplxActualImage.Theta FourierContinuation.ComplexLines.traceFrequency →L[ℂ] ℂ)
    (hM : M ∈ KPCplxWhittakerUnique.whittakerSpace
      FourierContinuation.ComplexLines.traceFrequency FourierContinuation.ComplexLines.traceCharacter)
    (v : KPGlobalResidualConstruction.complexCore)
    (hv : M (FourierContinuation.ComplexLines.harmonicInclusion v) ≠ 0) :
    C.projected.base.factorization.ell (Sum.inl w) v ≠ 0 :=
  FiniteFullProduct.local_value_nonzero_of_whittaker R C.projected.base.factorization
    C.localWhittakerForms w M hM v hv

end ThetaGlobal.FiniteFixedSource

#print axioms ThetaGlobal.FiniteFixedSource.source_nonempty

#print axioms ThetaGlobal.FiniteFixedSource.Source.archimedean_nonzero
