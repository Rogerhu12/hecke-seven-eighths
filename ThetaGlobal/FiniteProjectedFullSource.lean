module

public import ThetaGlobal.FiniteFullProduct
public import ThetaGlobal.FiniteTargetCutoff

/-!
# The actual finite projector retains the canonical full matrix product

This strengthens the upstream constructive projector proofs by retaining
one theorem about their unchanged core map.  Every source, local vector,
normalization and projector word is constructed by those existing proofs.
The newly retained property is proved for the literal canonical source in
`FiniteFullProduct.canonical_fullArchProduct`; it is not a final input.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace ThetaGlobal.FiniteProjectedFullSource
open NumberField MeasureTheory DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources DedekindZetaZeroFree.ThetaExpansion
open DedekindZetaZeroFree.RootDerivatives
open scoped Classical NumberField Topology TensorProduct

section Projected
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {N : TraceHaarTransport R} (A : JointExteriorCoefficientSources R N)
variable (I : R.A.Sf → Type) [∀ q, Fintype (I q)]
variable (c : ∀ q, I q → ℂ) (t : ∀ q, I q → q.val.adicCompletion F)
variable {Q' : AdmissibleFlatSources R} (T' : Realization R Q')
variable (hdq : Q'.dq = A.sources.dq)
variable (hpin : ∀ v, T'.theta v = _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.rootProjectorWord R I c t
  (Finset.univ : Finset R.A.Sf).toList (A.realization.theta v))

include I c t hdq hpin

theorem projected_factorization_full
    (hn : ∀ v, fourier R Q'.dq (T'.theta v) 1 ≠ 0)
    (hNative : SourceNativeLie R A.factorization)
    (hFull : FiniteFullProduct.FullArchProduct R A.factorization)
    (hLocal : FiniteFullProduct.LocalArchRatio R A.factorization) :
    ∃ D' : SourceFactorization R Q' T', SourceNativeLie R D' ∧
      FiniteFullProduct.FullArchProduct R D' ∧
      FiniteFullProduct.LocalArchRatio R D' ∧
      (∀ q, D'.finiteData q = A.factorization.finiteData q) ∧
      (∀ q, (D'.finiteData q).haar = (A.factorization.finiteData q).haar) ∧
      ExteriorCoefficients R Q' T' D' := by
  let D := A.factorization
  have hf := fun v => FiniteWhittakerProjectors.selected_rootProjectorWord_frozen R D I c t
    (Finset.univ : Finset R.A.Sf).toList v
  choose s x hs hx using hf
  have hsp := FiniteWhittakerProjectors.projected_rows_recovery R A I c t T' hdq hpin hn
  have hhc := FiniteWhittakerProjectors.hcHeckeSpan_le_of_finite_recovery R A.realization T' hsp
  let D' : SourceFactorization R Q' T' := {
    finiteData := D.finiteData
    references := D.references
    bad := D.bad
    bad_exact := D.bad_exact
    ell := D.ell
    reference_value := D.reference_value
    scalarSlot := D.scalarSlot
    coreMap := D.coreMap
    selected := fun v => RestrictedTensorSimple.stageInclusion _ D.references D.bad (s v) (PiTensorProduct.tprod ℂ (x v))
    selected_eq := fun v => (hx v).trans (hpin v).symm
    selected_frozen_stage := fun v => ⟨s v,x v,hs v,rfl⟩
    core_injective := D.core_injective
    core_same_residue := fun z => ⟨hhc (D.core_same_residue z).1,(D.core_same_residue z).2⟩
    finite_intertwining := D.finite_intertwining
    complex_intertwining := D.complex_intertwining
    product_integrable := by rw [hdq]; exact D.product_integrable
    product_exact := by rw [hdq]; exact D.product_exact
    spherical_reference := D.spherical_reference
    detected_tensor := by rw [hdq]; exact D.detected_tensor
    period_integrable := fun v g => FourierContinuation.theta_period_integrable T' v g
    detected := by obtain ⟨v,_⟩ := D.detected; exact ⟨v,hn v⟩ }
  have hFull' : FiniteFullProduct.FullArchProduct R D' := by
    simpa only [FiniteFullProduct.FullArchProduct, FiniteFullProduct.archRatio,
      FiniteCoreProduct.stageCoefficient, FiniteCoreProduct.stageFunction, D', hdq] using hFull
  have hLocal' : FiniteFullProduct.LocalArchRatio R D' := by
    simpa only [FiniteFullProduct.LocalArchRatio, FiniteFullProduct.archRatio,
      FiniteCoreProduct.stageCoefficient, FiniteCoreProduct.stageFunction, D', hdq] using hLocal
  refine ⟨D',hNative,hFull',hLocal',fun _ => rfl,fun _ => rfl,?_⟩
  exact ⟨A.exterior.rational_exact,A.exterior.crt_product,A.exterior.local_exact⟩

end Projected

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem finite_projector_full
    (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R)
    (N : TraceHaarTransport R) (A : FirstRootSphericalSeed R N) (B : FirstRootCutoffs R)
    (hNative : SourceNativeLie R A.base.factorization)
    (hFull : FiniteFullProduct.FullArchProduct R A.base.factorization)
    (hLocal : FiniteFullProduct.LocalArchRatio R A.base.factorization) :
    ∃ J : FirstRootProjected R N A B, SourceNativeLie R J.base.factorization ∧
      FiniteFullProduct.FullArchProduct R J.base.factorization ∧
      FiniteFullProduct.LocalArchRatio R J.base.factorization := by
  obtain ⟨C,I,inst,c,t,he,hle,hsub,hcut⟩ := FiniteWhittakerProjectors.cutoff_word_exists R A B
  letI := inst
  obtain ⟨Q,T,hdq,hpin⟩ := projected_realization R  hR A.base I c t
    (Finset.univ : Finset R.A.Sf).toList
  have hrad (v : R.A.UnitQuotient) (y : R.A.G) :
      fourier R Q.dq (T.theta v) (diagonal R y) = firstRootRadialProfile R C y := by
    rw [hdq,hpin]
    exact hcut v y
  have hd1 : diagonal R (1 : R.A.G) = 1 := by
    unfold diagonal localIdele
    simp only [Prod.fst_one, Prod.snd_one, Pi.one_apply, KPRationalAdelicSplitting.localIdele,
      map_one, Finset.prod_const_one, one_mul]
    unfold KPRationalAdelicSplitting.pglA KPRationalAdelicSplitting.A KPRationalAdelicSplitting.ATuple
    have ht : KPRationalAdelicSplitting.ATuple F R.A.zeta12 R.A.primitive_zeta12 1 = 1 := by
      ext v
      simp [KPRationalAdelicSplitting.ATuple, KPRationalAdelicSplitting.ACoordinates, KPStandardLocalRootLifts.A,
        KPLocalCover.sectionMap, KubotaRankTwo.d]
      have hm : (Matrix.GeneralLinearGroup.mkOfDetNeZero
          (!![(1 : KPHilbert.Completion F v), 0; 0, 1]) (by simp)) =
          (1 : Matrix.GeneralLinearGroup (Fin 2) (KPHilbert.Completion F v)) := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp
      change KPLocalCover.CubicGL2Raw.mk _ 1 = KPLocalCover.CubicGL2Raw.mk 1 1
      rw [hm]
    change KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12
        (KPRationalAdelicSplitting.ATuple F R.A.zeta12 R.A.primitive_zeta12 1)) = 1
    rw [ht,map_one,map_one]
  have hn (v : R.A.UnitQuotient) : fourier R Q.dq (T.theta v) 1 ≠ 0 := by
    rw [← hd1,hrad]
    exact FiniteWhittakerProjectors.radialProfile_one_ne_zero R C
  obtain ⟨D,hDN,hDF,hDL,hM,hH,E⟩ := projected_factorization_full R A.base I c t T hdq hpin hn hNative hFull hLocal
  let base : JointExteriorCoefficientSources R N := {
    aligned := hR
    transport := N
    transport_exact := rfl
    sources := Q
    realization := T
    factorization := D
    localHaarTransport := fun q => by
      have hh := A.base.localHaarTransport q
      rw [A.base.transport_exact] at hh
      exact hh.trans (congrArg (fun μ => ENNReal.ofReal (PoissonS.integerVolume F q) • μ) (hH q).symm)
    exterior := E }
  exact ⟨⟨C,he,hle,hsub,base,hrad⟩,hDN,hDF,hDL⟩

/-- Shrink inside the actual target character kernel, run the actual
projector, and retain the full arbitrary-vector archimedean product. -/
theorem target_projector_full
    (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R)
    (N : TraceHaarTransport R) (A : FirstRootSphericalSeed R N) (B : FirstRootCutoffs R)
    (hNative : SourceNativeLie R A.base.factorization)
    (hFull : FiniteFullProduct.FullArchProduct R A.base.factorization)
    (hLocal : FiniteFullProduct.LocalArchRatio R A.base.factorization)
    (θ : HeckeGeneral.Characters.HeckeCharacter F) :
    ∃ (B' : FirstRootCutoffs R) (J : FirstRootProjected R N A B'),
      (∀ p z, z ∈ J.cutoffs.cutoff p →
        HeckeGeneral.Characters.localComponent F p.val θ z = 1) ∧
      SourceNativeLie R J.base.factorization ∧
      FiniteFullProduct.FullArchProduct R J.base.factorization ∧
      FiniteFullProduct.LocalArchRatio R J.base.factorization := by
  obtain ⟨B', he, hle, hker⟩ := TargetFiniteCutoff.target_cutoffs_exist R θ B
  obtain ⟨J, hNative', hFull', hLocal'⟩ := finite_projector_full R hR N A B' hNative hFull hLocal
  exact ⟨B', J, fun p z hz => hker p z (J.cutoff_le p hz), hNative', hFull', hLocal'⟩

end ThetaGlobal.FiniteProjectedFullSource

#print axioms ThetaGlobal.FiniteProjectedFullSource.projected_factorization_full
#print axioms ThetaGlobal.FiniteProjectedFullSource.target_projector_full
