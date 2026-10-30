module

public import ThetaGlobal.GlobalAffineJets
public import ThetaGlobal.GlobalProjectFourierSmooth
public import ThetaGlobal.GlobalProjectRadial
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.AdelicAction.TwoSidedJets

@[expose] public section

/-!
# A summable Fourier majorant on compact families of actual core arguments

The parameter dependence of all upper-root jets is derived from the
existing two-sided adelic spatial-jet theorem.  The actual additive
quotient is handled through its open quotient map.  Compactness then
supplies the derivative bounds required by the rational Fourier theorem.

The result is a genuine local compact-family estimate, with no assumed
theta reflection or equality of integrated Fourier series.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section

namespace ThetaGlobal.GlobalProjectUniformFourier

open NumberField DedekindZetaZeroFree DedekindZetaZeroFree.MomentSources
open MeasureTheory KPGlobalResidualConstruction
open CanonicalComplexSmoothAction.TranslatedGenerators.NativeApproximation
open scoped NumberField Classical Topology ContDiff

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)
  {Q : AdmissibleFlatSources R} {T : Realization R Q}

open GlobalCoreSource GlobalProjectFourierSmooth

def upperLinear : mixedEmbedding.mixedSpace F →L[ℝ] ArchCoordinates F where
  toFun x w i := if i = 0 then
    x.2 ⟨w, KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w⟩ else 0
  map_add' x y := by
    ext w i
    split_ifs <;> simp
  map_smul' c x := by
    ext w i
    split_ifs <;> simp
  cont := by
    apply continuous_pi
    intro w
    apply continuous_pi
    intro i
    split_ifs
    · exact (continuous_apply _).comp continuous_snd
    · exact continuous_const

@[simp] theorem upperLinear_apply (x : mixedEmbedding.mixedSpace F)
    (w : InfinitePlace F) (i : Fin 3) :
    upperLinear R x w i = if i = 0 then
      x.2 ⟨w, KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w⟩ else 0 := rfl

theorem upper_affine_mem (x : mixedEmbedding.mixedSpace F) :
    archBase F + upperLinear R x ∈ archDomain F := by
  intro w
  simp [archBase]

theorem upper_affine_chart (x : mixedEmbedding.mixedSpace F) :
    archChart F R.A.zeta12 R.A.primitive_zeta12 (archBase F + upperLinear R x) =
      KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x, 0) : KPAdeles F) := by
  unfold archChart KPGlobalTorusFunctionData.N
  congr 2
  apply RestrictedProduct.ext
  intro p
  cases p with
  | inr p =>
    change 1 = KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) 0
    exact (KPStandardLocalRootLifts.N_zero F R.A.zeta12 R.A.primitive_zeta12 _).symm
  | inl w =>
    change KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w)
        ((InfinitePlace.Completion.ringEquivComplexOfIsComplex _).symm
          ((archBase F + upperLinear R x) w 0)) *
      KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w) _ *
      KPStandardLocalRootLifts.LowerN F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w)
        ((InfinitePlace.Completion.ringEquivComplexOfIsComplex _).symm
          ((archBase F + upperLinear R x) w 2)) =
      KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x w)
    have hxw : (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w)).symm
          (x.2 ⟨w, KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w⟩) =
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x w := by
      apply (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w)).injective
      rw [RingEquiv.apply_symm_apply]
      exact (OrbitExpansion.mixed_upper_coordinate R w x).symm
    simp [archBase, hxw, KPStandardLocalRootLifts.A_one,
      KPStandardLocalRootLifts.LowerN_zero]

theorem core_native_left_chart_contDiffOn (f : sameResidueModule T) (g : Group R) :
    ContDiffOn ℝ ∞ (fun x => f.val
      (archChart F R.A.zeta12 R.A.primitive_zeta12 x * g)) (archDomain F) := by
  have ht := KPLiteralPeriod.NonzeroResidue.smooth_right_translate
    F R.A.zeta12 R.A.primitive_zeta12 f.val (core_smooth R f) g
  have h := ht.2.1 1
  change ContDiffOn ℝ ∞ (fun x => f.val
    ((1 * archChart F R.A.zeta12 R.A.primitive_zeta12 x) * g)) (archDomain F) at h
  simpa only [one_mul] using h

theorem native_left_jet_continuous (f : sameResidueModule T) (n : ℕ) :
    Continuous (fun g : Group R => iteratedFDeriv ℝ n
      (fun x => f.val (archChart F R.A.zeta12 R.A.primitive_zeta12 x * g)) (archBase F)) := by
  have hj := two_sided_adelic_spatial_jets F R.A.zeta12 R.A.primitive_zeta12
    f.val (core_smooth R f) (fun _ : Group R => 1) id continuous_const continuous_id n
  have hbase : archBase F ∈ archDomain F := by intro w; simp [archBase]
  have h := hj.comp_continuous (continuous_const.prodMk continuous_id)
    (fun _ => ⟨hbase, Set.mem_univ _⟩)
  simpa only [Function.comp_def, id_eq, one_mul] using h

def upperJet (f : sameResidueModule T) (n : ℕ) (g : Group R) :=
  (iteratedFDeriv ℝ n
    (fun x => f.val (archChart F R.A.zeta12 R.A.primitive_zeta12 x * g))
      (archBase F)).compContinuousLinearMap (fun _ => upperLinear R)

theorem upperJet_continuous (f : sameResidueModule T) (n : ℕ) :
    Continuous (upperJet R f n) :=
  (ContinuousMultilinearMap.continuous_precomp (fun _ : Fin n => upperLinear R)).comp
    (native_left_jet_continuous R f n)

theorem smoothArchJet_mk (f : sameResidueModule T) (n : ℕ)
    (g : Group R) (z : KPAdeles F) :
    smoothArchJet n (fiber T f g) (QuotientAddGroup.mk z) =
      upperJet R f n (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 z * g) := by
  have he : (fun x : mixedEmbedding.mixedSpace F =>
      fiber T f g ((QuotientAddGroup.mk z) + smoothArchInclusion F x)) =
      (fun x => f.val (archChart F R.A.zeta12 R.A.primitive_zeta12
        (archBase F + upperLinear R x) *
          (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 z * g))) := by
    funext x
    rw [smoothArchInclusion, ← QuotientAddGroup.mk_add, fiber_mk,
      add_comm z, KPGlobalTorusFunctionData.N_add, mul_assoc, ← upper_affine_chart]
  unfold smoothArchJet
  rw [he]
  have h := GlobalAffineJets.iteratedFDeriv_comp_affine (upperLinear R) (archBase F)
    (fun x => f.val (archChart F R.A.zeta12 R.A.primitive_zeta12 x *
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 z * g)))
    (archDomain F) (KPGlobalTorusBorelTwistCompatibility.groupArchDomain_open F)
    (core_native_left_chart_contDiffOn R f _) 0 (upper_affine_mem R 0) n
  simpa only [map_zero, add_zero, upperJet] using h

theorem fiber_joint_jets_continuous (f : sameResidueModule T) (n : ℕ) :
    Continuous (fun z : Group R × KPAdditiveQuotient F =>
      smoothArchJet n (fiber T f z.1) z.2) := by
  letI : IsTopologicalGroup (Group R) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover
      F R.A.zeta12 R.A.primitive_zeta12).2.2.1
  apply ((IsOpenQuotientMap.id (X := Group R)).prodMap
    (QuotientAddGroup.isOpenQuotientMap_mk
      (N := AdeleRing.principalSubgroup (𝓞 F) F))).continuous_comp_iff.mp
  have h := (upperJet_continuous R f n).comp
    (((KPWildIndependentGenericity.NonzeroPeriod.actual_upper_root_continuous
      F R.A.zeta12 R.A.primitive_zeta12).comp continuous_snd).mul continuous_fst)
  simpa only [Function.comp_def, Prod.map, id_eq, smoothArchJet_mk] using h

/-- Actual rational coefficients admit a common summable majorant on any
compact continuous family of arguments. -/
theorem compact_rationalPeriod_majorant
    {P : Type*} [TopologicalSpace P] [CompactSpace P]
    (f : sameResidueModule T) (g : P → Group R) (hg : Continuous g) :
    ∃ b : F → ℝ, Summable b ∧ (∀ a, 0 ≤ b a) ∧
      ∀ p a, ‖rationalPeriod T f a (g p)‖ ≤ b a := by
  letI : Q.dq.IsAddHaarMeasure := Q.quotientHaar
  letI : IsProbabilityMeasure Q.dq := ⟨Q.probability⟩
  obtain ⟨K, hKc, hKo, hK⟩ := fiber_exists_uniform_compact_open_level R f
    (Set.range g) (isCompact_range hg)
  let φ : P × KPAdditiveQuotient F → ℂ := fun z => fiber T f (g z.1) z.2
  have hc : Continuous φ :=
    (GlobalProjectRadial.upper_integrand_joint_continuous R f.val
      f.property.2.1 f.property.2.2.1).comp (hg.prodMap continuous_id)
  have hj (n : ℕ) : Continuous (fun z : P × KPAdditiveQuotient F =>
      smoothArchJet n (fiber T f (g z.1)) z.2) :=
    (fiber_joint_jets_continuous R f n).comp (hg.prodMap continuous_id)
  let B := fun (n : ℕ) (v : Fin n → mixedEmbedding.mixedSpace F) =>
    sSup (Set.range (fun z : P × KPAdditiveQuotient F =>
      ‖smoothArchJet n (fiber T f (g z.1)) z.2 v‖))
  have hB (n : ℕ) (v : Fin n → mixedEmbedding.mixedSpace F) :
      BddAbove (Set.range (fun z : P × KPAdditiveQuotient F =>
        ‖smoothArchJet n (fiber T f (g z.1)) z.2 v‖)) :=
    (isCompact_range (((hj n).eval continuous_const).norm)).bddAbove
  have hunif : IsUniformArchSmoothFamily φ B := by
    refine ⟨hc, fun p => fiber_isArchSmooth R f (g p), hj, ?_⟩
    intro n v p q
    exact le_csSup (hB n v) (Set.mem_range_self (p, q))
  obtain ⟨b, hb, hp, hbound⟩ := ThetaRationalFourierSummation.rational_fourier_uniform_majorant F
    (PrincipalOfKP.standardCharacter F) (PrincipalOfKP.standardCharacter_nontrivial F)
    Q.dq K hKc hKo φ (fun p => hK (g p) (Set.mem_range_self p)) B hunif
  refine ⟨b, hb, hp, ?_⟩
  intro p a
  have h := hbound p a
  simpa only [OrbitExpansion.negativeFrequency_eq_star_rationalCharacter,
    φ, rationalPeriod] using h

end ThetaGlobal.GlobalProjectUniformFourier
