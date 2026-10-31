import ThetaGlobal.GlobalCoreSource
import DedekindZetaZeroFree.Theta.Whittaker.ArchimedeanFiberSmoothness
import DedekindZetaZeroFree.RepresentationTheory.Smooth.RightDerivativeCyclicSpan
import DedekindZetaZeroFree.Eisenstein.Residues.FlatRange.UniformFiniteLevels

/-!
# Absolute rational Fourier convergence for every residual core vector

The finite level and archimedean smoothness used by the upstream Fourier
theorem belong to every vector of the residual Harish--Chandra/Hecke core.
This file proves the pointwise norm summability directly from that fact.
It also retains a common compact open additive level for an arbitrary
compact family of group arguments, for use in the uniform version.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section

namespace ThetaGlobal.GlobalProjectFourierSmooth

open NumberField DedekindZetaZeroFree DedekindZetaZeroFree.MomentSources
open MeasureTheory IsDedekindDomain KPGlobalResidualConstruction KPLiteralChamber
open scoped NumberField Classical Topology ContDiff

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)
  {Q : AdmissibleFlatSources R} {T : Realization R Q}

open GlobalCoreSource

theorem core_smooth (f : sameResidueModule T) :
    KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 f.val :=
  RootDerivatives.hcHeckeSpan_smooth R T f.property.1

/-- A common additive level exists on every compact family of arguments.
No principal-character choice or preferred theta vector enters this lemma. -/
theorem fiber_exists_uniform_compact_open_level (f : sameResidueModule T)
    (C : Set (Group R)) (hC : IsCompact C) :
    ∃ K : AddSubgroup (FiniteAdeleRing (𝓞 F) F),
      IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)) ∧
      IsOpen (K : Set (FiniteAdeleRing (𝓞 F) F)) ∧
      ∀ g ∈ C, HasSmoothAdditiveLevel K (fiber T f g) := by
  letI : IsTopologicalGroup (Group R) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover
      F R.A.zeta12 R.A.primitive_zeta12).2.2.1
  obtain ⟨U, hU⟩ := (core_smooth R f).2.2
  obtain ⟨V, hV⟩ := ResidualFlatRange.compact_uniform_conjugated_finite_level
    F R.A.zeta12 R.A.primitive_zeta12 C hC U
  let n : Multiplicative (FiniteAdeleRing (𝓞 F) F) →*
      KPGlobalTorusFunctionData.finitePart F R.A.zeta12 R.A.primitive_zeta12 :=
    { toFun k := ⟨KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        (finiteLevelFiniteInclusion F k.toAdd), OrbitExpansion.finiteRoot_mem_finitePart R k.toAdd⟩
      map_one' := by
        apply Subtype.ext
        change KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
          (finiteLevelFiniteInclusion F 0) = 1
        rw [map_zero]
        exact (KPGlobalTorusFunctionData.Nhom F R.A.zeta12 R.A.primitive_zeta12).map_one
      map_mul' a b := by
        apply Subtype.ext
        change KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
          (finiteLevelFiniteInclusion F (a.toAdd + b.toAdd)) = _
        rw [map_add]
        exact KPGlobalTorusFunctionData.N_add F R.A.zeta12 R.A.primitive_zeta12 _ _ }
  let K₀ : AddSubgroup (FiniteAdeleRing (𝓞 F) F) :=
    { carrier := {k | n (Multiplicative.ofAdd k) ∈ V.toOpenSubgroup}
      zero_mem' := by exact (V.toOpenSubgroup.toSubgroup.comap n).one_mem
      add_mem' := by
        intro a b ha hb
        exact (V.toOpenSubgroup.toSubgroup.comap n).mul_mem ha hb
      neg_mem' := by
        intro a ha
        exact (V.toOpenSubgroup.toSubgroup.comap n).inv_mem ha }
  let K := K₀ ⊓ KPAdelicTopology.integralAdeles F
  have hn : Continuous n := by
    apply Continuous.subtype_mk
    exact (KPWildIndependentGenericity.NonzeroPeriod.actual_upper_root_continuous
      F R.A.zeta12 R.A.primitive_zeta12).comp
        (continuous_const.prodMk continuous_id)
  have hKo : IsOpen (K : Set (FiniteAdeleRing (𝓞 F) F)) :=
    (V.toOpenSubgroup.isOpen.preimage hn).inter
      (KPAdelicTopology.integralAdeles_isOpen F)
  have hKc : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)) :=
    (KPAdelicTopology.integralAdeles_isCompact F).of_isClosed_subset
      (K.isClosed_of_isOpen hKo) (fun _ h => h.2)
  refine ⟨K, hKc, hKo, ?_⟩
  intro g hg q h
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨k, hk, he⟩ := h.property
  change (QuotientAddGroup.mk (finiteLevelFiniteInclusion F k) : KPAdditiveQuotient F) = h.val at he
  rw [← he, ← QuotientAddGroup.mk_add, fiber_mk, fiber_mk,
    KPGlobalTorusFunctionData.N_add]
  have hmul : (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x *
      KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        (finiteLevelFiniteInclusion F k)) * g =
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x * g) *
        (g⁻¹ * KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
          (finiteLevelFiniteInclusion F k) * g) := by group
  rw [hmul]
  apply hU
  apply hV g hg
  exact ⟨n (Multiplicative.ofAdd k), hk.1, rfl⟩

theorem fiber_exists_compact_open_level (f : sameResidueModule T) (g : Group R) :
    ∃ K : AddSubgroup (FiniteAdeleRing (𝓞 F) F),
      IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)) ∧
      IsOpen (K : Set (FiniteAdeleRing (𝓞 F) F)) ∧
      HasSmoothAdditiveLevel K (fiber T f g) := by
  obtain ⟨K, hKc, hKo, hK⟩ :=
    fiber_exists_uniform_compact_open_level R f {g} isCompact_singleton
  exact ⟨K, hKc, hKo, hK g (Set.mem_singleton g)⟩

theorem core_left_chart_contDiffOn (f : sameResidueModule T) (g : Group R) :
    ContDiffOn ℝ ∞ (fun x => f.val
      (KPGlobalTorusBorelTwistCompatibility.groupArchChart F R.A.zeta12
        R.A.primitive_zeta12 x * g))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) := by
  apply contDiffOn_of_locally_contDiffOn
  intro x₀ hx₀
  obtain ⟨O, q, hO, hxO, hq, hqD, he⟩ :=
    literal_group_chart_local_transition F R.A.zeta12 R.A.primitive_zeta12 g x₀ hx₀
  refine ⟨O, hO, hxO, ?_⟩
  exact (((core_smooth R f).2.1
    (KPGlobalTorusBorelTwistCompatibility.groupArchChart F R.A.zeta12
      R.A.primitive_zeta12 x₀ * g)).comp hq hqD).congr
      (fun x hx => congrArg f.val (he x hx)) |>.mono Set.inter_subset_right

theorem fiber_arch_lift_contDiff (f : sameResidueModule T) (g : Group R) :
    ContDiff ℝ ∞ (fun x : mixedEmbedding.mixedSpace F =>
      fiber T f g (smoothArchInclusion F x)) := by
  let c : mixedEmbedding.mixedSpace F → KPGlobalTorusBorelTwistCompatibility.GroupArch F :=
    fun x w i => if i = 0 then 0 else if i = 1 then 1 else
      x.2 ⟨w, KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w⟩
  have hc : ContDiff ℝ ∞ c := by
    apply contDiff_pi.mpr
    intro w
    apply contDiff_pi.mpr
    intro i
    dsimp only [c]
    split_ifs <;> fun_prop
  have hcd : Set.MapsTo c Set.univ (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) := by
    intro x _ w
    simp [c]
  have hs := (core_left_chart_contDiffOn R f g).comp hc.contDiffOn hcd
  apply contDiffOn_univ.mp
  convert hs using 1
  funext x
  rw [smoothArchInclusion, fiber_mk, OrbitExpansion.upperArch_eq_leftChart]
  congr 2
  congr 1
  funext w i
  dsimp only [c]
  split_ifs <;> try rfl
  exact OrbitExpansion.mixed_upper_coordinate R w x

theorem fiber_isArchSmooth (f : sameResidueModule T) (g : Group R) :
    IsArchSmooth (fiber T f g) := by
  obtain ⟨K, hKc, hKo, hlev⟩ := fiber_exists_compact_open_level R f g
  apply (finiteLevel_smooth_iff K hKc hKo _ hlev).mpr
  unfold IsLevelTorusSmooth
  simpa only [smoothLevelPullback_mk K _ hlev] using fiber_arch_lift_contDiff R f g

theorem rationalPeriod_norm_summable (f : sameResidueModule T) (g : Group R) :
    Summable (fun a : F => ‖rationalPeriod T f a g‖) := by
  letI : Q.dq.IsAddHaarMeasure := Q.quotientHaar
  letI : IsProbabilityMeasure Q.dq := ⟨Q.probability⟩
  obtain ⟨K, hKc, hKo, hl⟩ := fiber_exists_compact_open_level R f g
  have hj := fiber_isArchSmooth R f g
  let φ := fiber T f g
  have hB (n : ℕ) (v : Fin n → mixedEmbedding.mixedSpace F) :
      BddAbove (Set.range (fun q => ‖smoothArchJet n φ q v‖)) :=
    (isCompact_range (((hj.2.2 n).eval continuous_const).norm)).bddAbove
  have hunif : IsUniformArchSmoothFamily (fun z : Unit × KPAdditiveQuotient F => φ z.2)
      (fun n v => sSup (Set.range (fun q => ‖smoothArchJet n φ q v‖))) := by
    refine ⟨hj.1.comp continuous_snd, fun _ => hj,
      fun n => (hj.2.2 n).comp continuous_snd, ?_⟩
    intro n v p q
    exact le_csSup (hB n v) (Set.mem_range_self q)
  obtain ⟨b, hb, hp, hbound⟩ := ThetaRationalFourierSummation.rational_fourier_uniform_majorant F
    (PrincipalOfKP.standardCharacter F) (PrincipalOfKP.standardCharacter_nontrivial F)
    Q.dq K hKc hKo (fun z : Unit × KPAdditiveQuotient F => φ z.2)
    (fun _ => hl) _ hunif
  apply hb.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro a
  have h := hbound () a
  change ‖∫ q, φ q * ThetaRationalFourierSummation.freq F
    (PrincipalOfKP.standardCharacter F) a q ∂Q.dq‖ ≤ b a at h
  simpa only [OrbitExpansion.negativeFrequency_eq_star_rationalCharacter, φ, rationalPeriod] using h

/-- The Fourier expansion of every actual core vector is now unconditional. -/
theorem rationalPeriod_hasSum (f : sameResidueModule T) (g : Group R) :
    HasSum (fun a : F => rationalPeriod T f a g) (f.val g) :=
  rationalPeriod_hasSum_of_norm_summable T f g (rationalPeriod_norm_summable R f g)

theorem nonzero_rationalPeriod_hasSum (f : sameResidueModule T) (g : Group R) :
    HasSum (fun a : Fˣ => rationalPeriod T f (a : F) g)
      (f.val g - upper R Q.dq f.val g) :=
  GlobalCoreSource.nonzero_rationalPeriod_hasSum T f g (rationalPeriod_norm_summable R f g)

end ThetaGlobal.GlobalProjectFourierSmooth
