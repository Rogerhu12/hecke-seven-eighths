import HeckeAxiom.ProbeFourier
import HeckeAxiom.MeasureAdapter
import DedekindZetaZeroFree.Moments.Probes.AnnularWeightsAndCancellingProfiles
import DedekindZetaZeroFree.Metaplectic.Weil.FiniteQuadraticFourierKernel

/-!
# The skeleton's additive probe test from Axiom's fixed weight

Axiom's `probe_fixed_weight_construction` gives, for any additive Haar measure on
the `S`-local product and any Haar measure on its units, an annular tensor `W0`
whose Fourier transform vanishes at `0` and whose Fourier–Mellin transform at
`1/6` is nonzero. We take the additive measure to be Axiom's Poisson measure built
from the skeleton's self-dual local measures, and the multiplicative measure to be
the sheet measure over the skeleton's norm-one Haar measure, so that Axiom's
radial Mellin identity applies to it.

The coordinates of `W0` give the skeleton's additive probe test, with its
archimedean factor read in the trace model and scaled by a constant `a`. By the
Fourier factorization its additive Fourier transform is `a · κ` times Axiom's at the
corresponding units, where `κ = 2^{-r₂} ∏ μ_v(𝒪_v)⁻¹`, and so is its additive Mellin
transform. Choosing `a = conj M / ‖M‖` for the nonzero value `M` at `1/6` makes the
skeleton's Mellin value at `1/6` the positive real `‖M‖`.
-/

set_option quotPrecheck false

noncomputable section

namespace HeckeAxiom

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Bridge NumberField.StandardAddChar
open HeckeGeneral.ThetaSkeleton.Physical ProbeUnits ProbeFourier
open scoped Classical ComplexConjugate

namespace ProbeTestChoice

variable {K : Type} [Field K] [NumberField K] (A : SArithmeticData K)

local notation "S" => (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
local notation "Rmix" => InfiniteAdeleRing.ringEquiv_mixedSpace K

/- These are the measurable structures of `selfDualProbeMeasures`, written as `borel`
so that instance search sees through them. -/
local instance : MeasurableSpace (sLocalNormOneGroup K S) := borel _
local instance : BorelSpace (sLocalNormOneGroup K S) := ⟨rfl⟩
local instance (v : HeightOneSpectrum (𝓞 K)) : MeasurableSpace (v.adicCompletion K) := borel _
local instance (v : HeightOneSpectrum (𝓞 K)) : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
local notation "μ" => (selfDualProbeMeasures K S).haar
local instance (p : S) : (μ p).IsAddHaarMeasure := (selfDualProbeMeasures K S).haar_isAddHaar p
local instance : MeasurableSpace (SLocalProduct K A.Sf) := borel _
local instance : BorelSpace (SLocalProduct K A.Sf) := ⟨rfl⟩
local instance : MeasurableSpace A.G1 := borel _
local instance : BorelSpace A.G1 := ⟨rfl⟩

local notation "Coords" => ProbeAnnularTensorWeights.AnnularCoordinates K A.Sf
local notation "tensor" => ProbeAnnularTensorWeights.tensor K A.Sf

/-! ### The test function given by annular coordinates -/

/-- The archimedean factor of an annular tensor, on the mixed space. -/
def archFactor (C : Coords) (m : mixedEmbedding.mixedSpace K) : ℂ :=
  (∏ v, C.fReal v (m.1 v)) * ∏ v, C.fComplex v (m.2 v)

theorem tensor_eq (C : Coords) (x : SLocalProduct K A.Sf) :
    tensor C x = archFactor A C ((Rmix) x.1) * ∏ v, C.fFinite v (x.2 v) :=
  rfl

theorem contDiff_archFactor (C : Coords) : ContDiff ℝ (⊤ : ℕ∞) (archFactor A C) := by
  unfold archFactor
  exact (contDiff_prod fun v _ => (C.real_regular v).1.comp
      ((contDiff_apply ℝ ℝ v).comp contDiff_fst)).mul
    (contDiff_prod fun v _ => (C.complex_regular v).1.comp
      ((contDiff_apply ℝ ℂ v).comp contDiff_snd))

theorem hasCompactSupport_archFactor (C : Coords) : HasCompactSupport (archFactor A C) := by
  refine HasCompactSupport.intro ((isCompact_univ_pi fun v => (C.real_regular v).2.1.isCompact).prod
    (isCompact_univ_pi fun v => (C.complex_regular v).2.1.isCompact)) fun m hm => ?_
  simp only [mem_prod, mem_univ_pi, not_and_or, not_forall] at hm
  unfold archFactor
  rcases hm with ⟨v, hv⟩ | ⟨v, hv⟩
  · rw [Finset.prod_eq_zero (Finset.mem_univ v)
      (image_eq_zero_of_notMem_tsupport (f := C.fReal v) hv), zero_mul]
  · rw [Finset.prod_eq_zero (Finset.mem_univ v)
      (image_eq_zero_of_notMem_tsupport (f := C.fComplex v) hv), mul_zero]

/-- The skeleton's archimedean Schwartz test: `a · archFactor`, in the trace model. -/
def schwartzTest (C : Coords) (a : ℂ) : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ :=
  HasCompactSupport.toSchwartzMap (f := fun y => a * archFactor A C (traceToMixed K y))
    ((hasCompactSupport_archFactor A C).comp_homeomorph (traceToMixed K).toHomeomorph).mul_left
    (contDiff_const.mul ((contDiff_archFactor A C).comp (traceToMixed K).contDiff))

theorem schwartzTest_symm (C : Coords) (a : ℂ) (m : mixedEmbedding.mixedSpace K) :
    schwartzTest A C a ((traceToMixed K).symm m) = a * archFactor A C m := by
  change a * archFactor A C (traceToMixed K ((traceToMixed K).symm m)) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]

theorem prod_places (h : ↥A.Sf → ℂ) : (∏ p : S, h p) = ∏ v : ↥A.Sf, h v :=
  rfl

theorem tensorTest_eq (C : Coords) (a : ℂ) (x : sLocalMultiplicativeGroup K S) :
    sLocalTensorTestFunction K S (schwartzTest A C a) (fun y => ∏ p : S, C.fFinite p (y p)) x =
      a * tensor C (toUnits A x : SLocalProduct K A.Sf) := by
  unfold sLocalTensorTestFunction
  rw [schwartzTest_symm, tensor_eq, val_toUnits, RingEquiv.apply_symm_apply, mul_assoc]
  rfl

/-- The skeleton's additive probe test given by the coordinates `C`, scaled by `a`. -/
def probeTest (C : Coords) (a : ℂ) (lower : ℝ) (hlower : 0 < lower)
    (hcompact : HasCompactSupport fun x : sLocalMultiplicativeGroup K S =>
      tensor C (toUnits A x : SLocalProduct K A.Sf))
    (hnorm : ∀ x : sLocalMultiplicativeGroup K S,
      tensor C (toUnits A x : SLocalProduct K A.Sf) ≠ 0 → lower ≤ sLocalProductNorm K S x) :
    AdditiveProbeTest K S where
  infiniteTest := schwartzTest A C a
  finiteTest p := C.fFinite p
  finite_locallyConstant p := (C.finite_regular p).1
  finite_compactSupport p := (C.finite_regular p).2.1
  tensor_compactSupport := by
    have h : sLocalTensorTestFunction K S (schwartzTest A C a)
        (fun y => ∏ p : S, C.fFinite p (y p)) =
          fun x => a * tensor C (toUnits A x : SLocalProduct K A.Sf) :=
      funext (tensorTest_eq A C a)
    rw [h]
    exact hcompact.mul_left
  lowerNorm := lower
  lowerNorm_pos := hlower
  norm_support x hx := by
    rw [tensorTest_eq] at hx
    exact hnorm x (right_ne_zero_of_mul hx)

/-! ### Fourier and Mellin transforms of the test -/

/-- The normalizing constant `2^{-r₂} ∏ μ_v(𝒪_v)⁻¹`. -/
def kappa : ℂ :=
  ((PoissonArch.haarScalar K : ℂ))⁻¹ *
    ∏ p : S, (((μ p).real (p.val.adicCompletionIntegers K : Set (p.val.adicCompletion K)) : ℂ))⁻¹

theorem integers_real_pos (p : S) :
    0 < (μ p).real (p.val.adicCompletionIntegers K : Set (p.val.adicCompletion K)) := by
  rw [measureReal_def, selfDualProbeMeasures_integers,
    ENNReal.toReal_ofReal (localHalfDifferentFactor_pos K p.val).le]
  exact localHalfDifferentFactor_pos K p.val

theorem kappa_ne_zero : kappa A ≠ 0 := by
  unfold kappa
  refine mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr (PoissonArch.haarScalar_pos K).ne'))
    (Finset.prod_ne_zero_iff.mpr fun p _ => inv_ne_zero ?_)
  exact Complex.ofReal_ne_zero.mpr (integers_real_pos A p).ne'

/-- Axiom's characters, measures and the trace character dictionary. -/
structure AxiomInputs where
  e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion K) Circle
  he : ∀ v z, (e v z : ℂ) = psiLocal K v.val z

/-- The skeleton's local Haar measures, on the Borel structures. -/
def localHaar (v : ↥A.Sf) : Measure (v.val.adicCompletion K) :=
  (selfDualProbeMeasures K S).haar v

theorem localHaar_isAddHaar (v : ↥A.Sf) : (localHaar A v).IsAddHaarMeasure :=
  (selfDualProbeMeasures K S).haar_isAddHaar v

theorem sigmaFinite_localHaar (v : ↥A.Sf) : SigmaFinite (localHaar A v) := by
  have : LocallyCompactSpace (v.val.adicCompletion K) :=
    (PoissonS.finite_components_locallyCompact K A.Sf).1 v
  have := localHaar_isAddHaar A v
  infer_instance

/-- Axiom's Poisson additive measure built from the skeleton's local measures. -/
def additiveMeasure : Measure (SLocalProduct K A.Sf) :=
  NormalizedProbe.poissonAdditiveMeasure A (localHaar A)

theorem fourierIntegral_const_mul {X : Type*} [CommRing X] [MeasurableSpace X]
    (ψ : AddChar X ℂ) (ν : Measure X) (g : X → ℂ) (a : ℂ) (w : X) :
    NumberField.AdelicFourier.fourierIntegral ψ ν (fun y => a * g y) w =
      a * NumberField.AdelicFourier.fourierIntegral ψ ν g w := by
  unfold NumberField.AdelicFourier.fourierIntegral
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)

/-- The skeleton's archimedean and local transforms of the test at `(yinf, yf)`, through
Axiom's Fourier transform of the tensor. -/
theorem skeleton_factor (I : AxiomInputs A) (C : Coords) (a : ℂ) (yinf : mixedEmbedding.mixedSpace K)
    (yf : (v : ↥A.Sf) → v.val.adicCompletion K) :
    NumberField.AdelicFourier.fourierIntegral (standardMixedAddCharacter K) volume
        (fun y => schwartzTest A C a ((traceToMixed K).symm y)) yinf *
      ∏ p : S, (((μ p).real (p.val.adicCompletionIntegers K : Set (p.val.adicCompletion K)) : ℂ))⁻¹ *
        NumberField.AdelicFourier.fourierIntegral (psiLocal K p.val) (μ p) (C.fFinite p) (yf p) =
    a * kappa A * ProbeWeight.fourier K A.Sf I.e (additiveMeasure A) (tensor C)
      ((Rmix).symm yinf, yf) := by
  have hfun : (fun y => schwartzTest A C a ((traceToMixed K).symm y)) =
      fun y => a * archFactor A C y := funext (schwartzTest_symm A C a)
  have := sigmaFinite_localHaar A
  have hF := ProbeFourier.fourier_eq A I.e I.he (localHaar A) (archFactor A C) C.fFinite
    (tensor C) (tensor_eq A C) ((Rmix).symm yinf, yf)
  rw [RingEquiv.apply_symm_apply] at hF
  have hR : ProbeWeight.fourier K A.Sf I.e (additiveMeasure A) (tensor C) ((Rmix).symm yinf, yf) =
      (PoissonArch.haarScalar K : ℂ) *
        NumberField.AdelicFourier.fourierIntegral (standardMixedAddCharacter K) volume
          (archFactor A C) yinf *
        ∏ p : S, NumberField.AdelicFourier.fourierIntegral (psiLocal K p.val) (μ p)
          (C.fFinite p) (yf p) :=
    hF
  rw [hR, hfun, fourierIntegral_const_mul, Finset.prod_mul_distrib]
  unfold kappa
  have hh : (PoissonArch.haarScalar K : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (PoissonArch.haarScalar_pos K).ne'
  field_simp
  try ring

theorem additiveFourier_probeTest (I : AxiomInputs A) (C : Coords) (a : ℂ) (lower : ℝ)
    (hlower : 0 < lower) (hcompact) (hnorm) (x : sLocalMultiplicativeGroup K S) :
    additiveFourier K S μ (probeTest A C a lower hlower hcompact hnorm) x =
      a * kappa A * ProbeWeight.fourier K A.Sf I.e (additiveMeasure A) (tensor C)
        (toUnits A x : SLocalProduct K A.Sf) := by
  rw [val_toUnits]
  exact skeleton_factor A I C a _ _

theorem additiveFourierAtZero_probeTest (I : AxiomInputs A) (C : Coords) (a : ℂ) (lower : ℝ)
    (hlower : 0 < lower) (hcompact) (hnorm) :
    additiveFourierAtZero K S μ (probeTest A C a lower hlower hcompact hnorm) =
      a * kappa A * ProbeWeight.fourier K A.Sf I.e (additiveMeasure A) (tensor C) 0 := by
  have h0 : (0 : SLocalProduct K A.Sf) = ((Rmix).symm 0, fun _ => 0) := by
    ext <;> simp
  rw [h0]
  exact skeleton_factor A I C a 0 fun _ => 0

/-- The skeleton's norm-one Haar measure, carried to Axiom's norm-one group. -/
def normOneMeasure : Measure A.G1 :=
  Measure.map (normOneEquiv A).toHomeomorph.toMeasurableEquiv (sUnitHaarMeasure K S)

theorem normOneMeasure_isHaar : (normOneMeasure A).IsHaarMeasure :=
  (normOneEquiv A).isHaarMeasure_map (sUnitHaarMeasure K S)

/-- On each sheet, the skeleton's norm-one integral of the test's transform is `a · κ`
times Axiom's envelope. -/
theorem sheet_integral (I : AxiomInputs A) (C : Coords) (a : ℂ) (lower : ℝ) (hlower : 0 < lower)
    (hcompact) (hnorm) (T : ℝ) (hT : 0 < T) :
    (∫ t : sLocalNormOneGroup K S, additiveFourier K S μ
        (probeTest A C a lower hlower hcompact hnorm)
        ((t : sLocalMultiplicativeGroup K S) * sLocalNormSection K S ⟨T, hT⟩)
        ∂(sUnitHaarMeasure K S)) =
      a * kappa A * ProbeSheet.envelope A I.e (additiveMeasure A) (normOneMeasure A) (tensor C) T := by
  simp_rw [additiveFourier_probeTest A I]
  rw [integral_const_mul]
  congr 1
  unfold ProbeSheet.envelope normOneMeasure
  rw [integral_map_equiv]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  change _ = ProbeWeight.fourier K A.Sf I.e (additiveMeasure A) (tensor C)
    (ProbeSheet.sheetPoint A T (normOneEquiv A t) : SLocalProduct K A.Sf)
  rw [sheetPoint_normOneEquiv A T hT t]

theorem additiveMellin_probeTest (I : AxiomInputs A) (C : Coords) (a : ℂ) (lower : ℝ)
    (hlower : 0 < lower) (hcompact) (hnorm) (z : ℂ) :
    additiveMellin K S μ (probeTest A C a lower hlower hcompact hnorm) z =
      a * kappa A * ∫ T in Ioi (0 : ℝ),
        ProbeSheet.envelope A I.e (additiveMeasure A) (normOneMeasure A) (tensor C) T *
          (T : ℂ) ^ z / (T : ℂ) := by
  unfold additiveMellin
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun T hT => ?_
  have hT' : 0 < T := hT
  simp only [hT', ↓reduceDIte]
  rw [sheet_integral A I C a lower hlower hcompact hnorm T hT']
  ring

/-! ### The choice -/

theorem mul_conj_div_norm (M : ℂ) (hM : M ≠ 0) :
    starRingEnd ℂ M / (‖M‖ : ℂ) * M = (‖M‖ : ℂ) := by
  have hn : (‖M‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hM)
  rw [div_mul_eq_mul_div, Complex.conj_mul', div_eq_iff hn]
  ring

/-- **D-TESTS.** An additive probe test whose additive Fourier transform vanishes at `0`
and whose additive Mellin transform at `1/6` is a positive real. -/
theorem exists_probeTest (hS : A.ContainsTraceBadPlaces) :
    ∃ W : AdditiveProbeTest K S, additiveFourierAtZero K S μ W = 0 ∧
      (additiveMellin K S μ W (1 / 6)).im = 0 ∧ 0 < (additiveMellin K S μ W (1 / 6)).re := by
  obtain ⟨hcont, htrace, -⟩ := PrincipalProbeConstruction.canonical_trace_contract A hS
  let I : AxiomInputs A :=
    ⟨fun v => ResidueTrace.localTraceCharacter v.val,
      fun v z => (TraceDictionary.psiLocal_eq_localTraceCharacter v.val z).symm⟩
  have hne : ∀ v : ↥A.Sf, I.e v ≠ 1 := by
    intro v h
    obtain ⟨x, hx⟩ := SArithmeticData.localTraceCharacter_exists_ne_one v.val
    exact hx (by simpa using DFunLike.congr_fun h x)
  have hμ : (additiveMeasure A).IsAddHaarMeasure := by
    have : (PoissonArch.traceMeasure K).IsAddHaarMeasure :=
      Measure.IsAddHaarMeasure.smul volume
        (ENNReal.ofReal_pos.mpr (PoissonArch.haarScalar_pos K)).ne' ENNReal.ofReal_ne_top
    have := localHaar_isAddHaar A
    have := sigmaFinite_localHaar A
    have : (PoissonS.productMeasure K A.Sf (localHaar A)).IsAddHaarMeasure := by
      unfold PoissonS.productMeasure
      exact Measure.prod.instIsAddHaarMeasure _ _
    unfold additiveMeasure NormalizedProbe.poissonAdditiveMeasure
    apply AddEquiv.isAddHaarMeasure_map
    · exact (poissonHomeomorph A).continuous
    · exact (poissonHomeomorph A).symm.continuous
  have := normOneMeasure_isHaar A
  let ν : Measure (SLocalProduct K A.Sf)ˣ :=
    Measure.map (fun q : ℝ × A.G1 => ProbeSheet.sheetPoint A q.1 q.2)
      (ProbeSheet.radialMeasure.prod (normOneMeasure A))
  have hν : ν.IsHaarMeasure := ProbeSheet.sheet_map_isHaar A (normOneMeasure A)
  obtain ⟨W1, W0, hannular, hcompact, hunits, hnonzero, hzero, hmellin, -⟩ :=
    probe_fixed_weight_construction K A I.e hcont htrace
      (additiveMeasure A) ν hμ hν
  have hME := probe_sheet_mellin_estimates_of_disintegration K A I.e hcont htrace hne
    (additiveMeasure A) ν (normOneMeasure A) hμ hν (normOneMeasure_isHaar A) rfl
    (Classical.arbitrary _) W0 W1 hannular hcompact hunits
  obtain ⟨fR, fC, fF, hr, hc, hf, hW⟩ := hannular
  let C : Coords := ⟨fR, fC, fF, hr, hc, hf⟩
  have hW0 : W0 = tensor C := funext hW
  subst hW0
  have hM : (∫ T in Ioi (0 : ℝ),
      ProbeSheet.envelope A I.e (additiveMeasure A) (normOneMeasure A) (tensor C) T *
        (T : ℂ) ^ (1 / 6 : ℂ) / (T : ℂ)) =
      ProbeWeight.fourierMellin K A.Sf I.e (additiveMeasure A) ν (tensor C) (1 / 6) :=
    (hME.2.2.1 (1 / 6) (by
      rw [show (1 / 6 : ℂ) = ((1 / 6 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
      norm_num)).2.2
  -- The compact support and a lower bound for the norm on it.
  let j : sLocalMultiplicativeGroup K S → SLocalProduct K A.Sf :=
    fun x => (toUnits A x : SLocalProduct K A.Sf)
  have hj : Topology.IsEmbedding j :=
    (ProbeSheet.units_val_isEmbedding A).comp
      ((toGHomeo A).trans (ProbeSheet.localUnitsContinuous A)).toHomeomorph.isEmbedding
  have hrange : tsupport (tensor C) ⊆ range j := by
    intro y hy
    obtain ⟨u, rfl⟩ := hunits hy
    exact ⟨(toG A).symm ((ProbeSheet.localUnits A).symm u), by simp [j, ProbeUnits.toUnits]⟩
  have hpre : IsCompact (j ⁻¹' tsupport (tensor C)) :=
    hj.isInducing.isCompact_preimage' hcompact.isCompact hrange
  have hcpt : HasCompactSupport fun x : sLocalMultiplicativeGroup K S =>
      tensor C (toUnits A x : SLocalProduct K A.Sf) :=
    IsCompact.of_isClosed_subset hpre (isClosed_tsupport _)
      (tsupport_comp_subset_preimage (tensor C) hj.continuous)
  have hnonempty : (j ⁻¹' tsupport (tensor C)).Nonempty := by
    obtain ⟨y, hy⟩ := Function.ne_iff.mp hnonzero
    obtain ⟨x, hx⟩ := hrange (subset_tsupport _ hy)
    exact ⟨x, by rw [mem_preimage, hx]; exact subset_tsupport _ hy⟩
  obtain ⟨x0, -, hmin⟩ := hpre.exists_isMinOn hnonempty
    (continuous_sLocalProductNorm K S).continuousOn
  have hnorm : ∀ x : sLocalMultiplicativeGroup K S,
      tensor C (toUnits A x : SLocalProduct K A.Sf) ≠ 0 →
        sLocalProductNorm K S x0 ≤ sLocalProductNorm K S x :=
    fun x hx => isMinOn_iff.mp hmin x (subset_tsupport _ hx)
  -- The scaling.
  set M := kappa A * ProbeWeight.fourierMellin K A.Sf I.e (additiveMeasure A) ν (tensor C) (1 / 6)
  have hM0 : M ≠ 0 := mul_ne_zero (kappa_ne_zero A) hmellin
  have hval : additiveMellin K S μ (probeTest A C (starRingEnd ℂ M / (‖M‖ : ℂ))
      (sLocalProductNorm K S x0) (sLocalProductNorm_pos K S x0) hcpt hnorm) (1 / 6) =
        (‖M‖ : ℂ) := by
    rw [additiveMellin_probeTest A I, hM, mul_assoc]
    exact mul_conj_div_norm M hM0
  refine ⟨probeTest A C (starRingEnd ℂ M / (‖M‖ : ℂ)) (sLocalProductNorm K S x0)
    (sLocalProductNorm_pos K S x0) hcpt hnorm, ?_, ?_, ?_⟩
  · rw [additiveFourierAtZero_probeTest A I]
    exact mul_eq_zero_of_right _ hzero
  · rw [hval, Complex.ofReal_im]
  · rw [hval, Complex.ofReal_re]
    exact norm_pos_iff.mpr hM0

end ProbeTestChoice

end HeckeAxiom
