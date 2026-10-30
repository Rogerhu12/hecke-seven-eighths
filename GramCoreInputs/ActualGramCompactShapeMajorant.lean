import ActualProbePairOrbitalPoisson
import ActualGramZeroFrequency
import HeckeGeneral.Characters.LocalResidueCosetFourier
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
UNCOMPILED candidate / native0. A real nonnegative additive majorant on any
fixed compact row shape, constructed independently of the arithmetic probe.
It is allowed to contain zero. It is not an AdditiveProbeTest, whose positive
lower-norm support would make a full row-ball majorant impossible.

Finite-place compact-open envelopes are actual finite unions of translates
of the local integer ring; no envelope or positivity assumption is added.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Bridge
open HeckeGeneral.ThetaSkeleton.Global
open ActualAdditiveGramDraft ActualProbePairOrbitalDraft
open scoped Classical BigOperators ComplexConjugate ContDiff

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "SF" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
/-- The actual additive product of the selected finite completions. -/
abbrev gramFiniteAdditiveSpace :=
  (v : (S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K
local notation "Af" => gramFiniteAdditiveSpace K S
local notation "Γ" => sixthPowerUnits K SF

/-- Compact subsets of the actual completion are contained in compact
clopen sets which also contain zero. No valuation cutoff is supplied. -/
theorem exists_local_compact_clopen_envelope
    (v : HeightOneSpectrum (𝓞 K)) (C : Set (v.adicCompletion K)) (hC : IsCompact C) :
    ∃ U : Set (v.adicCompletion K), IsCompact U ∧ IsClopen U ∧ insert 0 C ⊆ U := by
  letI : CompactSpace (LocalIntegerRing K v) :=
    NumberField.AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 K) K v
  let O : Set (v.adicCompletion K) := v.adicCompletionIntegers K
  have hOc : IsCompact O := isCompact_iff_compactSpace.mpr inferInstance
  have hOo : IsClopen O := Valued.isClopen_valuationSubring (v.adicCompletion K)
  let U : v.adicCompletion K → Set (v.adicCompletion K) :=
    fun x => (Homeomorph.addLeft x) '' O
  have hUc (x : v.adicCompletion K) : IsCompact (U x) :=
    hOc.image (Homeomorph.addLeft x).continuous
  have hUo (x : v.adicCompletion K) : IsClopen (U x) :=
    ⟨(Homeomorph.addLeft x).isClosedMap _ hOo.isClosed,
      (Homeomorph.addLeft x).isOpenMap _ hOo.isOpen⟩
  have hcover : insert 0 C ⊆ ⋃ x, U x := by
    intro x _
    apply mem_iUnion.mpr
    refine ⟨x, 0, ?_, ?_⟩
    · exact zero_mem (v.adicCompletionIntegers K)
    · simp
  obtain ⟨t, ht⟩ := (hC.insert 0).elim_finite_subcover U
    (fun x => (hUo x).isOpen) hcover
  exact ⟨⋃ x ∈ t, U x, t.isCompact_biUnion (fun x _ => hUc x),
    isClopen_biUnion_finset (fun x _ => hUo x), ht⟩

/-- Extend a finite-place family to the exact all-place API used by the
proved generic periodic Poisson formula. -/
def gramFiniteExtension (h : ∀ v : SF, v.val.adicCompletion K → ℂ)
    (v : HeightOneSpectrum (𝓞 K)) : v.adicCompletion K → ℂ :=
  if hv : v ∈ S then h ⟨v, hv⟩ else 0

@[simp] theorem gramFiniteExtension_at (h : ∀ v : SF, v.val.adicCompletion K → ℂ)
    (v : SF) : gramFiniteExtension K S h v.val = h v := by
  unfold gramFiniteExtension
  split_ifs with hv
  · rfl
  · exact (hv v.property).elim

/-- A constructed tensor which is one on the prescribed compact shape,
real nonnegative everywhere, and one at zero. The arithmetic probe is not
changed or used as an existence assumption. -/
theorem exists_compact_shape_majorant (C : Set (V × Af)) (hC : IsCompact C) :
    ∃ φ : SchwartzMap V ℂ, ∃ h : ∀ v : SF, v.val.adicCompletion K → ℂ,
      (∀ v, IsLocallyConstant (h v)) ∧ (∀ v, HasCompactSupport (h v)) ∧
      (∀ v x, h v x = 0 ∨ h v x = 1) ∧
      (∀ x : V, (φ x).im = 0 ∧ 0 ≤ (φ x).re) ∧
      φ 0 = 1 ∧ (∀ v, h v 0 = 1) ∧
      (∀ z : V × Af, (φ z.1 * ∏ v : SF, h v (z.2 v)).im = 0 ∧
        0 ≤ (φ z.1 * ∏ v : SF, h v (z.2 v)).re) ∧
      (∀ z ∈ C, φ z.1 * ∏ v : SF, h v (z.2 v) = 1) := by
  obtain ⟨R, hR, hbound⟩ := (hC.image continuous_fst).isBounded.exists_pos_norm_le
  let b : ContDiffBump (0 : V) :=
    { rIn := R
      rOut := R + 1
      rIn_pos := hR
      rIn_lt_rOut := by linarith }
  let φ : SchwartzMap V ℂ :=
    (b.hasCompactSupport.smul_right (f' := fun _ : V => (1 : ℂ))).toSchwartzMap
      (b.contDiff.smul contDiff_const)
  have hφ (x : V) : φ x = (b x : ℂ) := by
    change b x • (1 : ℂ) = _
    simp only [Complex.real_smul, mul_one]
  have hφreal (x : V) : (φ x).im = 0 ∧ 0 ≤ (φ x).re := by
    rw [hφ]
    exact ⟨Complex.ofReal_im _, b.nonneg⟩
  have hφzero : φ 0 = 1 := by
    rw [hφ, b.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall, dist_self] using hR.le)]
    rfl
  have hφC (z : V × Af) (hz : z ∈ C) : φ z.1 = 1 := by
    rw [hφ]
    have hb : b z.1 = 1 := by
      apply b.one_of_mem_closedBall
      change dist z.1 0 ≤ R
      rw [dist_zero_right]
      exact hbound z.1 (mem_image_of_mem _ hz)
    rw [hb]
    rfl
  have hlocal (v : SF) : ∃ U : Set (v.val.adicCompletion K),
      IsCompact U ∧ IsClopen U ∧
        insert 0 ((fun z : V × Af => z.2 v) '' C) ⊆ U :=
    exists_local_compact_clopen_envelope K v.val _
      (hC.image ((continuous_apply v).comp continuous_snd))
  choose U hUc hUo hUC using hlocal
  let h : ∀ v : SF, v.val.adicCompletion K → ℂ :=
    fun v => (U v).indicator (fun _ => 1)
  have hlc (v : SF) : IsLocallyConstant (h v) :=
    (LanglandsTunnell.TateLocal.IsSchwartzBruhat.indicator_const (hUo v) (hUc v) (1 : ℂ)).1
  have hcs (v : SF) : HasCompactSupport (h v) :=
    (LanglandsTunnell.TateLocal.IsSchwartzBruhat.indicator_const (hUo v) (hUc v) (1 : ℂ)).2
  have hrange (v : SF) (x : v.val.adicCompletion K) : h v x = 0 ∨ h v x = 1 := by
    by_cases hx : x ∈ U v
    · exact Or.inr (Set.indicator_of_mem hx _)
    · exact Or.inl (Set.indicator_of_notMem hx _)
  have hzero (v : SF) : h v 0 = 1 :=
    Set.indicator_of_mem (hUC v (mem_insert _ _)) _
  have hCeq (z : V × Af) (hz : z ∈ C) : φ z.1 * ∏ v : SF, h v (z.2 v) = 1 := by
    have hh (v : SF) : h v (z.2 v) = 1 :=
      Set.indicator_of_mem (hUC v (mem_insert_of_mem _ (mem_image_of_mem _ hz))) _
    simp only [hφC z hz, hh, Finset.prod_const_one, mul_one]
  have hnonneg (z : V × Af) : (φ z.1 * ∏ v : SF, h v (z.2 v)).im = 0 ∧
      0 ≤ (φ z.1 * ∏ v : SF, h v (z.2 v)).re := by
    by_cases hz : ∃ v : SF, h v (z.2 v) = 0
    · obtain ⟨v, hv⟩ := hz
      rw [Finset.prod_eq_zero (Finset.mem_univ v) hv, mul_zero]
      exact ⟨rfl, le_rfl⟩
    · have hh (v : SF) : h v (z.2 v) = 1 :=
        (hrange v _).resolve_left (fun hv => hz ⟨v, hv⟩)
      simp only [hh, Finset.prod_const_one, mul_one]
      exact hφreal z.1
  exact ⟨φ, h, hlc, hcs, hrange, hφreal, hφzero, hzero, hnonneg, hCeq⟩

/-- The actual chosen archimedean test; the choice depends only on the fixed
compact shape and not on the arithmetic data, ideals, or moving radius. -/
def compactShapeArchTest (C : Set (V × Af)) (hC : IsCompact C) : SchwartzMap V ℂ :=
  (exists_compact_shape_majorant K S C hC).choose

def compactShapeFiniteTest (C : Set (V × Af)) (hC : IsCompact C) :
    ∀ v : SF, v.val.adicCompletion K → ℂ :=
  (exists_compact_shape_majorant K S C hC).choose_spec.choose

theorem compactShapeMajorant_spec (C : Set (V × Af)) (hC : IsCompact C) :
    let φ := compactShapeArchTest K S C hC
    let h := compactShapeFiniteTest K S C hC
    (∀ v, IsLocallyConstant (h v)) ∧ (∀ v, HasCompactSupport (h v)) ∧
    (∀ v x, h v x = 0 ∨ h v x = 1) ∧
    (∀ x : V, (φ x).im = 0 ∧ 0 ≤ (φ x).re) ∧
    φ 0 = 1 ∧ (∀ v, h v 0 = 1) ∧
    (∀ z : V × Af, (φ z.1 * ∏ v : SF, h v (z.2 v)).im = 0 ∧
      0 ≤ (φ z.1 * ∏ v : SF, h v (z.2 v)).re) ∧
    (∀ z ∈ C, φ z.1 * ∏ v : SF, h v (z.2 v) = 1) :=
  (exists_compact_shape_majorant K S C hC).choose_spec.choose_spec

def compactShapeFiniteFamily (C : Set (V × Af)) (hC : IsCompact C)
    (v : HeightOneSpectrum (𝓞 K)) : v.adicCompletion K → ℂ :=
  gramFiniteExtension K S (compactShapeFiniteTest K S C hC) v

theorem compactShapeFiniteFamily_locallyConstant (C : Set (V × Af)) (hC : IsCompact C)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S) :
    IsLocallyConstant (compactShapeFiniteFamily K S C hC v) := by
  simpa only [compactShapeFiniteFamily, gramFiniteExtension, dif_pos hv] using
    (compactShapeMajorant_spec K S C hC).1 ⟨v, hv⟩

theorem compactShapeFiniteFamily_compactSupport (C : Set (V × Af)) (hC : IsCompact C)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S) :
    HasCompactSupport (compactShapeFiniteFamily K S C hC v) := by
  simpa only [compactShapeFiniteFamily, gramFiniteExtension, dif_pos hv] using
    (compactShapeMajorant_spec K S C hC).2.1 ⟨v, hv⟩

/-- In particular the original zero term has the proved value one; it is
not removed by a fictitious multiplicative annular-support argument. -/
theorem compactShapeMajorant_zero (C : Set (V × Af)) (hC : IsCompact C) :
    compactShapeArchTest K S C hC 0 *
      ∏ v : SF, compactShapeFiniteFamily K S C hC v.val 0 = 1 := by
  rcases compactShapeMajorant_spec K S C hC with
    ⟨_, _, _, _, hzero, hfinitezero, _, _⟩
  simp only [compactShapeFiniteFamily, gramFiniteExtension_at, hzero,
    hfinitezero, Finset.prod_const_one, mul_one]

/-- The literal principal zero tensor in adelic Poisson is one for this
constructed test, including the finite-place factors. -/
theorem compactShapeMajorant_tensor_zero (C : Set (V × Af)) (hC : IsCompact C) :
    sIntegerTensorTerm K S
      (traceSchwartzToMixed K (compactShapeArchTest K S C hC))
      (compactShapeFiniteFamily K S C hC) 0 = 1 := by
  rcases compactShapeMajorant_spec K S C hC with
    ⟨_, _, _, _, harchzero, hfinitezero, _, _⟩
  have hf : ∀ v ∈ S, compactShapeFiniteFamily K S C hC v 0 = 1 := by
    intro v hv
    simpa only [compactShapeFiniteFamily, gramFiniteExtension, dif_pos hv] using
      hfinitezero ⟨v, hv⟩
  have hp : (∏ v ∈ S, compactShapeFiniteFamily K S C hC v 0) = 1 :=
    Finset.prod_eq_one hf
  simp only [sIntegerTensorTerm, map_zero, traceSchwartzToMixed_apply, harchzero, hp,
    mul_one]

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (μf : Measure (FiniteAdeleRing (𝓞 K) K)) [μf.IsAddHaarMeasure]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
variable (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

local instance majorant_sixthUnits_finiteIndex : Subgroup.FiniteIndex Γ :=
  sUnit_power_range_finiteIndex K SF 6 (by decide)

include μ μf in
/-- Actual negative-Gauss-pair orbital Poisson with a constructed free
compact-shape majorant. P supplies only the original arithmetic and Gauss
coefficients; its annular additive test is never substituted for this test.
Both zero terms, the discriminant factor and the actual covolume remain. -/
theorem compactShapeMajorant_actual_pair_orbital_poisson
    (C : Set (V × Af)) (hC : IsCompact C)
    (P : ProbeData K SF) (I J : ExteriorIdeal K SF) (r : {r : ℝ // 0 < r}) :
    let φ := compactShapeArchTest K S C hC
    let h := compactShapeFiniteFamily K S C hC
    sIntegerWeightedOrbitalSeries K S Γ φ (sIntegerFiniteTestFunction K S h) r
        (probeNegativeGaussPairOrbitWeight K S P I J) =
      ((r.val : ℂ)⁻¹ * additiveGramPoissonFieldFactor K) *
        sIntegerWeightedOrbitalSeries K S Γ (traceSchwartzFourier K φ)
          (sIntegerFiniteFourierTestFunction K S μv h)
          (additiveGramPairDualRadius K S P I J r)
          (probeOriginalCorrelationOrbitWeight K S P I J) +
      ((sUnitHaarCovolume K SF Γ).toReal : ℂ) *
        (((r.val : ℂ)⁻¹ * additiveGramPoissonFieldFactor K) *
            (additiveGramFullCorrelation K S P I J 0 *
              sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K φ) h 0) -
          (probeGauss K SF P I 0 * conj (probeGauss K SF P J 0)) *
            sIntegerTensorTerm K S (traceSchwartzToMixed K φ) h 0) := by
  simpa only [additiveGramPairDualRadius, additiveGramPairModulus,
    additiveGramFullCorrelation, additiveGramPoissonFieldFactor] using
    probeGauss_pair_orbital_poisson (K := K) (S := S) (P := P) (I := I) (J := J)
      (ν := μf) (μv := μv) (μ := μ)
      (compactShapeArchTest K S C hC) (compactShapeFiniteFamily K S C hC)
      (compactShapeFiniteFamily_locallyConstant K S C hC)
      (compactShapeFiniteFamily_compactSupport K S C hC) r

end HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
