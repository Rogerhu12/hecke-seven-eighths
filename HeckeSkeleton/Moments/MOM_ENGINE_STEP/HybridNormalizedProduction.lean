import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridOrdinaryProduction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FiniteNormalizedChildren
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCapacityChildIntegrability
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalProfileNormalizationInput

/-!
# Actual ordinary rectangles in the concrete normalized child family

Each side starts with the original arithmetic calibration, its raw
prime estimates and its individual profile window. Dividing every
actual profile by the same positive amplitude proves the normalized
prime estimates internally. The four original rectangle pairs then
form a concrete finite normalized family.

The original right-side conjugation and negative first Fourier
location are already present in the side frame. No replacement of its
energy, correlation, arithmetic normalizer or row set is made here.
The selected children lie in a fixed profile unit ball, and finite
single-atom controls prove their integrability for the same two
Fourier measures with the exact pre-removal envelope.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open WholeAllocation

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {ω ψ : HeckeCharacter K}

namespace ActualAllocatedSource.Calibration.CapacityInput

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {k : ℕ} {s : ActualAllocatedSource A V H k}
variable {cal : s.Calibration (σ := σ) ω ψ}

/-- The normalized prime bound is a consequence of the original
individual prime estimate and the literal common profile rescaling. -/
def normalized (input : cal.CapacityInput)
    (amplitude : V → ℝ) (hpos : ∀ ξ, 0 < amplitude ξ)
    (bounds : Fin s.allocation.keep.card → ℝ) (hbound : ∀ i, 0 ≤ bounds i)
    (hfactor : ∀ ξ i, input.primeBound ξ i = amplitude ξ ^ 2 * bounds i) :
    cal.NormalizedCapacityData where
  geometry := input.skeleton
  b₂ := input.b₂
  p₂ := input.p₂
  boundary := input.boundary
  ell := input.ell
  gap := input.gap
  δ := input.delta
  mesh := input.mesh
  supportError := input.supportError
  rawClipError := input.rawClipError
  widthError := input.widthError
  leftAnnulus := input.leftAnnulus
  rightAnnulus := input.rightAnnulus
  leftAnnulus_one := input.leftAnnulus_one
  rightAnnulus_one := input.rightAnnulus_one
  left_annulus := input.left_window
  right_annulus := input.right_window
  gap_pos := input.gap_pos
  kappa_pos := input.kappa_pos
  mesh_nonneg := input.mesh_nonneg
  fits_mesh := input.mesh_bound
  enlargement := input.enlargement
  unit_length := input.unit_part
  actual_width := input.actual_width
  boundary_width := input.delta_bound
  radical_length := input.principal_part
  boundary_nonneg := input.boundary_nonneg
  parent_capacity := input.parent_capacity
  common_length := input.common_part
  paid_shift := input.paid_shift
  raw_length := input.raw_degree
  width_error := input.width_error
  budget_nonneg := input.budget_nonneg
  charge_nonneg := input.charge_nonneg
  radius := amplitude
  radius_pos := hpos
  primeBound := bounds
  primeBound_nonneg := hbound
  prime_bound := by
    intro ξ u hu i
    rw [primePolynomial_normalizedMomentProfiles, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hpos ξ)), mul_pow]
    have h := mul_le_mul_of_nonneg_left (input.prime_bound ξ u hu i)
      (sq_nonneg ((amplitude ξ)⁻¹))
    rw [hfactor ξ i] at h
    apply h.trans_eq
    field_simp [(hpos ξ).ne'] <;> ring

theorem normalized_exponent (input : cal.CapacityInput)
    (amplitude : V → ℝ) (hpos : ∀ ξ, 0 < amplitude ξ)
    (bounds : Fin s.allocation.keep.card → ℝ) (hbound : ∀ i, 0 ≤ bounds i)
    (hfactor : ∀ ξ i, input.primeBound ξ i = amplitude ξ ^ 2 * bounds i) :
    (input.normalized amplitude hpos bounds hbound hfactor).exponent = input.exponent := rfl

end ActualAllocatedSource.Calibration.CapacityInput

/-- Freezing a permitted original height makes the same profile window
valid at every new height, including the common zero-twist output. -/
def RawProfileWindow.freezeTime
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain window : Set ℝ}
    {seminorms : Finset (ℕ × ℕ)} {d : MomentData K ω ψ} {B : ℝ}
    (raw : RawProfileWindow rowDomain heightDomain window seminorms d B)
    (t₀ : ℝ) (ht₀ : t₀ ∈ heightDomain) :
    RawProfileWindow rowDomain Set.univ window seminorms (frozenMomentProfiles d t₀) B where
  inverseRep u _ := raw.inverseRep u t₀
  leftRep u _ := raw.leftRep u t₀
  rightRep u _ := raw.rightRep u t₀
  primeRep i _ := raw.primeRep i t₀
  inverse_eq u t y := by
    simpa only [frozenMomentProfiles, MomentData.separatedProfiles,
      IdealTest.freezeTwist, profilePower_zero, mul_one] using raw.inverse_eq u t₀ y
  left_eq u t y := by
    simpa only [frozenMomentProfiles, MomentData.separatedProfiles,
      IdealTest.freezeTwist, profilePower_zero, mul_one] using raw.left_eq u t₀ y
  right_eq u t y := by
    simpa only [frozenMomentProfiles, MomentData.separatedProfiles,
      IdealTest.freezeTwist, profilePower_zero, mul_one] using raw.right_eq u t₀ y
  prime_eq i t y := by
    simpa only [frozenMomentProfiles, MomentData.separatedProfiles,
      SlotGeometry.freezeTwists, PrimeWindow.freezeTwist, profilePower_zero, mul_one] using
      raw.prime_eq i t₀ y
  inverse_support u hu _ _ := raw.inverse_support u hu t₀ ht₀
  left_support u hu _ _ := raw.left_support u hu t₀ ht₀
  right_support u hu _ _ := raw.right_support u hu t₀ ht₀
  prime_support i _ _ := raw.prime_support i t₀ ht₀
  inverse_bound u hu _ _ := raw.inverse_bound u hu t₀ ht₀
  left_bound u hu _ _ := raw.left_bound u hu t₀ ht₀
  right_bound u hu _ _ := raw.right_bound u hu t₀ ht₀
  prime_bound i _ _ := raw.prime_bound i t₀ ht₀

namespace SecondSideNormalization

variable {H ι V : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {side : SecondColumnSide} {k : ℕ}
variable {f : SecondSideFrame (V := V) C R Ray side k}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain window : Set ℝ}
variable {seminorms : Finset (ℕ × ℕ)}
variable (N : SecondSideNormalization f ω ψ rowDomain heightDomain window seminorms)

def normalizedCapacityData : N.calibration.NormalizedCapacityData :=
  N.capacity.normalized N.amplitude N.amplitude_pos N.bounds N.bounds_nonneg N.factor

/-- Membership in the fixed unit ball follows from the individual raw
Schwartz profiles, after the actual fixed slot restriction. -/
theorem child_in_fixed_window (out : N.normalizedCapacityData.Child) (ξ : V) :
    InFixedProfileWindow rowDomain heightDomain window seminorms (out.data ξ) := by
  rw [out.data_eq_normalized_raw]
  apply normalizedMomentProfiles_in_fixed_window (N.amplitude_pos ξ)
  exact (N.profile ξ).restrictSlots
    (lengthSelection (N.calibration.clippedData ξ) f.source.allocation.keep.card
      (N.calibration.count ξ) (Finset.univ \ out.removed))

theorem frozen_child_in_fixed_window (out : N.normalizedCapacityData.Child) (ξ : V)
    (hheight : N.calibration.height ξ ∈ heightDomain) :
    InFixedProfileWindow rowDomain Set.univ window seminorms (out.frozenData ξ) := by
  obtain ⟨raw⟩ := N.child_in_fixed_window out ξ
  exact ⟨raw.freezeTime (N.calibration.height ξ) hheight⟩

end SecondSideNormalization

namespace HybridOrdinaryRectangles

variable {H : Type} {ι V : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {k l : ℕ}
variable {S₁ S₂ : Finset (Ideal (𝓞 K))} {S : Fin k → Finset (HeightOneSpectrum (𝓞 K))}
variable {T₁ T₂ : Finset (Ideal (𝓞 K))} {T : Fin l → Finset (HeightOneSpectrum (𝓞 K))}
variable {IA : AllocationColumn K k → A.Exterior} {IB : AllocationColumn K l → A.Exterior}
variable {rayLeft : AllocationColumn K k → Ray} {rayRight : AllocationColumn K l → Ray}
variable {wholeLeft : AllocationColumn K k → ℂ} {wholeRight : AllocationColumn K l → ℂ}
variable {x : H → AllocationColumn K k → V} {y : H → AllocationColumn K l → V}
variable {b : liveSecondAllocationBranches (Ray := Ray) S₁ S₂ S T₁ T₂ T IB}
variable {exceptional : H → Prop}
variable (B : HybridOrdinaryRectangles R Ray S₁ S₂ S T₁ T₂ T IA IB
  rayLeft rayRight wholeLeft wholeRight x y b exceptional)
variable (C : A.GeneralArithmeticContext σ η hS)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain window : Set ℝ}
variable {seminorms : Finset (ℕ × ℕ)}
variable (lc : ∀ r : Bool, SecondSideNormalization (B.leftFrame C r)
  ω ψ rowDomain heightDomain window seminorms)
variable (rc : ∀ r : Bool, SecondSideNormalization (B.rightFrame C r)
  ω ψ rowDomain heightDomain window seminorms)
variable (Z : ℝ)
variable (hleftBase : ∀ r, (B.leftFrame C r).source.base = Z)
variable (hrightBase : ∀ r, (B.rightFrame C r).source.base = Z)

/-- The four original ordinary rectangle pairs are the finite carrier.
The family computes active labels and fixed deletions itself. -/
def normalizedFamily : ActualNormalizedPairFamily A σ V (Bool × Bool) ω ψ Z where
  LeftRow _ := (R.restrictRows (fun h => ¬exceptional h)).live
  RightRow _ := (R.restrictRows (fun h => ¬exceptional h)).live
  leftSlots _ := k
  rightSlots _ := l
  leftSource rs := (B.leftFrame C rs.1).source
  rightSource rs := (B.rightFrame C rs.2).source
  leftCalibration rs := (lc rs.1).calibration
  rightCalibration rs := (rc rs.2).calibration
  leftCapacity rs := (lc rs.1).normalizedCapacityData
  rightCapacity rs := (rc rs.2).normalizedCapacityData
  left_base rs := hleftBase rs.1
  right_base rs := hrightBase rs.2
  leftNormalizer rs := (B.leftFrame C rs.1).normalizer
  rightNormalizer rs := (B.rightFrame C rs.2).normalizer

theorem normalizedFamily_sourcePair (parentWidth : ℝ) (rs : Bool × Bool) (ξ : V) :
    (B.normalizedFamily C lc rc Z hleftBase hrightBase).sourcePair parentWidth rs ξ =
      Real.sqrt ((B.leftFrame C rs.1).energy ξ) *
        Real.sqrt ((B.rightFrame C rs.2).energy ξ) / Z ^ parentWidth := by
  change (Real.sqrt (‖(B.leftFrame C rs.1).normalizer‖ ^ 2 *
    (B.leftFrame C rs.1).source.energy (σ := σ) ξ) *
      Real.sqrt (‖(B.rightFrame C rs.2).normalizer‖ ^ 2 *
        (B.rightFrame C rs.2).source.energy (σ := σ) ξ)) / Z ^ parentWidth = _
  rw [← (B.leftFrame C rs.1).energy_eq_source,
    ← (B.rightFrame C rs.2).energy_eq_source]

/-- The original ordinary source is compared with all four original
frame pairs before identically zero pairs are removed. -/
theorem ordinary_le_source_pairs (parentWidth : ℝ) (hZ : 0 < Z) (ξ : V) :
    B.originalIntegrand ξ / Z ^ parentWidth ≤
      ∑ rs : Bool × Bool,
        (B.normalizedFamily C lc rc Z hleftBase hrightBase).sourcePair parentWidth rs ξ := by
  have hb := div_le_div_of_nonneg_right (B.ordinary_le_rectangles C ξ)
    (Real.rpow_nonneg hZ.le parentWidth)
  have he : (∑ rs : Bool × Bool,
      (B.normalizedFamily C lc rc Z hleftBase hrightBase).sourcePair parentWidth rs ξ) =
      (Real.sqrt ((B.leftFrame C false).energy ξ) *
          Real.sqrt ((B.rightFrame C false).energy ξ) +
        Real.sqrt ((B.leftFrame C false).energy ξ) *
          Real.sqrt ((B.rightFrame C true).energy ξ) +
        Real.sqrt ((B.leftFrame C true).energy ξ) *
          Real.sqrt ((B.rightFrame C false).energy ξ) +
        Real.sqrt ((B.leftFrame C true).energy ξ) *
          Real.sqrt ((B.rightFrame C true).energy ξ)) / Z ^ parentWidth := by
    simp only [B.normalizedFamily_sourcePair C lc rc Z hleftBase hrightBase]
    rw [Fintype.sum_prod_type]
    simp <;> ring
  exact hb.trans_eq he.symm

/-- This is the original ordinary integrand, divided by its parent
normalization, bounded by the computed actual finite child family. -/
theorem ordinary_le_normalized_family (parentWidth : ℝ) (hZ : 0 < Z) (ξ : V) :
    let family := B.normalizedFamily C lc rc Z hleftBase hrightBase
    B.originalIntegrand ξ / Z ^ parentWidth ≤
      ∑ rs : family.active Finset.univ,
        family.weight Finset.univ parentWidth rs *
          family.envelope Finset.univ rs ξ * family.childPair Finset.univ rs ξ := by
  exact (B.ordinary_le_source_pairs C lc rc Z hleftBase hrightBase parentWidth hZ ξ).trans
    ((B.normalizedFamily C lc rc Z hleftBase hrightBase).finite_pointwise
      Finset.univ parentWidth hZ ξ)

/-- The fixed normalized-profile family contains each retained actual
child; the original evaluation height is frozen into that child's data. -/
theorem normalizedFamily_in_fixed_window
    (hleftHeight : ∀ r ξ, (lc r).calibration.height ξ ∈ heightDomain)
    (hrightHeight : ∀ r ξ, (rc r).calibration.height ξ ∈ heightDomain) :
    let family := B.normalizedFamily C lc rc Z hleftBase hrightBase
    ∀ rs : family.active Finset.univ, ∀ ξ,
      InFixedProfileWindow rowDomain Set.univ window seminorms
        (family.leftData Finset.univ rs ξ) ∧
      InFixedProfileWindow rowDomain Set.univ window seminorms
        (family.rightData Finset.univ rs ξ) := by
  dsimp only
  intro rs ξ
  exact ⟨(lc rs.val.1).frozen_child_in_fixed_window
      ((B.normalizedFamily C lc rc Z hleftBase hrightBase).leftChild Finset.univ rs) ξ
      (hleftHeight rs.val.1 ξ),
    (rc rs.val.2).frozen_child_in_fixed_window
      ((B.normalizedFamily C lc rc Z hleftBase hrightBase).rightChild Finset.univ rs) ξ
      (hrightHeight rs.val.2 ξ)⟩

end HybridOrdinaryRectangles

namespace ActualNormalizedPairFamily

section ProductIntegrability

variable {U E Λ : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Z : ℝ}
variable (family : ActualNormalizedPairFamily A σ (WithLp 2 (U × E)) Λ ω ψ Z)
variable (labels : Finset Λ)

/-- Keep the original two Fourier variables and put the exact
pre-removal envelope and arithmetic branch weight in one positive measure. -/
def productKernel (F₁ : 𝓢(U, ℂ)) (F₂ : 𝓢(E, ℂ))
    (parentWidth : ℝ) (b : family.active labels) : Measure (U × E) :=
  ENNReal.ofReal (family.weight labels parentWidth b) •
    (nestedFourierMeasure F₁ F₂).withDensity
      (fun z => ENNReal.ofReal (family.envelope labels b (WithLp.toLp 2 z)))

/-- The two actual frozen normalized energies, and their Cauchy product,
are integrable for this same branch kernel. Only original finite
single-atom controls and individual polynomial radii are assumed. -/
theorem productKernel_children_integrable
    (F₁ : 𝓢(U, ℂ)) (F₂ : 𝓢(E, ℂ))
    (parentWidth : ℝ) (hZ : 0 < Z) (b : family.active labels)
    (calL : ActualFiniteFamilyControl
      (fun z => (family.leftChild labels b).rawData (WithLp.toLp 2 z))
      (family.leftChild labels b).retainedCount
      (fun z => (family.leftChild labels b).raw_count (WithLp.toLp 2 z))
      (family.leftParameters labels b) Z
      (fun z => (family.leftCalibration b.val).height (WithLp.toLp 2 z)))
    (calR : ActualFiniteFamilyControl
      (fun z => (family.rightChild labels b).rawData (WithLp.toLp 2 z))
      (family.rightChild labels b).retainedCount
      (fun z => (family.rightChild labels b).raw_count (WithLp.toLp 2 z))
      (family.rightParameters labels b) Z
      (fun z => (family.rightCalibration b.val).height (WithLp.toLp 2 z)))
    (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (J₁₁ J₁₂ J₂₁ J₂₂ : ℕ)
    (hleftRadius : ∀ z, (family.leftCapacity b.val).radius (WithLp.toLp 2 z) =
      polynomialProfileRadius B₁ J₁₁ J₁₂ z)
    (hrightRadius : ∀ z, (family.rightCapacity b.val).radius (WithLp.toLp 2 z) =
      polynomialProfileRadius B₂ J₂₁ J₂₂ z) :
    Integrable (fun z => normalizedPairedEnergy
      (family.leftData labels b (WithLp.toLp 2 z)) (family.leftParameters labels b) Z 0)
      (family.productKernel labels F₁ F₂ parentWidth b) ∧
    Integrable (fun z => normalizedPairedEnergy
      (family.rightData labels b (WithLp.toLp 2 z)) (family.rightParameters labels b) Z 0)
      (family.productKernel labels F₁ F₂ parentWidth b) ∧
    Integrable (fun z =>
      Real.sqrt (normalizedPairedEnergy (family.leftData labels b (WithLp.toLp 2 z))
        (family.leftParameters labels b) Z 0) *
      Real.sqrt (normalizedPairedEnergy (family.rightData labels b (WithLp.toLp 2 z))
        (family.rightParameters labels b) Z 0))
      (family.productKernel labels F₁ F₂ parentWidth b) := by
  have hi := normalized_capacity_children_nested_actual_integrable
    (family.leftChild labels b) (family.rightChild labels b) Z hZ calL calR
    F₁ F₂ B₁ B₂ hB₁ hB₂ J₁₁ J₁₂ J₂₁ J₂₂ hleftRadius hrightRadius
  constructor
  · simpa only [leftData, leftParameters, productKernel, envelope,
      ActualAllocatedSource.Calibration.NormalizedCapacityData.Child.frozenData,
      normalizedPairedEnergy_frozenMomentProfiles] using
      hi.1.smul_measure (c := ENNReal.ofReal (family.weight labels parentWidth b))
        ENNReal.ofReal_ne_top
  constructor
  · simpa only [rightData, rightParameters, productKernel, envelope,
      ActualAllocatedSource.Calibration.NormalizedCapacityData.Child.frozenData,
      normalizedPairedEnergy_frozenMomentProfiles] using
      hi.2.1.smul_measure (c := ENNReal.ofReal (family.weight labels parentWidth b))
        ENNReal.ofReal_ne_top
  · simpa only [leftData, rightData, leftParameters, rightParameters, productKernel, envelope,
      ActualAllocatedSource.Calibration.NormalizedCapacityData.Child.frozenData,
      normalizedPairedEnergy_frozenMomentProfiles] using
      hi.2.2.smul_measure (c := ENNReal.ofReal (family.weight labels parentWidth b))
        ENNReal.ofReal_ne_top

end ProductIntegrability

end ActualNormalizedPairFamily

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.CapacityInput.normalized
#print axioms HeckeSkeleton.Moments.EngineStep.HybridOrdinaryRectangles.ordinary_le_normalized_family
#print axioms HeckeSkeleton.Moments.EngineStep.HybridOrdinaryRectangles.normalizedFamily_in_fixed_window
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.productKernel_children_integrable

