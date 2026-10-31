import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedCapacityRawBridge
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCapacityCanonicalBridge
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalCapacityKernelMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualChildAllowance
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedHybridLeaves

/-!
# Canonical costs on the actual normalized hybrid family

The original normalization data are rewired to the proved arithmetic
row, frozen-scalar and original-fibre costs before the finite child
family is produced.  The source, profile representatives, raw prime
bounds, original Gauss normalizers and all Fourier locations remain
literal.  Every chosen normalized child is then viewed as the raw
capacity child with the same deletion.  This identifies the mass of
the finite-family kernel with the canonical arithmetic kernel.
-/

noncomputable section
open scoped Classical BigOperators NumberField FourierTransform SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments CommonSupportMass

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ω ψ : HeckeCharacter F}
variable [IsPrincipalIdealRing A.R]

namespace SecondSideNormalization

variable {H ι V : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {side : SecondColumnSide} {k kLeft kRight : ℕ}
variable {f : SecondSideFrame (V := V) C R Ray side k}
variable {rowDomain : Set (NonzeroIdeal F)} {heightDomain window : Set ℝ}
variable {seminorms : Finset (ℕ × ℕ)}
variable (S : SecondSideNormalization f ω ψ rowDomain heightDomain window seminorms)

/-- Choose the numerical costs from original atoms and original ideal
fibres. No estimate on the old calibration's numerical fields is used. -/
def withArithmeticCosts (W : ActualSecondRowMass R C kLeft kRight)
    (B : f.source.FrozenAtomBounds) :
    SecondSideNormalization f ω ψ rowDomain heightDomain window seminorms :=
  S.withCosts W.rowBound B.scalarBound W.originalFiber W.rowBound_nonneg B.scalarBound_nonneg
    (f.arithmeticCalibration S.calibration W B).row_bound
    (f.arithmeticCalibration S.calibration W B).scalar_bound
    (f.arithmeticCalibration S.calibration W B).fibers

theorem withArithmeticCosts_calibration (W : ActualSecondRowMass R C kLeft kRight)
    (B : f.source.FrozenAtomBounds) :
    (S.withArithmeticCosts W B).calibration = f.arithmeticCalibration S.calibration W B := rfl

theorem withArithmeticCosts_data (W : ActualSecondRowMass R C kLeft kRight)
    (B : f.source.FrozenAtomBounds) :
    (S.withArithmeticCosts W B).calibration.data = S.calibration.data := rfl

theorem withArithmeticCosts_parameters (W : ActualSecondRowMass R C kLeft kRight)
    (B : f.source.FrozenAtomBounds) :
    (S.withArithmeticCosts W B).calibration.parameters = S.calibration.parameters := rfl

theorem withArithmeticCosts_amplitude (W : ActualSecondRowMass R C kLeft kRight)
    (B : f.source.FrozenAtomBounds) :
    (S.withArithmeticCosts W B).amplitude = S.amplitude := rfl

end SecondSideNormalization

namespace ActualHybridLeaf.NormalizationData

variable {H : Type} {ι U E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {leaf : ActualHybridLeaf F H U E} {C : A.GeneralArithmeticContext σ η hS}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray] {Z : ℝ}
variable {rowDomain : Set (NonzeroIdeal F)} {heightDomain window : Set ℝ}
variable {seminorms : Finset (ℕ × ℕ)}
variable (N : leaf.NormalizationData (ι := ι) C Ray ω ψ Z rowDomain heightDomain window seminorms)
variable {kLeft kRight : ℕ}
variable (W : ActualSecondRowMass (N.rows.restrictRows (fun h => ¬leaf.exceptional h)) C kLeft kRight)
variable (BL : ∀ r, (N.rectangles.leftFrame C r).source.FrozenAtomBounds)
variable (BR : ∀ r, (N.rectangles.rightFrame C r).source.FrozenAtomBounds)

/-- This record is what is actually passed to the existing normalized
hybrid producer. It retains the same four ordinary rectangles. -/
def withArithmeticCosts :
    leaf.NormalizationData (ι := ι) C Ray ω ψ Z rowDomain heightDomain window seminorms :=
  { N with
    left := fun r => (N.left r).withArithmeticCosts W (BL r)
    right := fun r => (N.right r).withArithmeticCosts W (BR r)
    left_height := N.left_height
    right_height := N.right_height }

theorem withArithmeticCosts_sourcePair (parentWidth : ℝ) (rs : Bool × Bool)
    (ξ : WithLp 2 (U × E)) :
    (N.withArithmeticCosts W BL BR).family.sourcePair parentWidth rs ξ =
      N.family.sourcePair parentWidth rs ξ := rfl

theorem withArithmeticCosts_active (labels : Finset (Bool × Bool)) :
    (N.withArithmeticCosts W BL BR).family.active labels = N.family.active labels := rfl

end ActualHybridLeaf.NormalizationData

section SamePairKernel

variable {H ι U E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (WithLp 2 (U × E))] [BorelSpace (WithLp 2 (U × E))]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {k l kLeft kRight : ℕ}
variable (left : SecondSideFrame (V := WithLp 2 (U × E)) C R Ray .left k)
variable (right : SecondSideFrame (V := WithLp 2 (U × E)) C R Ray .right l)
variable (calL : left.source.Calibration (σ := σ) ω ψ)
variable (calR : right.source.Calibration (σ := σ) ω ψ)
variable (W : ActualSecondRowMass R C kLeft kRight)
variable (BL : left.source.FrozenAtomBounds) (BR : right.source.FrozenAtomBounds)
variable (IL : (left.arithmeticCalibration calL W BL).CapacityInput)
variable (IR : (right.arithmeticCalibration calR W BR).CapacityInput)
variable (AL AR : WithLp 2 (U × E) → ℝ)
variable (hAL : ∀ ξ, 0 < AL ξ) (hAR : ∀ ξ, 0 < AR ξ)
variable (boundsL : Fin left.source.allocation.keep.card → ℝ)
variable (boundsR : Fin right.source.allocation.keep.card → ℝ)
variable (hBL : ∀ i, 0 ≤ boundsL i) (hBR : ∀ i, 0 ≤ boundsR i)
variable (hfL : ∀ ξ i, IL.primeBound ξ i = AL ξ ^ 2 * boundsL i)
variable (hfR : ∀ ξ i, IR.primeBound ξ i = AR ξ ^ 2 * boundsR i)
variable (lc : (IL.normalized AL hAL boundsL hBL hfL).Child)
variable (rc : (IR.normalized AR hAR boundsR hBR hfR).Child)

local notation "rawL" => IL.rawChild AL hAL boundsL hBL hfL lc
local notation "rawR" => IR.rawChild AR hAR boundsR hBR hfR rc

/-- The first allowance is the literal original positive scale. This
is the `ActualChildAllowance` theorem for the same children selected by
the normalized family, including both original complex normalizers. -/
theorem normalized_family_weight_relative_allowance_le
    (Z : ℝ) (hZ : 1 < Z) (a₀ q wo w krow g ell parentWidth boundary N : ℝ)
    (hN : N = Z ^ (a₀ + q + w + boundary))
    (hdiv : left.source.allocation.divisor = right.source.allocation.divisor)
    (LL : ActualCapacityNormLengths IL Z a₀ q wo w krow g ell
      W.leftIdeal W.rightIdeal W.unitIdeal.val W.nonunitIdeal.val)
    (LR : ActualCapacityNormLengths IR Z a₀ q wo w krow g ell
      W.leftIdeal W.rightIdeal W.unitIdeal.val W.nonunitIdeal.val)
    (NL : left.OriginalScaleWindow Z a₀) (NR : right.OriginalScaleWindow Z a₀)
    (hrow : Z ^ (-krow - g) ≤
      W.radius.val * (sIntegerElementNorm F (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
        (sIntegerMaskGenerator F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) W.mask)).val) :
    normalizedCapacityPairWeight lc rc left.normalizer right.normalizer Z parentWidth / N ≤
      (actualCapacityPairEnvelope left right calL calR W BL BR rawL rawR boundsL boundsR *
        W.commonEnvelope * orbitalFieldFactor F *
        Z ^ ((LL.slack + LR.slack) / 2 - boundary) * Z ^ wo * Z ^ ell / Z ^ parentWidth) *
        (1 / (Ideal.absNorm (commonRadical W.leftIdeal W.rightIdeal) : ℝ)) /
          (Ideal.absNorm left.source.allocation.divisor : ℝ) := by
  rw [normalized_pair_weight_eq_canonical left right calL calR W BL BR IL IR
    AL AR hAL hAR boundsL boundsR hBL hBR hfL hfR lc rc Z parentWidth (zero_lt_one.trans hZ)]
  exact actual_capacity_pair_relative_allowance_le left right calL calR W BL BR
    rawL rawR boundsL boundsR Z hZ a₀ q wo w krow g ell parentWidth boundary N hN
      hBL hBR hdiv LL LR NL NR hrow

/-- Exact equality for the mass used by ActualFiniteKernelMass.  The
children, original Gauss factors and original Fourier measures coincide. -/
theorem normalized_family_kernel_mass_eq_canonical
    (outer Z parentWidth : ℝ) (houter : 0 ≤ outer) (hZ : 0 < Z)
    (F₁ : 𝓢(U, ℂ)) (F₂ : 𝓢(E, ℂ)) (B₁ B₂ : ℝ)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (J₁ J₂ : ℕ)
    (hradiusL : ∀ z, AL (WithLp.toLp 2 z) = polynomialProfileRadius B₁ J₁ J₂ z)
    (hradiusR : ∀ z, AR (WithLp.toLp 2 z) = polynomialProfileRadius B₂ J₁ J₂ z) :
    (ENNReal.ofReal outer • normalizedCapacityPairKernel
      (Measure.map (WithLp.toLp 2) (nestedFourierMeasure F₁ F₂))
      lc rc left.normalizer right.normalizer Z parentWidth).real Set.univ =
      (CanonicalCapacityKernelMass.kernel left right calL calR W BL BR rawL rawR boundsL boundsR
        outer Z parentWidth F₁ F₂ B₁ B₂ J₁ J₂).real Set.univ := by
  rw [measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal houter,
    normalizedCapacityPairKernel_nested_mass_eq B₁ B₂ J₁ J₂ J₁ J₂ hradiusL hradiusR
      F₁ F₂ hB₁ hB₂ lc rc left.normalizer right.normalizer Z parentWidth hZ,
    normalized_pair_weight_eq_canonical left right calL calR W BL BR IL IR
      AL AR hAL hAR boundsL boundsR hBL hBR hfL hfR lc rc Z parentWidth hZ,
    CanonicalCapacityKernelMass.kernel_mass left right calL calR W BL BR rawL rawR boundsL boundsR
      outer Z parentWidth houter hZ]
  change outer * (_ * (normalizedPairMeasure F₁ F₂
    left.source.allocation.keep.card right.source.allocation.keep.card B₁ B₂ J₁ J₂).real Set.univ) = _
  ring

/-- The actual normalized-family kernel is bounded with no numerical
cost assumptions on the original calibrations. They have been replaced
by the canonical arithmetic calibration in its type. -/
theorem normalized_family_kernel_mass_le
    (cap J₁ J₂ : ℕ) (B : ℝ) (hB : 1 ≤ B)
    (P : CanonicalCapacityKernelMass.OriginalAtomWindow left right W BL BR boundsL boundsR cap B)
    (outer Z parentWidth remaining a₀ q wo w krow g ell : ℝ)
    (houter : 0 ≤ outer) (hZ : 1 < Z)
    (hdiv : left.source.allocation.divisor = right.source.allocation.divisor)
    (LL : ActualCapacityNormLengths IL Z a₀ q wo w krow g ell
      W.leftIdeal W.rightIdeal W.unitIdeal.val W.nonunitIdeal.val)
    (LR : ActualCapacityNormLengths IR Z a₀ q wo w krow g ell
      W.leftIdeal W.rightIdeal W.unitIdeal.val W.nonunitIdeal.val)
    (NL : left.OriginalScaleWindow Z a₀) (NR : right.OriginalScaleWindow Z a₀)
    (hrow : Z ^ (-krow - g) ≤
      W.radius.val * (sIntegerElementNorm F (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
        (sIntegerMaskGenerator F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) W.mask)).val)
    (hremaining : a₀ + q + w + (LL.slack + LR.slack) / 2 + wo + ell - parentWidth ≤ remaining)
    (F₁ : 𝓢(U, ℂ)) (F₂ : 𝓢(E, ℂ)) (B₁ B₂ : ℝ)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hB₁B : B₁ ≤ B) (hB₂B : B₂ ≤ B)
    (hradiusL : ∀ z, AL (WithLp.toLp 2 z) = polynomialProfileRadius B₁ J₁ J₂ z)
    (hradiusR : ∀ z, AR (WithLp.toLp 2 z) = polynomialProfileRadius B₂ J₁ J₂ z)
    (kernelBound₁ kernelBound₂ : ℝ)
    (hkernel₁ : (CanonicalCapacityKernelMass.fourierData (U := U) (E := E) cap J₁ J₂).leftSeminorms.sup
      (schwartzSeminormFamily ℝ U ℂ) F₁ ≤ kernelBound₁)
    (hkernel₂ : (CanonicalCapacityKernelMass.fourierData (U := U) (E := E) cap J₁ J₂).rightSeminorms.sup
      (schwartzSeminormFamily ℝ E ℂ) F₂ ≤ kernelBound₂) :
    IsFiniteMeasure (ENNReal.ofReal outer • normalizedCapacityPairKernel
      (Measure.map (WithLp.toLp 2) (nestedFourierMeasure F₁ F₂))
      lc rc left.normalizer right.normalizer Z parentWidth) ∧
    (ENNReal.ofReal outer • normalizedCapacityPairKernel
      (Measure.map (WithLp.toLp 2) (nestedFourierMeasure F₁ F₂))
      lc rc left.normalizer right.normalizer Z parentWidth).real Set.univ ≤
      outer * ((W.originalFiber : ℝ) * B ^ (3 * cap + 1) * orbitalFieldFactor F) * Z ^ remaining /
        ((Ideal.absNorm left.source.allocation.divisor : ℝ) *
          (Ideal.absNorm (commonRadical W.leftIdeal W.rightIdeal) : ℝ)) *
        ((1 + B) ^ (cap + 2) * (1 + B) ^ (cap + 2)) *
        (CanonicalCapacityKernelMass.fourierData (U := U) (E := E) cap J₁ J₂).constant *
          kernelBound₁ * kernelBound₂ := by
  have hmass := CanonicalCapacityKernelMass.kernel_mass_le left right calL calR W BL BR
    rawL rawR boundsL boundsR cap J₁ J₂ B hB P outer Z parentWidth remaining a₀ q wo w krow g ell
    houter hZ hBL hBR hdiv LL LR NL NR hrow hremaining F₁ F₂ B₁ B₂
    hB₁ hB₂ hB₁B hB₂B kernelBound₁ kernelBound₂ hkernel₁ hkernel₂
  haveI := normalizedCapacityPairKernel_nested_finite B₁ B₂ J₁ J₂ J₁ J₂
    hradiusL hradiusR F₁ F₂ hB₁ hB₂ lc rc left.normalizer right.normalizer Z parentWidth
  refine ⟨inferInstance, ?_⟩
  rw [normalized_family_kernel_mass_eq_canonical left right calL calR W BL BR IL IR
    AL AR hAL hAR boundsL boundsR hBL hBR hfL hfR lc rc
    outer Z parentWidth houter (zero_lt_one.trans hZ) F₁ F₂ B₁ B₂ hB₁ hB₂ J₁ J₂ hradiusL hradiusR]
  exact hmass.2

end SamePairKernel

namespace ActualNormalizedPairFamily

variable {V J Λ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [Fintype J] [Fintype Λ] {Z : ℝ}

/-- Exact regrouping of the retained carrier: the original outer leaf
and its original rectangle label both remain. No inactive label is
reintroduced and no frequency-dependent choice is made. -/
def activeCombineEquiv (families : J → ActualNormalizedPairFamily A σ V Λ ω ψ Z) :
    (combine families).active Finset.univ ≃ Σ j : J, (families j).active Finset.univ where
  toFun b := ⟨b.val.1, ⟨b.val.2, by
    simpa only [active, combine, Finset.mem_filter, Finset.mem_univ, true_and] using b.property⟩⟩
  invFun b := ⟨(b.1, b.2.val), by
    simpa only [active, combine, Finset.mem_filter, Finset.mem_univ, true_and] using b.2.property⟩
  left_inv b := by apply Subtype.ext; rfl
  right_inv b := by cases b; rfl

variable [MeasurableSpace V]

/-- The mass of the combined normalized hybrid family is the sum of
the masses of those exact same selected children on the original
finite leaves. This uses their canonical projections, not new choices. -/
theorem combined_kernel_total_mass
    (families : J → ActualNormalizedPairFamily A σ V Λ ω ψ Z)
    (μ : J × Λ → Measure V) (parentWidth : ℝ) :
    (∑ b : (combine families).active Finset.univ,
      ((combine families).kernel Finset.univ μ parentWidth b).real Set.univ) =
      ∑ j : J, ∑ b : (families j).active Finset.univ,
        ((families j).kernel Finset.univ (fun r => μ (j, r)) parentWidth b).real Set.univ := by
  rw [← Fintype.sum_sigma]
  exact Fintype.sum_equiv (activeCombineEquiv families) _ _ (fun b => rfl)

end ActualNormalizedPairFamily
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideNormalization.withArithmeticCosts
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.NormalizationData.withArithmeticCosts_sourcePair
#print axioms HeckeSkeleton.Moments.EngineStep.normalized_family_weight_relative_allowance_le
#print axioms HeckeSkeleton.Moments.EngineStep.normalized_family_kernel_mass_eq_canonical
#print axioms HeckeSkeleton.Moments.EngineStep.normalized_family_kernel_mass_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.combined_kernel_total_mass
