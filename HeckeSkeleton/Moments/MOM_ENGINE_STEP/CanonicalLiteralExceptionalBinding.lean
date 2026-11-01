import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalOuterScalar
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalFactory
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralStrippedCovered

/-!
# Bind the actual exceptional columns, including original row translations

The stored Fourier locations differ from the residual log-norm locations
by a constant on each row. Their phases have norm one, so this difference
is removed only after forming each complete centered column. The original
ordinary atom binding already supplies those individual locations and
coefficients on all rows. No ordinary estimate is used here.

The first scalar pair is moved outside only after the second common
atoms have entered the row. The final dictionary therefore uses the same
common row mass as the literal exceptional source factory.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralRectangles.Atoms

variable {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)

/-- Both original rectangles have exactly the same extra Gauss
normalizer. Their full difference is retained before taking a norm. -/
theorem exceptional_comparison_coefficient (phase : PUnit.{1} →* Circle)
    (i : AllocationColumn K k) :
    (CanonicalLiteralExceptionalFactory.comparison d phase).centeredCoefficient
      (Real.sqrt d.gauss₁ : ℂ)⁻¹ (Real.sqrt d.gauss₂ : ℂ)⁻¹
      (fun j => (Real.sqrt (d.gaussSlot j) : ℂ)⁻¹) i = d.whole i := by
  unfold SecondCoefficientComparison.centeredCoefficient
  rw [CanonicalLiteralExceptionalFactory.comparison_dictionary,
    SecondCoefficientTermDictionary.normalizedCoefficient_eq,
    SecondCoefficientTermDictionary.normalizedCoefficient_eq]
  rfl

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exceptional_frame_coefficient
    (R : ActualSecondCorrelationRows A σ H ι) (side : SecondColumnSide)
    (χ : (PUnit.{1} × PUnit.{1}) →* Circle)
    (ideal : AllocationColumn K k → A.Exterior)
    (hideal : ∀ i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots,
      (ideal i).val = allocationColumnIdeal i)
    (firstSign : ℝ) (L : Ideal (𝓞 K))
    (selection : primeSupport L → Finset (Fin (k + 2)))
    (hne : (pairedAllocatedColumns L selection d.plain₁ d.plain₂ d.slots
      id id HeightOneSpectrum.asIdeal).Nonempty)
    (h : H) (i : AllocationColumn K k) :
    ((d.factors R side χ ideal hideal firstSign false).frame C L selection hne).centeredCoefficient
          (CanonicalLiteralExceptionalFactory.comparison d (side.phase PUnit.{1} χ)) h i =
      side.actualCoefficient (σ := σ) PUnit.{1} ideal R.frequency (fun _ => PUnit.unit) χ
        d.whole h i := by
  have hray (phase : PUnit.{1} →* Circle) :
      (d.dictionary phase false).ray i = PUnit.unit := Subsingleton.elim _ _
  cases side <;>
    simp only [SecondSideFrame.centeredCoefficient, SecondRectangularFactors.frame,
      factors, SecondColumnSide.actualCoefficient, secondAllocatedLeftCoefficient,
      secondAllocatedRightCoefficient, d.exceptional_comparison_coefficient, hray]

end CanonicalLiteralRectangles.Atoms

namespace ActualHybridLeaf.OrdinaryBinding

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {H ι U V : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup U] [InnerProductSpace ℝ U]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {leaf : ActualHybridLeaf K H U V}
variable {S₁ S₂ : Finset (Ideal (𝓞 K))}
variable {S : Fin leaf.leftSlots → Finset (HeightOneSpectrum (𝓞 K))}
variable {T₁ T₂ : Finset (Ideal (𝓞 K))}
variable {T : Fin leaf.rightSlots → Finset (HeightOneSpectrum (𝓞 K))}
variable {IA : AllocationColumn K leaf.leftSlots → A.Exterior}
variable {IB : AllocationColumn K leaf.rightSlots → A.Exterior}
variable {rayLeft : AllocationColumn K leaf.leftSlots → Ray}
variable {rayRight : AllocationColumn K leaf.rightSlots → Ray}
variable {wholeLeft : AllocationColumn K leaf.leftSlots → ℂ}
variable {wholeRight : AllocationColumn K leaf.rightSlots → ℂ}
variable {x : H → AllocationColumn K leaf.leftSlots → WithLp 2 (U × V)}
variable {y : H → AllocationColumn K leaf.rightSlots → WithLp 2 (U × V)}
variable {b : liveSecondAllocationBranches (Ray := Ray) S₁ S₂ S T₁ T₂ T IB}
variable {exceptional : H → Prop}
variable {B : HybridOrdinaryRectangles R Ray S₁ S₂ S T₁ T₂ T IA IB
  rayLeft rayRight wholeLeft wholeRight x y b exceptional}
variable (binding : leaf.OrdinaryBinding B)

/-- The atom dictionary is valid on every original row, including the
exceptional classes. Row translations vanish in the two column norms,
without splitting either whole centered coefficient. -/
theorem pairMagnitude_eq (keep : H → Prop) (z : U × V) :
    jointColumnPairMagnitude (leaf.rows.filter keep) leaf.left leaf.right
      leaf.rowWeight leaf.leftCoefficient (fun h j => star (leaf.rightCoefficient h j))
      (fun h i => WithLp.toLp 2 (leaf.leftFirst h i, leaf.leftSecond h i))
      (fun h j => WithLp.toLp 2 (-leaf.rightFirst h j, leaf.rightSecond h j))
      (WithLp.toLp 2 z) =
    jointColumnPairMagnitude (R.rows.filter keep) (b.val.leftColumns S₁ S₂ S)
      b.val.rightColumns (fun h => R.weight h * R.correlation h)
      (secondAllocatedLeftCoefficient (σ := σ) Ray IA R.frequency rayLeft b.val.2.1 wholeLeft)
      (secondAllocatedRightCoefficient (σ := σ) Ray IB R.frequency rayRight b.val.2.1 wholeRight)
      x y (WithLp.toLp 2 z) := by
  calc
    _ = jointColumnPairMagnitude (R.rows.filter keep) leaf.left leaf.right
        leaf.rowWeight leaf.leftCoefficient (fun h j => star (leaf.rightCoefficient h j))
        (fun h i => WithLp.toLp 2 (leaf.leftFirst h i, leaf.leftSecond h i))
        (fun h j => WithLp.toLp 2 (-leaf.rightFirst h j, leaf.rightSecond h j))
        (WithLp.toLp 2 z) :=
      jointColumnPairMagnitude_filter_eq_on_zero_rows _ _ _ _ _ _ _ _ _ _ _
        binding.rows binding.rows_zero
    _ = _ := by
      rw [← binding.left, ← binding.right]
      unfold jointColumnPairMagnitude
      apply Finset.sum_congr rfl
      intro h hh
      have hm : h ∈ leaf.rows := binding.rows (Finset.mem_filter.mp hh).1
      obtain ⟨zl, hzl⟩ := binding.leftPoint h hm
      obtain ⟨zr, hzr⟩ := binding.rightPoint h hm
      have hl : jointFourierColumn leaf.left (leaf.leftCoefficient h)
          (fun i => WithLp.toLp 2 (leaf.leftFirst h i, leaf.leftSecond h i))
          (WithLp.toLp 2 z) =
          jointPhase (WithLp.toLp 2 z) zl * jointFourierColumn leaf.left
            (secondAllocatedLeftCoefficient (σ := σ) Ray IA R.frequency rayLeft
              b.val.2.1 wholeLeft h) (x h) (WithLp.toLp 2 z) := by
        rw [← jointFourierColumn_rowTranslation]
        unfold jointFourierColumn
        apply Finset.sum_congr rfl
        intro i hi
        rw [binding.leftCoefficient h hm i hi, hzl i hi]
      have hr : jointFourierColumn leaf.right (fun i => star (leaf.rightCoefficient h i))
          (fun i => WithLp.toLp 2 (-leaf.rightFirst h i, leaf.rightSecond h i))
          (WithLp.toLp 2 z) =
          jointPhase (WithLp.toLp 2 z) zr * jointFourierColumn leaf.right
            (secondAllocatedRightCoefficient (σ := σ) Ray IB R.frequency rayRight
              b.val.2.1 wholeRight h) (y h) (WithLp.toLp 2 z) := by
        rw [← jointFourierColumn_rowTranslation]
        unfold jointFourierColumn
        apply Finset.sum_congr rfl
        intro i hi
        rw [binding.rightCoefficient h hm i hi, hzr i hi]
      simp only [binding.rowWeight h hm, hl, hr, norm_mul, norm_jointPhase, one_mul]

variable [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U]
variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem thetaClass_integrand
    {theta : Finset (HeckeCharacter K)} (Q : PairedFiniteCharacters theta H)
    (hpredicate : leaf.exceptional = Q.exceptional) (χ : theta × theta) (z : U × V) :
    (leaf.thetaClassLeaf Q χ).exceptionalIntegrand z =
      jointColumnPairMagnitude (R.rows.filter (Q.thetaClass χ))
        (b.val.leftColumns S₁ S₂ S) b.val.rightColumns
        (fun h => R.weight h * R.correlation h)
        (secondAllocatedLeftCoefficient (σ := σ) Ray IA R.frequency rayLeft
          b.val.2.1 wholeLeft)
        (secondAllocatedRightCoefficient (σ := σ) Ray IB R.frequency rayRight
          b.val.2.1 wholeRight) x y (WithLp.toLp 2 z) := by
  rw [leaf.thetaClassLeaf_integrand Q hpredicate]
  exact binding.pairMagnitude_eq (Q.thetaClass χ) z

end ActualHybridLeaf.OrdinaryBinding


section OriginalCoveredLeaf

open MeasureTheory LocalFiniteSums
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.IdealMobiusDivisorSum

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex] [IsPrincipalIdealRing A.R]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable {ν : Measure (FiniteAdeleRing (𝓞 K) K)} [ν.IsAddHaarMeasure]
variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  MeasurableSpace (v.val.adicCompletion K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  BorelSpace (v.val.adicCompletion K)ˣ]


local instance canonicalLiteralExceptionalBindingCircleCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

namespace ActualGaussStage.CoveredClassKey

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {s : ActualGaussStage (E := ℝ) hΓ μv hDiff G finiteTest}
variable {LC RC : SourceCartesianCover G.columns G.ideal}
variable (v : s.CoveredClassKey LC RC)
variable (leftAtoms : CanonicalLiteralRectangles.Atoms (K := K)
  (LC.branch v.2.2.1).slotCount)
variable (rightAtoms : CanonicalLiteralRectangles.Atoms (K := K)
  (RC.branch v.2.2.2.1).slotCount)
variable (exceptional : s.CoverHybridPredicates LC RC)
variable (firstKernel : SchwartzMap ℝ ℂ) (x : ι → ℝ) (j : v.AllocationKey)
variable (leftCoefficient : ∀ i ∈ (LC.branch v.2.2.1).reindex.cartesian,
  (LC.branch v.2.2.1).reindex.index i ∈ v.block.leftColumns G.columns →
    v.chart.sourceLeftCoefficient ((LC.branch v.2.2.1).reindex.index i) = leftAtoms.whole i)
variable (rightCoefficient : ∀ i ∈ (RC.branch v.2.2.2.1).reindex.cartesian,
  (RC.branch v.2.2.2.1).reindex.index i ∈ v.block.rightColumns G.columns →
    v.chart.sourceRightCoefficient ((RC.branch v.2.2.2.1).reindex.index i) = rightAtoms.whole i)

variable (leftScalar rightScalar : ℂ) (hleftScalar : leftScalar ≠ 0)
variable (hrightScalar : rightScalar ≠ 0)
variable (firstSign : ℝ) (hlive : (v.leaf exceptional firstKernel x j).Live)
variable (leftBalance rightBalance : Bool → ℝ)
variable (hleftBalance : ∀ r, 0 < leftBalance r)
variable (hrightBalance : ∀ r, 0 < rightBalance r)

variable (leftPoint : ∀ h ∈ (v.leaf exceptional firstKernel x j).rows,
  ∃ z : WithLp 2 (ℝ × ℝ), ∀ i ∈ (v.leaf exceptional firstKernel x j).left,
    WithLp.toLp 2 ((v.leaf exceptional firstKernel x j).leftFirst h i,
      (v.leaf exceptional firstKernel x j).leftSecond h i) =
        z + rawSourceLocation (CanonicalLiteralLocations.plain firstSign)
          (CanonicalLiteralLocations.plain firstSign)
          (CanonicalLiteralLocations.prime firstSign) i)
variable (rightPoint : ∀ h ∈ (v.leaf exceptional firstKernel x j).rows,
  ∃ z : WithLp 2 (ℝ × ℝ), ∀ i ∈ (v.leaf exceptional firstKernel x j).right,
    WithLp.toLp 2 (-(v.leaf exceptional firstKernel x j).rightFirst h i,
      (v.leaf exceptional firstKernel x j).rightSecond h i) =
        z + rawSourceLocation (CanonicalLiteralLocations.plain (-firstSign))
          (CanonicalLiteralLocations.plain (-firstSign))
          (CanonicalLiteralLocations.prime (-firstSign)) i)


/-- The actual residual tables on the original common row mass. The
first scalar pair has already been moved outside and is not reinserted
in these rows. Reciprocal balancing preserves the whole columns. -/
def literalStripOuterRectangles :=
  CanonicalLiteralRectangles.balancedRectangles
    (v.literalSupportedRows leftAtoms rightAtoms)
    ((v.literalLeftAtoms leftAtoms).scale leftScalar⁻¹)
    ((v.literalRightAtoms rightAtoms).scale rightScalar⁻¹)
    leftBalance rightBalance hleftBalance hrightBalance
    (fun i => v.block.leftResidual (v.leftReindex.index i))
    (fun i => v.block.rightResidual (v.rightReindex.index i))
    v.leftReindex.ideal_product v.rightReindex.ideal_product
    (v.literalAllocation exceptional firstKernel x j hlive)
    (v.leaf exceptional firstKernel x j).exceptional firstSign (-firstSign)

/-- All fields come from the already constructed original two atom
bindings. This proves the outer-scalar normalization at the actual
stored leaf; no magnitude or terminal bound is assumed. -/
def literalStripOuterBinding :
    ((v.literalExtraction leftAtoms rightAtoms exceptional firstKernel x j
      leftCoefficient rightCoefficient).stripOuter
        leftScalar rightScalar hleftScalar hrightScalar).OrdinaryBinding
      (v.literalStripOuterRectangles leftAtoms rightAtoms exceptional firstKernel x j
        leftScalar rightScalar firstSign hlive leftBalance rightBalance
          hleftBalance hrightBalance) := by
  let base := v.literalOrdinaryBinding leftAtoms rightAtoms exceptional firstKernel x j
    leftCoefficient rightCoefficient firstSign hlive leftPoint rightPoint
  let stripped := v.literalStrippedOrdinaryBinding leftAtoms rightAtoms exceptional firstKernel x j
    leftCoefficient rightCoefficient leftScalar rightScalar hleftScalar hrightScalar
    firstSign hlive leftBalance rightBalance hleftBalance hrightBalance leftPoint rightPoint
  exact
    { rows := base.rows
      rows_zero := base.rows_zero
      left := base.left
      right := base.right
      exceptional := base.exceptional
      rowWeight := base.rowWeight
      leftCoefficient := stripped.leftCoefficient
      rightCoefficient := stripped.rightCoefficient
      leftPoint := base.leftPoint
      rightPoint := base.rightPoint }

end ActualGaussStage.CoveredClassKey
end OriginalCoveredLeaf

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.exceptional_comparison_coefficient
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.exceptional_frame_coefficient
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.OrdinaryBinding.pairMagnitude_eq
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.OrdinaryBinding.thetaClass_integrand

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalStripOuterBinding
