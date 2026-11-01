import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralChartCoefficients
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPoolAtlas
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstSecondSource

/-!
# The original chart and pool coefficients are the computed atom table

The first canonical logarithmic chart, the actual one-pool residual
coefficient and the second logarithmic chart retain their original
inverse norm and their three fixed residue phases.  The lemmas here
compute these fields before taking any polynomial norm.  In particular
the pool's original norm cancels its first inverse norm; the remaining
denominator is the actual post-pool residual norm.

The original Cartesian index is read from the parent atom tuple.  Its
coefficient identity is proved from the original two rectangles, rather
than supplied as a whole-column or whole-polynomial hypothesis.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support HeckePort.Moments.MobiusRegroup
open MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {htrace : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η htrace}

namespace FirstGaussPoolData

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {pool : PowerScaleExteriorPool A bad Z ell eps}
variable {ι : Type*} (d : FirstGaussPoolData C pool ι)

/-- The actual residual coefficient, for the literal coefficient of
the first logarithmic chart.  The cancellation uses the nonzero norm
of the same original column; there is no renormalized source input. -/
theorem residualCoefficient_logarithmic
    (p : ExteriorPrime A) (n : ℕ) (c : ι → ℂ) (δ : ℝ) (first : A.R)
    (i : d.valuationColumns p n) :
    d.residualCoefficient p n
        (fun j => (c j * ((A.exteriorNorm (d.ideal j) ^ δ : ℝ) : ℂ) *
          actualIdealResidue (A := A) (σ := σ) (d.ideal j).val first) /
            (A.exteriorNorm (d.ideal j) : ℂ)) i =
      (c i.val * ((A.exteriorNorm (d.ideal i.val) ^ δ : ℝ) : ℂ) /
          (A.exteriorNorm (d.residualPresentation p n i).residual : ℂ)) *
        actualIdealResidue (A := A) (σ := σ) (d.ideal i.val).val first *
        actualIdealResidue (A := A) (σ := σ)
          (d.residualPresentation p n i).residual.val (generator C p ^ (2 * n)) := by
  have hN : (A.exteriorNorm (d.ideal i.val) : ℂ) ≠ 0 := by
    exact_mod_cast (A.exteriorNorm_pos (d.ideal i.val)).ne'
  unfold residualCoefficient adjustedCoefficient
  rw [AmplifierResidualPresentation.columnPhase_eq_residue]
  field_simp [hN] <;> ring

end FirstGaussPoolData

namespace CompleteMovingRowRecipe

variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {X : Type*}
variable {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data)

/-- The literal atom table equals the original coefficient at every
original tuple, not just on a later chosen nonzero Fourier source. -/
theorem literalOriginalAtoms_whole_originalCoordinates (ξ : X)
    (W : NormProfileRecipe (fun _ : PUnit => data ξ))
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
    (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (v : (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).Column) :
    let atoms := (Q.arithmeticAtoms ξ).constantAtoms W a Z t
    (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).whole
        ((atoms.raw Y₁ Y₂).originalCoordinates v) =
      (atoms.values Y₁ Y₂).coefficient centered v := by
  dsimp only
  rw [Q.literalOriginalAtoms_whole,
    ParentRawAtoms.originalIndex_coordinates]

/-- The original coefficient on the reconstructed tuple gives the
literal two-stage atom table.  The index is the actual original
nonzero-ideal coercion, including all retained prime occurrences. -/
theorem literalOriginalAtoms_secondInput_whole (ξ : X)
    (W : NormProfileRecipe (fun _ : PUnit => data ξ))
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
    (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (support : Finset (Ideal (𝓞 K)))
    (b : SupportCartesianBranch
      (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).plain₁
      (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).plain₂
      (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).slots support)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (power firstFixed poolFixed unitFixed : A.Exterior)
    (firstElement poolElement unitElement : A.R)
    (hfirst : A.Generates firstFixed firstElement)
    (hpool : A.Generates poolFixed poolElement)
    (hunit : A.Generates unitFixed unitElement)
    (δ₁ δ₂ : ℝ) (i : AllocationColumn K b.keep.card)
    (hi : i ∈ b.residualColumns) (J : A.Exterior)
    (hJ : J.val = allocationColumnIdeal i) :
    let atoms := (Q.arithmeticAtoms ξ).constantAtoms W a Z t
    ((Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).secondInput
      (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).whole i =
      ((atoms.values Y₁ Y₂).coefficient centered
          ((atoms.raw Y₁ Y₂).originalIndex (b.reconstruct i)) *
        ((A.exteriorNorm (ExteriorIdealEuler.mul power J) ^ δ₁ : ℝ) : ℂ) /
          (A.exteriorNorm J : ℂ)) *
        actualIdealResidue (A := A) (σ := σ)
          (ExteriorIdealEuler.mul power J).val firstElement *
        actualIdealResidue (A := A) (σ := σ) J.val poolElement *
        ((A.exteriorNorm J ^ δ₂ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ) J.val unitElement := by
  dsimp only
  rw [CanonicalLiteralRectangles.Atoms.secondInput_whole _ b P R hroot hemb
    power firstFixed poolFixed unitFixed firstElement poolElement unitElement
    hfirst hpool hunit δ₁ δ₂ i hi J hJ,
    Q.literalOriginalAtoms_whole ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂]

end CompleteMovingRowRecipe

section FirstChart

variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  MeasurableSpace (v.val.adicCompletion K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  BorelSpace (v.val.adicCompletion K)ˣ]
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable (b : FirstCommonCharacterBlock fullI fullJ DE)
variable (C : A.GeneralArithmeticContext σ η htrace)
variable (left : Finset ι) (right : Finset κ)
variable (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
variable (c : ι → ℂ) (e : κ → ℂ)
variable (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
variable (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
variable (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
variable (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
variable (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {pool : PowerScaleExteriorPool A bad Z ell eps}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}

namespace FirstBlockPoolData

variable (p : FirstBlockPoolData
  (FirstBlockProfileChart.canonicalLogWithCoefficients hΓ μv ν b C left right φ c e
    finiteTest hlc hcs radius D δ hδ hδhalf) pool M X hX)
variable (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
variable (χ : (PUnit × PUnit) →* Circle)

/-- Both the first fixed finite phase and the internal divisor test
are read from the actual first coefficient.  The finite phase is one
because its ray element is the identity, independently of χ. -/
theorem canonicalLog_leftDivisorCoefficient
    (i : ι) (hi : i ∈ p.leftData.columns)
    (hSi : S.val ∣ (p.leftData.ideal i).val) :
    p.leftDivisorCoefficient S χ i =
      (c i * ((A.exteriorNorm (b.leftResidual i) ^ δ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ) (b.leftResidual i).val
          (CanonicalLiteralFirstPhase.leftElement C b.primes
            b.leftMultiplicity b.rightMultiplicity
            (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)) /
        (A.exteriorNorm (b.leftResidual i) : ℂ) := by
  have ha : A.IsAllowed C.correction.B
      (Units.mk0 (b.leftGenerator i : K)
        (by exact_mod_cast (b.left_generates i).1)) := by
    have hgen := p.leftData.allowed i hi
    simpa only [p.left_generator] using hgen
  unfold leftDivisorCoefficient
  rw [if_pos hSi]
  have hχ : (fixedLeftPhase PUnit χ PUnit.unit : ℂ) = 1 := by
    change ((fixedLeftPhase PUnit χ) (1 : PUnit) : ℂ) = 1
    rw [map_one, Circle.coe_one]
  rw [hχ, mul_one]
  exact FirstBlockProfileChart.canonicalLog_leftSourceCoefficient hΓ μv ν b C
    left right φ c e finiteTest hlc hcs radius δ hδ hδhalf D i ha

theorem canonicalLog_rightDivisorCoefficient
    (j : κ) (hj : j ∈ p.rightData.columns)
    (hSj : S.val ∣ (p.rightData.ideal j).val) :
    p.rightDivisorCoefficient S χ j =
      (e j * ((A.exteriorNorm (b.rightResidual j) ^ δ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ) (b.rightResidual j).val
          (CanonicalLiteralFirstPhase.rightElement C b.primes
            b.leftMultiplicity b.rightMultiplicity
            (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)) /
        (A.exteriorNorm (b.rightResidual j) : ℂ) := by
  have ha : A.IsAllowed C.correction.B
      (Units.mk0 (b.rightGenerator j : K)
        (by exact_mod_cast (b.right_generates j).1)) := by
    have hgen := p.rightData.allowed j hj
    simpa only [p.right_generator] using hgen
  unfold rightDivisorCoefficient
  rw [if_pos hSj]
  have hχ : (fixedRightPhase PUnit χ PUnit.unit : ℂ) = 1 := by
    change ((fixedRightPhase PUnit χ) (1 : PUnit) : ℂ) = 1
    rw [map_one, Circle.coe_one]
  rw [hχ, mul_one]
  exact FirstBlockProfileChart.canonicalLog_rightSourceCoefficient hΓ μv ν b C
    left right φ c e finiteTest hlc hcs radius δ hδ hδhalf D j ha

/-- The actual left valuation source, with the first divisor and phase
unchanged. The residual phase is computed by original reciprocity. -/
theorem canonicalLog_leftResidualCoefficient
    (q : ExteriorPrime A) (n : ℕ)
    (i : (p.divisorPools.leftData S).valuationColumns q n)
    (hSi : S.val ∣ (p.leftData.ideal i.val).val) :
    (p.divisorPools.leftData S).residualCoefficient q n
        (p.leftDivisorCoefficient S χ) i =
      (c i.val * ((A.exteriorNorm (b.leftResidual i.val) ^ δ : ℝ) : ℂ) /
          (A.exteriorNorm
            ((p.divisorPools.leftData S).residualPresentation q n i).residual : ℂ)) *
        actualIdealResidue (A := A) (σ := σ) (b.leftResidual i.val).val
          (CanonicalLiteralFirstPhase.leftElement C b.primes
            b.leftMultiplicity b.rightMultiplicity
            (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) *
        actualIdealResidue (A := A) (σ := σ)
          ((p.divisorPools.leftData S).residualPresentation q n i).residual.val
          (generator C q ^ (2 * n)) := by
  have hi : i.val ∈ p.leftData.columns := by
    simpa only [p.divisorPools.left_columns S] using
      (Finset.mem_filter.mp i.property).1
  have hN : (A.exteriorNorm (b.leftResidual i.val) : ℂ) ≠ 0 := by
    exact_mod_cast (A.exteriorNorm_pos (b.leftResidual i.val)).ne'
  unfold FirstGaussPoolData.residualCoefficient FirstGaussPoolData.adjustedCoefficient
  rw [canonicalLog_leftDivisorCoefficient hΓ μv ν b C left right φ c e
      finiteTest hlc hcs radius D δ hδ hδhalf p S χ i.val hi hSi,
    p.divisorPools.left_ideal S, p.left_ideal,
    AmplifierResidualPresentation.columnPhase_eq_residue]
  field_simp [hN] <;> ring

/-- The right valuation source retains its actual complementary first
phase. There is no conjugation of this original coefficient. -/
theorem canonicalLog_rightResidualCoefficient
    (q : ExteriorPrime A) (n : ℕ)
    (j : (p.divisorPools.rightData S).valuationColumns q n)
    (hSj : S.val ∣ (p.rightData.ideal j.val).val) :
    (p.divisorPools.rightData S).residualCoefficient q n
        (p.rightDivisorCoefficient S χ) j =
      (e j.val * ((A.exteriorNorm (b.rightResidual j.val) ^ δ : ℝ) : ℂ) /
          (A.exteriorNorm
            ((p.divisorPools.rightData S).residualPresentation q n j).residual : ℂ)) *
        actualIdealResidue (A := A) (σ := σ) (b.rightResidual j.val).val
          (CanonicalLiteralFirstPhase.rightElement C b.primes
            b.leftMultiplicity b.rightMultiplicity
            (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) *
        actualIdealResidue (A := A) (σ := σ)
          ((p.divisorPools.rightData S).residualPresentation q n j).residual.val
          (generator C q ^ (2 * n)) := by
  have hj : j.val ∈ p.rightData.columns := by
    simpa only [p.divisorPools.right_columns S] using
      (Finset.mem_filter.mp j.property).1
  have hN : (A.exteriorNorm (b.rightResidual j.val) : ℂ) ≠ 0 := by
    exact_mod_cast (A.exteriorNorm_pos (b.rightResidual j.val)).ne'
  unfold FirstGaussPoolData.residualCoefficient FirstGaussPoolData.adjustedCoefficient
  rw [canonicalLog_rightDivisorCoefficient hΓ μv ν b C left right φ c e
      finiteTest hlc hcs radius D δ hδ hδhalf p S χ j.val hj hSj,
    p.divisorPools.right_ideal S, p.right_ideal,
    AmplifierResidualPresentation.columnPhase_eq_residue]
  field_simp [hN] <;> ring

end FirstBlockPoolData
end FirstChart

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.residualCoefficient_logarithmic
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalOriginalAtoms_secondInput_whole
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.canonicalLog_leftResidualCoefficient
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.canonicalLog_rightResidualCoefficient

