import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralStrippedCovered

/-!
# Strip the original constants from an already constructed literal binding

The direct, main and residual source constructors already produce their
actual common-atom extraction and ordinary dictionary. This file uses
those computed values without reopening their private coefficient
proofs. A coefficient of the original live leaf proves each further
constant nonzero, before either ordinary rectangle is selected.

The resulting binding is the existing `literalStrippedRectangles` on
the same original leaf. Both continuous kernels, both finite column
carriers, the allocation and the exceptional predicate are retained.
No source inequality or whole-polynomial equality is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]
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

local instance canonicalLiteralStripExistingBindingCircleCharacterFintype :
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
variable (firstSign : ℝ) (hlive : (v.leaf exceptional firstKernel x j).Live)
variable (X : (v.leaf exceptional firstKernel x j).ConstantAtomExtraction)
variable (binding : X.leaf.OrdinaryBinding
  (v.literalRectangles leftAtoms rightAtoms exceptional firstKernel x j firstSign hlive))

include binding in
/-- The witness belongs to the original live leaf, including when its
ordinary row subset is empty. -/
theorem bound_literal_left_whole_present :
    ∃ i ∈ (v.leaf exceptional firstKernel x j).left,
      (v.literalLeftAtoms leftAtoms).whole i ≠ 0 := by
  obtain ⟨h, hh, i, hi, hc⟩ := hlive.2.1
  rw [X.left h hh i hi] at hc
  have hr : X.leaf.leftCoefficient h i ≠ 0 := right_ne_zero_of_mul hc
  rw [binding.leftCoefficient h hh i hi] at hr
  change (v.literalLeftAtoms leftAtoms).whole i * _ * _ ≠ 0 at hr
  exact ⟨i, hi, left_ne_zero_of_mul (left_ne_zero_of_mul hr)⟩

include binding in
theorem bound_literal_right_whole_present :
    ∃ i ∈ (v.leaf exceptional firstKernel x j).right,
      (v.literalRightAtoms rightAtoms).whole i ≠ 0 := by
  obtain ⟨h, hh, i, hi, hc⟩ := hlive.2.2
  rw [X.right h hh i hi] at hc
  have hr : X.leaf.rightCoefficient h i ≠ 0 := right_ne_zero_of_mul hc
  have hs : star (X.leaf.rightCoefficient h i) ≠ 0 := by
    simpa only [star_ne_zero] using hr
  rw [binding.rightCoefficient h hh i hi] at hs
  change star ((v.literalRightAtoms rightAtoms).whole i * _ * _) ≠ 0 at hs
  rw [star_ne_zero] at hs
  exact ⟨i, hi, left_ne_zero_of_mul (left_ne_zero_of_mul hs)⟩

include binding in
/-- `hform` is the proved normal form of the corresponding original
direct/main/residual atom constructor. -/
theorem bound_literal_left_scalar_nonzero
    (core : CanonicalLiteralRectangles.Atoms (K := K) (LC.branch v.2.2.1).slotCount)
    (c : ℂ) (hform : leftAtoms = core.scale c) : c ≠ 0 := by
  obtain ⟨i, _, hi⟩ := v.bound_literal_left_whole_present leftAtoms rightAtoms
    exceptional firstKernel x j firstSign hlive X binding
  rw [hform, v.literalLeftAtoms_scale core c,
    CanonicalLiteralRectangles.Atoms.scale_whole] at hi
  exact left_ne_zero_of_mul hi

include binding in
theorem bound_literal_right_scalar_nonzero
    (core : CanonicalLiteralRectangles.Atoms (K := K) (RC.branch v.2.2.2.1).slotCount)
    (c : ℂ) (hform : rightAtoms = core.scale c) : c ≠ 0 := by
  obtain ⟨i, _, hi⟩ := v.bound_literal_right_whole_present leftAtoms rightAtoms
    exceptional firstKernel x j firstSign hlive X binding
  rw [hform, v.literalRightAtoms_scale core c,
    CanonicalLiteralRectangles.Atoms.scale_whole] at hi
  exact left_ne_zero_of_mul hi

variable (leftScalar rightScalar : ℂ)
variable (hleftScalar : leftScalar ≠ 0) (hrightScalar : rightScalar ≠ 0)
variable (leftBalance rightBalance : Bool → ℝ)
variable (hleftBalance : ∀ r, 0 < leftBalance r)
variable (hrightBalance : ∀ r, 0 < rightBalance r)

/-- Compose the original computed extraction with the two proved
constant divisions. This is an exact dictionary transformation of the
already constructed literal binding, not a new normalization premise. -/
def stripExistingOrdinaryBinding :
    (X.trans (X.leaf.stripColumnConstants leftScalar rightScalar
      hleftScalar hrightScalar)).leaf.OrdinaryBinding
        (v.literalStrippedRectangles leftAtoms rightAtoms exceptional firstKernel x j
          leftScalar rightScalar firstSign hlive leftBalance rightBalance
          hleftBalance hrightBalance) := by
  have hrow (h) :
      (X.trans (X.leaf.stripColumnConstants leftScalar rightScalar
        hleftScalar hrightScalar)).leaf.rowWeight h =
          X.leaf.rowWeight h * leftScalar * star rightScalar :=
    congrArg (fun L => L.rowWeight h)
      (X.trans_leaf (X.leaf.stripColumnConstants leftScalar rightScalar
        hleftScalar hrightScalar))
  refine
    { rows := binding.rows
      rows_zero := ?_
      left := binding.left
      right := binding.right
      exceptional := binding.exceptional
      rowWeight := ?_
      leftCoefficient := ?_
      rightCoefficient := ?_
      leftPoint := binding.leftPoint
      rightPoint := binding.rightPoint }
  · intro h hh hn
    rw [hrow h, binding.rows_zero h hh hn, zero_mul, zero_mul]
  · intro h hh
    rw [hrow h, binding.rowWeight h hh]
    change ((_ * _) * leftScalar) * star rightScalar =
      (((v.literalSupportedRows leftAtoms rightAtoms).weight h * leftScalar) *
        star rightScalar) * (v.literalSupportedRows leftAtoms rightAtoms).correlation h
    ring
  · intro h hh i hi
    have hc := binding.leftCoefficient h hh i hi
    change leftScalar⁻¹ * _ = _
    rw [hc]
    unfold secondAllocatedLeftCoefficient
    rw [CanonicalLiteralRectangles.Atoms.scale_whole]
    ring
  · intro h hh i hi
    have hc := binding.rightCoefficient h hh i hi
    change star (rightScalar⁻¹ * _) = _
    rw [star_mul', hc]
    simp only [secondAllocatedRightCoefficient,
      CanonicalLiteralRectangles.Atoms.scale_whole, star_mul']
    ring

end ActualGaussStage.CoveredClassKey
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.bound_literal_left_scalar_nonzero
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.bound_literal_right_scalar_nonzero
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.stripExistingOrdinaryBinding
