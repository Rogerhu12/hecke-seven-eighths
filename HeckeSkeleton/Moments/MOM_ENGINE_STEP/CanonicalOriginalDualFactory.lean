import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalDualTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalGaussTuples
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalTerminalPowers
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.EmptyGaussMask

/-!
# Original tuple and fixed-degree inputs for the actual dual calibration

This constructor consumes the actual original single-profile window and
the computed source dictionaries. Its tail degree follows from fixed
length bounds, and its tuple multiplicity is the original occurrence
count. The only stage identities supplied at the end are its empty mask,
physical inverse radius and chosen cutoff.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {ι : Type*} {G : ActualGaussSource C ι}

namespace ActualGaussStage

variable (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
variable {ω ψ : HeckeCharacter K} {d : MomentData K ω ψ}
variable {a : RealParameters} {Z t Y₁ Y₂ : ℝ} {centered : Bool}
variable (atoms : ParentConstantAtoms
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) d a Z t)
variable {common : A.Exterior} {divisor : Ideal (𝓞 K)} {δ : ℝ}
variable (D : G.OriginalNumerator (atoms.raw Y₁ Y₂).exteriorColumns
  (atoms.raw Y₁ Y₂).columnExterior ((atoms.values Y₁ Y₂).coefficient centered)
  divisor common δ)
variable (post : G.OriginalPostIdeal (atoms.raw Y₁ Y₂).columnExterior D.index)
variable {k multiplicity : ℕ} (tuples : G.OriginalTupleData k multiplicity)
variable (hdivisor : divisor ≠ 0) (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
variable (hleftArithmetic : ∀ I, ‖atoms.leftArithmetic I‖ ≤ 1)
variable (hrightArithmetic : ∀ I, ‖atoms.rightArithmetic I‖ ≤ 1)
variable (hprimeArithmetic : ∀ i p, ‖atoms.primeArithmetic i p‖ ≤ 1)
variable (cap : ℕ) (hcap : d.geometry.slotCount ≤ cap)
variable (orders : Finset (ℕ × ℕ))
variable (B lo hi loss leftExponent rightExponent : ℝ)
variable (hB : 1 ≤ B) (hlo : 0 < lo) (hloOne : lo ≤ 1) (hhi : 1 ≤ hi)
variable (hlowerThreshold : (lo ^ (cap + 2))⁻¹ ≤ Z ^ loss)
variable (hupperThreshold : hi ^ (cap + 2) ≤ Z ^ loss)
variable {floor padding : ℝ}
variable (domain : PairedEngineDomain centered d a Z Y₁ Y₂ floor padding)
variable (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
variable (hleftPower : Z ^ a.n₁ ≤ Z ^ leftExponent)
variable (hrightPower : Z ^ a.n₂ ≤ Z ^ rightExponent)
variable (hY₁le : Y₁ ≤ Z ^ leftExponent) (hY₂le : Y₂ ≤ Z ^ rightExponent)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ}
variable (profiles : RawProfileWindow rowDomain heightDomain window
  (OriginalProfileAtomBounds.profileOrders orders) d B)
variable (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain)
variable (ht : t ∈ heightDomain)
variable (hlowerWindow : window ⊆ Set.Ici lo) (hupperWindow : window ⊆ Set.Iic hi)
variable (sTail sZero : Finset (ℕ × ℕ))
variable (totalBound coarseBound frozenBound radiusBound Nsave decay inverseRadiusExponent : ℝ)
variable (htotal : a.n₁ + a.n₂ + d.geometry.totalLength ≤ totalBound)
variable (hcoarseNonneg : 0 ≤ leftExponent + rightExponent + d.geometry.totalLength + loss)
variable (hcoarse : leftExponent + rightExponent + d.geometry.totalLength + loss ≤ coarseBound)
variable (hfrozen : idealLogLength Z post.frozen ≤ frozenBound)
variable (hloss : loss ≤ 1) (hinverse : inverseRadiusExponent ≤ radiusBound)
variable (hmaskEmpty : s.mask = ∅)
variable (hradius : s.radius.val⁻¹ ≤ Z ^ inverseRadiusExponent)
variable (hcutoff : s.cutoff = Z ^ firstTailCutoffExponent
  (CanonicalOriginalTerminalPowers.tailDegree k totalBound coarseBound frozenBound radiusBound)
  Nsave decay)

include domain in
private theorem originalTotal_nonneg : 0 ≤ a.n₁ + a.n₂ + d.geometry.totalLength := by
  have hlength : 0 ≤ d.geometry.totalLength :=
    Finset.sum_nonneg (fun i _ => (d.geometry.slots i).length_pos.le)
  exact add_nonneg (add_nonneg domain.plain_left_nonneg domain.plain_right_nonneg) hlength

/-- The tail degree is computed from numerical original length windows.
No bound on a terminal, child energy or transformed profile is an input. -/
def canonicalOriginalDualCalibrationOfTuples :
    s.DualTerminalCalibration sTail sZero k Z
      (CanonicalOriginalTerminalPowers.tailDegree k totalBound coarseBound frozenBound radiusBound)
      Nsave decay :=
  s.canonicalOriginalDualCalibration atoms D post hdivisor hδ
    hleftArithmetic hrightArithmetic hprimeArithmetic cap orders B lo hi loss leftExponent rightExponent
    hB hlo hloOne hhi hcap hlowerThreshold hupperThreshold domain hY₁ hY₂ hleftPower hrightPower
    hY₁le hY₂le profiles hrows ht hlowerWindow hupperWindow sTail sZero k
    (CanonicalOriginalTerminalPowers.tailDegree k totalBound coarseBound frozenBound radiusBound)
    Nsave decay 0 inverseRadiusExponent hcoarseNonneg
    tuples.factors multiplicity tuples.fiber_card tuples.product
    (by simp only [hmaskEmpty, sIntegerMaskGenerator_empty_norm K A.Sf, Real.rpow_zero, le_refl])
    hradius
    (CanonicalOriginalTerminalPowers.secondTailExponent_le_tailDegree k
      (a.n₁ + a.n₂ + d.geometry.totalLength)
      (leftExponent + rightExponent + d.geometry.totalLength + loss)
      (idealLogLength Z post.frozen) (idealLogLength Z common.val) loss δ inverseRadiusExponent
      totalBound coarseBound frozenBound radiusBound
      (originalTotal_nonneg domain) htotal hcoarse hfrozen
      (idealLogLength_nonneg Z domain.scale common.val common.property.1)
      hloss hδ hδhalf hinverse) hcutoff

local notation "calibration" => s.canonicalOriginalDualCalibrationOfTuples atoms D post tuples
  hdivisor hδ hδhalf hleftArithmetic hrightArithmetic hprimeArithmetic cap hcap
  orders B lo hi loss leftExponent rightExponent hB hlo hloOne hhi
  hlowerThreshold hupperThreshold domain hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le
  profiles hrows ht hlowerWindow hupperWindow sTail sZero
  totalBound coarseBound frozenBound radiusBound Nsave decay inverseRadiusExponent
  htotal hcoarseNonneg hcoarse hfrozen hloss hinverse hmaskEmpty hradius hcutoff

/-- The original tuple bound is retained exactly, including every
valuation-allocation factor in the pool cases. -/
theorem canonicalOriginalDualCalibrationOfTuples_multiplicity :
    (calibration).windows.multiplicity = multiplicity := by
  unfold canonicalOriginalDualCalibrationOfTuples canonicalOriginalDualCalibration
  split <;> rfl

theorem canonicalOriginalDualCalibrationOfTuples_zeroProductExponent :
    (calibration).zeroProductExponent =
      2 * max 0 (a.n₁ + a.n₂ + d.geometry.totalLength + loss - idealLogLength Z post.frozen) := by
  unfold canonicalOriginalDualCalibrationOfTuples canonicalOriginalDualCalibration
  split <;> rfl

/-- A nonzero supported fibre supplies the physical-row premise.
The zero coefficient case has already been discharged by the factory. -/
theorem canonicalOriginalDualCalibrationOfTuples_amplitude_bounds
    (hphysical : G.rows.Nonempty) :
    (calibration).tailAmplitude ≤ ((2 * B ^ (cap + 2)) ^ 2 / (Ideal.absNorm divisor : ℝ)) *
        sTail.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) s.profile ∧
      (calibration).zeroAmplitude ≤
        (((2 * B ^ (cap + 2)) ^ 2 *
          sZero.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) s.profile) /
            (Ideal.absNorm divisor : ℝ)) *
          Z ^ (-(a.n₁ + a.n₂ + d.geometry.totalLength) +
            2 * (a.n₁ + a.n₂ + d.geometry.totalLength + loss - idealLogLength Z common.val) * δ +
              inverseRadiusExponent + 2 * loss) := by
  unfold canonicalOriginalDualCalibrationOfTuples
  exact s.canonicalOriginalDualCalibration_amplitude_bounds atoms D post hdivisor hδ
    hleftArithmetic hrightArithmetic hprimeArithmetic cap orders B lo hi loss leftExponent rightExponent
    hB hlo hloOne hhi hcap hlowerThreshold hupperThreshold domain hY₁ hY₂ hleftPower hrightPower
    hY₁le hY₂le profiles hrows ht hlowerWindow hupperWindow sTail sZero k
    (CanonicalOriginalTerminalPowers.tailDegree k totalBound coarseBound frozenBound radiusBound)
    Nsave decay 0 inverseRadiusExponent hcoarseNonneg tuples.factors multiplicity
    tuples.fiber_card tuples.product _ hradius _ hcutoff hphysical hmaskEmpty

end ActualGaussStage
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.canonicalOriginalDualCalibrationOfTuples
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.canonicalOriginalDualCalibrationOfTuples_multiplicity
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.canonicalOriginalDualCalibrationOfTuples_zeroProductExponent
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.canonicalOriginalDualCalibrationOfTuples_amplitude_bounds
