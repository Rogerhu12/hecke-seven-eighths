import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralRowMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalAtomBudget

set_option linter.unusedSectionVars false

/-!
# Uniform original atom costs for the literal exceptional source

The constants below depend only on the number field, the fixed original
slot cap and the fixed prime annulus. The profile amplitude is retained
as an explicit natural power. In particular it is not inserted into a
constant chosen after a Fourier mode or an exceptional row.

The two atomic scales are the original `originalAtomicScales` of the
actual side frames. The common factors are the computed common atoms
of the same covered row source. Their individual bounds follow from
the original prime supports and the zero-order seminorms of their
actual Schwartz representatives. No complete atom-product, row-mass or
exceptional-source bound is assumed.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalAtomBudget

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum
open HeckePort.CenteredMomentCounting

variable {K : Type} [Field K] [NumberField K]

def pairDegree (cap : ℕ) : ℕ := 10 * cap + 4

def pairConstant (cap : ℕ) (annulus : ℝ) : ℝ :=
  idealCountConstant K ^ (2 * cap) * annulus ^ (5 * cap + 2)

def commonDegree (cap : ℕ) : ℕ := 2 * cap + 2

def commonConstant (cap : ℕ) (annulus : ℝ) : ℝ := annulus ^ (cap + 1)

def totalDegree (cap : ℕ) : ℕ := 12 * cap + 6

def totalConstant (cap : ℕ) (annulus : ℝ) : ℝ :=
  commonConstant cap annulus * pairConstant (K := K) cap annulus

/-- The original central-scale compensation is a fixed annulus power.
It is retained separately from the actual atomic scales. -/
def paidTotalConstant (cap : ℕ) (annulus : ℝ) (centralPower : ℕ) : ℝ :=
  annulus ^ centralPower * totalConstant (K := K) cap annulus

theorem pairConstant_one (cap : ℕ) (annulus : ℝ) (hannulus : 1 ≤ annulus) :
    1 ≤ pairConstant (K := K) cap annulus := by
  sorry

theorem pairConstant_pos (cap : ℕ) (annulus : ℝ) (hannulus : 1 ≤ annulus) :
    0 < pairConstant (K := K) cap annulus := by
  sorry

theorem commonConstant_one (cap : ℕ) (annulus : ℝ) (hannulus : 1 ≤ annulus) :
    1 ≤ commonConstant cap annulus := by
  sorry

theorem totalConstant_pos (cap : ℕ) (annulus : ℝ) (hannulus : 1 ≤ annulus) :
    0 < totalConstant (K := K) cap annulus := by
  sorry

theorem paidTotalConstant_pos (cap : ℕ) (annulus : ℝ) (centralPower : ℕ)
    (hannulus : 1 ≤ annulus) :
    0 < paidTotalConstant (K := K) cap annulus centralPower := by
  sorry

private theorem atomRadius_one (annulus amplitude : ℝ)
    (hannulus : 1 ≤ annulus) (hamplitude : 1 ≤ amplitude) :
    1 ≤ annulus * amplitude ^ 2 := by
  sorry

private theorem annulus_le_atomRadius (annulus amplitude : ℝ)
    (hannulus : 1 ≤ annulus) (hamplitude : 1 ≤ amplitude) :
    annulus ≤ annulus * amplitude ^ 2 := by
  sorry

private theorem amplitude_le_atomRadius (annulus amplitude : ℝ)
    (hannulus : 1 ≤ annulus) (hamplitude : 1 ≤ amplitude) :
    amplitude ≤ annulus * amplitude ^ 2 := by
  sorry

private theorem pair_polynomial (cap : ℕ) (annulus amplitude : ℝ) :
    (annulus * amplitude ^ 2) ^ (cap + 2) *
        (idealCountConstant K * (annulus * amplitude ^ 2) ^ 2) ^ (2 * cap) =
      pairConstant (K := K) cap annulus * amplitude ^ pairDegree cap := by
  sorry

private theorem common_polynomial (cap : ℕ) (annulus amplitude : ℝ) :
    (annulus * amplitude ^ 2) ^ (cap + 1) =
      commonConstant cap annulus * amplitude ^ commonDegree cap := by
  sorry

/-- The fixed constants and the original profile powers combine before
any summation or integration. -/
theorem budget_product (cap : ℕ) (annulus amplitude : ℝ) :
    (commonConstant cap annulus * amplitude ^ commonDegree cap) *
        (pairConstant (K := K) cap annulus * amplitude ^ pairDegree cap) =
      totalConstant (K := K) cap annulus * amplitude ^ totalDegree cap := by
  sorry

/-- A central-scale compensation changes only the fixed constant;
the original profile power and the original source remain unchanged. -/
theorem paid_budget_product (cap : ℕ) (annulus amplitude : ℝ) (centralPower : ℕ) :
    annulus ^ centralPower *
        ((commonConstant cap annulus * amplitude ^ commonDegree cap) *
          (pairConstant (K := K) cap annulus * amplitude ^ pairDegree cap)) =
      paidTotalConstant (K := K) cap annulus centralPower * amplitude ^ totalDegree cap := by
  sorry

/-- This applies to the original allocation records themselves. Each
frozen occurrence and each retained prime is paid by the same original
amplitude. The slot cap is fixed before either allocation. -/
theorem original_pair_constant_le
    (cap : ℕ) (annulus amplitude : ℝ)
    (hannulus : 1 ≤ annulus) (hamplitude : 1 ≤ amplitude)
    {k l : ℕ} (left : ActualColumnAllocation K k) (right : ActualColumnAllocation K l)
    (baseLeft plainTotalLeft baseRight plainTotalRight : ℝ)
    (lengthLeft : Fin k → ℝ) (lengthRight : Fin l → ℝ)
    (hleftLength : ∀ i, 0 ≤ lengthLeft i) (hrightLength : ∀ i, 0 ≤ lengthRight i)
    (hk : k ≤ cap) (hl : l ≤ cap) :
    (left.originalAtomicScales baseLeft plainTotalLeft lengthLeft hleftLength
        (fun _ => annulus) (fun _ => amplitude)
        (fun _ => hannulus) (fun _ => zero_le_one.trans hamplitude)).constant *
      (right.originalAtomicScales baseRight plainTotalRight lengthRight hrightLength
        (fun _ => annulus) (fun _ => amplitude)
        (fun _ => hannulus) (fun _ => zero_le_one.trans hamplitude)).constant ≤
      pairConstant (K := K) cap annulus * amplitude ^ pairDegree cap := by
  sorry

section ActualFrames

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι] {k l : ℕ}
variable (dL : CanonicalLiteralRectangles.Atoms (K := K) k)
variable (dR : CanonicalLiteralRectangles.Atoms (K := K) l)
variable (S : ActualSecondCorrelationRows A σ H ι)
variable (C : A.GeneralArithmeticContext σ η hS)
variable (χL χR : (PUnit.{1} × PUnit.{1}) →* Circle)
variable (idealL : AllocationColumn K k → A.Exterior)
variable (idealR : AllocationColumn K l → A.Exterior)
variable (hidealL : ∀ i ∈ childCartesianColumns dL.plain₁ dL.plain₂ dL.slots,
  (idealL i).val = allocationColumnIdeal i)
variable (hidealR : ∀ i ∈ childCartesianColumns dR.plain₁ dR.plain₂ dR.slots,
  (idealR i).val = allocationColumnIdeal i)
variable (firstSignL firstSignR : ℝ) (divisorL divisorR : Ideal (𝓞 K))
variable (selectionL : primeSupport divisorL → Finset (Fin (k + 2)))
variable (selectionR : primeSupport divisorR → Finset (Fin (l + 2)))
variable (hneL : (pairedAllocatedColumns divisorL selectionL dL.plain₁ dL.plain₂ dL.slots
  id id HeightOneSpectrum.asIdeal).Nonempty)
variable (hneR : (pairedAllocatedColumns divisorR selectionR dR.plain₁ dR.plain₂ dR.slots
  id id HeightOneSpectrum.asIdeal).Nonempty)

/-- The actual left and right frame scales used by both centered and
ordinary controls have this fixed polynomial budget. No control record
or finished atom bound is an input. -/
theorem actual_pair_constant_le
    (cap : ℕ) (annulus amplitude : ℝ)
    (hannulus : 1 ≤ annulus) (hamplitude : 1 ≤ amplitude)
    (hk : k ≤ cap) (hl : l ≤ cap) :
    (CanonicalLiteralExceptionalAtoms.scales dL S C .left χL idealL hidealL firstSignL
        divisorL selectionL hneL annulus amplitude hannulus
        (zero_le_one.trans hamplitude)).constant *
      (CanonicalLiteralExceptionalAtoms.scales dR S C .right χR idealR hidealR firstSignR
        divisorR selectionR hneR annulus amplitude hannulus
        (zero_le_one.trans hamplitude)).constant ≤
      pairConstant (K := K) cap annulus * amplitude ^ pairDegree cap := by
  sorry

end ActualFrames

section OriginalCommonAtoms

variable {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)
variable {W : d.ProfileData} {window : Set ℝ} (E : W.SchwartzModel window)

private theorem common_witness_slot_mem {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support) (i : Fin k) :
    b.witness.2 i ∈ d.slots i := by
  sorry

/-- The common atom cost is computed on the original witness. Its
annulus ratio and squared profile are bounded separately from the
original prime support and the same Schwartz representative. -/
theorem common_atom_le {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)
    (annulus amplitude : ℝ) (hannulus : 1 ≤ annulus)
    (hmask : d.characters.MaskIndicator)
    (hprime : d.PrimeNormWindow annulus)
    (hprofile : ∀ i, SchwartzMap.seminorm ℂ 0 0 (E.slot i) ≤ amplitude)
    (i : Fin k) :
    (d.commonAtomBounds b hmask).annulus i * (d.commonAtomBounds b hmask).profile i ≤
      annulus * amplitude ^ 2 := by
  sorry

end OriginalCommonAtoms

section CoveredCommonSource

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
variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {s : ActualGaussStage (E := ℝ) hΓ μv hDiff G finiteTest}
variable {LC RC : SourceCartesianCover G.columns G.ideal}
variable (v : s.CoveredClassKey LC RC)
variable (leftAtoms : CanonicalLiteralRectangles.Atoms (K := K) (LC.branch v.2.2.1).slotCount)
variable (rightAtoms : CanonicalLiteralRectangles.Atoms (K := K) (RC.branch v.2.2.2.1).slotCount)
variable (leftMask : leftAtoms.characters.MaskIndicator) (rightMask : rightAtoms.characters.MaskIndicator)
variable {leftProfiles : (v.literalLeftOriginal leftAtoms).ProfileData}
variable {rightProfiles : (v.literalRightOriginal rightAtoms).ProfileData}
variable {leftWindow rightWindow : Set ℝ}
variable (leftModel : leftProfiles.SchwartzModel leftWindow)
variable (rightModel : rightProfiles.SchwartzModel rightWindow)

/-- The common envelope belongs to the same literal covered row
source. The only analytic inputs are original single-slot seminorms
and the original row profile; the two frozen products are proved here. -/
theorem actual_commonEnvelope_le
    (cap : ℕ) (annulus amplitude : ℝ)
    (hannulus : 1 ≤ annulus) (hamplitude : 1 ≤ amplitude)
    (hleftCap : (LC.branch v.2.2.1).slotCount ≤ cap)
    (hrightCap : (RC.branch v.2.2.2.1).slotCount ≤ cap)
    (hleftPrime : (v.literalLeftOriginal leftAtoms).PrimeNormWindow annulus)
    (hrightPrime : (v.literalRightOriginal rightAtoms).PrimeNormWindow annulus)
    (hleftProfile : ∀ i, SchwartzMap.seminorm ℂ 0 0 (leftModel.slot i) ≤ amplitude)
    (hrightProfile : ∀ i, SchwartzMap.seminorm ℂ 0 0 (rightModel.slot i) ≤ amplitude)
    (hclass : v.chart.NonunitLabelStable)
    (hrow : ∀ h ∈ (v.chart.actualRows s.mask s.cutoff s.cutoff_one v.rowLabel).rows,
      ‖v.chart.weight h‖ ≤ amplitude) :
    (v.literalSupportedRowMass leftAtoms rightAtoms leftMask rightMask hclass
      amplitude (zero_le_one.trans hamplitude) hrow).commonEnvelope ≤
      commonConstant cap annulus * amplitude ^ commonDegree cap := by
  sorry

end CoveredCommonSource

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalAtomBudget

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalAtomBudget.original_pair_constant_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalAtomBudget.actual_pair_constant_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalAtomBudget.common_atom_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalAtomBudget.actual_commonEnvelope_le
