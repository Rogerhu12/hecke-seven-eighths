import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralRowMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalAtomBudget

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
    1 ≤ pairConstant (K := K) cap annulus :=
  one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ (one_le_idealCountConstant K)) (one_le_pow₀ hannulus)

theorem pairConstant_pos (cap : ℕ) (annulus : ℝ) (hannulus : 1 ≤ annulus) :
    0 < pairConstant (K := K) cap annulus :=
  zero_lt_one.trans_le (pairConstant_one cap annulus hannulus)

theorem commonConstant_one (cap : ℕ) (annulus : ℝ) (hannulus : 1 ≤ annulus) :
    1 ≤ commonConstant cap annulus := one_le_pow₀ hannulus

theorem totalConstant_pos (cap : ℕ) (annulus : ℝ) (hannulus : 1 ≤ annulus) :
    0 < totalConstant (K := K) cap annulus :=
  mul_pos (zero_lt_one.trans_le (commonConstant_one cap annulus hannulus))
    (pairConstant_pos cap annulus hannulus)

theorem paidTotalConstant_pos (cap : ℕ) (annulus : ℝ) (centralPower : ℕ)
    (hannulus : 1 ≤ annulus) :
    0 < paidTotalConstant (K := K) cap annulus centralPower :=
  mul_pos (pow_pos (zero_lt_one.trans_le hannulus) _)
    (totalConstant_pos cap annulus hannulus)

private theorem atomRadius_one (annulus amplitude : ℝ)
    (hannulus : 1 ≤ annulus) (hamplitude : 1 ≤ amplitude) :
    1 ≤ annulus * amplitude ^ 2 :=
  one_le_mul_of_one_le_of_one_le hannulus (one_le_pow₀ hamplitude)

private theorem annulus_le_atomRadius (annulus amplitude : ℝ)
    (hannulus : 1 ≤ annulus) (hamplitude : 1 ≤ amplitude) :
    annulus ≤ annulus * amplitude ^ 2 := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (one_le_pow₀ hamplitude (n := 2)) (zero_le_one.trans hannulus)

private theorem amplitude_le_atomRadius (annulus amplitude : ℝ)
    (hannulus : 1 ≤ annulus) (hamplitude : 1 ≤ amplitude) :
    amplitude ≤ annulus * amplitude ^ 2 := by
  have hs : amplitude ≤ amplitude ^ 2 := by
    nlinarith [mul_nonneg (zero_le_one.trans hamplitude) (sub_nonneg.mpr hamplitude)]
  have ha : amplitude ^ 2 ≤ annulus * amplitude ^ 2 := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hannulus (sq_nonneg amplitude)
  exact hs.trans ha

private theorem pair_polynomial (cap : ℕ) (annulus amplitude : ℝ) :
    (annulus * amplitude ^ 2) ^ (cap + 2) *
        (idealCountConstant K * (annulus * amplitude ^ 2) ^ 2) ^ (2 * cap) =
      pairConstant (K := K) cap annulus * amplitude ^ pairDegree cap := by
  let B := annulus * amplitude ^ 2
  calc
    _ = idealCountConstant K ^ (2 * cap) *
        (B ^ (cap + 2) * (B ^ 2) ^ (2 * cap)) := by
      rw [mul_pow (idealCountConstant K) (B ^ 2) (2 * cap)]
      ring
    _ = idealCountConstant K ^ (2 * cap) * B ^ (5 * cap + 2) := by
      rw [← pow_mul, ← pow_add,
        show cap + 2 + 2 * (2 * cap) = 5 * cap + 2 by omega]
    _ = _ := by
      dsimp only [B, pairConstant, pairDegree]
      rw [mul_pow, ← pow_mul,
        show 2 * (5 * cap + 2) = 10 * cap + 4 by omega]
      ring

private theorem common_polynomial (cap : ℕ) (annulus amplitude : ℝ) :
    (annulus * amplitude ^ 2) ^ (cap + 1) =
      commonConstant cap annulus * amplitude ^ commonDegree cap := by
  simp only [commonConstant, commonDegree, mul_pow, ← pow_mul, Nat.mul_add, Nat.mul_one]

/-- The fixed constants and the original profile powers combine before
any summation or integration. -/
theorem budget_product (cap : ℕ) (annulus amplitude : ℝ) :
    (commonConstant cap annulus * amplitude ^ commonDegree cap) *
        (pairConstant (K := K) cap annulus * amplitude ^ pairDegree cap) =
      totalConstant (K := K) cap annulus * amplitude ^ totalDegree cap := by
  calc
    _ = totalConstant (K := K) cap annulus *
        (amplitude ^ commonDegree cap * amplitude ^ pairDegree cap) := by
      unfold totalConstant
      ring
    _ = _ := by
      rw [← pow_add]
      congr 1
      congr 1
      simp only [commonDegree, pairDegree, totalDegree]
      omega

/-- A central-scale compensation changes only the fixed constant;
the original profile power and the original source remain unchanged. -/
theorem paid_budget_product (cap : ℕ) (annulus amplitude : ℝ) (centralPower : ℕ) :
    annulus ^ centralPower *
        ((commonConstant cap annulus * amplitude ^ commonDegree cap) *
          (pairConstant (K := K) cap annulus * amplitude ^ pairDegree cap)) =
      paidTotalConstant (K := K) cap annulus centralPower * amplitude ^ totalDegree cap := by
  rw [budget_product]
  unfold paidTotalConstant
  ring

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
  let UL := left.originalAtomicScales baseLeft plainTotalLeft lengthLeft hleftLength
    (fun _ => annulus) (fun _ => amplitude)
    (fun _ => hannulus) (fun _ => zero_le_one.trans hamplitude)
  let UR := right.originalAtomicScales baseRight plainTotalRight lengthRight hrightLength
    (fun _ => annulus) (fun _ => amplitude)
    (fun _ => hannulus) (fun _ => zero_le_one.trans hamplitude)
  have hB := atomRadius_one annulus amplitude hannulus hamplitude
  have ha := annulus_le_atomRadius annulus amplitude hannulus hamplitude
  have hp := amplitude_le_atomRadius annulus amplitude hannulus hamplitude
  have h := UL.pair_constant_le_from_atoms UR cap (annulus * amplitude ^ 2)
    hB hk hl (fun _ _ => le_rfl) (fun _ _ => le_rfl) hB hB
    (fun _ => ha) (fun _ => ha) (fun _ => hp) (fun _ => hp)
  exact h.trans_eq (pair_polynomial (K := K) cap annulus amplitude)

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
      pairConstant (K := K) cap annulus * amplitude ^ pairDegree cap :=
  original_pair_constant_le cap annulus amplitude hannulus hamplitude
    ((dL.factors S .left χL idealL hidealL firstSignL false).frame C divisorL selectionL hneL).allocation
    ((dR.factors S .right χR idealR hidealR firstSignR false).frame C divisorR selectionR hneR).allocation
    dL.base (Real.log (dL.scale₁ false * dL.scale₂ false) / Real.log dL.base)
    dR.base (Real.log (dR.scale₁ false * dR.scale₂ false) / Real.log dR.base)
    dL.length dR.length (fun i => (dL.length_pos i).le) (fun i => (dR.length_pos i).le) hk hl

end ActualFrames

section OriginalCommonAtoms

variable {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)
variable {W : d.ProfileData} {window : Set ℝ} (E : W.SchwartzModel window)

private theorem common_witness_slot_mem {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support) (i : Fin k) :
    b.witness.2 i ∈ d.slots i := by
  have hw : b.witness ∈ b.originalColumns := b.witness_mem
  rw [b.originalColumns_eq_filter] at hw
  exact Fintype.mem_piFinset.mp (Finset.mem_product.mp (Finset.mem_filter.mp hw).1).2 i

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
  have ha : (d.commonAtomBounds b hmask).annulus i ≤ annulus := by
    change (Ideal.absNorm (b.witness.2 i).asIdeal : ℝ) / d.base ^ d.length i ≤ annulus
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (zero_lt_one.trans d.base_gt_one) _)).mpr
      (hprime i _ (common_witness_slot_mem d b i))
  have hp : (d.commonAtomBounds b hmask).profile i ≤ amplitude ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _)
      (CanonicalLiteralExceptionalAtoms.slot_norm_le d E amplitude hprofile i (b.witness.2 i)) 2
  exact mul_le_mul ha hp (sq_nonneg _) (zero_le_one.trans hannulus)

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
  let mass := v.literalSupportedRowMass leftAtoms rightAtoms leftMask rightMask hclass
    amplitude (zero_le_one.trans hamplitude) hrow
  have h := mass.commonEnvelope_le_from_atoms cap (annulus * amplitude ^ 2)
    (atomRadius_one annulus amplitude hannulus hamplitude) hleftCap hrightCap
    (amplitude_le_atomRadius annulus amplitude hannulus hamplitude)
    (fun i _ => common_atom_le (v.literalLeftOriginal leftAtoms) leftModel
      v.literalLeftBranch annulus amplitude hannulus leftMask hleftPrime hleftProfile i)
    (fun i _ => common_atom_le (v.literalRightOriginal rightAtoms) rightModel
      v.literalRightBranch annulus amplitude hannulus rightMask hrightPrime hrightProfile i)
  exact h.trans_eq (common_polynomial cap annulus amplitude)

end CoveredCommonSource

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalAtomBudget

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalAtomBudget.original_pair_constant_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalAtomBudget.actual_pair_constant_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalAtomBudget.common_atom_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalAtomBudget.actual_commonEnvelope_le
