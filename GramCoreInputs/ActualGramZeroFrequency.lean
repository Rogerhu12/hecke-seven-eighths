import ActualAdditiveGramPoissonAssembly
import ActualSexticZeroFrequencyDiagonal

/-!
UNCOMPILED candidate. The actual ideal labels turn the principal-ideal
diagonal into literal equality of exterior ideals. The full zero correction
is then exactly a positive-dual diagonal contribution minus the ORIGINAL
zero-row square. Neither zero term is discarded or treated as a sheet limit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualAdditiveGramDraft

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton.Global
open ActualProbeGaussFourierDraft ActualProbePairPoissonDraft
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "SF" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer SF K

/-- The actual residue-unit count, including the unit ideal. -/
def additiveGramDiagonalUnitCount (P : ProbeData K SF) (I : ExteriorIdeal K SF) : ℕ :=
  Nat.card ((OS ⧸ Ideal.span ({(probeGenerator K SF P.arithmetic I).val} : Set OS))ˣ)

theorem additiveGramFullCorrelation_zero_of_ne (P : ProbeData K SF)
    (I J : ExteriorIdeal K SF) (hIJ : I ≠ J) :
    additiveGramFullCorrelation K S P I J 0 = 0 := by
  apply sIntegerSexticOriginalFullCorrelation_zero_of_contraction_ne
  intro h
  rw [probeGenerator_contraction, probeGenerator_contraction] at h
  exact hIJ (Subtype.ext (Subtype.ext h))

theorem additiveGramFullCorrelation_self_zero (P : ProbeData K SF)
    (I : ExteriorIdeal K SF) :
    additiveGramFullCorrelation K S P I I 0 =
      (additiveGramDiagonalUnitCount K S P I : ℂ) :=
  sIntegerSexticOriginalFullCorrelation_self_zero K SF
    P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding
    (probeArithmetic_six_support K SF P.arithmetic) (probeGenerator K SF P.arithmetic I)

theorem additiveGramDiagonalUnitCount_le_norm (P : ProbeData K SF)
    (I : ExteriorIdeal K SF) :
    (additiveGramDiagonalUnitCount K S P I : ℝ) ≤ exteriorNorm K SF I := by
  let u := probeGenerator K SF P.arithmetic I
  let Q := OS ⧸ Ideal.span ({u.val} : Set OS)
  letI : Finite Q := finite_sIntegerPrincipalResidue K SF u.val u.property
  have hc : Nat.card Qˣ ≤ Nat.card Q :=
    Nat.card_le_card_of_injective Units.val Units.val_injective
  have hn : Nat.card Q = I.val.val.absNorm := by
    rw [natCard_sIntegerPrincipalResidue K SF u.val u.property]
    exact congrArg Ideal.absNorm (probeGenerator_contraction K SF P.arithmetic I)
  change (Nat.card Qˣ : ℝ) ≤ (I.val.val.absNorm : ℝ)
  exact_mod_cast hc.trans_eq hn

/-- The complete finite ideal-pair sum at zero collapses to the genuine
diagonal, even with an arbitrary joint coefficient on the ideal pair. -/
theorem sum_additiveGramFullCorrelation_zero (P : ProbeData K SF)
    (F : Finset (ExteriorIdeal K SF))
    (a : ExteriorIdeal K SF → ExteriorIdeal K SF → ℂ) :
    (∑ I ∈ F, ∑ J ∈ F, a I J * additiveGramFullCorrelation K S P I J 0) =
      ∑ I ∈ F, a I I * (additiveGramDiagonalUnitCount K S P I : ℂ) := by
  apply Finset.sum_congr rfl
  intro I hI
  rw [Finset.sum_eq_single_of_mem I hI]
  · rw [additiveGramFullCorrelation_self_zero]
  · intro J hJ hJI
    rw [additiveGramFullCorrelation_zero_of_ne K S P I J (Ne.symm hJI), mul_zero]

variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
variable [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
variable [∀ v, (μv v).IsAddHaarMeasure]

/-- Both original zero contributions in the first Poisson formula, with
the central Y^(-3) normalization already applied. The negative term is the
square of the literal zero-row amplitude; its removal requires positivity
of the chosen majorant and is not asserted by this complex identity. -/
theorem sum_additiveGramPairZeroCorrection_eq_diagonal_sub_zeroRow
    (P : ProbeData K SF) (c : ExteriorIdeal K SF → ℂ) (W : SmoothAnnularTest)
    (Y ν : ℝ) (hY : 0 < Y) (r : {r : ℝ // 0 < r}) :
    ((Y ^ (-3 : ℝ) : ℝ) : ℂ) *
        (∑ I ∈ additiveGramIdealSupport K SF W Y,
          ∑ J ∈ additiveGramIdealSupport K SF W Y,
            actualAdditiveGramPairCoefficient K SF c W Y ν I J *
              additiveGramPairZeroCorrection K S μv P I J r) =
      ((r.val : ℂ)⁻¹ * ((Y ^ (-3 : ℝ) : ℝ) : ℂ) * additiveGramPoissonFieldFactor K) *
        sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K P.additive.infiniteTest)
          (probeFiniteFamily K S P) 0 *
        (∑ I ∈ additiveGramIdealSupport K SF W Y,
          actualAdditiveGramPairCoefficient K SF c W Y ν I I *
            (additiveGramDiagonalUnitCount K S P I : ℂ)) -
      ((‖actualAdditiveGramAmplitude K SF P c W Y ν (0 : OS)‖ ^ 2 : ℝ) : ℂ) *
        sIntegerTensorTerm K S (traceSchwartzToMixed K P.additive.infiniteTest)
          (probeFiniteFamily K S P) 0 := by
  let F := additiveGramIdealSupport K SF W Y
  let a := actualAdditiveGramPairCoefficient K SF c W Y ν
  let z : ℂ := ((Y ^ (-3 : ℝ) : ℝ) : ℂ)
  let b : ℂ := (r.val : ℂ)⁻¹ * additiveGramPoissonFieldFactor K
  let d : ℂ := sIntegerDualTensorTerm K μv S
    (traceSchwartzToMixed K P.additive.infiniteTest) (probeFiniteFamily K S P) 0
  let t : ℂ := sIntegerTensorTerm K S
    (traceSchwartzToMixed K P.additive.infiniteTest) (probeFiniteFamily K S P) 0
  let g := fun I J : ExteriorIdeal K SF =>
    probeGauss K SF P I 0 * conj (probeGauss K SF P J 0)
  have hrow :
      z * (∑ I ∈ F, ∑ J ∈ F, a I J * g I J) =
        ((‖actualAdditiveGramAmplitude K SF P c W Y ν (0 : OS)‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [z, F, a, g, actualAdditiveGramPairTerm,
      actualAdditiveGramPairCoefficient, neg_zero] using
      (actualAdditiveGramAmplitude_norm_sq_eq_double_sum K SF P c W Y ν hY (0 : OS)).symm
  have hrowt :
      z * ((∑ I ∈ F, ∑ J ∈ F, a I J * g I J) * t) =
        ((‖actualAdditiveGramAmplitude K SF P c W Y ν (0 : OS)‖ ^ 2 : ℝ) : ℂ) * t := by
    rw [← mul_assoc, hrow]
  have hsplit :
      (∑ I ∈ F, ∑ J ∈ F, a I J * additiveGramPairZeroCorrection K S μv P I J r) =
        b * d * (∑ I ∈ F, ∑ J ∈ F, a I J * additiveGramFullCorrelation K S P I J 0) -
          (∑ I ∈ F, ∑ J ∈ F, a I J * g I J) * t := by
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro I hI
    apply Finset.sum_congr rfl
    intro J hJ
    change a I J * (b * (additiveGramFullCorrelation K S P I J 0 * d) - g I J * t) = _
    ring
  change z * (∑ I ∈ F, ∑ J ∈ F, a I J * additiveGramPairZeroCorrection K S μv P I J r) = _
  rw [hsplit, sum_additiveGramFullCorrelation_zero K S P F a, mul_sub, hrowt]
  dsimp only [z, b, d, t, F, a]
  ring

end HeckeGeneral.ThetaSkeleton.Physical.ActualAdditiveGramDraft
