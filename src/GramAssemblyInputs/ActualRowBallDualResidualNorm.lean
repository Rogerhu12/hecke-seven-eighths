import ActualRowBallResidualScalarBound

/-!
UNCOMPILED / native 0. The complete original-Gamma row-ball dual integrand,
with the actual denominator and c = 1, is bounded by the finite sum of norms
of its genuine residual sums. Only finite triangle inequalities are used.
The original pair radii, free Fourier profile and coefficients are unchanged.
The representative is q.out; no individual artificial chart term is claimed
to descend to the Gamma quotient. Squarefree divisor labels are also
reindexed injectively to their actual exterior ideals.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualRowBallDualResidualNormDraft

open NumberField IsDedekindDomain MeasureTheory UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Arithmetic.IdealMobiusMask
open HeckeGeneral.Arithmetic.AllowedGeneratorSectionDraft
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.ActualGeneratorDivisionDraft
open HeckeGeneral.ThetaSkeleton.Global.ActualPairDivisorDraft
open HeckeGeneral.ThetaSkeleton.Global.ActualGcdMobiusDraft
open ActualAdditiveGramDraft ActualRowBallDualChartDraft
open ActualRowBallResidualScalarDraft
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (w : GeneratorMaskWitness K)

local notation "S" => (w.S : Set (HeightOneSpectrum (𝓞 K)))
local notation "E" => ExteriorIdeal K S
local notation "NZ" => NonzeroRingElements (Set.integer S K)
local notation "Γ" => sixthPowerUnits K S
local notation "OQ" => SIntegerOrbits K S Γ

/-- Different prime subsets give different actual exterior Mobius divisors. -/
theorem residualMobiusDivisor_injective (C : E) (A B : Finset E) :
    Function.Injective (residualMobiusDivisor K S C A B) := by
  intro T U h
  apply Subtype.ext
  apply Finset.val_injective
  apply Multiset.map_injective HeightOneSpectrum.asIdeal_injective
  have hI : primeProduct T.val = primeProduct U.val :=
    congrArg (fun D : E => D.val.val) h
  simpa only [normalizedFactors_primeProduct] using congrArg normalizedFactors hI

/-- The finite set consists of actual exterior ideals, without multiplicity. -/
def residualMobiusDivisorSet (C : E) (A B : Finset E) : Finset E :=
  (residualPrimeEnvelope K S C A B).powerset.attach.image
    (residualMobiusDivisor K S C A B)

theorem sum_residualMobiusDivisor_eq (C : E) (A B : Finset E) (f : E → ℝ) :
    (∑ T ∈ (residualPrimeEnvelope K S C A B).powerset.attach,
      f (residualMobiusDivisor K S C A B T)) =
        ∑ D ∈ residualMobiusDivisorSet K w C A B, f D := by
  symm
  exact Finset.sum_image (residualMobiusDivisor_injective K w C A B).injOn

private theorem norm_moebius_primeProduct_complex
    (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ‖(moebius (primeProduct T) : ℂ)‖ = 1 := by
  simp only [moebius_primeProduct, Int.cast_pow, Int.cast_neg, Int.cast_one,
    norm_pow, norm_neg, norm_one, one_pow]

variable [MeasurableSpace (sLocalNormOneGroup K
    (w.S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (w.S : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

/-- This individual residual is zero on the nondivisible branch. Its
vanishing is proved from the actual extension definition, not assumed. -/
theorem rowBallResidualSum_eq_zero_of_not_dvd
    (P : ProbeData K S) (hP : P.arithmetic = w.D)
    (Y η : ℝ) (r : {r : ℝ // 0 < r}) (C D : E) (j : NZ)
    (hj : ¬ w.D.generator C ∣ j.val) :
    rowBallResidualSum K w μv P Y η r C D j = 0 := by
  unfold rowBallResidualSum
  apply Finset.sum_eq_zero
  intro mn _
  rw [hP, thetaChartCorrelationExtension_eq_zero_of_not_dvd K S w.D C _ j hj,
    mul_zero]

/-- Exact residual expansion of the complete quotient integrand. The
same chosen representative is used throughout the finite expansion. -/
theorem rowBallDualIntegrand_eq_residuals
    (P : ProbeData K S) (Y η : ℝ) (r : {r : ℝ // 0 < r}) (q : OQ) :
    rowBallDualIntegrand K w.S μv P P.denominator.toSmoothAnnularTest Y η r q =
      let rows := additiveGramIdealSupport K S P.denominator.toSmoothAnnularTest Y
      ∑ C ∈ finiteCommonParts K S rows rows,
        ∑ T ∈ (residualPrimeEnvelope K S C rows rows).powerset.attach,
          (moebius (primeProduct T.val) : ℂ) *
            rowBallResidualSum K w μv P Y η r C
              (residualMobiusDivisor K S C rows rows T) q.out := by
  calc
    _ = rowBallDualIntegrand K w.S μv P P.denominator.toSmoothAnnularTest
        Y η r (Quotient.mk _ q.out) :=
      congrArg (rowBallDualIntegrand K w.S μv P P.denominator.toSmoothAnnularTest
        Y η r) (Quotient.out_eq q).symm
    _ = _ := by
      rw [rowBallDualIntegrand_mk_eq_chart]
      rfl

/-- Both finite triangle inequalities; every squarefree Mobius coefficient
has norm one, so no coefficient loss remains in the residual norm sum. -/
theorem norm_rowBallDualIntegrand_le_residuals
    (P : ProbeData K S) (Y η : ℝ) (r : {r : ℝ // 0 < r}) (q : OQ) :
    ‖rowBallDualIntegrand K w.S μv P P.denominator.toSmoothAnnularTest Y η r q‖ ≤
      let rows := additiveGramIdealSupport K S P.denominator.toSmoothAnnularTest Y
      ∑ C ∈ finiteCommonParts K S rows rows,
        ∑ T ∈ (residualPrimeEnvelope K S C rows rows).powerset.attach,
          ‖rowBallResidualSum K w μv P Y η r C
            (residualMobiusDivisor K S C rows rows T) q.out‖ := by
  rw [rowBallDualIntegrand_eq_residuals]
  dsimp only
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro C _
  refine (norm_sum_le _ _).trans_eq ?_
  apply Finset.sum_congr rfl
  intro T _
  rw [norm_mul, norm_moebius_primeProduct_complex, one_mul]

/-- The same bound with each subset label replaced by its actual ideal.
No infinite reordering, orbit-wise chart descent or final Gram estimate
is required for this finite identity and inequality. -/
theorem norm_rowBallDualIntegrand_le_actualDivisors
    (P : ProbeData K S) (Y η : ℝ) (r : {r : ℝ // 0 < r}) (q : OQ) :
    ‖rowBallDualIntegrand K w.S μv P P.denominator.toSmoothAnnularTest Y η r q‖ ≤
      let rows := additiveGramIdealSupport K S P.denominator.toSmoothAnnularTest Y
      ∑ C ∈ finiteCommonParts K S rows rows,
        ∑ D ∈ residualMobiusDivisorSet K w C rows rows,
          ‖rowBallResidualSum K w μv P Y η r C D q.out‖ := by
  refine (norm_rowBallDualIntegrand_le_residuals K w μv P Y η r q).trans_eq ?_
  dsimp only
  apply Finset.sum_congr rfl
  intro C _
  exact sum_residualMobiusDivisor_eq K w C _ _
    (fun D => ‖rowBallResidualSum K w μv P Y η r C D q.out‖)

end HeckeGeneral.ThetaSkeleton.Physical.ActualRowBallDualResidualNormDraft
