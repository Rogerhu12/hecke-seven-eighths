import HeckeSkeleton.GramDefinitions
import HeckeSkeleton.GramUnitInvariant
import HeckeSkeleton.GramOrdinaryCount
import HeckeSkeleton.GramDyadic
import HeckeSkeleton.GramIdealShell
import HeckeSkeleton.GramCorrelation
import HeckeSkeleton.GramMeanZero
import HeckeSkeleton.GramRowBall
import HeckeSkeleton.GramExceptionalCount
import HeckeSkeleton.GramSmallRadius

/-!
Top-down EXPLORATORY dependency skeleton for revised Proposition 3.8.
Remaining admissions are separately labelled. Cache work is evidence
of candidate work, not an imported proof. The final coarse bridge explicitly
retains the still missing chosen-generator/masked-whole-column identification.
Only c=1 (the actual T probe) is asserted; no arbitrary finite-ray family.
-/
set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.Gram
open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.Analysis.SquarefreeAmplification
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors
variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

-- OBLIGATION GR-01 | revised §3.5 (3.33), p.13.
-- Existing cache: ActualAdditiveGramAmplitude finite ideal support.
theorem amplitude_finite_support (P : ProbeData K S) (W : SmoothAnnularTest)
    (Y ν : ℝ) (hY : 0 < Y) (m : S.integer K) :
    (Function.support (gramTerm K S P W Y ν m)).Finite := by
  classical
  let F : Finset (ExteriorIdeal K S) :=
    (dyadicIdealSupport K (W.upper * Y / 2)).subtype
      (fun I : NonzeroIdeal K =>
        ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val → p ∉ S)
  apply F.finite_toSet.subset
  intro I hI
  have hW : W.toFun (exteriorNorm K S I / Y) ≠ 0 := by
    intro hz
    apply hI
    simp only [gramTerm, hz, zero_mul]
  have hnorm : exteriorNorm K S I ≤ W.upper * Y :=
    (div_le_iff₀ hY).mp (W.support hW).2
  have hu : 0 < W.upper := lt_of_lt_of_le W.lower_pos W.upper_ge
  have hD : 0 ≤ W.upper * Y / 2 :=
    div_nonneg (mul_nonneg hu.le hY.le) (by norm_num)
  change I ∈ F
  dsimp only [F]
  rw [Finset.mem_subtype, mem_dyadicIdealSupport_iff K hD I.val]
  change exteriorNorm K S I ≤ 2 * (W.upper * Y / 2)
  simpa only [show 2 * (W.upper * Y / 2) = W.upper * Y by ring] using hnorm

-- OBLIGATION GR-02 | revised §3.1/§3.5, pp.3–5,13–14.
-- Existing cache: ActualProbeGaussSixthUnitOrbit / UnitOrbits. Original Γ.
theorem amplitude_sixth_unit (P : ProbeData K S) (W : SmoothAnnularTest)
    (Y ν : ℝ) (γ : sixthPowerUnits K S) (m : S.integer K) :
    amplitude K S P W Y ν ((S.unitEquivUnitsInteger K γ.val).val * m) =
      amplitude K S P W Y ν m := by
  unfold amplitude
  congr 1
  apply tsum_congr
  intro I
  unfold gramTerm
  rw [gramProbeGauss_neg_mul_sixthPowerUnits]

/-- The allowed multiplication law genuinely supplies a SIXTH-power sector,
not an arbitrary generator-division unit. This step needs no admission. -/
theorem generator_product_sector (P : ProbeData K S)
    (hallowed : AllowedGeneratorInput K S P.arithmetic) (I J : ExteriorIdeal K S) :
    ∃ u : S.unit K, P.arithmetic.generator (exteriorMul K S I J) =
      (S.unitEquivUnitsInteger K u).val ^ 6 *
        P.arithmetic.generator I * P.arithmetic.generator J :=
  hallowed.multiplicative I J

-- OBLIGATION GR-03 | revised §3.5 (3.35), p.14.
-- Existing cache: ActualProbeGaussOriginalFourier / PairPeriodicFourier.
-- The literal denominator is gen(I)*gen(J), not an uncorrected gen(IJ).
theorem complete_pair_fourier (P : ProbeData K S) (I J : ExteriorIdeal K S)
    (m : S.integer K) :
    probeGauss K S P I (-m) * conj (probeGauss K S P J (-m)) =
      ∑' j : ThetaQuotient K S (exteriorMul K S I J),
        correlation K S P I J (Classical.choose (Ideal.Quotient.mk_surjective j)) *
          sLocalPrincipalPhase K S
            (((-m : S.integer K) : K) *
              ((Classical.choose (Ideal.Quotient.mk_surjective j) : S.integer K) : K) /
                ((P.arithmetic.generator I : K) * (P.arithmetic.generator J : K))) :=
  HeckeSkeleton.GramCorrelation.complete_pair_fourier K S P I J m

-- OBLIGATION GR-04 | revised §3.5, p.15 (zero frequency).
-- Existing cache: ActualSexticZeroFrequencyDiagonal, ActualGramZeroFrequency.
-- Associates are compared as ideals; only the I=J clause uses literal gen(I).
theorem zero_frequency_diagonal (P : ProbeData K S) (I J : ExteriorIdeal K S) :
    (I ≠ J → correlation K S P I J 0 = 0) ∧
    correlation K S P I I 0 = (Nat.card (ThetaQuotient K S I)ˣ : ℂ) :=
  HeckeSkeleton.GramCorrelation.zero_frequency_diagonal K S P I J

-- OBLIGATION GR-05 | revised §3.5 (3.36) and mean-zero paragraph, p.14.
-- Existing: actual finite sextic evaluations and full local correlation tables.
-- Necessary local cancellation only; it is NOT cancellation of an arbitrary
-- chosen-generator subset or a proof that the C6 choice mask is absent.
theorem residual_character_mean_zero (P : ProbeData K S) (I : ExteriorIdeal K S)
    (hI : ∃ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val.val ∧
      ¬ 6 ∣ idealPrimeMultiplicity K p I.val.val) :
    (∑' x : ThetaQuotient K S I, columnCharacter K S P I x) = 0 :=
  HeckeSkeleton.GramMeanZero.residual_character_mean_zero K S P I hI

-- OBLIGATION GR-06 | revised §3.1/§3.5, pp.3–5,15.
-- Existing cache: ActualOrdinaryOrbitShellCount, using verified ideal linear
-- count plus ALL SixthUnitClasses. Finite is retained, so Nat.card is meaningful.
theorem ordinary_frequency_count :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 0 < X →
      Finite (ordinaryCutoff K S X) ∧
      (Nat.card (ordinaryCutoff K S X) : ℝ) ≤ C * X := by
  exact gramOrdinaryFrequencyCount K S

-- OBLIGATION GR-07 | revised §3.5 exceptional paragraph, p.15.
-- Existing cache: ActualExceptionalSixthIdealCount / OrbitCount. kR means
-- the principal ideal of k in R=O_{K,S}, NOT a fixed multiplier R.
theorem exceptional_frequency_count {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : NonzeroIdeal K) (X : ℝ), 0 < X →
      Finite (exceptionalCutoff K S A X) ∧
      (Nat.card (exceptionalCutoff K S A X) : ℝ) ≤
        C * idealNorm K A ^ ε * X ^ (1 / 6 : ℝ) :=
  HeckeSkeleton.GramExceptionalCount.exceptional_frequency_count K S hε

-- OBLIGATION GR-08 | revised §3.5 dyadic display after (3.37), p.15.
-- Existing cache: ActualDyadicDoubleSum, static-reviewed, not imported here.
-- A=3>2, uniform also for 0<Λ<1; this is a NUMERICAL statement only.
theorem positive_dyadic_double_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ Λ : ℝ, 0 < Λ →
      Summable (fun ij : ℕ × ℕ =>
        (2 : ℝ) ^ (-(ij.1 + ij.2 : ℝ)) *
          min 1 (((2 : ℝ) ^ (ij.1 + ij.2) / Λ) ^ 3)) ∧
      (∑' ij : ℕ × ℕ,
        (2 : ℝ) ^ (-(ij.1 + ij.2 : ℝ)) *
          min 1 (((2 : ℝ) ^ (ij.1 + ij.2) / Λ) ^ 3)) ≤
        C * (1 + Real.log (2 + Λ)) / Λ :=
  HeckeSkeleton.GramDyadic.positive_dyadic_double_sum

-- OBLIGATION GR-09 | revised §3.5 ideal shells following (3.37), p.15.
-- Existing cache: actual ideal-shell reindex candidate, not a count hypothesis.
-- This and GR-08 are independent inputs of the coarse assembly; no
-- dependency between their admitted proofs is claimed.
-- Real ideals, not a replacement numerical lattice. The common Λ/4 slack
-- incurred on each norm shell must be handled inside this bridge.
theorem actual_ideal_double_shell :
    ∃ C : ℝ, 0 < C ∧ ∀ Λ : ℝ, 0 < Λ →
      Summable (fun IJ : NonzeroIdeal K × NonzeroIdeal K =>
        (idealNorm K IJ.1) ^ (-2 : ℝ) * (idealNorm K IJ.2) ^ (-2 : ℝ) *
          min 1 ((idealNorm K IJ.1 * idealNorm K IJ.2 / Λ) ^ 3)) ∧
      (∑' IJ : NonzeroIdeal K × NonzeroIdeal K,
        (idealNorm K IJ.1) ^ (-2 : ℝ) * (idealNorm K IJ.2) ^ (-2 : ℝ) *
          min 1 ((idealNorm K IJ.1 * idealNorm K IJ.2 / Λ) ^ 3)) ≤
        C * (1 + Real.log (2 + Λ)) / Λ :=
  HeckeSkeleton.GramIdealShell.actual_ideal_double_shell K

section Profiles
variable [MeasurableSpace (sLocalNormOneGroup K S)]
  [BorelSpace (sLocalNormOneGroup K S)]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

-- OBLIGATION GR-10 | revised §3.1 majorant / §3.5, pp.3–5,14–15.
-- Existing cache: ActualGramCompactShapeMajorant / RowBallOrbitalMajorant.
-- FREE tests allow zero; they are not the annular-away-from-zero P.additive.
-- No Haar covolume or Fourier-at-zero scalar is silently set to one.
theorem row_ball_majorant (B : ℝ) (hB : 0 < B) :
    ∃ (φ : SchwartzMap V ℂ)
      (ψ : ((v : S) → v.val.adicCompletion K) → ℂ) (c : ℝ),
      0 < c ∧ Continuous ψ ∧ HasCompactSupport ψ ∧
      (∀ x, (sLocalTensorTestFunction K S φ ψ x).im = 0 ∧
        0 ≤ (sLocalTensorTestFunction K S φ ψ x).re) ∧
      ∀ R : {r : ℝ // 0 < r}, R.val ≤ B →
        c ≤ (sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ) R).re :=
  HeckeSkeleton.GramRowBall.row_ball_majorant K S B hB

-- OBLIGATION GR-11 | revised §3.5 first shell / (3.37), p.15.
-- Existing SR26 / free-test generalization candidates: actual positive Mellin
-- moment -> FTC -> full log-axis point bound. A bare joint function of t+u
-- is NOT asserted to belong to L1(R²). The finite original seminorms and C
-- precede arbitrary φ and every radius, including R→0.
theorem small_radius_profile [IsTotallyComplex K]
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hcs : HasCompactSupport ψ)
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (J : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (φ : SchwartzMap V ℂ) (t : ℝ) (j : ℕ), j ≤ J →
        ‖iteratedDeriv j (fun v : ℝ =>
          sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
            ⟨Real.exp v, Real.exp_pos v⟩) t‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * Real.exp (-σ * t) :=
  HeckeSkeleton.GramSmallRadius.small_radius_profile K S ψ hψ hcs σ hσ hσ1 J

/-- Verified mainline large-radius bound. It retains its threshold R0 and
must NOT be used to prove GR-11 at small radii. -/
theorem large_radius_profile
    (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hcs : HasCompactSupport ψ)
    (A : Set (V × V)) (hA : IsCompact A)
    (hAΩ : A ⊆ Set.prod (traceArchRegular K) (traceArchRegular K))
    (B : ℝ) (M : ℕ)
    (hM : Module.finrank ℤ (traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)) < M)
    (hOrder : (Module.finrank ℚ K : ℝ) * B ≤ M) (J : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C R0 : ℝ, 0 ≤ C ∧ 1 ≤ R0 ∧
      ∀ (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}), R0 ≤ R.val →
      ∀ p ∈ A, ∀ n : ℕ, n ≤ J →
        ‖iteratedFDeriv ℝ n (traceJointOrbitalKernel K S φ ψ R) p‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-B) :=
  exists_traceJointOrbitalKernel_compact_power_bound K S Γ ψ hψ hcs
    A hA hAΩ B M hM hOrder J
end Profiles

-- OBLIGATION GR-12 | revised §3.5, pp.14–15; §6.5 (6.23), pp.40–41.
-- COARSE ASSEMBLY, NOT COMPLETED: exact free-majorant orbital PSF (both
-- zero terms, actual discriminant/covolume); finite gcd/Möbius reindex;
-- genuine-correlation -> chart only on coprime residuals; chosen-generator
-- ideal×unit enumeration; original-Γ choice mask on fixed depth 2H+J;
-- SAME d unit transport; nonexceptional mean-zero at the good exterior
-- prime; two-column Poisson min-saving; ordinary/exceptional shell sums.
-- Cache has concrete pieces for these arrows, but the exact full weighted
-- consumer is still missing. This one coarse obligation is intentionally
-- visible, and must be refined rather than counted as a proved assembly.
-- Exact leaf propositions are explicit parameters below and are applied
-- in the final theorem. No unused have is counted as a dependency.
theorem gram_assembly (P : ProbeData K S)
    (hallowed : AllowedGeneratorInput K S P.arithmetic)
    (hcal : ThetaCalibrationInput K S P.arithmetic P.Lambda P.G)
    (leaf01 : ∀ (P : ProbeData K S) (W : SmoothAnnularTest)
    (Y ν : ℝ) (hY : 0 < Y) (m : S.integer K),
      (Function.support (gramTerm K S P W Y ν m)).Finite)
    (leaf02 : ∀ (P : ProbeData K S) (W : SmoothAnnularTest)
    (Y ν : ℝ) (γ : sixthPowerUnits K S) (m : S.integer K),
      amplitude K S P W Y ν ((S.unitEquivUnitsInteger K γ.val).val * m) =
      amplitude K S P W Y ν m)
    (leaf03 : ∀ (P : ProbeData K S) (I J : ExteriorIdeal K S)
    (m : S.integer K),
      probeGauss K S P I (-m) * conj (probeGauss K S P J (-m)) =
      ∑' j : ThetaQuotient K S (exteriorMul K S I J),
        correlation K S P I J (Classical.choose (Ideal.Quotient.mk_surjective j)) *
          sLocalPrincipalPhase K S
            (((-m : S.integer K) : K) *
              ((Classical.choose (Ideal.Quotient.mk_surjective j) : S.integer K) : K) /
                ((P.arithmetic.generator I : K) * (P.arithmetic.generator J : K))))
    (leaf04 : ∀ (P : ProbeData K S) (I J : ExteriorIdeal K S),
      (I ≠ J → correlation K S P I J 0 = 0) ∧
    correlation K S P I I 0 = (Nat.card (ThetaQuotient K S I)ˣ : ℂ))
    (leaf05 : ∀ (P : ProbeData K S) (I : ExteriorIdeal K S)
    (hI : ∃ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val.val ∧
      ¬ 6 ∣ idealPrimeMultiplicity K p I.val.val),
      (∑' x : ThetaQuotient K S I, columnCharacter K S P I x) = 0)
    (leaf06 : ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 0 < X →
      Finite (ordinaryCutoff K S X) ∧
      (Nat.card (ordinaryCutoff K S X) : ℝ) ≤ C * X)
    (leaf07 : ∀ {ε : ℝ} (hε : 0 < ε),
      ∃ C : ℝ, 0 < C ∧ ∀ (A : NonzeroIdeal K) (X : ℝ), 0 < X →
      Finite (exceptionalCutoff K S A X) ∧
      (Nat.card (exceptionalCutoff K S A X) : ℝ) ≤
        C * idealNorm K A ^ ε * X ^ (1 / 6 : ℝ))
    (leaf08 : ∃ C : ℝ, 0 < C ∧ ∀ Λ : ℝ, 0 < Λ →
      Summable (fun ij : ℕ × ℕ =>
        (2 : ℝ) ^ (-(ij.1 + ij.2 : ℝ)) *
          min 1 (((2 : ℝ) ^ (ij.1 + ij.2) / Λ) ^ 3)) ∧
      (∑' ij : ℕ × ℕ,
        (2 : ℝ) ^ (-(ij.1 + ij.2 : ℝ)) *
          min 1 (((2 : ℝ) ^ (ij.1 + ij.2) / Λ) ^ 3)) ≤
        C * (1 + Real.log (2 + Λ)) / Λ)
    (leaf09 : ∃ C : ℝ, 0 < C ∧ ∀ Λ : ℝ, 0 < Λ →
      Summable (fun IJ : NonzeroIdeal K × NonzeroIdeal K =>
        (idealNorm K IJ.1) ^ (-2 : ℝ) * (idealNorm K IJ.2) ^ (-2 : ℝ) *
          min 1 ((idealNorm K IJ.1 * idealNorm K IJ.2 / Λ) ^ 3)) ∧
      (∑' IJ : NonzeroIdeal K × NonzeroIdeal K,
        (idealNorm K IJ.1) ^ (-2 : ℝ) * (idealNorm K IJ.2) ^ (-2 : ℝ) *
          min 1 ((idealNorm K IJ.1 * idealNorm K IJ.2 / Λ) ^ 3)) ≤
        C * (1 + Real.log (2 + Λ)) / Λ)
    (leaf10 : ∀ [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)] (B : ℝ) (hB : 0 < B),
      ∃ (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
      (ψ : ((v : S) → v.val.adicCompletion K) → ℂ) (c : ℝ),
      0 < c ∧ Continuous ψ ∧ HasCompactSupport ψ ∧
      (∀ x, (sLocalTensorTestFunction K S φ ψ x).im = 0 ∧
        0 ≤ (sLocalTensorTestFunction K S φ ψ x).re) ∧
      ∀ R : {r : ℝ // 0 < r}, R.val ≤ B →
        c ≤ (sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ) R).re)
    (leaf11 : ∀ [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)] [IsTotallyComplex K]
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hcs : HasCompactSupport ψ)
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (J : ℕ),
      ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ) (t : ℝ) (j : ℕ), j ≤ J →
        ‖iteratedDeriv j (fun v : ℝ =>
          sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
            ⟨Real.exp v, Real.exp_pos v⟩) t‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ (mixedEmbedding.euclidean.mixedSpace K) ℂ) φ * Real.exp (-σ * t)) :
    GramBound K S P := by
  sorry

/-- The final application explicitly supplies every mathematical leaf to
GR-12. The coarse assembly is itself admitted; no completed Gram proof is
claimed by this dependency skeleton. -/
theorem gramBound_of_calibrated (P : ProbeData K S)
    (hallowed : AllowedGeneratorInput K S P.arithmetic)
    (hcal : ThetaCalibrationInput K S P.arithmetic P.Lambda P.G) :
    GramBound K S P :=
  gram_assembly K S P hallowed hcal
    (amplitude_finite_support K S)
    (amplitude_sixth_unit K S)
    (complete_pair_fourier K S)
    (zero_frequency_diagonal K S)
    (residual_character_mean_zero K S)
    (ordinary_frequency_count K S)
    (@exceptional_frequency_count K _ _ S _)
    positive_dyadic_double_sum
    (actual_ideal_double_shell K)
    (@row_ball_majorant K _ _ S _)
    (@small_radius_profile K _ _ S _)

/-- Stable c=1 specialization for the actual physical denominator. Root's
Principal.low bridge may consume this without changing the arithmetic data. -/
theorem denominator_gram_bound (P : ProbeData K S)
    (hallowed : AllowedGeneratorInput K S P.arithmetic)
    (hcal : ThetaCalibrationInput K S P.arithmetic P.Lambda P.G) :
    ∀ (B L : ℝ), 0 < B → 0 < L →
      ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∃ C Z₀ : ℝ, 0 < C ∧ 1 ≤ Z₀ ∧
        ∀ (Z Q Y ν : ℝ), Z₀ ≤ Z → 1 ≤ Q → 1 ≤ Y →
          Q ≤ Z ^ L → Y ≤ Z ^ L → 1 ≤ Pa Q Y →
          rowEnergy K S P P.denominator.toSmoothAnnularTest B Q Y ν ≤
            C * (1 + |ν|) ^ J * gramScale Q Y * Z ^ ε :=
  gramBound_of_calibrated K S P hallowed hcal P.denominator.toSmoothAnnularTest

end HeckeSkeleton.Gram
