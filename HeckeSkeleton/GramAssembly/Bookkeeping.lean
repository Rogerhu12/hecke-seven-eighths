import ActualRowBallResidualScalarBound
import ActualRowBallResidualTrivialBound
import ActualRowBallDualResidualNorm
import ActualExceptionalWeightedShell
import ActualOrdinaryOrbitShellCount
import GeneratorMaskWitness
import HeckeSkeleton.GramAssembly.Dyadic

/-!
GR-12-ASSEMBLY, ideal and orbit bookkeeping: classification of a divisible
frequency into exceptional (with respect to `C`) or having a good prime, and
transfer of orbit counts from the frequency `j = g_C * k` to the quotient `k`.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.GramAssembly.Bookkeeping

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open AlgebraicNumberTheory.PowerResidueSymbols
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis HeckeGeneral.Bridge
open HeckeGeneral.Arithmetic.AllowedGeneratorSectionDraft
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.ActualGeneratorDivisionDraft
open HeckeGeneral.ThetaSkeleton.Global.ActualGcdMobiusDraft
open ActualProbeGaussFourierDraft ActualProbePairNormDraft ActualAdditiveGramDraft
open ActualGramJointChartDraft ActualGramJointChartCoverDraft
open ActualGramMajorantDraft ActualRowBallDualChartDraft
open ActualDenominatorGramWeightDraft ActualRowBallResidualAnalyticDraft
open ActualRowBallResidualMaskedDraft ActualAllowedTotalNormProviderDraft
open ActualChoiceMaskedTotalNormDraft ActualGeneratorChoiceDraft ActualGramJointMeanDraft
open HeckeGeneral.ThetaSkeleton.Physical.ActualRowBallResidualGoodPrimeDraft
open HeckeGeneral.ThetaSkeleton.Physical.ActualRowBallResidualScalarDraft
open HeckeGeneral.ThetaSkeleton.Physical.ActualRowBallDualResidualNormDraft
open HeckeGeneral.Analysis.ActualGramExceptionalCountDraft HeckeGeneral.Analysis.ActualSIntegerMoments
open scoped Classical BigOperators ContDiff nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (w : GeneratorMaskWitness K)
local notation "S" => (w.S : Set (HeightOneSpectrum (𝓞 K)))
local notation "E" => ExteriorIdeal K S
local notation "NZ" => NonzeroRingElements (Set.integer S K)
local notation "gen" => probeGenerator K S w.D

/-- The ideal of the generator of `C` is `C`. -/
theorem freq_gen (C : E) : actualFrequencyIdeal K S (gen C) = C.val.val :=
  probeGenerator_contraction K S w.D C

/-- The frequency ideal of `j = g_C * k` is `C` times that of `k`. -/
theorem freq_mul (C : E) (j : NZ) (hj : w.D.generator C ∣ j.val) :
    actualFrequencyIdeal K S j =
      C.val.val * actualFrequencyIdeal K S (thetaChartFrequencyQuotient K S w.D C j hj) := by
  have hfac := thetaChartFrequencyQuotient_factor K S w.D C j hj
  have hk := (thetaChartFrequencyQuotient K S w.D C j hj).property
  unfold actualFrequencyIdeal
  rw [← hfac, Arithmetic.sIntegerModulusContraction_mul K S _ _ (w.D.generator_ne_zero C) hk]
  rw [← freq_gen K w C]
  rfl

/-- The classification of a quotient frequency `k` relative to `C`: either it is
exceptional (all multiplicities outside `C` divisible by six), or a good prime
with multiplicity not divisible by six exists. -/
theorem exceptional_or_goodPrime (C : E) (k : NZ) :
    ExceptionalSixthIdeal K C.val (actualSIntegerOrbitIdeal K S (Quotient.mk _ k)) ∨
      ∃ p : jointPlaces K (actualFrequencyIdeal K S (gen C)) (actualFrequencyIdeal K S k)
        (actualFrequencyIdeal_ne_zero K S (gen C)) (actualFrequencyIdeal_ne_zero K S k),
      (¬ p.val.asIdeal ∣ actualFrequencyIdeal K S (gen C)) ∧
      (¬ 6 ∣ idealPrimeMultiplicity K p.val (actualFrequencyIdeal K S k)) := by
  by_cases h : ExceptionalSixthIdeal K C.val (actualSIntegerOrbitIdeal K S (Quotient.mk _ k))
  · exact Or.inl h
  · right
    unfold ExceptionalSixthIdeal at h
    push_neg at h
    obtain ⟨p, hpC, hp6⟩ := h
    have hkne := actualFrequencyIdeal_ne_zero K S k
    have hexp : primeExponents (actualSIntegerOrbitIdeal K S (Quotient.mk _ k)) p =
        idealPrimeMultiplicity K p (actualFrequencyIdeal K S k) :=
      (idealPrimeMultiplicity_eq_primeExponents K _ hkne p).symm
    rw [hexp] at hp6
    have hmem : p ∈ sexticIdealPlaces K (actualFrequencyIdeal K S k) hkne := by
      rw [Finsupp.mem_support_iff, sexticIdealPrimeExponents_apply]
      intro h0
      exact hp6 (by rw [h0]; exact dvd_zero 6)
    have hnd : ¬ p.asIdeal ∣ actualFrequencyIdeal K S (gen C) := by
      intro hdvd
      rw [freq_gen K w C] at hdvd
      exact hpC ((SquarefreeAmplification.mem_idealPrimeSupport_iff K C.val p).mpr hdvd)
    exact ⟨⟨p, Finset.mem_union_right _ hmem⟩, hnd, hp6⟩


-- Orbits of the original sixth-power S-unit quotient.
local notation "Orb" => SIntegerOrbits K S (sixthPowerUnits K S)

variable [MeasurableSpace (sLocalNormOneGroup K (w.S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (w.S : Set (HeightOneSpectrum (𝓞 K))))]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (μf : Measure (FiniteAdeleRing (𝓞 K) K)) [μf.IsAddHaarMeasure]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
variable [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
variable [∀ v, (μv v).IsAddHaarMeasure]

/-- Exceptional frequencies divisible by `g_C` inject, via the quotient frequency
`k = j / g_C`, into the exceptional orbit cutoff of the quotient. -/
theorem exc_count (P : ProbeData K S) (C : E) (T : ℝ) (hT : 0 < T) (G : Finset Orb)
    (hG : ∀ q ∈ G, ∃ hj : w.D.generator C ∣ q.out.val,
      ExceptionalSixthIdeal K C.val (actualSIntegerOrbitIdeal K S
        (Quotient.mk _ (thetaChartFrequencyQuotient K S w.D C q.out hj))) ∧
      (sIntegerOrbitNorm K S (sixthPowerUnits K S) q).val ≤ T) :
    (G.card : ℝ) ≤
      Nat.card (ActualExceptionalOrbitCutoff K S C.val (T / exteriorNorm K S C)) := by
  have hCpos : 0 < exteriorNorm K S C := by
    have := idealNorm_pos K C.val
    simpa [exteriorNorm, idealNorm] using this
  have hX : 0 ≤ T / exteriorNorm K S C := div_nonneg hT.le hCpos.le
  haveI := finite_actualExceptionalOrbitCutoff K S P C.val hX
  choose hj hAB using fun q : G => hG q.1 q.2
  let kq : G → NZ := fun q => thetaChartFrequencyQuotient K S w.D C q.1.out (hj q)
  have hfac : ∀ q : G, w.D.generator C * (kq q).val = q.1.out.val := fun q =>
    thetaChartFrequencyQuotient_factor K S w.D C q.1.out (hj q)
  have hnorm : ∀ q : G, (sIntegerElementNorm K S (kq q)).val ≤ T / exteriorNorm K S C := by
    intro q
    have h1 := residualFrequency_elementNorm_factor K w C q.1.out (hj q)
    rw [sIntegerOrbitNorm_out] at h1
    rw [le_div_iff₀ hCpos, mul_comm]
    exact h1.le.trans (hAB q).2
  let f : G → ActualExceptionalOrbitCutoff K S C.val (T / exteriorNorm K S C) := fun q =>
    ⟨Quotient.mk _ (kq q), by
      rw [actualSIntegerOrbitNorm_mk]
      exact hnorm q, (hAB q).1⟩
  have hinj : Function.Injective f := by
    intro q q' h
    have hk : (Quotient.mk _ (kq q) : SIntegerOrbits K S (sixthPowerUnits K S)) =
        Quotient.mk _ (kq q') := congrArg Subtype.val h
    have hq : ∀ r : G, r.1 = sIntegerOrbitDilation K S (sixthPowerUnits K S) (gen C)
        (Quotient.mk _ (kq r)) := by
      intro r
      rw [sIntegerOrbitDilation_mk]
      have : sIntegerNonzeroMul K S (gen C) (kq r) = r.1.out :=
        Subtype.ext (hfac r)
      rw [this, Quotient.out_eq]
    apply Subtype.ext
    rw [hq q, hq q', hk]
  have hfin : Finite (ActualExceptionalOrbitCutoff K S C.val (T / exteriorNorm K S C)) := inferInstance
  have hcard := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at hcard
  exact_mod_cast hcard



variable (P : ProbeData K (w.S : Set (HeightOneSpectrum (𝓞 K))))

/-- The good-prime scalar bound (`σ = 1/12`, `β = 5`, `A = 3`), as produced by
`exists_rowBallResidual_goodPrime_scalar_bound`. -/
abbrev GoodScalar (B : ℝ) (J : ℕ) : Prop :=
  ∀ (C D : E) (j : NZ) (hj : w.D.generator C ∣ j.val),
    let k := thetaChartFrequencyQuotient K S w.D C j hj
    ∀ p : jointPlaces K (actualFrequencyIdeal K S (gen C)) (actualFrequencyIdeal K S k)
      (actualFrequencyIdeal_ne_zero K S (gen C)) (actualFrequencyIdeal_ne_zero K S k),
    (¬ p.val.asIdeal ∣ actualFrequencyIdeal K S (gen C)) →
    (¬ 6 ∣ idealPrimeMultiplicity K p.val (actualFrequencyIdeal K S k)) →
    ∀ (Y η : ℝ) (_ : 0 < Y) (r : {r : ℝ // 0 < r}),
    let q := Y / (exteriorNorm K S C * exteriorNorm K S D)
    let qj := (sIntegerElementNorm K S j).val
    ‖rowBallResidualSum K w μv P Y η r C D j‖ ≤
      B * (1 + |η|) ^ J *
        min ((qj / (r.val * Y ^ 2)) ^ (-(1 / 12 : ℝ))) ((qj / (r.val * Y ^ 2)) ^ (-(5 : ℝ))) *
        exteriorNorm K S C * q ^ 2 * min 1 ((qj / q) ^ 3)

/-- The trivial scalar bound, as produced by
`exists_rowBallResidual_trivial_scalar_bound`. -/
abbrev TrivScalar (B : ℝ) (J : ℕ) : Prop :=
  ∀ (C D : E) (j : NZ) (_ : w.D.generator C ∣ j.val),
    ∀ (Y η : ℝ) (_ : 0 < Y) (r : {r : ℝ // 0 < r}),
    let q := Y / (exteriorNorm K S C * exteriorNorm K S D)
    let qj := (sIntegerElementNorm K S j).val
    ‖rowBallResidualSum K w μv P Y η r C D j‖ ≤
      B * (1 + |η|) ^ J *
        min ((qj / (r.val * Y ^ 2)) ^ (-(1 / 12 : ℝ))) ((qj / (r.val * Y ^ 2)) ^ (-(5 : ℝ))) *
        exteriorNorm K S C * q ^ 2

/-- Pointwise residual bound for one orbit, one `C` and one `D`. -/
theorem res_le (hP : P.arithmetic = w.D) (Bg Bt K1 : ℝ) (Jg Jt J : ℕ)
    (hgood : GoodScalar K w μv P Bg Jg) (htriv : TrivScalar K w μv P Bt Jt)
    (hBg : 0 ≤ Bg) (hBt : 0 ≤ Bt) (hg : Bg ≤ K1) (ht : Bt ≤ K1) (hJg : Jg ≤ J) (hJt : Jt ≤ J)
    (C D : E) (Y η : ℝ) (hY : 0 < Y) (r : {r : ℝ // 0 < r}) (q : Orb) :
    ‖rowBallResidualSum K w μv P Y η r C D q.out‖ ≤
      (if ∃ hj : w.D.generator C ∣ q.out.val,
          ExceptionalSixthIdeal K C.val (actualSIntegerOrbitIdeal K S
            (Quotient.mk _ (thetaChartFrequencyQuotient K S w.D C q.out hj)))
        then K1 * (1 + |η|) ^ J * Dyadic.mfun (r.val * Y ^ 2)
            (sIntegerOrbitNorm K S (sixthPowerUnits K S) q).val *
          exteriorNorm K S C * (Y / (exteriorNorm K S C * exteriorNorm K S D)) ^ 2 else 0) +
      (if w.D.generator C ∣ q.out.val
        then K1 * (1 + |η|) ^ J * Dyadic.mfun (r.val * Y ^ 2)
            (sIntegerOrbitNorm K S (sixthPowerUnits K S) q).val *
          exteriorNorm K S C * (Y / (exteriorNorm K S C * exteriorNorm K S D)) ^ 2 *
          min 1 (((sIntegerOrbitNorm K S (sixthPowerUnits K S) q).val /
            (Y / (exteriorNorm K S C * exteriorNorm K S D))) ^ 3) else 0) := by
  have hn0 : 0 < (sIntegerOrbitNorm K S (sixthPowerUnits K S) q).val :=
    (sIntegerOrbitNorm K S (sixthPowerUnits K S) q).property
  have ha0 : 0 < r.val * Y ^ 2 := mul_pos r.property (pow_pos hY 2)
  have hC0 : 0 < exteriorNorm K S C := by
    have := idealNorm_pos K C.val
    simpa [exteriorNorm, idealNorm] using this
  have hD0 : 0 < exteriorNorm K S D := by
    have := idealNorm_pos K D.val
    simpa [exteriorNorm, idealNorm] using this
  have hK1 : 0 ≤ K1 := hBg.trans hg
  have hm0 := Dyadic.mfun_nonneg (r.val * Y ^ 2)
    (sIntegerOrbitNorm K S (sixthPowerUnits K S) q).val ha0 hn0
  have hNpos : 0 < Y / (exteriorNorm K S C * exteriorNorm K S D) := by positivity
  have hη : 1 ≤ 1 + |η| := by linarith [abs_nonneg η]
  set n : ℝ := (sIntegerOrbitNorm K S (sixthPowerUnits K S) q).val with hn
  set a : ℝ := r.val * Y ^ 2 with ha
  set Nn : ℝ := Y / (exteriorNorm K S C * exteriorNorm K S D) with hNn
  set qC : ℝ := exteriorNorm K S C with hqC
  have hmf : Dyadic.mfun a n = min ((n / a) ^ (-(1 / 12 : ℝ))) ((n / a) ^ (-(5 : ℝ))) := rfl
  have hu0 : 0 ≤ K1 * (1 + |η|) ^ J * Dyadic.mfun a n * qC * Nn ^ 2 := by positivity
  have hg0 : 0 ≤ min 1 ((n / Nn) ^ 3) :=
    le_min zero_le_one (pow_nonneg (div_nonneg hn0.le hNpos.le) 3)
  by_cases hd : w.D.generator C ∣ q.out.val
  · rw [if_pos hd]
    have hqj : (sIntegerElementNorm K S q.out).val = n := by
      rw [sIntegerOrbitNorm_out]
    rcases exceptional_or_goodPrime K w C
        (thetaChartFrequencyQuotient K S w.D C q.out hd) with hexc | ⟨p, hpC, hpJ⟩
    · have hcond : ∃ hj : w.D.generator C ∣ q.out.val,
          ExceptionalSixthIdeal K C.val (actualSIntegerOrbitIdeal K S
            (Quotient.mk _ (thetaChartFrequencyQuotient K S w.D C q.out hj))) := ⟨hd, hexc⟩
      rw [if_pos hcond]
      have h := htriv C D q.out hd Y η hY r
      simp only [hqj] at h
      have hpow : (1 + |η|) ^ Jt ≤ (1 + |η|) ^ J := pow_le_pow_right₀ hη hJt
      have hBt' : Bt * (1 + |η|) ^ Jt ≤ K1 * (1 + |η|) ^ J :=
        mul_le_mul ht hpow (by positivity) hK1
      have hrest : 0 ≤ Dyadic.mfun a n * qC * Nn ^ 2 := by positivity
      have hle : ‖rowBallResidualSum K w μv P Y η r C D q.out‖ ≤
          K1 * (1 + |η|) ^ J * Dyadic.mfun a n * qC * Nn ^ 2 := by
        refine h.trans ?_
        rw [hmf] at hrest ⊢
        calc _ = (Bt * (1 + |η|) ^ Jt) * (min ((n / a) ^ (-(1 / 12 : ℝ))) ((n / a) ^ (-(5 : ℝ))) *
                qC * Nn ^ 2) := by ring
          _ ≤ (K1 * (1 + |η|) ^ J) * (min ((n / a) ^ (-(1 / 12 : ℝ))) ((n / a) ^ (-(5 : ℝ))) *
                qC * Nn ^ 2) := mul_le_mul_of_nonneg_right hBt' hrest
          _ = _ := by ring
      have h2 : 0 ≤ K1 * (1 + |η|) ^ J * Dyadic.mfun a n * qC * Nn ^ 2 *
          min 1 ((n / Nn) ^ 3) := mul_nonneg hu0 hg0
      linarith
    · have hcond0 : 0 ≤ (if ∃ hj : w.D.generator C ∣ q.out.val,
          ExceptionalSixthIdeal K C.val (actualSIntegerOrbitIdeal K S
            (Quotient.mk _ (thetaChartFrequencyQuotient K S w.D C q.out hj)))
        then K1 * (1 + |η|) ^ J * Dyadic.mfun a n * qC * Nn ^ 2 else 0) := by
        split_ifs
        · exact hu0
        · exact le_rfl
      have h := hgood C D q.out hd p hpC hpJ Y η hY r
      simp only [hqj] at h
      have hpow : (1 + |η|) ^ Jg ≤ (1 + |η|) ^ J := pow_le_pow_right₀ hη hJg
      have hBg' : Bg * (1 + |η|) ^ Jg ≤ K1 * (1 + |η|) ^ J :=
        mul_le_mul hg hpow (by positivity) hK1
      have hrest : 0 ≤ Dyadic.mfun a n * qC * Nn ^ 2 * min 1 ((n / Nn) ^ 3) :=
        mul_nonneg (by positivity) hg0
      have hle : ‖rowBallResidualSum K w μv P Y η r C D q.out‖ ≤
          K1 * (1 + |η|) ^ J * Dyadic.mfun a n * qC * Nn ^ 2 * min 1 ((n / Nn) ^ 3) := by
        refine h.trans ?_
        rw [hmf] at hrest ⊢
        calc _ = (Bg * (1 + |η|) ^ Jg) * (min ((n / a) ^ (-(1 / 12 : ℝ))) ((n / a) ^ (-(5 : ℝ))) *
                qC * Nn ^ 2 * min 1 ((n / Nn) ^ 3)) := by ring
          _ ≤ (K1 * (1 + |η|) ^ J) * (min ((n / a) ^ (-(1 / 12 : ℝ))) ((n / a) ^ (-(5 : ℝ))) *
                qC * Nn ^ 2 * min 1 ((n / Nn) ^ 3)) := mul_le_mul_of_nonneg_right hBg' hrest
          _ = _ := by ring
      linarith
  · have hcond : ¬ ∃ hj : w.D.generator C ∣ q.out.val,
        ExceptionalSixthIdeal K C.val (actualSIntegerOrbitIdeal K S
          (Quotient.mk _ (thetaChartFrequencyQuotient K S w.D C q.out hj))) :=
      fun ⟨hj, _⟩ => hd hj
    rw [if_neg hcond, if_neg hd, add_zero,
      rowBallResidualSum_eq_zero_of_not_dvd K w μv P hP Y η r C D q.out hd]
    simp


/-- The per-`(C, D)` shell bound for a finite set `F` of frequency orbits: the
exceptional part is counted through the quotient orbits, the ordinary part
through the divisible orbit count. -/
theorem perCD_sum (hP : P.arithmetic = w.D) (Bg Bt K1 : ℝ) (Jg Jt J : ℕ)
    (hgood : GoodScalar K w μv P Bg Jg) (htriv : TrivScalar K w μv P Bt Jt)
    (hBg : 0 ≤ Bg) (hBt : 0 ≤ Bt) (hg : Bg ≤ K1) (ht : Bt ≤ K1) (hJg : Jg ≤ J) (hJt : Jt ≤ J)
    (c0 : ℝ)
    (hdiv : ∀ (C : E) (T : ℝ), 0 < T → ∀ G : Finset Orb,
      (∀ q ∈ G, w.D.generator C ∣ q.out.val ∧
        (sIntegerOrbitNorm K S (sixthPowerUnits K S) q).val ≤ T) →
      (G.card : ℝ) ≤ c0 * T / exteriorNorm K S C)
    (C D : E) (Y η : ℝ) (hY : 0 < Y) (r : {r : ℝ // 0 < r}) (F : Finset Orb) (M : ℕ)
    (hM : ∀ q ∈ F, Dyadic.shellIndex (sIntegerOrbitNorm K S (sixthPowerUnits K S) q).val < M) :
    ∑ q ∈ F, ‖rowBallResidualSum K w μv P Y η r C D q.out‖ ≤
      (K1 * (1 + |η|) ^ J * exteriorNorm K S C *
          (Y / (exteriorNorm K S C * exteriorNorm K S D)) ^ 2) *
        (∑ k ∈ Finset.range M,
          (Nat.card (ActualExceptionalOrbitCutoff K S C.val ((2 : ℝ) ^ k / exteriorNorm K S C)) : ℝ) *
            Dyadic.mfun (r.val * Y ^ 2) ((2 : ℝ) ^ k / 2) +
         ∑ k ∈ Finset.range M,
          (c0 * (2 : ℝ) ^ k / exteriorNorm K S C) *
            (Dyadic.mfun (r.val * Y ^ 2) ((2 : ℝ) ^ k / 2) *
              min 1 (((2 : ℝ) ^ k / (Y / (exteriorNorm K S C * exteriorNorm K S D))) ^ 3))) := by
  set a : ℝ := r.val * Y ^ 2 with ha
  set Nn : ℝ := Y / (exteriorNorm K S C * exteriorNorm K S D) with hNn
  set qC : ℝ := exteriorNorm K S C with hqC
  set u0 : ℝ := K1 * (1 + |η|) ^ J with hu0
  have ha0 : 0 < a := mul_pos r.property (pow_pos hY 2)
  have hC0 : 0 < qC := by
    have := idealNorm_pos K C.val
    simpa [hqC, exteriorNorm, idealNorm] using this
  have hD0 : 0 < exteriorNorm K S D := by
    have := idealNorm_pos K D.val
    simpa [exteriorNorm, idealNorm] using this
  have hNpos : 0 < Nn := by positivity
  have hK1 : 0 ≤ K1 := hBg.trans hg
  have hu00 : 0 ≤ u0 := by positivity
  have hn1 : ∀ q : Orb, 1 ≤ (sIntegerOrbitNorm K S (sixthPowerUnits K S) q).val := fun q =>
    one_le_actualSIntegerOrbitNorm K S q
  -- pointwise reduction to two filtered sums
  have hpt : ∑ q ∈ F, ‖rowBallResidualSum K w μv P Y η r C D q.out‖ ≤
      ∑ q ∈ F, ((if ∃ hj : w.D.generator C ∣ q.out.val,
          ExceptionalSixthIdeal K C.val (actualSIntegerOrbitIdeal K S
            (Quotient.mk _ (thetaChartFrequencyQuotient K S w.D C q.out hj)))
        then u0 * Dyadic.mfun a (sIntegerOrbitNorm K S (sixthPowerUnits K S) q).val *
          qC * Nn ^ 2 else 0) +
      (if w.D.generator C ∣ q.out.val
        then u0 * Dyadic.mfun a (sIntegerOrbitNorm K S (sixthPowerUnits K S) q).val *
          qC * Nn ^ 2 *
          min 1 (((sIntegerOrbitNorm K S (sixthPowerUnits K S) q).val / Nn) ^ 3) else 0)) :=
    Finset.sum_le_sum (fun q _ => res_le K w μv P hP Bg Bt K1 Jg Jt J hgood htriv hBg hBt hg ht
      hJg hJt C D Y η hY r q)
  refine hpt.trans ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
  -- exceptional part
  have hexc : ∑ q ∈ F.filter (fun q => ∃ hj : w.D.generator C ∣ q.out.val,
        ExceptionalSixthIdeal K C.val (actualSIntegerOrbitIdeal K S
          (Quotient.mk _ (thetaChartFrequencyQuotient K S w.D C q.out hj)))),
      u0 * Dyadic.mfun a (sIntegerOrbitNorm K S (sixthPowerUnits K S) q).val * qC * Nn ^ 2 ≤
      (u0 * qC * Nn ^ 2) * ∑ k ∈ Finset.range M,
        (Nat.card (ActualExceptionalOrbitCutoff K S C.val ((2 : ℝ) ^ k / qC)) : ℝ) *
          Dyadic.mfun a ((2 : ℝ) ^ k / 2) := by
    have hsh := Dyadic.shell_sum_le
      (F.filter (fun q => ∃ hj : w.D.generator C ∣ q.out.val,
        ExceptionalSixthIdeal K C.val (actualSIntegerOrbitIdeal K S
          (Quotient.mk _ (thetaChartFrequencyQuotient K S w.D C q.out hj)))))
      (fun q => (sIntegerOrbitNorm K S (sixthPowerUnits K S) q).val)
      (fun q _ => hn1 q) (Dyadic.mfun a)
      (fun k => (Nat.card (ActualExceptionalOrbitCutoff K S C.val ((2 : ℝ) ^ k / qC)) : ℝ))
      (fun k => Dyadic.mfun a ((2 : ℝ) ^ k / 2))
      (fun k G hGF hGn => by
        apply exc_count K w P C ((2 : ℝ) ^ k) (by positivity) G
        intro q hq
        have := Finset.mem_filter.mp (hGF hq)
        exact ⟨this.2.choose, this.2.choose_spec, hGn q hq⟩)
      (fun k x hx1 hx2 hx3 => Dyadic.mfun_antitone a ha0 (by positivity) hx2.le)
      (fun k => Dyadic.mfun_nonneg a _ ha0 (by positivity)) M
      (fun q hq => hM q (Finset.mem_filter.mp hq).1)
    calc _ = (u0 * qC * Nn ^ 2) * ∑ q ∈ F.filter (fun q => ∃ hj : w.D.generator C ∣ q.out.val,
        ExceptionalSixthIdeal K C.val (actualSIntegerOrbitIdeal K S
          (Quotient.mk _ (thetaChartFrequencyQuotient K S w.D C q.out hj)))),
        Dyadic.mfun a (sIntegerOrbitNorm K S (sixthPowerUnits K S) q).val := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro q _; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsh (by positivity)
  -- ordinary part
  have hord : ∑ q ∈ F.filter (fun q => w.D.generator C ∣ q.out.val),
      u0 * Dyadic.mfun a (sIntegerOrbitNorm K S (sixthPowerUnits K S) q).val * qC * Nn ^ 2 *
        min 1 (((sIntegerOrbitNorm K S (sixthPowerUnits K S) q).val / Nn) ^ 3) ≤
      (u0 * qC * Nn ^ 2) * ∑ k ∈ Finset.range M,
        (c0 * (2 : ℝ) ^ k / qC) *
          (Dyadic.mfun a ((2 : ℝ) ^ k / 2) * min 1 (((2 : ℝ) ^ k / Nn) ^ 3)) := by
    have hsh := Dyadic.shell_sum_le
      (F.filter (fun q => w.D.generator C ∣ q.out.val))
      (fun q => (sIntegerOrbitNorm K S (sixthPowerUnits K S) q).val)
      (fun q _ => hn1 q) (fun x => Dyadic.mfun a x * min 1 ((x / Nn) ^ 3))
      (fun k => c0 * (2 : ℝ) ^ k / qC)
      (fun k => Dyadic.mfun a ((2 : ℝ) ^ k / 2) * min 1 (((2 : ℝ) ^ k / Nn) ^ 3))
      (fun k G hGF hGn => by
        apply hdiv C _ (by positivity) G
        intro q hq
        exact ⟨(Finset.mem_filter.mp (hGF hq)).2, hGn q hq⟩)
      (fun k x hx1 hx2 hx3 => by
        apply mul_le_mul (Dyadic.mfun_antitone a ha0 (by positivity) hx2.le)
        · apply min_le_min le_rfl
          exact pow_le_pow_left₀ (div_nonneg (by linarith) hNpos.le)
            (div_le_div_of_nonneg_right hx3 hNpos.le) 3
        · exact le_min zero_le_one (pow_nonneg (div_nonneg (by linarith) hNpos.le) 3)
        · exact Dyadic.mfun_nonneg a _ ha0 (by positivity))
      (fun k => mul_nonneg (Dyadic.mfun_nonneg a _ ha0 (by positivity))
        (le_min zero_le_one (pow_nonneg (div_nonneg (by positivity) hNpos.le) 3))) M
      (fun q hq => hM q (Finset.mem_filter.mp hq).1)
    calc _ = (u0 * qC * Nn ^ 2) * ∑ q ∈ F.filter (fun q => w.D.generator C ∣ q.out.val),
        (Dyadic.mfun a (sIntegerOrbitNorm K S (sixthPowerUnits K S) q).val *
          min 1 (((sIntegerOrbitNorm K S (sixthPowerUnits K S) q).val / Nn) ^ 3)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro q _; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsh (by positivity)
  calc _ ≤ (u0 * qC * Nn ^ 2) * ∑ k ∈ Finset.range M,
        (Nat.card (ActualExceptionalOrbitCutoff K S C.val ((2 : ℝ) ^ k / qC)) : ℝ) *
          Dyadic.mfun a ((2 : ℝ) ^ k / 2) + (u0 * qC * Nn ^ 2) * ∑ k ∈ Finset.range M,
        (c0 * (2 : ℝ) ^ k / qC) *
          (Dyadic.mfun a ((2 : ℝ) ^ k / 2) * min 1 (((2 : ℝ) ^ k / Nn) ^ 3)) := add_le_add hexc hord
    _ = _ := by rw [← mul_add]


/-- The residual majorant of one frequency orbit: the sum over the actual gcd
parts `C` and Mobius divisors `D` of the norms of the finite residual sums. -/
def residualMajorant (Y η : ℝ) (r : {r : ℝ // 0 < r}) (q : Orb) : ℝ :=
  let rows := additiveGramIdealSupport K S P.denominator.toSmoothAnnularTest Y
  ∑ C ∈ finiteCommonParts K S rows rows,
    ∑ D ∈ residualMobiusDivisorSet K w C rows rows,
      ‖rowBallResidualSum K w μv P Y η r C D q.out‖

end HeckeSkeleton.GramAssembly.Bookkeeping
