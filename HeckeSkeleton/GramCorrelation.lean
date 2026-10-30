import HeckeSkeleton.GramDefinitions
import ActualProbeGaussOriginalFourier
import ActualSexticZeroFrequencyDiagonal

/-!
# The literal Gram correlation and the original full correlation (GR-03, GR-04)

The skeleton's `correlation` is the literal two-column congruence sum over chosen
representatives. It equals the original full correlation of the natively verified
Gram core (`GramCoreInputs`) for the two actual generators. The core's
zero-frequency diagonal and its finite Fourier identity then give GR-04 and GR-03.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.GramCorrelation

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.Arithmetic.PeriodicFourier
open HeckeGeneral.ThetaSkeleton.Physical.ActualProbeGaussFourierDraft
open HeckeSkeleton.Gram
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local notation "R" => S.integer K

/-- The same finite residue columns as the core's local instances. -/
local instance gramColumnFinite (u : NonzeroRingElements R) :
    Finite (R ⧸ commonFactorColumnIdeal (⊤ : Ideal R) u.val) := by
  change Finite (R ⧸ ((⊤ : Ideal R) * Ideal.span ({u.val} : Set R)))
  rw [Ideal.top_mul]
  exact finite_sIntegerPrincipalResidue K S u.val u.property

local instance gramColumnFintype (u : NonzeroRingElements R) :
    Fintype (R ⧸ commonFactorColumnIdeal (⊤ : Ideal R) u.val) := Fintype.ofFinite _

local instance gramTotalFinite (u v : NonzeroRingElements R) :
    Finite (R ⧸ commonFactorTotalIdeal (⊤ : Ideal R) u.val v.val) := by
  have : Finite (R ⧸ Ideal.span ({u.val * v.val} : Set R)) :=
    finite_sIntegerPrincipalResidue K S _ (mul_ne_zero u.property v.property)
  exact Finite.of_equiv _ (originalFullTotalPrincipalEquiv K S u v).symm.toEquiv

local instance gramTotalFintype (u v : NonzeroRingElements R) :
    Fintype (R ⧸ commonFactorTotalIdeal (⊤ : Ideal R) u.val v.val) := Fintype.ofFinite _

local instance gramThetaFinite (I : ExteriorIdeal K S) : Finite (ThetaQuotient K S I) :=
  finite_sIntegerSexticIdealQuotient K S I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property

local instance gramThetaFintype (I : ExteriorIdeal K S) : Fintype (ThetaQuotient K S I) :=
  Fintype.ofFinite _

omit [Fintype S] in
/-- The total modulus of the two actual generators is the extended product ideal. -/
theorem totalIdeal_eq (D : ThetaArithmeticData K S) (I J : ExteriorIdeal K S) :
    commonFactorTotalIdeal (⊤ : Ideal R) (probeGenerator K S D I).val
        (probeGenerator K S D J).val =
      (exteriorMul K S I J).val.val.map (algebraMap (𝓞 K) R) := by
  have h : (exteriorMul K S I J).val.val = I.val.val * J.val.val := rfl
  rw [h, Ideal.map_mul, ← D.generator_span I, ← D.generator_span J]
  simp only [commonFactorTotalIdeal, probeGenerator, Ideal.top_mul]

/-- A residue column is the class of the chosen representative of its image. -/
theorem column_eq_mk_choose (D : ThetaArithmeticData K S) (I : ExteriorIdeal K S)
    (x : R ⧸ commonFactorColumnIdeal (⊤ : Ideal R) (probeGenerator K S D I).val) :
    x = Ideal.Quotient.mk _ (Classical.choose
      (Ideal.Quotient.mk_surjective (probeGeneratorColumnEquiv K S D I x))) := by
  apply (probeGeneratorColumnEquiv K S D I).injective
  rw [probeGeneratorColumnEquiv_mk]
  exact (Classical.choose_spec (Ideal.Quotient.mk_surjective _)).symm

/-- The skeleton correlation is the original full correlation of the two actual
generators, at every frequency. -/
theorem correlation_eq_originalFull (P : ProbeData K S) (I J : ExteriorIdeal K S) (j : R) :
    HeckeSkeleton.Gram.correlation K S P I J j =
      sIntegerSexticOriginalFullCorrelation K S P.arithmetic.root6 P.arithmetic.primitive6
        P.arithmetic.embedding (probeArithmetic_six_support K S P.arithmetic)
        (probeGenerator K S P.arithmetic I) (probeGenerator K S P.arithmetic J) j := by
  rw [← sIntegerSexticOriginalFullQuotientCorrelation_mk]
  unfold sIntegerSexticOriginalFullQuotientCorrelation mixedCorrelation HeckeSkeleton.Gram.correlation
  rw [Fintype.sum_prod_type]
  symm
  refine Fintype.sum_equiv (probeGeneratorColumnEquiv K S P.arithmetic I).toEquiv _ _
    (fun x => ?_)
  refine Fintype.sum_equiv (probeGeneratorColumnEquiv K S P.arithmetic J).toEquiv _ _
    (fun y => ?_)
  have hx := column_eq_mk_choose K S P.arithmetic I x
  have hy := column_eq_mk_choose K S P.arithmetic J y
  have hiff :
      (commonFactorFirstMultiplier (⊤ : Ideal R) (probeGenerator K S P.arithmetic I).val
          (probeGenerator K S P.arithmetic J).val x -
        commonFactorSecondMultiplier (⊤ : Ideal R) (probeGenerator K S P.arithmetic I).val
          (probeGenerator K S P.arithmetic J).val y = Ideal.Quotient.mk _ j) ↔
      (P.arithmetic.generator J *
            Classical.choose (Ideal.Quotient.mk_surjective
              ((probeGeneratorColumnEquiv K S P.arithmetic I).toEquiv x)) -
          P.arithmetic.generator I *
            Classical.choose (Ideal.Quotient.mk_surjective
              ((probeGeneratorColumnEquiv K S P.arithmetic J).toEquiv y)) - j ∈
        (exteriorMul K S I J).val.val.map (algebraMap (𝓞 K) R)) := by
    conv_lhs => rw [hx, hy]
    rw [commonFactorFullFibre_relation_mk_iff, totalIdeal_eq]
    rfl
  have hcI := probeQuotientFunction_eq_originalColumnWeight K S P.arithmetic I x
  have hcJ := probeQuotientFunction_eq_originalColumnWeight K S P.arithmetic J y
  simp only [hiff]
  unfold HeckeSkeleton.Gram.columnCharacter
  change _ = (if _ then
      sIntegerSexticIdealQuotientFunction K S P.arithmetic.root6 P.arithmetic.primitive6
        P.arithmetic.embedding I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
        (fun p hp => P.arithmetic.away_six p (I.property p hp))
        (probeGeneratorColumnEquiv K S P.arithmetic I x) *
      conj (sIntegerSexticIdealQuotientFunction K S P.arithmetic.root6 P.arithmetic.primitive6
        P.arithmetic.embedding J.val.val (nonZeroDivisors.coe_ne_zero J.val) J.property
        (fun p hp => P.arithmetic.away_six p (J.property p hp))
        (probeGeneratorColumnEquiv K S P.arithmetic J y)) else 0)
  rw [hcI, hcJ]

/-- GR-04 in the form stated in `HeckeSkeleton.Gram`. -/
theorem zero_frequency_diagonal (P : ProbeData K S) (I J : ExteriorIdeal K S) :
    (I ≠ J → HeckeSkeleton.Gram.correlation K S P I J 0 = 0) ∧
    HeckeSkeleton.Gram.correlation K S P I I 0 = (Nat.card (ThetaQuotient K S I)ˣ : ℂ) := by
  refine ⟨fun hIJ => ?_, ?_⟩
  · rw [correlation_eq_originalFull]
    apply sIntegerSexticOriginalFullCorrelation_zero_of_contraction_ne
    intro h
    rw [probeGenerator_contraction K S P.arithmetic I,
      probeGenerator_contraction K S P.arithmetic J] at h
    exact hIJ (Subtype.ext (Subtype.ext h))
  · rw [correlation_eq_originalFull, sIntegerSexticOriginalFullCorrelation_self_zero]
    exact_mod_cast Nat.card_congr (Units.mapEquiv
      (Ideal.quotEquivOfEq (P.arithmetic.generator_span I)).toMulEquiv).toEquiv

/-- GR-03 in the form stated in `HeckeSkeleton.Gram`. -/
theorem complete_pair_fourier (P : ProbeData K S) (I J : ExteriorIdeal K S) (m : R) :
    probeGauss K S P I (-m) * conj (probeGauss K S P J (-m)) =
      ∑' j : ThetaQuotient K S (exteriorMul K S I J),
        HeckeSkeleton.Gram.correlation K S P I J
            (Classical.choose (Ideal.Quotient.mk_surjective j)) *
          sLocalPrincipalPhase K S
            (((-m : R) : K) *
              ((Classical.choose (Ideal.Quotient.mk_surjective j) : R) : K) /
                ((P.arithmetic.generator I : K) * (P.arithmetic.generator J : K))) := by
  rw [probeGauss_mul_conj_eq_originalFull_fourier K S P I J (-m), tsum_fintype]
  unfold HeckeGeneral.Arithmetic.PeriodicFourier.fourier
  refine Fintype.sum_equiv
    (Ideal.quotEquivOfEq (totalIdeal_eq K S P.arithmetic I J)).toEquiv _ _ (fun t => ?_)
  set a := Classical.choose (Ideal.Quotient.mk_surjective
    ((Ideal.quotEquivOfEq (totalIdeal_eq K S P.arithmetic I J)).toEquiv t)) with ha
  have hta : t = Ideal.Quotient.mk _ a := by
    apply (Ideal.quotEquivOfEq (totalIdeal_eq K S P.arithmetic I J)).injective
    rw [Ideal.quotEquivOfEq_mk]
    exact (Classical.choose_spec (Ideal.Quotient.mk_surjective _)).symm
  rw [correlation_eq_originalFull]
  conv_lhs => rw [hta]
  rw [sIntegerSexticOriginalFullQuotientCorrelation_mk, ← map_mul,
    originalFullPositiveTraceCharacter_mk]
  congr 2

end HeckeSkeleton.GramCorrelation
