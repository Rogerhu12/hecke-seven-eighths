import HeckeGeneral.Analysis.ActualSIntegerZeroSlotMI
import HeckeGeneral.Analysis.LocalThetaInput

/-!
Actual sixth-power amplifier rows, constructed from the existing arithmetic
generator data. Contraction, norm, and injectivity are proved from generator_span,
not supplied as assumptions. No allowed-section calibration or lower count of
amplifiers is asserted. This does not claim that the sixth-power map on ALL
S-unit-subgroup orbits is injective: the domain here is actual exterior ideals.
-/

noncomputable section

namespace HeckeGeneral.Analysis.ActualSIntegerMoments

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton
open UniqueFactorizationMonoid
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

omit [Fintype S] in
/-- Actual contraction is invariant under the literal subgroup orbit relation. -/
theorem sIntegerModulusContraction_eq_of_sixthOrbitRel
    (a b : NonzeroRingElements (S.integer K))
    (hab : MulAction.orbitRel (sIntegerUnitSubgroup K S (sixthPowerSUnitSubgroup K S))
      (NonzeroRingElements (S.integer K)) a b) :
    sIntegerModulusContraction K S a.val = sIntegerModulusContraction K S b.val := by
  obtain ⟨γ, hγ⟩ :=
    (sIntegerOrbitRelation_iff K S (sixthPowerSUnitSubgroup K S) a b).mp hab
  have heq : (S.unitEquivUnitsInteger K γ.val).val * b.val = a.val := Subtype.ext hγ
  unfold sIntegerModulusContraction
  rw [← heq, Ideal.span_singleton_mul_left_unit (S.unitEquivUnitsInteger K γ.val).isUnit]

/-- The ordinary ideal actually contracted from the principal orbit modulus. -/
def actualSIntegerOrbitContraction (q : ActualSIntegerOrbit K S) : Ideal (𝓞 K) :=
  Quotient.liftOn q (fun a => sIntegerModulusContraction K S a.val)
    (sIntegerModulusContraction_eq_of_sixthOrbitRel K S)

omit [Fintype S] in
@[simp] theorem actualSIntegerOrbitContraction_mk
    (a : NonzeroRingElements (S.integer K)) :
    actualSIntegerOrbitContraction K S (Quotient.mk _ a) =
      sIntegerModulusContraction K S a.val := rfl

/-- The quotient norm is identified with the actual contraction, using the
proved principal residue equivalence and local product norm calculation. -/
theorem actualSIntegerOrbitNorm_eq_absNorm_contraction (q : ActualSIntegerOrbit K S) :
    actualSIntegerOrbitNorm K S q = (actualSIntegerOrbitContraction K S q).absNorm := by
  refine Quotient.inductionOn q ?_
  intro a
  rw [actualSIntegerOrbitNorm_mk, actualSIntegerOrbitContraction_mk,
    ← natCard_sIntegerPrincipalResidue_eq_productNorm K S a.val a.property,
    natCard_sIntegerPrincipalResidue K S a.val a.property]

variable (τ : ThetaArithmeticData K S)

/-- The existing generator really contracts to the exterior ideal it generates. -/
theorem contraction_thetaGenerator (A : ExteriorIdeal K S) :
    sIntegerModulusContraction K S (τ.generator A) = A.val.val := by
  unfold sIntegerModulusContraction
  rw [τ.generator_span]
  exact under_map_coprime_sIntegerIdeal K S A.val.val
    (sexticIdeal_coprime_S K S A.val.val A.property)

/-- Every power contracts to the corresponding actual ordinary ideal power. -/
theorem contraction_thetaGenerator_pow (A : ExteriorIdeal K S) (n : ℕ) :
    sIntegerModulusContraction K S (τ.generator A ^ n) = A.val.val ^ n := by
  unfold sIntegerModulusContraction
  rw [← Ideal.span_singleton_pow, τ.generator_span, ← Ideal.map_pow]
  exact under_map_coprime_sIntegerIdeal K S (A.val.val ^ n)
    (sexticIdeal_coprime_S K S (A.val.val ^ n)
      (fun p hp => A.property p (p.prime.dvd_of_dvd_pow hp)))

/-- The actual sixth power of the supplied nonzero S-integer generator. -/
def actualAmplifierElement (A : ExteriorIdeal K S) :
    NonzeroRingElements (S.integer K) :=
  ⟨τ.generator A ^ 6, pow_ne_zero 6 (τ.generator_ne_zero A)⟩

/-- Actual quotient row; no row character or arbitrary section of rows is used. -/
def actualAmplifierRow (A : ExteriorIdeal K S) : ActualSIntegerOrbit K S :=
  Quotient.mk _ (actualAmplifierElement K S τ A)

theorem actualAmplifierRow_contraction (A : ExteriorIdeal K S) :
    actualSIntegerOrbitContraction K S (actualAmplifierRow K S τ A) = A.val.val ^ 6 :=
  contraction_thetaGenerator_pow K S τ A 6

theorem actualAmplifierRow_norm (A : ExteriorIdeal K S) :
    actualSIntegerOrbitNorm K S (actualAmplifierRow K S τ A) = (idealNorm K A.val) ^ 6 := by
  rw [actualSIntegerOrbitNorm_eq_absNorm_contraction, actualAmplifierRow_contraction]
  simp only [map_pow, Nat.cast_pow, idealNorm]

/-- Actual ideal factor multiplicities recover A from its sixth-power row. -/
theorem actualAmplifierRow_injective : Function.Injective (actualAmplifierRow K S τ) := by
  intro A B hrow
  have hpower := congrArg (actualSIntegerOrbitContraction K S) hrow
  rw [actualAmplifierRow_contraction, actualAmplifierRow_contraction] at hpower
  apply Subtype.ext
  apply (primeExponentEquiv (R := 𝓞 K)).injective
  ext p
  change (normalizedFactors A.val.val).count p.asIdeal =
    (normalizedFactors B.val.val).count p.asIdeal
  have hcount := congrArg (fun I : Ideal (𝓞 K) => (normalizedFactors I).count p.asIdeal) hpower
  simp only [normalizedFactors_pow, Multiset.count_nsmul] at hcount
  omega

def actualAmplifierRowEmbedding : ExteriorIdeal K S ↪ ActualSIntegerOrbit K S :=
  ⟨actualAmplifierRow K S τ, actualAmplifierRow_injective K S τ⟩

theorem actualAmplifierRow_norm_le {P : ℝ} (A : ExteriorIdeal K S)
    (hA : idealNorm K A.val ≤ P) :
    actualSIntegerOrbitNorm K S (actualAmplifierRow K S τ A) ≤ P ^ 6 := by
  rw [actualAmplifierRow_norm]
  exact pow_le_pow_left₀ (idealNorm_pos K A.val).le hA 6

/-- The finite image of a genuine finite set of exterior amplifier ideals. -/
def actualAmplifierRows (F : Finset (ExteriorIdeal K S)) : Finset (ActualSIntegerOrbit K S) :=
  F.image (actualAmplifierRow K S τ)

@[simp] theorem card_actualAmplifierRows (F : Finset (ExteriorIdeal K S)) :
    (actualAmplifierRows K S τ F).card = F.card :=
  Finset.card_image_of_injective F (actualAmplifierRow_injective K S τ)

theorem actualAmplifierRows_norm_le (F : Finset (ExteriorIdeal K S)) {P : ℝ}
    (hF : ∀ A ∈ F, idealNorm K A.val ≤ P) :
    ∀ q ∈ actualAmplifierRows K S τ F, actualSIntegerOrbitNorm K S q ≤ P ^ 6 := by
  intro q hq
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hq
  exact actualAmplifierRow_norm_le K S τ A (hF A hA)

/-- Embed the finite amplifier domain into the genuine bounded-orbit type. -/
def boundedActualAmplifierRowEmbedding (F : Finset (ExteriorIdeal K S)) (P : ℝ)
    (hF : ∀ A ∈ F, idealNorm K A.val ≤ P) :
    {A : ExteriorIdeal K S // A ∈ F} ↪ ActualBoundedSIntegerOrbits K S (P ^ 6) where
  toFun A := ⟨actualAmplifierRow K S τ A.val,
    actualAmplifierRow_norm_le K S τ A.val (hF A.val A.property)⟩
  inj' _A _B h := Subtype.ext
    (actualAmplifierRow_injective K S τ (congrArg Subtype.val h))

include τ in
/-- Counting the bounded row image loses no amplifier cardinality. -/
theorem card_amplifiers_le_boundedOrbits (F : Finset (ExteriorIdeal K S)) (P : ℝ)
    (hF : ∀ A ∈ F, idealNorm K A.val ≤ P) :
    F.card ≤ Nat.card (ActualBoundedSIntegerOrbits K S (P ^ 6)) := by
  let e := boundedActualAmplifierRowEmbedding K S τ F P hF
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
    (Nat.card_le_card_of_injective e e.injective)

end HeckeGeneral.Analysis.ActualSIntegerMoments
