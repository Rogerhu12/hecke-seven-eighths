import HeckeGeneral.Analysis.SixthPowerFreeFactorization
import HeckeGeneral.Analysis.ActualSIntegerAmplifierRows
import HeckeGeneral.Arithmetic.SIntegerOrbitDilation

/-!
Simultaneous sixth-power amplification of actual sixth-power-free orbits.
The base orbit and amplifier ideal are both recovered from the output;
all original unit sectors are retained. No moment or amplifier lower-count
estimate is assumed or proved in this arithmetic module.
-/

noncomputable section
namespace HeckeGeneral.Analysis.ActualSIntegerMoments

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton HeckeGeneral.Analysis.ConditionalMoments
open scoped Classical nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem sIntegerModulusContraction_mul (a b : S.integer K)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    sIntegerModulusContraction K S (a * b) =
      sIntegerModulusContraction K S a * sIntegerModulusContraction K S b := by
  have hcop : ∀ v ∈ S,
      (sIntegerModulusContraction K S a * sIntegerModulusContraction K S b) ⊔
        v.asIdeal = ⊤ := by
    intro v hv
    rw [Ideal.mul_sup_eq_of_coprime_left
      (sIntegerModulusContraction_coprime K S a ha v hv)]
    exact sIntegerModulusContraction_coprime K S b hb v hv
  rw [← under_map_coprime_sIntegerIdeal K S _ hcop, Ideal.map_mul,
    map_sIntegerModulusContraction, map_sIntegerModulusContraction,
    Ideal.span_singleton_mul_span_singleton]
  rfl

def actualSIntegerOrbitIdeal (q : ActualSIntegerOrbit K S) : NonzeroIdeal K :=
  ⟨actualSIntegerOrbitContraction K S q, mem_nonZeroDivisors_of_ne_zero (by
    refine Quotient.inductionOn q ?_
    intro a
    exact sIntegerModulusContraction_ne_bot K S a.val a.property)⟩

abbrev ActualSixthPowerFreeOrbit :=
  {q : ActualSIntegerOrbit K S // SixthPowerFreeIdeal (actualSIntegerOrbitIdeal K S q)}

variable (τ : ThetaArithmeticData K S)

def actualSimultaneousAmplifier (q : ActualSIntegerOrbit K S) (A : ExteriorIdeal K S) :
    ActualSIntegerOrbit K S :=
  sIntegerOrbitDilation K S (sixthPowerSUnitSubgroup K S)
    (actualAmplifierElement K S τ A) q

theorem actualSimultaneousAmplifier_ideal (q : ActualSIntegerOrbit K S)
    (A : ExteriorIdeal K S) :
    actualSIntegerOrbitIdeal K S (actualSimultaneousAmplifier K S τ q A) =
      actualSIntegerOrbitIdeal K S q * A.val ^ 6 := by
  apply Subtype.ext
  refine Quotient.inductionOn q ?_
  intro a
  change sIntegerModulusContraction K S (τ.generator A ^ 6 * a.val) =
    sIntegerModulusContraction K S a.val * A.val.val ^ 6
  rw [sIntegerModulusContraction_mul K S _ _
    (pow_ne_zero 6 (τ.generator_ne_zero A)) a.property,
    contraction_thetaGenerator_pow, mul_comm]

theorem actualSimultaneousAmplifier_injective : Function.Injective
    (fun x : ActualSixthPowerFreeOrbit K S × ExteriorIdeal K S =>
      actualSimultaneousAmplifier K S τ x.1.val x.2) := by
  intro x y h
  have hi := congrArg (actualSIntegerOrbitIdeal K S) h
  rw [actualSimultaneousAmplifier_ideal, actualSimultaneousAmplifier_ideal] at hi
  obtain ⟨_, hA⟩ := sixthPowerFree_mul_sixth_unique x.1.property y.1.property hi
  have hxy : x.2 = y.2 := Subtype.ext hA
  apply Prod.ext
  · apply Subtype.ext
    change sIntegerOrbitDilation K S (sixthPowerSUnitSubgroup K S)
      (actualAmplifierElement K S τ x.2) x.1.val =
      sIntegerOrbitDilation K S (sixthPowerSUnitSubgroup K S)
      (actualAmplifierElement K S τ y.2) y.1.val at h
    rw [hxy] at h
    exact sIntegerOrbitDilation_injective K S (sixthPowerSUnitSubgroup K S)
      (actualAmplifierElement K S τ y.2) h
  · exact hxy

def actualSimultaneousAmplifierEmbedding :
    (ActualSixthPowerFreeOrbit K S × ExteriorIdeal K S) ↪ ActualSIntegerOrbit K S :=
  ⟨_, actualSimultaneousAmplifier_injective K S τ⟩

theorem actualSimultaneousAmplifier_norm (q : ActualSIntegerOrbit K S)
    (A : ExteriorIdeal K S) :
    actualSIntegerOrbitNorm K S (actualSimultaneousAmplifier K S τ q A) =
      actualSIntegerOrbitNorm K S q * (idealNorm K A.val) ^ 6 := by
  rw [actualSIntegerOrbitNorm_eq_absNorm_contraction]
  change ((actualSIntegerOrbitIdeal K S
    (actualSimultaneousAmplifier K S τ q A)).val.absNorm : ℝ) = _
  rw [actualSimultaneousAmplifier_ideal]
  simp only [Submonoid.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow,
    Nat.cast_mul, Nat.cast_pow]
  rw [actualSIntegerOrbitNorm_eq_absNorm_contraction]
  rfl

theorem actualSimultaneousAmplifier_norm_le {U P : ℝ}
    (q : ActualSIntegerOrbit K S) (A : ExteriorIdeal K S)
    (hq : actualSIntegerOrbitNorm K S q ≤ U) (hA : idealNorm K A.val ≤ P) :
    actualSIntegerOrbitNorm K S (actualSimultaneousAmplifier K S τ q A) ≤ U * P ^ 6 := by
  rw [actualSimultaneousAmplifier_norm]
  exact mul_le_mul hq (pow_le_pow_left₀ (idealNorm_pos K A.val).le hA 6)
    (by positivity) ((actualSIntegerOrbitNorm_pos K S q).le.trans hq)

/-- Independent bounds for the base row and amplifier produce the exact
product bound U P^6; no relation between U and P is imposed. -/
def boundedActualSimultaneousAmplifierEmbedding (U P : ℝ) :
    ({q : ActualSixthPowerFreeOrbit K S // actualSIntegerOrbitNorm K S q.val ≤ U} ×
      {A : ExteriorIdeal K S // idealNorm K A.val ≤ P}) ↪
        ActualBoundedSIntegerOrbits K S (U * P ^ 6) where
  toFun x := ⟨actualSimultaneousAmplifier K S τ x.1.val.val x.2.val,
    actualSimultaneousAmplifier_norm_le K S τ _ _ x.1.property x.2.property⟩
  inj' x y h := by
    have he := actualSimultaneousAmplifier_injective K S τ
      (a₁ := (x.1.val, x.2.val)) (a₂ := (y.1.val, y.2.val)) (congrArg Subtype.val h)
    exact Prod.ext (Subtype.ext (congrArg Prod.fst he))
      (Subtype.ext (congrArg Prod.snd he))

end HeckeGeneral.Analysis.ActualSIntegerMoments
