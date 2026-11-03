import CubicSieve.CubicConductors
import HeckeGeneral.Characters.ComplexCharacter
import DedekindZetaZeroFree.Arithmetic.Kummer.FrequencyClassesAndCharacterRigidity

/-!
Primitive ray realizations of the actual cubic Hecke characters. The upstream
character is transported through the genuine topological idele-class comparison.
Primitivity is supplied by the proved `primitiveRay_exists` construction. The
equality of its modulus with the actual finite conductor follows from the two
least-local-depth definitions, not from a supplied conductor comparison.
-/

set_option autoImplicit false
set_option maxRecDepth 2048
noncomputable section

namespace CubicSieve.PrimitiveCharacters

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Arithmetic
open HeckeGeneral.Characters.ArithmeticKummerDraft
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Analysis.PrimeCalibrationDraft
open DedekindZetaZeroFree DedekindZetaZeroFree.Detector
open CubicSieve.CubicCharacters
open scoped Classical NumberField nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

def upstreamCharacter (χ : HeckeCharacter K) : _root_.IdeleClassGroup K →ₜ* ℂˣ where
  toMonoidHom := Circle.toUnits.comp
    (χ.toMonoidHom.comp
      (_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K).toMonoidHom)
  continuous_toFun := complexCircleEmbedding.continuous.comp
    (χ.continuous.comp
      (_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K).continuous)

@[simp] theorem upstreamCharacter_apply (χ : HeckeCharacter K)
    (c : _root_.IdeleClassGroup K) :
    upstreamCharacter K χ c = complexCircleEmbedding
      (χ ((_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K) c)) := rfl

theorem upstreamCharacter_pow (χ : HeckeCharacter K) (n : ℕ) :
    upstreamCharacter K (χ ^ n) = upstreamCharacter K χ ^ n := by
  ext c
  simp only [upstreamCharacter_apply, ContinuousMonoidHom.pow_apply, map_pow]

theorem upstreamCharacter_local (χ : HeckeCharacter K)
    (p : HeightOneSpectrum (𝓞 K)) (u : (p.adicCompletion K)ˣ) :
    upstreamCharacter K χ (_root_.IdeleGroup.finitePlaceIdeleClass p u) =
      complexCircleEmbedding (localComponent K p χ u) := by
  rw [upstreamCharacter_apply]
  have hc : (_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K)
      (_root_.IdeleGroup.finitePlaceIdeleClass p u) = localIdeleClassMap K p u := by
    exact _root_.IdeleGroup.ideleClassGroupEquivMathlib_finitePlaceIdeleClass K p u
  rw [hc]
  rfl

theorem upstreamCharacter_local_eq_one_iff (χ : HeckeCharacter K)
    (p : HeightOneSpectrum (𝓞 K)) (u : (p.adicCompletion K)ˣ) :
    upstreamCharacter K χ (_root_.IdeleGroup.finitePlaceIdeleClass p u) = 1 ↔
      localComponent K p χ u = 1 := by
  rw [upstreamCharacter_local]
  constructor
  · intro h
    apply Circle.ext
    exact congrArg Units.val h
  · intro h
    rw [h, map_one]

/-- The two local filtrations are literally compared on integral unit representatives. -/
theorem trivialAtDepth_iff_upstream (χ : HeckeCharacter K)
    (p : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    TrivialAtDepth K χ p n ↔
      ∀ u : (p.adicCompletion K)ˣ, u ∈ ClassFieldTheory.rayLocalHigherUnitGroup p n →
        upstreamCharacter K χ (_root_.IdeleGroup.finitePlaceIdeleClass p u) = 1 := by
  rw [trivialAtDepth_iff_principalUnits_le_ker K p χ n]
  constructor
  · intro h u hu
    obtain ⟨y, hy, hcong⟩ := (ClassFieldTheory.mem_rayLocalHigherUnitGroup_iff p n u).mp hu
    have hm : y ∈ principalUnits K p n := (mem_principalUnits_iff K p n y).mpr hcong
    have hv := h hm
    apply (upstreamCharacter_local_eq_one_iff K χ p u).mpr
    have he : localIntegerUnitsEmbedding K p y = u := by
      apply Units.ext
      exact congrArg Units.val hy
    change localComponent K p χ (localIntegerUnitsEmbedding K p y) = 1 at hv
    rwa [he] at hv
  · intro h y hy
    change localComponent K p χ (localIntegerUnitsEmbedding K p y) = 1
    apply (upstreamCharacter_local_eq_one_iff K χ p _).mp
    apply h
    apply (ClassFieldTheory.mem_rayLocalHigherUnitGroup_iff p n _).mpr
    refine ⟨y, ?_, (mem_principalUnits_iff K p n y).mp hy⟩
    apply Units.ext
    rfl

structure Model (hc : NumberField.IsTotallyComplex K) (χ : HeckeCharacter K) where
  frequency : PrimitiveFrequencyCharacter K
  realizes : ∀ c : _root_.IdeleClassGroup K,
    RayClassBridge.ideleClassCharacter K hc frequency.conductor frequency.conductor_ne_zero
      frequency.character c = upstreamCharacter K χ c

theorem nonemptyModel (hc : NumberField.IsTotallyComplex K) (χ : HeckeCharacter K)
    (hχ : FiniteOrder χ) : Nonempty (Model K hc χ) := by
  obtain ⟨n, hn, hpow⟩ := (finiteOrder_iff_pointwise χ).mp hχ
  have ho : ∃ n : ℕ, 0 < n ∧ ∀ c : _root_.IdeleClassGroup K,
      upstreamCharacter K χ c ^ n = 1 := by
    refine ⟨n, hn, fun c => ?_⟩
    rw [upstreamCharacter_apply, ← map_pow, hpow, map_one]
  obtain ⟨m, hm, ρ, ψ, hprim, _, _, hreal, _⟩ :=
    PrimitiveRay.primitiveRay_exists hc (upstreamCharacter K χ) ho
  exact ⟨⟨⟨m, hm, ψ, hprim⟩, hreal⟩⟩

def model (hc : NumberField.IsTotallyComplex K) (χ : HeckeCharacter K)
    (hχ : FiniteOrder χ) : Model K hc χ := Classical.choice (nonemptyModel K hc χ hχ)

theorem Model.local_exponent_eq {hc : NumberField.IsTotallyComplex K} {χ : HeckeCharacter K}
    (P : Model K hc χ) (p : HeightOneSpectrum (𝓞 K)) :
    (RayClassBridge.narrowIdealModulus K P.frequency.conductor
      P.frequency.conductor_ne_zero).finitePart p = localConductorExponent K χ p := by
  have hleast := (PrimitiveRay.primitive_iff_local_isLeast hc P.frequency.conductor
    P.frequency.conductor_ne_zero P.frequency.character).mp P.frequency.primitive p
  simp only [P.realizes] at hleast
  apply le_antisymm
  · exact hleast.2 ((trivialAtDepth_iff_upstream K χ p _).mp
      (trivialAtDepth_localConductorExponent K χ p))
  · exact localConductorExponent_le K χ p ((trivialAtDepth_iff_upstream K χ p _).mpr hleast.1)

private theorem narrow_exponent_eq_primeExponents (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (p : HeightOneSpectrum (𝓞 K)) :
    (RayClassBridge.narrowIdealModulus K m hm).finitePart p =
      primeExponents (⟨m, mem_nonZeroDivisors_of_ne_zero hm⟩ : (Ideal (𝓞 K))⁰) p := by
  rw [RayClassBridge.narrowIdealModulus_finitePart, FractionalIdeal.count_coe K p hm,
    Int.toNat_natCast]
  rw [primeExponents_apply]
  exact Ideal.count_associates_factors_eq hm p.isPrime p.ne_bot

/-- Exact equality of the primitive ray modulus and the actual finite conductor. -/
theorem Model.conductor_eq {hc : NumberField.IsTotallyComplex K} {χ : HeckeCharacter K}
    (P : Model K hc χ) : P.frequency.conductor = (finiteConductor K χ).val := by
  have he : (⟨P.frequency.conductor,
      mem_nonZeroDivisors_of_ne_zero P.frequency.conductor_ne_zero⟩ : (Ideal (𝓞 K))⁰) =
      finiteConductor K χ := by
    apply (primeExponentEquiv (R := 𝓞 K)).injective
    ext p
    change primeExponents (⟨P.frequency.conductor,
      mem_nonZeroDivisors_of_ne_zero P.frequency.conductor_ne_zero⟩ : (Ideal (𝓞 K))⁰) p =
      primeExponents (finiteConductor K χ) p
    rw [primeExponents_finiteConductor, conductorExponents_apply,
      ← narrow_exponent_eq_primeExponents K _ P.frequency.conductor_ne_zero p]
    exact Model.local_exponent_eq K P p
  exact congrArg Subtype.val he

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

include D in
theorem totallyComplex : NumberField.IsTotallyComplex K :=
  DedekindZetaZeroFree.primitive12_totallyComplex K D.root12 D.primitive12

def primitiveCharacter (J : ExteriorIdeal K S) : PrimitiveFrequencyCharacter K :=
  (model K (totallyComplex K S D) (cubicCharacter K S D J)
    (cubicCharacter_finiteOrder K S D J)).frequency

theorem primitiveCharacter_realizes (J : ExteriorIdeal K S) (c : _root_.IdeleClassGroup K) :
    RayClassBridge.ideleClassCharacter K (totallyComplex K S D)
      (primitiveCharacter K S D J).conductor (primitiveCharacter K S D J).conductor_ne_zero
      (primitiveCharacter K S D J).character c =
        upstreamCharacter K (cubicCharacter K S D J) c :=
  (model K (totallyComplex K S D) (cubicCharacter K S D J)
    (cubicCharacter_finiteOrder K S D J)).realizes c

theorem primitiveCharacter_conductor (J : ExteriorIdeal K S) :
    (primitiveCharacter K S D J).conductor =
      (finiteConductor K (cubicCharacter K S D J)).val :=
  Model.conductor_eq K (model K (totallyComplex K S D) (cubicCharacter K S D J)
    (cubicCharacter_finiteOrder K S D J))

def localCharacter (J : ExteriorIdeal K S) (p : HeightOneSpectrum (𝓞 K)) :
    (p.adicCompletion K)ˣ →ₜ* ℂˣ :=
  complexCircleEmbedding.comp (localComponent K p (cubicCharacter K S D J))

theorem primitiveCharacter_local_component (J : ExteriorIdeal K S)
    (p : HeightOneSpectrum (𝓞 K)) (u : (p.adicCompletion K)ˣ) :
    RayClassBridge.ideleClassCharacter K (totallyComplex K S D)
      (primitiveCharacter K S D J).conductor (primitiveCharacter K S D J).conductor_ne_zero
      (primitiveCharacter K S D J).character (_root_.IdeleGroup.finitePlaceIdeleClass p u) =
        localCharacter K S D J p u := by
  rw [primitiveCharacter_realizes, upstreamCharacter_local]
  rfl

theorem localCharacter_cube (J : ExteriorIdeal K S) (p : HeightOneSpectrum (𝓞 K))
    (u : (p.adicCompletion K)ˣ) : localCharacter K S D J p u ^ 3 = 1 := by
  change complexCircleEmbedding
    (cubicCharacter K S D J (localIdeleClassMap K p u)) ^ 3 = 1
  rw [← map_pow]
  have h := congrArg (fun χ : HeckeCharacter K => χ (localIdeleClassMap K p u))
    (cubicCharacter_pow_three K S D J)
  change cubicCharacter K S D J (localIdeleClassMap K p u) ^ 3 = 1 at h
  rw [h, map_one]

end CubicSieve.PrimitiveCharacters
