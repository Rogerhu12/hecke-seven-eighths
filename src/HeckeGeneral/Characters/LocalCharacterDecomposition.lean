import HeckeGeneral.Characters.LocalUnitDecomposition
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Finite and unramified parts of an actual finite local component

Every actual local component is the product of a finite-order character
and a genuine local restriction of an idelic norm twist. The frequency is
chosen using the principal argument of its value on the chosen uniformizer.
-/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

def unramifiedLocalCharacter (v : HeightOneSpectrum (𝓞 K)) (z : Circle) :
    UnitaryCharacter (v.adicCompletion K)ˣ where
  toFun u := z ^ Multiplicative.toAdd (localOrder K v u)
  map_one' := by simp
  map_mul' u w := by
    rw [map_mul]
    exact zpow_add z _ _
  continuous_toFun :=
    (continuous_of_discreteTopology : Continuous (fun n : Multiplicative ℤ =>
      z ^ Multiplicative.toAdd n)).comp (localOrder K v).continuous

@[simp] theorem unramifiedLocalCharacter_integralUnit (v : HeightOneSpectrum (𝓞 K))
    (z : Circle) (u : (LocalIntegerRing K v)ˣ) :
    unramifiedLocalCharacter K v z (localIntegerUnitsEmbedding K v u) = 1 := by
  change z ^ Multiplicative.toAdd (localOrderHom K v (localIntegerUnitsEmbedding K v u)) = 1
  rw [localOrder_integralUnit]
  exact zpow_zero z

@[simp] theorem unramifiedLocalCharacter_uniformizer (v : HeightOneSpectrum (𝓞 K))
    (z : Circle) : unramifiedLocalCharacter K v z (localUniformizerUnit K v) = z := by
  change z ^ Multiplicative.toAdd (localOrderHom K v (localUniformizerUnit K v)) = z
  rw [localOrder_uniformizer]
  exact zpow_one z

/-- Integral units and one uniformizer determine a character of the whole local field. -/
theorem localCharacter_ext (v : HeightOneSpectrum (𝓞 K))
    (χ ψ : UnitaryCharacter (v.adicCompletion K)ˣ)
    (hi : ∀ u : (LocalIntegerRing K v)ˣ,
      χ (localIntegerUnitsEmbedding K v u) = ψ (localIntegerUnitsEmbedding K v u))
    (hπ : χ (localUniformizerUnit K v) = ψ (localUniformizerUnit K v)) : χ = ψ := by
  apply ContinuousMonoidHom.ext
  intro u
  calc
    χ u = χ (localIntegerUnitsEmbedding K v (localUnitPart K v u) *
        localUniformizerUnit K v ^ Multiplicative.toAdd (localOrder K v u)) :=
      congrArg χ (localUnit_decomposition K v u)
    _ = χ (localIntegerUnitsEmbedding K v (localUnitPart K v u)) *
        χ (localUniformizerUnit K v) ^ Multiplicative.toAdd (localOrder K v u) := by
      rw [map_mul, map_zpow]
    _ = ψ (localIntegerUnitsEmbedding K v (localUnitPart K v u)) *
        ψ (localUniformizerUnit K v) ^ Multiplicative.toAdd (localOrder K v u) := by rw [hi, hπ]
    _ = ψ u := by rw [← map_zpow, ← map_mul, ← localUnit_decomposition]

def localFinitePartCharacter (v : HeightOneSpectrum (𝓞 K)) (χ : HeckeCharacter K) :
    UnitaryCharacter (v.adicCompletion K)ˣ :=
  pullback (localUnitPart K v) (localIntegralComponent K v χ)

theorem finiteOrder_localFinitePartCharacter (v : HeightOneSpectrum (𝓞 K))
    (χ : HeckeCharacter K) : FiniteOrder (localFinitePartCharacter K v χ) :=
  finiteOrder_pullback (localUnitPart K v) (finiteOrder_localIntegralComponent K v χ)

@[simp] theorem localFinitePartCharacter_integralUnit (v : HeightOneSpectrum (𝓞 K))
    (χ : HeckeCharacter K) (u : (LocalIntegerRing K v)ˣ) :
    localFinitePartCharacter K v χ (localIntegerUnitsEmbedding K v u) =
      localIntegralComponent K v χ u := by
  change localIntegralComponent K v χ (localUnitPart K v (localIntegerUnitsEmbedding K v u)) = _
  rw [localUnitPart_integralUnit]

@[simp] theorem localFinitePartCharacter_uniformizer (v : HeightOneSpectrum (𝓞 K))
    (χ : HeckeCharacter K) : localFinitePartCharacter K v χ (localUniformizerUnit K v) = 1 := by
  change localIntegralComponent K v χ (localUnitPart K v (localUniformizerUnit K v)) = 1
  have h := localUnitPart_uniformizer_zpow K v (1 : ℤ)
  rw [zpow_one] at h
  rw [h, map_one]

theorem localComponent_eq_finitePart_mul_unramified (v : HeightOneSpectrum (𝓞 K))
    (χ : HeckeCharacter K) :
    localComponent K v χ = localFinitePartCharacter K v χ *
      unramifiedLocalCharacter K v (localComponent K v χ (localUniformizerUnit K v)) := by
  apply localCharacter_ext
  · intro u
    change localIntegralComponent K v χ u =
      localFinitePartCharacter K v χ (localIntegerUnitsEmbedding K v u) *
        unramifiedLocalCharacter K v _ (localIntegerUnitsEmbedding K v u)
    rw [localFinitePartCharacter_integralUnit, unramifiedLocalCharacter_integralUnit, mul_one]
  · change localComponent K v χ (localUniformizerUnit K v) =
      localFinitePartCharacter K v χ (localUniformizerUnit K v) *
        unramifiedLocalCharacter K v _ (localUniformizerUnit K v)
    rw [localFinitePartCharacter_uniformizer, unramifiedLocalCharacter_uniformizer, one_mul]

def localUnramifiedFrequency (v : HeightOneSpectrum (𝓞 K)) (z : Circle) : ℝ :=
  (z : ℂ).arg / Real.log (residueCard K v)

theorem unramifiedLocalCharacter_eq_normTwist (v : HeightOneSpectrum (𝓞 K)) (z : Circle) :
    unramifiedLocalCharacter K v z =
      localComponent K v (heckeNormTwist K (localUnramifiedFrequency K v z)) := by
  apply localCharacter_ext
  · intro u
    rw [unramifiedLocalCharacter_integralUnit]
    exact (unramifiedAt_normTwist K _ v _ (localIntegerUnitsEmbedding_norm K v u)).symm
  · rw [unramifiedLocalCharacter_uniformizer, heckeNormTwist_uniformizer]
    have hq : (1 : ℝ) < residueCard K v := by exact_mod_cast one_lt_residueCard K v
    rw [localUnramifiedFrequency, div_mul_cancel₀ _ (Real.log_pos hq).ne']
    exact (Circle.exp_arg z).symm

theorem localComponent_eq_finitePart_mul_normTwist (v : HeightOneSpectrum (𝓞 K))
    (χ : HeckeCharacter K) :
    localComponent K v χ = localFinitePartCharacter K v χ * localComponent K v
      (heckeNormTwist K (localUnramifiedFrequency K v
        (localComponent K v χ (localUniformizerUnit K v)))) := by
  exact (localComponent_eq_finitePart_mul_unramified K v χ).trans
    (congrArg (fun ψ => localFinitePartCharacter K v χ * ψ)
      (unramifiedLocalCharacter_eq_normTwist K v
        (localComponent K v χ (localUniformizerUnit K v))))

theorem exists_finiteOrder_mul_localNormTwist (v : HeightOneSpectrum (𝓞 K))
    (χ : HeckeCharacter K) :
    ∃ θ : UnitaryCharacter (v.adicCompletion K)ˣ, FiniteOrder θ ∧
      ∃ t : ℝ, localComponent K v χ = θ * localComponent K v (heckeNormTwist K t) :=
  ⟨localFinitePartCharacter K v χ, finiteOrder_localFinitePartCharacter K v χ,
    localUnramifiedFrequency K v (localComponent K v χ (localUniformizerUnit K v)),
    localComponent_eq_finitePart_mul_normTwist K v χ⟩

theorem localFinitePartCharacter_mul_normTwist (v : HeightOneSpectrum (𝓞 K))
    (χ : HeckeCharacter K) (t : ℝ) :
    localFinitePartCharacter K v (χ * heckeNormTwist K t) = localFinitePartCharacter K v χ := by
  apply ContinuousMonoidHom.ext
  intro u
  change localComponent K v (χ * heckeNormTwist K t)
    (localIntegerUnitsEmbedding K v (localUnitPart K v u)) = _
  change localComponent K v χ (localIntegerUnitsEmbedding K v (localUnitPart K v u)) *
    localComponent K v (heckeNormTwist K t) (localIntegerUnitsEmbedding K v (localUnitPart K v u)) = _
  rw [unramifiedAt_normTwist K t v _ (localIntegerUnitsEmbedding_norm K v _), mul_one]
  rfl

end HeckeGeneral.Characters
