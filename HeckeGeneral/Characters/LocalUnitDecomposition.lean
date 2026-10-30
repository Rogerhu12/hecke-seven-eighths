import HeckeGeneral.Characters.LocalResidueCharacter
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Instances.Int

/-! Uniformizer order and the continuous integral-unit part of a finite local unit. -/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter Topology
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

theorem localUnit_valuation_ne_zero (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ) :
    (Valued.v u.val : WithZero (Multiplicative ℤ)) ≠ 0 :=
  (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).map_eq_zero_iff.ne.mpr
    (Units.ne_zero u)

/-- Additive uniformizer order, represented in a multiplicative copy of `ℤ`. -/
def localOrderHom (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* Multiplicative ℤ where
  toFun u := Multiplicative.ofAdd (-WithZero.log (Valued.v u.val))
  map_one' := by simp
  map_mul' u w := by
    simp only [Units.val_mul, map_mul, WithZero.log_mul (localUnit_valuation_ne_zero K v u)
      (localUnit_valuation_ne_zero K v w), neg_add]
    rfl

theorem localOrder_valuation (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ) :
    (Valued.v u.val : WithZero (Multiplicative ℤ)) =
      WithZero.exp (-Multiplicative.toAdd (localOrderHom K v u)) := by
  change Valued.v u.val = WithZero.exp (- -WithZero.log (Valued.v u.val))
  rw [neg_neg, WithZero.exp_log (localUnit_valuation_ne_zero K v u)]

@[simp] theorem localOrder_uniformizer (v : HeightOneSpectrum (𝓞 K)) :
    localOrderHom K v (localUniformizerUnit K v) = Multiplicative.ofAdd (1 : ℤ) := by
  change Multiplicative.ofAdd (-WithZero.log (Valued.v (localUniformizer K v))) = _
  rw [localUniformizer_valuation, WithZero.log_exp]
  rfl

@[simp] theorem localOrder_integralUnit (v : HeightOneSpectrum (𝓞 K))
    (u : (LocalIntegerRing K v)ˣ) :
    localOrderHom K v (localIntegerUnitsEmbedding K v u) = 1 := by
  have hv := (adicCompletionIntegers.mem_units_iff_valued_eq_one (K := K) (v := v)).mp
    (localIntegerUnitsEmbedding_mem K v u)
  change Multiplicative.ofAdd (-WithZero.log (Valued.v (localIntegerUnitsEmbedding K v u).val)) = _
  rw [hv, WithZero.log_one]
  rfl

theorem localOrderHom_surjective (v : HeightOneSpectrum (𝓞 K)) :
    Function.Surjective (localOrderHom K v) := by
  intro n
  refine ⟨localUniformizerUnit K v ^ Multiplicative.toAdd n, ?_⟩
  rw [map_zpow, localOrder_uniformizer]
  rw [← ofAdd_zsmul]
  simp

theorem isLocallyConstant_localOrder (v : HeightOneSpectrum (𝓞 K)) :
    IsLocallyConstant (localOrderHom K v) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro u
  have hn := (Units.continuous_val.continuousAt (x := u)).preimage_mem_nhds
    (Valued.locally_const (localUnit_valuation_ne_zero K v u))
  filter_upwards [hn] with w hw
  change Valued.v w.val = Valued.v u.val at hw
  simp only [localOrderHom, MonoidHom.coe_mk, OneHom.coe_mk, hw]

def localOrder (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →ₜ* Multiplicative ℤ where
  toMonoidHom := localOrderHom K v
  continuous_toFun := (isLocallyConstant_localOrder K v).continuous

theorem uniformizer_zpow_valuation (v : HeightOneSpectrum (𝓞 K)) (n : ℤ) :
    (Valued.v (localUniformizerUnit K v ^ n).val : WithZero (Multiplicative ℤ)) =
      WithZero.exp (-n) := by
  rw [localOrder_valuation, map_zpow, localOrder_uniformizer]
  simp [toAdd_zpow]

/-- Remove the exact uniformizer power from a local nonzero element. -/
def localUnitPartHom (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ where
  toFun u := u * (localUniformizerUnit K v ^ Multiplicative.toAdd (localOrder K v u))⁻¹
  map_one' := by simp
  map_mul' u w := by
    change (u * w) * (localUniformizerUnit K v ^
      Multiplicative.toAdd (localOrder K v (u * w)))⁻¹ = _
    rw [map_mul]
    simp only [toAdd_mul, zpow_add, mul_inv_rev]
    ac_rfl

theorem localUnitPartHom_valuation (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ) :
    (Valued.v (localUnitPartHom K v u).val : WithZero (Multiplicative ℤ)) = 1 := by
  change Valued.v (u * (localUniformizerUnit K v ^
    Multiplicative.toAdd (localOrder K v u))⁻¹).val = 1
  rw [Units.val_mul, Units.val_inv_eq_inv_val]
  rw [map_mul, map_inv₀, uniformizer_zpow_valuation]
  rw [localOrder_valuation]
  exact mul_inv_cancel₀ WithZero.exp_ne_zero

theorem localUnitPartHom_mem (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ) :
    localUnitPartHom K v u ∈ (v.adicCompletionIntegers K).units :=
  (adicCompletionIntegers.mem_units_iff_valued_eq_one (K := K) (v := v)).mpr
    (localUnitPartHom_valuation K v u)

theorem continuous_localUnitPartHom (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (localUnitPartHom K v) := by
  have hp : Continuous (fun n : Multiplicative ℤ =>
      localUniformizerUnit K v ^ Multiplicative.toAdd n) := continuous_of_discreteTopology
  exact continuous_id.mul ((hp.comp (localOrder K v).continuous).inv)

def localUnitPart (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →ₜ* (LocalIntegerRing K v)ˣ where
  toFun u := integerUnitOfLocalUnit K v (localUnitPartHom K v u) (localUnitPartHom_mem K v u)
  map_one' := by
    apply Units.ext
    apply Subtype.ext
    exact congrArg Units.val (map_one (localUnitPartHom K v))
  map_mul' u w := by
    apply Units.ext
    apply Subtype.ext
    exact congrArg Units.val (map_mul (localUnitPartHom K v) u w)
  continuous_toFun := by
    apply Units.continuous_iff.mpr
    constructor
    · exact (Units.continuous_val.comp (continuous_localUnitPartHom K v)).subtype_mk
        (fun u => (localUnitPartHom_mem K v u).1)
    · exact (Units.continuous_coe_inv.comp (continuous_localUnitPartHom K v)).subtype_mk
        (fun u => (localUnitPartHom_mem K v u).2)

@[simp] theorem localIntegerUnitsEmbedding_localUnitPart (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ) :
    localIntegerUnitsEmbedding K v (localUnitPart K v u) = localUnitPartHom K v u := by
  apply Units.ext
  rfl

theorem localUnit_decomposition (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ) :
    u = localIntegerUnitsEmbedding K v (localUnitPart K v u) *
      localUniformizerUnit K v ^ Multiplicative.toAdd (localOrder K v u) := by
  rw [localIntegerUnitsEmbedding_localUnitPart]
  change u = (u * (localUniformizerUnit K v ^ Multiplicative.toAdd (localOrder K v u))⁻¹) * _
  simp

@[simp] theorem localUnitPart_integralUnit (v : HeightOneSpectrum (𝓞 K))
    (u : (LocalIntegerRing K v)ˣ) :
    localUnitPart K v (localIntegerUnitsEmbedding K v u) = u := by
  apply Units.ext
  apply Subtype.ext
  change (localUnitPartHom K v (localIntegerUnitsEmbedding K v u)).val = (u.val : v.adicCompletion K)
  have ho : localOrder K v (localIntegerUnitsEmbedding K v u) = 1 := localOrder_integralUnit K v u
  calc
    _ = (localIntegerUnitsEmbedding K v u).val := by simp [localUnitPartHom, ho]
    _ = (u.val : v.adicCompletion K) := rfl

@[simp] theorem localUnitPart_uniformizer_zpow (v : HeightOneSpectrum (𝓞 K)) (n : ℤ) :
    localUnitPart K v (localUniformizerUnit K v ^ n) = 1 := by
  apply Units.ext
  apply Subtype.ext
  change (localUnitPartHom K v (localUniformizerUnit K v ^ n)).val = 1
  have ho : localOrder K v (localUniformizerUnit K v ^ n) = Multiplicative.ofAdd n := by
    rw [map_zpow]
    change (localOrderHom K v (localUniformizerUnit K v)) ^ n = _
    rw [localOrder_uniformizer]
    rw [← ofAdd_zsmul]
    simp
  simp [localUnitPartHom, ho]

end HeckeGeneral.Characters
