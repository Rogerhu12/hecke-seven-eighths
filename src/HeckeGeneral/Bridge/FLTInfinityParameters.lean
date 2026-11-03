import HeckeGeneral.Bridge.FLTDuality
import HeckeGeneral.Characters.InfinityPacket
import FLTReuse.M974319314547c0e9

/-!
# Identify the Tate infinity parameters with the actual Hecke parameters

The imported radial/angular conditions determine the same local frequencies
and complex weights already extracted from the continuous local characters.
In particular the complex-place normalization retains its factor two.

The actual real sign fixes its representative exponent in `{0,1}`, while
the complex weight is an integer. The proved Tate existence theorem is used
to identify these already constructed parameters, rather than add inputs.
-/

noncomputable section

namespace HeckeGeneral.Bridge

open NumberField HeckeGeneral.Characters
open NumberField.InfinitePlace.Completion
open scoped Classical

variable (F : Type) [Field F] [NumberField F]

theorem fltArchUnitHom_eq (v : InfinitePlace F) (u : v.Completionˣ) :
    NumberField.TateGlobal.archUnitHom v u = infiniteIdeleEmbedding F v u := by
  apply Units.ext
  rfl

theorem fltArchLocalChar_coe (χ : HeckeCharacter F) (v : InfinitePlace F)
    (u : v.Completionˣ) :
    ((NumberField.TateGlobal.archLocalChar (complexIdeleCharacter F χ) v u : ℂˣ) : ℂ) =
      (infiniteComponent F v χ u : ℂ) := by
  change (complexIdeleCharacter F χ (NumberField.TateGlobal.archUnitHom v u) : ℂ) = _
  rw [fltArchUnitHom_eq]
  rfl

theorem fltIdeleNorm_archUnitHom (v : InfinitePlace F) (u : v.Completionˣ) :
    NumberField.TateGlobal.ideleNorm F (NumberField.TateGlobal.archUnitHom v u) =
      ‖u.val‖ ^ v.mult := by
  rw [fltArchUnitHom_eq, fltIdeleNorm_eq, idelicNorm_infiniteIdeleEmbedding]

omit [NumberField F] in
theorem extensionEmbedding_complexUnits (v : InfinitePlace F) (hv : v.IsComplex) (z : ℂˣ) :
    extensionEmbedding v (complexUnitsToCompletion hv z).val = z.val := by
  change extensionEmbedding v ((ringEquivComplexOfIsComplex hv).symm z.val) = z.val
  rw [← ringEquivComplexOfIsComplex_apply hv, RingEquiv.apply_symm_apply]

omit [NumberField F] in
theorem extensionEmbedding_realUnits (v : InfinitePlace F) (hv : v.IsReal) (z : ℝˣ) :
    extensionEmbedding v (realUnitsToCompletion hv z).val = (z.val : ℂ) := by
  rw [← extensionEmbeddingOfIsReal_apply hv]
  change ((ringEquivRealOfIsReal hv ((ringEquivRealOfIsReal hv).symm z.val) : ℝ) : ℂ) = _
  rw [RingEquiv.apply_symm_apply]

theorem positiveReal_cpow_imaginary {r : ℝ} (hr : 0 < r) (t : ℝ) :
    (r : ℂ) ^ ((t : ℂ) * Complex.I) = (Circle.exp (t * Real.log r) : ℂ) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'),
    ← Complex.ofReal_log hr.le, Circle.coe_exp, Complex.ofReal_mul]
  congr 1
  ring

theorem heckeRealParameter_eq_flt {χ : HeckeCharacter F} {τ : InfinitePlace F → ℝ}
    (hτ : FLTArchRadialCondition F χ τ) (v : InfinitePlace F) (hv : v.IsReal) :
    heckeRealParameter F v hv χ = τ v := by
  apply (realFrequency_eq_iff _ _).mpr
  intro x
  have h := hτ v (realUnitsToCompletion hv (realRadialExponential (Multiplicative.ofAdd x)))
    (by simpa only [extensionEmbedding_realUnits, realRadialExponential_val,
      Complex.ofReal_re] using Real.exp_pos x)
    (by rw [extensionEmbedding_realUnits]; exact Complex.ofReal_im _)
  rw [fltArchLocalChar_coe, fltIdeleNorm_archUnitHom, norm_realUnitsToCompletion,
    realRadialExponential_val, Real.norm_eq_abs, abs_of_pos (Real.exp_pos x),
    hv.mult_eq_one, pow_one, positiveReal_cpow_imaginary (Real.exp_pos x), Real.log_exp] at h
  exact Circle.ext h

theorem heckeComplexParameter_eq_flt {χ : HeckeCharacter F} {τ : InfinitePlace F → ℝ}
    (hτ : FLTArchRadialCondition F χ τ) (v : InfinitePlace F) (hv : v.IsComplex) :
    heckeComplexParameter F v hv χ = τ v := by
  have hf : complexFrequency (complexHeckeComponent F v hv χ) = 2 * τ v := by
    apply (realFrequency_eq_iff _ _).mpr
    intro x
    have h := hτ v (complexUnitsToCompletion hv
      (complexRadialExponential (Multiplicative.ofAdd x)))
      (by simpa only [extensionEmbedding_complexUnits, complexRadialExponential_val,
        Complex.ofReal_re] using Real.exp_pos x)
      (by rw [extensionEmbedding_complexUnits, complexRadialExponential_val];
          exact Complex.ofReal_im _)
    rw [fltArchLocalChar_coe, fltIdeleNorm_archUnitHom, norm_complexUnitsToCompletion,
      norm_complexRadialExponential, hv.mult_eq_two,
      positiveReal_cpow_imaginary (sq_pos_of_pos (Real.exp_pos x)),
      Real.log_pow, Real.log_exp] at h
    apply Circle.ext
    change ((infiniteComponent F v χ)
      (complexUnitsToCompletion hv (complexRadialExponential (Multiplicative.ofAdd x))) : ℂ) =
        (Circle.exp ((2 * τ v) * x) : ℂ)
    exact h.trans (congrArg (fun r : ℝ => (Circle.exp r : ℂ)) (by ring))
  change complexFrequency (complexHeckeComponent F v hv χ) / 2 = τ v
  rw [hf]
  ring

theorem heckeRadialParameter_eq_flt {χ : HeckeCharacter F} {τ : InfinitePlace F → ℝ}
    (hτ : FLTArchRadialCondition F χ τ) : (fun v => heckeRadialParameter F v χ) = τ := by
  funext v
  by_cases hv : v.IsReal
  · rw [heckeRadialParameter_of_real F v hv, heckeRealParameter_eq_flt F hτ]
  · have hc := v.not_isReal_iff_isComplex.mp hv
    rw [heckeRadialParameter_of_complex F v hc, heckeComplexParameter_eq_flt F hτ]

theorem heckeComplexWeight_eq_flt {χ : HeckeCharacter F} {m : InfinitePlace F → ℤ}
    (hm : FLTArchAngularCondition F χ m) (v : InfinitePlace F) (hv : v.IsComplex) :
    heckeComplexWeight F v hv χ = m v := by
  apply (circleWeight_eq_iff _ _).mpr
  intro z
  have h := hm v (complexUnitsToCompletion hv (complexCircleEmbedding z))
    (by rw [extensionEmbedding_complexUnits]; exact Circle.norm_coe z)
  rw [fltArchLocalChar_coe, extensionEmbedding_complexUnits] at h
  apply Circle.ext
  change ((infiniteComponent F v χ)
    (complexUnitsToCompletion hv (complexCircleEmbedding z)) : ℂ) = (z : ℂ) ^ m v
  simpa only [complexCircleEmbedding_val] using h

/-- The real angular condition is the actual value of the character at `-1`.
Without the vendor's `m = 0 ∨ m = 1` restriction, it determines only parity. -/
theorem heckeRealSign_eq_flt {χ : HeckeCharacter F} {m : InfinitePlace F → ℤ}
    (hm : FLTArchAngularCondition F χ m) (v : InfinitePlace F) (hv : v.IsReal) :
    heckeRealSign F v hv χ = (-1 : Circle) ^ m v := by
  have h := hm v (realUnitsToCompletion hv (-1))
    (by rw [extensionEmbedding_realUnits]; simp)
  rw [fltArchLocalChar_coe, extensionEmbedding_realUnits] at h
  apply Circle.ext
  change ((infiniteComponent F v χ) (realUnitsToCompletion hv (-1)) : ℂ) =
    (-1 : ℂ) ^ m v
  simpa only [Units.val_neg, Units.val_one, Complex.ofReal_neg, Complex.ofReal_one,
    Circle.coe_zpow, Circle.coe_neg, Circle.coe_one] using h

/-- The canonical real-place exponent uses the existing character's sign. -/
def heckeRealParity (v : InfinitePlace F) (hv : v.IsReal) (χ : HeckeCharacter F) : ℤ :=
  if heckeRealSign F v hv χ = 1 then 0 else 1

theorem heckeRealParity_zero_or_one (v : InfinitePlace F) (hv : v.IsReal)
    (χ : HeckeCharacter F) :
    heckeRealParity F v hv χ = 0 ∨ heckeRealParity F v hv χ = 1 := by
  unfold heckeRealParity
  split_ifs <;> simp

theorem heckeRealSign_inv (v : InfinitePlace F) (hv : v.IsReal) (χ : HeckeCharacter F) :
    heckeRealSign F v hv χ⁻¹ = (heckeRealSign F v hv χ)⁻¹ := rfl

/-- The real sign exponent is unchanged by inversion, rather than negated
as an integer: it is the representative in `{0,1}` of a parity class. -/
theorem heckeRealParity_inv (v : InfinitePlace F) (hv : v.IsReal)
    (χ : HeckeCharacter F) : heckeRealParity F v hv χ⁻¹ = heckeRealParity F v hv χ := by
  simp only [heckeRealParity, heckeRealSign_inv, inv_eq_one]

/-- Restricting the real exponent to zero or one removes its parity ambiguity. -/
theorem heckeRealParity_eq_flt {χ : HeckeCharacter F} {m : InfinitePlace F → ℤ}
    (hm : FLTArchAngularCondition F χ m)
    (hmreal : ∀ v : InfinitePlace F, v.IsReal → m v = 0 ∨ m v = 1)
    (v : InfinitePlace F) (hv : v.IsReal) : heckeRealParity F v hv χ = m v := by
  have hs := heckeRealSign_eq_flt F hm v hv
  rcases hmreal v hv with h0 | h1
  · rw [h0, zpow_zero] at hs
    simp [heckeRealParity, hs, h0]
  · rw [h1, zpow_one] at hs
    have hn : heckeRealSign F v hv χ ≠ 1 := by
      intro heq
      have h := congrArg (fun z : Circle => (z : ℂ)) (hs.symm.trans heq)
      norm_num at h
    simp [heckeRealParity, hn, h1]

/-- A total archimedean weight assembled from actual real signs and complex weights. -/
def heckeArchWeight (χ : HeckeCharacter F) (v : InfinitePlace F) : ℤ :=
  if hv : v.IsReal then heckeRealParity F v hv χ
  else heckeComplexWeight F v (v.not_isReal_iff_isComplex.mp hv) χ

theorem heckeArchWeight_of_real (χ : HeckeCharacter F) (v : InfinitePlace F)
    (hv : v.IsReal) : heckeArchWeight F χ v = heckeRealParity F v hv χ := by
  simp only [heckeArchWeight, dite_eq_left hv]

theorem heckeArchWeight_of_complex (χ : HeckeCharacter F) (v : InfinitePlace F)
    (hv : v.IsComplex) : heckeArchWeight F χ v = heckeComplexWeight F v hv χ := by
  simp only [heckeArchWeight, dite_eq_right (v.not_isReal_iff_isComplex.mpr hv)]

/-- The Gamma shifts use absolute weights, which agree for the actual dual.
Real canonical parity is fixed, while complex angular weight changes sign. -/
theorem abs_heckeArchWeight_inv (χ : HeckeCharacter F) (v : InfinitePlace F) :
    |heckeArchWeight F χ⁻¹ v| = |heckeArchWeight F χ v| := by
  by_cases hv : v.IsReal
  · simp only [heckeArchWeight, dite_eq_left hv, heckeRealParity_inv]
  · simp only [heckeArchWeight, dite_eq_right hv, heckeComplexWeight_inv, abs_neg]

theorem heckeArchWeight_eq_flt {χ : HeckeCharacter F} {m : InfinitePlace F → ℤ}
    (hm : FLTArchAngularCondition F χ m)
    (hmreal : ∀ v : InfinitePlace F, v.IsReal → m v = 0 ∨ m v = 1) :
    heckeArchWeight F χ = m := by
  funext v
  by_cases hv : v.IsReal
  · rw [heckeArchWeight_of_real F χ v hv]
    exact heckeRealParity_eq_flt F hm hmreal v hv
  · have hc := v.not_isReal_iff_isComplex.mp hv
    rw [heckeArchWeight_of_complex F χ v hc]
    exact heckeComplexWeight_eq_flt F hm v hc

/-- The genuine FLT existence theorem supplies the conditions for the already
constructed Hecke parameters. There are no free analytic parameters or inputs. -/
theorem fltArchConditions_heckeParameters (χ : HeckeCharacter F) :
    FLTArchRadialCondition F χ (fun v => heckeRadialParameter F v χ) ∧
      FLTArchAngularCondition F χ (heckeArchWeight F χ) ∧
      (∀ v : InfinitePlace F, v.IsReal →
        heckeArchWeight F χ v = 0 ∨ heckeArchWeight F χ v = 1) := by
  obtain ⟨τ, m, hτ, hm, hmreal⟩ :=
    NumberField.TateGlobal.exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar F
      (complexIdeleCharacter F χ) (complexIdeleCharacter_isUnitary F χ)
      (continuous_complexIdeleCharacter_coe F χ)
  have hr : FLTArchRadialCondition F χ τ := hτ
  have ha : FLTArchAngularCondition F χ m := hm
  have ht := heckeRadialParameter_eq_flt F hr
  have hw := heckeArchWeight_eq_flt F ha hmreal
  rw [← ht] at hr
  rw [← hw] at ha hmreal
  exact ⟨hr, ha, hmreal⟩

/-- Pure norm twists have angular exponent zero at every infinite place. -/
theorem heckeArchWeight_normTwist (t : ℝ) : heckeArchWeight F (heckeNormTwist F t) = 0 := by
  funext v
  by_cases hv : v.IsReal
  · simp [heckeArchWeight, hv, heckeRealParity, heckeRealSign_normTwist]
  · simp [heckeArchWeight, hv, heckeComplexWeight_normTwist]

end HeckeGeneral.Bridge
