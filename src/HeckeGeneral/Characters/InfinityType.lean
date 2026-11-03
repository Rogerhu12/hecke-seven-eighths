import HeckeGeneral.Characters.InfiniteComponent
import HeckeGeneral.Characters.ComplexCharacter
import HeckeGeneral.Characters.RealUnitCharacter

/-!+# Infinity types of actual Hecke characters

The local completion is transported through Mathlib's isometric field
isomorphisms, then classified as a character of `ℝˣ` or `ℂˣ`. In particular,
the complex radial parameter below uses the normalized modulus `|z|²`.
The factor two in the ordinary radial frequency is proved, not suppressed.
-/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField InfinitePlace.Completion

section Coordinates

variable {K : Type*} [Field K] {v : InfinitePlace K}

def complexUnitsToCompletion (hv : v.IsComplex) : ℂˣ →ₜ* v.Completionˣ where
  toMonoidHom := Units.map (ringEquivComplexOfIsComplex hv).symm.toMonoidHom
  continuous_toFun := Units.continuous_map (isometryEquivComplexOfIsComplex hv).symm.continuous

def completionUnitsToComplex (hv : v.IsComplex) : v.Completionˣ →ₜ* ℂˣ where
  toMonoidHom := Units.map (ringEquivComplexOfIsComplex hv).toMonoidHom
  continuous_toFun := Units.continuous_map (isometryEquivComplexOfIsComplex hv).continuous

@[simp] theorem completionUnitsToComplex_inverse (hv : v.IsComplex) (z : ℂˣ) :
    completionUnitsToComplex hv (complexUnitsToCompletion hv z) = z := by
  apply Units.ext
  exact (ringEquivComplexOfIsComplex hv).apply_symm_apply z.val

@[simp] theorem complexUnitsToCompletion_inverse (hv : v.IsComplex) (u : v.Completionˣ) :
    complexUnitsToCompletion hv (completionUnitsToComplex hv u) = u := by
  apply Units.ext
  exact (ringEquivComplexOfIsComplex hv).symm_apply_apply u.val

theorem norm_complexUnitsToCompletion (hv : v.IsComplex) (z : ℂˣ) :
    ‖(complexUnitsToCompletion hv z).val‖ = ‖z.val‖ :=
  (isometryEquivComplexOfIsComplex hv).symm.isometry.norm_map_of_map_zero
    ((ringEquivComplexOfIsComplex hv).symm.map_zero) z.val

theorem norm_completionUnitsToComplex (hv : v.IsComplex) (u : v.Completionˣ) :
    ‖(completionUnitsToComplex hv u).val‖ = ‖u.val‖ :=
  (isometryEquivComplexOfIsComplex hv).isometry.norm_map_of_map_zero
    ((ringEquivComplexOfIsComplex hv).map_zero) u.val

def realUnitsToCompletion (hv : v.IsReal) : ℝˣ →ₜ* v.Completionˣ where
  toMonoidHom := Units.map (ringEquivRealOfIsReal hv).symm.toMonoidHom
  continuous_toFun := Units.continuous_map (isometryEquivRealOfIsReal hv).symm.continuous

def completionUnitsToReal (hv : v.IsReal) : v.Completionˣ →ₜ* ℝˣ where
  toMonoidHom := Units.map (ringEquivRealOfIsReal hv).toMonoidHom
  continuous_toFun := Units.continuous_map (isometryEquivRealOfIsReal hv).continuous

@[simp] theorem completionUnitsToReal_inverse (hv : v.IsReal) (z : ℝˣ) :
    completionUnitsToReal hv (realUnitsToCompletion hv z) = z := by
  apply Units.ext
  exact (ringEquivRealOfIsReal hv).apply_symm_apply z.val

@[simp] theorem realUnitsToCompletion_inverse (hv : v.IsReal) (u : v.Completionˣ) :
    realUnitsToCompletion hv (completionUnitsToReal hv u) = u := by
  apply Units.ext
  exact (ringEquivRealOfIsReal hv).symm_apply_apply u.val

theorem norm_realUnitsToCompletion (hv : v.IsReal) (z : ℝˣ) :
    ‖(realUnitsToCompletion hv z).val‖ = ‖z.val‖ :=
  (isometryEquivRealOfIsReal hv).symm.isometry.norm_map_of_map_zero
    ((ringEquivRealOfIsReal hv).symm.map_zero) z.val

theorem norm_completionUnitsToReal (hv : v.IsReal) (u : v.Completionˣ) :
    ‖(completionUnitsToReal hv u).val‖ = ‖u.val‖ :=
  (isometryEquivRealOfIsReal hv).isometry.norm_map_of_map_zero
    ((ringEquivRealOfIsReal hv).map_zero) u.val

end Coordinates

variable (K : Type*) [Field K] [NumberField K]

/-- A genuine complex local Hecke character in the standard complex coordinate. -/
def complexHeckeComponent (v : InfinitePlace K) (hv : v.IsComplex) (χ : HeckeCharacter K) :
    UnitaryCharacter ℂˣ := pullback (complexUnitsToCompletion hv) (infiniteComponent K v χ)

/-- A genuine real local Hecke character in the standard real coordinate. -/
def realHeckeComponent (v : InfinitePlace K) (hv : v.IsReal) (χ : HeckeCharacter K) :
    UnitaryCharacter ℝˣ := pullback (realUnitsToCompletion hv) (infiniteComponent K v χ)

def heckeComplexWeight (v : InfinitePlace K) (hv : v.IsComplex) (χ : HeckeCharacter K) : ℤ :=
  complexWeight (complexHeckeComponent K v hv χ)

/-- Frequency with respect to the normalized local modulus, the squared ordinary norm. -/
def heckeComplexParameter (v : InfinitePlace K) (hv : v.IsComplex) (χ : HeckeCharacter K) : ℝ :=
  complexFrequency (complexHeckeComponent K v hv χ) / 2

def heckeRealParameter (v : InfinitePlace K) (hv : v.IsReal) (χ : HeckeCharacter K) : ℝ :=
  realUnitFrequency (realHeckeComponent K v hv χ)

def heckeRealSign (v : InfinitePlace K) (hv : v.IsReal) (χ : HeckeCharacter K) : Circle :=
  realUnitSign (realHeckeComponent K v hv χ)

/-- The complex completion's actual character, expressed in normalized local parameters. -/
theorem heckeComplexComponent_formula (v : InfinitePlace K) (hv : v.IsComplex)
    (χ : HeckeCharacter K) (z : ℂˣ) :
    complexHeckeComponent K v hv χ z = complexPhase z ^ heckeComplexWeight K v hv χ *
      Circle.exp (heckeComplexParameter K v hv χ * Real.log (‖z.val‖ ^ 2)) := by
  rw [complexCharacter_formula (complexHeckeComponent K v hv χ) z]
  unfold heckeComplexWeight heckeComplexParameter
  rw [Real.log_pow]
  congr 2
  push_cast
  ring

theorem heckeRealComponent_formula (v : InfinitePlace K) (hv : v.IsReal)
    (χ : HeckeCharacter K) (z : ℝˣ) :
    realHeckeComponent K v hv χ z = (if 0 < z.val then 1 else heckeRealSign K v hv χ) *
      Circle.exp (heckeRealParameter K v hv χ * Real.log |z.val|) :=
  realCharacter_formula (realHeckeComponent K v hv χ) z

theorem finiteOrder_complexHeckeComponent (v : InfinitePlace K) (hv : v.IsComplex)
    {χ : HeckeCharacter K} (hχ : FiniteOrder χ) : complexHeckeComponent K v hv χ = 1 := by
  apply (finiteOrder_complexCharacter_iff _).mp
  exact finiteOrder_pullback _ (finiteOrder_pullback _ hχ)

theorem heckeComplexWeight_finiteOrder (v : InfinitePlace K) (hv : v.IsComplex)
    {χ : HeckeCharacter K} (hχ : FiniteOrder χ) : heckeComplexWeight K v hv χ = 0 := by
  unfold heckeComplexWeight
  rw [finiteOrder_complexHeckeComponent K v hv hχ, complexWeight_one]

theorem heckeComplexParameter_finiteOrder (v : InfinitePlace K) (hv : v.IsComplex)
    {χ : HeckeCharacter K} (hχ : FiniteOrder χ) : heckeComplexParameter K v hv χ = 0 := by
  unfold heckeComplexParameter
  rw [finiteOrder_complexHeckeComponent K v hv hχ, complexFrequency_one, zero_div]

theorem heckeRealParameter_finiteOrder (v : InfinitePlace K) (hv : v.IsReal)
    {χ : HeckeCharacter K} (hχ : FiniteOrder χ) : heckeRealParameter K v hv χ = 0 :=
  (finiteOrder_realUnitCharacter_iff _).mp (finiteOrder_pullback _ (finiteOrder_pullback _ hχ))

theorem heckeRealSign_sq (v : InfinitePlace K) (hv : v.IsReal) (χ : HeckeCharacter K) :
    heckeRealSign K v hv χ ^ 2 = 1 := realUnitSign_sq _

/-- Global norm twists are angularly trivial, including at complex places. -/
theorem heckeComplexWeight_normTwist (v : InfinitePlace K) (hv : v.IsComplex) (t : ℝ) :
    heckeComplexWeight K v hv (heckeNormTwist K t) = 0 := by
  apply (circleWeight_eq_iff _ _).mpr
  intro z
  change infiniteComponent K v (heckeNormTwist K t)
    (complexUnitsToCompletion hv (complexCircleEmbedding z)) = z ^ (0 : ℤ)
  rw [heckeNormTwist_infinite, norm_complexUnitsToCompletion, norm_complexCircleEmbedding]
  simp

theorem heckeComplexFrequency_normTwist (v : InfinitePlace K) (hv : v.IsComplex) (t : ℝ) :
    complexFrequency (complexHeckeComponent K v hv (heckeNormTwist K t)) = -2 * t := by
  apply (realFrequency_eq_iff _ _).mpr
  intro x
  change infiniteComponent K v (heckeNormTwist K t)
    (complexUnitsToCompletion hv (complexRadialExponential (Multiplicative.ofAdd x))) = _
  rw [heckeNormTwist_infinite, norm_complexUnitsToCompletion,
    norm_complexRadialExponential, Real.log_exp, hv.mult_eq_two]
  congr 1
  push_cast
  ring

/-- One global norm twist subtracts the same normalized parameter at every complex place. -/
theorem heckeComplexParameter_normTwist (v : InfinitePlace K) (hv : v.IsComplex) (t : ℝ) :
    heckeComplexParameter K v hv (heckeNormTwist K t) = -t := by
  unfold heckeComplexParameter
  rw [heckeComplexFrequency_normTwist]
  ring

theorem heckeRealParameter_normTwist (v : InfinitePlace K) (hv : v.IsReal) (t : ℝ) :
    heckeRealParameter K v hv (heckeNormTwist K t) = -t := by
  apply (realFrequency_eq_iff _ _).mpr
  intro x
  change infiniteComponent K v (heckeNormTwist K t)
    (realUnitsToCompletion hv (realRadialExponential (Multiplicative.ofAdd x))) = _
  rw [heckeNormTwist_infinite, norm_realUnitsToCompletion, realRadialExponential_val,
    Real.norm_of_nonneg (Real.exp_pos x).le, Real.log_exp, hv.mult_eq_one]
  congr 1
  push_cast
  ring

theorem heckeRealSign_normTwist (v : InfinitePlace K) (hv : v.IsReal) (t : ℝ) :
    heckeRealSign K v hv (heckeNormTwist K t) = 1 := by
  change infiniteComponent K v (heckeNormTwist K t) (realUnitsToCompletion hv (-1)) = 1
  rw [heckeNormTwist_infinite, norm_realUnitsToCompletion]
  simp

end HeckeGeneral.Characters
