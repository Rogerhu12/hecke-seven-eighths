import HeckeSkeleton.ThetaLocal.ComplexRootPowers
import HeckeSkeleton.ThetaLocal.HighestHarmonicRoot
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
Weyl interchange of the actual two root strings.

The proof uses the explicit highest harmonic in the local principal-series
model.  Right multiplication by the swap Weyl matrix conjugates its angular
coordinate.  Conjugating the real-variable derivatives gives the opposite
root recursion with the same scalar coefficients.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace HeckeSkeleton.ThetaLocal

open DedekindZetaZeroFree
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxActualImage
open KPCplxRootDerivativeVectors KPCplxBessel KPCplxIntertwinerEigenvalues
open KPCplxHarmonicPropagation.RaisingCalculation
open HarmonicCalculation

local notation "Mat" => Matrix (Fin 2) (Fin 2) ℂ

private theorem rowB_weyl (g : ComplexGL2) : rowB (g * weyl) = rowB g := by
  simp [rowB, Matrix.GeneralLinearGroup.coe_mul, weyl, Matrix.mul_apply,
    Fin.sum_univ_two, add_comm]

private theorem rowW_weyl (g : ComplexGL2) : rowW (g * weyl) = star (rowW g) := by
  simp [rowW, rowB, Matrix.GeneralLinearGroup.coe_mul, weyl, Matrix.mul_apply,
    Fin.sum_univ_two, Complex.star_def, map_div₀, mul_comm, mul_left_comm, mul_assoc,
    add_comm]

private theorem norm_det_weyl (g : ComplexGL2) :
    ‖((g * weyl : ComplexGL2) : Mat).det‖ = ‖(g : Mat).det‖ := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, norm_mul]
  have hw : ‖((weyl : ComplexGL2) : Mat).det‖ = 1 := by
    norm_num [weyl, Matrix.det_fin_two]
  rw [hw, mul_one]

theorem harmonicSection_weyl (s : ℝ) (n : ℕ) (g : ComplexGL2) :
    harmonicSection s n (g * weyl) = star (harmonicSection s n g) := by
  change (Real.rpow
      (‖((g * weyl : ComplexGL2) : Mat).det‖ / rowB (g * weyl)) (1 + 2 * s) : ℂ) *
      rowW (g * weyl) ^ n =
    star ((Real.rpow (‖(g : Mat).det‖ / rowB g) (1 + 2 * s) : ℂ) * rowW g ^ n)
  rw [norm_det_weyl, rowB_weyl, rowW_weyl]
  simp [star_mul, star_pow, Complex.star_def, mul_comm]

/-- The explicit lowest harmonic, obtained by the actual Weyl action. -/
def lowestImage (β : ℂˣ) (n : ℕ) : Theta β :=
  imageAction β (Matrix.ProjGenLinGroup.mk weyl) (highestImage β n)

theorem lowestImage_apply (β : ℂˣ) (n : ℕ) (g : ComplexGL2) :
    (lowestImage β n : PrincipalSeries negativeParameter) g =
      star (harmonicSection negativeParameter n g) := by
  change harmonicSection negativeParameter n (g * weyl) = _
  exact harmonicSection_weyl negativeParameter n g

theorem lowestImage_zero (β : ℂˣ) : lowestImage β 0 = highestImage β 0 := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  rw [lowestImage_apply]
  change star ((Real.rpow (‖(g : Mat).det‖ / rowB g)
      (1 + 2 * negativeParameter) : ℂ) * rowW g ^ 0) =
    (Real.rpow (‖(g : Mat).det‖ / rowB g)
      (1 + 2 * negativeParameter) : ℂ) * rowW g ^ 0
  simp [Complex.star_def]

/-- The antiholomorphic root raises the lowest string with the same real scalar. -/
theorem lowestImage_upper (β : ℂˣ) (n : ℕ) :
    dPiComplexUpperRoot β Z_minus (lowestImage β n) =
      (-((n : ℂ) + (2 / 3 : ℂ)) / 2) • lowestImage β (n + 1) := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  have hd (z : ℂ) :
      deriv (fun t : ℝ => (lowestImage β n : PrincipalSeries negativeParameter)
        (g * upperUnipotent ((t : ℂ) * z))) 0 =
      star (deriv (fun t : ℝ => harmonicSection negativeParameter n
        (g * upperUnipotent ((t : ℂ) * z))) 0) := by
    simp_rw [lowestImage_apply]
    exact deriv.star
  change Z_minus.1 * deriv (fun t : ℝ =>
      (lowestImage β n : PrincipalSeries negativeParameter)
        (g * upperUnipotent ((t : ℂ) * 1))) 0 +
    Z_minus.2 * deriv (fun t : ℝ =>
      (lowestImage β n : PrincipalSeries negativeParameter)
        (g * upperUnipotent ((t : ℂ) * Complex.I))) 0 =
      (-((n : ℂ) + (2 / 3 : ℂ)) / 2) *
        (lowestImage β (n + 1) : PrincipalSeries negativeParameter) g
  rw [hd 1, hd Complex.I, lowestImage_apply]
  have hp := congrArg
    (fun h : Theta β => (h : PrincipalSeries negativeParameter) g)
    (highestImage_upper β n)
  change Z_plus.1 * deriv (fun t : ℝ => harmonicSection negativeParameter n
      (g * upperUnipotent ((t : ℂ) * 1))) 0 +
    Z_plus.2 * deriv (fun t : ℝ => harmonicSection negativeParameter n
      (g * upperUnipotent ((t : ℂ) * Complex.I))) 0 =
      (-((n : ℂ) + (2 / 3 : ℂ)) / 2) *
        harmonicSection negativeParameter (n + 1) g at hp
  have hs := congrArg star hp
  simpa [Z_plus, Z_minus, E_R, E_I, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, Complex.star_def, map_add, map_mul, map_div₀,
    mul_comm, mul_left_comm, mul_assoc] using hs

theorem dPiComplexUpperRoot_smul (β : ℂˣ) (X : ComplexifiedUpperRoot)
    (a : ℂ) (h : Theta β) :
    dPiComplexUpperRoot β X (a • h) = a • dPiComplexUpperRoot β X h := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  change X.1 * deriv (fun t : ℝ => a * (h : PrincipalSeries negativeParameter)
      (g * upperUnipotent ((t : ℂ) * 1))) 0 +
    X.2 * deriv (fun t : ℝ => a * (h : PrincipalSeries negativeParameter)
      (g * upperUnipotent ((t : ℂ) * Complex.I))) 0 =
    a * (X.1 * deriv (fun t : ℝ => (h : PrincipalSeries negativeParameter)
      (g * upperUnipotent ((t : ℂ) * 1))) 0 +
    X.2 * deriv (fun t : ℝ => (h : PrincipalSeries negativeParameter)
      (g * upperUnipotent ((t : ℂ) * Complex.I))) 0)
  rw [deriv_const_mul_field, deriv_const_mul_field]
  ring

/-- The common scalar coefficients of the two normalized root strings. -/
def rootStringCoefficient (c : ℝ) (β : ℂˣ) : ℕ → ℂ
  | 0 => ((KPCplxPlanarKernel.besselCoefficient c : ℂ)⁻¹) *
      (3 * characterScale β / 2 : ℂ)
  | n + 1 => (2 / (Complex.I * (c : ℂ))) * rootStringCoefficient c β n *
      (-((n : ℂ) + (2 / 3 : ℂ)) / 2)

theorem vZero_eq_highestImage (c : ℝ) (β : ℂˣ) :
    vZero c β = rootStringCoefficient c β 0 • highestImage β 0 := by
  have hzero : (highestImage β 0 : PrincipalSeries negativeParameter) =
      sphericalSection negativeParameter := by
    apply Subtype.ext
    funext g
    change sphericalSection negativeParameter g * rowW g ^ 0 =
      sphericalSection negativeParameter g
    simp
  apply Subtype.ext
  change ((KPCplxPlanarKernel.besselCoefficient c : ℂ)⁻¹) •
      (intertwinerToImage β (sphericalSection positiveParameter) :
        PrincipalSeries negativeParameter) =
    rootStringCoefficient c β 0 • (highestImage β 0 : PrincipalSeries negativeParameter)
  rw [(spherical_image β).1, hzero, smul_smul]
  rfl

theorem higherPlus_eq_highestImage (c : ℝ) (β : ℂˣ) (n : ℕ) :
    higherPlus c β n = rootStringCoefficient c β n • highestImage β n := by
  unfold higherPlus
  induction n with
  | zero => exact vZero_eq_highestImage c β
  | succ n ih =>
    rw [rootIterate, ih]
    simp only [normalizedRootPlus, dPiComplexUpperRoot_smul,
      highestImage_upper, smul_smul, rootStringCoefficient, mul_assoc]

theorem higherMinus_eq_lowestImage (c : ℝ) (β : ℂˣ) (n : ℕ) :
    higherMinus c β n = rootStringCoefficient c β n • lowestImage β n := by
  unfold higherMinus
  induction n with
  | zero =>
    rw [lowestImage_zero]
    exact vZero_eq_highestImage c β
  | succ n ih =>
    rw [rootIterate, ih]
    simp only [normalizedRootMinus, dPiComplexUpperRoot_smul,
      lowestImage_upper, smul_smul, rootStringCoefficient, mul_assoc]

/-- Actual Weyl interchange for every nonnegative angular weight. -/
theorem weyl_higherPlus (c : ℝ) (β : ℂˣ) (n : ℕ) :
    imageAction β (Matrix.ProjGenLinGroup.mk weyl) (higherPlus c β n) =
      higherMinus c β n := by
  rw [higherPlus_eq_highestImage, imageAction_smul, higherMinus_eq_lowestImage]
  rfl

private theorem weyl_squared (β : ℂˣ) (h : Theta β) :
    imageAction β (Matrix.ProjGenLinGroup.mk weyl)
      (imageAction β (Matrix.ProjGenLinGroup.mk weyl) h) = h := by
  have hw : (weyl : ComplexGL2) * weyl = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [weyl, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.one_apply]
  apply Subtype.ext
  apply Subtype.ext
  funext g
  change (h : PrincipalSeries negativeParameter) ((g * weyl) * weyl) =
    (h : PrincipalSeries negativeParameter) g
  rw [mul_assoc, hw, mul_one]

/-- Actual Weyl interchange for every nonpositive angular weight. -/
theorem weyl_higherMinus (c : ℝ) (β : ℂˣ) (n : ℕ) :
    imageAction β (Matrix.ProjGenLinGroup.mk weyl) (higherMinus c β n) =
      higherPlus c β n := by
  rw [← weyl_higherPlus c β n, weyl_squared]

/-- The actual root vector for an arbitrary integer angular weight. -/
def archRootVector (c : ℝ) (β : ℂˣ) : ℤ → Theta β
  | .ofNat n => higherPlus c β n
  | .negSucc n => higherMinus c β (n + 1)

/-- `π(w) φ_m = φ_{-m}` in the actual complex local theta representation. -/
theorem weyl_archRootVector (c : ℝ) (β : ℂˣ) (m : ℤ) :
    imageAction β (Matrix.ProjGenLinGroup.mk weyl) (archRootVector c β m) =
      archRootVector c β (-m) := by
  cases m with
  | ofNat n =>
    cases n with
    | zero =>
      change imageAction β (Matrix.ProjGenLinGroup.mk weyl) (higherPlus c β 0) =
        higherPlus c β 0
      rw [weyl_higherPlus]
      rfl
    | succ n =>
      change imageAction β (Matrix.ProjGenLinGroup.mk weyl) (higherPlus c β (n + 1)) =
        higherMinus c β (n + 1)
      exact weyl_higherPlus c β (n + 1)
  | negSucc n =>
    change imageAction β (Matrix.ProjGenLinGroup.mk weyl) (higherMinus c β (n + 1)) =
      higherPlus c β (n + 1)
    exact weyl_higherMinus c β (n + 1)

/-- The Whittaker value with a single integer angular power. -/
theorem whittaker_archRootVector (c : ℝ) (hc : 0 < c)
    (β : ℂˣ) (hβ : (β : ℂ) = (c : ℂ)) (m : ℤ) (y : ℂˣ) :
    whittakerValue β (archRootVector c β m) y =
      ((radius y ^ (m.natAbs + 1) : ℝ) : ℂ) * omegaPlus y ^ m *
        (besselKThird (c * radius y) : ℂ) := by
  cases m with
  | ofNat n =>
    change whittakerValue β (higherPlus c β n) y =
      ((radius y ^ (n + 1) : ℝ) : ℂ) * omegaPlus y ^ (n : ℤ) *
        (besselKThird (c * radius y) : ℂ)
    rw [zpow_natCast]
    exact whittaker_higherPlus_polar c hc β hβ n y
  | negSucc n =>
    simpa only [archRootVector, Int.natAbs_negSucc, zpow_negSucc,
      omegaMinus_eq_inv, inv_pow] using
      whittaker_higherMinus_polar c hc β hβ (n + 1) y

#print axioms lowestImage_upper
#print axioms higherPlus_eq_highestImage
#print axioms higherMinus_eq_lowestImage
#print axioms weyl_higherPlus
#print axioms weyl_higherMinus
#print axioms weyl_archRootVector
#print axioms whittaker_archRootVector

end HeckeSkeleton.ThetaLocal
