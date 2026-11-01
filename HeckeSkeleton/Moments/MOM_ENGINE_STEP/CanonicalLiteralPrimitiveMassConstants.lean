import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitiveMassCoefficient
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AmplifiedFiniteIndex

/-!
# Fixed constants for the actual primitive mass estimate

The contour and coefficient below are selected from the numerical
profile theorem before a scale, row, common ideal or source is given.
The harmonic constants are selected from the original finite arithmetic
carriers.  Their specifications are proved here, rather than supplied
as completed source or family estimates.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPrimitiveMassConstants

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums HeckeGeneral.Characters
open CommonSupportMass CanonicalLiteralPrimitiveMassCoefficient

variable (K : Type) [Field K] [NumberField K]
variable (A : SArithmeticData K) (σ : K →+* ℂ) (ω ψ : HeckeCharacter K)
variable (cap d heightDegree : ℕ) (annulus lo hi : ℝ)
variable (hlo : 0 < lo) (hhi : 1 ≤ hi) (hannulus : 0 ≤ annulus)
variable (lengthBound ε : ℝ) (hbound : 0 ≤ lengthBound) (hε : 0 < ε)
variable (orders : Finset (ℕ × ℕ)) (mesh heightConstant widthBound : ℝ)
variable (hwidth : 0 ≤ widthBound)
variable (unitIndex firstKernel secondKernel : ℝ)
variable (hunit : 0 ≤ unitIndex) (hfirst : 0 ≤ firstKernel) (hsecond : 0 ≤ secondKernel)

local notation "existence" => exists_uniform_product K A σ ω ψ
  cap d heightDegree annulus lo hi hlo hhi hannulus lengthBound ε hbound hε
  orders mesh heightConstant widthBound hwidth unitIndex firstKernel secondKernel
  hunit hfirst hsecond

def contour : ℝ := Classical.choose existence

def coefficient : ℝ := Classical.choose (Classical.choose_spec existence)

local notation "selectedContour" => contour K A σ ω ψ
  cap d heightDegree annulus lo hi hlo hhi hannulus lengthBound ε hbound hε
  orders mesh heightConstant widthBound hwidth unitIndex firstKernel secondKernel
  hunit hfirst hsecond
local notation "selectedCoefficient" => coefficient K A σ ω ψ
  cap d heightDegree annulus lo hi hlo hhi hannulus lengthBound ε hbound hε
  orders mesh heightConstant widthBound hwidth unitIndex firstKernel secondKernel
  hunit hfirst hsecond

theorem contour_pos : 0 < selectedContour :=
  (Classical.choose_spec (Classical.choose_spec existence)).1

theorem contour_le : selectedContour ≤ 1 / 4 :=
  (Classical.choose_spec (Classical.choose_spec existence)).2.1

theorem coefficient_pos : 0 < selectedCoefficient :=
  (Classical.choose_spec (Classical.choose_spec existence)).2.2.1

/-- The bound of the fixed choice applies to every original numerical
window.  Its contour is the one used to construct the actual children. -/
theorem coefficient_bound
    (Z T width height control originalBound error m total mask active moving : ℝ)
    (hZ : 1 ≤ Z) (hT : 0 ≤ T) (hbox : width ≤ widthBound)
    (hheight : height ≤ heightConstant * (1 + Real.log Z) * (1 + T) ^ heightDegree)
    (hcontrol : 1 + T ≤ control) (hB : 0 ≤ originalBound)
    (hBbound : originalBound ≤ control ^ d) (hm : 0 ≤ m)
    (htotal : total ≤ lengthBound) (hmask : mask ≤ lengthBound)
    (hactive : active ≤ lengthBound) :
    let η := CanonicalLiteralCombinedMassCoefficient.mellinTilt lengthBound ε
    kernelCoefficient K A σ ω ψ cap orders lo hi hlo η η selectedContour mesh
        Z height width originalBound firstKernel secondKernel *
      indexCoefficient K cap annulus originalBound unitIndex
        Z error mesh m total mask active η η moving ≤
      selectedCoefficient * control ^ CanonicalLiteralPassiveMassCoefficient.degree
        cap d 0 0 0 heightDegree * Z ^ (ε + 5 * error / 3 + mesh) * Z ^ moving :=
  (Classical.choose_spec (Classical.choose_spec existence)).2.2.2
    Z T width height control originalBound error m total mask active moving
    hZ hT hbox hheight hcontrol hB hBbound hm htotal hmask hactive

section Harmonic

variable (normBox harmonicLoss : ℝ) (hbox : 0 ≤ normBox) (hloss : 0 < harmonicLoss)

def directHarmonicConstant : ℝ :=
  Classical.choose (TwoDivisorCommonBranch.uniform_index_mass (K := K)
    (cap + 2) normBox harmonicLoss hbox hloss)

theorem directHarmonicConstant_pos :
    0 < directHarmonicConstant K cap normBox harmonicLoss hbox hloss :=
  (Classical.choose_spec (TwoDivisorCommonBranch.uniform_index_mass (K := K)
    (cap + 2) normBox harmonicLoss hbox hloss)).1

/-- The compulsory old divisor is the unit.  The complete deletion
mask stays in the original source and is not asserted to divide a column. -/
theorem direct_harmonic_sum (Z : ℝ) (hZ : 1 ≤ Z)
    (b : TwoDivisorCommonBranch (K := K))
    (hb : b.Admissible (cap + 2) normBox Z 1)
    {I : Type*} [Fintype I] (index : I → b.Index) (multiplicity : ℝ)
    (hmultiplicity : 0 ≤ multiplicity)
    (hcard : ∀ j, ((Finset.univ.filter (fun i => index i = j)).card : ℝ) ≤ multiplicity) :
    (∑ i : I, b.indexWeight (index i)) ≤
      multiplicity * directHarmonicConstant K cap normBox harmonicLoss hbox hloss *
        Z ^ harmonicLoss := by
  have h := (Classical.choose_spec (TwoDivisorCommonBranch.uniform_index_mass (K := K)
    (cap + 2) normBox harmonicLoss hbox hloss)).2
      Z hZ 1 (by simp) one_ne_zero b hb index multiplicity hmultiplicity hcard
  simpa only [map_one, Nat.cast_one, div_one] using h

variable (ell poolLoss rowBound frozenBound : ℝ)
variable (hell : 0 < ell) (hpoolLoss : 0 < poolLoss) (hpoolSmall : poolLoss < ell)
variable (hrow : 0 ≤ rowBound) (hfrozen : 0 ≤ frozenBound)

local notation "poolExistence" => amplified_finite_index_mass (A := A)
  (cap + 2) normBox harmonicLoss ell poolLoss rowBound frozenBound
  hbox hloss hell hpoolLoss hpoolSmall hrow hfrozen

def pooledHarmonicConstant : ℝ := Classical.choose poolExistence

def pooledThreshold : ℝ := Classical.choose (Classical.choose_spec poolExistence)

local notation "poolConstant" => pooledHarmonicConstant K A cap normBox harmonicLoss
  hbox hloss ell poolLoss rowBound frozenBound hell hpoolLoss hpoolSmall hrow hfrozen
local notation "poolThreshold" => pooledThreshold K A cap normBox harmonicLoss
  hbox hloss ell poolLoss rowBound frozenBound hell hpoolLoss hpoolSmall hrow hfrozen

theorem pooledHarmonicConstant_pos : 0 < poolConstant :=
  (Classical.choose_spec (Classical.choose_spec poolExistence)).1

theorem pooledThreshold_one_lt : 1 < poolThreshold :=
  (Classical.choose_spec (Classical.choose_spec poolExistence)).2.1

theorem pooled_harmonic_sum (Z : ℝ) (hZ : poolThreshold ≤ Z)
    (bad : Finset (HeightOneSpectrum (𝓞 K)))
    (P : PowerScaleExteriorPool A bad Z ell poolLoss)
    (main : TwoDivisorCommonBranch (K := K))
    (hmain : main.Admissible (cap + 2) normBox Z 1)
    (error : ℕ → ExteriorPrime A → TwoDivisorCommonBranch (K := K))
    (herror : ∀ n ∈ ({1, 6, 7} : Finset ℕ), ∀ p ∈ P.primes,
      (error n p).Admissible (cap + 2) normBox Z 1) :
    (∑ i : AmplifiedCommonIndex P main error,
      amplifiedIndexWeight P rowBound frozenBound main error i) ≤
        poolConstant * Z ^ (harmonicLoss + poolLoss) := by
  have h := (Classical.choose_spec (Classical.choose_spec poolExistence)).2.2
    Z hZ bad P rowBound frozenBound hrow le_rfl le_rfl
    1 (by simp) one_ne_zero main hmain error herror
  simpa only [map_one, Nat.cast_one, div_one] using h

end Harmonic
end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPrimitiveMassConstants

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPrimitiveMassConstants.coefficient_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPrimitiveMassConstants.direct_harmonic_sum
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPrimitiveMassConstants.pooled_harmonic_sum
