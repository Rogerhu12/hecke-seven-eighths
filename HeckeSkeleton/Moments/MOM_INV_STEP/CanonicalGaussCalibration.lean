import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalIdealRow
import HeckeSkeleton.Moments.MOM_INV_STEP.PrimitiveFourier
import HeckeSkeleton.Moments.MOM_INV_STEP.GaussConjugation

/-!
# Explicit finite MOM_BASE calibration and the actual residual columns

The input below contains only identities of actual finite Gauss sums.
Its mixed-digit formula specifies every local character, prime generator
and cross-symbol. Its homogeneous specialization uses the repository's
literal `thetaGamma`. It contains no Poisson formula, kernel identity or
energy estimate. This is the finite coefficient boundary supplied by
MOM_BASE under the task group's parallel-dependency rule.

The consequences retain the exact selected generators and the zeros of
the character row. They prove the fourth-power label in multiplication
of a₀, the first coefficient cycle on an extracted source column, and the
simultaneous cube-label and dual-dilation identity with J and q₀.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalGaussCalibration

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.Analysis
open ActualFiniteSource ConductorMasks PrimitivePoissonSource PrimitiveFourier
open CubeAlgebra
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "E" => CanonicalIdealRow.exteriorMonoid K S
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

local instance principalQuotientFinite (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) :
    Finite (PrincipalQuotient K S D B t) :=
  finite_sIntegerPrincipalResidue K Sset (primitiveModulus K S D B t)
    (primitiveModulus_ne_zero K S D B t)

local instance principalQuotientFintype (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) :
    Fintype (PrincipalQuotient K S D B t) := Fintype.ofFinite _

def activePrimeExterior (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (p : activeSupport B.support t) : Ext :=
  exteriorPrimeIdeal K Sset
    ⟨p.val, B.outside p.val (Finset.mem_filter.mp p.property).1⟩

/-- The complete canonical-generator finite CRT product. The diagonal
cross factor is one, and all off-diagonal factors are explicitly kept. -/
def canonicalPrimeGaussProduct (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) : ℂ :=
  ∏ p : activeSupport B.support t,
    thetaGamma K Sset D (activePrimeExterior K S B t p) (t p.val).val *
      ∏ q : activeSupport B.support t, if q = p then 1 else
        idealSymbol K Sset D (activePrimeExterior K S B t p)
          (D.generator (activePrimeExterior K S B t q)) ^ (t p.val).val

/-- An explicit finite-arithmetic MOM_BASE dependency. Both sides of
each field are actual normalized finite Gauss sums or their displayed
canonical CRT factors; no analytic or energy conclusion is a field. -/
structure FiniteGaussCRTInput : Prop where
  primitive_crt : ∀ (B : PrimeBlock K Sset)
      (t : HeightOneSpectrum (𝓞 K) → ZMod 6),
    normalizedPrimitiveGauss K S D B t = canonicalPrimeGaussProduct K S D B t
  homogeneous_product : ∀ (I J : Ext), IsCoprime I.val.val J.val.val →
    ∀ j : ℕ, 0 < j → j < 6 →
      thetaGamma K Sset D (exteriorMul K Sset I J) j =
        thetaGamma K Sset D I j * thetaGamma K Sset D J j *
          idealSymbol K Sset D I (D.generator J) ^ j *
          idealSymbol K Sset D J (D.generator I) ^ j

variable (hcrt : FiniteGaussCRTInput K S D)

include hcrt

/-- The mixed-digit input can be read literally as a sum over the actual
principal quotient. This is the finite sum used in the proved Poisson
packet, with its own generator-dependent additive phase. -/
theorem primitive_finite_sum (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) :
    (Real.sqrt ((primitiveIdeal B.support t).absNorm : ℝ) : ℂ)⁻¹ *
      (∑ q : PrincipalQuotient K S D B t, primitiveCoefficient K S D B t q *
        sIntegerActualModulusAddCharacter K Sset D.different_outside
          (primitiveModulus K S D B t) (primitiveModulus_ne_zero K S D B t) q) =
      canonicalPrimeGaussProduct K S D B t := by
  simpa only [normalizedPrimitiveGauss, primitiveGauss_eq_sum, div_eq_mul_inv, mul_comm]
    using hcrt.primitive_crt B t

variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)

include hallowed

/-- Reciprocity combines the two genuine finite cross-symbols into
the doubled power of the same actual ideal row. -/
theorem thetaGamma_mul (I J : Ext) (hcop : IsCoprime I.val.val J.val.val)
    (j : ℕ) (hj : 0 < j) (hj6 : j < 6) :
    thetaGamma K Sset D (exteriorMul K Sset I J) j =
      thetaGamma K Sset D I j * thetaGamma K Sset D J j *
        idealSymbol K Sset D I (D.generator J) ^ (2 * j) := by
  have h := hcrt.homogeneous_product I J hcop j hj hj6
  rw [hallowed.reciprocity J I] at h
  simpa only [Nat.two_mul, pow_add, mul_assoc] using h

theorem thetaGamma_two_mul (I J : Ext) (hcop : IsCoprime I.val.val J.val.val) :
    thetaGamma K Sset D (exteriorMul K Sset I J) 2 =
      thetaGamma K Sset D I 2 * thetaGamma K Sset D J 2 *
        idealSymbol K Sset D I (D.generator J) ^ 4 :=
  thetaGamma_mul K S D hcrt hallowed I J hcop 2 (by decide) (by decide)

/-- The fourth-power label is derived from the literal a₀ and the finite
Gauss CRT input. The Hecke character is not defined from this identity. -/
theorem canonicalCoefficient_mul (Λ : HeckeCharacter K)
    (I J : Ext) (hcop : IsCoprime I.val.val J.val.val) :
    CoefficientCycle.canonicalCoefficient K Sset D Λ (exteriorMul K Sset I J) =
      CoefficientCycle.canonicalCoefficient K Sset D Λ I *
        CoefficientCycle.canonicalCoefficient K Sset D Λ J *
          idealSymbol K Sset D I (D.generator J) ^ 4 := by
  simp only [CoefficientCycle.canonicalCoefficient]
  change conj (heckeIdealCoefficient K Λ (I.val * J.val)) *
      thetaGamma K Sset D (exteriorMul K Sset I J) 2 = _
  rw [heckeIdealCoefficient_mul, map_mul,
    thetaGamma_two_mul K S D hcrt hallowed I J hcop]
  ring

/-- The extracted actual source column returns μ(u) with its genuine
finite-order twist, while the label-only factor and live background keep
their original arguments. -/
theorem first_source_coefficient {Λ G : HeckeCharacter K}
    (hcal : ThetaCalibrationInput K Sset D Λ G) (ν : HeckeCharacter K)
    (L u : Ext) (hcop : IsCoprime L.val.val u.val.val)
    (hu : Squarefree u.val.val) :
    CoefficientCycle.canonicalCoefficient K Sset D Λ (exteriorMul K Sset L u) *
        heckeIdealCoefficient K ν (exteriorMul K Sset L u).val *
        thetaGamma K Sset D u 1 =
      CoefficientCycle.canonicalCoefficient K Sset D Λ L *
        heckeIdealCoefficient K ν L.val *
        ((UniqueFactorizationMonoid.moebius u.val.val : ℂ) *
          heckeIdealCoefficient K ν u.val * heckeIdealCoefficient K G u.val) *
        idealSymbol K Sset D u (D.generator L) ^ 4 := by
  have ha := canonicalCoefficient_mul K S D hcrt hallowed Λ L u hcop
  rw [hallowed.reciprocity L u] at ha
  rw [ha]
  change _ * heckeIdealCoefficient K ν (L.val * u.val) * _ = _
  rw [heckeIdealCoefficient_mul]
  calc
    _ = CoefficientCycle.canonicalCoefficient K Sset D Λ L *
        heckeIdealCoefficient K ν L.val *
        (CoefficientCycle.canonicalCoefficient K Sset D Λ u * thetaGamma K Sset D u 1) *
        heckeIdealCoefficient K ν u.val * idealSymbol K Sset D u (D.generator L) ^ 4 := by
      ring
    _ = _ := by rw [CoefficientCycle.first_cycle hcal u hu]; ring

/-- The actual coefficient cycle and the cube identity happen in the
same equality. The retained J factor and q₀ mask accompany the very same
dual dilation, including all zeros of the inverse row. -/
theorem first_cube_coefficient_after_dilation {Λ G : HeckeCharacter K}
    (hcal : ThetaCalibrationInput K Sset D Λ G) (ν : HeckeCharacter K)
    (u : Ext) (hu : Squarefree u.val.val) {ι : Type*}
    (p : ι → E) (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v i) (side : Bool)
    (hcop : IsCoprime (aLabel p B (if side then ε₂ else ε₁)).val.val u.val.val)
    (z : E) :
    (if IsCoprime u.val.val (cubeRadical p B).val.val then 1 else 0) *
      CoefficientCycle.canonicalCoefficient K Sset D Λ
        (exteriorMul K Sset
          (CanonicalIdealRow.toExterior K S (aLabel p B (if side then ε₂ else ε₁))) u) *
      heckeIdealCoefficient K ν
        (exteriorMul K Sset
          (CanonicalIdealRow.toExterior K S (aLabel p B (if side then ε₂ else ε₁))) u).val *
      thetaGamma K Sset D u 1 *
      idealSymbol K Sset D u (CanonicalIdealRow.generator K S D (crtLabel p B v ε₁ ε₂ side)) *
      conj (idealSymbol K Sset D u (CanonicalIdealRow.generator K S D z)) =
    (CoefficientCycle.canonicalCoefficient K Sset D Λ
        (CanonicalIdealRow.toExterior K S (aLabel p B (if side then ε₂ else ε₁))) *
      heckeIdealCoefficient K ν (aLabel p B (if side then ε₂ else ε₁)).val *
      ((UniqueFactorizationMonoid.moebius u.val.val : ℂ) *
        heckeIdealCoefficient K ν u.val * heckeIdealCoefficient K G u.val)) *
      (idealSymbol K Sset D u (CanonicalIdealRow.generator K S D (jLabel p B v ε₁ ε₂)) ^ 4 *
        (if IsCoprime u.val.val (b0Label p B v ε₁ ε₂).val.val then 1 else 0)) *
      conj (idealSymbol K Sset D u (CanonicalIdealRow.generator K S D (z * dilationLabel p B v ε₁ ε₂))) := by
  let L := aLabel p B (if side then ε₂ else ε₁)
  let c := CoefficientCycle.canonicalCoefficient K Sset D Λ (CanonicalIdealRow.toExterior K S L) *
    heckeIdealCoefficient K ν L.val *
    ((UniqueFactorizationMonoid.moebius u.val.val : ℂ) *
      heckeIdealCoefficient K ν u.val * heckeIdealCoefficient K G u.val)
  have hc := first_source_coefficient K S D hcrt hallowed hcal ν (CanonicalIdealRow.toExterior K S L) u hcop hu
  have hd := CanonicalIdealRow.first_pass_after_dual_dilation K S D hallowed
    u p B v ε₁ ε₂ hv side z
  change _ = c * _ * _
  calc
    _ = (CoefficientCycle.canonicalCoefficient K Sset D Λ (exteriorMul K Sset (CanonicalIdealRow.toExterior K S L) u) *
        heckeIdealCoefficient K ν (exteriorMul K Sset (CanonicalIdealRow.toExterior K S L) u).val *
        thetaGamma K Sset D u 1) *
      ((if IsCoprime u.val.val (cubeRadical p B).val.val then 1 else 0) *
        idealSymbol K Sset D u (CanonicalIdealRow.generator K S D (crtLabel p B v ε₁ ε₂ side)) *
        conj (idealSymbol K Sset D u (CanonicalIdealRow.generator K S D z))) := by dsimp only [L]; ring
    _ = c *
      (((if IsCoprime u.val.val (cubeRadical p B).val.val then 1 else 0) *
        idealSymbol K Sset D u (CanonicalIdealRow.generator K S D L) ^ 4 *
        idealSymbol K Sset D u (CanonicalIdealRow.generator K S D (crtLabel p B v ε₁ ε₂ side))) *
        conj (idealSymbol K Sset D u (CanonicalIdealRow.generator K S D z))) := by
      rw [hc]
      dsimp only [c, CanonicalIdealRow.generator]
      ring
    _ = _ := by
      rw [show
        ((if IsCoprime u.val.val (cubeRadical p B).val.val then 1 else 0) *
          idealSymbol K Sset D u (CanonicalIdealRow.generator K S D L) ^ 4 *
          idealSymbol K Sset D u (CanonicalIdealRow.generator K S D (crtLabel p B v ε₁ ε₂ side))) *
          conj (idealSymbol K Sset D u (CanonicalIdealRow.generator K S D z)) =
        (idealSymbol K Sset D u (CanonicalIdealRow.generator K S D (jLabel p B v ε₁ ε₂)) ^ 4 *
          (if IsCoprime u.val.val (b0Label p B v ε₁ ε₂).val.val then 1 else 0)) *
          conj (idealSymbol K Sset D u (CanonicalIdealRow.generator K S D (z * dilationLabel p B v ε₁ ε₂)))
          from hd]
      ring

/-- A frozen original label remains on the same column and becomes
the actual product fJ in the transformed column. Its zeros are retained. -/
theorem first_cube_coefficient_with_frozen_label {Λ G : HeckeCharacter K}
    (hcal : ThetaCalibrationInput K Sset D Λ G) (ν : HeckeCharacter K)
    (u : Ext) (hu : Squarefree u.val.val) {ι : Type*}
    (p : ι → E) (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v i) (side : Bool)
    (hcop : IsCoprime (aLabel p B (if side then ε₂ else ε₁)).val.val u.val.val)
    (f z : E) :
    (if IsCoprime u.val.val (cubeRadical p B).val.val then 1 else 0) *
      CoefficientCycle.canonicalCoefficient K Sset D Λ
        (exteriorMul K Sset
          (CanonicalIdealRow.toExterior K S (aLabel p B (if side then ε₂ else ε₁))) u) *
      heckeIdealCoefficient K ν
        (exteriorMul K Sset
          (CanonicalIdealRow.toExterior K S (aLabel p B (if side then ε₂ else ε₁))) u).val *
      thetaGamma K Sset D u 1 *
      idealSymbol K Sset D u (CanonicalIdealRow.generator K S D f) ^ 4 *
      idealSymbol K Sset D u (CanonicalIdealRow.generator K S D (crtLabel p B v ε₁ ε₂ side)) *
      conj (idealSymbol K Sset D u (CanonicalIdealRow.generator K S D z)) =
    (CoefficientCycle.canonicalCoefficient K Sset D Λ
        (CanonicalIdealRow.toExterior K S (aLabel p B (if side then ε₂ else ε₁))) *
      heckeIdealCoefficient K ν (aLabel p B (if side then ε₂ else ε₁)).val *
      ((UniqueFactorizationMonoid.moebius u.val.val : ℂ) *
        heckeIdealCoefficient K ν u.val * heckeIdealCoefficient K G u.val)) *
      (idealSymbol K Sset D u (CanonicalIdealRow.generator K S D (f * jLabel p B v ε₁ ε₂)) ^ 4 *
        (if IsCoprime u.val.val (b0Label p B v ε₁ ε₂).val.val then 1 else 0)) *
      conj (idealSymbol K Sset D u (CanonicalIdealRow.generator K S D (z * dilationLabel p B v ε₁ ε₂))) := by
  have h := congrArg (fun w : ℂ => idealSymbol K Sset D u (CanonicalIdealRow.generator K S D f) ^ 4 * w)
    (first_cube_coefficient_after_dilation K S D hcrt hallowed hcal ν u hu
      p B v ε₁ ε₂ hv side hcop z)
  rw [CanonicalIdealRow.fourth_label_mul K S D hallowed] 
  convert h using 1 <;> ring

/-- The complete first-column extraction n=A·C·u. The common factor C
is frozen with A in the outer coefficient and stays in the new label C·J.
The original f is removed from that label and enters the row as f². -/
theorem first_cube_coefficient_with_common_factor {Λ G : HeckeCharacter K}
    (hcal : ThetaCalibrationInput K Sset D Λ G) (ν : HeckeCharacter K)
    (u : Ext) (hu : Squarefree u.val.val) {ι : Type*}
    (p : ι → E) (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v i) (side : Bool) (C f z : E)
    (hcop : IsCoprime (aLabel p B (if side then ε₂ else ε₁) * C).val.val u.val.val) :
    (if IsCoprime u.val.val (cubeRadical p B).val.val then 1 else 0) *
      CoefficientCycle.canonicalCoefficient K Sset D Λ
        (exteriorMul K Sset (CanonicalIdealRow.toExterior K S
          (aLabel p B (if side then ε₂ else ε₁) * C)) u) *
      heckeIdealCoefficient K ν
        (exteriorMul K Sset (CanonicalIdealRow.toExterior K S
          (aLabel p B (if side then ε₂ else ε₁) * C)) u).val *
      thetaGamma K Sset D u 1 *
      idealSymbol K Sset D u (CanonicalIdealRow.generator K S D f) ^ 4 *
      idealSymbol K Sset D u (CanonicalIdealRow.generator K S D (crtLabel p B v ε₁ ε₂ side)) *
      conj (idealSymbol K Sset D u (CanonicalIdealRow.generator K S D z)) =
    (CoefficientCycle.canonicalCoefficient K Sset D Λ
        (CanonicalIdealRow.toExterior K S (aLabel p B (if side then ε₂ else ε₁) * C)) *
      heckeIdealCoefficient K ν (aLabel p B (if side then ε₂ else ε₁) * C).val *
      ((UniqueFactorizationMonoid.moebius u.val.val : ℂ) *
        heckeIdealCoefficient K ν u.val * heckeIdealCoefficient K G u.val)) *
      (idealSymbol K Sset D u (CanonicalIdealRow.generator K S D (C * jLabel p B v ε₁ ε₂)) ^ 4 *
        (if IsCoprime u.val.val (b0Label p B v ε₁ ε₂).val.val then 1 else 0)) *
      conj (idealSymbol K Sset D u
        (CanonicalIdealRow.generator K S D (z * f ^ 2 * dilationLabel p B v ε₁ ε₂))) := by
  let L := aLabel p B (if side then ε₂ else ε₁) * C
  let c := CoefficientCycle.canonicalCoefficient K Sset D Λ (CanonicalIdealRow.toExterior K S L) *
    heckeIdealCoefficient K ν L.val *
    ((UniqueFactorizationMonoid.moebius u.val.val : ℂ) *
      heckeIdealCoefficient K ν u.val * heckeIdealCoefficient K G u.val)
  have hc := first_source_coefficient K S D hcrt hallowed hcal ν
    (CanonicalIdealRow.toExterior K S L) u hcop hu
  have hd := CanonicalIdealRow.common_factor_after_dual_dilation K S D hallowed
    u p B v ε₁ ε₂ hv side C f z
  change _ = c * _ * _
  calc
    _ = (CoefficientCycle.canonicalCoefficient K Sset D Λ
          (exteriorMul K Sset (CanonicalIdealRow.toExterior K S L) u) *
        heckeIdealCoefficient K ν (exteriorMul K Sset (CanonicalIdealRow.toExterior K S L) u).val *
        thetaGamma K Sset D u 1) *
      ((if IsCoprime u.val.val (cubeRadical p B).val.val then 1 else 0) *
        idealSymbol K Sset D u (CanonicalIdealRow.generator K S D (crtLabel p B v ε₁ ε₂ side)) *
        idealSymbol K Sset D u (CanonicalIdealRow.generator K S D f) ^ 4 *
        conj (idealSymbol K Sset D u (CanonicalIdealRow.generator K S D z))) := by
      dsimp only [L]
      ring
    _ = c *
      ((if IsCoprime u.val.val (cubeRadical p B).val.val then 1 else 0) *
        idealSymbol K Sset D u (CanonicalIdealRow.generator K S D L) ^ 4 *
        idealSymbol K Sset D u (CanonicalIdealRow.generator K S D (crtLabel p B v ε₁ ε₂ side)) *
        idealSymbol K Sset D u (CanonicalIdealRow.generator K S D f) ^ 4 *
        conj (idealSymbol K Sset D u (CanonicalIdealRow.generator K S D z))) := by
      rw [hc]
      dsimp only [c, CanonicalIdealRow.generator]
      ring
    _ = _ := by rw [hd]; ring

/-- When the common source factor is the unit, J is the sole remaining
averaged label. The old f is entirely in the actual new row z·f²·E. -/
theorem first_cube_coefficient_with_old_label_in_row {Λ G : HeckeCharacter K}
    (hcal : ThetaCalibrationInput K Sset D Λ G) (ν : HeckeCharacter K)
    (u : Ext) (hu : Squarefree u.val.val) {ι : Type*}
    (p : ι → E) (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v i) (side : Bool)
    (hcop : IsCoprime (aLabel p B (if side then ε₂ else ε₁)).val.val u.val.val)
    (f z : E) :
    (if IsCoprime u.val.val (cubeRadical p B).val.val then 1 else 0) *
      CoefficientCycle.canonicalCoefficient K Sset D Λ
        (exteriorMul K Sset
          (CanonicalIdealRow.toExterior K S (aLabel p B (if side then ε₂ else ε₁))) u) *
      heckeIdealCoefficient K ν
        (exteriorMul K Sset
          (CanonicalIdealRow.toExterior K S (aLabel p B (if side then ε₂ else ε₁))) u).val *
      thetaGamma K Sset D u 1 *
      idealSymbol K Sset D u (CanonicalIdealRow.generator K S D f) ^ 4 *
      idealSymbol K Sset D u (CanonicalIdealRow.generator K S D (crtLabel p B v ε₁ ε₂ side)) *
      conj (idealSymbol K Sset D u (CanonicalIdealRow.generator K S D z)) =
    (CoefficientCycle.canonicalCoefficient K Sset D Λ
        (CanonicalIdealRow.toExterior K S (aLabel p B (if side then ε₂ else ε₁))) *
      heckeIdealCoefficient K ν (aLabel p B (if side then ε₂ else ε₁)).val *
      ((UniqueFactorizationMonoid.moebius u.val.val : ℂ) *
        heckeIdealCoefficient K ν u.val * heckeIdealCoefficient K G u.val)) *
      (idealSymbol K Sset D u (CanonicalIdealRow.generator K S D (jLabel p B v ε₁ ε₂)) ^ 4 *
        (if IsCoprime u.val.val (b0Label p B v ε₁ ε₂).val.val then 1 else 0)) *
      conj (idealSymbol K Sset D u
        (CanonicalIdealRow.generator K S D (z * f ^ 2 * dilationLabel p B v ε₁ ε₂))) := by
  simpa only [mul_one, one_mul] using
    first_cube_coefficient_with_common_factor K S D hcrt hallowed hcal ν u hu
      p B v ε₁ ε₂ hv side 1 f z (by simpa only [mul_one] using hcop)

end HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalGaussCalibration

end
