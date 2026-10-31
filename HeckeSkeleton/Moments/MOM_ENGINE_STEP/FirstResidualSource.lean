import HeckeSkeleton.Moments.MOM_ENGINE_STEP.GaussSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstFiniteSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstKernel

/-!
# The actual first periodic source and its residual Gauss columns

The source below is constructed from three original multiplicative
characters, on the literal modulus `a * (b * r)`.  Its complete first
divisor transform is proved from the actual S-local CRT Fourier formula.
Every mask-divisor character value is retained, including its possible
zero value.  The common character produces one common Gauss factor; its
two column factors belong to the whole coefficients.

The carrier `OrbitalGaussColumn` supplies a modulus, a multiplicative
character, and invariance under the original subgroup.  This file uses
those original characters to construct the first source; its residue is
not the two-Gauss source used for the second Poisson operation.
-/

noncomputable section
open scoped Classical BigOperators FourierTransform SchwartzMap

set_option maxHeartbeats 4000000

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Bridge MeasureTheory HeckePort.Moments
open HeckePort.Moments.MobiusRegroup UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K]
variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}
local notation "OS" => Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Q" => SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ

/-- The literal three-character source of the first transform. -/
def OrbitalGaussColumn.originalTriple (a b r : OrbitalGaussColumn K S Γ)
    (φ : SchwartzMap V ℂ) : ParentPeriodicPair K S Γ where
  modulus := a.modulus * (b.modulus * r.modulus)
  modulus_ne_zero := mul_ne_zero a.nonzero (mul_ne_zero b.nonzero r.nonzero)
  residue x :=
    a.character (completeFrequencyReduction a.modulus
      (a.modulus * (b.modulus * r.modulus)) (dvd_mul_right _ _) x) *
    b.character⁻¹ (completeFrequencyReduction b.modulus
      (a.modulus * (b.modulus * r.modulus))
      (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) x) *
    r.character (completeFrequencyReduction r.modulus
      (a.modulus * (b.modulus * r.modulus))
      (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) x)
  invariant u x := by
    simp only [completeFrequencyReduction_mk, map_mul, MulChar.inv_apply_eq_inv',
      a.invariant, b.invariant, r.invariant, inv_one, one_mul]
  profile := φ

def firstLeftDivisorFactor (a r : OrbitalGaussColumn K S Γ) (δ : OS) : ℂ :=
  a.character (Ideal.Quotient.mk _ δ) *
    a.character (Ideal.Quotient.mk _ r.modulus) *
    r.character (Ideal.Quotient.mk _ a.modulus)

def firstRightDivisorFactor (b r : OrbitalGaussColumn K S Γ) (δ : OS) : ℂ :=
  b.character (Ideal.Quotient.mk _ δ) *
    b.character (Ideal.Quotient.mk _ r.modulus) *
    star (r.character (Ideal.Quotient.mk _ b.modulus))

/-- The original two residual characters determine the reciprocal phase. -/
def firstReciprocalPhase (a b : OrbitalGaussColumn K S Γ) : ℂ :=
  a.character (Ideal.Quotient.mk _ b.modulus) *
    star (b.character (Ideal.Quotient.mk _ a.modulus))

variable (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)

/-- Complete finite first transform, with the nonunit divisor retained.
No character or Fourier-coefficient factorization is an input. -/
theorem originalTriple_divisor_fourier (a b r : OrbitalGaussColumn K S Γ)
    (φ : SchwartzMap V ℂ)
    (habr : IsCoprime a.modulus (b.modulus * r.modulus))
    (hbr : IsCoprime b.modulus r.modulus) (δ h : OS) :
    sIntegerPeriodicDivisorFourier K (S : Set (HeightOneSpectrum (𝓞 K))) hS
      (a.originalTriple b r φ).modulus (a.originalTriple b r φ).modulus_ne_zero
      (a.originalTriple b r φ).residue δ (Ideal.Quotient.mk _ h) =
      (firstLeftDivisorFactor a r δ * star (firstRightDivisorFactor b r δ)) *
        firstReciprocalPhase a b *
        (r.character (Ideal.Quotient.mk _ δ) *
          actualSIntegerGauss K (S : Set (HeightOneSpectrum (𝓞 K))) hS r.modulus r.nonzero r.character h) *
        (actualSIntegerGauss K (S : Set (HeightOneSpectrum (𝓞 K))) hS a.modulus a.nonzero a.character h *
          star (actualSIntegerGauss K (S : Set (HeightOneSpectrum (𝓞 K))) hS b.modulus b.nonzero b.character (-h))) := by
  letI := finite_sIntegerPrincipalResidue K (S : Set (HeightOneSpectrum (𝓞 K))) a.modulus a.nonzero
  letI := finite_sIntegerPrincipalResidue K (S : Set (HeightOneSpectrum (𝓞 K))) b.modulus b.nonzero
  letI := finite_sIntegerPrincipalResidue K (S : Set (HeightOneSpectrum (𝓞 K))) r.modulus r.nonzero
  letI := finite_sIntegerPrincipalResidue K (S : Set (HeightOneSpectrum (𝓞 K)))
    (b.modulus * r.modulus) (mul_ne_zero b.nonzero r.nonzero)
  letI := finite_sIntegerPrincipalResidue K (S : Set (HeightOneSpectrum (𝓞 K)))
    (a.modulus * (b.modulus * r.modulus))
    (mul_ne_zero a.nonzero (mul_ne_zero b.nonzero r.nonzero))
  letI := Fintype.ofFinite (OS ⧸ Ideal.span ({a.modulus} : Set OS))
  letI := Fintype.ofFinite (OS ⧸ Ideal.span ({b.modulus} : Set OS))
  letI := Fintype.ofFinite (OS ⧸ Ideal.span ({r.modulus} : Set OS))
  letI := Fintype.ofFinite (OS ⧸ Ideal.span ({b.modulus * r.modulus} : Set OS))
  letI := Fintype.ofFinite
    (OS ⧸ Ideal.span ({a.modulus * (b.modulus * r.modulus)} : Set OS))
  have he := actual_sInteger_three_factor_divisor_fourier K (S : Set (HeightOneSpectrum (𝓞 K))) hS
    a.modulus b.modulus r.modulus a.nonzero b.nonzero r.nonzero habr hbr
    a.character b.character⁻¹ r.character δ (Ideal.Quotient.mk _ h)
  have hcommon :
      (∑ y : OS ⧸ Ideal.span ({r.modulus} : Set OS),
        r.character (Ideal.Quotient.mk _ δ *
          (Ideal.Quotient.mk _ (a.modulus * b.modulus) * y)) *
          sIntegerActualModulusAddCharacter K (S : Set (HeightOneSpectrum (𝓞 K))) hS r.modulus r.nonzero
            (Ideal.Quotient.mk _ h * y)) =
        r.character (Ideal.Quotient.mk _ δ) *
          r.character (Ideal.Quotient.mk _ a.modulus) *
          r.character (Ideal.Quotient.mk _ b.modulus) *
          completeResidueGauss (actualSIntegerTrace K (S : Set (HeightOneSpectrum (𝓞 K))) hS)
            r.modulus r.character (Ideal.Quotient.mk _ h) := by
    unfold completeResidueGauss
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [actualSIntegerTrace_psi K (S : Set (HeightOneSpectrum (𝓞 K))) hS r.modulus r.nonzero]
    simp only [map_mul]
    ring
  simp only [completeFrequencyReduction_mk] at he
  rw [hcommon, completeResidueGauss_inverse] at he
  have hstar (χ : MulChar (OS ⧸ Ideal.span ({b.modulus} : Set OS)) ℂ) (x) :
      χ⁻¹ x = star (χ x) := (MulChar.star_apply' χ x).symm
  change PeriodicFourier.divisorTransform
    (sIntegerActualModulusAddCharacter K (S : Set (HeightOneSpectrum (𝓞 K))) hS
      (a.modulus * (b.modulus * r.modulus))
      (mul_ne_zero a.nonzero (mul_ne_zero b.nonzero r.nonzero)))
    (fun x : OS ⧸ Ideal.span ({a.modulus * (b.modulus * r.modulus)} : Set OS) =>
      a.character (completeFrequencyReduction a.modulus
        (a.modulus * (b.modulus * r.modulus)) (dvd_mul_right _ _) x) *
      b.character⁻¹ (completeFrequencyReduction b.modulus
        (a.modulus * (b.modulus * r.modulus))
        (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) x) *
      r.character (completeFrequencyReduction r.modulus
        (a.modulus * (b.modulus * r.modulus))
        (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) x))
    (Ideal.Quotient.mk _ δ) (Ideal.Quotient.mk _ h) = _
  rw [he]
  unfold firstLeftDivisorFactor firstRightDivisorFactor firstReciprocalPhase
    actualSIntegerGauss
  simp only [hstar, map_mul, ← map_neg, star_mul, star_star]
  ring

/-- The same coefficient identity on every original subgroup orbit. -/
theorem originalTriple_fourier_orbit (a b r : OrbitalGaussColumn K S Γ)
    (φ : SchwartzMap V ℂ)
    (habr : IsCoprime a.modulus (b.modulus * r.modulus))
    (hbr : IsCoprime b.modulus r.modulus) (δ : OS) (q : Q) :
    sIntegerPeriodicFourierOrbitWeight K (S : Set (HeightOneSpectrum (𝓞 K))) hS Γ
      (a.originalTriple b r φ).modulus (a.originalTriple b r φ).modulus_ne_zero
      (a.originalTriple b r φ).residue (a.originalTriple b r φ).invariant δ q =
      (firstLeftDivisorFactor a r δ * star (firstRightDivisorFactor b r δ)) *
        firstReciprocalPhase a b *
        (r.character (Ideal.Quotient.mk _ δ) *
          actualSIntegerGauss K (S : Set (HeightOneSpectrum (𝓞 K))) hS r.modulus r.nonzero r.character q.out.val) *
        (actualSIntegerGauss K (S : Set (HeightOneSpectrum (𝓞 K))) hS a.modulus a.nonzero a.character q.out.val *
          star (actualSIntegerGauss K (S : Set (HeightOneSpectrum (𝓞 K))) hS b.modulus b.nonzero b.character (-q.out.val))) := by
  conv_lhs => rw [← Quotient.out_eq q]
  rw [sIntegerPeriodicFourierOrbitWeight_mk]
  exact originalTriple_divisor_fourier hS a b r φ habr hbr δ q.out.val

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (Ray : Type*) [CommGroup Ray] [Fintype Ray]
local instance firstResidualSourceCircleCharacterFintype : Fintype ((Ray × Ray) →* Circle) := Fintype.ofFinite _

/-- The first residual kernel estimate on an arbitrary row carrier.
Using actual subgroup orbits as the carrier retains every sector; the
frequency map merely displays a representative in the complete Gauss sum. -/
theorem first_residual_gauss_kernel_bound_on {H ι κ : Type*}
    (F : 𝓢(E, ℂ)) (rows : Finset H) (frequency : H → OS)
    (leftColumns : Finset ι) (rightColumns : Finset κ)
    (leftIdeals : ι → Ideal (𝓞 K)) (rightIdeals : κ → Ideal (𝓞 K))
    (hRight : ∀ j ∈ rightColumns, rightIdeals j ≠ ⊥)
    (a : ι → OrbitalGaussColumn K S Γ) (b : κ → OrbitalGaussColumn K S Γ)
    (rayLeft : ι → Ray) (rayRight : κ → Ray) (phaseTable : Ray × Ray → Circle)
    (hphase : ∀ i j, IsCoprime (leftIdeals i) (rightIdeals j) →
      firstReciprocalPhase (a i) (b j) = (phaseTable (rayLeft i, rayRight j) : ℂ))
    (common q : H → ℂ) (c : ι → ℂ) (d : κ → ℂ)
    (x : ι → E) (y : κ → E) (z : H → E) :
    let G₁ := fun i h => actualSIntegerGauss K (S : Set (HeightOneSpectrum (𝓞 K))) hS
      (a i).modulus (a i).nonzero (a i).character (frequency h)
    let G₂ := fun j h => actualSIntegerGauss K (S : Set (HeightOneSpectrum (𝓞 K))) hS
      (b j).modulus (b j).nonzero (b j).character (-frequency h)
    let c₁ := fun D χ i => if D ∣ leftIdeals i then
      c i * (fixedLeftPhase Ray χ (rayLeft i) : ℂ) else 0
    let c₂ := fun D χ j => if D ∣ rightIdeals j then
      d j * (fixedRightPhase Ray χ (rayRight j) : ℂ) else 0
    ‖∑ h ∈ rows, q h * ∑ i ∈ leftColumns, ∑ j ∈ rightColumns,
      (if IsCoprime (leftIdeals i) (rightIdeals j) then
        common h * firstReciprocalPhase (a i) (b j) * (G₁ i h * star (G₂ j h)) else 0) *
        (c i * star (d j)) * F (z h + x i + y j)‖ ≤
      ∑ D ∈ divisorPool rightColumns rightIdeals, ‖(moebius D : ℂ)‖ *
        ∑ χ : (Ray × Ray) →* Circle, ‖fixedPhaseCoefficient Ray phaseTable χ‖ *
          ∫ ξ : E, ‖(𝓕 F) ξ‖ *
            (Real.sqrt (weightedEnergy rows (fun h => ‖q h * common h‖)
              (wholePolynomial leftColumns (fun i => c₁ D χ i * jointPhase ξ (x i)) G₁)) *
            Real.sqrt (weightedEnergy rows (fun h => ‖q h * common h‖)
              (wholePolynomial rightColumns
                (fun j => c₂ D χ j * star (jointPhase ξ (y j))) G₂))) := by
  dsimp only
  let G₁ := fun i h => actualSIntegerGauss K (S : Set (HeightOneSpectrum (𝓞 K))) hS
    (a i).modulus (a i).nonzero (a i).character (frequency h)
  let G₂ := fun j h => actualSIntegerGauss K (S : Set (HeightOneSpectrum (𝓞 K))) hS
    (b j).modulus (b j).nonzero (b j).character (-frequency h)
  have hbnd := full_correlation_kernel_bound F rows leftColumns rightColumns
    leftIdeals rightIdeals hRight
    (fun i j h => common h * firstReciprocalPhase (a i) (b j) * (G₁ i h * star (G₂ j h)))
    common q (fixedPhaseCoefficient Ray phaseTable)
    (fun χ i => (fixedLeftPhase Ray χ (rayLeft i) : ℂ))
    (fun χ j => (fixedRightPhase Ray χ (rayRight j) : ℂ)) G₁ G₂
    (fun i j h hc => by rw [hphase i j hc, fixed_phase_expansion Ray phaseTable])
    c d (fun h i => z h + x i) (fun _ j => y j)
  simpa only [kernelDivisorCoefficient_eq_fun, joint_energy_gauss_rows,
    joint_energy_conjugate_gauss_rows, G₁, G₂] using hbnd

/-- The explicit sum of whole residual Gauss energies arising from the
proved full Möbius and fixed-ray Fourier expansions. -/
def firstResidualKernelCost {H ι κ : Type*}
    (F : 𝓢(E, ℂ)) (rows : Finset H) (frequency : H → OS)
    (leftColumns : Finset ι) (rightColumns : Finset κ)
    (leftIdeals : ι → Ideal (𝓞 K)) (rightIdeals : κ → Ideal (𝓞 K))
    (a : ι → OrbitalGaussColumn K S Γ) (b : κ → OrbitalGaussColumn K S Γ)
    (rayLeft : ι → Ray) (rayRight : κ → Ray) (phaseTable : Ray × Ray → Circle)
    (common q : H → ℂ) (c : ι → ℂ) (d : κ → ℂ) (x : ι → E) (y : κ → E) : ℝ :=
  let G₁ := fun i h => actualSIntegerGauss K (S : Set (HeightOneSpectrum (𝓞 K))) hS
    (a i).modulus (a i).nonzero (a i).character (frequency h)
  let G₂ := fun j h => actualSIntegerGauss K (S : Set (HeightOneSpectrum (𝓞 K))) hS
    (b j).modulus (b j).nonzero (b j).character (-frequency h)
  let c₁ := fun D χ i => if D ∣ leftIdeals i then
    c i * (fixedLeftPhase Ray χ (rayLeft i) : ℂ) else 0
  let c₂ := fun D χ j => if D ∣ rightIdeals j then
    d j * (fixedRightPhase Ray χ (rayRight j) : ℂ) else 0
  ∑ D ∈ divisorPool rightColumns rightIdeals, ‖(moebius D : ℂ)‖ *
    ∑ χ : (Ray × Ray) →* Circle, ‖fixedPhaseCoefficient Ray phaseTable χ‖ *
      ∫ ξ : E, ‖(𝓕 F) ξ‖ *
        (Real.sqrt (weightedEnergy rows (fun h => ‖q h * common h‖)
          (wholePolynomial leftColumns (fun i => c₁ D χ i * jointPhase ξ (x i)) G₁)) *
        Real.sqrt (weightedEnergy rows (fun h => ‖q h * common h‖)
          (wholePolynomial rightColumns
            (fun j => c₂ D χ j * star (jointPhase ξ (y j))) G₂)))

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [Γ.FiniteIndex]
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

/-- The archimedean factor of a genuine divisor branch, including its
actual Poisson normalization and actual dual radius. -/
def ParentPeriodicPair.transformedProfile (p : ParentPeriodicPair K S Γ)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum OS)) (q : Q) : ℂ :=
  sIntegerMaskPoissonFactor K S p.modulus p.modulus_ne_zero radius
    (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D) *
  sUnitOrbitalProfile K (S : Set (HeightOneSpectrum (𝓞 K)))
    (sLocalTensorTestFunction K (S : Set (HeightOneSpectrum (𝓞 K)))
      (traceSchwartzFourier K p.profile) (sIntegerFiniteFourierTestFunction K S μv finiteTest))
    ⟨(p.dualRadius radius D).val *
        (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).val,
      mul_pos (p.dualRadius radius D).property (sIntegerOrbitNorm K _ Γ q).property⟩

theorem originalTriple_transformedRow (a b r : OrbitalGaussColumn K S Γ)
    (φ : SchwartzMap V ℂ)
    (habr : IsCoprime a.modulus (b.modulus * r.modulus))
    (hbr : IsCoprime b.modulus r.modulus)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum OS)) (q : Q) :
    let δ := (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D).val
    (a.originalTriple b r φ).transformedRow μv hS finiteTest radius D q =
      (moebius (IdealMobiusMask.primeProduct D) : ℂ) *
      ((firstLeftDivisorFactor a r δ * star (firstRightDivisorFactor b r δ)) *
        firstReciprocalPhase a b *
        (r.character (Ideal.Quotient.mk _ δ) *
          actualSIntegerGauss K (S : Set (HeightOneSpectrum (𝓞 K))) hS r.modulus r.nonzero r.character q.out.val) *
        (actualSIntegerGauss K (S : Set (HeightOneSpectrum (𝓞 K))) hS a.modulus a.nonzero a.character q.out.val *
          star (actualSIntegerGauss K (S : Set (HeightOneSpectrum (𝓞 K))) hS b.modulus b.nonzero b.character (-q.out.val)))) *
        (a.originalTriple b r φ).transformedProfile μv finiteTest radius D q := by
  dsimp only
  unfold ParentPeriodicPair.transformedRow sIntegerPeriodicFourierProfileTerm
  rw [originalTriple_fourier_orbit hS a b r φ habr hbr]
  unfold ParentPeriodicPair.transformedProfile
  ring

/-- One actual first-transform rectangle is controlled by whole Gauss
polynomials with row-independent coefficients.  The only analytic chart
input is a pointwise identity of the individual transformed profiles;
the complete finite Fourier factorization and the kernel-energy estimate
are proved internally.  Both sides use the same orbital rows and the same
continuous Fourier parameter. -/
theorem first_source_kernel_bound {ι κ : Type*}
    (F : 𝓢(E, ℂ)) (rows : Finset Q)
    (leftColumns : Finset ι) (rightColumns : Finset κ)
    (leftIdeals : ι → Ideal (𝓞 K)) (rightIdeals : κ → Ideal (𝓞 K))
    (hRight : ∀ j ∈ rightColumns, rightIdeals j ≠ ⊥)
    (a : ι → OrbitalGaussColumn K S Γ) (b : κ → OrbitalGaussColumn K S Γ)
    (r : OrbitalGaussColumn K S Γ) (profiles : ι → κ → SchwartzMap V ℂ)
    (hcoprime : ∀ i ∈ leftColumns, ∀ j ∈ rightColumns,
      IsCoprime (leftIdeals i) (rightIdeals j) →
        IsCoprime (a i).modulus ((b j).modulus * r.modulus) ∧
          IsCoprime (b j).modulus r.modulus)
    (rayLeft : ι → Ray) (rayRight : κ → Ray) (phaseTable : Ray × Ray → Circle)
    (hphase : ∀ i j, IsCoprime (leftIdeals i) (rightIdeals j) →
      firstReciprocalPhase (a i) (b j) = (phaseTable (rayLeft i, rayRight j) : ℂ))
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum OS))
    (q : Q → ℂ) (c : ι → ℂ) (d : κ → ℂ)
    (x : ι → E) (y : κ → E) (z : Q → E)
    (hprofile : ∀ t ∈ rows, ∀ i ∈ leftColumns, ∀ j ∈ rightColumns,
      IsCoprime (leftIdeals i) (rightIdeals j) →
      ((a i).originalTriple (b j) r (profiles i j)).transformedProfile μv finiteTest radius D t =
        q t * (c i * star (d j)) * F (z t + x i + y j)) :
    let δ := (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D).val
    let common := fun t : Q => (moebius (IdealMobiusMask.primeProduct D) : ℂ) *
      (r.character (Ideal.Quotient.mk _ δ) *
        actualSIntegerGauss K (S : Set (HeightOneSpectrum (𝓞 K))) hS r.modulus r.nonzero r.character t.out.val)
    ‖∑ t ∈ rows, ∑ i ∈ leftColumns, ∑ j ∈ rightColumns,
      if IsCoprime (leftIdeals i) (rightIdeals j) then
        ((a i).originalTriple (b j) r (profiles i j)).transformedRow μv hS finiteTest radius D t
      else 0‖ ≤
      firstResidualKernelCost hS Ray F rows (fun t => t.out.val)
        leftColumns rightColumns leftIdeals rightIdeals a b rayLeft rayRight phaseTable common q
        (fun i => c i * firstLeftDivisorFactor (a i) r δ)
        (fun j => d j * firstRightDivisorFactor (b j) r δ) x y := by
  dsimp only
  let δ := (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D).val
  let common := fun t : Q => (moebius (IdealMobiusMask.primeProduct D) : ℂ) *
    (r.character (Ideal.Quotient.mk _ δ) *
      actualSIntegerGauss K (S : Set (HeightOneSpectrum (𝓞 K))) hS r.modulus r.nonzero r.character t.out.val)
  have hbound := first_residual_gauss_kernel_bound_on hS Ray F rows (fun t => t.out.val)
    leftColumns rightColumns leftIdeals rightIdeals hRight a b rayLeft rayRight phaseTable hphase
    common q (fun i => c i * firstLeftDivisorFactor (a i) r δ)
    (fun j => d j * firstRightDivisorFactor (b j) r δ) x y z
  dsimp only at hbound
  have he :
      (∑ t ∈ rows, ∑ i ∈ leftColumns, ∑ j ∈ rightColumns,
        if IsCoprime (leftIdeals i) (rightIdeals j) then
          ((a i).originalTriple (b j) r (profiles i j)).transformedRow μv hS finiteTest radius D t
        else 0) =
      ∑ t ∈ rows, q t * ∑ i ∈ leftColumns, ∑ j ∈ rightColumns,
        (if IsCoprime (leftIdeals i) (rightIdeals j) then
          common t * firstReciprocalPhase (a i) (b j) *
            (actualSIntegerGauss K (S : Set (HeightOneSpectrum (𝓞 K))) hS (a i).modulus (a i).nonzero (a i).character t.out.val *
              star (actualSIntegerGauss K (S : Set (HeightOneSpectrum (𝓞 K))) hS
                (b j).modulus (b j).nonzero (b j).character (-t.out.val))) else 0) *
        ((c i * firstLeftDivisorFactor (a i) r δ) *
          star (d j * firstRightDivisorFactor (b j) r δ)) * F (z t + x i + y j) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hc : IsCoprime (leftIdeals i) (rightIdeals j)
    · rw [if_pos hc, if_pos hc]
      obtain ⟨habr, hbr⟩ := hcoprime i hi j hj hc
      rw [originalTriple_transformedRow hS μv (a i) (b j) r (profiles i j) habr hbr]
      rw [hprofile t ht i hi j hj hc]
      simp only [star_mul, common, δ]
      ring
    · simp only [if_neg hc, zero_mul, mul_zero]
  rw [he]
  exact hbound

end HeckeSkeleton.Moments.EngineStep

end

#print axioms HeckeSkeleton.Moments.EngineStep.originalTriple_divisor_fourier
#print axioms HeckeSkeleton.Moments.EngineStep.first_residual_gauss_kernel_bound_on
#print axioms HeckeSkeleton.Moments.EngineStep.first_source_kernel_bound

