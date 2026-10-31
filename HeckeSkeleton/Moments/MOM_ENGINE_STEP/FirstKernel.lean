import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SIntegerFirstFourier
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FinitePhase

/-!
# First residual Gauss norms with one common Fourier kernel

After the genuine first finite CRT formula, the residual columns are the
complete Gauss sums below.  The original reciprocal phase is expanded on
its fixed finite ray quotient, and the full residual coprimality sum is
inserted before Fourier separation.

The kernel has the form `F (z h + x i + y j)`.  The common row translation
contributes a phase of norm one; removing that phase from the two Cauchy
energies leaves coefficients independent of the row.  Consequently the
resulting whole Gauss polynomials have the precise coefficient dependence
required by a single prime-pool amplification.  The Fourier parameter
ranges over the entire space.
-/

noncomputable section
open scoped Classical BigOperators FourierTransform SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckePort.Moments HeckePort.Moments.MobiusRegroup UniqueFactorizationMonoid
open MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A common row translation has no cost in the separated squared energy.
The coefficient on the right depends on the Fourier parameter but not the row. -/
theorem joint_energy_gauss_rows {H ι : Type*}
    (rows : Finset H) (columns : Finset ι) (q : H → ℂ)
    (c : ι → ℂ) (G : ι → H → ℂ) (x : ι → V) (z : H → V) (ξ : V) :
    jointColumnEnergy rows columns q (fun h i => c i * G i h)
        (fun h i => z h + x i) ξ =
      weightedEnergy rows (fun h => ‖q h‖)
        (wholePolynomial columns (fun i => c i * jointPhase ξ (x i)) G) := by
  unfold jointColumnEnergy weightedEnergy
  apply Finset.sum_congr rfl
  intro h hh
  have hcolumn : jointFourierColumn columns (fun i => c i * G i h)
      (fun i => z h + x i) ξ =
      jointPhase ξ (z h) * wholePolynomial columns (fun i => c i * jointPhase ξ (x i)) G h := by
    unfold jointFourierColumn wholePolynomial
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [jointPhase_add]
    ring
  rw [hcolumn, norm_mul, norm_jointPhase, one_mul]

/-- The second Cauchy half is a whole conjugated polynomial.  Its Fourier
twist remains in the fixed coefficient, including its original mask. -/
theorem joint_energy_conjugate_gauss_rows {H ι : Type*}
    (rows : Finset H) (columns : Finset ι) (q : H → ℂ)
    (c : ι → ℂ) (G : ι → H → ℂ) (x : ι → V) (ξ : V) :
    jointColumnEnergy rows columns q (fun h i => star (c i * G i h))
        (fun _ i => x i) ξ =
      weightedEnergy rows (fun h => ‖q h‖)
        (wholePolynomial columns (fun i => c i * star (jointPhase ξ (x i))) G) := by
  unfold jointColumnEnergy weightedEnergy
  apply Finset.sum_congr rfl
  intro h hh
  have hcolumn : jointFourierColumn columns (fun i => star (c i * G i h)) x ξ =
      star (wholePolynomial columns (fun i => c i * star (jointPhase ξ (x i))) G h) := by
    unfold jointFourierColumn wholePolynomial
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [star_mul, star_star]
    ring
  rw [hcolumn, norm_star]

variable {K : Type} [Field K] [NumberField K]

/-- The divisor restriction belongs to the fixed whole coefficient. -/
theorem kernelDivisorCoefficient_eq_mul {ι H : Type*}
    (ideals : ι → Ideal (𝓞 K)) (D : Ideal (𝓞 K))
    (c phase : ι → ℂ) (G : ι → H → ℂ) (h : H) (i : ι) :
    kernelDivisorCoefficient ideals D c phase G h i =
      (if D ∣ ideals i then c i * phase i else 0) * G i h := by
  by_cases hd : D ∣ ideals i <;> simp [kernelDivisorCoefficient, hd]

variable (K) (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
local notation "OS" => S.integer K

/-- The complete positive-sign Gauss column on the actual S-integer ring.
Its multiplicative character retains its original zero extension, and
the frequency may be a nonunit or zero. -/
def actualSIntegerGauss (a : OS) (ha : a ≠ 0)
    (χ : MulChar (OS ⧸ Ideal.span ({a} : Set OS)) ℂ) (h : OS) : ℂ := by
  letI := finite_sIntegerPrincipalResidue K S a ha
  letI := Fintype.ofFinite (OS ⧸ Ideal.span ({a} : Set OS))
  exact completeResidueGauss (actualSIntegerTrace K S hS) a χ (Ideal.Quotient.mk _ h)

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable (Ray : Type*) [CommGroup Ray] [Fintype Ray]
local instance : Fintype ((Ray × Ray) →* Circle) := Fintype.ofFinite _

/-- The first residual mixed form is bounded by genuine whole Gauss norms.
The common finite factor is kept in the same row weight on both sides.
The normalized phase coefficients are constructed by finite Fourier
inversion, with total mass at most `(Nat.card Ray)^2` by
`fixed_phase_coefficient_mass`; no phase-mass bound is an assumption. -/
theorem first_residual_gauss_kernel_bound {ι κ : Type*}
    (F : 𝓢(V, ℂ)) (rows : Finset OS)
    (leftColumns : Finset ι) (rightColumns : Finset κ)
    (leftIdeals : ι → Ideal (𝓞 K)) (rightIdeals : κ → Ideal (𝓞 K))
    (hRight : ∀ j ∈ rightColumns, rightIdeals j ≠ ⊥)
    (a : ι → OS) (b : κ → OS) (ha : ∀ i, a i ≠ 0) (hb : ∀ j, b j ≠ 0)
    (χa : ∀ i, MulChar (OS ⧸ Ideal.span ({a i} : Set OS)) ℂ)
    (χb : ∀ j, MulChar (OS ⧸ Ideal.span ({b j} : Set OS)) ℂ)
    (phase : ι → κ → ℂ) (rayLeft : ι → Ray) (rayRight : κ → Ray)
    (phaseTable : Ray × Ray → Circle)
    (hphase : ∀ i j, IsCoprime (leftIdeals i) (rightIdeals j) →
      phase i j = (phaseTable (rayLeft i, rayRight j) : ℂ))
    (common q : OS → ℂ) (c : ι → ℂ) (d : κ → ℂ)
    (x : ι → V) (y : κ → V) (z : OS → V) :
    let G₁ := fun i h => actualSIntegerGauss K S hS (a i) (ha i) (χa i) h
    let G₂ := fun j h => actualSIntegerGauss K S hS (b j) (hb j) (χb j) (-h)
    let c₁ := fun D χ i => if D ∣ leftIdeals i then
      c i * (fixedLeftPhase Ray χ (rayLeft i) : ℂ) else 0
    let c₂ := fun D χ j => if D ∣ rightIdeals j then
      d j * (fixedRightPhase Ray χ (rayRight j) : ℂ) else 0
    ‖∑ h ∈ rows, q h * ∑ i ∈ leftColumns, ∑ j ∈ rightColumns,
      (if IsCoprime (leftIdeals i) (rightIdeals j) then
        common h * phase i j * (G₁ i h * star (G₂ j h)) else 0) *
        (c i * star (d j)) * F (z h + x i + y j)‖ ≤
      ∑ D ∈ divisorPool rightColumns rightIdeals, ‖(moebius D : ℂ)‖ *
        ∑ χ : (Ray × Ray) →* Circle, ‖fixedPhaseCoefficient Ray phaseTable χ‖ *
          ∫ ξ : V, ‖(𝓕 F) ξ‖ *
            (Real.sqrt (weightedEnergy rows (fun h => ‖q h * common h‖)
              (wholePolynomial leftColumns (fun i => c₁ D χ i * jointPhase ξ (x i)) G₁)) *
            Real.sqrt (weightedEnergy rows (fun h => ‖q h * common h‖)
              (wholePolynomial rightColumns
                (fun j => c₂ D χ j * star (jointPhase ξ (y j))) G₂))) := by
  dsimp only
  let G₁ := fun i h => actualSIntegerGauss K S hS (a i) (ha i) (χa i) h
  let G₂ := fun j h => actualSIntegerGauss K S hS (b j) (hb j) (χb j) (-h)
  have hbnd := full_correlation_kernel_bound F rows leftColumns rightColumns
    leftIdeals rightIdeals hRight
    (fun i j h => common h * phase i j * (G₁ i h * star (G₂ j h))) common q
    (fixedPhaseCoefficient Ray phaseTable)
    (fun χ i => (fixedLeftPhase Ray χ (rayLeft i) : ℂ))
    (fun χ j => (fixedRightPhase Ray χ (rayRight j) : ℂ)) G₁ G₂
    (fun i j h hc => by
      rw [hphase i j hc, fixed_phase_expansion Ray phaseTable])
    c d (fun h i => z h + x i) (fun _ j => y j)
  simpa only [kernelDivisorCoefficient_eq_mul, joint_energy_gauss_rows,
    joint_energy_conjugate_gauss_rows, G₁, G₂] using hbnd

end HeckeSkeleton.Moments.EngineStep

end

#print axioms HeckeSkeleton.Moments.EngineStep.joint_energy_gauss_rows
#print axioms HeckeSkeleton.Moments.EngineStep.first_residual_gauss_kernel_bound
