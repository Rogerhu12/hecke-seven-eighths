import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectGaussSource

/-!
# Primitive original Gauss data without a prime-pool parameter

The direct entrance needs the original finite rows and columns only.
In particular it does not require a positive pool exponent, density, or
any auxiliary pool whose existence would fail at the zero-slot entrance.
It still produces the same `ActualGaussSource` used by the universal
second transform and capacity algorithm.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {ι : Type*}

/-- Only the genuine finite arithmetic data needed for direct
enlargement. No positive-pool witness or density is present. -/
structure DirectGaussData (C : A.GeneralArithmeticContext σ η hS) (ι : Type*) where
  rows : Finset A.R
  row_nonzero : ∀ h ∈ rows, h ≠ 0
  columns : Finset ι
  ideal : ι → A.Exterior
  generator : ι → A.R
  generates : ∀ i, A.Generates (ideal i) (generator i)
  allowed : ∀ i ∈ columns, A.IsAllowed C.correction.B
    (Units.mk0 (generator i : K) (by exact_mod_cast (generates i).1))

namespace DirectGaussData

def directSource (d : DirectGaussData C ι) (c : ι → ℂ) : ActualGaussSource C ι where
  rows := d.rows
  row_nonzero := d.row_nonzero
  columns := d.columns
  ideal := d.ideal
  generator := d.generator
  generates := d.generates
  allowed := d.allowed
  coefficient := c

def gaussColumn (d : DirectGaussData C ι)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (i : ι) (h : A.R) : ℂ :=
  actualSIntegerGauss K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) hDiff
    (d.generator i) (d.generates i).1
    (generatedIdealCharacter (σ := σ) (d.ideal i) (d.generator i) (d.generates i)) h

theorem directSource_energy (d : DirectGaussData C ι) (c : ι → ℂ) :
    (d.directSource c).energy hDiff =
      ∑ h ∈ d.rows, ‖wholePolynomial d.columns c (d.gaussColumn hDiff) h‖ ^ 2 := rfl

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem directSource_twisted (d : DirectGaussData C ι)
    (c : ι → ℂ) (x : ι → V) (ξ : V) :
    d.directSource (FirstGaussPoolData.twistedCoefficient c x ξ) =
      (d.directSource c).withMultiplier (fun i => jointPhase ξ (x i)) := by
  unfold directSource ActualGaussSource.withMultiplier
  congr 1
  funext i
  exact mul_comm _ _

theorem directSource_phaseEnergy (d : DirectGaussData C ι)
    (c : ι → ℂ) (x : ι → V) (ξ : V) :
    (d.directSource c).phaseEnergy (hDiff := hDiff) x ξ =
      (d.directSource (FirstGaussPoolData.twistedCoefficient c x ξ)).energy hDiff := by
  rw [directSource_twisted]
  rfl

theorem weighted_direct_energy_bound {H : Type*}
    (d : DirectGaussData C ι)
    (rows : Finset H) (frequency : H → A.R)
    (hinj : Set.InjOn frequency (rows : Set H))
    (hrows : rows.image frequency ⊆ d.rows)
    (q : H → ℂ) (W : ℝ) (hW : 0 ≤ W)
    (hq : ∀ h ∈ rows, ‖q h‖ ≤ W) (c : ι → ℂ) :
    weightedEnergy rows (fun h => ‖q h‖)
      (fun h => wholePolynomial d.columns c (d.gaussColumn hDiff) (frequency h)) ≤
        W * (d.directSource c).energy hDiff := by
  rw [d.directSource_energy c]
  calc
    _ ≤ W * ∑ h ∈ rows,
        ‖wholePolynomial d.columns c (d.gaussColumn hDiff) (frequency h)‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun h hh => mul_le_mul_of_nonneg_right (hq h hh) (sq_nonneg _)
    _ = W * ∑ h ∈ rows.image frequency,
        ‖wholePolynomial d.columns c (d.gaussColumn hDiff) h‖ ^ 2 := by
      rw [Finset.sum_image hinj]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg hrows (fun h _ _ => sq_nonneg _)) hW

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem direct_twisted_integrable (d : DirectGaussData C ι)
    (F : 𝓢(V, ℂ)) (c : ι → ℂ) (x : ι → V) :
    Integrable (fun ξ => (d.directSource
      (FirstGaussPoolData.twistedCoefficient c x ξ)).energy hDiff)
      (actualFourierMeasure F) := by
  simpa only [d.directSource_phaseEnergy c x] using
    (d.directSource c).phaseEnergy_integrable (hDiff := hDiff) F x

end DirectGaussData

namespace FirstGaussPoolData

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}

def originalData (d : FirstGaussPoolData C P ι) : DirectGaussData C ι where
  rows := d.rows
  row_nonzero h hh := (d.row_generates h hh).1
  columns := d.columns
  ideal := d.ideal
  generator := d.generator
  generates := d.generates
  allowed := d.allowed

theorem originalData_source (d : FirstGaussPoolData C P ι) (c : ι → ℂ) :
    d.originalData.directSource c = d.directSource c := rfl

end FirstGaussPoolData

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.DirectGaussData.weighted_direct_energy_bound
#print axioms HeckeSkeleton.Moments.EngineStep.DirectGaussData.direct_twisted_integrable
