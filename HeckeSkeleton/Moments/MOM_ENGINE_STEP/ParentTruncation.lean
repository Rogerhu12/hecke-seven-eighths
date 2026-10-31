import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentSource
import HeckeGeneral.Analysis.SIntegerMaskedTruncation

/-!
# A finite first-transform expression for the actual parent

The cutoff and analytic order are common to all original column pairs and
all mask divisors.  The finite approximation is the actual orbital cutoff,
including all subgroup sectors and both zero contributions.  The tail is
proved from the uniform orbital theorem and retains the actual coefficient
mass of each pair; it is not a supplied error estimate.
-/

noncomputable section
open scoped Classical BigOperators nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Bridge
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {S : Finset (HeightOneSpectrum (𝓞 K))}
local notation "OS" => Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "L" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)} [Γ.FiniteIndex]
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

/-- The existing actual finite orbit approximation, with the original pair data. -/
def ParentPeriodicPair.finiteTransform (p : ParentPeriodicPair K S Γ)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) (X : ℝ) : ℂ :=
  sIntegerMaskedPeriodicApproximation K S Γ μv p.modulus p.modulus_ne_zero
    hS p.profile h M p.residue p.invariant r X

def ParentPeriodicPair.truncationMass (p : ParentPeriodicPair K S Γ)
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) : ℝ :=
  sIntegerMaskedTruncationMass K S p.modulus p.modulus_ne_zero M p.residue r

include ν μ in
/-- One finite cutoff for the actual whole parent, with constants and
original pair seminorm orders selected before the cutoff, moving mask,
moduli, columns, source profiles, and parent data. -/
theorem parent_first_finite_transform
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (decay : ℝ) (hdecay : 1 < decay) (order : ℕ)
    (horder : Module.finrank ℤ L < order)
    (hdegree : (Module.finrank ℚ K : ℝ) * decay ≤ order) :
    ∃ seminorms : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ X : ℝ, 1 ≤ X → ∀ M : Finset (HeightOneSpectrum OS),
      ∀ r : {r : ℝ // 0 < r},
      ∀ {ω ψ₀ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ₀)
        (a : RealParameters) (Z t Y₁ Y₂ : ℝ) {ι : Type*} (columns : Finset ι)
        (pairs : ι → ι → ParentPeriodicPair K S Γ) (B : ℕ),
      ParentSourceCalibration centered d a Z t Y₁ Y₂ columns pairs
        (sIntegerFiniteTestFunction K S h) r M B →
      pairedStageEnergy centered d a Z t Y₁ Y₂ ≤
        (B : ℝ) * ((∑ i ∈ columns, ∑ j ∈ columns,
            (pairs i j).finiteTransform μv hS h M r X).re +
          C * X ^ (1 - decay) * ∑ i ∈ columns, ∑ j ∈ columns,
            seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (pairs i j).profile *
              (pairs i j).truncationMass M r) := by
  obtain ⟨seminorms, C, hC, htail⟩ := exists_sIntegerMaskedPeriodicApproximation_bound
    K S Γ ν μv μ hS h hlc hcs decay hdecay order horder hdegree
  refine ⟨seminorms, C, hC, ?_⟩
  intro X hX M r ω ψ₀ centered d a Z t Y₁ Y₂ ι columns pairs B cal
  have hsource := parent_orbital_source_bound centered d a Z t Y₁ Y₂ columns pairs
    (sIntegerFiniteTestFunction K S h) (continuous_sIntegerFiniteTestFunction K S h hlc)
    (hasCompactSupport_sIntegerFiniteTestFunction K S h hcs) r M B cal
  have hp (i j : ι) :
      ((pairs i j).maskedSeries (sIntegerFiniteTestFunction K S h) r M).re ≤
        ((pairs i j).finiteTransform μv hS h M r X).re +
          C * X ^ (1 - decay) *
            (seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (pairs i j).profile *
              (pairs i j).truncationMass M r) := by
    have hb := (htail M (pairs i j).modulus (pairs i j).modulus_ne_zero
      (pairs i j).residue (pairs i j).invariant r (pairs i j).profile X hX).2
    have hb' : ‖(pairs i j).maskedSeries (sIntegerFiniteTestFunction K S h) r M -
        (pairs i j).finiteTransform μv hS h M r X‖ ≤
        C * X ^ (1 - decay) *
          (seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (pairs i j).profile *
            (pairs i j).truncationMass M r) := by
      convert hb using 1
      · rfl
      · unfold ParentPeriodicPair.truncationMass
        ring
    have hr := Complex.re_le_norm
      ((pairs i j).maskedSeries (sIntegerFiniteTestFunction K S h) r M -
        (pairs i j).finiteTransform μv hS h M r X)
    rw [Complex.sub_re] at hr
    linarith
  have hsum := Finset.sum_le_sum (s := columns) (fun i hi =>
    Finset.sum_le_sum (s := columns) (fun j hj => hp i j))
  have hsum' :
      (∑ i ∈ columns, ∑ j ∈ columns,
        (pairs i j).maskedSeries (sIntegerFiniteTestFunction K S h) r M).re ≤
      (∑ i ∈ columns, ∑ j ∈ columns, (pairs i j).finiteTransform μv hS h M r X).re +
        C * X ^ (1 - decay) * ∑ i ∈ columns, ∑ j ∈ columns,
          seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (pairs i j).profile *
            (pairs i j).truncationMass M r := by
    simpa only [Complex.re_sum, Finset.sum_add_distrib, Finset.mul_sum] using hsum
  exact hsource.trans (mul_le_mul_of_nonneg_left hsum' (Nat.cast_nonneg _))

end HeckeSkeleton.Moments.EngineStep

end

#print axioms HeckeSkeleton.Moments.EngineStep.parent_first_finite_transform

