import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalRowBallChart
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolSecondStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstGaussData

set_option linter.unusedSectionVars false

/-!
# The actual orbital fibres of the original Gauss rows

The finite multiplicity is computed from the literal element-to-orbit
map.  Direct rows are the original quotient representatives, with a
fixed nonzero multiplier (in particular either sign), and have unit
fibres.  Sixth-power amplified rows retain their genuine multiplicity:
each orbital fibre injects into the large prime divisors of its output
ideal.  No injectivity assertion about an arbitrary enlarged row set is
used.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {Γ : Subgroup A.U}

local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ

@[simp] theorem engineElementOrbit_out (q : Q) :
    engineElementOrbit (Γ := Γ) q.out.val = q := by
  sorry

theorem engineElementOrbit_mul (a b : A.R) (ha : a ≠ 0) (hb : b ≠ 0) :
    engineElementOrbit (Γ := Γ) (a * b) =
      sIntegerOrbitDilation K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
        ⟨b, hb⟩ (engineElementOrbit (Γ := Γ) a) := by
  sorry

theorem engineElementOrbit_cancel_mul {a a' b : A.R}
    (ha : a ≠ 0) (ha' : a' ≠ 0) (hb : b ≠ 0)
    (he : engineElementOrbit (Γ := Γ) (a * b) =
      engineElementOrbit (Γ := Γ) (a' * b)) :
    engineElementOrbit (Γ := Γ) a = engineElementOrbit (Γ := Γ) a' := by
  sorry

/-- The quotient map of actual signed representatives is injective;
the representatives themselves are not replaced by allowed generators. -/
theorem engineElementOrbit_out_mul_injective (b : A.R) (hb : b ≠ 0) :
    Function.Injective (fun q : Q => engineElementOrbit (Γ := Γ) (q.out.val * b)) := by
  sorry

theorem engineElementOrbit_generatedIdeal (I : A.Exterior)
    (h : A.R) (hh : A.Generates I h) :
    ProbeOrbitNormSum.principalExterior A (engineElementOrbit (Γ := Γ) h).out = I := by
  sorry

theorem engineElementOrbit_norm_of_generates (I : A.Exterior)
    (h : A.R) (hh : A.Generates I h) :
    (sIntegerOrbitNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
      (engineElementOrbit (Γ := Γ) h)).val = (Ideal.absNorm I.val : ℝ) := by
  sorry

theorem originalFrequencyIdeal_out_norm (q : Q) :
    A.exteriorNorm (originalFrequencyIdeal q.out.val) =
      (sIntegerOrbitNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ q).val := by
  sorry

theorem originalFrequencyIdeal_neg_out_norm (q : Q) :
    A.exteriorNorm (originalFrequencyIdeal (-q.out.val)) =
      (sIntegerOrbitNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ q).val := by
  sorry

/-- The exact maximum of the actual finite orbital fibre sizes. -/
def engineOrbitMultiplicity (rows : Finset A.R) : ℕ :=
  rows.sup (fun h => (rows.filter (fun h' =>
    engineElementOrbit (Γ := Γ) h' = engineElementOrbit (Γ := Γ) h)).card)

theorem engineOrbit_fibre_le_multiplicity (rows : Finset A.R) (q : Q) :
    (rows.filter (fun h => engineElementOrbit (Γ := Γ) h = q)).card ≤
      engineOrbitMultiplicity (Γ := Γ) rows := by
  sorry

theorem engineOrbitMultiplicity_le (rows : Finset A.R) (B : ℕ)
    (hB : ∀ q : Q,
      (rows.filter (fun h => engineElementOrbit (Γ := Γ) h = q)).card ≤ B) :
    engineOrbitMultiplicity (Γ := Γ) rows ≤ B := by
  sorry

/-- Every subset of the original representative image has unit fibres.
Taking `b = 1` or `b = -1` gives the two actual first-Cauchy sides. -/
theorem engineOrbit_image_fibres_le_one (source : Finset Q)
    (b : A.R) (hb : b ≠ 0) (rows : Finset A.R)
    (hrows : rows ⊆ source.image (fun q => q.out.val * b)) (q : Q) :
    (rows.filter (fun h => engineElementOrbit (Γ := Γ) h = q)).card ≤ 1 := by
  sorry

theorem engineOrbit_image_multiplicity_le_one (source : Finset Q)
    (b : A.R) (hb : b ≠ 0) (rows : Finset A.R)
    (hrows : rows ⊆ source.image (fun q => q.out.val * b)) :
    engineOrbitMultiplicity (Γ := Γ) rows ≤ 1 := by
  sorry

/-- A raw representative recipe gives the required injectivity on the
original rows, before the prime amplification is applied. -/
theorem engineOrbit_image_injOn (source : Finset Q)
    (b : A.R) (hb : b ≠ 0) (rows : Finset A.R)
    (hrows : rows ⊆ source.image (fun q => q.out.val * b)) :
    Set.InjOn (engineElementOrbit (Γ := Γ)) (rows : Set A.R) := by
  sorry

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {htrace : A.ContainsTraceBadPlaces}

/-- For a fixed auxiliary prime, cancellation of the actual nonzero
sixth power is injective on the original orbit rows.  Distinct primes
in a fibre divide the same original output ideal. -/
theorem actualFrequencyAmplify_orbit_fibre_count
    (C : A.GeneralArithmeticContext σ η htrace)
    (rows : Finset A.R) (rowIdeal : A.R → A.Exterior)
    (hrows : ∀ h ∈ rows, A.Generates (rowIdeal h) h)
    (hinj : Set.InjOn (engineElementOrbit (Γ := Γ)) (rows : Set A.R))
    (pairs : Finset (A.R × ExteriorPrime A))
    (hpairs : ∀ x ∈ pairs, x.1 ∈ rows)
    (q : Q)
    (houtput : ∀ x ∈ pairs, engineElementOrbit (Γ := Γ) (actualFrequencyAmplify C x) = q)
    (Z ell B : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hlower : ∀ x ∈ pairs, Z ^ ell ≤ (Ideal.absNorm x.2.val.asIdeal : ℝ))
    (hupper : (Ideal.absNorm (ProbeOrbitNormSum.principalExterior A q.out).val : ℝ) ≤ Z ^ B) :
    (pairs.card : ℝ) ≤ B / ell := by
  sorry

/-- The actual enlarged element row set retains this finite orbital
multiplicity.  It is controlled by original row and prime norm windows,
with no factor equal to the size of the auxiliary prime pool. -/
theorem actualFrequencyAmplify_orbit_output_fibres
    (C : A.GeneralArithmeticContext σ η htrace)
    (rows : Finset A.R) (rowIdeal : A.R → A.Exterior)
    (hrows : ∀ h ∈ rows, A.Generates (rowIdeal h) h)
    (hinj : Set.InjOn (engineElementOrbit (Γ := Γ)) (rows : Set A.R))
    (pool : Finset (ExteriorPrime A)) (allow : A.R → ExteriorPrime A → Prop)
    (Z ell M L : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hpl : ∀ p ∈ pool, Z ^ ell ≤ (Ideal.absNorm p.val.asIdeal : ℝ))
    (hpu : ∀ p ∈ pool, (Ideal.absNorm p.val.asIdeal : ℝ) ≤ Z ^ L)
    (hhu : ∀ h ∈ rows, (Ideal.absNorm (rowIdeal h).val : ℝ) ≤ Z ^ M)
    (q : Q) :
    ((((eligiblePairs rows pool allow).image (actualFrequencyAmplify C)).filter
      (fun h => engineElementOrbit (Γ := Γ) h = q)).card : ℝ) ≤ (M + 6 * L) / ell := by
  sorry

namespace FirstGaussPoolData

variable {C : A.GeneralArithmeticContext σ η htrace}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}

/-- The enlarged norm window follows from the original row window
and the actual single sixth-power prime insertion. -/
theorem main_originalFrequencyIdeal_norm_le (d : FirstGaussPoolData C P ι)
    (h : A.R) (hh : h ∈ d.mainRows) :
    A.exteriorNorm (originalFrequencyIdeal h) ≤ Z ^ (d.rowExponent + 6 * ell) := by
  sorry

theorem error_originalFrequencyIdeal_norm_le (d : FirstGaussPoolData C P ι)
    (p : ExteriorPrime A) (h : A.R) (hh : h ∈ d.errorRows p) :
    A.exteriorNorm (originalFrequencyIdeal h) ≤ Z ^ d.rowExponent := by
  sorry

/-- The pool keeps the exact orbital multiplicity of its actual main
row image. The earlier original representative recipe proves the input
injectivity; the enlarged rows need not be injective. -/
theorem main_orbit_fibres_le (d : FirstGaussPoolData C P ι)
    (source : Finset Q) (b : A.R) (hb : b ≠ 0)
    (horiginal : d.rows ⊆ source.image (fun q => q.out.val * b)) (q : Q) :
    ((d.mainRows.filter (fun h => engineElementOrbit (Γ := Γ) h = q)).card : ℝ) ≤
      d.multiplicity := by
  sorry

theorem main_orbit_multiplicity_le (d : FirstGaussPoolData C P ι)
    (source : Finset Q) (b : A.R) (hb : b ≠ 0)
    (horiginal : d.rows ⊆ source.image (fun q => q.out.val * b)) :
    engineOrbitMultiplicity (Γ := Γ) d.mainRows ≤ ⌈d.multiplicity⌉₊ := by
  sorry

/-- A fixed original exponent window chooses the integer fibre cap
before the scale, prime pool and moving source are used. -/
theorem main_orbit_multiplicity_le_uniform (M : ℝ)
    (d : FirstGaussPoolData C P ι) (hM : d.rowExponent ≤ M)
    (source : Finset Q) (b : A.R) (hb : b ≠ 0)
    (horiginal : d.rows ⊆ source.image (fun q => q.out.val * b)) :
    engineOrbitMultiplicity (Γ := Γ) d.mainRows ≤
      ⌈(M + 6 * ell) / (ell / 2)⌉₊ := by
  sorry

/-- Valuation corrections use subsets of the same original signed
representative image, so they retain unit orbital fibres. -/
theorem error_orbit_multiplicity_le_one (d : FirstGaussPoolData C P ι)
    (source : Finset Q) (b : A.R) (hb : b ≠ 0)
    (horiginal : d.rows ⊆ source.image (fun q => q.out.val * b))
    (p : ExteriorPrime A) :
    engineOrbitMultiplicity (Γ := Γ) (d.errorRows p) ≤ 1 := by
  sorry

end FirstGaussPoolData

section CanonicalFirst

variable (C : A.GeneralArithmeticContext σ η htrace)
variable {ι κ : Type*} (left : Finset ι) (right : Finset κ)
variable (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
variable (DE : Ideal (𝓞 K) × Ideal (𝓞 K))
variable (hDE : DE ∈ commonSupportPool left right
  (fun i => (fullI i).val) (fun j => (fullJ j).val))

theorem canonicalFirstLeftGaussData_orbit_multiplicity_le_one (rows : Finset Q) :
    engineOrbitMultiplicity (Γ := Γ)
      (canonicalFirstLeftGaussData C left right fullI fullJ DE hDE rows).rows ≤ 1 := by
  sorry

theorem canonicalFirstRightGaussData_orbit_multiplicity_le_one (rows : Finset Q) :
    engineOrbitMultiplicity (Γ := Γ)
      (canonicalFirstRightGaussData C left right fullI fullJ DE hDE rows).rows ≤ 1 := by
  sorry

theorem canonicalFirstLeftGaussData_norm_le (rows : Finset Q)
    (R : ℝ) (hR : ∀ q ∈ rows,
      (sIntegerOrbitNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ q).val ≤ R)
    (h : A.R) (hh : h ∈
      (canonicalFirstLeftGaussData C left right fullI fullJ DE hDE rows).rows) :
    A.exteriorNorm (originalFrequencyIdeal h) ≤ R := by
  sorry

theorem canonicalFirstRightGaussData_norm_le (rows : Finset Q)
    (R : ℝ) (hR : ∀ q ∈ rows,
      (sIntegerOrbitNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ q).val ≤ R)
    (h : A.R) (hh : h ∈
      (canonicalFirstRightGaussData C left right fullI fullJ DE hDE rows).rows) :
    A.exteriorNorm (originalFrequencyIdeal h) ≤ R := by
  sorry

end CanonicalFirst

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.engineOrbit_image_fibres_le_one
#print axioms HeckeSkeleton.Moments.EngineStep.actualFrequencyAmplify_orbit_fibre_count
#print axioms HeckeSkeleton.Moments.EngineStep.actualFrequencyAmplify_orbit_output_fibres
#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.main_orbit_multiplicity_le
#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.main_orbit_multiplicity_le_uniform
#print axioms HeckeSkeleton.Moments.EngineStep.canonicalFirstRightGaussData_orbit_multiplicity_le_one
#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.main_originalFrequencyIdeal_norm_le
#print axioms HeckeSkeleton.Moments.EngineStep.canonicalFirstRightGaussData_norm_le
