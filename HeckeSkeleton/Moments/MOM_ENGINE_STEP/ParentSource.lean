import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentMoment
import HeckeGeneral.Analysis.SIntegerMaskedOrbitalPoisson
import HeckePort.Moments.Descent.Fibers

/-!
# From the actual parent to its first orbital transform

The source calibration consists of individual column and profile identities.
It permits the original coefficients to depend on the row: each column pair
has its own genuine Schwartz test and its own complete periodic residue
function.  A pointwise Gram identity for those original tests supplies
positivity before Poisson.  This is the source chart that an admissible
profile provider must construct; a Fourier seminorm bound alone does not
construct that chart.

The finite row pushforward, expansion of the whole centered coefficient,
absolute orbital summability, and first Poisson formula are proved here.
There is no parent-moment bound, summed transform identity, or convergence
assumption in the calibration.  The result retains every orbit of the
original subgroup, every mask divisor, and both actual additive zero terms.
-/

noncomputable section
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open MeasureTheory HeckePort.Moments

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
local notation "Q" => SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ

/-- The actual periodic and archimedean input for one original column pair.
The modulus can vary with the pair; no enlarged common modulus is imposed. -/
structure ParentPeriodicPair where
  modulus : OS
  modulus_ne_zero : modulus ≠ 0
  residue : (OS ⧸ Ideal.span ({modulus} : Set OS)) → ℂ
  invariant : ∀ u : Γ, ∀ a : OS,
    residue (Ideal.Quotient.mk _
      (((S : Set (HeightOneSpectrum (𝓞 K))).unitEquivUnitsInteger K u.val).val * a)) =
        residue (Ideal.Quotient.mk _ a)
  profile : SchwartzMap V ℂ

variable {K S Γ}

def ParentPeriodicPair.orbitWeight (p : ParentPeriodicPair K S Γ) : Q → ℂ :=
  sIntegerPeriodicOrbitWeight K _ Γ p.modulus p.residue p.invariant

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]

def ParentPeriodicPair.orbitProfile (p : ParentPeriodicPair K S Γ)
    (ψ : ((v : (S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ)
    (r : {r : ℝ // 0 < r}) (q : Q) : ℂ :=
  sUnitOrbitalProfile K (S : Set (HeightOneSpectrum (𝓞 K)))
    (sLocalTensorTestFunction K (S : Set (HeightOneSpectrum (𝓞 K))) p.profile ψ)
    ⟨r.val * (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).val,
      mul_pos r.property (sIntegerOrbitNorm K _ Γ q).property⟩

def ParentPeriodicPair.maskedTerm (p : ParentPeriodicPair K S Γ)
    (ψ : ((v : (S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ)
    (r : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum OS)) (q : Q) : ℂ :=
  sIntegerOrbitAvoidanceMask K _ Γ M q * p.orbitWeight q * p.orbitProfile ψ r q

def ParentPeriodicPair.maskedSeries (p : ParentPeriodicPair K S Γ)
    (ψ : ((v : (S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ)
    (r : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum OS)) : ℂ :=
  sIntegerWeightedOrbitalSeries K S Γ p.profile ψ r
    (fun q => sIntegerOrbitAvoidanceMask K _ Γ M q * p.orbitWeight q)

variable [Γ.FiniteIndex]

theorem ParentPeriodicPair.maskedTerm_summable (p : ParentPeriodicPair K S Γ)
    (ψ : ((v : (S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (r : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum OS)) :
    Summable (p.maskedTerm ψ r M) :=
  (summable_norm_sIntegerMaskedOrbitalProfile K S Γ p.profile ψ hψ hψcs r M
    p.orbitWeight (sIntegerPeriodicResidueL1 K _ p.modulus p.modulus_ne_zero p.residue)
    (norm_sIntegerPeriodicOrbitWeight_le_L1 K _ Γ p.modulus p.modulus_ne_zero
      p.residue p.invariant)).of_norm

/-- Pointwise source data, before any row sum or Fourier transform.
`coefficient` retains the entire centered difference and all live slots.
The `gram` field calibrates the original pair profiles, not their Fourier
transforms and not a summed parent energy. -/
structure ParentSourceCalibration {ω ψ₀ : HeckeCharacter K}
    (centered : Bool) (d : MomentData K ω ψ₀) (a : RealParameters)
    (Z t Y₁ Y₂ : ℝ) {ι : Type*} (columns : Finset ι)
    (pairs : ι → ι → ParentPeriodicPair K S Γ)
    (ψ : ((v : (S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ)
    (r : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum OS)) (B : ℕ) where
  rowMap : NonzeroIdeal K → Q
  coefficient : Q → ι → ℂ
  phase : Q → ι → ℂ
  weight : Q → ℝ
  weight_nonneg : ∀ q, 0 ≤ weight q
  row_weight : ∀ u ∈ pairedRows d a Z, 1 ≤ weight (rowMap u)
  row_mask : ∀ u ∈ pairedRows d a Z,
    sIntegerOrbitAvoidanceMask K _ Γ M (rowMap u) = 1
  fiber : ∀ q : Q, ((pairedRows d a Z).filter (fun u => rowMap u = q)).card ≤ B
  polynomial : ∀ u ∈ pairedRows d a Z,
    pairedStagePolynomial centered d u (Z ^ a.n₁) (Z ^ a.n₂) Y₁ Y₂ Z t =
      ∑ i ∈ columns, coefficient (rowMap u) i * phase (rowMap u) i
  periodic : ∀ i ∈ columns, ∀ j ∈ columns, ∀ q,
    (pairs i j).orbitWeight q = phase q i * star (phase q j)
  gram : ∀ i ∈ columns, ∀ j ∈ columns, ∀ q,
    (pairs i j).orbitProfile ψ r q =
      (weight q : ℂ) * (coefficient q i * star (coefficient q j))

/-- The actual parent is bounded by actual masked orbital series, using
only finite fibers and the source's pointwise column/profile calibration. -/
theorem parent_orbital_source_bound {ω ψ₀ : HeckeCharacter K}
    (centered : Bool) (d : MomentData K ω ψ₀) (a : RealParameters)
    (Z t Y₁ Y₂ : ℝ) {ι : Type*} (columns : Finset ι)
    (pairs : ι → ι → ParentPeriodicPair K S Γ)
    (ψ : ((v : (S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (r : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum OS)) (B : ℕ)
    (cal : ParentSourceCalibration centered d a Z t Y₁ Y₂ columns pairs ψ r M B) :
    pairedStageEnergy centered d a Z t Y₁ Y₂ ≤
      (B : ℝ) * (∑ i ∈ columns, ∑ j ∈ columns, (pairs i j).maskedSeries ψ r M).re := by
  let P : Q → ℂ := fun q => ∑ i ∈ columns, cal.coefficient q i * cal.phase q i
  let T : Q → ℂ := fun q =>
    ∑ i ∈ columns, ∑ j ∈ columns, (pairs i j).maskedTerm ψ r M q
  let imageRows : Finset Q := (pairedRows d a Z).image cal.rowMap
  have hgram (q : Q) : T q =
      sIntegerOrbitAvoidanceMask K _ Γ M q * (cal.weight q : ℂ) *
        (P q * star (P q)) := by
    dsimp only [T, P]
    rw [star_sum, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [ParentPeriodicPair.maskedTerm, cal.periodic i hi j hj q, cal.gram i hi j hj q]
    simp only [star_mul]
    ring
  have hre (q : Q) : (T q).re =
      (sIntegerOrbitAvoidanceMask K _ Γ M q).re * cal.weight q * ‖P q‖ ^ 2 := by
    rw [hgram, Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow]
    rcases sIntegerOrbitAvoidanceMask_zero_or_one K _ Γ M q with h | h
    · simp only [h, zero_mul, Complex.zero_re]
    · rw [h, one_mul, Complex.one_re, one_mul,
        ← Complex.ofReal_mul, Complex.ofReal_re]
  have hnonneg (q : Q) : 0 ≤ (T q).re := by
    rw [hre]
    have hm : 0 ≤ (sIntegerOrbitAvoidanceMask K _ Γ M q).re := by
      rcases sIntegerOrbitAvoidanceMask_zero_or_one K _ Γ M q with h | h <;> simp [h]
    exact mul_nonneg (mul_nonneg hm (cal.weight_nonneg q)) (sq_nonneg _)
  have hpairs (i j : ι) : Summable ((pairs i j).maskedTerm ψ r M) :=
    (pairs i j).maskedTerm_summable ψ hψ hψcs r M
  have hinner (i : ι) : Summable
      (fun q : Q => ∑ j ∈ columns, (pairs i j).maskedTerm ψ r M q) :=
    summable_sum (fun j hj => hpairs i j)
  have hsum : Summable T := summable_sum (fun i hi => hinner i)
  have hsumre : Summable (fun q => (T q).re) := (Complex.hasSum_re hsum.hasSum).summable
  have htotal : (∑' q, T q) =
      ∑ i ∈ columns, ∑ j ∈ columns, (pairs i j).maskedSeries ψ r M := by
    change (∑' q, ∑ i ∈ columns, ∑ j ∈ columns,
      (pairs i j).maskedTerm ψ r M q) = _
    rw [Summable.tsum_finsetSum (fun i hi => hinner i)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Summable.tsum_finsetSum (fun j hj => hpairs i j)]
    rfl
  have hparent : pairedStageEnergy centered d a Z t Y₁ Y₂ =
      weightedEnergy (pairedRows d a Z) (fun _ => 1) (P ∘ cal.rowMap) := by
    unfold pairedStageEnergy weightedEnergy
    apply Finset.sum_congr rfl
    intro u hu
    rw [cal.polynomial u hu]
    simp only [one_mul, Function.comp_apply, P]
  have hfiber := weightedEnergy_fiber_bound (pairedRows d a Z) imageRows cal.rowMap
    (fun _ => 1) (fun _ => (B : ℝ)) P
    (fun u hu => Finset.mem_image_of_mem cal.rowMap hu)
    (fun q hq => by simpa using (Nat.cast_le.mpr (cal.fiber q) :
      (((pairedRows d a Z).filter (fun u => cal.rowMap u = q)).card : ℝ) ≤ (B : ℝ)))
  have hpoint (q : Q) (hq : q ∈ imageRows) : ‖P q‖ ^ 2 ≤ (T q).re := by
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hq
    rw [hre, cal.row_mask u hu, Complex.one_re, one_mul]
    exact le_mul_of_one_le_left (sq_nonneg _) (cal.row_weight u hu)
  calc
    _ ≤ (B : ℝ) * ∑ q ∈ imageRows, ‖P q‖ ^ 2 := by
      rw [hparent]
      simpa only [weightedEnergy, Finset.mul_sum] using hfiber
    _ ≤ (B : ℝ) * ∑ q ∈ imageRows, (T q).re :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpoint) (Nat.cast_nonneg _)
    _ ≤ (B : ℝ) * ∑' q, (T q).re :=
      mul_le_mul_of_nonneg_left
        (hsumre.sum_le_tsum imageRows (fun q hq => hnonneg q)) (Nat.cast_nonneg _)
    _ = _ := by rw [← Complex.re_tsum hsum, htotal]

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

/-- The explicit first transformed pair, with both genuine zero terms.
This is a definition of the provider's right-hand side, not transform data. -/
def ParentPeriodicPair.firstTransform (p : ParentPeriodicPair K S Γ)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) : ℂ :=
  ∑ D ∈ M.powerset, (moebius (IdealMobiusMask.primeProduct D) : ℂ) *
    (sIntegerMaskPoissonFactor K S p.modulus p.modulus_ne_zero r (sIntegerMaskGenerator K _ D) *
      sIntegerWeightedOrbitalSeries K S Γ (traceSchwartzFourier K p.profile)
        (sIntegerFiniteFourierTestFunction K S μv h)
        (sIntegerMaskDualRadius K S p.modulus p.modulus_ne_zero r (sIntegerMaskGenerator K _ D))
        (sIntegerPeriodicFourierOrbitWeight K _ hS Γ p.modulus p.modulus_ne_zero
          p.residue p.invariant (sIntegerMaskGenerator K _ D).val) +
      ((sUnitHaarCovolume K (S : Set (HeightOneSpectrum (𝓞 K))) Γ).toReal : ℂ) *
        (sIntegerMaskPoissonFactor K S p.modulus p.modulus_ne_zero r (sIntegerMaskGenerator K _ D) *
            (sIntegerPeriodicDivisorFourier K _ hS p.modulus p.modulus_ne_zero p.residue
                (sIntegerMaskGenerator K _ D).val 0 *
              sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K p.profile) h 0) -
          p.residue 0 * sIntegerTensorTerm K S (traceSchwartzToMixed K p.profile) h 0))

include ν μ in
theorem ParentPeriodicPair.maskedSeries_eq_firstTransform (p : ParentPeriodicPair K S Γ)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) :
    p.maskedSeries (sIntegerFiniteTestFunction K S h) r M = p.firstTransform μv hS h M r :=
  sIntegerMaskedPeriodicOrbitalPoisson K S Γ p.modulus p.modulus_ne_zero hS ν μv μ
    p.profile h hlc hcs M p.residue p.invariant r

include ν μ in
/-- First-transform bound for the actual centered or uncentered parent.
All summed identities and orbital convergence are discharged internally. -/
theorem parent_first_orbital_transform {ω ψ₀ : HeckeCharacter K}
    (centered : Bool) (d : MomentData K ω ψ₀) (a : RealParameters)
    (Z t Y₁ Y₂ : ℝ) {ι : Type*} (columns : Finset ι)
    (pairs : ι → ι → ParentPeriodicPair K S Γ)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (r : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum OS)) (B : ℕ)
    (cal : ParentSourceCalibration centered d a Z t Y₁ Y₂ columns pairs
      (sIntegerFiniteTestFunction K S h) r M B) :
    pairedStageEnergy centered d a Z t Y₁ Y₂ ≤
      (B : ℝ) * (∑ i ∈ columns, ∑ j ∈ columns,
        (pairs i j).firstTransform μv hS h M r).re := by
  have hsource := parent_orbital_source_bound centered d a Z t Y₁ Y₂ columns pairs
    (sIntegerFiniteTestFunction K S h) (continuous_sIntegerFiniteTestFunction K S h hlc)
    (hasCompactSupport_sIntegerFiniteTestFunction K S h hcs) r M B cal
  have hrewrite (i j : ι) := ParentPeriodicPair.maskedSeries_eq_firstTransform
    ν μv μ (pairs i j) hS h hlc hcs M r
  simpa only [hrewrite] using hsource

end HeckeSkeleton.Moments.EngineStep

end

#print axioms HeckeSkeleton.Moments.EngineStep.parent_orbital_source_bound
#print axioms HeckeSkeleton.Moments.EngineStep.parent_first_orbital_transform
