import HeckeSkeleton.Moments.MOM_ENGINE_STEP.GaussSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstFiniteSource

/-!
# The whole Gauss energy is an actual second-transform source

The coefficients of the whole Gauss polynomial are independent of the
frequency row.  The original common Schwartz test supplies its actual
Haar profile on every orbit of the original subgroup.  The chart records
only positivity, domination of the original row weights, mask avoidance,
and the finite fibers of the row map.

The periodic pair identity, the Gram identity, absolute summability, and
the finite-to-orbital comparison are proved from the actual Gauss
columns.  The finite source is then formed explicitly from these pairs.
Its common physical cutoff, both additive zero terms, and its complete
tail mass are the ones already computed by `FirstFiniteSource`.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Bridge
open HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]
variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}
local notation "OS" => Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Q" => SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ
local notation "L" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]

/-- The original common test integrated against the actual norm-one Haar
measure, at the radius of the actual subgroup orbit. -/
def gaussSourceProfile
    (φ : SchwartzMap V ℂ)
    (ψ : ((v : (S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ)
    (r : {r : ℝ // 0 < r}) (q : Q) : ℂ :=
  sUnitOrbitalProfile K (S : Set (HeightOneSpectrum (𝓞 K)))
    (sLocalTensorTestFunction K (S : Set (HeightOneSpectrum (𝓞 K))) φ ψ)
    ⟨r.val * (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).val,
      mul_pos r.property
        (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).property⟩

/-- Primitive conditions on a positive original profile chart.  There is
no whole-energy bound, summed source equality, or convergence field. -/
structure GaussEnergyChart {H : Type*}
    (rows : Finset H) (rowMap : H → Q) (w : H → ℝ)
    (φ : SchwartzMap V ℂ)
    (ψ : ((v : (S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ)
    (r : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum OS)) (B : ℕ) : Prop where
  weight_nonneg : ∀ h ∈ rows, 0 ≤ w h
  profile_real : ∀ q : Q, (gaussSourceProfile φ ψ r q).im = 0
  profile_nonneg : ∀ q : Q, 0 ≤ (gaussSourceProfile φ ψ r q).re
  row_weight : ∀ h ∈ rows, w h ≤ (gaussSourceProfile φ ψ r (rowMap h)).re
  row_mask : ∀ h ∈ rows,
    sIntegerOrbitAvoidanceMask K (S : Set (HeightOneSpectrum (𝓞 K))) Γ M (rowMap h) = 1
  fiber : ∀ q : Q, (rows.filter (fun h => rowMap h = q)).card ≤ B

theorem GaussEnergyChart.profile_eq_real {H : Type*}
    {rows : Finset H} {rowMap : H → Q} {w : H → ℝ}
    {φ : SchwartzMap V ℂ}
    {ψ : ((v : (S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ}
    {r : {r : ℝ // 0 < r}} {M : Finset (HeightOneSpectrum OS)} {B : ℕ}
    (cal : GaussEnergyChart rows rowMap w φ ψ r M B) (q : Q) :
    gaussSourceProfile φ ψ r q = ((gaussSourceProfile φ ψ r q).re : ℂ) := by
  apply Complex.ext
  · rfl
  · exact cal.profile_real q

variable [Γ.FiniteIndex]

/-- The whole weighted Gauss energy is bounded by its genuine orbital
pair source.  All identities and all summability needed here are derived
from the original columns and the common actual Haar profile. -/
theorem gauss_energy_orbital_source_bound
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    {H ι : Type*} (rows : Finset H) (rowMap : H → Q) (w : H → ℝ)
    (columns : Finset ι) (c : ι → ℂ) (col : ι → OrbitalGaussColumn K S Γ)
    (φ : SchwartzMap V ℂ)
    (ψ : ((v : (S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (r : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum OS)) (B : ℕ)
    (cal : GaussEnergyChart rows rowMap w φ ψ r M B) :
    weightedEnergy rows w (fun h => ∑ i ∈ columns, c i * (col i).orbit hS (rowMap h)) ≤
      (B : ℝ) * (∑ i ∈ columns, ∑ j ∈ columns,
        ((col i).pair hS (col j) ((c i * star (c j)) • φ)).maskedSeries ψ r M).re := by
  let P : Q → ℂ := fun q => ∑ i ∈ columns, c i * (col i).orbit hS q
  let pairs : ι → ι → ParentPeriodicPair K S Γ :=
    fun i j => (col i).pair hS (col j) ((c i * star (c j)) • φ)
  let T : Q → ℂ := fun q =>
    ∑ i ∈ columns, ∑ j ∈ columns, (pairs i j).maskedTerm ψ r M q
  let imageRows : Finset Q := rows.image rowMap
  have hperiodic (i j : ι) (q : Q) :
      (pairs i j).orbitWeight q = (col i).orbit hS q * star ((col j).orbit hS q) :=
    (col i).pair_orbitWeight hS (col j) ((c i * star (c j)) • φ) q
  have hprofile (i j : ι) (q : Q) :
      (pairs i j).orbitProfile ψ r q =
        (c i * star (c j)) * gaussSourceProfile φ ψ r q :=
    (col i).pair_profile hS (col j) φ (c i) (c j) ψ r q
  have hgram (q : Q) : T q =
      sIntegerOrbitAvoidanceMask K (S : Set (HeightOneSpectrum (𝓞 K))) Γ M q *
        gaussSourceProfile φ ψ r q * (P q * star (P q)) := by
    dsimp only [T, P]
    rw [star_sum, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [ParentPeriodicPair.maskedTerm, hperiodic, hprofile]
    simp only [star_mul]
    ring
  have hre (q : Q) : (T q).re =
      (sIntegerOrbitAvoidanceMask K (S : Set (HeightOneSpectrum (𝓞 K))) Γ M q).re *
        (gaussSourceProfile φ ψ r q).re * ‖P q‖ ^ 2 := by
    rw [hgram, cal.profile_eq_real q, Complex.star_def, Complex.mul_conj',
      ← Complex.ofReal_pow]
    rcases sIntegerOrbitAvoidanceMask_zero_or_one K
      (S : Set (HeightOneSpectrum (𝓞 K))) Γ M q with hz | ho
    · simp only [hz, zero_mul, Complex.zero_re]
    · rw [ho, one_mul, Complex.one_re, one_mul,
        ← Complex.ofReal_mul, Complex.ofReal_re]
      simp only [Complex.ofReal_re]
  have hnonneg (q : Q) : 0 ≤ (T q).re := by
    rw [hre]
    have hm : 0 ≤
        (sIntegerOrbitAvoidanceMask K (S : Set (HeightOneSpectrum (𝓞 K))) Γ M q).re := by
      rcases sIntegerOrbitAvoidanceMask_zero_or_one K
        (S : Set (HeightOneSpectrum (𝓞 K))) Γ M q with hmask | hmask <;> simp [hmask]
    exact mul_nonneg (mul_nonneg hm (cal.profile_nonneg q)) (sq_nonneg _)
  have hpairs (i j : ι) : Summable ((pairs i j).maskedTerm ψ r M) :=
    (pairs i j).maskedTerm_summable ψ hψ hψcs r M
  have hinner (i : ι) : Summable
      (fun q : Q => ∑ j ∈ columns, (pairs i j).maskedTerm ψ r M q) :=
    summable_sum (fun j hj => hpairs i j)
  have hsum : Summable T := summable_sum (fun i hi => hinner i)
  have hsumre : Summable (fun q => (T q).re) :=
    (Complex.hasSum_re hsum.hasSum).summable
  have htotal : (∑' q, T q) =
      ∑ i ∈ columns, ∑ j ∈ columns, (pairs i j).maskedSeries ψ r M := by
    change (∑' q, ∑ i ∈ columns, ∑ j ∈ columns,
      (pairs i j).maskedTerm ψ r M q) = _
    rw [Summable.tsum_finsetSum (fun i hi => hinner i)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Summable.tsum_finsetSum (fun j hj => hpairs i j)]
    rfl
  have hweight (q : Q) :
      (∑ h ∈ rows.filter (fun h => rowMap h = q), w h) ≤
        (B : ℝ) * (gaussSourceProfile φ ψ r q).re := by
    calc
      _ ≤ ∑ h ∈ rows.filter (fun h => rowMap h = q),
          (gaussSourceProfile φ ψ r q).re := by
        apply Finset.sum_le_sum
        intro h hh
        obtain ⟨hr, he⟩ := Finset.mem_filter.mp hh
        simpa only [he] using cal.row_weight h hr
      _ = ((rows.filter (fun h => rowMap h = q)).card : ℝ) *
          (gaussSourceProfile φ ψ r q).re := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr (cal.fiber q)) (cal.profile_nonneg q)
  have hfiber := weightedEnergy_fiber_bound rows imageRows rowMap w
    (fun q => (B : ℝ) * (gaussSourceProfile φ ψ r q).re) P
    (fun h hh => Finset.mem_image_of_mem rowMap hh) (fun q hq => hweight q)
  have hpoint (q : Q) (hq : q ∈ imageRows) :
      (gaussSourceProfile φ ψ r q).re * ‖P q‖ ^ 2 = (T q).re := by
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hq
    rw [hre, cal.row_mask h hh, Complex.one_re, one_mul]
  calc
    _ ≤ (B : ℝ) * ∑ q ∈ imageRows,
        (gaussSourceProfile φ ψ r q).re * ‖P q‖ ^ 2 := by
      simpa only [weightedEnergy, Function.comp_apply, Finset.mul_sum, mul_assoc, P]
        using hfiber
    _ = (B : ℝ) * ∑ q ∈ imageRows, (T q).re := by
      congr 1
      exact Finset.sum_congr rfl hpoint
    _ ≤ (B : ℝ) * ∑' q, (T q).re :=
      mul_le_mul_of_nonneg_left
        (hsumre.sum_le_tsum imageRows (fun q hq => hnonneg q)) (Nat.cast_nonneg _)
    _ = _ := by rw [← Complex.re_tsum hsum, htotal]

/-- The actual second-transform source of one whole Gauss polynomial.
The pair modulus, residue, and Schwartz profile are computed, not supplied. -/
def gaussFiniteSource
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    {ι : Type*} (columns : Finset ι) (c : ι → ℂ)
    (col : ι → OrbitalGaussColumn K S Γ) (φ : SchwartzMap V ℂ)
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r})
    (X : ℝ) (hX : 1 ≤ X) : FirstFiniteSource K S Γ ι ι where
  leftColumns := columns
  rightColumns := columns
  pairs i j := (col i).pair hS (col j) ((c i * star (c j)) • φ)
  mask := M
  radius := r
  cutoff := X
  cutoff_ge_one := hX

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

include ν μ in
/-- A genuine finite second transform bounds the complete weighted Gauss
energy.  The constant and seminorms are chosen before all moving data;
the tail is the computed mass of the actual product-modulus pairs. -/
theorem gauss_energy_finite_source_bound
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (decay : ℝ) (hdecay : 1 < decay) (order : ℕ)
    (horder : Module.finrank ℤ L < order)
    (hdegree : (Module.finrank ℚ K : ℝ) * decay ≤ order) :
    ∃ seminorms : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ X : ℝ, ∀ hX : 1 ≤ X, ∀ M : Finset (HeightOneSpectrum OS),
      ∀ r : {r : ℝ // 0 < r}, ∀ {H ι : Type*},
      ∀ (rows : Finset H) (rowMap : H → Q) (w : H → ℝ) (B : ℕ)
        (columns : Finset ι) (c : ι → ℂ) (col : ι → OrbitalGaussColumn K S Γ)
        (φ : SchwartzMap V ℂ),
      GaussEnergyChart rows rowMap w φ (sIntegerFiniteTestFunction K S h) r M B →
      let source := gaussFiniteSource hS columns c col φ M r X hX
      weightedEnergy rows w (fun a => ∑ i ∈ columns, c i * (col i).orbit hS (rowMap a)) ≤
        (B : ℝ) * ((source.transform μv hS h).re +
          C * X ^ (1 - decay) * ∑ i ∈ columns, ∑ j ∈ columns,
            seminorms.sup (schwartzSeminormFamily ℂ V ℂ) ((c i * star (c j)) • φ) *
              (source.pairs i j).truncationMass M r) := by
  obtain ⟨seminorms, C, hC, htail⟩ := finite_source_uniform_bound
    (K := K) (S := S) (Γ := Γ) ν μv μ hS h hlc hcs decay hdecay order horder hdegree
  refine ⟨seminorms, C, hC, ?_⟩
  intro X hX M r H ι rows rowMap w B columns c col φ cal
  let source := gaussFiniteSource hS columns c col φ M r X hX
  have hsource := gauss_energy_orbital_source_bound hS rows rowMap w columns c col φ
    (sIntegerFiniteTestFunction K S h) (continuous_sIntegerFiniteTestFunction K S h hlc)
    (hasCompactSupport_sIntegerFiniteTestFunction K S h hcs) r M B cal
  have ht := htail source
  have hre := Complex.re_le_norm
    ((∑ i ∈ columns, ∑ j ∈ columns,
      ((col i).pair hS (col j) ((c i * star (c j)) • φ)).maskedSeries
        (sIntegerFiniteTestFunction K S h) r M) - source.transform μv hS h)
  rw [Complex.sub_re] at hre
  have hb :
      (∑ i ∈ columns, ∑ j ∈ columns,
        ((col i).pair hS (col j) ((c i * star (c j)) • φ)).maskedSeries
          (sIntegerFiniteTestFunction K S h) r M).re ≤
        (source.transform μv hS h).re +
          C * X ^ (1 - decay) * ∑ i ∈ columns, ∑ j ∈ columns,
            seminorms.sup (schwartzSeminormFamily ℂ V ℂ) ((c i * star (c j)) • φ) *
              (source.pairs i j).truncationMass M r := by
    exact (sub_le_iff_le_add.mp (hre.trans ht)).trans_eq (add_comm _ _)
  exact hsource.trans (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _))

end HeckeSkeleton.Moments.EngineStep

end

#print axioms HeckeSkeleton.Moments.EngineStep.gauss_energy_orbital_source_bound
#print axioms HeckeSkeleton.Moments.EngineStep.gauss_energy_finite_source_bound

