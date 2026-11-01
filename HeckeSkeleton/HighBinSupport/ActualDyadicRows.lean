import HeckeSkeleton.HighBinSupport.DyadicRowPartition
import HeckeSkeleton.HighBinSupport.ActualDetectorBoundary

/-!
# The dyadic partition of the actual moderate frequency rows

Membership in the original finite frequency-row envelope is equivalent
to the literal norm cutoff. Its reverse direction explicitly reconstructs
the original ideal/sector index in `frequencyRows`.

The moderate source retains the original global upper cutoff. Intersecting
each full shell with this source is exactly the canonical dyadic fiber,
including the strict-lower, closed-upper endpoint convention. Thus the
last shell does not add rows beyond the global moderate range.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinDyadicRows

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeSkeleton.HighBinCanonicalBoundary
open HighBinVerified.Dyadic
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Every original frequency row below the norm cutoff occurs in the
original ideal/sector enumeration. No arithmetic sector is discarded. -/
theorem mem_frequencyRows_of_norm_le {U : ℝ} (hU : 0 ≤ U)
    (u : FrequencyRow K S) (hu : frequencyRowNorm K S u ≤ U) :
    u ∈ frequencyRows K S U := by
  letI : Fintype (SixthUnitClasses K S) := Fintype.ofFinite _
  let F := (dyadicIdealSupport K (U / 2)).filter fun I =>
    (∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val → p ∉ S) ∧
      (∀ p : HeightOneSpectrum (𝓞 K), primeExponents I p < 6)
  have hsupport : u.ideal.val ∈ dyadicIdealSupport K (U / 2) := by
    apply (mem_dyadicIdealSupport_iff K (div_nonneg hU (by norm_num)) u.ideal.val).mpr
    rw [show 2 * (U / 2) = U by ring]
    exact hu
  have hI : u.ideal.val ∈ F :=
    Finset.mem_filter.mpr ⟨hsupport, u.ideal.property, u.sixthPowerFree⟩
  unfold frequencyRows
  apply Finset.mem_image.mpr
  refine ⟨(⟨u.ideal.val, hI⟩, u.sector), ?_, ?_⟩
  · exact Finset.mem_product.mpr ⟨Finset.mem_attach _ _, Finset.mem_univ _⟩
  · cases u
    rfl

theorem mem_frequencyRows_iff {U : ℝ} (hU : 0 ≤ U) (u : FrequencyRow K S) :
    u ∈ frequencyRows K S U ↔ frequencyRowNorm K S u ≤ U :=
  ⟨HighBinBoundary.ActualEstimate.frequencyRowNorm_le_of_mem_rows K S hU u,
    mem_frequencyRows_of_norm_le K S hU u⟩

/-- The original finite moderate range with its global upper cutoff. -/
def moderateSource (Z upper : ℝ) : Finset (FrequencyRow K S) :=
  (frequencyRows K S (Z ^ upper)).filter fun u =>
    Z ^ (1 / 16 : ℝ) < frequencyRowNorm K S u ∧ ¬ principalFrequencyRow K S u

theorem moderateSource_bounds (Z upper : ℝ) (hZ : 0 ≤ Z)
    (u : FrequencyRow K S) (hu : u ∈ moderateSource K S Z upper) :
    Z ^ (1 / 16 : ℝ) < frequencyRowNorm K S u ∧ frequencyRowNorm K S u ≤ Z ^ upper := by
  obtain ⟨hmem, hlo, _⟩ := Finset.mem_filter.mp hu
  exact ⟨hlo, (mem_frequencyRows_iff K S (Real.rpow_nonneg hZ _) u).mp hmem⟩

theorem moderateSource_nonprincipal (Z upper : ℝ)
    (u : FrequencyRow K S) (hu : u ∈ moderateSource K S Z upper) :
    ¬ principalFrequencyRow K S u := (Finset.mem_filter.mp hu).2.2

/-- A source mask with the original norm and nonprincipal properties
turns the literal full shell into exactly the deterministic dyadic fiber. -/
theorem maskedShellRows_eq_shellFiber_of_source
    (source : Finset (FrequencyRow K S)) {Z lower upper : ℝ} (hZ : 1 < Z)
    (hsource : ∀ u ∈ source,
      Z ^ lower < frequencyRowNorm K S u ∧ frequencyRowNorm K S u ≤ Z ^ upper)
    (hnonprincipal : ∀ u ∈ source, ¬ principalFrequencyRow K S u)
    (j : Fin (shellCount Z lower upper)) :
    maskedShellRows K S source Z (shellExponent Z lower j.val) =
      shellFiber (frequencyRowNorm K S) source Z lower upper j := by
  rw [shellFiber_eq_annulus (frequencyRowNorm K S) source hZ hsource j]
  ext u
  have hU : 0 ≤ 2 * Z ^ shellExponent Z lower j.val := by
    apply mul_nonneg (by norm_num)
    exact Real.rpow_nonneg (by linarith) _
  constructor
  · intro hu
    obtain ⟨hmem, huSource⟩ := Finset.mem_filter.mp hu
    obtain ⟨hrow, hlo, _⟩ := Finset.mem_filter.mp hmem
    exact Finset.mem_filter.mpr ⟨huSource, hlo, (mem_frequencyRows_iff K S hU u).mp hrow⟩
  · intro hu
    obtain ⟨huSource, hlo, hhi⟩ := Finset.mem_filter.mp hu
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨(mem_frequencyRows_iff K S hU u).mpr hhi,
        hlo, hnonprincipal u huSource⟩, huSource⟩

/-- Actual moderate rows satisfy every source condition internally. -/
theorem maskedShellRows_eq_shellFiber (Z upper : ℝ) (hZ : 1 < Z)
    (j : Fin (shellCount Z (1 / 16) upper)) :
    maskedShellRows K S (moderateSource K S Z upper) Z (shellExponent Z (1 / 16) j.val) =
      shellFiber (frequencyRowNorm K S) (moderateSource K S Z upper) Z (1 / 16) upper j :=
  maskedShellRows_eq_shellFiber_of_source K S (moderateSource K S Z upper) hZ
    (fun u hu => moderateSource_bounds K S Z upper (by linarith) u hu)
    (moderateSource_nonprincipal K S Z upper) j

/-- Every actual source row occurs in one retained dyadic shell. -/
theorem maskedShellRows_covers (Z upper : ℝ) (hZ : 1 < Z)
    (u : FrequencyRow K S) (hu : u ∈ moderateSource K S Z upper) :
    ∃ j : Fin (shellCount Z (1 / 16) upper),
      u ∈ maskedShellRows K S (moderateSource K S Z upper) Z
        (shellExponent Z (1 / 16) j.val) := by
  obtain ⟨j, hj⟩ := shellFiber_covers (frequencyRowNorm K S) (moderateSource K S Z upper) hZ
    (fun u hu => moderateSource_bounds K S Z upper (by linarith) u hu) u hu
  exact ⟨j, by simpa only [maskedShellRows_eq_shellFiber K S Z upper hZ] using hj⟩

/-- Distinct actual shells never repeat a source row, including rows on
an exact dyadic endpoint. -/
theorem maskedShellRows_disjoint (Z upper : ℝ) (hZ : 1 < Z)
    {i j : Fin (shellCount Z (1 / 16) upper)} (hij : i ≠ j) :
    Disjoint
      (maskedShellRows K S (moderateSource K S Z upper) Z (shellExponent Z (1 / 16) i.val))
      (maskedShellRows K S (moderateSource K S Z upper) Z (shellExponent Z (1 / 16) j.val)) := by
  rw [maskedShellRows_eq_shellFiber K S Z upper hZ,
    maskedShellRows_eq_shellFiber K S Z upper hZ]
  exact shellFiber_disjoint (frequencyRowNorm K S) (moderateSource K S Z upper)
    Z (1 / 16) upper hij

/-- The literal sum over the masked arithmetic shells preserves the
original moderate source exactly. -/
theorem sum_maskedShellRows {M : Type*} [AddCommMonoid M]
    (Z upper : ℝ) (hZ : 1 < Z) (value : FrequencyRow K S → M) :
    (∑ j : Fin (shellCount Z (1 / 16) upper),
      ∑ u ∈ maskedShellRows K S (moderateSource K S Z upper) Z
        (shellExponent Z (1 / 16) j.val), value u) =
      ∑ u ∈ moderateSource K S Z upper, value u := by
  simp_rw [maskedShellRows_eq_shellFiber K S Z upper hZ]
  exact sum_shellFiber (frequencyRowNorm K S) (moderateSource K S Z upper) hZ
    (fun u hu => moderateSource_bounds K S Z upper (by linarith) u hu) value

end HeckeSkeleton.HighBinDyadicRows
