import Expansion.PhysicalRecipeRemainders
import Expansion.ActualLargeInfiniteTransport
import Expansion.ActualRetainedComponents

/-!
# Exact assembly of every actual nonprincipal frequency

The original nonprincipal initial integral is first truncated on its
literal height cube.  The resulting absolutely convergent row series is
then split at the two original norm cutoffs.  Small rows, the clipped
moderate schedule, and the strict large tail have disjoint endpoints.

Each of the three pieces uses its proved contour identity.  The final
formula therefore contains the original retained components and exactly
the five nonprincipal remainders used by the actual recipe.  No infinite
sum identity, integrability assertion, or contour move is an input to
that formula.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler
open Expansion.PhysicalInitialMellin
open ExpansionInterfaces
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))

local instance physicalOuter_sectorFintype : Fintype (SixthUnitClasses K Sset) :=
  Fintype.ofFinite _

/-- A summable original row function has an exact nonprincipal partition.
The strict large cutoff automatically excludes the unique principal norm.
The finite small lower endpoint remains the original zero endpoint. -/
theorem nonprincipal_frequencyRow_sum_partition
    {lower upper : ℝ} (hlower : 0 ≤ lower) (hupper : 1 ≤ upper)
    (hlowerUpper : lower ≤ upper) (f : FrequencyRow K Sset → ℂ) (hf : Summable f) :
    (∑' u : {u : FrequencyRow K Sset // ¬principalFrequencyRow K Sset u}, f u.val) =
      (∑ u ∈ (frequencyRows K Sset lower).filter
        (fun u => 0 < frequencyRowNorm K Sset u ∧ ¬principalFrequencyRow K Sset u), f u) +
      (∑ u ∈ (frequencyRows K Sset upper).filter
        (fun u => lower < frequencyRowNorm K Sset u ∧ ¬principalFrequencyRow K Sset u), f u) +
      ∑' u : {u : FrequencyRow K Sset // upper < frequencyRowNorm K Sset u}, f u.val := by
  have hupper0 : 0 ≤ upper := zero_le_one.trans hupper
  let head := (frequencyRows K Sset upper).filter
    (fun u => ¬principalFrequencyRow K Sset u)
  let small := (frequencyRows K Sset lower).filter
    (fun u => 0 < frequencyRowNorm K Sset u ∧ ¬principalFrequencyRow K Sset u)
  let middle := (frequencyRows K Sset upper).filter
    (fun u => lower < frequencyRowNorm K Sset u ∧ ¬principalFrequencyRow K Sset u)
  have hsmall : head.filter (fun u => frequencyRowNorm K Sset u ≤ lower) = small := by
    ext u
    simp only [head, small, Finset.mem_filter]
    rw [mem_frequencyRows_iff K Sset upper hupper0 u,
      mem_frequencyRows_iff K Sset lower hlower u]
    constructor
    · rintro ⟨⟨_, hn⟩, hl⟩
      exact ⟨hl, idealNorm_pos K u.ideal.val, hn⟩
    · rintro ⟨hl, _, hn⟩
      exact ⟨⟨hl.trans hlowerUpper, hn⟩, hl⟩
  have hmiddle : head.filter (fun u => ¬frequencyRowNorm K Sset u ≤ lower) = middle := by
    ext u
    simp only [head, middle, Finset.mem_filter, not_le]
    tauto
  let fN : FrequencyRow K Sset → ℂ :=
    {u | ¬principalFrequencyRow K Sset u}.indicator f
  have hfN : Summable fN := hf.indicator _
  have hfinite : (∑ u ∈ frequencyRows K Sset upper, fN u) =
      (∑ u ∈ small, f u) + ∑ u ∈ middle, f u := by
    calc
      _ = ∑ u ∈ head, f u := by
        simp only [head, fN, Finset.sum_filter, Set.indicator_apply, Set.mem_setOf_eq]
      _ = _ := by
        simpa only [hsmall, hmiddle] using
          (Finset.sum_filter_add_sum_filter_not head
            (fun u => frequencyRowNorm K Sset u ≤ lower) f).symm
  have hlarge :
      (∑' u : {u : FrequencyRow K Sset // u ∉ frequencyRows K Sset upper}, fN u.val) =
        ∑' u : {u : FrequencyRow K Sset // upper < frequencyRowNorm K Sset u}, f u.val := by
    rw [tsum_subtype, tsum_subtype]
    apply tsum_congr
    intro u
    by_cases hu : upper < frequencyRowNorm K Sset u
    · have hnot : u ∉ frequencyRows K Sset upper := by
        rw [mem_frequencyRows_iff K Sset upper hupper0 u]
        exact not_le.mpr hu
      have hnon : ¬principalFrequencyRow K Sset u := by
        intro hp
        have hnorm := frequencyRowNorm_of_principal K S u hp
        linarith
      simp [fN, hnot, hu, hnon]
    · have hmem : u ∈ frequencyRows K Sset upper :=
        (mem_frequencyRows_iff K Sset upper hupper0 u).mpr (le_of_not_gt hu)
      simp [hmem, hu]
  calc
    _ = ∑' u : FrequencyRow K Sset, fN u := tsum_subtype _ _
    _ = (∑ u ∈ frequencyRows K Sset upper, fN u) +
        ∑' u : {u : FrequencyRow K Sset // u ∉ frequencyRows K Sset upper}, fN u.val :=
      (hfN.sum_add_tsum_subtype_compl (frequencyRows K Sset upper)).symm
    _ = _ := by rw [hfinite, hlarge]

variable [∀ p : HeightOneSpectrum (𝓞 K), MeasurableSpace (p.adicCompletion K)]
variable [∀ p : HeightOneSpectrum (𝓞 K), BorelSpace (p.adicCompletion K)]
variable (mu : ∀ p : HeightOneSpectrum (𝓞 K), Measure (p.adicCompletion K))
variable [∀ p, (mu p).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
variable [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (nu : Measure (FiniteAdeleRing (𝓞 K) K)) [nu.IsAddHaarMeasure]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
local notation "muS" => (fun p : Sset => mu (Subtype.val p))

include nu in
/-- The partition applies to the literal initial boxes because their
absolute row convergence follows from the actual initial kernel. -/
theorem actual_nonprincipal_initial_box_partition
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {zeta Z : ℝ} (hzeta : 0 < zeta) (hZ : 1 ≤ Z) (H : ℝ) :
    (∑' u : {u : FrequencyRow K Sset // ¬principalFrequencyRow K Sset u},
      rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g ∅ u.val Z H 5 5 3) =
      finiteRowContourBlock K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g ∅ Z H 0 (Z ^ (1 / 16 : ℝ)) 5 5 3 +
      finiteRowContourBlock K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g ∅ Z H (Z ^ (1 / 16 : ℝ)) (Z ^ (13 / 16 + zeta)) 5 5 3 +
      actualLargeInitialBoxes K S mu P psi g Z H zeta := by
  letI : IsTotallyComplex K := ⟨hcomplex⟩
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hlower : 0 ≤ Z ^ (1 / 16 : ℝ) := (Real.rpow_pos_of_pos hZpos _).le
  have hupper : 1 ≤ Z ^ (13 / 16 + zeta) := Real.one_le_rpow hZ (by linarith)
  have hcut : Z ^ (1 / 16 : ℝ) ≤ Z ^ (13 / 16 + zeta) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hs := summable_actualInitialRowBoxes K S mu nu P hAllowed psi hcal hunram g ∅ hZpos H
  simpa only [finiteRowContourBlock, actualLargeInitialBoxes] using
    nonprincipal_frequencyRow_sum_partition K S hlower hupper hcut
      (fun u => rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g ∅ u Z H 5 5 3) hs

include nu in
/-- The complete nonprincipal initial series splits into its finite
height boxes and exactly its own summable exterior-height integrals. -/
theorem actual_nonprincipal_initial_integral_eq_boxes_add_tail
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {Z : ℝ} (hZ : 0 < Z) (H : ℝ) :
    (∑' u : FrequencyRow K Sset, if principalFrequencyRow K Sset u then 0
      else actualInitialRowIntegral K S mu P psi g ∅ Z u) =
      (∑' u : {u : FrequencyRow K Sset // ¬principalFrequencyRow K Sset u},
        rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
          g ∅ u.val Z H 5 5 3) + actualNonprincipalInitialTailSum K S mu P psi g Z H := by
  letI : IsTotallyComplex K := ⟨hcomplex⟩
  calc
    _ = ∑' u : {u : FrequencyRow K Sset // ¬principalFrequencyRow K Sset u},
        actualInitialRowIntegral K S mu P psi g ∅ Z u.val := by
      rw [tsum_subtype]
      simp only [Set.indicator_apply, Set.mem_setOf_eq, ite_not]
    _ = _ := by
      simp_rw [actualInitialRowIntegral_eq_box_add_tail K S mu nu P hAllowed psi hcal hunram
        g ∅ hZ H]
      exact ((summable_actualInitialRowBoxes K S mu nu P hAllowed psi hcal hunram
        g ∅ hZ H).subtype (fun u => ¬principalFrequencyRow K Sset u)).tsum_add
        ((summable_actualInitialRowTailIntegral K S mu nu P hAllowed psi hcal hunram
          g ∅ hZ H).subtype (fun u => ¬principalFrequencyRow K Sset u))

/-- The strict subtype sum is exactly the original retained large-row
indicator sum, including every sector. -/
theorem actualLargeTargetBoxes_eq_actualLargeRetained
    (P : ProbeData K Sset) (psi : HeckeCharacter K) (g : PrimeWindowGeometry)
    (Z H zeta : ℝ) :
    actualLargeTargetBoxes K S mu P psi g Z H zeta =
      actualLargeRetained K S mu P psi g Z H zeta := by
  simpa only [actualLargeTargetBoxes, actualLargeRetained, actualLargeRetainedTerm,
    Set.indicator_apply, Set.mem_setOf_eq] using!
    (tsum_subtype
      {u : FrequencyRow K Sset | Z ^ (13 / 16 + zeta) < frequencyRowNorm K Sset u}
      (fun u => rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g ∅ u Z H 2 2 (1 + 3 / zeta)))

include nu in
/-- Every actual nonprincipal initial row contributes once to a retained
component or to one of the five literal nonprincipal remainders. -/
theorem actual_nonprincipal_initial_recipe_expansion
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K)
    (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {B e zeta Z H : ℝ}
    (hB0 : 51 / 100 ≤ B) (hB : 7 / 8 < B) (hB1 : B ≤ 1)
    (he : 0 < e) (he1 : e ≤ 1 / 10000) (hzeta : 0 < zeta)
    (hZ : 1 < Z) (hH : 1 ≤ H)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    (∑' u : FrequencyRow K Sset, if principalFrequencyRow K Sset u then 0
      else actualInitialRowIntegral K S mu P psi g ∅ Z u) =
      actualSmallRetained K S mu P psi g Z H B e +
      actualLargeRetained K S mu P psi g Z H zeta +
      (∑ j : Fin (shellCount Z (1 / 16) (13 / 16 + zeta)),
        ∑ c : PhysicalRecipeChoice K Sset B e,
          physicalRecipeBlockValue K Sset P (arithmeticHighEulerData K Sset P psi)
            omega psi hpsi hB0 hB1 he hboundary muS g ∅ zeta Z H j c) +
      (actualNonprincipalInitialTailSum K S mu P psi g Z H +
        actualSmallRowHorizontalFaces K S mu P psi g ∅ Z H B e +
        actualLargeHorizontalFaces K S mu P psi g Z H zeta +
        physicalScheduledModerateFaces K S mu P (arithmeticHighEulerData K Sset P psi)
          omega psi hpsi hB0 hB1 he hboundary g zeta Z H +
        physicalScheduledWholeBoundary K S mu P (arithmeticHighEulerData K Sset P psi)
          omega psi hpsi hB0 hB1 he hboundary g zeta Z H) := by
  letI : IsTotallyComplex K := ⟨hcomplex⟩
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have heSmall : e < 1 / 1000 := by linarith
  have hi := actual_nonprincipal_initial_integral_eq_boxes_add_tail K S mu nu hcomplex
    P psi hAllowed hcal hunram g hZpos H
  have hp := actual_nonprincipal_initial_box_partition K S mu nu hcomplex P psi
    hAllowed hcal hunram g hzeta hZ.le H
  have hs := actual_small_initial_finite_transport K S mu nu P omega psi hpsi hAllowed
    g ∅ hB hB1 he heSmall hZpos hH0 hboundary
  have hl := (actual_large_initial_boxes_transport K S mu nu hcomplex P omega psi
    hpsi hAllowed hcal hunram g hB hB1 he heSmall hzeta hZ.le hH hboundary).2.2
  have hm := physicalScheduled_moderate_initial_transport K S mu nu P omega psi
    hpsi hB0 hB1 he hboundary g hcomplex hAllowed hB he1 zeta Z H hZ hH0
  rw [hi, hp, sub_eq_iff_eq_add.mp hs, sub_eq_iff_eq_add.mp hl, hm,
    actualLargeTargetBoxes_eq_actualLargeRetained]
  unfold actualSmallRetained
  ring

end Expansion.Project

#print axioms Expansion.Project.nonprincipal_frequencyRow_sum_partition
#print axioms Expansion.Project.actual_nonprincipal_initial_box_partition
#print axioms Expansion.Project.actual_nonprincipal_initial_integral_eq_boxes_add_tail
#print axioms Expansion.Project.actual_nonprincipal_initial_recipe_expansion
