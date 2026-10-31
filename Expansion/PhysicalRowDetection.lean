import Expansion.CanonicalRowSaturation
import Expansion.CanonicalCutoff
import Expansion.DetectorHeightGeometry
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Actual detection on the physical shell and buffered zero bins

The cutoff is the explicit smooth dyadic cutoff. The internal e, epsilon,
and positive height ceiling are chosen before tau; the common threshold
then precedes every shell, row, source exponent, bin and finite height index.
Only the actual selected/upper zero-bin predicates remain as row inputs.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Bridge
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ExpansionRecipe
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.ExpansionDetectorBridge HeckeSkeleton.HeckeBufferedReciprocal
open Expansion.ActualTerminalSaturation Expansion.Dyadic
open scoped Classical BigOperators ContDiff

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (E : RowEulerData K S P) (ψ : HeckeCharacter K)

/-- Output data from the actual detector, including its proof obligations.
These estimates are outputs and are never fields of the raw recipe input. -/
structure CanonicalDyadicDetection (u : FrequencyRow K S)
    (U a t η τ T : ℝ) (N : ℕ) where
  presentation : Fin 2
  zero : ℂ
  inverseIndex : ℕ
  plainIndex : ℕ
  fourier : ℝ
  zero_order : 0 < meromorphicOrderAt
    (heckeContinuation K (canonicalDetectorCharacter K ψ S P E presentation u)) zero
  zero_lower : a ≤ zero.re
  zero_upper : zero.re ≤ 1
  inverseIndex_le : inverseIndex ≤ dyadicCap (3 * U ^ (21 : ℕ))
  plainIndex_le : plainIndex ≤ dyadicCap (3 * U ^ (21 : ℕ))
  fourier_bound : ‖fourier‖ ≤ U ^ τ / (8 * Real.pi + 8)
  frequency_bound : |2 * Real.pi * fourier - zero.im| ≤ 3 * ((N : ℝ) + 1) * T
  source_support :
    (2 : ℝ) ^ inverseIndex < 4 * U ^ t ∧
      U ^ t / 8 < (2 : ℝ) ^ inverseIndex * (2 : ℝ) ^ plainIndex ∧
      (2 : ℝ) ^ inverseIndex * (2 : ℝ) ^ plainIndex < 8 * U ^ (21 : ℕ)
  saturation :
    let r := dyadicLength U inverseIndex
    let m := dyadicLength U plainIndex
    let ν := 2 * Real.pi * fourier - zero.im
    let χ := canonicalDetectorCharacter K ψ S P E presentation u
    let M := inverseDetectorValue K χ (originalDeletedPrimes K S u.ideal.val)
      cutoffProfile (U ^ t) U inverseIndex zero.re ν
    let Q := plainDetectorValue K χ (originalDeletedPrimes K S u.ideal.val)
      U plainIndex zero.re ν
    U ^ ((2 * a - 1) * (r + m) - η) ≤ ‖M * Q‖ ^ 2 ∧
    ‖M‖ ^ 2 ≤ U ^ ((2 * a - 1) * r + η) ∧
    ‖Q‖ ^ 2 ≤ U ^ ((2 * a - 1) * min m (1 - m) + η) ∧
    U ^ ((2 * a - 1) * r - 2 * η) ≤ ‖M‖ ^ 2 ∧
    U ^ ((2 * a - 1) * m - 2 * η) ≤ ‖Q‖ ^ 2 ∧
    m ≤ 1 / 2 + 75 * η ∧
    Real.log (U ^ t) / Real.log U - 1 / 2 - 75 * η - Real.log 8 / Real.log U ≤ r

/-- Genuine physical rows supply the two actual saturated factors with
one fixed choice of all internal parameters. The source cutoff remains
exactly U^t throughout the construction. -/
theorem exists_physical_row_detection
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex) (N : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ e ε ceiling : ℝ,
      0 < e ∧ e < 1 / 1000 ∧ 0 < ε ∧ 0 < ceiling ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ ceiling →
        ∃ Z₀ : ℝ, 2 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
          ∀ d t a : ℝ, 1 / 16 ≤ d → d ≤ 1 → 1 ≤ t → t ≤ 3 / 2 → 51 / 100 ≤ a →
          ∀ h : ℕ, h ≤ N → ∀ u : FrequencyRow K S,
            Z ^ d < frequencyRowNorm K S u → frequencyRowNorm K S u ≤ 2 * Z ^ d →
            rowZeroAbove K S ψ {1} P E u (ExpansionInterfaces.selectedHeight h (Z ^ τ)) a →
            rowZeroBelow K S ψ {1} P E u (ExpansionInterfaces.upperHeight h (Z ^ τ)) (a + 2 * e) →
            Nonempty (CanonicalDyadicDetection K S P E ψ u (Z ^ d) a t η τ (Z ^ τ) N) := by
  have hdegree : 0 ≤ heightDegree K := by unfold heightDegree; positivity
  obtain ⟨e, ε, ceiling, he, heSmall, hε, hceiling, hbudget⟩ :=
    exists_detector_numerical_budget (heightDegree K) η hdegree hη
  refine ⟨e, ε, ceiling, he, heSmall, hε, hceiling, ?_⟩
  intro τ hτ hτc
  obtain ⟨hzbudget, hforward, hreflected⟩ := hbudget τ hτ hτc
  obtain ⟨U₀, hU₀, hdetect⟩ := exists_canonical_row_saturation K S P E ψ hcomplex
    he heSmall hε cutoffProfile cutoffProfile_smooth cutoffProfile_one cutoffProfile_zero
    cutoffProfile_norm_le (fun x _ => cutoffProfile_complement_norm_le x)
    (3 * ((N : ℝ) + 1) + 2) (32 * τ) (32 * τ) τ η
    (by positivity) (by positivity) hτ hη hzbudget hforward hreflected
  obtain ⟨Z₁, hZ₁⟩ := (tendsto_atTop_atTop.mp
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 16))) U₀
  obtain ⟨Z₂, hZ₂⟩ := (tendsto_atTop_atTop.mp (tendsto_rpow_atTop hτ)) (3 * (N : ℝ))
  refine ⟨max 2 (max Z₁ Z₂), le_max_left _ _, ?_⟩
  intro Z hZ d t a hd hd' ht ht' ha h hh u huLower huUpper habove hbelow
  have hZtwo : 2 ≤ Z := (le_max_left _ _).trans hZ
  have hZone : 1 ≤ Z := by linarith
  have hU : U₀ ≤ Z ^ d :=
    (hZ₁ Z ((le_max_left _ _).trans ((le_max_right _ _).trans hZ))).trans
      (Real.rpow_le_rpow_of_exponent_le hZone hd)
  have hUone : 1 ≤ Z ^ d := by linarith [hU₀.trans hU]
  have hUpos : 0 < Z ^ d := by linarith
  have hT : 1 ≤ Z ^ τ := Real.one_le_rpow hZone hτ.le
  have hTN : 3 * (N : ℝ) ≤ Z ^ τ :=
    hZ₂ Z ((le_max_right _ _).trans ((le_max_right _ _).trans hZ))
  have hD : 2 ≤ (Z ^ d) ^ t := by
    have hp := Real.rpow_le_rpow_of_exponent_le hUone ht
    rw [Real.rpow_one] at hp
    linarith [hU₀.trans hU]
  have hDU := Real.rpow_le_rpow_of_exponent_le hUone ht'
  have hzeroheight := selected_height_power_envelope N h hh Z d τ hZone hd hd' hτ.le hTN
  have hupperheight := upper_height_power_envelope N h hh Z d τ hZone hd hd' hτ.le
  have hUT := (shell_height_powers Z d τ hZone hd hd' hτ.le).1
  have hpadding := physical_fourier_padding h (Z ^ d) (Z ^ τ) τ hUpos.le hT hUT
  obtain ⟨i, ρ, hz, hβ, hβ', hγ, j, hj, k, hk, ξ, hξ, hsupp, hsat⟩ :=
    hdetect u (Z ^ d) a (ExpansionInterfaces.selectedHeight h (Z ^ τ)) (Z ^ τ)
      (ExpansionInterfaces.upperHeight h (Z ^ τ)) ((Z ^ d) ^ t)
      hU huLower huUpper hD hDU ha habove hzeroheight hupperheight hUT hpadding hbelow
  have hξabs : |ξ| ≤ (Z ^ d) ^ τ / (8 * Real.pi + 8) := by
    simpa only [Real.norm_eq_abs] using hξ
  have hfreq1 : |2 * Real.pi * ξ| ≤
      2 * Real.pi * ((Z ^ d) ^ τ / (8 * Real.pi + 8)) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
    exact mul_le_mul_of_nonneg_left hξabs (by positivity)
  have htriangle := abs_sub (2 * Real.pi * ξ) ρ.im
  have hiT := mul_le_mul_of_nonneg_right
    (show (h : ℝ) ≤ N by exact_mod_cast hh) (by positivity : 0 ≤ Z ^ τ)
  have hfrequency : |2 * Real.pi * ξ - ρ.im| ≤ 3 * ((N : ℝ) + 1) * Z ^ τ := by
    unfold ExpansionInterfaces.selectedHeight at hγ
    unfold ExpansionInterfaces.selectedHeight ExpansionInterfaces.upperHeight at hpadding
    push_cast at hpadding
    nlinarith
  exact ⟨{
    presentation := i
    zero := ρ
    inverseIndex := j
    plainIndex := k
    fourier := ξ
    zero_order := hz
    zero_lower := hβ
    zero_upper := hβ'
    inverseIndex_le := hj
    plainIndex_le := hk
    fourier_bound := hξ
    frequency_bound := hfrequency
    source_support := hsupp
    saturation := hsat
  }⟩

end Expansion.Project

#print axioms Expansion.Project.exists_physical_row_detection
