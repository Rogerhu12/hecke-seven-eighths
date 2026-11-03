import Expansion.PhysicalInitialMellinTerm
import HeckeSkeleton.ExpansionModels.LargeRowTail
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Absolute convergence of the complete initial physical Mellin expansion

The actual ideal majorant on (5,5,3) is multiplied by N(u)^(-3), retaining
all sixth-unit sectors.  Its summability follows from the proved ideal
and frequency counts.  The scalar height factor is integrable by the
actual Gaussian, annular and additive Mellin estimates and the volume
preserving shear.  These supply every sum/integral exchange below.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.PhysicalInitialMellin

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualAbsolute HeckeSkeleton.Expansion.LargeRows
open Expansion.PhysicalInitialHeight HighBinVerified.NormFormMellin
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "FIdx" => FourIdealIndex K Sset

abbrev PhysicalInitialIndex := FrequencyRow K Sset × FIdx

instance countable_physicalFrequencyRow : Countable (FrequencyRow K Sset) := by
  have hi : Function.Injective (fun u : FrequencyRow K Sset => (u.ideal, u.sector)) := by
    intro u v huv
    cases u with
    | mk ui up us =>
      cases v with
      | mk vi vp vs =>
        have h : ui = vi ∧ us = vs := Prod.mk.inj huv
        rcases h with ⟨rfl, rfl⟩
        rfl
  exact hi.countable

def physicalInitialMajorant (i : PhysicalInitialIndex K S) : ℝ :=
  frequencyRowNorm K Sset i.1 ^ (-3 : ℝ) * initialMajorant K Sset 5 5 3 i.2

theorem physicalInitialMajorant_nonneg (i : PhysicalInitialIndex K S) :
    0 ≤ physicalInitialMajorant K S i :=
  mul_nonneg (Real.rpow_nonneg (idealNorm_pos K _).le _)
    (initialMajorant_nonneg K Sset 5 5 3 i.2)

theorem summable_physicalInitialMajorant : Summable (physicalInitialMajorant K S) :=
  (summable_frequencyRowNorm_rpow K Sset (p := -3) (by norm_num)).mul_of_nonneg
    (summable_initialMajorant K Sset 5 5 3 (by norm_num) (by norm_num) (by norm_num))
    (fun _ => Real.rpow_nonneg (idealNorm_pos K _).le _)
    (initialMajorant_nonneg K Sset 5 5 3)

variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
  [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]

def physicalInitialScalarAt (P : ProbeData K Sset) (X Y Z : ℝ) (t : Fin 3 → ℝ) : ℂ :=
  physicalInitialScalar K S μv P X Y Z
    (idealVerticalPoint 5 (t 0)) (idealVerticalPoint 5 (t 1)) (idealVerticalPoint 3 (t 2))

theorem norm_physicalInitialMellinTerm_le (P : ProbeData K Sset) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K Sset)) (X Y Z : ℝ)
    (i : PhysicalInitialIndex K S) (t : Fin 3 → ℝ) :
    ‖physicalInitialMellinTerm K S μv P ψ Q X Y Z i.1 i.2 t‖ ≤
      ‖physicalInitialScalarAt K S μv P X Y Z t‖ * physicalInitialMajorant K S i := by
  have hI := norm_initialRowEulerTerm_le K Sset P ψ Q i.1
    (idealVerticalPoint 5 (t 0)) (idealVerticalPoint 5 (t 1)) (idealVerticalPoint 3 (t 2)) i.2
  simp only [idealVerticalPoint_re] at hI
  have hu : ‖(frequencyRowNorm K Sset i.1 : ℂ) ^ (-idealVerticalPoint 3 (t 2))‖ =
      frequencyRowNorm K Sset i.1 ^ (-3 : ℝ) := by
    have hnorm : 0 < frequencyRowNorm K Sset i.1 := idealNorm_pos K _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hnorm,
      Complex.neg_re, idealVerticalPoint_re]
  unfold physicalInitialMellinTerm
  rw [norm_mul, norm_mul, hu]
  exact (mul_le_mul_of_nonneg_left hI
    (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (idealNorm_pos K _).le _))).trans_eq
      (mul_assoc _ _ _)

theorem summable_norm_physicalInitialMellinTerm (P : ProbeData K Sset)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K Sset))
    (X Y Z : ℝ) (t : Fin 3 → ℝ) :
    Summable (fun i : PhysicalInitialIndex K S =>
      ‖physicalInitialMellinTerm K S μv P ψ Q X Y Z i.1 i.2 t‖) :=
  ((summable_physicalInitialMajorant K S).mul_left
    ‖physicalInitialScalarAt K S μv P X Y Z t‖).of_nonneg_of_le
      (fun _ => norm_nonneg _)
      (fun i => norm_physicalInitialMellinTerm_le K S μv P ψ Q X Y Z i t)

theorem physicalInitialRowKernel_eq_tsum (P : ProbeData K Sset) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K Sset)) (X Y Z : ℝ)
    (u : FrequencyRow K Sset) (t : Fin 3 → ℝ) :
    physicalInitialRowKernel K S μv P ψ Q X Y Z u
        (idealVerticalPoint 5 (t 0)) (idealVerticalPoint 5 (t 1)) (idealVerticalPoint 3 (t 2)) =
      ∑' I : FIdx, physicalInitialMellinTerm K S μv P ψ Q X Y Z u I t := by
  simp only [physicalInitialRowKernel, initialRowEulerSeries, physicalInitialMellinTerm,
    tsum_mul_left]

variable [IsTotallyComplex K]
  [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]

include ν in
theorem integrable_physicalInitialScalarAt (P : ProbeData K Sset)
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    Integrable (physicalInitialScalarAt K S μv P X Y Z) := by
  let F : (Fin 3 → ℝ) → ℂ := fun t =>
    Complex.exp ((idealVerticalPoint 5 (t 0) + idealVerticalPoint 3 (t 2) - 1) ^ 2) *
      mellin P.denominator.toFun (idealVerticalPoint 5 (t 1)) *
      additiveMellin K Sset (fun v => μv v.val) P.additive (idealVerticalPoint 3 (t 2))
  have hF : Integrable F := by
    have hi := integrable_three_product
      (verticalIntegrable_gaussianMellin 7)
      (verticalIntegrable_mellin P.denominator.toSmoothAnnularTest 5)
      (verticalIntegrable_physical_additiveMellin K S μv ν P.additive 3 (by norm_num))
    have hs := (integrable_heightShear_iff _).mpr hi
    change Integrable (fun t : Fin 3 → ℝ =>
      Complex.exp ((idealVerticalPoint 7 ((heightShear t) 0)) ^ 2) *
        mellin P.denominator.toFun (idealVerticalPoint 5 ((heightShear t) 1)) *
        additiveMellin K Sset (fun v => μv v.val) P.additive
          (idealVerticalPoint 3 ((heightShear t) 2))) at hs
    have hshear1 (t : Fin 3 → ℝ) : (heightShear t) 1 = t 1 := rfl
    have hshear2 (t : Fin 3 → ℝ) : (heightShear t) 2 = t 2 := rfl
    simpa only [F, initial_shear_line, hshear1, hshear2] using hs
  let H : (Fin 3 → ℝ) → ℂ := fun t =>
    (physicalPoissonScalar K : ℂ) * (X : ℂ) ^ (1 / 2 - idealVerticalPoint 3 (t 2)) *
      (Z : ℂ) ^ (idealVerticalPoint 5 (t 0) + idealVerticalPoint 3 (t 2) - 1) *
      (Y : ℂ) ^ (idealVerticalPoint 5 (t 1) - 1)
  have hH : Continuous H := by
    have hc (σ : ℝ) (j : Fin 3) :
        Continuous (fun t : Fin 3 → ℝ => idealVerticalPoint σ (t j)) :=
      (continuous_idealVerticalPoint σ).comp (continuous_apply j)
    exact ((continuous_const.mul
      ((continuous_const.sub (hc 3 2)).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne')))).mul
      (((hc 5 0).add (hc 3 2) |>.sub continuous_const).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hZ.ne')))).mul
      (((hc 5 1).sub continuous_const).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hY.ne')))
  have hb (t : Fin 3 → ℝ) :
      ‖H t‖ ≤ ‖(physicalPoissonScalar K : ℂ)‖ * X ^ (-(5 / 2 : ℝ)) * Z ^ (7 : ℝ) * Y ^ (4 : ℝ) := by
    dsimp only [H]
    rw [norm_mul, norm_mul, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hX,
      Complex.norm_cpow_eq_rpow_re_of_pos hZ,
      Complex.norm_cpow_eq_rpow_re_of_pos hY]
    norm_num [Complex.sub_re, Complex.add_re, idealVerticalPoint_re]
  exact (hF.mul_bdd hH.aestronglyMeasurable (Filter.Eventually.of_forall hb)).congr
    (Filter.Eventually.of_forall (fun t => by
      dsimp only [physicalInitialScalarAt, physicalInitialScalar, F, H]
      ring))

include ν in
theorem integral_norm_physicalInitialMellinTerm_le (P : ProbeData K Sset)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K Sset))
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (i : PhysicalInitialIndex K S) :
    (∫ t : Fin 3 → ℝ, ‖physicalInitialMellinTerm K S μv P ψ Q X Y Z i.1 i.2 t‖) ≤
      (∫ t : Fin 3 → ℝ, ‖physicalInitialScalarAt K S μv P X Y Z t‖) *
        physicalInitialMajorant K S i := by
  rw [← integral_mul_const]
  apply integral_mono
    (integrable_physicalInitialMellinTerm K S μv ν P ψ Q X Y Z hX hY hZ i.1 i.2).norm
    ((integrable_physicalInitialScalarAt K S μv ν P X Y Z hX hY hZ).norm.mul_const _)
  exact norm_physicalInitialMellinTerm_le K S μv P ψ Q X Y Z i

include ν in
theorem summable_integral_norm_physicalInitialMellinTerm (P : ProbeData K Sset)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K Sset))
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    Summable (fun i : PhysicalInitialIndex K S =>
      ∫ t : Fin 3 → ℝ, ‖physicalInitialMellinTerm K S μv P ψ Q X Y Z i.1 i.2 t‖) :=
  ((summable_physicalInitialMajorant K S).mul_left
    (∫ t : Fin 3 → ℝ, ‖physicalInitialScalarAt K S μv P X Y Z t‖)).of_nonneg_of_le
      (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (integral_norm_physicalInitialMellinTerm_le K S μv ν P ψ Q X Y Z hX hY hZ)

include ν in
theorem physicalInitial_sum_integral_interchange (P : ProbeData K Sset)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K Sset))
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    Integrable (fun t : Fin 3 → ℝ => ∑' i : PhysicalInitialIndex K S,
      physicalInitialMellinTerm K S μv P ψ Q X Y Z i.1 i.2 t) ∧
    (∑' i : PhysicalInitialIndex K S, ∫ t : Fin 3 → ℝ,
      physicalInitialMellinTerm K S μv P ψ Q X Y Z i.1 i.2 t) =
      ∫ t : Fin 3 → ℝ, ∑' i : PhysicalInitialIndex K S,
        physicalInitialMellinTerm K S μv P ψ Q X Y Z i.1 i.2 t := by
  have hi (i : PhysicalInitialIndex K S) :=
    integrable_physicalInitialMellinTerm K S μv ν P ψ Q X Y Z hX hY hZ i.1 i.2
  have hs := summable_integral_norm_physicalInitialMellinTerm K S μv ν P ψ Q X Y Z hX hY hZ
  refine ⟨?_, integral_tsum_of_summable_integral_norm hi hs⟩
  apply ((integrable_physicalInitialScalarAt K S μv ν P X Y Z hX hY hZ).norm.mul_const
    (∑' i : PhysicalInitialIndex K S, physicalInitialMajorant K S i)).mono'
    (AEStronglyMeasurable.tsum (fun i => (hi i).aestronglyMeasurable))
  apply Filter.Eventually.of_forall
  intro t
  have hn := summable_norm_physicalInitialMellinTerm K S μv P ψ Q X Y Z t
  apply (norm_tsum_le_tsum_norm hn).trans
  rw [← tsum_mul_left]
  exact hn.tsum_le_tsum
    (fun i => norm_physicalInitialMellinTerm_le K S μv P ψ Q X Y Z i t)
    ((summable_physicalInitialMajorant K S).mul_left ‖physicalInitialScalarAt K S μv P X Y Z t‖)

include ν in
theorem summable_norm_physicalPoissonTerm (P : ProbeData K Sset)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K Sset))
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    Summable (fun i : PhysicalInitialIndex K S =>
      ‖physicalPoissonTerm K S μv P ψ Q X Y Z hX i.1 i.2‖) := by
  have hs := summable_integral_norm_physicalInitialMellinTerm K S μv ν P ψ Q X Y Z hX hY hZ
  apply (hs.mul_left ‖tripleMellinConstant‖).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro i
  rw [physicalPoissonTerm_eq_initial_integral K S μv ν P ψ Q X Y Z hX hY hZ, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)

end Expansion.PhysicalInitialMellin

#print axioms Expansion.PhysicalInitialMellin.physicalInitial_sum_integral_interchange
#print axioms Expansion.PhysicalInitialMellin.summable_norm_physicalPoissonTerm
