import HeckeSkeleton.HighBinSupport.ActualDetectorBoundary
import HeckeSkeleton.HighBinSupport.ActualDyadicRows
import HeckeSkeleton.HighBinSupport.DyadicShells
import HeckeGeneral.Analysis.PowerHeightComparison

/-!
The complete dyadic boundary of the canonical detector construction.
Every summand uses its literal finite source mask on both contours.
The actual finite shell schedule supplies its own count; no presentation
height bound, block-count estimate, or individual boundary estimate is
assumed.  A fixed scale exponent 14 and height degree zero precede every
external decay order.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinDyadicBoundary

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.HighBinDetectorGeometry
open HeckeSkeleton.HighBinActualBoundaryGeometry HeckeSkeleton.HighBinCanonicalBoundary
open HighBinVerified.Dyadic
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S₀" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ p : (S : Set (HeightOneSpectrum (𝓞 K))), MeasurableSpace (p.val.adicCompletion K)]
variable [∀ p : (S : Set (HeightOneSpectrum (𝓞 K))), BorelSpace (p.val.adicCompletion K)]
variable (μ : (p : (S : Set (HeightOneSpectrum (𝓞 K)))) → Measure (p.val.adicCompletion K))
variable [∀ p : (S : Set (HeightOneSpectrum (𝓞 K))), (μ p).IsAddHaarMeasure]
variable (P : ProbeData K (S : Set (HeightOneSpectrum (𝓞 K)))) (ψ : HeckeCharacter K)
variable (Θ : Finset (HeckeCharacter K)) (g : PrimeWindowGeometry)
variable (B e : ℝ) (he : 0 < e) (hB : 51 / 100 ≤ B)
variable (hcommon : ∀ u : FrequencyRow K (S : Set (HeightOneSpectrum (𝓞 K))), ∀ height : ℝ,
  rowZeroBelow K (S : Set (HeightOneSpectrum (𝓞 K))) ψ Θ P
    (arithmeticHighEulerData K (S : Set (HeightOneSpectrum (𝓞 K))) P ψ) u height B)

/-- Sum over the literal finite shell prefix and the nonempty detector
fibers in each masked shell. -/
def dyadicBoundary (ray : Finset (HeckeCharacter K))
    (source : Finset (FrequencyRow K S₀)) (Z T κ upper : ℝ) : ℂ :=
  ∑ j : Fin (shellCount Z (1 / 16) upper),
    maskedShellBoundary K S μ P ψ Θ g B e he hB hcommon ray source Z T κ
      (shellExponent Z (1 / 16) j.val)

/-- The whole constructed boundary is exactly the sum over the original
moderate source. Each row retains its own detector-dependent `w` line. -/
theorem dyadicBoundary_eq_sourceRowSum (ray : Finset (HeckeCharacter K))
    (Z T κ upper : ℝ) (hZ : 1 < Z) :
    dyadicBoundary K S μ P ψ Θ g B e he hB hcommon ray
      (HighBinDyadicRows.moderateSource K S₀ Z upper) Z T κ upper =
        ∑ u ∈ HighBinDyadicRows.moderateSource K S₀ Z upper,
          rowBoundaryAtChoice K S μ P ψ Θ g B e he hB hcommon ray Z T κ u := by
  unfold dyadicBoundary
  simp_rw [maskedShellBoundary_eq_rowSum]
  exact HighBinDyadicRows.sum_maskedShellRows K S₀ Z upper hZ
    (rowBoundaryAtChoice K S μ P ψ Θ g B e he hB hcommon ray Z T κ)

/-- One fixed explicit constant bounds all shell counts whose upper
exponent is at most one. -/
theorem shellCount_linear_bound {Z upper : ℝ} (hZ : 1 ≤ Z)
    (hlo : 1 / 16 ≤ upper) (hhi : upper ≤ 1) :
    (shellCount Z (1 / 16) upper : ℝ) ≤ (2 + 1 / Real.log 2) * Z := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc := shellCount_subpower (lower := (1 / 16 : ℝ)) hZ hlo
    (by norm_num : (0 : ℝ) < 1)
  simp only [div_one, Real.rpow_one] at hc
  apply hc.trans
  apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans hZ)
  apply add_le_add_left
  exact div_le_div_of_nonneg_right (by linarith) hlog.le

/-- Arbitrary external tail order for the whole canonical dyadic
boundary.  The constants are uniform in the source mask, ray filter,
internal-height exponent, and legal upper shell exponent. -/
theorem exists_dyadicBoundary_external_tail
    (hΘ : 1 ∈ Θ) (he1 : e ≤ 1 / 10000) (hB1 : B ≤ 1) :
    ∃ Z₀ : ℝ, 2 ≤ Z₀ ∧ ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (ray : Finset (HeckeCharacter K)) (source : Finset (FrequencyRow K S₀))
        (Z T κ upper : ℝ),
      Z₀ ≤ Z → 1 ≤ T → 1 / 16 ≤ upper → upper ≤ 1 →
      ‖dyadicBoundary K S μ P ψ Θ g B e he hB hcommon ray source Z T κ upper‖ ≤
        C * Z ^ 14 * T ^ (-(N : ℝ)) := by
  obtain ⟨Z₁, hZ₁, htail⟩ := exists_maskedShellBoundary_external_tail
    K S μ P ψ Θ hΘ g B e he he1 hB hB1 hcommon
  refine ⟨max Z₁ 2, le_max_right _ _, ?_⟩
  intro N
  obtain ⟨C, hC, hb⟩ := htail N
  let A : ℝ := 2 + 1 / Real.log 2
  have hA : 0 < A := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [A]
    positivity
  refine ⟨A * C, mul_pos hA hC, ?_⟩
  intro ray source Z T κ upper hZ hT hlo hhi
  have hZbase : Z₁ ≤ Z := (le_max_left _ _).trans hZ
  have hZ2 : 2 ≤ Z := (le_max_right _ _).trans hZ
  have hZlt : 1 < Z := by linarith
  have hZ0 : 0 ≤ Z := by linarith
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hpiece : ∀ j : Fin (shellCount Z (1 / 16) upper),
      ‖maskedShellBoundary K S μ P ψ Θ g B e he hB hcommon ray source Z T κ
        (shellExponent Z (1 / 16) j.val)‖ ≤ C * Z ^ 13 * T ^ (-(N : ℝ)) := by
    intro j
    have hj := actualShell_range hZlt j
    exact hb ray source Z T κ (shellExponent Z (1 / 16) j.val)
      hZbase hT hj.1 (hj.2.le.trans hhi)
  have hcount : (shellCount Z (1 / 16) upper : ℝ) ≤ A * Z :=
    shellCount_linear_bound hZlt.le hlo hhi
  unfold dyadicBoundary
  calc
    _ ≤ ∑ j : Fin (shellCount Z (1 / 16) upper),
        ‖maskedShellBoundary K S μ P ψ Θ g B e he hB hcommon ray source Z T κ
          (shellExponent Z (1 / 16) j.val)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin (shellCount Z (1 / 16) upper),
        C * Z ^ 13 * T ^ (-(N : ℝ)) := Finset.sum_le_sum fun j _ => hpiece j
    _ = (shellCount Z (1 / 16) upper : ℝ) * (C * Z ^ 13 * T ^ (-(N : ℝ))) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ (A * Z) * (C * Z ^ 13 * T ^ (-(N : ℝ))) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = (A * C) * Z ^ 14 * T ^ (-(N : ℝ)) := by ring

/-- The original power-height-tail proposition holds for the literal
constructed dyadic boundary with scale exponent 14 and height degree 0.
The source can even vary with both scale and external height. -/
theorem dyadicBoundary_powerHeightTailBound
    (hΘ : 1 ∈ Θ) (he1 : e ≤ 1 / 10000) (hB1 : B ≤ 1)
    (ray : Finset (HeckeCharacter K))
    (source : ℝ → ℝ → Finset (FrequencyRow K S₀)) (κ upper : ℝ)
    (hlo : 1 / 16 ≤ upper) (hhi : upper ≤ 1) :
    PowerHeightTailBound (fun Z T =>
      dyadicBoundary K S μ P ψ Θ g B e he hB hcommon ray (source Z T) Z T κ upper) := by
  obtain ⟨Z₀, hZ₀, htail⟩ := exists_dyadicBoundary_external_tail
    K S μ P ψ Θ g B e he hB hcommon hΘ he1 hB1
  refine ⟨0, 14, 1, le_rfl, by norm_num, ?_⟩
  intro τ hτ _ N
  obtain ⟨C, hC, hb⟩ := htail N
  refine ⟨C, Z₀, hC, by linarith, ?_⟩
  intro Z hZ
  have hZ1 : 1 ≤ Z := by linarith
  have hT : 1 ≤ Z ^ τ := Real.one_le_rpow hZ1 hτ.le
  have h := hb ray (source Z (Z ^ τ)) Z (Z ^ τ) κ upper hZ hT hlo hhi
  simpa only [Real.rpow_zero, mul_one, Real.rpow_natCast] using h

end HeckeSkeleton.HighBinDyadicBoundary

#print axioms HeckeSkeleton.HighBinDyadicBoundary.exists_dyadicBoundary_external_tail
#print axioms HeckeSkeleton.HighBinDyadicBoundary.dyadicBoundary_eq_sourceRowSum
#print axioms HeckeSkeleton.HighBinDyadicBoundary.dyadicBoundary_powerHeightTailBound
