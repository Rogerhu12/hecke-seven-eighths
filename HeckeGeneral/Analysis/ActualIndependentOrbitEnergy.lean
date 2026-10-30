import HeckeGeneral.Analysis.ActualIndependentAmplification
import HeckeGeneral.Analysis.IndependentAmplifierOptimization

/-! Independent two-scale energy for literal sixth-power-free S-integer
orbits, conditional on the named targetwise scale-supremum moment input.
This does not identify opaque MomentData/calibrated allowed sections with
these actual quotient rows. Each target may select its own finite S. -/

noncomputable section
namespace HeckeGeneral.Analysis.ActualSIntegerMoments

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton HeckeGeneral.Analysis.SquarefreeAmplification
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (τ : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

/-- Losses precede the target; the constant may depend on the target and
compact spectral set but is independent of R, U, D and s in that set. -/
theorem actualTargetScaleSup_independentOrbitEnergy
    {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (T : Set ℂ) (hT : IsCompact T)
    (χ : HeckeCharacter K)
    (hMI : ActualTargetZeroSlotScaleSupInput K (S : Set (HeightOneSpectrum (𝓞 K)))
      τ.root6 τ.primitive6 τ.embedding χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ U D : ℝ, 1 ≤ U → 1 ≤ D →
      ∀ R : Finset (ActualSixthPowerFreeOrbit K (S : Set (HeightOneSpectrum (𝓞 K)))),
        (∀ q ∈ R, actualSIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) q.val ≤ U) →
        ∀ s ∈ T,
          (∑ q ∈ R,
            ‖actualSIntegerInversePolynomial K (S : Set (HeightOneSpectrum (𝓞 K)))
              τ.root6 τ.primitive6 τ.embedding χ q.val D s‖ ^ 2) ≤
            C * max U (U ^ (1 / 6 : ℝ) * D ^ (5 * (1 + c) / 6)) * (U * D) ^ ε := by
  have hc1 : 0 < 1 + c := by linarith
  let a : ℝ := ε / (2 * (1 + c))
  let e : ℝ := ε / (6 * (1 + c))
  let gap : ℝ := c / (1 + c)
  let L : ℝ := 5 + 2 * a + 6 * e
  have ha : 0 < a := div_pos hε (by positivity)
  have he : 0 < e := div_pos hε (by positivity)
  have hgap : 0 < gap := div_pos hc hc1
  have hgap1 : gap < 1 := by
    dsimp [gap]
    exact (div_lt_one hc1).mpr (by linarith)
  have hcg : (1 + c) * (1 - gap) = 1 := by
    dsimp [gap]
    field_simp [ne_of_gt hc1]
    ring
  have heε : e ≤ ε := by
    exact div_le_self hε.le (by linarith : 1 ≤ 6 * (1 + c))
  have hUL : 1 + e - L / 6 ≤ 1 / 6 := by dsimp [L]; linarith
  have hDL : (1 + c) * (L / 6) ≤ 5 * (1 + c) / 6 + ε := by
    have heq : (1 + c) * (L / 6) = 5 * (1 + c) / 6 + ε / 3 := by
      dsimp [L, a, e]
      field_simp [ne_of_gt hc1]
      ring
    rw [heq]
    linarith
  obtain ⟨Cₘ, hCₘ, hamp⟩ := actualIndependent_amplification_to_orbit_majorant K
    (S : Set (HeightOneSpectrum (𝓞 K))) τ ha
  obtain ⟨k, P₀, hk, _hP₀, hcount⟩ :=
    exists_exteriorAmplifierIdeals_linear_lower K (S : Set (HeightOneSpectrum (𝓞 K)))
  obtain ⟨Cᵢ, H₀, hCᵢ, _hH₀, hmajorant⟩ := hMI gap e hgap hgap1 he T hT
  let A : ℝ := max 1 (max P₀ H₀)
  have hA : 1 ≤ A := le_max_left _ _
  have hAP : P₀ ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hAH : H₀ ≤ A := (le_max_right _ _).trans (le_max_right _ _)
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  let C : ℝ := (Cₘ * Cᵢ / k) * A ^ L
  have hC : 0 < C := mul_pos (div_pos (mul_pos hCₘ hCᵢ) hk)
    (Real.rpow_pos_of_pos hApos L)
  refine ⟨C, hC, ?_⟩
  intro U D hU hD R hR s hs
  have hUpos : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  let P := independentAmplifierSize A U D c
  have hPA : A ≤ P := independentAmplifierSize_ge hApos.le
  have hP : 1 ≤ P := hA.trans hPA
  have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hH : H₀ ≤ U * P ^ 6 := by
    have hP6 : P ≤ P ^ 6 := le_self_pow₀ hP (by decide)
    have hPU : P ^ 6 ≤ U * P ^ 6 := by nlinarith [pow_nonneg hPpos.le 6]
    exact hAH.trans (hPA.trans (hP6.trans hPU))
  have hscale : D ≤ (U * P ^ 6) ^ (1 - gap) :=
    independentAmplifierSize_scale hA hU hDpos hgap1 hcg
  obtain ⟨B, hB, hrow, hsum⟩ := hmajorant (U * P ^ 6) hH
  let F := exteriorAmplifierIdeals K (S : Set (HeightOneSpectrum (𝓞 K))) P
  have hF : ∀ A ∈ F, idealNorm K A.val ≤ P :=
    norm_le_of_mem_exteriorAmplifierIdeals K _ hPpos.le
  have hcard : k * P ≤ (F.card : ℝ) := hcount P (hAP.trans hPA)
  have hmain := hamp χ R F U P (U * P ^ 6) D s B hP le_rfl hDpos hR hF hB
    (fun q hq r hr hrD => hrow q hq r hr (hrD.trans hscale) s hs)
  have hsum0 : 0 ≤ ∑ q ∈ R,
      ‖actualSIntegerInversePolynomial K (S : Set (HeightOneSpectrum (𝓞 K)))
        τ.root6 τ.primitive6 τ.embedding χ q.val D s‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcombined : k * P * (∑ q ∈ R,
      ‖actualSIntegerInversePolynomial K (S : Set (HeightOneSpectrum (𝓞 K)))
        τ.root6 τ.primitive6 τ.embedding χ q.val D s‖ ^ 2) ≤
      Cₘ * P ^ (2 * a) * (Cᵢ * (U * P ^ 6) ^ (1 + e)) :=
    (mul_le_mul_of_nonneg_right hcard hsum0).trans
      (hmain.trans (mul_le_mul_of_nonneg_left hsum
        (mul_nonneg hCₘ.le (Real.rpow_nonneg hPpos.le _))))
  have hnormalize : Cₘ * P ^ (2 * a) * (Cᵢ * (U * P ^ 6) ^ (1 + e)) =
      (k * P) * ((Cₘ * Cᵢ / k) * (U ^ (1 + e) * P ^ L)) := by
    rw [Real.mul_rpow hUpos.le (pow_nonneg hPpos.le 6),
      ← Real.rpow_natCast_mul hPpos.le 6 (1 + e)]
    norm_num only [Nat.cast_ofNat]
    calc
      _ = (Cₘ * Cᵢ) * U ^ (1 + e) * (P ^ (2 * a) * P ^ (6 * (1 + e))) := by ring
      _ = (Cₘ * Cᵢ) * U ^ (1 + e) * P ^ (L + 1) := by
        rw [← Real.rpow_add hPpos]
        congr 2
        dsimp [L]
        ring
      _ = _ := by
        rw [Real.rpow_add hPpos, Real.rpow_one]
        field_simp [ne_of_gt hk]
  have hnormalized := (mul_le_mul_iff_right₀ (mul_pos hk hPpos)).mp
    (hcombined.trans_eq hnormalize)
  calc
    _ ≤ (Cₘ * Cᵢ / k) * (U ^ (1 + e) * P ^ L) := hnormalized
    _ ≤ (Cₘ * Cᵢ / k) *
        (A ^ L * max U (U ^ (1 / 6 : ℝ) * D ^ (5 * (1 + c) / 6)) * (U * D) ^ ε) :=
      mul_le_mul_of_nonneg_left
        (independentAmplifierSize_energy hApos hU hD heε hε.le hUL hDL)
        (div_pos (mul_pos hCₘ hCᵢ) hk).le
    _ = _ := by dsimp [C]; ring

end HeckeGeneral.Analysis.ActualSIntegerMoments
