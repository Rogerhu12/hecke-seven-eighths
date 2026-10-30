import HeckeGeneral.Analysis.ActualSIntegerSobolevScaleSup
import HeckeGeneral.Analysis.ActualScaleSupSeed

/-! A targetwise finite-test moment consumer. Each target may have its own
finite S and actual arithmetic generator data. The finite-test moment is an
explicit analytic source-calibration hypothesis; it is not deduced from the
older fixed-profile/fixed-scale MI. The arithmetic amplification, counting,
small-power coefficient mass and dyadic reciprocal identity are proved lemmas.
-/

noncomputable section
namespace HeckeGeneral.Analysis.ActualSIntegerMoments

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton HeckeGeneral.Analysis.SquarefreeAmplification
open scoped BigOperators Classical nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (τ : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

/-- This repeats the already proved amplifier inequality consumer with its
unused packet quantifier removed; frozen earlier sources are left intact. -/
theorem ActualTargetZeroSlotScaleSupInput.to_compactSingleRowEnergy
    (χ : HeckeCharacter K)
    (hMI : ActualTargetZeroSlotScaleSupInput K (S : Set (HeightOneSpectrum (𝓞 K)))
      τ.root6 τ.primitive6 τ.embedding χ) :
    CompactSingleRowEnergy K S τ χ := by
  intro c ε hc hε T hT
  have hc1 : 0 < 1 + c := by linarith
  let a : ℝ := ε / (2 * (1 + c))
  let e : ℝ := ε / (6 * (1 + c))
  let gap : ℝ := c / (1 + c)
  let r : ℝ := (1 + c) / 6
  let L : ℝ := 5 + 2 * a + 6 * e
  have ha : 0 < a := div_pos hε (by positivity)
  have he : 0 < e := div_pos hε (by positivity)
  have hgap : 0 < gap := div_pos hc hc1
  have hgap1 : gap < 1 := by
    dsimp [gap]
    exact (div_lt_one hc1).mpr (by linarith)
  have hr : 0 < r := div_pos hc1 (by norm_num)
  have hscaleexp : r * (6 * (1 - gap)) = 1 := by
    dsimp [r, gap]
    field_simp [ne_of_gt hc1]
    ring
  have hfinalexp : r * L ≤ 5 * (1 + c) / 6 + ε := by
    have heq : r * L = 5 * (1 + c) / 6 + ε / 3 := by
      dsimp [r, L, a, e]
      field_simp [ne_of_gt hc1]
      ring
    rw [heq]
    linarith
  obtain ⟨Cₘ, hCₘ, hamp⟩ := actualMellin_amplification_to_orbit_majorant K
    (S : Set (HeightOneSpectrum (𝓞 K))) τ ha
  obtain ⟨k, P₀, hk, hP₀, hcount⟩ :=
    exists_exteriorAmplifierIdeals_linear_lower K (S : Set (HeightOneSpectrum (𝓞 K)))
  obtain ⟨Cᵢ, H₀, hCᵢ, hH₀, hmajorant⟩ :=
    hMI gap e hgap hgap1 he T hT
  let A : ℝ := max 1 (max P₀ H₀)
  have hA : 1 ≤ A := le_max_left _ _
  have hAP : P₀ ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hAH : H₀ ≤ A := (le_max_right _ _).trans (le_max_right _ _)
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  let C : ℝ := (Cₘ * Cᵢ / k) * A ^ L
  have hC : 0 < C := mul_pos (div_pos (mul_pos hCₘ hCᵢ) hk)
    (Real.rpow_pos_of_pos hApos L)
  refine ⟨C, hC, ?_⟩
  intro D hD s hs
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  let P : ℝ := A * D ^ r
  have hDr : 1 ≤ D ^ r := Real.one_le_rpow hD hr.le
  have hPA : A ≤ P := by
    dsimp [P]
    nlinarith
  have hP : 1 ≤ P := hA.trans hPA
  have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hPH : P ≤ P ^ 6 := le_self_pow₀ hP (by decide)
  have hH : H₀ ≤ P ^ 6 := hAH.trans (hPA.trans hPH)
  have hscale : D ≤ (P ^ 6) ^ (1 - gap) := by
    have hbase : D ^ r ≤ P := by
      dsimp [P]
      nlinarith [Real.rpow_nonneg hDpos.le r]
    have h := Real.rpow_le_rpow (pow_nonneg (Real.rpow_nonneg hDpos.le r) 6)
      (pow_le_pow_left₀ (Real.rpow_nonneg hDpos.le r) hbase 6) (sub_nonneg.mpr hgap1.le)
    have heq : ((D ^ r) ^ 6) ^ (1 - gap) = D := by
      rw [← Real.rpow_natCast_mul (Real.rpow_nonneg hDpos.le r) 6 (1 - gap),
        ← Real.rpow_mul hDpos.le]
      norm_num only [Nat.cast_ofNat]
      rw [hscaleexp, Real.rpow_one]
    rwa [heq] at h
  obtain ⟨B, hB, hrow, hsum⟩ := hmajorant (P ^ 6) hH
  let F := exteriorAmplifierIdeals K (S : Set (HeightOneSpectrum (𝓞 K))) P
  have hF : ∀ A ∈ F, idealNorm K A.val ≤ P :=
    norm_le_of_mem_exteriorAmplifierIdeals K _ hPpos.le
  have hcard : k * P ≤ (F.card : ℝ) := hcount P (hAP.trans hPA)
  have hmain := hamp χ F P (P ^ 6) D s B hP le_rfl hDpos hF hB
    (fun q hq d hd hdD => hrow q hq d hd (hdD.trans hscale) s hs)
  have hcombined : k * P *
      ‖dyadicSexticMellinInversePolynomial K (S : Set (HeightOneSpectrum (𝓞 K)))
        τ.root6 τ.primitive6 τ.embedding χ 1 D s‖ ^ 2 ≤
      Cₘ * P ^ (2 * a) * (Cᵢ * (P ^ 6) ^ (1 + e)) := by
    exact (mul_le_mul_of_nonneg_right hcard (sq_nonneg _)).trans
      (hmain.trans (mul_le_mul_of_nonneg_left hsum
        (mul_nonneg hCₘ.le (Real.rpow_nonneg hPpos.le _))))
  have hnormalize : Cₘ * P ^ (2 * a) * (Cᵢ * (P ^ 6) ^ (1 + e)) =
      ((Cₘ * Cᵢ / k) * P ^ L) * (k * P) := by
    rw [← Real.rpow_natCast_mul hPpos.le 6 (1 + e)]
    norm_num only [Nat.cast_ofNat]
    calc
      _ = (Cₘ * Cᵢ) * (P ^ (2 * a) * P ^ (6 * (1 + e))) := by ring
      _ = (Cₘ * Cᵢ) * P ^ (L + 1) := by
        rw [← Real.rpow_add hPpos]
        congr 2
        dsimp [L]
        ring
      _ = _ := by
        rw [Real.rpow_add hPpos, Real.rpow_one]
        field_simp [ne_of_gt hk]
  have hnormalized :
      ‖dyadicSexticMellinInversePolynomial K (S : Set (HeightOneSpectrum (𝓞 K)))
        τ.root6 τ.primitive6 τ.embedding χ 1 D s‖ ^ 2 ≤ (Cₘ * Cᵢ / k) * P ^ L := by
    apply (mul_le_mul_iff_right₀ (mul_pos hk hPpos)).mp
    exact hcombined.trans_eq (hnormalize.trans (mul_comm _ _))
  calc
    _ ≤ (Cₘ * Cᵢ / k) * P ^ L := hnormalized
    _ = C * D ^ (r * L) := by
      dsimp [P, C]
      rw [Real.mul_rpow hApos.le (Real.rpow_nonneg hDpos.le r),
        ← Real.rpow_mul hDpos.le]
      ring
    _ ≤ C * D ^ (5 * (1 + c) / 6 + ε) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hD hfinalexp) hC.le

theorem ActualTargetZeroSlotSobolevMomentInput.to_compactSingleRowEnergy
    (χ : HeckeCharacter K)
    (hMI : ActualTargetZeroSlotSobolevMomentInput K (S : Set (HeightOneSpectrum (𝓞 K)))
      τ.root6 τ.primitive6 τ.embedding χ) :
    CompactSingleRowEnergy K S τ χ :=
  ActualTargetZeroSlotScaleSupInput.to_compactSingleRowEnergy K S τ χ
    (ActualTargetZeroSlotSobolevMomentInput.to_scaleSup K
      (S : Set (HeightOneSpectrum (𝓞 K))) τ.root6 τ.primitive6 τ.embedding χ hMI)

theorem heckeContinuation_seed_of_actual_target_sobolev
    (χ : HeckeCharacter K)
    (hMI : ActualTargetZeroSlotSobolevMomentInput K (S : Set (HeightOneSpectrum (𝓞 K)))
      τ.root6 τ.primitive6 τ.embedding χ) :
    MeromorphicZeroFreeOn (heckeContinuation K χ) (rightHalfPlane (11 / 12)) :=
  IdealDyadicMobius.heckeContinuation_seed_of_compact_growth K χ S
    (CompactSingleRowEnergy.to_compactShellGrowth K S τ χ
      (ActualTargetZeroSlotSobolevMomentInput.to_compactSingleRowEnergy K S τ χ hMI))

/-- S and all arithmetic data may depend on the full target character.
No uniform constants over the packet and no common S are requested. -/
theorem packetSeedReciprocal_of_actual_target_sobolev (ω : HeckeCharacter K)
    (hMI : ∀ χ : HeckePacketIndex K ω,
      ∃ (Sχ : Finset (HeightOneSpectrum (𝓞 K)))
        (τχ : ThetaArithmeticData K (Sχ : Set (HeightOneSpectrum (𝓞 K)))),
        ActualTargetZeroSlotSobolevMomentInput K (Sχ : Set (HeightOneSpectrum (𝓞 K)))
          τχ.root6 τχ.primitive6 τχ.embedding χ.val) :
    PacketSeedReciprocal K ω := by
  apply IdealDyadicMobius.packetSeedReciprocal_of_compact_growth K ω
  intro χ
  obtain ⟨Sχ, τχ, hχ⟩ := hMI χ
  exact ⟨Sχ, CompactSingleRowEnergy.to_compactShellGrowth K Sχ τχ χ.val
    (ActualTargetZeroSlotSobolevMomentInput.to_compactSingleRowEnergy K Sχ τχ χ.val hχ)⟩

theorem packetSeedBound_of_actual_target_sobolev (ω : HeckeCharacter K)
    (hMI : ∀ χ : HeckePacketIndex K ω,
      ∃ (Sχ : Finset (HeightOneSpectrum (𝓞 K)))
        (τχ : ThetaArithmeticData K (Sχ : Set (HeightOneSpectrum (𝓞 K)))),
        ActualTargetZeroSlotSobolevMomentInput K (Sχ : Set (HeightOneSpectrum (𝓞 K)))
          τχ.root6 τχ.primitive6 τχ.embedding χ.val) :
    SeedBound (heckePacketZeros K ω) :=
  PacketSeedReciprocal.seedBound K (packetSeedReciprocal_of_actual_target_sobolev K ω hMI)

end HeckeGeneral.Analysis.ActualSIntegerMoments
