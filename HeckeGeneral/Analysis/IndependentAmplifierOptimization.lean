import HeckeGeneral.Analysis.ActualSIntegerSobolevSeed

/-! Real parameter optimization for independent row and polynomial scales.
The amplifier size is A max(1,(D^(1+c)/U)^(1/6)). No moment estimate
or arithmetic counting assertion is included in these numerical lemmas. -/

noncomputable section
namespace HeckeGeneral.Analysis.ActualSIntegerMoments

def independentAmplifierSize (A U D c : ℝ) : ℝ :=
  A * max 1 ((D ^ (1 + c) / U) ^ (1 / 6 : ℝ))

theorem independentAmplifierSize_ge {A U D c : ℝ} (hA : 0 ≤ A) :
    A ≤ independentAmplifierSize A U D c := by
  unfold independentAmplifierSize
  nlinarith [le_max_left (1 : ℝ) ((D ^ (1 + c) / U) ^ (1 / 6 : ℝ))]

theorem independentAmplifierSize_scale {A U D c gap : ℝ}
    (hA : 1 ≤ A) (hU : 1 ≤ U) (hD : 0 < D)
    (hgap : gap < 1) (hcg : (1 + c) * (1 - gap) = 1) :
    D ≤ (U * independentAmplifierSize A U D c ^ 6) ^ (1 - gap) := by
  have hUpos : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hratio : 0 < D ^ (1 + c) / U :=
    div_pos (Real.rpow_pos_of_pos hD _) hUpos
  have hroot : 0 ≤ (D ^ (1 + c) / U) ^ (1 / 6 : ℝ) := Real.rpow_nonneg hratio.le _
  have hbase : (D ^ (1 + c) / U) ^ (1 / 6 : ℝ) ≤
      independentAmplifierSize A U D c := by
    unfold independentAmplifierSize
    have hm := le_max_right (1 : ℝ) ((D ^ (1 + c) / U) ^ (1 / 6 : ℝ))
    have hm0 := zero_le_one.trans (le_max_left (1 : ℝ)
      ((D ^ (1 + c) / U) ^ (1 / 6 : ℝ)))
    nlinarith
  have hpow := pow_le_pow_left₀ hroot hbase 6
  have heq : ((D ^ (1 + c) / U) ^ (1 / 6 : ℝ)) ^ 6 = D ^ (1 + c) / U := by
    rw [← Real.rpow_mul_natCast hratio.le]
    norm_num
  rw [heq] at hpow
  have hH : D ^ (1 + c) ≤ U * independentAmplifierSize A U D c ^ 6 := by
    simpa only [mul_comm] using (div_le_iff₀ hUpos).mp hpow
  have h := Real.rpow_le_rpow (Real.rpow_nonneg hD.le _) hH (sub_nonneg.mpr hgap.le)
  rw [← Real.rpow_mul hD.le, hcg, Real.rpow_one] at h
  exact h

/-- Once L is close enough to 5, the balancing choice yields the exact
two-scale central exponent. U and D are independent and at least one. -/
theorem independentAmplifierSize_energy {A U D c e L ε : ℝ}
    (hA : 0 < A) (hU : 1 ≤ U) (hD : 1 ≤ D)
    (he : e ≤ ε) (hε : 0 ≤ ε)
    (hUL : 1 + e - L / 6 ≤ 1 / 6)
    (hDL : (1 + c) * (L / 6) ≤ 5 * (1 + c) / 6 + ε) :
    U ^ (1 + e) * independentAmplifierSize A U D c ^ L ≤
      A ^ L * max U (U ^ (1 / 6 : ℝ) * D ^ (5 * (1 + c) / 6)) * (U * D) ^ ε := by
  have hUpos : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hratio : 0 < D ^ (1 + c) / U :=
    div_pos (Real.rpow_pos_of_pos hDpos _) hUpos
  have hUD : U ≤ U * D := by nlinarith
  have hDU : D ≤ U * D := by nlinarith
  have hmax0 : 0 ≤ max U (U ^ (1 / 6 : ℝ) * D ^ (5 * (1 + c) / 6)) :=
    hUpos.le.trans (le_max_left _ _)
  by_cases hlarge : D ^ (1 + c) ≤ U
  · have hr1 : D ^ (1 + c) / U ≤ 1 := (div_le_one hUpos).mpr hlarge
    have hroot1 : (D ^ (1 + c) / U) ^ (1 / 6 : ℝ) ≤ 1 := by
      simpa using Real.rpow_le_rpow hratio.le hr1 (show (0 : ℝ) ≤ 1 / 6 by norm_num)
    have hP : independentAmplifierSize A U D c = A := by
      simp only [independentAmplifierSize, max_eq_left hroot1, mul_one]
    rw [hP, Real.rpow_add hUpos, Real.rpow_one]
    calc
      U * U ^ e * A ^ L ≤ U * (U * D) ^ ε * A ^ L := by
        gcongr
        exact (Real.rpow_le_rpow_of_exponent_le hU he).trans
          (Real.rpow_le_rpow hUpos.le hUD hε)
      _ ≤ max U (U ^ (1 / 6 : ℝ) * D ^ (5 * (1 + c) / 6)) * (U * D) ^ ε * A ^ L := by
        gcongr
        exact le_max_left _ _
      _ = _ := by ring
  · have hr1 : 1 ≤ D ^ (1 + c) / U :=
      (one_le_div hUpos).mpr (le_of_not_ge hlarge)
    have hroot1 : 1 ≤ (D ^ (1 + c) / U) ^ (1 / 6 : ℝ) :=
      Real.one_le_rpow hr1 (by norm_num)
    have hP : independentAmplifierSize A U D c =
        A * (D ^ (1 + c) / U) ^ (1 / 6 : ℝ) := by
      simp only [independentAmplifierSize, max_eq_right hroot1]
    have hform : U ^ (1 + e) * independentAmplifierSize A U D c ^ L =
        A ^ L * (U ^ (1 + e - L / 6) * D ^ ((1 + c) * (L / 6))) := by
      rw [hP, Real.mul_rpow hA.le (Real.rpow_nonneg hratio.le _),
        ← Real.rpow_mul hratio.le]
      have hexp : (1 / 6 : ℝ) * L = L / 6 := by ring
      rw [hexp, Real.div_rpow (Real.rpow_nonneg hDpos.le _) hUpos.le,
        ← Real.rpow_mul hDpos.le, Real.rpow_sub hUpos]
      ring
    rw [hform]
    have hUbound := Real.rpow_le_rpow_of_exponent_le hU hUL
    have hDbound : D ^ ((1 + c) * (L / 6)) ≤
        D ^ (5 * (1 + c) / 6) * (U * D) ^ ε := by
      calc
        _ ≤ D ^ (5 * (1 + c) / 6 + ε) :=
          Real.rpow_le_rpow_of_exponent_le hD hDL
        _ = D ^ (5 * (1 + c) / 6) * D ^ ε := Real.rpow_add hDpos _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hDpos.le hDU hε) (Real.rpow_nonneg hDpos.le _)
    calc
      A ^ L * (U ^ (1 + e - L / 6) * D ^ ((1 + c) * (L / 6))) ≤
          A ^ L * (U ^ (1 / 6 : ℝ) *
            (D ^ (5 * (1 + c) / 6) * (U * D) ^ ε)) := by
        gcongr
      _ = A ^ L * (U ^ (1 / 6 : ℝ) * D ^ (5 * (1 + c) / 6)) * (U * D) ^ ε := by ring
      _ ≤ _ := by
        gcongr
        exact le_max_right _ _

end HeckeGeneral.Analysis.ActualSIntegerMoments
