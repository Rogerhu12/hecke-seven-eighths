import HeckeGeneral.Analysis.TIPSources

/-! Increasing a detector loss keeps the exact witnesses, values and rows.
This permits choosing the internal zero-bin width below a second outer loss
without shortening the shell range governed by the first outer loss. -/

set_option autoImplicit false
noncomputable section
namespace HeckeGeneral.ThetaSkeleton.TIP

theorem WitnessCover.mono_loss {Row : Type} {J : ℕ} {A : AmplitudeSet Row J}
    {t δ U lam lam' k : ℝ} (h : WitnessCover A t δ U lam k)
    (hU : 1 ≤ U) (hk : 0 ≤ k) (hlam : lam ≤ lam') :
    WitnessCover A t δ U lam' k := by
  refine ⟨h.1.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hU hlam) hk), h.2.1, ?_⟩
  intro j
  obtain ⟨hsub, hr, hn, hupper, hlower, hinv, hplain⟩ := h.2.2 j
  refine ⟨hsub, hr, hn, hupper.trans (by linarith),
    (sub_le_sub_left hlam t).trans hlower, ?_, ?_⟩
  · intro u hu
    exact (Real.rpow_le_rpow_of_exponent_le hU
      (sub_le_sub_left hlam _)).trans (hinv u hu)
  · intro u hu
    exact (Real.rpow_le_rpow_of_exponent_le hU
      (sub_le_sub_left hlam _)).trans (hplain u hu)

end HeckeGeneral.ThetaSkeleton.TIP

#print axioms HeckeGeneral.ThetaSkeleton.TIP.WitnessCover.mono_loss
