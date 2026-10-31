import ActualAnnularAllScaleCount

/-!
UNCOMPILED candidate. The trivial branch of the two-column estimate on
the actual annular support, for every positive norm scale. Only support
and pointwise magnitude are required of the summand; no counting premise
or lower bound on the norm scale is supplied.
-/

noncomputable section

namespace HeckeGeneral.Analysis.ActualAnnularAllScaleCountDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

local notation "NZ" => NonzeroRingElements (S.integer K)

/-- The uniform O(Q N²) bound includes N < 1 and retains all associates.
The support condition refers to the original two actual annular columns. -/
theorem exists_actualAnnular_trivial_sum_bound
    (a : ℝ → ℝ) (a0 b0 : ℝ) (ha0 : 0 < a0)
    (haSupport : tsupport a ⊆ Set.Icc a0 b0) :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 0 < Y → ∀ Q : ℝ, 0 ≤ Q →
      ∀ f : NZ × NZ → ℂ,
        (∀ m, f m ≠ 0 →
          sIntegerAnnularColumn K S Γ a (Y ^ (Module.finrank ℚ K : ℝ)⁻¹) m.1 ≠ 0 ∧
          sIntegerAnnularColumn K S Γ a (Y ^ (Module.finrank ℚ K : ℝ)⁻¹) m.2 ≠ 0) →
        (∀ m, ‖f m‖ ≤ Q) →
        ‖∑' m, f m‖ ≤ C * Q * Y ^ 2 := by
  obtain ⟨C, hC, hcount⟩ :=
    exists_sIntegerAnnularColumn_allScale_norm_count_le K S Γ a a0 b0 ha0 haSupport
  refine ⟨C ^ 2, pow_pos hC _, fun Y hY Q hQ f hsupport hsize => ?_⟩
  let r := Y ^ (Module.finrank ℚ K : ℝ)⁻¹
  have hr : r ≠ 0 := (Real.rpow_pos_of_pos hY _).ne'
  have hs := finite_support_sIntegerAnnularColumn K S Γ a a0 b0 ha0 haSupport r hr
  let T := hs.toFinset ×ˢ hs.toFinset
  have hzero : ∀ m ∉ T, f m = 0 := by
    intro m hm
    by_contra hne
    obtain ⟨h1, h2⟩ := hsupport m hne
    exact hm (Finset.mem_product.mpr
      ⟨hs.mem_toFinset.mpr h1, hs.mem_toFinset.mpr h2⟩)
  have hcard : (hs.toFinset.card : ℝ) ≤ C * Y := by
    rw [← Nat.card_eq_card_finite_toFinset hs]
    exact hcount Y hY
  have hpair : (T.card : ℝ) ≤ C ^ 2 * Y ^ 2 := by
    dsimp only [T]
    rw [Finset.card_product, Nat.cast_mul, ← pow_two]
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2).trans_eq (mul_pow _ _ _)
  rw [tsum_eq_sum hzero]
  calc
    _ ≤ ∑ _m ∈ T, Q := norm_sum_le_of_le _ (fun m _ => hsize m)
    _ = (T.card : ℝ) * Q := by simp
    _ ≤ (C ^ 2 * Y ^ 2) * Q := mul_le_mul_of_nonneg_right hpair hQ
    _ = C ^ 2 * Q * Y ^ 2 := by ring

end HeckeGeneral.Analysis.ActualAnnularAllScaleCountDraft
