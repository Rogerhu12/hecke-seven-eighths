import HeckeGeneral.Analysis.ActualSIntegerSimultaneousAmplifier

/-! The simultaneous amplifier injects the entire finite product of base
rows and amplifier ideals into the actual orbit sum, without a cardinality
loss in the number of base rows or an assumption of unique ideal generators. -/

noncomputable section
namespace HeckeGeneral.Analysis.ActualSIntegerMoments

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open HeckeGeneral.ThetaSkeleton
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (τ : ThetaArithmeticData K S)

theorem sum_simultaneous_majorants_le_bounded_orbits
    (R : Finset (ActualSixthPowerFreeOrbit K S)) (F : Finset (ExteriorIdeal K S))
    {U P H : ℝ}
    (hR : ∀ q ∈ R, actualSIntegerOrbitNorm K S q.val ≤ U)
    (hF : ∀ A ∈ F, idealNorm K A.val ≤ P) (hH : U * P ^ 6 ≤ H)
    (B : ActualSIntegerOrbit K S → ℝ) (hB : ∀ q, 0 ≤ B q) :
    (∑ q ∈ R, ∑ A ∈ F, B (actualSimultaneousAmplifier K S τ q.val A)) ≤
      ∑ q : ActualBoundedSIntegerOrbits K S H, B q.val := by
  let e : {x : ActualSixthPowerFreeOrbit K S × ExteriorIdeal K S // x ∈ R.product F} →
      ActualBoundedSIntegerOrbits K S H := fun x =>
    ⟨actualSimultaneousAmplifier K S τ x.val.1.val x.val.2,
      (actualSimultaneousAmplifier_norm_le K S τ _ _
        (hR _ (Finset.mem_product.mp x.property).1)
        (hF _ (Finset.mem_product.mp x.property).2)).trans hH⟩
  have he : Function.Injective e := by
    intro x y h
    exact Subtype.ext (actualSimultaneousAmplifier_injective K S τ (congrArg Subtype.val h))
  rw [← Finset.sum_product R F
    (fun x => B (actualSimultaneousAmplifier K S τ x.1.val x.2)),
    ← Finset.sum_coe_sort]
  exact Finset.sum_le_sum_of_injOn e he.injOn (Finset.subset_univ _)
    (fun _ _ => le_rfl) (fun q _ _ => hB q.val)

end HeckeGeneral.Analysis.ActualSIntegerMoments
