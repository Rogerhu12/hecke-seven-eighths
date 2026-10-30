import HeckeSkeleton.GramDefinitions
import HeckeSkeleton.SmallRadius.SmallRadiusUniformPointBound

/-!
# Small-radius orbital profile (obligation GR-11)

The orbital profile `R ↦ sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ) R`
of a free archimedean Schwartz test `φ` against a fixed compactly supported
continuous finite-place test `ψ` is controlled on the whole log-radius axis
`R = exp v` by finitely many original Schwartz seminorms of `φ`, with the
requested Mellin loss `exp (-σ t)` at the small-radius end.

The proof assembles the genuine chain of the `HeckeSkeleton.SmallRadius` modules:
the multi-place product-Haar absolute Mellin moment bound (finite and archimedean
Haar factors, radial comparison), Fubini on the norm-one orbit, and the actual
Euler FTC on a unit log interval.  The constant and the finite seminorm family
precede `φ`, the radius and the derivative order.
-/
set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.GramSmallRadius
open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.Analysis.SquarefreeAmplification
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors
variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

section Profiles
variable [MeasurableSpace (sLocalNormOneGroup K S)]
  [BorelSpace (sLocalNormOneGroup K S)]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

/-- GR-11, small-radius profile bound (free test, all radii). -/
theorem small_radius_profile [IsTotallyComplex K]
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hcs : HasCompactSupport ψ)
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (J : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (φ : SchwartzMap V ℂ) (t : ℝ) (j : ℕ), j ≤ J →
        ‖iteratedDeriv j (fun v : ℝ =>
          sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
            ⟨Real.exp v, Real.exp_pos v⟩) t‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * Real.exp (-σ * t) := by
  let _ : MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ := borel _
  have : BorelSpace (mixedEmbedding.mixedSpace K)ˣ := ⟨rfl⟩
  let _ : ∀ v : S, MeasurableSpace (v.val.adicCompletion K)ˣ := fun _ => borel _
  have : ∀ v : S, BorelSpace (v.val.adicCompletion K)ˣ := fun _ => ⟨rfl⟩
  obtain ⟨s, C, hC, hb⟩ :=
    HeckeGeneral.Analysis.SmallRadiusUniformPointDraft.exists_uniform_weighted_logEuler_point_bound
      K S (⊤ : Subgroup (S.unit K)) ψ hψ hcs σ hσ hσ1 J
  refine ⟨s, C, hC, fun φ t j hj => ?_⟩
  have hder : iteratedDeriv j (fun v : ℝ =>
      sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
        ⟨Real.exp v, Real.exp_pos v⟩) t =
      HeckeGeneral.Analysis.SmallRadiusOrbitalFTCDraft.sUnitEulerLogProfile K S φ ψ j t := by
    have h := HeckeGeneral.Analysis.SmallRadiusOrbitalFTCDraft.iteratedDeriv_sUnitEulerLogProfile
      K S (⊤ : Subgroup (S.unit K)) φ ψ hψ hcs 0 j t
    rw [zero_add] at h
    exact h
  rw [hder]
  have h := hb φ j hj t
  have hexp : Real.exp (σ * t) * Real.exp (-σ * t) = 1 := by
    rw [← Real.exp_add, show σ * t + -σ * t = 0 by ring, Real.exp_zero]
  calc
    _ = (Real.exp (σ * t) *
          ‖HeckeGeneral.Analysis.SmallRadiusOrbitalFTCDraft.sUnitEulerLogProfile K S φ ψ j t‖) *
        Real.exp (-σ * t) := by rw [mul_right_comm, hexp, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right h (Real.exp_pos _).le

end Profiles

end HeckeSkeleton.GramSmallRadius
