import ActualChoiceMaskedTotalNorm
import SmallRadiusAnnularMellinSchwartz

/-!
UNCOMPILED / native 0. Aggregate the existing all-positive-radius bound
for the original joint Schwartz kernel over the exact fixed finite fibres
used by the whole-column estimate. No Fourier seminorm is substituted for
an original Schwartz seminorm. The finite multiplicity is absorbed into
the constant before the Mellin parameter, Schwartz input and radius move.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualFixedBoxTotalNormSeminormDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.Arithmetic.AllowedGeneratorSectionDraft
open ActualGeneratorChoiceDraft ActualChoiceMaskedTotalNormDraft
open SmallRadiusAnnularMellinSchwartzDraft
open scoped Classical BigOperators ContDiff

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
  LanglandsTunnell.TateLocal.borelSpace_localBorel

variable (K : Type) [Field K] [NumberField K]
variable (w : GeneratorMaskWitness K)
local notation "S" => (w.S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Γ" => sixthPowerUnits K S
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local instance : Subgroup.FiniteIndex Γ := sUnit_power_range_finiteIndex K S 6 (by decide)
local notation "H" => finiteIndexSUnitBoxWidth K S Γ

variable [MeasurableSpace (sLocalNormOneGroup K (w.S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (w.S : Set (HeightOneSpectrum (𝓞 K))))]
variable (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a)
  (a0 b0 : ℝ) (ha0 : 0 < a0) (haSupport : tsupport a ⊆ Set.Icc a0 b0)
  (ψ : ((v : (w.S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ)
  (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)

/-- A genuine uniform scalar envelope for the exact finite seminorm sum.
The positive radius may be arbitrarily small; its only loss is R^(-σ). -/
theorem exists_fixedBoxTotalNormJointSeminormSum_allRadius_bound
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (t : Finset (ℕ × ℕ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, ∃ J : ℕ, 0 ≤ C ∧
      ∀ ν : ℝ, ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r},
        fixedBoxTotalNormJointSeminormSum K w a ha a0 b0 ha0 haSupport
          ψ hψ hψsupport t ν φ R ≤
        C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * R.val ^ (-σ) := by
  letI : IsTotallyComplex K := w.totallyComplex
  letI : MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ := borel _
  letI : BorelSpace (mixedEmbedding.mixedSpace K)ˣ := ⟨rfl⟩
  letI : ∀ v : S, MeasurableSpace (v.val.adicCompletion K)ˣ := fun _ => borel _
  letI : ∀ v : S, BorelSpace (v.val.adicCompletion K)ˣ := fun _ => ⟨rfl⟩
  obtain ⟨s, C, J, hC, hb⟩ :=
    exists_sUnitTotalNormAnnularPartitionJointSchwartz_finite_seminorm_allRadius_bound
      K S Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport σ hσ hσ1 t
  let n : ℝ := Fintype.card (S → Fin H)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  refine ⟨s, n * n * C, J, mul_nonneg (mul_nonneg hn hn) hC, ?_⟩
  intro ν φ R
  unfold fixedBoxTotalNormJointSeminormSum
  calc
    _ ≤ ∑ _e₁ : S → Fin H, ∑ _e₂ : S → Fin H,
        C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * R.val ^ (-σ) := by
      apply Finset.sum_le_sum
      intro e₁ _
      apply Finset.sum_le_sum
      intro e₂ _
      exact hb ν (sUnitPartitionFiniteFibreRepresentative K S H e₁)
        (sUnitPartitionFiniteFibreRepresentative K S H e₂) φ R
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      dsimp only [n]
      ring

end HeckeGeneral.ThetaSkeleton.Physical.ActualFixedBoxTotalNormSeminormDraft
