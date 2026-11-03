import HeckeSkeleton.GramDefinitions
import ActualGramRowBallOrbitalMajorant

/-!
GR-10 (row-ball majorant), closed from the natively verified Gram core module
`ActualGramRowBallOrbitalMajorant`.

The core states its results for `S : Finset (HeightOneSpectrum (𝓞 K))` with the
place set `(S : Set _)`; `HeckeSkeleton.Gram` works with `S : Set _` and a local
`[Fintype S]`. We transport by writing `S = ↑T` for a finset `T` and replacing the
local `Fintype` instance by the canonical `FinsetCoe.fintype` (`Fintype` is a
subsingleton). The test function is the core's `rowBallArchTest` tensored with
`sIntegerFiniteTestFunction` of `rowBallFiniteFamily`, and the constant is the
retained unnormalised Haar covolume of the sixth-power unit sectors.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.GramRowBall
open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.Analysis.SquarefreeAmplification
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors
-- Additional namespaces used only in the proof (core tests and the finite tensor).
open HeckeGeneral.Bridge
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

theorem row_ball_majorant (B : ℝ) (hB : 0 < B) :
    ∃ (φ : SchwartzMap V ℂ)
      (ψ : ((v : S) → v.val.adicCompletion K) → ℂ) (c : ℝ),
      0 < c ∧ Continuous ψ ∧ HasCompactSupport ψ ∧
      (∀ x, (sLocalTensorTestFunction K S φ ψ x).im = 0 ∧
        0 ≤ (sLocalTensorTestFunction K S φ ψ x).re) ∧
      ∀ R : {r : ℝ // 0 < r}, R.val ≤ B →
        c ≤ (sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ) R).re := by
  -- Positivity of `B` is not needed: for `B ≤ 0` the radius condition is vacuous.
  have _hB := hB
  obtain ⟨T, rfl⟩ : ∃ T : Finset (HeightOneSpectrum (𝓞 K)), (T : Set _) = S :=
    ⟨S.toFinset, Set.coe_toFinset S⟩
  obtain rfl : ‹Fintype (T : Set (HeightOneSpectrum (𝓞 K)))› = FinsetCoe.fintype T :=
    Subsingleton.elim _ _
  have : (sixthPowerUnits K (T : Set (HeightOneSpectrum (𝓞 K)))).FiniteIndex :=
    sUnit_power_range_finiteIndex K (T : Set (HeightOneSpectrum (𝓞 K))) 6 (by decide)
  exact ⟨rowBallArchTest K T B, sIntegerFiniteTestFunction K T (rowBallFiniteFamily K T B),
    (sUnitHaarCovolume K (T : Set (HeightOneSpectrum (𝓞 K)))
      (sixthPowerUnits K (T : Set (HeightOneSpectrum (𝓞 K))))).toReal,
    rowBall_covolume_pos K T,
    continuous_sIntegerFiniteTestFunction K T _ (rowBallFiniteFamily_locallyConstant K T B),
    hasCompactSupport_sIntegerFiniteTestFunction K T _
      (rowBallFiniteFamily_compactSupport K T B),
    rowBall_tensor_nonnegative K T B,
    fun R hR => rowBall_orbitalProfile_lower K T B R hR⟩

end HeckeSkeleton.GramRowBall
