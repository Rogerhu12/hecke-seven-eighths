import HeckeSkeleton.Moments.MOM_INV_STEP.FirstToSecondData

/-!
# The genuine second Poisson identity on the first free production energy

This is the actual first centered inverse family and fixed positive row
test. Its second source is formed by the genuine Poisson theorem. The
cutoff is frozen at the original fresh common ideal and actual divisor;
both additive zero terms are retained. The second statement isolates
the whole principal source, including its retained nonzero dual part.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstProductionPoisson

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools FirstParentRows FirstToSecondData
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "OS" => Set.integer Sset K
variable {σ : Type*} [DecidableEq σ]
variable (T : FirstParentEnergy.Data K S (σ := σ))
variable (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
variable (hbase : 1 < T.columns.base)
variable (R : OuterIndex K S D T → {r : ℝ // 0 < r})
variable (U : {r : ℝ // 0 < r}) (J : Finset σ) (s : ℝ)
variable (H₂ : ∀ o : OuterIndex K S D T, Ext → Finset (HeightOneSpectrum OS) → ℝ)

include ν μ in
theorem first_free_split (o : OuterIndex K S D T)
    (e : FirstOuterCenters.Overlap K S D T o) :
    FirstFreeMellinEnergy.freeEnergyAt K S Γ D T.columns Θ ψ G hν hG J U.val
      (-(1 / 2 : ℝ)) (triple K S D T o e) (label K S D T o).val.val
      (FirstLocalizedEnergy.divisor K S D T o).val (R o) s =
    let Q := data K S D T Θ ψ G hν hG hbase R U J s o e
    let a := DivisorInverseColumn.coefficient K S D Q.columns Q.triple Q.label.val.val Q.divisor.val
    (SecondAdaptiveCutoff.retainedSourceAt K S D Γ hΓ μv a
      (Q.columns.columns Q.triple ×ˢ Q.columns.columns Q.triple)
      Q.archTest Q.localTest Q.locallyConstant Q.compactSupport Q.radius (H₂ o) +
      SecondPoissonSplit.additiveZeros K S D Γ hΓ μv a (Q.columns.columns Q.triple)
        Q.archTest Q.localTest Q.locallyConstant Q.compactSupport Q.radius +
      SecondAdaptiveCutoff.tailSourceAt K S D Γ hΓ μv a
        (Q.columns.columns Q.triple ×ˢ Q.columns.columns Q.triple)
        Q.archTest Q.localTest Q.locallyConstant Q.compactSupport Q.radius (H₂ o)).re := by
  let Q := data K S D T Θ ψ G hν hG hbase R U J s o e
  exact congrArg Complex.re
    (SecondAdaptiveCutoff.genuine_second_split_at K S D Γ hΓ μv ν μ
      Q.columns Q.triple Q.label.val.val Q.divisor.val Q.archTest Q.localTest
      Q.locallyConstant Q.compactSupport Q.radius (H₂ o))

/-- Principal restoration subtracts the original principal dual source
after the full-source positive bound. No moving principal restriction
is introduced into either independent residual column. -/
include ν μ in
theorem first_free_principal_restored (o : OuterIndex K S D T)
    (e : FirstOuterCenters.Overlap K S D T o) :
    FirstFreeMellinEnergy.freeEnergyAt K S Γ D T.columns Θ ψ G hν hG J U.val
      (-(1 / 2 : ℝ)) (triple K S D T o e) (label K S D T o).val.val
      (FirstLocalizedEnergy.divisor K S D T o).val (R o) s =
    let Q := data K S D T Θ ψ G hν hG hbase R U J s o e
    let a := DivisorInverseColumn.coefficient K S D Q.columns Q.triple Q.label.val.val Q.divisor.val
    let P := Q.columns.columns Q.triple
    (SecondPoissonSplit.physicalPrincipal K S D Γ hΓ a P
      Q.archTest Q.localTest Q.locallyConstant Q.compactSupport Q.radius +
      (SecondAdaptiveCutoff.retainedSourceAt K S D Γ hΓ μv a (P ×ˢ P)
        Q.archTest Q.localTest Q.locallyConstant Q.compactSupport Q.radius (H₂ o) -
        SecondAdaptiveCutoff.retainedSourceAt K S D Γ hΓ μv a
          (SecondPoissonSplit.principalPairs K S D P)
          Q.archTest Q.localTest Q.locallyConstant Q.compactSupport Q.radius (H₂ o)) +
      (SecondAdaptiveCutoff.tailSourceAt K S D Γ hΓ μv a (P ×ˢ P)
        Q.archTest Q.localTest Q.locallyConstant Q.compactSupport Q.radius (H₂ o) -
        SecondAdaptiveCutoff.tailSourceAt K S D Γ hΓ μv a
          (SecondPoissonSplit.principalPairs K S D P)
          Q.archTest Q.localTest Q.locallyConstant Q.compactSupport Q.radius (H₂ o))).re := by
  rw [first_free_split K S D Γ hΓ μv ν μ T Θ ψ G hν hG hbase R U J s H₂ o e]
  dsimp only
  congr 1
  rw [SecondAdaptiveCutoff.physicalPrincipal_eq_retained_add_zeros_add_tail_at
    K S D Γ hΓ μv ν μ]
  ring

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstProductionPoisson

end
