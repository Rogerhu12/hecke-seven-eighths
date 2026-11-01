import HeckeSkeleton.Moments.MOM_INV_STEP.FirstActualErrorTotal
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstLocalizedRadialBudget
import HeckeSkeleton.Moments.MOM_INV_STEP.UniformSecondTail

/-!
# The radial and old-row small powers in the actual first error measure

Both factors are retained in the actual finite spectral error sum.
A single epsilon and old-row exponent are chosen before Z and all
source data, using the proved source geometry for the production mask
empty. Their total cost is any prescribed positive power of Z. The
comparison below then removes precisely these two factors from the
literal total estimated in FirstActualErrorTotal.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstActualErrorPowers

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools FirstParentRows
  FirstErrorIntegration FirstCenteredErrorIntegrals
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))

/-- A priori geometry, not an error estimate, pays for both powers.
Their exponents and the constant precede the source and all scales. -/
theorem exists_uniform_weight_cost (lengthCap Hcap pi : ℝ)
    (hcap : 0 ≤ lengthCap) (hHcap : 0 ≤ Hcap) (hpi : 0 < pi) :
    ∃ ε massEps : ℝ, 0 < ε ∧ 0 < massEps ∧ ∃ A : ℝ, 1 ≤ A ∧
      ∀ {σ : Type*} (T : FirstParentEnergy.Data K S (σ := σ)),
      T.mask = ∅ → ∀ Z R B L H : ℝ, 1 ≤ Z →
      R ≤ lengthCap → B ≤ lengthCap → L ≤ lengthCap → H ≤ Hcap →
      T.radius.val ≤ Z ^ R →
      (∀ b ∈ T.cubes, (b.val.val.absNorm : ℝ) ≤ Z ^ B) →
      T.scale.val ≤ Z ^ L →
      ∀ o : OuterIndex K S D T,
        FirstLocalizedEnergy.radialScale K S D T o ^ ε *
          (Z ^ H) ^ massEps ≤ A * Z ^ pi := by
  have hhalf : 0 < pi / 2 := by linarith
  obtain ⟨ε,hε,A,hA,hbound⟩ :=
    FirstLocalizedRadialBudget.exists_uniform_small_power K S D
      lengthCap (pi / 2) hcap hhalf
  let massEps := (pi / 2) / (Hcap + 1)
  have hden : 0 < Hcap + 1 := by linarith
  have hm : 0 < massEps := div_pos hhalf hden
  refine ⟨ε,massEps,hε,hm,A,hA,?_⟩
  intro σ T hmask Z R B L H hZ hR hB hL hH hr hb hX o
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  let Q := FirstInversePoisson.unitIdeal K S
  have hmasks : T.mask = FirstMaskGeometry.externalMask K S Q :=
    hmask.trans (UniformSecondTail.externalMask_unit K S).symm
  have hQ : (Q.val.val.absNorm : ℝ) ≤ Z ^ (0 : ℝ) := by
    change ((1 : Ideal (𝓞 K)).absNorm : ℝ) ≤ Z ^ (0 : ℝ)
    simp only [map_one, Nat.cast_one, Real.rpow_zero, le_refl]
  have hrad := hbound T Q hmasks Z R 0 B L hZ hR hcap hB hL hr hQ hb hX o
  have hexp : H * massEps ≤ pi / 2 := by
    calc
      H * massEps ≤ (Hcap + 1) * massEps :=
        mul_le_mul_of_nonneg_right (by linarith) hm.le
      _ = pi / 2 := by
        dsimp only [massEps]
        field_simp [hden.ne']
  have hrow : (Z ^ H) ^ massEps ≤ Z ^ (pi / 2) := by
    rw [← Real.rpow_mul hz.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ hexp
  have hh := mul_le_mul hrad hrow (Real.rpow_nonneg (Real.rpow_nonneg hz.le _) _)
    (mul_nonneg (zero_le_one.trans hA) (Real.rpow_nonneg hz.le _))
  calc
    _ ≤ (A * Z ^ (pi / 2)) * Z ^ (pi / 2) := hh
    _ = A * Z ^ pi := by
      rw [mul_assoc, ← Real.rpow_add hz]
      congr 2
      ring

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
variable {σ : Type*} [DecidableEq σ]
variable (T : FirstParentEnergy.Data K S (σ := σ))
variable (U : FirstErrorSource.Index K S D T → {r : ℝ // 0 < r})
variable (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
variable (hbase : 1 < T.columns.base)
variable (I : Finset (FirstErrorSource.Index K S D T)) (side : Bool)
variable (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
variable (m : ℕ) (coordinate : CommonKernel.LogPlane → ℝ)

def errorValue (Z H tau : ℝ) (hZ : 0 < Z)
    (i : FirstErrorSource.Index K S D T) (J : Finset σ) : ℝ :=
  spectralAverage (MellinSeparation.density W hW) m coordinate
    (fun s => FirstSecondReduction.errorAt K S D Γ hΓ μv T Θ ψ G hν hG hbase
      (FirstActualErrorTotal.rowCaps K S D T Z H hZ) (U i) J s
      (FirstSecondErrorBridge.cutoff K S D T
        (FirstActualErrorTotal.rowCaps K S D T Z H hZ) (U i) Z tau) i.1 i.2)

theorem errorValue_nonneg (Z H tau : ℝ) (hZ : 0 < Z)
    (i : FirstErrorSource.Index K S D T) (J : Finset σ) :
    0 ≤ errorValue K S D Γ hΓ μv T U Θ ψ G hν hG hbase W hW m coordinate
      Z H tau hZ i J := by
  apply integral_nonneg
  intro ξ
  apply mul_nonneg (FirstCommonEnvelope.frequencyEnvelope_nonneg m ξ)
  apply integral_nonneg
  intro t
  exact mul_nonneg (norm_nonneg _)
    (FirstSecondReduction.errorAt_nonneg K S D Γ hΓ μv T Θ ψ G hν hG hbase
      (FirstActualErrorTotal.rowCaps K S D T Z H hZ) (U i) J
      (t + coordinate ξ) (FirstSecondErrorBridge.cutoff K S D T
        (FirstActualErrorTotal.rowCaps K S D T Z H hZ) (U i) Z tau) i.1 i.2)

def weightedTotal (Z kappa H tau ε massEps : ℝ) (hZ : 0 < Z) : ℝ :=
  (Z ^ kappa * ((T.columns.slots.powerset.card : ℝ) *
    (InverseRowMajorant.rowCovolume K S)⁻¹) * mellinMass W hW) *
    ∑ i ∈ I, ∑ J ∈ T.columns.slots.powerset,
      (FirstLocalizedEnergy.radialScale K S D T i.1 ^ ε * (Z ^ H) ^ massEps) *
      (mobiusWeight K S D T i * ‖mark K S D T side i J‖ ^ 2 *
        errorValue K S D Γ hΓ μv T U Θ ψ G hν hG hbase W hW m coordinate Z H tau hZ i J)

/-- The two explicit positive weight factors are removed after their
proved geometry bound. The integrand is still the actual errorAt. -/
theorem weightedTotal_le (Z kappa H tau ε massEps A : ℝ) (hZ : 0 < Z)
    (hcost : ∀ i ∈ I, FirstLocalizedEnergy.radialScale K S D T i.1 ^ ε *
      (Z ^ H) ^ massEps ≤ A) :
    weightedTotal K S D Γ hΓ μv T U Θ ψ G hν hG hbase I side W hW m coordinate
      Z kappa H tau ε massEps hZ ≤
    A * FirstActualErrorTotal.total K S D Γ hΓ μv T U Θ ψ G hν hG hbase
      I side W hW m coordinate Z kappa H tau hZ := by
  have hout : 0 ≤ Z ^ kappa * ((T.columns.slots.powerset.card : ℝ) *
      (InverseRowMajorant.rowCovolume K S)⁻¹) * mellinMass W hW :=
    mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hZ.le _)
        (mul_nonneg (Nat.cast_nonneg _)
          (inv_nonneg.mpr (InverseRowMajorant.rowCovolume_pos K S).le)))
      (mellinMass_nonneg W hW)
  have hsum :
      (∑ i ∈ I, ∑ J ∈ T.columns.slots.powerset,
        (FirstLocalizedEnergy.radialScale K S D T i.1 ^ ε * (Z ^ H) ^ massEps) *
        (mobiusWeight K S D T i * ‖mark K S D T side i J‖ ^ 2 *
          errorValue K S D Γ hΓ μv T U Θ ψ G hν hG hbase W hW m coordinate Z H tau hZ i J)) ≤
      A * ∑ i ∈ I, ∑ J ∈ T.columns.slots.powerset,
        mobiusWeight K S D T i * ‖mark K S D T side i J‖ ^ 2 *
          errorValue K S D Γ hΓ μv T U Θ ψ G hν hG hbase W hW m coordinate Z H tau hZ i J := by
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro J hJ
    exact mul_le_mul_of_nonneg_right (hcost i hi)
      (mul_nonneg (mul_nonneg (mobiusWeight_nonneg K S D T i) (sq_nonneg _))
        (errorValue_nonneg K S D Γ hΓ μv T U Θ ψ G hν hG hbase W hW m coordinate
          Z H tau hZ i J))
  exact (mul_le_mul_of_nonneg_left hsum hout).trans_eq (by
    unfold FirstActualErrorTotal.total errorValue
    ring)

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstActualErrorPowers

end
