import HeckeSkeleton.Moments.MOM_INV_STEP.SecondParentProduction
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstMaskGeometry

/-!
# The actual second radial cost

The second mask divisor divides the fresh, frozen squarefree common
ideal. Consequently r N(d₂) (X/N(g))² is at most r X². This gives an
arbitrarily small uniform power of the base without any free scalar
envelope assumption, and without changing the original unit sectors.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondParentRadialBudget

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Bridge
  HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools ActualDivisorSectors
  SecondParentProduction
open scoped Classical BigOperators nonZeroDivisors

private theorem scalar_bound (r d X g : ℝ) (hr : 0 ≤ r) (hg : 1 ≤ g)
    (hd : d ≤ g) : r * d * (X / g) * (X / g) ≤ r * X ^ 2 := by
  have hg0 : 0 < g := zero_lt_one.trans_le hg
  have hgg : 0 < g * g := mul_pos hg0 hg0
  have hdg : d / (g * g) ≤ 1 := (div_le_one hgg).mpr
    (hd.trans (le_mul_of_one_le_right hg0.le hg))
  calc
    _ = (r * X ^ 2) * (d / (g * g)) := by field_simp [hg0.ne']; ring
    _ ≤ (r * X ^ 2) * 1 := mul_le_mul_of_nonneg_left hdg
      (mul_nonneg hr (sq_nonneg _))
    _ = _ := mul_one _

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))

variable {σ : Type*} [DecidableEq σ]
variable {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}

theorem selectedDivisor_dvd (T : Data K S σ Θ ψ) (i : Index K S D Γ T) :
    (divisorIdeal K S (selectedDivisor K S D Γ T i)).val.val ∣ i.1.val.val.val :=
  SecondSourceMasks.actual_divisor_dvd K S D i.1.val
    (squarefreePool_squarefree K Sset i.1.property) i.2.1.val
    (Finset.mem_powerset.mp i.2.1.property)

theorem selectedDivisor_norm_le (T : Data K S σ Θ ψ) (i : Index K S D Γ T) :
    (sIntegerElementNorm K Sset (selectedDivisor K S D Γ T i)).val ≤
      height K Sset i.1.val := by
  rw [← divisorIdeal_norm]
  exact FirstMaskGeometry.absNorm_le_of_dvd K _ _
    (nonZeroDivisors.coe_ne_zero i.1.val.val) (selectedDivisor_dvd K S D Γ T i)

/-- The whole second source, before selecting any frequency or sector,
has radial cost bounded by the original row and column scales. -/
theorem parent_radialScale_le (T : Data K S σ Θ ψ) (i : Index K S D Γ T) :
    radialScale K S D Γ T i ≤ T.radius.val * (scale K S T) ^ 2 := by
  change T.radius.val * (sIntegerElementNorm K Sset (selectedDivisor K S D Γ T i)).val *
      (scale K S T / height K Sset i.1.val) *
      (scale K S T / height K Sset i.1.val) ≤ _
  exact scalar_bound _ _ _ _ T.radius.property.le (height_one_le K Sset i.1.val)
    (selectedDivisor_norm_le K S D Γ T i)

theorem parent_radialScale_power_le (T : Data K S σ Θ ψ)
    (Z R L ε : ℝ) (hZ : 0 < Z) (hε : 0 ≤ ε)
    (hr : T.radius.val ≤ Z ^ R) (hX : scale K S T ≤ Z ^ L)
    (i : Index K S D Γ T) :
    radialScale K S D Γ T i ^ ε ≤ Z ^ ((R + 2 * L) * ε) := by
  have hbase : T.radius.val * (scale K S T) ^ 2 ≤ Z ^ (R + 2 * L) := by
    calc
      _ ≤ Z ^ R * (Z ^ L) ^ 2 :=
        mul_le_mul hr (pow_le_pow_left₀ (scale_pos K S T).le hX 2)
          (sq_nonneg _) (Real.rpow_nonneg hZ.le R)
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hZ.le,
          ← Real.rpow_add hZ]
        congr 1
        ring
  have hb := Real.rpow_le_rpow (radialScale_pos K S D Γ T i).le
    ((parent_radialScale_le K S D Γ T i).trans hbase) hε
  simpa only [← Real.rpow_mul hZ.le] using hb

/-- The common epsilon is chosen before the base, source data, labels,
prime lists, actual mask divisor and bare frequency. -/
theorem exists_uniform_small_power (lengthCap pi : ℝ)
    (hcap : 0 ≤ lengthCap) (hpi : 0 < pi) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ {σ₀ : Type*} [DecidableEq σ₀]
        {Θ₀ : Subgroup (HeckeCharacter K)} {ψ₀ : HeckeCharacter K}
        (T : Data K S σ₀ Θ₀ ψ₀),
      ∀ Z R L : ℝ, 1 ≤ Z → R ≤ lengthCap → L ≤ lengthCap →
      T.radius.val ≤ Z ^ R → scale K S T ≤ Z ^ L →
      ∀ i : Index K S D Γ T, radialScale K S D Γ T i ^ ε ≤ Z ^ pi := by
  let ε := pi / (3 * lengthCap + 1)
  have hden : 0 < 3 * lengthCap + 1 := by linarith
  have hε : 0 < ε := div_pos hpi hden
  refine ⟨ε, hε, ?_⟩
  intro σ₀ _ Θ₀ ψ₀ T Z R L hZ hR hL hr hX i
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hexponent : (R + 2 * L) * ε ≤ pi := by
    have hsum : R + 2 * L ≤ 3 * lengthCap := by linarith
    have hratio : 3 * lengthCap / (3 * lengthCap + 1) ≤ 1 :=
      (div_le_iff₀ hden).mpr (by linarith)
    calc
      _ ≤ (3 * lengthCap) * ε := mul_le_mul_of_nonneg_right hsum hε.le
      _ = pi * (3 * lengthCap / (3 * lengthCap + 1)) := by dsimp only [ε]; ring
      _ ≤ pi * 1 := mul_le_mul_of_nonneg_left hratio hpi.le
      _ = pi := mul_one _
  exact (parent_radialScale_power_le K S D Γ T Z R L ε hz hε.le hr hX i).trans
    (Real.rpow_le_rpow_of_exponent_le hZ hexponent)

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondParentRadialBudget

end
