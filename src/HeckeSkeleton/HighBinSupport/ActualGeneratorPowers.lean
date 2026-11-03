import HeckeGeneral.Analysis.PrincipalGeneratorCalibration
import HeckeGeneral.Characters.SIntegerSexticPowerMask
/-!
# Actual allowed-generator powers and locally invertible sixth powers

PROJECT-ONLY CANDIDATE: not included in the independently verified
Mathlib chain. These proof bodies use the exact uploaded project data.
The chosen prime-power generator is proved to differ from the power of
the prime generator by a sixth power of an actual S-unit.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-30.
-/

noncomputable section
namespace HeckeSkeleton.HighBinActualGenerators
open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open scoped Classical nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Powers retain exactly the same exterior condition. -/
def exteriorPower (I : ExteriorIdeal K S) (n : ℕ) : ExteriorIdeal K S :=
  ⟨I.val ^ n, by
    intro p hp
    apply I.property p
    apply p.prime.dvd_of_dvd_pow
    simpa only [SubmonoidClass.coe_pow] using hp⟩

@[simp] theorem exteriorPower_one (I : ExteriorIdeal K S) : exteriorPower K S I 1 = I := by
  apply Subtype.ext
  exact pow_one I.val

theorem exteriorPower_succ (I : ExteriorIdeal K S) (n : ℕ) :
    exteriorPower K S I (n + 1) = exteriorMul K S (exteriorPower K S I n) I := by
  apply Subtype.ext
  change I.val ^ (n + 1) = I.val ^ n * I.val
  exact pow_succ I.val n

/-- This produces the actual sixth unit; generator-power compatibility is
not inserted as another arithmetic input. The unit-ideal base case uses
the existing consequence of AllowedGeneratorInput.multiplicative. -/
theorem generator_power_eq_sixth_unit (D : ThetaArithmeticData K S)
    (hD : AllowedGeneratorInput K S D) (I : ExteriorIdeal K S) (n : ℕ) :
    ∃ u : S.unit K, D.generator (exteriorPower K S I n) =
      (S.unitEquivUnitsInteger K u).val ^ 6 * D.generator I ^ n := by
  induction n with
  | zero =>
    obtain ⟨u, hu⟩ :=
      AllowedGeneratorInput.generator_eq_sixth_power_of_ideal_eq_one K S D hD
        (exteriorPower K S I 0) (by change I.val ^ 0 = 1; exact pow_zero _)
    exact ⟨u, by simpa only [pow_zero, mul_one] using hu⟩
  | succ n ih =>
    obtain ⟨v, hv⟩ := ih
    obtain ⟨u, hu⟩ := hD.multiplicative (exteriorPower K S I n) I
    refine ⟨u * v, ?_⟩
    rw [exteriorPower_succ, hu, hv]
    simp only [map_mul, Units.val_mul, mul_pow]
    rw [pow_succ (D.generator I) n]
    ring

/-- A sixth power of a locally invertible numerator has symbol one.
Unlike a global S-unit statement, this covers the generators belonging
to a different CRT prime block. -/
theorem idealSymbol_sixth_power_of_coprime (D : ThetaArithmeticData K S)
    (I : ExteriorIdeal K S) (a : S.integer K)
    (ha : IsCoprime I.val.val (sIntegerModulusContraction K S a)) :
    idealSymbol K S D I (a ^ 6) = 1 := by
  unfold idealSymbol
  rw [sIntegerSexticIdealEvaluation_sixth_power_coprime_mask K S D.root6
    D.primitive6 D.embedding I.val.val (nonZeroDivisors.coe_ne_zero I.val)
    I.property (fun p hp => D.away_six p (I.property p hp)) a, if_pos ha]

/-- The original ideal-symbol function, including all zeros, is invariant
under that locally invertible sixth-power multiplication. -/
theorem idealSymbol_local_sixth_invariant (D : ThetaArithmeticData K S)
    (I : ExteriorIdeal K S) (a x : S.integer K)
    (ha : IsCoprime I.val.val (sIntegerModulusContraction K S a)) :
    idealSymbol K S D I (a ^ 6 * x) = idealSymbol K S D I x := by
  have hm : idealSymbol K S D I (a ^ 6 * x) =
      idealSymbol K S D I (a ^ 6) * idealSymbol K S D I x :=
    sIntegerSexticIdealEvaluation_mul K S D.root6 D.primitive6 D.embedding
      I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
      (fun p hp => D.away_six p (I.property p hp)) (a ^ 6) x
  rw [hm, idealSymbol_sixth_power_of_coprime K S D I a ha, one_mul]

#print axioms generator_power_eq_sixth_unit
#print axioms idealSymbol_local_sixth_invariant
end HeckeSkeleton.HighBinActualGenerators
