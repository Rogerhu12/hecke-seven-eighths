import ThetaGlobal.LocalDigitArithmetic
import ThetaGlobal.LocalDigitEvaluation

/-!
# The actual exterior source satisfies the literal local digit tables

The arithmetic data here use the recipe's own generators, embedding and
roots. The nonzero-digit computation starts from its actual reference
coefficient at `A(x) W N(-s/g_p)`, sums over the chosen residue lifts, and
then applies the proved finite-field phase-separation formula.

The actual local average follows from `JointExteriorCoefficientSources`;
no global identity or global absolute-convergence assumption is used.
The global interface is assembled separately in `LocalDigitInput`.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace ThetaGlobal.LocalDigitAverage

open NumberField IsDedekindDomain DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open ThetaGlobal.LocalDigitArithmetic ThetaGlobal.LocalDigitEvaluation
open scoped NumberField Classical BigOperators

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {N : TraceHaarTransport R} (C : JointExteriorCoefficientSources R N)
variable (hdiff : ∀ p : HeightOneSpectrum (𝓞 F),
  p ∉ (R.A.Sf : Set (HeightOneSpectrum (𝓞 F))) → localDifferentExponent F p = 0)

local notation "Sf" => (R.A.Sf : Set (HeightOneSpectrum (𝓞 F)))
local notation "Adata" => HeckeAxiom.thetaArithmeticData R.A R.probe.allowed R.σ hdiff

theorem nonzero_digits (p : ThetaBranch.ExteriorPrime R.A) (j : Fin 6) (x : Fˣ)
    (L : ThetaDigitAverage.Residue p.val → 𝓞 F)
    (hL : ∀ t, Ideal.Quotient.mk p.val.asIdeal (L t) = t) :
    (∑ t ∈ Finset.univ.erase (0 : ThetaDigitAverage.Residue p.val),
      digitMask F Sf Adata (prime R.A p) j t *
        localDigitValue R C p x (L t)) =
      if ThetaBranch.order p.val x + 2 < 0 then 0 else
        localWeylScalar F Sf Adata (prime R.A p) j
          (ThetaBranch.order p.val x + 2).toNat *
          thetaPrimeCharacter F Sf Adata (prime R.A p)
            (ThetaBranch.unitResidue p.val (ThetaBranch.localUnit R.A R.probe.allowed p x)) ^
              localWeylExponent j (ThetaBranch.order p.val x + 2).toNat := by
  let χ : MulChar (ThetaDigitAverage.Residue p.val) ℂ :=
    thetaPrimeCharacter F Sf Adata (prime R.A p)
  let u : ThetaDigitAverage.Residue p.val :=
    ThetaBranch.unitResidue p.val (ThetaBranch.localUnit R.A R.probe.allowed p x)
  have hvalue (t : ThetaDigitAverage.Residue p.val)
      (ht : t ∈ Finset.univ.erase (0 : ThetaDigitAverage.Residue p.val)) :
      localDigitValue R C p x (L t) =
        sexticSphericalCoefficient (ThetaBranch.residueCharacter R.A R.σ p)
          (Characters.psi R p) (ThetaBranch.order p.val x + 2) *
        χ u ^ (4 + 2 * (ThetaBranch.order p.val x + 2)) * χ t ^ (4 : ℕ) *
        (if ThetaBranch.order p.val x + 2 = 0 then
          primePhase F Sf Adata (prime R.A p) (u / t) else 1) := by
    have h := LocalDigitEvaluation.nonzero_localDigit R C p x (L t)
      (by rw [hL]; exact Finset.ne_of_mem_erase ht)
    rw [hL] at h
    simpa only [ThetaBranch.symbol,
      ← LocalDigitArithmetic.thetaPrimeCharacter_eq R.A R.probe.allowed R.σ hdiff p,
      ← LocalDigitArithmetic.primePhase_eq R hdiff p] using h
  by_cases hneg : ThetaBranch.order p.val x + 2 < 0
  · rw [if_pos hneg]
    apply Finset.sum_eq_zero
    intro t ht
    rw [hvalue t ht]
    simp only [sexticSphericalCoefficient, hneg, ↓reduceIte, zero_mul, mul_zero]
  · let n : ℕ := (ThetaBranch.order p.val x + 2).toNat
    have hn : (n : ℤ) = ThetaBranch.order p.val x + 2 :=
      Int.toNat_of_nonneg (le_of_not_gt hneg)
    have hcoeff :
        sexticSphericalCoefficient (ThetaBranch.residueCharacter R.A R.σ p)
          (Characters.psi R p) (ThetaBranch.order p.val x + 2) =
          sphericalDigit F Sf Adata (prime R.A p) n := by
      have h := (LocalDigitArithmetic.sphericalDigit_eq R hdiff p n).symm
      rw [hn] at h
      exact h
    have hpow : 4 + 2 * (ThetaBranch.order p.val x + 2) =
        ((4 + 2 * n : ℕ) : ℤ) := by omega
    have hzero : ThetaBranch.order p.val x + 2 = 0 ↔ n = 0 := by omega
    have hterm (t : ThetaDigitAverage.Residue p.val)
        (ht : t ∈ Finset.univ.erase (0 : ThetaDigitAverage.Residue p.val)) :
        localDigitValue R C p x (L t) =
          sphericalDigit F Sf Adata (prime R.A p) n * χ u ^ (4 + 2 * n) *
            χ t ^ (4 : ℕ) *
            (if n = 0 then primePhase F Sf Adata (prime R.A p) (u / t) else 1) := by
      rw [hvalue t ht, hcoeff, hpow, zpow_natCast]
      simp only [hzero]
    let f : ThetaDigitAverage.Residue p.val → ℂ := fun t =>
      digitMask F Sf Adata (prime R.A p) j t * χ t ^ (4 : ℕ) *
        (if n = 0 then primePhase F Sf Adata (prime R.A p) (u / t) else 1)
    have hfzero : f 0 = 0 := by
      simp [f, MulChar.map_zero]
    have hsum :
        (∑ t ∈ Finset.univ.erase (0 : ThetaDigitAverage.Residue p.val), f t) =
          ∑ v : (ThetaDigitAverage.Residue p.val)ˣ, f v := by
      calc
        _ = ∑ t : ThetaDigitAverage.Residue p.val, f t := by
          rw [← Finset.sum_erase_add _ _
            (Finset.mem_univ (0 : ThetaDigitAverage.Residue p.val)), hfzero, add_zero]
        _ = _ := (HeckeSkeleton.ThetaLocal.ResidueField.sum_units_eq_sum f hfzero).symm
    have hu : u ≠ 0 := ThetaBranch.unitResidue_ne_zero p.val
      (ThetaBranch.localUnit R.A R.probe.allowed p x)
      (ThetaBranch.localUnit_order R.A R.probe.allowed p x)
    let U : (ThetaDigitAverage.Residue p.val)ˣ := Units.mk0 u hu
    rw [if_neg hneg]
    change _ = localWeylScalar F Sf Adata (prime R.A p) j n *
      χ u ^ localWeylExponent j n
    calc
      _ = sphericalDigit F Sf Adata (prime R.A p) n * χ u ^ (4 + 2 * n) *
          ∑ t ∈ Finset.univ.erase (0 : ThetaDigitAverage.Residue p.val), f t := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        rw [hterm t ht]
        dsimp only [f]
        ring
      _ = sphericalDigit F Sf Adata (prime R.A p) n * χ u ^ (4 + 2 * n) *
          ∑ v : (ThetaDigitAverage.Residue p.val)ˣ, f v := by rw [hsum]
      _ = _ := localWeyl_phase_separation F Sf Adata (prime R.A p) j n U

end ThetaGlobal.LocalDigitAverage

#print axioms ThetaGlobal.LocalDigitAverage.nonzero_digits
