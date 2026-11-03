import ThetaGlobal.GlobalProjectSignedExtraction
import ThetaGlobal.GlobalProjectLiteralDigitWeights
import DedekindZetaZeroFree.Theta.Digits.SphericalValueBounds
import DedekindZetaZeroFree.Theta.Digits.RationalMaskFrequencies
import DedekindZetaZeroFree.Theta.Digits.Exterior.FiniteRowProducts

/-!
# Independent local digit products for the literal marked average

The global finite digit sum is a product of actual one-place sums.  The
proof uses the exact chosen residue lifts and the exact canonical local
representation.  The unaveraged exterior places retain their spherical
reference factors.  The local digit-table boundary is therefore a
finite sum at one finite place, not a global theta identity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section

namespace ThetaGlobal.GlobalProjectDigitProduct

open NumberField MeasureTheory DedekindZetaZeroFree DedekindZetaZeroFree.MomentSources
open DedekindZetaZeroFree.OrbitExpansion
open DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits
open ThetaGlobal.GlobalProjectSignedExtraction
open scoped NumberField Classical BigOperators

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)
  {Q : AdmissibleFlatSources R} {T : Realization R Q}
  (D : SourceFactorization R Q T)

def localDigit (p : ThetaBranch.ExteriorPrime R.A) (x : Fˣ) (t : 𝓞 F) : ℂ :=
  exteriorSlotValue R D p.val
    (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
      (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x) *
      KPStandardLocalRootLifts.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) *
      KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
        (-algebraMap (𝓞 F) (p.val.adicCompletion F) t /
          algebraMap F (p.val.adicCompletion F)
            (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p) : F)))

theorem at_row (m : ThetaReflectionData.Row R.A) (x : Fˣ)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property))
    (p : RowPrime R m) :
    OrbitFrequencies.exteriorDigitValue R D m x d (exteriorRowPrime R m p) =
      localDigit R D (exteriorRowPrime R m p) x
        ((ThetaDigitAverage.residueLifts _).lift p (d p)) := by
  rw [OrbitFrequencies.exteriorDigitValue_eq_slot,
    DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits.parameter_at_row R m d p]
  rfl

def offRowProduct (m : ThetaReflectionData.Row R.A) (x : Fˣ) : ℂ :=
  ∏ᶠ p : ThetaBranch.ExteriorPrime R.A,
    if p ∈ exteriorRows R m then 1 else D.exteriorValue R p x

theorem reverseCoefficient_product (m : ThetaReflectionData.Row R.A) (x : Fˣ)
    (w : (p : RowPrime R m) → ThetaDigitAverage.Residue p.val → ℂ) :
    reverseCoefficient R D m (fun d => ∏ p, w p (d p)) x =
      (∏ p : RowPrime R m, ∑ t : ThetaDigitAverage.Residue p.val,
        w p t * localDigit R D (exteriorRowPrime R m p) x
          ((ThetaDigitAverage.residueLifts _).lift p t)) *
        offRowProduct R D m x := by
  have hs (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) :
      (∏ᶠ p : ThetaBranch.ExteriorPrime R.A,
        OrbitFrequencies.exteriorDigitValue R D m x d p) =
      (∏ p : RowPrime R m, localDigit R D (exteriorRowPrime R m p) x
        ((ThetaDigitAverage.residueLifts _).lift p (d p))) * offRowProduct R D m x := by
    rw [split_product (exteriorRows R m) _
      (OrbitFrequencies.digitExterior_finite R D m x d), prod_exteriorRows]
    congr 1
    · apply Finset.prod_congr rfl
      intro p _
      exact at_row R D m x d p
    · apply finprod_congr
      intro p
      by_cases hp : p ∈ exteriorRows R m
      · simp [hp]
      · rw [if_neg hp, if_neg hp]
        exact OrbitFrequencies.exteriorDigitValue_off_row R D m x d p
          (fun h => hp ((mem_exteriorRows R m p).mpr h))
  unfold reverseCoefficient
  simp_rw [hs, ← mul_assoc]
  rw [← Finset.sum_mul]
  congr 1
  simp only [← Finset.prod_mul_distrib]
  rw [Fintype.prod_sum]
  all_goals first
  | rfl
  | (congr 1; done)
  | (congr 1 <;> first | rfl | exact congrArg (fun I => @Finset.univ _ I) (Subsingleton.elim _ _))

theorem offRowProduct_spherical (E : ExteriorCoefficients R Q T D)
    (m : ThetaReflectionData.Row R.A) (x : Fˣ) :
    offRowProduct R D m x =
      ∏ᶠ p : ThetaBranch.ExteriorPrime R.A, if p ∈ exteriorRows R m then 1 else
        ThetaBranch.sphericalFactor R.A R.probe.allowed R.σ (Characters.psi R) p x := by
  apply finprod_congr
  intro p
  simp only [E.rational_exact]

def forwardCoefficient (m : ThetaReflectionData.Row R.A)
    (c : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property) → ℂ)
    (x : Fˣ) : ℂ :=
  ∑ d, c d * (adelicTraceCharacter F
    (algebraMap F (KPAdeles F) (x : F) * digitParameter R m d) : ℂ)

theorem forwardCoefficient_product (m : ThetaReflectionData.Row R.A) (x : Fˣ)
    (hx : ∀ p ∈ ThetaDigitAverage.rowPrimes R.A m.val m.property,
      p.valuation F (x : F) ≤ 1)
    (w : (p : RowPrime R m) → ThetaDigitAverage.Residue p.val → ℂ) :
    forwardCoefficient R m (fun d => ∏ p, w p (d p)) x =
      ∏ p : RowPrime R m, ∑ t : ThetaDigitAverage.Residue p.val,
        w p t * Characters.psi R (exteriorRowPrime R m p)
          (ThetaBranch.unitResidue p.val x * t) := by
  unfold forwardCoefficient
  simp_rw [DigitMasks.digitParameter_rational_phase R m x hx]
  simp only [← Finset.prod_mul_distrib]
  rw [Fintype.prod_sum]
  all_goals first
  | rfl
  | (congr 1; done)
  | (congr 1 <;> first | rfl | exact congrArg (fun I => @Finset.univ _ I) (Subsingleton.elim _ _))

end ThetaGlobal.GlobalProjectDigitProduct
