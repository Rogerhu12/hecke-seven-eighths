import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceOrientation
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceReductionOverlap
import HeckeSkeleton.Moments.MOM_BASE.PairedPhases

/-!
# One live character for the actual inverse and its prime slots

After the exact inverse-only conjugation, the inverse has positive moving
orientation.  Each original slot is rewritten with the same live character
`inverseBackground * rowCharacter`, and with its own row-independent relative
coefficient.  The background and slot need only be unramified at the original
retained primes.  No ramification zero of the moving row is cancelled.

The ideal coefficient identity is proved from the actual finite prime
factorization.  These identities supply the literal common character needed
by the squarefree gcd extraction in `SourceReductionOverlap`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.Analysis.ConditionalMoments
open HeckeSkeleton.Moments.MOM_BASE.Paired
open scoped Classical BigOperators nonZeroDivisors

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

/-- The fixed relative coefficient does not depend on the moving row. -/
def inverseRelativeSlotCoefficient (d : MomentData K ω ψ)
    (i : Fin d.geometry.slotCount) (p : HeightOneSpectrum (𝓞 K)) : ℂ :=
  (primeCoefficient K d.inverseBackground p)⁻¹ *
    primeCoefficient K (d.slotCoefficient i) p

theorem inverseRelativeSlotCoefficient_norm_le_one
    (d : MomentData K ω ψ) (i : Fin d.geometry.slotCount)
    (p : HeightOneSpectrum (𝓞 K)) (hν : UnramifiedAt K d.inverseBackground p) :
    ‖inverseRelativeSlotCoefficient d i p‖ ≤ 1 := by
  rw [inverseRelativeSlotCoefficient, norm_mul, norm_inv,
    norm_primeCoefficient_of_unramified K d.inverseBackground p hν, inv_one, one_mul]
  exact norm_primeCoefficient_le_one K (d.slotCoefficient i) p

/-- The slot with the common live background written explicitly. -/
def sourceRelativeSlotTerm (d : MomentData K ω ψ) (u : NonzeroIdeal K)
    (Z t : ℝ) (i : Fin d.geometry.slotCount) (p : HeightOneSpectrum (𝓞 K)) : ℂ :=
  (Real.sqrt (Z ^ (d.geometry.slots i).length) : ℂ)⁻¹ *
    (primeCoefficient K (d.inverseBackground * d.rowCharacter u) p *
      inverseRelativeSlotCoefficient d i p *
      (d.geometry.slots i).profile t
        ((p.asIdeal.absNorm : ℝ) / Z ^ (d.geometry.slots i).length) *
      maskValue d u p.asIdeal)

/-- This is an identity on the original masked summand, even if the
moving row ramifies at the prime. -/
theorem sourceRelativeSlotTerm_eq (d : MomentData K ω ψ) (u : NonzeroIdeal K)
    (Z t : ℝ) (i : Fin d.geometry.slotCount) (p : HeightOneSpectrum (𝓞 K))
    (hν : d.commonMask u p.asIdeal = true → UnramifiedAt K d.inverseBackground p)
    (hθ : d.commonMask u p.asIdeal = true → UnramifiedAt K (d.slotCoefficient i) p) :
    sourceRelativeSlotTerm d u Z t i p = sourceSlotTerm d u Z t i p := by
  cases hm : d.commonMask u p.asIdeal with
  | false => simp [sourceRelativeSlotTerm, sourceSlotTerm, maskValue, hm]
  | true =>
    unfold sourceRelativeSlotTerm sourceSlotTerm inverseRelativeSlotCoefficient
    rw [paired_primeCoefficient_unramified_slot K d.inverseBackground
      (d.rowCharacter u) (d.slotCoefficient i) p (hν hm) (hθ hm)]

/-- Multiplication by a background unramified at the actual prime
divisors preserves every zero of the moving ideal coefficient. -/
theorem source_idealCoefficient_mul_unramified
    (ν χ : HeckeCharacter K) (I : NonzeroIdeal K)
    (hν : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val → UnramifiedAt K ν p) :
    heckeIdealCoefficient K (ν * χ) I =
      heckeIdealCoefficient K ν I * heckeIdealCoefficient K χ I := by
  rw [mul_comm ν χ, idealCoefficient_character_mul K χ ν I hν, mul_comm]

/-- The positive-oriented original inverse term with its exact
normalization, Mobius coefficient, profile and complete common mask. -/
theorem sourceInverseTerm_eq_live (d : MomentData K ω ψ)
    (u n : NonzeroIdeal K) (D t : ℝ) (hdir : d.direction = 1)
    (hν : d.commonMask u n.val = true →
      ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ n.val →
        UnramifiedAt K d.inverseBackground p) :
    sourceInverseTerm d u D t n =
      (Real.sqrt D : ℂ)⁻¹ *
        ((moebius n.val : ℂ) *
          heckeIdealCoefficient K (d.inverseBackground * d.rowCharacter u) n *
          d.inverseTest.profile u t (idealNorm K n / D) * maskValue d u n.val) := by
  cases hm : d.commonMask u n.val with
  | false => simp [sourceInverseTerm, maskValue, hm]
  | true =>
    rw [sourceInverseTerm, hdir, zpow_one,
      source_idealCoefficient_mul_unramified d.inverseBackground (d.rowCharacter u) n
        (hν hm)]
    ring

/-- All original prime windows can be expanded with the same live
character as the inverse column.  The relative coefficients remain
row-independent and the row masks remain inside their own terms. -/
theorem slotProduct_eq_relative_tuples (d : MomentData K ω ψ)
    (u : NonzeroIdeal K) (Z t : ℝ)
    (hν : ∀ i p, p ∈ (d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length) →
      d.commonMask u p.asIdeal = true → UnramifiedAt K d.inverseBackground p)
    (hθ : ∀ i p, p ∈ (d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length) →
      d.commonMask u p.asIdeal = true → UnramifiedAt K (d.slotCoefficient i) p) :
    slotProduct d u Z t = ∑ p ∈ sourceSlotTuples d Z t,
      ∏ i, sourceRelativeSlotTerm d u Z t i (p i) := by
  rw [slotProduct_eq_sourceSlotTuples]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.prod_congr rfl
  intro i _
  have hpi := Fintype.mem_piFinset.mp hp i
  exact (sourceRelativeSlotTerm_eq d u Z t i (p i) (hν i (p i) hpi)
    (hθ i (p i) hpi)).symm

end HeckeSkeleton.Moments.MOM_INV_INDUCTION

end
