import HeckeGeneral.Characters.FiniteRayCoefficientExpansion
import HeckeGeneral.Analysis.MomentPrimeWindowUnramified
import HeckeGeneral.Analysis.ActualMomentPolynomialBridges

/-!
Finite ray filtering on the actual prime polynomials is a finite average
of genuine fixed-character twists of the slot coefficients. The inverse
and plain polynomials, common masks and row enumeration are unchanged.
For the actual pretarget windows, the unramified premise is proved above
a threshold depending on the fixed finite ray family. The identity is
uniform in the row and height. No moment estimate or admissibility
instance is asserted for the resulting twisted families.
-/

noncomputable section

namespace HeckeGeneral.Analysis.ConditionalMoments

open NumberField IsDedekindDomain HeckeGeneral.Characters
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

/-- A genuine row-independent Hecke character twist of all slot coefficients. -/
abbrev MomentData.twistSlotCoefficients (d : MomentData K ω ψ) (θ : HeckeCharacter K) :
    MomentData K ω ψ :=
  { d with slotCoefficient := fun i => d.slotCoefficient i * θ }

@[simp] theorem inversePolynomial_twistSlotCoefficients
    (d : MomentData K ω ψ) (θ : HeckeCharacter K) (u : NonzeroIdeal K) (D t : ℝ) :
    inversePolynomial (d.twistSlotCoefficients θ) u D t = inversePolynomial d u D t := rfl

@[simp] theorem plainPolynomial_twistSlotCoefficients
    (d : MomentData K ω ψ) (θ : HeckeCharacter K) (W : IdealTest K)
    (u : NonzeroIdeal K) (N t : ℝ) :
    plainPolynomial (d.twistSlotCoefficients θ) W u N t = plainPolynomial d W u N t := rfl

@[simp] theorem pairedRows_twistSlotCoefficients
    (d : MomentData K ω ψ) (θ : HeckeCharacter K) (a : RealParameters) (Z : ℝ) :
    pairedRows (d.twistSlotCoefficients θ) a Z = pairedRows d a Z := rfl

end HeckeGeneral.Analysis.ConditionalMoments

namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain Set
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

/-- The finite averaging identity keeps every original summand and mask.
Ramification of the row character is allowed. Only the fixed ray characters
must be unramified on the actual support used by this polynomial. -/
theorem rayMaskedPrimePolynomial_eq_average
    (d : MomentData K ω ψ) (T : Finset (HeckeCharacter K))
    (n : T → ℕ) (hn : ∀ χ, 0 < n χ) (ho : ∀ χ : T, χ.val ^ n χ = 1)
    (i : Fin d.geometry.slotCount) (u : NonzeroIdeal K) (Z t : ℝ)
    (hU : ∀ p ∈ (d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length),
      ∀ χ ∈ T, UnramifiedAt K χ p) :
    rayMaskedPrimePolynomial K d T i u Z t =
      (∑ e : (χ : T) → Fin (n χ),
        primePolynomial (d.twistSlotCoefficients
          (cyclicRayTwist K (fun χ : T => χ.val) n e)) i u Z t) /
        (∏ χ : T, (n χ : ℂ)) := by
  let X := Z ^ (d.geometry.slots i).length
  let c : ℂ := (Real.sqrt X : ℂ)⁻¹
  let a := fun (e : (χ : T) → Fin (n χ)) (p : HeightOneSpectrum (𝓞 K)) =>
    primeCoefficient K ((d.rowCharacter u * d.slotCoefficient i) *
      cyclicRayTwist K (fun χ : T => χ.val) n e) p
  let b := fun p : HeightOneSpectrum (𝓞 K) =>
    (d.geometry.slots i).profile t ((p.asIdeal.absNorm : ℝ) / X)
  let m := fun p : HeightOneSpectrum (𝓞 K) => maskValue d u p.asIdeal
  let D : ℂ := ∏ χ : T, (n χ : ℂ)
  have ha (p : HeightOneSpectrum (𝓞 K))
      (hp : p ∈ (d.geometry.slots i).support t X) :
      (∑ e, a e p) / D =
        primeCoefficient K (d.rowCharacter u * d.slotCoefficient i) p *
          fixedRayPrimeIndicator K T p := by
    have h := finiteRayCoefficientExpansion K (fun χ : T => χ.val) n hn ho
      (d.rowCharacter u * d.slotCoefficient i) p (fun χ => hU p hp χ.val χ.property)
    simpa only [a, D, fixedRayPrimeIndicator, Subtype.forall] using h
  change c * ∑ p ∈ (d.geometry.slots i).support t X,
    primeCoefficient K (d.rowCharacter u * d.slotCoefficient i) p * b p * m p *
      fixedRayPrimeIndicator K T p = _
  calc
    _ = c * ∑ p ∈ (d.geometry.slots i).support t X,
        ((∑ e, a e p) / D) * b p * m p := by
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      rw [ha p hp]
      ring
    _ = (∑ e, c * ∑ p ∈ (d.geometry.slots i).support t X,
        a e p * b p * m p) / D := by
      conv_rhs => rw [← Finset.mul_sum, Finset.sum_comm, mul_div_assoc, Finset.sum_div]
      congr 1
      apply Finset.sum_congr rfl
      intro p _hp
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      ring
    _ = _ := by
      simp only [primePolynomial, MomentData.twistSlotCoefficients,
        maskValue, a, b, m, c, X, D, mul_assoc]

/-- All choices in the finite expansion and the scale threshold are made
before the arbitrary scale, row and height. Each twisting character has
finite order because the fixed ray characters do. -/
theorem exists_actualPrimeRayExpansion
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (P : ProbeData K S) (R : RowCharacterInput K S P)
    (ω η : HeckeCharacter K) (ξ : SixthUnitClasses K S) (V : IdealTest K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (hT : ∀ χ ∈ T, FiniteOrder χ) :
    ∃ n : T → ℕ, (∀ χ, 0 < n χ) ∧ (∀ χ : T, χ.val ^ n χ = 1) ∧
      (∀ e : (χ : T) → Fin (n χ),
        FiniteOrder (cyclicRayTwist K (fun χ : T => χ.val) n e)) ∧
      ∃ Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
        ∀ (i : Fin g.slots) (I : ExteriorIdeal K S) (t : ℝ),
          actualDecomposedPrimePolynomial K S P ξ (momentPrimeGeometry K g) T i I Z t =
            (∑ e : (χ : T) → Fin (n χ),
              primePolynomial
                ((decomposedMomentDataWithSlots K S P R ω η ξ V
                  (momentPrimeGeometry K g)).twistSlotCoefficients
                    (cyclicRayTwist K (fun χ : T => χ.val) n e)) i I.val Z t) /
                  (∏ χ : T, (n χ : ℂ)) := by
  have hord : ∀ χ : T, ∃ n : ℕ, 0 < n ∧ χ.val ^ n = 1 :=
    fun χ => (finiteOrder_iff χ.val).mp (hT χ.val χ.property)
  choose n hn ho using hord
  obtain ⟨Z₀, hZ₀, hU⟩ := exists_analyticMomentPrimeWindows_unramified K g T
  refine ⟨n, hn, ho, ?_, Z₀, hZ₀, ?_⟩
  · intro e
    exact cyclicRayTwist_finiteOrder K (fun χ : T => χ.val) n e
      (fun χ => hT χ.val χ.property)
  · intro Z hZ i I t
    exact (rayMaskedPrimePolynomial_decomposed K S P R ω η ξ V
      (momentPrimeGeometry K g) T i I Z t).symm.trans
        (rayMaskedPrimePolynomial_eq_average K
          (decomposedMomentDataWithSlots K S P R ω η ξ V (momentPrimeGeometry K g))
          T n hn ho i I.val Z t (fun p hp χ hχ => hU Z hZ i t p hp χ hχ))

end HeckeGeneral.ThetaSkeleton.Physical
