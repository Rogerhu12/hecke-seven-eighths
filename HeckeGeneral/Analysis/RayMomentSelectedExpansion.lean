import HeckeGeneral.Analysis.RayMomentPolynomialExpansion

/-!
Exact finite expansion of ray-filtered slot products. Every slot chooses
its own cyclic twist label; a single common twist would not give the
product of the individual averages. Repeated resulting characters are
retained as labels. The original common mask and ramified row zeros remain.

This is finite algebra, including empty slot and empty ray families. No
energy estimate, moment admissibility or detector existence is asserted.
-/

noncomputable section

namespace HeckeGeneral.Analysis.ConditionalMoments

open NumberField IsDedekindDomain HeckeGeneral.Characters
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

/-- Each slot receives an independent, row-independent actual character. -/
abbrev MomentData.twistEachSlotCoefficients (d : MomentData K ω ψ)
    (θ : Fin d.geometry.slotCount → HeckeCharacter K) : MomentData K ω ψ :=
  { d with slotCoefficient := fun i => d.slotCoefficient i * θ i }

@[simp] theorem inversePolynomial_twistEachSlotCoefficients
    (d : MomentData K ω ψ) (θ : Fin d.geometry.slotCount → HeckeCharacter K)
    (u : NonzeroIdeal K) (D t : ℝ) :
    inversePolynomial (d.twistEachSlotCoefficients θ) u D t =
      inversePolynomial d u D t := rfl

@[simp] theorem plainPolynomial_twistEachSlotCoefficients
    (d : MomentData K ω ψ) (θ : Fin d.geometry.slotCount → HeckeCharacter K)
    (W : IdealTest K) (u : NonzeroIdeal K) (N t : ℝ) :
    plainPolynomial (d.twistEachSlotCoefficients θ) W u N t =
      plainPolynomial d W u N t := rfl

@[simp] theorem pairedRows_twistEachSlotCoefficients
    (d : MomentData K ω ψ) (θ : Fin d.geometry.slotCount → HeckeCharacter K)
    (a : RealParameters) (Z : ℝ) :
    pairedRows (d.twistEachSlotCoefficients θ) a Z = pairedRows d a Z := rfl

@[simp] theorem rows_twistEachSlotCoefficients
    (d : MomentData K ω ψ) (θ : Fin d.geometry.slotCount → HeckeCharacter K) :
    (d.twistEachSlotCoefficients θ).rows = d.rows := rfl

@[simp] theorem commonMask_twistEachSlotCoefficients
    (d : MomentData K ω ψ) (θ : Fin d.geometry.slotCount → HeckeCharacter K) :
    (d.twistEachSlotCoefficients θ).commonMask = d.commonMask := rfl

/-- A single slot only sees its own chosen twist. -/
theorem primePolynomial_twistEachSlotCoefficients
    (d : MomentData K ω ψ) (θ : Fin d.geometry.slotCount → HeckeCharacter K)
    (i : Fin d.geometry.slotCount) (u : NonzeroIdeal K) (Z t : ℝ) :
    primePolynomial (d.twistEachSlotCoefficients θ) i u Z t =
      primePolynomial (d.twistSlotCoefficients (θ i)) i u Z t := rfl

end HeckeGeneral.Analysis.ConditionalMoments

namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

/-- The denominator is a product over slots, so it is 1 when there are
no slots. No division by a polynomial or by a local Euler factor occurs. -/
theorem rayMaskedSlotProduct_eq_independent_average
    (d : MomentData K ω ψ) (T : Finset (HeckeCharacter K))
    (n : T → ℕ) (hn : ∀ χ, 0 < n χ) (ho : ∀ χ : T, χ.val ^ n χ = 1)
    (u : NonzeroIdeal K) (Z t : ℝ)
    (hU : ∀ i : Fin d.geometry.slotCount,
      ∀ p ∈ (d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length),
        ∀ χ ∈ T, UnramifiedAt K χ p) :
    (∏ i : Fin d.geometry.slotCount, rayMaskedPrimePolynomial K d T i u Z t) =
      (∑ e : Fin d.geometry.slotCount → ((χ : T) → Fin (n χ)),
        slotProduct
          (d.twistEachSlotCoefficients
            (fun i => cyclicRayTwist K (fun χ : T => χ.val) n (e i))) u Z t) /
        (∏ _i : Fin d.geometry.slotCount, ∏ χ : T, (n χ : ℂ)) := by
  calc
    _ = (∏ i : Fin d.geometry.slotCount,
          ∑ e : (χ : T) → Fin (n χ),
            primePolynomial (d.twistSlotCoefficients
              (cyclicRayTwist K (fun χ : T => χ.val) n e)) i u Z t) /
          (∏ _i : Fin d.geometry.slotCount, ∏ χ : T, (n χ : ℂ)) := by
      rw [← Finset.prod_div_distrib]
      apply Finset.prod_congr rfl
      intro i _hi
      exact rayMaskedPrimePolynomial_eq_average K d T n hn ho i u Z t (hU i)
    _ = (∑ e : Fin d.geometry.slotCount → ((χ : T) → Fin (n χ)),
          ∏ i : Fin d.geometry.slotCount,
            primePolynomial (d.twistSlotCoefficients
              (cyclicRayTwist K (fun χ : T => χ.val) n (e i))) i u Z t) /
          (∏ _i : Fin d.geometry.slotCount, ∏ χ : T, (n χ : ℂ)) := by
      rw [Fintype.prod_sum]
    _ = _ := by
      congr 1

/-- Only selected slots require unramified filtering characters. The
independent labels are indexed by Fin J.card, exactly as restrictSlots. -/
theorem rayMaskedSelectedSlotProduct_eq_independent_average
    (d : MomentData K ω ψ) (J : Finset (Fin d.geometry.slotCount))
    (T : Finset (HeckeCharacter K))
    (n : T → ℕ) (hn : ∀ χ, 0 < n χ) (ho : ∀ χ : T, χ.val ^ n χ = 1)
    (u : NonzeroIdeal K) (Z t : ℝ)
    (hU : ∀ i ∈ J,
      ∀ p ∈ (d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length),
        ∀ χ ∈ T, UnramifiedAt K χ p) :
    (∏ i ∈ J, rayMaskedPrimePolynomial K d T i u Z t) =
      (∑ e : Fin J.card → ((χ : T) → Fin (n χ)),
        slotProduct
          ((d.restrictSlots J).twistEachSlotCoefficients
            (fun j => cyclicRayTwist K (fun χ : T => χ.val) n (e j))) u Z t) /
        (∏ _j : Fin J.card, ∏ χ : T, (n χ : ℂ)) := by
  calc
    _ = ∏ j : Fin J.card,
        rayMaskedPrimePolynomial K (d.restrictSlots J) T j u Z t := by
      change (∏ i ∈ J, rayMaskedPrimePolynomial K d T i u Z t) =
        ∏ j : Fin J.card, rayMaskedPrimePolynomial K d T (selectedSlotIndex J j) u Z t
      exact (selectedSlots_prod J (fun i => rayMaskedPrimePolynomial K d T i u Z t)).symm
    _ = _ := rayMaskedSlotProduct_eq_independent_average K (d.restrictSlots J)
      T n hn ho u Z t (fun j => hU _ (selectedSlotIndex_mem J j))

/-- Literal actual-orbit sextic values, with every original zero mask.
This specializes the algebraic product identity without a Hecke extension
of an arbitrary polynomial or any detector-witness assumption. -/
theorem actualDecomposedSelectedRayProduct_eq_independent_average
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (P : ProbeData K S) (R : RowCharacterInput K S P)
    (ω η : HeckeCharacter K) (ξ : SixthUnitClasses K S) (V : IdealTest K)
    (g : SlotGeometry K) (J : Finset (Fin g.slotCount))
    (T : Finset (HeckeCharacter K))
    (n : T → ℕ) (hn : ∀ χ, 0 < n χ) (ho : ∀ χ : T, χ.val ^ n χ = 1)
    (I : ExteriorIdeal K S) (Z t : ℝ)
    (hU : ∀ i ∈ J, ∀ p ∈ (g.slots i).support t (Z ^ (g.slots i).length),
      ∀ χ ∈ T, UnramifiedAt K χ p) :
    (∏ i ∈ J, actualDecomposedPrimePolynomial K S P ξ g T i I Z t) =
      (∑ e : Fin J.card → ((χ : T) → Fin (n χ)),
        slotProduct
          (((decomposedMomentDataWithSlots K S P R ω η ξ V g).restrictSlots J).twistEachSlotCoefficients
              (fun j => cyclicRayTwist K (fun χ : T => χ.val) n (e j))) I.val Z t) /
        (∏ _j : Fin J.card, ∏ χ : T, (n χ : ℂ)) := by
  calc
    _ = ∏ i ∈ J,
        rayMaskedPrimePolynomial K (decomposedMomentDataWithSlots K S P R ω η ξ V g)
          T i I.val Z t := by
      apply Finset.prod_congr rfl
      intro i _hi
      exact (rayMaskedPrimePolynomial_decomposed K S P R ω η ξ V g T i I Z t).symm
    _ = _ := rayMaskedSelectedSlotProduct_eq_independent_average K
      (decomposedMomentDataWithSlots K S P R ω η ξ V g) J T n hn ho I.val Z t hU

end HeckeGeneral.ThetaSkeleton.Physical
