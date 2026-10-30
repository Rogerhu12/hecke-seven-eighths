import HeckeGeneral.Analysis.SelectedMomentSlots
import HeckeGeneral.Analysis.DecomposedZeroSlotMomentData
import HeckeGeneral.Analysis.MomentPrimeWindows

/-! Literal finite-sum bridges for a complete ideal and a fixed unit sector.
The Hecke row identification still explicitly consumes RowCharacterInput.
All original fixed-S/6 and complete-ideal coprimality zeros remain. The ray
indicator below is NOT removed or declared to be an admissible coefficient.
There is no plain exceptional-row exclusion or moment inequality here. -/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (R : RowCharacterInput K S P)

/-- The actual plain finite sum, at the same complete ideal, sector, test
and scale as the moment polynomial. The actual evaluation is zero-extended. -/
def actualDecomposedPlainPolynomial (ξ : SixthUnitClasses K S) (W : IdealTest K)
    (I : ExteriorIdeal K S) (N t : ℝ) : ℂ :=
  (Real.sqrt N : ℂ)⁻¹ * ∑ J ∈ W.support I.val t N,
    actualOrbitSexticEvaluation K S P.arithmetic.root6 P.arithmetic.primitive6
      P.arithmetic.embedding J (decomposedIdealSectorOrbit K S P (I, ξ)) *
        W.profile I.val t (idealNorm K J / N)

theorem plainPolynomial_decomposedZeroSlotMomentData
    (ω η : HeckeCharacter K) (ξ : SixthUnitClasses K S)
    (V W : IdealTest K) (I : ExteriorIdeal K S) (N t : ℝ) :
    plainPolynomial (decomposedZeroSlotMomentData K S P R ω η ξ V) W I.val N t =
      actualDecomposedPlainPolynomial K S P ξ W I N t := by
  unfold plainPolynomial actualDecomposedPlainPolynomial
  congr 1
  apply Finset.sum_congr rfl
  intro J _hJ
  rw [actualOrbitSexticEvaluation_decomposed_character K S P R,
    decomposedZeroSlotMomentData_mask]
  change heckeIdealCoefficient K (1 * completeIdealRowCharacter K S P R ξ I.val) J *
      W.profile I.val t (idealNorm K J / N) * decomposedIdealRowMask K S I J = _
  rw [one_mul, completeIdealRowCharacter_exterior K S P R]
  ring

/-- Adding literal analytic slots leaves the inverse/plain tests and common
mask unchanged. Ray filtering is kept separately in the finite sum below. -/
abbrev decomposedMomentDataWithSlots (ω η : HeckeCharacter K)
    (ξ : SixthUnitClasses K S) (W : IdealTest K) (g : SlotGeometry K) :
    MomentData K ω η :=
  { decomposedZeroSlotMomentData K S P R ω η ξ W with
    geometry := g
    slotCoefficient := fun _ => 1 }

theorem inversePolynomial_decomposedMomentDataWithSlots
    (ω η : HeckeCharacter K) (ξ : SixthUnitClasses K S) (W : IdealTest K)
    (g : SlotGeometry K) (I : ExteriorIdeal K S) (D t : ℝ) :
    inversePolynomial (decomposedMomentDataWithSlots K S P R ω η ξ W g) I.val D t =
      sIntegerSexticInverseIdealPolynomial K S P.arithmetic.root6
        P.arithmetic.primitive6 P.arithmetic.embedding η (W.support I.val t D)
        (decomposedIdealSectorOrbit K S P (I, ξ)).out.val D (W.profile I.val t) :=
  inversePolynomial_decomposedZeroSlotMomentData K S P R ω η ξ W I D t

theorem plainPolynomial_decomposedMomentDataWithSlots
    (ω η : HeckeCharacter K) (ξ : SixthUnitClasses K S) (V W : IdealTest K)
    (g : SlotGeometry K) (I : ExteriorIdeal K S) (N t : ℝ) :
    plainPolynomial (decomposedMomentDataWithSlots K S P R ω η ξ V g) W I.val N t =
      actualDecomposedPlainPolynomial K S P ξ W I N t :=
  plainPolynomial_decomposedZeroSlotMomentData K S P R ω η ξ V W I N t

def momentPrimeIdeal (p : HeightOneSpectrum (𝓞 K)) : NonzeroIdeal K :=
  ⟨p.asIdeal, mem_nonZeroDivisors_of_ne_zero p.ne_bot⟩

/-- The fixed identity-ray condition is literal, including possible
ramification zeros of the filtering characters. -/
def fixedRayPrimeIndicator (T : Finset (HeckeCharacter K))
    (p : HeightOneSpectrum (𝓞 K)) : ℂ :=
  if ∀ χ ∈ T, primeCoefficient K χ p = 1 then 1 else 0

/-- A moment prime finite sum with the fixed ray indicator retained.
This definition makes no finite-character expansion or admissibility claim. -/
def rayMaskedPrimePolynomial {ω ψ : HeckeCharacter K} (d : MomentData K ω ψ)
    (T : Finset (HeckeCharacter K)) (i : Fin d.geometry.slotCount)
    (u : NonzeroIdeal K) (Z t : ℝ) : ℂ :=
  let X := Z ^ (d.geometry.slots i).length
  (Real.sqrt X : ℂ)⁻¹ * ∑ p ∈ (d.geometry.slots i).support t X,
    primeCoefficient K (d.rowCharacter u * d.slotCoefficient i) p *
      (d.geometry.slots i).profile t ((p.asIdeal.absNorm : ℝ) / X) *
      maskValue d u p.asIdeal * fixedRayPrimeIndicator K T p

def actualDecomposedPrimePolynomial (ξ : SixthUnitClasses K S)
    (g : SlotGeometry K) (T : Finset (HeckeCharacter K)) (i : Fin g.slotCount)
    (I : ExteriorIdeal K S) (Z t : ℝ) : ℂ :=
  let X := Z ^ (g.slots i).length
  (Real.sqrt X : ℂ)⁻¹ * ∑ p ∈ (g.slots i).support t X,
    actualOrbitSexticEvaluation K S P.arithmetic.root6 P.arithmetic.primitive6
      P.arithmetic.embedding (momentPrimeIdeal K p)
      (decomposedIdealSectorOrbit K S P (I, ξ)) *
        (g.slots i).profile t ((p.asIdeal.absNorm : ℝ) / X) *
        fixedRayPrimeIndicator K T p

theorem rayMaskedPrimePolynomial_decomposed
    (ω η : HeckeCharacter K) (ξ : SixthUnitClasses K S) (W : IdealTest K)
    (g : SlotGeometry K) (T : Finset (HeckeCharacter K)) (i : Fin g.slotCount)
    (I : ExteriorIdeal K S) (Z t : ℝ) :
    rayMaskedPrimePolynomial K (decomposedMomentDataWithSlots K S P R ω η ξ W g)
      T i I.val Z t = actualDecomposedPrimePolynomial K S P ξ g T i I Z t := by
  unfold rayMaskedPrimePolynomial actualDecomposedPrimePolynomial
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro p _hp
  rw [actualOrbitSexticEvaluation_decomposed_character K S P R]
  have hmask :
      maskValue (decomposedMomentDataWithSlots K S P R ω η ξ W g) I.val p.asIdeal =
        decomposedIdealRowMask K S I (momentPrimeIdeal K p) :=
    decomposedZeroSlotMomentData_mask K S P R ω η ξ W I (momentPrimeIdeal K p)
  rw [hmask]
  change primeCoefficient K (completeIdealRowCharacter K S P R ξ I.val * 1) p *
      (g.slots i).profile t ((p.asIdeal.absNorm : ℝ) / Z ^ (g.slots i).length) *
      decomposedIdealRowMask K S I (momentPrimeIdeal K p) * fixedRayPrimeIndicator K T p = _
  rw [mul_one, completeIdealRowCharacter_exterior K S P R]
  simp only [heckeIdealCoefficient, nonzeroIdealCoefficient, momentPrimeIdeal,
    idealCoefficient_prime]
  ring

/-- Specialization to the literal pretarget physical annuli. The support
is the analytic support before masks; the actual evaluation deletes S/6
and row zeros, and the ray indicator is still displayed in every summand. -/
theorem rayMaskedPhysicalPrimePolynomial_decomposed
    (ω η : HeckeCharacter K) (ξ : SixthUnitClasses K S) (W : IdealTest K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (i : Fin g.slots) (I : ExteriorIdeal K S) (Z : ℝ) :
    rayMaskedPrimePolynomial K
      (decomposedMomentDataWithSlots K S P R ω η ξ W (momentPrimeGeometry K g))
      T i I.val Z 0 =
      (Real.sqrt (primeScale g Z) : ℂ)⁻¹ *
        ∑ p ∈ analyticPrimeSupport K (g.weight i).toFun (primeScale g Z),
          actualOrbitSexticEvaluation K S P.arithmetic.root6 P.arithmetic.primitive6
            P.arithmetic.embedding (momentPrimeIdeal K p)
            (decomposedIdealSectorOrbit K S P (I, ξ)) *
              (g.weight i).toFun ((p.asIdeal.absNorm : ℝ) / primeScale g Z) *
              fixedRayPrimeIndicator K T p :=
  rayMaskedPrimePolynomial_decomposed K S P R ω η ξ W (momentPrimeGeometry K g) T i I Z 0

theorem rayMaskedPrimePolynomial_empty {ω ψ : HeckeCharacter K}
    (d : MomentData K ω ψ) (i : Fin d.geometry.slotCount)
    (u : NonzeroIdeal K) (Z t : ℝ) :
    rayMaskedPrimePolynomial K d ∅ i u Z t = primePolynomial d i u Z t := by
  simp [rayMaskedPrimePolynomial, fixedRayPrimeIndicator, primePolynomial]

theorem rayMaskedPrimePolynomial_restrictSlots {ω ψ : HeckeCharacter K}
    (d : MomentData K ω ψ) (T : Finset (HeckeCharacter K))
    (J : Finset (Fin d.geometry.slotCount)) (i : Fin J.card)
    (u : NonzeroIdeal K) (Z t : ℝ) :
    rayMaskedPrimePolynomial K (d.restrictSlots J) T i u Z t =
      rayMaskedPrimePolynomial K d T (selectedSlotIndex J i) u Z t := rfl

theorem rayMaskedPrimeProduct_restrictSlots {ω ψ : HeckeCharacter K}
    (d : MomentData K ω ψ) (T : Finset (HeckeCharacter K))
    (J : Finset (Fin d.geometry.slotCount)) (u : NonzeroIdeal K) (Z t : ℝ) :
    (∏ i : Fin J.card, rayMaskedPrimePolynomial K (d.restrictSlots J) T i u Z t) =
      ∏ i ∈ J, rayMaskedPrimePolynomial K d T i u Z t :=
  selectedSlots_prod J (fun i => rayMaskedPrimePolynomial K d T i u Z t)

theorem rayMaskedSelectedPrimeProduct_decomposed
    (ω η : HeckeCharacter K) (ξ : SixthUnitClasses K S) (W : IdealTest K)
    (g : SlotGeometry K) (T : Finset (HeckeCharacter K))
    (J : Finset (Fin g.slotCount)) (I : ExteriorIdeal K S) (Z t : ℝ) :
    (∏ i : Fin J.card,
      rayMaskedPrimePolynomial K
        ((decomposedMomentDataWithSlots K S P R ω η ξ W g).restrictSlots J)
        T i I.val Z t) =
      ∏ i ∈ J, actualDecomposedPrimePolynomial K S P ξ g T i I Z t := by
  calc
    _ = ∏ i ∈ J,
        rayMaskedPrimePolynomial K (decomposedMomentDataWithSlots K S P R ω η ξ W g)
          T i I.val Z t :=
      rayMaskedPrimeProduct_restrictSlots K
        (decomposedMomentDataWithSlots K S P R ω η ξ W g) T J I.val Z t
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _hi
      exact rayMaskedPrimePolynomial_decomposed K S P R ω η ξ W g T i I Z t

end HeckeGeneral.ThetaSkeleton.Physical
