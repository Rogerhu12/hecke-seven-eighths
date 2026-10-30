import HeckeGeneral.Analysis.DecomposedSIntegerRowCalibration
import HeckeGeneral.Analysis.ActualZeroSlotProfileCalibration

/-!
Concrete zero-slot MomentData, separately for each original unit sector.
Rows enumerate complete exterior ideals, not just sixth-power-free bases.
The character of a descendant is its calibrated base character; the mask
retains coprimality to the complete row ideal and fixed S/6 deletion.
This constructor and its polynomial equality supply no CanonicalAdmissibility
instance, uniform seminorm estimate, or moment inequality.
-/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.Analysis.SquarefreeAmplification HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (R : RowCharacterInput K S P)

def completeIdealIsExterior (I : NonzeroIdeal K) : Prop :=
  ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val → p ∉ S

def completeExteriorIdealRows (U : ℝ) : Finset (NonzeroIdeal K) :=
  if 0 ≤ U then
    (dyadicIdealSupport K (U / 2)).filter (completeIdealIsExterior K S)
  else ∅

omit [Fintype S] in
theorem mem_completeExteriorIdealRows (U : ℝ) (I : NonzeroIdeal K) :
    I ∈ completeExteriorIdealRows K S U ↔
      completeIdealIsExterior K S I ∧ idealNorm K I ≤ U := by
  by_cases hU : 0 ≤ U
  · rw [completeExteriorIdealRows, ite_eq_left hU, Finset.mem_filter,
      mem_dyadicIdealSupport_iff K (div_nonneg hU (by norm_num))]
    rw [show 2 * (U / 2) = U by ring]
    exact and_comm
  · have hn : ¬idealNorm K I ≤ U := by
      have := idealNorm_pos K I
      linarith
    simp [completeExteriorIdealRows, hU, hn]

def completeIdealRowCharacter (ξ : SixthUnitClasses K S) (I : NonzeroIdeal K) :
    HeckeCharacter K :=
  if h : completeIdealIsExterior K S I then
    R.character (decomposedFrequencyRow K S ⟨I, h⟩ ξ)
  else 1

theorem completeIdealRowCharacter_finite (ξ : SixthUnitClasses K S) (I : NonzeroIdeal K) :
    FiniteOrder (completeIdealRowCharacter K S P R ξ I) := by
  unfold completeIdealRowCharacter
  split
  · exact R.finite_order _
  · exact IsOfFinOrder.one

theorem completeIdealRowCharacter_exterior (ξ : SixthUnitClasses K S)
    (I : ExteriorIdeal K S) :
    completeIdealRowCharacter K S P R ξ I.val =
      R.character (decomposedFrequencyRow K S I ξ) := by
  unfold completeIdealRowCharacter
  split
  · rfl
  · rename_i h
    exact False.elim (h I.property)

def completeIdealCommonMask (I : NonzeroIdeal K) (J : Ideal (𝓞 K)) : Bool :=
  decide ((∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ J →
    p ∉ S ∧ (6 : 𝓞 K) ∉ p.asIdeal) ∧ IsCoprime J I.val)

/-- The background relation is literal: eta = psi*1, with psi=eta. -/
def decomposedZeroSlotMomentData (ω η : HeckeCharacter K)
    (ξ : SixthUnitClasses K S) (W : IdealTest K) : MomentData K ω η where
  theta := {1}
  theta_finite := by intro θ hθ; simp only [Finset.mem_singleton] at hθ; subst θ; exact IsOfFinOrder.one
  inverseBackground := η
  direction := -1
  direction_spec := Or.inl rfl
  directed_background := Or.inr ⟨1, Finset.mem_singleton_self 1, by simp⟩
  plainBackground := 1
  plain_background_spec := Or.inl rfl
  rowCharacter := completeIdealRowCharacter K S P R ξ
  rowCharacter_finite := completeIdealRowCharacter_finite K S P R ξ
  allowedRow := completeIdealIsExterior K S
  rows := completeExteriorIdealRows K S
  rows_spec := mem_completeExteriorIdealRows K S
  commonMask := completeIdealCommonMask K S
  inverseTest := W
  plainTest₁ := W
  plainTest₂ := W
  geometry := zeroSlotGeometry K
  slotCoefficient := Fin.elim0

theorem decomposedZeroSlotMomentData_mask (ω η : HeckeCharacter K)
    (ξ : SixthUnitClasses K S) (W : IdealTest K)
    (I : ExteriorIdeal K S) (J : NonzeroIdeal K) :
    maskValue (decomposedZeroSlotMomentData K S P R ω η ξ W) I.val J.val =
      decomposedIdealRowMask K S I J := by
  change (if completeIdealCommonMask K S I.val J.val then (1 : ℂ) else 0) = _
  simp [completeIdealCommonMask, decomposedIdealRowMask, sexticIdealOutsideS]
  rfl

/-- Exact equality for any actual IdealTest, including the six Sobolev tests.
The finite support and profile are literally the SAME on both sides. -/
theorem inversePolynomial_decomposedZeroSlotMomentData
    (ω η : HeckeCharacter K) (ξ : SixthUnitClasses K S) (W : IdealTest K)
    (I : ExteriorIdeal K S) (D t : ℝ) :
    inversePolynomial (decomposedZeroSlotMomentData K S P R ω η ξ W) I.val D t =
      sIntegerSexticInverseIdealPolynomial K S P.arithmetic.root6
        P.arithmetic.primitive6 P.arithmetic.embedding η (W.support I.val t D)
        (decomposedIdealSectorOrbit K S P (I, ξ)).out.val D (W.profile I.val t) := by
  rw [sIntegerSexticInverseIdealPolynomial_decomposed_character K S P R]
  unfold inversePolynomial
  change (Real.sqrt D : ℂ)⁻¹ *
    (∑ J ∈ W.support I.val t D,
      (UniqueFactorizationMonoid.moebius J.val : ℂ) * heckeIdealCoefficient K η J *
        heckeIdealCoefficient K (completeIdealRowCharacter K S P R ξ I.val) J ^ (-1 : ℤ) *
        W.profile I.val t (idealNorm K J / D) *
        maskValue (decomposedZeroSlotMomentData K S P R ω η ξ W) I.val J.val) = _
  rw [completeIdealRowCharacter_exterior K S P R]
  congr 1
  apply Finset.sum_congr rfl
  intro J hJ
  rw [decomposedZeroSlotMomentData_mask]

end HeckeGeneral.ThetaSkeleton.Physical
