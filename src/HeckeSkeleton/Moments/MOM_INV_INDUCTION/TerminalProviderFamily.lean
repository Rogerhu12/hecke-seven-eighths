import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderTheta
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderPuncture
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalChildren

/-!
# Literal canonical families enter the completed theta source

The period is the actual character `nu * Lambda⁻¹`. Its ideal
coefficient is proved equal to the canonical coefficient, preserving
the live background's possible zero values. The original family
puncture is projected to its exterior radical by a proved mask
identity. The complete pool is reduced only where the original
annular test vanishes, and the normalization keeps its original scale.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOM_BASE
open HeckeSkeleton.Moments.MOMInvStep
open HeckeSkeleton.Moments.MOM_INV_STEP
open FixedTripleFibers CanonicalChildren CanonicalNormPools
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

/-- This coefficient identity uses multiplication by the fixed
unramified calibration character only. The live `nu` is not altered. -/
theorem canonical_period_coefficient (Λ ν : HeckeCharacter K)
    (hΛ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K Λ p)
    (n : ExteriorIdeal K S) :
    thetaGamma K S D n 2 * heckeIdealCoefficient K (ν * Λ⁻¹) n.val =
      CoefficientCycle.canonicalCoefficient K S D Λ n *
        heckeIdealCoefficient K ν n.val := by
  rw [BackgroundCycle.exterior_coefficient_mul K S ν Λ⁻¹
    (fun p hp => (hΛ p hp).inv K) n, heckeIdealCoefficient_inv]
  unfold CoefficientCycle.canonicalCoefficient
  ring

/-- The completed finite source is the original canonical coefficient
with the actual raw puncture, row, label, mark, and norm profile. -/
theorem completeCanonicalColumn_eq_calibrated (Λ ν : HeckeCharacter K)
    (hΛ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K Λ p)
    (k : S.integer K) (f : ExteriorIdeal K S) (r : NonzeroIdeal K)
    (mark : Ideal (𝓞 K) → ℂ) (W : ℝ → ℂ) (X : ℝ) :
    completeCanonicalColumn K S D (ν * Λ⁻¹) k f (exteriorRadicalPuncture K S r)
        mark W X =
      (Real.sqrt X : ℂ)⁻¹ * ∑ n ∈ squarefreePool K S X,
        CoefficientCycle.canonicalCoefficient K S D Λ n *
          heckeIdealCoefficient K ν n.val *
          (if IsCoprime n.val.val r.val then 1 else 0) *
          idealSymbol K S D n k * idealSymbol K S D n (D.generator f) ^ 4 *
          mark n.val.val * W (exteriorNorm K S n / X) := by
  unfold completeCanonicalColumn
  rw [canonicalTau_exteriorRadicalPuncture]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [canonicalTau_label]
  calc
    _ = (thetaGamma K S D n 2 * heckeIdealCoefficient K (ν * Λ⁻¹) n.val) *
        (if IsCoprime n.val.val r.val then 1 else 0) * idealSymbol K S D n k *
        idealSymbol K S D n (D.generator f) ^ 4 *
        mark n.val.val * W (exteriorNorm K S n / X) := by ring
    _ = _ := by rw [canonical_period_coefficient K S D Λ ν hΛ n]

variable {σ Sector : Type*} {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}

/-- Equality from the actual provider family, on every exterior row
and original unit sector. No polynomial-calibration hypothesis occurs;
the row and label are the same concrete symbols on both sides. -/
theorem family_column_eq_completeCanonicalColumn
    (C : ColumnFamily K S σ Θ ψ) (γ : OuterTriple K)
    (sectorUnit : Sector → S.unit K) (k f : ExteriorIdeal K S) (ξ : Sector)
    (hbase : 0 < C.base)
    (hpool : C.columns γ = squarefreePool K S (2 * C.base ^ C.columnLength γ))
    (hW : tsupport (C.cutoff γ) ⊆ Set.Icc (1 : ℝ) 2)
    (hpuncture : childPuncture C.originalPuncture γ ≠ 0)
    (hΛ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K C.lambda p) :
    let X := C.base ^ C.columnLength γ
    let r : NonzeroIdeal K :=
      ⟨childPuncture C.originalPuncture γ, mem_nonZeroDivisors_of_ne_zero hpuncture⟩
    (Real.sqrt X : ℂ)⁻¹ * column K S D C sectorUnit γ f.val.val (k.val.val, ξ) =
      completeCanonicalColumn K S D (C.background γ * C.lambda⁻¹)
        ((S.unitEquivUnitsInteger K (sectorUnit ξ)).val * D.generator k)
        f (exteriorRadicalPuncture K S r)
        (divisorMark (C.survivors γ) C.primeLists C.primeWeights) (C.cutoff γ) X := by
  dsimp only
  rw [completeCanonicalColumn_eq_calibrated K S D C.lambda (C.background γ) hΛ]
  unfold column
  rw [hpool]
  simp_rw [sectorRow_exterior, labelRow_exterior]
  congr 1
  symm
  apply Finset.sum_subset
  · intro n hn
    have hh := (mem_squarefreePool K S _ n).mp hn
    apply (mem_squarefreePool K S _ n).mpr
    refine ⟨hh.1, ?_⟩
    have hX := (Real.rpow_pos_of_pos hbase (C.columnLength γ)).le
    linarith [hh.2]
  · intro n hn hnot
    have hsf := ((mem_squarefreePool K S _ n).mp hn).1
    have hz : C.cutoff γ (exteriorNorm K S n / C.base ^ C.columnLength γ) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hs
      have hb := (div_le_iff₀ (Real.rpow_pos_of_pos hbase (C.columnLength γ))).mp
        (hW hs).2
      exact hnot ((mem_squarefreePool K S _ n).mpr ⟨hsf, hb⟩)
    simp only [hz, mul_zero]

end HeckeSkeleton.Moments.MOM_INV_INDUCTION

end
