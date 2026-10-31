import HeckeSkeleton.Moments.MOM_INV_STEP.FirstSourceFrozen
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalBlock

/-!
# Literal marked first-source columns on a fixed extraction slice

This file connects the actual `CanonicalBlock.canonicalColumn` to the
proved signed first Fourier factorization. The original puncture,
individual prime weights, norm cutoff, and cube/label-only weight are
kept. The three ordered extracted factors in the mark expansion are
the old cube, its extracted squarefree part, and the common residual
part. Every resulting moving coefficient is still explicit.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalFirstSource

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open FirstSourceColumns FirstSourceFrozen CanonicalConductor
open HeckeSkeleton.Moments.MOMInvStep
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "E" => CanonicalIdealRow.exteriorMonoid K S
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable {σ : Type*}

/-- Exactly the original non-character decorations. -/
def decoration (C : CanonicalBlock.ColumnData K S σ) (b n : Ext) : ℂ :=
  (if IsCoprime n.val.val C.puncture then 1 else 0) *
    divisorMark C.slots C.primeLists C.primeWeights (n.val.val * b.val.val ^ 3) *
    C.cutoff ((n.val.val.absNorm : ℝ) / C.base ^ C.length)

theorem canonicalColumn_eq (C : CanonicalBlock.ColumnData K S σ) (f : E) (b n : Ext) :
    CanonicalBlock.canonicalColumn K S D C (CanonicalIdealRow.toExterior K S f) b n =
      C.labelWeight b (CanonicalIdealRow.toExterior K S f) *
        sourceCoefficient K S D C.lambda C.background n f * decoration K S C b n := by
  unfold CanonicalBlock.canonicalColumn sourceCoefficient decoration CanonicalIdealRow.generator
  ring

def frozenOriginal (r₁ r₂ b₁ b₂ : Ext) (side : Bool) (u : Ext) : Ext :=
  exteriorMul K Sset
    (CanonicalIdealRow.toExterior K S (extractedFactor K S r₁ r₂ b₁ b₂ side)) u

theorem frozenOriginal_residual (n₁ n₂ r₁ r₂ b₁ b₂ : Ext)
    (hn₁ : Squarefree n₁.val.val) (hn₂ : Squarefree n₂.val.val)
    (h : SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂) (side : Bool) :
    frozenOriginal K S r₁ r₂ b₁ b₂ side (residualIdeal K S D n₁ n₂ b₁ b₂ side) =
      sourceIdeal K S n₁ n₂ side := by
  have he := source_factorization K S D n₁ n₂ b₁ b₂ hn₁ hn₂ side
  rw [extractedFactor_eq K S n₁ n₂ r₁ r₂ b₁ b₂ h side] at he
  exact he

variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))

/-- The moving variable occurs only as the residual ideal. All marks
and the norm test are evaluated on its literal frozen reconstruction. -/
def fixedMarkedInverse (C : CanonicalBlock.ColumnData K S σ) (G : HeckeCharacter K)
    (r₁ r₂ b₁ b₂ : Ext) (side : Bool) (f z : E) (d : OS)
    (ξ : CanonicalSectors.UnitClasses K Sset Γ) (u : Ext) : ℂ :=
  fixedSectorCoefficient K S D Γ C.background G r₁ r₂ b₁ b₂ f z d ξ u *
    decoration K S C (sourceIdeal K S b₁ b₂ side)
      (frozenOriginal K S r₁ r₂ b₁ b₂ side u)

/-- The actual marked canonical source after the first finite Fourier
transform, with every original unit sector and mask-divisor phase. -/
theorem canonical_pair_sector (hallowed : AllowedGeneratorInput K Sset D)
    (C : CanonicalBlock.ColumnData K S σ) (G : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset D C.lambda G)
    (n₁ n₂ r₁ r₂ b₁ b₂ : Ext)
    (hn₁ : Squarefree n₁.val.val) (hn₂ : Squarefree n₂.val.val)
    (h : SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂)
    (f₁ f₂ z : E) (d : OS) (ξ : CanonicalSectors.UnitClasses K Sset Γ) :
    CanonicalBlock.canonicalColumn K S D C (CanonicalIdealRow.toExterior K S f₁) b₁ n₁ *
      conj (CanonicalBlock.canonicalColumn K S D C (CanonicalIdealRow.toExterior K S f₂) b₂ n₂) *
      pairFourier K S D n₁ n₂ b₁ b₂ d
        (CanonicalSectors.rowElement K Sset Γ D (CanonicalIdealRow.toExterior K S z, ξ)).val =
    cubeFourierScalar K S D r₁ r₂ b₁ b₂ d
        (CanonicalSectors.rowElement K Sset Γ D (CanonicalIdealRow.toExterior K S z, ξ)).val *
      (C.labelWeight b₁ (CanonicalIdealRow.toExterior K S f₁) *
        outerCoefficient K S D C.lambda C.background r₁ r₂ b₁ b₂ false f₁ *
        fixedMarkedInverse K S D Γ C G r₁ r₂ b₁ b₂ false f₁ z d ξ
          (residualIdeal K S D n₁ n₂ b₁ b₂ false)) *
      conj (C.labelWeight b₂ (CanonicalIdealRow.toExterior K S f₂) *
        outerCoefficient K S D C.lambda C.background r₁ r₂ b₁ b₂ true f₂ *
        fixedMarkedInverse K S D Γ C G r₁ r₂ b₁ b₂ true f₂ z d ξ
          (residualIdeal K S D n₁ n₂ b₁ b₂ true)) := by
  have he := congrArg (fun w : ℂ =>
    C.labelWeight b₁ (CanonicalIdealRow.toExterior K S f₁) * decoration K S C b₁ n₁ *
      conj (C.labelWeight b₂ (CanonicalIdealRow.toExterior K S f₂) *
        decoration K S C b₂ n₂) * w)
    (first_source_pair_sector K S D Γ hallowed hcal C.background
      n₁ n₂ r₁ r₂ b₁ b₂ hn₁ hn₂ h f₁ f₂ z d ξ)
  simp only [canonicalColumn_eq, fixedMarkedInverse,
    frozenOriginal_residual K S D n₁ n₂ r₁ r₂ b₁ b₂ hn₁ hn₂ h,
    sourceIdeal, Bool.false_eq_true, if_false, if_true, map_mul] at he ⊢
  convert he using 1 <;> ring

/-- Ordered priority acts on the actual original factors, preserving
the original individual coefficients and the exact cutoff scaling. -/
theorem decoration_priority (C : CanonicalBlock.ColumnData K S σ)
    (r₁ r₂ b₁ b₂ : Ext) (side : Bool) (u : Ext)
    (hL : ∀ i ∈ C.slots, ∀ P ∈ C.primeLists i, Prime P) :
    decoration K S C (sourceIdeal K S b₁ b₂ side)
        (frozenOriginal K S r₁ r₂ b₁ b₂ side u) =
      (if IsCoprime (extractedFactor K S r₁ r₂ b₁ b₂ side).val.val C.puncture then 1 else 0) *
      (if IsCoprime u.val.val C.puncture then 1 else 0) *
      priorityMarkExpansion
        [(sourceIdeal K S b₁ b₂ side).val.val ^ 3,
          (CanonicalCubeLabels.A K S b₁ b₂
            (squarefreeBit K S (sourceIdeal K S r₁ r₂ side))).val.val,
          (commonFactor K S r₁ r₂ b₁ b₂).val.val]
        C.slots C.primeLists C.primeWeights u.val.val *
      C.cutoff (((extractedFactor K S r₁ r₂ b₁ b₂ side).val.val.absNorm : ℝ) *
        (u.val.val.absNorm : ℝ) / C.base ^ C.length) := by
  let A := (CanonicalCubeLabels.A K S b₁ b₂
    (squarefreeBit K S (sourceIdeal K S r₁ r₂ side))).val.val
  let g := (commonFactor K S r₁ r₂ b₁ b₂).val.val
  let b := (sourceIdeal K S b₁ b₂ side).val.val
  have hv : (extractedFactor K S r₁ r₂ b₁ b₂ side).val.val = A * g := rfl
  have hn : (frozenOriginal K S r₁ r₂ b₁ b₂ side u).val.val =
      (extractedFactor K S r₁ r₂ b₁ b₂ side).val.val * u.val.val := rfl
  have hm : (extractedFactor K S r₁ r₂ b₁ b₂ side).val.val * u.val.val * b ^ 3 =
      ([b ^ 3, A, g] : List (Ideal (𝓞 K))).prod * u.val.val := by
    rw [hv]
    simp only [List.prod_cons, List.prod_nil, mul_one]
    ring
  have hp : (if IsCoprime ((extractedFactor K S r₁ r₂ b₁ b₂ side).val.val * u.val.val)
      C.puncture then (1 : ℂ) else 0) =
      (if IsCoprime (extractedFactor K S r₁ r₂ b₁ b₂ side).val.val C.puncture then 1 else 0) *
        (if IsCoprime u.val.val C.puncture then 1 else 0) := by
    rw [IsCoprime.mul_left_iff]
    split_ifs <;> simp_all
  unfold decoration
  rw [hn, hp, map_mul, Nat.cast_mul]
  change _ * divisorMark C.slots C.primeLists C.primeWeights
    ((extractedFactor K S r₁ r₂ b₁ b₂ side).val.val * u.val.val * b ^ 3) * _ = _
  rw [hm, primeMark_priority_list _ _ _ _ _ hL]
  rfl

end HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalFirstSource

end
