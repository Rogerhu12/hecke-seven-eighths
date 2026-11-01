import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualExceptionalIndexMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectNormalizedChildren
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalPoolAllowanceTransport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalPoolMonotonicity

/-!
# Sum the proved exceptional estimates over the actual source labels

The arithmetic carrier, its source map, admissibility and finite
fibres are supplied by the existing actual-source index-mass theorems.
Their constants precede the scale, profiles, source and divisor dyads.

The leaf inequalities below are internal conclusions consumed after
the actual exceptional factory and its original Fourier integration.
They are not new primitives of the engine theorem. No index, finite
family, total arithmetic mass or profile catalogue is supplied anew.
The amplified scalar transport retains the original pool, actual
valuation tag and its moving-prime length exactly once.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalUniformIndexBudget

open NumberField IsDedekindDomain DedekindZetaZeroFree
open DedekindZetaZeroFree.LocalFiniteSums (ExteriorPrime)
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup HeckePort.Moments.Support
open CommonSupportMass UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K] {A : SArithmeticData K}

section OriginalTag

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}

/-- Internal transport of the already proved original scalar. The
local density windows may vary with the actual source label, while
the same amplified arithmetic index uses one fixed upper window. -/
theorem original_tag_to_uniform_dyad
    (pool : PowerScaleExteriorPool A bad Z ell eps)
    (main : TwoDivisorCommonBranch (K := K))
    (error : ℕ → ExteriorPrime A → TwoDivisorCommonBranch (K := K))
    {localM localB M B : ℝ}
    (hlocalM : 0 ≤ localM) (hM : localM ≤ M) (hB : localB ≤ B)
    (hdensity : 0 < pool.rowDensity M B)
    (i : AmplifiedCommonIndex pool main error)
    (actual coefficient control remaining loss lower : ℝ)
    (hcoefficient : 0 ≤ coefficient) (hcontrol : 0 ≤ control)
    (hremaining : remaining ≤ loss + AmplifiedCommonIndex.movingLength pool main error i)
    (hraw : actual ≤ coefficient * control *
      AmplifiedCommonIndex.originalTagWeight pool localM localB main error i *
        Z ^ remaining * AmplifiedCommonIndex.dyadWeight pool main error lower i) :
    actual ≤ coefficient * control * Z ^ loss *
      amplifiedExceptionalDyadWeight pool M B main error lower i := by
  have htag := AmplifiedCommonIndex.originalTagWeight_mono_windows
    pool main error hlocalM hM hB hdensity i
  have hglobal : actual ≤ coefficient * control *
      AmplifiedCommonIndex.originalTagWeight pool M B main error i *
        Z ^ remaining * AmplifiedCommonIndex.dyadWeight pool main error lower i :=
    hraw.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left htag (mul_nonneg hcoefficient hcontrol))
        (Real.rpow_nonneg (zero_lt_one.trans pool.base_gt_one).le _))
      (AmplifiedCommonIndex.dyadWeight_nonneg pool main error
        (zero_lt_one.trans pool.base_gt_one).le lower i))
  exact AmplifiedCommonIndex.exceptional_pointwise_of_original_tag
    pool M B main error pool.base_gt_one pool.exponent_pos (hlocalM.trans hM)
    hdensity.le i actual coefficient control remaining loss lower
    hcoefficient hcontrol hremaining hglobal

end OriginalTag

variable {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {Θ : Type*} [Fintype Θ]

/-- Sum the integrated literal direct leaves using their actual
arithmetic image and original fibre. The fixed coefficient includes
the already paid theta, atom, common-profile and Fourier constants. -/
theorem direct
    (cap dimension width degree : ℕ) (normBox δ₁ δ₂ δ₃ coefficient : ℝ)
    (hbox : 0 ≤ normBox) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₃ : 0 < δ₃)
    (hcoefficient : 0 ≤ coefficient) :
    ∃ Cex : ℝ, 0 < Cex ∧ ∀ Z : ℝ, 1 < Z → ∀ P : ℝ, 1 ≤ P → ∀ loss : ℝ,
    ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ) (a : RealParameters)
      (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X)
      (s : ActualDirectFirstSource (E := U) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX)
      (R : s.SecondStages (E := E) (hDiff := hDiff))
      (L : SourceCartesianAtlas s.columns s.ideal) (hcap : L.slotCount ≤ cap)
      (exceptional : R.prepared.CoverHybridPredicates L) (N : s.Normalization),
    ∀ rows : R.prepared.OriginalFibreRows Θ dimension width normBox Z,
    ∀ oldMask : Ideal (𝓞 K), Squarefree oldMask → oldMask ≠ 0 →
      (∀ i ∈ s.columns, oldMask ∣ (s.ideal i).val) →
    ∀ maskIdeal : Ideal (𝓞 K), maskIdeal ≠ 0 →
      OriginalMaskPrimeData s.mask maskIdeal →
      (Ideal.absNorm maskIdeal : ℝ) ≤ Z ^ normBox →
      (∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ normBox) →
    ∀ (lower : R.prepared.liveLeaves L exceptional N → ℝ) (mesh : ℝ),
      (∀ i, (Ideal.absNorm (R.prepared.innerDivisor L i.val) : ℝ) ≤ Z ^ (lower i + mesh)) →
      (∀ i : R.prepared.liveLeaves L exceptional N,
        (R.prepared.parentLeaf L exceptional N i.val).exceptionalCost / Z ^ (a.m + a.q) ≤
          coefficient * P ^ degree * Z ^ loss *
            (R.prepared.arithmeticLabels L hcap exceptional N).carrier.exceptionalDyadWeight
              Z (lower i) (R.prepared.originalIndex L hcap exceptional N i)) →
      R.prepared.exceptionalBudget L exceptional N / Z ^ (a.m + a.q) ≤
        Cex * P ^ degree * Z ^ (loss + δ₁ + δ₂ + δ₃ + mesh) /
          (Ideal.absNorm oldMask : ℝ) := by
  obtain ⟨Ca, hCa, hmass⟩ := actual_direct_exceptional_index_mass
    (A := A) (C := C) (W := U) (E := E) (Θ := Θ)
    (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (finiteTest := finiteTest)
    cap dimension width normBox δ₁ δ₂ δ₃ hbox hδ₁ hδ₂ hδ₃
  refine ⟨(coefficient + 1) * Ca, mul_pos (by linarith) hCa, ?_⟩
  intro Z hZ P hP loss ω ψ centered d a t Y₁ Y₂ X hX s R L hcap exceptional N
    rows oldMask hs hs0 hmaskOld maskIdeal hmask0 mask hmaskN hN lower mesh hwindow hleaf
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hm := hmass Z hZ.le centered d a t Y₁ Y₂ X hX s R L hcap exceptional N
    rows oldMask hs hs0 hmaskOld maskIdeal hmask0 mask hmaskN hN lower mesh hwindow
  let dyad := fun i : R.prepared.liveLeaves L exceptional N =>
    (R.prepared.arithmeticLabels L hcap exceptional N).carrier.exceptionalDyadWeight
      Z (lower i) (R.prepared.originalIndex L hcap exceptional N i)
  have hscalar : 0 ≤ coefficient * P ^ degree * Z ^ loss :=
    mul_nonneg (mul_nonneg hcoefficient (pow_nonneg (zero_le_one.trans hP) _))
      (Real.rpow_nonneg hz.le _)
  have hnorm : 0 < (Ideal.absNorm oldMask : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs0))
  calc
    _ = ∑ i : R.prepared.liveLeaves L exceptional N,
        (R.prepared.parentLeaf L exceptional N i.val).exceptionalCost / Z ^ (a.m + a.q) := by
      simp only [ActualDirectFirstSource.SecondStages.exceptionalBudget,
        ActualDirectFirstSource.SecondStages.liveLeaf, Finset.sum_div]
    _ ≤ ∑ i : R.prepared.liveLeaves L exceptional N,
        coefficient * P ^ degree * Z ^ loss * dyad i :=
      Finset.sum_le_sum fun i _ => hleaf i
    _ = (coefficient * P ^ degree * Z ^ loss) * ∑ i, dyad i :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (coefficient * P ^ degree * Z ^ loss) *
        (Ca * Z ^ (δ₁ + δ₂ + δ₃ + mesh) / (Ideal.absNorm oldMask : ℝ)) :=
      mul_le_mul_of_nonneg_left hm hscalar
    _ = (coefficient * Ca) * P ^ degree *
        Z ^ (loss + δ₁ + δ₂ + δ₃ + mesh) / (Ideal.absNorm oldMask : ℝ) := by
      rw [show loss + δ₁ + δ₂ + δ₃ + mesh = loss + (δ₁ + δ₂ + δ₃ + mesh) by ring,
        Real.rpow_add hz loss (δ₁ + δ₂ + δ₃ + mesh)]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hCa.le)
          (pow_nonneg (zero_le_one.trans hP) _))
        (Real.rpow_nonneg hz.le _)) hnorm.le

/-- The amplified entrance sums the same actual supported, gated
leaves and their original arithmetic tags. The moving length has
already been absorbed by `original_tag_to_uniform_dyad`; the index
mass pays only its proved three small losses, pool loss and dyad mesh. -/
theorem amplified
    (cap dimension width degree : ℕ)
    (normBox δ₁ δ₂ δ₃ ell eps Mmax Bmax coefficient : ℝ)
    (hbox : 0 ≤ normBox) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₃ : 0 < δ₃)
    (hell : 0 < ell) (heps : 0 < eps) (hepsell : eps < ell)
    (hMmax : 0 ≤ Mmax) (hBmax : 0 ≤ Bmax) (hcoefficient : 0 ≤ coefficient) :
    ∃ Cex Z₀ : ℝ, 0 < Cex ∧ 1 < Z₀ ∧
    ∀ Z : ℝ, Z₀ ≤ Z → ∀ bad : Finset (HeightOneSpectrum (𝓞 K)),
    ∀ pool : PowerScaleExteriorPool A bad Z ell eps,
    ∀ M B P : ℝ, 0 ≤ M → M ≤ Mmax → B ≤ Bmax → 1 ≤ P → ∀ loss : ℝ,
    ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ) (a : RealParameters)
      (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X)
      (s : ActualFirstSource (E := U) hΓ μv C pool finiteTest centered d a t Y₁ Y₂ X hX)
      (R : s.SecondStages (E := E) (hDiff := hDiff))
      (L : SourceCartesianAtlas s.columns s.ideal) (hcap : L.slotCount ≤ cap)
      (exceptional : R.supported.gated.CoverHybridPredicates L) (N : s.Normalization)
      (B₀ : ℝ), B₀ + 7 * ell ≤ normBox →
    ∀ rows : R.supported.gated.OriginalFibreRows Θ dimension width normBox Z,
    ∀ oldMask : Ideal (𝓞 K), Squarefree oldMask → oldMask ≠ 0 →
      (∀ i ∈ s.columns, oldMask ∣ (s.ideal i).val) →
    ∀ maskIdeal : Ideal (𝓞 K), maskIdeal ≠ 0 →
      OriginalMaskPrimeData s.mask maskIdeal →
      (Ideal.absNorm maskIdeal : ℝ) ≤ Z ^ normBox →
      (∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ B₀) →
    ∀ (lower : R.supported.gated.liveLeaves L exceptional N → ℝ) (mesh : ℝ),
      (∀ i, (Ideal.absNorm (R.supported.gated.innerDivisor L i.val) : ℝ) ≤
        Z ^ (lower i + mesh)) →
      (∀ i : R.supported.gated.liveLeaves L exceptional N,
        (R.supported.gated.parentLeaf L exceptional N i.val).exceptionalCost / Z ^ (a.m + a.q) ≤
          coefficient * P ^ degree * Z ^ loss *
            amplifiedExceptionalDyadWeight pool M B
              ((R.supported.gated.arithmeticLabels L hcap exceptional N).mainCarrier
                (R.supported.gated.arithmeticTag L exceptional N))
              ((R.supported.gated.arithmeticLabels L hcap exceptional N).errorCarrier
                (R.supported.gated.arithmeticTag L exceptional N))
              (lower i) (R.supported.gated.arithmeticIndex L hcap exceptional N i)) →
      R.supported.gated.exceptionalBudget L exceptional N / Z ^ (a.m + a.q) ≤
        Cex * P ^ degree * Z ^ (loss + δ₁ + δ₂ + δ₃ + eps + mesh) /
          (Ideal.absNorm oldMask : ℝ) := by
  obtain ⟨Ca, Z₀, hCa, hZ₀, hmass⟩ := actual_amplified_exceptional_index_mass
    (A := A) (C := C) (W := U) (E := E) (Θ := Θ)
    (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (finiteTest := finiteTest)
    cap dimension width normBox δ₁ δ₂ δ₃ ell eps Mmax Bmax
    hbox hδ₁ hδ₂ hδ₃ hell heps hepsell hMmax hBmax
  refine ⟨(coefficient + 1) * Ca, Z₀, mul_pos (by linarith) hCa, hZ₀, ?_⟩
  intro Z hZ bad pool M B P hM hMM hBB hP loss ω ψ centered d a t Y₁ Y₂ X hX s R L hcap
    exceptional N B₀ hB₀ rows oldMask hs hs0 hmaskOld maskIdeal hmask0 mask hmaskN hN lower mesh
    hwindow hleaf
  have hz : 0 < Z := zero_lt_one.trans pool.base_gt_one
  have hm := hmass Z hZ bad pool M B hM hMM hBB centered d a t Y₁ Y₂ X hX s R L hcap
    exceptional N B₀ hB₀ rows oldMask hs hs0 hmaskOld maskIdeal hmask0 mask hmaskN hN lower mesh hwindow
  let dyad := fun i : R.supported.gated.liveLeaves L exceptional N =>
    amplifiedExceptionalDyadWeight pool M B
      ((R.supported.gated.arithmeticLabels L hcap exceptional N).mainCarrier
        (R.supported.gated.arithmeticTag L exceptional N))
      ((R.supported.gated.arithmeticLabels L hcap exceptional N).errorCarrier
        (R.supported.gated.arithmeticTag L exceptional N)) (lower i)
      (R.supported.gated.arithmeticIndex L hcap exceptional N i)
  have hscalar : 0 ≤ coefficient * P ^ degree * Z ^ loss :=
    mul_nonneg (mul_nonneg hcoefficient (pow_nonneg (zero_le_one.trans hP) _))
      (Real.rpow_nonneg hz.le _)
  have hnorm : 0 < (Ideal.absNorm oldMask : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs0))
  calc
    _ = ∑ i : R.supported.gated.liveLeaves L exceptional N,
        (R.supported.gated.parentLeaf L exceptional N i.val).exceptionalCost / Z ^ (a.m + a.q) := by
      rw [ActualFirstSource.SecondStages.exceptionalBudget, Finset.sum_div]
    _ ≤ ∑ i : R.supported.gated.liveLeaves L exceptional N,
        coefficient * P ^ degree * Z ^ loss * dyad i :=
      Finset.sum_le_sum fun i _ => hleaf i
    _ = (coefficient * P ^ degree * Z ^ loss) * ∑ i, dyad i :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (coefficient * P ^ degree * Z ^ loss) *
        (Ca * Z ^ (δ₁ + δ₂ + δ₃ + eps + mesh) / (Ideal.absNorm oldMask : ℝ)) :=
      mul_le_mul_of_nonneg_left hm hscalar
    _ = (coefficient * Ca) * P ^ degree *
        Z ^ (loss + δ₁ + δ₂ + δ₃ + eps + mesh) / (Ideal.absNorm oldMask : ℝ) := by
      rw [show loss + δ₁ + δ₂ + δ₃ + eps + mesh = loss + (δ₁ + δ₂ + δ₃ + eps + mesh) by ring,
        Real.rpow_add hz loss (δ₁ + δ₂ + δ₃ + eps + mesh)]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hCa.le)
          (pow_nonneg (zero_le_one.trans hP) _))
        (Real.rpow_nonneg hz.le _)) hnorm.le

end HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalUniformIndexBudget

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalUniformIndexBudget.original_tag_to_uniform_dyad
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalUniformIndexBudget.direct
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalUniformIndexBudget.amplified
