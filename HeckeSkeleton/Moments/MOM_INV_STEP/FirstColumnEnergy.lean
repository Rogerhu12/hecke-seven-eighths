import HeckeSkeleton.Moments.MOM_INV_STEP.FirstColumnAssembly
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstMellinEnergy
import HeckePort.CenteredMoment.IdealMobius

/-!
# The complete literal first column enters positive Mellin energy

The first source identity is proved in FirstColumnAssembly. Here the
frozen scalar is bounded with its actual N(e)⁻¹ square norm, and finite
Cauchy is applied over original assigned slot subsets. Squared assigned
marks retain the precise twice-slot history for the final fibres.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstColumnEnergy

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
  MeasureTheory
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalBlock CanonicalNormPools
  FirstSourceColumns FirstSourceFrozen FirstOverlapColumns FirstColumnAssembly
  CanonicalFirstEnergy FirstCompleteFamily FirstMellinEnergy CommonKernel
open scoped Classical BigOperators nonZeroDivisors

private theorem complex_mul_norm_le_one {a b : ℂ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖a * b‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ ha (norm_nonneg _) hb

/-- Uniform finite Cauchy preserves the square of every assigned mark. -/
theorem finite_square_cauchy {ι : Type*} (T : Finset ι) (a : ι → ℂ) :
    ‖∑ i ∈ T, a i‖ ^ 2 ≤ (T.card : ℝ) * ∑ i ∈ T, ‖a i‖ ^ 2 := by
  have h₁ := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le T a) 2
  have h₂ := Finset.sum_mul_sq_le_sq_mul_sq T (fun _ => (1 : ℝ)) (fun i => ‖a i‖)
  exact h₁.trans (by simpa only [one_mul, one_pow, Finset.sum_const,
    nsmul_eq_mul, mul_one] using h₂)

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "E" => CanonicalIdealRow.exteriorMonoid K S
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

theorem fixedSectorCoefficient_norm_le_one (ν G : HeckeCharacter K)
    (r₁ r₂ b₁ b₂ : Ext) (f z : E) (d : OS) (ξ : Sector) (u : Ext) :
    ‖fixedSectorCoefficient K S D Γ ν G r₁ r₂ b₁ b₂ f z d ξ u‖ ≤ 1 := by
  have hs (a : OS) := idealSymbol_norm_le_one K S D u a
  have hm := HeckePort.IdealMobiusDivisorSum.norm_ideal_moebius_le_one u.val.val
  have hν := norm_heckeIdealCoefficient_le_one K ν u.val
  have hG := norm_heckeIdealCoefficient_le_one K G u.val
  have hmask : ‖(if IsCoprime u.val.val (CanonicalCubeLabels.q0 K S b₁ b₂
      (ConductorMasks.squarefreeBit K S r₁) (ConductorMasks.squarefreeBit K S r₂)).val.val
      then (1 : ℂ) else 0)‖ ≤ 1 := by split_ifs <;> norm_num
  have hlabel : ‖idealSymbol K Sset D u (CanonicalIdealRow.generator K S D
      (commonFactor K S r₁ r₂ b₁ b₂ * CanonicalCubeLabels.J K S b₁ b₂
        (ConductorMasks.squarefreeBit K S r₁) (ConductorMasks.squarefreeBit K S r₂))) ^ 4‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (hs _)
  unfold fixedSectorCoefficient fixedMultiplierCoefficient fixedInverseCoefficient
  apply complex_mul_norm_le_one
  · apply complex_mul_norm_le_one (hs _)
    apply complex_mul_norm_le_one
    · exact complex_mul_norm_le_one
        (complex_mul_norm_le_one (complex_mul_norm_le_one hm hν) hG)
        (complex_mul_norm_le_one hlabel hmask)
    · simpa only [Complex.norm_conj] using hs _
  · simpa only [Complex.norm_conj] using hs _

theorem normWeight_sq (e : Ext) :
    ‖normWeight K e.val‖ ^ 2 = (height K Sset e)⁻¹ := by
  rw [normWeight, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg _)]
  rfl

variable {σ : Type*}

theorem extractedScalar_norm_le (C : ColumnData K S σ) (G : HeckeCharacter K)
    (r₁ r₂ b₁ b₂ : Ext) (side : Bool) (f z : E) (d : OS) (ξ : Sector) (e : Ext) :
    ‖extractedScalar K S D Γ C G r₁ r₂ b₁ b₂ side f z d ξ e‖ ≤ ‖normWeight K e.val‖ := by
  have hs := fixedSectorCoefficient_norm_le_one K S D Γ C.background G r₁ r₂ b₁ b₂ f z d ξ e
  have hm : ‖(if IsCoprime ((extractedFactor K S r₁ r₂ b₁ b₂ side).val.val * e.val.val)
      C.puncture then (1 : ℂ) else 0)‖ ≤ 1 := by split_ifs <;> norm_num
  rw [extractedScalar, norm_mul, norm_mul]
  calc
    _ ≤ ‖normWeight K e.val‖ * 1 * 1 := mul_le_mul
      (mul_le_mul_of_nonneg_left hs (norm_nonneg _)) hm (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) zero_le_one)
    _ = _ := by ring

def sourceColumn (C : ColumnData K S σ) (G : HeckeCharacter K)
    (X : {r : ℝ // 0 < r}) (r₁ r₂ b₁ b₂ : Ext) (side : Bool)
    (f z : E) (d : OS) (ξ : Sector) (e : Ext) (τ : ℝ) : ℂ :=
  ∑ U ∈ FirstNormPoolEnergy.sideDomain K S (dyadicPool K Sset X.val) r₁ r₂ b₁ b₂ side,
    if e.val.val ∣ IdealMobiusMask.primeProduct U then
      movingColumn K S D Γ C G r₁ r₂ b₁ b₂ side f z d ξ
        (FirstSourceReindexing.nonzeroProduct U) *
        columnPhase τ (Real.log (((IdealMobiusMask.primeProduct U).absNorm : ℝ) /
          (FirstNormPoolEnergy.residualScale K S X r₁ r₂ b₁ b₂ side).val))
    else 0

variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)

include hallowed in
theorem sourceColumn_sq_le_branches (C : ColumnData K S σ)
    (G : HeckeCharacter K)
    (hG : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset → UnramifiedAt K G p)
    (X : {r : ℝ // 0 < r}) (hCX : C.base ^ C.length = X.val)
    (r₁ r₂ b₁ b₂ : Ext) (side : Bool) (f z : E) (d : OS) (ξ : Sector)
    (e : Ext) (he : Squarefree e.val.val) (W : SchwartzMap ℝ ℂ)
    (hCW : C.cutoff = W) (τ : ℝ)
    (hprime : ∀ i ∈ C.slots, ∀ p ∈ C.primeLists i, Prime p) :
    ‖sourceColumn K S D Γ C G X r₁ r₂ b₁ b₂ side f z d ξ e τ‖ ^ 2 ≤
      (height K Sset e)⁻¹ * (C.slots.powerset.card : ℝ) *
        ∑ J ∈ C.slots.powerset, ‖assignedMark K S C r₁ r₂ b₁ b₂ side e J‖ ^ 2 *
          ‖residualBranch K S D Γ C G J (firstTriple K S r₁ r₂ b₁ b₂ e)
            (retainedLabel K S r₁ r₂ b₁ b₂).val.val d
            ((firstRow K S r₁ r₂ b₁ b₂ f z).val.val,ξ) W (-(1 / 2 : ℝ)) τ
            (extractedHeight K S r₁ r₂ b₁ b₂ side e) X.val
            (quotientScale K S X r₁ r₂ b₁ b₂ side e)‖ ^ 2 := by
  rw [sourceColumn, first_column_eq_branches K S D Γ hallowed C G hG X hCX
    r₁ r₂ b₁ b₂ side f z d ξ e he W hCW τ hprime]
  rw [norm_mul, mul_pow, norm_mul, norm_columnPhase, mul_one]
  have hs := pow_le_pow_left₀ (norm_nonneg _)
    (extractedScalar_norm_le K S D Γ C G r₁ r₂ b₁ b₂ side f z d ξ e) 2
  rw [normWeight_sq K S] at hs
  have hc := finite_square_cauchy C.slots.powerset (fun J =>
    assignedMark K S C r₁ r₂ b₁ b₂ side e J *
      residualBranch K S D Γ C G J (firstTriple K S r₁ r₂ b₁ b₂ e)
        (retainedLabel K S r₁ r₂ b₁ b₂).val.val d
        ((firstRow K S r₁ r₂ b₁ b₂ f z).val.val,ξ) W (-(1 / 2 : ℝ)) τ
        (extractedHeight K S r₁ r₂ b₁ b₂ side e) X.val
        (quotientScale K S X r₁ r₂ b₁ b₂ side e))
  simp only [norm_mul, mul_pow] at hc
  exact (mul_le_mul hs hc (sq_nonneg _) (inv_nonneg.mpr (height_pos K Sset e).le)).trans_eq
    (by ring)

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstColumnEnergy

end

