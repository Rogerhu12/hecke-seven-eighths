import HeckeSkeleton.Moments.MOM_INV_STEP.SecondMellinEnergy
import HeckeSkeleton.Moments.MOM_INV_STEP.CoefficientBounds

/-!
# The actual second Moebius columns enter literal child energy

The left sides retain the fully extended second source, its fixed
original common ideal, the actual mutual divisor and original marks.
The complete quotient identity is followed by finite Cauchy on the
assigned slot subsets and genuine Mellin Cauchy at a fixed center.
Every assigned mark occurs squared, with the original individual
weights. The only scalar discarded is proved to have norm at most one.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondColumnEnergy

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools CommonKernel
  SecondOverlapColumns SecondCanonicalEnergy SecondCompleteColumns
  SecondCenteredFamily SecondMellinEnergy CoefficientBounds
open scoped Classical BigOperators nonZeroDivisors

private theorem finite_square_cauchy {ι : Type*} (T : Finset ι) (a : ι → ℂ) :
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
local notation "Ext" => ExteriorIdeal K Sset
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

theorem forwardCoefficient_norm_le_one (Λ ν G : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset D Λ G)
    (v f I : Ext) (ξ : Sector) (hv : Squarefree v.val.val) :
    ‖forwardCoefficient K S Γ D Λ ν v f I ξ‖ ≤ 1 := by
  have hν := norm_heckeIdealCoefficient_le_one K ν v.val
  have hf := idealSymbol_norm_le_one K S D v (D.generator f)
  have hI := idealSymbol_norm_le_one K S D v
    (CanonicalSectors.rowElement K Sset Γ D (I,ξ)).val
  unfold forwardCoefficient CanonicalSectorRows.sectorCharacter
  simp only [norm_mul, norm_pow, CoefficientCycle.canonicalCoefficient_norm hcal v hv,
    one_mul]
  calc
    _ ≤ 1 * (1 ^ 4 * 1) := by gcongr
    _ = 1 := by norm_num

theorem extractedScalar_norm_le_one (Λ ν G : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset D Λ G)
    (g j d₂ v I : Ext) (ξ : Sector) (R : Ideal (𝓞 K))
    (hv : Squarefree v.val.val) :
    ‖extractedScalar K S Γ D Λ ν g j d₂ v I ξ R‖ ≤ 1 := by
  rw [extractedScalar, norm_mul]
  exact mul_le_one₀
    (forwardCoefficient_norm_le_one K S D Γ Λ ν G hcal v _ I ξ hv)
    (norm_nonneg _) (norm_idealCoprimeMask_le_one _ _)

def productHeight (g v : Ext) : ℝ := height K Sset g * height K Sset v

theorem productHeight_pos (g v : Ext) : 0 < productHeight K S g v :=
  mul_pos (height_pos K Sset g) (height_pos K Sset v)

def quotientScale (X : ℝ) (g v : Ext) : ℝ := X / productHeight K S g v

theorem quotientScale_pos (X : ℝ) (hX : 0 < X) (g v : Ext) :
    0 < quotientScale K S X g v := div_pos hX (productHeight_pos K S g v)

theorem actual_scale (X : ℝ) (g v : Ext) :
    X = productHeight K S g v * quotientScale K S X g v := by
  unfold quotientScale
  field_simp [(productHeight_pos K S g v).ne']
  <;> ring

theorem phase_at_product (τ Y : ℝ) (hY : 0 < Y) (v u : Ext) :
    columnPhase τ (Real.log (height K Sset (exteriorMul K Sset v u) / Y)) =
      columnPhase τ (Real.log (height K Sset v) - Real.log Y) *
        columnPhase τ (Real.log (height K Sset u)) := by
  rw [height_mul, Real.log_div (mul_ne_zero (height_pos K Sset v).ne'
    (height_pos K Sset u).ne') hY.ne',
    Real.log_mul (height_pos K Sset v).ne' (height_pos K Sset u).ne']
  rw [show Real.log (height K Sset v) + Real.log (height K Sset u) - Real.log Y =
      (Real.log (height K Sset v) - Real.log Y) + Real.log (height K Sset u) by ring,
    MellinWeightedTests.columnPhase_add]

variable {σ : Type*} [DecidableEq σ] {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}

/-- The physical first family has the complete sf pool of cap 2X.
After its actual common g is extracted this is precisely the pool
2X/N(g), before extracting the independent full-Moebius divisor v. -/
def sourceColumn (C : ColumnFamily K Sset σ Θ ψ) (γ₀ : OuterTriple K)
    (G : HeckeCharacter K) (g j d₂ v I : Ext) (ξ : Sector)
    (W : SchwartzMap ℝ ℂ) (X τ : ℝ) : ℂ :=
  ∑ z ∈ squarefreePool K Sset (2 * X / height K Sset g) with v.val.val ∣ z.val.val,
    sourceTerm K S Γ D C.lambda (C.background γ₀ * G⁻¹) g j d₂ I ξ
      (childPuncture C.originalPuncture γ₀) (C.survivors γ₀) C.primeLists C.primeWeights
      W (X / height K Sset g) z *
        columnPhase τ (Real.log (height K Sset z / (X / height K Sset g)))

variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)

include hallowed in
/-- The actual source becomes literal branches at the full product
N(g)N(v); all dependence on g in the eventual length is thus exposed
before choosing the common product center. -/
theorem sourceColumn_eq_branches (C : ColumnFamily K Sset σ Θ ψ) (γ₀ : OuterTriple K)
    (G : HeckeCharacter K) (g j d₂ v I : Ext) (ξ : Sector)
    (hg : Squarefree g.val.val) (hd₂ : d₂.val.val ∣ g.val.val) (hv : Squarefree v.val.val)
    (W : SchwartzMap ℝ ℂ) (X τ : ℝ) (hX : 0 < X)
    (hprime : ∀ i ∈ C.survivors γ₀, ∀ p ∈ C.primeLists i, Prime p) :
    sourceColumn K S D Γ C γ₀ G g j d₂ v I ξ W X τ =
      (extractedScalar K S Γ D C.lambda (C.background γ₀ * G⁻¹) g j d₂ v I ξ
          (childPuncture C.originalPuncture γ₀) *
        columnPhase τ (Real.log (height K Sset v) - Real.log (X / height K Sset g))) *
        ∑ J ∈ (C.survivors γ₀).powerset,
          assignedMark K S g v C.primeLists C.primeWeights J *
            branch K S D Γ C γ₀ G J
              (appendResidual K γ₀ (residual K S g d₂).val.val)
              (finalLabel K S j d₂ v).val.val (I.val.val,ξ)
              W τ (productHeight K S g v) X (quotientScale K S X g v) := by
  have hY : 0 < X / height K Sset g := div_pos hX (height_pos K Sset g)
  have hpool : (2 * X / height K Sset g) / height K Sset v =
      2 * quotientScale K S X g v := by
    unfold quotientScale productHeight
    field_simp [(height_pos K Sset g).ne', (height_pos K Sset v).ne']
    <;> ring
  rw [sourceColumn, quotient_column_eq K S Γ D hallowed C.lambda
    (C.background γ₀ * G⁻¹) g j d₂ v I ξ hg hd₂ hv
    (childPuncture C.originalPuncture γ₀) (C.survivors γ₀) C.primeLists C.primeWeights
    hprime W (X / height K Sset g) (2 * X / height K Sset g)
    (fun z => columnPhase τ (Real.log (height K Sset z / (X / height K Sset g)))), hpool]
  let p := columnPhase τ
    (Real.log (height K Sset v) - Real.log (X / height K Sset g))
  have hbranch (J : Finset σ) :
      (∑ u ∈ squarefreePool K Sset (2 * quotientScale K S X g v),
        childTerm K S Γ D C.lambda (C.background γ₀ * G⁻¹) g j d₂ v I ξ
          (childPuncture C.originalPuncture γ₀) (C.survivors γ₀) J
          C.primeLists C.primeWeights W (X / height K Sset g) u *
          columnPhase τ (Real.log
            (height K Sset (exteriorMul K Sset v u) / (X / height K Sset g)))) =
        p * branch K S D Γ C γ₀ G J
          (appendResidual K γ₀ (residual K S g d₂).val.val)
          (finalLabel K S j d₂ v).val.val (I.val.val,ξ)
          W τ (productHeight K S g v) X (quotientScale K S X g v) := by
    rw [branch, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    rw [childTerm_eq K S D Γ C γ₀ G J g j d₂ v I u ξ W (X / height K Sset g),
      phase_at_product K S τ (X / height K Sset g) hY v u]
    have he : height K Sset v * height K Sset u / (X / height K Sset g) =
        productHeight K S g v * height K Sset u / X := by
      unfold productHeight
      field_simp [(height_pos K Sset g).ne', hX.ne']
      <;> ring
    rw [he]
    dsimp only [p]
    ring
  simp only [hbranch, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  dsimp only [p]
  ring

include hallowed in
/-- Finite Cauchy preserves every squared original assigned mark.
No arbitrary coefficient or source-to-child identity is assumed. -/
theorem sourceColumn_sq_le_branches (C : ColumnFamily K Sset σ Θ ψ) (γ₀ : OuterTriple K)
    (G : HeckeCharacter K) (hcal : ThetaCalibrationInput K Sset D C.lambda G)
    (g j d₂ v I : Ext) (ξ : Sector)
    (hg : Squarefree g.val.val) (hd₂ : d₂.val.val ∣ g.val.val) (hv : Squarefree v.val.val)
    (W : SchwartzMap ℝ ℂ) (X τ : ℝ) (hX : 0 < X)
    (hprime : ∀ i ∈ C.survivors γ₀, ∀ p ∈ C.primeLists i, Prime p) :
    ‖sourceColumn K S D Γ C γ₀ G g j d₂ v I ξ W X τ‖ ^ 2 ≤
      ((C.survivors γ₀).powerset.card : ℝ) *
        ∑ J ∈ (C.survivors γ₀).powerset,
          ‖assignedMark K S g v C.primeLists C.primeWeights J‖ ^ 2 *
            ‖branch K S D Γ C γ₀ G J
              (appendResidual K γ₀ (residual K S g d₂).val.val)
              (finalLabel K S j d₂ v).val.val (I.val.val,ξ)
              W τ (productHeight K S g v) X (quotientScale K S X g v)‖ ^ 2 := by
  rw [sourceColumn_eq_branches K S D Γ hallowed C γ₀ G g j d₂ v I ξ
    hg hd₂ hv W X τ hX hprime, norm_mul, mul_pow, norm_mul, norm_columnPhase, mul_one]
  have hs := pow_le_pow_left₀ (norm_nonneg _)
    (extractedScalar_norm_le_one K S D Γ C.lambda (C.background γ₀ * G⁻¹) G hcal
      g j d₂ v I ξ (childPuncture C.originalPuncture γ₀) hv) 2
  rw [one_pow] at hs
  have hc := finite_square_cauchy (C.survivors γ₀).powerset (fun J =>
    assignedMark K S g v C.primeLists C.primeWeights J *
      branch K S D Γ C γ₀ G J
        (appendResidual K γ₀ (residual K S g d₂).val.val)
        (finalLabel K S j d₂ v).val.val (I.val.val,ξ)
        W τ (productHeight K S g v) X (quotientScale K S X g v))
  simp only [norm_mul, mul_pow] at hc
  exact (mul_le_mul_of_nonneg_right hs (sq_nonneg _)).trans (by simpa only [one_mul] using hc)

include hallowed in
/-- Production estimate for the actual positive second source column.
The child pool and test use one scale U throughout an entire g*v box;
the original frequency and the Mellin frequency enter the same test.
All displayed integrals are integrable by SecondMellinEnergy. -/
theorem sourceColumn_sq_le_mellin (C : ColumnFamily K Sset σ Θ ψ) (γ₀ : OuterTriple K)
    (G : HeckeCharacter K) (hG : G ∈ Θ)
    (hcal : ThetaCalibrationInput K Sset D C.lambda G)
    (g j d₂ v I : Ext) (ξ : Sector)
    (hg : Squarefree g.val.val) (hd₂ : d₂.val.val ∣ g.val.val) (hv : Squarefree v.val.val)
    (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 / 8 : ℝ) (21 / 8))
    (X τ center U : ℝ) (hX : 0 < X) (hZ : 1 < C.base) (hcenter : 0 < center) (hU : 0 < U)
    (hlo : center ≤ productHeight K S g v) (hhi : productHeight K S g v ≤ 4 * center)
    (hscale : X = center * U)
    (hprime : ∀ i ∈ C.survivors γ₀, ∀ p ∈ C.primeLists i, Prime p) :
    ‖sourceColumn K S D Γ C γ₀ G g j d₂ v I ξ W X τ‖ ^ 2 ≤
      (((C.survivors γ₀).powerset.card : ℝ) * mellinMass W hW) *
        ∑ J ∈ (C.survivors γ₀).powerset,
          ‖assignedMark K S g v C.primeLists C.primeWeights J‖ ^ 2 *
            columnEnergy K S D Γ C γ₀ G hG J U
              (appendResidual K γ₀ (residual K S g d₂).val.val)
              (finalLabel K S j d₂ v).val.val (I.val.val,ξ) W hW τ := by
  apply (sourceColumn_sq_le_branches K S D Γ hallowed C γ₀ G hcal g j d₂ v I ξ
    hg hd₂ hv W X τ hX hprime).trans
  calc
    _ ≤ ((C.survivors γ₀).powerset.card : ℝ) *
        ∑ J ∈ (C.survivors γ₀).powerset,
          ‖assignedMark K S g v C.primeLists C.primeWeights J‖ ^ 2 *
            (mellinMass W hW * columnEnergy K S D Γ C γ₀ G hG J U
              (appendResidual K γ₀ (residual K S g d₂).val.val)
              (finalLabel K S j d₂ v).val.val (I.val.val,ξ) W hW τ) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro J hJ
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact branch_sq_le K S D Γ C γ₀ G hG J U
        (appendResidual K γ₀ (residual K S g d₂).val.val)
        (finalLabel K S j d₂ v).val.val (I.val.val,ξ) W hW
        τ center (productHeight K S g v) X (quotientScale K S X g v)
        hZ hcenter (quotientScale_pos K S X hX g v) hU hlo hhi
        (actual_scale K S X g v) hscale
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro J hJ
      ring

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondColumnEnergy

end
