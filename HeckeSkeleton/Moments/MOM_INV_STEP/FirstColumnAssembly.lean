import HeckeSkeleton.Moments.MOM_INV_STEP.FirstOverlapColumns
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstCompletePools
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstCompleteFamily

/-!
# Actual first inverse branches and literal complete canonical families

The zero sets of the genuine retained label and cube mask restore the
original prime lists.  The extracted first overlap becomes the second
factor of the common puncture.  All rows, including every original unit
sector and the literal first mask divisor, are preserved.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstColumnAssembly

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FirstSourceColumns FirstSourceFrozen CanonicalFirstSource CanonicalFirstEnergy
  FirstOverlapColumns FirstCompletePools FirstSourceDecomposition FixedTripleFibers
  CanonicalChildren CanonicalNormPools
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "E" => CanonicalIdealRow.exteriorMonoid K S
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

def firstTriple (r₁ r₂ b₁ b₂ e : Ext) : OuterTriple K :=
  ⟨(CanonicalCubeLabels.q0 K S b₁ b₂
    (CanonicalConductor.squarefreeBit K S r₁) (CanonicalConductor.squarefreeBit K S r₂)).val.val,
    e.val.val, 1⟩

def retainedLabel (r₁ r₂ b₁ b₂ : Ext) : E :=
  commonFactor K S r₁ r₂ b₁ b₂ * CanonicalCubeLabels.J K S b₁ b₂
    (CanonicalConductor.squarefreeBit K S r₁) (CanonicalConductor.squarefreeBit K S r₂)

def firstRow (r₁ r₂ b₁ b₂ : Ext) (f z : E) : E :=
  z * f ^ 2 * CanonicalCubeLabels.dilation K S b₁ b₂
    (CanonicalConductor.squarefreeBit K S r₁) (CanonicalConductor.squarefreeBit K S r₂)

variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)

include hallowed in
theorem symbol_generator_live (u : Ext) (I : E)
    (h : idealSymbol K Sset D u (CanonicalIdealRow.generator K S D I) ≠ 0) :
    IsCoprime u.val.val I.val.val := by
  have hm := CanonicalIdealRow.row_mask K S D hallowed u I
  simp only [CubeAlgebra.sixthMask, CanonicalIdealRow.row_apply] at hm
  by_contra hc
  rw [if_neg hc] at hm
  exact h ((pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)).mp hm)

include hallowed in
/-- Nonvanishing of the actual inverse row forces avoidance of the
whole original cube and the frozen common factor. -/
theorem fixed_live_coprime (ν G : HeckeCharacter K)
    (r₁ r₂ b₁ b₂ : Ext) (f z : E) (d : OS) (ξ : Sector) (u : Ext)
    (hlive : fixedSectorCoefficient K S D Γ ν G r₁ r₂ b₁ b₂ f z d ξ u ≠ 0) :
    IsCoprime u.val.val (b₁.val.val * b₂.val.val) ∧
      IsCoprime u.val.val (commonFactor K S r₁ r₂ b₁ b₂).val.val := by
  have hq : IsCoprime u.val.val (CanonicalCubeLabels.q0 K S b₁ b₂
      (CanonicalConductor.squarefreeBit K S r₁) (CanonicalConductor.squarefreeBit K S r₂)).val.val := by
    by_contra hc
    apply hlive
    simp only [fixedSectorCoefficient, fixedMultiplierCoefficient, fixedInverseCoefficient,
      if_neg hc, mul_zero, zero_mul]
  have hj : idealSymbol K Sset D u
      (CanonicalIdealRow.generator K S D (retainedLabel K S r₁ r₂ b₁ b₂)) ≠ 0 := by
    intro hz
    apply hlive
    simp only [fixedSectorCoefficient, fixedMultiplierCoefficient, fixedInverseCoefficient,
      retainedLabel] at hz ⊢
    rw [hz]
    simp only [zero_pow (by decide : (4 : ℕ) ≠ 0), zero_mul, mul_zero]
  have hlabel := symbol_generator_live K S D hallowed u _ hj
  change IsCoprime u.val.val
    ((commonFactor K S r₁ r₂ b₁ b₂).val.val *
      (CanonicalCubeLabels.J K S b₁ b₂ (CanonicalConductor.squarefreeBit K S r₁)
        (CanonicalConductor.squarefreeBit K S r₂)).val.val) at hlabel
  have hJ := hlabel.of_mul_right_right
  rw [CanonicalCubeLabels.q0_val] at hq
  rw [CanonicalCubeLabels.J_val, CubeLabels.J_eq_s_mul_J2] at hJ
  refine ⟨?_, hlabel.of_mul_right_left⟩
  rw [CubeLabels.actual_cube_decomposition b₁.val b₂.val
    (CanonicalConductor.squarefreeBit K S r₁) (CanonicalConductor.squarefreeBit K S r₂)]
  exact (hq.pow_right.mul_right hJ.of_mul_right_right.pow_right).mul_right
    hJ.of_mul_right_left

include hallowed in
theorem fixed_live_avoids (ν G : HeckeCharacter K)
    (r₁ r₂ b₁ b₂ : Ext) (f z : E) (d : OS) (ξ : Sector) (u : Ext)
    (hlive : fixedSectorCoefficient K S D Γ ν G r₁ r₂ b₁ b₂ f z d ξ u ≠ 0) :
    Disjoint (primeSupport u.val) (blockedSupport K S r₁ r₂ b₁ b₂) := by
  obtain ⟨hB, hC⟩ := fixed_live_coprime K S D Γ hallowed ν G r₁ r₂ b₁ b₂ f z d ξ u hlive
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hpu := (mem_primeSupport u.val p).mp hp
  rcases Finset.mem_union.mp hq with hq | hq
  · exact p.prime.not_unit (hB.isUnit_of_dvd' hpu
      ((mem_primeSupport (b₁.val * b₂.val) p).mp hq))
  · have hpc : p.asIdeal ∣ (commonFactor K S r₁ r₂ b₁ b₂).val.val :=
      Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum (𝓞 K) => q.asIdeal) hq
    exact p.prime.not_unit (hC.isUnit_of_dvd' hpu hpc)

include hallowed in
theorem fixed_live_markBase_coprime (ν G : HeckeCharacter K)
    (r₁ r₂ b₁ b₂ : Ext) (side : Bool) (f z : E) (d : OS) (ξ : Sector) (e u : Ext)
    (he : IsCoprime e.val.val u.val.val)
    (hlive : fixedSectorCoefficient K S D Γ ν G r₁ r₂ b₁ b₂ f z d ξ u ≠ 0) :
    IsCoprime u.val.val (markBase K S r₁ r₂ b₁ b₂ side e) := by
  obtain ⟨hB, hC⟩ := fixed_live_coprime K S D Γ hallowed ν G r₁ r₂ b₁ b₂ f z d ξ u hlive
  have hA : IsCoprime u.val.val
      (IdealMobiusMask.primeProduct (extractedSupportSide K S r₁ r₂ b₁ b₂ side)) := by
    apply IsCoprime.prod_right
    intro p hp
    exact hB.of_isCoprime_of_dvd_right ((mem_primeSupport (b₁.val * b₂.val) p).mp
      (extractedSupportSide_subset K S r₁ r₂ b₁ b₂ side hp))
  have hE : IsCoprime u.val.val (extractedFactor K S r₁ r₂ b₁ b₂ side).val.val := by
    rw [extractedFactor_support_product K S D]
    exact hA.mul_right hC
  have hb : IsCoprime u.val.val (sourceIdeal K S b₁ b₂ side).val.val := by
    cases side
    · exact hB.of_mul_right_left
    · exact hB.of_mul_right_right
  exact (hb.pow_right.mul_right hE).mul_right he.symm

variable {σ : Type*} [DecidableEq σ]

theorem original_marks_on_coprime (slots : Finset σ)
    (lists : σ → Finset (Ideal (𝓞 K))) (a : σ → Ideal (𝓞 K) → ℂ)
    (hprime : ∀ i ∈ slots, ∀ p ∈ lists i, Prime p)
    (I₀ n : Ideal (𝓞 K)) (hc : IsCoprime n I₀) :
    divisorMark slots (residualDivisorLists I₀ lists) a n = divisorMark slots lists a n := by
  unfold divisorMark
  apply Finset.prod_congr rfl
  intro i hi
  change (∑ p ∈ (lists i).filter (fun p => ¬p ∣ I₀), if p ∣ n then a i p else 0) = _
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro p hp hnot
  have hE : p ∣ I₀ := by
    by_contra h
    exact hnot (Finset.mem_filter.mpr ⟨hp, h⟩)
  have hn : ¬p ∣ n := fun hd => (hprime i hi p hp).not_unit (hc.isUnit_of_dvd' hd hE)
  exact if_neg hn

/-- The bare canonical coefficient is the literal fixed inverse row,
with precisely the original puncture and the first overlap mask. -/
theorem bareCoefficient_eq (C : CanonicalBlock.ColumnData K S σ) (G : HeckeCharacter K)
    (hG : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset → UnramifiedAt K G p)
    (r₁ r₂ b₁ b₂ : Ext) (f z : E) (d : OS) (ξ : Sector) (e u : Ext) (J : Finset σ) :
    FirstCompleteFamily.bareCoefficient K S D Γ C G J (firstTriple K S r₁ r₂ b₁ b₂ e)
      (retainedLabel K S r₁ r₂ b₁ b₂).val.val d
      ((firstRow K S r₁ r₂ b₁ b₂ f z).val.val, ξ) u =
      fixedSectorCoefficient K S D Γ C.background G r₁ r₂ b₁ b₂ f z d ξ u *
        (if IsCoprime u.val.val C.puncture then 1 else 0) *
        (if IsCoprime u.val.val e.val.val then 1 else 0) *
        divisorMark (C.slots \ J) C.primeLists C.primeWeights u.val.val := by
  cases Subsingleton.elim ‹DecidableEq σ› (Classical.typeDecidableEq σ)
  have hmask := childPuncture_mask C.puncture u.val.val (firstTriple K S r₁ r₂ b₁ b₂ e)
  simp only [idealCoprimeMask, firstTriple, isCoprime_one_right, if_true, mul_one] at hmask
  unfold FirstCompleteFamily.bareCoefficient
  rw [BackgroundCycle.exterior_coefficient_mul K Sset C.background G hG u]
  erw [hmask]
  rw [show (retainedLabel K S r₁ r₂ b₁ b₂).val.val =
    (CanonicalIdealRow.toExterior K S (retainedLabel K S r₁ r₂ b₁ b₂)).val.val from rfl,
    labelRow_exterior]
  rw [show (firstRow K S r₁ r₂ b₁ b₂ f z).val.val =
    (CanonicalIdealRow.toExterior K S (firstRow K S r₁ r₂ b₁ b₂ f z)).val.val from rfl,
    sectorRow_exterior, CanonicalPoissonSource.idealSymbol_mul]
  unfold fixedSectorCoefficient fixedMultiplierCoefficient fixedInverseCoefficient
    retainedLabel firstRow CanonicalIdealRow.generator
  simp only [map_mul, Complex.star_def]
  ring

include hallowed in
/-- Priority deletion and the overlap coprimality restriction are
both restored by actual zeros before the norm test is separated. -/
theorem residualTerm_restored (C : CanonicalBlock.ColumnData K S σ) (G : HeckeCharacter K)
    (hG : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset → UnramifiedAt K G p)
    (r₁ r₂ b₁ b₂ : Ext) (side : Bool) (f z : E) (d : OS) (ξ : Sector)
    (e u : Ext) (J : Finset σ)
    (hprime : ∀ i ∈ C.slots, ∀ p ∈ C.primeLists i, Prime p) :
    (if IsCoprime e.val.val u.val.val then
      residualTerm K S D Γ C G r₁ r₂ b₁ b₂ side f z d ξ e J u else 0) =
      normWeight K u.val *
        FirstCompleteFamily.bareCoefficient K S D Γ C G J (firstTriple K S r₁ r₂ b₁ b₂ e)
          (retainedLabel K S r₁ r₂ b₁ b₂).val.val d
          ((firstRow K S r₁ r₂ b₁ b₂ f z).val.val, ξ) u *
        C.cutoff (((extractedFactor K S r₁ r₂ b₁ b₂ side).val.val.absNorm : ℝ) *
          (e.val.val.absNorm : ℝ) * (u.val.val.absNorm : ℝ) / C.base ^ C.length) := by
  rw [bareCoefficient_eq K S D Γ C G hG]
  by_cases he : IsCoprime e.val.val u.val.val
  · rw [if_pos he, if_pos he.symm]
    by_cases hlive : fixedSectorCoefficient K S D Γ C.background G r₁ r₂ b₁ b₂ f z d ξ u = 0
    · simp only [residualTerm, hlive, mul_zero, zero_mul]
    · have hc := fixed_live_markBase_coprime K S D Γ hallowed C.background G
        r₁ r₂ b₁ b₂ side f z d ξ e u he hlive
      unfold residualTerm
      rw [original_marks_on_coprime K (C.slots \ J) C.primeLists C.primeWeights
        (fun i hi p hp => hprime i (Finset.mem_sdiff.mp hi).1 p hp) _ _ hc]
      ring
  · have he' : ¬IsCoprime u.val.val e.val.val := fun h => he h.symm
    simp only [if_neg he, if_neg he', mul_zero, zero_mul]

include hallowed in
theorem movingColumn_zero_outside (C : CanonicalBlock.ColumnData K S σ)
    (G : HeckeCharacter K) (r₁ r₂ b₁ b₂ : Ext) (side : Bool) (f z : E)
    (d : OS) (ξ : Sector) (u : Ext)
    (hbad : ¬Disjoint (primeSupport u.val) (blockedSupport K S r₁ r₂ b₁ b₂)) :
    movingColumn K S D Γ C G r₁ r₂ b₁ b₂ side f z d ξ u.val = 0 := by
  have hz : fixedSectorCoefficient K S D Γ C.background G r₁ r₂ b₁ b₂ f z d ξ u = 0 := by
    by_contra hlive
    exact hbad (fixed_live_avoids K S D Γ hallowed C.background G
      r₁ r₂ b₁ b₂ f z d ξ u hlive)
  simp only [movingColumn, extendExterior_val, fixedMarkedInverse, hz, zero_mul, mul_zero]

include hallowed in
/-- The complete original norm pool removes its frozen support filter
by genuine inverse-character zeros, before taking absolute values. -/
theorem source_sum_complete (C : CanonicalBlock.ColumnData K S σ)
    (G : HeckeCharacter K) (X : {r : ℝ // 0 < r})
    (r₁ r₂ b₁ b₂ : Ext) (side : Bool) (f z : E) (d : OS) (ξ : Sector)
    (e : Ext) (P : (Ideal (𝓞 K))⁰ → ℂ) :
    (∑ U ∈ FirstNormPoolEnergy.sideDomain K S (dyadicPool K Sset X.val)
        r₁ r₂ b₁ b₂ side,
      if e.val.val ∣ IdealMobiusMask.primeProduct U then
        movingColumn K S D Γ C G r₁ r₂ b₁ b₂ side f z d ξ
          (FirstSourceReindexing.nonzeroProduct U) * P (FirstSourceReindexing.nonzeroProduct U)
      else 0) =
      ∑ u ∈ dyadicPool K Sset
          (FirstNormPoolEnergy.residualScale K S X r₁ r₂ b₁ b₂ side).val
          with e.val.val ∣ u.val.val,
        movingColumn K S D Γ C G r₁ r₂ b₁ b₂ side f z d ξ u.val * P u.val := by
  calc
    _ = ∑ u ∈ residualPool K S X r₁ r₂ b₁ b₂ side,
        if e.val.val ∣ u.val.val then
          movingColumn K S D Γ C G r₁ r₂ b₁ b₂ side f z d ξ u.val * P u.val else 0 := by
      simpa only [FirstSourceReindexing.nonzeroProduct] using
        (sum_sideDomain K S D X r₁ r₂ b₁ b₂ side
          (fun n : (Ideal (𝓞 K))⁰ => if e.val.val ∣ n.val then
            movingColumn K S D Γ C G r₁ r₂ b₁ b₂ side f z d ξ n * P n else 0))
    _ = _ := by
      unfold residualPool
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro u hu
      by_cases hc : Disjoint (primeSupport u.val) (blockedSupport K S r₁ r₂ b₁ b₂)
      · simp only [if_pos hc]
      · rw [if_neg hc, movingColumn_zero_outside K S D Γ hallowed C G
          r₁ r₂ b₁ b₂ side f z d ξ u hc]
        simp only [zero_mul, ite_self]

include hallowed in
theorem movingColumn_complete (C : CanonicalBlock.ColumnData K S σ) (G : HeckeCharacter K)
    (hG : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset → UnramifiedAt K G p)
    (r₁ r₂ b₁ b₂ : Ext) (side : Bool) (f z : E) (d : OS) (ξ : Sector)
    (e u : Ext) (hprime : ∀ i ∈ C.slots, ∀ p ∈ C.primeLists i, Prime p) :
    (if IsCoprime e.val.val u.val.val then
      movingColumn K S D Γ C G r₁ r₂ b₁ b₂ side f z d ξ (exteriorMul K Sset e u).val
      else 0) =
      extractedScalar K S D Γ C G r₁ r₂ b₁ b₂ side f z d ξ e *
        ∑ J ∈ C.slots.powerset, assignedMark K S C r₁ r₂ b₁ b₂ side e J *
          (normWeight K u.val *
            FirstCompleteFamily.bareCoefficient K S D Γ C G J (firstTriple K S r₁ r₂ b₁ b₂ e)
              (retainedLabel K S r₁ r₂ b₁ b₂).val.val d
              ((firstRow K S r₁ r₂ b₁ b₂ f z).val.val, ξ) u *
            C.cutoff (((extractedFactor K S r₁ r₂ b₁ b₂ side).val.val.absNorm : ℝ) *
              (e.val.val.absNorm : ℝ) * (u.val.val.absNorm : ℝ) / C.base ^ C.length)) := by
  calc
    _ = extractedScalar K S D Γ C G r₁ r₂ b₁ b₂ side f z d ξ e *
        ∑ J ∈ C.slots.powerset, assignedMark K S C r₁ r₂ b₁ b₂ side e J *
          (if IsCoprime e.val.val u.val.val then
            residualTerm K S D Γ C G r₁ r₂ b₁ b₂ side f z d ξ e J u else 0) := by
      by_cases he : IsCoprime e.val.val u.val.val
      · simp only [if_pos he]
        exact movingColumn_mul K S D Γ C G r₁ r₂ b₁ b₂ side f z d ξ e u he hprime
      · simp only [if_neg he, mul_zero, Finset.sum_const_zero]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro J hJ
      rw [residualTerm_restored K S D Γ hallowed C G hG
        r₁ r₂ b₁ b₂ side f z d ξ e u J hprime]

def quotientScale (X : {r : ℝ // 0 < r}) (r₁ r₂ b₁ b₂ : Ext) (side : Bool)
    (e : Ext) : ℝ :=
  (FirstNormPoolEnergy.residualScale K S X r₁ r₂ b₁ b₂ side).val / height K Sset e

def extractedHeight (r₁ r₂ b₁ b₂ : Ext) (side : Bool) (e : Ext) : ℝ :=
  ((extractedFactor K S r₁ r₂ b₁ b₂ side).val.val.absNorm : ℝ) * height K Sset e

theorem quotientScale_pos (X : {r : ℝ // 0 < r}) (r₁ r₂ b₁ b₂ : Ext)
    (side : Bool) (e : Ext) : 0 < quotientScale K S X r₁ r₂ b₁ b₂ side e :=
  div_pos (FirstNormPoolEnergy.residualScale K S X r₁ r₂ b₁ b₂ side).property
    (height_pos K Sset e)

theorem extractedHeight_pos (r₁ r₂ b₁ b₂ : Ext) (side : Bool) (e : Ext) :
    0 < extractedHeight K S r₁ r₂ b₁ b₂ side e := by
  apply mul_pos _ (height_pos K Sset e)
  exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors
    (extractedFactor K S r₁ r₂ b₁ b₂ side).val

/-- The true source scale, used to check the exact family before the
later uniform dyadic-center Mellin separation. -/
theorem exact_source_scale (X : {r : ℝ // 0 < r}) (r₁ r₂ b₁ b₂ : Ext)
    (side : Bool) (e : Ext) :
    X.val = extractedHeight K S r₁ r₂ b₁ b₂ side e *
      quotientScale K S X r₁ r₂ b₁ b₂ side e := by
  have hE : ((extractedFactor K S r₁ r₂ b₁ b₂ side).val.val.absNorm : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_pos_of_nonZeroDivisors
      (extractedFactor K S r₁ r₂ b₁ b₂ side).val).ne'
  unfold extractedHeight quotientScale FirstNormPoolEnergy.residualScale
  field_simp [hE, (height_pos K Sset e).ne']

theorem normWeight_power (u : Ext) :
    normWeight K u.val = ((height K Sset u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  rw [normWeight, height, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow,
    Complex.ofReal_inv]

theorem phase_at_product (τ Y : ℝ) (hY : 0 < Y) (e u : Ext) :
    CommonKernel.columnPhase τ
        (Real.log (height K Sset (exteriorMul K Sset e u) / Y)) =
      CommonKernel.columnPhase τ (Real.log (height K Sset e) - Real.log Y) *
        CommonKernel.columnPhase τ (Real.log (height K Sset u)) := by
  rw [height_mul, Real.log_div (mul_ne_zero (height_pos K Sset e).ne'
    (height_pos K Sset u).ne') hY.ne',
    Real.log_mul (height_pos K Sset e).ne' (height_pos K Sset u).ne']
  rw [show Real.log (height K Sset e) + Real.log (height K Sset u) - Real.log Y =
      (Real.log (height K Sset e) - Real.log Y) + Real.log (height K Sset u) by ring,
    MellinWeightedTests.columnPhase_add]

include hallowed in
/-- Complete actual source-to-branch assembly.  The original finite
support domain, actual overlap divisor, norm weight, marks and phase
appear on the left.  The right side is the literal canonical inverse
branch, with no arbitrary residual coefficients or source identities. -/
theorem first_column_eq_branches (C : CanonicalBlock.ColumnData K S σ)
    (G : HeckeCharacter K)
    (hG : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset → UnramifiedAt K G p)
    (X : {r : ℝ // 0 < r}) (hCX : C.base ^ C.length = X.val)
    (r₁ r₂ b₁ b₂ : Ext) (side : Bool) (f z : E) (d : OS) (ξ : Sector)
    (e : Ext) (he : Squarefree e.val.val) (W : SchwartzMap ℝ ℂ)
    (hCW : C.cutoff = W) (τ : ℝ)
    (hprime : ∀ i ∈ C.slots, ∀ p ∈ C.primeLists i, Prime p) :
    (∑ U ∈ FirstNormPoolEnergy.sideDomain K S (dyadicPool K Sset X.val)
        r₁ r₂ b₁ b₂ side,
      if e.val.val ∣ IdealMobiusMask.primeProduct U then
        movingColumn K S D Γ C G r₁ r₂ b₁ b₂ side f z d ξ
          (FirstSourceReindexing.nonzeroProduct U) *
          CommonKernel.columnPhase τ
            (Real.log (((IdealMobiusMask.primeProduct U).absNorm : ℝ) /
              (FirstNormPoolEnergy.residualScale K S X r₁ r₂ b₁ b₂ side).val))
      else 0) =
      (extractedScalar K S D Γ C G r₁ r₂ b₁ b₂ side f z d ξ e *
        CommonKernel.columnPhase τ (Real.log (height K Sset e) -
          Real.log (FirstNormPoolEnergy.residualScale K S X r₁ r₂ b₁ b₂ side).val)) *
        ∑ J ∈ C.slots.powerset, assignedMark K S C r₁ r₂ b₁ b₂ side e J *
          FirstCompleteFamily.residualBranch K S D Γ C G J
            (firstTriple K S r₁ r₂ b₁ b₂ e) (retainedLabel K S r₁ r₂ b₁ b₂).val.val d
            ((firstRow K S r₁ r₂ b₁ b₂ f z).val.val, ξ) W (-(1 / 2 : ℝ)) τ
            (extractedHeight K S r₁ r₂ b₁ b₂ side e) X.val
            (quotientScale K S X r₁ r₂ b₁ b₂ side e) := by
  let Y := (FirstNormPoolEnergy.residualScale K S X r₁ r₂ b₁ b₂ side).val
  have hY : 0 < Y := (FirstNormPoolEnergy.residualScale K S X r₁ r₂ b₁ b₂ side).property
  calc
    _ = ∑ u ∈ dyadicPool K Sset Y with e.val.val ∣ u.val.val,
        movingColumn K S D Γ C G r₁ r₂ b₁ b₂ side f z d ξ u.val *
          CommonKernel.columnPhase τ (Real.log (height K Sset u / Y)) := by
      simpa only [FirstSourceReindexing.nonzeroProduct, Y, height] using
        (source_sum_complete K S D Γ hallowed C G X r₁ r₂ b₁ b₂ side f z d ξ e
          (fun n : (Ideal (𝓞 K))⁰ => CommonKernel.columnPhase τ
            (Real.log ((n.val.absNorm : ℝ) / Y))))
    _ = _ := by
      rw [sum_dyadic_multiples K S Y e he
        (fun u : Ext => movingColumn K S D Γ C G r₁ r₂ b₁ b₂ side f z d ξ u.val *
          CommonKernel.columnPhase τ (Real.log (height K Sset u / Y)))]
      simp only [Finset.sum_filter]
      calc
        _ = ∑ u ∈ dyadicPool K Sset (Y / height K Sset e),
            (extractedScalar K S D Γ C G r₁ r₂ b₁ b₂ side f z d ξ e *
              ∑ J ∈ C.slots.powerset, assignedMark K S C r₁ r₂ b₁ b₂ side e J *
                (normWeight K u.val *
                  FirstCompleteFamily.bareCoefficient K S D Γ C G J
                    (firstTriple K S r₁ r₂ b₁ b₂ e) (retainedLabel K S r₁ r₂ b₁ b₂).val.val d
                    ((firstRow K S r₁ r₂ b₁ b₂ f z).val.val, ξ) u *
                  C.cutoff (((extractedFactor K S r₁ r₂ b₁ b₂ side).val.val.absNorm : ℝ) *
                    (e.val.val.absNorm : ℝ) * (u.val.val.absNorm : ℝ) / C.base ^ C.length))) *
              CommonKernel.columnPhase τ (Real.log (height K Sset (exteriorMul K Sset e u) / Y)) := by
          apply Finset.sum_congr rfl
          intro u hu
          have hh := congrArg (fun w : ℂ => w * CommonKernel.columnPhase τ
              (Real.log (height K Sset (exteriorMul K Sset e u) / Y)))
            (movingColumn_complete K S D Γ hallowed C G hG r₁ r₂ b₁ b₂ side f z d ξ e u hprime)
          simpa only [ite_mul, zero_mul, height] using hh
        _ = _ := by
          simp only [FirstCompleteFamily.residualBranch, quotientScale, Finset.mul_sum,
            Finset.sum_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro J hJ
          apply Finset.sum_congr rfl
          intro u hu
          rw [phase_at_product K S τ Y hY e u, normWeight_power K S u, hCW, hCX]
          unfold extractedHeight height
          ring

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstColumnAssembly

end
