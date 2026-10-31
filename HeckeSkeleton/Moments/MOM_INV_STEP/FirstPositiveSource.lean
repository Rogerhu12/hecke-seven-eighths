import HeckeSkeleton.Moments.MOM_INV_STEP.FirstCenteredColumnEnergy
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstMobiusGeometry

/-!
# Exact positive first-source energies on both sides

The right column is conjugated, so its actual Fourier frequency is
negated before applying the same canonical-column construction. Every
full Möbius divisor is converted to its proved exterior ideal.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstPositiveSource

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
  MeasureTheory
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalBlock CanonicalNormPools
  FirstSourceReindexing FirstNormPoolEnergy CanonicalFirstEnergy FirstColumnEnergy
  FirstMobiusGeometry CommonKernel
open scoped Classical BigOperators nonZeroDivisors ComplexConjugate

theorem columnPhase_neg (τ x : ℝ) : columnPhase (-τ) x = conj (columnPhase τ x) := by
  simp only [columnPhase, inner_neg_left, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

theorem conjugated_column_norm {ι : Type*} (T : Finset ι)
    (p : ι → Prop) [DecidablePred p] (a : ι → ℂ) (x : ι → ℝ) (τ : ℝ) :
    ‖∑ i ∈ T, if p i then conj (a i) * columnPhase τ (x i) else 0‖ =
      ‖∑ i ∈ T, if p i then a i * columnPhase (-τ) (x i) else 0‖ := by
  have he : (∑ i ∈ T, if p i then conj (a i) * columnPhase τ (x i) else 0) =
      conj (∑ i ∈ T, if p i then a i * columnPhase (-τ) (x i) else 0) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp only [map_mul, columnPhase_neg, Complex.conj_conj, map_zero]
  rw [he, Complex.norm_conj]

def coordinate (side : Bool) (ξ : LogPlane) : ℝ := if side then ξ.snd else ξ.fst

def signedCoordinate (side : Bool) (ξ : LogPlane) : ℝ :=
  if side then -ξ.snd else ξ.fst

theorem signedCoordinate_continuous (side : Bool) : Continuous (signedCoordinate side) := by
  cases side
  · exact logCoordinates.continuous.fst
  · exact logCoordinates.continuous.snd.neg

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "E" => CanonicalIdealRow.exteriorMonoid K S
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ
variable {σ : Type*}

def sourceEnergy (C : ColumnData K S σ) (G : HeckeCharacter K)
    (P : Profile K S) (X : {r : ℝ // 0 < r})
    (r₁ r₂ b₁ b₂ : Ext) (side : Bool) (f z : E) (d : OS) (ξ : Sector) : ℝ :=
  positiveEnergy K S Γ P
    (leftDomain K S (dyadicPool K Sset X.val) r₁ r₂ b₁ b₂)
    (sideDomain K S (dyadicPool K Sset X.val) r₁ r₂ b₁ b₂ side)
    (residualScale K S X r₁ r₂ b₁ b₂ side) (coordinate side)
    (fun u => if side then conj (movingColumn K S D Γ C G r₁ r₂ b₁ b₂ side f z d ξ u)
      else movingColumn K S D Γ C G r₁ r₂ b₁ b₂ side f z d ξ u)

theorem actual_column_norm (C : ColumnData K S σ) (G : HeckeCharacter K)
    (X : {r : ℝ // 0 < r}) (r₁ r₂ b₁ b₂ : Ext) (side : Bool)
    (f z : E) (d : OS) (ξ : Sector) (e : Ext) (η : LogPlane) :
    ‖∑ U ∈ sideDomain K S (dyadicPool K Sset X.val) r₁ r₂ b₁ b₂ side
      with e.val.val ∣ IdealMobiusMask.primeProduct U,
      (if side then conj (movingColumn K S D Γ C G r₁ r₂ b₁ b₂ side f z d ξ
          (nonzeroProduct U))
        else movingColumn K S D Γ C G r₁ r₂ b₁ b₂ side f z d ξ (nonzeroProduct U)) *
        columnPhase (coordinate side η)
          (Real.log (normScale K (residualScale K S X r₁ r₂ b₁ b₂ side)
            (nonzeroProduct U)).val)‖ =
      ‖sourceColumn K S D Γ C G X r₁ r₂ b₁ b₂ side f z d ξ e (signedCoordinate side η)‖ := by
  cases side
  · simp only [sourceColumn, coordinate, signedCoordinate, Bool.false_eq_true, if_false,
      Finset.sum_filter, normScale, nonzeroProduct]
  · simp only [sourceColumn, coordinate, signedCoordinate, if_true,
      Finset.sum_filter, normScale, nonzeroProduct]
    exact conjugated_column_norm _ _ _ _ _

theorem sourceColumn_continuous (C : ColumnData K S σ) (G : HeckeCharacter K)
    (X : {r : ℝ // 0 < r}) (r₁ r₂ b₁ b₂ : Ext) (side : Bool)
    (f z : E) (d : OS) (ξ : Sector) (e : Ext) :
    Continuous (fun τ => sourceColumn K S D Γ C G X r₁ r₂ b₁ b₂ side f z d ξ e τ) := by
  apply continuous_finsetSum
  intro U hU
  by_cases he : e.val.val ∣ IdealMobiusMask.primeProduct U
  · simp only [he, if_true]
    exact continuous_const.mul (continuous_columnPhase _)
  · simp only [he, if_false]
    exact continuous_const

theorem sourceEnergy_eq (C : ColumnData K S σ) (G : HeckeCharacter K)
    (P : Profile K S) (X : {r : ℝ // 0 < r}) (r₁ r₂ b₁ b₂ : Ext)
    (side : Bool) (f z : E) (d : OS) (ξ : Sector) :
    sourceEnergy K S D Γ C G P X r₁ r₂ b₁ b₂ side f z d ξ =
      ∑ e : overlapPool K S X r₁ r₂ b₁ b₂ false, ‖(UniqueFactorizationMonoid.moebius e.val : ℂ)‖ *
        ∫ η : LogPlane, ‖P.density K S Γ η‖ *
          ‖sourceColumn K S D Γ C G X r₁ r₂ b₁ b₂ side f z d ξ
            (overlapIdeal K S D X r₁ r₂ b₁ b₂ false e) (signedCoordinate side η)‖ ^ 2 := by
  unfold sourceEnergy positiveEnergy
  change (∑ e ∈ overlapPool K S X r₁ r₂ b₁ b₂ false, ‖(UniqueFactorizationMonoid.moebius e : ℂ)‖ * _) = _
  rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro e he
  congr 1
  apply integral_congr_ae
  filter_upwards [] with η
  rw [actual_column_norm K S D Γ C G X r₁ r₂ b₁ b₂ side f z d ξ
    (overlapIdeal K S D X r₁ r₂ b₁ b₂ false e) η]

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstPositiveSource

end

