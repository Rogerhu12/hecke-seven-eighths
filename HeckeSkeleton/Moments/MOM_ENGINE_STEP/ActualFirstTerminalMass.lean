import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstTerminalIndexMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCommonLabelConditions
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstSourceFiniteLeaves
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstBlockMaskCardinality

/-!
# The original first-label mass of the real zero and tail budgets

The carrier here is literally the original first common pair, its
original mask subset, its original shared divisor and finite character.
The first two Cauchy allowances give the exact `firstCommonWeight` and
the coefficient-atom calibration gives `1/N(S)`.

The shared-divisor norm window is proved from its actual original
residual ideal, and every common ideal is bounded by an original column.
Mask cardinalities are proved from their original prime identifications.
No estimate of a final terminal sum or of a surrogate carrier is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open DedekindZetaZeroFree.LargeSieve
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support HeckePort.Moments.MobiusRegroup
open HeckePort.IdealMobiusDivisorSum CommonSupportMass UniqueFactorizationMonoid MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
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
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U]
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}
variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
local instance actualFirstTerminalMassCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

namespace ActualFirstSource

variable (s : ActualFirstSource (E := U) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX)

/-- These are exactly the finite labels already present in
`SecondStages.TerminalCalibration.classZeroBudget` and `classTailBudget`. -/
def firstTerminalArithmeticMass : ℝ :=
  ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
    ∑ S : divisorPool (s.pools v D).rightData.columns
      (fun j => ((s.pools v D).rightData.ideal j).val),
    ∑ χ : (PUnit × PUnit) →* Circle,
      firstCommonWeight Z v.val.1 v.val.2 *
        (‖(moebius S.val : ℂ)‖ / (Ideal.absNorm S.val : ℝ)) *
          ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖

theorem first_divisor_original_norm
    (v : s.CommonLabel) (D : ((s.block v).mask s.mask).powerset)
    (S : divisorPool (s.pools v D).rightData.columns
      (fun j => ((s.pools v D).rightData.ideal j).val))
    (Y : ℝ) (hcolumns : ∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Y) :
    (Ideal.absNorm S.val : ℝ) ≤ Y := by
  obtain ⟨j, hj, hSj⟩ := Finset.mem_biUnion.mp S.property
  have hdiv := (mem_idealDivisors ((s.pools v D).rightData.ideal j).property.1).mp hSj
  have hj' : j ∈ (s.block v).rightColumns s.columns := by
    rwa [(s.pools v D).right_columns] at hj
  have hresidual : ((s.pools v D).rightData.ideal j).val ∣ (s.ideal j).val := by
    rw [(s.pools v D).right_ideal, (s.block v).right_residual]
    exact ⟨supportExtract (s.ideal j).val (primeSupport v.val.1), by
      rw [mul_comm]
      exact (support_reconstruct _ (s.ideal j).property.1 _).symm⟩
  exact (norm_le_of_dvd (s.ideal j).property.1 (hdiv.trans hresidual)).trans
    (hcolumns j (Finset.mem_filter.mp hj').1)

private theorem commonWeight_sum_le_actualLabels :
    (∑ v : s.CommonLabel, firstCommonWeight Z v.val.1 v.val.2) ≤
      ∑ v ∈ actualCommonLabels s.columns s.columns
        (fun i => (s.ideal i).val) (fun j => (s.ideal j).val),
        firstCommonWeight Z v.1.1 v.1.2 := by
  let base : Finset (Label K) := s.CommonLabel.image (fun DE => (DE, ∅))
  have hinj : Function.Injective (fun DE : Ideal (𝓞 K) × Ideal (𝓞 K) =>
      (DE, (∅ : Finset (Ideal (𝓞 K))))) := by
    intro x y h
    exact congrArg Prod.fst h
  have hsum : (∑ v : s.CommonLabel, firstCommonWeight Z v.val.1 v.val.2) =
      ∑ v ∈ base, firstCommonWeight Z v.1.1 v.1.2 := by
    rw [Finset.sum_coe_sort, Finset.sum_image]
    · rfl
    · exact fun x _ y _ h => hinj h
  have hsub : base ⊆ actualCommonLabels s.columns s.columns
      (fun i => (s.ideal i).val) (fun j => (s.ideal j).val) := by
    intro v hv
    obtain ⟨DE, hDE, rfl⟩ := Finset.mem_image.mp hv
    exact (mem_actualCommonLabels _ _ _ _ _).mpr ⟨hDE, Finset.empty_subset _⟩
  rw [hsum]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun v _ _ => Real.rpow_nonneg (zero_le_one.trans P.base_gt_one.le) _)

end ActualFirstSource

/-- All three arithmetic constants are fixed before the actual source,
mask ideals, scale and finite labels.  Original prime data proves the
mask cost; no cardinality or terminal-mass bound is assumed. -/
theorem actual_first_terminal_mass_from_original_windows
    (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ Cmass : ℝ, 0 < Cmass ∧
      ∀ (Z ell eps : ℝ) (bad : Finset (HeightOneSpectrum (𝓞 K)))
        (P : PowerScaleExteriorPool A bad Z ell eps),
      ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ)
        (a : RealParameters) (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X),
      ∀ s : ActualFirstSource (E := U) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX,
      ∀ oldMask : Ideal (𝓞 K), Squarefree oldMask → oldMask ≠ 0 →
      (∀ i ∈ s.columns, oldMask ∣ (s.ideal i).val) →
      (∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ B) →
      ∀ maskIdeal : Ideal (𝓞 K), maskIdeal ≠ 0 →
      (Ideal.absNorm maskIdeal : ℝ) ≤ Z ^ B →
      OriginalMaskPrimeData s.mask maskIdeal →
        s.firstTerminalArithmeticMass ≤
          Cmass * Z ^ ε / (Ideal.absNorm oldMask : ℝ) := by
  let δ : ℝ := ε / 3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨Ccommon, hCcommon, hcommon⟩ := actual_first_common_mass (K := K) B δ hB hδ
  obtain ⟨Cdivisor, hCdivisor, hdivisor⟩ := ideal_inverse_norm_subpower (K := K) B δ hB hδ
  obtain ⟨Cmask, hCmask, hmask⟩ := first_block_mask_labels_subpower (K := K) B δ hB hδ
  let phaseCard : ℝ := Fintype.card ((PUnit × PUnit) →* Circle)
  have hphaseCard : 0 < phaseCard := by
    exact_mod_cast (Fintype.card_pos (α := (PUnit × PUnit) →* Circle))
  refine ⟨Ccommon * Cdivisor * Cmask * phaseCard, by positivity, ?_⟩
  intro Z ell eps bad P ω ψ centered d a t Y₁ Y₂ X hX s oldMask hsq hmask0 hdiv hnorm
    maskIdeal hmaskIdeal0 hmaskIdealN hmaskPrimes
  have hz : 0 < Z := zero_lt_one.trans P.base_gt_one
  have hphase : (∑ χ : (PUnit × PUnit) →* Circle,
      ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖) ≤ phaseCard := by
    calc
      _ ≤ ∑ _χ : (PUnit × PUnit) →* Circle, (1 : ℝ) :=
        Finset.sum_le_sum fun χ _ => fixed_phase_coefficient_norm PUnit (fun _ => (1 : Circle)) χ
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, phaseCard]
  have hinner (v : s.CommonLabel) (D : ((s.block v).mask s.mask).powerset) :
      (∑ S : divisorPool (s.pools v D).rightData.columns
        (fun j => ((s.pools v D).rightData.ideal j).val),
        ∑ χ : (PUnit × PUnit) →* Circle,
          firstCommonWeight Z v.val.1 v.val.2 *
            (‖(moebius S.val : ℂ)‖ / (Ideal.absNorm S.val : ℝ)) *
              ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖) ≤
        firstCommonWeight Z v.val.1 v.val.2 * (Cdivisor * Z ^ δ) * phaseCard := by
    have hS :
        (∑ S : divisorPool (s.pools v D).rightData.columns
          (fun j => ((s.pools v D).rightData.ideal j).val),
            ‖(moebius S.val : ℂ)‖ / (Ideal.absNorm S.val : ℝ)) ≤ Cdivisor * Z ^ δ := by
      rw [Finset.sum_coe_sort]
      apply le_trans (Finset.sum_le_sum ?_)
        (hdivisor Z P.base_gt_one.le _ (first_divisor_pool_nonzero (s.pools v D).rightData)
          (fun S hS => s.first_divisor_original_norm v D ⟨S, hS⟩ _ hnorm))
      intro S _
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      unfold UniqueFactorizationMonoid.moebius
      split_ifs <;> simp
    calc
      _ = (firstCommonWeight Z v.val.1 v.val.2 *
          ∑ S : divisorPool (s.pools v D).rightData.columns
            (fun j => ((s.pools v D).rightData.ideal j).val),
            ‖(moebius S.val : ℂ)‖ / (Ideal.absNorm S.val : ℝ)) *
          ∑ χ : (PUnit × PUnit) →* Circle,
            ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖ := by
        simp_rw [← Finset.mul_sum]
        rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ _ := mul_le_mul
        (mul_le_mul_of_nonneg_left hS (Real.rpow_nonneg hz.le _)) hphase
        (Finset.sum_nonneg fun χ _ => norm_nonneg _)
        (mul_nonneg (Real.rpow_nonneg hz.le _) (mul_nonneg hCdivisor.le (Real.rpow_nonneg hz.le _)))
  have hmasks (v : s.CommonLabel) :
      (((s.block v).mask s.mask).powerset.card : ℝ) ≤ Cmask * Z ^ δ := by
    have hnorms := actualCommonLabels_norm s.columns s.columns
      (fun i => (s.ideal i).val) (fun j => (s.ideal j).val)
      (fun i _ => (s.ideal i).property.1) (fun i _ => (s.ideal i).property.1)
      (Z ^ B) hnorm hnorm (v.val, ∅)
      ((mem_actualCommonLabels _ _ _ _ _).mpr ⟨v.property, Finset.empty_subset _⟩)
    exact hmask Z P.base_gt_one.le (s.block v) s.mask maskIdeal
      hmaskIdeal0 hmaskIdealN hnorms.1 hmaskPrimes
  have hcommons : (∑ v : s.CommonLabel, firstCommonWeight Z v.val.1 v.val.2) ≤
      Ccommon * Z ^ δ / (Ideal.absNorm oldMask : ℝ) := by
    apply s.commonWeight_sum_le_actualLabels.trans
    exact hcommon Z P.base_gt_one oldMask hsq hmask0 _
      (actualCommonLabels_valid s.columns s.columns _ _ oldMask hsq
        (fun i _ => (s.ideal i).property.1) (fun i _ => (s.ideal i).property.1) hdiv hdiv)
      (actualCommonLabels_norm s.columns s.columns _ _
        (fun i _ => (s.ideal i).property.1) (fun i _ => (s.ideal i).property.1)
        (Z ^ B) hnorm hnorm)
  unfold ActualFirstSource.firstTerminalArithmeticMass
  calc
    _ ≤ ∑ v : s.CommonLabel, ∑ _D : ((s.block v).mask s.mask).powerset,
        firstCommonWeight Z v.val.1 v.val.2 * (Cdivisor * Z ^ δ) * phaseCard :=
      Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun D _ => hinner v D
    _ ≤ ∑ v : s.CommonLabel, (Cmask * Z ^ δ) *
        (firstCommonWeight Z v.val.1 v.val.2 * (Cdivisor * Z ^ δ) * phaseCard) := by
      apply Finset.sum_le_sum
      intro v _
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (hmasks v) (by
        exact mul_nonneg
          (mul_nonneg (Real.rpow_nonneg hz.le _)
            (mul_nonneg hCdivisor.le (Real.rpow_nonneg hz.le _))) hphaseCard.le)
    _ = (Cmask * Z ^ δ) * ((Cdivisor * Z ^ δ) * phaseCard) *
        (∑ v : s.CommonLabel, firstCommonWeight Z v.val.1 v.val.2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ ≤ (Cmask * Z ^ δ) * ((Cdivisor * Z ^ δ) * phaseCard) *
        (Ccommon * Z ^ δ / (Ideal.absNorm oldMask : ℝ)) :=
      mul_le_mul_of_nonneg_left hcommons (by positivity)
    _ = _ := by
      have he : ε = δ + δ + δ := by dsimp [δ]; ring
      rw [he, Real.rpow_add hz, Real.rpow_add hz]
      ring

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.first_divisor_original_norm
#print axioms HeckeSkeleton.Moments.EngineStep.actual_first_terminal_mass_from_original_windows
