import HeckeSkeleton.Moments.MOM_INV_STEP.DivisorInverseColumn
import ActualGramRowBallOrbitalMajorant

/-!
# A genuine fixed positive orbital majorant for the intermediate rows

The fixed compact Schwartz/finite-place test dominates every row of norm
at most H at radius H⁻¹. The positive row sum is enlarged to all original
Γ-orbits with external mask empty before the second Poisson transform.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.InverseRowMajorant

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton
  HeckeGeneral.ThetaSkeleton.Global MeasureTheory
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open HeckeSkeleton.Moments.MOMInvStep.FixedTripleFibers CanonicalChildren
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]

local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "Orbit" => SIntegerOrbits K Sset Γ
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

def rowRadius (H : {r : ℝ // 0 < r}) : {r : ℝ // 0 < r} :=
  ⟨H.val⁻¹, inv_pos.mpr H.property⟩

local instance sixthUnits_finiteIndex : Subgroup.FiniteIndex
    (Physical.sixthPowerUnits K (S : Set (HeightOneSpectrum (𝓞 K)))) :=
  sUnit_power_range_finiteIndex K (S : Set (HeightOneSpectrum (𝓞 K))) 6 (by decide)

def rowCovolume : ℝ :=
  (sUnitHaarCovolume K Sset (Physical.sixthPowerUnits K Sset)).toReal

theorem rowCovolume_pos : 0 < rowCovolume K S := rowBall_covolume_pos K S

def fixedProfile (H : {r : ℝ // 0 < r}) (q : Orbit) : ℝ :=
  (sUnitOrbitalProfile K Sset
    (sLocalTensorTestFunction K Sset (rowBallArchTest K S 1)
      (sIntegerFiniteTestFunction K S (rowBallFiniteFamily K S 1)))
    ⟨H.val⁻¹ * (sIntegerOrbitNorm K Sset Γ q).val,
      mul_pos (inv_pos.mpr H.property) (sIntegerOrbitNorm K Sset Γ q).property⟩).re

theorem fixedProfile_nonneg (H : {r : ℝ // 0 < r}) (q : Orbit) :
    0 ≤ fixedProfile K S Γ H q :=
  (rowBall_orbitalProfile_real_nonnegative K S 1 _).2

theorem fixedProfile_lower (H : {r : ℝ // 0 < r}) (q : Orbit)
    (hq : (sIntegerOrbitNorm K Sset Γ q).val ≤ H.val) :
    rowCovolume K S ≤ fixedProfile K S Γ H q := by
  apply rowBall_orbitalProfile_lower K S 1
  change H.val⁻¹ * (sIntegerOrbitNorm K Sset Γ q).val ≤ 1
  rw [inv_mul_eq_div]
  exact (div_le_one H.property).mpr hq

def amplitude (N : Finset Ext) (a : Ext → ℂ) (q : Orbit) : ℂ :=
  ∑ n ∈ N, a n * star (idealSymbol K Sset D n q.out.val)

theorem amplitude_norm_le (N : Finset Ext) (a : Ext → ℂ) (q : Orbit) :
    ‖amplitude K S Γ D N a q‖ ≤ ∑ n ∈ N, ‖a n‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_mul, norm_star]
  exact (mul_le_mul_of_nonneg_left
    (norm_sIntegerSexticIdealEvaluation_le_one K Sset D.root6 D.primitive6 D.embedding
      n.val.val (nonZeroDivisors.coe_ne_zero n.val) n.property
      (fun p hp => D.away_six p (n.property p hp)) q.out.val) (norm_nonneg _)).trans_eq
      (mul_one _)

theorem summable_norm_fixedProfile (H : {r : ℝ // 0 < r}) :
    Summable (fun q => ‖fixedProfile K S Γ H q‖) := by
  have hs := summable_norm_sIntegerOrbitalProfile K Sset Γ (rowBallArchTest K S 1)
    (sIntegerFiniteTestFunction K S (rowBallFiniteFamily K S 1))
    (continuous_sIntegerFiniteTestFunction K S _ (rowBallFiniteFamily_locallyConstant K S 1))
    (hasCompactSupport_sIntegerFiniteTestFunction K S _ (rowBallFiniteFamily_compactSupport K S 1))
    (rowRadius H)
  apply Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_) hs
  simpa only [fixedProfile, rowRadius, Real.norm_eq_abs] using (Complex.abs_re_le_norm _)

theorem summable_norm_weightedProfile (N : Finset Ext) (a : Ext → ℂ)
    (H : {r : ℝ // 0 < r}) :
    Summable (fun q => ‖((‖amplitude K S Γ D N a q‖ ^ 2 : ℝ) : ℂ) *
      sUnitOrbitalProfile K Sset
        (sLocalTensorTestFunction K Sset (rowBallArchTest K S 1)
          (sIntegerFiniteTestFunction K S (rowBallFiniteFamily K S 1)))
        ⟨H.val⁻¹ * (sIntegerOrbitNorm K Sset Γ q).val,
          mul_pos (inv_pos.mpr H.property) (sIntegerOrbitNorm K Sset Γ q).property⟩‖) := by
  apply summable_norm_sIntegerWeightedOrbitalProfile K S Γ (rowBallArchTest K S 1)
    (sIntegerFiniteTestFunction K S (rowBallFiniteFamily K S 1))
    (continuous_sIntegerFiniteTestFunction K S _ (rowBallFiniteFamily_locallyConstant K S 1))
    (hasCompactSupport_sIntegerFiniteTestFunction K S _ (rowBallFiniteFamily_compactSupport K S 1))
    (rowRadius H) (fun q => ((‖amplitude K S Γ D N a q‖ ^ 2 : ℝ) : ℂ))
    ((∑ n ∈ N, ‖a n‖) ^ 2)
  intro q
  rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (amplitude_norm_le K S Γ D N a q) 2

def energy (N : Finset Ext) (a : Ext → ℂ) (H : {r : ℝ // 0 < r}) : ℝ :=
  ∑' q, ‖amplitude K S Γ D N a q‖ ^ 2 * fixedProfile K S Γ H q

theorem summable_energy (N : Finset Ext) (a : Ext → ℂ) (H : {r : ℝ // 0 < r}) :
    Summable (fun q => ‖amplitude K S Γ D N a q‖ ^ 2 * fixedProfile K S Γ H q) := by
  have hs := (summable_norm_weightedProfile K S Γ D N a H).of_norm
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    fixedProfile] using (Complex.hasSum_re hs.hasSum).summable

theorem energy_nonneg (N : Finset Ext) (a : Ext → ℂ) (H : {r : ℝ // 0 < r}) :
    0 ≤ energy K S Γ D N a H :=
  tsum_nonneg (fun q => mul_nonneg (sq_nonneg _) (fixedProfile_nonneg K S Γ H q))

theorem finite_rows_le_energy (N : Finset Ext) (a : Ext → ℂ)
    (H : {r : ℝ // 0 < r}) (T : Finset Orbit)
    (hT : ∀ q ∈ T, (sIntegerOrbitNorm K Sset Γ q).val ≤ H.val) :
    (∑ q ∈ T, ‖amplitude K S Γ D N a q‖ ^ 2) ≤
      (rowCovolume K S)⁻¹ * energy K S Γ D N a H := by
  have hp : rowCovolume K S * (∑ q ∈ T, ‖amplitude K S Γ D N a q‖ ^ 2) ≤
      energy K S Γ D N a H := by
    rw [Finset.mul_sum]
    apply (Finset.sum_le_sum (fun q hq =>
      show rowCovolume K S * ‖amplitude K S Γ D N a q‖ ^ 2 ≤
        ‖amplitude K S Γ D N a q‖ ^ 2 * fixedProfile K S Γ H q from
      (mul_le_mul_of_nonneg_right (fixedProfile_lower K S Γ H q (hT q hq))
        (sq_nonneg _)).trans_eq (mul_comm _ _))).trans
    exact (summable_energy K S Γ D N a H).sum_le_tsum T
      (fun q hq => mul_nonneg (sq_nonneg _) (fixedProfile_nonneg K S Γ H q))
  calc
    _ = (rowCovolume K S)⁻¹ *
        (rowCovolume K S * (∑ q ∈ T, ‖amplitude K S Γ D N a q‖ ^ 2)) := by
      rw [← mul_assoc, inv_mul_cancel₀ (rowCovolume_pos K S).ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr (rowCovolume_pos K S).le)

variable {σ : Type*} {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}

theorem free_weightedEnergy_re (C : ColumnFamily K Sset σ Θ ψ)
    (γ : OuterTriple K) (j : Ideal (𝓞 K)) (d : OS) (H : {r : ℝ // 0 < r}) :
    (DivisorInverseColumn.weightedEnergy K S Γ D C γ j d
      (rowBallArchTest K S 1) (rowBallFiniteFamily K S 1) ∅ (rowRadius H)).re =
      energy K S Γ D (C.columns γ) (DivisorInverseColumn.coefficient K S D C γ j d) H := by
  unfold DivisorInverseColumn.weightedEnergy sIntegerWeightedOrbitalSeries
  simp only [sIntegerOrbitAvoidanceMask, Finset.notMem_empty, false_implies, implies_true,
    if_true, one_mul]
  have hs := (summable_norm_weightedProfile K S Γ D (C.columns γ)
    (DivisorInverseColumn.coefficient K S D C γ j d) H).of_norm
  dsimp only [amplitude] at hs
  dsimp only [DivisorInverseColumn.orbitColumn, rowRadius]
  rw [Complex.re_tsum hs]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rfl

variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)

include hΓ in
theorem canonical_sector_rows_le_free_energy (C : ColumnFamily K Sset σ Θ ψ)
    (γ : OuterTriple K) (j : Ideal (𝓞 K)) (d : OS)
    (H : {r : ℝ // 0 < r}) (T : Finset (Ext × Sector))
    (hT : ∀ x ∈ T, (x.1.val.val.absNorm : ℝ) ≤ H.val) :
    (∑ x ∈ T, ‖DivisorInverseColumn.column K S Γ D C γ j d (x.1.val.val,x.2)‖ ^ 2) ≤
      (rowCovolume K S)⁻¹ *
        (DivisorInverseColumn.weightedEnergy K S Γ D C γ j d
          (rowBallArchTest K S 1) (rowBallFiniteFamily K S 1) ∅ (rowRadius H)).re := by
  rw [free_weightedEnergy_re]
  have he := finite_rows_le_energy K S Γ D (C.columns γ)
    (DivisorInverseColumn.coefficient K S D C γ j d) H
    (T.image (CanonicalSectors.rowOrbit K Sset Γ D)) (by
      intro q hq
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
      rw [CanonicalSectors.rowOrbit_norm]
      exact hT x hx)
  rw [Finset.sum_image (fun _ _ _ _ h => CanonicalSectors.rowOrbit_injective K Sset Γ D h)] at he
  convert he using 1
  apply Finset.sum_congr rfl
  intro x hx
  change _ = ‖DivisorInverseColumn.orbitColumn K S Γ D C γ j d
    (CanonicalSectors.rowOrbit K Sset Γ D x)‖ ^ 2
  rcases x with ⟨I,ξ⟩
  rw [DivisorInverseColumn.orbitColumn_rowOrbit K S Γ D hΓ]

end HeckeSkeleton.Moments.MOM_INV_STEP.InverseRowMajorant

end

