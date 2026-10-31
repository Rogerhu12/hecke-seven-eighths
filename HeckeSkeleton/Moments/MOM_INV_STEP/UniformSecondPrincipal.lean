import HeckeSkeleton.Moments.MOM_INV_STEP.SecondPrincipalEstimate
import HeckeSkeleton.Moments.MOM_INV_STEP.PrincipalProfileBounds
import HeckeSkeleton.Moments.MOM_INV_STEP.PrincipalScaleBudget

/-!
# Uniform principal cost of the literal intermediate inverse columns

The window may occupy the complete squarefree pool up to four times its
fixed center. Both physical principal copies and both additive zeros are
bounded from the actual coefficients. Constants and Schwartz indices are
chosen before the column family, every row/label and the physical lengths.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.UniformSecondPrincipal

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton MeasureTheory
open HeckeSkeleton.Moments.MOMInvStep CanonicalChildren PrincipalOrbitalMass PrincipalZero
open scoped Classical BigOperators nonZeroDivisors

private theorem physical_power (Z H U eps rowEps : ℝ) (hZ : 0 < Z) :
    Z ^ ((1 + rowEps) * H) * (4 * Z ^ U) ^ (1 + 2 * eps) =
      4 ^ (1 + 2 * eps) * Z ^ (H + U + (rowEps * H + 2 * eps * U)) := by
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4)
    (Real.rpow_nonneg hZ.le _), ← Real.rpow_mul hZ.le]
  calc
    _ = 4 ^ (1 + 2 * eps) *
        (Z ^ ((1 + rowEps) * H) * Z ^ (U * (1 + 2 * eps))) := by ring
    _ = _ := by
      rw [← Real.rpow_add hZ]
      congr 2
      ring

private theorem zero_power (Z H U eps : ℝ) (hZ : 0 < Z) :
    Z ^ H * (4 * Z ^ U) ^ (1 + 4 * eps) =
      4 ^ (1 + 4 * eps) * Z ^ (H + U + 4 * eps * U) := by
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4)
    (Real.rpow_nonneg hZ.le _), ← Real.rpow_mul hZ.le]
  calc
    _ = 4 ^ (1 + 4 * eps) * (Z ^ H * Z ^ (U * (1 + 4 * eps))) := by ring
    _ = _ := by
      rw [← Real.rpow_add hZ]
      congr 2
      ring

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [Γ.FiniteIndex]
  [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Varch" => mixedEmbedding.euclidean.mixedSpace K

/-- No energy estimate is a premise: only the genuine common column
pool and the original product coefficient bounds are used. -/
theorem exists_uniform_principal_bound
    (slotCap : ℕ) (Hmax Umax loss : ℝ) (hHmax : 0 ≤ Hmax) (hUmax : 0 ≤ Umax)
    (hloss : 0 < loss)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) :
    ∃ s : Finset (ℕ × ℕ), ∃ A : ℝ, 0 ≤ A ∧
      ∀ {σ : Type*} {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}
      (C : ColumnFamily K Sset σ Θ ψ)
      (γ : OuterTriple K) (j : Ideal (𝓞 K)) (d : OS)
      (Z H U : ℝ) (φ : SchwartzMap Varch ℂ), ∀ hZ : 1 ≤ Z,
      0 ≤ H → H ≤ Hmax → 0 ≤ U → U ≤ Umax →
      C.originalSlots.card ≤ slotCap →
      (∀ i ∈ C.originalSlots, ∀ P ∈ C.primeLists i, ‖C.primeWeights i P‖ ≤ 1) →
      (∀ n ∈ C.columns γ, (n.val.val.absNorm : ℝ) ≤ 4 * Z ^ U) →
      2 * ‖SecondPoissonSplit.physicalPrincipal K S D Γ hΓ
          (DivisorInverseColumn.coefficient K S D C γ j d) (C.columns γ) φ h hlc hcs
          ⟨Z ^ (-H), Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _⟩‖ +
        ‖SecondPoissonSplit.additiveZeros K S D Γ hΓ μv
          (DivisorInverseColumn.coefficient K S D C γ j d) (C.columns γ) φ h hlc hcs
          ⟨Z ^ (-H), Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _⟩‖ ≤
      A * (SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ)) ^ 2 *
        s.sup (schwartzSeminormFamily ℝ Varch ℂ) φ * Z ^ (H + U + loss) := by
  obtain ⟨eps, rowEps, heps, hrow, hbudget⟩ :=
    PrincipalScaleBudget.exists_uniform_inverse_principal_losses
      Hmax Umax loss hHmax hUmax hloss
  obtain ⟨Ap, hAp, hp⟩ :=
    SecondPrincipalEstimate.exists_physicalPrincipal_bound K S D Γ hΓ slotCap eps heps
  obtain ⟨A₀, hA₀, hz⟩ :=
    SecondPrincipalEstimate.exists_additiveZeros_bound K S D Γ hΓ μv slotCap eps heps
  obtain ⟨s₁, Am, hAm, hm⟩ :=
    exists_absoluteRowMass_rowScale_bound K Sset Γ (sIntegerFiniteTestFunction K S h)
      (continuous_sIntegerFiniteTestFunction K S h hlc)
      (hasCompactSupport_sIntegerFiniteTestFunction K S h hcs) rowEps hrow
  obtain ⟨s₂, Az, hAz, hprofile⟩ :=
    PrincipalProfileBounds.exists_zeroProfileSize_bound K S μv Γ h
  let s := s₁ ∪ s₂
  let Cp := Ap * Am * 4 ^ (1 + 2 * eps)
  let Cz := A₀ * Az * 4 ^ (1 + 4 * eps)
  have hCp : 0 ≤ Cp := by dsimp only [Cp]; positivity
  have hCz : 0 ≤ Cz := by dsimp only [Cz]; positivity
  refine ⟨s, 2 * Cp + Cz, by positivity, ?_⟩
  intro σ Θ ψ C γ j d Z H U φ hZ hH0 hH hU0 hU hcap ha hN
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  let R : {r : ℝ // 0 < r} := ⟨Z ^ (-H), Real.rpow_pos_of_pos hZpos _⟩
  let W := SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ)
  let p := s.sup (schwartzSeminormFamily ℝ Varch ℂ) φ
  have hW : 0 ≤ W := apply_nonneg _ _
  have hp0 : 0 ≤ p := apply_nonneg _ _
  have hX : 1 ≤ 4 * Z ^ U := by
    have hh := Real.one_le_rpow hZ hU0
    linarith
  have hsup₁ : s₁.sup (schwartzSeminormFamily ℝ Varch ℂ) φ ≤ p := by
    apply Seminorm.finset_sup_apply_le hp0
    intro i hi
    exact Seminorm.le_finset_sup_apply (Finset.mem_union_left _ hi)
  have hsup₂ : s₂.sup (schwartzSeminormFamily ℝ Varch ℂ) φ ≤ p := by
    apply Seminorm.finset_sup_apply_le hp0
    intro i hi
    exact Seminorm.le_finset_sup_apply (Finset.mem_union_right _ hi)
  obtain ⟨hbp, hbz⟩ := hbudget H U hH hU
  have hm' : absoluteRowMass K Sset Γ φ (sIntegerFiniteTestFunction K S h) R ≤
      Am * p * Z ^ ((1 + rowEps) * H) :=
    (hm φ Z H hZ hH0).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsup₁ hAm) (Real.rpow_nonneg hZpos.le _))
  have hz' : zeroEnvelope K S Γ μv φ h R ≤ Az * p * Z ^ H := by
    apply (zeroEnvelope_physical_scale K S Γ μv φ h Z H hZ hH0).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZpos.le _)
    exact (hprofile φ).trans (mul_le_mul_of_nonneg_left hsup₂ hAz)
  have hp' : ‖SecondPoissonSplit.physicalPrincipal K S D Γ hΓ
        (DivisorInverseColumn.coefficient K S D C γ j d) (C.columns γ) φ h hlc hcs R‖ ≤
      Cp * W ^ 2 * p * Z ^ (H + U + loss) := by
    apply (hp C γ j d (4 * Z ^ U) φ h hlc hcs R hX hcap ha hN).trans
    calc
      _ ≤ Ap * W ^ 2 * (Am * p * Z ^ ((1 + rowEps) * H)) *
          (4 * Z ^ U) ^ (1 + 2 * eps) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
        exact mul_le_mul_of_nonneg_left hm' (by positivity)
      _ = (Ap * Am * W ^ 2 * p) *
          (Z ^ ((1 + rowEps) * H) * (4 * Z ^ U) ^ (1 + 2 * eps)) := by ring
      _ = Cp * W ^ 2 * p * Z ^ (H + U + (rowEps * H + 2 * eps * U)) := by
        rw [physical_power Z H U eps rowEps hZpos]
        dsimp only [Cp]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)
  have hz'' : ‖SecondPoissonSplit.additiveZeros K S D Γ hΓ μv
        (DivisorInverseColumn.coefficient K S D C γ j d) (C.columns γ) φ h hlc hcs R‖ ≤
      Cz * W ^ 2 * p * Z ^ (H + U + loss) := by
    apply (hz C γ j d (4 * Z ^ U) φ h hlc hcs R hX hcap ha hN).trans
    calc
      _ ≤ A₀ * W ^ 2 * (Az * p * Z ^ H) * (4 * Z ^ U) ^ (1 + 4 * eps) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
        exact mul_le_mul_of_nonneg_left hz' (by positivity)
      _ = (A₀ * Az * W ^ 2 * p) *
          (Z ^ H * (4 * Z ^ U) ^ (1 + 4 * eps)) := by ring
      _ = Cz * W ^ 2 * p * Z ^ (H + U + 4 * eps * U) := by
        rw [zero_power Z H U eps hZpos]
        dsimp only [Cz]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)
  have hall := add_le_add (mul_le_mul_of_nonneg_left hp' (by norm_num : (0 : ℝ) ≤ 2)) hz''
  convert hall using 1 <;> ring

end HeckeSkeleton.Moments.MOM_INV_STEP.UniformSecondPrincipal

end

