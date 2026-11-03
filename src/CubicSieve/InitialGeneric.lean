import CubicSieve.InitialArithmetic
import CubicSieve.LocalTypesCanonical

/-! Transfer the proved conductor large sieve to a realized cubic family.
The model identities in this intermediate theorem are supplied by the actual
primitive construction in the following module, not postulated as an endpoint. -/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.InitialGeneric

open NumberField IsDedekindDomain
open DedekindZetaZeroFree DedekindZetaZeroFree.Detector
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open scoped Classical NumberField BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (Sf : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (Sf : Set (HeightOneSpectrum (𝓞 K))))

local notation "S" => (Sf : Set (HeightOneSpectrum (𝓞 K)))

theorem prefix_bound_of_model
    (hD : AllowedGeneratorInput K S D)
    (ω : ExteriorIdeal K S → PrimitiveFrequencyCharacter K)
    (hK : NumberField.IsTotallyComplex K)
    (hcube : ∀ J c, RayClassBridge.ideleClassCharacter K hK (ω J).conductor
      (ω J).conductor_ne_zero (ω J).character c ^ 3 = 1)
    (hcoeff : ∀ J : ExteriorIdeal K S, Squarefree J.val.val → ∀ I : ExteriorIdeal K S,
      (ω J).character I.val.val = ExteriorKernel.positiveKernel K S D J I)
    (hsep : ∀ I J : ExteriorIdeal K S, Squarefree I.val.val → Squarefree J.val.val →
      I ≠ J → ¬ samePrimitiveFrequencyCharacter K (ω I) (ω J))
    (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hcond : ∀ J : ExteriorIdeal K S, Squarefree J.val.val →
      ((ω J).conductor.absNorm : ℝ) ≤ C₀ * exteriorNorm K S J)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X Y : ℝ, 2 ≤ X → 2 ≤ Y →
      ExteriorSieve.B K S D X Y ≤ C * (X + Y ^ 2) * (X * Y) ^ ε := by
  let A := InitialArithmetic.arithmeticData K Sf D
  obtain ⟨K_bal, hcompact, ⟨section'⟩⟩ := InitialArithmetic.exists_balanced_section K Sf D
  have hdyadic : ∀ σ ∈ LocalTypes.typeSet A,
      HasExteriorDyadicConductorSieve K A σ C₀ := by
    intro σ hσ
    exact hasExteriorDyadicConductorSieve_of_balancedSection K A ⊤ K_bal hcompact
      section' σ (LocalTypes.typeSet_finiteOrder A hσ) C₀ hC₀
  obtain ⟨C, hC, hb⟩ :=
    Quantitative.AllIdealSieveTransfer31.all_ideal_sieve_transfer_of_dyadic A C₀ hC₀
      (LocalTypes.typeSet A) (LocalTypes.typeSet_finite A) hdyadic ε hε
  refine ⟨C, hC, ?_⟩
  intro X Y hX hY
  let R := ExteriorSieve.cutoff K S X
  let T := ExteriorSieve.cutoff K S Y
  let f := ExteriorSieve.underlyingIdeal K S
  have hf : Function.Injective f := ExteriorSieve.underlyingIdeal_injective K S
  let L := C * (X + Y ^ 2) * (X * Y) ^ ε
  have hXpos : 0 < X := by linarith
  have hYpos : 0 < Y := by linarith
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hbound : FiniteKernel.HasBound T R (ExteriorKernel.positiveKernel K S D) L := by
    intro z
    let b : Ideal (𝓞 K) → ℂ := fun I =>
      if h : ∃ i ∈ R, f i = I then z (Classical.choose h) else 0
    have hbval (i : ExteriorIdeal K S) (hi : i ∈ R) : b (f i) = z i := by
      have hex : ∃ j ∈ R, f j = f i := ⟨i, hi, rfl⟩
      dsimp only [b]
      rw [dite_eq_left hex]
      exact congrArg z (hf (Classical.choose_spec hex).2)
    have hRI : ∀ I ∈ R.image f, I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ X := by
      intro I hI
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hI
      exact ⟨nonZeroDivisors.coe_ne_zero i.val,
        ((ExteriorSieve.mem_cutoff K S X i).mp hi).2⟩
    have hdist : ∀ I ∈ T, ∀ J ∈ T, I ≠ J →
        ¬ samePrimitiveFrequencyCharacter K (ω I) (ω J) := by
      intro I hI J hJ hIJ
      exact hsep I J ((ExteriorSieve.mem_cutoff K S Y I).mp hI).1
        ((ExteriorSieve.mem_cutoff K S Y J).mp hJ).1 hIJ
    have hconductor : ∀ J ∈ T, ((ω J).conductor.absNorm : ℝ) ≤ C₀ * Y := by
      intro J hJ
      have hj := (ExteriorSieve.mem_cutoff K S Y J).mp hJ
      exact (hcond J hj.1).trans (mul_le_mul_of_nonneg_left hj.2 hC₀.le)
    have htypes : ∀ J ∈ T, ∃ σ ∈ LocalTypes.typeSet A,
        HasFixedFullSLocalTuple K A (ω J) σ :=
      fun J _ => LocalTypes.cover_of_idelic_cube A hK (ω J) (hcube J)
    have hh := hb Y X hY hX T ω hdist hconductor htypes (R.image f) hRI b
    have he : (∑ I ∈ R.image f, ‖b I‖ ^ 2) = FiniteKernel.energy R z := by
      rw [Finset.sum_image (fun i _ j _ h => hf h)]
      exact Finset.sum_congr rfl (fun i hi => by rw [hbval i hi])
    have hrow (J : ExteriorIdeal K S) (hJ : J ∈ T) :
        (∑ I ∈ R.image f, b I * (ω J).character I) =
          ∑ i ∈ R, ExteriorKernel.positiveKernel K S D J i * z i := by
      rw [Finset.sum_image (fun i _ j _ h => hf h)]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hbval i hi]
      change z i * (ω J).character i.val.val =
        ExteriorKernel.positiveKernel K S D J i * z i
      rw [hcoeff J ((ExteriorSieve.mem_cutoff K S Y J).mp hJ).1 i]
      exact mul_comm _ _
    have hleft : (∑ J ∈ T, ‖∑ I ∈ R.image f, b I * (ω J).character I‖ ^ 2) =
        FiniteKernel.form T R (ExteriorKernel.positiveKernel K S D) z := by
      apply Finset.sum_congr rfl
      intro J hJ
      rw [hrow J hJ]
    rw [hleft, he] at hh
    simpa only [L, mul_comm X Y] using hh
  have ht := FiniteKernel.transpose_bound T R (ExteriorKernel.positiveKernel K S D) L hL hbound
  have hsym : (fun I J : ExteriorIdeal K S => ExteriorKernel.positiveKernel K S D J I) =
      ExteriorKernel.positiveKernel K S D := by
    funext I J
    exact ExteriorKernel.kernel_reciprocity K S D hD 2 J I
  rw [hsym] at ht
  exact (FiniteKernel.hasBound_iff_norm_sq_le R T _ L hL).mp ht

theorem exponent_two_of_model
    (hD : AllowedGeneratorInput K S D)
    (ω : ExteriorIdeal K S → PrimitiveFrequencyCharacter K)
    (hK : NumberField.IsTotallyComplex K)
    (hcube : ∀ J c, RayClassBridge.ideleClassCharacter K hK (ω J).conductor
      (ω J).conductor_ne_zero (ω J).character c ^ 3 = 1)
    (hcoeff : ∀ J : ExteriorIdeal K S, Squarefree J.val.val → ∀ I : ExteriorIdeal K S,
      (ω J).character I.val.val = ExteriorKernel.positiveKernel K S D J I)
    (hsep : ∀ I J : ExteriorIdeal K S, Squarefree I.val.val → Squarefree J.val.val →
      I ≠ J → ¬ samePrimitiveFrequencyCharacter K (ω I) (ω J))
    (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hcond : ∀ J : ExteriorIdeal K S, Squarefree J.val.val →
      ((ω J).conductor.absNorm : ℝ) ≤ C₀ * exteriorNorm K S J) :
    Bootstrap.HasCubicExponent (ExteriorSieve.B K S D) 2 := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := prefix_bound_of_model K Sf D hD ω hK hcube hcoeff hsep C₀ hC₀ hcond ε hε
  refine ⟨4 * C * (4 : ℝ) ^ ε, by positivity, ?_⟩
  intro X Y hX hY
  have hXpos : 0 < X := by linarith
  have hYpos : 0 < Y := by linarith
  have hshape : 2 * X + (2 * Y) ^ 2 ≤
      4 * (X + Y ^ (2 : ℝ) + (X * Y) ^ (2 / 3 : ℝ)) := by
    rw [Real.rpow_two]
    nlinarith [Real.rpow_nonneg (mul_pos hXpos hYpos).le (2 / 3 : ℝ)]
  have hp : ((2 * X) * (2 * Y)) ^ ε = (4 : ℝ) ^ ε * (X * Y) ^ ε := by
    rw [show (2 * X) * (2 * Y) = 4 * (X * Y) by ring,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (mul_pos hXpos hYpos).le]
  calc
    _ ≤ ExteriorSieve.B K S D (2 * X) (2 * Y) :=
      ExteriorSieve.B_mono K S D (by linarith) (by linarith)
    _ ≤ C * (2 * X + (2 * Y) ^ 2) * ((2 * X) * (2 * Y)) ^ ε :=
      hb _ _ (by linarith) (by linarith)
    _ ≤ C * (4 * (X + Y ^ (2 : ℝ) + (X * Y) ^ (2 / 3 : ℝ))) *
        ((4 : ℝ) ^ ε * (X * Y) ^ ε) := by
      rw [hp]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hshape hC.le)
        (by positivity)
    _ = _ := by ring

end CubicSieve.InitialGeneric
