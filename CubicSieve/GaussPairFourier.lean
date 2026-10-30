import CubicSieve.GaussPair
import CubicSieve.GaussPairFourierCRT

/-! The actual pair Fourier identity at every frequency, with its exact Gauss phase.
No zero or nonunit frequency is deleted. -/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.GaussPairFourier

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Arithmetic.PeriodicFourier
open HeckeGeneral.Arithmetic.ProductResidueFourier
open CubicSieve.GaussCharacters CubicSieve.GaussSquarefree CubicSieve.GaussPair
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

local instance thetaFinite (I : ExteriorIdeal K S) : Finite (ThetaQuotient K S I) :=
  finite_sIntegerSexticIdealQuotient K S I.val.val
    (nonZeroDivisors.coe_ne_zero I.val) I.property
local instance thetaFintype (I : ExteriorIdeal K S) : Fintype (ThetaQuotient K S I) :=
  Fintype.ofFinite _

private theorem principal_cube (I : ExteriorIdeal K S) (hI : Squarefree I.val.val) :
    principalCubicCharacter K S D I hI ^ 3 = 1 := by
  apply DFunLike.ext
  intro q
  by_cases hq : IsUnit q
  · rw [MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), MulChar.one_apply hq]
    have hqu : IsUnit (principalEquiv K S D I q) := hq.map (principalEquiv K S D I).toMonoidHom
    have h := congrArg (fun χ : MulChar (ThetaQuotient K S I) ℂ =>
      χ (principalEquiv K S D I q)) (quotientCubicCharacter_cube K S D I hI)
    change quotientCubicCharacter K S D I hI (principalEquiv K S D I q) ^ 3 = 1
    simpa only [MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), MulChar.one_apply hqu] using h
  · rw [MulChar.map_nonunit _ hq, MulChar.map_nonunit _ hq]

private theorem principal_inverse_eq_square (I : ExteriorIdeal K S)
    (hI : Squarefree I.val.val) :
    (principalCubicCharacter K S D I hI)⁻¹ = principalCubicCharacter K S D I hI ^ 2 := by
  apply mul_left_cancel (a := principalCubicCharacter K S D I hI)
  rw [mul_inv_cancel, ← pow_succ']
  exact (principal_cube K S D I hI).symm

private theorem principal_inverse_apply (I : ExteriorIdeal K S)
    (hI : Squarefree I.val.val) (q : PrincipalQuotient K S D I) :
    (principalCubicCharacter K S D I hI)⁻¹ q =
      quotientFunction K S D I (principalEquiv K S D I q) ^ 4 := by
  rw [principal_inverse_eq_square, MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0)]
  change (quotientCubicCharacter K S D I hI (principalEquiv K S D I q)) ^ 2 = _
  rw [quotientCubicCharacter_apply, ← pow_mul]

theorem principal_inverse_fourier (I : ExteriorIdeal K S) (hI : Squarefree I.val.val)
    (h : PrincipalQuotient K S D I) :
    fourier (principalPhase K S D I)
      ((principalCubicCharacter K S D I hI)⁻¹ : MulChar (PrincipalQuotient K S D I) ℂ) h =
      star ((principalCubicCharacter K S D I hI)⁻¹ h) *
        gaussSum (principalCubicCharacter K S D I hI)⁻¹ (principalPhase K S D I) := by
  unfold principalPhase
  have ht (q : PrincipalQuotient K S D I) := transport_fourier (principalEquiv K S D I)
    (thetaPrincipalAddCharacter K S D I) (fun x => quotientFunction K S D I x ^ (4 : ℕ)) q
  rw [GaussPoissonFinite.principal_addCharacter_transport] at ht
  have heq : (fun q : PrincipalQuotient K S D I =>
      quotientFunction K S D I (principalEquiv K S D I q) ^ (4 : ℕ)) =
        ((principalCubicCharacter K S D I hI)⁻¹ : MulChar (PrincipalQuotient K S D I) ℂ) := by
    funext q
    exact (principal_inverse_apply K S D I hI q).symm
  rw [heq] at ht
  calc
    _ = fourier (thetaPrincipalAddCharacter K S D I)
        (fun q => quotientFunction K S D I q ^ (4 : ℕ)) (principalEquiv K S D I h) := ht h
    _ = star (quotientFunction K S D I (principalEquiv K S D I h) ^ (4 : ℕ)) *
        fourier (thetaPrincipalAddCharacter K S D I)
          (fun q => quotientFunction K S D I q ^ (4 : ℕ)) 1 :=
      quotientFunction_power_fourier K S D I hI 4 (Or.inr rfl) _ _
    _ = _ := by
      rw [← principal_inverse_apply K S D I hI h]
      have h1 := ht (1 : PrincipalQuotient K S D I)
      rw [map_one] at h1
      rw [← h1]
      simp only [HeckeGeneral.Arithmetic.PeriodicFourier.fourier, gaussSum, one_mul]

private theorem principal_positive_eigen (I : ExteriorIdeal K S) (hI : Squarefree I.val.val)
    (h : PrincipalQuotient K S D I) :
    fourier (principalPhase K S D I) (principalCubicCharacter K S D I hI) h =
      star (principalCubicCharacter K S D I hI h) *
        gaussSum (principalCubicCharacter K S D I hI) (principalPhase K S D I) := by
  simpa only [principalPhase, HeckeGeneral.Arithmetic.PeriodicFourier.fourier, gaussSum, one_mul]
    using GaussPoissonFinite.principal_fourier K S D I hI h

/-- The exact pair eigenidentity, before any size estimate or Gauss phase deletion. -/
theorem pair_eigen (I J : ExteriorIdeal K S) (hI : Squarefree I.val.val)
    (hJ : Squarefree J.val.val) (hcop : IsCoprime I.val.val J.val.val)
    (h : PairQuotient K S D I J) :
    fourier (pairPhase K S D I J) (pairRow K S D I J hI hJ) h =
      star (pairRow K S D I J hI hJ h) *
        fourier (pairPhase K S D I J) (pairRow K S D I J hI hJ) 1 := by
  obtain ⟨u, v, hbez⟩ := GaussPairCRT.bezout_of_principal_coprime (principal_coprime K S D I J hcop)
  have ha : ((S.integer K).val.toRingHom (D.generator I)) ≠ 0 := by
    intro h; exact D.generator_ne_zero I (Subtype.ext h)
  have hb : ((S.integer K).val.toRingHom (D.generator J)) ≠ 0 := by
    intro h; exact D.generator_ne_zero J (Subtype.ext h)
  let e := Ideal.quotientMulEquivQuotientProd (principalIdeal K S D I) (principalIdeal K S D J)
    (GaussPairCRT.principal_coprime_of_bezout hbez)
  have hl := GaussPairCRT.leftAddChar_principal (S.integer K).val.toRingHom
    (sLocalPrincipalPhase K S) hbez ha hb (principalPhase K S D I) (pairPhase K S D I J)
    (principalPhase_mk K S D I) (pairPhase_mk K S D I J)
  have hr := GaussPairCRT.rightAddChar_principal (S.integer K).val.toRingHom
    (sLocalPrincipalPhase K S) hbez ha hb (principalPhase K S D J) (pairPhase K S D I J)
    (principalPhase_mk K S D J) (pairPhase_mk K S D I J)
  have hrow : pairRow K S D I J hI hJ = GaussPairFourierCRT.coefficient e
      (principalCubicCharacter K S D I hI)⁻¹ (principalCubicCharacter K S D J hJ) := by
    funext x
    simp only [pairRow, GaussPairFourierCRT.coefficient, e,
      Ideal.quotientMulEquivQuotientProd_fst, Ideal.quotientMulEquivQuotientProd_snd]
  rw [hrow]
  apply GaussPairFourierCRT.product_eigen
  · intro q
    rw [hl]
    exact GaussPairFourierCRT.eigen_mulShift _ _ (principal_inverse_fourier K S D I hI) _ q
  · intro q
    rw [hr]
    exact GaussPairFourierCRT.eigen_mulShift _ _ (principal_positive_eigen K S D J hJ) _ q

/-- All frequencies remain, and the scalar is the actual normalized pair Gauss sum. -/
theorem pairFourier (I J : ExteriorIdeal K S) (hI : Squarefree I.val.val)
    (hJ : Squarefree J.val.val) (hcop : IsCoprime I.val.val J.val.val)
    (h : PairQuotient K S D I J) :
    fourier (pairPhase K S D I J) (pairRow K S D I J hI hJ) h =
      star (pairRow K S D I J hI hJ h) *
        (Real.sqrt (exteriorNorm K S I * exteriorNorm K S J) : ℂ) *
          pairNormalizedGauss K S D I J hI hJ := by
  have hn : exteriorNorm K S (exteriorMul K S I J) =
      exteriorNorm K S I * exteriorNorm K S J := by
    simp only [exteriorNorm, exteriorMul, Submonoid.coe_mul, map_mul, Nat.cast_mul]
  have hpos : 0 < exteriorNorm K S I * exteriorNorm K S J := by
    apply mul_pos
    · change 0 < (I.val.val.absNorm : ℝ)
      exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I.val
    · change 0 < (J.val.val.absNorm : ℝ)
      exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors J.val
  have hsqrt : (Real.sqrt (exteriorNorm K S I * exteriorNorm K S J) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hpos).ne'
  have h0 : fourier (pairPhase K S D I J) (pairRow K S D I J hI hJ) 1 =
      (Real.sqrt (exteriorNorm K S I * exteriorNorm K S J) : ℂ) *
        pairNormalizedGauss K S D I J hI hJ := by
    simp only [HeckeGeneral.Arithmetic.PeriodicFourier.fourier, one_mul, pairNormalizedGauss, normalizer, hn]
    rw [← mul_assoc, mul_inv_cancel₀ hsqrt, one_mul]
  rw [pair_eigen K S D I J hI hJ hcop h, h0, mul_assoc]

end CubicSieve.GaussPairFourier
