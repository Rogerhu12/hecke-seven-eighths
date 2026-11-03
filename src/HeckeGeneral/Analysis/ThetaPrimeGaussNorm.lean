import HeckeGeneral.Analysis.LocalThetaInput
import HeckeGeneral.Arithmetic.ResidueGaussSums
import Mathlib.Tactic.NormNum

/-!
The prime Gauss norm is a consequence of actual finite residue algebra:
the specified-root character has exact order six, its square is nontrivial,
and the actual theta additive character is primitive. We transport that
character through the proved S-integer residue equivalence and reindex the
literal quotient sum. No Gauss-norm or character-nontriviality input is added.

This supplies the arithmetic gauss_norm sub-obligation.
No KP digit-table realization or theta calibration identity is constructed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Arithmetic.ResidueTraceCharacters
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

theorem thetaPrimeCharacter_sq_ne_one (p : ExteriorPrime K S) :
    thetaPrimeCharacter K S D p ^ 2 ≠ 1 := by
  intro h
  have hdiv := orderOf_dvd_of_pow_eq_one h
  have horder : orderOf (thetaPrimeCharacter K S D p) = 6 :=
    sexticResidueCharacter_order K D.root6 D.primitive6 D.embedding p.val
      (D.away_six p.val p.property)
  rw [horder] at hdiv
  norm_num at hdiv

/-- The existing localization equivalence at the actual exterior prime. -/
def thetaPrimeResidueEquiv (p : ExteriorPrime K S) :
    (𝓞 K ⧸ p.val.asIdeal) ≃+* ThetaQuotient K S (exteriorPrimeIdeal K S p) :=
  sIntegerResidueEquiv K S p.val.asIdeal
    (sIntegerSexticResidue_coprime K S p.val p.property)

/-- State the exterior proof with the literal prime ideal in its type,
so dependent rewriting does not need to unfold exteriorPrimeIdeal. -/
private theorem thetaPrimeExterior (p : ExteriorPrime K S) :
    ∀ q : HeightOneSpectrum (𝓞 K), q.asIdeal ∣ p.val.asIdeal → q ∉ S := by
  simpa only [exteriorPrimeIdeal] using (exteriorPrimeIdeal K S p).property

private def thetaPrimeQuotientFunction (p : ExteriorPrime K S) :
    ThetaQuotient K S (exteriorPrimeIdeal K S p) → ℂ :=
  sIntegerSexticIdealQuotientFunction K S D.root6 D.primitive6 D.embedding
    p.val.asIdeal p.val.ne_bot (thetaPrimeExterior K S p)
    (fun q hq => D.away_six q (thetaPrimeExterior K S p q hq))

private theorem thetaPrimeIdealEvaluation (p : ExteriorPrime K S) (a : S.integer K) :
    sIntegerSexticIdealEvaluation K S D.root6 D.primitive6 D.embedding
        p.val.asIdeal p.val.ne_bot (thetaPrimeExterior K S p)
        (fun q hq => D.away_six q (thetaPrimeExterior K S p q hq)) a =
      sIntegerSexticEvaluation K S p.val p.property D.root6 D.primitive6 D.embedding
        (D.away_six p.val p.property) a := by
  let p0 : idealPrimeDivisors K p.val.asIdeal := ⟨p.val, dvd_refl _⟩
  letI : Fintype (idealPrimeDivisors K p.val.asIdeal) :=
    (idealPrimeDivisors_finite K p.val.asIdeal p.val.ne_bot).fintype
  have hsingle : ∀ q : idealPrimeDivisors K p.val.asIdeal, q = p0 := by
    intro q
    apply Subtype.ext
    have he : p.val.asIdeal = q.val.asIdeal :=
      p.val.isMaximal.eq_of_le q.val.isPrime.ne_top (Ideal.dvd_iff_le.mp q.property)
    exact HeightOneSpectrum.ext he.symm
  have hmult : idealPrimeMultiplicity K p.val p.val.asIdeal = 1 := by
    unfold idealPrimeMultiplicity
    exact Associates.count_self p.val.associates_irreducible
  change (∏ q : idealPrimeDivisors K p.val.asIdeal,
    sIntegerSexticEvaluation K S q.val (thetaPrimeExterior K S p q.val q.property)
      D.root6 D.primitive6 D.embedding
      (D.away_six q.val (thetaPrimeExterior K S p q.val q.property)) a ^
        idealPrimeMultiplicity K q.val p.val.asIdeal) = _
  rw [Finset.prod_eq_single_of_mem p0 (Finset.mem_univ p0)
    (fun q _ hne => False.elim (hne (hsingle q)))]
  change sIntegerSexticEvaluation K S p.val p.property D.root6 D.primitive6 D.embedding
    (D.away_six p.val p.property) a ^ idealPrimeMultiplicity K p.val p.val.asIdeal = _
  rw [hmult, pow_one]

private theorem thetaPrimeQuotientFunction_equiv (p : ExteriorPrime K S)
    (x : 𝓞 K ⧸ p.val.asIdeal) :
    thetaPrimeQuotientFunction K S D p (thetaPrimeResidueEquiv K S p x) =
      thetaPrimeCharacter K S D p x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change sIntegerSexticIdealQuotientFunction K S D.root6 D.primitive6 D.embedding
      p.val.asIdeal p.val.ne_bot (thetaPrimeExterior K S p)
      (fun q hq => D.away_six q (thetaPrimeExterior K S p q hq))
      (sIntegerResidueEquiv K S p.val.asIdeal
        (sIntegerSexticResidue_coprime K S p.val p.property) (Ideal.Quotient.mk _ a)) = _
  rw [sIntegerResidueEquiv_mk, sIntegerSexticIdealQuotientFunction_mk,
    thetaPrimeIdealEvaluation, sIntegerSexticEvaluation_algebraMap]
  rfl

/-- The actual normalized prime theta Gauss sum has norm one, without
assuming LocalThetaInput or any property of a proposed digit table. -/
theorem thetaGamma_exteriorPrime_two_norm (p : ExteriorPrime K S) :
    ‖thetaGamma K S D (exteriorPrimeIdeal K S p) 2‖ = 1 := by
  let F := 𝓞 K ⧸ p.val.asIdeal
  let Q := ThetaQuotient K S (exteriorPrimeIdeal K S p)
  letI : Field F := Ideal.Quotient.field _
  letI : Fintype F := Fintype.ofFinite _
  letI : Finite Q := finite_sIntegerSexticIdealQuotient K S p.val.asIdeal
    p.val.ne_bot (thetaPrimeExterior K S p)
  letI : Fintype Q := Fintype.ofFinite _
  let e : F ≃+* Q := thetaPrimeResidueEquiv K S p
  let χ : MulChar F ℂ := thetaPrimeCharacter K S D p
  let ψQ : AddChar Q ℂ := thetaPrincipalAddCharacter K S D (exteriorPrimeIdeal K S p)
  let ψ : AddChar F ℂ := transportCharacter e ψQ
  have hψ : ψ.IsPrimitive := transportCharacter_isPrimitive e ψQ
    (thetaPrincipalAddCharacter_isPrimitive K S D (exteriorPrimeIdeal K S p))
  have hχ : χ ^ 2 ≠ 1 := thetaPrimeCharacter_sq_ne_one K S D p
  have hsum :
      (∑ x : Q, thetaPrimeQuotientFunction K S D p x ^ 2 * ψQ x) =
        gaussSum (χ ^ 2) ψ := by
    calc
      _ = ∑ x : F, thetaPrimeQuotientFunction K S D p (e x) ^ 2 * ψQ (e x) :=
        (e.toEquiv.sum_comp (fun x => thetaPrimeQuotientFunction K S D p x ^ 2 * ψQ x)).symm
      _ = gaussSum (χ ^ 2) ψ := by
        unfold gaussSum
        apply Finset.sum_congr rfl
        intro x _
        rw [show thetaPrimeQuotientFunction K S D p (e x) = χ x from
          thetaPrimeQuotientFunction_equiv K S D p x]
        rw [MulChar.pow_apply' χ (by decide : (2 : ℕ) ≠ 0)]
        rfl
  have hgauss := HeckeGeneral.Arithmetic.ResidueGaussSums.gauss_norm ψ hψ (χ ^ 2) hχ
  have hcard : Fintype.card F = p.val.asIdeal.absNorm := card_primeIdealResidueField K p.val
  rw [hcard] at hgauss
  have hN : 0 < p.val.asIdeal.absNorm :=
    lt_trans Nat.zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm p.val)
  have hsqrt : 0 < Real.sqrt (p.val.asIdeal.absNorm : ℝ) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hnormsqrt : ‖(Real.sqrt (p.val.asIdeal.absNorm : ℝ) : ℂ)‖ =
      Real.sqrt (p.val.asIdeal.absNorm : ℝ) := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsqrt]
  change ‖(Real.sqrt (p.val.asIdeal.absNorm : ℝ) : ℂ)⁻¹ *
    ∑ x : Q, thetaPrimeQuotientFunction K S D p x ^ 2 * ψQ x‖ = 1
  rw [hsum, norm_mul, norm_inv, hnormsqrt, hgauss, inv_mul_cancel₀ hsqrt.ne']

end HeckeGeneral.ThetaSkeleton
