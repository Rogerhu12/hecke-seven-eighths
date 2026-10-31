import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AmplifierGaussExtraction

/-!
# Support and norms of the actual amplifier residual presentation

Every frozen divisor avoided by the amplifier prime survives in the
real residual ideal.  The reciprocal column phase is proved to have
norm one on that same genuine coprime presentation.  The complete ideal
norm splits exactly, with the prime-power normalization still explicit.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open LocalFiniteSums HeckePort.Moments.CommonSupport

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS} {p : ExteriorPrime A} {n : ℕ}
  {I : A.Exterior}

namespace AmplifierResidualPresentation

theorem dvd_residual_of_dvd_original (R : AmplifierResidualPresentation C p n I)
    (S : Ideal (𝓞 F)) (hS : S ∣ I.val) (hpS : ¬p.val.asIdeal ∣ S) :
    S ∣ R.residual.val := by
  have hcop : IsCoprime p.val.asIdeal S := by
    rw [Ideal.isCoprime_iff_sup_eq]
    have hmax : p.val.asIdeal.IsMaximal := p.val.isPrime.isMaximal p.val.ne_bot
    exact hmax.out.2 _ (lt_of_le_of_ne le_sup_left (fun he =>
      hpS (Ideal.dvd_iff_le.mpr (sup_eq_left.mp he.symm))))
  have hpow : IsCoprime S (p.val.asIdeal ^ n) := by
    simpa only [pow_one] using (hcop.symm.pow :
      IsCoprime (S ^ 1) (p.val.asIdeal ^ n))
  apply hpow.dvd_of_dvd_mul_left
  rwa [← R.reconstructed]

theorem norm_reconstructed (R : AmplifierResidualPresentation C p n I) :
    A.exteriorNorm I = Q p ^ n * A.exteriorNorm R.residual := by
  change (Ideal.absNorm I.val : ℝ) = _
  rw [R.reconstructed, map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]
  rfl

theorem norm_residual (R : AmplifierResidualPresentation C p n I) :
    A.exteriorNorm R.residual = A.exteriorNorm I / Q p ^ n := by
  rw [R.norm_reconstructed]
  field_simp [(pow_pos (primeNorm_pos p) n).ne']
  ring

theorem columnPhase_norm (R : AmplifierResidualPresentation C p n I) :
    ‖R.columnPhase‖ = 1 := by
  letI : Finite (A.R ⧸ Ideal.span {LocalFiniteSums.generator C p ^ n}) :=
    LocalFiniteSums.residueFinite C p n
  letI : Fintype (A.R ⧸ Ideal.span {LocalFiniteSums.generator C p ^ n}) := Fintype.ofFinite _
  letI : Finite (A.R ⧸ Ideal.span {R.generator}) := by
    rw [R.generates.2]
    exact A.exteriorResidue_finite _
  letI : Fintype (A.R ⧸ Ideal.span {R.generator}) := Fintype.ofFinite _
  have hcop := generated_elements_coprime (powerIdeal p n) R.residual
    (LocalFiniteSums.generator C p ^ n) R.generator
    (generator_power_generates C p n) R.generates R.power_coprime
  have hleft :
      ‖generatedIdealCharacter (σ := σ) (powerIdeal p n)
        (LocalFiniteSums.generator C p ^ n) (generator_power_generates C p n)
        (Ideal.Quotient.mk _ R.generator)‖ = 1 := by
    have hh := Complex.norm_eq_one_of_mem_rootsOfUnity
      ((generatedIdealCharacter (σ := σ) (powerIdeal p n)
        (LocalFiniteSums.generator C p ^ n) (generator_power_generates C p n)).apply_mem_rootsOfUnity
          (residueUnit (LocalFiniteSums.generator C p ^ n) R.generator hcop))
    simpa only [MulChar.coe_equivToUnitHom, residueUnit_coe] using hh
  have hright :
      ‖generatedIdealCharacter (σ := σ) R.residual R.generator R.generates
        (Ideal.Quotient.mk _ (LocalFiniteSums.generator C p ^ n))‖ = 1 := by
    have hh := Complex.norm_eq_one_of_mem_rootsOfUnity
      ((generatedIdealCharacter (σ := σ) R.residual R.generator R.generates).apply_mem_rootsOfUnity
        (residueUnit R.generator (LocalFiniteSums.generator C p ^ n) hcop.symm))
    simpa only [MulChar.coe_equivToUnitHom, residueUnit_coe] using hh
  rw [columnPhase, norm_mul, hleft, hright, one_mul]

end AmplifierResidualPresentation
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.AmplifierResidualPresentation.dvd_residual_of_dvd_original
#print axioms HeckeSkeleton.Moments.EngineStep.AmplifierResidualPresentation.columnPhase_norm

