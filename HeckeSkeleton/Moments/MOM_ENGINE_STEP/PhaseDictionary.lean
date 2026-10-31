import HeckeGeneral.Characters.SIntegerModulusPhaseUnit
import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.CodifferentTraceDuality
import FLTReuse.Mee8f17f44a5cc910
import FLTReuse.M254fea41d68176b5
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SIntegerFirstFourier
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CoprimeCoefficient

/-!
# The arithmetic and orbital additive phases agree

The finite-coefficient recipes use the Circle-valued field trace
character.  Orbital Poisson uses the standard adelic character.  This
file identifies the two actual constructions, including their negative
finite-place sign, before using any finite transform formula.

The rational local comparison follows from integral differences of
fractional representatives.  The number-field comparison then uses the
actual completion trace and the archimedean trace product formula.
-/

noncomputable section
open scoped Classical NumberField BigOperators
open NumberField IsDedekindDomain
open DedekindZetaZeroFree NumberField.StandardAddChar

namespace HeckeSkeleton.Moments.EngineStep

theorem rational_trace_phase_eq_standard (p : Nat.Primes) (x : ℚ_[p]) :
    (rationalPadicCharacter p x : ℂ) = psiPadic x := by
  obtain ⟨a, k, ha⟩ := exists_pPow_approx x
  let q : ℚ := (a : ℚ) / (p.val : ℚ) ^ k
  have hq : q ∈ rationalPInverted p := by
    dsimp only [q]
    rw [div_eq_mul_inv, ← inv_pow]
    exact (rationalPInverted p).mul_mem (intCast_mem (rationalPInverted p) a)
      ((rationalPInverted p).pow_mem (Subring.subset_closure (by simp)) k)
  have hqx : ‖x - (q : ℚ_[p])‖ ≤ 1 := by
    simpa only [q, Rat.cast_div, Rat.cast_pow, Rat.cast_intCast, Rat.cast_natCast] using ha
  have hr := padicFractionalPart_spec p x
  have hi : ∃ z : ℤ, padicFractionalPart p x - q = z := by
    apply RationalPadicArithmetic.integral_of_norm_le p _
      ((rationalPInverted p).sub_mem hr.1 hq)
    have hd : ((padicFractionalPart p x - q : ℚ) : ℚ_[p]) =
        (x - (q : ℚ_[p])) - (x - (padicFractionalPart p x : ℚ_[p])) := by
      push_cast
      ring
    rw [hd, sub_eq_add_neg]
    apply (Padic.nonarchimedean _ _).trans
    exact max_le hqx (by
      rw [norm_neg]
      exact (RationalPadicArithmetic.range_iff_norm p _).mp hr.2.2.2)
  change (Circle.exp (-(2 * Real.pi * (padicFractionalPart p x : ℝ))) : ℂ) = _
  rw [negative_exp_congr _ _ hi, Circle.coe_exp, psiPadic_apply, psiPadicFun_eq ha]
  dsimp only [q]
  push_cast
  congr 1
  ring

variable (K : Type) [Field K] [NumberField K]

theorem local_trace_phase_eq_standard (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    (ResidueTrace.localTraceCharacter v (algebraMap K (v.adicCompletion K) x) : ℂ) =
      psiLocal K v (algebraMap K (v.adicCompletion K) x) := by
  rw [CodifferentResidueSieve.localTraceCharacter_eq_localFiniteCharacter]
  change (rationalPadicCharacter (PlaceTraceAdapter.prime K v)
    (PlaceTraceAdapter.trace K v (algebraMap K (v.adicCompletion K) x)) : ℂ) = _
  rw [rational_trace_phase_eq_standard, PlaceTraceAdapter.trace_algebraMap]
  rw [psiLocal_eq_psiLocal_trace ℚ K (PlaceTraceAdapter.rationalPlace K v) ⟨v, rfl⟩,
    psiLocal_rat_eq_psiV, psiV_apply]
  rfl

theorem actual_field_phase_eq_orbital (A : SArithmeticData K) (x : K) :
    (A.fieldTraceCharacter x : ℂ) =
      HeckeGeneral.Characters.sLocalPrincipalPhase K
        (A.Sf : Set (HeightOneSpectrum (𝓞 K))) x := by
  change Circle.coeHom
    ((∏ w : InfinitePlace K, archTraceCharacter w (algebraMap K w.Completion x)) *
      ∏ v : A.Sf, ResidueTrace.localTraceCharacter v.val
        (algebraMap K (v.val.adicCompletion K) x)) = _
  rw [ResidueTraceFactorProductFormula.archTraceCharacter_product_eq_trace,
    map_mul, map_prod]
  unfold HeckeGeneral.Characters.sLocalPrincipalPhase
  congr 1
  · change (Circle.exp _ : ℂ) = _
    rw [Circle.coe_exp]
    push_cast
    congr 1
    ring
  · apply Finset.prod_congr rfl
    intro v _
    exact local_trace_phase_eq_standard K v.val x

set_option Elab.async false in
set_option maxHeartbeats 1600000 in
/-- The complete Gauss column used after the first orbital transform is
the very same finite Gauss sum used by the arithmetic coefficient recipe. -/
theorem completeResidueGauss_eq_finiteGauss (A : SArithmeticData K)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (a : A.R) (ha : a ≠ 0)
    [Fintype (FiniteTransform.Residue A.R.toSubring a)]
    (χ : MulChar (FiniteTransform.Residue A.R.toSubring a) ℂ) (h : A.R) :
    completeResidueGauss (R := A.R) (actualSIntegerTrace K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) hS) a χ
        (Ideal.Quotient.mk _ h) =
      FiniteTransform.gaussSum A.R.toSubring a χ
        (Circle.coeHom.compAddChar A.fieldTraceCharacter) h := by
  unfold completeResidueGauss FiniteTransform.gaussSum FiniteTransform.gaussSumWithLifts
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  let v : A.R := (FiniteTransform.canonicalLifts A.R.toSubring a).val x
  have hv : Ideal.Quotient.mk (Ideal.span ({a} : Set A.R)) v = x :=
    (FiniteTransform.canonicalLifts A.R.toSubring a).property x
  rw [actualSIntegerTrace_psi K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) hS a ha]
  conv_lhs => rw [← hv, ← map_mul,
    HeckeGeneral.Characters.sIntegerActualModulusAddCharacter_mk]
  change HeckeGeneral.Characters.sLocalPrincipalPhase K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      (((h * v : A.R) : K) / (a : K)) =
    (A.fieldTraceCharacter ((h : K) * (v : K) / (a : K)) : ℂ)
  rw [Subalgebra.coe_mul]
  exact (actual_field_phase_eq_orbital K A _).symm

set_option Elab.async false in
set_option maxHeartbeats 1600000 in
/-- The old common modulus, the first-transform Gauss column and the
amplifier's finite coefficient are connected without a phase hypothesis. -/
theorem finiteCoefficient_coprime_orbital (A : SArithmeticData K)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (htrace : A.ContainsTraceBadPlaces) (s a h : A.R)
    (hs : s ≠ 0) (ha : a ≠ 0) (hcop : IsCoprime s a)
    [Fintype (FiniteTransform.Residue A.R.toSubring s)]
    [Fintype (FiniteTransform.Residue A.R.toSubring a)]
    (χs : MulChar (FiniteTransform.Residue A.R.toSubring s) ℂ)
    (χa : MulChar (FiniteTransform.Residue A.R.toSubring a) ℂ) :
    FiniteTransform.finiteCoefficient A.R.toSubring s a h χs χa
        (Circle.coeHom.compAddChar A.fieldTraceCharacter) =
      χs (FiniteTransform.residueMap A.R.toSubring s h) *
        star (χs (FiniteTransform.residueMap A.R.toSubring s a)) *
        χa (FiniteTransform.residueMap A.R.toSubring a s) *
        completeResidueGauss (R := A.R) (actualSIntegerTrace K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) hS) a χa
          (Ideal.Quotient.mk _ h) := by
  rw [completeResidueGauss_eq_finiteGauss K A hS a ha]
  apply finiteCoefficient_coprime_factor A.R.toSubring s a h hs ha hcop χs χa
  intro r
  change (A.fieldTraceCharacter (r : K) : ℂ) = 1
  rw [A.eS_integer htrace r, Circle.coe_one]

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.rational_trace_phase_eq_standard
#print axioms HeckeSkeleton.Moments.EngineStep.local_trace_phase_eq_standard
#print axioms HeckeSkeleton.Moments.EngineStep.actual_field_phase_eq_orbital
#print axioms HeckeSkeleton.Moments.EngineStep.finiteCoefficient_coprime_orbital

