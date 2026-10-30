module

public import ThetaGlobal.GlobalPhases
public import HeckeGeneral.Analysis.MarkedThetaReflection
public import HeckeGeneral.Characters.SIntegerSexticPowerMask

@[expose] public section

/-!
# Actual ideal-symbol cross phases

This specializes the zero-extended sextic identities to the project's
literal residue symbols.  The only extra arithmetic hypothesis is
`AllowedGeneratorInput`, exactly the allowed-generator/reciprocity input
already proved for the selected arithmetic choice in `Theta.lean`.

No reflection identity or conclusion about theta coefficients is a
hypothesis.  Compilation against the whole supplied project is listed
separately from the self-contained `GlobalPhases` module in the report.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GlobalProjectPhases

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

theorem idealSymbol_mul (I : ExteriorIdeal K S) (a b : S.integer K) :
    idealSymbol K S D I (a * b) = idealSymbol K S D I a * idealSymbol K S D I b :=
  sIntegerSexticIdealEvaluation_mul K S D.root6 D.primitive6 D.embedding
    I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp)) a b

theorem idealSymbol_one (I : ExteriorIdeal K S) : idealSymbol K S D I 1 = 1 :=
  sIntegerSexticIdealEvaluation_one K S D.root6 D.primitive6 D.embedding
    I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp))

theorem idealSymbol_pow (I : ExteriorIdeal K S) (a : S.integer K) (n : ℕ) :
    idealSymbol K S D I (a ^ n) = idealSymbol K S D I a ^ n := by
  induction n with
  | zero => simpa only [pow_zero] using idealSymbol_one K S D I
  | succ n ih => rw [pow_succ, idealSymbol_mul K S D, ih, pow_succ]

/-- The sixth power is the genuine coprimality indicator even at zeros. -/
theorem idealSymbol_sixth_pow_mask (I : ExteriorIdeal K S) (a : S.integer K) :
    idealSymbol K S D I a ^ 6 =
      if IsCoprime I.val.val (sIntegerModulusContraction K S a) then 1 else 0 := by
  rw [← idealSymbol_pow K S D]
  exact sIntegerSexticIdealEvaluation_sixth_power_coprime_mask K S D.root6
    D.primitive6 D.embedding I.val.val (nonZeroDivisors.coe_ne_zero I.val)
    I.property (fun p hp => D.away_six p (I.property p hp)) a

theorem idealSymbol_sexticValue (I : ExteriorIdeal K S) (a : S.integer K) :
    GlobalPhases.SexticValue (idealSymbol K S D I a) := by
  by_cases hz : idealSymbol K S D I a = 0
  · exact Or.inl hz
  · apply Or.inr
    by_cases hc : IsCoprime I.val.val (sIntegerModulusContraction K S a)
    · simpa only [if_pos hc] using idealSymbol_sixth_pow_mask K S D I a
    · have hp : idealSymbol K S D I a ^ 6 = 0 := by
        simpa only [if_neg hc] using idealSymbol_sixth_pow_mask K S D I a
      exact False.elim ((pow_ne_zero 6 hz) hp)

theorem contraction_generator (I : ExteriorIdeal K S) :
    sIntegerModulusContraction K S (D.generator I) = I.val.val := by
  unfold sIntegerModulusContraction
  rw [D.generator_span]
  exact under_map_coprime_sIntegerIdeal K S I.val.val
    (sexticIdeal_coprime_S K S I.val.val I.property)

theorem idealSymbol_nonzeroMask_generator (I J : ExteriorIdeal K S) :
    GlobalPhases.nonzeroMask (idealSymbol K S D I (D.generator J)) =
      if IsCoprime I.val.val J.val.val then 1 else 0 := by
  rw [← GlobalPhases.mark_cube_coupling (idealSymbol_sexticValue K S D I (D.generator J)),
    idealSymbol_sixth_pow_mask K S D, contraction_generator K S D]

/-- The literal five moving interactions in the marked reflection reduce
to the quadratic row, cubic mark, and the two displayed coprimality masks.
The ideals need not be coprime: the equality retains all symbol zeros. -/
theorem actual_moving_couplings (hA : AllowedGeneratorInput K S D)
    (d P c n : ExteriorIdeal K S) :
    (idealSymbol K S D d (D.generator c) *
        idealSymbol K S D c (D.generator d) ^ (-4 : ℤ)) *
      (idealSymbol K S D d (D.generator P) ^ (-2 : ℤ) *
        idealSymbol K S D P (D.generator d) ^ (-4 : ℤ)) *
      (idealSymbol K S D P (D.generator c) ^ 2 *
        idealSymbol K S D c (D.generator P) ^ (-4 : ℤ)) *
      idealSymbol K S D d (D.generator n) ^ 3 *
      idealSymbol K S D P (D.generator n) ^ 6 =
    idealSymbol K S D d (D.generator c * D.generator n) ^ 3 *
      idealSymbol K S D P (D.generator c) ^ (-2 : ℤ) *
      (if IsCoprime d.val.val P.val.val then 1 else 0) *
      (if IsCoprime P.val.val n.val.val then 1 else 0) := by
  rw [← hA.reciprocity d c, ← hA.reciprocity d P, ← hA.reciprocity P c]
  rw [GlobalPhases.separated_moving_couplings
    _ _ _ _ _
    (idealSymbol_sexticValue K S D d (D.generator c))
    (idealSymbol_sexticValue K S D d (D.generator P))
    (idealSymbol_sexticValue K S D P (D.generator c))
    (idealSymbol_sexticValue K S D P (D.generator n))]
  rw [← idealSymbol_mul K S D,
    idealSymbol_nonzeroMask_generator K S D, idealSymbol_nonzeroMask_generator K S D]

end ThetaGlobal.GlobalProjectPhases
