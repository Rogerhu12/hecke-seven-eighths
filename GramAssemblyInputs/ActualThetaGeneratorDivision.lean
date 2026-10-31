import HeckeGeneral.Analysis.GlobalThetaData
import HeckeGeneral.Arithmetic.SIntegerModulusNorm

/-!
UNCOMPILED / native 0. Literal division of the supplied theta generators
along an actual exterior ideal product I = C*N. The quotient S-integer is
constructed with an explicit general unit; the chosen generator function
is not assumed multiplicative. Its principal ideal, contraction, actual
S-local norm, uniqueness and field quotient are proved from generator_span.
No allowed-generator, PID or sixth-power-unit assumption is introduced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.ActualGeneratorDivisionDraft

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

local notation "OS" => S.integer K
local notation "NZ" => NonzeroRingElements OS

/-- The product of the two supplied generators and the supplied generator
of the product ideal differ by an actual general unit of the S-integer ring. -/
theorem exists_thetaGenerator_product_unit
    (C N I : ExteriorIdeal K S) (hI : I = exteriorMul K S C N) :
    ∃ u : OSˣ, D.generator I = D.generator C * (D.generator N * (u : OS)) := by
  have hval := congrArg (fun A : ExteriorIdeal K S => A.val.val) hI
  change I.val.val = C.val.val * N.val.val at hval
  have hspan : Ideal.span ({D.generator C * D.generator N} : Set OS) =
      Ideal.span ({D.generator I} : Set OS) := by
    rw [← Ideal.span_singleton_mul_span_singleton,
      D.generator_span, D.generator_span, D.generator_span, ← Ideal.map_mul, ← hval]
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  exact ⟨u, by simpa only [mul_assoc] using hu.symm⟩

/-- The explicit unit discrepancy between the supplied generators.
No membership in any proper subgroup of units is asserted. -/
def thetaGeneratorDivisionUnit
    (C N I : ExteriorIdeal K S) (hI : I = exteriorMul K S C N) : OSˣ :=
  Classical.choose (exists_thetaGenerator_product_unit K S D C N I hI)

theorem thetaGeneratorDivisionUnit_spec
    (C N I : ExteriorIdeal K S) (hI : I = exteriorMul K S C N) :
    D.generator I = D.generator C *
      (D.generator N * (thetaGeneratorDivisionUnit K S D C N I hI : OS)) :=
  Classical.choose_spec (exists_thetaGenerator_product_unit K S D C N I hI)

/-- Literal nonzero quotient generator: gen(N) times the retained actual
unit, rather than a replacement by gen(N). -/
def thetaGeneratorDivision
    (C N I : ExteriorIdeal K S) (hI : I = exteriorMul K S C N) : NZ :=
  ⟨D.generator N * (thetaGeneratorDivisionUnit K S D C N I hI : OS),
    mul_ne_zero (D.generator_ne_zero N)
      (thetaGeneratorDivisionUnit K S D C N I hI).ne_zero⟩

theorem thetaGeneratorDivision_factor
    (C N I : ExteriorIdeal K S) (hI : I = exteriorMul K S C N) :
    D.generator I = D.generator C * (thetaGeneratorDivision K S D C N I hI).val :=
  thetaGeneratorDivisionUnit_spec K S D C N I hI

theorem thetaGeneratorDivision_eq_generator_mul_unit
    (C N I : ExteriorIdeal K S) (hI : I = exteriorMul K S C N) :
    (thetaGeneratorDivision K S D C N I hI).val =
      D.generator N * (thetaGeneratorDivisionUnit K S D C N I hI : OS) := rfl

/-- The quotient element generates precisely the extension of N. -/
theorem thetaGeneratorDivision_span
    (C N I : ExteriorIdeal K S) (hI : I = exteriorMul K S C N) :
    Ideal.span ({(thetaGeneratorDivision K S D C N I hI).val} : Set OS) =
      N.val.val.map (algebraMap (𝓞 K) OS) := by
  change Ideal.span ({D.generator N *
    (thetaGeneratorDivisionUnit K S D C N I hI : OS)} : Set OS) = _
  rw [Ideal.span_singleton_mul_right_unit
    (thetaGeneratorDivisionUnit K S D C N I hI).isUnit, D.generator_span]

/-- Exterior support makes contraction of that extension exactly N. -/
theorem thetaGeneratorDivision_contraction
    (C N I : ExteriorIdeal K S) (hI : I = exteriorMul K S C N) :
    sIntegerModulusContraction K S (thetaGeneratorDivision K S D C N I hI).val =
      N.val.val := by
  unfold sIntegerModulusContraction
  rw [thetaGeneratorDivision_span]
  exact under_map_coprime_sIntegerIdeal K S N.val.val
    (sexticIdeal_coprime_S K S N.val.val N.property)

/-- Its actual S-local product norm is q_N, with all finite S factors. -/
theorem thetaGeneratorDivision_norm
    (C N I : ExteriorIdeal K S) (hI : I = exteriorMul K S C N) :
    (sIntegerElementNorm K S (thetaGeneratorDivision K S D C N I hI)).val =
      exteriorNorm K S N := by
  rewrite [← natCard_sIntegerPrincipalResidue_eq_productNorm K S
    (thetaGeneratorDivision K S D C N I hI).val
    (thetaGeneratorDivision K S D C N I hI).property,
    natCard_sIntegerPrincipalResidue K S
      (thetaGeneratorDivision K S D C N I hI).val
      (thetaGeneratorDivision K S D C N I hI).property,
    thetaGeneratorDivision_contraction]
  rfl

/-- Cancellation by the nonzero supplied generator makes the quotient
independent of any way its existence was proved. -/
theorem thetaGeneratorDivision_unique
    (C N I : ExteriorIdeal K S) (hI : I = exteriorMul K S C N)
    (n : OS) (hn : D.generator I = D.generator C * n) :
    n = (thetaGeneratorDivision K S D C N I hI).val := by
  exact mul_left_cancel₀ (D.generator_ne_zero C)
    (hn.symm.trans (thetaGeneratorDivision_factor K S D C N I hI))

theorem existsUnique_thetaGenerator_division
    (C N I : ExteriorIdeal K S) (hI : I = exteriorMul K S C N) :
    ∃! n : OS, D.generator I = D.generator C * n := by
  refine ⟨(thetaGeneratorDivision K S D C N I hI).val,
    thetaGeneratorDivision_factor K S D C N I hI, ?_⟩
  intro n hn
  exact thetaGeneratorDivision_unique K S D C N I hI n hn

/-- In the fraction field it is exactly gen(I)/gen(C). This does not
identify it with the independently supplied generator of N. -/
theorem thetaGeneratorDivision_coe_eq_div
    (C N I : ExteriorIdeal K S) (hI : I = exteriorMul K S C N) :
    ((thetaGeneratorDivision K S D C N I hI).val : K) =
      (D.generator I : K) / (D.generator C : K) := by
  have hC : (D.generator C : K) ≠ 0 := by
    intro h
    exact D.generator_ne_zero C (Subtype.ext h)
  apply (eq_div_iff hC).mpr
  have hf := congrArg (fun a : OS => (a : K))
    (thetaGeneratorDivision_factor K S D C N I hI)
  change (D.generator I : K) = (D.generator C : K) *
    ((thetaGeneratorDivision K S D C N I hI).val : K) at hf
  exact (mul_comm _ _).trans hf.symm

end HeckeGeneral.ThetaSkeleton.ActualGeneratorDivisionDraft
