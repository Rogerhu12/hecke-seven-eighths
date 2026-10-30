module

public import ThetaGlobal.ActualAnnularProfiles
public import ThetaGlobal.GammaDeconvolverProject
public import ThetaGlobal.ActualRegularizerRemoval
public import ThetaGlobal.ScalarKernelProject
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# Arbitrary annular tests from the literal actual fixed-profile seed

This is the analytic assembly, deliberately stated as an implication
from the separately proved arithmetic seed. Every convolution, weighted
sum interchange, Gaussian deconvolver and limiting operation is derived.
The seed is never a field of the local data or an asserted theorem here.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.ActualAnnularTransfer

open NumberField IsDedekindDomain MeasureTheory Filter DedekindZetaZeroFree
open DedekindZetaZeroFree.ThetaProfileHaarSheets
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators Topology

variable {K : Type} [Field K] [NumberField K]
  {S₀ : SArithmeticData K} {η : RayClassCharacter K S₀.modulus}
  (R : PrincipalMellin.ActualRecipe S₀ η) (θ : HeckeCharacter K)
  (C : FiniteFixedSource.Source R θ) (L : FiniteLocalHighK.Input R θ C)

local notation "S" => (R.A.Sf : Set (HeightOneSpectrum (𝓞 K)))
local notation "M" => FiniteLocalHighK.finiteMellinData R θ C L

def directTest (w : InfinitePlace K) (t : ℝ) : ℂ :=
  if ht : 0 < t then FiniteNormalizedMellin.direct R θ C L w ⟨t, ht⟩ else 0

def reflectedProfile (u : R.A.UnitQuotient) (κ : SixthLocalClasses K S)
    (w : InfinitePlace K) (t : ℝ) : ℂ :=
  if ht : 0 < t then FiniteNormalizedMellin.reflected R θ C L u κ w ⟨t, ht⟩ else 0

theorem directTest_eq_log (w : InfinitePlace K) {t : ℝ} (ht : 0 < t) :
    directTest R θ C L w t = ActualAnnularProfiles.directLog R θ C L w (Real.log t) := by
  simp [directTest, ActualAnnularProfiles.directLog, PositiveAxisLog.logEquiv,
    ht, Real.exp_log ht]

theorem reflectedProfile_eq_log (u : R.A.UnitQuotient) (κ : SixthLocalClasses K S)
    (w : InfinitePlace K) {t : ℝ} (ht : 0 < t) :
    reflectedProfile R θ C L u κ w t =
      ActualAnnularProfiles.reflectedLog R θ C L u κ w (Real.log t) := by
  simp [reflectedProfile, ActualAnnularProfiles.reflectedLog, PositiveAxisLog.logEquiv,
    ht, Real.exp_log ht]

variable (D : ThetaArithmeticData K S) (d : MarkedDatum K S)

/-- The precise statement to be supplied by the independently proved
automorphic and coefficient dictionary. This definition is not a local
input and is not used to claim the seed has been proved. -/
def LiteralSeed (w : InfinitePlace K) : Prop :=
  ∀ X : ℝ, 0 < X →
    completedThetaSum K S D θ (rowElement K S D d) d.puncture d.marks
      (directTest R θ C L w) X =
    ∑' i : ReflectionIndex K S d,
      ReflectedArithmetic.reflectedCoefficient K S D d i θ *
        reflectedProfile R θ C L (QuotientGroup.mk d.rowUnit)
          (frequencyClass K S D d i) w (ReflectedLimitProject.argument K S d X i)

def directCoefficient (cn : ExteriorIdeal K S × ExteriorIdeal K S) : ℂ :=
  completedTerm K S D θ (rowElement K S D d) d.puncture d.marks (fun _ => 1) 1 cn

def directArgument (X : ℝ) (cn : ExteriorIdeal K S × ExteriorIdeal K S) : ℝ :=
  exteriorNorm K S (completedIdeal K S cn.1 cn.2) / X

theorem completedTerm_eq_coefficient (V : ℝ → ℂ) (X : ℝ)
    (cn : ExteriorIdeal K S × ExteriorIdeal K S) :
    completedTerm K S D θ (rowElement K S D d) d.puncture d.marks V X cn =
      directCoefficient R θ D d cn * V (directArgument R X cn) := by
  unfold completedTerm directCoefficient
  dsimp only
  split_ifs <;> simp [directArgument]

theorem directCoefficient_norm_le_one (cn : ExteriorIdeal K S × ExteriorIdeal K S) :
    ‖directCoefficient R θ D d cn‖ ≤ 1 := by
  unfold directCoefficient completedTerm
  dsimp only
  split_ifs
  · simpa only [mul_one] using
      HeckeGeneral.ThetaSkeleton.Physical.ActualThetaAbsoluteDraft.norm_completedCoefficient_le_one
        K S D θ (rowElement K S D d) cn.1 cn.2
  · simp

theorem exp_neg_two_log {t : ℝ} (ht : 0 < t) :
    Real.exp (-2 * Real.log t) = ReflectedAbsolute.inverseSquare t := by
  simpa only [Real.exp_log ht, ReflectedAbsolute.inverseSquare] using
    (PositiveAxisLog.exp_inverse_sq (Real.log t)).symm

theorem direct_mass_summable {X : ℝ} (hX : 0 < X) :
    Summable (fun cn => ‖directCoefficient R θ D d cn‖ *
      Real.exp (-2 * Real.log (directArgument R X cn))) := by
  apply (PrimalLimitProject.summable_majorant K S 1 X).of_nonneg_of_le
    (fun _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
  intro cn
  rw [exp_neg_two_log (PrimalLimitProject.completed_argument_pos K S hX cn)]
  calc
    _ ≤ 1 * ReflectedAbsolute.inverseSquare (directArgument R X cn) :=
      mul_le_mul_of_nonneg_right (directCoefficient_norm_le_one R θ D d cn)
        (ReflectedAbsolute.inverseSquare_nonneg _)
    _ ≤ PrimalLimitProject.majorant K S 1 X cn := by
      simpa only [one_mul, PrimalLimitProject.majorant] using
        PrimalLimitProject.completed_argument_inverseSquare_le K S hX cn

theorem reflected_mass_summable {X : ℝ} (hX : 0 < X) :
    Summable (fun i : ReflectionIndex K S d =>
      ‖ReflectedArithmetic.reflectedCoefficient K S D d i θ‖ *
        Real.exp (-2 * Real.log (ReflectedLimitProject.argument K S d X i))) := by
  have h := ReflectedLimitProject.summable_majorant K S D d θ (B := 1) (by norm_num) hX
  simpa only [ReflectedLimitProject.majorant, mul_one,
    exp_neg_two_log (ReflectedLimitProject.argument_pos K S d hX _)] using h

private theorem direct_log_scale {X : ℝ} (hX : 0 < X) (u : ℝ)
    (cn : ExteriorIdeal K S × ExteriorIdeal K S) :
    Real.log (directArgument R (X * Real.exp (-u)) cn) =
      u + Real.log (directArgument R X cn) := by
  have hn := ReflectedArithmetic.exteriorNorm_pos K S (completedIdeal K S cn.1 cn.2)
  simp only [directArgument, Real.log_div hn.ne' (mul_pos hX (Real.exp_pos _)).ne',
    Real.log_div hn.ne' hX.ne', Real.log_mul hX.ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

private theorem reflected_log_scale {X : ℝ} (hX : 0 < X) (u : ℝ)
    (i : ReflectionIndex K S d) :
    Real.log (ReflectedLimitProject.argument K S d (X * Real.exp (-u)) i) =
      Real.log (ReflectedLimitProject.argument K S d X i) - u := by
  have he : ReflectedLimitProject.argument K S d (X * Real.exp (-u)) i =
      ReflectedLimitProject.argument K S d X i * Real.exp (-u) := by
    unfold ReflectedLimitProject.argument
    ring
  rw [he, Real.log_mul (ReflectedLimitProject.argument_pos K S d hX i).ne'
    (Real.exp_pos _).ne', Real.log_exp]
  ring

theorem logarithmic_seed (w : InfinitePlace K) (hseed : LiteralSeed R θ C L D d w)
    {X : ℝ} (hX : 0 < X) (u : ℝ) :
    (∑' cn, directCoefficient R θ D d cn *
      (ActualAnnularProfiles.localProfiles R θ C L (QuotientGroup.mk d.rowUnit) w).direct
        (u + Real.log (directArgument R X cn))) =
    ∑' i : ReflectionIndex K S d, ReflectedArithmetic.reflectedCoefficient K S D d i θ *
      (ActualAnnularProfiles.localProfiles R θ C L (QuotientGroup.mk d.rowUnit) w).reflected
        (frequencyClass K S D d i)
        (Real.log (ReflectedLimitProject.argument K S d X i) - u) := by
  have hz := mul_pos hX (Real.exp_pos (-u))
  have hs := hseed (X * Real.exp (-u)) hz
  unfold completedThetaSum at hs
  simp_rw [completedTerm_eq_coefficient,
    directTest_eq_log R θ C L w (PrimalLimitProject.completed_argument_pos K S hz _),
    direct_log_scale R hX u,
    reflectedProfile_eq_log R θ C L (QuotientGroup.mk d.rowUnit) _ w
      (ReflectedLimitProject.argument_pos K S d hz _),
    reflected_log_scale R d hX u] at hs
  exact hs

local instance : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
local instance : Countable (ReflectionIndex K S d) :=
  Countable.of_injective (ReflectedAbsoluteProject.reflectionEncode K S d)
    (ReflectedAbsoluteProject.reflectionEncode_injective K S d)

/-- The actual scalar Fubini theorem produces the positive-regularizer
identity; it is not an independent premise of the final limit step. -/
theorem regularized_identity (w : InfinitePlace K) (hseed : LiteralSeed R θ C L D d w)
    (V : SmoothAnnularTest) {ε X : ℝ} (hε : 0 < ε) (hX : 0 < X) :
    ActualRegularizerRemoval.RegularizedMarkedIdentity K S D d M θ V ε X := by
  let P := ActualAnnularProfiles.localProfiles R θ C L (QuotientGroup.mk d.rowUnit) w
  let J : AnnularTransfer.DeconvolverData P.M
      (fun t => mellin V.toFun ((t : ℂ) * Complex.I)) ε :=
    GammaDeconvolverProject.actualDeconvolver K S M θ V ε hε
  have hc := AnnularTransfer.regularized_reflection P
    (fun t => mellin V.toFun ((t : ℂ) * Complex.I))
    (directCoefficient R θ D d)
    (fun i => ReflectedArithmetic.reflectedCoefficient K S D d i θ)
    (fun cn => Real.log (directArgument R X cn))
    (fun i => Real.log (ReflectedLimitProject.argument K S d X i))
    (frequencyClass K S D d)
    (direct_mass_summable R θ D d hX) (reflected_mass_summable R θ D d hX)
    (logarithmic_seed R θ C L D d w hseed hX) ε J
  unfold ActualRegularizerRemoval.RegularizedMarkedIdentity completedThetaSum
  calc
    _ = ∑' cn, directCoefficient R θ D d cn *
        ScalarMellinConvolution.regularizedTest
          (fun t => mellin V.toFun ((t : ℂ) * Complex.I)) ε
          (Real.log (directArgument R X cn)) := by
      apply tsum_congr
      intro cn
      rw [completedTerm_eq_coefficient,
        TestMellinLimit.scalar_regularizedTest_eq (mellin V.toFun) ε
          (PrimalLimitProject.completed_argument_pos K S hX cn)]
      rfl
    _ = _ := hc
    _ = _ := by
      apply tsum_congr
      intro i
      exact (ScalarKernelProject.regularizedTerm_eq_scalar K S M θ D d V ε hX i).symm

theorem marked_reflection_of_literal_seed
    (hM : FiniteMellinAdmissible K S M) (w : InfinitePlace K)
    (hseed : LiteralSeed R θ C L D d w) (V : SmoothAnnularTest)
    {X : ℝ} (hX : 0 < X) :
    completedThetaSum K S D θ (rowElement K S D d) d.puncture d.marks V.toFun X =
      ∑' i : ReflectionIndex K S d, reflectedTerm K S D d i M θ V.toFun X := by
  letI : Finite (SixthLocalClasses K S) := by
    letI := primitive12_totallyComplex K R.A.zeta12 R.A.primitive_zeta12
    exact HeckeSkeleton.SixthLocalFinite.sixthLocalClasses_finite K S
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεpos (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hε₁ (n : ℕ) : ε n ≤ 1 := by
    dsimp [ε]
    exact (div_le_one (by positivity)).mpr (by positivity)
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  exact (ActualRegularizerRemoval.marked_reflection_of_regularized_identities
    K S D d M θ hM V ε hεpos hε₁ hε hX
    (fun n => regularized_identity R θ C L D d w hseed V (hεpos n) hX)).2.2

end ThetaGlobal.ActualAnnularTransfer
