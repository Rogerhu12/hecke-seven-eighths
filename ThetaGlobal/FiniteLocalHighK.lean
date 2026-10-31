import ThetaGlobal.FiniteFixedSource
import ThetaGlobal.FiniteHighKWeyl
import ThetaGlobal.FiniteDirectMellin

/-!
# Explicit local high K-type Mellin inputs and their normalization

Every assumed formula below concerns one completed archimedean
representation, one actual vector, and one local Haar integral.  The
finite table, global tensor, Haar disintegration and reflection identity
are not fields.  In particular C₀ is the ratio of the actual cutoff
volume and the two products of local Mellin constants.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
noncomputable section

namespace ThetaGlobal.FiniteLocalHighK

open NumberField MeasureTheory DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources
open DedekindZetaZeroFree.KPCplxCharacterHaar
open DedekindZetaZeroFree.FourierContinuation.ComplexLines
open DedekindZetaZeroFree.KPLiteralScalarHCCompactOrbit
open DedekindZetaZeroFree.ThetaProfileHaarSheets
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton.Global
open scoped NumberField Classical BigOperators

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (θ : HeckeCharacter F) (C : FiniteFixedSource.Source R θ)

def localArgument (w : InfinitePlace F) (reflected : Bool) (z : w.Completionˣ) : ComplexPGL2 :=
  Matrix.ProjGenLinGroup.mk
    (KPCplxCharacterHaar.diagonal
      (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (R.A.complex_place w)).toMonoidHom z) * if reflected then weyl else 1)

def localProfile
    (M : KPCplxActualImage.Theta traceFrequency →L[ℂ] ℂ)
    (φ : KPGlobalResidualConstruction.complexCore)
    (w : InfinitePlace F) (reflected : Bool) (z : w.Completionˣ) : ℂ :=
  (if reflected then (infiniteComponent F w θ z : ℂ)⁻¹
    else (infiniteComponent F w θ z : ℂ)) *
    M (KPCplxActualImage.imageAction traceFrequency (localArgument R w reflected z)
      (harmonicInclusion φ)) / M (harmonicInclusion φ)

private theorem complexDiagonal_inv (z : ℂˣ) :
    (KPCplxCharacterHaar.diagonal z)⁻¹ = KPCplxCharacterHaar.diagonal z⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [KPCplxCharacterHaar.diagonal, Matrix.mul_apply, Fin.sum_univ_two]

private theorem complexDiagonal_continuous : Continuous KPCplxCharacterHaar.diagonal := by
  have hv : Continuous (fun z : ℂˣ =>
      (KPCplxCharacterHaar.diagonal z : Matrix (Fin 2) (Fin 2) ℂ)) := by
    change Continuous (fun z : ℂˣ => !![(z : ℂ), 0; 0, 1])
    fun_prop
  apply Units.continuous_iff.mpr
  refine ⟨hv, ?_⟩
  simpa only [complexDiagonal_inv] using hv.comp continuous_inv

theorem localArgument_continuous (w : InfinitePlace F) (reflected : Bool) :
    Continuous (localArgument R w reflected) := by
  have he : Continuous (Units.map
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (R.A.complex_place w)).toMonoidHom) :=
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (R.A.complex_place w)).continuous.units_map _
  exact (continuous_coinduced_rng : Continuous
    (Matrix.ProjGenLinGroup.mk : ComplexGL2 → ComplexPGL2)).comp
      ((complexDiagonal_continuous.comp he).mul continuous_const)

/-- Local regularity follows from the actual completed representation's
jointly continuous action and its continuous Whittaker functional. -/
theorem localProfile_continuous
    (M : KPCplxActualImage.Theta traceFrequency →L[ℂ] ℂ)
    (φ : KPGlobalResidualConstruction.complexCore)
    (w : InfinitePlace F) (reflected : Bool) :
    Continuous (localProfile R θ M φ w reflected) := by
  have hθ : Continuous (fun z : w.Completionˣ =>
      (infiniteComponent F w θ z : ℂ)) :=
    continuous_subtype_val.comp (infiniteComponent F w θ).continuous
  have hp : Continuous (fun z : w.Completionˣ =>
      if reflected then (infiniteComponent F w θ z : ℂ)⁻¹
      else (infiniteComponent F w θ z : ℂ)) := by
    cases reflected
    · simpa using hθ
    · simpa using hθ.inv₀ (fun z => Circle.coe_ne_zero _)
  have hm : Continuous (fun z : w.Completionˣ =>
      M (KPCplxActualImage.imageAction traceFrequency (localArgument R w reflected z)
        (harmonicInclusion φ))) :=
    M.continuous.comp ((KPCplxActualImage.imageAction_continuous traceFrequency).comp
      ((localArgument_continuous R w reflected).prodMk continuous_const))
  exact (hp.mul hm).div_const _

def gammaPair (w : InfinitePlace F) (s : ℂ) : ℂ :=
  Complex.Gamma ((archShift F θ ⟨w, R.A.complex_place w⟩ : ℂ) + s +
    Complex.I * archRadial F θ ⟨w, R.A.complex_place w⟩ + 1 / 6) *
  Complex.Gamma ((archShift F θ ⟨w, R.A.complex_place w⟩ : ℂ) + s +
    Complex.I * archRadial F θ ⟨w, R.A.complex_place w⟩ - 1 / 6)

def directGammaPair (w : InfinitePlace F) (s : ℂ) : ℂ :=
  Complex.Gamma ((archShift F θ ⟨w, R.A.complex_place w⟩ : ℂ) + s -
    Complex.I * archRadial F θ ⟨w, R.A.complex_place w⟩ + 1 / 6) *
  Complex.Gamma ((archShift F θ ⟨w, R.A.complex_place w⟩ : ℂ) + s -
    Complex.I * archRadial F θ ⟨w, R.A.complex_place w⟩ - 1 / 6)

/-- Permitted local archimedean inputs.  All functionals and actions are
those of the actual completed exceptional representation. -/
structure Input where
  vector : InfinitePlace F → KPGlobalResidualConstruction.complexCore
  functional : InfinitePlace F → KPCplxActualImage.Theta traceFrequency →L[ℂ] ℂ
  whittaker : ∀ w, functional w ∈
    KPCplxWhittakerUnique.whittakerSpace traceFrequency traceCharacter
  functional_nonzero : ∀ w, functional w (harmonicInclusion (vector w)) ≠ 0
  source_nonzero : ∀ w, C.projected.base.factorization.ell (Sum.inl w) (vector w) ≠ 0
  scale : InfinitePlace F → ℝ
  scale_pos : ∀ w, 0 < scale w
  directConstant : InfinitePlace F → ℂ
  directConstant_nonzero : ∀ w, directConstant w ≠ 0
  reflectedConstant : InfinitePlace F → ℂ
  reflectedConstant_nonzero : ∀ w, reflectedConstant w ≠ 0
  direct_integrable : ∀ (w : InfinitePlace F) (s : ℂ), -(1 / 3 : ℝ) < s.re →
    Integrable (fun z : w.Completionˣ =>
      localProfile R θ (functional w) (vector w) w false z *
        ((‖z.val‖ ^ 2 : ℝ) : ℂ) ^ s)
      (archHaar R.A w (C.transport.angularHaar w))
  reflected_integrable : ∀ (w : InfinitePlace F) (s : ℂ), -(1 / 3 : ℝ) < s.re →
    Integrable (fun z : w.Completionˣ =>
      localProfile R θ (functional w) (vector w) w true z *
        ((‖z.val‖ ^ 2 : ℝ) : ℂ) ^ s)
      (archHaar R.A w (C.transport.angularHaar w))
  direct_bound : ∀ (w : InfinitePlace F) (σ : ℝ), -(1 / 3 : ℝ) < σ →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : w.Completionˣ,
      ‖localProfile R θ (functional w) (vector w) w false z‖ ≤
        B * (‖z.val‖ ^ 2 : ℝ) ^ (-σ)
  reflected_bound : ∀ (w : InfinitePlace F) (σ : ℝ), -(1 / 3 : ℝ) < σ →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : w.Completionˣ,
      ‖localProfile R θ (functional w) (vector w) w true z‖ ≤
        B * (‖z.val‖ ^ 2 : ℝ) ^ (-σ)
  direct_mellin : ∀ (w : InfinitePlace F) (s : ℂ), -(1 / 3 : ℝ) < s.re →
    (∫ z : w.Completionˣ,
      localProfile R θ (functional w) (vector w) w false z *
        ((‖z.val‖ ^ 2 : ℝ) : ℂ) ^ s ∂archHaar R.A w (C.transport.angularHaar w)) =
      directConstant w * (scale w : ℂ) ^ s * directGammaPair R θ w s
  reflected_mellin : ∀ (w : InfinitePlace F) (s : ℂ), -(1 / 3 : ℝ) < s.re →
    (∫ z : w.Completionˣ,
      localProfile R θ (functional w) (vector w) w true z *
        ((‖z.val‖ ^ 2 : ℝ) : ℂ) ^ s ∂archHaar R.A w (C.transport.angularHaar w)) =
      reflectedConstant w * (scale w : ℂ) ^ s * gammaPair R θ w s

variable (L : Input R θ C)

def A₀ : ℝ := ∏ w, L.scale w

theorem A₀_pos : 0 < A₀ R θ C L :=
  Finset.prod_pos (fun w _ => L.scale_pos w)

def directConstant : ℂ := ∏ w, L.directConstant w

def reflectedConstant : ℂ := ∏ w, L.reflectedConstant w

theorem directConstant_nonzero : directConstant R θ C L ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun w _ => L.directConstant_nonzero w)

theorem reflectedConstant_nonzero : reflectedConstant R θ C L ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun w _ => L.reflectedConstant_nonzero w)

def C₀ : ℂ :=
  FiniteMellinRatio.normalization
    (FiniteDirectMellin.cutoffVolume R C.transport C.projected.cutoffs : ℂ)
    (directConstant R θ C L) (reflectedConstant R θ C L)

theorem C₀_ne_zero : C₀ R θ C L ≠ 0 :=
  FiniteMellinRatio.normalization_ne_zero
    (Complex.ofReal_ne_zero.mpr
      (FiniteDirectMellin.cutoffVolume_pos R C.transport C.projected.cutoffs).ne')
    (directConstant_nonzero R θ C L) (reflectedConstant_nonzero R θ C L)

def finiteMellinData : FiniteMellinData F
    (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) :=
  ProjectedFiniteMellin.targetFiniteMellinData R C.projected.base.factorization C.transport
    (C₀ R θ C L) (C₀_ne_zero R θ C L) (A₀ R θ C L) (A₀_pos R θ C L) θ

theorem archRatio_local (u : R.A.UnitQuotient) (w : InfinitePlace F) (a : ComplexPGL2) :
    FiniteFullProduct.archRatio R C.projected.base.factorization
      (ProjectedFiniteMellin.frozenStage R C.projected.base.factorization u)
      (FiniteHighKTensor.tuple R C.projected.base.factorization u L.vector) w a =
        L.functional w (KPCplxActualImage.imageAction traceFrequency a
          (harmonicInclusion (L.vector w))) /
          L.functional w (harmonicInclusion (L.vector w)) := by
  exact C.localArchRatio _ _ w
    (FiniteCoreProduct.arch_mem R C.projected.base.factorization _
      (ProjectedFiniteMellin.frozenStage_exact R C.projected.base.factorization u) w)
    (FiniteHighKTensor.source_scalar_nonzero R C.projected.base.factorization
      (FiniteFixedSource.Source.period_nonzero R θ C) u L.vector L.source_nonzero)
    (L.functional w) (L.whittaker w) (L.functional_nonzero w) a

theorem reflected_archLocal (u : R.A.UnitQuotient) (w : InfinitePlace F)
    (z : w.Completionˣ) :
    FiniteHighKWeyl.archLocal R C.projected.base.factorization θ u L.vector w z =
      localProfile R θ (L.functional w) (L.vector w) w true z := by
  rw [FiniteHighKWeyl.archLocal, archRatio_local R θ C L]
  simp [localProfile, localArgument, FiniteHighKWeyl.archArgument, mul_div_assoc]

end ThetaGlobal.FiniteLocalHighK

#print axioms ThetaGlobal.FiniteLocalHighK.C₀_ne_zero
#print axioms ThetaGlobal.FiniteLocalHighK.archRatio_local
