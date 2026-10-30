module

public import ThetaGlobal.GlobalProjectDigitDescent

@[expose] public section

/-!
# Ordinary, punctured, and marked weights on an arbitrary support row

The auxiliary row records the finite set of exterior digit places only.
The weight at each place is selected independently of that row's
exponents.  Consequently an auxiliary squarefree row with support T
implements any finite T containing the original row, punctures, and
marks, using the exact upstream cover matrices and residue lifts.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section

namespace ThetaGlobal.GlobalProjectWeightedDigits

open NumberField DedekindZetaZeroFree DedekindZetaZeroFree.MomentSources
open DedekindZetaZeroFree.ThetaProfileHaarSheets
open DedekindZetaZeroFree.ThetaSheetExactUnfolding
open MeasureTheory
open scoped NumberField Classical Topology BigOperators

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)

open GlobalProjectDigitDescent

abbrev Places (m : ThetaReflectionData.Row R.A) :=
  ↥(ThetaDigitAverage.rowPrimes R.A m.val m.property)

abbrev Digits (m : ThetaReflectionData.Row R.A) :=
  ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)

def ReindexInvariant (m : ThetaReflectionData.Row R.A) (c : Digits R m → ℂ) : Prop :=
  ∀ (u : R.A.U) (d : Digits R m),
    c (ThetaExpansion.QuotientDescent.digitReindex R m u d) = c d

def tensorWeight (m : ThetaReflectionData.Row R.A)
    (j : Places R m → Fin 6) (marked : Places R m → Bool) (d : Digits R m) : ℂ :=
  ∏ p : Places R m,
    if marked p then (Fintype.card (ThetaDigitAverage.Residue p.val) : ℂ)⁻¹ else
      let hp := ((ThetaDigitAverage.rowPrimes_finite R.A m.val m.property).mem_toFinset.mp p.property).1
      sexticFourierMask (ThetaBranch.residueCharacter R.A R.σ ⟨p.val, hp⟩)
        (Characters.psi R ⟨p.val, hp⟩) (j p) (d p)

/-- This includes α_0 at every puncture and the constant 1/q at every
mark.  The local exponent j is independent of the auxiliary support row. -/
theorem tensorWeight_reindexInvariant (m : ThetaReflectionData.Row R.A)
    (j : Places R m → Fin 6) (marked : Places R m → Bool) :
    ReindexInvariant R m (tensorWeight R m j marked) := by
  intro u d
  unfold tensorWeight
  apply Finset.prod_congr rfl
  intro p _
  split_ifs
  · rfl
  · exact DigitMasks.mask_residueSixthUnit R ⟨p.val,
      ((ThetaDigitAverage.rowPrimes_finite R.A m.val m.property).mem_toFinset.mp p.property).1⟩
      u (j p) (d p)

theorem ordinaryWeight_reindexInvariant (m : ThetaReflectionData.Row R.A) :
    ReindexInvariant R m (digitWeight R m) :=
  ThetaExpansion.QuotientDescent.digitWeight_reindex R m

def average (m : ThetaReflectionData.Row R.A) (c : Digits R m → ℂ)
    (f : Functions R) (b : Bool) (y : R.A.G) : ℂ :=
  ∑ d : Digits R m, c d * f (signedArgument R m b y d)

theorem average_gamma (m : ThetaReflectionData.Row R.A) (c : Digits R m → ℂ)
    (hc : ReindexInvariant R m c)
    (f : Functions R) (hr : RationalDiagonalInvariant R f)
    (hext : GlobalProjectExterior.FullExteriorInvariant R f)
    (b : Bool) (γ : R.A.Gamma1) (y : R.A.G) :
    average R m c f b (γ.val.val * y) = average R m c f b y := by
  let δ : R.A.Gamma := ⟨γ.val.val, γ.property⟩
  obtain ⟨q, ⟨ε, hε, rfl⟩, hq⟩ := δ.property
  let u : R.A.U := ⟨ε, hε⟩
  have hγ : γ.val.val = R.A.diagonal (u.val ^ 6) := hq.symm
  rw [hγ]
  unfold average
  rw [← Equiv.sum_comp (ThetaExpansion.QuotientDescent.digitReindex R m u)]
  apply Finset.sum_congr rfl
  intro d _
  rw [hc u d, signed_term_reindex R f hr hext]

theorem average_continuous (m : ThetaReflectionData.Row R.A) (c : Digits R m → ℂ)
    (f : Functions R) (hf : Continuous f) (b : Bool) :
    Continuous (average R m c f b) := by
  apply continuous_finset_sum
  intro d _
  exact continuous_const.mul (hf.comp (DigitMasks.signedArgument_continuous R m b d))

def quotientAverage (L : R.A.G →* ℂ)
    (m : ThetaReflectionData.Row R.A) (c : Digits R m → ℂ)
    (f : Functions R) (b : Bool)
    (l : PositiveAxis) (q : SheetQuotient R.A l) : ℂ :=
  GlobalProjectUnfolding.weight R L R.probe.correction.B (Quotient.out q).val *
    average R m c f b (Quotient.out q).val

theorem quotientAverage_projection (L : R.A.G →* ℂ)
    (hL : ∀ γ : R.A.Gamma1, L γ.val.val = 1)
    (m : ThetaReflectionData.Row R.A) (c : Digits R m → ℂ)
    (hc : ReindexInvariant R m c)
    (f : Functions R) (hr : RationalDiagonalInvariant R f)
    (hext : GlobalProjectExterior.FullExteriorInvariant R f)
    (b : Bool) (l : PositiveAxis) (y : Sheet R.A l) :
    quotientAverage R L m c f b l (sheetProjection R.A l y) =
      GlobalProjectUnfolding.weight R L R.probe.correction.B y.val *
        average R m c f b y.val := by
  have he := Quotient.exact (Quotient.out_eq (sheetProjection R.A l y))
  obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp he)
  have hv := congrArg Subtype.val hγ
  change γ.val.val * y.val = (Quotient.out (sheetProjection R.A l y)).val at hv
  unfold quotientAverage
  rw [← hv, GlobalProjectUnfolding.weight_gamma R L R.probe.correction.B hL,
    average_gamma R m c hc f hr hext]

theorem quotientAverage_integrable (w : InfinitePlace F) (μG : Measure R.A.G)
    [μG.IsHaarMeasure] (L : R.A.G →* ℂ)
    (hL : ∀ γ : R.A.Gamma1, L γ.val.val = 1)
    (hLm : Measurable L) (hLn : ∀ y, ‖L y‖ = 1)
    (m : ThetaReflectionData.Row R.A) (c : Digits R m → ℂ)
    (hc : ReindexInvariant R m c)
    (f : Functions R) (hf : Continuous f) (hr : RationalDiagonalInvariant R f)
    (hext : GlobalProjectExterior.FullExteriorInvariant R f)
    (b : Bool) (l : PositiveAxis) :
    Integrable (quotientAverage R L m c f b l) (sheetQuotientHaar R.A w μG l) := by
  apply DigitMasks.quotient_integrable_of_continuous_bdd_weight R.A w μG l
    (average R m c f b) (GlobalProjectUnfolding.weight R L R.probe.correction.B)
    (quotientAverage R L m c f b l) (average_continuous R m c f hf b)
  · exact (DigitMasks.finite_class_measurable R.A
      (fun κ => if κ ∈ R.probe.correction.B then (1 : ℂ) else 0)).mul hLm.inv
  · intro y
    unfold GlobalProjectUnfolding.weight
    rw [norm_mul, norm_inv, hLn, inv_one, mul_one]
    split_ifs <;> simp
  · exact quotientAverage_projection R L hL m c hc f hr hext b l

end ThetaGlobal.GlobalProjectWeightedDigits
