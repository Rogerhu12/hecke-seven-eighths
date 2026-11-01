import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFullSupportFirstWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstDualOriginalExponent

/-!
# Numerical first terminals for the actual full-support source

The powerful-counting loss and the first mask loss are fixed before the
moving recipe, its original profiles and its real parameters. The
actual constructor supplies the sharp negative coefficient exponent,
the product window on nonzero Gram profiles and the full-support
inverse radius. Their length contributions cancel internally.

The tail seminorm and its analytic constant may be chosen by the
existing uniform first-stage theorem before applying this result.
This theorem then computes the numerical tail constant from the same
original physical windows. Neither a terminal estimate nor a final
exponent ledger is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical MeasureTheory
open HeckePort.Moments HeckePort.CenteredMomentCounting

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

/-- The same fixed constants bound the literal first dual-zero sum,
the original physical-tail budget and their sum.
The tail seminorm and constant are fixed analytic data, before every
source variable. The zero seminorm and all numerical constants are
selected here, also before those source variables. -/
theorem exists_canonical_full_support_first_terminal_bound
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (cap degree : ℕ) (bound ε : ℝ) (hbound : 0 ≤ bound) (hε : 0 < ε)
    (orders sTail : Finset (ℕ × ℕ)) (Ctail : ℝ) (hCtail : 0 ≤ Ctail)
    (Nsave decay : ℝ) (hNsave : 0 ≤ Nsave) (hdecay : 1 < decay) :
    ∃ (sZero : Finset (ℕ × ℕ)) (Czero Cerror Cterminal : ℝ),
      0 < Czero ∧ 0 ≤ Cerror ∧
      Cerror = Ctail * (2 * firstTailFieldConstant K *
        idealCountConstant K ^ (2 * (cap + 2))) ∧ 0 < Cterminal ∧
    ∀ {ω ψ : HeckeCharacter K}
      {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
      {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
      {Index : Type*} {data : Index → MomentData K ω ψ}
      (Q : CompleteMovingRowRecipe A P R data) (W : NormProfileRecipe data) (ξ : Index)
      (a : RealParameters) (Z t Y₁ Y₂ : ℝ)
      (C : A.GeneralArithmeticContext σ η hS)
      (B control annulus loss leftExponent rightExponent : ℝ),
      1 ≤ B → 1 ≤ control → B ≤ control ^ degree →
      1 ≤ annulus → 0 ≤ loss → loss ≤ 1 → loss ≤ ε / 4 →
      (data ξ).geometry.slotCount ≤ cap →
      annulus ^ (cap + 2) ≤ Z ^ loss →
    ∀ (centered : Bool) {floor padding : ℝ}
      (domain : PairedEngineDomain centered (data ξ) a Z Y₁ Y₂ floor padding),
      0 < Y₁ → 0 < Y₂ →
      a.n₁ ≤ leftExponent → a.n₂ ≤ rightExponent →
      Y₁ ≤ Z ^ leftExponent → Y₂ ≤ Z ^ rightExponent →
    ∀ {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain window : Set ℝ}
      (profiles : RawProfileWindow rowDomain heightDomain window
        (OriginalProfileAtomBounds.profileOrders orders) (data ξ) B),
      (∀ u ∈ pairedRows (data ξ) a Z, u ∈ rowDomain) →
      t ∈ heightDomain → window ⊆ Set.Iic annulus →
    ∀ (hcolumn : leftExponent + rightExponent + (data ξ).geometry.totalLength + loss ≤ bound)
      (hwidth : a.m + a.q ≤ bound)
      (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
        HeckeGeneral.Characters.localDifferentExponent K v = 0),
    let atoms := (Q.arithmeticAtoms ξ).constantAtoms (W.at ξ) a Z t;
    let raw := atoms.raw Y₁ Y₂;
    let gram := fun i j => ((atoms.values Y₁ Y₂).coefficient centered i *
      star ((atoms.values Y₁ Y₂).coefficient centered j)) • CanonicalRowBall.archTest K A.Sf 1;
    let radius := Q.fullSupportRadius Z (a.m + a.q) (zero_lt_one.trans domain.scale);
    let cutoff := Z ^ firstTailCutoffExponent (originalFirstPhysicalDegree cap bound) Nsave decay;
    let hcutoff : 1 ≤ cutoff := Real.one_le_rpow domain.scale.le
      (firstTailCutoffExponent_nonneg (originalFirstPhysicalDegree cap bound) Nsave decay hdecay);
    let zeroCost := ∑ DE : FirstZeroLabel raw.exteriorColumns raw.exteriorColumns
          raw.columnExterior raw.columnExterior,
        ‖((raw.originalFirstBlocks C DE).finiteSource
          (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) C
          raw.exteriorColumns raw.exteriorColumns gram ∅ radius cutoff hcutoff).dualZeroTerm
            μv hDiff finiteTest‖;
    let tailCost := Ctail * cutoff ^ (1 - decay) *
        firstBlockTailMass
          (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) C
          raw.exteriorColumns raw.exteriorColumns raw.columnExterior raw.columnExterior
          (raw.originalFirstBlocks C) sTail gram radius ∅;
    zeroCost / Z ^ (a.m + a.q) ≤
      Cterminal * control ^ firstDualOriginalProfileDegree cap degree * Z ^ ε ∧
    tailCost / Z ^ (a.m + a.q) ≤
      Cterminal * control ^ firstDualOriginalProfileDegree cap degree * Z ^ (-Nsave) ∧
    (zeroCost + tailCost) / Z ^ (a.m + a.q) ≤
      Cterminal * control ^ firstDualOriginalProfileDegree cap degree * Z ^ ε := by
  have hδ : 0 < ε / 4 := div_pos hε (by norm_num)
  have hγ := firstDualCountingLoss_pos bound ε hbound hε
  obtain ⟨sZero, Czero, hCzero, hzero⟩ :=
    first_dual_zero_diagonal_supported (σ := σ) (η := η) (hS := hS)
      (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      (μv := μv) finiteTest (2 * (cap + 2)) (firstDualCountingLoss bound ε) hγ
  let Cnum := 2 * firstTailFieldConstant K * idealCountConstant K ^ (2 * (cap + 2))
  have hCnum : 0 ≤ Cnum := mul_nonneg
    (mul_nonneg (by norm_num) firstTailFieldConstant_nonneg)
    (pow_nonneg (zero_le_one.trans (one_le_idealCountConstant K)) _)
  let Cerror := Ctail * Cnum
  have hCerror : 0 ≤ Cerror := mul_nonneg hCtail hCnum
  let maskConstant := originalFirstMaskConstant (K := K) bound (ε / 4) hbound hδ
  have hmaskConstant : 0 ≤ maskConstant :=
    (originalFirstMaskConstant_pos (K := K) bound (ε / 4) hbound hδ).le
  let zeroConstant := Czero * maskConstant * (4 * CanonicalRowBall.terminalSeminorm A sZero)
  let tailConstant := Cerror * (4 * CanonicalRowBall.terminalSeminorm A sTail)
  have hzconst : 0 ≤ zeroConstant :=
    mul_nonneg (mul_nonneg hCzero.le hmaskConstant)
      (mul_nonneg (by norm_num) (CanonicalRowBall.terminalSeminorm_nonneg sZero))
  have htconst : 0 ≤ tailConstant := mul_nonneg hCerror
    (mul_nonneg (by norm_num) (CanonicalRowBall.terminalSeminorm_nonneg sTail))
  let Cterminal := 1 + zeroConstant + tailConstant
  have hCterminal : 0 < Cterminal := by dsimp only [Cterminal]; linarith
  refine ⟨sZero, Czero, Cerror, Cterminal, hCzero, hCerror, rfl, hCterminal, ?_⟩
  intro ω ψ P R Index data Q W ξ a Z t Y₁ Y₂ C B control annulus loss
    leftExponent rightExponent hB hcontrol hprofileBound hannulus hloss hlossOne hlossBudget
    hcap hannulusZ centered floor padding domain hY₁ hY₂ hleftExponent hrightExponent
    hY₁le hY₂le rowDomain heightDomain window profiles hrows ht hwindow hcolumn hwidth hDiff
  dsimp only
  let atoms := (Q.arithmeticAtoms ξ).constantAtoms (W.at ξ) a Z t
  let raw := atoms.raw Y₁ Y₂
  let gram := fun i j => ((atoms.values Y₁ Y₂).coefficient centered i *
    star ((atoms.values Y₁ Y₂).coefficient centered j)) • CanonicalRowBall.archTest K A.Sf 1
  have hz : 0 < Z := zero_lt_one.trans domain.scale
  let radius := Q.fullSupportRadius Z (a.m + a.q) hz
  let cutoff := Z ^ firstTailCutoffExponent (originalFirstPhysicalDegree cap bound) Nsave decay
  have hcutoff : 1 ≤ cutoff := Real.one_le_rpow domain.scale.le
    (firstTailCutoffExponent_nonneg (originalFirstPhysicalDegree cap bound) Nsave decay hdecay)
  let T := Q.canonicalFullSupportFirstWindows W ξ a Z t Y₁ Y₂ C cap orders
    B annulus loss leftExponent rightExponent bound Nsave decay
    hB hannulus hloss hbound hcap hannulusZ centered domain hY₁ hY₂
    hleftExponent hrightExponent hY₁le hY₂le profiles hrows ht hwindow hcolumn hwidth sTail sZero
  have htotal : a.n₁ + a.n₂ + (data ξ).geometry.totalLength ≤ bound := by linarith
  have hcoefficient : T.zeroProfileExponent =
      -(a.n₁ + a.n₂ + (data ξ).geometry.totalLength) := by
    change 2 * (-(a.n₁ + a.n₂ + (data ξ).geometry.totalLength) / 2) = _
    ring
  have hproduct : T.zeroProductExponent =
      2 * (a.n₁ + a.n₂ + (data ξ).geometry.totalLength + loss) := rfl
  have hradius : T.zeroInverseRadiusExponent ≤
      (a.m + a.q) - Q.fullSupportLength Z := le_rfl
  have hzeroProfile : T.zeroProfileConstant ≤
      (4 * CanonicalRowBall.terminalSeminorm A sZero) *
        control ^ firstDualOriginalProfileDegree cap degree :=
    first_dual_original_profile_constant_le cap degree B control
      (CanonicalRowBall.terminalSeminorm A sZero) (zero_le_one.trans hB)
      hcontrol (CanonicalRowBall.terminalSeminorm_nonneg sZero) hprofileBound
  have htailProfile : T.tailProfileConstant ≤
      (4 * CanonicalRowBall.terminalSeminorm A sTail) *
        control ^ firstDualOriginalProfileDegree cap degree :=
    first_dual_original_profile_constant_le cap degree B control
      (CanonicalRowBall.terminalSeminorm A sTail) (zero_le_one.trans hB)
      hcontrol (CanonicalRowBall.terminalSeminorm_nonneg sTail) hprofileBound
  have hzeroScalar :
      (Czero * T.zeroAmplitude hbound (ε / 4) hδ *
          Z ^ (T.zeroProductExponent * firstDualCountingLoss bound ε)) / Z ^ (a.m + a.q) ≤
        zeroConstant * control ^ firstDualOriginalProfileDegree cap degree * Z ^ ε := by
    have hb := T.normalized_zero_le_original_lengths hbound (ε / 4) hδ
      1 (a.m + a.q) Czero (a.n₁ + a.n₂ + (data ξ).geometry.totalLength)
      bound (Q.fullSupportLength Z) loss ε hCzero.le hbound htotal
      (Q.fullSupportLength_nonneg Z domain.scale) hlossOne hlossBudget le_rfl hε
      hcoefficient hproduct hradius
    simp only [Nat.cast_one, one_mul] at hb
    apply hb.trans
    calc
      _ ≤ (Czero * maskConstant) *
          ((4 * CanonicalRowBall.terminalSeminorm A sZero) *
            control ^ firstDualOriginalProfileDegree cap degree) * Z ^ ε :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hzeroProfile (mul_nonneg hCzero.le hmaskConstant))
          (Real.rpow_nonneg hz.le _)
      _ = _ := by dsimp only [zeroConstant]; ring
  have htailScalar :
      (Cerror * T.tailProfileConstant * Z ^ (-Nsave)) / Z ^ (a.m + a.q) ≤
        tailConstant * control ^ firstDualOriginalProfileDegree cap degree * Z ^ (-Nsave) := by
    have hb := T.normalized_tail_le 1 (a.m + a.q) Cerror (-Nsave) hCerror
      (by linarith [domain.width_nonneg])
    simp only [Nat.cast_one, one_mul] at hb
    apply hb.trans
    calc
      _ ≤ Cerror * ((4 * CanonicalRowBall.terminalSeminorm A sTail) *
          control ^ firstDualOriginalProfileDegree cap degree) * Z ^ (-Nsave) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htailProfile hCerror)
          (Real.rpow_nonneg hz.le _)
      _ = _ := by dsimp only [tailConstant]; ring
  have hzeroActual := hzero C raw.exteriorColumns raw.exteriorColumns
    raw.columnExterior raw.columnExterior (raw.originalFirstBlocks C) gram hDiff radius ∅
    cutoff hcutoff T.windows.factors T.windows.factors_injective T.windows.factor_product
    (Z ^ T.zeroProductExponent) (T.zeroAmplitude hbound (ε / 4) hδ)
    (Real.one_le_rpow domain.scale.le T.zeroProductExponent_nonneg)
    (T.zeroAmplitude_nonneg hbound (ε / 4) hδ) T.zero_product_norm
    (T.zero_normalization hbound (ε / 4) hδ)
  rw [← Real.rpow_mul hz.le] at hzeroActual
  have htailActual := T.tailMass_bound hdecay Ctail hCtail
  have hpower : 0 ≤ control ^ firstDualOriginalProfileDegree cap degree :=
    pow_nonneg (zero_le_one.trans hcontrol) _
  have hzeroConstant_le : zeroConstant ≤ Cterminal := by dsimp only [Cterminal]; linarith
  have htailConstant_le : tailConstant ≤ Cterminal := by dsimp only [Cterminal]; linarith
  have hzeroPaid := (div_le_div_of_nonneg_right hzeroActual
    (Real.rpow_nonneg hz.le (a.m + a.q))).trans hzeroScalar
  have htailPaid := (div_le_div_of_nonneg_right htailActual
    (Real.rpow_nonneg hz.le (a.m + a.q))).trans htailScalar
  refine ⟨?_, ?_, ?_⟩
  · exact hzeroPaid.trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hzeroConstant_le hpower)
          (Real.rpow_nonneg hz.le _))
  · exact htailPaid.trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htailConstant_le hpower)
          (Real.rpow_nonneg hz.le _))
  · rw [add_div]
    calc
      _ ≤ zeroConstant * control ^ firstDualOriginalProfileDegree cap degree * Z ^ ε +
          tailConstant * control ^ firstDualOriginalProfileDegree cap degree * Z ^ (-Nsave) :=
        add_le_add hzeroPaid htailPaid
      _ ≤ zeroConstant * control ^ firstDualOriginalProfileDegree cap degree * Z ^ ε +
          tailConstant * control ^ firstDualOriginalProfileDegree cap degree * Z ^ ε :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le domain.scale.le (by linarith : -Nsave ≤ ε))
          (mul_nonneg htconst hpower))
      _ = (zeroConstant + tailConstant) *
          control ^ firstDualOriginalProfileDegree cap degree * Z ^ ε := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (by dsimp only [Cterminal]; linarith : zeroConstant + tailConstant ≤ Cterminal) hpower)
        (Real.rpow_nonneg hz.le _)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.exists_canonical_full_support_first_terminal_bound
