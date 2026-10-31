import HeckeSkeleton.LowEnergy.ActualBlockEnergy
import HeckeSkeleton.LowEnergy.BlockPolynomial
import HeckeSkeleton.LowEnergy.PhysicalBlockPolynomial

/-!
# General completed scales in the actual reflected block

The completed scale X is independent of the active mark P.  Consequently
both powers of P remain in the conductor denominator.  The frozen datum
retains an arbitrary squarefree puncture, and the theorem is uniform in
the annular test, its support, all four ideal ranges, all frozen states,
and arbitrary bounded active-mark coefficients.

The coefficient and masks are the literal coefficients of
`MarkedThetaReflection`; `source_reflectedTerm` identifies every genuine
summand before the common Mellin profile is estimated.  Only the two
original sieves and the original Mellin-kernel input are analytic inputs.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.GeneralReflectedBlock

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckePort.CenteredMomentGenerator
open HeckeSkeleton.LowEnergy.ActualReflection HeckeSkeleton.LowEnergy.ActualSymbols
open HeckeSkeleton.LowEnergy.ActualSieveDictionary HeckeSkeleton.LowEnergy.ActualRawHybrid
open HeckeSkeleton.LowEnergy.ActualReflectionReindex HeckeSkeleton.LowEnergy.ActualSeparatedBlock
open HeckeSkeleton.LowEnergy.ActualBlockEnergy HeckeSkeleton.LowEnergy.ActualHybridEntry
open HeckeSkeleton.LowEnergy.ActualFrozenIndependence
open HeckeSkeleton.LowEnergy.ActualFrozenMajorant HeckeSkeleton.LowEnergy.ActualFrozenCube
open HeckeSkeleton.LowEnergy.ActualGeneratorClasses
open HeckeSkeleton.LowEnergy.ClassSlices HeckeSkeleton.LowEnergy.ActualClassSlices
open scoped Classical BigOperators NumberField

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

/-- The ordinary completed scale retains both active-mark norm powers. -/
def baseScale (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
    (X : ℝ) : ℝ :=
  X * exteriorNorm K S s.minimum / exteriorNorm K S (primeSetIdeal K S s.active) ^ 2

def normalizedScale (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
    (X Klo Plo Clo Blo : ℝ) : ℝ :=
  baseScale K S f s X * Clo * Blo ^ 3 / (Klo ^ 2 * Plo ^ 2)

theorem normalizedScale_pos (f : FixedData K S)
    (s : FrozenState K S f.frozen f.puncture) {X Klo Plo Clo Blo : ℝ}
    (hX : 0 < X) (hK : 0 < Klo) (hP : 0 < Plo) (hC : 0 < Clo) (hB : 0 < Blo) :
    0 < normalizedScale K S f s X Klo Plo Clo Blo := by
  have hA := exteriorNorm_pos K S s.minimum
  have hF := exteriorNorm_pos K S (primeSetIdeal K S s.active)
  unfold normalizedScale baseScale
  positivity

theorem argument_normalized (f : FixedData K S)
    (s : FrozenState K S f.frozen f.puncture)
    (X Klo Plo Clo Blo : ℝ) (k P c b : Ideal (𝓞 K))
    (hK : 0 < Klo) (hP : 0 < Plo) (hC : 0 < Clo) (hB : 0 < Blo) :
    CommonMellin.argument (baseScale K S f s X)
      (safeNorm k) (safeNorm P) (safeNorm c) (safeNorm b) =
    CommonMellin.argument (normalizedScale K S f s X Klo Plo Clo Blo)
      (safeNorm k / Klo) (safeNorm P / Plo) (safeNorm c / Clo) (safeNorm b / Blo) := by
  unfold CommonMellin.argument normalizedScale
  have hk := (safeNorm_pos K k).ne'
  have hp := (safeNorm_pos K P).ne'
  field_simp [hK.ne', hP.ne', hC.ne', hB.ne', hk, hp]
  <;> ring

/-- The general kernel is separated on the same one common Mellin line,
with the row-type factor on both the row and the active mark. -/
theorem kernel_separation_at_zero
    {F : FiniteMellinData K S} (θ : HeckeCharacter K) (hKernel : MellinKernelInput K S F θ)
    (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S) (V : SmoothAnnularTest)
    {Y d P n b : ℝ} (hY : 0 < Y) (hd : 0 < d) (hP : 0 < P)
    (hn : 0 < n) (hb : 0 < b) :
    mellinReflectionKernel K S F θ u κ V.toFun 0 (CommonMellin.argument Y d P n b) =
      (CommonMellinTail.scalar Y : ℂ) * ∫ t : ℝ,
        ActualCommonMellinTail.profile F θ u κ V Y t *
        CommonMellinTail.rowFactor Y d t * CommonMellinTail.rowFactor Y P t *
        CommonMellinTail.columnFactor Y n b t := by
  rw [hKernel.line_independent V u κ 0 (CommonMellinTail.line Y)
    (CommonMellin.argument Y d P n b) (by norm_num)
    (by linarith [(CommonMellinTail.line_bounds Y).1])
    (CommonMellin.argument_pos hY hd hP hn hb)]
  unfold mellinReflectionKernel
  repeat rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  have hc := CommonMellin.argument_cpow hY hd hP hn hb (CommonMellinTail.vertical Y t)
  unfold kernelIntegrand
  change (2 * (Real.pi : ℂ))⁻¹ *
    (mellin V.toFun (-CommonMellinTail.vertical Y t) *
      reflectionMultiplier K S F θ u κ (CommonMellinTail.vertical Y t) *
      (CommonMellin.argument Y d P n b : ℂ) ^ (-CommonMellinTail.vertical Y t)) = _
  rw [hc]
  unfold ActualCommonMellinTail.profile ActualCommonMellinTail.amplitude
    CommonMellinTail.density CommonMellinTail.phase CommonMellinTail.rowFactor
    CommonMellinTail.columnFactor
  have hscalar : (CommonMellinTail.scalar Y : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (CommonMellinTail.scalar_pos hY).ne'
  field_simp [hscalar]
  <;> ring

/-- Exact equality with the actual source reflection, for arbitrary X. -/
theorem source_reflectedTerm (f : FixedData K S)
    (s : FrozenState K S f.frozen f.puncture)
    (k P : ExteriorIdeal K S) (hk : RowAdmissible K S f k)
    (hP : MarkAdmissible K S f P) (hkP : IsCoprime k.val.val P.val.val)
    (cb : FrozenColumn K S s) (hPb : IsCoprime P.val.val cb.val.2.val.val)
    (hD : AllowedGeneratorInput K S D)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K) (V : ℝ → ℂ) (X : ℝ) :
    reflectedTerm K S D (sourceDatum K S f k P hk hP hkP)
      (sourceIndex K S f s k P hk hP hkP cb hPb) F θ V X =
    inactiveWeight K S f * rowCoefficient K S D θ f s k *
      hybridAtom K S D (markCoefficient K S D θ f s P)
        (commonDualCoefficient K S D θ (baseDatum K S f) s cb)
        k.val.val P.val.val cb.val.1.val.val cb.val.2.val.val *
      mellinReflectionKernel K S F θ (QuotientGroup.mk f.rowUnit)
        (blockFrequency (frozenClass K S D f s) (generatorLocalClass K S D k)
          (generatorLocalClass K S D P) (generatorLocalClass K S D cb.val.1)
          (generatorLocalClass K S D cb.val.2)) V 0
        (CommonMellin.argument (baseScale K S f s X)
          (exteriorNorm K S k) (exteriorNorm K S P)
          (exteriorNorm K S cb.val.1) (exteriorNorm K S cb.val.2)) := by
  rw [reflectedTerm_eq_hybridAtom K S D hD]
  rw [source_inactive K S f s k P hk hP hkP cb hPb,
    source_minimum K S f s k P hk hP hkP cb hPb,
    source_markedIdeal K S f s k P hk hP hkP cb hPb,
    source_fullCube K S f s k P hk hP hkP cb hPb,
    ← fullCubeCoefficient_frozenOnly,
    source_coefficient K S D f s k P hk hP hkP cb hPb θ,
    source_frequency K S D f s k P hk hP hkP cb hPb hD]
  dsimp only [sourceDatum, sourceIndex, sourceCoordinates, fromCoordinates,
    activeFrozenIdeal, frequencyUnit, baseDatum]
  have harg :
      X * exteriorNorm K S s.minimum * exteriorNorm K S cb.val.1 *
          exteriorNorm K S cb.val.2 ^ 3 /
        (exteriorNorm K S k * exteriorNorm K S (primeSetIdeal K S s.active) *
          exteriorNorm K S P) ^ 2 =
      CommonMellin.argument (baseScale K S f s X)
        (exteriorNorm K S k) (exteriorNorm K S P)
        (exteriorNorm K S cb.val.1) (exteriorNorm K S cb.val.2) := by
    unfold CommonMellin.argument baseScale
    have hact := (exteriorNorm_pos K S (primeSetIdeal K S s.active)).ne'
    have hk0 := (exteriorNorm_pos K S k).ne'
    have hp0 := (exteriorNorm_pos K S P).ne'
    field_simp [hact, hk0, hp0]
    <;> ring
  rw [harg]
  rfl

variable (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)

/-- The mark Fourier phase has exponent 2w at a fixed completed scale. -/
def modeMark (θ : HeckeCharacter K) (q : FourClasses (SixthLocalClasses K S))
    (markWeight : Ideal (𝓞 K) → ℂ) (Y Plo t : ℝ) (P : Ideal (𝓞 K)) : ℂ :=
  markWeight P * ordinaryMark K S D f s θ q P *
    CommonMellinTail.rowFactor Y (safeNorm P / Plo) t

theorem continuous_modeMark (θ : HeckeCharacter K) (q : FourClasses (SixthLocalClasses K S))
    (markWeight : Ideal (𝓞 K) → ℂ) (Y Plo : ℝ) (hP : 0 < Plo) (P : Ideal (𝓞 K)) :
    Continuous (fun t => modeMark K S D f s θ q markWeight Y Plo t P) :=
  (continuous_rowFactor Y _ (div_pos (safeNorm_pos K P) hP)).const_mul _

theorem modeMark_norm_le (θ : HeckeCharacter K)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (q : FourClasses (SixthLocalClasses K S))
    (markWeight : Ideal (𝓞 K) → ℂ) (A Y Plo t : ℝ) (P : Ideal (𝓞 K))
    (hA : 0 ≤ A) (hw : ‖markWeight P‖ ≤ A)
    (hP0 : 1 ≤ safeNorm P / Plo) (hP1 : safeNorm P / Plo ≤ 2) :
    ‖modeMark K S D f s θ q markWeight Y Plo t P‖ ≤ 16 * A := by
  rw [modeMark, norm_mul, norm_mul]
  have hw' : ‖markWeight P‖ * ‖ordinaryMark K S D f s θ q P‖ ≤ A := by
    simpa only [mul_one] using mul_le_mul hw
      (ordinaryMark_norm_le_one K S D f s θ hθ q P) (norm_nonneg _) hA
  have h := mul_le_mul hw' (CommonMellinTail.norm_rowFactor_le (Y := Y) hP0 hP1 t)
    (norm_nonneg _) hA
  simpa only [mul_comm A] using h

def slicedBlock (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (q : FourClasses (SixthLocalClasses K S)) (markWeight : Ideal (𝓞 K) → ℂ)
    (V : ℝ → ℂ) (Z : ℝ)
    (ps cs bs : Finset (Ideal (𝓞 K))) (k : Ideal (𝓞 K)) : ℂ :=
  inactiveWeight K S f * ordinaryRow K S D f s θ q k *
    ∑ P ∈ ps, ∑ c ∈ cs, ∑ b ∈ bs,
      (markWeight P * ordinaryMark K S D f s θ q P) * ordinaryColumn K S D f s θ q c b *
      FiniteHybridIntegral.hybridKernel (cubicKernel K S D) (quadraticKernel K S D) k P c b *
      mellinReflectionKernel K S F θ (QuotientGroup.mk f.rowUnit)
        (blockFrequency (frozenClass K S D f s) q.1.1 q.1.2 q.2.1 q.2.2) V 0
        (CommonMellin.argument (baseScale K S f s Z)
          (safeNorm k) (safeNorm P) (safeNorm c) (safeNorm b))

theorem slicedBlock_eq_integral [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ : HeckeCharacter K) (hKernel : MellinKernelInput K S F θ)
    (q : FourClasses (SixthLocalClasses K S)) (markWeight : Ideal (𝓞 K) → ℂ)
    (V : SmoothAnnularTest)
    (Z Klo Plo Clo Blo : ℝ)
    (hZ : 0 < Z) (hK : 0 < Klo) (hP : 0 < Plo) (hC : 0 < Clo) (hB : 0 < Blo)
    (ps cs bs : Finset (Ideal (𝓞 K))) (k : Ideal (𝓞 K))
    (hk0 : 1 ≤ safeNorm k / Klo) (hk1 : safeNorm k / Klo ≤ 2)
    (hp : ∀ P ∈ ps, 1 ≤ safeNorm P / Plo ∧ safeNorm P / Plo ≤ 2)
    (hc : ∀ c ∈ cs, 1 ≤ safeNorm c / Clo ∧ safeNorm c / Clo ≤ 2)
    (hb : ∀ b ∈ bs, 1 ≤ safeNorm b / Blo ∧ safeNorm b / Blo ≤ 2) :
    slicedBlock K S D f s F θ q markWeight V.toFun Z ps cs bs k =
      inactiveWeight K S f * (CommonMellinTail.scalar (normalizedScale K S f s Z Klo Plo Clo Blo) : ℂ) *
      ∫ t : ℝ,
        ActualCommonMellinTail.profile F θ (QuotientGroup.mk f.rowUnit)
          (blockFrequency (frozenClass K S D f s) q.1.1 q.1.2 q.2.1 q.2.2)
          V (normalizedScale K S f s Z Klo Plo Clo Blo) t *
        (modeRow K S D f s θ q (normalizedScale K S f s Z Klo Plo Clo Blo) Klo t k *
          HeckeSkeleton.LowEnergy.IdealCanonicalColumns.hybridRow
            (cubicKernel K S D) (quadraticKernel K S D) ps cs bs
            (modeMark K S D f s θ q markWeight (normalizedScale K S f s Z Klo Plo Clo Blo) Plo t)
            (modeColumn K S D f s θ q (normalizedScale K S f s Z Klo Plo Clo Blo) Clo Blo t) k) := by
  let Y := normalizedScale K S f s Z Klo Plo Clo Blo
  let κ := blockFrequency (frozenClass K S D f s) q.1.1 q.1.2 q.2.1 q.2.2
  let rho := ActualCommonMellinTail.profile F θ (QuotientGroup.mk f.rowUnit) κ V Y
  have hY : 0 < Y := normalizedScale_pos K S f s hZ hK hP hC hB
  have hphase : Continuous (CommonMellinTail.phase Y) :=
    ((continuous_vertical Y).neg.const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hY.ne'))).div_const _
  have hrho : Continuous rho :=
    (ActualCommonMellinTail.continuous_amplitude hF θ (QuotientGroup.mk f.rowUnit) κ V Y).mul hphase
  obtain ⟨C, hC0, hbound⟩ := ActualCommonMellinTail.profile_uniform_weighted_L1_of_finite hF θ 0
  have hint : Integrable (fun t => ‖rho t‖) := by
    simpa only [pow_zero, one_mul] using (hbound V (QuotientGroup.mk f.rowUnit) κ Y hY).1
  have heq := FiniteHybridIntegral.separated_kernel_sum_eq_hybrid_integral
    (cubicKernel K S D) (quadraticKernel K S D) ps cs bs
    (fun P => markWeight P * ordinaryMark K S D f s θ q P) (ordinaryColumn K S D f s θ q)
    rho (CommonMellinTail.rowFactor Y (safeNorm k / Klo))
    (fun t P => CommonMellinTail.rowFactor Y (safeNorm P / Plo) t)
    (fun t c b => CommonMellinTail.columnFactor Y (safeNorm c / Clo) (safeNorm b / Blo) t)
    (fun P c b => mellinReflectionKernel K S F θ (QuotientGroup.mk f.rowUnit) κ V.toFun 0
      (CommonMellin.argument (baseScale K S f s Z)
        (safeNorm k) (safeNorm P) (safeNorm c) (safeNorm b)))
    (CommonMellinTail.scalar Y : ℂ) k hrho hint
    (continuous_rowFactor Y _ (div_pos (safeNorm_pos K k) hK))
    (fun P => continuous_rowFactor Y _ (div_pos (safeNorm_pos K P) hP))
    (fun c b => continuous_columnFactor Y _ _ (div_pos (safeNorm_pos K c) hC)
      (div_pos (safeNorm_pos K b) hB))
    16 (fun _ => 16) (fun _ _ => 4)
    (CommonMellinTail.norm_rowFactor_le hk0 hk1)
    (fun P hPm => CommonMellinTail.norm_rowFactor_le (hp P hPm).1 (hp P hPm).2)
    (fun c hcm b hbm => CommonMellinTail.norm_columnFactor_le
      (hc c hcm).1 (hc c hcm).2 (hb b hbm).1 (hb b hbm).2)
    (by
      intro P hPm c hcm b hbm
      rw [argument_normalized K S f s Z Klo Plo Clo Blo k P c b hK hP hC hB]
      have hsep := kernel_separation_at_zero K S θ hKernel
        (QuotientGroup.mk f.rowUnit) κ V hY
        (div_pos (safeNorm_pos K k) hK) (div_pos (safeNorm_pos K P) hP)
        (div_pos (safeNorm_pos K c) hC) (div_pos (safeNorm_pos K b) hB)
      convert hsep using 1
      congr 1
      congr 1
      funext t
      ring)
  unfold slicedBlock
  rw [heq]
  repeat rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  delta modeMark modeColumn
  dsimp only [rho, κ, Y, modeRow]
  ring


variable {f s}

theorem general_block_energy [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ : HeckeCharacter K) (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
        (q : FourClasses (SixthLocalClasses K S)) (V : SmoothAnnularTest)
        (Z Klo Plo Clo Blo Kup Pup Cup Bup : ℝ),
      0 < Z → 0 < Klo → 0 < Plo → 0 < Clo → 0 < Blo →
      1 ≤ Kup → 1 ≤ Pup → 1 ≤ Cup → 1 ≤ Bup →
      ∀ rows ps cs bs : Finset (Ideal (𝓞 K)),
      (∀ k ∈ rows, IsExterior K S k ∧ Squarefree k ∧ (k.absNorm : ℝ) ≤ Kup) →
      (∀ P ∈ ps, IsExterior K S P ∧ Squarefree P ∧ (P.absNorm : ℝ) ≤ Pup) →
      (∀ c ∈ cs, IsExterior K S c ∧ Squarefree c ∧ (c.absNorm : ℝ) ≤ Cup) →
      (∀ b ∈ bs, IsExterior K S b ∧ (b.absNorm : ℝ) ≤ Bup) →
      (∀ k ∈ rows, 1 ≤ safeNorm k / Klo ∧ safeNorm k / Klo ≤ 2) →
      (∀ P ∈ ps, 1 ≤ safeNorm P / Plo ∧ safeNorm P / Plo ≤ 2) →
      (∀ c ∈ cs, 1 ≤ safeNorm c / Clo ∧ safeNorm c / Clo ≤ 2) →
      (∀ b ∈ bs, 1 ≤ safeNorm b / Blo ∧ safeNorm b / Blo ≤ 2) →
      ∀ (markWeight : Ideal (𝓞 K) → ℂ) (A : ℝ), 0 < A →
      (∀ P ∈ ps, ‖markWeight P‖ ≤ A) →
      (∑ k ∈ rows, ‖slicedBlock K S D f s F θ q markWeight V.toFun Z ps cs bs k‖ ^ 2) ≤
        C * A ^ 2 * testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
        ‖inactiveWeight K S f‖ ^ 2 *
        CommonMellinTail.scalar (normalizedScale K S f s Z Klo Plo Clo Blo) ^ 2 *
        (stateMajorant K S s ^ 2 / (Clo * Blo ^ 2)) *
        (Kup * Cup * Bup * Pup) ^ eps * (Kup + Cup * Bup) * Bup *
        (Cup + Pup + (Cup * Pup) ^ (2 / 3 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := GeneralSeparatedEnergy.general_separated_energy K S D F hF θ hθ hD
    hquadratic hcubic eps heps
  refine ⟨C, hC, ?_⟩
  intro f s q V Z Klo Plo Clo Blo Kup Pup Cup Bup hZ hK hP hC hB
    hKu hPu hCu hBu rows ps cs bs hrows hps hcs hbs hd hp hc hbsRatio markWeight A hA hw
  let Y := normalizedScale K S f s Z Klo Plo Clo Blo
  have hY : 0 < Y := normalizedScale_pos K S f s hZ hK hP hC hB
  have he := hb false f s q V Y Klo Plo Clo Blo Kup Pup Cup Bup hY hK hP hC hB
    hKu hPu hCu hBu rows ps cs bs hrows hps hcs hbs hd hp hc hbsRatio markWeight A hA hw
  have hrow (k : Ideal (𝓞 K)) (hk : k ∈ rows) :
      slicedBlock K S D f s F θ q markWeight V.toFun Z ps cs bs k =
      GeneralSeparatedEnergy.separatedRow K S D false f s F θ q markWeight V
        Y Klo Plo Clo Blo ps cs bs k := by
    exact slicedBlock_eq_integral K S D f s F hF θ hKernel q markWeight V
      Z Klo Plo Clo Blo hZ hK hP hC hB ps cs bs k
      (hd k hk).1 (hd k hk).2 hp hc hbsRatio
  calc
    _ = ∑ k ∈ rows, ‖GeneralSeparatedEnergy.separatedRow K S D false f s F θ q markWeight V
          Y Klo Plo Clo Blo ps cs bs k‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hrow k hk]
    _ ≤ _ := he


#print axioms kernel_separation_at_zero
#print axioms source_reflectedTerm
#print axioms slicedBlock_eq_integral
#print axioms general_block_energy

end HeckeSkeleton.LowEnergy.GeneralReflectedBlock
