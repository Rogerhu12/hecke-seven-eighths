import HeckeSkeleton.LowEnergy.ActualBlockEnergy

/-!
# Fixed-scale canonical Mellin separation

The physical marked theorem has one active-mark norm in its kernel
argument. Here the completed scale is fixed before the active ideal,
so the exact argument has its square. The same proved common profile
is used, with a mark-only factor of exponent `2w`. No new analytic
hypothesis is introduced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalMellin

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckePort.CenteredMomentGenerator
open HeckeSkeleton.LowEnergy.ActualReflection
  HeckeSkeleton.LowEnergy.ActualReflectionReindex
  HeckeSkeleton.LowEnergy.ActualFrozenCharges
  HeckeSkeleton.LowEnergy.ActualFrozenIndependence
  HeckeSkeleton.LowEnergy.ActualHybridEntry
  HeckeSkeleton.LowEnergy.ActualSeparatedBlock
  HeckeSkeleton.LowEnergy.ActualSymbols
  HeckeSkeleton.LowEnergy.ClassSlices
  HeckeSkeleton.LowEnergy.ActualClassSlices
open HeckeSkeleton.LowEnergy
open scoped Classical BigOperators nonZeroDivisors NumberField

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

/-- The common positive line remains independent of every moving ideal.
Squaring the positive mark coordinate converts the existing physical
kernel identity into the exact fixed-scale canonical one. -/
theorem kernel_canonical_separation_at_zero
    {F : FiniteMellinData K S}
    (θ : HeckeCharacter K) (hK : MellinKernelInput K S F θ)
    (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S)
    (V : SmoothAnnularTest) {Y d P n b : ℝ}
    (hY : 0 < Y) (hd : 0 < d) (hP : 0 < P) (hn : 0 < n) (hb : 0 < b) :
    mellinReflectionKernel K S F θ u κ V.toFun 0 (CommonMellin.argument Y d P n b) =
      (CommonMellinTail.scalar Y : ℂ) * ∫ t : ℝ,
        ActualCommonMellinTail.profile F θ u κ V Y t *
          CommonMellinTail.rowFactor Y d t * CommonMellinTail.rowFactor Y P t *
            CommonMellinTail.columnFactor Y n b t := by
  have he := ActualCommonMellinTail.kernel_physical_separation_at_zero θ hK
    u κ V hY hd (sq_pos_of_pos hP) hn hb
  have hmark (t : ℝ) : CommonMellinTail.markFactor Y (P ^ 2) t =
      CommonMellinTail.rowFactor Y P t := by
    unfold CommonMellinTail.markFactor CommonMellinTail.rowFactor
    simpa only [Nat.cast_ofNat] using
      CommonMellin.ofReal_pow_cpow P hP.le 2 (CommonMellinTail.vertical Y t)
  simpa only [CommonMellin.physicalArgument, CommonMellin.argument, hmark] using he

variable (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)

def canonicalBase (X : ℝ) : ℝ :=
  X * exteriorNorm K S s.minimum / exteriorNorm K S (primeSetIdeal K S s.active) ^ 2

def canonicalScale (X Klo Plo Clo Blo : ℝ) : ℝ :=
  canonicalBase K S f s X * Clo * Blo ^ 3 / (Klo ^ 2 * Plo ^ 2)

theorem canonicalScale_pos {X Klo Plo Clo Blo : ℝ}
    (hX : 0 < X) (hK : 0 < Klo) (hP : 0 < Plo) (hC : 0 < Clo) (hB : 0 < Blo) :
    0 < canonicalScale K S f s X Klo Plo Clo Blo := by
  have hA := exteriorNorm_pos K S s.minimum
  have hF := exteriorNorm_pos K S (primeSetIdeal K S s.active)
  unfold canonicalScale canonicalBase
  positivity

theorem canonical_argument_normalized (X Klo Plo Clo Blo : ℝ) (k P c b : Ideal (𝓞 K))
    (hK : 0 < Klo) (hP : 0 < Plo) (hC : 0 < Clo) (hB : 0 < Blo) :
    CommonMellin.argument (canonicalBase K S f s X)
      (safeNorm k) (safeNorm P) (safeNorm c) (safeNorm b) =
    CommonMellin.argument (canonicalScale K S f s X Klo Plo Clo Blo)
      (safeNorm k / Klo) (safeNorm P / Plo) (safeNorm c / Clo) (safeNorm b / Blo) := by
  unfold CommonMellin.argument canonicalScale
  field_simp [hK.ne', hP.ne', hC.ne', hB.ne',
    (safeNorm_pos K k).ne', (safeNorm_pos K P).ne']
  <;> ring

def canonicalModeMark (θ : HeckeCharacter K) (q : FourClasses (SixthLocalClasses K S))
    (markWeight : Ideal (𝓞 K) → ℂ) (Y Plo t : ℝ) (P : Ideal (𝓞 K)) : ℂ :=
  markWeight P * ordinaryMark K S D f s θ q P *
    CommonMellinTail.rowFactor Y (safeNorm P / Plo) t

theorem continuous_canonicalModeMark (θ : HeckeCharacter K)
    (q : FourClasses (SixthLocalClasses K S)) (markWeight : Ideal (𝓞 K) → ℂ)
    (Y Plo : ℝ) (hP : 0 < Plo) (P : Ideal (𝓞 K)) :
    Continuous (fun t => canonicalModeMark K S D f s θ q markWeight Y Plo t P) :=
  (continuous_rowFactor Y _ (div_pos (safeNorm_pos K P) hP)).const_mul _

theorem canonicalModeMark_norm_le (θ : HeckeCharacter K)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (q : FourClasses (SixthLocalClasses K S))
    (markWeight : Ideal (𝓞 K) → ℂ) (A Y Plo t : ℝ) (P : Ideal (𝓞 K))
    (hA : 0 ≤ A) (hw : ‖markWeight P‖ ≤ A)
    (hP0 : 1 ≤ safeNorm P / Plo) (hP1 : safeNorm P / Plo ≤ 2) :
    ‖canonicalModeMark K S D f s θ q markWeight Y Plo t P‖ ≤ 16 * A := by
  rw [canonicalModeMark, norm_mul, norm_mul]
  have hw' : ‖markWeight P‖ * ‖ordinaryMark K S D f s θ q P‖ ≤ A := by
    simpa only [mul_one] using mul_le_mul hw
      (ordinaryMark_norm_le_one K S D f s θ hθ q P) (norm_nonneg _) hA
  have h := mul_le_mul hw' (CommonMellinTail.norm_rowFactor_le (Y := Y) hP0 hP1 t)
    (norm_nonneg _) hA
  simpa only [mul_comm A] using h

def slicedCanonicalBlock (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (q : FourClasses (SixthLocalClasses K S)) (markWeight : Ideal (𝓞 K) → ℂ)
    (V : ℝ → ℂ) (Z : ℝ)
    (ps cs bs : Finset (Ideal (𝓞 K))) (k : Ideal (𝓞 K)) : ℂ :=
  inactiveWeight K S f * ordinaryRow K S D f s θ q k *
    ∑ P ∈ ps, ∑ c ∈ cs, ∑ b ∈ bs,
      (markWeight P * ordinaryMark K S D f s θ q P) * ordinaryColumn K S D f s θ q c b *
      FiniteHybridIntegral.hybridKernel (cubicKernel K S D) (quadraticKernel K S D) k P c b *
      mellinReflectionKernel K S F θ (QuotientGroup.mk f.rowUnit)
        (blockFrequency (frozenClass K S D f s) q.1.1 q.1.2 q.2.1 q.2.2) V 0
        (CommonMellin.argument (canonicalBase K S f s Z)
          (safeNorm k) (safeNorm P) (safeNorm c) (safeNorm b))

theorem slicedCanonicalBlock_zero_of_markWeight (F : FiniteMellinData K S)
    (θ : HeckeCharacter K) (q : FourClasses (SixthLocalClasses K S))
    (a : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (Z : ℝ)
    (ps cs bs : Finset (Ideal (𝓞 K))) (k : Ideal (𝓞 K))
    (ha : ∀ P ∈ ps, a P = 0) :
    slicedCanonicalBlock K S D f s F θ q a V Z ps cs bs k = 0 := by
  unfold slicedCanonicalBlock
  have hz : (∑ P ∈ ps, ∑ c ∈ cs, ∑ b ∈ bs,
      (a P * ordinaryMark K S D f s θ q P) * ordinaryColumn K S D f s θ q c b *
      FiniteHybridIntegral.hybridKernel (cubicKernel K S D) (quadraticKernel K S D) k P c b *
      mellinReflectionKernel K S F θ (QuotientGroup.mk f.rowUnit)
        (blockFrequency (frozenClass K S D f s) q.1.1 q.1.2 q.2.1 q.2.2) V 0
        (CommonMellin.argument (canonicalBase K S f s Z)
          (safeNorm k) (safeNorm P) (safeNorm c) (safeNorm b))) = 0 := by
    apply Finset.sum_eq_zero
    intro P hP
    simp [ha P hP]
  rw [hz, mul_zero]

theorem slicedCanonicalBlock_zero_of_ordinaryRow (F : FiniteMellinData K S)
    (θ : HeckeCharacter K) (q : FourClasses (SixthLocalClasses K S))
    (a : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (Z : ℝ)
    (ps cs bs : Finset (Ideal (𝓞 K))) (k : Ideal (𝓞 K))
    (hk : ordinaryRow K S D f s θ q k = 0) :
    slicedCanonicalBlock K S D f s F θ q a V Z ps cs bs k = 0 := by
  simp [slicedCanonicalBlock, hk]

/-- The finite block identity is before squaring and retains the common
profile, the inactive scalar, all active marks, both columns and both masks. -/
theorem slicedCanonicalBlock_eq_integral [Finite (SixthLocalClasses K S)]
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
    slicedCanonicalBlock K S D f s F θ q markWeight V.toFun Z ps cs bs k =
      inactiveWeight K S f * (CommonMellinTail.scalar (canonicalScale K S f s Z Klo Plo Clo Blo) : ℂ) *
      ∫ t : ℝ,
        ActualCommonMellinTail.profile F θ (QuotientGroup.mk f.rowUnit)
          (blockFrequency (frozenClass K S D f s) q.1.1 q.1.2 q.2.1 q.2.2)
          V (canonicalScale K S f s Z Klo Plo Clo Blo) t *
        (modeRow K S D f s θ q (canonicalScale K S f s Z Klo Plo Clo Blo) Klo t k *
          HeckeSkeleton.LowEnergy.IdealCanonicalColumns.hybridRow
            (cubicKernel K S D) (quadraticKernel K S D) ps cs bs
            (canonicalModeMark K S D f s θ q markWeight (canonicalScale K S f s Z Klo Plo Clo Blo) Plo t)
            (modeColumn K S D f s θ q (canonicalScale K S f s Z Klo Plo Clo Blo) Clo Blo t) k) := by
  let Y := canonicalScale K S f s Z Klo Plo Clo Blo
  let κ := blockFrequency (frozenClass K S D f s) q.1.1 q.1.2 q.2.1 q.2.2
  let rho := ActualCommonMellinTail.profile F θ (QuotientGroup.mk f.rowUnit) κ V Y
  have hY : 0 < Y := canonicalScale_pos K S f s hZ hK hP hC hB
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
      (CommonMellin.argument (canonicalBase K S f s Z)
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
      rw [canonical_argument_normalized K S f s Z Klo Plo Clo Blo k P c b hK hP hC hB]
      have hsep := kernel_canonical_separation_at_zero K S θ hKernel
        (QuotientGroup.mk f.rowUnit) κ V hY
        (div_pos (safeNorm_pos K k) hK) (div_pos (safeNorm_pos K P) hP)
        (div_pos (safeNorm_pos K c) hC) (div_pos (safeNorm_pos K b) hB)
      convert hsep using 1
      congr 1
      congr 1
      funext t
      ring)
  unfold slicedCanonicalBlock
  rw [heq]
  repeat rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  delta canonicalModeMark modeColumn
  dsimp only [rho, κ, Y, modeRow]
  ring

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalMellin

end
