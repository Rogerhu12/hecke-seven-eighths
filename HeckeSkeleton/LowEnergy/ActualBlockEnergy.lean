import HeckeSkeleton.LowEnergy.ActualSeparatedBlock
import HeckeSkeleton.LowEnergy.ActualRawHybrid
import HeckeSkeleton.LowEnergy.MellinHybrid

/-!
# Actual finite reflected block energy from the two permitted sieves

The constant is selected before the frozen datum, frozen state, class slice,
annular test, physical scale, four dyads and finite ideal supports.  The
inverse squarefree/full-cube column mass is kept explicitly, including the
zero frozen-majorant case.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.ActualBlockEnergy

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckePort.CenteredMomentGenerator
open HeckeSkeleton.LowEnergy.ActualSymbols HeckeSkeleton.LowEnergy.ActualSieveDictionary
open HeckeSkeleton.LowEnergy.ActualRawHybrid HeckeSkeleton.LowEnergy.ActualReflectionReindex
open HeckeSkeleton.LowEnergy.ActualSeparatedBlock HeckeSkeleton.LowEnergy.ClassSlices
open HeckeSkeleton.LowEnergy.ActualClassSlices
open scoped Classical BigOperators NumberField

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

theorem modeColumn_norm_le_dyad (θ : HeckeCharacter K)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
    (q : FourClasses (SixthLocalClasses K S)) (Y Clo Blo t : ℝ)
    (hC : 0 < Clo) (hB : 0 < Blo) (c b : Ideal (𝓞 K))
    (hc : IsExterior K S c) (hb : IsExterior K S b)
    (hc0 : 1 ≤ safeNorm c / Clo) (hc1 : safeNorm c / Clo ≤ 2)
    (hb0 : 1 ≤ safeNorm b / Blo) (hb1 : safeNorm b / Blo ≤ 2) :
    ‖modeColumn K S D f s θ q Y Clo Blo t c b‖ ≤
      4 * stateMajorant K S s / (Real.sqrt Clo * Blo) := by
  have hcnorm : safeNorm c = (c.absNorm : ℝ) :=
    safeNorm_exterior K S (toExterior K S c hc)
  have hbnorm : safeNorm b = (b.absNorm : ℝ) :=
    safeNorm_exterior K S (toExterior K S b hb)
  have hclower : Clo ≤ (c.absNorm : ℝ) := by
    simpa only [one_mul, hcnorm] using (le_div_iff₀ hC).mp hc0
  have hblower : Blo ≤ (b.absNorm : ℝ) := by
    simpa only [one_mul, hbnorm] using (le_div_iff₀ hB).mp hb0
  have hden : Real.sqrt Clo * Blo ≤ Real.sqrt (c.absNorm : ℝ) * (b.absNorm : ℝ) :=
    mul_le_mul (Real.sqrt_le_sqrt hclower) hblower hB.le (Real.sqrt_nonneg _)
  exact (modeColumn_norm_le K S D f s θ hθ q Y Clo Blo t c b hc hb hc0 hc1 hb0 hb1).trans
    (div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (stateMajorant_nonneg K S s))
      (mul_pos (Real.sqrt_pos.mpr hC) hB) hden)

theorem actual_block_energy [Finite (SixthLocalClasses K S)]
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
      (∑ k ∈ rows, ‖slicedPhysicalBlock K S D f s F θ q markWeight V.toFun Z ps cs bs k‖ ^ 2) ≤
        C * A ^ 2 * testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
        ‖inactiveWeight K S f‖ ^ 2 *
        CommonMellinTail.scalar (normalizedScale K S f s Z Klo Plo Clo Blo) ^ 2 *
        (stateMajorant K S s ^ 2 / (Clo * Blo ^ 2)) *
        (Kup * Cup * Bup * Pup) ^ eps * (Kup + Cup * Bup) * Bup *
        (Cup + Pup + (Cup * Pup) ^ (2 / 3 : ℝ)) := by
  have hextdvd : ∀ I J : Ideal (𝓞 K), IsExterior K S I → J ∣ I → IsExterior K S J := by
    intro I J hI hJI
    exact ⟨ne_zero_of_dvd_ne_zero hI.1 hJI, fun p hp => hI.2 p (dvd_trans hp hJI)⟩
  obtain ⟨Ce, hCe, he⟩ := MellinHybrid.integrated_hybrid_energy
    (IsExterior K S) (fun I hI => hI.1)
    (fun I J hI hJ => (isExterior_mul_iff K S).mpr ⟨hI, hJ⟩) hextdvd
    (cubicKernel K S D) (quadraticKernel K S D) (actual_cubic_axioms K S D hD)
    (fun k c m h t hk hc ht => original_quadratic_square_mask K S D hD k c m h t hk hc ht)
    (ordinaryQuadratic_of_exterior K S D hD hquadratic)
    (ordinaryCubic_of_exterior K S D hcubic) eps heps
  obtain ⟨Cm, hCm, hm⟩ := ActualCommonMellinTail.profile_uniform_weighted_L1_of_finite hF θ 0
  refine ⟨65536 * Ce * (Cm + 1) ^ 2, by positivity, ?_⟩
  intro f s q V Z Klo Plo Clo Blo Kup Pup Cup Bup hZ hK hP hC hB
    hKu hPu hCu hBu rows ps cs bs hrows hps hcs hbs hd hp hc hb markWeight A hA hw
  by_cases hzero : stateMajorant K S s = 0
  · have hz : ∀ c b, ordinaryColumn K S D f s θ q c b = 0 := by
      intro c b
      by_cases hec : IsExterior K S c
      · by_cases heb : IsExterior K S b
        · apply norm_eq_zero.mp
          have h := ordinaryColumn_norm_le K S D f s θ hθ q c b hec heb
          rw [hzero, zero_div] at h
          exact le_antisymm h (norm_nonneg _)
        · simp [ordinaryColumn, heb]
      · simp [ordinaryColumn, hec]
    simp [slicedPhysicalBlock, hz, hzero]
  have hCf : 0 < stateMajorant K S s :=
    lt_of_le_of_ne (stateMajorant_nonneg K S s) (Ne.symm hzero)
  let Y := normalizedScale K S f s Z Klo Plo Clo Blo
  let κ := blockFrequency (frozenClass K S D f s) q.1.1 q.1.2 q.2.1 q.2.2
  let rho := ActualCommonMellinTail.profile F θ (QuotientGroup.mk f.rowUnit) κ V Y
  let Bamp := 4 * stateMajorant K S s / (Real.sqrt Clo * Blo)
  have hBamp : 0 < Bamp := by dsimp [Bamp]; positivity
  have hY : 0 < Y := normalizedScale_pos K S f s hZ hK hP hC hB
  have hphase : Continuous (CommonMellinTail.phase Y) :=
    ((continuous_vertical Y).neg.const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hY.ne'))).div_const _
  have hrho : Continuous rho :=
    (ActualCommonMellinTail.continuous_amplitude hF θ (QuotientGroup.mk f.rowUnit) κ V Y).mul hphase
  have hprof := hm V (QuotientGroup.mk f.rowUnit) κ Y hY
  have hint : Integrable (fun t => ‖rho t‖) := by
    simpa only [pow_zero, one_mul] using hprof.1
  have hL1 : (∫ t : ℝ, ‖rho t‖) ≤
      Cm * testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 := by
    simpa only [pow_zero, one_mul] using hprof.2
  have hsemi : 0 ≤ testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 :=
    (HeckeSkeleton.ThetaKernel.Iint_nonneg V 0 2).trans
      (HeckeSkeleton.ThetaKernel.Iint_right_le V 0 (ActualCommonMellinTail.order K 0) (by omega) 2)
  have hL1' : (∫ t : ℝ, ‖rho t‖) ≤
      (Cm + 1) * testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 :=
    hL1.trans (mul_le_mul_of_nonneg_right (by linarith) hsemi)
  have hL10 : 0 ≤ ∫ t : ℝ, ‖rho t‖ := integral_nonneg (fun t => norm_nonneg _)
  have hL12 : (∫ t : ℝ, ‖rho t‖) ^ 2 ≤
      ((Cm + 1) * testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hL1' hL1' hL10 (hL10.trans hL1')
  have hi := he Kup Cup Bup Pup hKu hCu hBu hPu rows cs bs ps hrows hcs hbs hps
    rho (modeMark K S D f s θ q markWeight Y Plo) (modeRow K S D f s θ q Y Klo)
    (modeColumn K S D f s θ q Y Clo Blo) hrho hint
    (continuous_modeMark K S D f s θ q markWeight Y Plo hP)
    (continuous_modeRow K S D f s θ q Y Klo hK)
    (continuous_modeColumn K S D f s θ q Y Clo Blo hC hB)
    (4 * A) Bamp 16 (CommonMellinTail.scalar Y) (by positivity) hBamp (by norm_num)
    (fun t P hPm => modeMark_norm_le K S D f s θ hθ q markWeight A Y Plo t P hA.le (hw P hPm)
      (hp P hPm).1 (hp P hPm).2)
    (fun t c hcm b hbm => modeColumn_norm_le_dyad K S D θ hθ f s q Y Clo Blo t hC hB c b
      (hcs c hcm).1 (hbs b hbm).1 (hc c hcm).1 (hc c hcm).2 (hb b hbm).1 (hb b hbm).2)
    (fun t k hkm => modeRow_norm_le K S D f s θ hθ q Y Klo t k
      (hd k hkm).1 (hd k hkm).2)
  have hscale : (16 * (4 * A) * Bamp) ^ 2 =
      65536 * A ^ 2 * (stateMajorant K S s ^ 2 / (Clo * Blo ^ 2)) := by
    dsimp [Bamp]
    calc
      _ = (256 * A * stateMajorant K S s / (Real.sqrt Clo * Blo)) ^ 2 := by
        congr 1
        ring
      _ = _ := by
        simp only [div_pow, mul_pow, Real.sq_sqrt hC.le]
        norm_num <;> ring
  have hW : 0 ≤ (Kup * Cup * Bup * Pup) ^ eps * (Kup + Cup * Bup) * Bup *
      (Cup + Pup + (Cup * Pup) ^ (2 / 3 : ℝ)) := by
    have hKu0 := zero_le_one.trans hKu
    have hPu0 := zero_le_one.trans hPu
    have hCu0 := zero_le_one.trans hCu
    have hBu0 := zero_le_one.trans hBu
    positivity
  have hcharged := mul_le_mul_of_nonneg_left hi (sq_nonneg ‖inactiveWeight K S f‖)
  have hleft :
      (∑ k ∈ rows, ‖slicedPhysicalBlock K S D f s F θ q markWeight V.toFun Z ps cs bs k‖ ^ 2) =
      ‖inactiveWeight K S f‖ ^ 2 *
        ∑ k ∈ rows, ‖(CommonMellinTail.scalar Y : ℂ) * ∫ t : ℝ,
          rho t * (modeRow K S D f s θ q Y Klo t k *
            IdealCanonicalColumns.hybridRow (cubicKernel K S D) (quadraticKernel K S D)
              ps cs bs (modeMark K S D f s θ q markWeight Y Plo t)
              (modeColumn K S D f s θ q Y Clo Blo t) k)‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hkm
    rw [slicedPhysicalBlock_eq_integral K S D f s F hF θ hKernel q markWeight V
      Z Klo Plo Clo Blo hZ hK hP hC hB ps cs bs k
      (hd k hkm).1 (hd k hkm).2 hp hc hb]
    rw [mul_assoc, norm_mul, mul_pow]
  rw [hleft]
  apply hcharged.trans
  rw [hscale]
  have hright := mul_le_mul_of_nonneg_right hL12
    (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg ‖inactiveWeight K S f‖)
      (sq_nonneg (CommonMellinTail.scalar Y)))
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 65536) (sq_nonneg A))
        (div_nonneg (sq_nonneg (stateMajorant K S s))
          (by positivity : (0 : ℝ) ≤ Clo * Blo ^ 2))))
      (mul_nonneg hCe.le hW))
  convert hright using 1 <;> (try dsimp [Y]) <;> ring

#print axioms modeColumn_norm_le_dyad
#print axioms actual_block_energy

end HeckeSkeleton.LowEnergy.ActualBlockEnergy
