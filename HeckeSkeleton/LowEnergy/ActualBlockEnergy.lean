import HeckeSkeleton.LowEnergy.GeneralSeparatedEnergy

/-!
# Actual finite reflected block energy from the two permitted sieves

This is the mark-dependent-scale specialization of
`GeneralSeparatedEnergy.general_separated_energy`.  The same theorem also
proves the arbitrary fixed completed scale.  The constant is selected before the frozen datum, frozen state, class slice,
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
  obtain ⟨C, hC, hb⟩ := GeneralSeparatedEnergy.general_separated_energy K S D F hF θ hθ hD
    hquadratic hcubic eps heps
  refine ⟨C, hC, ?_⟩
  intro f s q V Z Klo Plo Clo Blo Kup Pup Cup Bup hZ hK hP hC hB
    hKu hPu hCu hBu rows ps cs bs hrows hps hcs hbs hd hp hc hbsRatio markWeight A hA hw
  let Y := normalizedScale K S f s Z Klo Plo Clo Blo
  have hY : 0 < Y := normalizedScale_pos K S f s hZ hK hP hC hB
  have he := hb true f s q V Y Klo Plo Clo Blo Kup Pup Cup Bup hY hK hP hC hB
    hKu hPu hCu hBu rows ps cs bs hrows hps hcs hbs hd hp hc hbsRatio markWeight A hA hw
  have hrow (k : Ideal (𝓞 K)) (hk : k ∈ rows) :
      slicedPhysicalBlock K S D f s F θ q markWeight V.toFun Z ps cs bs k =
      GeneralSeparatedEnergy.separatedRow K S D true f s F θ q markWeight V
        Y Klo Plo Clo Blo ps cs bs k := by
    exact slicedPhysicalBlock_eq_integral K S D f s F hF θ hKernel q markWeight V
      Z Klo Plo Clo Blo hZ hK hP hC hB ps cs bs k
      (hd k hk).1 (hd k hk).2 hp hc hbsRatio
  calc
    _ = ∑ k ∈ rows, ‖GeneralSeparatedEnergy.separatedRow K S D true f s F θ q markWeight V
          Y Klo Plo Clo Blo ps cs bs k‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hrow k hk]
    _ ≤ _ := he


#print axioms modeColumn_norm_le_dyad
#print axioms actual_block_energy

end HeckeSkeleton.LowEnergy.ActualBlockEnergy
