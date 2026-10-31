import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondSourceNormalization
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondCoefficientBinding

/-!
# Extra Gauss normalization of the whole second source

The raw child coefficient already contains its plain and prime central
normalizations. The additional Gauss-column normalization is an exact
single-column identity, fixed before the Fourier parameter. It is moved
outside the entire energy, preserving its centered difference, all
columns, and the original row weight. It is not inferred from an
arbitrary coefficient and does not reuse the frozen allocation scalar.

The final comparison has density one. The only pool average remains in
FiniteBranchMass, while the main pool allowance and the 1/6/7 moving
norms remain explicit in the scalar bound.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open CommonSupportMass

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The hypothesis is the original coefficient identity on its literal
finite support. No whole-polynomial or energy estimate is assumed. -/
theorem joint_energy_extra_normalization {H ι : Type*}
    (rows : Finset H) (columns : Finset ι) (q : H → ℂ)
    (source raw : H → ι → ℂ) (x : H → ι → V)
    (N : ℝ) (hN : 0 < N)
    (hsource : ∀ h ∈ rows, ∀ i ∈ columns,
      source h i = raw h i / (Real.sqrt N : ℂ)) (ξ : V) :
    jointColumnEnergy rows columns q source x ξ =
      jointColumnEnergy rows columns q raw x ξ / N := by
  calc
    _ = jointColumnEnergy rows columns q
        (fun h i => (Real.sqrt N : ℂ)⁻¹ * raw h i) x ξ := by
      unfold jointColumnEnergy
      apply Finset.sum_congr rfl
      intro h hh
      have hc : jointFourierColumn columns (source h) (x h) ξ =
          jointFourierColumn columns (fun i => (Real.sqrt N : ℂ)⁻¹ * raw h i) (x h) ξ := by
        unfold jointFourierColumn
        apply Finset.sum_congr rfl
        intro i hi
        rw [hsource h hh i hi]
        ring
      rw [hc]
    _ = ‖(Real.sqrt N : ℂ)⁻¹‖ ^ 2 * jointColumnEnergy rows columns q raw x ξ :=
      joint_energy_constant_coefficient rows columns q raw x _ ξ
    _ = _ := by
      simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hN.le]
      ring

private theorem sqrt_pair_normalization (EL ER NL NR T : ℝ)
    (hEL : 0 ≤ EL) (hER : 0 ≤ ER) (hT : 0 < T) :
    Real.sqrt (EL / NL) * Real.sqrt (ER / NR) =
      (T / (Real.sqrt NL * Real.sqrt NR)) *
        (Real.sqrt (EL / T) * Real.sqrt (ER / T)) := by
  have hl : Real.sqrt EL = Real.sqrt T * Real.sqrt (EL / T) := by
    rw [← Real.sqrt_mul hT.le]
    congr 1
    field_simp [ne_of_gt hT]
  have hr : Real.sqrt ER = Real.sqrt T * Real.sqrt (ER / T) := by
    rw [← Real.sqrt_mul hT.le]
    congr 1
    field_simp [ne_of_gt hT]
  have ht : Real.sqrt T * Real.sqrt T = T := by
    nlinarith [Real.sq_sqrt hT.le]
  calc
    _ = (Real.sqrt EL / Real.sqrt NL) * (Real.sqrt ER / Real.sqrt NR) := by
      rw [Real.sqrt_div hEL, Real.sqrt_div hER]
    _ = ((Real.sqrt T * Real.sqrt T) / (Real.sqrt NL * Real.sqrt NR)) *
        (Real.sqrt (EL / T) * Real.sqrt (ER / T)) := by rw [hl, hr]; ring
    _ = _ := by rw [ht]

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]
variable {α β : Type*} {fullI : α → A.Exterior} {fullJ : β → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}

def FirstCommonCharacterBlock.secondSourceBudget
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS)
    (Z a₀ q wo w B krow g ell : ℝ) (h : A.R) : ℝ :=
  Z ^ (secondCommonChildWidth Z a₀ q wo krow g DE.1 DE.2
      (b.secondUnitRadical C h).val (b.secondNonunitRadical C h).val +
    secondCommonChildAllowance Z w B ell DE.1 DE.2)

/-- The extra normalization is charged once outside the whole source;
the right side retains the two complete raw child energies. -/
theorem FirstCommonCharacterBlock.second_whole_normalized_kernel_bound
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS)
    (Z : ℝ) (hZ : 1 < Z) (a₀ q₀ wo w B krow g ell NL NR : ℝ)
    (hNL : 0 < NL) (hNR : 0 < NR)
    (r : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
    (hrow : Z ^ (-krow - g) ≤
      r.val * (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D)).val)
    (hcentral : Z ^ a₀ ≤ Real.sqrt NL * Real.sqrt NR)
    (a d : A.R)
    (ha : A.Generates (primePowerProduct b.primes b.leftMultiplicity) a)
    (hd : A.Generates (primePowerProduct b.primes b.rightMultiplicity) d)
    (h : A.R) {H : Type*} (rows : Finset H) (left : Finset α) (right : Finset β)
    (rowWeight : H → ℂ) (sourceLeft rawLeft : H → α → ℂ)
    (sourceRight rawRight : H → β → ℂ) (x : H → α → V) (y : H → β → V)
    (hleft : ∀ j ∈ rows, ∀ i ∈ left,
      sourceLeft j i = rawLeft j i / (Real.sqrt NL : ℂ))
    (hright : ∀ j ∈ rows, ∀ i ∈ right,
      sourceRight j i = rawRight j i / (Real.sqrt NR : ℂ)) (ξ : V) :
    (‖secondOrbitalScalar (K := K) (S := A.Sf) r D‖ *
        ‖b.secondCorrelation (σ := σ) a d ha hd h‖ /
        (Real.sqrt (Ideal.absNorm DE.1 : ℝ) * Real.sqrt (Ideal.absNorm DE.2 : ℝ))) *
      (Real.sqrt (jointColumnEnergy rows left rowWeight sourceLeft x ξ) *
        Real.sqrt (jointColumnEnergy rows right rowWeight sourceRight y ξ)) ≤
      (orbitalFieldFactor K * Z ^ (a₀ + q₀ + w + B) * Z ^ wo * Z ^ ell /
        (Ideal.absNorm (commonRadical DE.1 DE.2) : ℝ)) *
      (Real.sqrt (jointColumnEnergy rows left rowWeight rawLeft x ξ /
          b.secondSourceBudget C Z a₀ q₀ wo w B krow g ell h) *
        Real.sqrt (jointColumnEnergy rows right rowWeight rawRight y ξ /
          b.secondSourceBudget C Z a₀ q₀ wo w B krow g ell h)) := by
  have hbudget : 0 < b.secondSourceBudget C Z a₀ q₀ wo w B krow g ell h :=
    Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  rw [joint_energy_extra_normalization rows left rowWeight sourceLeft rawLeft x NL hNL hleft ξ,
    joint_energy_extra_normalization rows right rowWeight sourceRight rawRight y NR hNR hright ξ]
  rw [sqrt_pair_normalization _ _ NL NR
    (b.secondSourceBudget C Z a₀ q₀ wo w B krow g ell h)
    (jointColumnEnergy_nonneg rows left rowWeight rawLeft x ξ)
    (jointColumnEnergy_nonneg rows right rowWeight rawRight y ξ) hbudget]
  calc
    _ = b.secondSourceWeight C Z a₀ q₀ wo w B krow g ell 1 NL NR r D a d ha hd h *
        (Real.sqrt (jointColumnEnergy rows left rowWeight rawLeft x ξ /
            b.secondSourceBudget C Z a₀ q₀ wo w B krow g ell h) *
          Real.sqrt (jointColumnEnergy rows right rowWeight rawRight y ξ /
            b.secondSourceBudget C Z a₀ q₀ wo w B krow g ell h)) := by
      unfold FirstCommonCharacterBlock.secondSourceWeight
      dsimp only [FirstCommonCharacterBlock.secondSourceBudget]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (b.secondSourceWeight_without_density_le C Z hZ a₀ q₀ wo w B krow g ell NL NR
        r D hrow hcentral a d ha hd h)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.joint_energy_extra_normalization
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.second_whole_normalized_kernel_bound
