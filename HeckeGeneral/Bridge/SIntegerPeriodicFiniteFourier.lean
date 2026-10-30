import HeckeGeneral.Bridge.SIntegerPeriodicFiniteTest
import HeckeGeneral.Bridge.SIntegerFourierFactorization
import HeckeGeneral.Characters.LocalResidueCosetNormalizedFourier
import HeckeGeneral.Characters.SIntegerModulusCosetPhase
import HeckeGeneral.Arithmetic.SIntegerModulusFourierMass
import HeckeGeneral.Arithmetic.SIntegerPeriodicFourier

/-!
# The actual finite Fourier coefficient at an S-integer modulus frequency

The normalized finite adelic Fourier integral at frequencies equal to `a/c`
outside the original S is computed by
actual coset integration. Local Haar masses cancel only after their positivity
is proved. The exterior prime-power mass is the actual reciprocal modulus
norm, and global character cancellation gives the positive S-local phase.
The original S-local Fourier factors and the literal nonunit coefficient
`f(d*r)` are retained. The frequency `a` may be zero or a nonunit.
-/

noncomputable section

namespace HeckeGeneral.Bridge

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  NumberField.StandardAddChar NumberField.AdelicFourier MeasureTheory
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)

local notation "OS" => Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K

variable (c : Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) (hc : c ≠ 0)


local notation "P" => sIntegerModulusPlaces K (S : Set (HeightOneSpectrum (𝓞 K))) c hc

theorem outsideModulusAnnihilator_div (a : OS) (w : FiniteAdeleRing (𝓞 K) K)
    (hw : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      w v = algebraMap K (v.adicCompletion K) ((a : K) / (c : K))) :
    outsideSStandardAnnihilator K (S ∪ P) w := by
  intro v hv z hz
  have hvS : v ∉ S := fun hs => hv (Finset.mem_union_left P hs)
  have hvP : v ∉ P := fun hp => hv (Finset.mem_union_right S hp)
  have hint := sInteger_div_modulus_integral_outside K
    (S : Set (HeightOneSpectrum (𝓞 K))) c hc a v hvS hvP
  rw [hw v hvS]
  exact LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers K v _
    ((v.adicCompletionIntegers K).mul_mem _ _ hz hint)

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

/-- Every exterior local coset integral uses its actual global lift as center. -/
theorem sIntegerPeriodicLocalFourier_modulusProduct
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (r : (OS ⧸ Ideal.span ({c} : Set OS))) (a : OS) (w : FiniteAdeleRing (𝓞 K) K)
    (hw : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      w v = algebraMap K (v.adicCompletion K) ((a : K) / (c : K))) :
    (∏ v : P,
      (((μv v.val).real (v.val.adicCompletionIntegers K : Set (v.val.adicCompletion K)) : ℂ))⁻¹ *
        fourierIntegral (psiLocal K v.val) (μv v.val)
          (sIntegerPeriodicLocalFactor K S c hc h r v.val)
          (w v.val)) =
      ((sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨c, hc⟩).val : ℂ)⁻¹ *
        sIntegerActualModulusAddCharacter K (S : Set (HeightOneSpectrum (𝓞 K))) hS c hc
          (Ideal.Quotient.mk _ a * r) := by
  calc
    _ = ∏ v : P,
        (((v.val.asIdeal.absNorm : ℝ) ^
          (-(sIntegerModulusPrimeExponents K (S : Set (HeightOneSpectrum (𝓞 K)))
            c hc v.val : ℤ))) : ℂ) *
          psiLocal K v.val
            (-(algebraMap K (v.val.adicCompletion K) ((Quotient.out r : OS) : K) *
              algebraMap K (v.val.adicCompletion K) ((a : K) / (c : K)))) := by
      apply Finset.prod_congr rfl
      intro v _
      have hvS := sIntegerModulusPlaces_not_mem K (S : Set (HeightOneSpectrum (𝓞 K))) c hc v
      have hbound : Valued.v (algebraMap K (v.val.adicCompletion K) ((a : K) / (c : K))) ≤
          WithZero.exp (localDifferentExponent K v.val +
            (sIntegerModulusPrimeExponents K (S : Set (HeightOneSpectrum (𝓞 K)))
              c hc v.val : ℤ)) := by
        rw [hS v.val hvS, zero_add]
        exact sInteger_div_modulus_completion_valuation_le K
          (S : Set (HeightOneSpectrum (𝓞 K))) c hc a v.val hvS
      rw [hw v.val hvS, sIntegerPeriodicLocalFactor_at_modulus,
        normalizedFourier_localIntegerResidueCosetIndicator, if_pos hbound, mul_one]
      simp only [Complex.ofReal_zpow]
      rfl
    _ = _ := by
      rw [Finset.prod_mul_distrib,
        sIntegerModulus_complexPrimeMass_eq_inv_productNorm,
        sIntegerModulusCosetPhase_out_eq K (S : Set (HeightOneSpectrum (𝓞 K))) hS c hc a r]

/-- One global coset contributes its actual primitive residue phase. -/
theorem sIntegerPeriodicCosetMask_fourier_div
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (r : (OS ⧸ Ideal.span ({c} : Set OS))) (a : OS)
    (w : FiniteAdeleRing (𝓞 K) K)
    (hw : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      w v = algebraMap K (v.adicCompletion K) ((a : K) / (c : K))) :
    ((ν.real (AdelicBox.integralFiniteAdeles (𝓞 K) K) : ℂ))⁻¹ *
        fourierIntegral (standardFiniteAddCharacter K) ν
          (sIntegerPeriodicCosetMask K S c hc h r) w =
      ((sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨c, hc⟩).val : ℂ)⁻¹ *
        sIntegerLocalFourierProduct K μv S h w *
        sIntegerActualModulusAddCharacter K (S : Set (HeightOneSpectrum (𝓞 K))) hS c hc
          (Ideal.Quotient.mk _ a * r) := by
  have hlocal := sIntegerPeriodicLocalFactor_locallyConstant_compactSupport K S c hc h hlc hcs r
  rw [sIntegerPeriodicCosetMask,
    sIntegerFiniteMask_fourier_factorization K ν μv (S ∪ P) _
      (fun v hv => (hlocal v hv).1) (fun v hv => (hlocal v hv).2),
    if_pos (outsideModulusAnnihilator_div K S c hc a w hw), mul_one]
  unfold sIntegerLocalFourierProduct
  rw [Finset.prod_union (sIntegerModulusPlaces_disjoint K S c hc)]
  have hleft : (∏ v ∈ S,
      (((μv v).real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℂ))⁻¹ *
        fourierIntegral (psiLocal K v) (μv v) (sIntegerPeriodicLocalFactor K S c hc h r v)
          (w v)) =
      ∏ v ∈ S,
      (((μv v).real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℂ))⁻¹ *
        fourierIntegral (psiLocal K v) (μv v) (h v)
          (w v) := by
    apply Finset.prod_congr rfl
    intro v hv
    rw [sIntegerPeriodicLocalFactor_of_mem K S c hc h r v hv]
  rw [hleft, ← Finset.prod_coe_sort P]
  rw [sIntegerPeriodicLocalFourier_modulusProduct K S hS c hc μv h r a w hw]
  ring

/-- The finite coset sum commutes with the actual integral after integrability. -/
theorem fourierIntegral_sIntegerPeriodicFiniteTest
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (f : (OS ⧸ Ideal.span ({c} : Set OS)) → ℂ) (d : OS)
    (w : FiniteAdeleRing (𝓞 K) K) :
    fourierIntegral (standardFiniteAddCharacter K) ν
        (sIntegerPeriodicFiniteTest K S c hc h f d) w =
      letI := finite_sIntegerPrincipalResidue K (S : Set (HeightOneSpectrum (𝓞 K))) c hc
      letI := Fintype.ofFinite (OS ⧸ Ideal.span ({c} : Set OS))
      ∑ r : (OS ⧸ Ideal.span ({c} : Set OS)), f (Ideal.Quotient.mk _ d * r) *
        fourierIntegral (standardFiniteAddCharacter K) ν
          (sIntegerPeriodicCosetMask K S c hc h r) w := by
  letI := finite_sIntegerPrincipalResidue K (S : Set (HeightOneSpectrum (𝓞 K))) c hc
  letI := Fintype.ofFinite (OS ⧸ Ideal.span ({c} : Set OS))
  have hchar : Continuous (standardFiniteAddCharacter K) :=
    (isGlobalAddChar_stdAddChar K).continuous.comp (continuous_const.prodMk continuous_id)
  have hint (r : (OS ⧸ Ideal.span ({c} : Set OS))) : Integrable (fun z : FiniteAdeleRing (𝓞 K) K =>
      standardFiniteAddCharacter K (-(z * w)) *
        (f (Ideal.Quotient.mk _ d * r) * sIntegerPeriodicCosetMask K S c hc h r z)) ν := by
    have hm := sIntegerPeriodicCosetMask_locallyConstant_compactSupport K S c hc h hlc hcs r
    exact ((hchar.comp ((continuous_id.mul continuous_const).neg)).mul
      (continuous_const.mul hm.1.continuous)).integrable_of_hasCompactSupport
        hm.2.mul_left.mul_left
  unfold fourierIntegral sIntegerPeriodicFiniteTest
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun r _ => hint r)]
  apply Finset.sum_congr rfl
  intro r _
  rw [← integral_const_mul]
  congr 1
  funext z
  ring

/-- The normalized transform is the actual divisor Fourier coefficient.
Both `a = 0` and noninvertible `d` are included. -/
theorem sIntegerPeriodicFiniteTest_fourier_div
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (f : (OS ⧸ Ideal.span ({c} : Set OS)) → ℂ) (d a : OS)
    (w : FiniteAdeleRing (𝓞 K) K)
    (hw : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      w v = algebraMap K (v.adicCompletion K) ((a : K) / (c : K))) :
    ((ν.real (AdelicBox.integralFiniteAdeles (𝓞 K) K) : ℂ))⁻¹ *
        fourierIntegral (standardFiniteAddCharacter K) ν
          (sIntegerPeriodicFiniteTest K S c hc h f d) w =
      ((sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨c, hc⟩).val : ℂ)⁻¹ *
        sIntegerLocalFourierProduct K μv S h w *
        sIntegerPeriodicDivisorFourier K (S : Set (HeightOneSpectrum (𝓞 K))) hS c hc f d
          (Ideal.Quotient.mk _ a) := by
  letI := finite_sIntegerPrincipalResidue K (S : Set (HeightOneSpectrum (𝓞 K))) c hc
  letI := Fintype.ofFinite (OS ⧸ Ideal.span ({c} : Set OS))
  rw [fourierIntegral_sIntegerPeriodicFiniteTest K S c hc ν h hlc hcs f d,
    Finset.mul_sum, sIntegerPeriodicDivisorFourier_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  calc
    _ = f (Ideal.Quotient.mk _ d * r) *
        (((ν.real (AdelicBox.integralFiniteAdeles (𝓞 K) K) : ℂ))⁻¹ *
          fourierIntegral (standardFiniteAddCharacter K) ν
            (sIntegerPeriodicCosetMask K S c hc h r) w) := by ring
    _ = _ := by
      rw [sIntegerPeriodicCosetMask_fourier_div K S hS c hc ν μv h hlc hcs r a w hw]
      ring

end HeckeGeneral.Bridge

