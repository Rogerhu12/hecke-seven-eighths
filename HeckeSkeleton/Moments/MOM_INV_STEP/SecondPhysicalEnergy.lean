import HeckeSkeleton.Moments.MOM_INV_STEP.SecondColumnEnergy
import HeckeSkeleton.Moments.MOM_INV_STEP.SecondParentRetained
import HeckeSkeleton.Moments.MOM_INV_STEP.FixedSecondCutoff

/-!
# The genuine second Haar source enters its positive canonical columns

The logarithmic cutoff is fixed once and proved to equal one whenever
the original powered norm test is nonzero. Thus the complete squarefree
pool can remain intact. Full mutual Moebius extension retains the
physical Haar kernel before Cauchy. Both energies use its same actual
Fourier density, with only the first frequency reflected by conjugation.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondPhysicalEnergy

open NumberField IsDedekindDomain MeasureTheory UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
  DedekindZetaZeroFree.LargeSieve
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools CommonKernel
  SecondCanonicalEnergy CanonicalFirstEnergy FullMobius
open scoped Classical BigOperators FourierTransform nonZeroDivisors

theorem star_phase_neg (τ x : ℝ) : star (columnPhase (-τ) x) = columnPhase τ x := by
  have he : columnPhase (-τ) x = star (columnPhase τ x) := by
    simp only [columnPhase, inner_neg_left, AddChar.map_neg_eq_inv,
      Circle.coe_inv_eq_conj, Complex.star_def]
  rw [he, star_star]

theorem conjugate_column_norm {ι : Type*} (T : Finset ι) (a : ι → ℂ) (x : ι → ℝ)
    (τ : ℝ) :
    ‖∑ i ∈ T, star (a i) * columnPhase τ (x i)‖ =
      ‖∑ i ∈ T, a i * columnPhase (-τ) (x i)‖ := by
  have he : (∑ i ∈ T, star (a i) * columnPhase τ (x i)) =
      star (∑ i ∈ T, a i * columnPhase (-τ) (x i)) := by
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [star_mul', star_phase_neg]
  rw [he, norm_star]

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ
variable {σ : Type*} [DecidableEq σ] {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}

def kernel (P : Profile K S) : SchwartzMap LogPlane ℂ :=
  orbitalKernel K Sset Γ P.finiteTest P.finiteTest_continuous P.finiteTest_compact
    secondCutoff secondCutoff_contDiff secondCutoff_hasCompactSupport P.archTest P.radius

def density (P : Profile K S) : SchwartzMap LogPlane ℂ := 𝓕 (kernel K S Γ P)

theorem profile_eq_kernel (P : Profile K S) (Y : ℝ)
    (hleft : P.leftScale.val = Y) (hright : P.rightScale.val = Y)
    (z₁ z₂ : Ext)
    (h₁ : height K Sset z₁ / Y ∈ Set.Icc (1 / 8 : ℝ) (21 / 8))
    (h₂ : height K Sset z₂ / Y ∈ Set.Icc (1 / 8 : ℝ) (21 / 8)) :
    P.value K S z₁.val z₂.val =
      kernel K S Γ P (logPoint (Real.log (height K Sset z₁ / Y))
        (Real.log (height K Sset z₂ / Y))) := by
  rw [kernel, orbitalKernel_apply, secondCutoff_one _ _ h₁.1 h₁.2 h₂.1 h₂.2, one_mul]
  have hp := sUnitJointRadialProfile_at_logs K Sset P.archTest P.finiteTest P.radius
    (FirstSourceEnergy.normScale K P.leftScale z₁.val)
    (FirstSourceEnergy.normScale K P.rightScale z₂.val) 0
  rw [traceSchwartzEulerIterCLM_zero] at hp
  change P.value K S z₁.val z₂.val =
    sUnitJointRadialProfile K Sset P.archTest P.finiteTest P.radius 0
      (Real.log (height K Sset z₁ / Y), Real.log (height K Sset z₂ / Y))
  simpa only [Profile.value, FirstSourceEnergy.normScale, height, hleft, hright] using hp.symm

variable (C : ColumnFamily K Sset σ Θ ψ) (γ₀ : OuterTriple K)
variable (G : HeckeCharacter K) (g j d₂ I : Ext) (ξ : Sector)
variable (W : SchwartzMap ℝ ℂ) (X : ℝ)

def sourceCoefficient (z : Ext) : ℂ :=
  sourceTerm K S Γ D C.lambda (C.background γ₀ * G⁻¹) g j d₂ I ξ
    (childPuncture C.originalPuncture γ₀) (C.survivors γ₀) C.primeLists C.primeWeights
    W (X / height K Sset g) z

def sourcePool : Finset Ext := squarefreePool K Sset (2 * X / height K Sset g)

def mobiusColumn (v : Ideal (𝓞 K)) (τ : ℝ) : ℂ :=
  ∑ z ∈ sourcePool K S g X with v ∣ z.val.val,
    sourceCoefficient K S D Γ C γ₀ G g j d₂ I ξ W X z *
      columnPhase τ (Real.log (height K Sset z / (X / height K Sset g)))

theorem mobiusColumn_exterior (v : Ext) (τ : ℝ) :
    mobiusColumn K S D Γ C γ₀ G g j d₂ I ξ W X v.val.val τ =
      SecondColumnEnergy.sourceColumn K S D Γ C γ₀ G g j d₂ v I ξ W X τ := rfl

def source (P : Profile K S) : ℂ :=
  ∑ z₁ ∈ sourcePool K S g X, ∑ z₂ ∈ sourcePool K S g X,
    if IsCoprime z₁.val.val z₂.val.val then
      star (sourceCoefficient K S D Γ C γ₀ G g j d₂ I ξ W X z₁) *
        sourceCoefficient K S D Γ C γ₀ G g j d₂ I ξ W X z₂ *
          P.value K S z₁.val z₂.val else 0

def positiveEnergy (P : Profile K S) (coordinate : LogPlane → ℝ) : ℝ :=
  ∑ v ∈ divisorPool (sourcePool K S g X) (fun z => z.val.val), ‖(moebius v : ℂ)‖ *
    ∫ τ : LogPlane, ‖density K S Γ P τ‖ *
      ‖mobiusColumn K S D Γ C γ₀ G g j d₂ I ξ W X v (coordinate τ)‖ ^ 2

theorem sourceCoefficient_window
    (hW : tsupport W ⊆ Set.Icc (1 / 8 : ℝ) (21 / 8)) (z : Ext)
    (hz : sourceCoefficient K S D Γ C γ₀ G g j d₂ I ξ W X z ≠ 0) :
    height K Sset z / (X / height K Sset g) ∈ Set.Icc (1 / 8 : ℝ) (21 / 8) := by
  apply hW
  apply subset_closure
  apply Function.mem_support.mpr
  intro hw
  apply hz
  unfold sourceCoefficient sourceTerm
  change _ * W (height K Sset z / (X / height K Sset g)) = 0
  rw [hw, mul_zero]

theorem source_eq_common_kernel (P : Profile K S)
    (hleft : P.leftScale.val = X / height K Sset g)
    (hright : P.rightScale.val = X / height K Sset g)
    (hW : tsupport W ⊆ Set.Icc (1 / 8 : ℝ) (21 / 8)) :
    source K S D Γ C γ₀ G g j d₂ I ξ W X P =
      ∑ z₁ ∈ sourcePool K S g X, ∑ z₂ ∈ sourcePool K S g X,
        if IsCoprime z₁.val.val z₂.val.val then
          star (sourceCoefficient K S D Γ C γ₀ G g j d₂ I ξ W X z₁) *
            sourceCoefficient K S D Γ C γ₀ G g j d₂ I ξ W X z₂ *
              kernel K S Γ P (logPoint
                (Real.log (height K Sset z₁ / (X / height K Sset g)))
                (Real.log (height K Sset z₂ / (X / height K Sset g)))) else 0 := by
  unfold source
  apply Finset.sum_congr rfl
  intro z₁ hz₁
  apply Finset.sum_congr rfl
  intro z₂ hz₂
  by_cases hc₁ : sourceCoefficient K S D Γ C γ₀ G g j d₂ I ξ W X z₁ = 0
  · simp only [hc₁, star_zero, zero_mul]
  by_cases hc₂ : sourceCoefficient K S D Γ C γ₀ G g j d₂ I ξ W X z₂ = 0
  · simp only [hc₂, mul_zero, zero_mul]
  rw [profile_eq_kernel K S Γ P (X / height K Sset g) hleft hright z₁ z₂
    (sourceCoefficient_window K S D Γ C γ₀ G g j d₂ I ξ W X hW z₁ hc₁)
    (sourceCoefficient_window K S D Γ C γ₀ G g j d₂ I ξ W X hW z₂ hc₂)]

/-- The full genuine fixed-common Haar source is extended before
separation. The same actual Fourier density enters both positive
energies; the common factor g is never recomputed. -/
theorem full_source_energy (P : Profile K S)
    (hleft : P.leftScale.val = X / height K Sset g)
    (hright : P.rightScale.val = X / height K Sset g)
    (hW : tsupport W ⊆ Set.Icc (1 / 8 : ℝ) (21 / 8)) :
    ‖source K S D Γ C γ₀ G g j d₂ I ξ W X P‖ ≤
      Real.sqrt (positiveEnergy K S D Γ C γ₀ G g j d₂ I ξ W X P (fun τ => -τ.fst)) *
        Real.sqrt (positiveEnergy K S D Γ C γ₀ G g j d₂ I ξ W X P (fun τ => τ.snd)) := by
  rw [source_eq_common_kernel K S D Γ C γ₀ G g j d₂ I ξ W X P hleft hright hW]
  have hb := full_mobius_energy (sourcePool K S g X) (sourcePool K S g X)
    (fun z => z.val.val) (fun z => z.val.val)
    (fun z _ => nonZeroDivisors.coe_ne_zero z.val) (kernel K S Γ P)
    (fun z => Real.log (height K Sset z / (X / height K Sset g)))
    (fun z => Real.log (height K Sset z / (X / height K Sset g)))
    (fun z => star (sourceCoefficient K S D Γ C γ₀ G g j d₂ I ξ W X z))
    (sourceCoefficient K S D Γ C γ₀ G g j d₂ I ξ W X)
  simpa only [positiveEnergy, mobiusColumn, density, conjugate_column_norm] using hb

theorem column_energy_integrable (P : Profile K S) (v : Ideal (𝓞 K))
    (coordinate : LogPlane →L[ℝ] ℝ) :
    Integrable (fun τ : LogPlane => ‖density K S Γ P τ‖ *
      ‖mobiusColumn K S D Γ C γ₀ G g j d₂ I ξ W X v (coordinate τ)‖ ^ 2) := by
  exact IntegralEnergy.integrable_fourier_column_energy
    ((sourcePool K S g X).filter (fun z => v ∣ z.val.val))
    (sourceCoefficient K S D Γ C γ₀ G g j d₂ I ξ W X)
    (fun z => Real.log (height K Sset z / (X / height K Sset g)))
    (kernel K S Γ P) coordinate

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondPhysicalEnergy

end
