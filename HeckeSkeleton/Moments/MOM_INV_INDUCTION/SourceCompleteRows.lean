import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceAnnularRows

/-!
# Literal complete-row calibration for the fixed annular columns

Every complete exterior ideal, in its original sector, is sent to its
actual sixth-unit orbit.  The map is injective and preserves the ideal
norm, including ideals that are not sixth-free.  The coefficient identity
uses the same complete-row coprimality mask, so the larger row ball is
controlled before any amplification or sixth-free restriction.

For positive moving orientation the whole zero-slot polynomial is
conjugated.  Its norm is unchanged; the background and supported test are
both conjugated, and every ramified zero stays zero.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceCompleteRows

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.UniformAmplify
open HeckeSkeleton.Moments.MOM_INV_STEP
open SourceAnnularRows
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]

def conjugateTestCLM : SchwartzMap ℝ ℂ →L[ℝ] SchwartzMap ℝ ℂ :=
  SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap

def conjugateTest (W : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ := conjugateTestCLM W

@[simp] theorem conjugateTest_apply (W : SchwartzMap ℝ ℂ) (x : ℝ) :
    conjugateTest W x = conj (W x) := rfl

theorem conjugateTest_support (W : SchwartzMap ℝ ℂ) :
    tsupport (conjugateTest W) = tsupport W := by
  apply congrArg closure
  ext x
  simp only [Function.mem_support, conjugateTest_apply, map_ne_zero]

/-- The conjugation operator has uniform finite Schwartz control,
selected before any source test or scale. -/
theorem conjugateTest_seminorm (q : Finset (ℕ × ℕ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ W : SchwartzMap ℝ ℂ,
      q.sup (schwartzSeminormFamily ℝ ℝ ℂ) (conjugateTest W) ≤
        C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  let p : Seminorm ℝ (SchwartzMap ℝ ℂ) :=
    (q.sup (schwartzSeminormFamily ℝ ℝ ℂ)).comp conjugateTestCLM.toLinearMap
  have hq : Continuous (fun W : SchwartzMap ℝ ℂ =>
      q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) :=
    Seminorm.continuous_finsetSup (fun i hi =>
      (schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm i)
  obtain ⟨s, C, hC, hb⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℝ ℝ ℂ) p (hq.comp conjugateTestCLM.continuous)
  exact ⟨s, C, C.property, fun W => Seminorm.le_def.mp hb W⟩

variable {ω ψ : HeckeCharacter K}

theorem conjugate_coefficient (d : MomentData K ω ψ) (u I : NonzeroIdeal K) :
    inverseRowCoefficient (conjugateInverseModel d) u I =
      conj (inverseRowCoefficient d u I) := by
  change (UniqueFactorizationMonoid.moebius I.val : ℂ) *
    heckeIdealCoefficient K d.inverseBackground⁻¹ I *
    heckeIdealCoefficient K (d.rowCharacter u) I ^ (-d.direction) * maskValue d u I.val = _
  rw [heckeIdealCoefficient_inv, directed_coefficient_conjugate]
  simp only [inverseRowCoefficient, map_mul, map_intCast, source_mask_conjugate]

theorem conjugate_polynomial (d : MomentData K ω ψ) (u : NonzeroIdeal K)
    (X : ℝ) (W : SchwartzMap ℝ ℂ) :
    polynomial K (conjugateInverseModel d) u X (conjugateTest W) =
      conj (polynomial K d u X W) := by
  simp only [polynomial, conjugate_coefficient, conjugateTest_apply,
    map_mul, map_sum, map_inv₀, Complex.conj_ofReal]

variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset

variable (P : ProbeData K (S : Set (HeightOneSpectrum (𝓞 K))))
  (R : RowCharacterInput K (S : Set (HeightOneSpectrum (𝓞 K))) P)

/-- The coefficient calibration covers every exterior ideal, with no
physical-witness or sixth-free membership premise. -/
theorem negative_polynomial_eq_source (d : MomentData K ω ψ)
    (sector : SixthUnitClasses K Sset)
    (hdir : d.direction = -1)
    (hchar : d.rowCharacter = completeIdealRowCharacter K Sset P R sector)
    (hmask : d.commonMask = completeIdealCommonMask K Sset)
    (I : Ext) (X : ℝ) (hX : 0 < X) (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) :
    polynomial K d I.val X W =
      SourceReductionPoisson.sourceColumn K S P.arithmetic d.inverseBackground
        (fun _ => 1) W X (decomposedIdealSectorOrbit K Sset P (I, sector)).out.val := by
  let d₀ := decomposedZeroSlotMomentData K Sset P R ω d.inverseBackground sector
    (supportedTest K W hW)
  have heq : inversePolynomial (testData K d W hW) I.val X 0 =
      inversePolynomial d₀ I.val X 0 := by
    simp only [inversePolynomial, testData, d₀, decomposedZeroSlotMomentData,
      hdir, hchar, maskValue, hmask]
  rw [← polynomial_eq K d I.val X hX W hW, heq]
  exact SourceReductionPoisson.decomposed_moment_eq_sourceColumn K S P R ω
    d.inverseBackground sector (supportedTest K W hW) I 0 X hX
    (fun y hy => (hW (subset_closure hy)).2)

/-- Norm identity for the actual positive-oriented inverse family. -/
theorem positive_polynomial_norm (d : MomentData K ω ψ)
    (sector : SixthUnitClasses K Sset)
    (hdir : d.direction = 1)
    (hchar : d.rowCharacter = completeIdealRowCharacter K Sset P R sector)
    (hmask : d.commonMask = completeIdealCommonMask K Sset)
    (I : Ext) (X : ℝ) (hX : 0 < X) (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) :
    ‖polynomial K d I.val X W‖ =
      ‖SourceReductionPoisson.sourceColumn K S P.arithmetic d.inverseBackground⁻¹
        (fun _ => 1) (conjugateTest W) X
        (decomposedIdealSectorOrbit K Sset P (I, sector)).out.val‖ := by
  have heq := negative_polynomial_eq_source K S P R (conjugateInverseModel d) sector
    (by change -d.direction = -1; rw [hdir]) hchar hmask I X hX (conjugateTest W)
    (by rw [conjugateTest_support]; exact hW)
  rw [conjugate_polynomial] at heq
  simpa only [Complex.norm_conj] using congrArg norm heq

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
local notation "Γ" => sixthPowerSUnitSubgroup K Sset
local notation "Orbit" => ActualSIntegerOrbit K Sset

/-- Positive enlargement of the entire complete ideal row ball.  The
map to actual orbits is injective and norm-preserving, so no multiplicity
or row-count factor is introduced before the true Poisson source. -/
theorem complete_positive_rows_le_orbital (d : MomentData K ω ψ)
    (sector : SixthUnitClasses K Sset)
    (hdir : d.direction = 1)
    (hchar : d.rowCharacter = completeIdealRowCharacter K Sset P R sector)
    (hmask : d.commonMask = completeIdealCommonMask K Sset)
    (hrows : d.allowedRow = completeIdealIsExterior K Sset)
    (H X : ℝ) (hH : 0 < H) (hX : 0 < X) (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) :
    (∑ u ∈ d.rows H, ‖polynomial K d u X W‖ ^ 2) ≤
      (InverseRowMajorant.rowCovolume K S)⁻¹ *
        ‖SourceReductionPoisson.orbitalEnergy K S P.arithmetic Γ d.inverseBackground⁻¹
          (fun _ => 1) (conjugateTest W) X ⟨H, hH⟩‖ := by
  let exterior (u : {u // u ∈ d.rows H}) : Ext :=
    ⟨u.val, by
      have he := ((d.rows_spec H u.val).mp u.property).1
      simpa only [hrows] using he⟩
  let row (u : {u // u ∈ d.rows H}) : Orbit :=
    decomposedIdealSectorOrbit K Sset P (exterior u, sector)
  have hinj : Function.Injective row := by
    intro u v huv
    apply Subtype.ext
    have he := congrArg Prod.fst (decomposedIdealSectorOrbit_injective K Sset P huv)
    exact congrArg Subtype.val he
  let T : Finset Orbit := (d.rows H).attach.image row
  have hT : ∀ q ∈ T, (sIntegerOrbitNorm K Sset Γ q).val ≤ H := by
    intro q hq
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hq
    change actualSIntegerOrbitNorm K Sset (decomposedIdealSectorOrbit K Sset P
      (exterior u, sector)) ≤ H
    rw [decomposedIdealSectorOrbit_norm]
    exact ((d.rows_spec H u.val).mp u.property).2
  have heq : (∑ u ∈ d.rows H, ‖polynomial K d u X W‖ ^ 2) =
      ∑ q ∈ T, ‖SourceReductionPoisson.sourceColumn K S P.arithmetic d.inverseBackground⁻¹
        (fun _ => 1) (conjugateTest W) X q.out.val‖ ^ 2 := by
    dsimp only [T]
    rw [Finset.sum_image (fun u hu v hv h => hinj h)]
    rw [← Finset.sum_attach (d.rows H) (fun u => ‖polynomial K d u X W‖ ^ 2)]
    apply Finset.sum_congr rfl
    intro u hu
    rw [positive_polynomial_norm K S P R d sector hdir hchar hmask (exterior u) X hX W hW]
  rw [heq]
  exact SourceReductionPoisson.finite_rows_le_orbital_norm K S P.arithmetic Γ
    d.inverseBackground⁻¹ (fun _ => 1) (conjugateTest W) X ⟨H, hH⟩ T hT

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceCompleteRows

end
