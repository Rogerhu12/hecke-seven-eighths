import HeckeSkeleton.Moments.MOM_INV_STEP.InverseRowMajorant
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalNormPools
import HeckeGeneral.Analysis.DecomposedZeroSlotMomentData

/-!
# The literal initial inverse polynomial and its first Poisson transform

The source here is the original finite ideal polynomial.  Its deleted-S
and nonsquarefree terms vanish before reindexing to the complete exterior
pool.  The inverse sextic value is conjugation also at its zeros.

For an arbitrary row-independent whole-column mark, the same finite
polynomial has a fixed positive orbital majorant.  Primitive Poisson is
then applied to that actual squared orbital series.  Its two fresh
squarefree columns, principal masks, and zero frequencies are retained.
No initial energy inequality or source reconstruction is an input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceReductionPoisson

open NumberField IsDedekindDomain UniqueFactorizationMonoid MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Analysis.ActualSIntegerMoments
  HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open HeckeSkeleton.Moments.MOM_INV_STEP
open CanonicalNormPools
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "OS" => Set.integer Sset K
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

/-- Conjugation of the actual symbol includes the ramified zero case. -/
theorem idealSymbol_inverse (n : Ext) (a : OS) :
    idealSymbol K Sset D n a ^ (-1 : ℤ) = star (idealSymbol K Sset D n a) := by
  by_cases hz : idealSymbol K Sset D n a = 0
  · simp [hz]
  · have hn : ‖idealSymbol K Sset D n a‖ = 1 :=
      norm_sIntegerSexticIdealEvaluation_eq_one K Sset D.root6 D.primitive6 D.embedding
        n.val.val (nonZeroDivisors.coe_ne_zero n.val) n.property
        (fun p hp => D.away_six p (n.property p hp)) a (by
          intro p hp hzero
          exact hz (sIntegerSexticIdealEvaluation_eq_zero_of_badPrime
            K Sset D.root6 D.primitive6 D.embedding n.val.val
            (nonZeroDivisors.coe_ne_zero n.val) n.property
            (fun p hp => D.away_six p (n.property p hp)) a p hp hzero))
    simpa only [zpow_neg_one, Complex.star_def] using Complex.inv_eq_conj hn

theorem zeroExtended_exterior (n : Ext) (a : OS) :
    zeroExtendedSexticIdealEvaluation K Sset D.root6 D.primitive6 D.embedding n.val a =
      idealSymbol K Sset D n a := by
  have hgood : sexticIdealOutsideS K Sset n.val := by
    intro p hp
    exact ⟨n.property p hp, D.away_six p (n.property p hp)⟩
  rw [zeroExtendedSexticIdealEvaluation, dif_pos hgood]
  rfl

/-- The coefficient is fixed before choosing an orbital row.  The
whole-index mark may contain the original puncture and residual slots. -/
def coefficient (ν : HeckeCharacter K) (mark : Ext → ℂ)
    (W : ℝ → ℂ) (X : ℝ) (n : Ext) : ℂ :=
  (Real.sqrt X : ℂ)⁻¹ *
    ((moebius n.val.val : ℂ) * heckeIdealCoefficient K ν n.val *
      mark n * W (height K Sset n / X))

def sourceColumn (ν : HeckeCharacter K) (mark : Ext → ℂ)
    (W : ℝ → ℂ) (X : ℝ) (a : OS) : ℂ :=
  ∑ n ∈ squarefreePool K Sset X,
    coefficient K S ν mark W X n * star (idealSymbol K Sset D n a)

/-- The exterior pool is the exact squarefree part of the original
finite norm envelope with only its fixed-S deleted ideals removed. -/
theorem squarefreePool_image (X : ℝ) (hX : 0 ≤ X) :
    (squarefreePool K Sset X).image (fun n : Ext => n.val) =
      (dyadicIdealSupport K X).filter (fun I => Squarefree I.val ∧
        ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val → p ∉ Sset) := by
  ext I
  simp only [Finset.mem_image, mem_squarefreePool, Finset.mem_filter,
    mem_dyadicIdealSupport_iff K hX]
  constructor
  · rintro ⟨n, ⟨hsf, hnorm⟩, rfl⟩
    exact ⟨hnorm, hsf, n.property⟩
  · rintro ⟨hnorm, hsf, hS⟩
    exact ⟨⟨I, hS⟩, ⟨hsf, hnorm⟩, rfl⟩

/-- Exact equality starting with the original finite inverse ideal
polynomial. No coefficient, support, or row identity is postulated. -/
theorem physical_polynomial_eq_sourceColumn (ν : HeckeCharacter K)
    (W : ℝ → ℂ) (X : ℝ) (hX : 0 ≤ X) (a : OS) :
    sIntegerSexticInverseIdealPolynomial K Sset D.root6 D.primitive6 D.embedding
        ν (dyadicIdealSupport K X) a X W =
      sourceColumn K S D ν (fun _ => 1) W X a := by
  let f : NonzeroIdeal K → ℂ :=
    sIntegerSexticInverseIdealTerm K Sset D.root6 D.primitive6 D.embedding ν a X W
  have hsum : (∑ I ∈ dyadicIdealSupport K X, f I) =
      ∑ I ∈ (dyadicIdealSupport K X).filter (fun I => Squarefree I.val ∧
        ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val → p ∉ Sset), f I := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro I hI hbad
    by_cases hsf : Squarefree I.val
    · have hdeleted : ¬ sexticIdealOutsideS K Sset I := by
        intro hgood
        exact hbad (Finset.mem_filter.mpr ⟨hI, hsf, fun p hp => (hgood p hp).1⟩)
      exact sIntegerSexticInverseIdealTerm_eq_zero_of_deleted
        K Sset D.root6 D.primitive6 D.embedding ν a X W I hdeleted
    · simp only [f, sIntegerSexticInverseIdealTerm, moebius_of_not_squarefree hsf,
        Int.cast_zero, zero_mul]
  rw [← squarefreePool_image K S X hX,
    Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)] at hsum
  unfold sIntegerSexticInverseIdealPolynomial
  change (Real.sqrt X : ℂ)⁻¹ * (∑ I ∈ dyadicIdealSupport K X, f I) = _
  rw [hsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only [f, coefficient, sIntegerSexticInverseIdealTerm]
  rw [zeroExtended_exterior, idealSymbol_inverse]
  change _ = (Real.sqrt X : ℂ)⁻¹ *
    ((moebius n.val.val : ℂ) * heckeIdealCoefficient K ν n.val * 1 *
      W (idealNorm K n.val / X)) * star (idealSymbol K Sset D n a)
  ring

/-- An actual `IdealTest` is extended to the complete norm envelope
using its exact support theorem. The analytic scale and its square-root
normalization remain the original `X`. -/
theorem physical_test_eq_sourceColumn (ν : HeckeCharacter K)
    (W : ConditionalMoments.IdealTest K) (u : NonzeroIdeal K) (t X : ℝ)
    (hX : 0 < X) (hW : Function.support (W.profile u t) ⊆ Set.Iic 2)
    (a : OS) :
    sIntegerSexticInverseIdealPolynomial K Sset D.root6 D.primitive6 D.embedding
        ν (W.support u t X) a X (W.profile u t) =
      sourceColumn K S D ν (fun _ => 1) (W.profile u t) X a := by
  rw [← physical_polynomial_eq_sourceColumn K S D ν (W.profile u t) X hX.le a]
  unfold sIntegerSexticInverseIdealPolynomial
  congr 1
  apply Finset.sum_subset
  · intro I hI
    apply (mem_dyadicIdealSupport_iff K hX.le I).mpr
    exact (div_le_iff₀ hX).mp (hW ((W.support_spec u t X I).mp hI))
  · intro I hI hnot
    have hz : W.profile u t (idealNorm K I / X) = 0 := by
      by_contra hne
      exact hnot ((W.support_spec u t X I).mpr hne)
    simp only [sIntegerSexticInverseIdealTerm, hz, mul_zero]

/-- The original complete-row zero-slot moment polynomial reaches the
literal first-Poisson source through its proved finite-ray calibration.
This theorem quantifies over every exterior row and original sector. -/
theorem decomposed_moment_eq_sourceColumn
    (P : HeckeGeneral.ThetaSkeleton.Physical.ProbeData K Sset)
    (R : HeckeGeneral.ThetaSkeleton.Physical.RowCharacterInput K Sset P)
    (ω η : HeckeCharacter K)
    (ξ : SixthUnitClasses K Sset)
    (W : ConditionalMoments.IdealTest K) (I : Ext) (t X : ℝ)
    (hX : 0 < X) (hW : Function.support (W.profile I.val t) ⊆ Set.Iic 2) :
    ConditionalMoments.inversePolynomial
        (HeckeGeneral.ThetaSkeleton.Physical.decomposedZeroSlotMomentData
          K Sset P R ω η ξ W) I.val X t =
      sourceColumn K S P.arithmetic η (fun _ => 1) (W.profile I.val t) X
        (HeckeGeneral.ThetaSkeleton.Physical.decomposedIdealSectorOrbit
          K Sset P (I, ξ)).out.val := by
  rw [HeckeGeneral.ThetaSkeleton.Physical.inversePolynomial_decomposedZeroSlotMomentData]
  exact physical_test_eq_sourceColumn K S P.arithmetic η W I.val t X hX hW _

variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [Γ.FiniteIndex]

local notation "Orbit" => SIntegerOrbits K Sset Γ
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

def orbitalEnergy (ν : HeckeCharacter K) (mark : Ext → ℂ)
    (W : ℝ → ℂ) (X : ℝ) (H : {r : ℝ // 0 < r}) : ℂ :=
  sIntegerWeightedOrbitalSeries K S Γ (rowBallArchTest K S 1)
    (sIntegerFiniteTestFunction K S (rowBallFiniteFamily K S 1))
    (InverseRowMajorant.rowRadius H)
    (fun q => ((‖sourceColumn K S D ν mark W X q.out.val‖ ^ 2 : ℝ) : ℂ))

theorem orbitalEnergy_re (ν : HeckeCharacter K) (mark : Ext → ℂ)
    (W : ℝ → ℂ) (X : ℝ) (H : {r : ℝ // 0 < r}) :
    (orbitalEnergy K S D Γ ν mark W X H).re =
      InverseRowMajorant.energy K S Γ D (squarefreePool K Sset X)
        (coefficient K S ν mark W X) H := by
  unfold orbitalEnergy sIntegerWeightedOrbitalSeries
  have hs := (InverseRowMajorant.summable_norm_weightedProfile
    K S Γ D (squarefreePool K Sset X) (coefficient K S ν mark W X) H).of_norm
  change (∑' q : Orbit,
    ((‖InverseRowMajorant.amplitude K S Γ D (squarefreePool K Sset X)
      (coefficient K S ν mark W X) q‖ ^ 2 : ℝ) : ℂ) *
      sUnitOrbitalProfile K Sset
        (sLocalTensorTestFunction K Sset (rowBallArchTest K S 1)
          (sIntegerFiniteTestFunction K S (rowBallFiniteFamily K S 1)))
        ⟨H.val⁻¹ * (sIntegerOrbitNorm K Sset Γ q).val,
          mul_pos (inv_pos.mpr H.property) (sIntegerOrbitNorm K Sset Γ q).property⟩).re = _
  rw [Complex.re_tsum hs]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rfl

/-- Positive enlargement uses one fixed row test and the full orbit
family; its coefficient mass and original symbols are unchanged. -/
theorem finite_rows_le_orbital_norm (ν : HeckeCharacter K) (mark : Ext → ℂ)
    (W : ℝ → ℂ) (X : ℝ) (H : {r : ℝ // 0 < r}) (T : Finset Orbit)
    (hT : ∀ q ∈ T, (sIntegerOrbitNorm K Sset Γ q).val ≤ H.val) :
    (∑ q ∈ T, ‖sourceColumn K S D ν mark W X q.out.val‖ ^ 2) ≤
      (InverseRowMajorant.rowCovolume K S)⁻¹ *
        ‖orbitalEnergy K S D Γ ν mark W X H‖ := by
  have h := InverseRowMajorant.finite_rows_le_energy
    K S Γ D (squarefreePool K Sset X) (coefficient K S ν mark W X) H T hT
  apply h.trans
  rw [← orbitalEnergy_re]
  exact mul_le_mul_of_nonneg_left (Complex.re_le_norm _)
    (inv_nonneg.mpr (InverseRowMajorant.rowCovolume_pos K S).le)

theorem orbitalEnergy_eq_inverseSquared (ν : HeckeCharacter K) (mark : Ext → ℂ)
    (W : ℝ → ℂ) (X : ℝ) (H : {r : ℝ // 0 < r}) :
    orbitalEnergy K S D Γ ν mark W X H =
      CanonicalPoissonSource.inverseSquaredRowOrbitalSeries K S D Γ
        (squarefreePool K Sset X) id (fun _ => FirstInversePoisson.unitIdeal K S)
        (coefficient K S ν mark W X) (rowBallArchTest K S 1)
        (rowBallFiniteFamily K S 1) ∅ (InverseRowMajorant.rowRadius H) := by
  unfold orbitalEnergy CanonicalPoissonSource.inverseSquaredRowOrbitalSeries
  congr 1
  funext q
  simp only [sIntegerOrbitAvoidanceMask, Finset.notMem_empty, false_implies, implies_true,
    if_true, one_mul, sourceColumn, FirstInversePoisson.idealSymbol_unit, one_pow,
    id_eq, starRingEnd_apply]

variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
  [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (νa : Measure (FiniteAdeleRing (𝓞 K) K)) [νa.IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include νa μ in
/-- The genuine first primitive Poisson identity on the original
inverse source. All principal and additive-zero terms remain inside the
actual transformed block. -/
theorem genuine_initial_poisson (ν : HeckeCharacter K) (mark : Ext → ℂ)
    (W : ℝ → ℂ) (X : ℝ) (H : {r : ℝ // 0 < r}) :
    orbitalEnergy K S D Γ ν mark W X H =
      ∑ p ∈ squarefreePool K Sset X ×ˢ squarefreePool K Sset X,
        conj (coefficient K S ν mark W X p.1) * coefficient K S ν mark W X p.2 *
          (PrimitivePoissonSource.block K S D Γ hΓ
            (PrimitivePoissonSource.pairSupport K S D p.1 p.2
              (FirstInversePoisson.unitIdeal K S) (FirstInversePoisson.unitIdeal K S))
            (PrimitivePoissonSource.pairExponent K S p.1 p.2
              (FirstInversePoisson.unitIdeal K S) (FirstInversePoisson.unitIdeal K S))
            (rowBallArchTest K S 1) (rowBallFiniteFamily K S 1)
            (rowBallFiniteFamily_locallyConstant K S 1)
            (rowBallFiniteFamily_compactSupport K S 1)
            ∅ (InverseRowMajorant.rowRadius H)).transformed μv D.different_outside := by
  rw [orbitalEnergy_eq_inverseSquared]
  exact PrimitivePoissonSource.inverseSquaredRowOrbitalSeries_primitive_poisson
    K S D Γ hΓ μv νa μ (squarefreePool K Sset X) id
    (fun _ => FirstInversePoisson.unitIdeal K S) (coefficient K S ν mark W X)
    (fun _ hn => squarefreePool_squarefree K Sset hn)
    (rowBallArchTest K S 1) (rowBallFiniteFamily K S 1)
    (rowBallFiniteFamily_locallyConstant K S 1)
    (rowBallFiniteFamily_compactSupport K S 1) ∅ (InverseRowMajorant.rowRadius H)

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceReductionPoisson

end
