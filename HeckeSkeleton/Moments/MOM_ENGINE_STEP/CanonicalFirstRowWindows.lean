import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalGaussOrbitRows

set_option linter.unusedSectionVars false

/-!
# Original radius windows bound the actual first frequencies

The physical cutoff is computed from all original pair moduli and mask
divisors. Its maximum costs no extra factor for the number of columns.
The two actual Gauss row sets use the same cutoff, including the literal
negative representatives on the right. Thus their arithmetic norm
windows follow from original individual radius and modulus windows;
they are not separate hypotheses about a transformed row family.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Bridge
open HeckeGeneral.Characters
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]

section PhysicalCutoff

variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable {ι κ : Type*}

/-- Original single-pair norm windows bound the actual maximum of
inverse dual radii. The cutoff and every exponent are fixed before the
physical frequency is selected. -/
theorem FirstFiniteSource.physicalCutoff_le_original_windows
    (s : FirstFiniteSource K S Γ ι κ)
    (Z cutoffExponent radiusExponent maskExponent modulusExponent : ℝ)
    (hZ : 0 < Z) (hcutoff : s.cutoff ≤ Z ^ cutoffExponent)
    (hradius : s.radius.val ≤ Z ^ radiusExponent)
    (hmask : ∀ D ∈ s.mask.powerset,
      (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val ≤
          Z ^ maskExponent)
    (hmodulus : ∀ i ∈ s.leftColumns, ∀ j ∈ s.rightColumns,
      (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
        ⟨(s.pairs i j).modulus, (s.pairs i j).modulus_ne_zero⟩).val ≤
          Z ^ modulusExponent) :
    s.physicalCutoff ≤ Z ^
      (cutoffExponent + radiusExponent + maskExponent + modulusExponent) := by
  sorry

end PhysicalCutoff

section ArithmeticRows

variable {A : SArithmeticData K}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]

local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ

/-- The negative first frequency has the same principal modulus. No
choice of another orbit representative is involved. -/
theorem originalFrequencyIdeal_neg_norm (h : A.R) (hh : h ≠ 0) :
    A.exteriorNorm (originalFrequencyIdeal (-h)) =
      A.exteriorNorm (originalFrequencyIdeal h) := by
  sorry

variable {ι κ : Type*}

theorem FirstFiniteSource.originalFrequency_norm_le
    (s : FirstFiniteSource K A.Sf Γ ι κ) (q : Q) (hq : q ∈ s.rows) :
    A.exteriorNorm (originalFrequencyIdeal q.out.val) ≤ s.physicalCutoff := by
  sorry

theorem FirstFiniteSource.originalNegativeFrequency_norm_le
    (s : FirstFiniteSource K A.Sf Γ ι κ) (q : Q) (hq : q ∈ s.rows) :
    A.exteriorNorm (originalFrequencyIdeal (-q.out.val)) ≤ s.physicalCutoff := by
  sorry

variable {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable (C : A.GeneralArithmeticContext σ η hS)
variable (left : Finset ι) (right : Finset κ)
variable (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
variable (DE : Ideal (𝓞 K) × Ideal (𝓞 K))
variable (hDE : DE ∈ commonSupportPool left right
  (fun i => (fullI i).val) (fun j => (fullJ j).val))

/-- Both actual Gauss row dictionaries inherit the one physical cutoff
bound. This supplies the two row windows in `withOriginalPool` from the
original finite source, before any pool or output-row choice. -/
theorem canonicalFirstGaussData_row_windows
    (s : FirstFiniteSource K A.Sf Γ ι κ) (Z R : ℝ)
    (hcutoff : s.physicalCutoff ≤ Z ^ R) :
    (∀ h ∈ (canonicalFirstLeftGaussData C left right fullI fullJ DE hDE s.rows).rows,
      A.exteriorNorm (originalFrequencyIdeal h) ≤ Z ^ R) ∧
    (∀ h ∈ (canonicalFirstRightGaussData C left right fullI fullJ DE hDE s.rows).rows,
      A.exteriorNorm (originalFrequencyIdeal h) ≤ Z ^ R) := by
  sorry

end ArithmeticRows
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstFiniteSource.physicalCutoff_le_original_windows
#print axioms HeckeSkeleton.Moments.EngineStep.originalFrequencyIdeal_neg_norm
#print axioms HeckeSkeleton.Moments.EngineStep.canonicalFirstGaussData_row_windows
