import ActualGramRowBallOrbitalMajorant
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentConstantSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentOrbitFibre
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondTailBudget

/-!
# A constructed positive orbital test for the original row ball

The fixed compact tensor from `ActualGramRowBallOrbitalMajorant` is
normalized by its actual positive Haar covolume.  It dominates one on
every positive radius at most one.  Thus the original row cutoff gives
the required positive Gauss chart, with unit fibres obtained from the
original row ideals.  Neither a positive-profile certificate nor a
row-weight estimate is a premise of the parent constructor.

The subgroup used to construct the fixed bump is the full sixth-power
unit subgroup.  The resulting Haar profile works for any original
subgroup: the orbital integral itself only depends on its positive
radial argument.  No original unit sector is changed.

This constructs the original source majorant.  It does not assert a
translated common Fourier chart for the transformed columns.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open DedekindZetaZeroFree

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft

namespace CanonicalRowBall

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "SF" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
variable [MeasurableSpace (sLocalNormOneGroup K ((S : Set (HeightOneSpectrum (𝓞 K)))))]
  [BorelSpace (sLocalNormOneGroup K ((S : Set (HeightOneSpectrum (𝓞 K)))))]

def mass : ℝ := (sUnitHaarCovolume K SF (sixthPowerUnits K SF)).toReal

theorem mass_pos : 0 < mass K S := rowBall_covolume_pos K S

/-- This test and its finite-place family are fixed before the moving
row radius, model, characters, or polynomial coefficients. -/
def archTest (B : ℝ) : 𝓢(V, ℂ) :=
  (((mass K S)⁻¹ : ℝ) : ℂ) • rowBallArchTest K S B

variable {K S}
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}
local notation "Q" => SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ

theorem profile_eq (B : ℝ) (r : {r : ℝ // 0 < r}) (q : Q) :
    gaussSourceProfile (archTest K S B)
      (sIntegerFiniteTestFunction K S (rowBallFiniteFamily K S B)) r q =
      (((mass K S)⁻¹ : ℝ) : ℂ) *
        sUnitOrbitalProfile K (S : Set (HeightOneSpectrum (𝓞 K)))
          (sLocalTensorTestFunction K (S : Set (HeightOneSpectrum (𝓞 K)))
            (rowBallArchTest K S B)
            (sIntegerFiniteTestFunction K S (rowBallFiniteFamily K S B)))
          ⟨r.val * (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).val,
            mul_pos r.property
              (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).property⟩ := by
  unfold gaussSourceProfile archTest
  rw [sUnitOrbitalProfile_tensor_smul, smul_eq_mul]

theorem profile_real_nonnegative (B : ℝ) (r : {r : ℝ // 0 < r}) (q : Q) :
    (gaussSourceProfile (archTest K S B)
      (sIntegerFiniteTestFunction K S (rowBallFiniteFamily K S B)) r q).im = 0 ∧
    0 ≤ (gaussSourceProfile (archTest K S B)
      (sIntegerFiniteTestFunction K S (rowBallFiniteFamily K S B)) r q).re := by
  rw [profile_eq]
  have hp := rowBall_orbitalProfile_real_nonnegative K S B
    ⟨r.val * (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).val,
      mul_pos r.property
        (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).property⟩
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, sub_zero, hp.1, mul_zero]
  exact ⟨rfl, mul_nonneg (inv_nonneg.mpr (mass_pos K S).le) hp.2⟩

theorem profile_ge_one (B : ℝ) (r : {r : ℝ // 0 < r}) (q : Q)
    (hq : r.val * (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).val ≤ B) :
    1 ≤ (gaussSourceProfile (archTest K S B)
      (sIntegerFiniteTestFunction K S (rowBallFiniteFamily K S B)) r q).re := by
  rw [profile_eq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hp := rowBall_orbitalProfile_lower K S B
    ⟨r.val * (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).val,
      mul_pos r.property
        (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).property⟩ hq
  change mass K S ≤ _ at hp
  calc
    1 = (mass K S)⁻¹ * mass K S := (inv_mul_cancel₀ (mass_pos K S).ne').symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr (mass_pos K S).le)

/-- The positive-profile fields are consequences of the constructed
fixed bump.  Only the literal finite row map and its arithmetic mask
and fibre information remain. -/
theorem chart {H : Type*} (rows : Finset H) (rowMap : H → Q)
    (r : {r : ℝ // 0 < r}) (B : ℝ)
    (mask : Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)))
    (fibres : ℕ)
    (hnorm : ∀ h ∈ rows,
      r.val * (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ (rowMap h)).val ≤ B)
    (hmask : ∀ h ∈ rows,
      sIntegerOrbitAvoidanceMask K (S : Set (HeightOneSpectrum (𝓞 K))) Γ mask (rowMap h) = 1)
    (hfibres : ∀ q, (rows.filter (fun h => rowMap h = q)).card ≤ fibres) :
    GaussEnergyChart rows rowMap (fun _ => 1) (archTest K S B)
      (sIntegerFiniteTestFunction K S (rowBallFiniteFamily K S B)) r mask fibres where
  weight_nonneg _ _ := zero_le_one
  profile_real q := (profile_real_nonnegative B r q).1
  profile_nonneg q := (profile_real_nonnegative B r q).2
  row_weight h hh := profile_ge_one B r (rowMap h) (hnorm h hh)
  row_mask := hmask
  fiber := hfibres

end CanonicalRowBall

section Parent

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {Γ : Subgroup A.U}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable {ω ψ : HeckeCharacter K} {d : MomentData K ω ψ} {a : RealParameters} {Z : ℝ}
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ

/-- The genuine orbit norm is recovered from the original row ideal. -/
theorem parent_orbit_norm_of_originalIdeal
    (rowMap : HeckeGeneral.Analysis.NonzeroIdeal K → Q)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hideal : (ProbeOrbitNormSum.principalExterior A (rowMap u).out).val = u.val) :
    (sIntegerOrbitNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ (rowMap u)).val =
      idealNorm K u := by
  rw [← sIntegerOrbitNorm_out K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ (rowMap u)]
  have hn := generates_sIntegerElementNorm
    (ProbeOrbitNormSum.principalExterior A (rowMap u).out) (rowMap u).out.val
    (ProbeOrbitNormSum.principalExterior_generates A (rowMap u).out)
  change (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
    (rowMap u).out).val = (Ideal.absNorm u.val : ℝ)
  simpa only [hideal] using hn

namespace CanonicalRowBall

def parentRadius (a : RealParameters) (Z : ℝ) (hZ : 0 < Z) : {r : ℝ // 0 < r} :=
  ⟨(Z ^ (a.m + a.q))⁻¹, inv_pos.mpr (Real.rpow_pos_of_pos hZ _)⟩

/-- One fixed normalized test covers the complete actual parent row
ball.  Its norm window and unit fibre are proved internally. -/
theorem parent_chart (hZ : 0 < Z)
    (rowMap : HeckeGeneral.Analysis.NonzeroIdeal K → Q)
    (mask : Finset (HeightOneSpectrum A.R))
    (hideal : ∀ u ∈ pairedRows d a Z,
      (ProbeOrbitNormSum.principalExterior A (rowMap u).out).val = u.val)
    (hmask : ∀ u ∈ pairedRows d a Z,
      sIntegerOrbitAvoidanceMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ mask (rowMap u) = 1) :
    GaussEnergyChart (pairedRows d a Z) rowMap (fun _ => 1) (archTest K A.Sf 1)
      (sIntegerFiniteTestFunction K A.Sf (rowBallFiniteFamily K A.Sf 1))
      (parentRadius a Z hZ) mask 1 := by
  apply chart (pairedRows d a Z) rowMap (parentRadius a Z hZ) 1 mask 1 _ hmask
    (parent_rowMap_fibres_le_one_of_originalIdeal (pairedRows d a Z) rowMap hideal)
  intro u hu
  have hn := ((d.rows_spec (Z ^ (a.m + a.q)) u).mp (Finset.mem_filter.mp hu).1).2
  change (Z ^ (a.m + a.q))⁻¹ *
    (sIntegerOrbitNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ (rowMap u)).val ≤ 1
  rw [parent_orbit_norm_of_originalIdeal rowMap u (hideal u hu)]
  exact (mul_le_mul_of_nonneg_left hn
    (inv_nonneg.mpr (Real.rpow_pos_of_pos hZ _).le)).trans_eq
      (inv_mul_cancel₀ (Real.rpow_pos_of_pos hZ _).ne')

end CanonicalRowBall

variable [Γ.FiniteIndex]
variable {t Y₁ Y₂ : ℝ}
variable {raw : ParentRawAtoms (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) d a Z t Y₁ Y₂}

/-- The actual original source is now produced from the single-column
phase dictionary and the original row ideals.  The common positive
test, its domination, the row fibres, and all four Gram profiles are
constructed inside this definition, for either value of `centered`. -/
def ParentRawAtoms.ConstantValues.rowBallCalibration
    (values : raw.ConstantValues) (hZ : 0 < Z)
    (mask : Finset (HeightOneSpectrum A.R))
    (hideal : ∀ u ∈ pairedRows d a Z,
      (ProbeOrbitNormSum.principalExterior A (raw.rowMap u).out).val = u.val)
    (hmask : ∀ u ∈ pairedRows d a Z,
      sIntegerOrbitAvoidanceMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ mask (raw.rowMap u) = 1)
    (centered : Bool) (col : raw.Column → OrbitalGaussColumn K A.Sf Γ)
    (phase : ∀ i ∈ raw.columns, ∀ q, raw.phase q i = (col i).originalOrbit q) :
    ParentSourceCalibration centered d a Z t Y₁ Y₂ raw.columns
      (fun i j => (col i).originalPair (col j)
        ((values.coefficient centered i * star (values.coefficient centered j)) •
          CanonicalRowBall.archTest K A.Sf 1))
      (sIntegerFiniteTestFunction K A.Sf (rowBallFiniteFamily K A.Sf 1))
      (CanonicalRowBall.parentRadius a Z hZ) mask 1 :=
  values.actualCalibration
    (CanonicalRowBall.parent_chart hZ raw.rowMap mask hideal hmask)
    (continuous_sIntegerFiniteTestFunction K A.Sf _
      (rowBallFiniteFamily_locallyConstant K A.Sf 1))
    (hasCompactSupport_sIntegerFiniteTestFunction K A.Sf _
      (rowBallFiniteFamily_compactSupport K A.Sf 1))
    centered col phase

end Parent

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalRowBall.chart
#print axioms HeckeSkeleton.Moments.EngineStep.parent_orbit_norm_of_originalIdeal
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalRowBall.parent_chart
#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.ConstantValues.rowBallCalibration
