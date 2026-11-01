import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CompleteMovingRowRecipe
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondExceptionalPartition
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CenteredAllocatedChildren

/-!
# Actual residual unit sectors before child calibration

The residual element determines both its complete exterior ideal and
its original unit sector.  Two elements generating the same ideal need
not lie in the same sector.  The source is therefore partitioned by the
actual sector before its complete-row calibration is constructed.

The restriction changes the row type to the corresponding subtype.
Thus a dictionary quantified over every row of that type has the sector
identity even outside the finite source carrier.  Only filtering a
finset while retaining the original row type would not have this fact.

Every original row is retained in exactly one sector.  All coefficients,
locations, scales, allocations and extracted elements remain literal.
Both ordinary energy and the complete centered subtraction are preserved
by the finite partition, before either capacity choice.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}

namespace ActualChildRow

variable {Ih : A.Exterior} {h g : A.R} {factor : ℝ}
variable (r : ActualChildRow Ih h g factor)

/-- The very residual element chosen by the source, modulo sixth
powers of original S-units. -/
def orbit : ActualSIntegerOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) :=
  Quotient.mk _ (⟨r.element, r.generates.1⟩ : NonzeroRingElements A.R)

theorem orbit_ideal :
    actualSIntegerOrbitIdeal K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) r.orbit =
      r.momentIdeal := by
  apply Subtype.ext
  change sIntegerModulusContraction K
    (A.Sf : Set (HeightOneSpectrum (𝓞 K))) r.element = r.ideal.val
  unfold sIntegerModulusContraction
  rw [r.generates.2]
  exact under_map_coprime_sIntegerIdeal K
    (A.Sf : Set (HeightOneSpectrum (𝓞 K))) r.ideal.val
    (fun v hv => (A.exterior_iff ⟨r.ideal.val, r.ideal.property.1⟩).mp
      r.ideal.property.2 v (Finset.mem_coe.mp hv))

variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))

def completeDecomposition :
    ExteriorIdeal K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) ×
      SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) :=
  (exteriorIdealSectorsEquivActualOrbits K
    (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P).symm r.orbit

def sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) :=
  (r.completeDecomposition P).2

theorem completeDecomposition_ideal :
    (r.completeDecomposition P).1 = HeckeAxiom.exteriorEquiv A r.ideal := by
  apply Subtype.ext
  have he := (exteriorIdealSectorsEquivActualOrbits K
    (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P).apply_symm_apply r.orbit
  have hi := congrArg
    (actualSIntegerOrbitIdeal K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) he
  change actualSIntegerOrbitIdeal K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
    (decomposedIdealSectorOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      P (r.completeDecomposition P)) = _ at hi
  rw [decomposedIdealSectorOrbit_ideal, r.orbit_ideal] at hi
  exact hi

theorem orbit_eq_decomposed :
    r.orbit = decomposedIdealSectorOrbit K
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P
        (HeckeAxiom.exteriorEquiv A r.ideal, r.sector P) := by
  have he := (exteriorIdealSectorsEquivActualOrbits K
    (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P).apply_symm_apply r.orbit
  change decomposedIdealSectorOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
    P (r.completeDecomposition P) = r.orbit at he
  calc
    r.orbit = decomposedIdealSectorOrbit K
        (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P (r.completeDecomposition P) := he.symm
    _ = _ := congrArg (decomposedIdealSectorOrbit K
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
        (Prod.ext (r.completeDecomposition_ideal P) rfl)

/-- The exact complete-row dictionary, with the sector computed from
the actual residual element rather than chosen independently. -/
theorem orbit_evaluation
    (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    actualOrbitSexticEvaluation K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding I r.orbit =
      heckeIdealCoefficient K
        (completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
          P R (r.sector P) r.momentIdeal) I *
        decomposedIdealRowMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
          (HeckeAxiom.exteriorEquiv A r.ideal) I := by
  rw [r.orbit_eq_decomposed P, actualOrbitSexticEvaluation_decomposed_character K
    (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R]
  rw [completeIdealRowCharacter_exterior K
    (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R (r.sector P)
    (HeckeAxiom.exteriorEquiv A r.ideal)]
  rfl

end ActualChildRow

namespace ActualAllocatedSource

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {σ : K →+* ℂ} {k : ℕ}
variable (s : ActualAllocatedSource A V H k)

/-- Retype the original source; every row in the new type satisfies p,
independently of membership in the finite carrier. -/
def subtypeRows (p : H → Prop) : ActualAllocatedSource A V {h : H // p h} k where
  allocation := s.allocation
  rows := s.rows.subtype p
  weight h := s.weight h.val
  originalIdeal h := s.originalIdeal h.val
  frequency h := s.frequency h.val
  extractedFactor h := s.extractedFactor h.val
  normFactor h := s.normFactor h.val
  row h := s.row h.val
  characters h := s.characters h.val
  scale₁ := s.scale₁
  scale₂ := s.scale₂
  base := s.base
  base_gt_one := s.base_gt_one
  length := s.length
  length_pos := s.length_pos
  leftWeight h := s.leftWeight h.val
  rightWeight h := s.rightWeight h.val
  slotWeight h := s.slotWeight h.val
  leftLocation h := s.leftLocation h.val
  rightLocation h := s.rightLocation h.val
  slotLocation h := s.slotLocation h.val

theorem subtypeRows_energy (p : H → Prop) (ξ : V) :
    (s.subtypeRows p).energy (σ := σ) ξ =
      (s.restrictRows p).energy (σ := σ) ξ := by
  simp only [energy, subtypeRows, restrictRows, jointColumnEnergy,
    Finset.sum_subtype_eq_sum_filter]

theorem subtypeRows_centeredEnergy (p : H → Prop) (N₁ N₂ : ℝ)
    (v₁ v₂ : H → HeckeGeneral.Analysis.NonzeroIdeal K → ℂ) (ξ : V) :
    (s.subtypeRows p).centeredEnergy (σ := σ) N₁ N₂
        (fun h => v₁ h.val) (fun h => v₂ h.val) ξ =
      (s.restrictRows p).centeredEnergy (σ := σ) N₁ N₂ v₁ v₂ ξ := by
  simp only [centeredEnergy, subtypeRows, restrictRows, jointColumnEnergy,
    Finset.sum_subtype_eq_sum_filter]

variable {B : Type*} [Fintype B]

/-- A finite original classifier gives an exact partition of the
source energy; no row is discarded and no new coefficient is inserted. -/
theorem energy_eq_sum_subtypeRows (label : H → B) (ξ : V) :
    s.energy (σ := σ) ξ =
      ∑ b, (s.subtypeRows (fun h => label h = b)).energy (σ := σ) ξ := by
  simp_rw [s.subtypeRows_energy]
  unfold energy restrictRows jointColumnEnergy
  exact (Finset.sum_fiberwise s.rows label _).symm

theorem centeredEnergy_eq_sum_subtypeRows (label : H → B) (N₁ N₂ : ℝ)
    (v₁ v₂ : H → HeckeGeneral.Analysis.NonzeroIdeal K → ℂ) (ξ : V) :
    s.centeredEnergy (σ := σ) N₁ N₂ v₁ v₂ ξ =
      ∑ b, (s.subtypeRows (fun h => label h = b)).centeredEnergy (σ := σ)
        N₁ N₂ (fun h => v₁ h.val) (fun h => v₂ h.val) ξ := by
  simp_rw [s.subtypeRows_centeredEnergy]
  unfold centeredEnergy restrictRows jointColumnEnergy
  exact (Finset.sum_fiberwise s.rows label _).symm

private theorem sqrt_sum_le_sum_sqrt (I : Finset B) (f : B → ℝ) :
    Real.sqrt (∑ i ∈ I, f i) ≤ ∑ i ∈ I, Real.sqrt (f i) := by
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    simp only [Finset.sum_insert hi]
    exact (sqrt_add_le_sqrt_add_sqrt _ _).trans (add_le_add_left ih _)

theorem sqrt_energy_le_sum_subtypeRows (label : H → B) (ξ : V) :
    Real.sqrt (s.energy (σ := σ) ξ) ≤
      ∑ b, Real.sqrt ((s.subtypeRows (fun h => label h = b)).energy (σ := σ) ξ) := by
  rw [s.energy_eq_sum_subtypeRows label ξ]
  exact sqrt_sum_le_sum_sqrt _ _

variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))

def sectorSource (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) :
    ActualAllocatedSource A V {h : H // (s.row h).sector P = ν} k :=
  s.subtypeRows (fun h => (s.row h).sector P = ν)

theorem sectorSource_sector
    (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (h : {h : H // (s.row h).sector P = ν}) :
    ((s.sectorSource P ν).row h).sector P = ν := h.property

/-- The sector identity is valid on every row of the new type, as
required by FullCalibration.dictionary. -/
theorem sectorSource_orbit
    (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (h : {h : H // (s.row h).sector P = ν}) :
    ((s.sectorSource P ν).row h).orbit = decomposedIdealSectorOrbit K
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P
        (HeckeAxiom.exteriorEquiv A ((s.sectorSource P ν).row h).ideal, ν) := by
  rw [ActualChildRow.orbit_eq_decomposed, s.sectorSource_sector P ν h]

local instance actualChildSectorsUnitClassesFintype :
    Fintype (SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) :=
  Fintype.ofFinite _

theorem energy_eq_sum_sectors : ∀ ξ : V,
    s.energy (σ := σ) ξ = ∑ ν, (s.sectorSource P ν).energy (σ := σ) ξ :=
  s.energy_eq_sum_subtypeRows (fun h => (s.row h).sector P)

theorem sqrt_energy_le_sum_sectors : ∀ ξ : V,
    Real.sqrt (s.energy (σ := σ) ξ) ≤
      ∑ ν, Real.sqrt ((s.sectorSource P ν).energy (σ := σ) ξ) :=
  s.sqrt_energy_le_sum_subtypeRows (fun h => (s.row h).sector P)

/-- Cauchy on two independently partitioned sides retains every
cross-sector pair.  No same-sector inequality is substituted for it. -/
theorem paired_sqrt_energy_le_sum_sectorPairs
    {H' : Type*} {k' : ℕ} (right : ActualAllocatedSource A V H' k') (ξ : V) :
    Real.sqrt (s.energy (σ := σ) ξ) * Real.sqrt (right.energy (σ := σ) ξ) ≤
      ∑ ν, ∑ μ,
        Real.sqrt ((s.sectorSource P ν).energy (σ := σ) ξ) *
          Real.sqrt ((right.sectorSource P μ).energy (σ := σ) ξ) := by
  have h := mul_le_mul (s.sqrt_energy_le_sum_sectors P ξ)
    (right.sqrt_energy_le_sum_sectors P ξ) (Real.sqrt_nonneg _)
    (Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _)
  simpa only [Finset.sum_mul, Finset.mul_sum] using h

end ActualAllocatedSource
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualChildRow.orbit_evaluation
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.centeredEnergy_eq_sum_subtypeRows
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.sectorSource_orbit
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.energy_eq_sum_sectors
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.paired_sqrt_energy_le_sum_sectorPairs
