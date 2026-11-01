import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalActualJointSources
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalBlockRowClasses
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedCapacityChild

/-!
# The existing row label retains the same calibrated source

A predicate which holds on the entire original row type only attaches
proofs to those rows. Removing those proofs preserves the actual source,
its row fibres, its child data and every numerical capacity field. No new
finite class, source bound, or choice of a removed set is introduced.

The canonical block labels already contain the nonunit pattern. Their
finite character coordinate can also carry the actual extracted sector;
this is chosen before either Fourier variable and before child selection.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ω ψ : HeckeCharacter K} {k : ℕ}

namespace ActualAllocatedSource

variable (s : ActualAllocatedSource A V H k) (p : H → Prop) (hp : ∀ h, p h)

/-- Proof-only retyping is an equivalence on all original row indices. -/
def allSubtypeEquiv : H ≃ {h : H // p h} where
  toFun h := ⟨h, hp h⟩
  invFun h := h.val
  left_inv _ := rfl
  right_inv _ := rfl

include hp in
theorem allSubtype_energy (ξ : V) :
    (s.subtypeRows p).energy (σ := σ) ξ = s.energy (σ := σ) ξ := by
  rw [s.subtypeRows_energy p ξ]
  have he : s.rows.filter p = s.rows := Finset.filter_eq_self.mpr (fun h _ => hp h)
  change jointColumnEnergy (s.rows.filter p) _ _ _ _ ξ = _
  rw [he]
  rfl

namespace Calibration

variable {s p}
variable (D : (s.subtypeRows p).Calibration (σ := σ) ω ψ)

/-- The original source receives the same already constructed atom
calibration. All child fields are unchanged; the row proofs are erased. -/
def ofAllSubtype (hp : ∀ h, p h) : s.Calibration (σ := σ) ω ψ where
  data := D.data
  parameters := D.parameters
  height := D.height
  count := D.count
  lengths := D.lengths
  left_scale := D.left_scale
  right_scale := D.right_scale
  slot_sum := D.slot_sum
  dictionary ξ h := D.dictionary ξ ⟨h, hp h⟩
  left_support ξ h hh := D.left_support ξ ⟨h, hp h⟩ (Finset.mem_subtype.mpr hh)
  right_support ξ h hh := D.right_support ξ ⟨h, hp h⟩ (Finset.mem_subtype.mpr hh)
  slot_support ξ h hh i := D.slot_support ξ ⟨h, hp h⟩ (Finset.mem_subtype.mpr hh) i
  left_profile ξ h hh I hI :=
    D.left_profile ξ ⟨h, hp h⟩ (Finset.mem_subtype.mpr hh) I hI
  right_profile ξ h hh I hI :=
    D.right_profile ξ ⟨h, hp h⟩ (Finset.mem_subtype.mpr hh) I hI
  slot_profile ξ h hh i q hq :=
    D.slot_profile ξ ⟨h, hp h⟩ (Finset.mem_subtype.mpr hh) i q hq
  allowed ξ h hh := D.allowed ξ ⟨h, hp h⟩ (Finset.mem_subtype.mpr hh)
  cutoff h hh := D.cutoff ⟨h, hp h⟩ (Finset.mem_subtype.mpr hh)
  nonexceptional ξ h hh := D.nonexceptional ξ ⟨h, hp h⟩ (Finset.mem_subtype.mpr hh)
  rowBound := D.rowBound
  rowBound_nonneg := D.rowBound_nonneg
  row_bound h hh := D.row_bound ⟨h, hp h⟩ (Finset.mem_subtype.mpr hh)
  scalarBound := D.scalarBound
  scalarBound_nonneg := D.scalarBound_nonneg
  scalar_bound h hh := D.scalar_bound ⟨h, hp h⟩ (Finset.mem_subtype.mpr hh)
  fiberBound := D.fiberBound
  fibers I := by
    have he : (s.rows.filter (fun h => (s.row h).momentIdeal = I)).card =
        ((s.subtypeRows p).rows.filter
          (fun h => ((s.subtypeRows p).row h).momentIdeal = I)).card := by
      apply Finset.card_bij (fun h _ => (⟨h, hp h⟩ : {h : H // p h}))
      · intro h hh
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_subtype.mpr (Finset.mem_filter.mp hh).1, (Finset.mem_filter.mp hh).2⟩
      · intro h _ h' _ he
        exact congrArg Subtype.val he
      · intro h hh
        refine ⟨h.val, Finset.mem_filter.mpr ?_, ?_⟩
        · exact ⟨Finset.mem_subtype.mp (Finset.mem_filter.mp hh).1,
            (Finset.mem_filter.mp hh).2⟩
        · rfl
    exact he.trans_le (D.fibers I)
  principal_in_theta := D.principal_in_theta
  slot_in_theta := D.slot_in_theta

@[simp] theorem ofAllSubtype_data (hp : ∀ h, p h) :
    (D.ofAllSubtype hp).data = D.data := rfl

@[simp] theorem ofAllSubtype_parameters (hp : ∀ h, p h) :
    (D.ofAllSubtype hp).parameters = D.parameters := rfl

@[simp] theorem ofAllSubtype_mass (hp : ∀ h, p h) :
    (D.ofAllSubtype hp).mass = D.mass := rfl

namespace NormalizedCapacityData

variable {D}

/-- Capacity data are transported before any capacity choice. In
particular the prime bounds and the signed profile radius stay literal. -/
def ofAllSubtype (G : D.NormalizedCapacityData) (hp : ∀ h, p h) :
    (D.ofAllSubtype hp).NormalizedCapacityData where
  geometry := G.geometry
  b₂ := G.b₂
  p₂ := G.p₂
  boundary := G.boundary
  ell := G.ell
  gap := G.gap
  δ := G.δ
  mesh := G.mesh
  supportError := G.supportError
  rawClipError := G.rawClipError
  widthError := G.widthError
  leftAnnulus := G.leftAnnulus
  rightAnnulus := G.rightAnnulus
  leftAnnulus_one := G.leftAnnulus_one
  rightAnnulus_one := G.rightAnnulus_one
  left_annulus := G.left_annulus
  right_annulus := G.right_annulus
  gap_pos := G.gap_pos
  kappa_pos := G.kappa_pos
  mesh_nonneg := G.mesh_nonneg
  fits_mesh := G.fits_mesh
  enlargement := G.enlargement
  unit_length := G.unit_length
  actual_width := G.actual_width
  boundary_width := G.boundary_width
  radical_length := G.radical_length
  boundary_nonneg := G.boundary_nonneg
  parent_capacity := G.parent_capacity
  common_length := G.common_length
  paid_shift := G.paid_shift
  raw_length := G.raw_length
  width_error := G.width_error
  budget_nonneg := G.budget_nonneg
  charge_nonneg := G.charge_nonneg
  radius := G.radius
  radius_pos := G.radius_pos
  primeBound := G.primeBound
  primeBound_nonneg := G.primeBound_nonneg
  prime_bound := G.prime_bound

@[simp] theorem ofAllSubtype_radius (G : D.NormalizedCapacityData) (hp : ∀ h, p h) :
    (G.ofAllSubtype hp).radius = G.radius := rfl

@[simp] theorem ofAllSubtype_primeBound (G : D.NormalizedCapacityData) (hp : ∀ h, p h) :
    (G.ofAllSubtype hp).primeBound = G.primeBound := rfl

end NormalizedCapacityData
end Calibration
end ActualAllocatedSource

namespace CanonicalActualJointSources

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (rows : ActualSecondCorrelationRows A σ H ι)
variable (C : A.GeneralArithmeticContext σ η hS)
variable (s : ActualAllocatedSource A V rows.live k)
variable (pattern : ι → Bool)
variable (sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (hpattern : ∀ h : rows.live,
  actualNonunitPattern C rows.primes rows.leftMultiplicity rows.rightMultiplicity
    (rows.frequency h.val) = pattern)
variable (hsector : ∀ h : rows.live, (rows.extractedRow C h).sector P = sector)

/-- For one existing stable label these are the same original rows,
with the two classifier proofs attached. No labels are enumerated. -/
def patternSectorEquiv : rows.live ≃
    CanonicalOriginalPhaseCalibration.PatternSector P rows C pattern sector where
  toFun h := ⟨⟨h, hpattern h⟩, hsector h⟩
  invFun h := h.val.val
  left_inv _ := rfl
  right_inv _ := rfl

include hpattern hsector in
theorem byPatternSector_energy_of_stable (ξ : V) :
    (byPatternSector P rows C s pattern sector).energy (σ := σ) ξ =
      s.energy (σ := σ) ξ := by
  unfold byPatternSector
  rw [ActualAllocatedSource.allSubtype_energy _ _ (fun h => hsector h.val),
    s.allSubtype_energy _ hpattern]

/-- Consume the atom calibration on the proof-bearing row type and
return it to the literal original source, without changing its mass. -/
def calibrationOfStablePatternSector
    (D : (byPatternSector P rows C s pattern sector).Calibration (σ := σ) ω ψ) :
    s.Calibration (σ := σ) ω ψ :=
  (D.ofAllSubtype (fun h => hsector h.val)).ofAllSubtype hpattern

@[simp] theorem calibrationOfStablePatternSector_mass
    (D : (byPatternSector P rows C s pattern sector).Calibration (σ := σ) ω ψ) :
    (calibrationOfStablePatternSector P rows C s pattern sector hpattern hsector D).mass =
      D.mass := rfl

def capacityOfStablePatternSector
    {D : (byPatternSector P rows C s pattern sector).Calibration (σ := σ) ω ψ}
    (G : D.NormalizedCapacityData) :
    (calibrationOfStablePatternSector P rows C s pattern sector hpattern hsector D).
      NormalizedCapacityData :=
  (G.ofAllSubtype (fun h => hsector h.val)).ofAllSubtype hpattern

end CanonicalActualJointSources
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.ofAllSubtype
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalActualJointSources.calibrationOfStablePatternSector
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalActualJointSources.capacityOfStablePatternSector
