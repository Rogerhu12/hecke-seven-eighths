import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalOrbitFibre
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentRawSourceInput

/-!
# The original parent ideal-to-orbit map has unit fibres

The original parent rows are actual nonzero ideals.  If the ideal of
each supplied orbit representative is that same original ideal, equality
of two orbits forces equality of the original rows.  This proves the
parent fibre bound `1` from individual ideal identities.

The initial-source default uses the already chosen allowed generator in
the arithmetic context.  Its ideal identity is proved from its generator
identity and the original subgroup orbit relation.  The adapter for an
existing `ParentRawAtoms` consumes its own row map throughout.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory

section Representative

variable {R : Type*} [CommRing R] [IsDomain R]

/-- A representative chosen by the quotient still generates the
principal ideal of the element that defined the orbit. -/
theorem nonzero_orbit_out_span_mk (Γ : Subgroup Rˣ)
    (x : NonzeroRingElements R) :
    Ideal.span {(Quotient.mk _ x : MulAction.orbitRel.Quotient Γ
      (NonzeroRingElements R)).out.val} = Ideal.span {x.val} := by
  let q : MulAction.orbitRel.Quotient Γ (NonzeroRingElements R) := Quotient.mk _ x
  have hrel : MulAction.orbitRel Γ (NonzeroRingElements R) q.out x :=
    Quotient.exact (Quotient.out_eq q)
  obtain ⟨u, hu⟩ := hrel
  have hval : q.out.val = (u.val : R) * x.val :=
    (congrArg (fun a : NonzeroRingElements R => a.val) hu).symm
  change Ideal.span {q.out.val} = Ideal.span {x.val}
  rw [hval]
  exact Ideal.span_singleton_mul_left_unit u.val.isUnit x.val

end Representative

variable {K : Type} [Field K] [NumberField K]
variable (A : SArithmeticData K) (Γ : Subgroup A.U)

local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ

/-- An actual generating identity determines the genuine exterior
ideal.  This is a pointwise ideal identity, before any finite count. -/
theorem principalExterior_eq_of_generates (I : A.Exterior)
    (r : A.R) (hr : A.Generates I r) :
    ProbeOrbitNormSum.principalExterior A ⟨r, hr.1⟩ = I := by
  apply A.exteriorIdealEquiv.injective
  apply Subtype.ext
  change A.extendIdeal (ProbeOrbitNormSum.principalExterior A ⟨r, hr.1⟩) = A.extendIdeal I
  exact (ProbeOrbitNormSum.principalExterior_generates A ⟨r, hr.1⟩).2.symm.trans hr.2

/-- The orbit of the literal supplied generator, with the original
global subgroup transported to the S-integer unit group. -/
def parentGeneratorOrbit (I : A.Exterior) (r : A.R) (hr : A.Generates I r) : Q :=
  Quotient.mk _ ⟨r, hr.1⟩

theorem parentGeneratorOrbit_originalIdeal (I : A.Exterior)
    (r : A.R) (hr : A.Generates I r) :
    ProbeOrbitNormSum.principalExterior A (parentGeneratorOrbit A Γ I r hr).out = I := by
  have hspan : Ideal.span {(parentGeneratorOrbit A Γ I r hr).out.val} = A.extendIdeal I :=
    (nonzero_orbit_out_span_mk
      (sIntegerUnitSubgroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)
      (⟨r, hr.1⟩ : NonzeroRingElements A.R)).trans hr.2
  exact principalExterior_eq_of_generates A I _
    ⟨(parentGeneratorOrbit A Γ I r hr).out.property, hspan⟩

variable {A Γ}

/-- Identity of the original ideal is a left inverse on the genuine
finite row carrier, so its orbital row map is injective there. -/
theorem parent_rowMap_injective_of_originalIdeal
    (rows : Finset (HeckeGeneral.Analysis.NonzeroIdeal K))
    (rowMap : HeckeGeneral.Analysis.NonzeroIdeal K → Q)
    (hideal : ∀ u ∈ rows,
      (ProbeOrbitNormSum.principalExterior A (rowMap u).out).val = u.val) :
    Set.InjOn rowMap (rows : Set (HeckeGeneral.Analysis.NonzeroIdeal K)) := by
  intro u hu v hv huv
  apply Subtype.ext
  calc
    u.val = (ProbeOrbitNormSum.principalExterior A (rowMap u).out).val := (hideal u hu).symm
    _ = (ProbeOrbitNormSum.principalExterior A (rowMap v).out).val := by rw [huv]
    _ = v.val := hideal v hv

/-- Every actual orbital image has at most one original ideal row.
No bound on the full finite parent carrier is supplied. -/
theorem parent_rowMap_fibres_le_one_of_originalIdeal
    (rows : Finset (HeckeGeneral.Analysis.NonzeroIdeal K))
    (rowMap : HeckeGeneral.Analysis.NonzeroIdeal K → Q)
    (hideal : ∀ u ∈ rows,
      (ProbeOrbitNormSum.principalExterior A (rowMap u).out).val = u.val)
    (q : Q) : (rows.filter (fun u => rowMap u = q)).card ≤ 1 := by
  apply Finset.card_le_one_iff.mpr
  intro u v hu hv
  obtain ⟨hu, hqu⟩ := Finset.mem_filter.mp hu
  obtain ⟨hv, hqv⟩ := Finset.mem_filter.mp hv
  exact parent_rowMap_injective_of_originalIdeal rows rowMap hideal hu hv (hqu.trans hqv.symm)

/-- An equivalent raw interface uses the original exterior ideal and
the principal-span identity of the actual representative. -/
theorem parent_rowMap_fibres_le_one_of_generates
    (rows : Finset (HeckeGeneral.Analysis.NonzeroIdeal K))
    (rowMap : HeckeGeneral.Analysis.NonzeroIdeal K → Q)
    (original : HeckeGeneral.Analysis.NonzeroIdeal K → A.Exterior)
    (horiginal : ∀ u ∈ rows, (original u).val = u.val)
    (hgenerates : ∀ u ∈ rows, A.Generates (original u) (rowMap u).out.val)
    (q : Q) : (rows.filter (fun u => rowMap u = q)).card ≤ 1 := by
  apply parent_rowMap_fibres_le_one_of_originalIdeal rows rowMap _ q
  intro u hu
  have he := principalExterior_eq_of_generates A (original u) (rowMap u).out.val
    (hgenerates u hu)
  exact (congrArg Subtype.val he).trans (horiginal u hu)

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {htrace : A.ContainsTraceBadPlaces}

/-- A default for initial source construction, using exactly the
context's already selected allowed generator. -/
def parentAllowedOrbit (C : A.GeneralArithmeticContext σ η htrace)
    (Γ : Subgroup A.U) (I : A.Exterior) :
    SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ :=
  parentGeneratorOrbit A Γ I (engineAllowedGenerator C I) (engineAllowedGenerator_generates C I)

theorem parentAllowedOrbit_originalIdeal (C : A.GeneralArithmeticContext σ η htrace)
    (Γ : Subgroup A.U) (I : A.Exterior) :
    ProbeOrbitNormSum.principalExterior A (parentAllowedOrbit C Γ I).out = I :=
  parentGeneratorOrbit_originalIdeal A Γ I _ (engineAllowedGenerator_generates C I)

/-- The map is total on nonzero ideals.  Its active rows use their
actual exterior ideal and the existing allowed generator. -/
def defaultParentRowMap (C : A.GeneralArithmeticContext σ η htrace)
    (Γ : Subgroup A.U) (u : HeckeGeneral.Analysis.NonzeroIdeal K) :
    SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ :=
  if h : u.val ⊔ A.cS = ⊤ then
    parentAllowedOrbit C Γ ⟨u.val, mem_nonZeroDivisors_iff_ne_zero.mp u.property, h⟩
  else Quotient.mk _ ⟨1, one_ne_zero⟩

theorem defaultParentRowMap_originalIdeal (C : A.GeneralArithmeticContext σ η htrace)
    (Γ : Subgroup A.U) (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hu : u.val ⊔ A.cS = ⊤) :
    (ProbeOrbitNormSum.principalExterior A (defaultParentRowMap C Γ u).out).val = u.val := by
  simp only [defaultParentRowMap, dif_pos hu]
  exact congrArg (fun I : A.Exterior => I.val)
    (parentAllowedOrbit_originalIdeal C Γ
      ⟨u.val, mem_nonZeroDivisors_iff_ne_zero.mp u.property, hu⟩)

theorem defaultParentRowMap_fibres_le_one (C : A.GeneralArithmeticContext σ η htrace)
    (Γ : Subgroup A.U) (rows : Finset (HeckeGeneral.Analysis.NonzeroIdeal K))
    (hexterior : ∀ u ∈ rows, u.val ⊔ A.cS = ⊤)
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) :
    (rows.filter (fun u => defaultParentRowMap C Γ u = q)).card ≤ 1 :=
  parent_rowMap_fibres_le_one_of_originalIdeal rows (defaultParentRowMap C Γ)
    (fun u hu => defaultParentRowMap_originalIdeal C Γ u (hexterior u hu)) q

variable {ω ψ : HeckeCharacter K} {d : MomentData K ω ψ} {a : RealParameters}
variable {Z t Y₁ Y₂ : ℝ}

namespace ParentRawAtoms

variable (raw : ParentRawAtoms (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) d a Z t Y₁ Y₂)

theorem rowMap_injective_of_originalIdeal
    (hideal : ∀ u ∈ pairedRows d a Z,
      (ProbeOrbitNormSum.principalExterior A (raw.rowMap u).out).val = u.val) :
    Set.InjOn raw.rowMap (pairedRows d a Z : Set (HeckeGeneral.Analysis.NonzeroIdeal K)) :=
  parent_rowMap_injective_of_originalIdeal (pairedRows d a Z) raw.rowMap hideal

theorem rowMap_fibres_le_one_of_originalIdeal
    (hideal : ∀ u ∈ pairedRows d a Z,
      (ProbeOrbitNormSum.principalExterior A (raw.rowMap u).out).val = u.val)
    (q : Q) : ((pairedRows d a Z).filter (fun u => raw.rowMap u = q)).card ≤ 1 :=
  parent_rowMap_fibres_le_one_of_originalIdeal (pairedRows d a Z) raw.rowMap hideal q

end ParentRawAtoms

variable [Γ.FiniteIndex]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]

namespace ParentRectangleProfiles

variable {raw : ParentRawAtoms (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) d a Z t Y₁ Y₂}
variable {finiteTest : ((v : (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) →
  v.val.adicCompletion K) → ℂ}
variable {radius : {r : ℝ // 0 < r}} {weight : (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) → ℝ}
variable (profiles : ParentRectangleProfiles raw finiteTest radius weight)

/-- The original rectangle profiles produce an orbital source with
parent fibre `1`, retaining the supplied map and every original phase.
The fibre field is discharged from the single-row ideal identities. -/
def toRawOrbitalInput_of_originalIdeal
    (hTest : Continuous finiteTest) (hTestcs : HasCompactSupport finiteTest)
    (centered : Bool) (template : raw.Column → raw.Column → ParentPeriodicPair K A.Sf Γ)
    (mask : Finset (HeightOneSpectrum A.R))
    (weight_nonneg : ∀ q, 0 ≤ weight q)
    (row_weight : ∀ u ∈ pairedRows d a Z, 1 ≤ weight (raw.rowMap u))
    (row_mask : ∀ u ∈ pairedRows d a Z,
      sIntegerOrbitAvoidanceMask K _ Γ mask (raw.rowMap u) = 1)
    (hideal : ∀ u ∈ pairedRows d a Z,
      (ProbeOrbitNormSum.principalExterior A (raw.rowMap u).out).val = u.val)
    (periodic : ∀ i ∈ raw.columns, ∀ j ∈ raw.columns, ∀ q,
      (template i j).orbitWeight q = raw.phase q i * star (raw.phase q j)) :
    ParentRawOrbitalInput A.Sf Γ centered raw (profiles.pairs centered template)
      finiteTest radius mask 1 :=
  profiles.toRawOrbitalInput hTest hTestcs centered template mask 1
    weight_nonneg row_weight row_mask (raw.rowMap_fibres_le_one_of_originalIdeal hideal) periodic

end ParentRectangleProfiles
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.parent_rowMap_fibres_le_one_of_originalIdeal
#print axioms HeckeSkeleton.Moments.EngineStep.parent_rowMap_fibres_le_one_of_generates
#print axioms HeckeSkeleton.Moments.EngineStep.defaultParentRowMap_fibres_le_one
#print axioms HeckeSkeleton.Moments.EngineStep.ParentRectangleProfiles.toRawOrbitalInput_of_originalIdeal
