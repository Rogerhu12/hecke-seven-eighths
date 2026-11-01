import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondAllocatedSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocatedCapacityProvider
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondRowPartition
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondBranchPartition
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FiniteThetaAction

/-!
# One arithmetic exceptional partition for both actual child sides

The original theta family is retained as a finite set. A subgroup of
actual corrections acts on that set, and the individual inducing-character
ratios belong to this correction subgroup. Membership is then proved to
agree for both sides without assuming theta itself is a subgroup.
The smooth phases stay in profiles.

Raw arithmetic/profile calibration is made on all rows.  Only after this
one arithmetic partition do we construct the actual nonexceptional
calibrations needed by clipping and capacity repair.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {H V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ω ψ : HeckeCharacter F} {k : ℕ}

/-- The primitive finite-character input owned by MOM_BASE.  It fixes
the same original theta family and a pointwise character ratio; no row
count, polynomial estimate or exceptional energy appears here. -/
structure PairedFiniteCharacters (theta : Finset (HeckeCharacter F)) (H : Type*) where
  subgroup : Subgroup (HeckeCharacter F)
  action : ∀ χ ∈ subgroup, ActualThetaAction theta χ
  left : H → HeckeCharacter F
  right : H → HeckeCharacter F
  ratio_mem : ∀ h, left h / right h ∈ subgroup

namespace PairedFiniteCharacters

variable {theta : Finset (HeckeCharacter F)}

/-- Older genuine subgroup data still give the weaker action interface. -/
def ofSubgroup (Θ : Subgroup (HeckeCharacter F))
    (hmem : ∀ χ, χ ∈ theta ↔ χ ∈ Θ)
    (left right : H → HeckeCharacter F)
    (hratio : ∀ h, left h / right h ∈ Θ) : PairedFiniteCharacters theta H where
  subgroup := Θ
  action χ hχ := ActualThetaAction.of_subgroup Θ hmem χ hχ
  left := left
  right := right
  ratio_mem := hratio

variable (T : PairedFiniteCharacters theta H)

def exceptional (h : H) : Prop := T.left h ∈ theta

theorem right_exceptional (h : H) : T.right h ∈ theta ↔ T.exceptional h := by
  unfold exceptional
  exact (ActualThetaAction.mem_iff_of_ratio (T.action _ (T.ratio_mem h))).symm

theorem nonexceptional_left (h : H) (hh : ¬ T.exceptional h) : T.left h ∉ theta := hh

theorem nonexceptional_right (h : H) (hh : ¬ T.exceptional h) : T.right h ∉ theta := by
  intro hr
  exact hh ((T.right_exceptional h).mp hr)

/-- Original-row predicates are pulled back to the actual nonzero
correlation rows without making a second character choice. -/
def comap {J : Type*} (f : J → H) : PairedFiniteCharacters theta J where
  subgroup := T.subgroup
  action := T.action
  left := T.left ∘ f
  right := T.right ∘ f
  ratio_mem h := T.ratio_mem (f h)

theorem exceptional_iff_of_left_ratio (h : H) (χ : HeckeCharacter F)
    (hχ : χ / T.left h ∈ T.subgroup) : χ ∈ theta ↔ T.exceptional h := by
  unfold exceptional
  exact ActualThetaAction.mem_iff_of_ratio (T.action _ hχ)

theorem exceptional_iff_of_right_ratio (h : H) (χ : HeckeCharacter F)
    (hχ : χ / T.right h ∈ T.subgroup) : χ ∈ theta ↔ T.exceptional h := by
  calc
    χ ∈ theta ↔ T.right h ∈ theta :=
      ActualThetaAction.mem_iff_of_ratio (T.action _ hχ)
    _ ↔ T.exceptional h := T.right_exceptional h

/-- The same predicate works when either side has no live slots.
The ordinary zero-slot exclusion follows from the original principal
character's membership in theta, rather than being inferred from width. -/
theorem actual_nonexceptional
    (left right : V → MomentData F ω ψ) (a b : RealParameters)
    (leftRow rightRow : H → HeckeGeneral.Analysis.NonzeroIdeal F)
    (left_theta : ∀ ξ, (left ξ).theta = theta)
    (right_theta : ∀ ξ, (right ξ).theta = theta)
    (left_character : ∀ ξ h, (left ξ).rowCharacter (leftRow h) = T.left h)
    (right_character : ∀ ξ h, (right ξ).rowCharacter (rightRow h) = T.right h)
    (left_principal : ∀ ξ u,
      (left ξ).plainBackground * (left ξ).rowCharacter u = 1 →
        (left ξ).rowCharacter u ∈ (left ξ).theta)
    (right_principal : ∀ ξ u,
      (right ξ).plainBackground * (right ξ).rowCharacter u = 1 →
        (right ξ).rowCharacter u ∈ (right ξ).theta)
    (ξ : V) (h : H) (hh : ¬ T.exceptional h) :
    (if a.z = 0 then (left ξ).plainBackground * (left ξ).rowCharacter (leftRow h) ≠ 1
      else (left ξ).rowCharacter (leftRow h) ∉ (left ξ).theta) ∧
    (if b.z = 0 then (right ξ).plainBackground * (right ξ).rowCharacter (rightRow h) ≠ 1
      else (right ξ).rowCharacter (rightRow h) ∉ (right ξ).theta) := by
  have hl : (left ξ).rowCharacter (leftRow h) ∉ (left ξ).theta := by
    rw [left_theta ξ, left_character ξ h]
    exact T.nonexceptional_left h hh
  have hr : (right ξ).rowCharacter (rightRow h) ∉ (right ξ).theta := by
    rw [right_theta ξ, right_character ξ h]
    exact T.nonexceptional_right h hh
  constructor
  · split_ifs
    · exact fun he => hl (left_principal ξ _ he)
    · exact hl
  · split_ifs
    · exact fun he => hr (right_principal ξ _ he)
    · exact hr

end PairedFiniteCharacters

namespace ActualAllocatedSource

def restrictRows (s : ActualAllocatedSource A V H k) (p : H → Prop) :
    ActualAllocatedSource A V H k := { s with rows := s.rows.filter p }

theorem restrictRows_negativeSide (s : ActualAllocatedSource A V H k) (p : H → Prop) :
    (s.restrictRows p).negativeSide = s.negativeSide.restrictRows p := rfl

theorem restrictRows_energy (s : ActualAllocatedSource A V H k) (p : H → Prop) (ξ : V) :
    (s.restrictRows p).energy (σ := σ) ξ =
      jointColumnEnergy (s.rows.filter p) s.allocation.columns s.weight
        (fun h => rawSourceCoefficient (σ := σ) (s.characters h)
          (s.extractedFactor h) (s.row h).element s.scale₁ s.scale₂ s.base s.length
          (s.leftWeight h) (s.rightWeight h) (s.slotWeight h))
        (fun h => rawSourceLocation (s.leftLocation h) (s.rightLocation h) (s.slotLocation h)) ξ := rfl

theorem energy_partition (s : ActualAllocatedSource A V H k) (p : H → Prop) (ξ : V) :
    s.energy (σ := σ) ξ =
      (s.restrictRows p).energy (σ := σ) ξ +
        (s.restrictRows (fun h => ¬ p h)).energy (σ := σ) ξ := by
  simp only [energy, restrictRows, jointColumnEnergy, Finset.sum_filter,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hp : p h <;> simp [hp]

/-- Calibration of the original profiles and arithmetic on every row,
before the common exceptional predicate is imposed. -/
structure FullCalibration (s : ActualAllocatedSource A V H k) (ω ψ : HeckeCharacter F) where
  data : V → MomentData F ω ψ
  parameters : RealParameters
  height : V → ℝ
  count : ∀ ξ, (data ξ).geometry.slotCount = s.allocation.keep.card
  lengths : ∀ ξ i, ((data ξ).geometry.slots i).length = s.childLength (Fin.cast (count ξ) i)
  left_scale : s.base ^ parameters.n₁ =
    s.scale₁ / HeckeGeneral.Analysis.idealNorm F (s.allocation.plainDivisor 0)
  right_scale : s.base ^ parameters.n₂ =
    s.scale₂ / HeckeGeneral.Analysis.idealNorm F (s.allocation.plainDivisor (Fin.succ 0))
  slot_sum : parameters.z = ∑ i, s.childLength i
  dictionary : ∀ ξ h, ((s.characters h).restrictSlots s.allocation.keep).Calibration
    (σ := σ) (data ξ) (count ξ) (s.row h).momentIdeal
      (s.extractedFactor h) (s.row h).element
  left_support : ∀ ξ, ∀ h ∈ s.rows,
    EffectivePlainSupport (data ξ) (data ξ).plainTest₁ (s.row h).momentIdeal
      (s.base ^ parameters.n₁) (height ξ) s.allocation.childPlain₁
  right_support : ∀ ξ, ∀ h ∈ s.rows,
    EffectivePlainSupport (data ξ) (data ξ).plainTest₂ (s.row h).momentIdeal
      (s.base ^ parameters.n₂) (height ξ) s.allocation.childPlain₂
  slot_support : ∀ ξ, ∀ h ∈ s.rows, ∀ i,
    EffectivePrimeSupport (data ξ) i (s.row h).momentIdeal s.base (height ξ)
      (s.allocation.childSlots (Fin.cast (count ξ) i))
  left_profile : ∀ ξ, ∀ h ∈ s.rows, ∀ I ∈ s.allocation.childPlain₁,
    s.leftWeight h (s.allocation.plainDivisor 0 * I) *
      jointPhase ξ (s.leftLocation h (s.allocation.plainDivisor 0 * I)) =
      (data ξ).plainTest₁.profile (s.row h).momentIdeal (height ξ)
        (HeckeGeneral.Analysis.idealNorm F I / s.base ^ parameters.n₁)
  right_profile : ∀ ξ, ∀ h ∈ s.rows, ∀ I ∈ s.allocation.childPlain₂,
    s.rightWeight h (s.allocation.plainDivisor (Fin.succ 0) * I) *
      jointPhase ξ (s.rightLocation h (s.allocation.plainDivisor (Fin.succ 0) * I)) =
      (data ξ).plainTest₂.profile (s.row h).momentIdeal (height ξ)
        (HeckeGeneral.Analysis.idealNorm F I / s.base ^ parameters.n₂)
  slot_profile : ∀ ξ, ∀ h ∈ s.rows, ∀ i,
    ∀ p ∈ s.allocation.childSlots (Fin.cast (count ξ) i),
      s.slotWeight h (SlotRestriction.index s.allocation.keep (Fin.cast (count ξ) i)) p *
        jointPhase ξ
          (s.slotLocation h (SlotRestriction.index s.allocation.keep (Fin.cast (count ξ) i)) p) =
          ((data ξ).geometry.slots i).profile (height ξ)
            ((Ideal.absNorm p.asIdeal : ℝ) / s.base ^ ((data ξ).geometry.slots i).length)
  allowed : ∀ ξ, ∀ h ∈ s.rows, (data ξ).allowedRow (s.row h).momentIdeal
  cutoff : ∀ h ∈ s.rows,
    A.exteriorNorm (s.originalIdeal h) ≤ s.normFactor h * s.base ^ (parameters.m + parameters.q)
  rowBound : ℝ
  rowBound_nonneg : 0 ≤ rowBound
  row_bound : ∀ h ∈ s.rows, ‖s.weight h‖ ≤ rowBound
  scalarBound : ℝ
  scalarBound_nonneg : 0 ≤ scalarBound
  scalar_bound : ∀ h ∈ s.rows, ‖s.frozenScalar (σ := σ) h‖ ^ 2 ≤ scalarBound
  fiberBound : ℕ
  fibers : ∀ I : HeckeGeneral.Analysis.NonzeroIdeal F,
    (s.rows.filter (fun h => (s.row h).momentIdeal = I)).card ≤ fiberBound
  principal_in_theta : ∀ ξ, ∀ u : HeckeGeneral.Analysis.NonzeroIdeal F,
    (data ξ).plainBackground * (data ξ).rowCharacter u = 1 →
      (data ξ).rowCharacter u ∈ (data ξ).theta
  slot_in_theta : ∀ ξ i, (data ξ).slotCoefficient i ∈ (data ξ).theta

namespace FullCalibration

variable {s : ActualAllocatedSource A V H k} (D : FullCalibration s (σ := σ) ω ψ)

/-- Restrict only the original row carrier.  Its fiber bound follows
from the original fiber by inclusion; no new aggregate bound is used. -/
def restrict (p : H → Prop)
    (hnonexceptional : ∀ ξ h, h ∈ s.rows → p h →
      if D.parameters.z = 0 then
        (D.data ξ).plainBackground * (D.data ξ).rowCharacter (s.row h).momentIdeal ≠ 1
      else (D.data ξ).rowCharacter (s.row h).momentIdeal ∉ (D.data ξ).theta) :
    (s.restrictRows p).Calibration (σ := σ) ω ψ where
  data := D.data
  parameters := D.parameters
  height := D.height
  count := D.count
  lengths := D.lengths
  left_scale := D.left_scale
  right_scale := D.right_scale
  slot_sum := D.slot_sum
  dictionary := D.dictionary
  left_support ξ h hh := D.left_support ξ h (Finset.mem_filter.mp hh).1
  right_support ξ h hh := D.right_support ξ h (Finset.mem_filter.mp hh).1
  slot_support ξ h hh := D.slot_support ξ h (Finset.mem_filter.mp hh).1
  left_profile ξ h hh := D.left_profile ξ h (Finset.mem_filter.mp hh).1
  right_profile ξ h hh := D.right_profile ξ h (Finset.mem_filter.mp hh).1
  slot_profile ξ h hh := D.slot_profile ξ h (Finset.mem_filter.mp hh).1
  allowed ξ h hh := D.allowed ξ h (Finset.mem_filter.mp hh).1
  cutoff h hh := D.cutoff h (Finset.mem_filter.mp hh).1
  nonexceptional ξ h hh :=
    hnonexceptional ξ h (Finset.mem_filter.mp hh).1 (Finset.mem_filter.mp hh).2
  rowBound := D.rowBound
  rowBound_nonneg := D.rowBound_nonneg
  row_bound h hh := D.row_bound h (Finset.mem_filter.mp hh).1
  scalarBound := D.scalarBound
  scalarBound_nonneg := D.scalarBound_nonneg
  scalar_bound h hh := D.scalar_bound h (Finset.mem_filter.mp hh).1
  fiberBound := D.fiberBound
  fibers I := by
    apply le_trans (Finset.card_le_card (show
      ((s.rows.filter p).filter (fun h => (s.row h).momentIdeal = I)) ⊆
        s.rows.filter (fun h => (s.row h).momentIdeal = I) from ?_)) (D.fibers I)
    intro h hh
    have hm := Finset.mem_filter.mp hh
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hm.1).1, hm.2⟩
  principal_in_theta := D.principal_in_theta
  slot_in_theta := D.slot_in_theta

end FullCalibration

end ActualAllocatedSource

namespace PairedFiniteCharacters

variable {theta : Finset (HeckeCharacter F)} {l : ℕ}
variable (T : PairedFiniteCharacters theta H)
variable {sL : ActualAllocatedSource A V H k} {sR : ActualAllocatedSource A V H l}

/-- The two actual nonexceptional child calibrations are constructed
from the original full-row dictionaries and one correction-action/ratio input.
Their row predicate is identical and precedes every Fourier parameter. -/
def nonexceptionalCalibrations
    (DL : ActualAllocatedSource.FullCalibration sL (σ := σ) ω ψ)
    (DR : ActualAllocatedSource.FullCalibration sR (σ := σ) ω ψ)
    (left_theta : ∀ ξ, (DL.data ξ).theta = theta)
    (right_theta : ∀ ξ, (DR.data ξ).theta = theta)
    (left_character : ∀ ξ h, (DL.data ξ).rowCharacter (sL.row h).momentIdeal = T.left h)
    (right_character : ∀ ξ h, (DR.data ξ).rowCharacter (sR.row h).momentIdeal = T.right h) :
    (sL.restrictRows (fun h => ¬ T.exceptional h)).Calibration (σ := σ) ω ψ ×
      (sR.restrictRows (fun h => ¬ T.exceptional h)).Calibration (σ := σ) ω ψ :=
  ⟨DL.restrict (fun h => ¬ T.exceptional h) (fun ξ h _ hh =>
    (T.actual_nonexceptional DL.data DR.data DL.parameters DR.parameters
      (fun h => (sL.row h).momentIdeal) (fun h => (sR.row h).momentIdeal)
      left_theta right_theta left_character right_character
      DL.principal_in_theta DR.principal_in_theta ξ h hh).1),
   DR.restrict (fun h => ¬ T.exceptional h) (fun ξ h _ hh =>
    (T.actual_nonexceptional DL.data DR.data DL.parameters DR.parameters
      (fun h => (sL.row h).momentIdeal) (fun h => (sR.row h).momentIdeal)
      left_theta right_theta left_character right_character
      DL.principal_in_theta DR.principal_in_theta ξ h hh).2)⟩

/-- Finite phase characters and allocation factors may change the
inducing character. Membership of their ratios in the correction
subgroup proves that every such label uses the same original partition.
The inputs are character identities, not selected row subsets. -/
def nonexceptionalCalibrationsOfFiniteTwists
    (DL : ActualAllocatedSource.FullCalibration sL (σ := σ) ω ψ)
    (DR : ActualAllocatedSource.FullCalibration sR (σ := σ) ω ψ)
    (left_theta : ∀ ξ, (DL.data ξ).theta = theta)
    (right_theta : ∀ ξ, (DR.data ξ).theta = theta)
    (left_ratio : ∀ ξ h,
      (DL.data ξ).rowCharacter (sL.row h).momentIdeal / T.left h ∈ T.subgroup)
    (right_ratio : ∀ ξ h,
      (DR.data ξ).rowCharacter (sR.row h).momentIdeal / T.right h ∈ T.subgroup) :
    (sL.restrictRows (fun h => ¬ T.exceptional h)).Calibration (σ := σ) ω ψ ×
      (sR.restrictRows (fun h => ¬ T.exceptional h)).Calibration (σ := σ) ω ψ := by
  refine ⟨DL.restrict (fun h => ¬ T.exceptional h) ?_,
    DR.restrict (fun h => ¬ T.exceptional h) ?_⟩
  · intro ξ h _ hh
    have hn : (DL.data ξ).rowCharacter (sL.row h).momentIdeal ∉ (DL.data ξ).theta := by
      rw [left_theta ξ]
      intro hm
      exact hh ((T.exceptional_iff_of_left_ratio h _ (left_ratio ξ h)).mp hm)
    split_ifs
    · intro hp
      exact hn (DL.principal_in_theta ξ _ hp)
    · exact hn
  · intro ξ h _ hh
    have hn : (DR.data ξ).rowCharacter (sR.row h).momentIdeal ∉ (DR.data ξ).theta := by
      rw [right_theta ξ]
      intro hm
      exact hh ((T.exceptional_iff_of_right_ratio h _ (right_ratio ξ h)).mp hm)
    split_ifs
    · intro hp
      exact hn (DR.principal_in_theta ξ _ hp)
    · exact hn

end PairedFiniteCharacters

variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace ActualSecondCorrelationRows

theorem restrictRows_correlation (R : ActualSecondCorrelationRows A σ H ι)
    (p : H → Prop) (h : H) : (R.restrictRows p).correlation h = R.correlation h := rfl

theorem restrictRows_live (R : ActualSecondCorrelationRows A σ H ι) (p : H → Prop) :
    (R.restrictRows p).live = R.live.filter p := by
  ext h
  simp only [live, restrictRows, Finset.mem_filter, restrictRows_correlation]
  tauto

theorem restrictRows_factor (R : ActualSecondCorrelationRows A σ H ι)
    (p : H → Prop) (C : A.GeneralArithmeticContext σ η hS) (h : H) :
    (R.restrictRows p).factor C h = R.factor C h := rfl

theorem restrictRows_normFactor (R : ActualSecondCorrelationRows A σ H ι)
    (p : H → Prop) (C : A.GeneralArithmeticContext σ η hS) (h : H) :
    (R.restrictRows p).normFactor C h = R.normFactor C h := rfl

/-- Both sides use the same inclusion of retained true correlation rows. -/
def liveInclusion (R : ActualSecondCorrelationRows A σ H ι) (p : H → Prop)
    (h : (R.restrictRows p).live) : R.live :=
  ⟨h.val, (Finset.mem_filter.mp (by
    simpa only [R.restrictRows_live p] using h.property)).1⟩

theorem liveInclusion_injective (R : ActualSecondCorrelationRows A σ H ι) (p : H → Prop) :
    Function.Injective (R.liveInclusion p) := by
  intro h h' he
  exact Subtype.ext (congrArg Subtype.val he)

/-- Restricting rows does not choose a different residual generator.
The existence proof changes only in propositionally irrelevant proofs. -/
theorem restrictRows_extractedRow (R : ActualSecondCorrelationRows A σ H ι)
    (p : H → Prop) (C : A.GeneralArithmeticContext σ η hS)
    (h : (R.restrictRows p).live) :
    (R.restrictRows p).extractedRow C h = R.extractedRow C (R.liveInclusion p h) := rfl

/-- Taking the nonzero-correlation subtype commutes with restriction
by the original arithmetic row predicate. -/
theorem sum_restrictRows_live (R : ActualSecondCorrelationRows A σ H ι)
    (p : H → Prop) {M : Type*} [AddCommMonoid M] (f : R.live → M) :
    (∑ h : (R.restrictRows p).live, f (R.liveInclusion p h)) =
      ∑ h ∈ (Finset.univ : Finset R.live).filter (fun h => p h.val), f h := by
  refine Finset.sum_bij (fun h _ => R.liveInclusion p h) ?_ ?_ ?_ ?_
  · intro h _
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hm : h.val ∈ R.live.filter p := by
      simpa only [R.restrictRows_live p] using h.property
    exact (Finset.mem_filter.mp hm).2
  · intro h _ h' _ he
    exact R.liveInclusion_injective p he
  · intro h hh
    have hm : h.val ∈ (R.restrictRows p).live := by
      rw [R.restrictRows_live p]
      exact Finset.mem_filter.mpr ⟨h.property, (Finset.mem_filter.mp hh).2⟩
    exact ⟨⟨h.val, hm⟩, Finset.mem_univ _, Subtype.ext rfl⟩
  · intro h _
    rfl

variable {Ray : Type*} [CommGroup Ray]

/-- Restrict before the row Cauchy inequality or restrict the actual
allocated source afterwards: the same nonzero rows, generators and
complete coefficients give exactly the same left energy. -/
theorem source_restrictRows_energy (R : ActualSecondCorrelationRows A σ H ι)
    (p : H → Prop) (C : A.GeneralArithmeticContext σ η hS)
    (B : ActualColumnAllocation F k) (T : FixedChildCharacters F k)
    (phase : Ray →* Circle)
    (D : SecondCoefficientTermDictionary T phase B.plain₁ B.plain₂ B.slots)
    (hbase : 1 < D.base) (hlength : ∀ i, 0 < D.length i)
    (x₁ x₂ : H → HeckeGeneral.Analysis.NonzeroIdeal F → V)
    (x : H → Fin k → HeightOneSpectrum (𝓞 F) → V) (ξ : V) :
    ((R.restrictRows p).source C B T phase D hbase hlength x₁ x₂ x).energy (σ := σ) ξ =
      ((R.source C B T phase D hbase hlength x₁ x₂ x).restrictRows
        (fun h => p h.val)).energy (σ := σ) ξ := by
  let f : R.live → ℝ := fun h => ‖R.weight h.val * R.correlation h.val‖ *
    ‖jointFourierColumn B.columns
      (rawSourceCoefficient (σ := σ) T (R.factor C h.val) (R.extractedRow C h).element
        D.scale₁ D.scale₂ D.base D.length D.leftWeight D.rightWeight D.slotWeight)
      (rawSourceLocation (x₁ h.val) (x₂ h.val) (x h.val)) ξ‖ ^ 2
  change (∑ h : (R.restrictRows p).live, f (R.liveInclusion p h)) =
    ∑ h ∈ (Finset.univ : Finset R.live).filter (fun h => p h.val), f h
  exact R.sum_restrictRows_live p f

/-- The same exact identity retains the negative source frequency and
all negated Fourier locations on the conjugated right side. -/
theorem negative_source_restrictRows_energy (R : ActualSecondCorrelationRows A σ H ι)
    (p : H → Prop) (C : A.GeneralArithmeticContext σ η hS)
    (B : ActualColumnAllocation F k) (T : FixedChildCharacters F k)
    (phase : Ray →* Circle)
    (D : SecondCoefficientTermDictionary T phase B.plain₁ B.plain₂ B.slots)
    (hbase : 1 < D.base) (hlength : ∀ i, 0 < D.length i)
    (x₁ x₂ : H → HeckeGeneral.Analysis.NonzeroIdeal F → V)
    (x : H → Fin k → HeightOneSpectrum (𝓞 F) → V) (ξ : V) :
    ((R.restrictRows p).source C B T phase D hbase hlength x₁ x₂ x).negativeSide.energy
      (σ := σ) ξ =
      ((R.source C B T phase D hbase hlength x₁ x₂ x).negativeSide.restrictRows
        (fun h => p h.val)).energy (σ := σ) ξ := by
  let f : R.live → ℝ := fun h => ‖R.weight h.val * R.correlation h.val‖ *
    ‖jointFourierColumn B.columns
      (rawSourceCoefficient (σ := σ) T (-R.factor C h.val) (R.extractedRow C h).element
        D.scale₁ D.scale₂ D.base D.length D.leftWeight D.rightWeight D.slotWeight)
      (rawSourceLocation (fun I => -x₁ h.val I) (fun I => -x₂ h.val I)
        (fun i q => -x h.val i q)) ξ‖ ^ 2
  change (∑ h : (R.restrictRows p).live, f (R.liveInclusion p h)) =
    ∑ h ∈ (Finset.univ : Finset R.live).filter (fun h => p h.val), f h
  exact R.sum_restrictRows_live p f

end ActualSecondCorrelationRows

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.PairedFiniteCharacters.actual_nonexceptional
#print axioms HeckeSkeleton.Moments.EngineStep.PairedFiniteCharacters.ofSubgroup
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.energy_partition
#print axioms HeckeSkeleton.Moments.EngineStep.PairedFiniteCharacters.nonexceptionalCalibrations
#print axioms HeckeSkeleton.Moments.EngineStep.PairedFiniteCharacters.nonexceptionalCalibrationsOfFiniteTwists
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondCorrelationRows.source_restrictRows_energy
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondCorrelationRows.negative_source_restrictRows_energy

