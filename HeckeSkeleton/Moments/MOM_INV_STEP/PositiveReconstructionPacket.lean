import HeckeSkeleton.Moments.MOM_INV_STEP.PositiveReconstruction

/-!
# Fixed-triple packets of the actual post-Cauchy positive source

The source here has an actual first extraction key and an independent
second overlap. It contains no historical residual columns. Its proved
injective tuple map preserves every finite source summand. Original
slice and overlap zeros force squarefree labels before the positive
label/row range is enlarged. Only the original finite scalar contraction
and the declared numbers of original mark slots are inputs.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.PositiveReconstructionPacket

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep FixedTripleFibers FixedTripleEnergy
open PositiveReconstruction
open scoped Classical BigOperators nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]
variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K)))}
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ
variable {Jo Jn : ℕ} {N : Finset (ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K))))} {X : ℝ}
variable {oldLists : Fin Jo → Finset (HeightOneSpectrum (𝓞 K))}
variable {newLists : Fin Jn → Finset (HeightOneSpectrum (𝓞 K))}
local notation "Src" => PositiveReconstruction.Source K S D Γ N X oldLists newLists
local notation "Tuple" => SecondTuple K Sector Jo Jn
local notation "transport" => ActualMaskReconstruction.sectorTransport K S D Γ

def tupleRange (T : Finset Src) : Finset Tuple := T.image Source.tuple

def sourceScalar (R : Src → Ideal (𝓞 K)) (a : Src → ℂ) (B : Src) : ℂ :=
  a B * B.retainedZero (R B)

def scalar (R : Src → Ideal (𝓞 K)) (a : Src → ℂ) : Tuple → ℂ :=
  Function.extend Source.tuple (sourceScalar R a) (fun _ => 0)

@[simp] theorem scalar_tuple (R : Src → Ideal (𝓞 K)) (a : Src → ℂ) (B : Src) :
    scalar R a B.tuple = sourceScalar R a B :=
  PositiveReconstruction.tuple_injective.extend_apply _ _ B

def liveTuples (T : Finset Src) (R : Src → Ideal (𝓞 K)) (a : Src → ℂ) : Finset Tuple :=
  originalSource (tupleRange T) oldLists newLists (fun t => scalar R a t ≠ 0)

theorem mem_liveTuples (T : Finset Src) (R : Src → Ideal (𝓞 K)) (a : Src → ℂ) (t : Tuple) :
    t ∈ liveTuples T R a ↔ ∃ B ∈ T, B.tuple = t ∧ sourceScalar R a B ≠ 0 := by
  simp only [liveTuples, originalSource, Finset.mem_filter]
  constructor
  · rintro ⟨ht, hslots⟩
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp ht
    exact ⟨B,hB,rfl, by simpa only [scalar_tuple] using hslots.2.2⟩
  · rintro ⟨B,hB,rfl,hlive⟩
    exact ⟨Finset.mem_image.mpr ⟨B,hB,rfl⟩, B.old_mem, B.new_mem,
      by simpa only [scalar_tuple] using hlive⟩

theorem liveTuples_eq_filter (T : Finset Src) (R : Src → Ideal (𝓞 K)) (a : Src → ℂ) :
    liveTuples T R a = (tupleRange T).filter (fun t => scalar R a t ≠ 0) := by
  ext t
  rw [mem_liveTuples, Finset.mem_filter]
  constructor
  · rintro ⟨B,hB,rfl,hlive⟩
    exact ⟨Finset.mem_image.mpr ⟨B,hB,rfl⟩, by simpa only [scalar_tuple] using hlive⟩
  · rintro ⟨ht,hlive⟩
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp ht
    exact ⟨B,hB,rfl, by simpa only [scalar_tuple] using hlive⟩

def childLabels (T : Finset Src) (R : Src → Ideal (𝓞 K)) (a : Src → ℂ) :
    Finset (Ideal (𝓞 K)) :=
  (liveTuples T R a).image fun t => (secondChild transport t).2.1

def childRows (T : Finset Src) (R : Src → Ideal (𝓞 K)) (a : Src → ℂ) :
    Finset (Ideal (𝓞 K) × Sector) :=
  (liveTuples T R a).image fun t => (secondChild transport t).2.2

theorem live_valid (T : Finset Src) (R : Src → Ideal (𝓞 K)) (a : Src → ℂ)
    (t : Tuple) (ht : t ∈ liveTuples T R a) :
    Valid transport t (secondChild transport t).1
      (secondChild transport t).2.1 (secondChild transport t).2.2 := by
  obtain ⟨B,hB,rfl,hlive⟩ := (mem_liveTuples T R a t).mp ht
  exact B.valid

theorem live_label_squarefree (T : Finset Src) (R : Src → Ideal (𝓞 K)) (a : Src → ℂ)
    (t : Tuple) (ht : t ∈ liveTuples T R a) :
    Squarefree (secondChild transport t).2.1 := by
  obtain ⟨B,hB,rfl,hlive⟩ := (mem_liveTuples T R a t).mp ht
  exact B.label_squarefree_of_retainedZero (R B) (mul_ne_zero_iff.mp hlive).2

theorem live_label_nonzero (T : Finset Src) (R : Src → Ideal (𝓞 K)) (a : Src → ℂ)
    (t : Tuple) (ht : t ∈ liveTuples T R a) : (secondChild transport t).2.1 ≠ 0 := by
  obtain ⟨B,hB,rfl,hlive⟩ := (mem_liveTuples T R a t).mp ht
  exact B.newLabel_ne_zero

theorem live_outer_nonzero (T : Finset Src) (R : Src → Ideal (𝓞 K)) (a : Src → ℂ)
    (t : Tuple) (ht : t ∈ liveTuples T R a) :
    t.outer.q0 ≠ 0 ∧ t.outer.quotient ≠ 0 ∧ t.outer.residual ≠ 0 := by
  obtain ⟨B,hB,rfl,hlive⟩ := (mem_liveTuples T R a t).mp ht
  exact B.outer_nonzero

/-- An actual arithmetic packet. Its structural validity, squarefree
labels, nonzero triple and genuine sector transport are all conclusions
of the source construction. The pointwise scalar bound is not an energy
or source-reconstruction assumption. -/
def packet (T : Finset Src) (R : Src → Ideal (𝓞 K)) (a : Src → ℂ)
    (ha : ∀ B ∈ T, ‖a B‖ ≤ 1) (slotCap : ℕ)
    (ho : Jo ≤ 2 * slotCap) (hn : Jn ≤ 2 * slotCap) :
    ReconstructionPacket (K := K) (Sector := Sector) transport slotCap Jo Jn where
  source := tupleRange T
  oldLists := oldLists
  newLists := newLists
  keep := fun t => scalar R a t ≠ 0
  labels := childLabels T R a
  rows := childRows T R a
  scalar := scalar R a
  valid := live_valid T R a
  label_squarefree := by
    intro f hf
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hf
    exact live_label_squarefree T R a t ht
  label_nonzero := by
    intro f hf
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hf
    exact live_label_nonzero T R a t ht
  outer_nonzero := by
    intro γ hγ
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hγ
    exact live_outer_nonzero T R a t ht
  child_mem := by
    intro t ht
    exact ⟨Finset.mem_image.mpr ⟨t,ht,rfl⟩, Finset.mem_image.mpr ⟨t,ht,rfl⟩⟩
  old_cap := ho
  new_cap := hn
  scalar_norm := by
    intro t ht
    obtain ⟨B,hB,rfl,hlive⟩ := (mem_liveTuples T R a t).mp ht
    rw [scalar_tuple, sourceScalar, norm_mul]
    exact mul_le_one₀ (ha B hB) (norm_nonneg _) (B.norm_retainedZero_le_one (R B))

theorem sum_tupleRange {A : Type*} [AddCommMonoid A] (T : Finset Src) (H : Tuple → A) :
    (∑ t ∈ tupleRange T, H t) = ∑ B ∈ T, H B.tuple := by
  exact Finset.sum_image (fun B hB A hA h => PositiveReconstruction.tuple_injective h)

/-- No source multiplicity is discarded: the actual positive source
has an injective reconstruction map, and only literal zero summands are
removed. This is the equality needed before applying the fiber bound. -/
theorem positive_sum_eq_live (T : Finset Src) (R : Src → Ideal (𝓞 K)) (a : Src → ℂ)
    (F : SecondChild K Sector → ℂ) :
    (∑ B ∈ T, ‖sourceScalar R a B‖ * ‖F (B.outer,B.newLabel,B.newRow)‖ ^ 2) =
      ∑ t ∈ liveTuples T R a, ‖scalar R a t‖ * ‖F (secondChild transport t)‖ ^ 2 := by
  rw [liveTuples_eq_filter, Finset.sum_filter]
  calc
    _ = ∑ t ∈ tupleRange T, ‖scalar R a t‖ * ‖F (secondChild transport t)‖ ^ 2 := by
      rw [sum_tupleRange]
      apply Finset.sum_congr rfl
      intro B hB
      rw [scalar_tuple, B.child_eq]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t ht
      by_cases hz : scalar R a t = 0 <;> simp [hz]

/-- The genuine fixed-triple fiber estimate now applies directly to
the actual post-Cauchy positive source, with the row and label weights
kept in their separate measures. -/
theorem source_energy_le_packet (T : Finset Src) (R : Src → Ideal (𝓞 K)) (a : Src → ℂ)
    (ha : ∀ B ∈ T, ‖a B‖ ≤ 1) (slotCap : ℕ)
    (ho : Jo ≤ 2 * slotCap) (hn : Jn ≤ 2 * slotCap)
    (F : SecondChild K Sector → ℂ) :
    (∑ B ∈ T, ‖sourceScalar R a B‖ * ‖F (B.outer,B.newLabel,B.newRow)‖ ^ 2) ≤
      ∑ γ ∈ (packet T R a ha slotCap ho hn).triples,
        tripleDivisorWeight slotCap γ * (packet T R a ha slotCap ho hn).energy F γ := by
  rw [positive_sum_eq_live T R a F]
  let P := packet T R a ha slotCap ho hn
  exact source_energy_projection transport P.source P.oldLists P.newLists P.keep P.valid
    P.labels P.rows P.label_nonzero P.outer_nonzero P.child_mem slotCap ho hn
    (fun t => ‖P.scalar t‖) P.scalar_norm F

theorem packet_signedValue_eq_source (T : Finset Src) (R : Src → Ideal (𝓞 K))
    (a : Src → ℂ) (ha : ∀ B ∈ T, ‖a B‖ ≤ 1) (slotCap : ℕ)
    (ho : Jo ≤ 2 * slotCap) (hn : Jn ≤ 2 * slotCap)
    (F G : SecondChild K Sector → ℂ) :
    (packet T R a ha slotCap ho hn).signedValue F G =
      ∑ B ∈ T, sourceScalar R a B * F (B.outer,B.newLabel,B.newRow) *
        star (G (B.outer,B.newLabel,B.newRow)) := by
  change (∑ t ∈ liveTuples T R a, scalar R a t * F (secondChild transport t) *
    star (G (secondChild transport t))) = _
  rw [liveTuples_eq_filter, Finset.sum_filter]
  calc
    _ = ∑ t ∈ tupleRange T, scalar R a t * F (secondChild transport t) *
        star (G (secondChild transport t)) := by
      apply Finset.sum_congr rfl
      intro t ht
      by_cases hz : scalar R a t = 0 <;> simp [hz]
    _ = _ := by
      rw [sum_tupleRange]
      apply Finset.sum_congr rfl
      intro B hB
      rw [scalar_tuple, B.child_eq]

end HeckeSkeleton.Moments.MOM_INV_STEP.PositiveReconstructionPacket

end
