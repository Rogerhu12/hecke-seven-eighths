import HeckeSkeleton.Moments.MOM_INV_STEP.PositiveLiteralChildren
import HeckeSkeleton.Moments.MOM_INV_STEP.PrimeChoiceSlots

/-!
# Original squared marks construct the positive reconstruction source

The arithmetic records contain the actual mask subsets and the fresh
common ideal, but no prime assignments. Each of the two squared marks
chooses its two independent original prime tuples. Their membership
conditions imply the reconstruction divisibilities. The combined finite
map is injective, retaining all mask, extraction and prime choices.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.PositiveAssignedSource

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep FixedTripleFibers FixedTripleEnergy
open PositiveReconstruction AssignedMarkSource FirstSourceDecomposition
open scoped Classical BigOperators nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]
variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K)))}
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ
variable {N : Finset (ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K))))} {X : ℝ} {Jo Jn : ℕ}

def noLists : Fin 0 → Finset (HeightOneSpectrum (𝓞 K)) := fun i => Fin.elim0 i

abbrev BareSource := PositiveReconstruction.Source K S D Γ N X
  (noLists (K := K)) (noLists (K := K))

def doubledLists {J : ℕ} (P : Fin J → Finset (HeightOneSpectrum (𝓞 K))) :
    Fin (J + J) → Finset (HeightOneSpectrum (𝓞 K)) := Fin.addCases P P

variable (oldLists : Fin Jo → Finset (HeightOneSpectrum (𝓞 K)))
variable (newLists : Fin Jn → Finset (HeightOneSpectrum (𝓞 K)))
local notation "Bare" => BareSource (K := K) (S := S) (D := D) (Γ := Γ) (N := N) (X := X)
local notation "Marked" => PositiveReconstruction.Source K S D Γ N X
  (doubledLists oldLists) (doubledLists newLists)

def forget (B : Marked) : Bare where
  b₁ := B.b₁
  b₂ := B.b₂
  extraction := B.extraction
  extraction_mem := B.extraction_mem
  quotient := B.quotient
  common := B.common
  common_mem := B.common_mem
  overlap := B.overlap
  overlap_mem := B.overlap_mem
  firstDivisor := B.firstDivisor
  first_mem := B.first_mem
  secondDivisor := B.secondDivisor
  second_mem := B.second_mem
  frequency := B.frequency
  oldAssigned := fun i => Fin.elim0 i
  newAssigned := fun i => Fin.elim0 i
  old_mem := fun i => Fin.elim0 i
  new_mem := fun i => Fin.elim0 i
  old_dvd := fun i => Fin.elim0 i
  new_dvd := fun i => Fin.elim0 i

def oldExtracted (B : Bare) (side : Bool) : Ideal (𝓞 K) :=
  FirstOverlapColumns.markBase K S B.refs.1 B.refs.2 B.b₁ B.b₂ side B.quotient

def newExtracted (B : Bare) : Ideal (𝓞 K) := B.common.val.val * B.overlap.val.val

/-- Original primes dividing b_side³ A_side C e divide the coarse
extracted support C rad(b₁b₂)e used in the exact reconstruction count. -/
theorem old_prime_dvd (B : Bare) (side : Bool) (p : HeightOneSpectrum (𝓞 K))
    (hp : p.asIdeal ∣ oldExtracted B side) :
    p.asIdeal ∣ B.firstCommon * (B.b₁.val.val * B.b₂.val.val).radical * B.quotient.val.val := by
  have hb : ∀ (b : Ext), b = B.b₁ ∨ b = B.b₂ →
      p.asIdeal ∣ b.val.val → p.asIdeal ∣ (B.b₁.val.val * B.b₂.val.val).radical := by
    intro b he hd
    have hd' : p.asIdeal ∣ B.b₁.val.val * B.b₂.val.val := by
      rcases he with rfl | rfl
      · exact dvd_mul_of_dvd_left hd _
      · exact dvd_mul_of_dvd_right hd _
    change p.asIdeal ∣ (B.b₁.val * B.b₂.val).val.radical
    rw [radical_eq_primeProduct]
    exact Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum (𝓞 K) => q.asIdeal)
      ((mem_primeSupport (B.b₁.val * B.b₂.val) p).mpr hd')
  have hrad : ∀ n : Ext, p.asIdeal ∣ A n.val B.b₁.val B.b₂.val →
      p.asIdeal ∣ (B.b₁.val.val * B.b₂.val.val).radical :=
    fun n hd => hd.trans (B.A_dvd_radical n)
  have hp' : p.asIdeal ∣
      (FirstSourceColumns.sourceIdeal K S B.b₁ B.b₂ side).val.val ^ 3 *
        (A (FirstSourceColumns.sourceIdeal K S B.refs.1 B.refs.2 side).val B.b₁.val B.b₂.val *
          B.firstCommon) * B.quotient.val.val := by
    change p.asIdeal ∣ _ *
      (FirstSourceColumns.extractedFactor K S B.refs.1 B.refs.2 B.b₁ B.b₂ side).val.val * _ at hp
    rw [FirstSourceColumns.extractedFactor_val K S D,
      CanonicalConductor.commonResidualIdeal_eq_C] at hp
    exact hp
  rcases p.prime.dvd_mul.mp hp' with hp' | he
  · rcases p.prime.dvd_mul.mp hp' with hp' | ha
    · have hr : p.asIdeal ∣ (B.b₁.val.val * B.b₂.val.val).radical := by
        apply hb (FirstSourceColumns.sourceIdeal K S B.b₁ B.b₂ side)
        · cases side <;> simp [FirstSourceColumns.sourceIdeal]
        · exact p.prime.dvd_of_dvd_pow hp'
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hr _) _
    · rcases p.prime.dvd_mul.mp ha with ha | hc
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (hrad _ ha) _) _
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hc _) _
  · exact dvd_mul_of_dvd_right he _

def choices (B : Bare) (side : Bool) :=
  pairedChoices oldLists (oldExtracted B side) ×ˢ pairedChoices newLists (newExtracted B)

def reconstruction (B : Bare) (side : Bool) (q : choices oldLists newLists B side) : Marked where
  b₁ := B.b₁
  b₂ := B.b₂
  extraction := B.extraction
  extraction_mem := B.extraction_mem
  quotient := B.quotient
  common := B.common
  common_mem := B.common_mem
  overlap := B.overlap
  overlap_mem := B.overlap_mem
  firstDivisor := B.firstDivisor
  first_mem := B.first_mem
  secondDivisor := B.secondDivisor
  second_mem := B.second_mem
  frequency := B.frequency
  oldAssigned := pairedAssignment q.val.1
  newAssigned := pairedAssignment q.val.2
  old_mem := fun i => (pairedAssignment_source oldLists (oldExtracted B side) q.val.1
    (Finset.mem_product.mp q.property).1 i).1
  new_mem := fun i => (pairedAssignment_source newLists (newExtracted B) q.val.2
    (Finset.mem_product.mp q.property).2 i).1
  old_dvd := fun i => old_prime_dvd B side _
    (pairedAssignment_source oldLists (oldExtracted B side) q.val.1
      (Finset.mem_product.mp q.property).1 i).2
  new_dvd := fun i => (pairedAssignment_source newLists (newExtracted B) q.val.2
    (Finset.mem_product.mp q.property).2 i).2

theorem forget_reconstruction (B : Bare) (side : Bool)
    (q : choices oldLists newLists B side) :
    forget oldLists newLists (reconstruction oldLists newLists B side q) = B := by
  apply PositiveReconstruction.Source.ext <;> try rfl
  · funext i
    exact Fin.elim0 i
  · funext i
    exact Fin.elim0 i

theorem reconstruction_injective (B : Bare) (side : Bool) :
    Function.Injective (reconstruction oldLists newLists B side) := by
  intro q r h
  apply Subtype.ext
  apply Prod.ext
  · exact pairedAssignment_injective (congrArg PositiveReconstruction.Source.oldAssigned h)
  · exact pairedAssignment_injective (congrArg PositiveReconstruction.Source.newAssigned h)

abbrev Expanded (T : Finset Bare) (side : Bool) :=
  Σ B : T, ↥(choices oldLists newLists B.val side)

def expandedReconstruction (T : Finset Bare) (side : Bool)
    (q : Expanded oldLists newLists T side) : Marked :=
  reconstruction oldLists newLists q.1.val side q.2

theorem expandedReconstruction_injective (T : Finset Bare) (side : Bool) :
    Function.Injective (expandedReconstruction oldLists newLists T side) := by
  intro a b h
  have hb : a.1 = b.1 := by
    apply Subtype.ext
    have hh := congrArg (forget oldLists newLists) h
    simpa only [expandedReconstruction, forget_reconstruction] using hh
  rcases a with ⟨a,qa⟩
  rcases b with ⟨b,qb⟩
  dsimp only at hb
  cases hb
  have hq : qa = qb := reconstruction_injective oldLists newLists a.val side h
  cases hq
  rfl

def source (T : Finset Bare) (side : Bool) : Finset Marked :=
  Finset.univ.image (expandedReconstruction oldLists newLists T side)

def choiceScalar (aold : Fin Jo → Ideal (𝓞 K) → ℂ)
    (anew : Fin Jn → Ideal (𝓞 K) → ℂ)
    (B : Bare) (side : Bool) (q : choices oldLists newLists B side) : ℂ :=
  pairedWeight aold q.val.1 * pairedWeight anew q.val.2

theorem choiceScalar_norm_le_one (aold : Fin Jo → Ideal (𝓞 K) → ℂ)
    (anew : Fin Jn → Ideal (𝓞 K) → ℂ)
    (ho : ∀ i, ∀ p ∈ oldLists i, ‖aold i p.asIdeal‖ ≤ 1)
    (hn : ∀ i, ∀ p ∈ newLists i, ‖anew i p.asIdeal‖ ≤ 1)
    (B : Bare) (side : Bool) (q : choices oldLists newLists B side) :
    ‖choiceScalar oldLists newLists aold anew B side q‖ ≤ 1 := by
  rw [choiceScalar, norm_mul]
  exact mul_le_one₀
    (pairedWeight_norm_le_one oldLists aold (oldExtracted B side) ho q.val.1
      (Finset.mem_product.mp q.property).1)
    (norm_nonneg _)
    (pairedWeight_norm_le_one newLists anew (newExtracted B) hn q.val.2
      (Finset.mem_product.mp q.property).2)

/-- The actual two assigned mark squares are expanded before taking a
norm. This retains their original signed coefficient products. -/
theorem actual_marks_expansion (aold : Fin Jo → Ideal (𝓞 K) → ℂ)
    (anew : Fin Jn → Ideal (𝓞 K) → ℂ) (B : Bare) (side : Bool) :
    ((‖divisorMark Finset.univ (fun i => (oldLists i).image HeightOneSpectrum.asIdeal)
      aold (oldExtracted B side)‖ ^ 2 : ℝ) : ℂ) *
    ((‖divisorMark Finset.univ (fun i => (newLists i).image HeightOneSpectrum.asIdeal)
      anew (newExtracted B)‖ ^ 2 : ℝ) : ℂ) =
      ∑ q : choices oldLists newLists B side, choiceScalar oldLists newLists aold anew B side q := by
  change _ = ∑ q : ↥(choices oldLists newLists B side),
    pairedWeight aold q.val.1 * pairedWeight anew q.val.2
  rw [Finset.sum_coe_sort (choices oldLists newLists B side)
    (fun q => pairedWeight aold q.1 * pairedWeight anew q.2),
    divisorMark_norm_sq_eq_pairedChoices, divisorMark_norm_sq_eq_pairedChoices]
  simp only [choices, Finset.sum_product, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem actual_marks_norm_bound (aold : Fin Jo → Ideal (𝓞 K) → ℂ)
    (anew : Fin Jn → Ideal (𝓞 K) → ℂ) (B : Bare) (side : Bool) :
    ‖divisorMark Finset.univ (fun i => (oldLists i).image HeightOneSpectrum.asIdeal)
      aold (oldExtracted B side)‖ ^ 2 *
    ‖divisorMark Finset.univ (fun i => (newLists i).image HeightOneSpectrum.asIdeal)
      anew (newExtracted B)‖ ^ 2 ≤
      ∑ q : choices oldLists newLists B side, ‖choiceScalar oldLists newLists aold anew B side q‖ := by
  have h := norm_sum_le Finset.univ (choiceScalar oldLists newLists aold anew B side)
  rw [← actual_marks_expansion oldLists newLists aold anew B side, norm_mul,
    Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _),
    Real.norm_of_nonneg (sq_nonneg _)] at h
  exact h

def expandedScalar (T : Finset Bare) (side : Bool) (aOuter : Bare → ℂ)
    (aold : Fin Jo → Ideal (𝓞 K) → ℂ) (anew : Fin Jn → Ideal (𝓞 K) → ℂ)
    (q : Expanded oldLists newLists T side) : ℂ :=
  aOuter q.1.val * choiceScalar oldLists newLists aold anew q.1.val side q.2

def scalar (T : Finset Bare) (side : Bool) (aOuter : Bare → ℂ)
    (aold : Fin Jo → Ideal (𝓞 K) → ℂ) (anew : Fin Jn → Ideal (𝓞 K) → ℂ) : Marked → ℂ :=
  Function.extend (expandedReconstruction oldLists newLists T side)
    (expandedScalar oldLists newLists T side aOuter aold anew) (fun _ => 0)

theorem scalar_reconstruction (T : Finset Bare) (side : Bool) (aOuter : Bare → ℂ)
    (aold : Fin Jo → Ideal (𝓞 K) → ℂ) (anew : Fin Jn → Ideal (𝓞 K) → ℂ)
    (q : Expanded oldLists newLists T side) :
    scalar oldLists newLists T side aOuter aold anew
      (expandedReconstruction oldLists newLists T side q) =
      expandedScalar oldLists newLists T side aOuter aold anew q :=
  (expandedReconstruction_injective oldLists newLists T side).extend_apply _ _ q

theorem scalar_norm_le_one (T : Finset Bare) (side : Bool) (aOuter : Bare → ℂ)
    (aold : Fin Jo → Ideal (𝓞 K) → ℂ) (anew : Fin Jn → Ideal (𝓞 K) → ℂ)
    (hOuter : ∀ B ∈ T, ‖aOuter B‖ ≤ 1)
    (ho : ∀ i, ∀ p ∈ oldLists i, ‖aold i p.asIdeal‖ ≤ 1)
    (hn : ∀ i, ∀ p ∈ newLists i, ‖anew i p.asIdeal‖ ≤ 1)
    (B : Marked) (hB : B ∈ source oldLists newLists T side) :
    ‖scalar oldLists newLists T side aOuter aold anew B‖ ≤ 1 := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hB
  rw [scalar_reconstruction, expandedScalar, norm_mul]
  exact mul_le_one₀ (hOuter q.1.val q.1.property) (norm_nonneg _)
    (choiceScalar_norm_le_one oldLists newLists aold anew ho hn q.1.val side q.2)

def reconstructionPacket (T : Finset Bare) (side : Bool) (R : Bare → Ideal (𝓞 K))
    (aOuter : Bare → ℂ) (aold : Fin Jo → Ideal (𝓞 K) → ℂ)
    (anew : Fin Jn → Ideal (𝓞 K) → ℂ)
    (hOuter : ∀ B ∈ T, ‖aOuter B‖ ≤ 1)
    (ho : ∀ i, ∀ p ∈ oldLists i, ‖aold i p.asIdeal‖ ≤ 1)
    (hn : ∀ i, ∀ p ∈ newLists i, ‖anew i p.asIdeal‖ ≤ 1)
    (slotCap : ℕ) (hJo : Jo ≤ slotCap) (hJn : Jn ≤ slotCap) :
    ReconstructionPacket (K := K) («Sector» := Sector)
      (ActualMaskReconstruction.sectorTransport K S D Γ) slotCap (Jo + Jo) (Jn + Jn) :=
  PositiveReconstructionPacket.packet (source oldLists newLists T side)
    (fun B => R (forget oldLists newLists B)) (scalar oldLists newLists T side aOuter aold anew)
    (scalar_norm_le_one oldLists newLists T side aOuter aold anew hOuter ho hn)
    slotCap (by omega) (by omega)

theorem source_sum_eq_choices (T : Finset Bare) (side : Bool) (R : Bare → Ideal (𝓞 K))
    (aOuter : Bare → ℂ) (aold : Fin Jo → Ideal (𝓞 K) → ℂ)
    (anew : Fin Jn → Ideal (𝓞 K) → ℂ) (F : SecondChild K Sector → ℂ) :
    (∑ B ∈ source oldLists newLists T side,
      ‖PositiveReconstructionPacket.sourceScalar (fun B => R (forget oldLists newLists B))
        (scalar oldLists newLists T side aOuter aold anew) B‖ *
          ‖F (B.outer,B.newLabel,B.newRow)‖ ^ 2) =
      ∑ B ∈ T, ∑ q : choices oldLists newLists B side,
        ‖(aOuter B * choiceScalar oldLists newLists aold anew B side q) *
          B.retainedZero (R B)‖ * ‖F (B.outer,B.newLabel,B.newRow)‖ ^ 2 := by
  rw [source, Finset.sum_image
    (fun _ _ _ _ h => expandedReconstruction_injective oldLists newLists T side h)]
  simp only [PositiveReconstructionPacket.sourceScalar, scalar_reconstruction]
  rw [Fintype.sum_sigma]
  rw [← Finset.sum_coe_sort T]
  apply Finset.sum_congr rfl
  intro B hB
  apply Finset.sum_congr rfl
  intro q hq
  rw [show forget oldLists newLists
      (expandedReconstruction oldLists newLists T side ⟨B,q⟩) = B.val from
        forget_reconstruction oldLists newLists B.val side q]
  rfl

/-- The actual old mark on b_side³ A_side C e and the actual new mark
on g v enter a packet constructed from their independent original prime
choices. There is no abstract scalar bound beyond the original weight
contractions, and no source-to-packet equality hypothesis. -/
theorem actual_source_energy_le_packet (T : Finset Bare) (side : Bool)
    (R : Bare → Ideal (𝓞 K)) (aOuter : Bare → ℂ)
    (aold : Fin Jo → Ideal (𝓞 K) → ℂ) (anew : Fin Jn → Ideal (𝓞 K) → ℂ)
    (hOuter : ∀ B ∈ T, ‖aOuter B‖ ≤ 1)
    (ho : ∀ i, ∀ p ∈ oldLists i, ‖aold i p.asIdeal‖ ≤ 1)
    (hn : ∀ i, ∀ p ∈ newLists i, ‖anew i p.asIdeal‖ ≤ 1)
    (slotCap : ℕ) (hJo : Jo ≤ slotCap) (hJn : Jn ≤ slotCap)
    (F : SecondChild K Sector → ℂ) :
    (∑ B ∈ T, ‖aOuter B * B.retainedZero (R B)‖ *
      ‖divisorMark Finset.univ (fun i => (oldLists i).image HeightOneSpectrum.asIdeal)
        aold (oldExtracted B side)‖ ^ 2 *
      ‖divisorMark Finset.univ (fun i => (newLists i).image HeightOneSpectrum.asIdeal)
        anew (newExtracted B)‖ ^ 2 * ‖F (B.outer,B.newLabel,B.newRow)‖ ^ 2) ≤
      ∑ γ ∈ (reconstructionPacket oldLists newLists T side R aOuter aold anew
        hOuter ho hn slotCap hJo hJn).triples,
        tripleDivisorWeight slotCap γ *
          (reconstructionPacket oldLists newLists T side R aOuter aold anew
            hOuter ho hn slotCap hJo hJn).energy F γ := by
  have hp := PositiveReconstructionPacket.source_energy_le_packet
    (source oldLists newLists T side) (fun B => R (forget oldLists newLists B))
    (scalar oldLists newLists T side aOuter aold anew)
    (scalar_norm_le_one oldLists newLists T side aOuter aold anew hOuter ho hn)
    slotCap (by omega : Jo + Jo ≤ 2 * slotCap) (by omega : Jn + Jn ≤ 2 * slotCap) F
  rw [source_sum_eq_choices] at hp
  apply le_trans _ hp
  apply Finset.sum_le_sum
  intro B hB
  have hm := actual_marks_norm_bound oldLists newLists aold anew B side
  calc
    _ = ‖aOuter B * B.retainedZero (R B)‖ *
        (‖divisorMark Finset.univ (fun i => (oldLists i).image HeightOneSpectrum.asIdeal)
          aold (oldExtracted B side)‖ ^ 2 *
        ‖divisorMark Finset.univ (fun i => (newLists i).image HeightOneSpectrum.asIdeal)
          anew (newExtracted B)‖ ^ 2) * ‖F (B.outer,B.newLabel,B.newRow)‖ ^ 2 := by ring
    _ ≤ ‖aOuter B * B.retainedZero (R B)‖ *
        (∑ q : choices oldLists newLists B side,
          ‖choiceScalar oldLists newLists aold anew B side q‖) *
          ‖F (B.outer,B.newLabel,B.newRow)‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (norm_nonneg _)) (sq_nonneg _)
    _ = _ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      simp only [norm_mul]
      ring

end HeckeSkeleton.Moments.MOM_INV_STEP.PositiveAssignedSource

end
