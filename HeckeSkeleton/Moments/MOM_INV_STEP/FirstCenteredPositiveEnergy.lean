import HeckeSkeleton.Moments.MOM_INV_STEP.FirstPositiveSource
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstCommonEnvelope

/-!
# Whole first positive energies at common fixed centers

The center index is finite and fixed. A literal overlap divisor is
assigned to a geometric box, and the output energy is grouped by that
index before its family is selected. Thus the complete pool and norm
length of each displayed family depend on the box, not on a source
reconstruction inside it.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstCenteredPositiveEnergy

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
  MeasureTheory
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalBlock CanonicalNormPools
  FirstOverlapColumns FirstColumnAssembly FirstColumnEnergy FirstCenteredColumnEnergy
  FirstCenteredMellinEnergy FirstPositiveSource FirstMobiusGeometry CommonKernel
open scoped Classical BigOperators nonZeroDivisors

def centerScale (X v : {r : ℝ // 0 < r}) : {r : ℝ // 0 < r} :=
  ⟨X.val / v.val, div_pos X.property v.property⟩

theorem centerScale_eq (X v : {r : ℝ // 0 < r}) :
    X.val = v.val * (centerScale X v).val := by
  dsimp only [centerScale]
  field_simp [v.property.ne']

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "E" => CanonicalIdealRow.exteriorMonoid K S

/-- Only actual geometric box membership is data. No source identity,
norm bound on a column, or energy estimate occurs here. -/
structure Centering (ι : Type*) [Fintype ι] (X : {r : ℝ // 0 < r})
    (r₁ r₂ b₁ b₂ : Ext) (side : Bool) where
  center : ι → {r : ℝ // 0 < r}
  assignment : overlapPool K S X r₁ r₂ b₁ b₂ false → ι
  lower : ∀ e, (center (assignment e)).val ≤
    extractedHeight K S r₁ r₂ b₁ b₂ side (overlapIdeal K S D X r₁ r₂ b₁ b₂ false e)
  upper : ∀ e, extractedHeight K S r₁ r₂ b₁ b₂ side
    (overlapIdeal K S D X r₁ r₂ b₁ b₂ false e) ≤ 2 * (center (assignment e)).val

variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ
variable {σ ι : Type*} [Fintype ι]
variable (C : ColumnData K S σ)
variable (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ C.background) (hG : G ∈ Θ)
variable (X : {r : ℝ // 0 < r})
  (r₁ r₂ b₁ b₂ : ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K)))) (side : Bool)
variable (centers : Centering K S D ι X r₁ r₂ b₁ b₂ side)
variable (f z : CanonicalIdealRow.exteriorMonoid K S)
  (d : Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) (ξ : CanonicalSectors.UnitClasses K (S : Set (HeightOneSpectrum (𝓞 K))) Γ)
variable (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)

def branchEnergy (k : ι) (e : overlapPool K S X r₁ r₂ b₁ b₂ false) (η : LogPlane) : ℝ :=
  ((height K Sset (overlapIdeal K S D X r₁ r₂ b₁ b₂ false e))⁻¹ *
      (C.slots.powerset.card : ℝ)) *
    (((centerScale X (centers.center k)).val ^ (-(1 / 2 : ℝ))) ^ 2 *
      (∫ t : ℝ, ‖MellinSeparation.density W hW t‖)) *
    ∑ J ∈ C.slots.powerset,
      ‖assignedMark K S C r₁ r₂ b₁ b₂ side
        (overlapIdeal K S D X r₁ r₂ b₁ b₂ false e) J‖ ^ 2 *
      mellinEnergy K S Γ D C Θ ψ G hν hG J (centerScale X (centers.center k)).val
        (-(1 / 2 : ℝ)) (firstTriple K S r₁ r₂ b₁ b₂
          (overlapIdeal K S D X r₁ r₂ b₁ b₂ false e))
        (retainedLabel K S r₁ r₂ b₁ b₂).val.val d W hW
        (CanonicalIdealRow.toExterior K S (firstRow K S r₁ r₂ b₁ b₂ f z), ξ)
        (signedCoordinate side η)

theorem branchEnergy_nonneg (k : ι) (e : overlapPool K S X r₁ r₂ b₁ b₂ false)
    (η : LogPlane) :
    0 ≤ branchEnergy K S D Γ C Θ ψ G hν hG X r₁ r₂ b₁ b₂ side centers f z d ξ W hW k e η := by
  unfold branchEnergy
  apply mul_nonneg
  · exact mul_nonneg
      (mul_nonneg (inv_nonneg.mpr (height_pos K Sset _).le) (Nat.cast_nonneg _))
      (mul_nonneg (sq_nonneg _) (integral_nonneg (fun _ => norm_nonneg _)))
  · apply Finset.sum_nonneg
    intro J hJ
    exact mul_nonneg (sq_nonneg _)
      (mellinEnergy_nonneg K S Γ D C Θ ψ G hν hG J _ _ _ _ d W hW _ _)

def centeredEnergy (w : LogPlane → ℝ) : ℝ :=
  ∑ k : ι, ∑ e : overlapPool K S X r₁ r₂ b₁ b₂ false,
    if centers.assignment e = k then
      ‖(moebius e.val : ℂ)‖ *
        ∫ η : LogPlane, w η *
          branchEnergy K S D Γ C Θ ψ G hν hG X r₁ r₂ b₁ b₂ side centers f z d ξ W hW k e η
    else 0

theorem centeredEnergy_eq (w : LogPlane → ℝ) :
    centeredEnergy K S D Γ C Θ ψ G hν hG X r₁ r₂ b₁ b₂ side centers f z d ξ W hW w =
      ∑ e : overlapPool K S X r₁ r₂ b₁ b₂ false, ‖(moebius e.val : ℂ)‖ *
        ∫ η : LogPlane, w η *
          branchEnergy K S D Γ C Θ ψ G hν hG X r₁ r₂ b₁ b₂ side centers f z d ξ W hW
            (centers.assignment e) e η := by
  unfold centeredEnergy
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)

include hΓ in
theorem branchEnergy_integrable (k : ι) (e : overlapPool K S X r₁ r₂ b₁ b₂ false)
    (w : LogPlane → ℝ) (hw : Integrable w) :
    Integrable (fun η : LogPlane => w η *
      branchEnergy K S D Γ C Θ ψ G hν hG X r₁ r₂ b₁ b₂ side centers f z d ξ W hW k e η) := by
  unfold branchEnergy
  simp only [Finset.mul_sum]
  apply integrable_finset_sum
  intro J hJ
  have hi := fourier_mellinEnergy_integrable K S Γ D C Θ ψ G hν hG J
    (centerScale X (centers.center k)).val (-(1 / 2 : ℝ))
    (firstTriple K S r₁ r₂ b₁ b₂ (overlapIdeal K S D X r₁ r₂ b₁ b₂ false e))
    (retainedLabel K S r₁ r₂ b₁ b₂).val.val d hΓ W hW
    (CanonicalIdealRow.toExterior K S (firstRow K S r₁ r₂ b₁ b₂ f z), ξ)
    w hw (signedCoordinate side) (signedCoordinate_continuous side)
  convert hi.const_mul
    (((height K Sset (overlapIdeal K S D X r₁ r₂ b₁ b₂ false e))⁻¹ *
        (C.slots.powerset.card : ℝ)) *
      (((centerScale X (centers.center k)).val ^ (-(1 / 2 : ℝ))) ^ 2 *
        (∫ t : ℝ, ‖MellinSeparation.density W hW t‖)) *
      ‖assignedMark K S C r₁ r₂ b₁ b₂ side
        (overlapIdeal K S D X r₁ r₂ b₁ b₂ false e) J‖ ^ 2) using 1
  funext η
  ring

variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)

include hallowed hΓ in
theorem sourceColumn_le_branchEnergy
    (hGunramified : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset → UnramifiedAt K G p)
    (hCX : C.base ^ C.length = X.val) (hZ : 1 < C.base) (hCW : C.cutoff = W)
    (hprime : ∀ i ∈ C.slots, ∀ p ∈ C.primeLists i, Prime p)
    (e : overlapPool K S X r₁ r₂ b₁ b₂ false) (η : LogPlane) :
    ‖sourceColumn K S D Γ C G X r₁ r₂ b₁ b₂ side f z d ξ
      (overlapIdeal K S D X r₁ r₂ b₁ b₂ false e) (signedCoordinate side η)‖ ^ 2 ≤
      branchEnergy K S D Γ C Θ ψ G hν hG X r₁ r₂ b₁ b₂ side centers f z d ξ W hW
        (centers.assignment e) e η :=
  sourceColumn_sq_le_centered_energy K S D Γ hallowed hΓ C Θ ψ G hν hG hGunramified X hCX
    r₁ r₂ b₁ b₂ side f z d ξ (overlapIdeal K S D X r₁ r₂ b₁ b₂ false e)
    (overlap_squarefree K S X r₁ r₂ b₁ b₂ false e.val e.property)
    W hW hCW (signedCoordinate side η) hprime
    (centers.center (centers.assignment e)).val
    (centerScale X (centers.center (centers.assignment e))).val hZ
    (centers.center (centers.assignment e)).property
    (centerScale X (centers.center (centers.assignment e))).property
    (centers.lower e) (centers.upper e) (centerScale_eq X _)

include hallowed hΓ in
/-- The density hypothesis is a pointwise analytic comparison. The
actual first density is supplied by FirstCommonEnvelope below. -/
theorem sourceEnergy_le_of_density_bound
    (hGunramified : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset → UnramifiedAt K G p)
    (hCX : C.base ^ C.length = X.val) (hZ : 1 < C.base) (hCW : C.cutoff = W)
    (hprime : ∀ i ∈ C.slots, ∀ p ∈ C.primeLists i, Prime p)
    (P : Profile K S) (w : LogPlane → ℝ) (hw : Integrable w) (hw0 : ∀ η, 0 ≤ w η)
    (M : ℝ) (hM : 0 ≤ M) (hP : ∀ η, ‖P.density K S Γ η‖ ≤ M * w η) :
    sourceEnergy K S D Γ C G P X r₁ r₂ b₁ b₂ side f z d ξ ≤
      M * centeredEnergy K S D Γ C Θ ψ G hν hG X r₁ r₂ b₁ b₂ side centers f z d ξ W hW w := by
  rw [sourceEnergy_eq K S D Γ, centeredEnergy_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  have hnonneg (η : LogPlane) := branchEnergy_nonneg
    K S D Γ C Θ ψ G hν hG X r₁ r₂ b₁ b₂ side centers f z d ξ W hW
    (centers.assignment e) e η
  have hbound (η : LogPlane) :
      ‖P.density K S Γ η‖ *
        ‖sourceColumn K S D Γ C G X r₁ r₂ b₁ b₂ side f z d ξ
          (overlapIdeal K S D X r₁ r₂ b₁ b₂ false e) (signedCoordinate side η)‖ ^ 2 ≤
      M * (w η * branchEnergy K S D Γ C Θ ψ G hν hG X r₁ r₂ b₁ b₂ side
        centers f z d ξ W hW (centers.assignment e) e η) := by
    exact (mul_le_mul (hP η)
      (sourceColumn_le_branchEnergy K S D Γ C Θ ψ G hν hG X r₁ r₂ b₁ b₂ side
        centers f z d ξ W hW hΓ hallowed hGunramified hCX hZ hCW hprime e η)
      (sq_nonneg _) (mul_nonneg hM (hw0 η))).trans_eq (mul_assoc _ _ _)
  have hr := (branchEnergy_integrable K S D Γ C Θ ψ G hν hG X r₁ r₂ b₁ b₂ side
    centers f z d ξ W hW hΓ (centers.assignment e) e w hw).const_mul M
  have hpd : Continuous (P.density K S Γ) :=
    (orbitalDensity K Sset Γ P.finiteTest P.finiteTest_continuous P.finiteTest_compact
      dyadicCutoff dyadicCutoff_contDiff dyadicCutoff_hasCompactSupport P.archTest P.radius).continuous
  have hsc := (sourceColumn_continuous K S D Γ C G X r₁ r₂ b₁ b₂ side f z d ξ
    (overlapIdeal K S D X r₁ r₂ b₁ b₂ false e)).comp (signedCoordinate_continuous side)
  have hl := hr.mono_nonneg (hpd.norm.mul (hsc.norm.pow 2)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun η => mul_nonneg (norm_nonneg _) (sq_nonneg _))
    (Filter.Eventually.of_forall hbound)
  have hi := integral_mono hl hr hbound
  rw [integral_const_mul] at hi
  exact (mul_le_mul_of_nonneg_left hi (norm_nonneg (moebius e.val : ℂ))).trans_eq (by ring)

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstCenteredPositiveEnergy

end

