import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialSpectral

/-!
# Uniform bound for the literal initial retained-production totals

All source conditions are arithmetic, geometric, or profile support
conditions. The actual three-coordinate norm boxes, fixed common/overlap
centers, original slot subsets and common Mellin density are summed here.
The constants and finite seminorm precede the original profile and every
source parameter. The only energy input is the proved canonical stage
bound that the full induction supplies.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

noncomputable section

universe u

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialEstimate

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep HeckeSkeleton.Moments.MOM_INV_STEP
open CanonicalChildren CanonicalNormPools ProviderNodes CommonKernel SecondSpectralCost
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))

/-- The actual source geometry for the initial inverse transform.
There is no energy, fiber estimate, terminal conclusion or production
identity among these fields. -/
structure SourceConditions {σ : Type u} (C : CanonicalBlock.ColumnData K S σ)
    (Lambda G : HeckeCharacter K) (slotCap : ℕ)
    (A m Q z c h tau lo hi : ℝ) (markLengths : σ → ℝ) : Prop where
  base_gt_one : 1 < C.base
  row_nonneg : 0 ≤ m
  column_nonneg : 0 ≤ C.length
  column_le : C.length ≤ A
  puncture_nonneg : 0 ≤ Q
  mark_nonneg : 0 ≤ z
  mesh : h ∈ Set.Icc (0 : ℝ) 1
  truncation_nonneg : 0 ≤ tau
  mesh_width : 2 ≤ C.base ^ h
  pool_cap : 4 * C.base ^ C.length ≤ C.base ^ A
  source_margin_one : C.length + Q + z ≤ m - c
  source_margin_two : 2 * C.length + 6 * z ≤ 3 * m - c
  loss_budget : 100 * h + 3 * tau ≤ c / 4
  lambda_eq : C.lambda = Lambda
  calibration : ThetaCalibrationInput K Sset D C.lambda G
  background_unramified : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset → UnramifiedAt K C.background p
  puncture_nonzero : C.puncture ≠ 0
  puncture_bound : (C.puncture.radical.absNorm : ℝ) ≤ C.base ^ Q
  marks : MarkConditions K S slotCap C.base z lo hi C.slots C.primeLists C.primeWeights markLengths

variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ
local instance unitClassesFintype :
    Fintype (CanonicalSectors.UnitClasses K (S : Set (HeightOneSpectrum (𝓞 K))) Γ) :=
  Fintype.ofFinite _

/-- Both actual initial positive production totals satisfy the
original m-power bound. The displayed 48h+5pi accounts for all norm
windows, physical/radial factors, frozen measure and finite partitions. -/
theorem exists_uniform_total_bound (slotCap : ℕ) (A pi : ℝ)
    (hA : 0 ≤ A) (hpi : 0 < pi) (qchild : Finset (ℕ × ℕ)) :
    ∃ e : ℝ, 0 < e ∧ ∃ k : ℕ, ∃ q : Finset (ℕ × ℕ), ∃ B : ℝ, 0 ≤ B ∧
      ∀ {σ : Type u} [DecidableEq σ]
        (C : CanonicalBlock.ColumnData K S σ)
        (Theta : Subgroup (HeckeCharacter K)) (psi : HeckeCharacter K)
        (hnu : BackgroundCycle.Admissible K Theta psi C.background)
        (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
        (Lambda G : HeckeCharacter K) (hG : G ∈ Theta)
        (m Q z c h tau lo hi : ℝ) (markLengths : σ → ℝ)
        (hb : SourceConditions K S D C Lambda G slotCap A m Q z c h tau lo hi markLengths)
        (eps Cih : ℝ), 0 ≤ eps → 0 ≤ Cih →
      UniformBound.{u} (Γ := Γ) (Θ := Theta) (ψ := psi) D Lambda G slotCap C.base m
        (3 * c / 4) z lo hi eps m Cih qchild → ∀ side : Bool,
      let T := ProviderInitialProduction.parent K S C Theta psi hnu W hb.base_gt_one hW m
      let H := SecondAdaptiveCutoff.fineCutoff K S T.radius (C.base ^ C.length) C.base tau
      (C.base ^ C.length)⁻¹ * SecondAdaptiveProduction.totalAt K S D Γ T H G hG e k side ≤
        B * (Cih + (Fintype.card Sector : ℝ)) *
          (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 *
          C.base ^ (m + 48 * h + 5 * pi + eps) := by
  obtain ⟨e, he, s, Bpoint, hBpoint, hpoint⟩ :=
    ProviderInitialPointwise.exists_uniform_source_bound K S D Γ slotCap A pi hA hpi qchild
  obtain ⟨k, Bpoly, hBpoly, q, Bspec, hBspec, hpoly, hspectral⟩ :=
    ProviderInitialSpectral.exists_uniform_spectral_cost s
  obtain ⟨Bcenter, hBcenter, hcenters⟩ := ProviderInitialBoxes.exists_center_count_bound A pi hA hpi
  obtain ⟨Bbox, hBbox, hboxes⟩ := ProviderInitialBoxes.exists_box_count_bound A pi hA hpi
  let B := Bpoint * Bcenter * Bbox * ((2 : ℝ) ^ slotCap) ^ 2 * Bspec
  have hBbox0 : 0 ≤ Bbox := zero_le_one.trans hBbox
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨e, he, k, q, B, hB, ?_⟩
  intro σ _ C Theta psi hnu W hW Lambda G hG m Q z c h tau lo hi markLengths hb
    eps Cih heps hCih hih side
  let Z := C.base
  let X := C.base ^ C.length
  let T := ProviderInitialProduction.parent K S C Theta psi hnu W hb.base_gt_one hW m
  let H := SecondAdaptiveCutoff.fineCutoff K S T.radius X C.base tau
  let E := m + 48 * h + 3 * pi + eps
  let Cpoint := Bpoint * (Cih + (Fintype.card Sector : ℝ)) * Z ^ E
  let I := ∫ p : LogPlane × ℝ, ProviderInitialIntegral.density W hW k p *
    polynomialCost k Bpoly (SecondParentProduction.coordinate side) p
    ∂((volume : Measure LogPlane).prod (volume : Measure ℝ))
  have hz : 0 < Z := zero_lt_one.trans hb.base_gt_one
  have hCpoint : 0 ≤ Cpoint := mul_nonneg
    (mul_nonneg hBpoint (add_nonneg hCih (Nat.cast_nonneg _))) (Real.rpow_nonneg hz.le _)
  have hI : 0 ≤ I := integral_nonneg (fun p => mul_nonneg
    (ProviderInitialIntegral.density_nonneg W hW k p)
    (polynomialCost_nonneg k Bpoly hBpoly _ p))
  have hmass : 0 ≤ SecondMellinEnergy.mellinMass (ProviderInitialIntegral.mellinTest W)
      (ProviderInitialIntegral.mellinTest_support W hW) := SecondMellinEnergy.mellinMass_nonneg _ _
  have hsource (b : SecondMobiusGeometry.Index X) (J : Finset σ) (hJ : J ⊆ C.slots)
      (j : ProviderInitialBoxes.BoxIndex Z A) :
      ProviderInitialIntegral.sourceIntegral K S D Γ C Theta psi hnu W G hG hb.base_gt_one hW
        m H e k side (ProviderInitialBoxes.boxed K S D Γ X H Finset.univ b Z A j) b J ≤ Cpoint * I := by
    have hbound (p : LogPlane × ℝ) :
        ProviderInitialPointwise.sourceSum K S D Γ C Theta psi hnu W G hG hb.base_gt_one hW
          m H (ProviderInitialBoxes.boxed K S D Γ X H Finset.univ b Z A j) b J e
          (p.2 + SecondParentProduction.coordinate side p.1) ≤
        Cpoint * polynomialCost k Bpoly (SecondParentProduction.coordinate side) p := by
      have hp := hpoint C Theta psi hnu W G hG hb.base_gt_one hW
        m Q z c h tau lo hi eps Cih markLengths H Finset.univ b j J Lambda
        hb.row_nonneg hb.column_le hb.puncture_nonneg hb.mark_nonneg hb.mesh hb.truncation_nonneg
        hb.mesh_width hb.pool_cap hb.source_margin_one hb.source_margin_two hb.loss_budget rfl
        hb.lambda_eq hb.calibration hb.background_unramified hb.puncture_nonzero hb.puncture_bound
        hb.marks hJ heps hCih hih (p.2 + SecondParentProduction.coordinate side p.1)
      apply hp.trans
      convert mul_le_mul_of_nonneg_left (hpoly side p) hCpoint using 1 <;>
        dsimp only [Cpoint, E, Z] <;> ring
    unfold ProviderInitialIntegral.sourceIntegral
    rw [show Cpoint * I = ∫ p : LogPlane × ℝ,
      Cpoint * (ProviderInitialIntegral.density W hW k p *
        polynomialCost k Bpoly (SecondParentProduction.coordinate side) p)
        ∂((volume : Measure LogPlane).prod (volume : Measure ℝ)) by rw [integral_const_mul]]
    apply integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun p => mul_nonneg
        (ProviderInitialIntegral.density_nonneg W hW k p)
        (ProviderInitialPointwise.sourceSum_nonneg K S D Γ C Theta psi hnu W G hG
          hb.base_gt_one hW m H _ b J e _)))
      ((ProviderInitialSpectral.joint_polynomial_integrable W hW k Bpoly
        (SecondParentProduction.coordinate side)).const_mul Cpoint)
    exact Filter.Eventually.of_forall (fun p =>
      (mul_le_mul_of_nonneg_left (hbound p)
        (ProviderInitialIntegral.density_nonneg W hW k p)).trans_eq (by ring))
  let nB := (Fintype.card (SecondMobiusGeometry.Index X) : ℝ)
  let nJ := (C.slots.powerset.card : ℝ)
  let nQ := (Fintype.card (ProviderInitialBoxes.BoxIndex Z A) : ℝ)
  have hsum : (∑ b : SecondMobiusGeometry.Index X, ∑ J ∈ C.slots.powerset,
      ∑ j : ProviderInitialBoxes.BoxIndex Z A,
        ProviderInitialIntegral.sourceIntegral K S D Γ C Theta psi hnu W G hG hb.base_gt_one hW
          m H e k side (ProviderInitialBoxes.boxed K S D Γ X H Finset.univ b Z A j) b J) ≤
        nB * nJ * nQ * (Cpoint * I) := by
    calc
      _ ≤ ∑ _b : SecondMobiusGeometry.Index X, ∑ _J ∈ C.slots.powerset,
          ∑ _j : ProviderInitialBoxes.BoxIndex Z A, Cpoint * I :=
        Finset.sum_le_sum (fun b _ => Finset.sum_le_sum (fun J hJ =>
          Finset.sum_le_sum (fun j _ => hsource b J (Finset.mem_powerset.mp hJ) j)))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nB, nJ, nQ]; ring
  have hnB : nB ≤ Bcenter * Z ^ pi := hcenters Z X hb.base_gt_one.le
    (by have hX := Real.one_le_rpow hb.base_gt_one.le hb.column_nonneg; dsimp only [X] at *; linarith)
    hb.pool_cap
  have hnQ : nQ ≤ Bbox * Z ^ pi := hboxes Z hb.base_gt_one.le
  have hnJ : nJ ≤ (2 : ℝ) ^ slotCap := by
    dsimp only [nJ]
    rw [Finset.card_powerset, Nat.cast_pow, Nat.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) hb.marks.card_le
  have hcount : nB * nQ * nJ ^ 2 ≤
      (Bcenter * Bbox * ((2 : ℝ) ^ slotCap) ^ 2) * Z ^ (2 * pi) := by
    have hp := mul_le_mul hnB hnQ (Nat.cast_nonneg _) (mul_nonneg hBcenter (Real.rpow_nonneg hz.le _))
    have hq := pow_le_pow_left₀ (Nat.cast_nonneg _) hnJ 2
    apply (mul_le_mul hp hq (sq_nonneg _) (by positivity)).trans_eq
    rw [show Z ^ (2 * pi) = Z ^ pi * Z ^ pi by
      rw [← Real.rpow_add hz]; congr 1; ring]
    ring
  have hcost := hspectral W hW side
  change SecondMellinEnergy.mellinMass (ProviderInitialIntegral.mellinTest W)
      (ProviderInitialIntegral.mellinTest_support W hW) * I ≤
    Bspec * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 at hcost
  dsimp only
  rw [ProviderInitialIntegral.actualTotal_eq_boxed_integrals K S D Γ C Theta psi hnu W G hG
    hb.base_gt_one hW m H e k side A]
  apply (mul_le_mul_of_nonneg_left hsum
    (mul_nonneg (Nat.cast_nonneg _) hmass)).trans
  have hcombine := mul_le_mul (mul_le_mul_of_nonneg_right hcount hCpoint) hcost
    (mul_nonneg hmass hI)
    (mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hz.le _)) hCpoint)
  have heq : ProviderInitialIntegral.cauchyMass K S C W hW *
      (nB * nJ * nQ * (Cpoint * I)) =
      (nB * nQ * nJ ^ 2 * Cpoint) *
        (SecondMellinEnergy.mellinMass (ProviderInitialIntegral.mellinTest W)
          (ProviderInitialIntegral.mellinTest_support W hW) * I) := by
    dsimp only [ProviderInitialIntegral.cauchyMass, nJ]
    ring
  rw [heq]
  apply hcombine.trans_eq
  dsimp only [B, Cpoint, E, Z]
  rw [show C.base ^ (m + 48 * h + 5 * pi + eps) =
    C.base ^ (2 * pi) * C.base ^ (m + 48 * h + 3 * pi + eps) by
      rw [← Real.rpow_add hz]; congr 1; ring]
  ring

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialEstimate

end
