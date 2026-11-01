import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceUnmarkedOrbital
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceMarkedPhysical
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedScale

/-!
# Initial Poisson closure for the actual extracted marked source

The puncture is the extracted product of common primes.  The remaining
prime windows, lengths, coefficients and test are literal column data.
Both initial strict margins follow from the original marked capacity;
fixed support and annular dilation constants are paid at one base
threshold selected before every source parameter.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceMarkedOrbital

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep HeckeSkeleton.Moments.MOM_INV_STEP
open ProviderNodes ProviderInitialEstimate
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))

def columns {σ : Type u} (Λ ν₀ : HeckeCharacter K)
    (j : Ideal (𝓞 K)) (slots : Finset σ) (lists : σ → Finset (Ideal (𝓞 K)))
    (a : σ → Ideal (𝓞 K) → ℂ) (Z X : ℝ) (W : SchwartzMap ℝ ℂ) :
    CanonicalBlock.ColumnData K S σ where
  lambda := Λ
  background := ν₀
  puncture := j
  slots := slots
  primeLists := lists
  primeWeights := a
  labelWeight := fun _ _ => 1
  cutoff := W
  base := Z
  length := Real.logb Z X

theorem sourceMark_eq {σ : Type u} (Λ ν₀ : HeckeCharacter K)
    (j : Ideal (𝓞 K)) (slots : Finset σ) (lists : σ → Finset (Ideal (𝓞 K)))
    (a : σ → Ideal (𝓞 K) → ℂ) (Z X : ℝ) (W : SchwartzMap ℝ ℂ) :
    ProviderInitialInverse.sourceMark K S (columns K S Λ ν₀ j slots lists a Z X W) =
      fun n => SourceMarkedPhysical.mark slots lists a j n.val.val := rfl

theorem radical_norm_le (j : Ideal (𝓞 K)) (hj : j ≠ 0) :
    (j.radical.absNorm : ℝ) ≤ (j.absNorm : ℝ) := by
  have hn : 0 < j.absNorm := Nat.pos_of_ne_zero
    (fun hz => hj (Ideal.absNorm_eq_zero_iff.mp hz))
  exact_mod_cast Nat.le_of_dvd hn (Ideal.absNorm_dvd_absNorm_of_le Ideal.le_radical)

variable (D : ThetaArithmeticData K Sset)

/-- The actual logarithmic column scale and extracted puncture are
charged to the original margins.  There is no assumed initial energy. -/
theorem source_conditions {σ : Type u} (slotCap : ℕ)
    (Λ Gcal ν₀ : HeckeCharacter K) (hcal : ThetaCalibrationInput K Sset D Λ Gcal)
    (hν₀ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset → UnramifiedAt K ν₀ p)
    (j : Ideal (𝓞 K)) (hj : j ≠ 0)
    (slots : Finset σ) (lists : σ → Finset (Ideal (𝓞 K)))
    (a : σ → Ideal (𝓞 K) → ℂ) (lengths : σ → ℝ)
    (gap eps supportC Z X m r z G lo hi : ℝ) (W : SchwartzMap ℝ ℂ)
    (hgap : 0 < gap) (heps : 0 < eps) (hZ : 2 ≤ Z) (hX : 1 ≤ X)
    (hm0 : 0 ≤ m) (hm2 : m ≤ 2) (hG : 0 ≤ G) (hGz : G ≤ z)
    (hfirst : r + 2 * z ≤ m - 2 * gap)
    (hsecond : 2 * r + 8 * z ≤ 3 * m - 2 * gap)
    (hjbound : (j.absNorm : ℝ) ≤ supportC * Z ^ G)
    (hXbound : X ≤ supportC * Z ^ ProviderMarkedScale.columnLength r z G)
    (hsupport : supportC ≤ Z ^ (gap / 4))
    (hwidth : 2 ≤ Z ^ SourceUnmarkedOrbital.mesh gap eps)
    (hmarks : MarkConditions K S slotCap Z (z - G) lo hi slots lists a lengths) :
    SourceConditions K S D (columns K S Λ ν₀ j slots lists a Z X W) Λ Gcal slotCap
      4 m (G + gap / 4) (z - G) gap (SourceUnmarkedOrbital.mesh gap eps)
      (SourceUnmarkedOrbital.truncation gap) lo hi lengths := by
  have hZ1 : 1 < Z := by linarith
  have hZp : 0 < Z := zero_lt_one.trans hZ1
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hlen : Real.logb Z X ≤ ProviderMarkedScale.columnLength r z G + gap / 4 := by
    have hu : X ≤ Z ^ (ProviderMarkedScale.columnLength r z G + gap / 4) := by
      calc
        X ≤ supportC * Z ^ ProviderMarkedScale.columnLength r z G := hXbound
        _ ≤ Z ^ (gap / 4) * Z ^ ProviderMarkedScale.columnLength r z G :=
          mul_le_mul_of_nonneg_right hsupport (Real.rpow_nonneg hZp.le _)
        _ = _ := by rw [← Real.rpow_add hZp]; congr 1; ring
    simpa only [Real.logb_rpow hZp (ne_of_gt hZ1)] using
      Real.logb_le_logb_of_le hZ1 hXp hu
  have hmargin := ProviderMarkedScale.strict_margins m r z G (2 * gap) hG hfirst hsecond
  have hmarg1 : Real.logb Z X + (G + gap / 4) + (z - G) ≤ m - gap := by
    linarith [hmargin.1]
  have hmarg2 : 2 * Real.logb Z X + 6 * (z - G) ≤ 3 * m - gap := by
    linarith [hmargin.2]
  have hQ : 0 ≤ G + gap / 4 := by positivity
  have hz : 0 ≤ z - G := sub_nonneg.mpr hGz
  have hL2 : Real.logb Z X ≤ 2 := by linarith
  have hpuncture : (j.radical.absNorm : ℝ) ≤ Z ^ (G + gap / 4) := by
    calc
      _ ≤ (j.absNorm : ℝ) := radical_norm_le K j hj
      _ ≤ supportC * Z ^ G := hjbound
      _ ≤ Z ^ (gap / 4) * Z ^ G :=
        mul_le_mul_of_nonneg_right hsupport (Real.rpow_nonneg hZp.le _)
      _ = _ := by rw [← Real.rpow_add hZp]; congr 1; ring
  have hpool : 4 * Z ^ Real.logb Z X ≤ Z ^ (4 : ℝ) := by
    have h4 : (4 : ℝ) ≤ Z ^ (2 : ℝ) := by
      norm_num only [Real.rpow_two]
      nlinarith
    calc
      _ ≤ Z ^ (2 : ℝ) * Z ^ (2 : ℝ) :=
        mul_le_mul h4 (Real.rpow_le_rpow_of_exponent_le hZ1.le hL2)
          (Real.rpow_nonneg hZp.le _) (Real.rpow_nonneg hZp.le _)
      _ = _ := by rw [← Real.rpow_add hZp]; norm_num
  exact {
    base_gt_one := hZ1
    row_nonneg := hm0
    column_nonneg := Real.logb_nonneg hZ1 hX
    column_le := hL2.trans (by norm_num)
    puncture_nonneg := hQ
    mark_nonneg := hz
    mesh := ⟨(SourceUnmarkedOrbital.mesh_pos hgap heps).le,
      SourceUnmarkedOrbital.mesh_le_one gap eps⟩
    truncation_nonneg := by unfold SourceUnmarkedOrbital.truncation; positivity
    mesh_width := hwidth
    pool_cap := hpool
    source_margin_one := hmarg1
    source_margin_two := hmarg2
    loss_budget := (SourceUnmarkedOrbital.source_loss_budget gap eps).trans (by linarith)
    lambda_eq := rfl
    calibration := hcal
    background_unramified := hν₀
    puncture_nonzero := hj
    puncture_bound := hpuncture
    marks := hmarks }

variable (Γ : Subgroup (Sset.unit K))
variable [MeasurableSpace (sLocalNormOneGroup K Sset)] [BorelSpace (sLocalNormOneGroup K Sset)]
  [Γ.FiniteIndex] [IsPrincipalIdealRing (Set.integer Sset K)]

/-- Shrinking the capacity and row cap leaves every actual node inside
the uniform class.  The mark budget and its two margins are unchanged. -/
theorem uniform_restrict (Θ : Subgroup (HeckeCharacter K)) (ψ Λ G : HeckeCharacter K)
    (slotCap : ℕ) (Z A A' c z lo hi eps R R' C : ℝ) (q : Finset (ℕ × ℕ))
    (hA : A ≤ A') (hR : R ≤ R')
    (hb : UniformBound.{u} (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap
      Z A' c z lo hi eps R' C q) :
    UniformBound.{u} (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap
      Z A c z lo hi eps R C q := by
  intro σ x hx hrow
  exact hb x { hx with total_le := hx.total_le.trans hA } (hrow.trans hR)

variable (hΓ : Γ ≤ (powMonoidHom 6 : (Sset.unit K) →* (Sset.unit K)).range)
  (hallowed : AllowedGeneratorInput K Sset D)
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include hΓ hallowed μv ν μ in
theorem exists_uniform_orbital_bound (slotCap : ℕ) (gap eps supportC : ℝ)
    (hgap : 0 < gap) (heps : 0 < eps) (hC : 1 ≤ supportC)
    (qchild : Finset (ℕ × ℕ)) :
    ∃ q : Finset (ℕ × ℕ), ∃ C Z₀ : ℝ, 1 ≤ C ∧ 2 ≤ Z₀ ∧
      ∀ {σ : Type u} [DecidableEq σ] (Θ : Subgroup (HeckeCharacter K))
        (ψ Λ Gcal ν₀ : HeckeCharacter K), Gcal ∈ Θ →
      ThetaCalibrationInput K Sset D Λ Gcal → BackgroundCycle.Admissible K Θ ψ ν₀ →
      (∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset → UnramifiedAt K ν₀ p) →
      ∀ (j : Ideal (𝓞 K)), j ≠ 0 → ∀ (slots : Finset σ)
        (lists : σ → Finset (Ideal (𝓞 K))) (a : σ → Ideal (𝓞 K) → ℂ)
        (lengths : σ → ℝ) (Z X m r z G lo hi : ℝ),
      Z₀ ≤ Z → 1 ≤ X → 0 ≤ m → m ≤ 2 → 0 ≤ G → G ≤ z →
      r + 2 * z ≤ m - 2 * gap → 2 * r + 8 * z ≤ 3 * m - 2 * gap →
      (j.absNorm : ℝ) ≤ supportC * Z ^ G →
      X ≤ supportC * Z ^ ProviderMarkedScale.columnLength r z G →
      MarkConditions K S slotCap Z (z - G) lo hi slots lists a lengths →
      ∀ (W : SchwartzMap ℝ ℂ), tsupport W ⊆ Set.Icc (1 : ℝ) 2 →
      ∀ Cih : ℝ, 1 ≤ Cih →
      UniformBound.{u} (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ Gcal slotCap Z 2
        (3 * gap / 4) (z - G) lo hi (eps / 2) 2 Cih qchild →
      ‖SourceReductionPoisson.orbitalEnergy K S D Γ ν₀
        (fun n => SourceMarkedPhysical.mark slots lists a j n.val.val) W X
        ⟨Z ^ m, Real.rpow_pos_of_pos (by linarith) m⟩‖ ≤
      C * Cih * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 * Z ^ (m + eps) := by
  obtain ⟨q, C, hC0, hb⟩ := ProviderInitialClosure.exists_uniform_orbital_bound
    K S D Γ hΓ hallowed μv ν μ slotCap 4 2 (SourceUnmarkedOrbital.auxiliaryLoss eps)
      (SourceUnmarkedOrbital.truncation gap) (by norm_num) (by norm_num)
      (by unfold SourceUnmarkedOrbital.auxiliaryLoss; positivity)
      (by unfold SourceUnmarkedOrbital.truncation; positivity) qchild
  obtain ⟨Z₁, hZ₁, hw⟩ := exists_uniform_power_threshold
    (SourceUnmarkedOrbital.mesh gap eps) 2 (SourceUnmarkedOrbital.mesh_pos hgap heps) (by norm_num)
  obtain ⟨Z₂, hZ₂, hs⟩ := exists_uniform_power_threshold (gap / 4) supportC (by positivity) hC
  refine ⟨q, C, max Z₁ Z₂, hC0, hZ₁.trans (le_max_left _ _), ?_⟩
  intro σ _ Θ ψ Λ Gcal ν₀ hGcal hcal hν hunram j hj slots lists a lengths
    Z X m r z G lo hi hZ hX hm0 hm2 hG hGz hf hg hjbound hXbound hmarks W hW Cih hCih hih
  have hZ1 : Z₁ ≤ Z := (le_max_left _ _).trans hZ
  have hZ2 : Z₂ ≤ Z := (le_max_right _ _).trans hZ
  have hZtwo : 2 ≤ Z := hZ₁.trans hZ1
  have hZgt : 1 < Z := by linarith
  have hZp : 0 < Z := zero_lt_one.trans hZgt
  let C₀ := columns K S Λ ν₀ j slots lists a Z X W
  have hcond := source_conditions K S D slotCap Λ Gcal ν₀ hcal hunram j hj
    slots lists a lengths gap eps supportC Z X m r z G lo hi W hgap heps hZtwo hX
    hm0 hm2 hG hGz hf hg hjbound hXbound (hs Z hZ2) (hw Z hZ1) hmarks
  have hih' : UniformBound.{u} (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ Gcal slotCap
      Z m (3 * gap / 4) (z - G) lo hi (eps / 2) m Cih qchild :=
    uniform_restrict K S D Γ Θ ψ Λ Gcal slotCap Z m 2
      (3 * gap / 4) (z - G) lo hi (eps / 2) m 2 Cih qchild hm2 hm2 hih
  have hbound := hb C₀ Θ ψ hν W hW Λ Gcal hGcal m (G + gap / 4) (z - G)
    gap (SourceUnmarkedOrbital.mesh gap eps) (SourceUnmarkedOrbital.truncation gap)
    lo hi lengths hcond (eps / 2) Cih hm2 le_rfl (by positivity) hCih hih'
  have hscale : C₀.base ^ C₀.length = X :=
    Real.rpow_logb hZp (ne_of_gt hZgt) (zero_lt_one.trans_le hX)
  have hrow : ProviderInitialProduction.rowCap K S C₀ hcond.base_gt_one m =
      ⟨Z ^ m, Real.rpow_pos_of_pos hZp m⟩ := rfl
  rw [hscale, hrow, sourceMark_eq] at hbound
  apply hbound.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le hZgt.le
  linarith [SourceUnmarkedOrbital.final_loss_budget (gap := gap) heps.le]

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceMarkedOrbital

end
