import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CombinedDirectSecondTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectFirstTerminalMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualDirectSecondSourceTerminal

/-!
# Original direct source sums after the central degree cancels

The first profile shift and the opposite second coefficient exponent
are combined on each actual class. The original common label, physical
mask, internal divisor, finite phase and first Fourier mass are then
summed without changing their carrier. The inverse internal-divisor
norm remains in the original arithmetic mass.

The only counting costs are the actual complete-tuple multiplicities
and the already proved original arithmetic mass. Their constants are
chosen before all moving sources and scales. The public zero and tail
entries build their class bounds from individual amplitude windows;
neither accepts a terminal or transformed-source bound.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup
open CommonSupportMass UniqueFactorizationMonoid MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {E W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {Z : ℝ}
variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX}

local instance combinedDirectSourceTerminalCircleCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

namespace ActualDirectFirstSource

/-- Individual original arithmetic and first-profile windows. The
shift stays with its own first common label and physical divisor. -/
structure CombinedTerminalOriginalWindows
    (s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX)
    (normBound parentWidth firstAmplitude kernelBound : ℝ)
    (total shift : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ) where
  oldMask : Ideal (𝓞 K)
  old_squarefree : Squarefree oldMask
  old_ne_zero : oldMask ≠ 0
  old_divides : ∀ i ∈ s.columns, oldMask ∣ (s.ideal i).val
  column_norm : ∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ normBound
  maskIdeal : Ideal (𝓞 K)
  mask_ne_zero : maskIdeal ≠ 0
  mask_norm : (Ideal.absNorm maskIdeal : ℝ) ≤ Z ^ normBound
  original_mask : OriginalMaskPrimeData s.mask maskIdeal
  first_profile : ∀ v D, (s.pieces v D).weightBound ≤
    firstAmplitude * Z ^ (parentWidth - total v D + shift v D)
  first_kernel : ∀ v D, (firstTerminalFourierControl (W := W)).seminorms.sup
    (schwartzSeminormFamily ℝ W ℂ) (s.charts v D).kernel ≤ kernelBound

namespace SecondStages

variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

/-- The two raw zero amplitudes and their numerical exponent ledgers.
An empty actual source fibre needs no post-pool divisibility window. -/
structure CombinedZeroAmplitudeWindows
    (T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (ε loss profileConstant : ℝ) (fiberCap : ℕ)
    (total shift : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ) where
  exponentL : ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
    ∀ S : divisorPool (s.pieces v D).rightData.columns
      (fun j => ((s.pieces v D).rightData.ideal j).val), ((PUnit × PUnit) →* Circle) → ℝ
  exponentR : ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
    ∀ S : divisorPool (s.pieces v D).rightData.columns
      (fun j => ((s.pieces v D).rightData.ideal j).val), ((PUnit × PUnit) →* Circle) → ℝ
  fiber_left : ∀ v D S χ, ((R v D).left S χ).fiber ≤ fiberCap
  fiber_right : ∀ v D S χ, ((R v D).right S χ).fiber ≤ fiberCap
  tuples_left : ∀ v D S χ, ((T v D).left S χ).windows.multiplicity ≤
    idealDivisorCount (v.val.1 ^ 2) ^ k
  tuples_right : ∀ v D S χ, ((T v D).right S χ).windows.multiplicity ≤
    idealDivisorCount (v.val.2 ^ 2) ^ k
  amplitude_left : ∀ v D S χ, ((R v D).left S χ).fiber ≠ 0 →
    ((T v D).left S χ).zeroAmplitude ≤
      (profileConstant / (Ideal.absNorm S.val : ℝ)) * Z ^ exponentL v D S χ
  amplitude_right : ∀ v D S χ, ((R v D).right S χ).fiber ≠ 0 →
    ((T v D).right S χ).zeroAmplitude ≤
      (profileConstant / (Ideal.absNorm S.val : ℝ)) * Z ^ exponentR v D S χ
  exponent_left : ∀ v D S χ, ((R v D).left S χ).fiber ≠ 0 →
    exponentL v D S χ + ((T v D).left S χ).zeroProductExponent * ε ≤
      (total v D - idealLogLength Z v.val.1 + firstAllowance
        (idealLogLength Z v.val.1) (idealLogLength Z v.val.2)
        (idealLogLength Z (firstActiveRadical v.val.1 v.val.2))) + loss - shift v D
  exponent_right : ∀ v D S χ, ((R v D).right S χ).fiber ≠ 0 →
    exponentR v D S χ + ((T v D).right S χ).zeroProductExponent * ε ≤
      (total v D - idealLogLength Z v.val.2 + firstAllowance
        (idealLogLength Z v.val.2) (idealLogLength Z v.val.1)
        (idealLogLength Z (firstActiveRadical v.val.1 v.val.2))) + loss - shift v D

/-- The original full-Cartesian tail uses the same first allowances,
divisor density, fibres and complete tuple multiplicities. -/
structure CombinedTailAmplitudeWindows
    (T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (loss profileConstant : ℝ) (fiberCap : ℕ)
    (total shift : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ) where
  exponentL : ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
    ∀ S : divisorPool (s.pieces v D).rightData.columns
      (fun j => ((s.pieces v D).rightData.ideal j).val), ((PUnit × PUnit) →* Circle) → ℝ
  exponentR : ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
    ∀ S : divisorPool (s.pieces v D).rightData.columns
      (fun j => ((s.pieces v D).rightData.ideal j).val), ((PUnit × PUnit) →* Circle) → ℝ
  fiber_left : ∀ v D S χ, ((R v D).left S χ).fiber ≤ fiberCap
  fiber_right : ∀ v D S χ, ((R v D).right S χ).fiber ≤ fiberCap
  tuples_left : ∀ v D S χ, ((T v D).left S χ).windows.multiplicity ≤
    idealDivisorCount (v.val.1 ^ 2) ^ k
  tuples_right : ∀ v D S χ, ((T v D).right S χ).windows.multiplicity ≤
    idealDivisorCount (v.val.2 ^ 2) ^ k
  amplitude_left : ∀ v D S χ, ((R v D).left S χ).fiber ≠ 0 →
    ((T v D).left S χ).tailAmplitude ≤
      (profileConstant / (Ideal.absNorm S.val : ℝ)) * Z ^ exponentL v D S χ
  amplitude_right : ∀ v D S χ, ((R v D).right S χ).fiber ≠ 0 →
    ((T v D).right S χ).tailAmplitude ≤
      (profileConstant / (Ideal.absNorm S.val : ℝ)) * Z ^ exponentR v D S χ
  exponent_left : ∀ v D S χ, ((R v D).left S χ).fiber ≠ 0 →
    exponentL v D S χ - Nsave ≤
      (total v D - idealLogLength Z v.val.1 + firstAllowance
        (idealLogLength Z v.val.1) (idealLogLength Z v.val.2)
        (idealLogLength Z (firstActiveRadical v.val.1 v.val.2))) + loss - shift v D
  exponent_right : ∀ v D S χ, ((R v D).right S χ).fiber ≠ 0 →
    exponentR v D S χ - Nsave ≤
      (total v D - idealLogLength Z v.val.2 + firstAllowance
        (idealLogLength Z v.val.2) (idealLogLength Z v.val.1)
        (idealLogLength Z (firstActiveRadical v.val.1 v.val.2))) + loss - shift v D

end SecondStages
end ActualDirectFirstSource

/-- The finite summation step only. The actual terminal entries below
derive its class inequality from their raw amplitude windows. -/
theorem combined_direct_class_sum_from_original_windows
    (k : ℕ) (normBound ε : ℝ) (hN : 0 ≤ normBound) (hε : 0 < ε) :
    ∃ Csum : ℝ, 0 < Csum ∧
    ∀ (Z : ℝ) (hZ : 1 < Z),
    ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ)
      (a : RealParameters) (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X),
    ∀ s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX,
    ∀ (Cterminal parentWidth loss firstAmplitude kernelBound profileConstant : ℝ)
      (fiberCap : ℕ), 0 ≤ Cterminal → 0 ≤ firstAmplitude → 0 ≤ kernelBound →
      0 ≤ profileConstant →
    ∀ total shift : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ,
    ∀ O : s.CombinedTerminalOriginalWindows normBound parentWidth firstAmplitude kernelBound total shift,
    ∀ cost : ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
      ∀ S : divisorPool (s.pieces v D).rightData.columns
        (fun j => ((s.pieces v D).rightData.ideal j).val), ((PUnit × PUnit) →* Circle) → ℝ,
    (∀ v D S χ, cost v D S χ / Z ^ parentWidth ≤
      (firstAmplitude * firstTerminalFourierCost (s.charts v D).kernel *
        (((fiberCap : ℝ) * Cterminal * (idealDivisorCount (v.val.1 ^ 2) ^ k : ℕ) * profileConstant +
          (fiberCap : ℝ) * Cterminal * (idealDivisorCount (v.val.2 ^ 2) ^ k : ℕ) * profileConstant) / 2)) *
        (firstCommonWeight Z v.val.1 v.val.2 *
          (‖(moebius S.val : ℂ)‖ / (Ideal.absNorm S.val : ℝ)) *
            ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖) * Z ^ loss) →
      ((s.fiber : ℝ) * ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
        ∑ S : divisorPool (s.pieces v D).rightData.columns
          (fun j => ((s.pieces v D).rightData.ideal j).val),
        ∑ χ : (PUnit × PUnit) →* Circle, cost v D S χ) / Z ^ parentWidth ≤
      (s.fiber : ℝ) * fiberCap * Cterminal * firstAmplitude * kernelBound *
        profileConstant * Csum * Z ^ (loss + ε) / (Ideal.absNorm O.oldMask : ℝ) := by
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨Ccount, hCcount, hcount⟩ := support_tuple_multiplicity_subpower
    (K := K) k (2 * normBound) δ (by positivity) hδ
  obtain ⟨Cmass, hCmass, hmass⟩ := actual_direct_first_terminal_mass_from_original_windows
    (U := W) (C := C) (hΓ := hΓ) (μv := μv) (finiteTest := finiteTest)
    normBound δ hN hδ
  let CF := (firstTerminalFourierControl (W := W)).constant
  have hCF : 0 < CF := (firstTerminalFourierControl (W := W)).constant_pos
  refine ⟨CF * Ccount * Cmass, by positivity, ?_⟩
  intro Z hZ ω ψ centered d a t Y₁ Y₂ X hX s Cterminal parentWidth loss
    firstAmplitude kernelBound profileConstant fiberCap hC hfirst hkernel hprofile
    total shift O cost hclass
  have hz : 0 < Z := zero_lt_one.trans hZ
  let H : ℝ := firstAmplitude * (CF * kernelBound) *
    ((fiberCap : ℝ) * Cterminal * profileConstant) * Ccount
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hnorm (v : s.CommonLabel) :
      (Ideal.absNorm v.val.1 : ℝ) ≤ Z ^ normBound ∧
        (Ideal.absNorm v.val.2 : ℝ) ≤ Z ^ normBound :=
    actualCommonLabels_norm s.columns s.columns _ _
      (fun i _ => (s.ideal i).property.1) (fun i _ => (s.ideal i).property.1)
      (Z ^ normBound) O.column_norm O.column_norm (v.val, ∅)
      ((mem_actualCommonLabels _ _ _ _ _).mpr ⟨v.property, Finset.empty_subset _⟩)
  have htuple (J : Ideal (𝓞 K)) (hJ : (Ideal.absNorm J : ℝ) ≤ Z ^ normBound) :
      (idealDivisorCount (J ^ 2) ^ k : ℕ) ≤ Ccount * Z ^ δ := by
    have hJ2 : (Ideal.absNorm (J ^ 2) : ℝ) ≤ Z ^ (2 * normBound) := by
      calc
        _ = (Ideal.absNorm J : ℝ) ^ 2 := by simp only [map_pow, Nat.cast_pow]
        _ ≤ (Z ^ normBound) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hJ 2
        _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le]; congr 1; ring
    simpa only [Nat.cast_pow] using hcount Z hZ.le (J ^ 2) hJ2
  have hcoefficient (v : s.CommonLabel) (D : ((s.block v).mask s.mask).powerset) :
      firstAmplitude * firstTerminalFourierCost (s.charts v D).kernel *
        (((fiberCap : ℝ) * Cterminal * (idealDivisorCount (v.val.1 ^ 2) ^ k : ℕ) * profileConstant +
          (fiberCap : ℝ) * Cterminal * (idealDivisorCount (v.val.2 ^ 2) ^ k : ℕ) * profileConstant) / 2) ≤
        H * Z ^ δ := by
    have hside (J : Ideal (𝓞 K)) (hJ : (Ideal.absNorm J : ℝ) ≤ Z ^ normBound) :
        (fiberCap : ℝ) * Cterminal * (idealDivisorCount (J ^ 2) ^ k : ℕ) * profileConstant ≤
          ((fiberCap : ℝ) * Cterminal * profileConstant) * Ccount * Z ^ δ := by
      apply (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (htuple J hJ) (mul_nonneg (Nat.cast_nonneg _) hC))
        hprofile).trans_eq
      ring
    have hmean := div_le_div_of_nonneg_right
      (add_le_add (hside v.val.1 (hnorm v).1) (hside v.val.2 (hnorm v).2))
      (by norm_num : (0 : ℝ) ≤ 2)
    have hmean' :
        ((fiberCap : ℝ) * Cterminal * (idealDivisorCount (v.val.1 ^ 2) ^ k : ℕ) * profileConstant +
          (fiberCap : ℝ) * Cterminal * (idealDivisorCount (v.val.2 ^ 2) ^ k : ℕ) * profileConstant) / 2 ≤
          ((fiberCap : ℝ) * Cterminal * profileConstant) * Ccount * Z ^ δ :=
      hmean.trans_eq (by ring)
    have hF : firstTerminalFourierCost (s.charts v D).kernel ≤ CF * kernelBound :=
      mul_le_mul_of_nonneg_left (O.first_kernel v D) hCF.le
    calc
      _ ≤ firstAmplitude * firstTerminalFourierCost (s.charts v D).kernel *
          (((fiberCap : ℝ) * Cterminal * profileConstant) * Ccount * Z ^ δ) :=
        mul_le_mul_of_nonneg_left hmean'
          (mul_nonneg hfirst (firstTerminalFourierCost_nonneg _))
      _ ≤ firstAmplitude * (CF * kernelBound) *
          (((fiberCap : ℝ) * Cterminal * profileConstant) * Ccount * Z ^ δ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hF hfirst) (by positivity)
      _ = _ := by dsimp only [H]; ring
  have hm := hmass Z hZ centered d a t Y₁ Y₂ X hX s O.oldMask
    O.old_squarefree O.old_ne_zero O.old_divides O.column_norm O.maskIdeal
    O.mask_ne_zero O.mask_norm O.original_mask
  calc
    _ = (s.fiber : ℝ) * ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
        ∑ S : divisorPool (s.pieces v D).rightData.columns
          (fun j => ((s.pieces v D).rightData.ideal j).val),
        ∑ χ : (PUnit × PUnit) →* Circle, cost v D S χ / Z ^ parentWidth := by
      rw [mul_div_assoc]
      simp only [Finset.sum_div]
    _ ≤ (s.fiber : ℝ) * ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
        ∑ S : divisorPool (s.pieces v D).rightData.columns
          (fun j => ((s.pieces v D).rightData.ideal j).val),
        ∑ χ : (PUnit × PUnit) →* Circle,
          (H * Z ^ δ) *
            (firstCommonWeight Z v.val.1 v.val.2 *
              (‖(moebius S.val : ℂ)‖ / (Ideal.absNorm S.val : ℝ)) *
                ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖) * Z ^ loss := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro v _
      apply Finset.sum_le_sum
      intro D _
      apply Finset.sum_le_sum
      intro S _
      apply Finset.sum_le_sum
      intro χ _
      apply (hclass v D S χ).trans
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hz.le _)
      exact mul_le_mul_of_nonneg_right (hcoefficient v D)
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg hz.le _)
          (div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))) (norm_nonneg _))
    _ = ((s.fiber : ℝ) * H * Z ^ δ * Z ^ loss) * s.firstTerminalArithmeticMass := by
      simp only [ActualDirectFirstSource.firstTerminalArithmeticMass, Finset.mul_sum,
        mul_assoc, mul_left_comm, mul_comm]
    _ ≤ ((s.fiber : ℝ) * H * Z ^ δ * Z ^ loss) *
        (Cmass * Z ^ δ / (Ideal.absNorm O.oldMask : ℝ)) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by
      have he : loss + ε = δ + loss + δ := by dsimp only [δ]; ring
      rw [he, Real.rpow_add hz, Real.rpow_add hz]
      dsimp only [H]
      ring

/-- Uniform complete direct zero budget. Every class inequality is
constructed here from the actual amplitudes after its first-profile
shift cancels. The first arithmetic carrier is unchanged. -/
theorem actual_direct_second_dual_zero_from_combined_windows
    (k : ℕ) (normBound ε : ℝ) (hN : 0 ≤ normBound) (hε : 0 < ε) :
    ∃ Csum : ℝ, 0 < Csum ∧
    ∀ (Z : ℝ) (hZ : 1 < Z),
    ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ)
      (a : RealParameters) (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X),
    ∀ s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX,
    ∀ R : s.SecondStages (E := E) (hDiff := hDiff),
    ∀ (sTail sZero : Finset (ℕ × ℕ)) (Lmax Nsave decay : ℝ),
    ∀ T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay,
    ∀ (εzero Czero parentWidth loss firstAmplitude kernelBound profileConstant : ℝ)
      (fiberCap : ℕ), 0 ≤ Czero → 0 ≤ firstAmplitude → 0 ≤ kernelBound →
      0 ≤ profileConstant →
    ∀ total shift : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ,
    ∀ O : s.CombinedTerminalOriginalWindows normBound parentWidth firstAmplitude kernelBound total shift,
    ∀ U : R.CombinedZeroAmplitudeWindows T εzero loss profileConstant fiberCap total shift,
      R.dualSecondZeroBudget T (s.canonicalNormalization hZ total) εzero Czero / Z ^ parentWidth ≤
        (s.fiber : ℝ) * fiberCap * Czero * firstAmplitude * kernelBound *
          profileConstant * Csum * Z ^ (loss + ε) / (Ideal.absNorm O.oldMask : ℝ) := by
  obtain ⟨Csum, hCsum, hsum⟩ := combined_direct_class_sum_from_original_windows
    (W := W) (C := C) (hΓ := hΓ) (μv := μv) (finiteTest := finiteTest) k normBound ε hN hε
  refine ⟨Csum, hCsum, ?_⟩
  intro Z hZ ω ψ centered d a t Y₁ Y₂ X hX s R sTail sZero Lmax Nsave decay T
    εzero Czero parentWidth loss firstAmplitude kernelBound profileConstant fiberCap
    hC hfirst hkernel hprofile total shift O U
  let cost := fun v : s.CommonLabel => fun D : ((s.block v).mask s.mask).powerset =>
    (T v D).classZeroBudget
      (fun _ _ => firstLeftAllowance Z (total v D) v.val.1 v.val.2)
      (fun _ _ => firstRightAllowance Z (total v D) v.val.1 v.val.2) εzero Czero
  have hclass (v : s.CommonLabel) (D : ((s.block v).mask s.mask).powerset)
      (S : divisorPool (s.pieces v D).rightData.columns
        (fun j => ((s.pieces v D).rightData.ideal j).val))
      (χ : (PUnit × PUnit) →* Circle) :=
    (T v D).classZeroBudget_le_combined_profiles hZ S χ εzero Czero (total v D)
      parentWidth loss (shift v D) firstAmplitude profileConstant profileConstant
      (U.exponentL v D S χ) (U.exponentR v D S χ) fiberCap
      (idealDivisorCount (v.val.1 ^ 2) ^ k) (idealDivisorCount (v.val.2 ^ 2) ^ k)
      hC hprofile hprofile (U.fiber_left v D S χ) (U.fiber_right v D S χ)
      (U.tuples_left v D S χ) (U.tuples_right v D S χ)
      (U.amplitude_left v D S χ) (U.amplitude_right v D S χ)
      (U.exponent_left v D S χ) (U.exponent_right v D S χ) (O.first_profile v D)
  have h := hsum Z hZ centered d a t Y₁ Y₂ X hX s Czero parentWidth loss
    firstAmplitude kernelBound profileConstant fiberCap hC hfirst hkernel hprofile
    total shift O cost hclass
  simpa only [ActualDirectFirstSource.SecondStages.dualSecondZeroBudget,
    FirstBlockDirectData.SecondStages.DualTerminalCalibration.zeroBudget,
    ActualDirectFirstSource.canonicalNormalization, cost] using h

/-- The complete direct tail uses the same finite arithmetic mass
and original Fourier kernel. Its additional pre-pool degree remains
in the supplied individual decay ledgers, before this summation. -/
theorem actual_direct_second_dual_tail_from_combined_windows
    (k : ℕ) (normBound ε : ℝ) (hN : 0 ≤ normBound) (hε : 0 < ε) :
    ∃ Csum : ℝ, 0 < Csum ∧
    ∀ (Z : ℝ) (hZ : 1 < Z),
    ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ)
      (a : RealParameters) (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X),
    ∀ s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX,
    ∀ R : s.SecondStages (E := E) (hDiff := hDiff),
    ∀ (sTail sZero : Finset (ℕ × ℕ)) (Lmax Nsave decay : ℝ),
    ∀ T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay,
    ∀ (Cerror parentWidth loss firstAmplitude kernelBound profileConstant : ℝ)
      (fiberCap : ℕ), 0 ≤ Cerror → 0 ≤ firstAmplitude → 0 ≤ kernelBound →
      0 ≤ profileConstant →
    ∀ total shift : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ,
    ∀ O : s.CombinedTerminalOriginalWindows normBound parentWidth firstAmplitude kernelBound total shift,
    ∀ U : R.CombinedTailAmplitudeWindows T loss profileConstant fiberCap total shift,
      R.dualSecondTailBudget T (s.canonicalNormalization hZ total) Cerror / Z ^ parentWidth ≤
        (s.fiber : ℝ) * fiberCap * Cerror * firstAmplitude * kernelBound *
          profileConstant * Csum * Z ^ (loss + ε) / (Ideal.absNorm O.oldMask : ℝ) := by
  obtain ⟨Csum, hCsum, hsum⟩ := combined_direct_class_sum_from_original_windows
    (W := W) (C := C) (hΓ := hΓ) (μv := μv) (finiteTest := finiteTest) k normBound ε hN hε
  refine ⟨Csum, hCsum, ?_⟩
  intro Z hZ ω ψ centered d a t Y₁ Y₂ X hX s R sTail sZero Lmax Nsave decay T
    Cerror parentWidth loss firstAmplitude kernelBound profileConstant fiberCap
    hC hfirst hkernel hprofile total shift O U
  let cost := fun v : s.CommonLabel => fun D : ((s.block v).mask s.mask).powerset =>
    (T v D).classTailBudget
      (fun _ _ => firstLeftAllowance Z (total v D) v.val.1 v.val.2)
      (fun _ _ => firstRightAllowance Z (total v D) v.val.1 v.val.2) Cerror
  have hclass (v : s.CommonLabel) (D : ((s.block v).mask s.mask).powerset)
      (S : divisorPool (s.pieces v D).rightData.columns
        (fun j => ((s.pieces v D).rightData.ideal j).val))
      (χ : (PUnit × PUnit) →* Circle) :=
    (T v D).classTailBudget_le_combined_profiles hZ S χ Cerror (total v D)
      parentWidth loss (shift v D) firstAmplitude profileConstant profileConstant
      (U.exponentL v D S χ) (U.exponentR v D S χ) fiberCap
      (idealDivisorCount (v.val.1 ^ 2) ^ k) (idealDivisorCount (v.val.2 ^ 2) ^ k)
      hC hprofile hprofile (U.fiber_left v D S χ) (U.fiber_right v D S χ)
      (U.tuples_left v D S χ) (U.tuples_right v D S χ)
      (U.amplitude_left v D S χ) (U.amplitude_right v D S χ)
      (U.exponent_left v D S χ) (U.exponent_right v D S χ) (O.first_profile v D)
  have h := hsum Z hZ centered d a t Y₁ Y₂ X hX s Cerror parentWidth loss
    firstAmplitude kernelBound profileConstant fiberCap hC hfirst hkernel hprofile
    total shift O cost hclass
  simpa only [ActualDirectFirstSource.SecondStages.dualSecondTailBudget,
    FirstBlockDirectData.SecondStages.DualTerminalCalibration.tailBudget,
    ActualDirectFirstSource.canonicalNormalization, cost] using h

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.combined_direct_class_sum_from_original_windows
#print axioms HeckeSkeleton.Moments.EngineStep.actual_direct_second_dual_zero_from_combined_windows
#print axioms HeckeSkeleton.Moments.EngineStep.actual_direct_second_dual_tail_from_combined_windows
