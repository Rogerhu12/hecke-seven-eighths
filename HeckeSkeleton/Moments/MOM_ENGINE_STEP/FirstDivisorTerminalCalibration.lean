import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstDivisorFrozenCost
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CommonTerminalCalibration

/-!
# First-divisor density in the literal zero and tail calibrations

Every actual column is factored at its original occurrences.  The
frozen atoms contain the first shared divisor, and only their individual
annulus/profile bounds enter the proof.  The remaining windows concern
the literal residual Gram profile, the original ideals, radius and mask.

The zero and tail amplitudes below are computed outputs.  In particular
their inverse first-divisor norm is proved from the actual coefficients,
and the zero-mask sum is bounded from its genuine norm-dilated radii.
No aggregate terminal inequality is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments HeckePort.Moments.Support UniqueFactorizationMonoid
open MeasureTheory

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}

/-- The entire divisor, with its original exponents, is retained in
the extraction of its prime support.  This also handles labels whose
Möbius coefficient is zero, without changing the original carrier. -/
theorem first_divisor_dvd_own_supportExtract
    (S I : Ideal (𝓞 F)) (hI : I ≠ 0) (hSI : S ∣ I) :
    S ∣ supportExtract I (primeSupport S) := by
  have hS : S ≠ 0 := by
    intro hz
    rw [hz, zero_dvd_iff] at hSI
    exact hI hSI
  obtain ⟨J, hIJ⟩ := hSI
  have hJ : J ≠ 0 := by
    intro hz
    apply hI
    rw [hIJ, hz, mul_zero]
  have hself : supportExtract S (primeSupport S) = S := by
    change ((normalizedFactors S).filter (fun P => P ∈ primeSupport S)).prod = S
    rw [Multiset.filter_eq_self.mpr (by
      intro P hP
      exact Multiset.mem_toFinset.mpr hP)]
    exact Ideal.prod_normalizedFactors_eq_self hS
  rw [hIJ, supportExtract_mul S J hS hJ, hself]
  exact dvd_mul_right S _

/-- Original single-column identities and original frozen atoms.
The residual coefficient is the actual factor remaining after those
atoms have been extracted.  No norm bound on a whole coefficient is
part of this input. -/
structure FirstDivisorCoefficientAtoms {ι : Type*}
    (columns : Finset ι) (coefficient : ι → ℂ)
    (S : Ideal (𝓞 F)) (k : ℕ) (B : ℝ) where
  divisor_ne_zero : S ≠ 0
  bound_ge_one : 1 ≤ B
  active : ι → Prop
  atoms : ι → FrozenSourceAtoms A σ Unit ({()} : Finset Unit) k
  rawResidualCoefficient : ι → ℂ
  coefficient_eq : ∀ i ∈ columns,
    coefficient i = if active i then (atoms i).value () * rawResidualCoefficient i else 0
  divisor_dvd : ∀ i ∈ columns, active i → S ∣ (atoms i).ideal
  atom_bound : ∀ i ∈ columns, active i → ∀ j ∈ Finset.univ \ (atoms i).keep,
    (atoms i).annulus j * (atoms i).profile j ≤ B

namespace FirstDivisorCoefficientAtoms

variable {ι : Type*} {columns : Finset ι} {coefficient : ι → ℂ}
variable {Sdiv : Ideal (𝓞 F)} {k : ℕ} {B : ℝ}
variable (W : FirstDivisorCoefficientAtoms (A := A) (σ := σ) columns coefficient Sdiv k B)

def residualCoefficient (i : ι) : ℂ := if W.active i then W.rawResidualCoefficient i else 0

def scalarCost (_W : FirstDivisorCoefficientAtoms (A := A) (σ := σ)
    columns coefficient Sdiv k B) : ℝ := B ^ k / (Ideal.absNorm Sdiv : ℝ)

theorem scalarCost_nonneg : 0 ≤ W.scalarCost :=
  div_nonneg (pow_nonneg (zero_le_one.trans W.bound_ge_one) _) (Nat.cast_nonneg _)

theorem envelope_le (i : ι) (hi : i ∈ columns) (ha : W.active i) :
    (W.atoms i).envelope ≤ B ^ k := by
  calc
    _ ≤ ∏ _j ∈ Finset.univ \ (W.atoms i).keep, B :=
      Finset.prod_le_prod₀
        (fun j _ => mul_nonneg ((W.atoms i).annulus_nonneg j)
          ((W.atoms i).profile_nonneg j)) (W.atom_bound i hi ha)
    _ = B ^ (Finset.univ \ (W.atoms i).keep).card := by rw [Finset.prod_const]
    _ ≤ B ^ k := pow_le_pow_right₀ W.bound_ge_one
      ((Finset.card_le_univ _).trans_eq (Fintype.card_fin k))

theorem atom_norm_sq_le (C : A.GeneralArithmeticContext σ η hS)
    (i : ι) (hi : i ∈ columns) (ha : W.active i) :
    ‖(W.atoms i).value ()‖ ^ 2 ≤ W.scalarCost := by
  exact ((W.atoms i).norm_sq_le_divisor C Sdiv (W.divisor_dvd i hi ha)
    () (Finset.mem_singleton_self ())).trans
      (div_le_div_of_nonneg_right (W.envelope_le i hi ha) (Nat.cast_nonneg _))

/-- The whole residual coefficient stays inside the test profile.
The first divisor is paid only by the original frozen atoms. -/
theorem gram_seminorm_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (C : A.GeneralArithmeticContext σ η hS)
    (i j : ι) (hi : i ∈ columns) (hj : j ∈ columns)
    (p : Seminorm ℂ V) (φ : V) :
    p ((coefficient i * star (coefficient j)) • φ) ≤
      W.scalarCost * p ((W.residualCoefficient i * star (W.residualCoefficient j)) • φ) := by
  by_cases hai : W.active i
  swap
  · simp [W.coefficient_eq i hi, residualCoefficient, hai]
  by_cases haj : W.active j
  swap
  · simp [W.coefficient_eq j hj, residualCoefficient, haj]
  have hB : 0 ≤ B ^ k := pow_nonneg (zero_le_one.trans W.bound_ge_one) _
  have hN : 0 < (Ideal.absNorm Sdiv : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr W.divisor_ne_zero))
  have hpair := paired_scalar_inverse_norm ((W.atoms i).value ()) ((W.atoms j).value ())
    (Ideal.absNorm Sdiv : ℝ) (B ^ k) (B ^ k) hN hB hB
    (W.atom_norm_sq_le (C := C) i hi hai) (W.atom_norm_sq_le (C := C) j hj haj)
  rw [Real.mul_self_sqrt hB] at hpair
  rw [W.coefficient_eq i hi, W.coefficient_eq j hj, if_pos hai, if_pos haj]
  simp only [residualCoefficient, if_pos hai, if_pos haj]
  have he :
      (((W.atoms i).value () * W.rawResidualCoefficient i) *
        star ((W.atoms j).value () * W.rawResidualCoefficient j)) • φ =
      ((W.atoms i).value () * star ((W.atoms j).value ())) •
        ((W.rawResidualCoefficient i * star (W.rawResidualCoefficient j)) • φ) := by
    rw [smul_smul, star_mul]
    congr 1
    ring
  rw [he, map_smul_eq_mul, norm_mul, norm_star]
  exact mul_le_mul_of_nonneg_right hpair (apply_nonneg _ _)

variable {S₁ S₂ : Finset (Ideal (𝓞 F))}
variable {slots : Fin k → Finset (HeightOneSpectrum (𝓞 F))}

/-- Build the column identities from genuine occurrence extraction.
Different original columns may have different frozen support branches.
Both rectangles and their original extra normalizer are preserved. -/
def ofCenteredSupport
    (b : ι → SupportCartesianBranch S₁ S₂ slots (primeSupport Sdiv))
    (chars : FixedChildCharacters F k)
    (X₁ X₂ Y₁ Y₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ v₁ v₂ : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ)
    (bounds : ∀ i, (b i).CommonAtomBounds chars Z length w)
    (x : ∀ i, AllocationColumn F (b i).keep.card)
    (hx : ∀ i ∈ columns, x i ∈ (b i).residualColumns)
    (originalIdeal : ι → A.Exterior)
    (hideal : ∀ i ∈ columns,
      (originalIdeal i).val = allocationColumnIdeal ((b i).reconstruct (x i)))
    (normalizer : ι → ℂ)
    (hcoefficient : ∀ i ∈ columns, coefficient i =
      if Sdiv ∣ (originalIdeal i).val then normalizer i *
        (rawBareSourceCoefficient chars X₁ X₂ Z length w₁ w₂ w ((b i).reconstruct (x i)) -
          rawBareSourceCoefficient chars Y₁ Y₂ Z length v₁ v₂ w ((b i).reconstruct (x i)))
      else 0)
    (hS0 : Sdiv ≠ 0)
    (hB : 1 ≤ B)
    (hatom : ∀ i ∈ columns, Sdiv ∣ (originalIdeal i).val → ∀ j ∈ Finset.univ \ (b i).keep,
      (bounds i).annulus j * (bounds i).profile j ≤ B) :
    FirstDivisorCoefficientAtoms (A := A) (σ := σ) columns coefficient Sdiv k B where
  divisor_ne_zero := hS0
  bound_ge_one := hB
  active i := Sdiv ∣ (originalIdeal i).val
  atoms i := (bounds i).atoms ({()} : Finset Unit)
  rawResidualCoefficient i := normalizer i *
    ((b i).bareResidualCoefficient chars X₁ X₂ Z length w₁ w₂ w (x i) -
      (b i).bareResidualCoefficient chars Y₁ Y₂ Z length v₁ v₂ w (x i))
  coefficient_eq i hi := by
    rw [hcoefficient i hi]
    by_cases hd : Sdiv ∣ (originalIdeal i).val
    swap
    · simp only [if_neg hd]
    simp only [if_pos hd]
    have he : (b i).plainExtract₁ * (b i).plainExtract₂ * (∏ j, (b i).slotExtract j) =
        (extractedExterior (originalIdeal i) (primeSupport Sdiv)).val := by
      rw [← (b i).extract_ideal ((b i).reconstruct (x i))
        ((b i).reconstruct_mem (x i) (hx i hi)), ← hideal i hi]
      rfl
    rw [(b i).raw_centered_bare_extract chars X₁ X₂ Y₁ Y₂ Z length w₁ w₂ v₁ v₂ w
        (x i) (hx i hi),
      (bounds i).atoms_value ({()} : Finset Unit)
        (extractedExterior (originalIdeal i) (primeSupport Sdiv)) he ()]
    ring
  divisor_dvd i hi hd := by
    rw [(bounds i).atoms_ideal ({()} : Finset Unit),
      ← (b i).extract_ideal ((b i).reconstruct (x i))
        ((b i).reconstruct_mem (x i) (hx i hi)), ← hideal i hi]
    exact first_divisor_dvd_own_supportExtract Sdiv (originalIdeal i).val
      (originalIdeal i).property.1 hd
  atom_bound := hatom

end FirstDivisorCoefficientAtoms

variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup F (A.Sf : Set (HeightOneSpectrum (𝓞 F))))]
  [BorelSpace (sLocalNormOneGroup F (A.Sf : Set (HeightOneSpectrum (𝓞 F))))]

/-- A genuine mask divisor dilates the radius upward by an arithmetic
norm at least one.  Its Möbius coefficient has norm at most one. -/
theorem firstZeroDivisorWeight_le_inverse_radius
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R)) :
    firstZeroDivisorWeight radius D ≤ radius.val⁻¹ := by
  have hnorm := one_le_sIntegerElementNorm F (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
    (sIntegerMaskGenerator F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) D)
  have hradius : radius.val ≤
      (sIntegerMaskDilationRadius F A.Sf radius
        (sIntegerMaskGenerator F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) D)).val := by
    change radius.val ≤ radius.val * _
    nlinarith [radius.property]
  have hinverse :
      (sIntegerMaskDilationRadius F A.Sf radius
        (sIntegerMaskGenerator F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) D)).val⁻¹ ≤
      radius.val⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le radius.property hradius
  have hmoebius : ‖(moebius (IdealMobiusMask.primeProduct D) : ℂ)‖ ≤ 1 := by
    unfold UniqueFactorizationMonoid.moebius
    split_ifs <;> simp
  exact (mul_le_mul_of_nonneg_right hmoebius
    (inv_nonneg.mpr (sIntegerMaskDilationRadius F A.Sf radius
      (sIntegerMaskGenerator F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) D)).property.le)).trans
      (by simpa only [one_mul] using hinverse)

theorem sum_firstZeroDivisorWeight_le
    (radius : {r : ℝ // 0 < r}) (mask : Finset (HeightOneSpectrum A.R)) :
    (∑ D ∈ mask.powerset, firstZeroDivisorWeight radius D) ≤
      (2 : ℝ) ^ mask.card * radius.val⁻¹ := by
  calc
    _ ≤ ∑ _D ∈ mask.powerset, radius.val⁻¹ :=
      Finset.sum_le_sum fun D _ => firstZeroDivisorWeight_le_inverse_radius radius D
    _ = _ := by simp

variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent F v = 0}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local notation "V" => mixedEmbedding.euclidean.mixedSpace F

namespace ActualGaussStage

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ}
variable {s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest}
variable {Sdiv : Ideal (𝓞 F)} {slots : ℕ} {B : ℝ}

/-- Raw windows for the actual residual profiles.  The tail record
retains the original ideal-factor tuple and its proved finite fibres.
For the zero term only individual residual seminorms and individual
original ideal norms are supplied. -/
structure ResidualTerminalWindows
    (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
    (W : FirstDivisorCoefficientAtoms (A := A) (σ := σ)
      G.columns G.coefficient Sdiv slots B)
    (sTail sZero : Finset (ℕ × ℕ))
    (k : ℕ) (Z Lmax Nsave decay : ℝ) where
  productExponent : ℝ
  profileExponent : ℝ
  maskExponent : ℝ
  inverseRadiusExponent : ℝ
  tailProfileConstant : ℝ
  zeroProfileConstant : ℝ
  zeroProfileConstant_nonneg : 0 ≤ zeroProfileConstant
  zeroProfileExponent : ℝ
  zeroColumnExponent : ℝ
  windows : SecondTailWindows C G.columns G.columns G.ideal G.ideal
    (fun DE : FirstZeroLabel G.columns G.columns G.ideal G.ideal =>
      canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal DE.val DE.property)
    sTail (fun i j => (W.residualCoefficient i * star (W.residualCoefficient j)) • s.profile)
    s.radius s.mask k Z productExponent profileExponent maskExponent inverseRadiusExponent
    tailProfileConstant
  exponent_bound : secondTailExponent k productExponent profileExponent maskExponent
    inverseRadiusExponent ≤ Lmax
  cutoff_eq : s.cutoff = Z ^ firstTailCutoffExponent Lmax Nsave decay
  profile_zero : s.profile 0 = 0
  residual_zero_profile : ∀ v ∈ firstZeroPairs G.columns G.columns G.ideal G.ideal,
    sZero.sup (schwartzSeminormFamily ℂ V ℂ)
      ((W.residualCoefficient v.2.1 * star (W.residualCoefficient v.2.2)) • s.profile) ≤
        zeroProfileConstant * Z ^ zeroProfileExponent
  column_norm : ∀ i ∈ G.columns, A.exteriorNorm (G.ideal i) ≤ Z ^ zeroColumnExponent

namespace ResidualTerminalWindows

variable {W : FirstDivisorCoefficientAtoms (A := A) (σ := σ)
  G.columns G.coefficient Sdiv slots B}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Z Lmax Nsave decay : ℝ}
variable (T : s.ResidualTerminalWindows W sTail sZero k Z Lmax Nsave decay)

def tailAmplitude : ℝ := W.scalarCost * T.tailProfileConstant

def zeroAmplitude : ℝ :=
  W.scalarCost * T.zeroProfileConstant * Z ^ T.zeroProfileExponent *
    Z ^ T.zeroColumnExponent * ((2 : ℝ) ^ s.mask.card * Z ^ T.inverseRadiusExponent) *
      Real.sqrt (Z ^ T.productExponent)

theorem zeroAmplitude_nonneg : 0 ≤ T.zeroAmplitude := by
  have hz : 0 ≤ Z := zero_le_one.trans T.windows.base_ge_one
  have hscalar := W.scalarCost_nonneg
  have hprofile := T.zeroProfileConstant_nonneg
  unfold zeroAmplitude
  positivity

/-- This constructs the original calibration with both amplitudes
computed from genuine frozen atoms and original residual windows. -/
def calibration : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay where
  productExponent := T.productExponent
  profileExponent := T.profileExponent
  maskExponent := T.maskExponent
  inverseRadiusExponent := T.inverseRadiusExponent
  tailAmplitude := T.tailAmplitude
  zeroAmplitude := T.zeroAmplitude
  zeroAmplitude_nonneg := T.zeroAmplitude_nonneg
  windows :=
    { T.windows with
      amplitude_nonneg := mul_nonneg W.scalarCost_nonneg T.windows.amplitude_nonneg
      profile_seminorm := by
        intro v hv
        have hmem := (mem_firstZeroPairs G.columns G.columns G.ideal G.ideal v).mp hv
        have hp := W.gram_seminorm_le (C := C) v.2.1 v.2.2 hmem.1 hmem.2.1
          (sTail.sup (schwartzSeminormFamily ℂ V ℂ)) s.profile
        exact (hp.trans (mul_le_mul_of_nonneg_left
          (T.windows.profile_seminorm v hv) W.scalarCost_nonneg)).trans_eq (by
            dsimp only [tailAmplitude]
            ring) }
  exponent_bound := T.exponent_bound
  cutoff_eq := T.cutoff_eq
  profile_zero := T.profile_zero
  zero_normalization := by
    intro v hv
    have hmem := (mem_firstZeroPairs G.columns G.columns G.ideal G.ideal v).mp hv
    have hz : 0 < Z := zero_lt_one.trans_le T.windows.base_ge_one
    have hsqrt : Real.sqrt (Z ^ T.productExponent) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (Real.rpow_pos_of_pos hz _))
    have hp := (W.gram_seminorm_le (C := C) v.2.1 v.2.2 hmem.1 hmem.2.1
      (sZero.sup (schwartzSeminormFamily ℂ V ℂ)) s.profile).trans
        (mul_le_mul_of_nonneg_left (T.residual_zero_profile v hv) W.scalarCost_nonneg)
    have hm : (∑ D ∈ s.mask.powerset, firstZeroDivisorWeight s.radius D) ≤
        (2 : ℝ) ^ s.mask.card * Z ^ T.inverseRadiusExponent :=
      (sum_firstZeroDivisorWeight_le s.radius s.mask).trans
        (mul_le_mul_of_nonneg_left T.windows.inverse_radius (by positivity))
    have hnorm : 0 ≤ A.exteriorNorm (G.ideal v.2.1) :=
      (A.exteriorNorm_pos _).le
    have hmask : 0 ≤ ∑ D ∈ s.mask.powerset, firstZeroDivisorWeight s.radius D :=
      Finset.sum_nonneg fun D _ => firstZeroDivisorWeight_nonneg s.radius D
    have hprofile : 0 ≤ W.scalarCost *
        (T.zeroProfileConstant * Z ^ T.zeroProfileExponent) :=
      mul_nonneg W.scalarCost_nonneg
        (mul_nonneg T.zeroProfileConstant_nonneg (Real.rpow_nonneg hz.le _))
    have hbound := mul_le_mul
      (mul_le_mul hp (T.column_norm v.2.1 hmem.1) hnorm hprofile)
      hm hmask (mul_nonneg hprofile (Real.rpow_nonneg hz.le _))
    apply hbound.trans_eq
    dsimp only [zeroAmplitude]
    rw [mul_div_cancel_right₀ _ hsqrt]
    ring

theorem calibration_tailAmplitude : T.calibration.tailAmplitude =
    (B ^ slots / (Ideal.absNorm Sdiv : ℝ)) * T.tailProfileConstant := rfl

theorem calibration_zeroAmplitude : T.calibration.zeroAmplitude =
    (B ^ slots / (Ideal.absNorm Sdiv : ℝ)) * T.zeroProfileConstant *
      Z ^ T.zeroProfileExponent * Z ^ T.zeroColumnExponent *
        ((2 : ℝ) ^ s.mask.card * Z ^ T.inverseRadiusExponent) *
          Real.sqrt (Z ^ T.productExponent) := rfl

/-- The numerical ledger receives the genuine first-divisor factor,
the actual mask cardinality, and only the primitive profile exponents. -/
theorem calibration_zeroAmplitude_power : T.calibration.zeroAmplitude =
    (B ^ slots * T.zeroProfileConstant * (2 : ℝ) ^ s.mask.card /
      (Ideal.absNorm Sdiv : ℝ)) *
      Z ^ (T.zeroProfileExponent + T.zeroColumnExponent + T.inverseRadiusExponent +
        T.productExponent / 2) := by
  have hz : 0 < Z := zero_lt_one.trans_le T.windows.base_ge_one
  have hsqrt : Real.sqrt (Z ^ T.productExponent) = Z ^ (T.productExponent / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hz.le]
    congr 1
    ring
  rw [T.calibration_zeroAmplitude, hsqrt]
  simp only [Real.rpow_add hz]
  ring

end ResidualTerminalWindows
end ActualGaussStage
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstDivisorCoefficientAtoms.ofCenteredSupport
#print axioms HeckeSkeleton.Moments.EngineStep.first_divisor_dvd_own_supportExtract
#print axioms HeckeSkeleton.Moments.EngineStep.sum_firstZeroDivisorWeight_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.ResidualTerminalWindows.calibration
