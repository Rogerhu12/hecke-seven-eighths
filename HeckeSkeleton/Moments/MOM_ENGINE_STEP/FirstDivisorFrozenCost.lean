import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCommonAtomBinding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.GaussPhaseTerminal

/-!
# The first shared divisor is paid by its actual frozen atoms

The first Möbius divisor restricts both original columns.  Extracting
its prime support from those original occurrences puts that divisor
inside each actual frozen ideal.  The two squared scalar bounds then
give one full inverse divisor norm in the original Gram-profile
seminorm.  Both complete centered coefficients retain their original
two rectangles, prime factors and extra Gauss normalizers.

This is the pointwise profile input for a zero/tail calibration.  It
does not introduce a second-divisor carrier or an assumed terminal
bound to manufacture the first-divisor density.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum WholeAllocation
open UniqueFactorizationMonoid

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

/-- A squarefree divisor is entirely inside extraction of its own
prime support, including every selected prime in a repeated slot. -/
theorem first_divisor_dvd_supportExtract
    (S I : Ideal (𝓞 F)) (hS : Squarefree S) (hI : I ≠ 0) (hSI : S ∣ I) :
    S ∣ supportExtract I (primeSupport S) := by
  have hsub : primeSupport S ⊆ primeSupport (supportExtract I (primeSupport S)) := by
    rw [supportExtract_support]
    intro p hp
    exact Finset.mem_inter.mpr ⟨squarefree_divisor_support hI hS hSI hp, hp⟩
  simpa only [squarefree_support_product_self hS] using
    support_product_dvd (supportExtract_ne_zero I (primeSupport S)) hsub

namespace FrozenSourceAtoms

variable {H : Type*} {rows : Finset H} {k : ℕ}

/-- The inverse norm is derived from literal divisibility of the
computed frozen ideal, using the individual atom estimates. -/
theorem norm_sq_le_divisor (W : FrozenSourceAtoms A σ H rows k)
    (C : A.GeneralArithmeticContext σ η hS)
    (S : Ideal (𝓞 F)) (hdiv : S ∣ W.ideal) (h : H) (hh : h ∈ rows) :
    ‖W.value h‖ ^ 2 ≤ W.envelope / (Ideal.absNorm S : ℝ) := by
  have hS : S ≠ 0 := by
    intro hz
    rw [hz, zero_dvd_iff] at hdiv
    exact W.ideal_ne_zero hdiv
  exact (W.norm_sq_le C h hh).trans
    (div_le_div_of_nonneg_left W.envelope_nonneg
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hS)))
      (ideal_norm_le_of_dvd W.ideal_ne_zero hdiv))

variable {H' : Type*} {rows' : Finset H'} {l : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The actual complete Gram coefficient and its original Schwartz
profile acquire the first divisor denominator exactly once.  The
residual coefficient is still literal on the right. -/
theorem gram_seminorm_le_divisor
    (left : FrozenSourceAtoms A σ H rows k)
    (right : FrozenSourceAtoms A σ H' rows' l)
    (C : A.GeneralArithmeticContext σ η hS)
    (S : Ideal (𝓞 F)) (hleft : S ∣ left.ideal) (hright : S ∣ right.ideal)
    (h : H) (hh : h ∈ rows) (h' : H') (hh' : h' ∈ rows')
    (p : Seminorm ℂ V) (φ : V) (c d : ℂ) :
    p (((left.value h * c) * star (right.value h' * d)) • φ) ≤
      (Real.sqrt left.envelope * Real.sqrt right.envelope / (Ideal.absNorm S : ℝ)) *
        p ((c * star d) • φ) := by
  have hS : S ≠ 0 := by
    intro hz
    rw [hz, zero_dvd_iff] at hleft
    exact left.ideal_ne_zero hleft
  have hscalar := paired_scalar_inverse_norm (left.value h) (right.value h')
    (Ideal.absNorm S : ℝ) left.envelope right.envelope
    (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hS)))
    left.envelope_nonneg right.envelope_nonneg
    (left.norm_sq_le_divisor C S hleft h hh)
    (right.norm_sq_le_divisor C S hright h' hh')
  have he : ((left.value h * c) * star (right.value h' * d)) • φ =
      (left.value h * star (right.value h')) • ((c * star d) • φ) := by
    rw [smul_smul, star_mul]
    congr 1
    ring
  rw [he, map_smul_eq_mul, norm_mul, norm_star]
  exact mul_le_mul_of_nonneg_right hscalar (apply_nonneg _ _)

end FrozenSourceAtoms

namespace SupportCartesianBranch

variable {k l : ℕ} {Sdiv : Ideal (𝓞 F)}
variable {S₁ S₂ T₁ T₂ : Finset (Ideal (𝓞 F))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 F))}
variable {T : Fin l → Finset (HeightOneSpectrum (𝓞 F))}

theorem first_divisor_dvd_atoms
    (b : SupportCartesianBranch S₁ S₂ S (primeSupport Sdiv))
    {chars : FixedChildCharacters F k} {Z : ℝ} {length : Fin k → ℝ}
    {w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ}
    (B : b.CommonAtomBounds chars Z length w)
    (x : AllocationColumn F k) (hx : x ∈ b.originalColumns)
    (I : A.Exterior) (hI : I.val = allocationColumnIdeal x)
    (hS : Squarefree Sdiv) (hdiv : Sdiv ∣ I.val)
    {H : Type*} (rows : Finset H) :
    Sdiv ∣ (B.atoms (A := A) (σ := σ) rows).ideal := by
  rw [B.atoms_ideal rows, ← b.extract_ideal x hx, ← hI]
  exact first_divisor_dvd_supportExtract Sdiv I.val hS I.property.1 hdiv

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The actual original support tuples derive both frozen divisibility
facts.  The sole bound on a test profile is the seminorm itself. -/
theorem first_divisor_bare_gram_seminorm_le
    (left : SupportCartesianBranch S₁ S₂ S (primeSupport Sdiv))
    (right : SupportCartesianBranch T₁ T₂ T (primeSupport Sdiv))
    {charsL : FixedChildCharacters F k} {charsR : FixedChildCharacters F l}
    {ZL ZR : ℝ} {lengthL : Fin k → ℝ} {lengthR : Fin l → ℝ}
    {wL : Fin k → HeightOneSpectrum (𝓞 F) → ℂ}
    {wR : Fin l → HeightOneSpectrum (𝓞 F) → ℂ}
    (BL : left.CommonAtomBounds charsL ZL lengthL wL)
    (BR : right.CommonAtomBounds charsR ZR lengthR wR)
    (C : A.GeneralArithmeticContext σ η hS)
    (x : AllocationColumn F k) (hx : x ∈ left.originalColumns)
    (y : AllocationColumn F l) (hy : y ∈ right.originalColumns)
    (I J : A.Exterior) (hI : I.val = allocationColumnIdeal x)
    (hJ : J.val = allocationColumnIdeal y)
    (hSdiv : Squarefree Sdiv) (hSI : Sdiv ∣ I.val) (hSJ : Sdiv ∣ J.val)
    (p : Seminorm ℂ V) (φ : V) (c d : ℂ) :
    p (((left.bareCommonScalar charsL ZL lengthL wL * c) *
      star (right.bareCommonScalar charsR ZR lengthR wR * d)) • φ) ≤
      (Real.sqrt (BL.atoms (A := A) (σ := σ) ({()} : Finset Unit)).envelope *
        Real.sqrt (BR.atoms (A := A) (σ := σ) ({()} : Finset Unit)).envelope /
          (Ideal.absNorm Sdiv : ℝ)) * p ((c * star d) • φ) := by
  let rows : Finset Unit := {()}
  have hL : left.plainExtract₁ * left.plainExtract₂ * (∏ i, left.slotExtract i) =
      (extractedExterior I (primeSupport Sdiv)).val := by
    rw [← left.extract_ideal x hx, ← hI]
    rfl
  have hR : right.plainExtract₁ * right.plainExtract₂ * (∏ i, right.slotExtract i) =
      (extractedExterior J (primeSupport Sdiv)).val := by
    rw [← right.extract_ideal y hy, ← hJ]
    rfl
  have hpair := FrozenSourceAtoms.gram_seminorm_le_divisor
    (BL.atoms (A := A) (σ := σ) rows) (BR.atoms (A := A) (σ := σ) rows)
    C Sdiv (left.first_divisor_dvd_atoms BL x hx I hI hSdiv hSI rows)
    (right.first_divisor_dvd_atoms BR y hy J hJ hSdiv hSJ rows)
    () (Finset.mem_singleton_self ()) () (Finset.mem_singleton_self ()) p φ c d
  rw [BL.atoms_value rows (extractedExterior I (primeSupport Sdiv)) hL (),
    BR.atoms_value rows (extractedExterior J (primeSupport Sdiv)) hR ()] at hpair
  exact hpair

/-- Both original rectangles share the same first-divisor scalar. -/
theorem raw_centered_bare_extract
    (b : SupportCartesianBranch S₁ S₂ S (primeSupport Sdiv))
    (chars : FixedChildCharacters F k)
    (X₁ X₂ Y₁ Y₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ v₁ v₂ : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ)
    (y : AllocationColumn F b.keep.card) (hy : y ∈ b.residualColumns) :
    (rawBareSourceCoefficient chars X₁ X₂ Z length w₁ w₂ w (b.reconstruct y) -
      rawBareSourceCoefficient chars Y₁ Y₂ Z length v₁ v₂ w (b.reconstruct y)) =
      b.bareCommonScalar chars Z length w *
        (b.bareResidualCoefficient chars X₁ X₂ Z length w₁ w₂ w y -
          b.bareResidualCoefficient chars Y₁ Y₂ Z length v₁ v₂ w y) := by
  rw [b.raw_bare_extract chars X₁ X₂ Z length w₁ w₂ w y hy,
    b.raw_bare_extract chars Y₁ Y₂ Z length v₁ v₂ w y hy, mul_sub]

/-- Apply the frozen-divisor estimate to the original complete
centered coefficients themselves.  Their remaining Gram profile has
the actual quotient plain scales and the retained original slots. -/
theorem first_divisor_centered_gram_seminorm_le
    (left : SupportCartesianBranch S₁ S₂ S (primeSupport Sdiv))
    (right : SupportCartesianBranch T₁ T₂ T (primeSupport Sdiv))
    (charsL : FixedChildCharacters F k) (charsR : FixedChildCharacters F l)
    (XL₁ XL₂ YL₁ YL₂ XR₁ XR₂ YR₁ YR₂ ZL ZR : ℝ)
    (lengthL : Fin k → ℝ) (lengthR : Fin l → ℝ)
    (wL₁ wL₂ vL₁ vL₂ wR₁ wR₂ vR₁ vR₂ : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ)
    (wL : Fin k → HeightOneSpectrum (𝓞 F) → ℂ)
    (wR : Fin l → HeightOneSpectrum (𝓞 F) → ℂ)
    (BL : left.CommonAtomBounds charsL ZL lengthL wL)
    (BR : right.CommonAtomBounds charsR ZR lengthR wR)
    (C : A.GeneralArithmeticContext σ η hS)
    (x : AllocationColumn F left.keep.card) (hx : x ∈ left.residualColumns)
    (y : AllocationColumn F right.keep.card) (hy : y ∈ right.residualColumns)
    (I J : A.Exterior) (hI : I.val = allocationColumnIdeal (left.reconstruct x))
    (hJ : J.val = allocationColumnIdeal (right.reconstruct y))
    (hSdiv : Squarefree Sdiv) (hSI : Sdiv ∣ I.val) (hSJ : Sdiv ∣ J.val)
    (p : Seminorm ℂ V) (φ : V) (normalL normalR : ℂ) :
    let originalL := normalL *
      (rawBareSourceCoefficient charsL XL₁ XL₂ ZL lengthL wL₁ wL₂ wL (left.reconstruct x) -
        rawBareSourceCoefficient charsL YL₁ YL₂ ZL lengthL vL₁ vL₂ wL (left.reconstruct x))
    let originalR := normalR *
      (rawBareSourceCoefficient charsR XR₁ XR₂ ZR lengthR wR₁ wR₂ wR (right.reconstruct y) -
        rawBareSourceCoefficient charsR YR₁ YR₂ ZR lengthR vR₁ vR₂ wR (right.reconstruct y))
    let residualL := normalL *
      (left.bareResidualCoefficient charsL XL₁ XL₂ ZL lengthL wL₁ wL₂ wL x -
        left.bareResidualCoefficient charsL YL₁ YL₂ ZL lengthL vL₁ vL₂ wL x)
    let residualR := normalR *
      (right.bareResidualCoefficient charsR XR₁ XR₂ ZR lengthR wR₁ wR₂ wR y -
        right.bareResidualCoefficient charsR YR₁ YR₂ ZR lengthR vR₁ vR₂ wR y)
    p ((originalL * star originalR) • φ) ≤
      (Real.sqrt (BL.atoms (A := A) (σ := σ) ({()} : Finset Unit)).envelope *
        Real.sqrt (BR.atoms (A := A) (σ := σ) ({()} : Finset Unit)).envelope /
          (Ideal.absNorm Sdiv : ℝ)) * p ((residualL * star residualR) • φ) := by
  dsimp only
  rw [left.raw_centered_bare_extract charsL XL₁ XL₂ YL₁ YL₂ ZL lengthL
    wL₁ wL₂ vL₁ vL₂ wL x hx,
    right.raw_centered_bare_extract charsR XR₁ XR₂ YR₁ YR₂ ZR lengthR
      wR₁ wR₂ vR₁ vR₂ wR y hy]
  have hleft (c : ℂ) : normalL * (left.bareCommonScalar charsL ZL lengthL wL * c) =
      left.bareCommonScalar charsL ZL lengthL wL * (normalL * c) := by ring
  have hright (c : ℂ) : normalR * (right.bareCommonScalar charsR ZR lengthR wR * c) =
      right.bareCommonScalar charsR ZR lengthR wR * (normalR * c) := by ring
  rw [hleft, hright]
  exact first_divisor_bare_gram_seminorm_le left right BL BR C
    (left.reconstruct x) (left.reconstruct_mem x hx)
    (right.reconstruct y) (right.reconstruct_mem y hy) I J hI hJ hSdiv hSI hSJ p φ _ _

end SupportCartesianBranch
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.first_divisor_dvd_supportExtract
#print axioms HeckeSkeleton.Moments.EngineStep.FrozenSourceAtoms.gram_seminorm_le_divisor
#print axioms HeckeSkeleton.Moments.EngineStep.SupportCartesianBranch.first_divisor_bare_gram_seminorm_le
#print axioms HeckeSkeleton.Moments.EngineStep.SupportCartesianBranch.first_divisor_centered_gram_seminorm_le
