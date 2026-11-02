import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TailsOriginalAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalParentTuples
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.TailBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstBlockMaskCardinality

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Physical original support bounds for the V2 tail proof

A nonzero whole coefficient has a nonzero original rectangle. The
support window therefore bounds its whole ideal using the product of
the two actual plain scales. Zero columns remain in every public
source; the tail proof may omit their zero contributions when counting.

The first physical mask and periodic modulus are bounded by divisors
of those same original ideals. No transformed estimate is assumed.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

open EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support HeckePort.Moments.Active

variable {K : Type} [Field K] [NumberField K]

namespace ScalarValues

variable {Q : Type*} {ω ψ : HeckeCharacter K}
variable {d : MomentData K ω ψ} {a : RealParameters} {Z t Y₁ Y₂ : ℝ}
variable {raw : ParentRawAtoms Q d a Z t Y₁ Y₂} (values : raw.ConstantValues)

/-- A nonzero centered coefficient has a nonzero literal rectangle.
The comparison rectangle can occur only in the centered case. -/
theorem tailsV2_coefficient_ne_zero_has_rectangle
    (centered : Bool) (v : raw.Column) (hv : values.coefficient centered v ≠ 0) :
    ∃ comparison : Bool, (comparison = true → centered = true) ∧
      values.rectangle comparison v ≠ 0 := by
  by_cases hfalse : values.rectangle false v ≠ 0
  · exact ⟨false, by simp, hfalse⟩
  · have hz : values.rectangle false v = 0 := not_not.mp hfalse
    cases centered with
    | false => exact False.elim (hv (by simp [ParentRawAtoms.ConstantValues.coefficient, hz]))
    | true =>
        refine ⟨true, by simp, ?_⟩
        intro htrue
        exact hv (by simp [ParentRawAtoms.ConstantValues.coefficient, hz, htrue])

end ScalarValues

namespace ScalarAtoms

section LiteralRectangle

variable {Q : Type*} {ω ψ : HeckeCharacter K}
variable {d : MomentData K ω ψ} {a : RealParameters} {Z t Y₁ Y₂ : ℝ}
variable (atoms : ParentConstantAtoms Q d a Z t)

/-- Nonvanishing is extracted from the actual scalar product, with all
prime occurrences retained, including the empty product. -/
theorem tailsV2_rectangle_profiles_ne_zero
    (comparison : Bool) (v : (atoms.raw Y₁ Y₂).Column)
    (hv : (atoms.values Y₁ Y₂).rectangle comparison v ≠ 0) :
    atoms.leftProfile (idealNorm K v.1.1 / (if comparison then Y₁ else Z ^ a.n₁)) ≠ 0 ∧
    atoms.rightProfile (idealNorm K v.1.2 / (if comparison then Y₂ else Z ^ a.n₂)) ≠ 0 ∧
    ∀ i, (d.geometry.slots i).profile t
      ((Ideal.absNorm (v.2 i).asIdeal : ℝ) / Z ^ (d.geometry.slots i).length) ≠ 0 := by
  change atoms.leftValue (if comparison then Y₁ else Z ^ a.n₁) v.1.1 *
    atoms.rightValue (if comparison then Y₂ else Z ^ a.n₂) v.1.2 *
      (∏ i, atoms.primeValue i (v.2 i)) ≠ 0 at hv
  obtain ⟨hplain, hprime⟩ := mul_ne_zero_iff.mp hv
  obtain ⟨hleft, hright⟩ := mul_ne_zero_iff.mp hplain
  refine ⟨?_, ?_, ?_⟩
  · change (Real.sqrt (if comparison then Y₁ else Z ^ a.n₁) : ℂ)⁻¹ *
      (atoms.leftArithmetic v.1.1 * atoms.leftProfile
        (idealNorm K v.1.1 / (if comparison then Y₁ else Z ^ a.n₁))) ≠ 0 at hleft
    exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hleft).2).2
  · change (Real.sqrt (if comparison then Y₂ else Z ^ a.n₂) : ℂ)⁻¹ *
      (atoms.rightArithmetic v.1.2 * atoms.rightProfile
        (idealNorm K v.1.2 / (if comparison then Y₂ else Z ^ a.n₂))) ≠ 0 at hright
    exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hright).2).2
  · intro i
    have hi := Finset.prod_ne_zero_iff.mp hprime i (Finset.mem_univ i)
    change (Real.sqrt (Z ^ (d.geometry.slots i).length) : ℂ)⁻¹ *
      (atoms.primeArithmetic i (v.2 i) * (d.geometry.slots i).profile t
        ((Ideal.absNorm (v.2 i).asIdeal : ℝ) / Z ^ (d.geometry.slots i).length)) ≠ 0 at hi
    exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hi).2).2

variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)} {amplitude : ℝ}
variable (profiles : RawProfileWindow rowDomain heightDomain window orders d amplitude)

include profiles

/-- Each norm is paid by the corresponding profile in this single
nonzero rectangle. The equality of the two plain-scale products is used
only after the individual support bounds; no coordinatewise comparison
between a comparison scale and a main scale is required. -/
theorem tailsV2_original_active_rectangle_column_norm_le_annulus
    (annulus : ℝ) (hannulus : 0 ≤ annulus) (hZ : 0 < Z)
    (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Iic annulus)
    (comparison : Bool)
    (hleftScale : 0 < (if comparison then Y₁ else Z ^ a.n₁))
    (hrightScale : 0 < (if comparison then Y₂ else Z ^ a.n₂))
    (hscaleProduct : (if comparison then Y₁ else Z ^ a.n₁) *
      (if comparison then Y₂ else Z ^ a.n₂) = Z ^ (a.n₁ + a.n₂))
    (v : (atoms.raw Y₁ Y₂).Column) (hv : v ∈ (atoms.raw Y₁ Y₂).columns)
    (hrectangle : (atoms.values Y₁ Y₂).rectangle comparison v ≠ 0) :
    (Ideal.absNorm ((atoms.raw Y₁ Y₂).columnIdeal v) : ℝ) ≤
      annulus ^ (d.geometry.slotCount + 2) *
        Z ^ (a.n₁ + a.n₂ + d.geometry.totalLength) := by
  have hm := Finset.mem_product.mp hv
  have hplain := Finset.mem_product.mp hm.1
  obtain ⟨u, hu, _⟩ := Finset.mem_biUnion.mp hplain.1
  have hprofiles := ScalarAtoms.tailsV2_rectangle_profiles_ne_zero atoms comparison v hrectangle
  have hleftRep : profiles.leftRep u t
      (idealNorm K v.1.1 / (if comparison then Y₁ else Z ^ a.n₁)) ≠ 0 := by
    simpa only [← atoms.left_profile u hu, profiles.left_eq] using hprofiles.1
  have hrightRep : profiles.rightRep u t
      (idealNorm K v.1.2 / (if comparison then Y₂ else Z ^ a.n₂)) ≠ 0 := by
    simpa only [← atoms.right_profile u hu, profiles.right_eq] using hprofiles.2.1
  have hleft : idealNorm K v.1.1 ≤ annulus * (if comparison then Y₁ else Z ^ a.n₁) :=
    (div_le_iff₀ hleftScale).mp
      (hwindow (profiles.left_support u (hrows u hu) t ht hleftRep))
  have hright : idealNorm K v.1.2 ≤ annulus * (if comparison then Y₂ else Z ^ a.n₂) :=
    (div_le_iff₀ hrightScale).mp
      (hwindow (profiles.right_support u (hrows u hu) t ht hrightRep))
  have hprime (i : Fin d.geometry.slotCount) :
      (Ideal.absNorm (v.2 i).asIdeal : ℝ) ≤ annulus * Z ^ (d.geometry.slots i).length := by
    have hi : profiles.primeRep i t
        ((Ideal.absNorm (v.2 i).asIdeal : ℝ) / Z ^ (d.geometry.slots i).length) ≠ 0 := by
      simpa only [profiles.prime_eq] using hprofiles.2.2 i
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp
      (hwindow (profiles.prime_support i t ht hi))
  have hprod : (∏ i, (Ideal.absNorm (v.2 i).asIdeal : ℝ)) ≤
      ∏ i, annulus * Z ^ (d.geometry.slots i).length :=
    Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun i _ => hprime i)
  calc
    _ = (idealNorm K v.1.1 * idealNorm K v.1.2) *
        ∏ i, (Ideal.absNorm (v.2 i).asIdeal : ℝ) := by
      simp only [ParentRawAtoms.columnIdeal, idealNorm, map_mul, map_prod,
        Nat.cast_mul, Nat.cast_prod]
    _ ≤ ((annulus * (if comparison then Y₁ else Z ^ a.n₁)) *
          (annulus * (if comparison then Y₂ else Z ^ a.n₂))) *
        ∏ i, annulus * Z ^ (d.geometry.slots i).length :=
      mul_le_mul
        (mul_le_mul hleft hright (idealNorm_pos K _).le
          (mul_nonneg hannulus hleftScale.le)) hprod
        (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))
        (mul_nonneg (mul_nonneg hannulus hleftScale.le)
          (mul_nonneg hannulus hrightScale.le))
    _ = annulus ^ (d.geometry.slotCount + 2) *
        (((if comparison then Y₁ else Z ^ a.n₁) *
          (if comparison then Y₂ else Z ^ a.n₂)) *
            Z ^ (∑ i, (d.geometry.slots i).length)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, ← Real.rpow_sum_of_pos hZ, pow_add, pow_two]
      ring
    _ = _ := by
      rw [hscaleProduct, ← Real.rpow_add hZ]
      rfl

end LiteralRectangle

section ActualExteriorCarrier

variable {A : SArithmeticData K} {Γ : Subgroup A.U}
variable {ω ψ : HeckeCharacter K} {d : MomentData K ω ψ}
variable {a : RealParameters} {Z t Y₁ Y₂ : ℝ}
variable (atoms : ParentConstantAtoms
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) d a Z t)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)} {amplitude : ℝ}
variable (profiles : RawProfileWindow rowDomain heightDomain window orders d amplitude)

include profiles

/-- The complete original coefficient determines which actual
rectangle supplies the sharp whole-column norm. Empty original row or
column carriers cause no extra existence premise. -/
theorem tailsV2_original_active_column_norm_le_annulus
    (annulus : ℝ) (hannulus : 0 ≤ annulus) (hZ : 0 < Z)
    (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Iic annulus)
    (centered : Bool) (hY₁ : centered = true → 0 ≤ Y₁)
    (hcomparison : centered = true → Y₁ * Y₂ = Z ^ (a.n₁ + a.n₂))
    (v : (atoms.raw Y₁ Y₂).Column) (hv : v ∈ (atoms.raw Y₁ Y₂).exteriorColumns)
    (hcoefficient : (atoms.values Y₁ Y₂).coefficient centered v ≠ 0) :
    (Ideal.absNorm ((atoms.raw Y₁ Y₂).columnExterior v).val : ℝ) ≤
      annulus ^ (d.geometry.slotCount + 2) *
        Z ^ (a.n₁ + a.n₂ + d.geometry.totalLength) := by
  rw [(atoms.raw Y₁ Y₂).columnExterior_val_of_mem v hv]
  obtain ⟨comparison, hallowed, hrectangle⟩ :=
    ScalarValues.tailsV2_coefficient_ne_zero_has_rectangle (atoms.values Y₁ Y₂) centered v hcoefficient
  have hmem : v ∈ (atoms.raw Y₁ Y₂).columns := (Finset.mem_filter.mp hv).1
  cases comparison with
  | false =>
      exact ScalarAtoms.tailsV2_original_active_rectangle_column_norm_le_annulus atoms profiles annulus hannulus hZ
        hrows ht hwindow false (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _)
        (by simpa only [Bool.false_eq_true, if_false] using
          (Real.rpow_add hZ a.n₁ a.n₂).symm) v hmem hrectangle
  | true =>
      have hc : centered = true := hallowed rfl
      have hproduct : 0 < Y₁ * Y₂ := by
        rw [hcomparison hc]
        exact Real.rpow_pos_of_pos hZ _
      have hscales : 0 < Y₁ ∧ 0 < Y₂ := by
        rcases mul_pos_iff.mp hproduct with hpos | hneg
        · exact hpos
        · exact False.elim ((not_lt_of_ge (hY₁ hc)) hneg.1)
      exact ScalarAtoms.tailsV2_original_active_rectangle_column_norm_le_annulus atoms profiles annulus hannulus hZ
        hrows ht hwindow true hscales.1 hscales.2 (hcomparison hc) v hmem hrectangle


end ActualExteriorCarrier
end ScalarAtoms
/-- Element divisibility gives norm monotonicity because the quotient
is a nonzero S-integer and has norm at least one. -/
theorem tailsV2_sIntegerElementNorm_le_of_dvd
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (d c : Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)
    (hd : d ≠ 0) (hc : c ≠ 0) (h : d ∣ c) :
    (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨d, hd⟩).val ≤
      (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨c, hc⟩).val := by
  obtain ⟨x, hx⟩ := h
  have hx0 : x ≠ 0 := by
    intro hzero
    apply hc
    rw [hx, hzero, mul_zero]
  have he : (⟨c, hc⟩ : NonzeroRingElements
      (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)) =
      sIntegerNonzeroMul K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨d, hd⟩ ⟨x, hx0⟩ :=
    Subtype.ext hx
  rw [he, sIntegerElementNorm_nonzeroMul]
  exact le_mul_of_one_le_right
    (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨d, hd⟩).property.le
    (one_le_sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨x, hx0⟩)

theorem tailsV2_physical_ideal_norm_le_of_dvd
    (D I : Ideal (𝓞 K)) (hI : I ≠ 0) (h : D ∣ I) :
    (Ideal.absNorm D : ℝ) ≤ (Ideal.absNorm I : ℝ) := by
  have hpos : 0 < Ideal.absNorm I :=
    Nat.pos_of_ne_zero (by simpa only [Ideal.absNorm_eq_zero_iff] using hI)
  exact_mod_cast Nat.le_of_dvd hpos
    (Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd h))

variable {A : SArithmeticData K}

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}

namespace PhysicalBlock

variable (b : FirstCommonCharacterBlock fullI fullJ DE)

/-- The complete principal first mask divides a generator of the
original common ideal, independent of its unit normalization. -/
theorem tailsV2_principal_mask_generator_dvd_common
    (g : A.R) (hg : A.Generates (primePowerProduct b.primes b.leftMultiplicity) g) :
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (b.mask ∅)).val ∣ g := by
  change IdealMobiusMask.maskGenerator (b.mask ∅) ∣ g
  rw [IdealMobiusMask.maskGenerator_dvd_iff, IdealMobiusMask.mem_primeProduct]
  intro p hp
  have hp' : p ∈ firstPrincipalPrimeMask b.primes b.leftMultiplicity b.rightMultiplicity := by
    simpa only [FirstCommonCharacterBlock.mask, Finset.empty_union] using hp
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp'
  have hd : (primeIdeal (b.primes i)).val ∣
      (primePowerProduct b.primes b.leftMultiplicity).val := by
    rw [b.common_left]
    exact b.originalCommonPrimeData.divides i (Finset.mem_univ i)
  have hle : A.extendIdeal (primePowerProduct b.primes b.leftMultiplicity) ≤
      A.extendIdeal (primeIdeal (b.primes i)) :=
    Ideal.map_mono (Ideal.le_of_dvd hd)
  apply hle
  rw [← hg.2]
  exact Ideal.mem_span_singleton_self g

/-- The physical mask norm is bounded by the actual complete left
common ideal, rather than by a supplied mask estimate. -/
theorem tailsV2_principal_mask_norm_le_common
    (C : A.GeneralArithmeticContext σ η hS) :
    (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (b.mask ∅))).val ≤
        (Ideal.absNorm DE.1 : ℝ) := by
  obtain ⟨g, u, hg, hu, hallowed⟩ :=
    C.allowed_integral (primePowerProduct b.primes b.leftMultiplicity)
  have hnorm := tailsV2_sIntegerElementNorm_le_of_dvd A.Sf
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (b.mask ∅)).val
    g (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (b.mask ∅)).property
    hg.1 (PhysicalBlock.tailsV2_principal_mask_generator_dvd_common b g hg)
  rw [generates_sIntegerElementNorm _ _ hg, b.common_left] at hnorm
  exact hnorm

theorem tailsV2_principal_mask_norm_le_original_column
    (C : A.GeneralArithmeticContext σ η hS)
    (left : Finset ι) (i : ι) (hi : i ∈ b.leftColumns left) :
    (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (b.mask ∅))).val ≤
        (Ideal.absNorm (fullI i).val : ℝ) := by
  apply (PhysicalBlock.tailsV2_principal_mask_norm_le_common b C).trans
  apply tailsV2_physical_ideal_norm_le_of_dvd DE.1 (fullI i).val (fullI i).property.1
  rw [← b.common_left]
  exact ⟨(b.leftResidual i).val, b.left_reconstruct left i hi⟩

variable {Γ : Subgroup A.U}
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)

/-- Gating does not change the modulus. Its norm is exactly that of
the two original residual ideals times the actual active radical. -/
theorem tailsV2_first_modulus_norm
    (C : A.GeneralArithmeticContext σ η hS)
    (profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (i : ι) (j : κ) :
    (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      ⟨(b.pair hΓ C profiles i j).modulus,
        (b.pair hΓ C profiles i j).modulus_ne_zero⟩).val =
      (Ideal.absNorm ((b.leftResidual i).val * ((b.rightResidual j).val *
        (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity).val)) : ℝ) := by
  change (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
    (sIntegerNonzeroMul K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      ⟨b.leftGenerator i, (b.left_generates i).1⟩
      (sIntegerNonzeroMul K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        ⟨b.rightGenerator j, (b.right_generates j).1⟩
        ⟨firstActiveGenerator C b.primes b.leftMultiplicity b.rightMultiplicity,
          (firstActiveGenerator_generates C b.primes b.leftMultiplicity b.rightMultiplicity).1⟩))).val = _
  rw [sIntegerElementNorm_nonzeroMul, sIntegerElementNorm_nonzeroMul,
    generates_sIntegerElementNorm _ _ (b.left_generates i),
    generates_sIntegerElementNorm _ _ (b.right_generates j),
    generates_sIntegerElementNorm _ _
      (firstActiveGenerator_generates C b.primes b.leftMultiplicity b.rightMultiplicity)]
  simp only [map_mul, Nat.cast_mul]

/-- The actual first modulus ideal divides the full original pair.
Only existing common and residual factors occur in the quotient. -/
theorem tailsV2_first_modulus_norm_le_original_product
    (C : A.GeneralArithmeticContext σ η hS)
    (left : Finset ι) (right : Finset κ)
    (profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (i : ι) (hi : i ∈ b.leftColumns left) (j : κ) (hj : j ∈ b.rightColumns right) :
    (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      ⟨(b.pair hΓ C profiles i j).modulus,
        (b.pair hΓ C profiles i j).modulus_ne_zero⟩).val ≤
      (Ideal.absNorm ((fullI i).val * (fullJ j).val) : ℝ) := by
  rw [PhysicalBlock.tailsV2_first_modulus_norm b hΓ C profiles i j]
  apply tailsV2_physical_ideal_norm_le_of_dvd _ _
    (mul_ne_zero (fullI i).property.1 (fullJ j).property.1)
  obtain ⟨T, hT⟩ := firstActiveIdeal_dvd_common b.primes
    b.leftMultiplicity b.rightMultiplicity b.left_positive
  refine ⟨T * (primePowerProduct b.primes b.rightMultiplicity).val, ?_⟩
  rw [b.left_reconstruct left i hi, b.right_reconstruct right j hj, hT]
  ac_rfl

end PhysicalBlock

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

