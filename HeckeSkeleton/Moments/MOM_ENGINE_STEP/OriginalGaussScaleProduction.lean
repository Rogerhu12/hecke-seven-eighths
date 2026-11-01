import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentOriginalAtlas
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FrozenScalarMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondCoefficientNormalization
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ProfileNormalizationInput
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondAllowanceCancellation
import Mathlib.Topology.Order.Compact

/-!
# Original support annuli determine the residual Gauss normalization

The residual scales are the two original plain scales divided by their
actual extracted ideal norms, together with the unchanged live prime
scales. The complete extracted ideal contains the actual prime norms.
Their ratio is therefore the product of the original frozen prime
annular ratios. A fixed compact support in the positive half-line gives
a fixed reciprocal lower endpoint before any base, slots or labels.

The resulting factor B^cap is retained explicitly. An arbitrary fixed
annulus need not start at one, so an uncorrected lower bound for the
residual normalization would in general be false.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]

/-- A single reciprocal annulus constant is selected from the fixed
compact positive support, before any original moment or source label. -/
theorem exists_reciprocal_window_bound (window : Set ℝ)
    (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0) :
    ∃ B : ℝ, 1 ≤ B ∧ window ⊆ Set.Ici B⁻¹ := by
  obtain ⟨c, hc, hlower⟩ := hcompact.exists_forall_le' continuousOn_id
    (fun x hx => hpositive hx)
  refine ⟨max 1 c⁻¹, le_max_left _ _, ?_⟩
  intro x hx
  have hrecip : (max 1 c⁻¹)⁻¹ ≤ c := by
    simpa only [one_div, inv_inv] using
      (one_div_le_one_div_of_le (inv_pos.mpr hc) (le_max_right 1 c⁻¹))
  exact hrecip.trans (hlower x hx)

namespace RawProfileWindow

variable {ω ψ : HeckeCharacter K} {d : MomentData K ω ψ}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain window : Set ℝ}
variable {seminorms : Finset (ℕ × ℕ)} {amplitude : ℝ}
variable (profiles : RawProfileWindow rowDomain heightDomain window seminorms d amplitude)

/-- This lower norm window follows from membership in the original
literal prime support, using its own profile representative. -/
include profiles in
theorem primeScale_le_annulus_mul_norm (B Z t : ℝ)
    (hB : 0 < B) (hZ : 0 < Z) (ht : t ∈ heightDomain)
    (hwindow : window ⊆ Set.Ici B⁻¹)
    (i : Fin d.geometry.slotCount) (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∈ (d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length)) :
    Z ^ (d.geometry.slots i).length ≤ B * (Ideal.absNorm p.asIdeal : ℝ) := by
  have hprofile := ((d.geometry.slots i).support_spec t
    (Z ^ (d.geometry.slots i).length) p).mp hp
  have hrep : profiles.primeRep i t
      ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ (d.geometry.slots i).length) ≠ 0 := by
    simpa only [profiles.prime_eq] using hprofile
  have hy := hwindow (profiles.prime_support i t ht hrep)
  have hdiv : (1 : ℝ) / B ≤
      (Ideal.absNorm p.asIdeal : ℝ) / Z ^ (d.geometry.slots i).length := by
    simpa only [Set.mem_Ici, one_div] using hy
  have h := (div_le_div_iff₀ hB (Real.rpow_pos_of_pos hZ _)).mp hdiv
  simpa only [one_mul, mul_comm] using h

end RawProfileWindow

namespace SupportCartesianBranch

variable {k : ℕ}
variable {S₁ S₂ : Finset (Ideal (𝓞 K))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 K))}
variable {P : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch S₁ S₂ S P)

/-- The original quotient scales after this actual support extraction.
The retained prime scales still use their original occurrence lengths. -/
def residualGaussScale (Z : ℝ) (length : Fin k → ℝ) (X₁ X₂ : ℝ) : ℝ :=
  extraGaussScale (X₁ / idealNorm K b.plainDivisor₁)
    (X₂ / idealNorm K b.plainDivisor₂)
    (fun j => Z ^ length (SlotRestriction.index b.keep j))

theorem residualGaussScale_pos (Z : ℝ) (length : Fin k → ℝ) (X₁ X₂ : ℝ)
    (hZ : 0 < Z) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    0 < b.residualGaussScale Z length X₁ X₂ :=
  extraGaussScale_pos _ _ _ (div_pos hX₁ (idealNorm_pos K _))
    (div_pos hX₂ (idealNorm_pos K _)) (fun _ => Real.rpow_pos_of_pos hZ _)

/-- Exact norm cancellation. Every repeated frozen occurrence remains
in the product, even when the same ideal occurs in multiple slots. -/
theorem residualGaussScale_mul_frozenNorm
    (Z : ℝ) (length : Fin k → ℝ) (X₁ X₂ : ℝ) :
    b.residualGaussScale Z length X₁ X₂ *
        (Ideal.absNorm (frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂
          b.keep b.witness.2) : ℝ) =
      X₁ * X₂ * (∏ j, Z ^ length (SlotRestriction.index b.keep j)) *
        ∏ i ∈ Finset.univ \ b.keep, (Ideal.absNorm (b.witness.2 i).asIdeal : ℝ) := by
  unfold residualGaussScale extraGaussScale
  rw [frozenSourceIdeal_norm]
  field_simp [(idealNorm_pos K b.plainDivisor₁).ne',
    (idealNorm_pos K b.plainDivisor₂).ne']
  <;> ring

/-- The exact original prime-scale product splits into the actual
removed occurrences and the actual retained indexing equivalence. -/
theorem originalScale_product (Z : ℝ) (length : Fin k → ℝ) :
    (∏ i, Z ^ length i) =
      (∏ i ∈ Finset.univ \ b.keep, Z ^ length i) *
        ∏ j, Z ^ length (SlotRestriction.index b.keep j) := by
  simpa only [Finset.sdiff_eq_filter, Finset.mem_univ, true_and] using
    (SlotRestriction.product_extend b.keep (fun _ => (PUnit.unit : PUnit.{1}))
      (fun _ => (PUnit.unit : PUnit.{1})) (fun i _ => Z ^ length i))

/-- Only the original single-prime lower annulus is used. Its fixed
cost is paid once per original occurrence, uniformly in the branch. -/
theorem originalScale_le_compensated
    (Z : ℝ) (length : Fin k → ℝ) (X₁ X₂ B : ℝ) (cap : ℕ)
    (hZ : 0 < Z) (hX₁ : 0 ≤ X₁) (hX₂ : 0 ≤ X₂)
    (hB : 1 ≤ B) (hcap : k ≤ cap)
    (hprime : ∀ i ∈ Finset.univ \ b.keep,
      Z ^ length i ≤ B * (Ideal.absNorm (b.witness.2 i).asIdeal : ℝ)) :
    X₁ * X₂ * (∏ i, Z ^ length i) ≤
      B ^ cap * (b.residualGaussScale Z length X₁ X₂ *
        (Ideal.absNorm (frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂
          b.keep b.witness.2) : ℝ)) := by
  have hcardKeep : (Finset.univ \ b.keep).card ≤ k := by
    simpa only [Fintype.card_fin] using
      (Finset.card_le_univ (Finset.univ \ b.keep))
  have hcard : (Finset.univ \ b.keep).card ≤ cap := hcardKeep.trans hcap
  have hfrozen : (∏ i ∈ Finset.univ \ b.keep, Z ^ length i) ≤
      B ^ cap * ∏ i ∈ Finset.univ \ b.keep,
        (Ideal.absNorm (b.witness.2 i).asIdeal : ℝ) := by
    calc
      _ ≤ ∏ i ∈ Finset.univ \ b.keep,
          B * (Ideal.absNorm (b.witness.2 i).asIdeal : ℝ) :=
        Finset.prod_le_prod₀ (fun _ _ => Real.rpow_nonneg hZ.le _) hprime
      _ = B ^ (Finset.univ \ b.keep).card *
          ∏ i ∈ Finset.univ \ b.keep,
            (Ideal.absNorm (b.witness.2 i).asIdeal : ℝ) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB hcard)
        (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))
  rw [b.originalScale_product, b.residualGaussScale_mul_frozenNorm]
  have hfactor : 0 ≤ X₁ * X₂ * ∏ j, Z ^ length (SlotRestriction.index b.keep j) :=
    mul_nonneg (mul_nonneg hX₁ hX₂)
      (Finset.prod_nonneg (fun _ _ => Real.rpow_nonneg hZ.le _))
  convert mul_le_mul_of_nonneg_left hfrozen hfactor using 1 <;> ring

/-- The exponent is the original total length minus the norm of the
complete extracted ideal. The fixed annulus cost stays explicit. -/
theorem residualGaussScale_lower
    (Z : ℝ) (hZ : 1 < Z) (length : Fin k → ℝ) (X₁ X₂ total B : ℝ) (cap : ℕ)
    (hX₁ : 0 ≤ X₁) (hX₂ : 0 ≤ X₂) (hB : 1 ≤ B) (hcap : k ≤ cap)
    (hproduct : X₁ * X₂ = Z ^ total)
    (hprime : ∀ i ∈ Finset.univ \ b.keep,
      Z ^ length i ≤ B * (Ideal.absNorm (b.witness.2 i).asIdeal : ℝ)) :
    Z ^ (total + (∑ i, length i) -
      idealLogLength Z (frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂
        b.keep b.witness.2)) ≤
      B ^ cap * b.residualGaussScale Z length X₁ X₂ := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hnorm := rpow_idealLogLength Z hZ
    (frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂ b.keep b.witness.2)
    (frozenSourceIdeal_ne_zero _ _ _ _)
  have hnormPos : 0 < (Ideal.absNorm (frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂
      b.keep b.witness.2) : ℝ) := by
    rw [← hnorm]
    exact Real.rpow_pos_of_pos hz _
  rw [Real.rpow_sub hz, hnorm]
  apply (div_le_iff₀ hnormPos).mpr
  calc
    _ = X₁ * X₂ * (∏ i, Z ^ length i) := by
      rw [Real.rpow_add hz, ← hproduct, Real.rpow_sum_of_pos hz]
    _ ≤ B ^ cap * (b.residualGaussScale Z length X₁ X₂ *
        (Ideal.absNorm (frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂
          b.keep b.witness.2) : ℝ)) :=
      b.originalScale_le_compensated Z length X₁ X₂ B cap hz hX₁ hX₂ hB hcap hprime
    _ = _ := by ring

end SupportCartesianBranch

namespace ParentRawAtoms

variable {A : SArithmeticData K} {Γ : Subgroup A.U} {ω ψ : HeckeCharacter K}
variable {d : MomentData K ω ψ} {a : RealParameters} {Z t Y₁ Y₂ : ℝ}
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
variable (raw : ParentRawAtoms (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) d a Z t Y₁ Y₂)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain window : Set ℝ}
variable {seminorms : Finset (ℕ × ℕ)} {amplitude : ℝ}

/-- The actual original atlas supplies all frozen primes from the
original profile supports. Thus no Gauss lower-window record is an
assumption of this theorem, even for an empty retained slot set. -/
theorem original_branch_gaussScale_lower
    (profiles : RawProfileWindow rowDomain heightDomain window seminorms d amplitude)
    (B : ℝ) (hB : 1 ≤ B) (hwindow : window ⊆ Set.Ici B⁻¹)
    (ht : t ∈ heightDomain) (hZ : 1 < Z)
    (cap : ℕ) (hcap : d.geometry.slotCount ≤ cap)
    (P : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
    (label : raw.originalAtlas.labels P D)
    (X₁ X₂ total : ℝ) (hX₁ : 0 ≤ X₁) (hX₂ : 0 ≤ X₂)
    (hproduct : X₁ * X₂ = Z ^ total) :
    Z ^ (total + d.geometry.totalLength - idealLogLength Z D) ≤
      B ^ cap * (raw.originalAtlas.branch P D label).residualGaussScale Z
        (fun i => (d.geometry.slots i).length) X₁ X₂ := by
  let b := raw.originalAtlas.branch P D label
  have hprime (i) (_hi : i ∈ Finset.univ \ b.keep) :
      Z ^ (d.geometry.slots i).length ≤ B * (Ideal.absNorm (b.witness.2 i).asIdeal : ℝ) := by
    have hp := (Finset.mem_filter.mp (b.witness_slots i)).1
    change b.witness.2 i ∈ raw.exteriorSlots i at hp
    exact profiles.primeScale_le_annulus_mul_norm B Z t (zero_lt_one.trans_le hB)
      (zero_lt_one.trans hZ) ht hwindow i (b.witness.2 i) (Finset.mem_filter.mp hp).1
  have h := b.residualGaussScale_lower Z hZ (fun i => (d.geometry.slots i).length)
    X₁ X₂ total B cap hX₁ hX₂ hB hcap hproduct hprime
  have hD : frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂ b.keep b.witness.2 = D :=
    b.frozenSourceIdeal_eq.trans (raw.originalAtlas.branch_product P D label)
  change Z ^ (total + d.geometry.totalLength - idealLogLength Z D) ≤
    B ^ cap * b.residualGaussScale Z (fun i => (d.geometry.slots i).length) X₁ X₂
  simpa only [hD, SlotGeometry.totalLength] using h

end ParentRawAtoms
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.exists_reciprocal_window_bound
#print axioms HeckeSkeleton.Moments.EngineStep.RawProfileWindow.primeScale_le_annulus_mul_norm
#print axioms HeckeSkeleton.Moments.EngineStep.SupportCartesianBranch.residualGaussScale_mul_frozenNorm
#print axioms HeckeSkeleton.Moments.EngineStep.SupportCartesianBranch.residualGaussScale_lower
#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.original_branch_gaussScale_lower
