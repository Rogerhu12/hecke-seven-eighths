import ActualAllowedGeneratorOrbitMask
import ActualAdicSixthPowerDepth
import ActiveBoxPrincipalUnitRatio
import HeckeGeneral.Analysis.SUnitFinitePartitionBox
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.LocallyConstant.Algebra

/-!
UNCOMPILED / native 0. The same witness's finite-S choice mask has a real
compact-open extension to the additive completion product after restriction
to the actual fixed valuation box. The extension is not the unrestricted
mask with zero inserted at the origin. It agrees with the original mask
on the fixed box and vanishes outside the box's image in the field product.
No archimedean coordinate, enlarged S, or moving arithmetic parameter occurs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualGeneratorChoiceDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.Arithmetic.AllowedGeneratorConstruction
open HeckeGeneral.Arithmetic.AllowedGeneratorSectionDraft
open HeckeGeneral.Arithmetic.ActualAdicSixthPowerDraft
open HeckeGeneral.Arithmetic.ActiveBoxPrincipalUnitDraft
open HeckeGeneral.Characters
open Set Topology
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (w : GeneratorMaskWitness K)

local notation "S" => (w.S : Set (HeightOneSpectrum (𝓞 K)))
local notation "U" => SFiniteLocalGroup K S
abbrev choiceFieldProduct : Type := (v : w.S) → v.val.adicCompletion K
local notation "V" => choiceFieldProduct K w

/-- The literal coordinatewise inclusion of the original finite-S units. -/
def choiceFiniteUnitsVal (x : U) : V := fun v => (x v).val

theorem isOpenEmbedding_choiceFiniteUnitsVal :
    IsOpenEmbedding (choiceFiniteUnitsVal K w) := by
  exact IsOpenEmbedding.piMap (fun v : w.S =>
    IsOpenUnits.isOpenEmbedding_unitsVal (M := v.val.adicCompletion K))

theorem choiceFiniteUnitsVal_injective :
    Function.Injective (choiceFiniteUnitsVal K w) :=
  (isOpenEmbedding_choiceFiniteUnitsVal K w).injective

/-- Actual quotient discreteness comes from proved power-image openness. -/
theorem isLocallyConstant_choiceFiniteClassHom :
    IsLocallyConstant (choiceFiniteClassHom K w :
      U → sameSLocalPowerQuotients K w.S 6) := by
  letI : ∀ v : w.S, DiscreteTopology
      ((v.val.adicCompletion K)ˣ ⧸
        (powMonoidHom 6 : (v.val.adicCompletion K)ˣ →*
          (v.val.adicCompletion K)ˣ).range) :=
    fun v => discrete_sixthPowerQuotient K v.val
  apply (IsLocallyConstant.iff_continuous _).mpr
  apply continuous_pi
  intro v
  exact QuotientGroup.continuous_mk.comp (continuous_apply v)

theorem isLocallyConstant_choiceFiniteMask :
    IsLocallyConstant (choiceFiniteMask K w) := by
  exact (isLocallyConstant_choiceFiniteClassHom K w).comp
    (fun q => if q ∈ w.C6 then (1 : ℂ) else 0)

/-- The same complement condition inside the fixed ORIGINAL valuation box. -/
def choiceActiveUnitSet (H : ℕ) : Set U :=
  finiteLocalValuationBox K S H ∩
    (choiceFiniteClassHom K w) ⁻¹' (w.C6 : Set (sameSLocalPowerQuotients K w.S 6))

theorem isClopen_choiceActiveUnitSet (H : ℕ) :
    IsClopen (choiceActiveUnitSet K w H) := by
  have hc : IsClopen ((choiceFiniteClassHom K w) ⁻¹'
      (w.C6 : Set (sameSLocalPowerQuotients K w.S 6))) :=
    ⟨⟨isLocallyConstant_choiceFiniteClassHom K w
        (w.C6 : Set (sameSLocalPowerQuotients K w.S 6))ᶜ⟩,
      isLocallyConstant_choiceFiniteClassHom K w
        (w.C6 : Set (sameSLocalPowerQuotients K w.S 6))⟩
  exact (isClopen_finiteLocalValuationBox K S H).inter hc

theorem isCompact_choiceActiveUnitSet (H : ℕ) :
    IsCompact (choiceActiveUnitSet K w H) :=
  (isCompact_finiteLocalValuationBox K S H).of_isClosed_subset
    (isClopen_choiceActiveUnitSet K w H).isClosed Set.inter_subset_left

/-- Its image is a genuine compact-open subset of the additive field product. -/
def choiceActiveFieldSet (H : ℕ) : Set V :=
  choiceFiniteUnitsVal K w '' choiceActiveUnitSet K w H

theorem isCompact_choiceActiveFieldSet (H : ℕ) :
    IsCompact (choiceActiveFieldSet K w H) :=
  (isCompact_choiceActiveUnitSet K w H).image
    (isOpenEmbedding_choiceFiniteUnitsVal K w).continuous

theorem isClopen_choiceActiveFieldSet (H : ℕ) :
    IsClopen (choiceActiveFieldSet K w H) :=
  ⟨(isCompact_choiceActiveFieldSet K w H).isClosed,
    (isOpenEmbedding_choiceFiniteUnitsVal K w).isOpenMap _
      (isClopen_choiceActiveUnitSet K w H).isOpen⟩

/-- The actual compact-open extension, taking only the values zero and one. -/
def choiceCompactOpenExtension (H : ℕ) : LocallyConstant V ℂ :=
  LocallyConstant.charFn ℂ (isClopen_choiceActiveFieldSet K w H)

@[simp] theorem choiceCompactOpenExtension_units (H : ℕ) (x : U) :
    choiceCompactOpenExtension K w H (choiceFiniteUnitsVal K w x) =
      if x ∈ finiteLocalValuationBox K S H then choiceFiniteMask K w x else 0 := by
  have hm : choiceFiniteUnitsVal K w x ∈ choiceActiveFieldSet K w H ↔
      x ∈ choiceActiveUnitSet K w H := by
    exact (choiceFiniteUnitsVal_injective K w).mem_set_image
  change (Set.indicator (choiceActiveFieldSet K w H) (1 : V → ℂ)
      (choiceFiniteUnitsVal K w x)) = _
  simp only [Set.indicator_apply, Pi.one_apply, hm, choiceActiveUnitSet,
    Set.mem_inter_iff, Set.mem_preimage, choiceFiniteMask]
  split_ifs <;> simp_all

theorem choiceCompactOpenExtension_eq_mask_on_box (H : ℕ) (x : U)
    (hx : x ∈ finiteLocalValuationBox K S H) :
    choiceCompactOpenExtension K w H (choiceFiniteUnitsVal K w x) =
      choiceFiniteMask K w x := by
  simp only [choiceCompactOpenExtension_units, if_pos hx]

theorem choiceCompactOpenExtension_zero_outside_box (H : ℕ) (x : V)
    (hx : x ∉ choiceFiniteUnitsVal K w '' finiteLocalValuationBox K S H) :
    choiceCompactOpenExtension K w H x = 0 := by
  apply (LocallyConstant.charFn_eq_zero ℂ x (isClopen_choiceActiveFieldSet K w H)).mpr
  rintro ⟨u, hu, rfl⟩
  exact hx ⟨u, hu.1, rfl⟩

/-- At any zero local coordinate the extension vanishes. This statement also
handles the empty-S boundary without falsely asserting that its unique tuple is zero. -/
theorem choiceCompactOpenExtension_zero_coordinate (H : ℕ) (x : V)
    (v : w.S) (hx : x v = 0) :
    choiceCompactOpenExtension K w H x = 0 := by
  apply choiceCompactOpenExtension_zero_outside_box K w H x
  rintro ⟨u, _, hu⟩
  have hv : (u v).val = 0 := (congrFun hu v).trans hx
  exact (u v).ne_zero hv

theorem hasCompactSupport_choiceCompactOpenExtension (H : ℕ) :
    HasCompactSupport (choiceCompactOpenExtension K w H : V → ℂ) := by
  apply (isCompact_choiceActiveFieldSet K w H).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (isClopen_choiceActiveFieldSet K w H).isClosed
  intro x hx
  by_contra hn
  exact hx ((LocallyConstant.charFn_eq_zero ℂ x
    (isClopen_choiceActiveFieldSet K w H)).mpr hn)

/-- One actual local depth, chosen before the box width or any moving parameter. -/
def choiceMaskLocalDepth (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  Classical.choose (exists_adicPrincipalUnits_le_sixthPowerRange K v)

theorem choiceMaskLocalDepth_pos (v : HeightOneSpectrum (𝓞 K)) :
    1 ≤ choiceMaskLocalDepth K v :=
  (Classical.choose_spec (exists_adicPrincipalUnits_le_sixthPowerRange K v)).1

theorem choiceMaskLocalDepth_le_sixthPowers (v : HeightOneSpectrum (𝓞 K)) :
    RayClass.localHigherUnitGroup v (choiceMaskLocalDepth K v) ≤
      (powMonoidHom 6 : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range :=
  (Classical.choose_spec (exists_adicPrincipalUnits_le_sixthPowerRange K v)).2

/-- A small ADDITIVE increment preserves the same original box and the true
finite-S class. The box's valuation sign gives valuation(x) at least one,
so the depth does not increase with H. -/
theorem choiceFiniteClass_small_add (H : ℕ) (x : U) (h : V)
    (hx : x ∈ finiteLocalValuationBox K S H)
    (hh : ∀ v : w.S,
      (Valued.v (h v) : WithZero (Multiplicative ℤ)) ≤
        WithZero.exp (-(choiceMaskLocalDepth K v.val : ℤ))) :
    ∃ y : U, choiceFiniteUnitsVal K w y = choiceFiniteUnitsVal K w x + h ∧
      y ∈ finiteLocalValuationBox K S H ∧
      choiceFiniteClassHom K w y = choiceFiniteClassHom K w x := by
  have hex (v : w.S) := exists_localValuationBox_translate_higherUnit
    K v.val H (choiceMaskLocalDepth K v.val) (choiceMaskLocalDepth_pos K v.val)
      (x v) (hx v) (h v) (hh v)
  choose y hyval hyorder hybox hyratio using hex
  have hyfield : choiceFiniteUnitsVal K w y = choiceFiniteUnitsVal K w x + h :=
    funext hyval
  have hclass : choiceFiniteClassHom K w y = choiceFiniteClassHom K w x := by
    funext v
    change QuotientGroup.mk' _ (y v) = QuotientGroup.mk' _ (x v)
    apply QuotientGroup.eq_iff_div_mem.mpr
    apply choiceMaskLocalDepth_le_sixthPowers K v.val
    exact hyratio v
  exact ⟨y, hyfield, hybox, hclass⟩

/-- The actual mask comparison used by a sufficiently fine cleared residue
fibre. The closeness condition is on the ORIGINAL, uncleared local columns. -/
theorem choiceFiniteMask_eq_of_small_sub (H : ℕ) (x y : U)
    (hx : x ∈ finiteLocalValuationBox K S H)
    (hh : ∀ v : w.S,
      (Valued.v ((y v).val - (x v).val) : WithZero (Multiplicative ℤ)) ≤
        WithZero.exp (-(choiceMaskLocalDepth K v.val : ℤ))) :
    choiceFiniteMask K w y = choiceFiniteMask K w x := by
  obtain ⟨z, hz, _, hclass⟩ := choiceFiniteClass_small_add K w H x
    (choiceFiniteUnitsVal K w y - choiceFiniteUnitsVal K w x) hx hh
  have hzy : z = y := (choiceFiniteUnitsVal_injective K w) (by simpa using hz)
  rw [hzy] at hclass
  unfold choiceFiniteMask
  rw [hclass]

theorem mem_choiceActiveFieldSet_add_small (H : ℕ) (x h : V)
    (hh : ∀ v : w.S,
      (Valued.v (h v) : WithZero (Multiplicative ℤ)) ≤
        WithZero.exp (-(choiceMaskLocalDepth K v.val : ℤ)))
    (hx : x ∈ choiceActiveFieldSet K w H) :
    x + h ∈ choiceActiveFieldSet K w H := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨y, hy, hybox, hyclass⟩ := choiceFiniteClass_small_add K w H u h hu.1 hh
  refine ⟨y, ⟨hybox, ?_⟩, hy⟩
  change choiceFiniteClassHom K w y ∈ w.C6
  rw [hyclass]
  exact hu.2

/-- A literal field-product additive period, including inactive and zero fibres. -/
theorem choiceCompactOpenExtension_add_small (H : ℕ) (x h : V)
    (hh : ∀ v : w.S,
      (Valued.v (h v) : WithZero (Multiplicative ℤ)) ≤
        WithZero.exp (-(choiceMaskLocalDepth K v.val : ℤ))) :
    choiceCompactOpenExtension K w H (x + h) = choiceCompactOpenExtension K w H x := by
  have hn : ∀ v : w.S,
      (Valued.v ((-h) v) : WithZero (Multiplicative ℤ)) ≤
        WithZero.exp (-(choiceMaskLocalDepth K v.val : ℤ)) := by
    intro v
    simpa only [Pi.neg_apply, Valuation.map_neg] using hh v
  have hm : x + h ∈ choiceActiveFieldSet K w H ↔ x ∈ choiceActiveFieldSet K w H := by
    constructor
    · intro hx
      simpa only [add_neg_cancel_right] using
        mem_choiceActiveFieldSet_add_small K w H (x + h) (-h) hn hx
    · exact mem_choiceActiveFieldSet_add_small K w H x h hh
  change Set.indicator (choiceActiveFieldSet K w H) (1 : V → ℂ) (x + h) =
    Set.indicator (choiceActiveFieldSet K w H) (1 : V → ℂ) x
  simp only [Set.indicator_apply, Pi.one_apply, hm]

/-- An ordinary ideal supported ONLY on the original S, fixed before H,
moving ideals, the denominator scale, or the Fourier frequency. -/
def choiceMaskOrdinaryPeriod : Ideal (𝓞 K) :=
  ∏ v : w.S, v.val.asIdeal ^ choiceMaskLocalDepth K v.val

theorem choiceMaskOrdinaryPeriod_ne_bot : choiceMaskOrdinaryPeriod K w ≠ ⊥ := by
  exact Finset.prod_ne_zero_iff.mpr (fun v _ => pow_ne_zero _ v.val.ne_bot)

theorem choiceMaskOrdinaryPeriod_le_prime_pow (v : w.S) :
    choiceMaskOrdinaryPeriod K w ≤ v.val.asIdeal ^ choiceMaskLocalDepth K v.val :=
  Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ v))

/-- The concrete ordinary-period statement for the original additive completion product. -/
theorem choiceCompactOpenExtension_add_integer_period (H : ℕ) (x : V) (t : 𝓞 K)
    (ht : t ∈ choiceMaskOrdinaryPeriod K w) :
    choiceCompactOpenExtension K w H
        (x + fun v : w.S => algebraMap (𝓞 K) (v.val.adicCompletion K) t) =
      choiceCompactOpenExtension K w H x := by
  apply choiceCompactOpenExtension_add_small K w H x
  intro v
  have h1 : (Valued.v (algebraMap (𝓞 K) (v.val.adicCompletion K) t) :
      WithZero (Multiplicative ℤ)) = v.val.valuation K (algebraMap (𝓞 K) K t) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 K) K (v.val.adicCompletion K) t]
    exact HeightOneSpectrum.adicCompletion.valued_coe (K := K) (v := v.val) _
  rw [h1, HeightOneSpectrum.valuation_of_algebraMap]
  exact (v.val.intValuation_le_pow_iff_mem t (choiceMaskLocalDepth K v.val)).mpr
    (choiceMaskOrdinaryPeriod_le_prime_pow K w v ht)

/-- The same nonzero period works for every box width, before any moving data. -/
theorem exists_fixed_choiceCompactOpenExtension_period :
    ∃ M : Ideal (𝓞 K), M ≠ ⊥ ∧ ∀ (H : ℕ) (x : V) (t : 𝓞 K), t ∈ M →
      choiceCompactOpenExtension K w H
          (x + fun v : w.S => algebraMap (𝓞 K) (v.val.adicCompletion K) t) =
        choiceCompactOpenExtension K w H x :=
  ⟨choiceMaskOrdinaryPeriod K w, choiceMaskOrdinaryPeriod_ne_bot K w,
    fun H x t ht => choiceCompactOpenExtension_add_integer_period K w H x t ht⟩

theorem norm_choiceCompactOpenExtension_le_one (H : ℕ) (x : V) :
    ‖choiceCompactOpenExtension K w H x‖ ≤ 1 := by
  change ‖Set.indicator (choiceActiveFieldSet K w H) (1 : V → ℂ) x‖ ≤ 1
  by_cases hx : x ∈ choiceActiveFieldSet K w H <;> simp [Set.indicator_apply, hx]

end HeckeGeneral.ThetaSkeleton.Physical.ActualGeneratorChoiceDraft
