import ActualAllowedGeneratorOrbitMask
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
UNCOMPILED / native 0. The actual finite-local choice mask selects precisely
one original sixth-power-unit orbit per exterior ideal. Its selected columns
are enumerated by the SAME ideal and a unique member of the SAME Gamma.
The ideal is recovered by actual contraction; unit uniqueness uses the
nonzero generator and cancellation in K. No generator multiplicativity or
orbit bijection is supplied as a hypothesis.

All two-column sums below are indexed by a single product type. No infinite
Fubini exchange or comparison with the unmasked whole-column sum is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualGeneratorChoiceDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Arithmetic.AllowedGeneratorConstruction
open HeckeGeneral.Arithmetic.AllowedGeneratorSectionDraft
open ActualProbeGaussFourierDraft
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (w : GeneratorMaskWitness K)

local notation "S" => (w.S : Set (HeightOneSpectrum (𝓞 K)))
local notation "NZ" => NonzeroRingElements (Set.integer S K)
local notation "E" => ExteriorIdeal K S
local notation "Γ" => sixthPowerUnits K S

def choiceMaskedColumns :=
  {m : NZ // choiceFiniteMask K w (sLocalNonzeroIntegerDiagonal K S m).2 = 1}

@[simp] theorem choiceColumnIdeal_probeGenerator (I : E) :
    choiceColumnIdeal K w (probeGenerator K S w.D I) = I := by
  apply Subtype.ext
  apply Subtype.ext
  exact probeGenerator_contraction K S w.D I

/-- All original Gamma translates have the same actual contracted ideal. -/
@[simp] theorem choiceColumnIdeal_translate (u : Γ) (m : NZ) :
    choiceColumnIdeal K w (sIntegerOrbitTranslate K S Γ u m) =
      choiceColumnIdeal K w m := by
  apply Subtype.ext
  apply Subtype.ext
  change (Ideal.span ({((S).unitEquivUnitsInteger K u.val).val * m.val} :
      Set ((S).integer K))).under (𝓞 K) =
    (Ideal.span ({m.val} : Set ((S).integer K))).under (𝓞 K)
  rw [Ideal.span_singleton_mul_left_unit ((S).unitEquivUnitsInteger K u.val).isUnit]

def choiceGeneratorOrbitColumn (p : E × Γ) : choiceMaskedColumns K w :=
  ⟨sIntegerOrbitTranslate K S Γ p.2 (probeGenerator K S w.D p.1),
    choiceFiniteMask_generator_translate K w p.1 p.2⟩

theorem choiceGeneratorOrbitColumn_injective :
    Function.Injective (choiceGeneratorOrbitColumn K w) := by
  rintro ⟨I, u⟩ ⟨J, v⟩ huv
  have he : sIntegerOrbitTranslate K S Γ u (probeGenerator K S w.D I) =
      sIntegerOrbitTranslate K S Γ v (probeGenerator K S w.D J) :=
    congrArg Subtype.val huv
  have hI : I = J := by
    have h := congrArg (choiceColumnIdeal K w) he
    simpa only [choiceColumnIdeal_translate, choiceColumnIdeal_probeGenerator] using h
  subst J
  have hu : u = v := by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    have h := congrArg (fun a : NZ => (a.val : K)) he
    change ((u.val : Kˣ) : K) * ((probeGenerator K S w.D I).val : K) =
      ((v.val : Kˣ) : K) * ((probeGenerator K S w.D I).val : K) at h
    exact mul_right_cancel₀ (nonzeroSIntegerFieldUnit K S
      (probeGenerator K S w.D I)).ne_zero h
  exact Prod.ext rfl hu

theorem choiceGeneratorOrbitColumn_surjective :
    Function.Surjective (choiceGeneratorOrbitColumn K w) := by
  intro m
  obtain ⟨I, u, hu⟩ :=
    (choiceFiniteMask_eq_one_iff_generator_translate K w m.val).mp m.property
  refine ⟨(I, u), ?_⟩
  exact Subtype.ext hu.symm

/-- Literal columns selected by the actual choice mask, with no arbitrary
representative replacing the existing generator section. -/
def choiceGeneratorOrbitEquiv : E × Γ ≃ choiceMaskedColumns K w :=
  Equiv.ofBijective (choiceGeneratorOrbitColumn K w)
    ⟨choiceGeneratorOrbitColumn_injective K w,
      choiceGeneratorOrbitColumn_surjective K w⟩

@[simp] theorem choiceGeneratorOrbitEquiv_apply_val (I : E) (u : Γ) :
    (choiceGeneratorOrbitEquiv K w (I, u)).val =
      sIntegerOrbitTranslate K S Γ u (probeGenerator K S w.D I) := rfl

/-- The inverse ideal coordinate is the literal contraction, not an
independently chosen ideal label. -/
theorem choiceGeneratorOrbitEquiv_symm_fst (m : choiceMaskedColumns K w) :
    ((choiceGeneratorOrbitEquiv K w).symm m).1 = choiceColumnIdeal K w m.val := by
  have h := congrArg
    (fun a : choiceMaskedColumns K w => choiceColumnIdeal K w a.val)
    ((choiceGeneratorOrbitEquiv K w).apply_symm_apply m)
  change choiceColumnIdeal K w (sIntegerOrbitTranslate K S Γ
    ((choiceGeneratorOrbitEquiv K w).symm m).2
    (probeGenerator K S w.D ((choiceGeneratorOrbitEquiv K w).symm m).1)) =
      choiceColumnIdeal K w m.val at h
  simpa only [choiceColumnIdeal_translate, choiceColumnIdeal_probeGenerator] using h

theorem summable_choiceGeneratorOrbit_iff (f : NZ → ℂ) :
    Summable (fun p : E × Γ =>
      f (sIntegerOrbitTranslate K S Γ p.2 (probeGenerator K S w.D p.1))) ↔
    Summable (fun m : choiceMaskedColumns K w => f m.val) := by
  change Summable ((fun m : choiceMaskedColumns K w => f m.val) ∘
    choiceGeneratorOrbitEquiv K w) ↔ _
  exact (choiceGeneratorOrbitEquiv K w).summable_iff

theorem tsum_choiceMaskedColumns_eq_generatorOrbit (f : NZ → ℂ) :
    (∑' m : choiceMaskedColumns K w, f m.val) =
      ∑' p : E × Γ,
        f (sIntegerOrbitTranslate K S Γ p.2 (probeGenerator K S w.D p.1)) := by
  exact ((choiceGeneratorOrbitEquiv K w).tsum_eq
    (fun m : choiceMaskedColumns K w => f m.val)).symm

/-- Multiplication by the actual binary mask is exactly restriction to its
selected columns. The identity remains a single reindexed totalized sum. -/
theorem tsum_choiceFiniteMask_eq_generatorOrbit (f : NZ → ℂ) :
    (∑' m : NZ, choiceFiniteMask K w (sLocalNonzeroIntegerDiagonal K S m).2 * f m) =
      ∑' p : E × Γ,
        f (sIntegerOrbitTranslate K S Γ p.2 (probeGenerator K S w.D p.1)) := by
  have hind (m : NZ) :
      choiceFiniteMask K w (sLocalNonzeroIntegerDiagonal K S m).2 * f m =
      ({a : NZ | choiceFiniteMask K w (sLocalNonzeroIntegerDiagonal K S a).2 = 1} :
        Set NZ).indicator f m := by
    by_cases h : choiceFiniteClassHom K w (sLocalNonzeroIntegerDiagonal K S m).2 ∈ w.C6
    · rw [choiceFiniteClassHom_diagonal] at h
      simp [choiceFiniteMask, Set.indicator, h]
    · rw [choiceFiniteClassHom_diagonal] at h
      simp [choiceFiniteMask, Set.indicator, h]
  calc
    _ = ∑' m : NZ,
        ({a : NZ | choiceFiniteMask K w (sLocalNonzeroIntegerDiagonal K S a).2 = 1} :
          Set NZ).indicator f m := tsum_congr hind
    _ = ∑' m : choiceMaskedColumns K w, f m.val := (tsum_subtype _ _).symm
    _ = _ := tsum_choiceMaskedColumns_eq_generatorOrbit K w f

/-- Independent original-Gamma coordinates for two columns. -/
def choiceGeneratorPairEquiv : (E × Γ) × (E × Γ) ≃
    choiceMaskedColumns K w × choiceMaskedColumns K w :=
  Equiv.prodCongr (choiceGeneratorOrbitEquiv K w) (choiceGeneratorOrbitEquiv K w)

theorem summable_choiceGeneratorPair_iff (f : NZ × NZ → ℂ) :
    Summable (fun p : (E × Γ) × (E × Γ) => f
      (sIntegerOrbitTranslate K S Γ p.1.2 (probeGenerator K S w.D p.1.1),
       sIntegerOrbitTranslate K S Γ p.2.2 (probeGenerator K S w.D p.2.1))) ↔
    Summable (fun m : choiceMaskedColumns K w × choiceMaskedColumns K w =>
      f (m.1.val, m.2.val)) := by
  change Summable ((fun m : choiceMaskedColumns K w × choiceMaskedColumns K w =>
    f (m.1.val, m.2.val)) ∘ choiceGeneratorPairEquiv K w) ↔ _
  exact (choiceGeneratorPairEquiv K w).summable_iff

/-- This is one product-indexed tsum reindexing. In particular it does not
silently replace a non-summable double series by iterated sums. -/
theorem tsum_choiceMaskedPairs_eq_generatorPairs (f : NZ × NZ → ℂ) :
    (∑' m : choiceMaskedColumns K w × choiceMaskedColumns K w, f (m.1.val, m.2.val)) =
      ∑' p : (E × Γ) × (E × Γ), f
        (sIntegerOrbitTranslate K S Γ p.1.2 (probeGenerator K S w.D p.1.1),
         sIntegerOrbitTranslate K S Γ p.2.2 (probeGenerator K S w.D p.2.1)) := by
  exact ((choiceGeneratorPairEquiv K w).tsum_eq
    (fun m : choiceMaskedColumns K w × choiceMaskedColumns K w =>
      f (m.1.val, m.2.val))).symm

end HeckeGeneral.ThetaSkeleton.Physical.ActualGeneratorChoiceDraft
