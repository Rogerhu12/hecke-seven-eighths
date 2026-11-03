import HeckeGeneral.Arithmetic.SIntegerBalancedRepresentatives
import HeckeGeneral.Arithmetic.PrincipalOrbitCounting
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Linear counting of actual nonzero S-integer orbits

The compact representative theorem supplies a common denominator and bounded
ordinary integral representatives. Their ordinary ideal and ordinary-unit
subgroup sector identify the original S-integer orbit injectively. Counting
then uses the proved general number-field ideal bound. Nonprincipal ideals
are allowed, with empty generator fibers; the ordinary integer ring is never
assumed to be a PID. All subgroup sectors are retained in the target count.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain Ideal
open scoped Classical nonZeroDivisors

section ForgetGeneratorIdeal

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Forgetting a fixed nonzero generator ideal respects the actual subgroup action. -/
def generatorOrbitToNonzeroOrbit (Δ : Subgroup Rˣ) (I : Ideal R) [NeZero I] :
    GeneratorOrbits Δ I → MulAction.orbitRel.Quotient Δ (NonzeroRingElements R) :=
  Quotient.map (fun a : PrincipalGenerators I =>
    (⟨a.val, principalGenerators_ne_zero I a⟩ : NonzeroRingElements R)) (by
      intro a b hab
      obtain ⟨u, hu⟩ := hab
      refine ⟨u, ?_⟩
      apply Subtype.ext
      exact congrArg (fun z : PrincipalGenerators I => (z.val : R)) hu)

@[simp] theorem generatorOrbitToNonzeroOrbit_mk (Δ : Subgroup Rˣ)
    (I : Ideal R) [NeZero I] (a : PrincipalGenerators I) :
    generatorOrbitToNonzeroOrbit Δ I (Quotient.mk _ a) =
      Quotient.mk _ (⟨a.val, principalGenerators_ne_zero I a⟩ : NonzeroRingElements R) := rfl

end ForgetGeneratorIdeal

variable (K : Type*) [Field K] [NumberField K]

/-- The actual integral principal ideal norm equals the archimedean arithmetic norm. -/
theorem absNorm_span_integer_eq_mixedNorm (b : 𝓞 K) :
    (Ideal.absNorm (Ideal.span ({b} : Set (𝓞 K))) : ℝ) =
      mixedEmbedding.norm (mixedEmbedding K (b : K)) := by
  rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, ← Rat.cast_intCast,
    Int.cast_abs, Algebra.coe_norm_int, mixedEmbedding.norm_eq_norm]

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

local notation "Q" => SIntegerOrbits K S Γ
local notation "Δ" => ordinaryUnitPullback K S Γ

/-- Actual orbital norm cutoff; no ideal norm is substituted in its definition. -/
def BoundedSIntegerOrbits (H : ℝ) := {q : Q // (sIntegerOrbitNorm K S Γ q).val ≤ H}

private def boundedGeneratorSectorToNonzeroOrbit (n : ℕ)
    (p : BoundedGeneratorSectors K Δ n) :
    MulAction.orbitRel.Quotient Δ (NonzeroRingElements (𝓞 K)) :=
  generatorOrbitToNonzeroOrbit Δ p.1.val.val p.2

/-- The selected bounded ordinary generators give an injection, not just a
surjection onto some chosen collection of principal ideals. -/
theorem exists_boundedSIntegerOrbits_embedding :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ,
      Nonempty (BoundedSIntegerOrbits K S Γ H ↪
        BoundedGeneratorSectors K Δ ⌈C * max 0 H⌉₊) := by
  obtain ⟨d, hd, C, hC, hrep⟩ := exists_uniform_integral_sInteger_representatives K S Γ
  choose u b hb hbound using hrep
  have hdK : (d : K) ≠ 0 := by
    intro h
    exact hd (RingOfIntegers.coe_injective (by simpa only [map_zero] using h))
  refine ⟨C, hC, fun H => ?_⟩
  let n : ℕ := ⌈C * max 0 H⌉₊
  let chosen : BoundedSIntegerOrbits K S Γ H → NonzeroRingElements (𝓞 K) :=
    fun q => b q.val.out
  have hchosen (q : BoundedSIntegerOrbits K S Γ H) :
      Ideal.absNorm (Ideal.span ({(chosen q).val} : Set (𝓞 K))) ≤ n := by
    have hn : (Ideal.absNorm (Ideal.span ({(chosen q).val} : Set (𝓞 K))) : ℝ) ≤
        C * max 0 H := by
      rw [absNorm_span_integer_eq_mixedNorm]
      apply (hbound q.val.out).trans
      rw [sIntegerOrbitNorm_out]
      exact mul_le_mul_of_nonneg_left (q.property.trans (le_max_right _ _)) hC.le
    exact_mod_cast hn.trans (Nat.le_ceil (C * max 0 H))
  let targetIdeal (q : BoundedSIntegerOrbits K S Γ H) : BoundedNonzeroIdeals K n :=
    ⟨⟨Ideal.span ({(chosen q).val} : Set (𝓞 K)),
      mem_nonZeroDivisors_iff_ne_zero.mpr (by
        intro h
        apply (chosen q).property
        exact Ideal.span_singleton_eq_bot.mp h)⟩, hchosen q⟩
  let e : BoundedSIntegerOrbits K S Γ H → BoundedGeneratorSectors K Δ n :=
    fun q => ⟨targetIdeal q, Quotient.mk _ ⟨(chosen q).val, rfl⟩⟩
  refine ⟨⟨e, ?_⟩⟩
  intro q q' heq
  have hforget := congrArg (boundedGeneratorSectorToNonzeroOrbit K S Γ n) heq
  change (Quotient.mk _ (chosen q) :
    MulAction.orbitRel.Quotient Δ (NonzeroRingElements (𝓞 K))) =
      Quotient.mk _ (chosen q') at hforget
  obtain ⟨v, hv⟩ := Quotient.exact hforget
  let vΓ : Γ := ⟨ordinaryUnitToSUnit K S v.val, v.property⟩
  have hvField : (b q.val.out).val =
      (v.val : 𝓞 K) * (b q'.val.out).val := by
    exact (congrArg Subtype.val hv).symm
  have heField : (d : K) * ((((u q.val.out).val : Kˣ) : K) * (q.val.out.val : K)) =
      ((v.val : 𝓞 K) : K) *
        ((d : K) * ((((u q'.val.out).val : Kˣ) : K) * (q'.val.out.val : K))) := by
    rw [← hb q.val.out, ← hb q'.val.out]
    exact congrArg (fun z : 𝓞 K => (z : K)) hvField
  have hcancel : (((u q.val.out).val : Kˣ) : K) * (q.val.out.val : K) =
      ((v.val : 𝓞 K) : K) *
        ((((u q'.val.out).val : Kˣ) : K) * (q'.val.out.val : K)) := by
    apply mul_left_cancel₀ hdK
    calc
      _ = ((v.val : 𝓞 K) : K) *
          ((d : K) * ((((u q'.val.out).val : Kˣ) : K) * (q'.val.out.val : K))) := heField
      _ = _ := by ac_rfl
  have hrel : MulAction.orbitRel (sIntegerUnitSubgroup K S Γ)
      (NonzeroRingElements (S.integer K)) q.val.out q'.val.out := by
    apply (sIntegerOrbitRelation_iff K S Γ _ _).mpr
    refine ⟨(u q.val.out)⁻¹ * vΓ * u q'.val.out, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_inv_eq_inv_val]
    change (((((u q.val.out).val : Kˣ) : K)⁻¹ * ((v.val : 𝓞 K) : K)) *
      (((u q'.val.out).val : Kˣ) : K)) * (q'.val.out.val : K) = (q.val.out.val : K)
    calc
      _ = (((u q.val.out).val : Kˣ) : K)⁻¹ *
          (((v.val : 𝓞 K) : K) *
            ((((u q'.val.out).val : Kˣ) : K) * (q'.val.out.val : K))) := by ring
      _ = _ := by rw [← hcancel, ← mul_assoc,
        inv_mul_cancel₀ ((u q.val.out).val : Kˣ).ne_zero, one_mul]
  apply Subtype.ext
  exact (Quotient.out_eq q.val).symm.trans ((Quotient.sound hrel).trans (Quotient.out_eq q'.val))

/-- Finiteness holds at every real cutoff, including the empty negative cutoffs. -/
instance finite_boundedSIntegerOrbits (H : ℝ) : Finite (BoundedSIntegerOrbits K S Γ H) := by
  obtain ⟨C, _hC, he⟩ := exists_boundedSIntegerOrbits_embedding K S Γ
  obtain ⟨e⟩ := he H
  exact Finite.of_injective e e.injective

/-- The field and subgroup determine one constant, uniform in the norm cutoff. -/
theorem exists_card_boundedSIntegerOrbits_le :
    ∃ D : ℝ, 0 < D ∧ ∀ H : ℝ, 0 ≤ H →
      (Nat.card (BoundedSIntegerOrbits K S Γ H) : ℝ) ≤ D * (1 + H) := by
  obtain ⟨C, hC, he⟩ := exists_boundedSIntegerOrbits_embedding K S Γ
  obtain ⟨B, hB, hbound⟩ := exists_card_boundedGeneratorSectors_le K Δ
  let E : ℝ := (Subgroup.index Δ : ℝ) * B
  have hindex : (0 : ℝ) < Subgroup.index Δ := by
    exact_mod_cast Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := Δ))
  have hE : 0 < E := mul_pos hindex hB
  refine ⟨E * (C + 2), mul_pos hE (by linarith), fun H hH => ?_⟩
  obtain ⟨e⟩ := he H
  have hcard : (Nat.card (BoundedSIntegerOrbits K S Γ H) : ℝ) ≤
      (Nat.card (BoundedGeneratorSectors K Δ ⌈C * max 0 H⌉₊) : ℝ) := by
    exact_mod_cast Nat.card_le_card_of_injective e e.injective
  have hn : (⌈C * max 0 H⌉₊ : ℝ) ≤ C * H + 1 := by
    simpa only [max_eq_right hH] using (Nat.ceil_lt_add_one (mul_nonneg hC.le hH)).le
  calc
    _ ≤ E * (1 + (⌈C * max 0 H⌉₊ : ℝ)) := hcard.trans (hbound _)
    _ ≤ E * (2 + C * H) := mul_le_mul_of_nonneg_left (by linarith) hE.le
    _ ≤ E * (C + 2) * (1 + H) := by
      calc
        E * (2 + C * H) ≤ E * ((C + 2) * (1 + H)) :=
          mul_le_mul_of_nonneg_left (by nlinarith) hE.le
        _ = _ := (mul_assoc E (C + 2) (1 + H)).symm

end HeckeGeneral.Arithmetic
