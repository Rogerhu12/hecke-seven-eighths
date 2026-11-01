import HeckeSkeleton.Moments.MOM_BASE.PairedContext
import HeckeGeneral.Characters.FiniteRayCoefficientExpansion

/-!
# Actual finite-ray tables and frozen slot allocation

The finite tables here are the repository's actual cyclic Hecke-character
tables, with their genuine normalization and identity-ray predicate.
Their finite orders can be chosen before the prime, the background and
the source row.  The paired relative slot is kept throughout the table.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.MOM_BASE.Paired

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

/-- Assignment to frozen and live factors partitions the complete paired
slot, so each inverse background stays beside its own whole-index factor. -/
theorem frozen_live_slot_partition {ι : Type*} [DecidableEq ι]
    (F L : Finset ι) (hFL : Disjoint F L) (P : Presentation K ι)
    (p : ι → HeightOneSpectrum (𝓞 K))
    (hω : ∀ i ∈ F ∪ L, UnramifiedAt K P.background (p i)) :
    (∏ i ∈ F, primeCoefficient K P.plainCharacter (p i) *
        primeCoefficient K (P.relativeCharacter i) (p i)) *
      (∏ i ∈ L, primeCoefficient K P.plainCharacter (p i) *
        primeCoefficient K (P.relativeCharacter i) (p i)) =
      ∏ i ∈ F ∪ L, primeCoefficient K (P.actualFiniteCharacter i) (p i) *
        originalPrimeMask K P.row (P.slot i) (p i) := by
  rw [← Finset.prod_union hFL]
  apply Finset.prod_congr rfl
  intro i hi
  exact P.prime_pairing i (p i) (hω i hi)

/-- Every entry of a normalized actual ray table has the same paired
background cancellation.  Its original finite-factor zeros stay explicit. -/
theorem finiteRayTable_after_pairing {ι : Type*} [Fintype ι]
    (χ : ι → HeckeCharacter K) (n : ι → ℕ)
    (ω ξ θ : HeckeCharacter K) (p : HeightOneSpectrum (𝓞 K))
    (hω : UnramifiedAt K ω p) :
    ((∑ e : ∀ i, Fin (n i),
        primeCoefficient K ((ω * ξ) * cyclicRayTwist K χ n e) p) /
        (∏ i, (n i : ℂ))) * primeCoefficient K (ω⁻¹ * θ) p =
      (∑ e : ∀ i, Fin (n i),
        primeCoefficient K ((ξ * cyclicRayTwist K χ n e) * θ) p *
          originalPrimeMask K (ξ * cyclicRayTwist K χ n e) θ p) /
        (∏ i, (n i : ℂ)) := by
  rw [div_mul_eq_mul_div, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro e _he
  rw [mul_assoc ω ξ (cyclicRayTwist K χ n e)]
  exact paired_relativeCoefficient K ω (ξ * cyclicRayTwist K χ n e) θ p hω

theorem finiteRayTable_character_finite {ι : Type*} [Fintype ι]
    (χ : ι → HeckeCharacter K) (n : ι → ℕ) (hχ : ∀ i, FiniteOrder (χ i))
    (ξ θ : HeckeCharacter K) (hξ : FiniteOrder ξ) (hθ : FiniteOrder θ)
    (e : ∀ i, Fin (n i)) :
    FiniteOrder ((ξ * cyclicRayTwist K χ n e) * θ) :=
  (hξ.mul (cyclicRayTwist_finiteOrder K χ n e hχ)).mul hθ

/-- Both complete finite tables can be expanded before cancelling the
same specified relative slot.  Neither normalization changes allocation. -/
theorem twoFiniteRayTables_after_pairing {ι κ : Type*} [Fintype ι] [Fintype κ]
    (χ : ι → HeckeCharacter K) (n : ι → ℕ)
    (ρ : κ → HeckeCharacter K) (m : κ → ℕ)
    (ω ξ θ : HeckeCharacter K) (p : HeightOneSpectrum (𝓞 K))
    (hω : UnramifiedAt K ω p) :
    ((∑ e : ∀ i, Fin (n i), ∑ f : ∀ j, Fin (m j),
        primeCoefficient K (ω * ((ξ * cyclicRayTwist K χ n e) *
          cyclicRayTwist K ρ m f)) p) /
        ((∏ i, (n i : ℂ)) * (∏ j, (m j : ℂ)))) *
        primeCoefficient K (ω⁻¹ * θ) p =
      (∑ e : ∀ i, Fin (n i), ∑ f : ∀ j, Fin (m j),
        primeCoefficient K (((ξ * cyclicRayTwist K χ n e) *
          cyclicRayTwist K ρ m f) * θ) p *
          originalPrimeMask K ((ξ * cyclicRayTwist K χ n e) *
            cyclicRayTwist K ρ m f) θ p) /
        ((∏ i, (n i : ℂ)) * (∏ j, (m j : ℂ))) := by
  rw [div_mul_eq_mul_div, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro e _he
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro f _hf
  exact paired_relativeCoefficient K ω
    ((ξ * cyclicRayTwist K χ n e) * cyclicRayTwist K ρ m f) θ p hω

theorem twoFiniteRayTables_character_finite {ι κ : Type*} [Fintype ι] [Fintype κ]
    (χ : ι → HeckeCharacter K) (n : ι → ℕ) (hχ : ∀ i, FiniteOrder (χ i))
    (ρ : κ → HeckeCharacter K) (m : κ → ℕ) (hρ : ∀ j, FiniteOrder (ρ j))
    (ξ θ : HeckeCharacter K) (hξ : FiniteOrder ξ) (hθ : FiniteOrder θ)
    (e : ∀ i, Fin (n i)) (f : ∀ j, Fin (m j)) :
    FiniteOrder (((ξ * cyclicRayTwist K χ n e) * cyclicRayTwist K ρ m f) * θ) :=
  ((hξ.mul (cyclicRayTwist_finiteOrder K χ n e hχ)).mul
    (cyclicRayTwist_finiteOrder K ρ m f hρ)).mul hθ

/-- The full finite-ray identity, including its exact denominator and
original all-characters predicate, after the genuine slot is paired. -/
theorem finiteRayTable_pairing {ι : Type*} [Fintype ι] [DecidableEq ι]
    (χ : ι → HeckeCharacter K) (n : ι → ℕ)
    (hn : ∀ i, 0 < n i) (horder : ∀ i, χ i ^ n i = 1)
    (ω ξ θ : HeckeCharacter K) (p : HeightOneSpectrum (𝓞 K))
    (hω : UnramifiedAt K ω p) (hχ : ∀ i, UnramifiedAt K (χ i) p) :
    ((∑ e : ∀ i, Fin (n i),
        primeCoefficient K ((ω * ξ) * cyclicRayTwist K χ n e) p) /
        (∏ i, (n i : ℂ))) * primeCoefficient K (ω⁻¹ * θ) p =
      (primeCoefficient K (ξ * θ) p * originalPrimeMask K ξ θ p) *
        (if ∀ i, primeCoefficient K (χ i) p = 1 then 1 else 0) := by
  rw [finiteRayCoefficientExpansion K χ n hn horder (ω * ξ) p hχ]
  calc
    _ = (primeCoefficient K (ω * ξ) p * primeCoefficient K (ω⁻¹ * θ) p) *
        (if ∀ i, primeCoefficient K (χ i) p = 1 then 1 else 0) := by ring
    _ = _ := by rw [paired_relativeCoefficient K ω ξ θ p hω]

/-- The actual target supplies the live-background unramifiedness for the
finite-ray table; only the fixed filtering characters need to be checked. -/
theorem context_finiteRayTable_pairing {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : TargetContext K) (d : MomentData K c.family.omega (targetCharacter K c))
    (u : NonzeroIdeal K) (i : Fin d.geometry.slotCount)
    (χ : ι → HeckeCharacter K) (n : ι → ℕ)
    (hn : ∀ j, 0 < n j) (horder : ∀ j, χ j ^ n j = 1)
    (p : ExteriorPrime K (places K c)) (hχ : ∀ j, UnramifiedAt K (χ j) p.val) :
    ((∑ e : ∀ j, Fin (n j),
        primeCoefficient K ((d.plainBackground * d.rowCharacter u) *
          cyclicRayTwist K χ n e) p.val) / (∏ j, (n j : ℂ))) *
        primeCoefficient K (d.plainBackground⁻¹ * d.slotCoefficient i) p.val =
      (primeCoefficient K (d.rowCharacter u * d.slotCoefficient i) p.val *
        originalPrimeMask K (d.rowCharacter u) (d.slotCoefficient i) p.val) *
        (if ∀ j, primeCoefficient K (χ j) p.val = 1 then 1 else 0) :=
  finiteRayTable_pairing K χ n hn horder d.plainBackground (d.rowCharacter u)
    (d.slotCoefficient i) p.val
    (context_plainBackground_unramified K c d p.val p.property) hχ

/-- For any fixed finite collection of actual finite-order characters,
one positive-order table works for every exterior prime, background and
row.  The character submitted to prime cancellation is proved finite. -/
theorem finiteRayTables_exist (T : Finset (HeckeCharacter K))
    (hT : ∀ χ ∈ T, FiniteOrder χ) :
    ∃ n : T → ℕ, (∀ χ : T, 0 < n χ) ∧ (∀ χ : T, χ.val ^ n χ = 1) ∧
      (∀ (ξ θ : HeckeCharacter K), FiniteOrder ξ → FiniteOrder θ →
        ∀ e : ∀ χ : T, Fin (n χ),
          FiniteOrder ((ξ * cyclicRayTwist K (fun χ : T => χ.val) n e) * θ)) ∧
      ∀ (ω ξ θ : HeckeCharacter K) (p : HeightOneSpectrum (𝓞 K)),
        UnramifiedAt K ω p → (∀ χ ∈ T, UnramifiedAt K χ p) →
        ((∑ e : ∀ χ : T, Fin (n χ),
            primeCoefficient K ((ω * ξ) * cyclicRayTwist K (fun χ : T => χ.val) n e) p) /
            (∏ χ : T, (n χ : ℂ))) * primeCoefficient K (ω⁻¹ * θ) p =
          (primeCoefficient K (ξ * θ) p * originalPrimeMask K ξ θ p) *
            (if ∀ χ ∈ T, primeCoefficient K χ p = 1 then 1 else 0) := by
  obtain ⟨n, hn, horder, hfinite, hexpansion⟩ :=
    finiteRayCoefficientExpansion_of_finiteOrder K T hT
  refine ⟨n, hn, horder, ?_, ?_⟩
  · intro ξ θ hξ hθ e
    exact (hξ.mul (hfinite e)).mul hθ
  · intro ω ξ θ p hω hχ
    rw [hexpansion (ω * ξ) p hχ]
    calc
      _ = (primeCoefficient K (ω * ξ) p * primeCoefficient K (ω⁻¹ * θ) p) *
          (if ∀ χ ∈ T, primeCoefficient K χ p = 1 then 1 else 0) := by ring
      _ = _ := by rw [paired_relativeCoefficient K ω ξ θ p hω]

end HeckeSkeleton.Moments.MOM_BASE.Paired
