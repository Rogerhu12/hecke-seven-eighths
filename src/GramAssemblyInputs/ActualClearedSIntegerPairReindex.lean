import ActualSIntegerDivisorColumn
import ActualSexticClearedColumnProfile

/-!
UNCOMPILED / native 0. Exact ordinary-coordinate reindexing of an actual
cleared S-integer fiber. The inverse coordinate is z / D^M in the original
S-integer ring. Zero axes are extended by zero, and all nonzero associates
and all residue values are retained. No sum identity is supplied as input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeGeneral.Characters.ActualClearedPairReindexDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open ActualGramJointChartCoverDraft ActualGramClearedColumnDraft ActualGramJointChartDraft
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "OS" => S.integer K
local notation "NZ" => NonzeroRingElements OS
local notation "NO" => NonzeroRingElements (𝓞 K)
local notation "D" => finiteSIntegerDenominator K S

private theorem integerMap_injective : Function.Injective (algebraMap (𝓞 K) OS) := by
  intro x y h
  apply IsFractionRing.injective (𝓞 K) K
  simpa using congrArg (fun x : OS => (x : K)) h

/-- The actual inverse of clearing, on every nonzero ordinary integer. -/
def unclearedInteger (M : ℕ) (z : NO) : NZ :=
  ⟨(↑(commonDenominatorUnit K S M)⁻¹ : OS) * algebraMap (𝓞 K) OS z.val,
    mul_ne_zero (Units.ne_zero _) (by
      intro h
      exact z.property (integerMap_injective K S (by simpa using h)))⟩

theorem unclearedInteger_clear (M : ℕ) (z : NO) :
    algebraMap (𝓞 K) OS (D ^ M) * (unclearedInteger K S M z).val =
      algebraMap (𝓞 K) OS z.val := by
  rw [← commonDenominatorUnit_val K S M]
  exact (commonDenominatorUnit K S M).mul_inv_cancel_left _

theorem unclearedInteger_injective (M : ℕ) :
    Function.Injective (unclearedInteger K S M) := by
  intro z t h
  apply Subtype.ext
  apply integerMap_injective K S
  calc
    _ = algebraMap (𝓞 K) OS (D ^ M) * (unclearedInteger K S M z).val :=
      (unclearedInteger_clear K S M z).symm
    _ = algebraMap (𝓞 K) OS (D ^ M) * (unclearedInteger K S M t).val :=
      congrArg (fun m : NZ => algebraMap (𝓞 K) OS (D ^ M) * m.val) h
    _ = _ := unclearedInteger_clear K S M t

/-- Exact image of the actual ordinary-coordinate injection. -/
theorem exists_unclearedInteger_eq_iff (M : ℕ) (m : NZ) :
    (∃ z : NO, unclearedInteger K S M z = m) ↔
      ∃ z : 𝓞 K, algebraMap (𝓞 K) OS (D ^ M) * m.val = algebraMap (𝓞 K) OS z := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z.val, unclearedInteger_clear K S M z⟩
  · rintro ⟨z, hz⟩
    have hD : algebraMap (𝓞 K) OS (D ^ M) ≠ 0 := by
      rw [← commonDenominatorUnit_val K S M]
      exact Units.ne_zero _
    have hzne : z ≠ 0 := by
      intro hzero
      exact mul_ne_zero hD m.property (by simpa only [hzero, map_zero] using hz)
    refine ⟨⟨z, hzne⟩, ?_⟩
    apply Subtype.ext
    apply mul_left_cancel₀ hD
    exact (unclearedInteger_clear K S M ⟨z, hzne⟩).trans hz.symm

variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6)

/-- A genuine refinement by the cleared ordinary S residue, not the
coarser fixed-S chart of d*m. -/
def clearedColumnFiber (M N : ℕ) (z₀ : 𝓞 K) (m : NZ) : Prop :=
  ∃ z : 𝓞 K, algebraMap (𝓞 K) OS (D ^ M) * m.val = algebraMap (𝓞 K) OS z ∧
    z - z₀ ∈ clearedSModulus K S ζ hζ N

theorem unclearedInteger_mem_fiber_iff (M N : ℕ) (z₀ : 𝓞 K) (z : NO) :
    clearedColumnFiber K S ζ hζ M N z₀ (unclearedInteger K S M z) ↔
      z.val - z₀ ∈ clearedSModulus K S ζ hζ N := by
  constructor
  · rintro ⟨t, ht, hmem⟩
    have he : t = z.val := integerMap_injective K S
      (ht.symm.trans (unclearedInteger_clear K S M z))
    simpa only [he] using hmem
  · intro hz
    exact ⟨z.val, unclearedInteger_clear K S M z, hz⟩

def clearedPairSummand (M N : ℕ) (z₀₁ z₀₂ : 𝓞 K)
    (f : NZ × NZ → ℂ) (m : NZ × NZ) : ℂ :=
  if clearedColumnFiber K S ζ hζ M N z₀₁ m.1 ∧
      clearedColumnFiber K S ζ hζ M N z₀₂ m.2 then f m else 0

/-- Literal zero extension at the two ordinary-coordinate zero axes. -/
def ordinaryPairExtension (M N : ℕ) (z₀₁ z₀₂ : 𝓞 K)
    (f : NZ × NZ → ℂ) (z : 𝓞 K × 𝓞 K) : ℂ :=
  if h₁ : z.1 ≠ 0 then if h₂ : z.2 ≠ 0 then
    clearedPairSummand K S ζ hζ M N z₀₁ z₀₂ f
      (unclearedInteger K S M ⟨z.1, h₁⟩, unclearedInteger K S M ⟨z.2, h₂⟩)
  else 0 else 0

/-- Exact complete reindexing, without deleting any unit sector or residue.
For the actual annular consumer both sides also have finite support. -/
theorem tsum_clearedPair_eq_ordinary (M N : ℕ) (z₀₁ z₀₂ : 𝓞 K)
    (f : NZ × NZ → ℂ) :
    (∑' m : NZ × NZ, clearedPairSummand K S ζ hζ M N z₀₁ z₀₂ f m) =
      ∑' z : 𝓞 K × 𝓞 K, ordinaryPairExtension K S ζ hζ M N z₀₁ z₀₂ f z := by
  let j : NO × NO → NZ × NZ := fun z =>
    (unclearedInteger K S M z.1, unclearedInteger K S M z.2)
  have hj : Function.Injective j := by
    intro z t h
    exact Prod.ext
      (unclearedInteger_injective K S M (congrArg Prod.fst h))
      (unclearedInteger_injective K S M (congrArg Prod.snd h))
  have hcover : Function.support (clearedPairSummand K S ζ hζ M N z₀₁ z₀₂ f) ⊆
      Set.range j := by
    intro m hm
    by_cases h : clearedColumnFiber K S ζ hζ M N z₀₁ m.1 ∧
        clearedColumnFiber K S ζ hζ M N z₀₂ m.2
    · obtain ⟨z₁, hz₁⟩ := (exists_unclearedInteger_eq_iff K S M m.1).mpr
        ⟨h.1.choose, h.1.choose_spec.1⟩
      obtain ⟨z₂, hz₂⟩ := (exists_unclearedInteger_eq_iff K S M m.2).mpr
        ⟨h.2.choose, h.2.choose_spec.1⟩
      exact ⟨(z₁, z₂), Prod.ext hz₁ hz₂⟩
    · exact False.elim (hm (by simp only [clearedPairSummand, if_neg h]))
  let i : NO × NO → 𝓞 K × 𝓞 K := fun z => (z.1.val, z.2.val)
  have hi : Function.Injective i := by
    intro z t h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  have hordinary : Function.support (ordinaryPairExtension K S ζ hζ M N z₀₁ z₀₂ f) ⊆
      Set.range i := by
    intro z hz
    by_cases h₁ : z.1 ≠ 0
    · by_cases h₂ : z.2 ≠ 0
      · exact ⟨(⟨z.1, h₁⟩, ⟨z.2, h₂⟩), rfl⟩
      · exact False.elim (hz (by simp only [ordinaryPairExtension, dif_pos h₁, dif_neg h₂]))
    · exact False.elim (hz (by simp only [ordinaryPairExtension, dif_neg h₁]))
  calc
    _ = ∑' z : NO × NO, clearedPairSummand K S ζ hζ M N z₀₁ z₀₂ f (j z) :=
      (hj.tsum_eq hcover).symm
    _ = ∑' z : NO × NO, ordinaryPairExtension K S ζ hζ M N z₀₁ z₀₂ f (i z) := by
      apply tsum_congr
      intro z
      simp only [ordinaryPairExtension, i, j, dif_pos z.1.property, dif_pos z.2.property]
    _ = _ := hi.tsum_eq hordinary

variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
variable (σ : K →+* ℂ) (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)

/-- The actual annular fiber is genuinely summable by finite support,
independently of the joint factor and all arithmetic coefficient zeros. -/
theorem summable_cleared_original_annularPair (M N : ℕ) (z₀₁ z₀₂ : 𝓞 K)
    (c k d : NZ) (a : ℝ → ℝ) (a0 b0 : ℝ) (ha0 : 0 < a0)
    (haSupport : tsupport a ⊆ Set.Icc a0 b0) (r : ℝ) (hr : r ≠ 0)
    (H : NZ × NZ → ℂ) :
    Summable (clearedPairSummand K S ζ hζ M N z₀₁ z₀₂
      (ActualGramFamilyDraft.annularOriginalSummand K S ζ hζ Γ σ hS6 c k d a a r r H)) := by
  have hs := ActualGramFamilyDraft.finite_support_divisor_annularColumn
    K S Γ d a a0 b0 ha0 haSupport r hr
  let T : Finset (NZ × NZ) := hs.toFinset ×ˢ hs.toFinset
  apply summable_of_hasFiniteSupport
  apply T.finite_toSet.subset
  intro m hm
  by_cases h₁ : sIntegerAnnularColumn K S Γ a r (divisorColumn K S d m.1) = 0
  · exact False.elim (hm (by
      simp only [clearedPairSummand, ActualGramFamilyDraft.annularOriginalSummand,
        h₁, Complex.ofReal_zero, mul_zero, zero_mul, ite_self]))
  by_cases h₂ : sIntegerAnnularColumn K S Γ a r (divisorColumn K S d m.2) = 0
  · exact False.elim (hm (by
      simp only [clearedPairSummand, ActualGramFamilyDraft.annularOriginalSummand,
        h₂, Complex.ofReal_zero, mul_zero, zero_mul, ite_self]))
  exact Finset.mem_product.mpr ⟨hs.mem_toFinset.mpr h₁, hs.mem_toFinset.mpr h₂⟩

end HeckeGeneral.Characters.ActualClearedPairReindexDraft
