import HeckeSkeleton.Moments.MOM_INV_STEP.PrincipalDiagonal
import HeckeSkeleton.Moments.MOM_INV_STEP.PrincipalCounting

/-!
# Count the actual principal source, before discarding its masks

The finite set is defined by the actual primitive conductor of the
original four ideals. Its injection into one squarefree column and a
square-product cube pair follows from the proved local diagonal theorem.
Thus the principal count is derived from the original source predicate.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.PrincipalSource

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.ThetaSkeleton
open PrimitivePoissonSource ConductorMasks PrincipalDiagonal
open HeckeSkeleton.Moments.MOMInvStep PrincipalCounting
open DedekindZetaZeroFree.LargeSieve
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset

def principalPairs (B N : Finset Ext) : Finset ((Ext × Ext) × (Ext × Ext)) :=
  ((B ×ˢ N) ×ˢ (B ×ˢ N)).filter fun p =>
    activeSupport (pairSupport K S D p.1.2 p.2.2 p.1.1 p.2.1).support
      (pairExponent K S p.1.2 p.2.2 p.1.1 p.2.1) = ∅

theorem exterior_value_injective : Function.Injective (fun I : Ext => I.val.val) := by
  intro I J h
  exact Subtype.ext (Subtype.ext h)

theorem principalPairs_diagonal (B N : Finset Ext)
    (hN : ∀ n ∈ N, Squarefree n.val.val) (p : principalPairs K S D B N) :
    p.val.1.2 = p.val.2.2 ∧
      ∃ q : Ideal (𝓞 K), q ^ 2 = p.val.1.1.val.val * p.val.2.1.val.val := by
  obtain ⟨hp, hz⟩ := Finset.mem_filter.mp p.property
  obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
  exact principal_source_diagonal K S D p.val.1.2 p.val.2.2 p.val.1.1 p.val.2.1
    (hN _ (Finset.mem_product.mp hp₁).2) (hN _ (Finset.mem_product.mp hp₂).2) hz

theorem principalPairs_card_le (B N : Finset Ext)
    (hN : ∀ n ∈ N, Squarefree n.val.val) :
    (principalPairs K S D B N).card ≤
      N.card * (squarePairs K (B.image (fun I => I.val.val))).card := by
  let T := N × squarePairs K (B.image (fun I => I.val.val))
  let encode (p : principalPairs K S D B N) : T :=
    ⟨⟨p.val.1.2, (Finset.mem_product.mp
      (Finset.mem_product.mp (Finset.mem_filter.mp p.property).1).1).2⟩,
      ⟨(p.val.1.1.val.val, p.val.2.1.val.val), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr
          ⟨Finset.mem_image.mpr ⟨p.val.1.1, (Finset.mem_product.mp
            (Finset.mem_product.mp (Finset.mem_filter.mp p.property).1).1).1, rfl⟩,
           Finset.mem_image.mpr ⟨p.val.2.1, (Finset.mem_product.mp
            (Finset.mem_product.mp (Finset.mem_filter.mp p.property).1).2).1, rfl⟩⟩,
          (principalPairs_diagonal K S D B N hN p).2⟩⟩⟩
  have hinj : Function.Injective encode := by
    intro p q he
    have hn : p.val.1.2 = q.val.1.2 := congrArg (fun x : T => x.1.val) he
    have hb₁ : p.val.1.1 = q.val.1.1 := exterior_value_injective K S
      (congrArg (fun x : T => x.2.val.1) he)
    have hb₂ : p.val.2.1 = q.val.2.1 := exterior_value_injective K S
      (congrArg (fun x : T => x.2.val.2) he)
    have hn₂ : p.val.2.2 = q.val.2.2 :=
      (principalPairs_diagonal K S D B N hN p).1.symm.trans
        (hn.trans (principalPairs_diagonal K S D B N hN q).1)
    exact Subtype.ext (Prod.ext (Prod.ext hb₁ hn) (Prod.ext hb₂ hn₂))
  simpa only [T, Fintype.card_prod, Fintype.card_coe] using
    Fintype.card_le_of_injective encode hinj

/-- Uniform actual-source principal count with no supplied diagonal or
principal-energy estimate. -/
theorem exists_principalPairs_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (B N : Finset Ext) (H X : ℝ),
      1 ≤ H → 1 ≤ X →
      (∀ n ∈ N, Squarefree n.val.val) →
      (∀ b ∈ B, (b.val.val.absNorm : ℝ) ≤ H) →
      (∀ n ∈ N, (n.val.val.absNorm : ℝ) ≤ X) →
      ((principalPairs K S D B N).card : ℝ) ≤ C * X * H ^ (1 + ε) := by
  obtain ⟨A, hA, hcount⟩ := exists_ideal_count_bound K
  obtain ⟨C, hC, hpairs⟩ := exists_squarePairs_bound K ε hε
  refine ⟨A * C, one_le_mul_of_one_le_of_one_le hA hC, ?_⟩
  intro B N H X hH hX hsf hB hN
  have hNcard : (N.card : ℝ) ≤ A * X := by
    let encode (n : N) : boundedNormIdeals K X :=
      ⟨n.val.val.val, mem_boundedNormIdeals.mpr (hN n.val n.property)⟩
    have hinj : Function.Injective encode := by
      intro n m he
      exact Subtype.ext (exterior_value_injective K S (congrArg Subtype.val he))
    have hc : N.card ≤ (boundedNormIdeals K X).card := by
      simpa only [Fintype.card_coe] using Fintype.card_le_of_injective encode hinj
    exact (by exact_mod_cast hc).trans (hcount X hX)
  have hB0 : ∀ I ∈ B.image (fun I => I.val.val), I ≠ 0 := by
    intro I hI
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hI
    exact nonZeroDivisors.coe_ne_zero b.val
  have hBI : ∀ I ∈ B.image (fun I => I.val.val), (I.absNorm : ℝ) ≤ H := by
    intro I hI
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hI
    exact hB b hb
  calc
    _ ≤ (N.card : ℝ) * ((squarePairs K (B.image (fun I => I.val.val))).card : ℝ) := by
      exact_mod_cast principalPairs_card_le K S D B N hsf
    _ ≤ (A * X) * (C * H ^ (1 + ε)) :=
      mul_le_mul hNcard (hpairs _ H hH hB0 hBI) (Nat.cast_nonneg _)
        (mul_nonneg (le_trans zero_le_one hA) (le_trans zero_le_one hX))
    _ = (A * C) * X * H ^ (1 + ε) := by ring

end HeckeSkeleton.Moments.MOM_INV_STEP.PrincipalSource

end
