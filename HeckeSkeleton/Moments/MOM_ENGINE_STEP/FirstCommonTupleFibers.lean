import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ResidualTupleCount
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstBlocks

/-!
# The actual factor fibres after the first common-support extraction

The first common block keeps the original whole coefficient index.
Removing its common support from every factor therefore need not preserve
injectivity.  The lost tuple consists of actual divisors of the fixed
common ideal.  Removing the amplifier prime loses, in addition, its
finite valuation allocation.  The two finite losses are proved here from
the exact original-factor reconstruction, including the empty tuple.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open DedekindZetaZeroFree.LargeSieve
open HeckePort.IdealMobiusDivisorSum HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}

def actualSupportResidualFactors {k : ℕ} (R : Finset (Ideal (𝓞 K)))
    (f : Fin k → A.Exterior) : Fin k → A.Exterior :=
  fun i => residualExterior (f i) R

def actualSupportExtractedFactors {k : ℕ} (R : Finset (Ideal (𝓞 K)))
    (f : Fin k → A.Exterior) : Fin k → Ideal (𝓞 K) :=
  fun i => supportExtract (f i).val R

theorem actual_support_factor_reconstruct {k : ℕ}
    (R : Finset (Ideal (𝓞 K))) (f : Fin k → A.Exterior) (i : Fin k) :
    (f i).val = actualSupportExtractedFactors R f i *
      (actualSupportResidualFactors R f i).val :=
  (support_reconstruct (f i).val (f i).property.1 R).symm

theorem actual_support_extracted_tuple_product {k : ℕ}
    (R : Finset (Ideal (𝓞 K))) (f : Fin k → A.Exterior) :
    PowerfulDiagonal.tupleIdeal (actualSupportExtractedFactors R f) =
      supportExtract (PowerfulDiagonal.tupleIdeal (fun i => (f i).val)) R :=
  (supportExtract_prod Finset.univ (fun i => (f i).val)
    (fun i _ => (f i).property.1) R).symm

theorem actual_support_residual_tuple_product {k : ℕ}
    (R : Finset (Ideal (𝓞 K))) (f : Fin k → A.Exterior) :
    PowerfulDiagonal.tupleIdeal (fun i => (actualSupportResidualFactors R f i).val) =
      supportResidual (PowerfulDiagonal.tupleIdeal (fun i => (f i).val)) R :=
  (supportResidual_prod Finset.univ (fun i => (f i).val)
    (fun i _ => (f i).property.1) R).symm

/-- Fixing the actual extracted ideal makes the residual map injective
on one occurrence, before any Cartesian product is formed. -/
theorem supportResidual_injOn_fixed_extract
    (R : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K)) :
    Set.InjOn (fun I : Ideal (𝓞 K) => supportResidual I R)
      {I | I ≠ 0 ∧ supportExtract I R = D} := by
  intro I hI J hJ he
  calc
    I = supportExtract I R * supportResidual I R := (support_reconstruct I hI.1 R).symm
    _ = supportExtract J R * supportResidual J R := by rw [hI.2, hJ.2, he]
    _ = J := support_reconstruct J hJ.1 R

/-- With the complete extracted occurrence tuple fixed, the original
whole tuple injection descends to the actual residual tuple. -/
theorem actual_support_residual_tuple_injective_on_extract {α : Type*} {k : ℕ}
    (S : Finset α) (f : α → Fin k → A.Exterior)
    (hinj : Set.InjOn (fun x i => (f x i).val) (S : Set α))
    (R : Finset (Ideal (𝓞 K))) (D : Fin k → Ideal (𝓞 K))
    (hextract : ∀ x ∈ S, actualSupportExtractedFactors R (f x) = D) :
    Set.InjOn (fun x i => (actualSupportResidualFactors R (f x) i).val) (S : Set α) := by
  intro x hx y hy he
  apply hinj hx hy
  funext i
  rw [actual_support_factor_reconstruct R (f x) i,
    actual_support_factor_reconstruct R (f y) i,
    hextract x hx, hextract y hy, congrFun he i]

private theorem support_fingerprint_mem {k : ℕ}
    (R : Finset (Ideal (𝓞 K))) (f : Fin k → A.Exterior)
    (D : Ideal (𝓞 K)) (hD : D ≠ 0)
    (hextract : supportExtract (PowerfulDiagonal.tupleIdeal (fun i => (f i).val)) R = D) :
    actualSupportExtractedFactors R f ∈
      Fintype.piFinset (fun _ : Fin k => idealDivisors D) := by
  apply Fintype.mem_piFinset.mpr
  intro i
  apply (mem_idealDivisors hD).mpr
  have hd : actualSupportExtractedFactors R f i ∣
      PowerfulDiagonal.tupleIdeal (actualSupportExtractedFactors R f) :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  rwa [actual_support_extracted_tuple_product, hextract] at hd

/-- The first common-support quotient has its actual finite divisor
multiplicity.  Injectivity is required only for the original full tuple. -/
theorem actual_support_residual_tuple_fiber_card {α : Type*} {k : ℕ}
    (S : Finset α) (f : α → Fin k → A.Exterior)
    (hinj : Set.InjOn (fun x i => (f x i).val) (S : Set α))
    (R : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K)) (hD : D ≠ 0)
    (hextract : ∀ x ∈ S,
      supportExtract (PowerfulDiagonal.tupleIdeal (fun i => (f x i).val)) R = D)
    (v : Fin k → Ideal (𝓞 K)) :
    (S.filter (fun x => (fun i => (actualSupportResidualFactors R (f x) i).val) = v)).card ≤
      idealDivisorCount D ^ k := by
  let T := S.filter
    (fun x => (fun i => (actualSupportResidualFactors R (f x) i).val) = v)
  have hi : Set.InjOn (fun x => actualSupportExtractedFactors R (f x)) (T : Set α) := by
    intro x hx y hy he
    apply hinj (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1
    funext i
    rw [actual_support_factor_reconstruct R (f x) i,
      actual_support_factor_reconstruct R (f y) i, congrFun he i]
    rw [congrFun (Finset.mem_filter.mp hx).2 i,
      congrFun (Finset.mem_filter.mp hy).2 i]
  have hsub : T.image (fun x => actualSupportExtractedFactors R (f x)) ⊆
      Fintype.piFinset (fun _ : Fin k => idealDivisors D) := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
    exact support_fingerprint_mem R (f x) D hD (hextract x (Finset.mem_filter.mp hx).1)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hi] at hc
  simpa only [Fintype.card_piFinset_const, idealDivisorCount] using hc

/-- Both losses are counted together.  In particular no injection of
the already support-extracted tuple is assumed before the amplifier. -/
theorem actual_support_amplifier_tuple_fiber_card {α : Type*} {k n : ℕ}
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (S : Finset α) (f : α → Fin k → A.Exterior)
    (hinj : Set.InjOn (fun x i => (f x i).val) (S : Set α))
    (R : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K)) (hD : D ≠ 0)
    (hextract : ∀ x ∈ S,
      supportExtract (PowerfulDiagonal.tupleIdeal (fun i => (f x i).val)) R = D)
    (hvaluation : ∀ x ∈ S,
      ∑ i, actualFactorValuation p (actualSupportResidualFactors R (f x)) i = n)
    (v : Fin k → Ideal (𝓞 K)) :
    (S.filter (fun x =>
      actualResidualFactorTuple C p (actualSupportResidualFactors R (f x)) = v)).card ≤
        idealDivisorCount D ^ k * (n + 1) ^ k := by
  let T := S.filter (fun x =>
    actualResidualFactorTuple C p (actualSupportResidualFactors R (f x)) = v)
  let fingerprint := fun x =>
    (actualSupportExtractedFactors R (f x),
      actualFactorValuation p (actualSupportResidualFactors R (f x)))
  have hi : Set.InjOn fingerprint (T : Set α) := by
    intro x hx y hy he
    have he₁ := congrArg Prod.fst he
    have he₂ := congrArg Prod.snd he
    apply hinj (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1
    funext i
    rw [actual_support_factor_reconstruct R (f x) i,
      actual_support_factor_reconstruct R (f y) i,
      actual_factor_reconstructed C p (actualSupportResidualFactors R (f x)) i,
      actual_factor_reconstructed C p (actualSupportResidualFactors R (f y)) i]
    rw [congrFun he₁ i, congrFun he₂ i,
      (Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hy).2]
  have hsub : T.image fingerprint ⊆
      (Fintype.piFinset (fun _ : Fin k => idealDivisors D)) ×ˢ
        ValuationAllocation.choices k n := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
    apply Finset.mem_product.mpr
    exact ⟨support_fingerprint_mem R (f x) D hD
      (hextract x (Finset.mem_filter.mp hx).1),
      ValuationAllocation.mem_choices_of_sum _
        (hvaluation x (Finset.mem_filter.mp hx).1)⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hi, Finset.card_product,
    Fintype.card_piFinset_const] at hc
  exact hc.trans (Nat.mul_le_mul_left _ (ValuationAllocation.card_choices_le k n))

/-- A pair of original whole tuples in one common block gives the
literal pair of residual ideals and a divisor-count fibre bound. -/
theorem actual_support_residual_pair_data {ι : Type*} {k : ℕ}
    (columns : Finset ι) (fullI : ι → A.Exterior)
    (f : ι × ι → Fin k → A.Exterior)
    (hinj : Set.InjOn (fun ij i => (f ij i).val) ((columns ×ˢ columns) : Set (ι × ι)))
    (hproduct : ∀ ij ∈ columns ×ˢ columns,
      PowerfulDiagonal.tupleIdeal (fun i => (f ij i).val) =
        (fullI ij.1).val * (fullI ij.2).val)
    (R : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K)) (hD : D ≠ 0)
    (hcommon : ∀ i ∈ columns, supportExtract (fullI i).val R = D) :
    (∀ ij ∈ columns ×ˢ columns,
      PowerfulDiagonal.tupleIdeal
        (fun i => (actualSupportResidualFactors R (f ij) i).val) =
        (residualExterior (fullI ij.1) R).val * (residualExterior (fullI ij.2) R).val) ∧
    (∀ v, ((columns ×ˢ columns).filter (fun ij =>
      (fun i => (actualSupportResidualFactors R (f ij) i).val) = v)).card ≤
        idealDivisorCount (D ^ 2) ^ k) := by
  constructor
  · intro ij hij
    rw [actual_support_residual_tuple_product, hproduct ij hij,
      supportResidual_mul _ _ (fullI ij.1).property.1 (fullI ij.2).property.1 R]
    rfl
  · intro v
    apply actual_support_residual_tuple_fiber_card
      (columns ×ˢ columns) f hinj R (D ^ 2) (pow_ne_zero 2 hD) _ v
    intro ij hij
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hij
    rw [hproduct ij hij,
      supportExtract_mul _ _ (fullI ij.1).property.1 (fullI ij.2).property.1 R,
      hcommon ij.1 hi, hcommon ij.2 hj, pow_two]

/-- The same original pair, first support-extracted and then genuinely
amplified.  The product is the pair of actual quotient ideals, and the
finite multiplicity records both pieces of information that were lost. -/
theorem actual_support_amplifier_pair_data {ι : Type*} {k n : ℕ}
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (columns : Finset ι) (fullI : ι → A.Exterior)
    (f : ι × ι → Fin k → A.Exterior)
    (hinj : Set.InjOn (fun ij i => (f ij i).val) ((columns ×ˢ columns) : Set (ι × ι)))
    (hproduct : ∀ ij ∈ columns ×ˢ columns,
      PowerfulDiagonal.tupleIdeal (fun i => (f ij i).val) =
        (fullI ij.1).val * (fullI ij.2).val)
    (R : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K)) (hD : D ≠ 0)
    (hcommon : ∀ i ∈ columns, supportExtract (fullI i).val R = D)
    (Q : ∀ i, AmplifierResidualPresentation C p n (residualExterior (fullI i) R)) :
    (∀ ij ∈ columns ×ˢ columns,
      PowerfulDiagonal.tupleIdeal
        (actualResidualFactorTuple C p (actualSupportResidualFactors R (f ij))) =
        (Q ij.1).residual.val * (Q ij.2).residual.val) ∧
    (∀ v, ((columns ×ˢ columns).filter (fun ij =>
      actualResidualFactorTuple C p (actualSupportResidualFactors R (f ij)) = v)).card ≤
        idealDivisorCount (D ^ 2) ^ k * (n + n + 1) ^ k) := by
  have hsupport := (actual_support_residual_pair_data columns fullI f hinj hproduct
    R D hD hcommon).1
  constructor
  · intro ij hij
    exact actual_residual_pair_tuple_product C p (actualSupportResidualFactors R (f ij))
      (residualExterior (fullI ij.1) R) (residualExterior (fullI ij.2) R)
      (hsupport ij hij) (Q ij.1) (Q ij.2)
  · intro v
    apply actual_support_amplifier_tuple_fiber_card C p (columns ×ˢ columns) f
      hinj R (D ^ 2) (pow_ne_zero 2 hD) _ _ v
    · intro ij hij
      obtain ⟨hi, hj⟩ := Finset.mem_product.mp hij
      rw [hproduct ij hij,
        supportExtract_mul _ _ (fullI ij.1).property.1 (fullI ij.2).property.1 R,
        hcommon ij.1 hi, hcommon ij.2 hj, pow_two]
    · intro ij hij
      have hs := actual_factor_valuation_sum p (actualSupportResidualFactors R (f ij))
        (ExteriorIdealEuler.mul (residualExterior (fullI ij.1) R)
          (residualExterior (fullI ij.2) R)) (hsupport ij hij)
      rw [primeExponent_exterior_mul, (Q ij.1).original_valuation,
        (Q ij.2).original_valuation] at hs
      exact hs

/-- The fibre loss is a fixed small-power cost; its constant and
exponent are selected before the common ideal and the scale. -/
theorem support_tuple_multiplicity_subpower (k : ℕ) (B ε : ℝ)
    (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z : ℝ), 1 ≤ Z →
      ∀ D : Ideal (𝓞 K), (Ideal.absNorm D : ℝ) ≤ Z ^ B →
      (idealDivisorCount D : ℝ) ^ k ≤ C * Z ^ ε := by
  let δ := ε / (((k : ℝ) + 1) * (B + 1))
  have hden : 0 < ((k : ℝ) + 1) * (B + 1) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  obtain ⟨C, hC, hdiv⟩ := ideal_divisor_count_le_rpow K δ hδ
  refine ⟨C ^ k, pow_pos (zero_lt_one.trans_le hC) k, ?_⟩
  intro Z hZ D hD
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hbudget : B * (δ * (k : ℝ)) ≤ ε := by
    have he : δ * (((k : ℝ) + 1) * (B + 1)) = ε :=
      div_mul_cancel₀ ε hden.ne'
    nlinarith [mul_nonneg hδ.le hB, mul_nonneg hδ.le (Nat.cast_nonneg k)]
  calc
    _ ≤ (C * (Ideal.absNorm D : ℝ) ^ δ) ^ k :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (hdiv D) k
    _ = C ^ k * (Ideal.absNorm D : ℝ) ^ (δ * (k : ℝ)) := by
      rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
    _ ≤ C ^ k * (Z ^ B) ^ (δ * (k : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hD
          (mul_nonneg hδ.le (Nat.cast_nonneg k)))
        (pow_nonneg (zero_le_one.trans hC) k)
    _ = C ^ k * Z ^ (B * (δ * (k : ℝ))) := by
      rw [← Real.rpow_mul hz.le]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ hbudget)
      (pow_nonneg (zero_le_one.trans hC) k)

/-- The literal pair multiplicity needed by a main or 1/6/7 source is
uniformly a small power.  The amplifier prime is absent from the bound. -/
theorem common_amplifier_fiber_subpower (k : ℕ) (B ε : ℝ)
    (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z : ℝ), 1 ≤ Z →
      ∀ (D : Ideal (𝓞 K)) (n : ℕ), n ≤ 7 →
      (Ideal.absNorm D : ℝ) ≤ Z ^ B →
      ((idealDivisorCount (D ^ 2) ^ k * (n + n + 1) ^ k : ℕ) : ℝ) ≤ C * Z ^ ε := by
  obtain ⟨C, hC, hb⟩ := support_tuple_multiplicity_subpower (K := K) k (2 * B) ε
    (mul_nonneg (by norm_num) hB) hε
  refine ⟨C * (15 : ℝ) ^ k, mul_pos hC (by positivity), ?_⟩
  intro Z hZ D n hn hD
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hD₂ : (Ideal.absNorm (D ^ 2) : ℝ) ≤ Z ^ (2 * B) := by
    calc
      _ = (Ideal.absNorm D : ℝ) ^ 2 := by simp only [map_pow, Nat.cast_pow]
      _ ≤ (Z ^ B) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hD 2
      _ = _ := by
        rw [← Real.rpow_mul_natCast hz.le]
        congr 1
        norm_num <;> ring
  have hn' : ((n + n + 1) ^ k : ℝ) ≤ (15 : ℝ) ^ k := by
    exact_mod_cast Nat.pow_le_pow_left (by omega : n + n + 1 ≤ 15) k
  calc
    _ = (idealDivisorCount (D ^ 2) : ℝ) ^ k * ((n + n + 1) ^ k : ℝ) := by
      push_cast <;> rfl
    _ ≤ (C * Z ^ ε) * (15 : ℝ) ^ k :=
      mul_le_mul (hb Z hZ (D ^ 2) hD₂) hn' (by positivity)
        (mul_nonneg hC.le (Real.rpow_nonneg hz.le _))
    _ = _ := by ring

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_support_residual_tuple_fiber_card
#print axioms HeckeSkeleton.Moments.EngineStep.actual_support_residual_tuple_injective_on_extract
#print axioms HeckeSkeleton.Moments.EngineStep.actual_support_amplifier_tuple_fiber_card
#print axioms HeckeSkeleton.Moments.EngineStep.actual_support_residual_pair_data
#print axioms HeckeSkeleton.Moments.EngineStep.actual_support_amplifier_pair_data
#print axioms HeckeSkeleton.Moments.EngineStep.support_tuple_multiplicity_subpower
#print axioms HeckeSkeleton.Moments.EngineStep.common_amplifier_fiber_subpower

