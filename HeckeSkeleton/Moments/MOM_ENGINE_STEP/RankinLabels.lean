import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PrimeSupportMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CommonRadical

/-!
# Counting genuine common-support labels over a number field

Exact-support Rankin counting and the existing prime-support subset bound
control complete ideal pairs and every allocation of their common primes.
The constants are chosen before the support, old mask and finite label set.

The supported-power arguments generalize openai/math
`Moments/RankinSubset.lean`; the label carrier is the actual pair of ideals
together with its selected subset of common primes.
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep.CommonSupportMass

open NumberField UniqueFactorizationMonoid
open HeckePort.IdealMobiusDivisorSum HeckePort.CenteredMomentCounting
open HeckeSkeleton.Moments.EngineStep.PrimeSupportMass

variable {K : Type} [Field K] [NumberField K]

theorem supported_power_count (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (Q : Ideal (𝓞 K)),Q ≠ 0 → ∀ S : Finset (Ideal (𝓞 K)),
      (∀ I ∈ S,I ≠ 0) → (∀ I ∈ S,primeSupport I ⊆ primeSupport Q) →
      ∀ X : ℝ,0 < X → (∀ I ∈ S,(Ideal.absNorm I:ℝ) ≤ X) →
      (S.card:ℝ) ≤ C*X^a*(Ideal.absNorm Q:ℝ)^ε := by
  obtain ⟨C,hC,hcount⟩ := fixed_support_count K a ha
  obtain ⟨D,hD,hsub⟩ := HeckePort.Moments.prime_support_subsets_bound K ε hε
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro Q hQ S hS hs X hX hN
  have hf : ∀ I ∈ S,primeSupport I ∈ (primeSupport Q).powerset :=
    fun I hI => Finset.mem_powerset.mpr (hs I hI)
  have he := Finset.card_eq_sum_card_fiberwise hf
  have hfiber (R : Finset (Ideal (𝓞 K))) (hR : R ∈ (primeSupport Q).powerset) :
      ((S.filter (fun I => primeSupport I=R)).card:ℝ) ≤ C*X^a := by
    apply hcount R _ (fun P hP => support_prime ((Finset.mem_powerset.mp hR) hP))
      (fun I hI => hS I (Finset.mem_filter.mp hI).1)
      (fun I hI => (Finset.mem_filter.mp hI).2) X hX
      (fun I hI => hN I (Finset.mem_filter.mp hI).1)
  calc
    _ = ∑ R ∈ (primeSupport Q).powerset,((S.filter (fun I => primeSupport I=R)).card:ℝ) := by
      exact_mod_cast he
    _ ≤ ∑ _R ∈ (primeSupport Q).powerset,C*X^a := Finset.sum_le_sum hfiber
    _ = (2:ℝ)^(primeSupport Q).card*(C*X^a) := by simp
    _ ≤ (D*(Ideal.absNorm Q:ℝ)^ε)*(C*X^a) :=
      mul_le_mul_of_nonneg_right (hsub Q hQ) (mul_nonneg hC.le (Real.rpow_nonneg hX.le _))
    _ = _ := by ring

theorem supported_power_pair_count (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (Q : Ideal (𝓞 K)),Q ≠ 0 → ∀ S : Finset (Ideal (𝓞 K) × Ideal (𝓞 K)),
      (∀ v ∈ S,v.1 ≠ 0 ∧ v.2 ≠ 0) →
      (∀ v ∈ S,primeSupport v.1 ⊆ primeSupport Q ∧ primeSupport v.2 ⊆ primeSupport Q) →
      ∀ X Y : ℝ,0 < X → 0 < Y →
      (∀ v ∈ S,(Ideal.absNorm v.1:ℝ) ≤ X ∧ (Ideal.absNorm v.2:ℝ) ≤ Y) →
      (S.card:ℝ) ≤ C*X^a*Y^a*(Ideal.absNorm Q:ℝ)^ε := by
  obtain ⟨C,hC,hcount⟩ := supported_power_count (K := K) a (ε/2) ha (by positivity)
  refine ⟨C^2,pow_pos hC _,?_⟩
  intro Q hQ S hS hs X Y hX hY hN
  have hfst : ((S.image Prod.fst).card:ℝ) ≤ C*X^a*(Ideal.absNorm Q:ℝ)^(ε/2) := by
    refine hcount Q hQ _ ?_ ?_ X hX ?_
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hS v hv).1
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hs v hv).1
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hN v hv).1
  have hsnd : ((S.image Prod.snd).card:ℝ) ≤ C*Y^a*(Ideal.absNorm Q:ℝ)^(ε/2) := by
    refine hcount Q hQ _ ?_ ?_ Y hY ?_
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hS v hv).2
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hs v hv).2
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hN v hv).2
  have hin : S ⊆ (S.image Prod.fst) ×ˢ (S.image Prod.snd) := by
    intro v hv
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hv,Finset.mem_image_of_mem _ hv⟩
  have hn : (0:ℝ) < Ideal.absNorm Q := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hQ)
  calc
    _ ≤ ((S.image Prod.fst).card:ℝ)*((S.image Prod.snd).card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hin).trans_eq (Finset.card_product _ _)
    _ ≤ (C*X^a*(Ideal.absNorm Q:ℝ)^(ε/2))*(C*Y^a*(Ideal.absNorm Q:ℝ)^(ε/2)) :=
      mul_le_mul hfst hsnd (Nat.cast_nonneg _) (by positivity)
    _ = C^2*X^a*Y^a*((Ideal.absNorm Q:ℝ)^(ε/2)*(Ideal.absNorm Q:ℝ)^(ε/2)) := by ring
    _ = _ := by rw [← Real.rpow_add hn]; congr 2; ring


abbrev Label (K : Type) [Field K] [NumberField K] :=
  (Ideal (𝓞 K) × Ideal (𝓞 K)) × Finset (Ideal (𝓞 K))

/-- The literal arithmetic conditions on one complete common-support label. -/
def Valid (s : Ideal (𝓞 K)) (v : Label K) : Prop :=
  v.1.1 ≠ 0 ∧ v.1.2 ≠ 0 ∧ primeSupport v.1.1 = primeSupport v.1.2 ∧
    s ∣ v.1.1 ∧ s ∣ v.1.2 ∧ v.2 ⊆ primeSupport (commonRadical v.1.1 v.1.2)

/-- Supported ideal pairs and their genuine prime-subset allocations have
a uniform small-power bound. -/
theorem partitioned_supported_pair_count (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : Ideal (𝓞 K)), Q ≠ 0 → ∀ S : Finset (Label K),
      (∀ v ∈ S, v.1.1 ≠ 0 ∧ v.1.2 ≠ 0) →
      (∀ v ∈ S, primeSupport v.1.1 ⊆ primeSupport Q ∧
        primeSupport v.1.2 ⊆ primeSupport Q) →
      (∀ v ∈ S, v.2 ⊆ primeSupport Q) →
      ∀ X Y : ℝ, 0 < X → 0 < Y →
      (∀ v ∈ S, (Ideal.absNorm v.1.1 : ℝ) ≤ X ∧
        (Ideal.absNorm v.1.2 : ℝ) ≤ Y) →
      (S.card : ℝ) ≤ C * X ^ a * Y ^ a * (Ideal.absNorm Q : ℝ) ^ ε := by
  obtain ⟨C, hC, hcount⟩ := supported_power_pair_count (K := K) a (ε / 2) ha (by positivity)
  obtain ⟨D, hD, hsub⟩ := HeckePort.Moments.prime_support_subsets_bound K (ε / 2) (by positivity)
  refine ⟨C * D, mul_pos hC hD, ?_⟩
  intro Q hQ S hS hs hpart X Y hX hY hN
  have hpairs := hcount Q hQ (S.image Prod.fst)
    (by intro v hv; obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv; exact hS w hw)
    (by intro v hv; obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv; exact hs w hw)
    X Y hX hY
    (by intro v hv; obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv; exact hN w hw)
  have hin : S ⊆ (S.image Prod.fst) ×ˢ (primeSupport Q).powerset := by
    intro v hv
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem _ hv, Finset.mem_powerset.mpr (hpart v hv)⟩
  have hc : (S.card : ℝ) ≤ ((S.image Prod.fst).card : ℝ) *
      (2 : ℝ) ^ (primeSupport Q).card := by
    have hh := Finset.card_le_card hin
    rw [Finset.card_product, Finset.card_powerset] at hh
    exact_mod_cast hh
  have hn : (0 : ℝ) < Ideal.absNorm Q := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hQ)
  calc
    _ ≤ ((S.image Prod.fst).card : ℝ) * (2 : ℝ) ^ (primeSupport Q).card := hc
    _ ≤ (C * X ^ a * Y ^ a * (Ideal.absNorm Q : ℝ) ^ (ε / 2)) *
        (D * (Ideal.absNorm Q : ℝ) ^ (ε / 2)) :=
      mul_le_mul hpairs (hsub Q hQ) (by positivity) (by positivity)
    _ = (C * D) * X ^ a * Y ^ a *
        ((Ideal.absNorm Q : ℝ) ^ (ε / 2) * (Ideal.absNorm Q : ℝ) ^ (ε / 2)) := by ring
    _ = _ := by rw [← Real.rpow_add hn]; congr 2; ring

/-- Every fiber over an actual common radical has this uniform cardinality.
The old mask and the complete label set are chosen after the constant. -/
theorem common_radical_fiber_count (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Ideal (𝓞 K)) (S : Finset (Label K)),
      (∀ v ∈ S, Valid s v) → ∀ (R : Ideal (𝓞 K)), R ≠ 0 →
      ∀ X Y : ℝ, 0 < X → 0 < Y →
      (∀ v ∈ S, (Ideal.absNorm v.1.1 : ℝ) ≤ X ∧
        (Ideal.absNorm v.1.2 : ℝ) ≤ Y) →
      ((S.filter (fun v => commonRadical v.1.1 v.1.2 = R)).card : ℝ) ≤
        C * X ^ a * Y ^ a * (Ideal.absNorm R : ℝ) ^ ε := by
  obtain ⟨C, hC, hcount⟩ := partitioned_supported_pair_count (K := K) a ε ha hε
  refine ⟨C, hC, ?_⟩
  intro s S hS R hR X Y hX hY hN
  apply hcount R hR (S.filter (fun v => commonRadical v.1.1 v.1.2 = R))
  · intro v hv
    exact ⟨(hS v (Finset.mem_filter.mp hv).1).1, (hS v (Finset.mem_filter.mp hv).1).2.1⟩
  · intro v hv
    obtain ⟨hv, hvr⟩ := Finset.mem_filter.mp hv
    have he : primeSupport R = primeSupport v.1.1 := by
      rw [← hvr, commonRadical_support, ← (hS v hv).2.2.1, Finset.inter_self]
    rw [he, (hS v hv).2.2.1]
    exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩
  · intro v hv
    obtain ⟨hv, hvr⟩ := Finset.mem_filter.mp hv
    simpa only [hvr] using (hS v hv).2.2.2.2.2
  · exact hX
  · exact hY
  · intro v hv
    exact hN v (Finset.mem_filter.mp hv).1

/-- Counting complete labels retains the old-mask density. -/
theorem partitioned_common_pair_count (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Ideal (𝓞 K)), Squarefree s → s ≠ 0 →
      ∀ S : Finset (Label K), (∀ v ∈ S, Valid s v) →
      ∀ X₁ X₂ Y : ℝ, 0 < X₁ → 0 < X₂ → 0 < Y →
      (∀ v ∈ S, (Ideal.absNorm v.1.1 : ℝ) ≤ X₁ ∧
        (Ideal.absNorm v.1.2 : ℝ) ≤ X₂) →
      (∀ v ∈ S, (Ideal.absNorm (commonRadical v.1.1 v.1.2) : ℝ) ≤ Y) →
      (S.card : ℝ) ≤ C * X₁ ^ a * X₂ ^ a * Y ^ (1 + ε) /
        (Ideal.absNorm s : ℝ) := by
  obtain ⟨C, hC, hfiber⟩ := common_radical_fiber_count (K := K) a ε ha hε
  have hKC : 0 < idealCountConstant K := zero_lt_one.trans_le (one_le_idealCountConstant K)
  refine ⟨idealCountConstant K * C, mul_pos hKC hC, ?_⟩
  intro s hs hs0 S hS X₁ X₂ Y hX₁ hX₂ hY hN hR
  let rad : Label K → Ideal (𝓞 K) := fun v => commonRadical v.1.1 v.1.2
  have hb (R : Ideal (𝓞 K)) (hRmem : R ∈ S.image rad) :
      ((S.filter (fun v => rad v = R)).card : ℝ) ≤ C * X₁ ^ a * X₂ ^ a * Y ^ ε := by
    obtain ⟨v, hv, hvR⟩ := Finset.mem_image.mp hRmem
    have hR0 : R ≠ 0 := hvR ▸ commonRadical_ne_zero v.1.1 v.1.2
    have hRN : (Ideal.absNorm R : ℝ) ≤ Y := hvR ▸ hR v hv
    exact (hfiber s S hS R hR0 X₁ X₂ hX₁ hX₂ hN).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hRN hε.le) (by positivity))
  have hrad := old_mask_radical_count S (fun v => v.1.1) (fun v => v.1.2) s hs hs0
    (fun v hv => (hS v hv).1) (fun v hv => (hS v hv).2.1)
    (fun v hv => (hS v hv).2.2.2.1) (fun v hv => (hS v hv).2.2.2.2.1) Y hY.le hR
  have he := Finset.card_eq_sum_card_fiberwise
    (fun v (hv : v ∈ S) => Finset.mem_image_of_mem rad hv)
  calc
    _ = ∑ R ∈ S.image rad, ((S.filter (fun v => rad v = R)).card : ℝ) := by exact_mod_cast he
    _ ≤ ∑ _R ∈ S.image rad, C * X₁ ^ a * X₂ ^ a * Y ^ ε := Finset.sum_le_sum hb
    _ = ((S.image rad).card : ℝ) * (C * X₁ ^ a * X₂ ^ a * Y ^ ε) := by simp
    _ ≤ (idealCountConstant K * Y / (Ideal.absNorm s : ℝ)) *
        (C * X₁ ^ a * X₂ ^ a * Y ^ ε) :=
      mul_le_mul_of_nonneg_right hrad (by positivity)
    _ = _ := by rw [Real.rpow_add hY, Real.rpow_one]; ring

end HeckeSkeleton.Moments.EngineStep.CommonSupportMass

end

#print axioms HeckeSkeleton.Moments.EngineStep.CommonSupportMass.supported_power_count
#print axioms HeckeSkeleton.Moments.EngineStep.CommonSupportMass.partitioned_common_pair_count

