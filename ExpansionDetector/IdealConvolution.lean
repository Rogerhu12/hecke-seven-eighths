import ExpansionDetector.IdealCutoff
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-! Exact Cauchy product of the genuine ideal Moebius cutoff and a
multiplicative ideal weight. The fiber is the actual multiplication of
integral ideals; no principal-ideal or unique-factorization-of-elements
assumption is used. -/
noncomputable section
namespace ExpansionDetector.IdealCutoff
open UniqueFactorizationMonoid
open scoped NumberField Classical BigOperators
variable {K : Type*} [Field K] [NumberField K]

def idealDivisors (I : Ideal (𝓞 K)) : Finset (Ideal (𝓞 K)) :=
  if I = 0 then ∅ else
    (Ideal.finite_setOfPred_absNorm_le (Ideal.absNorm I)).toFinset.filter (fun J => J ∣ I)

lemma mem_idealDivisors (I : Ideal (𝓞 K)) (hI : I ≠ 0) (J : Ideal (𝓞 K)) :
    J ∈ idealDivisors I ↔ J ∣ I := by
  simp only [idealDivisors, if_neg hI, Finset.mem_filter, Set.Finite.mem_toFinset,
    Set.mem_setOf_eq]
  constructor
  · exact And.right
  · intro h
    exact ⟨Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
      (map_dvd Ideal.absNorm h), h⟩

lemma support_product_injective {I : Ideal (𝓞 K)}
    {S T : Finset (Ideal (𝓞 K))} (hS : S ⊆ primeSupport I) (hT : T ⊆ primeSupport I)
    (h : (∏ P ∈ S, P) = ∏ P ∈ T, P) : S = T := by
  have hf := congrArg normalizedFactors h
  rw [factors_support_product hS, factors_support_product hT] at hf
  exact Finset.val_inj.mp hf

lemma squarefree_divisor_support {I J : Ideal (𝓞 K)} (hI : I ≠ 0)
    (hJ : Squarefree J) (hJI : J ∣ I) : primeSupport J ⊆ primeSupport I := by
  have hf := (dvd_iff_normalizedFactors_le_normalizedFactors hJ.ne_zero hI).mp hJI
  intro P hP
  exact Multiset.mem_toFinset.mpr (Multiset.mem_of_le hf (Multiset.mem_toFinset.mp hP))

lemma squarefree_support_product_self {J : Ideal (𝓞 K)} (hJ : Squarefree J) :
    (∏ P ∈ primeSupport J, P) = J := by
  have hn : (normalizedFactors J).Nodup :=
    (squarefree_iff_nodup_normalizedFactors hJ.ne_zero).mp hJ
  have hv : (primeSupport J).val = normalizedFactors J := by
    simpa only [primeSupport, Multiset.toFinset_val] using hn.dedup
  calc
    _ = (primeSupport J).val.prod := (Finset.prod_val _).symm
    _ = (normalizedFactors J).prod := by rw [hv]
    _ = J := Ideal.prod_normalizedFactors_eq_self hJ.ne_zero

lemma squarefree_divisors_eq_image (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
    (idealDivisors I).filter Squarefree =
      (primeSupport I).powerset.image (fun S => ∏ P ∈ S, P) := by
  ext J
  simp only [Finset.mem_filter, mem_idealDivisors I hI, Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨hJI, hJ⟩
    exact ⟨primeSupport J, squarefree_divisor_support hI hJ hJI,
      squarefree_support_product_self hJ⟩
  · rintro ⟨S, hS, rfl⟩
    exact ⟨support_product_dvd hI hS, squarefree_support_product hS⟩

/-- The powerset construction is exactly the usual ideal divisor convolution. -/
theorem coefficient_eq_divisor_sum (V : ℝ → ℂ) (D : ℝ) (I : Ideal (𝓞 K)) :
    coefficient V D I =
      ∑ J ∈ idealDivisors I, (moebius J : ℂ) * V ((Ideal.absNorm J : ℝ) / D) := by
  by_cases hI : I = 0
  · simp [hI, coefficient, idealDivisors]
  have hfilter : (∑ J ∈ idealDivisors I, (moebius J : ℂ) * V ((Ideal.absNorm J : ℝ) / D)) =
      ∑ J ∈ (idealDivisors I).filter Squarefree,
        (moebius J : ℂ) * V ((Ideal.absNorm J : ℝ) / D) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro J hJ hnot
    have hn : ¬ Squarefree J := by simpa only [Finset.mem_filter, hJ, true_and] using hnot
    rw [moebius_of_not_squarefree hn, Int.cast_zero, zero_mul]
  rw [hfilter, squarefree_divisors_eq_image I hI, Finset.sum_image]
  · simp only [coefficient, if_neg hI]
  · intro S hS T hT hST
    exact support_product_injective (Finset.mem_powerset.mp hS)
      (Finset.mem_powerset.mp hT) hST

abbrev IdealMulFiber (I : Ideal (𝓞 K)) :=
  {p : Ideal (𝓞 K) × Ideal (𝓞 K) // p.1 * p.2 = I}

def fiberFirst (I : Ideal (𝓞 K)) (p : IdealMulFiber I) :
    {J : Ideal (𝓞 K) // J ∣ I} :=
  ⟨p.val.1, ⟨p.val.2, p.property.symm⟩⟩

lemma fiberFirst_bijective (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
    Function.Bijective (fiberFirst I) := by
  constructor
  · intro p q heq
    have hfst : p.val.1 = q.val.1 := congrArg Subtype.val heq
    have hp0 : p.val.1 ≠ 0 := by
      intro hz
      apply hI
      rw [← p.property, hz, zero_mul]
    apply Subtype.ext
    apply Prod.ext hfst
    apply mul_left_cancel₀ hp0
    calc
      p.val.1 * p.val.2 = I := p.property
      _ = q.val.1 * q.val.2 := q.property.symm
      _ = p.val.1 * q.val.2 := by rw [hfst]
  · intro J
    obtain ⟨A, hA⟩ := J.property
    exact ⟨⟨(J.val, A), hA.symm⟩, rfl⟩

def idealMulFiberEquivDivisor (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
    IdealMulFiber I ≃ {J : Ideal (𝓞 K) // J ∣ I} :=
  Equiv.ofBijective (fiberFirst I) (fiberFirst_bijective I hI)

lemma divisor_tsum_eq_sum (I : Ideal (𝓞 K)) (hI : I ≠ 0) (f : Ideal (𝓞 K) → ℂ) :
    (∑' J : {J : Ideal (𝓞 K) // J ∣ I}, f J.val) = ∑ J ∈ idealDivisors I, f J := by
  let e : {J : Ideal (𝓞 K) // J ∣ I} ≃ {J : Ideal (𝓞 K) // J ∈ idealDivisors I} :=
    { toFun := fun J => ⟨J.val, (mem_idealDivisors I hI J.val).mpr J.property⟩
      invFun := fun J => ⟨J.val, (mem_idealDivisors I hI J.val).mp J.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    _ = ∑' J : {J : Ideal (𝓞 K) // J ∈ idealDivisors I}, f J.val := e.tsum_eq _
    _ = _ := Finset.tsum_subtype _ _

lemma convolution_fiber_eq (w : Ideal (𝓞 K) →*₀ ℂ) (V : ℝ → ℂ) (D : ℝ)
    (I : Ideal (𝓞 K)) :
    (∑' p : IdealMulFiber I,
      ((moebius p.val.1 : ℂ) * V ((Ideal.absNorm p.val.1 : ℝ) / D) * w p.val.1) *
        w p.val.2) = coefficient V D I * w I := by
  let a : Ideal (𝓞 K) → ℂ := fun J => (moebius J : ℂ) * V ((Ideal.absNorm J : ℝ) / D)
  have hp (p : IdealMulFiber I) : (a p.val.1 * w p.val.1) * w p.val.2 = a p.val.1 * w I := by
    rw [mul_assoc, ← map_mul, p.property]
  change (∑' p : IdealMulFiber I, (a p.val.1 * w p.val.1) * w p.val.2) = _
  simp_rw [hp]
  by_cases hI : I = 0
  · subst I
    simp only [map_zero, mul_zero, tsum_zero]
  calc
    _ = ∑' J : {J : Ideal (𝓞 K) // J ∣ I}, a J.val * w I :=
      (idealMulFiberEquivDivisor I hI).tsum_eq _
    _ = (∑' J : {J : Ideal (𝓞 K) // J ∣ I}, a J.val) * w I := tsum_mul_right
    _ = coefficient V D I * w I := by
      rw [divisor_tsum_eq_sum I hI a, coefficient_eq_divisor_sum]

/-- The actual Cauchy product, regrouped by ideal multiplication. For an
initial Dirichlet line w is the actual `idealEulerWeightHom`; the two
summability hypotheses are supplied by ordinary absolute convergence. -/
theorem weighted_convolution_hasSum (w : Ideal (𝓞 K) →*₀ ℂ) (V : ℝ → ℂ) (D : ℝ)
    (hmu : Summable (fun J : Ideal (𝓞 K) =>
      ‖(moebius J : ℂ) * V ((Ideal.absNorm J : ℝ) / D) * w J‖))
    (hw : Summable (fun J : Ideal (𝓞 K) => ‖w J‖)) :
    HasSum (fun I : Ideal (𝓞 K) => coefficient V D I * w I)
      ((∑' J : Ideal (𝓞 K), (moebius J : ℂ) * V ((Ideal.absNorm J : ℝ) / D) * w J) *
        ∑' J : Ideal (𝓞 K), w J) := by
  let a : Ideal (𝓞 K) → ℂ := fun J =>
    (moebius J : ℂ) * V ((Ideal.absNorm J : ℝ) / D) * w J
  have hs : Summable (fun p : Ideal (𝓞 K) × Ideal (𝓞 K) => a p.1 * w p.2) :=
    summable_mul_of_summable_norm hmu hw
  have hp : HasSum (fun p : Ideal (𝓞 K) × Ideal (𝓞 K) => a p.1 * w p.2)
      ((∑' J, a J) * ∑' J, w J) := by
    rw [tsum_mul_tsum_of_summable_norm hmu hw]
    exact hs.hasSum
  have hg := hp.tsum_fiberwise (fun p : Ideal (𝓞 K) × Ideal (𝓞 K) => p.1 * p.2)
  apply hg.congr_fun
  intro I
  exact (convolution_fiber_eq w V D I).symm

theorem weighted_convolution_identity (w : Ideal (𝓞 K) →*₀ ℂ) (V : ℝ → ℂ) (D : ℝ)
    (hmu : Summable (fun J : Ideal (𝓞 K) =>
      ‖(moebius J : ℂ) * V ((Ideal.absNorm J : ℝ) / D) * w J‖))
    (hw : Summable (fun J : Ideal (𝓞 K) => ‖w J‖)) :
    ((∑' J : Ideal (𝓞 K), (moebius J : ℂ) * V ((Ideal.absNorm J : ℝ) / D) * w J) *
        ∑' J : Ideal (𝓞 K), w J) =
      ∑' I : Ideal (𝓞 K), coefficient V D I * w I :=
  (weighted_convolution_hasSum w V D hmu hw).tsum_eq.symm

end ExpansionDetector.IdealCutoff
