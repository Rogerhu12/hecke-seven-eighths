import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalProfilePowerControl
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AmplifiedFiniteIndex

/-!
# Internal assembly of the same normalized kernels and arithmetic indices

These are assembly helpers, not an engine producer interface. Their
pointwise label inequalities and finite-fibre estimates must be supplied
by the original source dictionaries and finite-image counting theorems.
No total kernel mass or total arithmetic weight is assumed.

The Fourier seminorms, numerical constants, profile degrees and, for the
amplified entrance, the scale threshold precede the original profile
control, scale and moving source family. Every measure is the existing
family kernel with its already selected children.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.InternalMassAssembly

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open CommonSupportMass LocalFiniteSums

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {ω ψ : HeckeCharacter K}
variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (WithLp 2 (U × E))] [BorelSpace (WithLp 2 (U × E))]

/-- Raw polynomial radius and original Schwartz-seminorm windows for
the same finite family. These fields contain no integral estimate. -/
structure ProfileWindows {Λ : Type*} {Z : ℝ}
    (family : ActualNormalizedPairFamily A σ (WithLp 2 (U × E)) Λ ω ψ Z)
    (labels : Finset Λ) (F₁ : Λ → 𝓢(U, ℂ)) (F₂ : Λ → 𝓢(E, ℂ))
    (outer B₁ B₂ : Λ → ℝ) (P : ℝ)
    (cap J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂ : ℕ)
    (seminorms₁ seminorms₂ : Finset (ℕ × ℕ)) : Prop where
  outer_nonneg : ∀ b ∈ labels, 0 ≤ outer b
  left_radius_nonneg : ∀ b ∈ labels, 0 ≤ B₁ b
  right_radius_nonneg : ∀ b ∈ labels, 0 ≤ B₂ b
  left_slots : ∀ b ∈ labels, (family.leftSource b).allocation.keep.card ≤ cap
  right_slots : ∀ b ∈ labels, (family.rightSource b).allocation.keep.card ≤ cap
  left_radius : ∀ b ∈ labels, ∀ z,
    (family.leftCapacity b).radius (WithLp.toLp 2 z) =
      polynomialProfileRadius (B₁ b) J₁₁ J₁₂ z
  right_radius : ∀ b ∈ labels, ∀ z,
    (family.rightCapacity b).radius (WithLp.toLp 2 z) =
      polynomialProfileRadius (B₂ b) J₂₁ J₂₂ z
  left_radius_power : ∀ b ∈ labels, B₁ b ≤ P ^ dBL
  right_radius_power : ∀ b ∈ labels, B₂ b ≤ P ^ dBR
  first_kernel_power : ∀ b ∈ labels,
    seminorms₁.sup (schwartzSeminormFamily ℝ U ℂ) (F₁ b) ≤ P ^ dF₁
  second_kernel_power : ∀ b ∈ labels,
    seminorms₂.sup (schwartzSeminormFamily ℝ E ℂ) (F₂ b) ≤ P ^ dF₂

/-- The degree is fixed before the original profile control. -/
def totalProfileDegree (cap dBL dBR dF₁ dF₂ dWeight dFiber : ℕ) : ℕ :=
  originalProfilePowerDegree cap dBL dBR dF₁ dF₂ + dWeight + dFiber

private theorem sum_pointwise_index {I J : Type*} [Fintype I]
    (index : I → J) (weight : J → ℝ) (actual : I → ℝ) (factor : ℝ)
    (h : ∀ i, actual i ≤ factor * weight (index i)) :
    (∑ i, actual i) ≤ factor * ∑ i, weight (index i) := by
  calc
    _ ≤ ∑ i, factor * weight (index i) := Finset.sum_le_sum (fun i _ => h i)
    _ = _ := (Finset.mul_sum _ _ _).symm

private theorem profile_index_product
    (CF CW CM CI P Z denominator : ℝ) (dp dw dm : ℕ) (a b c : ℝ) (hZ : 0 < Z) :
    (CF * P ^ dp) *
      ((CW * P ^ dw * Z ^ a) * ((CM * P ^ dm * Z ^ b) * CI * Z ^ c / denominator)) =
      (CF * CW * CM * CI) * P ^ (dp + dw + dm) * Z ^ (a + b + c) / denominator := by
  rw [pow_add, pow_add, Real.rpow_add hZ, Real.rpow_add hZ]
  ring

private theorem drop_original_mask (mask : Ideal (𝓞 K)) (hmask : mask ≠ 0)
    {x y : ℝ} (hy : 0 ≤ y) (h : x ≤ y / (Ideal.absNorm mask : ℝ)) : x ≤ y := by
  have hn : (1 : ℝ) ≤ (Ideal.absNorm mask : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hmask)
  apply h.trans
  apply (div_le_iff₀ (zero_lt_one.trans_le hn)).2
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hn hy

/-- Internal direct-index assembly. The two supplied estimates concern
each literal source label and each actual finite fibre. The total
arithmetic mass is obtained from uniform_index_mass inside the proof. -/
theorem direct_kernel_mass_of_pointwise_index
    (cap J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂ dWeight dFiber N : ℕ)
    (normBox ε Cweight Cfiber : ℝ)
    (hbox : 0 ≤ normBox) (hε : 0 < ε)
    (hCweight : 0 < Cweight) (hCfiber : 0 < Cfiber) :
    ∃ seminorms₁ seminorms₂ : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ {Λ : Type*} (Z : ℝ), 1 < Z → ∀ P : ℝ, 1 ≤ P →
    ∀ family : ActualNormalizedPairFamily A σ (WithLp 2 (U × E)) Λ ω ψ Z,
    ∀ (labels : Finset Λ) (F₁ : Λ → 𝓢(U, ℂ)) (F₂ : Λ → 𝓢(E, ℂ))
      (outer B₁ B₂ : Λ → ℝ) (parentWidth : ℝ),
    ProfileWindows family labels F₁ F₂ outer B₁ B₂ P
      cap J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂ seminorms₁ seminorms₂ →
    ∀ mask : Ideal (𝓞 K), Squarefree mask → mask ≠ 0 →
    ∀ branch : TwoDivisorCommonBranch (K := K), branch.Admissible N normBox Z mask →
    ∀ index : family.active labels → branch.Index,
      (∀ b : family.active labels,
        outer b.val * family.weight labels parentWidth b ≤
          (Cweight * P ^ dWeight * Z ^ (ε / 4)) * branch.indexWeight (index b)) →
      (∀ j, ((Finset.univ.filter (fun b : family.active labels => index b = j)).card : ℝ) ≤
        Cfiber * P ^ dFiber * Z ^ (ε / 4)) →
      (∀ b : family.active labels,
        IsFiniteMeasure (family.kernel labels (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b)) ∧
      (∑ b : family.active labels,
        (family.kernel labels (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b).real Set.univ) ≤
          C * P ^ totalProfileDegree cap dBL dBR dF₁ dF₂ dWeight dFiber * Z ^ ε := by
  obtain ⟨seminorms₁, seminorms₂, CF, hCF, hfourier⟩ :=
    actual_finite_normalized_kernel_mass_original_profiles
      (A := A) (σ := σ) (ω := ω) (ψ := ψ) (U := U) (E := E)
      cap J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂
  obtain ⟨CI, hCI, hindex⟩ := TwoDivisorCommonBranch.uniform_index_mass (K := K)
    N normBox (ε / 2) hbox (by positivity)
  refine ⟨seminorms₁, seminorms₂, CF * Cweight * Cfiber * CI, by positivity, ?_⟩
  intro Λ Z hZ P hP family labels F₁ F₂ outer B₁ B₂ parentWidth win
    mask hmask hmask0 branch hbranch index hweight hcard
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hp : 0 ≤ P := zero_le_one.trans hP
  have hk := hfourier Z hz P hP family labels F₁ F₂ outer B₁ B₂ parentWidth
    win.outer_nonneg win.left_radius_nonneg win.right_radius_nonneg
    win.left_slots win.right_slots win.left_radius win.right_radius
    win.left_radius_power win.right_radius_power win.first_kernel_power win.second_kernel_power
  have hi := hindex Z hZ.le mask hmask hmask0 branch hbranch index
    (Cfiber * P ^ dFiber * Z ^ (ε / 4)) (by positivity) hcard
  have hs :
      (∑ b : family.active labels, outer b.val * family.weight labels parentWidth b) ≤
      (Cweight * P ^ dWeight * Z ^ (ε / 4)) *
        ((Cfiber * P ^ dFiber * Z ^ (ε / 4)) * CI * Z ^ (ε / 2) /
          (Ideal.absNorm mask : ℝ)) :=
    (sum_pointwise_index index branch.indexWeight
      (fun b => outer b.val * family.weight labels parentWidth b) _ hweight).trans
      (mul_le_mul_of_nonneg_left hi (by positivity))
  have ht := hk.2.trans (mul_le_mul_of_nonneg_left hs
    (mul_nonneg hCF.le (pow_nonneg hp _)))
  rw [profile_index_product CF Cweight Cfiber CI P Z (Ideal.absNorm mask : ℝ)
    (originalProfilePowerDegree cap dBL dBR dF₁ dF₂) dWeight dFiber
    (ε / 4) (ε / 4) (ε / 2) hz] at ht
  have he : ε / 4 + ε / 4 + ε / 2 = ε := by ring
  rw [he] at ht
  refine ⟨hk.1, ?_⟩
  simpa only [totalProfileDegree] using drop_original_mask mask hmask0 (by positivity) ht

/-- Internal one-pool assembly. The original pool and its valuation
tags stay inside the exact index. The pool loss is paid once, and the
density positivity is obtained from the proved uniform pool theorem. -/
theorem amplified_kernel_mass_of_pointwise_index
    (cap J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂ dWeight dFiber N : ℕ)
    (normBox ε Cweight Cfiber ell eps Mmax Bmax : ℝ)
    (hbox : 0 ≤ normBox) (hε : 0 < ε)
    (hCweight : 0 < Cweight) (hCfiber : 0 < Cfiber)
    (hell : 0 < ell) (heps : 0 < eps) (hepsell : eps < ell) (hepsε : eps ≤ ε / 4)
    (hMmax : 0 ≤ Mmax) (hBmax : 0 ≤ Bmax) :
    ∃ seminorms₁ seminorms₂ : Finset (ℕ × ℕ), ∃ C Z₀ : ℝ, 0 < C ∧ 1 < Z₀ ∧
    ∀ {Λ : Type*} (Z : ℝ), Z₀ ≤ Z → ∀ P : ℝ, 1 ≤ P →
    ∀ family : ActualNormalizedPairFamily A σ (WithLp 2 (U × E)) Λ ω ψ Z,
    ∀ (labels : Finset Λ) (F₁ : Λ → 𝓢(U, ℂ)) (F₂ : Λ → 𝓢(E, ℂ))
      (outer B₁ B₂ : Λ → ℝ) (parentWidth : ℝ),
    ProfileWindows family labels F₁ F₂ outer B₁ B₂ P
      cap J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂ seminorms₁ seminorms₂ →
    ∀ bad : Finset (HeightOneSpectrum (𝓞 K)),
    ∀ pool : PowerScaleExteriorPool A bad Z ell eps,
    ∀ M B : ℝ, 0 ≤ M → M ≤ Mmax → B ≤ Bmax →
    ∀ mask : Ideal (𝓞 K), Squarefree mask → mask ≠ 0 →
    ∀ main : TwoDivisorCommonBranch (K := K), main.Admissible N normBox Z mask →
    ∀ error : ℕ → ExteriorPrime A → TwoDivisorCommonBranch (K := K),
      (∀ n ∈ ({1, 6, 7} : Finset ℕ), ∀ p ∈ pool.primes,
        (error n p).Admissible N normBox Z mask) →
    ∀ index : family.active labels → AmplifiedCommonIndex pool main error,
      (∀ b : family.active labels,
        outer b.val * family.weight labels parentWidth b ≤
          (Cweight * P ^ dWeight * Z ^ (ε / 4)) *
            amplifiedIndexWeight pool M B main error (index b)) →
      (∀ j, ((Finset.univ.filter (fun b : family.active labels => index b = j)).card : ℝ) ≤
        Cfiber * P ^ dFiber * Z ^ (ε / 4)) →
      (∀ b : family.active labels,
        IsFiniteMeasure (family.kernel labels (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b)) ∧
      (∑ b : family.active labels,
        (family.kernel labels (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b).real Set.univ) ≤
          C * P ^ totalProfileDegree cap dBL dBR dF₁ dF₂ dWeight dFiber * Z ^ ε := by
  obtain ⟨seminorms₁, seminorms₂, CF, hCF, hfourier⟩ :=
    actual_finite_normalized_kernel_mass_original_profiles
      (A := A) (σ := σ) (ω := ω) (ψ := ψ) (U := U) (E := E)
      cap J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂
  obtain ⟨CI, Zindex, hCI, hZindex, hindex⟩ := amplified_finite_index_mass
    (A := A) N normBox (ε / 4) ell eps Mmax Bmax hbox (by positivity)
      hell heps hepsell hMmax hBmax
  obtain ⟨Zpool, hZpool, hpool⟩ := uniform_pool_density_and_mass (A := A)
    ell eps Mmax Bmax hell heps hepsell hMmax hBmax
  refine ⟨seminorms₁, seminorms₂, CF * Cweight * Cfiber * CI, max Zindex Zpool,
    by positivity, hZindex.trans_le (le_max_left _ _), ?_⟩
  intro Λ Z hZ P hP family labels F₁ F₂ outer B₁ B₂ parentWidth win
    bad pool M B hM hMM hBB mask hmask hmask0 main hmain error herror index hweight hcard
  have hzi : Zindex ≤ Z := (le_max_left _ _).trans hZ
  have hzp : Zpool ≤ Z := (le_max_right _ _).trans hZ
  have hZ1 : 1 < Z := hZindex.trans_le hzi
  have hz : 0 < Z := zero_lt_one.trans hZ1
  have hp : 0 ≤ P := zero_le_one.trans hP
  obtain ⟨hdensity, _, _, _⟩ := hpool Z hzp bad pool M B hMM hBB
  have hk := hfourier Z hz P hP family labels F₁ F₂ outer B₁ B₂ parentWidth
    win.outer_nonneg win.left_radius_nonneg win.right_radius_nonneg
    win.left_slots win.right_slots win.left_radius win.right_radius
    win.left_radius_power win.right_radius_power win.first_kernel_power win.second_kernel_power
  have hbase := hindex Z hzi bad pool M B hM hMM hBB mask hmask hmask0 main hmain error herror
  have hf := sum_weighted_fibres_le index (amplifiedIndexWeight pool M B main error)
    (amplifiedIndexWeight_nonneg pool M B main error hz.le hell hM hdensity.le)
    (Cfiber * P ^ dFiber * Z ^ (ε / 4)) hcard
  have hi :
      (∑ b : family.active labels, amplifiedIndexWeight pool M B main error (index b)) ≤
      (Cfiber * P ^ dFiber * Z ^ (ε / 4)) * CI * Z ^ (ε / 4 + eps) /
        (Ideal.absNorm mask : ℝ) :=
    hf.trans ((mul_le_mul_of_nonneg_left hbase (by positivity)).trans_eq (by ring))
  have hs :
      (∑ b : family.active labels, outer b.val * family.weight labels parentWidth b) ≤
      (Cweight * P ^ dWeight * Z ^ (ε / 4)) *
        ((Cfiber * P ^ dFiber * Z ^ (ε / 4)) * CI * Z ^ (ε / 4 + eps) /
          (Ideal.absNorm mask : ℝ)) :=
    (sum_pointwise_index index (amplifiedIndexWeight pool M B main error)
      (fun b => outer b.val * family.weight labels parentWidth b) _ hweight).trans
      (mul_le_mul_of_nonneg_left hi (by positivity))
  have ht := hk.2.trans (mul_le_mul_of_nonneg_left hs
    (mul_nonneg hCF.le (pow_nonneg hp _)))
  rw [profile_index_product CF Cweight Cfiber CI P Z (Ideal.absNorm mask : ℝ)
    (originalProfilePowerDegree cap dBL dBR dF₁ dF₂) dWeight dFiber
    (ε / 4) (ε / 4) (ε / 4 + eps) hz] at ht
  have hplain := drop_original_mask mask hmask0 (by positivity) ht
  have hpower : Z ^ (ε / 4 + ε / 4 + (ε / 4 + eps)) ≤ Z ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith)
  refine ⟨hk.1, ?_⟩
  exact hplain.trans (mul_le_mul_of_nonneg_left hpower (by
    change 0 ≤ (CF * Cweight * Cfiber * CI) *
      P ^ (originalProfilePowerDegree cap dBL dBR dF₁ dF₂ + dWeight + dFiber)
    positivity))

end HeckeSkeleton.Moments.EngineStep.InternalMassAssembly

#print axioms HeckeSkeleton.Moments.EngineStep.InternalMassAssembly.direct_kernel_mass_of_pointwise_index
#print axioms HeckeSkeleton.Moments.EngineStep.InternalMassAssembly.amplified_kernel_mass_of_pointwise_index
