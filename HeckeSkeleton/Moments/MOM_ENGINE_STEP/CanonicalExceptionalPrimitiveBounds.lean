import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalVolume
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalUniformAmplitude

/-!
# Uniform exceptional source estimates from the original ideal series

The fixed finite character family and its original single-series volume
primitive determine one set of seminorms, one height order and one
constant.  All of them precede the moving profiles, allocations,
frequencies, masks and rectangle scales.  The profile amplitude stays
explicit as a square.

The volume controls and the centered estimate are constructed inside the
proof.  Neither a catalogue of finished volume controls nor a bound on
an exceptional source is supplied by the caller.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalVolume

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.CenteredMomentCounting

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]

/-- The primitive estimate is for a single original smoothed ideal sum.
The two absolute estimates and the one centered saving concern the same
actual allocated source, with no change to its four rectangles. -/
theorem exists_original_source_bounds
    (χ : ι → HeckeCharacter K)
    (density : ι → 𝓢(ℝ, ℂ) → ℂ)
    (remainder : ι → Seminorm ℂ (𝓢(ℝ, ℂ)))
    (hcontinuous : ∀ i, Continuous (remainder i))
    (hvolume : ∀ i (φ : 𝓢(ℝ, ℂ)) (X : ℝ), 0 < X →
      ‖(∑' I : Ideal (𝓞 K), coefficient (χ i) I *
          φ ((Ideal.absNorm I : ℝ) / X)) - (X : ℂ) * density i φ‖ ≤ remainder i φ)
    (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0)
    (ε maskExponent : ℝ) (hε : 0 < ε) (hmask : 0 ≤ maskExponent) :
    ∃ orders : Finset (ℕ × ℕ), (0, 0) ∈ orders ∧
      ∃ n : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (i : ι) (φ₁ φ₂ : 𝓢(ℝ, ℂ)),
        tsupport φ₁ ⊆ window → tsupport φ₂ ⊆ window →
        ∀ P : ℝ, 0 ≤ P →
        orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ₁ ≤ P →
        orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ₂ ≤ P →
        (∀ {g h' : A.R} {k : ℕ}
          (s : AllocatedExceptionalSource (V := V) (σ := σ)
            (coefficient (χ i)) φ₁ φ₂ g h' k),
          ‖s.ordinaryValue‖ ≤ C * P ^ 2 * s.rawMass ∧
          ‖s.value‖ ≤ C * P ^ 2 * s.rawMass) ∧
        (∀ Z : ℝ, 1 ≤ Z → ∀ {g h' : A.R} {k : ℕ}
          (s : AllocatedExceptionalSource (V := V) (σ := σ)
            (coefficient (χ i)) φ₁ φ₂ g h' k),
          s.mask ≠ ⊥ → (Ideal.absNorm s.mask : ℝ) ≤ Z ^ maskExponent →
          ∀ L : ℝ, Z ^ L ≤ s.lower →
          ‖s.value‖ ≤ C * P ^ 2 * Z ^ ε * (1 + ‖s.time‖) ^ n *
            s.rawMass * Z ^ (-max L 0)) := by
  obtain ⟨orders, hzero, n, Cv, a, b, hCv, ha, hb, hcontrols⟩ :=
    exists_uniform_volume_controls χ density remainder hcontinuous hvolume
      window hcompact hpositive
  obtain ⟨Cc, hCc, hcentered⟩ :=
    AllocatedExceptionalSource.exists_uniform_centered_constant
      (V := V) (σ := σ) b Cv ε maskExponent n
      (zero_le_one.trans hb) hCv.le hε hmask
  let Cabs := 2 * (idealCountConstant K * b) ^ 2
  have hCabs : 0 ≤ Cabs := mul_nonneg (by norm_num) (sq_nonneg _)
  let C := Cc + Cabs
  have hC : 0 < C := add_pos_of_pos_of_nonneg hCc hCabs
  have hCcC : Cc ≤ C := by dsimp only [C]; linarith
  have hCabsC : Cabs ≤ C := by dsimp only [C]; linarith
  refine ⟨orders, hzero, n, C, hC, ?_⟩
  intro i φ₁ φ₂ hs₁ hs₂ P hP hP₁ hP₂
  obtain ⟨H, hlow₁, hlow₂, hup₁, hup₂, hb₁, hb₂, hn₁, hn₂, he₁, he₂⟩ :=
    hcontrols i φ₁ φ₂ hs₁ hs₂ P hP hP₁ hP₂
  have fields : H.UniformFields b P Cv n :=
    ⟨hup₁, hup₂, hb₁, hb₂, hn₁, hn₂, he₁, he₂⟩
  constructor
  · intro g h' k s
    have habs := s.uniform_absolute H b P Cv n fields
    have hc : Cabs * P ^ 2 * s.rawMass ≤ C * P ^ 2 * s.rawMass :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCabsC (sq_nonneg P)) s.rawMass_nonneg
    constructor
    · apply habs.1.trans
      apply le_trans _ hc
      apply mul_le_mul_of_nonneg_right _ s.rawMass_nonneg
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg P)
      dsimp only [Cabs]
      nlinarith [sq_nonneg (idealCountConstant K * b)]
    · exact habs.2.trans hc
  · intro Z hZ g h' k s hR hRnorm L hL
    apply (hcentered H P hP fields Z hZ s hR hRnorm L hL).trans
    apply mul_le_mul_of_nonneg_right _
      (Real.rpow_nonneg (zero_le_one.trans hZ) _)
    apply mul_le_mul_of_nonneg_right _ s.rawMass_nonneg
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by positivity) _)
    apply mul_le_mul_of_nonneg_right _
      (Real.rpow_nonneg (zero_le_one.trans hZ) _)
    exact mul_le_mul_of_nonneg_right hCcC (sq_nonneg P)

end HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalVolume

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalVolume.exists_original_source_bounds
