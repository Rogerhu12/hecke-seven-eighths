import HeckeSkeleton.LowEnergy.ActualSymbols

/-!
# The two actual exterior sieves as ordinary-ideal kernel estimates

The hypotheses are exactly the two large-sieve inequalities permitted by
TASK.md, stated for generic K,S,D rather than importing the unfinished
Moments skeleton.  Finite sets are explicitly lifted to actual exterior
ideals; no ideal, prime support, or coefficient mass is silently changed.

The quadratic kernel is written row-first, so allowed-generator reciprocity
identifies it with the column-first quadratic sieve.  The inverse cubic
kernel is already in the target cubic sieve's column-first orientation.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.LowEnergy.ActualSieveDictionary

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckePort.CenteredMomentGenerator
open HeckeSkeleton.LowEnergy.ActualSymbols
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

/-- Verbatim generic-data version of `HeckeSkeleton.QuadraticSieveBound`. -/
def ExteriorQuadraticBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X Y : ℝ, 1 ≤ X → 1 ≤ Y →
    ∀ A B : Finset (ExteriorIdeal K S),
      (∀ I ∈ A, Squarefree I.val.val ∧ exteriorNorm K S I ≤ X) →
      (∀ J ∈ B, Squarefree J.val.val ∧ exteriorNorm K S J ≤ Y) →
      ∀ z : ExteriorIdeal K S → ℂ,
        ∑ I ∈ A, ‖∑ J ∈ B, z J * idealSymbol K S D J (D.generator I) ^ 3‖ ^ 2 ≤
          C * (X * Y) ^ ε * (X + Y) * ∑ J ∈ B, ‖z J‖ ^ 2

/-- Verbatim generic-data version of `HeckeSkeleton.CubicSieveBound`. -/
def ExteriorCubicBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X Y : ℝ, 1 ≤ X → 1 ≤ Y →
    ∀ A B : Finset (ExteriorIdeal K S),
      (∀ I ∈ A, Squarefree I.val.val ∧ exteriorNorm K S I ≤ X) →
      (∀ J ∈ B, Squarefree J.val.val ∧ exteriorNorm K S J ≤ Y) →
      ∀ e : ℤ, (e = 2 ∨ e = -2) → ∀ z : ExteriorIdeal K S → ℂ,
        ∑ I ∈ A, ‖∑ J ∈ B, z J * idealSymbol K S D J (D.generator I) ^ e‖ ^ 2 ≤
          C * (X * Y) ^ ε * (X + Y + (X * Y) ^ (2 / 3 : ℝ)) *
            ∑ J ∈ B, ‖z J‖ ^ 2

/-- Lift a genuine finite exterior support, rather than replacing it by a ball. -/
def liftIdeals (A : Finset (Ideal (𝓞 K)))
    (hA : ∀ I ∈ A, IsExterior K S I) : Finset (ExteriorIdeal K S) :=
  A.attach.image (fun I => toExterior K S I.val (hA I.val I.property))

@[simp] theorem mem_liftIdeals (A : Finset (Ideal (𝓞 K)))
    (hA : ∀ I ∈ A, IsExterior K S I) (I : ExteriorIdeal K S) :
    I ∈ liftIdeals K S A hA ↔ I.val.val ∈ A := by
  constructor
  · intro hI
    obtain ⟨j, _hj, hji⟩ := Finset.mem_image.mp hI
    have he : j.val = I.val.val := congrArg (fun J : ExteriorIdeal K S => J.val.val) hji
    exact he ▸ j.property
  · intro hI
    refine Finset.mem_image.mpr ⟨⟨I.val.val, hI⟩, Finset.mem_attach _ _, ?_⟩
    exact Subtype.ext (Subtype.ext rfl)

theorem image_liftIdeals (A : Finset (Ideal (𝓞 K)))
    (hA : ∀ I ∈ A, IsExterior K S I) :
    (liftIdeals K S A hA).image (fun I => I.val.val) = A := by
  ext I
  constructor
  · intro hI
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    exact (mem_liftIdeals K S A hA J).mp hJ
  · intro hI
    refine Finset.mem_image.mpr ⟨toExterior K S I (hA I hI), ?_, rfl⟩
    exact (mem_liftIdeals K S A hA _).mpr hI

/-- Finite reindexing preserves arbitrary coefficients and their exact norm mass. -/
theorem sum_liftIdeals {E : Type*} [AddCommMonoid E]
    (A : Finset (Ideal (𝓞 K))) (hA : ∀ I ∈ A, IsExterior K S I)
    (f : Ideal (𝓞 K) → E) :
    (∑ I ∈ liftIdeals K S A hA, f I.val.val) = ∑ I ∈ A, f I := by
  calc
    _ = ∑ I ∈ (liftIdeals K S A hA).image (fun I => I.val.val), f I := by
      rw [Finset.sum_image]
      intro I _ J _ h
      exact Subtype.ext (Subtype.ext h)
    _ = _ := by rw [image_liftIdeals]

theorem sexticSymbol_on_exterior (I J : ExteriorIdeal K S) :
    sexticSymbol K S D I.val.val J.val.val = idealSymbol K S D I (D.generator J) := by
  exact sexticSymbol_of_exterior K S D I.val.val J.val.val
    ⟨nonZeroDivisors.coe_ne_zero I.val, I.property⟩
    ⟨nonZeroDivisors.coe_ne_zero J.val, J.property⟩

/-- Column-first quadratic sieve versus row-first hybrid kernel. -/
theorem quadraticKernel_on_exterior (hD : AllowedGeneratorInput K S D)
    (I J : ExteriorIdeal K S) :
    quadraticKernel K S D I.val.val J.val.val = idealSymbol K S D J (D.generator I) ^ 3 := by
  rw [quadraticKernel, sexticSymbol_on_exterior, hD.reciprocity I J]

theorem cubicKernel_on_exterior (I J : ExteriorIdeal K S) :
    cubicKernel K S D I.val.val J.val.val =
      idealSymbol K S D I (D.generator J) ^ (-2 : ℤ) := by
  rw [cubicKernel, sexticSymbol_on_exterior]

/-- The actual quadratic estimate on ordinary ideal finite sets.
The constant is selected before scales, supports, and independent coefficients. -/
def OrdinaryQuadraticBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X Y : ℝ, 1 ≤ X → 1 ≤ Y →
    ∀ A B : Finset (Ideal (𝓞 K)),
      (∀ I ∈ A, IsExterior K S I ∧ Squarefree I ∧ (I.absNorm : ℝ) ≤ X) →
      (∀ J ∈ B, IsExterior K S J ∧ Squarefree J ∧ (J.absNorm : ℝ) ≤ Y) →
      ∀ z : Ideal (𝓞 K) → ℂ,
        ∑ I ∈ A, ‖∑ J ∈ B, z J * quadraticKernel K S D I J‖ ^ 2 ≤
          C * (X * Y) ^ ε * (X + Y) * ∑ J ∈ B, ‖z J‖ ^ 2

/-- The inverse cubic kernel retains its column-first orientation. -/
def OrdinaryCubicBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X Y : ℝ, 1 ≤ X → 1 ≤ Y →
    ∀ A B : Finset (Ideal (𝓞 K)),
      (∀ I ∈ A, IsExterior K S I ∧ Squarefree I ∧ (I.absNorm : ℝ) ≤ X) →
      (∀ J ∈ B, IsExterior K S J ∧ Squarefree J ∧ (J.absNorm : ℝ) ≤ Y) →
      ∀ z : Ideal (𝓞 K) → ℂ,
        ∑ I ∈ A, ‖∑ J ∈ B, z J * cubicKernel K S D J I‖ ^ 2 ≤
          C * (X * Y) ^ ε * (X + Y + (X * Y) ^ (2 / 3 : ℝ)) *
            ∑ J ∈ B, ‖z J‖ ^ 2

/-- Finite exact transport of the permitted quadratic sieve hypothesis. -/
theorem ordinaryQuadratic_of_exterior (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D) : OrdinaryQuadraticBound K S D := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := hquadratic ε hε
  refine ⟨C, hC, ?_⟩
  intro X Y hX hY A B hA hB z
  let hAe : ∀ I ∈ A, IsExterior K S I := fun I hI => (hA I hI).1
  let hBe : ∀ J ∈ B, IsExterior K S J := fun J hJ => (hB J hJ).1
  let A' := liftIdeals K S A hAe
  let B' := liftIdeals K S B hBe
  have hAs : ∀ I ∈ A', Squarefree I.val.val ∧ exteriorNorm K S I ≤ X := by
    intro I hI
    exact (hA I.val.val ((mem_liftIdeals K S A hAe I).mp hI)).2
  have hBs : ∀ J ∈ B', Squarefree J.val.val ∧ exteriorNorm K S J ≤ Y := by
    intro J hJ
    exact (hB J.val.val ((mem_liftIdeals K S B hBe J).mp hJ)).2
  have h := hb X Y hX hY A' B' hAs hBs (fun J => z J.val.val)
  have hinner (I : ExteriorIdeal K S) :
      (∑ J ∈ B', z J.val.val * idealSymbol K S D J (D.generator I) ^ 3) =
        ∑ J ∈ B, z J * quadraticKernel K S D I.val.val J := by
    calc
      _ = ∑ J ∈ B', z J.val.val * quadraticKernel K S D I.val.val J.val.val := by
        apply Finset.sum_congr rfl
        intro J _
        rw [quadraticKernel_on_exterior K S D hD]
      _ = _ := sum_liftIdeals K S B hBe _
  have hleft : (∑ I ∈ A',
      ‖∑ J ∈ B', z J.val.val * idealSymbol K S D J (D.generator I) ^ 3‖ ^ 2) =
      ∑ I ∈ A, ‖∑ J ∈ B, z J * quadraticKernel K S D I J‖ ^ 2 := by
    simp_rw [hinner]
    exact sum_liftIdeals K S A hAe _
  have hright : (∑ J ∈ B', ‖z J.val.val‖ ^ 2) = ∑ J ∈ B, ‖z J‖ ^ 2 :=
    sum_liftIdeals K S B hBe _
  rw [hleft, hright] at h
  exact h

/-- Finite exact transport of the permitted cubic sieve hypothesis at exponent -2. -/
theorem ordinaryCubic_of_exterior (hcubic : ExteriorCubicBound K S D) :
    OrdinaryCubicBound K S D := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := hcubic ε hε
  refine ⟨C, hC, ?_⟩
  intro X Y hX hY A B hA hB z
  let hAe : ∀ I ∈ A, IsExterior K S I := fun I hI => (hA I hI).1
  let hBe : ∀ J ∈ B, IsExterior K S J := fun J hJ => (hB J hJ).1
  let A' := liftIdeals K S A hAe
  let B' := liftIdeals K S B hBe
  have hAs : ∀ I ∈ A', Squarefree I.val.val ∧ exteriorNorm K S I ≤ X := by
    intro I hI
    exact (hA I.val.val ((mem_liftIdeals K S A hAe I).mp hI)).2
  have hBs : ∀ J ∈ B', Squarefree J.val.val ∧ exteriorNorm K S J ≤ Y := by
    intro J hJ
    exact (hB J.val.val ((mem_liftIdeals K S B hBe J).mp hJ)).2
  have h := hb X Y hX hY A' B' hAs hBs (-2) (Or.inr rfl) (fun J => z J.val.val)
  have hinner (I : ExteriorIdeal K S) :
      (∑ J ∈ B', z J.val.val * idealSymbol K S D J (D.generator I) ^ (-2 : ℤ)) =
        ∑ J ∈ B, z J * cubicKernel K S D J I.val.val := by
    calc
      _ = ∑ J ∈ B', z J.val.val * cubicKernel K S D J.val.val I.val.val := by
        apply Finset.sum_congr rfl
        intro J _
        rw [cubicKernel_on_exterior]
      _ = _ := sum_liftIdeals K S B hBe _
  have hleft : (∑ I ∈ A',
      ‖∑ J ∈ B', z J.val.val * idealSymbol K S D J (D.generator I) ^ (-2 : ℤ)‖ ^ 2) =
      ∑ I ∈ A, ‖∑ J ∈ B, z J * cubicKernel K S D J I‖ ^ 2 := by
    simp_rw [hinner]
    exact sum_liftIdeals K S A hAe _
  have hright : (∑ J ∈ B', ‖z J.val.val‖ ^ 2) = ∑ J ∈ B, ‖z J‖ ^ 2 :=
    sum_liftIdeals K S B hBe _
  rw [hleft, hright] at h
  exact h

end HeckeSkeleton.LowEnergy.ActualSieveDictionary
