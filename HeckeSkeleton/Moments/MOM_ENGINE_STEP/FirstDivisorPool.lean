import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstPooledResidual

/-!
# One prime pool with the internal common divisor frozen

The internal Möbius divisor is inserted into both frozen products before
eligible primes are selected. The prime pool itself is the earlier fixed
parameter. The same original columns and physical rows are retained for
every divisor and every continuous Fourier parameter.

Only individual ideal norm windows enter the constructor. In particular,
no divisibility assertion about a later residual ideal is assumed.
-/

noncomputable section
open scoped Classical BigOperators NumberField FourierTransform SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters MeasureTheory
open HeckePort.Moments HeckePort.Moments.MobiusRegroup UniqueFactorizationMonoid
open DedekindZetaZeroFree.LargeSieve

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {P : PowerScaleExteriorPool A bad Z ell eps}
variable {ι κ : Type*}

/-- Actual divisors of the nonzero original right ideals are nonzero. -/
theorem first_divisor_pool_nonzero (right : FirstGaussPoolData C P κ)
    (S : Ideal (𝓞 K))
    (hS : S ∈ divisorPool right.columns (fun j => (right.ideal j).val)) : S ≠ 0 := by
  obtain ⟨j, hj, hSj⟩ := Finset.mem_biUnion.mp hS
  have hd := (mem_idealDivisors (right.ideal j).property.1).mp hSj
  intro hzero
  obtain ⟨J, hJ⟩ := hd
  exact (right.ideal j).property.1
    (by simpa only [hzero, zero_mul, Ideal.zero_eq_bot] using hJ)

/-- The arithmetic data may vary with the internal divisor only after
the single pool has been fixed. Both frozen products contain that divisor. -/
structure FirstDivisorPoolData
    (left : FirstGaussPoolData C P ι) (right : FirstGaussPoolData C P κ) where
  leftData : ∀ S : divisorPool right.columns (fun j => (right.ideal j).val),
    FirstGaussPoolData C P ι
  rightData : ∀ S : divisorPool right.columns (fun j => (right.ideal j).val),
    FirstGaussPoolData C P κ
  left_columns : ∀ S, (leftData S).columns = left.columns
  right_columns : ∀ S, (rightData S).columns = right.columns
  left_ideal : ∀ S, (leftData S).ideal = left.ideal
  right_ideal : ∀ S, (rightData S).ideal = right.ideal
  left_generator : ∀ S, (leftData S).generator = left.generator
  right_generator : ∀ S, (rightData S).generator = right.generator
  left_rows : ∀ S, (leftData S).rows = left.rows
  right_rows : ∀ S, (rightData S).rows = right.rows
  left_frozen : ∀ S, (leftData S).frozen = left.frozen * S.val
  right_frozen : ∀ S, (rightData S).frozen = right.frozen * S.val

namespace FirstDivisorPoolData

variable {left : FirstGaussPoolData C P ι} {right : FirstGaussPoolData C P κ}

/-- A uniform individual divisor norm window gives one uniform density
on each side. No eligible-prime count is taken as an input. -/
def ofNormWindows (left : FirstGaussPoolData C P ι)
    (right : FirstGaussPoolData C P κ) (B : ℝ)
    (hNorm : ∀ S ∈ divisorPool right.columns (fun j => (right.ideal j).val),
      (Ideal.absNorm S : ℝ) ≤ Z ^ B)
    (hleft : 0 < P.rowDensity left.rowExponent (left.frozenExponent + B))
    (hright : 0 < P.rowDensity right.rowExponent (right.frozenExponent + B)) :
    FirstDivisorPoolData left right where
  leftData S := left.withFrozenFactor S.val (first_divisor_pool_nonzero right S.val S.property)
    B (hNorm S.val S.property) hleft
  rightData S := right.withFrozenFactor S.val (first_divisor_pool_nonzero right S.val S.property)
    B (hNorm S.val S.property) hright
  left_columns _ := rfl
  right_columns _ := rfl
  left_ideal _ := rfl
  right_ideal _ := rfl
  left_generator _ := rfl
  right_generator _ := rfl
  left_rows _ := rfl
  right_rows _ := rfl
  left_frozen _ := rfl
  right_frozen _ := rfl

theorem eligible_left_avoids_divisor (p : FirstDivisorPoolData left right)
    (S : divisorPool right.columns (fun j => (right.ideal j).val))
    (hp : A.R × ExteriorPrime A) (hmem : hp ∈ (p.leftData S).eligible) :
    ¬hp.2.val.asIdeal ∣ S.val := by
  have he := (Finset.mem_filter.mp hmem).2
  change ¬hp.2.val.asIdeal ∣ ((p.leftData S).rowIdeal hp.1).val ∧
    ¬hp.2.val.asIdeal ∣ (p.leftData S).frozen at he
  rw [p.left_frozen S] at he
  intro hdiv
  exact he.2 (hdiv.trans ⟨left.frozen, mul_comm _ _⟩)

theorem eligible_right_avoids_divisor (p : FirstDivisorPoolData left right)
    (S : divisorPool right.columns (fun j => (right.ideal j).val))
    (hp : A.R × ExteriorPrime A) (hmem : hp ∈ (p.rightData S).eligible) :
    ¬hp.2.val.asIdeal ∣ S.val := by
  have he := (Finset.mem_filter.mp hmem).2
  change ¬hp.2.val.asIdeal ∣ ((p.rightData S).rowIdeal hp.1).val ∧
    ¬hp.2.val.asIdeal ∣ (p.rightData S).frozen at he
  rw [p.right_frozen S] at he
  intro hdiv
  exact he.2 (hdiv.trans ⟨right.frozen, mul_comm _ _⟩)

theorem ofNormWindows_left_density
    (B : ℝ)
    (hNorm : ∀ S ∈ divisorPool right.columns (fun j => (right.ideal j).val),
      (Ideal.absNorm S : ℝ) ≤ Z ^ B)
    (hleft : 0 < P.rowDensity left.rowExponent (left.frozenExponent + B))
    (hright : 0 < P.rowDensity right.rowExponent (right.frozenExponent + B))
    (S : divisorPool right.columns (fun j => (right.ideal j).val)) :
    ((ofNormWindows left right B hNorm hleft hright).leftData S).density =
      P.rowDensity left.rowExponent (left.frozenExponent + B) := rfl

theorem ofNormWindows_right_density
    (B : ℝ)
    (hNorm : ∀ S ∈ divisorPool right.columns (fun j => (right.ideal j).val),
      (Ideal.absNorm S : ℝ) ≤ Z ^ B)
    (hleft : 0 < P.rowDensity left.rowExponent (left.frozenExponent + B))
    (hright : 0 < P.rowDensity right.rowExponent (right.frozenExponent + B))
    (S : divisorPool right.columns (fun j => (right.ideal j).val)) :
    ((ofNormWindows left right B hNorm hleft hright).rightData S).density =
      P.rowDensity right.rowExponent (right.frozenExponent + B) := rfl

end FirstDivisorPoolData

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable (Ray : Type*) [CommGroup Ray] [Fintype Ray]
local instance : Fintype ((Ray × Ray) →* Circle) := Fintype.ofFinite _

/-- The same internal divisor occurs in the original whole coefficient,
in each frozen product, and in both pooled energies. -/
def firstDivisorPooledResidualCost
    (F : 𝓢(V, ℂ)) (left : FirstGaussPoolData C P ι) (right : FirstGaussPoolData C P κ)
    (p : FirstDivisorPoolData left right)
    (rayLeft : ι → Ray) (rayRight : κ → Ray) (phaseTable : Ray × Ray → Circle)
    (W : ℝ) (c : ι → ℂ) (d : κ → ℂ) (x : ι → V) (y : κ → V) : ℝ :=
  ∑ S : divisorPool right.columns (fun j => (right.ideal j).val), ‖(moebius S.val : ℂ)‖ *
    ∑ χ : (Ray × Ray) →* Circle, ‖fixedPhaseCoefficient Ray phaseTable χ‖ *
      ∫ ξ : V, ‖(𝓕 F) ξ‖ *
        (Real.sqrt (W * (p.leftData S).energy
          (FirstGaussPoolData.twistedCoefficient
            (fun i => if S.val ∣ (left.ideal i).val then
              c i * (fixedLeftPhase Ray χ (rayLeft i) : ℂ) else 0) x ξ)) *
         Real.sqrt (W * (p.rightData S).energy
          (FirstGaussPoolData.twistedCoefficient
            (fun j => if S.val ∣ (right.ideal j).val then
              d j * (fixedRightPhase Ray χ (rayRight j) : ℂ) else 0) (fun j => -y j) ξ)))

variable {Γ : Subgroup A.U}
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)

/-- The genuine first residual cost is bounded after freezing its
internal divisor on both sides. The common Fourier measure occurs once. -/
theorem first_residual_cost_le_divisor_pool {H : Type*}
    (F : 𝓢(V, ℂ)) (left : FirstGaussPoolData C P ι) (right : FirstGaussPoolData C P κ)
    (p : FirstDivisorPoolData left right)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (rows : Finset H) (frequency : H → A.R)
    (hinj : Set.InjOn frequency (rows : Set H))
    (hleft_rows : rows.image frequency ⊆ left.rows)
    (hright_rows : rows.image (fun h => -frequency h) ⊆ right.rows)
    (rayLeft : ι → Ray) (rayRight : κ → Ray) (phaseTable : Ray × Ray → Circle)
    (common q : H → ℂ) (W : ℝ) (hW : 0 ≤ W)
    (hq : ∀ h ∈ rows, ‖q h * common h‖ ≤ W)
    (c : ι → ℂ) (d : κ → ℂ) (x : ι → V) (y : κ → V) :
    firstResidualKernelCost hDiff Ray F rows frequency left.columns right.columns
      (fun i => (left.ideal i).val) (fun j => (right.ideal j).val)
      (fun i => generatedOriginalColumn (σ := σ) hΓ
        (left.ideal i) (left.generator i) (left.generates i))
      (fun j => generatedOriginalColumn (σ := σ) hΓ
        (right.ideal j) (right.generator j) (right.generates j))
      rayLeft rayRight phaseTable common q c d x y ≤
        firstDivisorPooledResidualCost Ray F left right p
          rayLeft rayRight phaseTable W c d x y := by
  unfold firstResidualKernelCost firstDivisorPooledResidualCost
  dsimp only
  rw [← Finset.sum_coe_sort]
  apply Finset.sum_le_sum
  intro S hS
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.sum_le_sum
  intro χ hχ
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have he := first_gauss_pool_integral_bound F (p.leftData S) (p.rightData S)
    hDiff rows frequency (fun h => -frequency h) hinj
    (fun h hh h' hh' he => hinj hh hh' (neg_injective he))
    (by simpa only [p.left_rows S] using hleft_rows)
    (by simpa only [p.right_rows S] using hright_rows)
    (fun h => q h * common h) W hW hq
    (fun i => if S.val ∣ (left.ideal i).val then
      c i * (fixedLeftPhase Ray χ (rayLeft i) : ℂ) else 0)
    (fun j => if S.val ∣ (right.ideal j).val then
      d j * (fixedRightPhase Ray χ (rayRight j) : ℂ) else 0) x y
  have hleft : (p.leftData S).gaussColumn hDiff = left.gaussColumn hDiff := by
    funext i h
    simp only [FirstGaussPoolData.gaussColumn, p.left_ideal S, p.left_generator S]
  have hright : (p.rightData S).gaussColumn hDiff = right.gaussColumn hDiff := by
    funext j h
    simp only [FirstGaussPoolData.gaussColumn, p.right_ideal S, p.right_generator S]
  rw [hleft, hright] at he
  simp only [p.left_columns S, p.right_columns S] at he
  simpa only [wholePolynomial, FirstGaussPoolData.gaussColumn,
    generatedOriginalColumn] using he

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstDivisorPoolData.eligible_left_avoids_divisor
#print axioms HeckeSkeleton.Moments.EngineStep.FirstDivisorPoolData.eligible_right_avoids_divisor
#print axioms HeckeSkeleton.Moments.EngineStep.first_residual_cost_le_divisor_pool

