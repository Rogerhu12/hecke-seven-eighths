import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.AnnularSchwartzControl
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.SchwartzEulerControl
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ProfileTimeIndependentCore
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ProfileControlAnnulus
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ProfileNormalizationInput

/-!
# Uniform finite-order bridges for the literal moment profiles

The source and induction use weighted Euler integral seminorms. The
single-step producer uses finite Schwartz seminorms. Both comparisons
below choose their orders and constants on one fixed positive annulus,
before a model, row, height or Fourier value is selected.

The forward bridge represents the actual time-independent functions as
Schwartz maps. The reverse bridge consumes the producer's actual unit
window. A tighter, already proved support is retained in both directions;
the fixed maximal annulus is used only to choose the numerical constants.
The last theorem makes the reverse coefficient uniform over the finite
rank schedule, so the source profile envelope can absorb it once.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical NumberField SchwartzMap ContDiff BigOperators

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain Set
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.UniformAmplify
open HeckeSkeleton.Moments.EngineStep

variable {K : Type} [Field K] [NumberField K] {«ω» ψ : HeckeCharacter K}

private theorem profileSchwartzOrders_mono {s t : Finset (ℕ × ℕ)}
    (hst : s ⊆ t) (φ : SchwartzMap ℝ ℂ) :
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ ≤
      t.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ :=
  Seminorm.finset_sup_apply_le (apply_nonneg _ φ)
    (fun i hi => Seminorm.le_finset_sup_apply (hst hi))

/-- The same finite Schwartz orders control every literal inverse,
plain and prime profile. Only its actual support proof is required;
all coefficient choices precede the model and its budget. -/
theorem exists_rawWindow_modelProfileControl
    (a b : ℝ) (ha : 0 < a) (J : ℕ) (A : ℝ) :
    ∃ s : Finset (ℕ × ℕ), ∃ D : ℝ, 0 < D ∧
      ∀ (lo hi B : ℝ) (orders : Finset (ℕ × ℕ)), s ⊆ orders →
      Icc lo hi ⊆ Icc a b → ∀ (d : MomentData K «ω» ψ),
      RawProfileWindow Set.univ Set.univ (Icc lo hi) orders d B →
      ModelProfileControl d J A (D * B) 0 lo hi 0 := by
  obtain ⟨s, D, hD, hbound⟩ := exists_schwartz_sliceControl_bound a b ha J A
  refine ⟨s, D, hD, ?_⟩
  intro lo hi B orders horders hinterval d w
  have consume (φ : SchwartzMap ℝ ℂ)
      (hsupport : Function.support (φ : ℝ → ℂ) ⊆ Icc lo hi)
      (hseminorm : orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ ≤ B) :
      SliceControl J A (D * B) 0 lo hi 0 (φ : ℝ → ℂ) := by
    have h := hbound φ B (hsupport.trans hinterval)
      ((profileSchwartzOrders_mono horders φ).trans hseminorm)
    exact ⟨h.1, fun _ hy => hsupport hy, h.2.2⟩
  intro q
  cases q with
  | inverse u =>
    change SliceControl J A (D * B) 0 lo hi 0 (d.inverseTest.profile u 0)
    rw [show d.inverseTest.profile u 0 = (w.inverseRep u 0 : ℝ → ℂ) from
      funext (w.inverse_eq u 0)]
    exact consume _ (w.inverse_support u (Set.mem_univ _) 0 (Set.mem_univ _))
      (w.inverse_bound u (Set.mem_univ _) 0 (Set.mem_univ _))
  | plain₁ u =>
    change SliceControl J A (D * B) 0 lo hi 0 (d.plainTest₁.profile u 0)
    rw [show d.plainTest₁.profile u 0 = (w.leftRep u 0 : ℝ → ℂ) from
      funext (w.left_eq u 0)]
    exact consume _ (w.left_support u (Set.mem_univ _) 0 (Set.mem_univ _))
      (w.left_bound u (Set.mem_univ _) 0 (Set.mem_univ _))
  | plain₂ u =>
    change SliceControl J A (D * B) 0 lo hi 0 (d.plainTest₂.profile u 0)
    rw [show d.plainTest₂.profile u 0 = (w.rightRep u 0 : ℝ → ℂ) from
      funext (w.right_eq u 0)]
    exact consume _ (w.right_support u (Set.mem_univ _) 0 (Set.mem_univ _))
      (w.right_bound u (Set.mem_univ _) 0 (Set.mem_univ _))
  | prime i =>
    change SliceControl J A (D * B) 0 lo hi 0 ((d.geometry.slots i).profile 0)
    rw [show (d.geometry.slots i).profile 0 = (w.primeRep i 0 : ℝ → ℂ) from
      funext (w.prime_eq i 0)]
    exact consume _ (w.prime_support i 0 (Set.mem_univ _))
      (w.prime_bound i 0 (Set.mem_univ _))

/-- The concrete finite orders are selected before the backward engine
order function. Naming this choice avoids a circular order selection. -/
def eulerSchwartzOrders (a b : ℝ) (ha : 0 < a) (J : ℕ) (A : ℝ) :
    Finset (ℕ × ℕ) :=
  (exists_rawWindow_modelProfileControl (K := K) («ω» := «ω») (ψ := ψ) a b ha J A).choose

def eulerSchwartzCoefficient (a b : ℝ) (ha : 0 < a) (J : ℕ) (A : ℝ) : ℝ :=
  (exists_rawWindow_modelProfileControl (K := K) («ω» := «ω») (ψ := ψ)
    a b ha J A).choose_spec.choose

theorem eulerSchwartzCoefficient_pos (a b : ℝ) (ha : 0 < a) (J : ℕ) (A : ℝ) :
    0 < eulerSchwartzCoefficient (K := K) («ω» := «ω») (ψ := ψ) a b ha J A :=
  (exists_rawWindow_modelProfileControl (K := K) («ω» := «ω») (ψ := ψ)
    a b ha J A).choose_spec.choose_spec.1

theorem rawWindow_modelProfileControl (a b : ℝ) (ha : 0 < a) (J : ℕ) (A : ℝ)
    (lo hi B : ℝ) (orders : Finset (ℕ × ℕ))
    (horders : eulerSchwartzOrders (K := K) («ω» := «ω») (ψ := ψ) a b ha J A ⊆ orders)
    (hinterval : Icc lo hi ⊆ Icc a b) (d : MomentData K «ω» ψ)
    (w : RawProfileWindow Set.univ Set.univ (Icc lo hi) orders d B) :
    ModelProfileControl d J A
      (eulerSchwartzCoefficient (K := K) («ω» := «ω») (ψ := ψ) a b ha J A * B) 0 lo hi 0 :=
  (exists_rawWindow_modelProfileControl (K := K) («ω» := «ω») (ψ := ψ)
    a b ha J A).choose_spec.choose_spec.2 lo hi B orders horders hinterval d w

/-- The parent Euler order and raw Schwartz coefficient are chosen
before every literal model. Time independence is a proved structural
property of the prepared Mellin models; it is not an energy input. -/
theorem exists_modelProfileControl_rawWindow
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (orders : Finset (ℕ × ℕ)) :
    ∃ J : ℕ, ∃ D : ℝ, 0 < D ∧
      ∀ (lo hi A P : ℝ), 0 ≤ A → Icc lo hi ⊆ Icc a b →
      ∀ (d : MomentData K «ω» ψ), ProfileTimeIndependent d →
      ModelProfileControl d J A P 0 lo hi 0 →
      Nonempty (RawProfileWindow Set.univ Set.univ (Icc lo hi) orders d (D * P)) := by
  obtain ⟨J, D, hD, hbound⟩ := exists_sliceControl_schwartz_bound a b ha hab orders
  refine ⟨J, 2 * D, mul_pos (by norm_num) hD, ?_⟩
  intro lo hi A P hA hinterval d htime hprofiles
  have hwide : ModelProfileControl d J A P 0 a b 0 := by
    intro q
    exact ⟨(hprofiles q).1, fun y hy => hinterval ((hprofiles q).2.1 y hy),
      (hprofiles q).2.2⟩
  have hzero := modelProfileControl_weight_zero hwide hA ha hab
  choose F hF hseminorm using
    fun q : ModelProfileIndex d => hbound (modelProfile d q) (2 * P) 0 0 (hzero q)
  have hbudget (q : ModelProfileIndex d) :
      orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) (F q) ≤ (2 * D) * P := by
    calc
      _ ≤ D * (2 * P) * (1 + (0 : ℝ)) ^ (0 : ℝ) := hseminorm q
      _ = (2 * D) * P := by simp only [Real.rpow_zero, mul_one]; ring
  have hsupport (q : ModelProfileIndex d) :
      Function.support (F q : ℝ → ℂ) ⊆ Icc lo hi := by
    intro y hy
    apply (hprofiles q).2.1 y
    simpa only [Function.mem_support, hF q y] using hy
  refine ⟨{
    inverseRep := fun u _ => F (.inverse u)
    leftRep := fun u _ => F (.plain₁ u)
    rightRep := fun u _ => F (.plain₂ u)
    primeRep := fun i _ => F (.prime i)
    inverse_eq := ?_
    left_eq := ?_
    right_eq := ?_
    prime_eq := ?_
    inverse_support := fun u _ _ _ => hsupport (.inverse u)
    left_support := fun u _ _ _ => hsupport (.plain₁ u)
    right_support := fun u _ _ _ => hsupport (.plain₂ u)
    prime_support := fun i _ _ => hsupport (.prime i)
    inverse_bound := fun u _ _ _ => hbudget (.inverse u)
    left_bound := fun u _ _ _ => hbudget (.plain₁ u)
    right_bound := fun u _ _ _ => hbudget (.plain₂ u)
    prime_bound := fun i _ _ => hbudget (.prime i) }⟩
  · intro u t y
    rw [htime.inverse u t]
    exact (hF (.inverse u) y).symm
  · intro u t y
    rw [htime.plain₁ u t]
    exact (hF (.plain₁ u) y).symm
  · intro u t y
    rw [htime.plain₂ u t]
    exact (hF (.plain₂ u) y).symm
  · intro i t y
    rw [htime.prime i t]
    exact (hF (.prime i) y).symm

/-- The actual Euler order demanded by any prescribed producer input
orders. This choice is independent of all moment data. -/
def schwartzSourceEulerOrder (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (orders : Finset (ℕ × ℕ)) : ℕ :=
  (exists_modelProfileControl_rawWindow (K := K) («ω» := «ω») (ψ := ψ)
    a b ha hab orders).choose

def schwartzSourceCoefficient (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (orders : Finset (ℕ × ℕ)) : ℝ :=
  (exists_modelProfileControl_rawWindow (K := K) («ω» := «ω») (ψ := ψ)
    a b ha hab orders).choose_spec.choose

theorem schwartzSourceCoefficient_pos (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (orders : Finset (ℕ × ℕ)) :
    0 < schwartzSourceCoefficient (K := K) («ω» := «ω») (ψ := ψ) a b ha hab orders :=
  (exists_modelProfileControl_rawWindow (K := K) («ω» := «ω») (ψ := ψ)
    a b ha hab orders).choose_spec.choose_spec.1

theorem modelProfileControl_rawWindow (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (orders : Finset (ℕ × ℕ)) (lo hi A P : ℝ) (hA : 0 ≤ A)
    (hinterval : Icc lo hi ⊆ Icc a b) (d : MomentData K «ω» ψ)
    (htime : ProfileTimeIndependent d)
    (hprofiles : ModelProfileControl d
      (schwartzSourceEulerOrder (K := K) («ω» := «ω») (ψ := ψ) a b ha hab orders)
      A P 0 lo hi 0) :
    Nonempty (RawProfileWindow Set.univ Set.univ (Icc lo hi) orders d
      (schwartzSourceCoefficient (K := K) («ω» := «ω») (ψ := ψ) a b ha hab orders * P)) :=
  (exists_modelProfileControl_rawWindow (K := K) («ω» := «ω») (ψ := ψ)
    a b ha hab orders).choose_spec.choose_spec.2 lo hi A P hA hinterval d htime hprofiles

/-- All finite ranks share one numerical Euler budget. The requested
Schwartz sets may vary with the prescribed Euler order, but the common
coefficient is selected before all actual children and Fourier values. -/
theorem exists_finiteRank_rawWindow_controls
    (a b : ℝ) (ha : 0 < a) (N : ℕ) (order : ℕ → ℕ) (A : ℝ) :
    ∃ D : ℝ, 1 ≤ D ∧
      ∀ rank : ℕ, rank ≤ N → ∀ (lo hi : ℝ) (orders : Finset (ℕ × ℕ)),
      eulerSchwartzOrders (K := K) («ω» := «ω») (ψ := ψ) a b ha (order rank) A ⊆ orders →
      Icc lo hi ⊆ Icc a b →
      ∀ (d : MomentData K «ω» ψ),
      InFixedProfileWindow Set.univ Set.univ (Icc lo hi) orders d →
      ModelProfileControl d (order rank) A D 0 lo hi 0 := by
  let coefficients := fun rank =>
    eulerSchwartzCoefficient (K := K) («ω» := «ω») (ψ := ψ) a b ha (order rank) A
  have hcoefficients (rank : ℕ) : 0 < coefficients rank :=
    eulerSchwartzCoefficient_pos a b ha (order rank) A
  let D := 1 + ∑ rank ∈ Finset.range (N + 1), coefficients rank
  have hsum : 0 ≤ ∑ rank ∈ Finset.range (N + 1), coefficients rank :=
    Finset.sum_nonneg (fun rank _ => (hcoefficients rank).le)
  have hD : 1 ≤ D := by dsimp only [D]; linarith
  refine ⟨D, hD, ?_⟩
  intro rank hrank lo hi orders horders hinterval d hwindow
  obtain ⟨w⟩ := hwindow
  have hc : coefficients rank ≤ D := by
    have hsingle := Finset.single_le_sum (fun r _ => (hcoefficients r).le)
      (Finset.mem_range.mpr (show rank < N + 1 by omega))
    dsimp only [D]
    linarith
  have h := rawWindow_modelProfileControl a b ha (order rank) A
    lo hi 1 orders horders hinterval d w
  apply modelProfileControl_fixed_budget h
  simpa only [mul_one, Real.rpow_zero] using hc

end HeckeSkeleton.Moments.EngineInduction

#print axioms HeckeSkeleton.Moments.EngineInduction.exists_rawWindow_modelProfileControl
#print axioms HeckeSkeleton.Moments.EngineInduction.exists_modelProfileControl_rawWindow
#print axioms HeckeSkeleton.Moments.EngineInduction.exists_finiteRank_rawWindow_controls
