import HeckeSkeleton.Moments.MOM_INV_STEP.LogLatticeCounting
import HeckeGeneral.Arithmetic.SUnitFiniteGeneration
import HeckeGeneral.Arithmetic.SUnitArchimedeanBalancing

/-!
# Actual S-unit logarithmic boxes

The finite valuation vector is the repository's actual S-unit valuation
map. Two S-units in one fiber have a quotient in the ordinary unit group;
the integral unit is constructed through the proved empty-S equivalence.
Finite valuation boxes and the actual unit log lattice therefore give a
polynomial count in the joint logarithmic height.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SUnitLogCounting

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open LogLatticeCounting
open scoped Classical BigOperators

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

def valuationVector (u : S.unit K) : S → ℤ :=
  fun v => (sUnitValuations K S u v).toAdd

def archLog (u : S.unit K) (w : InfinitePlace K) : ℝ :=
  (InfinitePlace.mult w : ℝ) * Real.log (w ((u : Kˣ) : K))

theorem archLog_div (u v : S.unit K) (w : InfinitePlace K) :
    archLog K S (u / v) w = archLog K S u w - archLog K S v w := by
  have hu : w ((u : Kˣ) : K) ≠ 0 :=
    (InfinitePlace.pos_iff.mpr (u : Kˣ).ne_zero).ne'
  have hv : w ((v : Kˣ) : K) ≠ 0 :=
    (InfinitePlace.pos_iff.mpr (v : Kˣ).ne_zero).ne'
  change (InfinitePlace.mult w : ℝ) * Real.log
    (w (((u : Kˣ) : K) / ((v : Kˣ) : K))) = _
  rw [map_div₀, Real.log_div hu hv, mul_sub]

def kernelUnit (u : S.unit K) (hu : sUnitValuations K S u = 1) : (𝓞 K)ˣ :=
  Set.unitEmptyEquivUnits K ⟨u.val, by
    have hk : u ∈ (sUnitValuations K S).ker := hu
    rw [sUnitValuations_ker K S] at hk
    exact hk⟩

@[simp] theorem kernelUnit_coe (u : S.unit K) (hu : sUnitValuations K S u = 1) :
    algebraMap (𝓞 K) K (kernelUnit K S u hu : 𝓞 K) = ((u : Kˣ) : K) :=
  Set.algebraMap_unitEmptyEquivUnits_apply K _

theorem valuations_eq_of_vector_eq (u v : S.unit K)
    (h : valuationVector K S u = valuationVector K S v) :
    sUnitValuations K S u = sUnitValuations K S v := by
  funext p
  apply Multiplicative.toAdd.injective
  exact congrFun h p

/-- An actual integral unit representing the quotient in a valuation
fiber. The construction uses no section or chosen principal generator. -/
def ordinaryRatio (u v : S.unit K)
    (h : valuationVector K S u = valuationVector K S v) : (𝓞 K)ˣ :=
  kernelUnit K S (u / v) (by
    rw [map_div, valuations_eq_of_vector_eq K S u v h, div_self])

@[simp] theorem ordinaryRatio_coe (u v : S.unit K)
    (h : valuationVector K S u = valuationVector K S v) :
    algebraMap (𝓞 K) K (ordinaryRatio K S u v h : 𝓞 K) =
      ((u : Kˣ) : K) / ((v : Kˣ) : K) := kernelUnit_coe K S (u / v) _

theorem ordinaryRatio_injective_left (v u₁ u₂ : S.unit K)
    (h₁ : valuationVector K S u₁ = valuationVector K S v)
    (h₂ : valuationVector K S u₂ = valuationVector K S v)
    (h : ordinaryRatio K S u₁ v h₁ = ordinaryRatio K S u₂ v h₂) : u₁ = u₂ := by
  have he := congrArg (fun a : (𝓞 K)ˣ => algebraMap (𝓞 K) K (a : 𝓞 K)) h
  rw [ordinaryRatio_coe, ordinaryRatio_coe] at he
  apply Subtype.ext
  apply Units.ext
  exact (div_left_inj' (v : Kˣ).ne_zero).mp he

theorem ordinaryRatio_log (u v : S.unit K)
    (h : valuationVector K S u = valuationVector K S v)
    (w : {w : InfinitePlace K // w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    NumberField.Units.logEmbedding K (Additive.ofMul (ordinaryRatio K S u v h)) w =
      archLog K S u w.val - archLog K S v w.val := by
  change (InfinitePlace.mult w.val : ℝ) * Real.log
    (w.val (algebraMap (𝓞 K) K (ordinaryRatio K S u v h : 𝓞 K))) = _
  rw [ordinaryRatio_coe]
  exact archLog_div K S u v w.val

theorem ordinaryRatio_log_norm_le (u v : S.unit K)
    (h : valuationVector K S u = valuationVector K S v)
    (T : ℝ) (hT : 0 ≤ T)
    (hu : ∀ w : InfinitePlace K, |archLog K S u w| ≤ T)
    (hv : ∀ w : InfinitePlace K, |archLog K S v w| ≤ T) :
    ‖NumberField.Units.logEmbedding K (Additive.ofMul (ordinaryRatio K S u v h))‖ ≤ 2 * T := by
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * T)).mpr
  intro w
  rw [ordinaryRatio_log, Real.norm_eq_abs]
  exact (abs_sub _ _).trans ((add_le_add (hu w.val) (hv w.val)).trans_eq (two_mul T).symm)

/-- Uniform bound for every actual finite valuation fiber. Choosing one
unit in that fiber is used only to inject its elements into ordinary units. -/
theorem valuation_fiber_card_le (M : ℕ) (hM : NumberField.Units.rank K < M)
    (T : ℝ) (hT : 0 ≤ T) (s : Finset (S.unit K))
    (hs : ∀ u ∈ s, ∀ w : InfinitePlace K, |archLog K S u w| ≤ T)
    (e : S → ℤ) :
    ((s.filter (fun u => valuationVector K S u = e)).card : ℝ) ≤
      (Nat.card (NumberField.Units.torsion K) : ℝ) *
        (1 + (2 * T) ^ M * latticeInversePowerMass (NumberField.Units.unitLattice K) M) := by
  let t := s.filter (fun u => valuationVector K S u = e)
  change (t.card : ℝ) ≤ _
  have hmass : 0 ≤ latticeInversePowerMass (NumberField.Units.unitLattice K) M :=
    tsum_nonneg (fun _ => by positivity)
  by_cases ht : t.Nonempty
  · obtain ⟨u₀, hu₀⟩ := ht
    have h₀ : valuationVector K S u₀ = e := (Finset.mem_filter.mp hu₀).2
    let f : t → (𝓞 K)ˣ := fun u => ordinaryRatio K S u.val u₀
      ((Finset.mem_filter.mp u.property).2.trans h₀.symm)
    have hf : Function.Injective f := by
      intro u v huv
      apply Subtype.ext
      exact ordinaryRatio_injective_left K S u₀ u.val v.val _ _ huv
    have hcard : (t.attach.image f).card = t.card := by
      rw [Finset.card_image_of_injective _ hf, Finset.card_attach]
    have hb := ordinary_unit_log_count K M hM (2 * T) (by positivity)
      (t.attach.image f) (by
        intro u hu
        obtain ⟨v, _hv, rfl⟩ := Finset.mem_image.mp hu
        exact ordinaryRatio_log_norm_le K S v.val u₀ _ T hT
          (hs v.val (Finset.mem_filter.mp v.property).1)
          (hs u₀ (Finset.mem_filter.mp hu₀).1))
    rwa [hcard] at hb
  · rw [Finset.not_nonempty_iff_eq_empty.mp ht, Finset.card_empty, Nat.cast_zero]
    positivity

theorem valuation_image_card_le (N : ℕ) (s : Finset (S.unit K))
    (hs : ∀ u ∈ s, ∀ v : S, |valuationVector K S u v| ≤ (N : ℤ)) :
    (s.image (valuationVector K S)).card ≤ (2 * N + 1) ^ Fintype.card S := by
  have hsub : s.image (valuationVector K S) ⊆
      Fintype.piFinset (fun _ : S => Finset.Icc (-(N : ℤ)) (N : ℤ)) := by
    intro e he
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp he
    rw [Fintype.mem_piFinset]
    intro v
    exact Finset.mem_Icc.mpr (abs_le.mp (hs u hu v))
  have hI : (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1 := by
    rw [Int.card_Icc]
    omega
  have hcard : (Fintype.piFinset (fun _ : S => Finset.Icc (-(N : ℤ)) (N : ℤ))).card =
      (2 * N + 1) ^ Fintype.card S := by
    simp only [Fintype.card_piFinset, hI, Finset.prod_const, Finset.card_univ]
  exact (Finset.card_le_card hsub).trans_eq hcard

/-- Genuine S-unit log-box counting: a finite integer valuation box
times the proved ordinary-unit logarithmic count. -/
theorem sunit_log_box_count (M : ℕ) (hM : NumberField.Units.rank K < M)
    (N : ℕ) (T : ℝ) (hT : 0 ≤ T) (s : Finset (S.unit K))
    (harch : ∀ u ∈ s, ∀ w : InfinitePlace K, |archLog K S u w| ≤ T)
    (hfin : ∀ u ∈ s, ∀ v : S, |valuationVector K S u v| ≤ (N : ℤ)) :
    (s.card : ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ) ^ Fintype.card S *
      ((Nat.card (NumberField.Units.torsion K) : ℝ) *
        (1 + (2 * T) ^ M * latticeInversePowerMass (NumberField.Units.unitLattice K) M)) := by
  let C := (Nat.card (NumberField.Units.torsion K) : ℝ) *
    (1 + (2 * T) ^ M * latticeInversePowerMass (NumberField.Units.unitLattice K) M)
  have hmass : 0 ≤ latticeInversePowerMass (NumberField.Units.unitLattice K) M :=
    tsum_nonneg (fun _ => by positivity)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hcard : (s.card : ℝ) = ∑ e ∈ s.image (valuationVector K S),
      ((s.filter (fun u => valuationVector K S u = e)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image (valuationVector K S) s
  have himage : ((s.image (valuationVector K S)).card : ℝ) ≤
      ((2 * N + 1 : ℕ) : ℝ) ^ Fintype.card S := by
    exact_mod_cast valuation_image_card_le K S N s hfin
  calc
    _ = ∑ e ∈ s.image (valuationVector K S),
        ((s.filter (fun u => valuationVector K S u = e)).card : ℝ) := hcard
    _ ≤ ∑ _e ∈ s.image (valuationVector K S), C :=
      Finset.sum_le_sum (fun e _ => valuation_fiber_card_le K S M hM T hT s harch e)
    _ = ((s.image (valuationVector K S)).card : ℝ) * C := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right himage hC

end HeckeSkeleton.Moments.MOM_INV_STEP.SUnitLogCounting

end
