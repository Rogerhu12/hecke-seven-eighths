import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalActiveColumnNorm

/-!
# The sharp lower norm window on the original coefficient support

A nonzero complete parent coefficient selects one of its two literal
rectangles.  Each factor of that rectangle lies above its original
scale, and the two plain scales have the prescribed common product.
This proves the lower norm window on the unchanged original carrier.
Zero cross-rectangle coefficients need no lower window.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

namespace ParentConstantAtoms

section LiteralRectangle

variable {Q : Type*} {ω ψ : HeckeCharacter K}
variable {d : MomentData K ω ψ} {a : RealParameters} {Z t Y₁ Y₂ : ℝ}
variable (atoms : ParentConstantAtoms Q d a Z t)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)} {amplitude : ℝ}
variable (profiles : RawProfileWindow rowDomain heightDomain window orders d amplitude)

include profiles

/-- The original support lower endpoint is used separately for every
occurrence. No comparison scale is bounded coordinatewise. -/
theorem original_active_rectangle_column_norm_lower
    (hZ : 0 < Z) (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Ici 1)
    (comparison : Bool)
    (hleftScale : 0 < (if comparison then Y₁ else Z ^ a.n₁))
    (hrightScale : 0 < (if comparison then Y₂ else Z ^ a.n₂))
    (hscaleProduct : (if comparison then Y₁ else Z ^ a.n₁) *
      (if comparison then Y₂ else Z ^ a.n₂) = Z ^ (a.n₁ + a.n₂))
    (v : (atoms.raw Y₁ Y₂).Column) (hv : v ∈ (atoms.raw Y₁ Y₂).columns)
    (hrectangle : (atoms.values Y₁ Y₂).rectangle comparison v ≠ 0) :
    Z ^ (a.n₁ + a.n₂ + d.geometry.totalLength) ≤
      (Ideal.absNorm ((atoms.raw Y₁ Y₂).columnIdeal v) : ℝ) := by
  have hm := Finset.mem_product.mp hv
  have hplain := Finset.mem_product.mp hm.1
  obtain ⟨u, hu, _⟩ := Finset.mem_biUnion.mp hplain.1
  have hprofiles := atoms.rectangle_profiles_ne_zero comparison v hrectangle
  have hleftRep : profiles.leftRep u t
      (idealNorm K v.1.1 / (if comparison then Y₁ else Z ^ a.n₁)) ≠ 0 := by
    simpa only [← atoms.left_profile u hu, profiles.left_eq] using hprofiles.1
  have hrightRep : profiles.rightRep u t
      (idealNorm K v.1.2 / (if comparison then Y₂ else Z ^ a.n₂)) ≠ 0 := by
    simpa only [← atoms.right_profile u hu, profiles.right_eq] using hprofiles.2.1
  have hleft : (if comparison then Y₁ else Z ^ a.n₁) ≤ idealNorm K v.1.1 := by
    simpa only [one_mul] using (le_div_iff₀ hleftScale).mp
      (hwindow (profiles.left_support u (hrows u hu) t ht hleftRep))
  have hright : (if comparison then Y₂ else Z ^ a.n₂) ≤ idealNorm K v.1.2 := by
    simpa only [one_mul] using (le_div_iff₀ hrightScale).mp
      (hwindow (profiles.right_support u (hrows u hu) t ht hrightRep))
  have hprime (i : Fin d.geometry.slotCount) :
      Z ^ (d.geometry.slots i).length ≤ (Ideal.absNorm (v.2 i).asIdeal : ℝ) := by
    have hi : profiles.primeRep i t
        ((Ideal.absNorm (v.2 i).asIdeal : ℝ) / Z ^ (d.geometry.slots i).length) ≠ 0 := by
      simpa only [profiles.prime_eq] using hprofiles.2.2 i
    simpa only [one_mul] using (le_div_iff₀ (Real.rpow_pos_of_pos hZ _)).mp
      (hwindow (profiles.prime_support i t ht hi))
  have hprod : (∏ i, Z ^ (d.geometry.slots i).length) ≤
      ∏ i, (Ideal.absNorm (v.2 i).asIdeal : ℝ) :=
    Finset.prod_le_prod₀ (fun _ _ => Real.rpow_nonneg hZ.le _) (fun i _ => hprime i)
  calc
    _ = ((if comparison then Y₁ else Z ^ a.n₁) *
          (if comparison then Y₂ else Z ^ a.n₂)) *
            ∏ i, Z ^ (d.geometry.slots i).length := by
      rw [hscaleProduct, ← Real.rpow_sum_of_pos hZ, ← Real.rpow_add hZ]
      rfl
    _ ≤ (idealNorm K v.1.1 * idealNorm K v.1.2) *
        ∏ i, (Ideal.absNorm (v.2 i).asIdeal : ℝ) :=
      mul_le_mul
        (mul_le_mul hleft hright hrightScale.le (idealNorm_pos K _).le)
        hprod (Finset.prod_nonneg (fun _ _ => Real.rpow_nonneg hZ.le _))
        (mul_nonneg (idealNorm_pos K _).le (idealNorm_pos K _).le)
    _ = _ := by
      simp only [ParentRawAtoms.columnIdeal, idealNorm, map_mul, map_prod,
        Nat.cast_mul, Nat.cast_prod]

end LiteralRectangle

section ActualExteriorCarrier

variable {A : SArithmeticData K} {Γ : Subgroup A.U}
variable {ω ψ : HeckeCharacter K} {d : MomentData K ω ψ}
variable {a : RealParameters} {Z t Y₁ Y₂ : ℝ}
variable (atoms : ParentConstantAtoms
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) d a Z t)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)} {amplitude : ℝ}
variable (profiles : RawProfileWindow rowDomain heightDomain window orders d amplitude)

include profiles

/-- Both centered rectangles give exactly the same whole lower scale.
The implication is only on the support of the actual coefficient. -/
theorem original_active_column_norm_lower
    (hZ : 0 < Z) (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Ici 1)
    (centered : Bool) (hY₁ : centered = true → 0 ≤ Y₁)
    (hcomparison : centered = true → Y₁ * Y₂ = Z ^ (a.n₁ + a.n₂))
    (v : (atoms.raw Y₁ Y₂).Column) (hv : v ∈ (atoms.raw Y₁ Y₂).exteriorColumns)
    (hcoefficient : (atoms.values Y₁ Y₂).coefficient centered v ≠ 0) :
    Z ^ (a.n₁ + a.n₂ + d.geometry.totalLength) ≤
      (Ideal.absNorm ((atoms.raw Y₁ Y₂).columnExterior v).val : ℝ) := by
  rw [(atoms.raw Y₁ Y₂).columnExterior_val_of_mem v hv]
  obtain ⟨comparison, hallowed, hrectangle⟩ :=
    (atoms.values Y₁ Y₂).coefficient_ne_zero_has_rectangle centered v hcoefficient
  have hmem : v ∈ (atoms.raw Y₁ Y₂).columns := (Finset.mem_filter.mp hv).1
  cases comparison with
  | false =>
      exact atoms.original_active_rectangle_column_norm_lower profiles hZ hrows ht hwindow
        false (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _)
        (by simpa only [Bool.false_eq_true, if_false] using
          (Real.rpow_add hZ a.n₁ a.n₂).symm) v hmem hrectangle
  | true =>
      have hc : centered = true := hallowed rfl
      have hproduct : 0 < Y₁ * Y₂ := by
        rw [hcomparison hc]
        exact Real.rpow_pos_of_pos hZ _
      have hscales : 0 < Y₁ ∧ 0 < Y₂ := by
        rcases mul_pos_iff.mp hproduct with hpos | hneg
        · exact hpos
        · exact False.elim ((not_lt_of_ge (hY₁ hc)) hneg.1)
      exact atoms.original_active_rectangle_column_norm_lower profiles hZ hrows ht hwindow
        true hscales.1 hscales.2 (hcomparison hc) v hmem hrectangle

theorem original_active_column_norm_lower_of_domain
    (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Ici 1)
    {centered : Bool} {floor padding : ℝ}
    (domain : PairedEngineDomain centered d a Z Y₁ Y₂ floor padding)
    (v : (atoms.raw Y₁ Y₂).Column) (hv : v ∈ (atoms.raw Y₁ Y₂).exteriorColumns)
    (hcoefficient : (atoms.values Y₁ Y₂).coefficient centered v ≠ 0) :
    Z ^ (a.n₁ + a.n₂ + d.geometry.totalLength) ≤
      (Ideal.absNorm ((atoms.raw Y₁ Y₂).columnExterior v).val : ℝ) :=
  atoms.original_active_column_norm_lower profiles (zero_lt_one.trans domain.scale)
    hrows ht hwindow centered domain.comparison_scale_left_nonneg
    domain.comparison_product_eq_power v hv hcoefficient

end ActualExteriorCarrier
end ParentConstantAtoms
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ParentConstantAtoms.original_active_rectangle_column_norm_lower
#print axioms HeckeSkeleton.Moments.EngineStep.ParentConstantAtoms.original_active_column_norm_lower
#print axioms HeckeSkeleton.Moments.EngineStep.ParentConstantAtoms.original_active_column_norm_lower_of_domain
