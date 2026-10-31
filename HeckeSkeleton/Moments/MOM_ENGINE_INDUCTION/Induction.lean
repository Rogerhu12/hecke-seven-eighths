import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.Interface

/-!
# Three projections of the paired fourth-moment induction

The same finite-rank positive induction proves the zero-slot, positive below-one,
and positive endpoint conclusions for finite sums and continuous child measures.
The provider hypotheses below include the additional parent norm assembly.
The zero-slot result has no plain-length capacity hypothesis; the endpoint
has no zero-free hypothesis.

`SourceFamily` is the axiom-clean generalization of the exploratory source
index.  `SkeletonFamily.lean` gives exact definitional identifications with
the source model energies and original uniform-bound quantifiers.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open scoped BigOperators Classical

universe u v w

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

/-- Undo central normalization after the finite recursive bound. -/
theorem ClosedParentReduction.energy_bound {σ W : ℝ}
    {S : PolynomialSystem.{u} K ω ψ σ W} {U T t C H β δ : ℝ}
    (step : ClosedParentReduction K S U T t C H β δ)
    (hC : 0 ≤ C) (hU : 1 ≤ U) (hT : 0 ≤ T) (hH : 0 ≤ H) (hδ : 0 ≤ δ)
    (x : S.Label) :
    (S.node x).energy U t ≤
      (C * (1 + C) ^ (4 * (widthBand σ W + 1))) *
        U ^ ((S.node x).width + β + (4 * (widthBand σ W + 1) : ℕ) * δ) *
        (1 + T) ^ (H * ((4 * (widthBand σ W + 1) : ℕ) + 1)) := by
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have hnorm := step.reduction.power_bound C U T H β δ
    hC hU hT hH hδ step.terminal step.mass x
  change (S.node x).energy U t / U ^ (S.node x).width ≤ _ at hnorm
  have hraw := (div_le_iff₀ (Real.rpow_pos_of_pos hUpos _)).mp hnorm
  apply hraw.trans_eq
  rw [show (S.node x).width + β + (4 * (widthBand σ W + 1) : ℕ) * δ =
      (S.node x).width + (β + (4 * (widthBand σ W + 1) : ℕ) * δ) by ring,
    Real.rpow_add hUpos (S.node x).width (β + (4 * (widthBand σ W + 1) : ℕ) * δ)]
  ring

/-- Uniformity is proved before summing sectors.  The output constants
depend only on the common local constants and the finite state count. -/
theorem ParentReductionInput.sectorBound
    {Index : ℝ → ℝ → Type v} {Sector : Type w}
    {F : SourceFamily K ω ψ Index Sector}
    {indexMap : ∀ Z T, Index Z T → Index Z T}
    {eligible : ∀ Z T, Index Z T → Prop}
    (input : ParentReductionInput.{u} F indexMap eligible) : F.SectorBound indexMap eligible := by
  let N : ℕ := 4 * (widthBand input.sigma input.widthLimit + 1)
  refine ⟨input.heightDegree * ((N : ℝ) + 1), input.ceiling,
    mul_nonneg input.heightDegree_nonneg (by positivity), input.ceiling_pos, ?_⟩
  intro τ hτ hτc
  obtain ⟨Z₀, C, hZ₀, hC, hcert⟩ := input.certificates τ hτ hτc
  refine ⟨Z₀, C * (1 + C) ^ N, hZ₀, mul_nonneg hC (pow_nonneg (by linarith) _), ?_⟩
  intro Z hZ i hbin helig s
  obtain ⟨cert⟩ := hcert Z hZ i hbin helig s
  have hZn : 0 ≤ Z := zero_le_one.trans (hZ₀.trans hZ)
  have hT : 0 ≤ Z ^ τ := Real.rpow_nonneg hZn τ
  have hb := cert.step.energy_bound
    hC cert.base_one_le hT
    input.heightDegree_nonneg input.edgeLoss_nonneg cert.root
  have hw : (cert.system.node cert.root).width = F.rowWidth i := by
    rw [cert.root_eq]
    simp only [Node.width, Node.ordinary, SourceFamily.parameters, add_zero]
    change F.rowWidth (indexMap Z (Z ^ τ) i) = F.rowWidth i
    simp only [SourceFamily.rowWidth, input.base_at Z (Z ^ τ) i]
  rw [hw, cert.root_eq, Node.ordinary_energy] at hb
  rw [input.base_at Z (Z ^ τ) i]
  apply hb.trans
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_left
    · exact Real.rpow_le_rpow_of_exponent_le cert.base_one_le (by
        have hbudget := input.loss_budget
        linarith)
    · exact mul_nonneg hC (pow_nonneg (by linarith) _)
  · exact Real.rpow_nonneg (by linarith) _

variable {Index : ℝ → ℝ → Type v} {Sector : Type w} [Fintype Sector]

/-- The unrestricted zero-slot projection of the finite induction.
There is no hypothesis bounding the sum of the two plain lengths. -/
theorem paired_zero_slot_models
    (F : SourceFamily K ω ψ Index Sector)
    (hassembly : ParentReductionInput.{u} F F.noSlots (fun _ _ _ => True)) :
    F.ZeroSlotBound :=
  F.zeroSlotBound_of_sectorBound hassembly.sectorBound

/-- The below-one positive-slot projection.  The parent-assembly producer
receives the existing prime-product premise and is responsible for all
recursive masks and slot-removal estimates. -/
theorem paired_positive_below_one
    (F : SourceFamily K ω ψ Index Sector)
    (hκ : F.kappa < 1)
    (hprime : F.PrimeProductBound F.kappa)
    (hassembly : F.kappa < 1 → F.PrimeProductBound F.kappa →
      Nonempty (ParentReductionInput.{u} F (fun _ _ i => i)
        (fun _ _ i => F.positiveEligible i))) :
    F.PositiveSlotBound := by
  obtain ⟨input⟩ := hassembly hκ hprime
  exact F.positiveSlotBound_of_sectorBound input.sectorBound

/-- The exact endpoint projection.  Its assumptions mention no zero-free
statement and use the absolute endpoint prime-product bound. -/
theorem paired_positive_endpoint
    (F : SourceFamily K ω ψ Index Sector)
    (hκ : F.kappa = 1)
    (hprime : F.PrimeProductBound 1)
    (hassembly : F.kappa = 1 → F.PrimeProductBound 1 →
      Nonempty (ParentReductionInput.{u} F (fun _ _ i => i)
        (fun _ _ i => F.positiveEligible i))) :
    F.PositiveSlotBound := by
  obtain ⟨input⟩ := hassembly hκ hprime
  exact F.positiveSlotBound_of_sectorBound input.sectorBound

end HeckeSkeleton.Moments.EngineInduction
