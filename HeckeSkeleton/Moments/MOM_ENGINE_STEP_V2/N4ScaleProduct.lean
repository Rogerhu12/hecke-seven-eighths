import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OriginalOccurrenceData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalGaussScaleProduction

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N4: the two original occurrence extractions retain their scale product

The frozen norm includes both plain divisors and every removed prime
occurrence. Its exact cancellation is the merged base identity. The
upper annulus is paid at most once per original slot at each extraction.
All products use the original occurrence maps, including their count
transports; no scale window for the final child is an input here.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

section OneExtraction

variable {k : ℕ} {S₁ S₂ : Finset (Ideal (𝓞 K))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 K))}
variable {P : Finset (Ideal (𝓞 K))}

/-- The same exact cancellation as the base lower bound, now using
the original upper annulus. Repeated frozen primes are retained. -/
theorem residualGaussScale_mul_frozenNorm_le
    (b : SupportCartesianBranch S₁ S₂ S P)
    (Z : ℝ) (length : Fin k → ℝ) (X₁ X₂ B : ℝ) (cap : ℕ)
    (hZ : 0 < Z) (hX₁ : 0 ≤ X₁) (hX₂ : 0 ≤ X₂)
    (hB : 1 ≤ B) (hcap : k ≤ cap)
    (hprime : ∀ i ∈ Finset.univ \ b.keep,
      (Ideal.absNorm (b.witness.2 i).asIdeal : ℝ) ≤ B * Z ^ length i) :
    b.residualGaussScale Z length X₁ X₂ *
        (Ideal.absNorm (frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂
          b.keep b.witness.2) : ℝ) ≤
      B ^ cap * (X₁ * X₂ * ∏ i, Z ^ length i) := by
  have hcardKeep : (Finset.univ \ b.keep).card ≤ k := by
    simpa only [Fintype.card_fin] using
      (Finset.card_le_univ (Finset.univ \ b.keep))
  have hcard : (Finset.univ \ b.keep).card ≤ cap := hcardKeep.trans hcap
  have hfrozen :
      (∏ i ∈ Finset.univ \ b.keep, (Ideal.absNorm (b.witness.2 i).asIdeal : ℝ)) ≤
        B ^ cap * ∏ i ∈ Finset.univ \ b.keep, Z ^ length i := by
    calc
      _ ≤ ∏ i ∈ Finset.univ \ b.keep, B * Z ^ length i :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) hprime
      _ = B ^ (Finset.univ \ b.keep).card *
          ∏ i ∈ Finset.univ \ b.keep, Z ^ length i := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB hcard)
        (Finset.prod_nonneg (fun _ _ => Real.rpow_nonneg hZ.le _))
  rw [b.residualGaussScale_mul_frozenNorm, b.originalScale_product]
  have hfactor : 0 ≤ X₁ * X₂ * ∏ j, Z ^ length (SlotRestriction.index b.keep j) :=
    mul_nonneg (mul_nonneg hX₁ hX₂)
      (Finset.prod_nonneg (fun _ _ => Real.rpow_nonneg hZ.le _))
  convert mul_le_mul_of_nonneg_left hfrozen hfactor using 1 <;> ring

end OneExtraction

private theorem prod_fin_cast {n m : ℕ} (h : n = m) (f : Fin m → ℝ) :
    (∏ i : Fin n, f (Fin.cast h i)) = ∏ i : Fin m, f i := by
  subst m
  rfl

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {packet : RawLeafPacket call p} {O : OrdinaryData packet}

/-- The actual complete first frozen ideal, including the pool power
when the physical source has a nontrivial valuation tag. -/
def firstFrozenIdeal (packet : RawLeafPacket call p) (side : Bool) : Ideal (𝓞 K) :=
  let b := packet.firstBranch side
  frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂ b.keep b.witness.2

/-- The actual complete second frozen ideal. -/
def secondFrozenIdeal (packet : RawLeafPacket call p) (side : Bool) : Ideal (𝓞 K) :=
  let b := packet.secondBranch side
  frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂ b.keep b.witness.2

theorem firstFrozenIdeal_ne_zero (packet : RawLeafPacket call p) (side : Bool) :
    firstFrozenIdeal packet side ≠ 0 := frozenSourceIdeal_ne_zero _ _ _ _

theorem secondFrozenIdeal_ne_zero (packet : RawLeafPacket call p) (side : Bool) :
    secondFrozenIdeal packet side ≠ 0 := frozenSourceIdeal_ne_zero _ _ _ _

theorem secondFrozenIdeal_eq (packet : RawLeafPacket call p) (side : Bool) :
    secondFrozenIdeal packet side = packet.secondIdeal side :=
  (packet.secondBranch side).frozenSourceIdeal_eq.trans
    ((packet.firstAtlas side).branch_product
      (primeSupport packet.key.1.val.1) (packet.secondIdeal side)
      (packet.secondSupportKey side))

def firstStageProduct (D : OriginalOccurrenceData O) (side rectangle : Bool) : ℝ :=
  packet.firstPlainScale side rectangle false * packet.firstPlainScale side rectangle true *
    ∏ i : Fin (packet.firstAtlas side).slotCount,
      call.base ^ call.originalLength (D.firstIndex side i)

def beforeStageProduct (D : OriginalOccurrenceData O) (side rectangle : Bool) : ℝ :=
  D.beforePlainScale side rectangle false * D.beforePlainScale side rectangle true *
    ∏ i : Fin (O.originalSlotCount side), call.base ^ D.beforeLength side i

theorem firstStageProduct_eq (D : OriginalOccurrenceData O) (side rectangle : Bool) :
    firstStageProduct D side rectangle =
      (packet.firstBranch side).residualGaussScale call.base call.originalLength
        (call.originalPlainScale rectangle false) (call.originalPlainScale rectangle true) := by
  exact congrArg
    (fun t : ℝ =>
      packet.firstPlainScale side rectangle false * packet.firstPlainScale side rectangle true * t)
    (prod_fin_cast (D.first_count side).symm
      (fun j : Fin (packet.firstBranch side).keep.card =>
        call.base ^ call.originalLength (SlotRestriction.index (packet.firstBranch side).keep j)))

theorem beforeStageProduct_eq (D : OriginalOccurrenceData O) (side rectangle : Bool) :
    beforeStageProduct D side rectangle =
      (packet.secondBranch side).residualGaussScale call.base
        (fun i => call.originalLength (D.firstIndex side i))
        (packet.firstPlainScale side rectangle false)
        (packet.firstPlainScale side rectangle true) := by
  exact congrArg
    (fun t : ℝ =>
      D.beforePlainScale side rectangle false * D.beforePlainScale side rectangle true * t)
    (prod_fin_cast (D.second_count side).symm
      (fun j : Fin (packet.secondBranch side).keep.card =>
        call.base ^ call.originalLength
          (D.firstIndex side (SlotRestriction.index (packet.secondBranch side).keep j))))

theorem originalPlainScale_pos (rectangle plain : Bool) :
    0 < call.originalPlainScale rectangle plain := by
  cases rectangle <;> cases plain <;>
    exact Real.rpow_pos_of_pos call.base_pos _

theorem firstPlainScale_pos (packet : RawLeafPacket call p) (side rectangle plain : Bool) :
    0 < packet.firstPlainScale side rectangle plain :=
  div_pos (originalPlainScale_pos rectangle plain) (idealNorm_pos K _)

theorem originalPlainScale_product (rectangle : Bool) :
    call.originalPlainScale rectangle false * call.originalPlainScale rectangle true =
      call.base ^ (call.node.parameters.n₁ + call.node.parameters.n₂) := by
  cases rectangle with
  | false => exact (Real.rpow_add call.base_pos _ _).symm
  | true =>
    change call.base ^ call.workingComparison₁ * call.base ^ call.workingComparison₂ = _
    rw [← Real.rpow_add call.base_pos]
    apply congrArg (fun x : ℝ => call.base ^ x)
    cases hc : call.node.centered <;>
      simp only [Call.workingComparison₁, Call.workingComparison₂, hc,
        Bool.false_eq_true, if_false, if_true]
    exact call.node.comparison_sum

theorem originalScaleProduct_eq (rectangle : Bool) :
    call.originalPlainScale rectangle false * call.originalPlainScale rectangle true *
        (∏ i, call.base ^ call.originalLength i) =
      call.base ^ (call.node.parameters.n₁ + call.node.parameters.n₂ +
        call.node.parameters.z) := by
  rw [originalPlainScale_product, ← Real.rpow_sum_of_pos call.base_pos]
  have hlength : (∑ i, call.originalLength i) = call.node.parameters.z :=
    call.domain.total_length.symm
  rw [hlength, ← Real.rpow_add call.base_pos]

/-- Both extractions use the same fixed original cap. The equality of
the two comparison degrees is used before either side is estimated. -/
theorem two_extraction_compensated_le
    (D : OriginalOccurrenceData O) (side rectangle : Bool) (B : ℝ) (hB : 1 ≤ B)
    (hfirst : ∀ i ∈ Finset.univ \ (packet.firstBranch side).keep,
      (Ideal.absNorm ((packet.firstBranch side).witness.2 i).asIdeal : ℝ) ≤
        B * call.base ^ call.originalLength i)
    (hsecond : ∀ i ∈ Finset.univ \ (packet.secondBranch side).keep,
      (Ideal.absNorm ((packet.secondBranch side).witness.2 i).asIdeal : ℝ) ≤
        B * call.base ^ call.originalLength (D.firstIndex side i)) :
    beforeStageProduct D side rectangle *
        ((Ideal.absNorm (firstFrozenIdeal packet side) : ℝ) *
          (Ideal.absNorm (secondFrozenIdeal packet side) : ℝ)) ≤
      B ^ (2 * c.geometry.slots) *
        call.base ^ (call.node.parameters.n₁ + call.node.parameters.n₂ +
          call.node.parameters.z) := by
  have hcap₁ : call.localizedData.geometry.slotCount ≤ c.geometry.slots := call.slots_le
  have hcap₂ : (packet.firstAtlas side).slotCount ≤ c.geometry.slots := by
    rw [← D.first_count side]
    have hkeep : (packet.firstBranch side).keep.card ≤
        call.localizedData.geometry.slotCount := by
      simpa only [Fintype.card_fin] using (Finset.card_le_univ (packet.firstBranch side).keep)
    exact hkeep.trans hcap₁
  have h₁ := residualGaussScale_mul_frozenNorm_le (packet.firstBranch side)
    call.base call.originalLength
    (call.originalPlainScale rectangle false) (call.originalPlainScale rectangle true)
    B c.geometry.slots call.base_pos (originalPlainScale_pos rectangle false).le
    (originalPlainScale_pos rectangle true).le hB hcap₁ hfirst
  rw [← firstStageProduct_eq D side rectangle] at h₁
  change firstStageProduct D side rectangle *
    (Ideal.absNorm (firstFrozenIdeal packet side) : ℝ) ≤ _ at h₁
  have h₂ := residualGaussScale_mul_frozenNorm_le (packet.secondBranch side)
    call.base (fun i => call.originalLength (D.firstIndex side i))
    (packet.firstPlainScale side rectangle false) (packet.firstPlainScale side rectangle true)
    B c.geometry.slots call.base_pos (firstPlainScale_pos packet side rectangle false).le
    (firstPlainScale_pos packet side rectangle true).le hB hcap₂ hsecond
  rw [← beforeStageProduct_eq D side rectangle] at h₂
  change beforeStageProduct D side rectangle *
    (Ideal.absNorm (secondFrozenIdeal packet side) : ℝ) ≤
      B ^ c.geometry.slots * firstStageProduct D side rectangle at h₂
  calc
    _ = (beforeStageProduct D side rectangle *
        (Ideal.absNorm (secondFrozenIdeal packet side) : ℝ)) *
          (Ideal.absNorm (firstFrozenIdeal packet side) : ℝ) := by ring
    _ ≤ (B ^ c.geometry.slots * firstStageProduct D side rectangle) *
        (Ideal.absNorm (firstFrozenIdeal packet side) : ℝ) :=
      mul_le_mul_of_nonneg_right h₂ (Nat.cast_nonneg _)
    _ = B ^ c.geometry.slots * (firstStageProduct D side rectangle *
        (Ideal.absNorm (firstFrozenIdeal packet side) : ℝ)) := by ring
    _ ≤ B ^ c.geometry.slots * (B ^ c.geometry.slots *
        (call.originalPlainScale rectangle false * call.originalPlainScale rectangle true *
          ∏ i, call.base ^ call.originalLength i)) :=
      mul_le_mul_of_nonneg_left h₁ (pow_nonneg (zero_le_one.trans hB) _)
    _ = B ^ (2 * c.geometry.slots) *
        (call.originalPlainScale rectangle false * call.originalPlainScale rectangle true *
          ∏ i, call.base ^ call.originalLength i) := by
      rw [two_mul, pow_add]
      ring
    _ = _ := by rw [originalScaleProduct_eq]

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.residualGaussScale_mul_frozenNorm_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.two_extraction_compensated_le
