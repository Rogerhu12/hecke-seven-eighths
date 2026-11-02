import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bUnscaledAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLogProfileBounds

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Fixed supported representatives for the original exceptional profiles

The maximal annulus of the fixed rank schedule contains every actual
input window. The same original representatives, multiplied by the
prescribed two-tilt norm power, give the two plain profiles on both
comparison rectangles. Constants are selected on this fixed annulus
before the moving call, source or Fourier variable.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

namespace T3b

def profileRange (c : TargetContext K) (frame : SourceFrame) : StrictProfileRange :=
  StrictProfileRange.ofSchedule frame.lower frame.upper frame.lower_pos frame.interval.le
    (6 * (widthBand (recipeInductionSigma c) 2 + 1))

def profileWindow (c : TargetContext K) (frame : SourceFrame) : Set ℝ :=
  Set.Icc (profileRange c frame).expanded.lower (profileRange c frame).expanded.upper

theorem profileWindow_compact (c : TargetContext K) (frame : SourceFrame) :
    IsCompact (profileWindow c frame) := isCompact_Icc

theorem profileWindow_positive (c : TargetContext K) (frame : SourceFrame) :
    profileWindow c frame ⊆ Set.Ioi 0 := by
  intro x hx
  exact (profileRange c frame).expanded.lower_pos.trans_le hx.1

end T3b

namespace Call

variable {c : TargetContext K} (call : Call c)

theorem t3b_window_subset (input : ProfileInput call) :
    call.window ⊆ T3b.profileWindow c call.frame := by
  change Set.Icc (call.prepared.lower / 2) (2 * call.prepared.upper) ⊆ _
  rw [input.regular.lower, input.regular.upper]
  exact StrictProfileRange.expanded_contains_schedule call.frame.lower call.frame.upper
    call.frame.lower_pos call.frame.interval.le call.rankBound call.rank

end Call

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace RawLeafPacket

variable (packet : RawLeafPacket call p) (hpacket : packet.Realizes)
variable (input : ProfileInput call)

def t3bParentPlain (plain : Bool) : 𝓢(ℝ, ℂ) :=
  if plain then input.raw.rightRep (packet.originalReference hpacket) 0
  else input.raw.leftRep (packet.originalReference hpacket) 0

theorem t3bParentPlain_apply (plain : Bool) (x : ℝ) :
    packet.t3bParentPlain hpacket input plain x =
      (if plain then call.localizedNormProfiles.right PUnit.unit 0 x
       else call.localizedNormProfiles.left PUnit.unit 0 x) := by
  have href : call.node.data.allowedRow (packet.originalReference hpacket) :=
    ((call.node.data.rows_spec _ _).mp
      (Finset.mem_filter.mp (packet.originalReference_mem hpacket)).1).1
  cases plain with
  | false =>
    exact (input.raw.left_eq _ 0 x).symm.trans
      (call.normProfiles.left_eq PUnit.unit _ href 0 x)
  | true =>
    exact (input.raw.right_eq _ 0 x).symm.trans
      (call.normProfiles.right_eq PUnit.unit _ href 0 x)

theorem t3bParentPlain_support (plain : Bool) :
    tsupport (packet.t3bParentPlain hpacket input plain) ⊆
      T3b.profileWindow c call.frame := by
  apply Set.Subset.trans (t := call.window) ?_ (call.t3b_window_subset input)
  cases plain with
  | false =>
    exact closure_minimal (input.raw.left_support _ (Set.mem_univ _) 0
      (Set.mem_univ _)) isClosed_Icc
  | true =>
    exact closure_minimal (input.raw.right_support _ (Set.mem_univ _) 0
      (Set.mem_univ _)) isClosed_Icc

theorem t3bParentPlain_bound (plain : Bool) (orders : Finset (ℕ × ℕ))
    (horders : orders ⊆ input.orders) :
    orders.sup (schwartzSeminormFamily ℂ ℝ ℂ)
      (packet.t3bParentPlain hpacket input plain) ≤ input.amplitude := by
  have hmono : orders.sup (schwartzSeminormFamily ℂ ℝ ℂ)
      (packet.t3bParentPlain hpacket input plain) ≤
      input.orders.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        (packet.t3bParentPlain hpacket input plain) :=
    Seminorm.finset_sup_apply_le (apply_nonneg _ _)
      (fun q hq => Seminorm.le_finset_sup_apply (horders hq))
  apply hmono.trans
  cases plain with
  | false => exact input.raw.left_bound _ (Set.mem_univ _) 0 (Set.mem_univ _)
  | true => exact input.raw.right_bound _ (Set.mem_univ _) 0 (Set.mem_univ _)

def t3bNormProfile (plain : Bool) : 𝓢(ℝ, ℂ) :=
  CanonicalLogProfiles.shapeSchwartz (T3b.profileWindow c call.frame)
    (T3b.profileWindow_compact c call.frame) (T3b.profileWindow_positive c call.frame)
    (-1 + 2 * p.tilt) 0 (packet.t3bParentPlain hpacket input plain)
    (packet.t3bParentPlain_support hpacket input plain)

theorem t3bNormProfile_apply (plain : Bool) (x : ℝ) :
    packet.t3bNormProfile hpacket input plain x = packet.normProfile plain x := by
  rw [t3bNormProfile, CanonicalLogProfiles.shapeSchwartz_apply]
  change packet.t3bParentPlain hpacket input plain x *
      (((x ^ (-1 + 2 * p.tilt) : ℝ) : ℂ) *
        Complex.exp (Complex.I * (0 : ℂ) * (Real.log x : ℂ))) = _
  simp only [mul_zero, zero_mul, Complex.exp_zero, mul_one]
  rw [packet.t3bParentPlain_apply hpacket input]
  rfl

theorem t3bNormProfile_support (plain : Bool) :
    tsupport (packet.t3bNormProfile hpacket input plain) ⊆
      T3b.profileWindow c call.frame :=
  (CanonicalLogProfiles.tsupport_shapeProduct_subset (-1 + 2 * p.tilt) 0
    (packet.t3bParentPlain hpacket input plain)).trans
      (packet.t3bParentPlain_support hpacket input plain)

end RawLeafPacket

namespace T3b

/-- The original orders and scalar are fixed before every actual
parent representative and source extraction. -/
theorem exists_normProfile_bound (c : TargetContext K) (p : SourceParameters c)
    (frame : SourceFrame) (orders : Finset (ℕ × ℕ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (call : Call c) (input : ProfileInput call),
      call.frame = frame → CanonicalLogProfiles.sourceOrders orders ⊆ input.orders →
      ∀ (packet : RawLeafPacket call p) (hpacket : packet.Realizes) (plain : Bool),
        orders.sup (schwartzSeminormFamily ℂ ℝ ℂ)
          (packet.t3bNormProfile hpacket input plain) ≤ C * input.amplitude := by
  obtain ⟨C, hC, hbound⟩ := CanonicalLogProfiles.shapeSchwartz_finset_bound
    (profileWindow c frame) (profileWindow_compact c frame)
    (profileWindow_positive c frame) (-1 + 2 * p.tilt) orders
  refine ⟨C, hC, ?_⟩
  intro call input hframe horders packet hpacket plain
  have hs : tsupport (packet.t3bParentPlain hpacket input plain) ⊆ profileWindow c frame := by
    simpa only [hframe] using packet.t3bParentPlain_support hpacket input plain
  have hb := hbound 0 (packet.t3bParentPlain hpacket input plain) hs
  simp only [abs_zero, add_zero, one_pow, mul_one] at hb
  have hraw := packet.t3bParentPlain_bound hpacket input plain
    (CanonicalLogProfiles.sourceOrders orders) horders
  have hfinal := hb.trans (mul_le_mul_of_nonneg_left hraw hC)
  simpa only [RawLeafPacket.t3bNormProfile, hframe] using hfinal

/-- The two original Fourier coordinates give one norm twist. -/
def time (firstSign : ℝ) (ξ : EngineParameter) : ℝ :=
  -(2 * Real.pi * inner ℝ ξ (CanonicalLiteralLocations.direction firstSign))

theorem phase_log (firstSign : ℝ) (ξ : EngineParameter) (N : ℝ) (hN : 0 < N) :
    jointPhase ξ (-Real.log N • CanonicalLiteralLocations.direction firstSign) =
      (N : ℂ) ^ (Complex.I * (time firstSign ξ : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hN.ne'),
    ← Complex.ofReal_log hN.le]
  simp only [jointPhase, Real.fourierChar_apply, inner_smul_right, time,
    Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
  congr 1
  ring

theorem phase_ideal (firstSign : ℝ) (ξ : EngineParameter)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    jointPhase ξ (CanonicalLiteralLocations.plain firstSign I) =
      (Ideal.absNorm I.val : ℂ) ^ (Complex.I * (time firstSign ξ : ℂ)) := by
  simpa only [CanonicalLiteralLocations.plain, idealNorm, Complex.ofReal_natCast] using
    phase_log firstSign ξ (idealNorm K I) (idealNorm_pos K I)

theorem plain_mul (firstSign : ℝ)
    (B I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    CanonicalLiteralLocations.plain firstSign (B * I) =
      CanonicalLiteralLocations.plain firstSign B +
        CanonicalLiteralLocations.plain firstSign I := by
  have hm : idealNorm K (B * I) = idealNorm K B * idealNorm K I := by
    change (Ideal.absNorm (B.val * I.val) : ℝ) = _
    rw [map_mul, Nat.cast_mul]
    rfl
  simp only [CanonicalLiteralLocations.plain, hm,
    Real.log_mul (idealNorm_pos K B).ne' (idealNorm_pos K I).ne', neg_add, add_smul]

theorem phase_mul (firstSign : ℝ) (ξ : EngineParameter)
    (B I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    jointPhase ξ (CanonicalLiteralLocations.plain firstSign (B * I)) =
      jointPhase ξ (CanonicalLiteralLocations.plain firstSign B) *
        (Ideal.absNorm I.val : ℂ) ^ (Complex.I * (time firstSign ξ : ℂ)) := by
  rw [plain_mul, jointPhase_add, phase_ideal]

def phasedProfile (firstSign : ℝ) (ξ : EngineParameter)
    (B : HeckeGeneral.Analysis.NonzeroIdeal K) (φ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  jointPhase ξ (CanonicalLiteralLocations.plain firstSign B) • φ

theorem phasedProfile_support (firstSign : ℝ) (ξ : EngineParameter)
    (B : HeckeGeneral.Analysis.NonzeroIdeal K) (φ : 𝓢(ℝ, ℂ)) :
    tsupport (phasedProfile firstSign ξ B φ) ⊆ tsupport φ :=
  tsupport_mul_subset_right

theorem phasedProfile_seminorm (firstSign : ℝ) (ξ : EngineParameter)
    (B : HeckeGeneral.Analysis.NonzeroIdeal K) (φ : 𝓢(ℝ, ℂ))
    (orders : Finset (ℕ × ℕ)) :
    orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) (phasedProfile firstSign ξ B φ) =
      orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ := by
  rw [phasedProfile, map_smul_eq_mul, norm_jointPhase, one_mul]

end T3b
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Call.t3b_window_subset
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.exists_normProfile_bound
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.phase_ideal
