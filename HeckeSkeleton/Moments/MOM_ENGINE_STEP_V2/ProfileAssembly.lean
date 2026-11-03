import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ProfileDictionary

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# A global profile dictionary gives the actual raw windows

The uniform formula certificate is an explicit input. Its chosen
degree and coefficient are used for every inverse, plain and prime
representative of the same calibrated data. The only input-order check
is inclusion in the actual original profile window. No task theorem is
imported, and the resulting representatives agree at every real point.
-/

noncomputable section
open scoped Classical SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Assembly

open NumberField
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open Blueprint EngineStep

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c}

theorem parentRepresentative_support (kind : ParentProfileKind call)
    (input : ProfileInput call) (row : NonzeroIdeal K) (time : ℝ) :
    Function.support (kind.representative input row time) ⊆ call.window := by
  cases kind with
  | inverse => exact input.raw.inverse_support row (Set.mem_univ _) time (Set.mem_univ _)
  | plain side =>
    cases side with
    | false => exact input.raw.left_support row (Set.mem_univ _) time (Set.mem_univ _)
    | true => exact input.raw.right_support row (Set.mem_univ _) time (Set.mem_univ _)
  | prime slot => exact input.raw.prime_support slot time (Set.mem_univ _)

theorem parentRepresentative_bound (kind : ParentProfileKind call)
    (input : ProfileInput call) (row : NonzeroIdeal K) (time : ℝ)
    (orders : Finset (ℕ × ℕ)) (horders : orders ⊆ input.orders) :
    orders.sup (schwartzSeminormFamily ℂ ℝ ℂ)
      (kind.representative input row time) ≤ input.amplitude := by
  have hmono : orders.sup (schwartzSeminormFamily ℂ ℝ ℂ)
      (kind.representative input row time) ≤
      input.orders.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        (kind.representative input row time) :=
    Seminorm.finset_sup_apply_le (apply_nonneg _ _)
      (fun j hj => Seminorm.le_finset_sup_apply (horders hj))
  apply hmono.trans
  cases kind with
  | inverse => exact input.raw.inverse_bound row (Set.mem_univ _) time (Set.mem_univ _)
  | plain side =>
    cases side with
    | false => exact input.raw.left_bound row (Set.mem_univ _) time (Set.mem_univ _)
    | true => exact input.raw.right_bound row (Set.mem_univ _) time (Set.mem_univ _)
  | prime slot => exact input.raw.prime_bound slot time (Set.mem_univ _)

/-- The actual representative selected by the supplied universal
formula certificate, for one specified parent profile. -/
def profileFormulaControl {input : ProfileInput call} {shape : ProfileShape}
    {scalarBound : ℝ} {window : Set ℝ} {orders : Finset (ℕ × ℕ)}
    (certificate : ProfileFormulaCertificate shape
      (call.prepared.lower / 2) (2 * call.prepared.upper) orders)
    (horders : certificate.inputOrders ⊆ input.orders)
    (hscalar : 0 ≤ scalarBound)
    (formula : OriginalProfileFormula input)
    (bounded : formula.Bounded shape scalarBound window) :
    formula.formula.SchwartzControl
      (call.prepared.lower / 2) (2 * call.prepared.upper) orders
      (certificate.coefficient * input.amplitude * scalarBound) certificate.degree := by
  apply Classical.choice
  apply certificate.control formula.formula bounded.shape_bound
  · rw [formula.original]
    exact parentRepresentative_support formula.kind input formula.row formula.time
  · exact zero_le_one.trans input.amplitude_one_le
  · exact hscalar
  · rw [formula.original]
    exact parentRepresentative_bound formula.kind input formula.row formula.time
      certificate.inputOrders horders
  · exact bounded.scalar

/-- Global equality, support and seminorm bounds are transported
together to the actual `MomentData` of every Fourier parameter. -/
def profileWindow_of_dictionary {input : ProfileInput call}
    {data : EngineParameter → MomentData K c.family.omega (targetCharacter K c)}
    {slots : ℕ} {count : ∀ ξ, (data ξ).geometry.slotCount = slots}
    {shape : ProfileShape} {scalarBound : ℝ} {window : Set ℝ}
    (dictionary : GlobalProfileDictionary input data slots count shape scalarBound window)
    {orders : Finset (ℕ × ℕ)}
    (certificate : ProfileFormulaCertificate shape
      (call.prepared.lower / 2) (2 * call.prepared.upper) orders)
    (horders : certificate.inputOrders ⊆ input.orders)
    (hscalar : 0 ≤ scalarBound) (ξ : EngineParameter) :
    RawProfileWindow Set.univ Set.univ window orders (data ξ)
      (polynomialProfileRadius
        (certificate.coefficient * input.amplitude * scalarBound)
        certificate.degree certificate.degree (WithLp.ofLp ξ)) := by
  let inverse := fun u t => profileFormulaControl certificate horders hscalar
    (dictionary.inverse u t) (dictionary.inverse_bounded u t)
  let plain := fun side u t => profileFormulaControl certificate horders hscalar
    (dictionary.plain side u t) (dictionary.plain_bounded side u t)
  let prime := fun i t => profileFormulaControl certificate horders hscalar
    (dictionary.prime i t) (dictionary.prime_bounded i t)
  exact {
    inverseRep := fun u t => (inverse u t).representative ξ
    leftRep := fun u t => (plain false u t).representative ξ
    rightRep := fun u t => (plain true u t).representative ξ
    primeRep := fun i t => (prime (Fin.cast (count ξ) i) t).representative ξ
    inverse_eq := fun u t x =>
      (dictionary.inverse_eq ξ u t x).trans ((inverse u t).value_eq ξ x).symm
    left_eq := fun u t x =>
      (dictionary.left_eq ξ u t x).trans ((plain false u t).value_eq ξ x).symm
    right_eq := fun u t x =>
      (dictionary.right_eq ξ u t x).trans ((plain true u t).value_eq ξ x).symm
    prime_eq := fun i t x =>
      (dictionary.prime_eq ξ i t x).trans
        ((prime (Fin.cast (count ξ) i) t).value_eq ξ x).symm
    inverse_support := fun u _ t _ =>
      ((inverse u t).support ξ).trans (dictionary.inverse_bounded u t).support
    left_support := fun u _ t _ =>
      ((plain false u t).support ξ).trans (dictionary.plain_bounded false u t).support
    right_support := fun u _ t _ =>
      ((plain true u t).support ξ).trans (dictionary.plain_bounded true u t).support
    prime_support := fun i t _ =>
      ((prime (Fin.cast (count ξ) i) t).support ξ).trans
        (dictionary.prime_bounded (Fin.cast (count ξ) i) t).support
    inverse_bound := fun u _ t _ => (inverse u t).bound ξ
    left_bound := fun u _ t _ => (plain false u t).bound ξ
    right_bound := fun u _ t _ => (plain true u t).bound ξ
    prime_bound := fun i t _ => (prime (Fin.cast (count ξ) i) t).bound ξ }

end HeckeSkeleton.Moments.EngineStepV2.Assembly

#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.profileFormulaControl
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.profileWindow_of_dictionary
