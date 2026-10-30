import ThetaGlobal.GlobalFrequencyReconstruction
import ThetaGlobal.GlobalUnitCoordinates

/-!
# Actual exterior ideals for the reconstructed frequency coordinates

The numerical reconstruction is converted to the *same* arithmetic
datum's exterior ideals by its prime-exponent equivalence.  No principal
ideal generator is chosen afresh: all representatives use the supplied
allowed recipe G, and the unit sector uses the stored representatives U.

This is the arithmetic part of support reindexing.  Its input is the
local valuation support condition, which must be obtained from the
local digit table; it does not take a theta identity as an input.
Project-facing file: compilation status is reported separately.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace ThetaGlobal.GlobalIdealCoordinates

open NumberField DedekindZetaZeroFree DedekindZetaZeroFree.ThetaBranch
open scoped NumberField Classical BigOperators

variable {F : Type} [Field F] [NumberField F]
  (A : SArithmeticData F)

abbrev exponent (I : A.Exterior) (p : ExteriorPrime A) : ℕ :=
  idealPrimeExponent p.val.asIdeal I.val

def idealOfExponents (f : ExteriorPrime A → ℕ)
    (hf : {p | f p ≠ 0}.Finite) : A.Exterior :=
  (CanonicalCoordinateProof.idealEquiv A).symm (Finsupp.ofSupportFinite f hf)

theorem exponent_idealOfExponents (f : ExteriorPrime A → ℕ)
    (hf : {p | f p ≠ 0}.Finite) (p : ExteriorPrime A) :
    exponent A (idealOfExponents A f hf) p = f p := by
  exact congrArg (fun g : ExteriorPrime A →₀ ℕ => g p)
    ((CanonicalCoordinateProof.idealEquiv A).apply_symm_apply
      (Finsupp.ofSupportFinite f hf))

theorem ideal_ext (I J : A.Exterior)
    (h : ∀ p, exponent A I p = exponent A J p) : I = J := by
  apply (CanonicalCoordinateProof.idealEquiv A).injective
  ext p
  exact h p

def primeSetIdeal (s : Finset (ExteriorPrime A)) : A.Exterior :=
  idealOfExponents A (fun p => if p ∈ s then 1 else 0) (by
    apply s.finite_toSet.subset
    intro p hp
    by_contra hn
    exact hp (if_neg hn))

theorem exponent_primeSetIdeal (s : Finset (ExteriorPrime A)) (p : ExteriorPrime A) :
    exponent A (primeSetIdeal A s) p = if p ∈ s then 1 else 0 :=
  exponent_idealOfExponents A _ _ p

theorem primeSetIdeal_squarefree (s : Finset (ExteriorPrime A)) :
    Squarefree (primeSetIdeal A s).val := by
  apply CanonicalCoordinateProof.squarefree_of_exponents_le_one A
  intro p
  change exponent A (primeSetIdeal A s) p ≤ 1
  rw [exponent_primeSetIdeal]
  split_ifs <;> omega

structure Coordinates where
  active : Finset (ExteriorPrime A)
  a : A.Exterior
  c : A.Exterior
  n : A.Exterior

def Coordinates.toBranch (b : Coordinates A) : GlobalFrequency.Branch (ExteriorPrime A) where
  active := b.active
  a := exponent A b.a
  c := exponent A b.c
  n := exponent A b.n

theorem Coordinates.toBranch_injective :
    Function.Injective (Coordinates.toBranch A) := by
  intro b b' h
  have ha : b.active = b'.active := by
    apply Finset.coe_injective
    exact congrArg GlobalFrequency.Branch.active h
  have haa : b.a = b'.a := ideal_ext A _ _ (congrFun (congrArg GlobalFrequency.Branch.a h))
  have hc : b.c = b'.c := ideal_ext A _ _ (congrFun (congrArg GlobalFrequency.Branch.c h))
  have hn : b.n = b'.n := ideal_ext A _ _ (congrFun (congrArg GlobalFrequency.Branch.n h))
  cases b
  cases b'
  cases ha
  cases haa
  cases hc
  cases hn
  rfl

def coordinatesOfBranch (b : GlobalFrequency.Branch (ExteriorPrime A))
    (ha : b.active.Finite) (haa : {p | b.a p ≠ 0}.Finite)
    (hc : {p | b.c p ≠ 0}.Finite) (hn : {p | b.n p ≠ 0}.Finite) : Coordinates A where
  active := ha.toFinset
  a := idealOfExponents A b.a haa
  c := idealOfExponents A b.c hc
  n := idealOfExponents A b.n hn

theorem coordinatesOfBranch_toBranch (b : GlobalFrequency.Branch (ExteriorPrime A))
    (ha : b.active.Finite) (haa : {p | b.a p ≠ 0}.Finite)
    (hc : {p | b.c p ≠ 0}.Finite) (hn : {p | b.n p ≠ 0}.Finite) :
    (coordinatesOfBranch A b ha haa hc hn).toBranch A = b := by
  apply GlobalFrequency.Branch.ext
  · ext p
    exact Set.Finite.mem_toFinset ha
  · funext p
    exact exponent_idealOfExponents A b.a haa p
  · funext p
    exact exponent_idealOfExponents A b.c hc p
  · funext p
    exact exponent_idealOfExponents A b.n hn p

theorem existsUnique_coordinates (mandatory allowed : Set (ExteriorPrime A))
    (v : ExteriorPrime A → ℤ)
    (hv : GlobalFrequencyReconstruction.LocalSupport mandatory allowed v)
    (hallowed : allowed.Finite) (hfinite : (Function.support v).Finite) :
    ∃! b : Coordinates A,
      GlobalFrequency.Supported mandatory (b.toBranch A) ∧
      GlobalFrequency.valuation (b.toBranch A) = v := by
  let b := GlobalFrequencyReconstruction.reconstruct mandatory v
  obtain ⟨ha, haa, hc, hn⟩ :=
    GlobalFrequencyReconstruction.reconstructed_supports_finite
      mandatory allowed v hv hallowed hfinite
  let c := coordinatesOfBranch A b ha haa hc hn
  have he : c.toBranch A = b := coordinatesOfBranch_toBranch A b ha haa hc hn
  refine ⟨c, ?_, ?_⟩
  · rw [he]
    exact ⟨GlobalFrequencyReconstruction.reconstructed_supported mandatory allowed v hv,
      GlobalFrequencyReconstruction.reconstructed_valuation mandatory allowed v hv⟩
  · intro d hd
    apply Coordinates.toBranch_injective A
    apply GlobalFrequency.supported_valuation_injective mandatory _ _ hd.1
    · rw [he]
      exact GlobalFrequencyReconstruction.reconstructed_supported mandatory allowed v hv
    · rw [he, hd.2]
      exact (GlobalFrequencyReconstruction.reconstructed_valuation mandatory allowed v hv).symm

theorem coordinates_squarefree (mandatory : Set (ExteriorPrime A))
    (b : Coordinates A) (hb : GlobalFrequency.Supported mandatory (b.toBranch A)) :
    Squarefree b.c.val :=
  CanonicalCoordinateProof.squarefree_of_exponents_le_one A b.c hb.c_squarefree

private theorem order_mul (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (x y : Fˣ) :
    order p (x * y) = order p x + order p y := by
  simp only [order, Units.val_mul, map_mul]
  rw [WithZero.log_mul ((Valuation.ne_zero_iff _).mpr x.ne_zero)
    ((Valuation.ne_zero_iff _).mpr y.ne_zero), neg_add]

private theorem order_pow (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (x : Fˣ) (n : ℕ) : order p (x ^ n) = n * order p x := by
  induction n with
  | zero => simp [order]
  | succ n ih => rw [pow_succ, order_mul, ih]; push_cast; ring

private theorem order_div (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (x y : Fˣ) :
    order p (x / y) = order p x - order p y := by
  rw [div_eq_mul_inv, order_mul]
  simp [order, Units.val_inv_eq_inv_val, map_inv₀, WithZero.log_inv]

variable (G : AllowedRecipe A)

def representative (d : A.Exterior) (b : Coordinates A) : Fˣ :=
  G.generator b.a * G.generator b.c * G.generator b.n ^ 3 /
    (G.generator d * G.generator (primeSetIdeal A b.active)) ^ 2

theorem representative_order (d : A.Exterior) (b : Coordinates A) (p : ExteriorPrime A) :
    order p.val (representative A G d b) =
      GlobalFrequency.valuation (b.toBranch A) p - 2 * (exponent A d p : ℤ) := by
  simp only [representative, order_div, order_mul, order_pow,
    generator_order, ← exponent, exponent_primeSetIdeal]
  unfold GlobalFrequency.valuation Coordinates.toBranch
  by_cases hp : p ∈ b.active <;> simp [hp] <;> ring

theorem finite_normalized_orders (d : A.Exterior) (x : Fˣ) :
    (Function.support (fun p : ExteriorPrime A =>
      order p.val x + 2 * (exponent A d p : ℤ))).Finite := by
  have hx := (order_finite_support x).preimage
    (f := fun p : ExteriorPrime A => p.val) Subtype.val_injective.injOn
  have hd := ((CanonicalCoordinateProof.idealEquiv A) d).finite_support
  apply (hx.union hd).subset
  intro p hp
  by_contra hn
  have hnx : order p.val x = 0 := by
    by_contra h
    exact hn (Or.inl h)
  have hnd : exponent A d p = 0 := by
    by_contra h
    exact hn (Or.inr h)
  exact hp (by simp [hnx, hnd])

/-- Actual frequency existence, using the fixed allowed generators and
the fixed unit representatives.  The only support assumptions are local
valuation restrictions, before any coefficient or theta sum is formed. -/
theorem exists_frequency_coordinates (U : UnitRepresentatives A)
    (d : A.Exterior) (mandatory allowed : Set (ExteriorPrime A))
    (hallowed : allowed.Finite) (x : Fˣ)
    (hv : GlobalFrequencyReconstruction.LocalSupport mandatory allowed
      (fun p => order p.val x + 2 * (exponent A d p : ℤ))) :
    ∃ b : Coordinates A, ∃ ε : A.UnitQuotient,
      GlobalFrequency.Supported mandatory (b.toBranch A) ∧
      (b.active : Set (ExteriorPrime A)) ⊆ allowed ∧
      GlobalUnitCoordinates.frequency A U (representative A G d b) ε = QuotientGroup.mk x := by
  let v : ExteriorPrime A → ℤ := fun p => order p.val x + 2 * (exponent A d p : ℤ)
  obtain ⟨b, hb, _⟩ := existsUnique_coordinates A mandatory allowed v hv hallowed
    (finite_normalized_orders A d x)
  have horders (p : ExteriorPrime A) :
      order p.val x = order p.val (representative A G d b) := by
    rw [representative_order, congrFun hb.2 p]
    dsimp [v]
    ring
  obtain ⟨ε, hε⟩ := GlobalUnitCoordinates.exists_unit_sector A U x
    (representative A G d b) horders
  refine ⟨b, ε, hb.1, ?_, hε⟩
  intro p hp
  have ha := (GlobalFrequency.active_iff_mandatory_or_negative mandatory
    (b.toBranch A) hb.1 p).mp hp
  rcases ha with hm | hn
  · exact hv.mandatory_allowed hm
  · exact hv.negative_allowed p (by rwa [hb.2] at hn)

private theorem order_unit (p : ExteriorPrime A) (u : A.U) :
    order p.val u.val = 0 := by
  have hu : p.val.valuation F (u.val : F) = 1 := u.property p.val p.property
  simp [order, hu]

/-- Both the ideal coordinates and the stored unit sector are determined
by the actual rational frequency on the supported index. -/
theorem frequency_coordinates_unique (U : UnitRepresentatives A)
    (d : A.Exterior) (mandatory : Set (ExteriorPrime A))
    (b b' : Coordinates A) (ε ε' : A.UnitQuotient)
    (hb : GlobalFrequency.Supported mandatory (b.toBranch A))
    (hb' : GlobalFrequency.Supported mandatory (b'.toBranch A))
    (hfreq : GlobalUnitCoordinates.frequency A U (representative A G d b) ε =
      GlobalUnitCoordinates.frequency A U (representative A G d b') ε') :
    b = b' ∧ ε = ε' := by
  have hv : GlobalFrequency.valuation (b.toBranch A) =
      GlobalFrequency.valuation (b'.toBranch A) := by
    funext p
    have ho := CanonicalCoordinateProof.order_eq_of_frequency_eq A
      ((U.representative ε).val * representative A G d b)
      ((U.representative ε').val * representative A G d b') hfreq p
    rw [order_mul, order_mul, order_unit, order_unit, zero_add, zero_add,
      representative_order, representative_order] at ho
    omega
  have he : b = b' := Coordinates.toBranch_injective A
    (GlobalFrequency.supported_valuation_injective mandatory _ _ hb hb' hv)
  refine ⟨he, ?_⟩
  subst b'
  exact GlobalUnitCoordinates.frequency_injective A U (representative A G d b) hfreq

theorem existsUnique_frequency_coordinates (U : UnitRepresentatives A)
    (d : A.Exterior) (mandatory allowed : Set (ExteriorPrime A))
    (hallowed : allowed.Finite) (x : Fˣ)
    (hv : GlobalFrequencyReconstruction.LocalSupport mandatory allowed
      (fun p => order p.val x + 2 * (exponent A d p : ℤ))) :
    ∃! z : Coordinates A × A.UnitQuotient,
      GlobalFrequency.Supported mandatory (z.1.toBranch A) ∧
      (z.1.active : Set (ExteriorPrime A)) ⊆ allowed ∧
      GlobalUnitCoordinates.frequency A U (representative A G d z.1) z.2 =
        QuotientGroup.mk x := by
  obtain ⟨b, ε, hb, ha, hf⟩ :=
    exists_frequency_coordinates A G U d mandatory allowed hallowed x hv
  refine ⟨(b, ε), ⟨hb, ha, hf⟩, ?_⟩
  intro z hz
  obtain ⟨h1, h2⟩ := frequency_coordinates_unique A G U d mandatory
    z.1 b z.2 ε hz.1 hb (hz.2.2.trans hf.symm)
  exact Prod.ext h1 h2

end ThetaGlobal.GlobalIdealCoordinates
