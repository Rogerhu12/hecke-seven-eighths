import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderMarkFamily
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderHilbert
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderStateEnergy
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.UniformThreshold

/-!
# The original tuple masses in the actual reflected row Hilbert space

Active tuples retain their row-independent coefficient bound one.
Inactive tuples are summed with their original reciprocal-prime mass.
The finite active-subset and frozen-state factors are explicit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalMarkEnergy

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowEnergy.ActualReflection HeckeSkeleton.LowEnergy.ActualReflectionReindex
open HeckeSkeleton.LowEnergy.ActualSeparatedBlock
open TerminalMarks TerminalAggregation TerminalTupleSplit TerminalMarkFamily
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable {σ : Type*} [DecidableEq σ]
variable (I : Finset σ) (L : σ → Finset (Ideal (𝓞 K)))
variable (a : σ → Ideal (𝓞 K) → ℂ)
variable (hprime : ∀ i ∈ I, ∀ p ∈ L i, Prime p)
variable (hexterior : ∀ i ∈ I, ∀ p ∈ L i, MOM_INV_STEP.CanonicalChildren.IsExterior K S p)
variable (hdisjoint : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (L i) (L j))

theorem tupleIdeal_norm (q : tuplePool K I L) :
    exteriorNorm K S (tupleIdeal K S I L hprime hexterior q) =
      ∏ i : I, ((q.val i).absNorm : ℝ) := by
  rw [tupleIdeal, HeckeSkeleton.LowEnergy.ActualFrozenCharges.primeSetIdeal_norm]
  unfold tuplePrimes
  rw [Finset.prod_image]
  · rfl
  · intro i hi j hj hij
    exact tuplePrime_injective K S I L hprime hexterior hdisjoint q hij

theorem tupleIdeal_norm_le (slotCap : ℕ) (Z z hi : ℝ) (hZ : 1 ≤ Z)
    (lengths : σ → ℝ) (hI : I.card ≤ slotCap)
    (hlength : (∑ i ∈ I, lengths i) ≤ z)
    (hnorm : ∀ i ∈ I, ∀ p ∈ L i, (p.absNorm : ℝ) ≤ hi * Z ^ lengths i)
    (q : tuplePool K I L) :
    exteriorNorm K S (tupleIdeal K S I L hprime hexterior q) ≤
      (max 1 hi) ^ slotCap * Z ^ z := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  rw [tupleIdeal_norm K S I L hprime hexterior hdisjoint q]
  calc
    _ ≤ ∏ i : I, max 1 hi * Z ^ lengths i.val := by
      apply Finset.prod_le_prod
      · intro i hi'
        positivity
      · intro i hi'
        exact (hnorm i.val i.property (q.val i) ((Fintype.mem_piFinset.mp q.property) i)).trans
          (mul_le_mul_of_nonneg_right (le_max_right 1 hi) (Real.rpow_nonneg hz.le _))
    _ = (max 1 hi) ^ I.card * Z ^ (∑ i ∈ I, lengths i) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
      rw [← Real.rpow_sum_of_pos hz (fun i : I => lengths i.val) Finset.univ]
      rw [Finset.sum_coe_sort]
    _ ≤ _ := mul_le_mul
      (pow_le_pow_right₀ (le_max_left 1 hi) hI)
      (Real.rpow_le_rpow_of_exponent_le hZ hlength)
      (Real.rpow_nonneg hz.le _) (pow_nonneg (by positivity) _)

theorem idealPool_norm_le (slotCap : ℕ) (Z z hi : ℝ) (hZ : 1 ≤ Z)
    (lengths : σ → ℝ) (hI : I.card ≤ slotCap)
    (hlength : (∑ i ∈ I, lengths i) ≤ z)
    (hnorm : ∀ i ∈ I, ∀ p ∈ L i, (p.absNorm : ℝ) ≤ hi * Z ^ lengths i)
    (P : ExteriorIdeal K S) (hP : P ∈ idealPool K S I L hprime hexterior) :
    exteriorNorm K S P ≤ (max 1 hi) ^ slotCap * Z ^ z := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hP
  exact tupleIdeal_norm_le K S I L hprime hexterior hdisjoint
    slotCap Z z hi hZ lengths hI hlength hnorm q

theorem inactiveWeight_norm (g r : ExteriorIdeal K S) (hr : Squarefree r.val.val)
    (u : S.unit K) (q : tuplePool K I L)
    (hq : InactiveAway K S g r (tuplePrimes K S I L hprime hexterior q)) :
    ‖inactiveWeight K S (fixedMarkData K S g r hr u _ hq)‖ =
      reciprocalWeight K S I L hprime hexterior q := by
  unfold inactiveWeight reciprocalWeight
  rw [norm_prod]
  apply Finset.prod_congr rfl
  intro p hp
  rw [norm_inv, Complex.norm_natCast]

theorem subsets_card : Fintype.card {J : Finset σ // J ⊆ I} = 2 ^ I.card := by
  have he : {J : Finset σ // J ⊆ I} ≃ I.powerset :=
    Equiv.subtypeEquivRight (fun J => Finset.mem_powerset.symm)
  rw [Fintype.card_congr he, Fintype.card_coe, Finset.card_powerset]

variable (D : ThetaArithmeticData K S)
local notation "Ext" => ExteriorIdeal K S

/-- Minkowski is applied to the complete inactive row vectors, with
their actual reciprocal weights. The source equality is already proved. -/
theorem marked_source_energy
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (g r : Ext) (hr : Squarefree r.val.val) (u : S.unit K)
    (rows : Finset Ext)
    (hrows : ∀ k ∈ rows, Squarefree k.val.val ∧
      IsCoprime k.val.val g.val.val ∧ IsCoprime k.val.val r.val.val)
    (V : SmoothAnnularTest) (X B Mass : ℝ) (hX : 0 < X) (hB : 0 ≤ B) (hMass : 0 ≤ Mass)
    (hmass : ∀ J : {J : Finset σ // J ⊆ I},
      (∑ qi : tuplePool K (I \ J.val) L, ‖tupleWeight K (I \ J.val) a qi.val‖ *
        reciprocalWeight K S (I \ J.val) L
          (fun i hi => hprime i (Finset.mem_sdiff.mp hi).1)
          (fun i hi => hexterior i (Finset.mem_sdiff.mp hi).1) qi) ≤ Mass)
    (hpiece : ∀ (s : FrozenState K S g r) (J : {J : Finset σ // J ⊆ I})
      (qi : tuplePool K (I \ J.val) L),
      (∑ k ∈ rows, ‖inactiveBlock K S D I L a hprime hexterior
        F θ g r hr u s J qi V.toFun X k‖ ^ 2) ≤
        (reciprocalWeight K S (I \ J.val) L
          (fun i hi => hprime i (Finset.mem_sdiff.mp hi).1)
          (fun i hi => hexterior i (Finset.mem_sdiff.mp hi).1) qi) ^ 2 * B) :
    (∑ k ∈ rows, ‖MOM_BASE.canonicalCompletedSum (MOM_BASE.exteriorGamma K S D)
      (MOM_BASE.canonicalTau K S D θ
        ((S.unitEquivUnitsInteger K u).val * D.generator (exteriorMul K S k g)) r.val.val)
      (MOMInvStep.divisorMark I L a) V.toFun X‖ ^ 2) ≤
      (Nat.card (FrozenState K S g r) : ℝ) ^ 2 * (2 : ℝ) ^ (2 * I.card) * Mass ^ 2 * B := by
  have hinner (s : FrozenState K S g r) (J : {J : Finset σ // J ⊆ I}) :
      (∑ k ∈ rows, ‖∑ qi : tuplePool K (I \ J.val) L,
        tupleWeight K (I \ J.val) a qi.val * inactiveBlock K S D I L a hprime hexterior
          F θ g r hr u s J qi V.toFun X k‖ ^ 2) ≤ Mass ^ 2 * B := by
    have h := TerminalHilbert.finite_coefficient_energy Finset.univ rows
      (fun qi _ => tupleWeight K (I \ J.val) a qi.val)
      (fun qi k => inactiveBlock K S D I L a hprime hexterior F θ g r hr u s J qi V.toFun X k)
      (fun qi => ‖tupleWeight K (I \ J.val) a qi.val‖)
      (reciprocalWeight K S (I \ J.val) L
        (fun i hi => hprime i (Finset.mem_sdiff.mp hi).1)
        (fun i hi => hexterior i (Finset.mem_sdiff.mp hi).1)) B hB
      (fun qi _ => norm_nonneg _) (fun qi _ => reciprocalWeight_nonneg K S _ _ _ _ qi)
      (fun qi _ k _ => le_refl _) (fun qi _ => hpiece s J qi)
    exact h.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Finset.sum_nonneg fun qi _ => mul_nonneg (norm_nonneg _)
        (reciprocalWeight_nonneg K S _ _ _ _ qi)) (hmass J) 2) hB)
  have hsubsets (s : FrozenState K S g r) :
      (∑ k ∈ rows, ‖∑ J : {J : Finset σ // J ⊆ I},
        ∑ qi : tuplePool K (I \ J.val) L,
          tupleWeight K (I \ J.val) a qi.val * inactiveBlock K S D I L a hprime hexterior
            F θ g r hr u s J qi V.toFun X k‖ ^ 2) ≤
        (2 : ℝ) ^ (2 * I.card) * Mass ^ 2 * B := by
    have h := TerminalHilbert.finite_sum_energy Finset.univ rows
      (fun J k => ∑ qi : tuplePool K (I \ J.val) L,
        tupleWeight K (I \ J.val) a qi.val * inactiveBlock K S D I L a hprime hexterior
          F θ g r hr u s J qi V.toFun X k) (fun _ => (1 : ℝ)) (Mass ^ 2 * B)
      (by positivity) (by simp) (fun J _ => by simpa using hinner s J)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      subsets_card, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, mul_comm I.card 2, mul_assoc] using h
  have h := TerminalHilbert.finite_sum_energy Finset.univ rows
    (fun s k => ∑ J : {J : Finset σ // J ⊆ I},
      ∑ qi : tuplePool K (I \ J.val) L,
        tupleWeight K (I \ J.val) a qi.val * inactiveBlock K S D I L a hprime hexterior
          F θ g r hr u s J qi V.toFun X k)
    (fun _ => (1 : ℝ)) ((2 : ℝ) ^ (2 * I.card) * Mass ^ 2 * B)
    (by positivity) (by simp) (fun s _ => by simpa using hsubsets s)
  have he : (∑ k ∈ rows, ‖MOM_BASE.canonicalCompletedSum (MOM_BASE.exteriorGamma K S D)
      (MOM_BASE.canonicalTau K S D θ
        ((S.unitEquivUnitsInteger K u).val * D.generator (exteriorMul K S k g)) r.val.val)
      (MOMInvStep.divisorMark I L a) V.toFun X‖ ^ 2) =
      ∑ k ∈ rows, ‖∑ s : FrozenState K S g r, ∑ J : {J : Finset σ // J ⊆ I},
        ∑ qi : tuplePool K (I \ J.val) L,
          tupleWeight K (I \ J.val) a qi.val * inactiveBlock K S D I L a hprime hexterior
            F θ g r hr u s J qi V.toFun X k‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [canonicalCompletedSum_eq_inactive_blocks K S D I L a hprime hexterior hdisjoint
      F θ hreflection g r k hr u (hrows k hk).1 (hrows k hk).2.1 (hrows k hk).2.2 V X hX]
  rw [he]
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Nat.card_eq_fintype_card, mul_assoc] using h

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalMarkEnergy

end
