import ClassFieldTheory.LocalClassFieldTheory.Finite.Conductor
import ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertSymbolLaws
import ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertPairingNondegeneracy
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PowerClassFiniteness

/-! SOURCE ONLY, UNRUN. A common principal-unit depth for the actual local
Kummer Hilbert symbol. Actual norm-subgroup conductors give a depth for each
of finitely many power-class representatives. Pairing descent transfers the
kernel statement to all second arguments; skew gives the other variable.
No continuity, perfectness or nondegeneracy hypothesis is supplied or used.
The imported pairing module exports quotient descent as well as its stronger
results; only the descent evaluation is used here. Ordinary ideal powers,
S-integer additive congruences and global reciprocity remain later bridges. -/

noncomputable section
namespace HeckeGeneral.Arithmetic

open KummerTheory LocalClassFieldTheory LocalClassFieldTheory.Kummer
open scoped Classical BigOperators

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (n : ℕ+) (hnF : ((n : ℕ) : F) ≠ 0)
variable (hmu : (primitiveRoots (n : ℕ) F).Nonempty)

/-- Actual finite-extension conductors produce one positive depth killing
the Hilbert symbol in its first argument for EVERY second argument. -/
theorem exists_kummerHilbert_principalUnit_left_period :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ r : Fˣ,
      r ∈ LocalFieldTheory.fieldPrincipalUnits F N → ∀ b : Fˣ,
        LocalClassFieldTheory.Kummer.localHilbertSymbol F n hnF hmu r b = 1 := by
  let P := (powMonoidHom (n : ℕ) : Fˣ →* Fˣ).range
  let Q := Fˣ ⧸ P
  letI : Finite Q :=
    LocalFieldTheory.finite_nthPowerQuotient_of_natCast_ne_zero F (n : ℕ) hnF
  letI : Fintype Q := Fintype.ofFinite Q
  let rep : Q → Fˣ := fun q => Quotient.out q
  have hrep (q : Q) : QuotientGroup.mk' P (rep q) = q :=
    Quotient.out_eq q
  have hdepth (q : Q) : ∃ d : ℕ, 1 ≤ d ∧ ∀ r : Fˣ,
      r ∈ LocalFieldTheory.fieldPrincipalUnits F d →
        LocalClassFieldTheory.Kummer.localHilbertSymbol F n hnF hmu r (rep q) = 1 := by
    let E := chosenSimpleKummerExtension F n hnF (rep q)
    letI : FiniteDimensional F E :=
      chosenSimpleKummerExtension_finiteDimensional F n hnF (rep q)
    letI : IsAbelianGalois F E :=
      chosenSimpleKummerExtension_isAbelianGalois F n hnF hmu (rep q)
    let d := max 1 (localConductorExponent F E)
    refine ⟨d, le_max_left _ _, fun r hr => ?_⟩
    apply (localHilbertSymbol_eq_one_iff_mem_localNormSubgroup
      F n hnF hmu r (rep q)).mpr
    exact localConductorExponent_spec F E
      (fieldPrincipalUnits_antitone F (le_max_right _ _) hr)
  choose depth hpositive hkernel using hdepth
  let N : ℕ := 1 + ∑ q : Q, depth q
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hle (q : Q) : depth q ≤ N := by
    have hsum : depth q ≤ ∑ q : Q, depth q :=
      Finset.single_le_sum (fun q _ => Nat.zero_le (depth q)) (Finset.mem_univ q)
    dsimp only [N]
    omega
  refine ⟨N, hN, fun r hr b => ?_⟩
  let q : Q := QuotientGroup.mk' P b
  have hk : LocalClassFieldTheory.Kummer.localHilbertSymbol
      F n hnF hmu r (rep q) = 1 :=
    hkernel q r (fieldPrincipalUnits_antitone F (hle q) hr)
  calc
    LocalClassFieldTheory.Kummer.localHilbertSymbol F n hnF hmu r b =
        localHilbertPairing F n hnF hmu
          (QuotientGroup.mk' P r) (QuotientGroup.mk' P b) :=
      (localHilbertPairing_apply F n hnF hmu r b).symm
    _ = localHilbertPairing F n hnF hmu
          (QuotientGroup.mk' P r) (QuotientGroup.mk' P (rep q)) := by
      rw [hrep]
    _ = LocalClassFieldTheory.Kummer.localHilbertSymbol F n hnF hmu r (rep q) :=
      localHilbertPairing_apply F n hnF hmu r (rep q)
    _ = 1 := hk

/-- The SAME positive depth lies in the kernel in either variable. -/
theorem exists_kummerHilbert_principalUnit_two_sided_period :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ r : Fˣ,
      r ∈ LocalFieldTheory.fieldPrincipalUnits F N → ∀ b : Fˣ,
        LocalClassFieldTheory.Kummer.localHilbertSymbol F n hnF hmu r b = 1 ∧
        LocalClassFieldTheory.Kummer.localHilbertSymbol F n hnF hmu b r = 1 := by
  obtain ⟨N, hN, hk⟩ := exists_kummerHilbert_principalUnit_left_period F n hnF hmu
  refine ⟨N, hN, fun r hr b => ⟨hk r hr b, ?_⟩⟩
  rw [localHilbertSymbol_skew F n hnF hmu b r, hk r hr b, inv_one]

/-- Independent multiplicative principal-unit increments preserve the
actual pairing on arbitrary nonzero local elements. The depth is chosen
before both increments and both arguments. -/
theorem exists_kummerHilbert_principalUnit_paired_invariance :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ r s : Fˣ,
      r ∈ LocalFieldTheory.fieldPrincipalUnits F N →
      s ∈ LocalFieldTheory.fieldPrincipalUnits F N → ∀ a b : Fˣ,
        LocalClassFieldTheory.Kummer.localHilbertSymbol F n hnF hmu (a * r) (b * s) =
          LocalClassFieldTheory.Kummer.localHilbertSymbol F n hnF hmu a b := by
  obtain ⟨N, hN, hk⟩ := exists_kummerHilbert_principalUnit_two_sided_period F n hnF hmu
  refine ⟨N, hN, fun r s hr hs a b => ?_⟩
  calc
    LocalClassFieldTheory.Kummer.localHilbertSymbol F n hnF hmu (a * r) (b * s) =
        LocalClassFieldTheory.Kummer.localHilbertSymbol F n hnF hmu a (b * s) *
          LocalClassFieldTheory.Kummer.localHilbertSymbol F n hnF hmu r (b * s) :=
      map_mul (localHilbertSymbolHom F n hnF hmu (b * s)) a r
    _ = (LocalClassFieldTheory.Kummer.localHilbertSymbol F n hnF hmu a b *
          LocalClassFieldTheory.Kummer.localHilbertSymbol F n hnF hmu a s) * 1 := by
      rw [localHilbertSymbol_mul_right F n hnF hmu a b s, (hk r hr (b * s)).1]
    _ = LocalClassFieldTheory.Kummer.localHilbertSymbol F n hnF hmu a b := by
      rw [(hk s hs a).2, mul_one, mul_one]

end HeckeGeneral.Arithmetic
