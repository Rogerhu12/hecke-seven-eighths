import HeckeSkeleton.LowFrozenCube.TableExit

/-!
# Canonical frozen pairs constructed from original local indices

The fixed-minimum block still contains every original local index. Its local
table zero terms can be discarded. Every surviving exponent is admissible,
so the cube factor is constructed from the raw index and the original index
is recovered uniquely. Canonical frozen pairs are thus outputs of this file.
-/

namespace HeckeSkeleton.LowFrozenCube.FrozenReduction

open scoped BigOperators Classical

noncomputable section

variable {ι A : Type*} [CommMonoid A]

namespace Data

variable (D : Data ι A)

def rawTable (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (a : A) : ℂ :=
  LocalTable.localProduct D.ordinary (fun p => normI (D.prime p))
    first prefactor atZero D.digit (PrimeCoordinates.valuation D.coords a)

def minimumBlock (inputs : Finset (A × A)) : Finset (A × A) :=
  inputs.filter fun q => PrimeCoordinates.minimumFactor D.coords q.1 = D.minimum

def activeInputBlock (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (inputs : Finset (A × A)) : Finset (A × A) :=
  (D.minimumBlock inputs).filter fun q => D.rawTable normI first prefactor atZero q.1 ≠ 0

def freezePair (q : A × A) : A × A :=
  (PrimeCoordinates.residualCubeFactor D.coords q.1, q.2)

def frozenInputPairs (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (inputs : Finset (A × A)) : Finset (A × A) :=
  (D.activeInputBlock normI first prefactor atZero inputs).image D.freezePair

@[simp] theorem mem_activeInputBlock (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (inputs : Finset (A × A)) (q : A × A) :
    q ∈ D.activeInputBlock normI first prefactor atZero inputs ↔
      q ∈ inputs ∧ PrimeCoordinates.minimumFactor D.coords q.1 = D.minimum ∧
        D.rawTable normI first prefactor atZero q.1 ≠ 0 := by
  simp [activeInputBlock, minimumBlock, and_assoc]

theorem rawTable_nonzero_admissible (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (a : A)
    (ha : PrimeCoordinates.Supported D.coords D.ordinary a)
    (htable : D.rawTable normI first prefactor atZero a ≠ 0) :
    ∀ p, AdmissibleExponent (PrimeCoordinates.valuation D.coords a p) := by
  intro p
  by_cases hp : p ∈ D.ordinary
  · exact LocalTable.localProduct_nonzero_admissible D.ordinary
      (fun p => normI (D.prime p)) first prefactor atZero D.digit
      (PrimeCoordinates.valuation D.coords a) htable p hp
  · simp [ha p hp, AdmissibleExponent]

theorem canonical_of_minimumFactor_eq (a : A)
    (hminimum : PrimeCoordinates.minimumFactor D.coords a = D.minimum) :
    D.CanonicalCube (PrimeCoordinates.residualCubeFactor D.coords a) := by
  intro p
  change CanonicalFrozenPair (PrimeCoordinates.valuation D.coords D.minimum p)
    (PrimeCoordinates.valuation D.coords (PrimeCoordinates.residualCubeFactor D.coords a) p)
  rw [← hminimum]
  simp only [PrimeCoordinates.minimumFactor, PrimeCoordinates.residualCubeFactor,
    PrimeCoordinates.valuation_mapExponents]
  exact frozenPair_canonical _

/-- A surviving original index equals the frozen minimum times the cube of
its explicitly constructed residual factor. -/
theorem activeInput_reconstruct (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (inputs : Finset (A × A))
    (hsupport : ∀ q ∈ inputs, PrimeCoordinates.Supported D.coords D.ordinary q.1)
    (q : A × A) (hq : q ∈ D.activeInputBlock normI first prefactor atZero inputs) :
    q.1 = D.minimum * (PrimeCoordinates.residualCubeFactor D.coords q.1) ^ 3 := by
  have hq' := (D.mem_activeInputBlock normI first prefactor atZero inputs q).mp hq
  calc
    q.1 = PrimeCoordinates.minimumFactor D.coords q.1 *
        (PrimeCoordinates.residualCubeFactor D.coords q.1) ^ 3 :=
      PrimeCoordinates.minimum_mul_residualCube D.coords q.1
        (D.rawTable_nonzero_admissible normI first prefactor atZero q.1
          (hsupport q hq'.1) hq'.2.2)
    _ = _ := by rw [hq'.2.1]

theorem freezePair_injOn (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (inputs : Finset (A × A))
    (hsupport : ∀ q ∈ inputs, PrimeCoordinates.Supported D.coords D.ordinary q.1) :
    Set.InjOn D.freezePair (D.activeInputBlock normI first prefactor atZero inputs :
      Set (A × A)) := by
  intro q hq r hr hqr
  have hx : PrimeCoordinates.residualCubeFactor D.coords q.1 =
      PrimeCoordinates.residualCubeFactor D.coords r.1 := congrArg Prod.fst hqr
  apply Prod.ext
  · calc
      q.1 = D.minimum * (PrimeCoordinates.residualCubeFactor D.coords q.1) ^ 3 :=
        D.activeInput_reconstruct normI first prefactor atZero inputs hsupport q hq
      _ = D.minimum * (PrimeCoordinates.residualCubeFactor D.coords r.1) ^ 3 := by rw [hx]
      _ = r.1 :=
        (D.activeInput_reconstruct normI first prefactor atZero inputs hsupport r hr).symm
  · have hn := congrArg (fun t : A × A => t.2) hqr
    simpa only [freezePair] using hn

/-- Both hypotheses needed by the full-cube reindexing are now derived from
the original input support and the fixed-minimum fiber. -/
theorem frozenInputPairs_canonical (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (inputs : Finset (A × A))
    (haway : ∀ q ∈ inputs, PrimeCoordinates.Avoids D.coords D.ordinary q.2)
    (q : A × A) (hq : q ∈ D.frozenInputPairs normI first prefactor atZero inputs) :
    D.CanonicalCube q.1 ∧ PrimeCoordinates.Avoids D.coords D.ordinary q.2 := by
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
  have hr' := (D.mem_activeInputBlock normI first prefactor atZero inputs r).mp hr
  exact ⟨D.canonical_of_minimumFactor_eq r.1 hr'.2.1, haway r hr'.1⟩

theorem minimum_supported_of_activeInput (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (inputs : Finset (A × A))
    (hsupport : ∀ q ∈ inputs, PrimeCoordinates.Supported D.coords D.ordinary q.1)
    (q : A × A) (hq : q ∈ D.activeInputBlock normI first prefactor atZero inputs) :
    PrimeCoordinates.Supported D.coords D.ordinary D.minimum := by
  have hq' := (D.mem_activeInputBlock normI first prefactor atZero inputs q).mp hq
  rw [← hq'.2.1]
  exact PrimeCoordinates.minimumFactor_supported D.coords D.ordinary q.1 (hsupport q hq'.1)

end Data

end

end HeckeSkeleton.LowFrozenCube.FrozenReduction
