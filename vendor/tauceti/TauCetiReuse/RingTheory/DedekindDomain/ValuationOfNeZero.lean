/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.SelmerGroup

/-! Only the two valuation triviality lemmas are ported. The upstream field-extension transport section is outside this slice. -/

public section

open scoped WithZero

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The `Multiplicative ℤ`-valued valuation of a unit is determined by the `ℤᵐ⁰`-valued one.
Mathlib carries only the coerced form `valuationOfNeZero_eq`, which this complements. -/
@[simp]
theorem valuationOfNeZero_eq_iff (v : HeightOneSpectrum R) (u : Kˣ) (m : Multiplicative ℤ) :
    v.valuationOfNeZero u = m ↔ v.valuation K u = (m : ℤᵐ⁰) := by
  rw [← WithZero.coe_inj, valuationOfNeZero_eq]

/-- A unit has trivial `v`-adic `valuationOfNeZero` iff its `v`-adic valuation is `1`, the case
`m = 1` of `valuationOfNeZero_eq_iff`. -/
-- Deliberately not `@[simp]`: `valuationOfNeZero_eq_iff` carries the annotation, and with both
-- marked `simpNF` rejects this one — "simp can prove this" — since the general form subsumes it.
theorem valuationOfNeZero_eq_one_iff (v : HeightOneSpectrum R) (x : Kˣ) :
    v.valuationOfNeZero x = 1 ↔ v.valuation K x = 1 := by
  simp only [valuationOfNeZero_eq_iff, WithZero.coe_one]

end IsDedekindDomain.HeightOneSpectrum

end
