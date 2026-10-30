/-
Ported from Vilin97/lean-pool at
01db1d7049cf9668bda1e9e106875ee1278b43e6,
LeanPool/Odlyzko/Theta/TraceDualIdeal.lean.
The pooled source originates from the FLT Project; its original license and
attribution header below are retained. Local changes adapt the namespace and
imports to this project's fixed Lean/Mathlib version.
-/
/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/

import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-! TODO: Add doc-string. -/



noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace HeckeGeneral.Arithmetic

variable (K : Type*) [Field K] [NumberField K]

/-- A trace dual ideal unit used in the Odlyzko-bound argument. -/
noncomputable def traceDualIdealUnit
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0
    (FractionalIdeal.dual ℤ ℚ
      (I : FractionalIdeal (𝓞 K)⁰ K))
    (FractionalIdeal.dual_ne_zero ℤ ℚ (Units.ne_zero I))

@[simp]
theorem coe_traceDualIdealUnit
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (traceDualIdealUnit K I : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ
        (I : FractionalIdeal (𝓞 K)⁰ K) :=
  rfl

@[simp]
theorem traceDualIdealUnit_traceDualIdealUnit
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    traceDualIdealUnit K (traceDualIdealUnit K I) = I := by
  ext
  simp

theorem coe_traceDualIdealUnit_eq_dual_one_mul_inv
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (traceDualIdealUnit K I : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ
          (1 : FractionalIdeal (𝓞 K)⁰ K) *
        (I : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  rw [coe_traceDualIdealUnit,
    FractionalIdeal.dual_eq_mul_inv]

/-- The trace dual is the inverse different times the inverse ideal.
This identifies the arithmetic object used by the polar lattice formula. -/
theorem coe_traceDualIdealUnit_eq_inverseDifferent_mul_inv
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (traceDualIdealUnit K I : FractionalIdeal (𝓞 K)⁰ K) =
      (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ *
        (I : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  rw [coe_traceDualIdealUnit_eq_dual_one_mul_inv,
    coeIdeal_differentIdeal ℤ ℚ K (𝓞 K), inv_inv]

theorem absNorm_traceDualIdealUnit
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    FractionalIdeal.absNorm
        (traceDualIdealUnit K I :
          FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.absNorm
          (FractionalIdeal.dual ℤ ℚ
            (1 : FractionalIdeal (𝓞 K)⁰ K)) *
        (FractionalIdeal.absNorm
          (I : FractionalIdeal (𝓞 K)⁰ K))⁻¹ := by
  rw [coe_traceDualIdealUnit_eq_dual_one_mul_inv,
    map_mul, map_inv₀]

theorem absNorm_traceDual_one :
    FractionalIdeal.absNorm
        (FractionalIdeal.dual ℤ ℚ
          (1 : FractionalIdeal (𝓞 K)⁰ K)) =
      ((|(discr K : ℤ)| : ℚ))⁻¹ := by
  have hdifferent :=
    congrArg FractionalIdeal.absNorm
      (coeIdeal_differentIdeal ℤ ℚ K (𝓞 K))
  rw [map_inv₀, FractionalIdeal.coeIdeal_absNorm,
    NumberField.absNorm_differentIdeal K] at hdifferent
  simp_all

end HeckeGeneral.Arithmetic

