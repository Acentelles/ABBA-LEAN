import Mathlib

set_option linter.style.header false

/-!
# ABBA — remaining small results

* Lemma `Lemma:centrality`: `α` is commutator-linear iff central, and central
  scalars preserve tracelessness (the counterexample for non-central scalars is
  in `Cap.lean`).
* Rem `Rem:syndromegap`: the statistical distance between the uniform
  distributions on a finite set and on a nonempty subset is `1 - |B|/|A|`
  (stated as the explicit half-`L¹` sum), together with the bound
  `1 - ρ^m ≤ m·ε` for `ρ ≥ 1 - ε`.
-/

namespace Abba

open Finset

section Centrality

variable {R : Type*} [Ring R]

/-- Lemma `centrality`, single-commutator form: `[a, αx] = α[a, x]` for all
`a, x` iff `α` is central. -/
theorem commutator_linear_iff (α : R) :
    (∀ a x : R, a * (α * x) - (α * x) * a = α * (a * x - x * a))
      ↔ α ∈ Set.center R := by
  constructor
  · intro h
    rw [Semigroup.mem_center_iff]
    intro a
    have h1 := h a 1
    simp only [mul_one, one_mul] at h1
    -- h1 : a * α - α * a = α * (a - a) = 0
    have h2 : a * α - α * a = 0 := by
      rw [h1, sub_self, mul_zero]
    exact sub_eq_zero.mp h2
  · intro hα a x
    have hc : ∀ b : R, α * b = b * α := fun b =>
      ((Semigroup.mem_center_iff.mp hα) b).symm
    calc a * (α * x) - (α * x) * a
        = α * (a * x) - α * (x * a) := by
          rw [show a * (α * x) = α * (a * x) by rw [← mul_assoc, ← hc a, mul_assoc],
            show (α * x) * a = α * (x * a) by rw [mul_assoc]]
      _ = α * (a * x - x * a) := by rw [mul_sub]

/-- The summed form used in the paper (`m` coordinates). -/
theorem commutator_sum_linear {m : ℕ} (α : R) (hα : α ∈ Set.center R)
    (a x : Fin m → R) :
    ∑ i, (a i * (α * x i) - (α * x i) * a i)
      = α * ∑ i, (a i * x i - x i * a i) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ =>
    (commutator_linear_iff α).mpr hα (a i) (x i)

/-- Central scalars preserve tracelessness (`α·𝒯₀ ⊆ 𝒯₀`), matrix form. -/
theorem trace_smul_eq_zero {F : Type*} [CommRing F] {n : Type*} [Fintype n]
    (c : F) (t : Matrix n n F) (ht : t.trace = 0) : (c • t).trace = 0 := by
  rw [Matrix.trace_smul, ht, smul_zero]

end Centrality

section SD

/-- Rem `syndromegap`, the statistical-distance identity: for a nonempty subset
`B ⊆ A`, `SD(U_A, U_B) = 1 - |B|/|A|` (as the explicit half-`L¹` sum). -/
theorem sd_uniform_subset {α : Type*} [DecidableEq α] (A B : Finset α)
    (hBA : B ⊆ A) (hB : B.Nonempty) :
    (1 / 2 : ℚ) * ∑ x ∈ A, |(if x ∈ B then ((B.card : ℚ))⁻¹ else 0) - ((A.card : ℚ))⁻¹|
      = 1 - (B.card : ℚ) / (A.card : ℚ) := by
  have hA : A.Nonempty := hB.mono hBA
  have hBpos : (0 : ℚ) < B.card := by exact_mod_cast hB.card_pos
  have hApos : (0 : ℚ) < A.card := by exact_mod_cast hA.card_pos
  have hle : (B.card : ℚ) ≤ A.card := by exact_mod_cast Finset.card_le_card hBA
  have hinv : ((A.card : ℚ))⁻¹ ≤ ((B.card : ℚ))⁻¹ := by
    have h5 := one_div_le_one_div_of_le hBpos hle
    rwa [one_div, one_div] at h5
  have hsplit : ∑ x ∈ A, |(if x ∈ B then ((B.card : ℚ))⁻¹ else 0) - ((A.card : ℚ))⁻¹|
      = ∑ x ∈ A \ B, |(if x ∈ B then ((B.card : ℚ))⁻¹ else 0) - ((A.card : ℚ))⁻¹|
        + ∑ x ∈ B, |(if x ∈ B then ((B.card : ℚ))⁻¹ else 0) - ((A.card : ℚ))⁻¹| :=
    (Finset.sum_sdiff hBA).symm
  have hout : ∑ x ∈ A \ B, |(if x ∈ B then ((B.card : ℚ))⁻¹ else 0) - ((A.card : ℚ))⁻¹|
      = (A.card - B.card : ℚ) * ((A.card : ℚ))⁻¹ := by
    rw [Finset.sum_congr rfl fun x hx => by
      rw [if_neg (Finset.mem_sdiff.mp hx).2, zero_sub, abs_neg,
        abs_of_pos (by positivity)]]
    rw [Finset.sum_const, Finset.card_sdiff, Finset.inter_eq_left.mpr hBA, nsmul_eq_mul,
      Nat.cast_sub (Finset.card_le_card hBA)]
  have hin : ∑ x ∈ B, |(if x ∈ B then ((B.card : ℚ))⁻¹ else 0) - ((A.card : ℚ))⁻¹|
      = (B.card : ℚ) * (((B.card : ℚ))⁻¹ - ((A.card : ℚ))⁻¹) := by
    rw [Finset.sum_congr rfl fun x hx => by
      rw [if_pos hx, abs_of_nonneg (by linarith [hinv])]]
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [hsplit, hout, hin]
  field_simp
  ring

/-- The paper's bound: if `ρ ≥ 1 - ε` and `ρ ≥ 0` then `1 - ρ^m ≤ m·ε`. -/
theorem one_sub_pow_le (ρ ε : ℚ) (h0 : 0 ≤ ρ) (h : 1 - ε ≤ ρ) (m : ℕ) :
    1 - ρ ^ m ≤ m * ε := by
  have h1 : 1 + (m : ℚ) * (ρ - 1) ≤ ρ ^ m := by
    have := one_add_mul_le_pow (a := ρ - 1) (by linarith) m
    simpa using this
  have h2 : 1 - ρ ≤ ε := by linarith
  nlinarith [h1, h2, Nat.cast_nonneg (α := ℚ) m]

end SD

end Abba
