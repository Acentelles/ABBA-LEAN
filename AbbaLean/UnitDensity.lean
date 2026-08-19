import Mathlib

set_option linter.style.header false

/-!
# ABBA — Lemma `unitdensity`

Paper: Lemma `Lemma:unitdensity`: for `Λ_q ≅ ∏_{i=1}^n M₂(𝔽_q)`,
`ρ = ((1 - q⁻¹)(1 - q⁻²))ⁿ ≥ 1 - 2n/q`.

Formalized on the matrix-ring side of the isomorphism (the isomorphism is
Lemma `structure`, the final target):
`card_GL2` / `card_units_pi` count units, `unit_density` gives the exact density,
`unit_density_ge` the union bound.
-/

namespace Abba

section UnitDensity

variable (𝔽 : Type*) [Field 𝔽] [Fintype 𝔽]

local notation "q" => Fintype.card 𝔽

/-- `|GL₂(𝔽_q)| = (q² - 1)(q² - q)`. -/
theorem card_GL2 : Nat.card (GL (Fin 2) 𝔽) = (q ^ 2 - 1) * (q ^ 2 - q) := by
  rw [Matrix.card_GL_field]
  simp [Fin.prod_univ_two, pow_one]

variable (n : ℕ)

/-- Unit count of the product ring `∏_{i<n} M₂(𝔽_q)`. -/
theorem card_units_pi :
    Nat.card ((Fin n → Matrix (Fin 2) (Fin 2) 𝔽))ˣ = ((q ^ 2 - 1) * (q ^ 2 - q)) ^ n := by
  rw [Nat.card_congr (MulEquiv.piUnits).toEquiv, Nat.card_pi]
  have h : Nat.card (Matrix (Fin 2) (Fin 2) 𝔽)ˣ = (q ^ 2 - 1) * (q ^ 2 - q) := card_GL2 𝔽
  simp [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

omit [Field 𝔽] in
/-- Cardinality of the ambient space: `|∏ M₂(𝔽_q)| = q^(4n)`. -/
theorem card_pi : Nat.card (Fin n → Matrix (Fin 2) (Fin 2) 𝔽) = q ^ (4 * n) := by
  rw [Nat.card_pi]
  have h : Nat.card (Matrix (Fin 2) (Fin 2) 𝔽) = q ^ 4 := by
    rw [Nat.card_eq_fintype_card]
    change Fintype.card (Fin 2 → Fin 2 → 𝔽) = q ^ 4
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin]
    ring
  rw [Finset.prod_congr rfl fun i _ => h, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← pow_mul, mul_comm 4 n]

/-- Exact unit density `((1 - q⁻¹)(1 - q⁻²))ⁿ`. -/
theorem unit_density :
    (Nat.card ((Fin n → Matrix (Fin 2) (Fin 2) 𝔽))ˣ : ℚ)
      / (Nat.card (Fin n → Matrix (Fin 2) (Fin 2) 𝔽) : ℚ)
      = ((1 - (q : ℚ)⁻¹) * (1 - (q : ℚ)⁻¹ ^ 2)) ^ n := by
  have hq1 : 1 < q := Fintype.one_lt_card
  have hq0 : (q : ℚ) ≠ 0 := by
    have : 0 < q := by omega
    exact_mod_cast this.ne'
  have hle1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hleq : q ≤ q ^ 2 := by nlinarith
  rw [card_units_pi, card_pi]
  have hcast : (((q ^ 2 - 1) * (q ^ 2 - q)) ^ n : ℕ)
      = ((((q:ℚ) ^ 2 - 1) * ((q:ℚ) ^ 2 - q)) ^ n : ℚ) := by
    push_cast [Nat.cast_sub hle1, Nat.cast_sub hleq]
    ring
  rw [hcast]
  have hden : ((q ^ (4 * n) : ℕ) : ℚ) = ((q : ℚ) ^ 4) ^ n := by
    push_cast
    rw [← pow_mul]
  rw [hden, ← div_pow]
  congr 1
  field_simp

/-- The union bound `ρ ≥ 1 - 2n/q`. -/
theorem unit_density_ge :
    1 - 2 * (n : ℚ) / q ≤ ((1 - (q : ℚ)⁻¹) * (1 - (q : ℚ)⁻¹ ^ 2)) ^ n := by
  have hq1 : 1 < q := Fintype.one_lt_card
  have hq2 : (2 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq1
  set x : ℚ := (q : ℚ)⁻¹ with hx_def
  have hq0 : (0 : ℚ) < (q : ℚ) := by linarith
  have hx0 : 0 < x := by positivity
  have hx2 : x ≤ 1 / 2 := by
    rw [hx_def]
    rw [inv_le_comm₀ hq0 (by norm_num : (0:ℚ) < 1/2)]
    linarith
  have h1 : 1 - 2 * x ≤ (1 - x) * (1 - x ^ 2) := by nlinarith
  have h2 : (1 - 2 * x) ^ n ≤ ((1 - x) * (1 - x ^ 2)) ^ n := by
    apply pow_le_pow_left₀ (by linarith) h1
  have h3 : 1 + (n : ℚ) * (-(2 * x)) ≤ (1 + (-(2 * x))) ^ n :=
    one_add_mul_le_pow (by linarith) n
  have hstart : 1 - 2 * (n : ℚ) / q = 1 + (n : ℚ) * (-(2 * x)) := by
    rw [hx_def]
    field_simp
    ring
  rw [hstart]
  calc 1 + (n : ℚ) * (-(2 * x)) ≤ (1 + (-(2 * x))) ^ n := h3
    _ = (1 - 2 * x) ^ n := by ring_nf
    _ ≤ ((1 - x) * (1 - x ^ 2)) ^ n := h2

end UnitDensity

end Abba
