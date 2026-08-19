import Mathlib

set_option linter.style.header false

/-!
# ABBA — Lemma `shortinvert` (core steps)

Paper: Lemma `Lemma:shortinvert`.  Formalized as three reusable steps, phrased so as
not to require `𝓞_{K⁺} = ℤ[ζ+ζ⁻¹]`:

1. `abs_embedding_zeta_add_inv_le`: every embedding sends `ζ^i + ζ^{-i}` into the
   closed disc of radius 2.
2. `abs_norm_le_of_embeddings_le`: embedding bounds give `|N_{K/ℚ}(α)| ≤ B^{[K:ℚ]}`.
3. `isUnit_mod_of_norm_coprime`: if `q ∤ N(α)` then `α` is a unit in `𝓞_K/(q)`.

Combining: `α = c₀ + Σ cᵢ(ζ^i + ζ^{-i})` nonzero with `|cᵢ| ≤ β` has all embeddings
`< 2d⁺β`; if `(2d⁺β)^{d⁺} ≤ q^f ≤` every prime-power norm above `q`, then `q ∤ N(α)`
and `α` is invertible mod `q` (Cor `Hc` for differences of challenge elements).
-/

namespace Abba

open NumberField Module

section EmbeddingBound

/-- Step 1: embeddings of `ζ^i + ζ^{-i}` have absolute value at most 2. -/
theorem abs_embedding_zeta_add_inv_le {K : Type*} [Field K] {n : ℕ} (hn : n ≠ 0)
    (ζ : K) (hζ : IsPrimitiveRoot ζ n) (φ : K →+* ℂ) (i : ℕ) :
    ‖φ (ζ ^ i + ζ⁻¹ ^ i)‖ ≤ 2 := by
  have hpow : (φ ζ) ^ n = 1 := by
    rw [← map_pow, hζ.pow_eq_one, map_one]
  have h1 : ‖φ ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hpow hn
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hn
  have h2 : ‖φ (ζ⁻¹)‖ = 1 := by
    rw [map_inv₀, norm_inv, h1, inv_one]
  calc ‖φ (ζ ^ i + ζ⁻¹ ^ i)‖ = ‖φ ζ ^ i + φ ζ⁻¹ ^ i‖ := by rw [map_add, map_pow, map_pow]
    _ ≤ ‖φ ζ ^ i‖ + ‖φ ζ⁻¹ ^ i‖ := norm_add_le _ _
    _ = ‖φ ζ‖ ^ i + ‖φ ζ⁻¹‖ ^ i := by rw [norm_pow, norm_pow]
    _ = 2 := by rw [h1, h2]; norm_num

end EmbeddingBound

section NormBound

variable {K : Type*} [Field K] [NumberField K]

private instance : Nonempty (K →ₐ[ℚ] ℂ) := by
  have h : Fintype.card (K →ₐ[ℚ] ℂ) = finrank ℚ K := AlgHom.card ℚ K ℂ
  have hpos : 0 < Fintype.card (K →ₐ[ℚ] ℂ) := by rw [h]; exact finrank_pos
  exact Fintype.card_pos_iff.mp hpos

/-- Step 2: if every complex embedding of `α` has norm at most `B`, then
`|N_{K/ℚ}(α)| ≤ B ^ [K:ℚ]`. -/
theorem abs_norm_le_of_embeddings_le (α : 𝓞 K) {B : ℝ}
    (h : ∀ φ : K →ₐ[ℚ] ℂ, ‖φ (algebraMap (𝓞 K) K α)‖ ≤ B) :
    |((Algebra.norm ℤ α : ℤ) : ℝ)| ≤ B ^ finrank ℚ K := by
  classical
  set a : K := algebraMap (𝓞 K) K α with ha
  have hnorm : ((Algebra.norm ℚ a : ℚ) : ℂ) = ∏ φ : K →ₐ[ℚ] ℂ, φ a := by
    have h1 := Algebra.norm_eq_prod_embeddings (K := ℚ) (L := K) (E := ℂ) a
    simpa using h1
  have hcoe : ((Algebra.norm ℤ α : ℚ)) = Algebra.norm ℚ a := by
    rw [ha]
    exact_mod_cast Algebra.coe_norm_int α
  have habs : |((Algebra.norm ℤ α : ℤ) : ℝ)| = ∏ φ : K →ₐ[ℚ] ℂ, ‖φ a‖ := by
    have h1 : ‖((Algebra.norm ℚ a : ℚ) : ℂ)‖ = ∏ φ : K →ₐ[ℚ] ℂ, ‖φ a‖ := by
      rw [hnorm, norm_prod]
    rw [← hcoe, Complex.norm_ratCast] at h1
    rw [← h1]
    push_cast
    norm_cast
  rw [habs]
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (h (Classical.arbitrary _))
  calc ∏ φ : K →ₐ[ℚ] ℂ, ‖φ a‖ ≤ ∏ _φ : K →ₐ[ℚ] ℂ, B :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun φ _ => h φ)
    _ = B ^ finrank ℚ K := by
        rw [Finset.prod_const, Finset.card_univ, AlgHom.card ℚ K ℂ]

end NormBound

section UnitMod

variable {K : Type*} [Field K] [NumberField K]

/-- Step 3: an algebraic integer whose ℤ-norm is prime to `q` is a unit modulo `q`. -/
theorem isUnit_mod_of_norm_coprime (α : 𝓞 K) (q : ℕ) (hq : Nat.Prime q)
    (h : ¬ (q : ℤ) ∣ Algebra.norm ℤ α) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(q : 𝓞 K)}) α) := by
  by_contra hu
  -- otherwise span {α, q} is proper, hence inside a maximal ideal M
  have htop : Ideal.span {α} ⊔ Ideal.span {(q : 𝓞 K)} ≠ ⊤ := by
    intro htop
    apply hu
    have h1 : (1 : 𝓞 K) ∈ Ideal.span {α} ⊔ Ideal.span {(q : 𝓞 K)} := by
      rw [htop]; trivial
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ha
    have hb0 : Ideal.Quotient.mk (Ideal.span {(q : 𝓞 K)}) b = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hb
    have hmk : Ideal.Quotient.mk (Ideal.span {(q : 𝓞 K)}) (c * α) = 1 := by
      have h2 : Ideal.Quotient.mk (Ideal.span {(q : 𝓞 K)}) (a + b) = 1 := by
        rw [hab]; exact map_one _
      rwa [map_add, hb0, add_zero, ← hc] at h2
    have hmul : Ideal.Quotient.mk (Ideal.span {(q : 𝓞 K)}) α
        * Ideal.Quotient.mk (Ideal.span {(q : 𝓞 K)}) c = 1 := by
      rw [← map_mul, mul_comm α c]
      exact hmk
    exact isUnit_iff_exists.mpr ⟨_, hmul, by rwa [mul_comm] at hmul⟩
  obtain ⟨M, hM, hMle⟩ := Ideal.exists_le_maximal _ htop
  have hα : Ideal.span {α} ≤ M := le_trans le_sup_left hMle
  have hqM : Ideal.span {(q : 𝓞 K)} ≤ M := le_trans le_sup_right hMle
  -- absNorm M divides both |N(α)| and q^n
  have d1 : Ideal.absNorm M ∣ (Algebra.norm ℤ α).natAbs := by
    have := Ideal.absNorm_dvd_absNorm_of_le hα
    rwa [Ideal.absNorm_span_singleton] at this
  have d2 : Ideal.absNorm M ∣ q ^ finrank ℚ K := by
    have hqmap : (q : 𝓞 K) = algebraMap ℤ (𝓞 K) (q : ℤ) := by push_cast; rfl
    have := Ideal.absNorm_dvd_absNorm_of_le hqM
    rwa [Ideal.absNorm_span_singleton, hqmap, Algebra.norm_algebraMap,
      NumberField.RingOfIntegers.rank, Int.natAbs_pow, Int.natAbs_natCast] at this
  have hMne : Ideal.absNorm M ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact hM.ne_top
  obtain ⟨p, pp, pdvd⟩ := Nat.exists_prime_and_dvd hMne
  have hpq : p = q := (Nat.prime_dvd_prime_iff_eq pp hq).mp
    (pp.dvd_of_dvd_pow (pdvd.trans d2))
  apply h
  rw [← Int.dvd_natAbs]
  exact_mod_cast (hpq ▸ pdvd).trans d1

end UnitMod

end Abba
