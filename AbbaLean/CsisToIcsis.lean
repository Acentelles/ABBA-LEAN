import Mathlib

set_option linter.style.header false

/-!
# ABBA — Proposition `CSIStoICSIS` (deterministic core)

Paper: "ABBA: Lattice-based Commitments from Commutators", Prop. `Propn:CSIStoICSIS`.
The "PPT reduction" wrapper is not formalizable (no complexity theory in Mathlib);
we verify the mathematical content:

1. `solution_map` / `solution_ne_zero`: correctness of `z := (y₁,…,y_m,1)`.
2. `trace_one`: `Tr_{K/ℚ}(1) = n`, giving `‖1‖² = 2n` for the coefficient norm
   `‖x‖² = 2·Tr(Σ x_{ab}²)`.
3. `trace_sum_sq_ge`: the AM-GM floor — for totally real `K` of degree `n` and a
   nonzero family of integers `x`, `Tr(Σ xᵢ²) ≥ n`, hence `‖x‖ ≥ √(2n)`.
   (Remark after Prop `ICSIStoICSISx`.)

The distributional step (`v := -a_{m+1}` yields an exactly-distributed I-CSIS
instance) is definitional and is checked exactly in `abba_checks.sage`.
-/

namespace Abba

/-! ## 1. The algebraic solution mapping -/

section Algebraic

variable {R : Type*} [Ring R] {m : ℕ}

/-- If `∑ aᵢ yᵢ = v` and `v = -a_{m+1}`, then `z := (y, 1)` satisfies `∑ aᵢ zᵢ = 0`. -/
theorem solution_map (a : Fin (m + 1) → R) (y : Fin m → R)
    (h : ∑ i, a i.castSucc * y i = -a (Fin.last m)) :
    ∑ i, a i * (Fin.snoc y 1 : Fin (m + 1) → R) i = 0 := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, mul_one]
  rw [h]
  exact neg_add_cancel _

/-- The padded solution is nonzero, since its last coordinate is `1`. -/
theorem solution_ne_zero [Nontrivial R] (y : Fin m → R) :
    (Fin.snoc y 1 : Fin (m + 1) → R) ≠ 0 := by
  intro h
  have h1 : (Fin.snoc y 1 : Fin (m + 1) → R) (Fin.last m) = 0 := congrFun h (Fin.last m)
  rw [Fin.snoc_last] at h1
  exact one_ne_zero h1

end Algebraic

/-! ## 2. The trace identity `Tr(1) = n` (so `‖1‖² = 2n`) -/

section TraceOne

variable (K : Type*) [Field K] [NumberField K]

open Module

theorem trace_one : Algebra.trace ℚ K 1 = (finrank ℚ K : ℚ) := by
  simpa using Algebra.trace_algebraMap (S := K) (1 : ℚ)

end TraceOne

/-! ## 3. The AM-GM norm floor -/

section NormFloor

open NumberField Module

variable {K : Type*} [Field K] [NumberField K] [IsTotallyReal K]

private lemma prod_rpow_of_nonneg' {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h : ∀ i ∈ s, 0 ≤ f i) (r : ℝ) :
    (∏ i ∈ s, f i) ^ r = ∏ i ∈ s, f i ^ r := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.prod_cons, Finset.prod_cons,
      Real.mul_rpow (h a (by simp)) (Finset.prod_nonneg fun i hi => h i (by simp [hi])),
      ih fun i hi => h i (by simp [hi])]

/-- Every ℚ-algebra embedding of a totally real field into ℂ takes real values. -/
private lemma im_eq_zero (σ : K →ₐ[ℚ] ℂ) (y : K) : (σ y).im = 0 := by
  have h1 : NumberField.ComplexEmbedding.IsReal (σ : K →+* ℂ) :=
    NumberField.IsTotallyReal.complexEmbedding_isReal _
  have h2 := RingHom.congr_fun h1 y
  simpa [Complex.conj_eq_iff_im, NumberField.ComplexEmbedding.conjugate] using h2

private instance : Nonempty (K →ₐ[ℚ] ℂ) := by
  have h : Fintype.card (K →ₐ[ℚ] ℂ) = finrank ℚ K := AlgHom.card ℚ K ℂ
  have hpos : 0 < Fintype.card (K →ₐ[ℚ] ℂ) := by rw [h]; exact finrank_pos
  exact Fintype.card_pos_iff.mp hpos

/-- AM-GM floor: a nonzero sum of squares of algebraic integers in a totally real
field of degree `n` has trace at least `n`. -/
theorem trace_sum_sq_ge {ι : Type*} [Fintype ι] (x : ι → 𝓞 K) (hx : x ≠ 0) :
    (finrank ℚ K : ℚ) ≤ Algebra.trace ℚ K (algebraMap (𝓞 K) K (∑ i, x i ^ 2)) := by
  classical
  set u : 𝓞 K := ∑ i, x i ^ 2 with hu_def
  set t : K := algebraMap (𝓞 K) K u with ht_def
  have ht2 : t = ∑ i, (algebraMap (𝓞 K) K (x i)) ^ 2 := by
    rw [ht_def, hu_def, map_sum]
    exact Finset.sum_congr rfl fun i _ => map_pow _ _ _
  -- each embedding value of t is the real number s σ ≥ 0
  set s : (K →ₐ[ℚ] ℂ) → ℝ := fun σ => (σ t).re with hs_def
  have hσt : ∀ σ : K →ₐ[ℚ] ℂ, σ t = ((s σ : ℝ) : ℂ) := by
    intro σ
    apply Complex.ext
    · simp [hs_def]
    · simp [im_eq_zero σ t]
  have hs_eq : ∀ σ : K →ₐ[ℚ] ℂ, s σ = ∑ i, ((σ (algebraMap (𝓞 K) K (x i))).re) ^ 2 := by
    intro σ
    have h1 : σ t = ∑ i, (σ (algebraMap (𝓞 K) K (x i))) ^ 2 := by
      rw [ht2, map_sum]
      exact Finset.sum_congr rfl fun i _ => map_pow _ _ _
    have h2 : ∀ i : ι, σ (algebraMap (𝓞 K) K (x i))
        = (((σ (algebraMap (𝓞 K) K (x i))).re : ℝ) : ℂ) := by
      intro i
      apply Complex.ext
      · simp
      · simp [im_eq_zero σ]
    have h3 : σ t = ((∑ i, ((σ (algebraMap (𝓞 K) K (x i))).re) ^ 2 : ℝ) : ℂ) := by
      rw [h1, Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [Complex.ofReal_pow]
        exact congrArg (· ^ 2) (h2 i)
    simp only [hs_def]
    rw [h3, Complex.ofReal_re]
  have hs_nonneg : ∀ σ : K →ₐ[ℚ] ℂ, 0 ≤ s σ := by
    intro σ
    rw [hs_eq σ]
    positivity
  -- nonvanishing of u
  have hu_ne : u ≠ 0 := by
    intro h0
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    have hσ : Nonempty (K →ₐ[ℚ] ℂ) := inferInstance
    obtain ⟨σ⟩ := hσ
    have hz : s σ = 0 := by
      rw [hs_def, ht_def, h0]
      simp
    rw [hs_eq σ] at hz
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => sq_nonneg ((σ (algebraMap (𝓞 K) K (x j))).re))).mp hz i (Finset.mem_univ i)
    have hre : (σ (algebraMap (𝓞 K) K (x i))).re = 0 := by
      have := sq_eq_zero_iff.mp hterm
      exact this
    have hzero : σ (algebraMap (𝓞 K) K (x i)) = 0 := by
      apply Complex.ext
      · simpa using hre
      · simpa using im_eq_zero σ (algebraMap (𝓞 K) K (x i))
    have hK0 : algebraMap (𝓞 K) K (x i) = 0 := by
      have hinj : Function.Injective (σ : K →+* ℂ) := (σ : K →+* ℂ).injective
      exact hinj (by simpa using hzero)
    have hxi : x i = 0 := by
      have hinj2 : Function.Injective (algebraMap (𝓞 K) K) := IsFractionRing.injective _ _
      exact hinj2 (by simpa using hK0)
    exact hi hxi
  -- trace and norm as sums/products of the s σ
  have htr : ((Algebra.trace ℚ K t : ℚ) : ℂ) = ∑ σ : K →ₐ[ℚ] ℂ, σ t := by
    have h := trace_eq_sum_embeddings (K := ℚ) (L := K) (E := ℂ) (x := t)
    simpa using h
  have htr_re : ((Algebra.trace ℚ K t : ℚ) : ℝ) = ∑ σ : K →ₐ[ℚ] ℂ, s σ := by
    have h : ((Algebra.trace ℚ K t : ℚ) : ℂ) = ((∑ σ : K →ₐ[ℚ] ℂ, s σ : ℝ) : ℂ) := by
      rw [htr, Finset.sum_congr rfl fun σ _ => hσt σ]
      push_cast
      rfl
    exact_mod_cast h
  have hnorm : ((Algebra.norm ℚ t : ℚ) : ℂ) = ∏ σ : K →ₐ[ℚ] ℂ, σ t := by
    have h := Algebra.norm_eq_prod_embeddings (K := ℚ) (L := K) (E := ℂ) t
    simpa using h
  have hnorm_re : ((Algebra.norm ℚ t : ℚ) : ℝ) = ∏ σ : K →ₐ[ℚ] ℂ, s σ := by
    have h : ((Algebra.norm ℚ t : ℚ) : ℂ) = ((∏ σ : K →ₐ[ℚ] ℂ, s σ : ℝ) : ℂ) := by
      rw [hnorm, Finset.prod_congr rfl fun σ _ => hσt σ]
      push_cast
      rfl
    exact_mod_cast h
  -- |N| ≥ 1, and N = ∏ s ≥ 0, so ∏ s ≥ 1
  have hprod1 : (1 : ℝ) ≤ ∏ σ : K →ₐ[ℚ] ℂ, s σ := by
    have hNz : Algebra.norm ℤ u ≠ 0 := by
      rw [Algebra.norm_ne_zero_iff]
      exact hu_ne
    have h1 : (1 : ℤ) ≤ |Algebra.norm ℤ u| := Int.one_le_abs hNz
    have hcoe : ((Algebra.norm ℤ u : ℚ)) = Algebra.norm ℚ t := by
      rw [ht_def]
      exact_mod_cast Algebra.coe_norm_int u
    have hnn : 0 ≤ ∏ σ : K →ₐ[ℚ] ℂ, s σ :=
      Finset.prod_nonneg fun σ _ => hs_nonneg σ
    have habs : (1 : ℝ) ≤ |((Algebra.norm ℚ t : ℚ) : ℝ)| := by
      rw [← hcoe]
      push_cast
      exact_mod_cast h1
    rwa [hnorm_re, abs_of_nonneg hnn] at habs
  -- AM-GM
  set nK := finrank ℚ K with hnK
  have hn_pos : 0 < nK := finrank_pos
  have hcard : Fintype.card (K →ₐ[ℚ] ℂ) = nK := by
    rw [hnK]
    exact AlgHom.card ℚ K ℂ
  have hw_sum : ∑ _σ : K →ₐ[ℚ] ℂ, ((nK : ℝ))⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    field_simp
  have hamgm := Real.geom_mean_le_arith_mean_weighted (s := Finset.univ)
    (fun _ => ((nK : ℝ))⁻¹) s (fun _ _ => by positivity) hw_sum (fun σ _ => hs_nonneg σ)
  have hlhs : (1 : ℝ) ≤ ∏ σ : K →ₐ[ℚ] ℂ, s σ ^ ((nK : ℝ))⁻¹ := by
    rw [← prod_rpow_of_nonneg' _ _ (fun σ _ => hs_nonneg σ)]
    calc (1 : ℝ) = 1 ^ ((nK : ℝ))⁻¹ := (Real.one_rpow _).symm
      _ ≤ (∏ σ : K →ₐ[ℚ] ℂ, s σ) ^ ((nK : ℝ))⁻¹ :=
          Real.rpow_le_rpow zero_le_one hprod1 (by positivity)
  have hsum : (nK : ℝ) ≤ ∑ σ : K →ₐ[ℚ] ℂ, s σ := by
    have h1 : (1 : ℝ) ≤ ((nK : ℝ))⁻¹ * ∑ σ : K →ₐ[ℚ] ℂ, s σ := by
      calc (1 : ℝ) ≤ ∏ σ : K →ₐ[ℚ] ℂ, s σ ^ ((nK : ℝ))⁻¹ := hlhs
        _ ≤ ∑ σ : K →ₐ[ℚ] ℂ, ((nK : ℝ))⁻¹ * s σ := hamgm
        _ = ((nK : ℝ))⁻¹ * ∑ σ : K →ₐ[ℚ] ℂ, s σ := by rw [Finset.mul_sum]
    have hn' : (0 : ℝ) < (nK : ℝ) := by exact_mod_cast hn_pos
    have h2 := mul_le_mul_of_nonneg_left h1 hn'.le
    rwa [mul_one, ← mul_assoc, mul_inv_cancel₀ hn'.ne', one_mul] at h2
  have : ((finrank ℚ K : ℚ) : ℝ) ≤ ((Algebra.trace ℚ K t : ℚ) : ℝ) := by
    rw [htr_re]
    exact_mod_cast hsum
  exact_mod_cast this

end NormFloor

end Abba
