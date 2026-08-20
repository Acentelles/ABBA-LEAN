import Mathlib
import AbbaLean.StructureNumberField
import AbbaLean.StructureFixed

set_option linter.style.header false

/-!
# ABBA — Lemma `structure`, the ABBA instantiation

Discharges the remaining hypotheses of `structure_numberField` for the paper's
setting `L = ℚ(ζ_{2^r})`, `K = L⁺`, `ξ₀ = -1`, `q` odd:

* `delta_mul_sq_eq_four` — the discriminant element has the explicit cofactor
  `(ζ·Σ_{j<m} ζ^{2j})²`: from `ζσ(ζ) = 1` and `ζ^{2m} = -1`,
  `((ζ+σζ)² - 4ζσζ)·(ζ·Σζ^{2j})² = 4`, so `hδ` reduces to `2 ∉ 𝔮ᵢ` (`q` odd);
* residue-ring finiteness from maximality (`𝓞_K` is not a field, so `𝔮ᵢ ≠ ⊥`);
* `-1 ∉ 𝔮ᵢ` from properness;
* the dimension `[𝓞_L/𝔮ᵢ𝓞_L : 𝓞_K/𝔮ᵢ] = [L:K] = 2` via `finrank_quotient_map`.

Main result: `abba_structure` — the paper's `Λ_q ≅ ∏ M₂(𝓞_K/𝔮ᵢ)` with only the
factorization data and `2 ∉ 𝔮ᵢ` as inputs — and `abba_fixed`, the corresponding
center identification.
-/

namespace Abba

namespace Twisted

open Function Module NumberField

section Delta

/-- The discriminant element of a root of unity with `ζσ(ζ) = 1`, `ζ^{2m} = -1`
has an explicit cofactor squaring to `4`. -/
theorem delta_mul_sq_eq_four {B : Type*} [CommRing B] (ζ σζ : B) (hζ : ζ * σζ = 1)
    (m : ℕ) (hhalf : ζ ^ (2 * m) = -1) :
    ((ζ + σζ) ^ 2 - 4 * (ζ * σζ))
      * (ζ * ∑ j ∈ Finset.range m, ζ ^ (2 * j)) ^ 2 = 4 := by
  set E := ∑ j ∈ Finset.range m, ζ ^ (2 * j) with hE
  have hE2 : E = ∑ j ∈ Finset.range m, (ζ ^ 2) ^ j := by
    rw [hE]
    exact Finset.sum_congr rfl fun j _ => by rw [pow_mul]
  have hgeom : (ζ ^ 2 - 1) * E = -2 := by
    rw [hE2, mul_comm, geom_sum_mul, ← pow_mul, hhalf]
    ring
  have e1 : (ζ - σζ) * ζ = ζ ^ 2 - 1 := by linear_combination -hζ
  have e2 : ((ζ + σζ) ^ 2 - 4 * (ζ * σζ)) * (ζ * E) ^ 2
      = ((ζ - σζ) * ζ * E) ^ 2 := by ring
  rw [e2, e1, hgeom]
  norm_num

end Delta

section AbbaCase

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L]

/-- Residue-ring finiteness for the factors, from maximality alone. -/
theorem finite_factor (J : Ideal (𝓞 K)) [J.IsMaximal] :
    Finite ((𝓞 L) ⧸ J.map (algebraMap (𝓞 K) (𝓞 L))) := by
  have hbot : J ≠ ⊥ := by
    have h4 := Ideal.bot_lt_of_maximal J (RingOfIntegers.not_isField K)
    exact h4.ne'
  have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 L)) := by
    have hKL : Function.Injective (algebraMap (𝓞 K) L) := by
      rw [IsScalarTower.algebraMap_eq (𝓞 K) K L, RingHom.coe_comp]
      exact (algebraMap K L).injective.comp (IsFractionRing.injective (𝓞 K) K)
    intro a b hab
    apply hKL
    rw [IsScalarTower.algebraMap_eq (𝓞 K) (𝓞 L) L, RingHom.coe_comp,
      Function.comp_apply, Function.comp_apply, hab]
  have hbotB : J.map (algebraMap (𝓞 K) (𝓞 L)) ≠ ⊥ := by
    obtain ⟨x, hxmem, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    intro hb
    have h5 : algebraMap (𝓞 K) (𝓞 L) x ∈ (⊥ : Ideal (𝓞 L)) :=
      hb ▸ Ideal.mem_map_of_mem _ hxmem
    rw [Ideal.mem_bot] at h5
    exact hx0 (hinj (by rw [h5, map_zero]))
  exact Ring.HasFiniteQuotients.finiteQuotient hbotB

set_option linter.deprecated false in
/-- The per-factor dimension is `[L:K]`. -/
theorem dim_factor (J : Ideal (𝓞 K)) [J.IsMaximal] :
    finrank ((𝓞 K) ⧸ J) ((𝓞 L) ⧸ J.map (algebraMap (𝓞 K) (𝓞 L))) = finrank K L :=
  Ideal.finrank_quotient_map (R := 𝓞 K) (S := 𝓞 L) (p := J) K L

/-- Discriminant invertibility from `2 ∉ J` and the explicit cofactor. -/
theorem hdelta_factor (J : Ideal (𝓞 K)) [J.IsMaximal] (h2 : (2 : 𝓞 K) ∉ J)
    (ζ σζ : 𝓞 L) (hζ : ζ * σζ = 1) (m : ℕ) (hhalf : ζ ^ (2 * m) = -1) :
    IsUnit (Ideal.Quotient.mk (J.map (algebraMap (𝓞 K) (𝓞 L)))
      ((ζ + σζ) ^ 2 - 4 * (ζ * σζ))) := by
  have h2K : IsUnit (Ideal.Quotient.mk J (2 : 𝓞 K)) := by
    letI : Field ((𝓞 K) ⧸ J) := Ideal.Quotient.field J
    rw [isUnit_iff_ne_zero, Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact h2
  have h2B : IsUnit (Ideal.Quotient.mk (J.map (algebraMap (𝓞 K) (𝓞 L))) (2 : 𝓞 L)) := by
    have h3 := h2K.map
      (algebraMap ((𝓞 K) ⧸ J) ((𝓞 L) ⧸ J.map (algebraMap (𝓞 K) (𝓞 L))))
    rw [factorAlgebra_algebraMap, map_ofNat] at h3
    exact h3
  have h4B : IsUnit (Ideal.Quotient.mk (J.map (algebraMap (𝓞 K) (𝓞 L))) (4 : 𝓞 L)) := by
    have h6 : (4 : 𝓞 L) = 2 * 2 := by norm_num
    rw [h6, map_mul]
    exact h2B.mul h2B
  have hkey := delta_mul_sq_eq_four ζ σζ hζ m hhalf
  have h7 : Ideal.Quotient.mk (J.map (algebraMap (𝓞 K) (𝓞 L)))
        (((ζ + σζ) ^ 2 - 4 * (ζ * σζ))
          * (ζ * ∑ j ∈ Finset.range m, ζ ^ (2 * j)) ^ 2)
      = Ideal.Quotient.mk (J.map (algebraMap (𝓞 K) (𝓞 L))) (4 : 𝓞 L) := by
    rw [hkey]
  rw [map_mul] at h7
  exact isUnit_of_mul_isUnit_left (h7 ▸ h4B)

/-- **The ABBA instantiation of Lemma `structure`**: for `ξ₀ = -1`, a root of
unity `ζ` with `ζσ(ζ) = 1` and `ζ^{2m} = -1`, `[L:K] = 2`, and `Q = ∏ 𝔮ᵢ` a
product of distinct maximal ideals not containing `2` (i.e. `q` odd), the global
twisted algebra is `∏ᵢ M₂(𝓞_K/𝔮ᵢ)`. -/
theorem abba_structure
    (σL : L ≃ₐ[K] L) (hσL : ∀ x, σL (σL x) = x)
    (ζ : 𝓞 L) (hσζ : ζ * intConj σL ζ = 1)
    (m : ℕ) (hhalf : ζ ^ (2 * m) = -1)
    (hrank : finrank K L = 2)
    {ι : Type*} [Fintype ι]
    (J : ι → Ideal (𝓞 K)) [∀ i, (J i).IsMaximal]
    (hJne : Pairwise (fun i j => J i ≠ J j))
    (Q : Ideal (𝓞 K)) (hQ : Q = ∏ i, J i)
    (h2 : ∀ i, (2 : 𝓞 K) ∉ J i) :
    Nonempty (Twisted (quotData (intConj σL) (intConj_invol σL hσL) (-1) Q)
      ≃+* ∀ i, Matrix (Fin 2) (Fin 2) ((𝓞 K) ⧸ J i)) := by
  haveI hfin : ∀ i, Finite ((𝓞 L) ⧸ (J i).map (algebraMap (𝓞 K) (𝓞 L))) :=
    fun i => finite_factor (J i)
  have hdim : ∀ i, finrank ((𝓞 K) ⧸ J i)
      ((𝓞 L) ⧸ (J i).map (algebraMap (𝓞 K) (𝓞 L))) = 2 := by
    intro i
    rw [dim_factor (J i), hrank]
  have hδ : ∀ i, IsUnit (Ideal.Quotient.mk ((J i).map (algebraMap (𝓞 K) (𝓞 L)))
      ((ζ + intConj σL ζ) ^ 2 - 4 * (ζ * intConj σL ζ))) :=
    fun i => hdelta_factor (J i) (h2 i) ζ (intConj σL ζ) hσζ m hhalf
  have hξJ : ∀ i, (-1 : 𝓞 K) ∉ J i := by
    intro i hmem
    exact Ideal.IsMaximal.ne_top inferInstance
      (Ideal.eq_top_of_isUnit_mem _ hmem isUnit_one.neg)
  exact structure_numberField σL hσL (-1) J hJne Q hQ hdim ζ hδ hξJ

/-- **The ABBA instantiation of the center statement**: every `θ`-fixed element
of `𝓞_L ⧸ Q𝓞_L` comes from `𝓞_K`, so `Z(Λ_Q) = 𝓞_{K_Q}` with `center_global`. -/
theorem abba_fixed
    (σL : L ≃ₐ[K] L) (hσL : ∀ x, σL (σL x) = x)
    (ζ : 𝓞 L) (hσζ : ζ * intConj σL ζ = 1)
    (m : ℕ) (hhalf : ζ ^ (2 * m) = -1)
    (hrank : finrank K L = 2)
    {ι : Type*} [Fintype ι]
    (J : ι → Ideal (𝓞 K)) [∀ i, (J i).IsMaximal]
    (hJne : Pairwise (fun i j => J i ≠ J j))
    (Q : Ideal (𝓞 K)) (hQ : Q = ∏ i, J i)
    (h2 : ∀ i, (2 : 𝓞 K) ∉ J i)
    (x : (𝓞 L) ⧸ Q.map (algebraMap (𝓞 K) (𝓞 L)))
    (hx : (quotData (intConj σL) (intConj_invol σL hσL) (-1) Q).θ x = x) :
    ∃ a : 𝓞 K, x = Ideal.Quotient.mk (Q.map (algebraMap (𝓞 K) (𝓞 L)))
      (algebraMap (𝓞 K) (𝓞 L) a) := by
  classical
  haveI hfin : ∀ i, Finite ((𝓞 L) ⧸ (J i).map (algebraMap (𝓞 K) (𝓞 L))) :=
    fun i => finite_factor (J i)
  have hcopA : Pairwise (IsCoprime on J) := by
    intro i j hij
    show IsCoprime (J i) (J j)
    rw [Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne inferInstance inferInstance (hJne hij)
  have hcop : Pairwise (IsCoprime on fun i => (J i).map (algebraMap (𝓞 K) (𝓞 L))) := by
    intro i j hij
    exact isCoprime_map (hcopA hij)
  have hglob : Q.map (algebraMap (𝓞 K) (𝓞 L))
      = ⨅ i, (J i).map (algebraMap (𝓞 K) (𝓞 L)) := by
    rw [hQ, map_finset_prod]
    rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime (hcop.set_pairwise _)]
    simp
  have hdim : ∀ i, finrank ((𝓞 K) ⧸ J i)
      ((𝓞 L) ⧸ (J i).map (algebraMap (𝓞 K) (𝓞 L))) = 2 := by
    intro i
    rw [dim_factor (J i), hrank]
  have hδ : ∀ i, IsUnit (Ideal.Quotient.mk ((J i).map (algebraMap (𝓞 K) (𝓞 L)))
      ((ζ + intConj σL ζ) ^ 2 - 4 * (ζ * intConj σL ζ))) :=
    fun i => hdelta_factor (J i) (h2 i) ζ (intConj σL ζ) hσζ m hhalf
  exact fixed_global (intConj σL) (intConj_invol σL hσL) (-1) J hcopA Q hglob
    hdim ζ hδ x hx

end AbbaCase

end Twisted

end Abba
