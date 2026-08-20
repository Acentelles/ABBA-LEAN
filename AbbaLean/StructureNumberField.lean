import Mathlib
import AbbaLean.StructureGlobal
import AbbaLean.StructureFactor

set_option linter.style.header false

/-!
# ABBA — Lemma `structure`, number-field instantiation

The paper's setting: `L/K` number fields, conjugation `σ` restricted to rings of
integers via `galRestrict`, `Q = q𝓞_K = ∏ 𝔮ᵢ` a product of distinct maximal
ideals.  Combining the equivariant CRT, the per-factor matrix-ring isomorphism,
and the arithmetic discharges:

`structure_numberField : Λ_Q ≃+* ∏ᵢ M₂(𝓞_K ⧸ 𝔮ᵢ)`.

The remaining inputs are the finiteness/dimension facts for the factors (from
`finrank_quotient_map` and finiteness of residue rings) and the discriminant
invertibility `hδ`, both direct consequences of `q` odd and unramified.
-/

namespace Abba

namespace Twisted

open Function Module NumberField

section NumberFieldInst

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L]

/-- Conjugation restricted to the rings of integers. -/
noncomputable def intConj (σL : L ≃ₐ[K] L) : (𝓞 L) ≃ₐ[𝓞 K] (𝓞 L) :=
  galRestrict (𝓞 K) K L (𝓞 L) σL

theorem intConj_invol (σL : L ≃ₐ[K] L) (hσL : ∀ x, σL (σL x) = x) :
    ∀ x, intConj σL (intConj σL x) = x := by
  intro x
  have h1 : σL * σL = 1 := by
    ext y
    exact hσL y
  have h2 : intConj σL (intConj σL x)
      = ((galRestrict (𝓞 K) K L (𝓞 L)) (σL * σL)) x := by
    rw [map_mul]
    rfl
  rw [h2, h1, map_one]
  rfl

/-- `Ideal.map` commutes with finite products. -/
theorem map_finset_prod {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    {ι : Type*} (J : ι → Ideal A) (s : Finset ι) :
    (∏ i ∈ s, J i).map f = ∏ i ∈ s, (J i).map f := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp [Ideal.one_eq_top, Ideal.map_top]
  | cons a s ha ih => rw [Finset.prod_cons, Finset.prod_cons, Ideal.map_mul, ih]

/-- **Lemma `structure`, number-field form**: for distinct maximal ideals `𝔮ᵢ`
with `Q = ∏ 𝔮ᵢ`, discriminant invertible and `ξ₀` coprime to each `𝔮ᵢ`, the
global twisted algebra over `𝓞_L ⧸ Q𝓞_L` is `∏ᵢ M₂(𝓞_K ⧸ 𝔮ᵢ)`. -/
theorem structure_numberField
    (σL : L ≃ₐ[K] L) (hσL : ∀ x, σL (σL x) = x) (ξ₀ : 𝓞 K)
    {ι : Type*} [Fintype ι]
    (J : ι → Ideal (𝓞 K)) [∀ i, (J i).IsMaximal]
    (hJne : Pairwise (fun i j => J i ≠ J j))
    (Q : Ideal (𝓞 K)) (hQ : Q = ∏ i, J i)
    [∀ i, Finite ((𝓞 L) ⧸ (J i).map (algebraMap (𝓞 K) (𝓞 L)))]
    (hdim : ∀ i, finrank ((𝓞 K) ⧸ J i)
      ((𝓞 L) ⧸ (J i).map (algebraMap (𝓞 K) (𝓞 L))) = 2)
    (ζ : 𝓞 L)
    (hδ : ∀ i, IsUnit (Ideal.Quotient.mk ((J i).map (algebraMap (𝓞 K) (𝓞 L)))
      ((ζ + intConj σL ζ) ^ 2 - 4 * (ζ * intConj σL ζ))))
    (hξJ : ∀ i, ξ₀ ∉ J i) :
    Nonempty (Twisted (quotData (intConj σL) (intConj_invol σL hσL) ξ₀ Q)
      ≃+* ∀ i, Matrix (Fin 2) (Fin 2) ((𝓞 K) ⧸ J i)) := by
  classical
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
  exact structure_global (intConj σL) (intConj_invol σL hσL) ξ₀ J Q
    (fun i => (𝓞 K) ⧸ J i) hcop hglob
    (fun i => factor_matrix_ring (J i) (intConj σL) (intConj_invol σL hσL) ξ₀
      (hdim i) ζ (hδ i) (hξJ i))

end NumberFieldInst

end Twisted

end Abba
