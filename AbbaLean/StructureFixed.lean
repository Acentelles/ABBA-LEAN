import Mathlib
import AbbaLean.StructureNumberField

set_option linter.style.header false

/-!
# ABBA — Lemma `structure`: the fixed points are `𝓞_K/Q`

Completes the paper's center statement `Z(Λ_Q) = 𝓞_{K_Q}`: every `θ`-fixed
element of `𝓞_L ⧸ Q𝓞_L` is the image of an element of `𝓞_K`.

The proof needs no CRT transport: a fixed element is fixed modulo each factor
`𝔮ᵢ𝓞_L` (since `Q𝓞_L ⊆ 𝔮ᵢ𝓞_L`), the per-factor fixed points are scalars
(`fixed_mem_range`), and the resulting family of scalars glues to a single
element of `𝓞_K` by CRT surjectivity on the `𝓞_K`-side
(`Ideal.pi_quotient_surjective`).
-/

namespace Abba

namespace Twisted

open Function Module NumberField

section Fixed

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable (σ : B ≃ₐ[A] B) (hσ : ∀ x, σ (σ x) = x) (ξ₀ : A)

/-- **Global fixed points**: with the per-factor data, every `θ`-fixed element of
`B ⧸ Q·B` comes from `A`.  Together with `center_global`, this is the paper's
`Z(Λ_Q) = 𝓞_{K_Q}`. -/
theorem fixed_global {ι : Type*} [Fintype ι]
    (J : ι → Ideal A) [∀ i, (J i).IsMaximal]
    (hcopA : Pairwise (IsCoprime on J))
    (Q : Ideal A)
    (hglob : Q.map (algebraMap A B) = ⨅ i, (J i).map (algebraMap A B))
    [∀ i, Finite (B ⧸ (J i).map (algebraMap A B))]
    (hdim : ∀ i, finrank (A ⧸ J i) (B ⧸ (J i).map (algebraMap A B)) = 2)
    (ζ : B)
    (hδ : ∀ i, IsUnit (Ideal.Quotient.mk ((J i).map (algebraMap A B))
      ((ζ + σ ζ) ^ 2 - 4 * (ζ * σ ζ))))
    (x : B ⧸ Q.map (algebraMap A B))
    (hx : (quotData σ hσ ξ₀ Q).θ x = x) :
    ∃ a : A, x = Ideal.Quotient.mk (Q.map (algebraMap A B)) (algebraMap A B a) := by
  classical
  obtain ⟨xb, rfl⟩ := Ideal.Quotient.mk_surjective x
  -- the difference σ(xb) - xb lies in Q·B
  have hmem : σ xb - xb ∈ Q.map (algebraMap A B) := by
    rw [quotData_θ_mk] at hx
    exact Ideal.Quotient.eq.mp hx
  -- per-factor fixedness
  have hfix_i : ∀ i, (quotData σ hσ ξ₀ (J i)).θ
      (Ideal.Quotient.mk ((J i).map (algebraMap A B)) xb)
        = Ideal.Quotient.mk ((J i).map (algebraMap A B)) xb := by
    intro i
    rw [quotData_θ_mk, Ideal.Quotient.eq]
    have hQle : Q.map (algebraMap A B) ≤ (J i).map (algebraMap A B) :=
      hglob ▸ iInf_le _ i
    exact hQle hmem
  -- per-factor scalars
  have hscal : ∀ i, ∃ a : A,
      Ideal.Quotient.mk ((J i).map (algebraMap A B)) xb
        = Ideal.Quotient.mk ((J i).map (algebraMap A B)) (algebraMap A B a) := by
    intro i
    letI : Field (A ⧸ J i) := Ideal.Quotient.field (J i)
    letI : FiniteDimensional (A ⧸ J i) (B ⧸ (J i).map (algebraMap A B)) :=
      Module.Finite.of_finite
    have hwu := exists_theta_sub_unit σ hσ ξ₀ (J i) ζ (hδ i)
    obtain ⟨r, hr⟩ := fixed_mem_range (quotData σ hσ ξ₀ (J i))
      (quotData_hθk (J i) σ hσ ξ₀) (hdim i) hwu _ (hfix_i i)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [factorAlgebra_algebraMap] at hr
    exact ⟨a, hr⟩
  choose af haf using hscal
  -- glue by CRT surjectivity on the A-side
  obtain ⟨a, ha⟩ := Ideal.pi_quotient_surjective hcopA
    (fun i => Ideal.Quotient.mk (J i) (af i))
  refine ⟨a, ?_⟩
  rw [Ideal.Quotient.eq, hglob]
  rw [Submodule.mem_iInf]
  intro i
  -- xb - algebraMap a = (xb - algebraMap (af i)) + algebraMap (af i - a)
  have h1 : xb - algebraMap A B (af i) ∈ (J i).map (algebraMap A B) := by
    have := haf i
    rw [Ideal.Quotient.eq] at this
    exact this
  have h2 : af i - a ∈ J i := by
    have h3 := ha i
    -- h3 : mk (J i) a = mk (J i) (af i)  (or symm)
    have h4 : (Ideal.Quotient.mk (J i)) (af i - a) = 0 := by
      rw [map_sub, ← h3, sub_self]
    exact Ideal.Quotient.eq_zero_iff_mem.mp h4
  have h5 : algebraMap A B (af i - a) ∈ (J i).map (algebraMap A B) :=
    Ideal.mem_map_of_mem _ h2
  have h6 : xb - algebraMap A B a
      = (xb - algebraMap A B (af i)) + algebraMap A B (af i - a) := by
    rw [map_sub]
    ring
  rw [h6]
  exact Ideal.add_mem _ h1 h5

end Fixed

end Twisted

end Abba
