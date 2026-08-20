import Mathlib
import AbbaLean.StructureUniform
import AbbaLean.StructureDischarge
import AbbaLean.Hilbert90

set_option linter.style.header false

/-!
# ABBA — Lemma `structure`: the per-factor matrix-ring isomorphism, assembled

For a maximal ideal `J` of `A` with finite 2-dimensional quotient data, the
factor `Twisted (quotData σ hσ ξ₀ J)` is a 2×2 matrix ring over `A ⧸ J`:
`hθk` comes from the descent (`quotData_θ_fixes`), `θ(w) - w` a unit from the
discriminant (`exists_theta_sub_unit`), the norm equation `c·θ(c) = ξ` from
Hilbert-90 norm surjectivity (`norm_unit_surjective`), and the isomorphism from
the uniform theorem (`uniformEquiv`).
-/

namespace Abba

namespace Twisted

section Factor

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable (J : Ideal A)

/-- The quotient-algebra structure `A⧸J → B⧸J·B`. -/
noncomputable instance factorAlgebra :
    Algebra (A ⧸ J) (B ⧸ J.map (algebraMap A B)) :=
  Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map

@[simp] theorem factorAlgebra_algebraMap (a : A) :
    algebraMap (A ⧸ J) (B ⧸ J.map (algebraMap A B)) (Ideal.Quotient.mk J a)
      = Ideal.Quotient.mk (J.map (algebraMap A B)) (algebraMap A B a) := by
  rfl

variable (σ : B ≃ₐ[A] B) (hσ : ∀ x, σ (σ x) = x) (ξ₀ : A)

/-- The descended involution fixes `A⧸J`-scalars (input to the uniform theorem). -/
theorem quotData_hθk (r : A ⧸ J) :
    (quotData σ hσ ξ₀ J).θ (algebraMap (A ⧸ J) (B ⧸ J.map (algebraMap A B)) r)
      = algebraMap (A ⧸ J) (B ⧸ J.map (algebraMap A B)) r := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [factorAlgebra_algebraMap]
  exact quotData_θ_fixes σ hσ ξ₀ J a

/-- **Per-factor matrix-ring isomorphism.** -/
theorem factor_matrix_ring [J.IsMaximal]
    [Finite (B ⧸ J.map (algebraMap A B))]
    (hdim : Module.finrank (A ⧸ J) (B ⧸ J.map (algebraMap A B)) = 2)
    (ζ : B)
    (hδ : IsUnit (Ideal.Quotient.mk (J.map (algebraMap A B))
      ((ζ + σ ζ) ^ 2 - 4 * (ζ * σ ζ))))
    (hξJ : ξ₀ ∉ J) :
    Nonempty (Twisted (quotData σ hσ ξ₀ J) ≃+* Matrix (Fin 2) (Fin 2) (A ⧸ J)) := by
  letI : Field (A ⧸ J) := Ideal.Quotient.field J
  letI : FiniteDimensional (A ⧸ J) (B ⧸ J.map (algebraMap A B)) :=
    Module.Finite.of_finite
  have hwu := exists_theta_sub_unit σ hσ ξ₀ J ζ hδ
  have hξr : (Ideal.Quotient.mk J ξ₀ : A ⧸ J) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hξJ
  obtain ⟨c, hcu, hc⟩ := norm_unit_surjective (quotData σ hσ ξ₀ J)
    (quotData_hθk J σ hσ ξ₀) hdim hwu (Ideal.Quotient.mk J ξ₀) hξr
  have hc' : c * (quotData σ hσ ξ₀ J).θ c = (quotData σ hσ ξ₀ J).ξ := by
    rw [hc, factorAlgebra_algebraMap]
    rfl
  exact ⟨uniformEquiv (quotData σ hσ ξ₀ J) (quotData_hθk J σ hσ ξ₀) c hc' hcu hwu hdim⟩

end Factor

end Twisted

end Abba
