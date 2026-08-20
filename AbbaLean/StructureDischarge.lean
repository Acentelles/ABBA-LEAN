import Mathlib
import AbbaLean.StructureCRT

set_option linter.style.header false

/-!
# ABBA — per-factor discharge from the discriminant

For a quadratic generator `ζ` (paper: `ζ = ζ_{2^r}` with `𝓞_L = 𝓞_K[ζ]`), the
identity `(σζ - ζ)² = (ζ + σζ)² - 4·ζ·σζ` shows that `θ(w) - w` is a unit for
`w = ζ mod J·B` as soon as the discriminant element `(ζ+σζ)² - 4ζσζ` is
invertible modulo `J·B` — which is exactly the unramifiedness input (for odd `q`
coprime to the discriminant).  This discharges hypothesis `hwu` of the uniform
per-factor theorem and, via `mem_center_iff`, gives the global center statement:
`Z(Λ_Q) = {a + u·0 : θ(a) = a}`.
-/

namespace Abba

namespace Twisted

section Discharge

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable (σ : B ≃ₐ[A] B) (hσ : ∀ x, σ (σ x) = x) (ξ₀ : A)

/-- Discharge of the `θ(w) - w` unit hypothesis from invertibility of the
discriminant element `(ζ+σζ)² - 4ζσζ` modulo the extended ideal. -/
theorem exists_theta_sub_unit (J : Ideal A) (ζ : B)
    (hδ : IsUnit (Ideal.Quotient.mk (J.map (algebraMap A B))
      ((ζ + σ ζ) ^ 2 - 4 * (ζ * σ ζ)))) :
    ∃ w, IsUnit ((quotData σ hσ ξ₀ J).θ w - w) := by
  refine ⟨Ideal.Quotient.mk _ ζ, ?_⟩
  have key : ((quotData σ hσ ξ₀ J).θ (Ideal.Quotient.mk (J.map (algebraMap A B)) ζ)
        - Ideal.Quotient.mk (J.map (algebraMap A B)) ζ) ^ 2
      = Ideal.Quotient.mk (J.map (algebraMap A B)) ((ζ + σ ζ) ^ 2 - 4 * (ζ * σ ζ)) := by
    rw [quotData_θ_mk, ← map_sub, ← map_pow]
    congr 1
    ring
  have h2 : IsUnit (((quotData σ hσ ξ₀ J).θ (Ideal.Quotient.mk (J.map (algebraMap A B)) ζ)
      - Ideal.Quotient.mk (J.map (algebraMap A B)) ζ) ^ 2) := by
    rw [key]
    exact hδ
  rw [sq] at h2
  exact isUnit_of_mul_isUnit_left h2

/-- **Global center statement**: with the discriminant invertible mod `Q·B`, the
center of the global twisted algebra consists exactly of the `θ`-fixed scalars
(paper: `Z(Λ_q) = 𝓞_{K_q}`, as fixed points). -/
theorem center_global (Q : Ideal A) (ζ : B)
    (hδ : IsUnit (Ideal.Quotient.mk (Q.map (algebraMap A B))
      ((ζ + σ ζ) ^ 2 - 4 * (ζ * σ ζ))))
    (x : Twisted (quotData σ hσ ξ₀ Q)) :
    x ∈ Subring.center (Twisted (quotData σ hσ ξ₀ Q))
      ↔ x.2 = 0 ∧ (quotData σ hσ ξ₀ Q).θ x.1 = x.1 :=
  mem_center_iff (exists_theta_sub_unit σ hσ ξ₀ Q ζ hδ) x

end Discharge

end Twisted

end Abba
