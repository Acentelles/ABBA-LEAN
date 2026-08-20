import Mathlib
import AbbaLean.StructureUniform
import AbbaLean.TwistedPi

set_option linter.style.header false

/-!
# ABBA — Lemma `structure`: twisting data on quotients

Descent of an involution to quotients by extended ideals: for `σ : B ≃ₐ[A] B`
with `σ² = 1` and an ideal `J` of `A`, the extended ideal `J·B` is `σ`-stable, so
`σ` descends to `B ⧸ J·B` and, together with a twist `ξ₀ ∈ A`, yields
`TwistData (B ⧸ J·B)` (`quotData`).

For the paper: `A = 𝓞_K`, `B = 𝓞_L`, `σ` the conjugation restricted to integers
(`galRestrict`), `J = q𝓞_K` or a prime factor `𝔮ᵢ`; this is the global `Λ_q`
(via `Twisted (quotData …)`) and its CRT factors.
-/

namespace Abba

namespace Twisted

section Quot

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable (σ : B ≃ₐ[A] B)

/-- Extended ideals are stable under `A`-algebra automorphisms. -/
theorem map_extended_stable (J : Ideal A) :
    (J.map (algebraMap A B)).map ((σ : B ≃+* B) : B →+* B) = J.map (algebraMap A B) := by
  rw [Ideal.map_map]
  congr 1
  ext a
  exact σ.commutes a

/-- The involution descended to the quotient by an extended ideal. -/
def quotTheta (J : Ideal A) :
    (B ⧸ J.map (algebraMap A B)) ≃+* (B ⧸ J.map (algebraMap A B)) :=
  Ideal.quotientEquiv _ _ (σ : B ≃+* B) (map_extended_stable σ J).symm

@[simp] theorem quotTheta_mk (J : Ideal A) (x : B) :
    quotTheta σ J (Ideal.Quotient.mk (J.map (algebraMap A B)) x)
      = Ideal.Quotient.mk (J.map (algebraMap A B)) (σ x) :=
  Ideal.quotientEquiv_mk _ _ _ _ x

variable (hσ : ∀ x, σ (σ x) = x) (ξ₀ : A)

/-- The twisting data on `B ⧸ J·B`: descended involution and the twist `ξ₀ ∈ A`. -/
def quotData (J : Ideal A) : TwistData (B ⧸ J.map (algebraMap A B)) where
  θ := quotTheta σ J
  invol := by
    intro s
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective s
    rw [quotTheta_mk, quotTheta_mk, hσ]
  ξ := Ideal.Quotient.mk _ (algebraMap A B ξ₀)
  fixed := by
    rw [quotTheta_mk, σ.commutes]

@[simp] theorem quotData_θ_mk (J : Ideal A) (x : B) :
    (quotData σ hσ ξ₀ J).θ (Ideal.Quotient.mk (J.map (algebraMap A B)) x)
      = Ideal.Quotient.mk (J.map (algebraMap A B)) (σ x) :=
  quotTheta_mk σ J x

@[simp] theorem quotData_ξ (J : Ideal A) :
    (quotData σ hσ ξ₀ J).ξ = Ideal.Quotient.mk (J.map (algebraMap A B)) (algebraMap A B ξ₀) :=
  rfl

/-- The descended involution fixes the image of `A` (the input to `hθk` of the
uniform theorem, phrased at the level of representatives). -/
theorem quotData_θ_fixes (J : Ideal A) (a : A) :
    (quotData σ hσ ξ₀ J).θ (Ideal.Quotient.mk (J.map (algebraMap A B)) (algebraMap A B a))
      = Ideal.Quotient.mk (J.map (algebraMap A B)) (algebraMap A B a) := by
  rw [quotData_θ_mk, σ.commutes]

end Quot

end Twisted

end Abba
