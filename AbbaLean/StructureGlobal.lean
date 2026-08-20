import Mathlib
import AbbaLean.StructureCRT

set_option linter.style.header false

/-!
# ABBA — Lemma `structure`, global assembly

Combining the equivariant CRT (`crtTwisted`) with per-factor matrix-ring
isomorphisms: if each factor `Twisted (quotData σ hσ ξ₀ (J i))` is isomorphic to
`M₂(kᵢ)`, then the global twisted algebra over `B ⧸ Q·B` is isomorphic to
`∏ᵢ M₂(kᵢ)`.  The per-factor input is exactly what `uniformEquiv` produces from
the two unit hypotheses (a unit `c` with `c·θ(c) = ξ` and a `w` with `θ(w) - w`
a unit) plus the dimension-2 fact; their arithmetic discharge from
unramifiedness is the remaining step.
-/

namespace Abba

namespace Twisted

open Function

section Global

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable (σ : B ≃ₐ[A] B) (hσ : ∀ x, σ (σ x) = x) (ξ₀ : A)
variable {ι : Type*} [Finite ι]
variable (J : ι → Ideal A) (Q : Ideal A)
variable (k : ι → Type*) [∀ i, CommRing (k i)]

/-- **Lemma `structure`, global assembly**: given the CRT hypotheses and a
matrix-ring isomorphism for each factor, the global twisted algebra is a product
of 2×2 matrix rings. -/
theorem structure_global
    (hcop : Pairwise (IsCoprime on fun i => (J i).map (algebraMap A B)))
    (hglob : Q.map (algebraMap A B) = ⨅ i, (J i).map (algebraMap A B))
    (hfac : ∀ i, Nonempty
      (Twisted (quotData σ hσ ξ₀ (J i)) ≃+* Matrix (Fin 2) (Fin 2) (k i))) :
    Nonempty (Twisted (quotData σ hσ ξ₀ Q) ≃+* ∀ i, Matrix (Fin 2) (Fin 2) (k i)) := by
  have e1 := crtTwisted σ hσ ξ₀ J Q hcop hglob
  have e2 : (∀ i, Twisted (quotData σ hσ ξ₀ (J i)))
      ≃+* ∀ i, Matrix (Fin 2) (Fin 2) (k i) :=
    RingEquiv.piCongrRight fun i => (hfac i).some
  exact ⟨e1.trans e2⟩

end Global

end Twisted

end Abba
