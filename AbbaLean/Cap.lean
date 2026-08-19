import Mathlib

set_option linter.style.header false

/-!
# ABBA — Lemma `cap` (challenge-set cap)

Paper: Lemma `Lemma:cap`.  The ring-theoretic core is independent of the structure
lemma: in any product ring with a nontrivial factor, a set with pairwise-invertible
differences projects injectively onto that factor.  Applied to
`Z(Λ_q) ≅ ∏ 𝔽_{q^f}` this gives `|𝒞| ≤ q^f`.

Note the `Nontrivial` hypothesis: in a trivial factor `0` is a unit, and the claim
fails — a boundary case surfaced by formalization (harmless for the paper, where the
factors are `M₂(𝔽_{q^f})`).
-/

namespace Abba

section Cap

variable {ι : Type*} {R : ι → Type*} [∀ i, Ring (R i)]

/-- In a product ring, a set with pairwise-invertible differences projects
injectively onto every nontrivial factor. -/
theorem injOn_proj_of_pairwise_unit_sub (C : Set (Π i, R i))
    (h : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → IsUnit (x - y)) (i₀ : ι) [Nontrivial (R i₀)] :
    Set.InjOn (fun x => x i₀) C := by
  intro x hx y hy hxy
  by_contra hne
  have hu : IsUnit ((x - y) i₀) := (h x hx y hy hne).map (Pi.evalRingHom R i₀)
  have hxy' : x i₀ = y i₀ := hxy
  rw [Pi.sub_apply, hxy', sub_self] at hu
  exact hu.ne_zero rfl

/-- Cardinality form: `|𝒞| ≤ |R i₀|` for any nontrivial finite factor `i₀`. -/
theorem card_le_of_pairwise_unit_sub (C : Set (Π i, R i))
    (h : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → IsUnit (x - y)) (i₀ : ι)
    [Nontrivial (R i₀)] [Finite (R i₀)] :
    Nat.card C ≤ Nat.card (R i₀) := by
  have hinj := injOn_proj_of_pairwise_unit_sub C h i₀
  calc Nat.card C = Nat.card ((fun x => x i₀) '' C) :=
        (Nat.card_image_of_injOn hinj).symm
    _ ≤ Nat.card (Set.univ : Set (R i₀)) :=
        Nat.card_mono Set.finite_univ (Set.subset_univ _)
    _ = Nat.card (R i₀) := Nat.card_univ

end Cap

/-- The non-central counterexample from the paper's remark: over any field (here `ℤ`
for concreteness), `ρ = E₂₁` and the traceless `t = E₁₂` give `ρt = E₂₂` with
nonzero trace, so `𝒯₀` is not stable under one-sided non-central multiplication. -/
example : ∃ ρ t : Matrix (Fin 2) (Fin 2) ℤ,
    t.trace = 0 ∧ (ρ * t).trace ≠ 0 := by
  refine ⟨!![0,0;1,0], !![0,1;0,0], ?_, ?_⟩
  · simp [Matrix.trace_fin_two]
  · norm_num [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

end Abba
