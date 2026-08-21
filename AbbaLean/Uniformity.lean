import Mathlib

set_option linter.style.header false

/-!
# ABBA — the uniformity chain, deterministic and counting cores

* `fiber_card_eq` / `prob_fiber` / `commprob0` — Lemma `commprob0`: an additive
  map pushes the uniform distribution to the uniform distribution on its range
  (all fibers over the range have the kernel's cardinality), applied to
  `𝐚 ↦ Σᵢ [aᵢ, zᵢ]`.
* `statdistcollisions` — the Impagliazzo–Zuckerman collision lemma (imported in
  the paper): `SD(p, U_S) ≤ ½√(|S|·CP(p) - 1)`, by Cauchy–Schwarz.
* `comm_mem_span_pairs` — Lemma `gensetT0`, bilinear core: if `x` spans, every
  commutator lies in the span of the pairwise commutators `[xᵢ, xⱼ]`.
* `commSpan_matrix_eq_traceless` — in `M₂(F)`, the commutator span is exactly
  the traceless matrices (explicit witnesses; this replaces the imported
  single-commutator theorem of Estes–Taussky, which is stronger than needed).
* `range_commMapL_eq` — Cor `commprobunif`, deterministic heart: if the `zᵢ`
  span, the range of `𝐚 ↦ Σᵢ [aᵢ, zᵢ]` is the full commutator span (hence
  `𝒯₀`, and with `commprob0` the syndrome is uniform on `𝒯₀`).

Remaining imports of the paper's chain, not formalized: the Gaussian facts
(`regev316` on linear independence of Gaussian samples, the `√2σ` convolution
step) and the final negligible-fraction bookkeeping.
-/

namespace Abba

section CommProb

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- Fibers of an additive map over its range all have the kernel's size. -/
theorem fiber_card_eq (f : A →+ B) (b : B) (hb : b ∈ f.range) :
    Nat.card {a : A // f a = b} = Nat.card f.ker := by
  obtain ⟨a₀, rfl⟩ := hb
  refine Nat.card_congr ⟨fun x => ⟨x.1 - a₀, ?_⟩, fun y => ⟨y.1 + a₀, ?_⟩, ?_, ?_⟩
  · have hx := x.2
    rw [AddMonoidHom.mem_ker, map_sub, hx, sub_self]
  · have hy := y.2
    rw [AddMonoidHom.mem_ker] at hy
    rw [map_add, hy, zero_add]
  · intro x
    ext
    simp
  · intro y
    ext
    simp

/-- **Lemma `commprob0`, abstract form**: the probability that a uniform input
hits any fixed range element is `1/|range|`. -/
theorem prob_fiber (f : A →+ B) [Finite A] (b : B) (hb : b ∈ f.range) :
    (Nat.card {a : A // f a = b} : ℚ) / Nat.card A
      = 1 / Nat.card f.range := by
  have h1 := fiber_card_eq f b hb
  haveI : Finite f.range :=
    Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivRange f).toEquiv
  have h2 : Nat.card A = Nat.card f.range * Nat.card f.ker := by
    rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv]
    exact AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker
  have hk : 0 < Nat.card f.ker := Nat.card_pos
  have hr : 0 < Nat.card f.range := Nat.card_pos
  rw [h1, h2]
  push_cast
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

variable {R : Type*} [Ring R] {m : ℕ}

/-- The syndrome map `𝐚 ↦ Σᵢ [aᵢ, zᵢ]`, additive in `𝐚`. -/
def commMap (z : Fin m → R) : (Fin m → R) →+ R where
  toFun a := ∑ i, (a i * z i - z i * a i)
  map_zero' := by simp
  map_add' a b := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    show (a i + b i) * z i - z i * (a i + b i) = _
    noncomm_ring

@[simp] theorem commMap_apply (z a : Fin m → R) :
    commMap z a = ∑ i, (a i * z i - z i * a i) := rfl

/-- **Lemma `commprob0`**: for uniform `𝐚`, the syndrome `Σᵢ [aᵢ, zᵢ]` is
uniform on its range `𝒯₀^𝐳`; in particular `Pr[Σᵢ [aᵢ, zᵢ] = b] = 1/|𝒯₀^𝐳|`
for every `b` in the range. -/
theorem commprob0 (z : Fin m → R) [Finite R] (b : R) (hb : b ∈ (commMap z).range) :
    (Nat.card {a : Fin m → R // commMap z a = b} : ℚ) / Nat.card (Fin m → R)
      = 1 / Nat.card (commMap z).range :=
  prob_fiber _ b hb

end CommProb

section IZ

open Finset

/-- **The Impagliazzo–Zuckerman collision lemma** (Lemma `statdistcollisions`):
the statistical distance from uniform is at most `½√(|S|·CP - 1)` where `CP`
is the collision probability. -/
theorem statdistcollisions {S : Type*} [Fintype S] [Nonempty S] (p : S → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    (1 / 2) * ∑ x, |p x - ((Fintype.card S : ℝ))⁻¹|
      ≤ (1 / 2) * Real.sqrt ((Fintype.card S) * (∑ x, (p x) ^ 2) - 1) := by
  set u : ℝ := ((Fintype.card S : ℝ))⁻¹ with hu
  have hcard : (0 : ℝ) < Fintype.card S := by
    exact_mod_cast Fintype.card_pos
  have hcu : (Fintype.card S : ℝ) * u = 1 := by
    rw [hu, mul_inv_cancel₀ (ne_of_gt hcard)]
  -- variance identity
  have hvar : ∑ x, (p x - u) ^ 2 = (∑ x, (p x) ^ 2) - u := by
    have h1 : ∑ x, (p x - u) ^ 2
        = (∑ x, (p x) ^ 2) - 2 * u * (∑ x, p x) + (Fintype.card S : ℝ) * u ^ 2 := by
      rw [Finset.sum_congr rfl (fun x _ => by ring :
        ∀ x ∈ Finset.univ, (p x - u) ^ 2 = (p x) ^ 2 - 2 * u * p x + u ^ 2)]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [h1, hsum]
    have h2 : (Fintype.card S : ℝ) * u ^ 2 = u := by
      rw [sq, ← mul_assoc, hcu, one_mul]
    rw [h2]
    ring
  -- Cauchy–Schwarz with ones
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset S)) (f := fun x => |p x - u|)
  rw [Finset.card_univ] at hcs
  have habs : ∑ x, |p x - u| ^ 2 = ∑ x, (p x - u) ^ 2 :=
    Finset.sum_congr rfl fun x _ => sq_abs _
  rw [habs, hvar] at hcs
  -- conclude via sqrt
  have hle : ∑ x, |p x - u| ≤ Real.sqrt ((Fintype.card S) * (∑ x, (p x) ^ 2) - 1) := by
    rw [show (Fintype.card S : ℝ) * (∑ x, (p x) ^ 2) - 1
        = (Fintype.card S : ℝ) * ((∑ x, (p x) ^ 2) - u) by
      rw [mul_sub, hcu]]
    exact Real.le_sqrt_of_sq_le hcs
  linarith

end IZ

section GensetT0

variable {F R : Type*} [CommRing F] [Ring R] [Algebra F R]

/-- The span of all commutators. -/
def commSpan (F R : Type*) [CommRing F] [Ring R] [Algebra F R] : Submodule F R :=
  Submodule.span F {w | ∃ y z : R, w = y * z - z * y}

/-- **Lemma `gensetT0`, bilinear core**: if the family `x` spans, every
commutator lies in the span of the pairwise commutators `[xᵢ, xⱼ]`. -/
theorem comm_mem_span_pairs {ι : Type*} (x : ι → R)
    (hx : Submodule.span F (Set.range x) = ⊤) (y z : R) :
    y * z - z * y ∈ Submodule.span F {w | ∃ i j, w = x i * x j - x j * x i} := by
  set P := Submodule.span F {w | ∃ i j, w = x i * x j - x j * x i} with hP
  have h1 : ∀ (i : ι) (w : R), x i * w - w * x i ∈ P := by
    intro i w
    have hw : w ∈ Submodule.span F (Set.range x) := by rw [hx]; trivial
    induction hw using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨j, rfl⟩ := hv
      exact Submodule.subset_span ⟨i, j, rfl⟩
    | zero => simpa using P.zero_mem
    | add a b _ _ ha hb =>
      have h3 : x i * (a + b) - (a + b) * x i
          = (x i * a - a * x i) + (x i * b - b * x i) := by noncomm_ring
      rw [h3]
      exact P.add_mem ha hb
    | smul c a _ ha =>
      have h3 : x i * (c • a) - (c • a) * x i = c • (x i * a - a * x i) := by
        rw [mul_smul_comm, smul_mul_assoc, smul_sub]
      rw [h3]
      exact P.smul_mem c ha
  have hy : y ∈ Submodule.span F (Set.range x) := by rw [hx]; trivial
  induction hy using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨i, rfl⟩ := hv
    exact h1 i z
  | zero => simpa using P.zero_mem
  | add a b _ _ ha hb =>
    have h3 : (a + b) * z - z * (a + b) = (a * z - z * a) + (b * z - z * b) := by
      noncomm_ring
    rw [h3]
    exact P.add_mem ha hb
  | smul c a _ ha =>
    have h3 : (c • a) * z - z * (c • a) = c • (a * z - z * a) := by
      rw [smul_mul_assoc, mul_smul_comm, smul_sub]
    rw [h3]
    exact P.smul_mem c ha

/-- In `M₂(F)`, the commutator span is exactly the traceless matrices
(with explicit commutator witnesses; the paper imports the stronger
single-commutator theorem, which is unnecessary for the span statement). -/
theorem commSpan_matrix_eq_traceless {F : Type*} [CommRing F] :
    commSpan F (Matrix (Fin 2) (Fin 2) F)
      = LinearMap.ker (Matrix.traceLinearMap (Fin 2) F F) := by
  apply le_antisymm
  · rw [commSpan, Submodule.span_le]
    rintro _ ⟨y, z, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    show Matrix.trace (y * z - z * y) = 0
    rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
  · intro M hM
    rw [LinearMap.mem_ker] at hM
    have hM11 : M 1 1 = -(M 0 0) := by
      have h0 : Matrix.trace M = 0 := hM
      have h1 : Matrix.trace M = M 0 0 + M 1 1 := Matrix.trace_fin_two M
      have h2 : M 0 0 + M 1 1 = 0 := by rw [← h1, h0]
      linear_combination h2
    have hdecomp : M
        = M 0 1 • ((!![1,0;0,0] : Matrix (Fin 2) (Fin 2) F) * !![0,1;0,0]
            - !![0,1;0,0] * !![1,0;0,0])
          + M 1 0 • ((!![0,0;0,1] : Matrix (Fin 2) (Fin 2) F) * !![0,0;1,0]
            - !![0,0;1,0] * !![0,0;0,1])
          + M 0 0 • ((!![0,1;0,0] : Matrix (Fin 2) (Fin 2) F) * !![0,0;1,0]
            - !![0,0;1,0] * !![0,1;0,0]) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, hM11] <;> ring
    rw [hdecomp]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_ <;>
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, rfl⟩)

variable {m : ℕ}

/-- The syndrome map as an `F`-linear map in `𝐚`. -/
def commMapL (F : Type*) [CommRing F] {R : Type*} [Ring R] [Algebra F R]
    (z : Fin m → R) : (Fin m → R) →ₗ[F] R where
  toFun a := ∑ i, (a i * z i - z i * a i)
  map_add' a b := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    show (a i + b i) * z i - z i * (a i + b i) = _
    noncomm_ring
  map_smul' c a := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    show (c • a i) * z i - z i * (c • a i) = _
    rw [smul_mul_assoc, mul_smul_comm, smul_sub]

@[simp] theorem commMapL_apply (z a : Fin m → R) :
    commMapL F z a = ∑ i, (a i * z i - z i * a i) := rfl

/-- **Cor `commprobunif`, deterministic heart**: if the `zᵢ` span, the range of
the syndrome map `𝐚 ↦ Σᵢ [aᵢ, zᵢ]` is the full commutator span (`= 𝒯₀` for
matrix rings by `commSpan_matrix_eq_traceless`). -/
theorem range_commMapL_eq (z : Fin m → R)
    (hz : Submodule.span F (Set.range z) = ⊤) :
    LinearMap.range (commMapL F z) = commSpan F R := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    rw [commMapL_apply]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.subset_span ⟨a i, z i, rfl⟩
  · rw [commSpan, Submodule.span_le]
    rintro _ ⟨y, w, rfl⟩
    rw [SetLike.mem_coe]
    have hw : w ∈ Submodule.span F (Set.range z) := by rw [hz]; trivial
    induction hw using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨i, rfl⟩ := hv
      refine ⟨Pi.single i y, ?_⟩
      rw [commMapL_apply, Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj]
      · intro h
        exact absurd (Finset.mem_univ i) h
    | zero => simpa using (LinearMap.range (commMapL F z)).zero_mem
    | add a b _ _ ha hb =>
      have h3 : y * (a + b) - (a + b) * y = (y * a - a * y) + (y * b - b * y) := by
        noncomm_ring
      rw [h3]
      exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      have h3 : y * (c • a) - (c • a) * y = c • (y * a - a * y) := by
        rw [mul_smul_comm, smul_mul_assoc, smul_sub]
      rw [h3]
      exact Submodule.smul_mem _ c ha

end GensetT0

end Abba
