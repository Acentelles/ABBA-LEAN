import Mathlib
import AbbaLean.Structure

set_option linter.style.header false

/-!
# ABBA — Hilbert 90 and norm surjectivity for quadratic algebras

For a commutative `k`-algebra `S` of dimension 2 with involution `θ` fixing `k`
and some `θ(w) - w` a unit, we prove without any case analysis:

* `fixed_mem_range` — the `θ`-fixed points are exactly `k` (else `{x, 1}` spans
  and `θ = id`, contradicting the unit `θ(w) - w`);
* `exists_unit_mul_theta_eq` — Hilbert 90: if `b·θ(b) = 1` then `b = a·θ(a)⁻¹`
  for a unit `a`.  Proof: `T(x) = x + b·θ(x)` satisfies `b·θ(T x) = T x`; if the
  range of `T` contains no unit it has dimension ≤ 1, hence lies in one maximal
  ideal `M`; then `T 1 = 1 + b ∈ M` and `T w ∈ M` give `w - θ(w) ∈ M`,
  contradicting the unit;
* `norm_unit_surjective` — for `S` finite, every nonzero `ξ ∈ k` is a "norm"
  `c·θ(c)` of a unit `c` (group counting with `φ(u) = u·θ(u)`,
  `ψ(u) = u·θ(u)⁻¹`, `ker φ = range ψ` by Hilbert 90, `ker ψ = k^×`).

This discharges the last per-factor hypothesis of the uniform theorem with no
étale dichotomy and no reducedness input.
-/

namespace Abba

namespace Twisted

open Module

section H90

variable {k S : Type*} [Field k] [CommRing S] [Algebra k S]
variable (d : TwistData S)
variable (hθk : ∀ r : k, d.θ (algebraMap k S r) = algebraMap k S r)
variable [FiniteDimensional k S]

include hθk in
/-- Fixed points of the involution are scalars, given `dim = 2` and a unit
`θ(w) - w`. -/
theorem fixed_mem_range (hdim : finrank k S = 2)
    (hwu : ∃ w : S, IsUnit (d.θ w - w)) (x : S) (hx : d.θ x = x) :
    ∃ r : k, x = algebraMap k S r := by
  have hnt : Nontrivial S := by
    rcases subsingleton_or_nontrivial S with hs | hs
    · rw [Module.finrank_zero_of_subsingleton] at hdim
      omega
    · exact hs
  by_contra hcon
  push_neg at hcon
  -- {x, 1} is linearly independent
  have hli : LinearIndependent k ![x, 1] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_contra hne
    push_neg at hne
    rcases eq_or_ne s 0 with hs | hs
    · rcases eq_or_ne t 0 with ht | ht
      · exact (hne hs) ht
      · apply ht
        have h1 : (algebraMap k S) t = 0 := by
          have := hst
          rw [hs, zero_smul, zero_add, Algebra.smul_def, mul_one] at this
          exact this
        exact (algebraMap k S).injective (by rw [h1, map_zero])
    · apply hcon (-t / s)
      have h1 : x = (-t / s) • (1 : S) := by
        have h2 : s • x = -(t • (1 : S)) := by
          rw [eq_neg_iff_add_eq_zero]
          exact hst
        have h3 : x = s⁻¹ • (-(t • (1 : S))) := by
          rw [← h2, smul_smul, inv_mul_cancel₀ hs, one_smul]
        rw [h3]
        rw [smul_neg, smul_smul]
        rw [show s⁻¹ * t = -(-t / s) by field_simp]
        rw [neg_smul, neg_neg]
      rw [h1, Algebra.smul_def, mul_one]
  -- span {x, 1} = ⊤
  have hspan : Submodule.span k (Set.range ![x, 1]) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hli, hdim]
    simp
  -- θ fixes everything
  have hall : ∀ y : S, d.θ y = y := by
    intro y
    have hy : y ∈ Submodule.span k (Set.range ![x, 1]) := by
      rw [hspan]; trivial
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      fin_cases i
      · exact hx
      · exact map_one _
    | zero => exact map_zero _
    | add a b _ _ ha hb => rw [map_add, ha, hb]
    | smul r a _ ha =>
      rw [Algebra.smul_def, map_mul, hθk, ha]
  obtain ⟨w, hw⟩ := hwu
  rw [hall w, sub_self] at hw
  exact zero_ne_one (isUnit_zero_iff.mp hw)

include hθk in
/-- **Hilbert 90**: if `b·θ(b) = 1` then `b = a·θ(a)⁻¹` for some unit `a`,
in the form `b·θ(a) = a`. -/
theorem exists_unit_mul_theta_eq (hdim : finrank k S = 2)
    (hwu : ∃ w : S, IsUnit (d.θ w - w)) (b : S) (hb : b * d.θ b = 1) :
    ∃ a : Sˣ, b * d.θ (a : S) = (a : S) := by
  classical
  set T : S →ₗ[k] S :=
    { toFun := fun x => x + b * d.θ x
      map_add' := by
        intro v w
        simp only [map_add]
        ring
      map_smul' := by
        intro r y
        simp only [Algebra.smul_def, map_mul, hθk, RingHom.id_apply]
        ring } with hT
  have hT_apply : ∀ x, T x = x + b * d.θ x := fun _ => rfl
  have hkey : ∀ x, b * d.θ (T x) = T x := by
    intro x
    have h1 : T x = x + b * d.θ x := rfl
    rw [h1, map_add, map_mul, d.invol]
    calc b * (d.θ x + d.θ b * x)
        = b * d.θ x + (b * d.θ b) * x := by ring
      _ = x + b * d.θ x := by rw [hb]; ring
  by_cases hunit : ∃ x, IsUnit (T x)
  · obtain ⟨x, hx⟩ := hunit
    obtain ⟨a, ha⟩ := hx
    exact ⟨a, by rw [ha]; exact hkey x⟩
  · exfalso
    push_neg at hunit
    obtain ⟨w, hw⟩ := hwu
    obtain ⟨M, hM, hT1, hTw⟩ : ∃ M : Ideal S, M.IsMaximal ∧ T 1 ∈ M ∧ T w ∈ M := by
      have hnt : Nontrivial S := by
        rcases subsingleton_or_nontrivial S with hs | hs
        · rw [Module.finrank_zero_of_subsingleton] at hdim
          omega
        · exact hs
      rcases eq_or_ne (LinearMap.range T) ⊥ with hbot | hbot
      · obtain ⟨M, hM⟩ := Ideal.exists_maximal S
        have hz : T = 0 := LinearMap.range_eq_bot.mp hbot
        refine ⟨M, hM, ?_, ?_⟩ <;> simp [hz]
      · obtain ⟨y, hy_mem, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
        have hr1 : finrank k (LinearMap.range T) ≤ 1 := by
          by_contra hcon
          push_neg at hcon
          have h2 : finrank k (LinearMap.range T) = 2 :=
            le_antisymm (hdim ▸ Submodule.finrank_le _) hcon
          have htop : LinearMap.range T = ⊤ :=
            Submodule.eq_top_of_finrank_eq (by rw [h2, hdim])
          obtain ⟨x, hx⟩ := LinearMap.range_eq_top.mp htop 1
          exact hunit x (hx ▸ isUnit_one)
        have hspan : LinearMap.range T = Submodule.span k {y} := by
          symm
          apply Submodule.eq_of_le_of_finrank_le
          · rw [Submodule.span_le, Set.singleton_subset_iff]
            exact hy_mem
          · rw [finrank_span_singleton hy0]
            exact hr1
        obtain ⟨x₀, hx₀⟩ := hy_mem
        have hynu : y ∈ nonunits S := by
          rw [← hx₀]
          exact hunit x₀
        obtain ⟨M, hM, hyM⟩ := exists_max_ideal_of_mem_nonunits hynu
        have hmem : ∀ z : S, z ∈ LinearMap.range T → z ∈ M := by
          intro z hz
          rw [hspan] at hz
          obtain ⟨r, hr'⟩ := Submodule.mem_span_singleton.mp hz
          rw [← hr', Algebra.smul_def]
          exact M.mul_mem_left _ hyM
        exact ⟨M, hM, hmem _ (LinearMap.mem_range_self T 1),
          hmem _ (LinearMap.mem_range_self T w)⟩
    have h1b : (1 : S) + b ∈ M := by
      have h0 := hT1
      rwa [hT_apply, map_one, mul_one] at h0
    have hsub : w - d.θ w ∈ M := by
      have h2 := M.sub_mem hTw (M.mul_mem_left (d.θ w) h1b)
      have h3 : T w - d.θ w * (1 + b) = w - d.θ w := by
        rw [hT_apply]
        ring
      rwa [h3] at h2
    have hu : IsUnit (w - d.θ w) := by
      have h4 := hw.neg
      simpa using h4
    exact hM.ne_top (M.eq_top_of_isUnit_mem hsub hu)

end H90

section NormSurj

variable {k S : Type*} [Field k] [CommRing S] [Algebra k S]
variable (d : TwistData S)
variable (hθk : ∀ r : k, d.θ (algebraMap k S r) = algebraMap k S r)
variable [FiniteDimensional k S]

/-- The involution on units. -/
def θU : Sˣ →* Sˣ := Units.map (d.θ : S ≃+* S).toRingHom.toMonoidHom

@[simp] theorem θU_coe (u : Sˣ) : ((θU d u : Sˣ) : S) = d.θ (u : S) := rfl

include hθk in
/-- **Norm surjectivity**: every nonzero scalar is `c·θ(c)` for a unit `c`. -/
theorem norm_unit_surjective [Finite S] (hdim : finrank k S = 2)
    (hwu : ∃ w : S, IsUnit (d.θ w - w)) (ξr : k) (hξr : ξr ≠ 0) :
    ∃ c : S, IsUnit c ∧ c * d.θ c = algebraMap k S ξr := by
  classical
  have hnt : Nontrivial S := by
    rcases subsingleton_or_nontrivial S with hs | hs
    · rw [Module.finrank_zero_of_subsingleton] at hdim
      omega
    · exact hs
  set φ : Sˣ →* Sˣ := MonoidHom.mk' (fun u => u * θU d u)
    (fun u v => by
      rw [map_mul]
      exact mul_mul_mul_comm u v (θU d u) (θU d v)) with hφ
  have hφ_apply : ∀ u, φ u = u * θU d u := fun _ => rfl
  set ψ : Sˣ →* Sˣ := MonoidHom.mk' (fun u => u * (θU d u)⁻¹)
    (fun u v => by
      rw [map_mul, mul_inv]
      exact mul_mul_mul_comm u v (θU d u)⁻¹ (θU d v)⁻¹) with hψ
  have hψ_apply : ∀ u, ψ u = u * (θU d u)⁻¹ := fun _ => rfl
  have hθθ : ∀ u : Sˣ, θU d (θU d u) = u := by
    intro u
    ext
    simp [d.invol]
  -- ker φ = range ψ
  have hker_range : φ.ker = ψ.range := by
    ext u
    constructor
    · intro hu
      have hu1 : φ u = 1 := hu
      have hu' : (u : S) * d.θ (u : S) = 1 := by
        have h2 := congrArg (Units.val) hu1
        rw [hφ_apply] at h2
        simpa using h2
      obtain ⟨a, ha⟩ := exists_unit_mul_theta_eq d hθk hdim hwu (u : S) hu'
      have hEq : u * θU d a = a := by
        ext
        simpa using ha
      refine ⟨a, ?_⟩
      rw [hψ_apply, mul_inv_eq_iff_eq_mul]
      exact hEq.symm
    · rintro ⟨v, rfl⟩
      have h1 : φ (ψ v) = 1 := by
        rw [hφ_apply, hψ_apply, map_mul, map_inv, hθθ]
        group
      exact h1
  -- ker ψ = range of k^×
  set ι : kˣ →* Sˣ := Units.map (algebraMap k S).toMonoidHom with hι
  have hι_coe : ∀ r : kˣ, ((ι r : Sˣ) : S) = algebraMap k S (r : k) := fun _ => rfl
  have hker_ψ : ψ.ker = ι.range := by
    ext u
    constructor
    · intro hu
      have hu1 : ψ u = 1 := hu
      rw [hψ_apply] at hu1
      have hu2 : u = θU d u := mul_inv_eq_one.mp hu1
      have hfix : d.θ (u : S) = (u : S) := by
        have h6 := congrArg (Units.val) hu2
        rw [θU_coe] at h6
        exact h6.symm
      obtain ⟨r, hr⟩ := fixed_mem_range d hθk hdim hwu (u : S) hfix
      have hr0 : r ≠ 0 := by
        intro h0
        rw [h0, map_zero] at hr
        exact u.ne_zero hr
      refine ⟨Units.mk0 r hr0, ?_⟩
      ext
      show algebraMap k S r = _
      exact hr.symm
    · rintro ⟨r, rfl⟩
      have h1 : θU d (ι r) = ι r := by
        ext
        show d.θ (algebraMap k S (r : k)) = algebraMap k S (r : k)
        exact hθk r
      show ψ (ι r) = 1
      rw [hψ_apply, h1]
      exact mul_inv_cancel _
  -- range φ ⊆ range ι
  have hrange_le : φ.range ≤ ι.range := by
    rintro _ ⟨u, rfl⟩
    have hfix : d.θ ((φ u : Sˣ) : S) = ((φ u : Sˣ) : S) := by
      rw [hφ_apply]
      show d.θ ((u : S) * d.θ (u : S)) = (u : S) * d.θ (u : S)
      rw [map_mul, d.invol]
      ring
    obtain ⟨r, hr⟩ := fixed_mem_range d hθk hdim hwu _ hfix
    have hr0 : r ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hr
      exact (φ u).ne_zero hr
    refine ⟨Units.mk0 r hr0, ?_⟩
    ext
    show algebraMap k S r = _
    exact hr.symm
  -- counting
  have hcard1 : Nat.card φ.range * Nat.card φ.ker = Nat.card Sˣ := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker).symm
  have hcard2 : Nat.card ψ.range * Nat.card ψ.ker = Nat.card Sˣ := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker).symm
  have hψrange_pos : 0 < Nat.card ψ.range := Nat.card_pos
  have hcard_eq : Nat.card φ.range = Nat.card ψ.ker := by
    have h1 : Nat.card φ.range * Nat.card ψ.range = Nat.card Sˣ := by
      rw [← hker_range]
      exact hcard1
    apply Nat.eq_of_mul_eq_mul_left hψrange_pos
    calc Nat.card ψ.range * Nat.card φ.range
        = Nat.card φ.range * Nat.card ψ.range := mul_comm _ _
      _ = Nat.card Sˣ := h1
      _ = Nat.card ψ.range * Nat.card ψ.ker := hcard2.symm
  have hcard_ι : Nat.card ι.range = Nat.card ψ.ker := by rw [hker_ψ]
  -- range φ = range ι by cardinality
  have hrange_eq : φ.range = ι.range := by
    apply SetLike.ext'
    refine Set.eq_of_subset_of_ncard_le hrange_le ?_ (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe,
      SetLike.coe_sort_coe, hcard_ι, ← hcard_eq]
  have hmem : ι (Units.mk0 ξr hξr) ∈ φ.range := by
    rw [hrange_eq]
    exact ⟨Units.mk0 ξr hξr, rfl⟩
  obtain ⟨u, hu⟩ := hmem
  refine ⟨(u : S), u.isUnit, ?_⟩
  have h5 := congrArg (Units.val) hu
  rw [hφ_apply] at h5
  have h7 : ((u * θU d u : Sˣ) : S) = (u : S) * d.θ (u : S) := by
    rw [Units.val_mul, θU_coe]
  rw [h7] at h5
  rw [h5]
  rfl

end NormSurj

end Twisted

end Abba
