module

public import MMP.AlgebraicGeometry.DeRham.LogCartierCoordinates
public import StacksFrontier.LinearAlgebra.ExteriorPower.Localization
public import StacksFrontier.RingTheory.DeRham.PolynomialHomotopy

/-!
# The logarithmic inverse Cartier isomorphism: gluing

Let `p` be a prime and `A → L` a map of rings of characteristic `p`. A closed form `x` of `L`
over `A` **represents** the inverse Cartier image of a form `ω` when the class of `x` in the
cohomology of the Frobenius-twisted de Rham complex is `C⁻¹ ω`
(`MMP.DeRham.IsInvCartierRep`). Representatives add, are Frobenius-semilinear, multiply under
the wedge product, and are compatible with localization `L → L'`.

Let `B → L` be a ring map and `uⱼ ∈ B` with unit images in `L`. Suppose that every maximal ideal
of `B` avoids some `f` such that on the localization `L_f = L[1/f]` the logarithmic forms (the
`B`-combinations of wedges of `db` and `dlog uⱼ`) satisfy the logarithmic inverse Cartier theorem
up to powers of `f`: logarithmic forms have logarithmic representatives, a logarithmic closed form
which is exact is the differential of a logarithmic form, `C⁻¹` is injective, and every closed
logarithmic form represents `C⁻¹` of a logarithmic form. Then the same holds on `L` itself, and
the logarithmic inverse Cartier map of `L` is an isomorphism onto the cohomology of the
logarithmic de Rham complex (`MMP.DeRham.exists_logInverseCartier_of_forall_isMaximal`). The proof
is the usual partition of unity argument: for each statement the elements `b ∈ B` for which it
holds after multiplying by `b` (or by `b^p`) form an ideal containing a power of every `f ∈ S`.

## Main definitions

* `MMP.DeRham.IsInvCartierRep`: `x` is a closed form whose class is `C⁻¹ ω`.
* `MMP.DeRham.IsLocalLogCartier`: the logarithmic inverse Cartier theorem on `L[1/f]`, up to
  powers of `f`.

## Main results

* `MMP.DeRham.IsInvCartierRep.wedge`: representatives multiply.
* `MMP.DeRham.IsInvCartierRep.map`: representatives localize.
* `MMP.DeRham.exists_logInverseCartier_of_forall_isMaximal`: **the logarithmic inverse Cartier
  isomorphism, glued from a cover**.
* `MMP.DeRham.isLocalLogCartier_of_coordinates`: the local hypothesis from Frobenius coordinates
  and a coordinate basis of the differentials.

## References

* [P. Deligne, L. Illusie, *Relèvements modulo p² et décomposition du complexe de de Rham*,
  Invent. Math. 89 (1987)][DeligneIllusie1987], §4.
-/

@[expose] public noncomputable section

open KaehlerDifferential KaehlerDifferential.Cartier exteriorPower

universe u

namespace MMP.DeRham

/-! ### Representatives of the inverse Cartier map -/

section Rep

variable (p : ℕ) [Fact p.Prime] {A L : Type u} [CommRing A] [CommRing L] [Algebra A L]
  [CharP L p]

/-- `x` represents `C⁻¹ ω`: the form `x` is closed and its class in the cohomology of the
Frobenius-twisted de Rham complex is the inverse Cartier image of `ω`. -/
def IsInvCartierRep (i : ℕ) (ω x : ⋀[L]^i (Ω[L⁄A])) : Prop :=
  ∃ z : closedForms p A L i, (z : twistedForms p A L i) = twist p x ∧
    cohomologyMk p A L i z = inverseCartier p A L i ω

variable {p}

/-- The twist of `x` is exact if and only if `x` is zero or the differential of a form. -/
theorem twist_mem_exactForms_iff {n : ℕ} (x : ⋀[L]^n (Ω[L⁄A])) :
    twist p x ∈ exactForms p A L n ↔ (x : ExteriorAlgebra L (Ω[L⁄A])) = 0 ∨
      ∃ (k : ℕ) (w : ⋀[L]^k (Ω[L⁄A])), k + 1 = n ∧
        ((deRhamDifferential (A := A) k w : ⋀[L]^(k + 1) (Ω[L⁄A])) :
          ExteriorAlgebra L (Ω[L⁄A])) = x := by
  cases n with
  | zero =>
    rw [twist_mem_exactForms_zero, ← Submodule.coe_eq_zero (x := x)]
    exact ⟨Or.inl, fun h ↦ h.elim id fun ⟨k, _, hk, _⟩ ↦ absurd hk (Nat.succ_ne_zero k)⟩
  | succ n =>
    rw [twist_mem_exactForms_succ]
    constructor
    · rintro ⟨y, rfl⟩
      exact Or.inr ⟨n, y, rfl, rfl⟩
    · rintro (h | ⟨k, w, hk, h⟩)
      · refine ⟨0, ?_⟩
        rw [map_zero]
        exact (Subtype.coe_injective
          (h.trans (Submodule.coe_zero (p := ⋀[L]^(n+1) (Ω[L⁄A]))).symm)).symm
      · obtain rfl : k = n := by omega
        exact ⟨w, Subtype.coe_injective h⟩

namespace IsInvCartierRep

variable {i : ℕ} {ω η x y : ⋀[L]^i (Ω[L⁄A])}

/-- The twist of a representative is a closed form. -/
theorem twist_mem (h : IsInvCartierRep p i ω x) : twist p x ∈ closedForms p A L i := by
  obtain ⟨z, hz, -⟩ := h
  exact hz ▸ z.2

/-- A representative is closed: its de Rham differential vanishes. -/
theorem deRhamDifferential_eq_zero (h : IsInvCartierRep p i ω x) :
    deRhamDifferential (A := A) i x = 0 :=
  (twist_mem_closedForms x).1 h.twist_mem

/-- Representatives add: `x + y` represents `C⁻¹ (ω + η)`. -/
theorem add (h₁ : IsInvCartierRep p i ω x) (h₂ : IsInvCartierRep p i η y) :
    IsInvCartierRep p i (ω + η) (x + y) := by
  obtain ⟨z, hz, ez⟩ := h₁
  obtain ⟨w, hw, ew⟩ := h₂
  exact ⟨z + w, by rw [Submodule.coe_add, hz, hw, map_add], by rw [map_add, map_add, ez, ew]⟩

/-- `-x` represents `C⁻¹ (-ω)`. -/
theorem neg (h : IsInvCartierRep p i ω x) : IsInvCartierRep p i (-ω) (-x) := by
  obtain ⟨z, hz, ez⟩ := h
  exact ⟨-z, by rw [Submodule.coe_neg, hz, map_neg], by rw [map_neg, map_neg, ez]⟩

/-- Representatives subtract: `x - y` represents `C⁻¹ (ω - η)`. -/
theorem sub (h₁ : IsInvCartierRep p i ω x) (h₂ : IsInvCartierRep p i η y) :
    IsInvCartierRep p i (ω - η) (x - y) := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg

/-- Representatives are Frobenius-semilinear: `c^p x` represents `C⁻¹ (c ω)`. -/
theorem smul (h : IsInvCartierRep p i ω x) (c : L) :
    IsInvCartierRep p i (c • ω) (c ^ p • x) := by
  obtain ⟨z, hz, ez⟩ := h
  exact ⟨c • z, by rw [Submodule.coe_smul, hz, smul_twist], by rw [map_smul, map_smul, ez]⟩

/-- `0` represents `C⁻¹ 0`. -/
theorem zero : IsInvCartierRep p (A := A) (L := L) i 0 0 :=
  ⟨0, by rw [Submodule.coe_zero, map_zero], by rw [map_zero, map_zero]⟩

/-- Two representatives of the same class differ by an exact form. -/
theorem sub_mem_exactForms (h₁ : IsInvCartierRep p i ω x) (h₂ : IsInvCartierRep p i ω y) :
    twist p (y - x) ∈ exactForms p A L i := by
  obtain ⟨z, hz, ez⟩ := h₁
  obtain ⟨w, hw, ew⟩ := h₂
  have := (cohomologyMk_eq_iff _ _).1 (ew.trans ez.symm)
  rwa [hz, hw, ← map_sub] at this

/-- Changing a representative by an exact form gives a representative. -/
theorem of_sub_mem_exactForms (h : IsInvCartierRep p i ω x)
    (hd : twist p (y - x) ∈ exactForms p A L i) : IsInvCartierRep p i ω y := by
  obtain ⟨z, hz, ez⟩ := h
  let e : closedForms p A L i := ⟨twist p (y - x), exactForms_le_closedForms p A L i hd⟩
  refine ⟨z + e, ?_, ?_⟩
  · rw [Submodule.coe_add, hz]
    change twist p x + twist p (y - x) = twist p y
    rw [map_sub, add_sub_cancel]
  · rw [map_add, ez, (cohomologyMk_eq_zero_iff e).2 hd, add_zero]

/-- `x` represents `C⁻¹ 0` if and only if the twist of `x` is exact. -/
theorem _root_.MMP.DeRham.isInvCartierRep_zero_iff :
    IsInvCartierRep p i 0 x ↔ twist p x ∈ exactForms p A L i :=
  ⟨fun h ↦ by simpa using (zero (p := p)).sub_mem_exactForms h,
    fun h ↦ (zero (p := p)).of_sub_mem_exactForms (by rwa [sub_zero])⟩

end IsInvCartierRep

/-- Every form `ω` has a representative of `C⁻¹ ω`. -/
theorem exists_isInvCartierRep (i : ℕ) (ω : ⋀[L]^i (Ω[L⁄A])) :
    ∃ x, IsInvCartierRep p i ω x := by
  obtain ⟨z, hz⟩ := cohomologyMk_surjective p A L i (inverseCartier p A L i ω)
  exact ⟨(twist p).symm z, z, (AddEquiv.apply_symm_apply _ _).symm, hz⟩

/-- `b₁^{p-1} db₁ ∧ ⋯ ∧ b_i^{p-1} db_i` represents `C⁻¹ (db₁ ∧ ⋯ ∧ db_i)`. -/
theorem isInvCartierRep_ιMulti_D {i : ℕ} (g : Fin i → L) :
    IsInvCartierRep p i (ιMulti L i fun k ↦ D A L (g k))
      (ιMulti L i fun k ↦ g k ^ (p - 1) • D A L (g k)) :=
  ⟨_, coe_wedgeClosed_cartierForm p (A := A) g, (inverseCartier_ιMulti_D p g).symm⟩

/-- In degree `0` a representative is unique. -/
theorem IsInvCartierRep.eq_of_zero {ω x y : ⋀[L]^0 (Ω[L⁄A])} (h₁ : IsInvCartierRep p 0 ω x)
    (h₂ : IsInvCartierRep p 0 ω y) : x = y :=
  (sub_eq_zero.1 ((twist_mem_exactForms_zero _).1 (h₁.sub_mem_exactForms h₂))).symm

/-! #### Wedge products of representatives -/

section Wedge

variable {i j : ℕ}

/-- A closed form wedged with an exact form is exact. -/
theorem twist_wedgeMul_mem_exactForms_of_right {x : ⋀[L]^i (Ω[L⁄A])} {y : ⋀[L]^j (Ω[L⁄A])}
    (hx : deRhamDifferential (A := A) i x = 0) (hy : twist p y ∈ exactForms p A L j) :
    twist p (wedgeMul i j x y) ∈ exactForms p A L (i + j) := by
  rw [twist_mem_exactForms_iff] at hy ⊢
  rcases hy with hy | ⟨k, w, rfl, hw⟩
  · left; rw [wedgeMul_apply_coe, hy, mul_zero]
  · right
    have hd := coe_deRhamDifferential_wedgeMul (A := A) i k x w
    rw [hx, Submodule.coe_zero, zero_mul, zero_add, hw] at hd
    rcases neg_one_pow_eq_or (ExteriorAlgebra L (Ω[L⁄A])) i with he | he
    · refine ⟨i + k, wedgeMul i k x w, by omega, ?_⟩
      rw [hd, he, one_mul, wedgeMul_apply_coe]
    · refine ⟨i + k, -wedgeMul i k x w, by omega, ?_⟩
      rw [map_neg, Submodule.coe_neg, hd, he, neg_one_mul, neg_neg, wedgeMul_apply_coe]

/-- An exact form wedged with a closed form is exact. -/
theorem twist_wedgeMul_mem_exactForms_of_left {x : ⋀[L]^i (Ω[L⁄A])} {y : ⋀[L]^j (Ω[L⁄A])}
    (hx : twist p x ∈ exactForms p A L i) (hy : deRhamDifferential (A := A) j y = 0) :
    twist p (wedgeMul i j x y) ∈ exactForms p A L (i + j) := by
  rw [twist_mem_exactForms_iff] at hx ⊢
  rcases hx with hx | ⟨k, w, rfl, hw⟩
  · left; rw [wedgeMul_apply_coe, hx, zero_mul]
  · right
    have hd := coe_deRhamDifferential_wedgeMul (A := A) k j w y
    rw [hy, Submodule.coe_zero, mul_zero, mul_zero, add_zero, hw] at hd
    exact ⟨k + j, wedgeMul k j w y, by omega, by rw [hd, wedgeMul_apply_coe]⟩

/-- If some representatives of `C⁻¹ ω` and `C⁻¹ η` multiply to a representative of
`C⁻¹ (ω ∧ η)`, then all of them do. -/
theorem IsInvCartierRep.wedgeMul_of_exists {ω : ⋀[L]^i (Ω[L⁄A])} {η : ⋀[L]^j (Ω[L⁄A])}
    (h : ∃ x₀ y₀, IsInvCartierRep p i ω x₀ ∧ IsInvCartierRep p j η y₀ ∧
      IsInvCartierRep p (i + j) (wedgeMul i j ω η) (wedgeMul i j x₀ y₀))
    {x : ⋀[L]^i (Ω[L⁄A])} {y : ⋀[L]^j (Ω[L⁄A])} (hx : IsInvCartierRep p i ω x)
    (hy : IsInvCartierRep p j η y) :
    IsInvCartierRep p (i + j) (wedgeMul i j ω η) (wedgeMul i j x y) := by
  obtain ⟨x₀, y₀, hx₀, hy₀, h₀⟩ := h
  refine h₀.of_sub_mem_exactForms ?_
  have he : wedgeMul i j x y - wedgeMul i j x₀ y₀ =
      wedgeMul i j (x - x₀) y + wedgeMul i j x₀ (y - y₀) := by
    simp only [map_sub, LinearMap.sub_apply]; abel
  rw [he, map_add]
  exact add_mem
    (twist_wedgeMul_mem_exactForms_of_left (hx₀.sub_mem_exactForms hx)
      hy.deRhamDifferential_eq_zero)
    (twist_wedgeMul_mem_exactForms_of_right hx₀.deRhamDifferential_eq_zero
      (hy₀.sub_mem_exactForms hy))

/-- **Induction on forms**: a property of forms stable under sums and scalar multiples and
holding on the wedges `dg₁ ∧ ⋯ ∧ dg_i` holds for all forms. -/
theorem forms_induction {P : ⋀[L]^i (Ω[L⁄A]) → Prop} (h0 : P 0)
    (hadd : ∀ ω η, P ω → P η → P (ω + η)) (hsmul : ∀ (c : L) ω, P ω → P (c • ω))
    (hgen : ∀ g : Fin i → L, P (ιMulti L i fun k ↦ D A L (g k))) (ω : ⋀[L]^i (Ω[L⁄A])) :
    P ω := by
  have hω : ω ∈ Submodule.span A (Set.range fun c : Fin (i + 1) → L ↦
      c 0 • ιMulti L i fun k ↦ D A L (c k.succ)) := by
    rw [Crystalline.span_range_smul_ιMulti_eq_top (D A L) (span_range_derivation A L) i]
    exact Submodule.mem_top
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, rfl⟩ := hx
    exact hsmul _ _ (hgen _)
  | zero => exact h0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul a x _ hx => rw [← algebraMap_smul L a x]; exact hsmul _ _ hx

/-- The wedge of `φ(g₁) ∧ ⋯ ∧ φ(gᵢ)` and `φ(g'₁) ∧ ⋯ ∧ φ(g'ⱼ)` is the wedge of `φ` along
`Fin.append g g'`. -/
theorem wedgeMul_ιMulti_comp (φ : L → Ω[L⁄A]) (g : Fin i → L) (g' : Fin j → L) :
    wedgeMul i j (ιMulti L i fun k ↦ φ (g k)) (ιMulti L j fun k ↦ φ (g' k)) =
      ιMulti L (i + j) fun k ↦ φ (Fin.append g g' k) := by
  refine Subtype.ext ?_
  rw [wedgeMul_apply_coe, ιMulti_apply_coe, ιMulti_apply_coe, ιMulti_apply_coe,
    ExteriorAlgebra.ιMulti_mul_ιMulti]
  congr 1
  funext k
  refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) k <;> simp

/-- The wedge of the representatives of `C⁻¹ (dg₁ ∧ ⋯ ∧ dgᵢ)` and `C⁻¹ (dg'₁ ∧ ⋯ ∧ dg'ⱼ)` of
`isInvCartierRep_ιMulti_D` represents `C⁻¹` of the wedge. -/
theorem isInvCartierRep_wedgeMul_ιMulti_D (g : Fin i → L) (g' : Fin j → L) :
    IsInvCartierRep p (i + j)
      (wedgeMul i j (ιMulti L i fun k ↦ D A L (g k)) (ιMulti L j fun k ↦ D A L (g' k)))
      (wedgeMul i j (ιMulti L i fun k ↦ g k ^ (p - 1) • D A L (g k))
        (ιMulti L j fun k ↦ g' k ^ (p - 1) • D A L (g' k))) := by
  rw [wedgeMul_ιMulti_comp (D A L), wedgeMul_ιMulti_comp fun b ↦ b ^ (p - 1) • D A L b]
  exact isInvCartierRep_ιMulti_D _

/-- **Representatives multiply**: if `x` represents `C⁻¹ ω` and `y` represents `C⁻¹ η`, then
`x ∧ y` represents `C⁻¹ (ω ∧ η)`. -/
theorem IsInvCartierRep.wedge {ω : ⋀[L]^i (Ω[L⁄A])} {η : ⋀[L]^j (Ω[L⁄A])}
    {x : ⋀[L]^i (Ω[L⁄A])} {y : ⋀[L]^j (Ω[L⁄A])} (hx : IsInvCartierRep p i ω x)
    (hy : IsInvCartierRep p j η y) :
    IsInvCartierRep p (i + j) (wedgeMul i j ω η) (wedgeMul i j x y) := by
  let Q : ⋀[L]^i (Ω[L⁄A]) → ⋀[L]^j (Ω[L⁄A]) → Prop := fun ω η ↦
    ∀ x y, IsInvCartierRep p i ω x → IsInvCartierRep p j η y →
      IsInvCartierRep p (i + j) (wedgeMul i j ω η) (wedgeMul i j x y)
  have hex : ∀ ω η, (∃ x₀ y₀, IsInvCartierRep p i ω x₀ ∧ IsInvCartierRep p j η y₀ ∧
      IsInvCartierRep p (i + j) (wedgeMul i j ω η) (wedgeMul i j x₀ y₀)) → Q ω η :=
    fun ω η h x y hx hy ↦ IsInvCartierRep.wedgeMul_of_exists h hx hy
  have hleft : ∀ η, (∀ g : Fin i → L, Q (ιMulti L i fun k ↦ D A L (g k)) η) → ∀ ω, Q ω η := by
    intro η hg
    refine forms_induction ?_ ?_ ?_ hg
    · obtain ⟨y₀, hy₀⟩ := exists_isInvCartierRep (p := p) j η
      refine hex _ _ ⟨0, y₀, IsInvCartierRep.zero, hy₀, ?_⟩
      simpa only [map_zero, LinearMap.zero_apply] using IsInvCartierRep.zero
    · intro ω₁ ω₂ h₁ h₂
      obtain ⟨x₁, hx₁⟩ := exists_isInvCartierRep (p := p) i ω₁
      obtain ⟨x₂, hx₂⟩ := exists_isInvCartierRep (p := p) i ω₂
      obtain ⟨y₀, hy₀⟩ := exists_isInvCartierRep (p := p) j η
      refine hex _ _ ⟨x₁ + x₂, y₀, hx₁.add hx₂, hy₀, ?_⟩
      simpa only [map_add, LinearMap.add_apply] using (h₁ _ _ hx₁ hy₀).add (h₂ _ _ hx₂ hy₀)
    · intro c ω₁ h₁
      obtain ⟨x₁, hx₁⟩ := exists_isInvCartierRep (p := p) i ω₁
      obtain ⟨y₀, hy₀⟩ := exists_isInvCartierRep (p := p) j η
      refine hex _ _ ⟨c ^ p • x₁, y₀, hx₁.smul c, hy₀, ?_⟩
      simpa only [map_smul, LinearMap.smul_apply] using (h₁ _ _ hx₁ hy₀).smul c
  have hright : ∀ g : Fin i → L, ∀ η, Q (ιMulti L i fun k ↦ D A L (g k)) η := by
    intro g
    refine forms_induction ?_ ?_ ?_ ?_
    · obtain ⟨x₀, hx₀⟩ := exists_isInvCartierRep (p := p) i (ιMulti L i fun k ↦ D A L (g k))
      refine hex _ _ ⟨x₀, 0, hx₀, IsInvCartierRep.zero, ?_⟩
      simpa only [map_zero] using IsInvCartierRep.zero
    · intro η₁ η₂ h₁ h₂
      obtain ⟨x₀, hx₀⟩ := exists_isInvCartierRep (p := p) i (ιMulti L i fun k ↦ D A L (g k))
      obtain ⟨y₁, hy₁⟩ := exists_isInvCartierRep (p := p) j η₁
      obtain ⟨y₂, hy₂⟩ := exists_isInvCartierRep (p := p) j η₂
      refine hex _ _ ⟨x₀, y₁ + y₂, hx₀, hy₁.add hy₂, ?_⟩
      simpa only [map_add] using (h₁ _ _ hx₀ hy₁).add (h₂ _ _ hx₀ hy₂)
    · intro c η₁ h₁
      obtain ⟨x₀, hx₀⟩ := exists_isInvCartierRep (p := p) i (ιMulti L i fun k ↦ D A L (g k))
      obtain ⟨y₁, hy₁⟩ := exists_isInvCartierRep (p := p) j η₁
      refine hex _ _ ⟨x₀, c ^ p • y₁, hx₀, hy₁.smul c, ?_⟩
      simpa only [map_smul] using (h₁ _ _ hx₀ hy₁).smul c
    · exact fun g' ↦ hex _ _ ⟨_, _, isInvCartierRep_ιMulti_D g, isInvCartierRep_ιMulti_D g',
        isInvCartierRep_wedgeMul_ιMulti_D g g'⟩
  exact hleft η (fun g ↦ hright g η) ω x y hx hy

end Wedge

end Rep

/-! ### Localization -/

section Localization

variable {p : ℕ} [Fact p.Prime] {A L L' : Type u} [CommRing A] [CommRing L] [CommRing L']
  [Algebra A L] [Algebra A L'] [Algebra L L'] [IsScalarTower A L L']

/-- The image under `mapExteriorPower A L L' i` of a form whose twist is exact has exact
twist. -/
theorem twist_mapExteriorPower_mem_exactForms [CharP L p] [CharP L' p] {i : ℕ}
    {y : ⋀[L]^i (Ω[L⁄A])} (hy : twist p y ∈ exactForms p A L i) :
    twist p (mapExteriorPower A L L' i y) ∈ exactForms p A L' i := by
  cases i with
  | zero =>
    rw [twist_mem_exactForms_zero] at hy ⊢
    rw [hy, map_zero]
  | succ i =>
    obtain ⟨w, rfl⟩ := (twist_mem_exactForms_succ y).1 hy
    exact (twist_mem_exactForms_succ _).2
      ⟨_, (mapExteriorPower_deRhamDifferential A L L' i w).symm⟩

/-- `mapExteriorPower A L L' i` is semilinear along `algebraMap L L'`. -/
theorem mapExteriorPower_smul {i : ℕ} (c : L) (y : ⋀[L]^i (Ω[L⁄A])) :
    mapExteriorPower A L L' i (c • y) = algebraMap L L' c • mapExteriorPower A L L' i y := by
  rw [map_smul, algebraMap_smul]

/-- The image of `(c db₁) ∧ ⋯ ∧ (c dbᵢ)` under `mapExteriorPower A L L' i` is the
corresponding wedge of the images of `c` and `bₖ` in `L'`. -/
theorem mapExteriorPower_ιMulti_D {i : ℕ} (c : L) (g : Fin i → L) :
    mapExteriorPower A L L' i (ιMulti L i fun k ↦ c • D A L (g k)) =
      ιMulti L' i fun k ↦ algebraMap L L' c • D A L' (algebraMap L L' (g k)) := by
  rw [mapExteriorPower_ιMulti]
  congr 1
  funext k
  rw [map_smul, map_D, algebraMap_smul]

/-- **Representatives localize**: if `x` represents `C⁻¹ ω` on `L`, then the image of `x`
represents `C⁻¹` of the image of `ω` on any `L`-algebra `L'`. -/
theorem IsInvCartierRep.map [CharP L p] [CharP L' p] {i : ℕ} {ω x : ⋀[L]^i (Ω[L⁄A])}
    (h : IsInvCartierRep p i ω x) :
    IsInvCartierRep p i (mapExteriorPower A L L' i ω) (mapExteriorPower A L L' i x) := by
  let Q : ⋀[L]^i (Ω[L⁄A]) → Prop := fun ω ↦ ∀ x, IsInvCartierRep p i ω x →
    IsInvCartierRep p i (mapExteriorPower A L L' i ω) (mapExteriorPower A L L' i x)
  have hex : ∀ ω, (∃ x₀, IsInvCartierRep p i ω x₀ ∧
      IsInvCartierRep p i (mapExteriorPower A L L' i ω) (mapExteriorPower A L L' i x₀)) →
      Q ω := by
    rintro ω ⟨x₀, hx₀, h₀⟩ x hx
    refine h₀.of_sub_mem_exactForms ?_
    rw [← map_sub]
    exact twist_mapExteriorPower_mem_exactForms (hx₀.sub_mem_exactForms hx)
  refine forms_induction (P := Q) ?_ ?_ ?_ ?_ ω x h
  · refine hex _ ⟨0, IsInvCartierRep.zero, ?_⟩
    rw [map_zero]
    exact IsInvCartierRep.zero
  · intro ω₁ ω₂ h₁ h₂
    obtain ⟨x₁, hx₁⟩ := exists_isInvCartierRep (p := p) i ω₁
    obtain ⟨x₂, hx₂⟩ := exists_isInvCartierRep (p := p) i ω₂
    refine hex _ ⟨x₁ + x₂, hx₁.add hx₂, ?_⟩
    rw [map_add, map_add]
    exact (h₁ _ hx₁).add (h₂ _ hx₂)
  · intro c ω₁ h₁
    obtain ⟨x₁, hx₁⟩ := exists_isInvCartierRep (p := p) i ω₁
    refine hex _ ⟨c ^ p • x₁, hx₁.smul c, ?_⟩
    rw [mapExteriorPower_smul, mapExteriorPower_smul, map_pow]
    exact (h₁ _ hx₁).smul _
  · intro g
    refine hex _ ⟨_, isInvCartierRep_ιMulti_D g, ?_⟩
    have e₁ := mapExteriorPower_ιMulti_D (A := A) (L' := L') (1 : L) g
    simp only [one_smul, map_one] at e₁
    have e₃ : mapExteriorPower A L L' i (ιMulti L i fun k ↦ g k ^ (p - 1) • D A L (g k)) =
        ιMulti L' i fun k ↦ algebraMap L L' (g k) ^ (p - 1) • D A L' (algebraMap L L' (g k)) := by
      rw [mapExteriorPower_ιMulti]
      congr 1
      funext k
      rw [map_smul, map_D, ← map_pow, algebraMap_smul]
    rw [e₁, e₃]
    exact isInvCartierRep_ιMulti_D _

/-- **The kernel of localization**: a form of `L` vanishing on `L' = L[1/f]` is killed by a
power of `f`. -/
theorem exists_pow_smul_eq_zero_of_mapExteriorPower_eq_zero (f : L) [IsLocalization.Away f L']
    {i : ℕ} {y : ⋀[L]^i (Ω[L⁄A])} (hy : mapExteriorPower A L L' i y = 0) :
    ∃ N : ℕ, f ^ N • y = 0 := by
  have : IsLocalizedModule (Submonoid.powers f) (mapExteriorPower A L L' i) :=
    IsLocalization.isLocalizedModule_of_exteriorPower L' (KaehlerDifferential.map A A L L') i
      (Submonoid.powers f) _ (mapExteriorPower_ιMulti A L L' i)
  obtain ⟨⟨_, N, rfl⟩, hN⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f)
    (f := mapExteriorPower A L L' i) (hy.trans (map_zero _).symm)
  rw [smul_zero, Submonoid.smul_def] at hN
  exact ⟨N, hN⟩

end Localization

/-! ### Logarithmic forms under localization -/

section LogLocal

variable {A L L' B B' : Type u} [CommRing A] [CommRing L] [CommRing L'] [CommRing B]
  [CommRing B'] [Algebra A L] [Algebra A L'] [Algebra L L'] [IsScalarTower A L L']
  [Algebra B L] [Algebra B L'] [IsScalarTower B L L'] [Algebra B B'] [Algebra B' L']
  [IsScalarTower B B' L'] {ι : Type*}

/-- A ring homomorphism commutes with `Ring.inverse` on units. -/
theorem map_ringInverse_of_isUnit {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) {x : R}
    (hx : IsUnit x) : g (Ring.inverse x) = Ring.inverse (g x) := by
  obtain ⟨v, rfl⟩ := hx
  rw [Ring.inverse_unit, show g ↑v = ↑(Units.map g.toMonoidHom v) from rfl, Ring.inverse_unit]
  rfl

omit [Algebra B L'] [IsScalarTower B L L'] [Algebra B B'] [Algebra B' L']
  [IsScalarTower B B' L'] in
/-- The image of `dlog x` is `dlog` of the image of `x`. -/
theorem map_dlog {x : L} (hx : IsUnit x) :
    KaehlerDifferential.map A A L L' (Ring.inverse x • D A L x) =
      Ring.inverse (algebraMap L L' x) • D A L' (algebraMap L L' x) := by
  rw [map_smul, map_D, ← algebraMap_smul L', map_ringInverse_of_isUnit _ hx]

omit [Algebra B L'] [IsScalarTower B L L'] [Algebra B B'] [Algebra B' L']
  [IsScalarTower B B' L'] in
/-- **Logarithmic forms are multilinear**: a wedge of `B`-combinations of the generators `db`
and `dlog uⱼ` is a logarithmic form. -/
theorem ιMulti_mem_logForms_of_mem_span {u : ι → B} {i : ℕ} (w : Fin i → Ω[L⁄A])
    (hw : ∀ m, w m ∈ Submodule.span B (logGenerators A L u)) :
    ExteriorAlgebra.ιMulti L i w ∈ logForms A L u i := by
  classical
  suffices key : ∀ s : Finset (Fin i), ∀ w : Fin i → Ω[L⁄A],
      (∀ m, w m ∈ Submodule.span B (logGenerators A L u)) →
      (∀ m ∉ s, w m ∈ logGenerators A L u) → ExteriorAlgebra.ιMulti L i w ∈ logForms A L u i from
    key Finset.univ w hw (fun m hm ↦ absurd (Finset.mem_univ m) hm)
  intro s
  induction s using Finset.induction_on with
  | empty => exact fun w _ hw ↦ ιMulti_mem_logForms w fun m ↦ hw m (Finset.notMem_empty m)
  | insert a s ha ih =>
    intro w hspan hw
    have hupd : ∀ x ∈ Submodule.span B (logGenerators A L u),
        ExteriorAlgebra.ιMulti L i (Function.update w a x) ∈ logForms A L u i := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        refine ih _ (fun m ↦ ?_) (fun m hm ↦ ?_)
        · by_cases h : m = a
          · subst h; rw [Function.update_self]; exact Submodule.subset_span hx
          · rw [Function.update_of_ne h]; exact hspan m
        · by_cases h : m = a
          · subst h; rw [Function.update_self]; exact hx
          · rw [Function.update_of_ne h]
            exact hw m (by simp [h, hm])
      | zero => rw [AlternatingMap.map_update_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [AlternatingMap.map_update_add]; exact add_mem hx hy
      | smul b x _ hx =>
        rw [← algebraMap_smul L b x, AlternatingMap.map_update_smul, algebraMap_smul]
        exact Submodule.smul_mem _ b hx
    simpa using hupd (w a) (hspan a)

variable (u : ι → B)

/-- `mapExteriorPower A L L' i (b • y)` is `algebraMap B B' b • mapExteriorPower A L L' i y` in the
exterior algebra, for `b ∈ B`. -/
theorem mapExteriorPower_algebraMap_smul {i : ℕ} (b : B) (y : ⋀[L]^i (Ω[L⁄A])) :
    ((mapExteriorPower A L L' i (b • y) : ⋀[L']^i (Ω[L'⁄A])) : ExteriorAlgebra L' (Ω[L'⁄A])) =
      algebraMap B B' b • ((mapExteriorPower A L L' i y : ⋀[L']^i (Ω[L'⁄A])) :
        ExteriorAlgebra L' (Ω[L'⁄A])) := by
  rw [← algebraMap_smul L b y, mapExteriorPower_smul, ← IsScalarTower.algebraMap_apply B L L' b,
    Submodule.coe_smul, ← algebraMap_smul L' (algebraMap B B' b) (_ : ExteriorAlgebra L' _),
    ← IsScalarTower.algebraMap_apply B B' L' b]

/-- **Logarithmic forms localize**: the image on `L'` of a logarithmic form of `B` is a
logarithmic form of `B'`. -/
theorem coe_mapExteriorPower_mem_logForms (hu : ∀ j, IsUnit (algebraMap B L (u j))) {i : ℕ}
    (y : ⋀[L]^i (Ω[L⁄A])) (hy : (y : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i) :
    ((mapExteriorPower A L L' i y : ⋀[L']^i (Ω[L'⁄A])) : ExteriorAlgebra L' (Ω[L'⁄A])) ∈
      logForms A L' (fun j ↦ algebraMap B B' (u j)) i := by
  let S : Submodule B (⋀[L]^i (Ω[L⁄A])) :=
    { carrier := {y | ((mapExteriorPower A L L' i y : ⋀[L']^i (Ω[L'⁄A])) :
        ExteriorAlgebra L' (Ω[L'⁄A])) ∈ logForms A L' (fun j ↦ algebraMap B B' (u j)) i}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        simp only [Set.mem_ofPred_eq, map_add, Submodule.coe_add] at hx hy ⊢
        exact add_mem hx hy
      smul_mem' := by
        intro b y hy
        simp only [Set.mem_ofPred_eq] at hy ⊢
        rw [mapExteriorPower_algebraMap_smul (B' := B')]
        exact Submodule.smul_mem _ _ hy }
  refine mem_of_mem_logForms S (fun v hv ↦ ?_) y hy
  change ((mapExteriorPower A L L' i (ιMulti L i v) : ⋀[L']^i (Ω[L'⁄A])) :
    ExteriorAlgebra L' (Ω[L'⁄A])) ∈ logForms A L' (fun j ↦ algebraMap B B' (u j)) i
  rw [mapExteriorPower_ιMulti, ιMulti_apply_coe]
  refine ιMulti_mem_logForms _ fun m ↦ ?_
  rcases hv m with ⟨b, hb⟩ | ⟨j, hj⟩
  · rw [← hb, map_D, ← IsScalarTower.algebraMap_apply B L L' b,
      IsScalarTower.algebraMap_apply B B' L' b]
    exact D_mem_logGenerators _ _
  · rw [← hj, map_dlog (hu j), ← IsScalarTower.algebraMap_apply B L L' (u j),
      IsScalarTower.algebraMap_apply B B' L' (u j)]
    exact dlog_mem_logGenerators _ j

/-- `KaehlerDifferential.map A A L L'` sends `b • w` to `b • KaehlerDifferential.map A A L L' w`
for `b ∈ B`. -/
theorem map_algebraMap_smul (b : B) (w : Ω[L⁄A]) :
    KaehlerDifferential.map A A L L' (algebraMap B L b • w) =
      algebraMap B L' b • KaehlerDifferential.map A A L L' w := by
  rw [map_smul, ← algebraMap_smul L', ← IsScalarTower.algebraMap_apply]

/-- **Clearing denominators in `dc`**: for `c ∈ B' = B[1/f]`, some `f^n dc` is the image of a
`B`-combination of differentials `db`. -/
theorem exists_map_eq_pow_smul_D (f : B) [IsLocalization.Away f B'] (c : B') :
    ∃ (n : ℕ) (w : Ω[L⁄A]), w ∈ Submodule.span B (logGenerators A L u) ∧
      KaehlerDifferential.map A A L L' w =
        algebraMap B L' f ^ n • D A L' (algebraMap B' L' c) := by
  obtain ⟨n, a, h⟩ := IsLocalization.Away.surj f c
  have hC : algebraMap B' L' c * algebraMap B L' f ^ n = algebraMap B L' a := by
    have := congrArg (algebraMap B' L') h
    rwa [map_mul, map_pow, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply] at this
  have hgen : ∀ b : B, D A L (algebraMap B L b) ∈ Submodule.span B (logGenerators A L u) :=
    fun b ↦ Submodule.subset_span (D_mem_logGenerators u b)
  have hmapD : ∀ b : B, KaehlerDifferential.map A A L L' (D A L (algebraMap B L b)) =
      D A L' (algebraMap B L' b) := fun b ↦ by
    rw [map_D, ← IsScalarTower.algebraMap_apply]
  cases n with
  | zero =>
    refine ⟨0, D A L (algebraMap B L a), hgen a, ?_⟩
    rw [pow_zero, one_smul, hmapD, ← hC, pow_zero, mul_one]
  | succ m =>
    refine ⟨2 * m + 3, algebraMap B L (f ^ (m + 2)) • D A L (algebraMap B L a) -
      algebraMap B L (a * f ^ (m + 1)) • ((m + 1) • D A L (algebraMap B L f)), ?_, ?_⟩
    · refine sub_mem ?_ ?_
      · rw [algebraMap_smul]; exact Submodule.smul_mem _ _ (hgen a)
      · rw [algebraMap_smul]
        exact Submodule.smul_mem _ _ (Submodule.smul_of_tower_mem _ _ (hgen f))
    · rw [map_sub, map_algebraMap_smul, map_algebraMap_smul, map_nsmul, hmapD, hmapD, map_mul,
        map_pow, map_pow, ← hC, Derivation.leibniz, Derivation.leibniz_pow, Nat.add_sub_cancel]
      set F := algebraMap B L' f
      set C := algebraMap B' L' c
      module

/-- **Clearing denominators in logarithmic forms**: for a logarithmic form `y'` of
`B' = B[1/f]` on `L'`, some `f^N y'` is the image of a logarithmic form of `B` on `L`. -/
theorem exists_mapExteriorPower_eq_pow_smul (f : B) [IsLocalization.Away f B']
    (hu : ∀ j, IsUnit (algebraMap B L (u j))) {i : ℕ} (y' : ⋀[L']^i (Ω[L'⁄A]))
    (hy' : (y' : ExteriorAlgebra L' (Ω[L'⁄A])) ∈ logForms A L' (fun j ↦ algebraMap B B' (u j)) i) :
    ∃ (N : ℕ) (y : ⋀[L]^i (Ω[L⁄A])), (y : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i ∧
      mapExteriorPower A L L' i y = algebraMap B L' f ^ N • y' := by
  set F := algebraMap B L' f
  let S : Submodule B' (⋀[L']^i (Ω[L'⁄A])) :=
    { carrier := {y' | ∃ (N : ℕ) (y : ⋀[L]^i (Ω[L⁄A])),
        (y : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i ∧
        mapExteriorPower A L L' i y = F ^ N • y'}
      zero_mem' := ⟨0, 0, zero_mem _, by rw [map_zero, smul_zero]⟩
      add_mem' := by
        rintro y₁ y₂ ⟨N₁, x₁, hx₁, e₁⟩ ⟨N₂, x₂, hx₂, e₂⟩
        refine ⟨N₁ + N₂, algebraMap B L (f ^ N₂) • x₁ + algebraMap B L (f ^ N₁) • x₂, ?_, ?_⟩
        · rw [algebraMap_smul, algebraMap_smul, Submodule.coe_add]
          exact add_mem (Submodule.smul_mem _ _ hx₁) (Submodule.smul_mem _ _ hx₂)
        · rw [map_add, mapExteriorPower_smul, mapExteriorPower_smul, e₁, e₂,
            ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, map_pow,
            map_pow, smul_smul, smul_smul, ← pow_add, ← pow_add, smul_add, add_comm N₂ N₁]
      smul_mem' := by
        rintro c y' ⟨N, x, hx, e⟩
        obtain ⟨n, a, h⟩ := IsLocalization.Away.surj f c
        have hC : algebraMap B' L' c * F ^ n = algebraMap B L' a := by
          have := congrArg (algebraMap B' L') h
          rwa [map_mul, map_pow, ← IsScalarTower.algebraMap_apply,
            ← IsScalarTower.algebraMap_apply] at this
        refine ⟨N + n, algebraMap B L a • x, ?_, ?_⟩
        · rw [algebraMap_smul]; exact Submodule.smul_mem _ _ hx
        · rw [mapExteriorPower_smul, e, ← IsScalarTower.algebraMap_apply, ← hC,
            ← algebraMap_smul L' c y', smul_smul, smul_smul, pow_add]
          congr 1
          ring }
  refine mem_of_mem_logForms S (fun v hv ↦ ?_) y' hy'
  have hgen : ∀ m, ∃ (n : ℕ) (w : Ω[L⁄A]), w ∈ Submodule.span B (logGenerators A L u) ∧
      KaehlerDifferential.map A A L L' w = F ^ n • v m := by
    intro m
    rcases hv m with ⟨c, hc⟩ | ⟨j, hj⟩
    · rw [← hc]; exact exists_map_eq_pow_smul_D u f c
    · refine ⟨0, _, Submodule.subset_span (dlog_mem_logGenerators u j), ?_⟩
      rw [pow_zero, one_smul, ← hj, map_dlog (hu j), ← IsScalarTower.algebraMap_apply B L L',
        IsScalarTower.algebraMap_apply B B' L']
  choose n w hw e using hgen
  refine ⟨∑ m, n m, ιMulti L i w, ?_, ?_⟩
  · rw [ιMulti_apply_coe]
    exact ιMulti_mem_logForms_of_mem_span w hw
  · rw [mapExteriorPower_ιMulti]
    simp only [e]
    rw [AlternatingMap.map_smul_univ, Finset.prod_pow_eq_pow_sum]

end LogLocal

/-! ### The local hypothesis -/

/-- **The logarithmic inverse Cartier theorem on `L'`, up to powers of `f`**: logarithmic forms
have logarithmic representatives up to a power of `f`; a logarithmic form which is exact is,
up to a power of `f^p`, the differential of a logarithmic form; the inverse Cartier map is
injective; and a closed logarithmic form represents, up to a power of `f^p`, the inverse Cartier
image of a logarithmic form. -/
structure IsLocalLogCartier (p : ℕ) [Fact p.Prime] (A : Type u) {B : Type u} (L' : Type u)
    [CommRing A] [CommRing B] [CommRing L'] [Algebra A L'] [Algebra B L'] [CharP L' p]
    {ι : Type*} (u : ι → B) (f : B) : Prop where
  /-- Some `f ^ M • y` of a logarithmic form `y` has a logarithmic representative. -/
  exists_rep : ∀ (i : ℕ) (y : ⋀[L']^i (Ω[L'⁄A])),
    (y : ExteriorAlgebra L' (Ω[L'⁄A])) ∈ logForms A L' u i → ∃ (M : ℕ) (x : ⋀[L']^i (Ω[L'⁄A])),
      (x : ExteriorAlgebra L' (Ω[L'⁄A])) ∈ logForms A L' u i ∧
      IsInvCartierRep p i (algebraMap B L' f ^ M • y) x
  /-- A logarithmic representative of `C⁻¹ 0` is, up to a power of `f ^ p`, the differential of a
  logarithmic form. -/
  mem_exactLogForms : ∀ (i : ℕ) (x : ⋀[L']^i (Ω[L'⁄A])),
    (x : ExteriorAlgebra L' (Ω[L'⁄A])) ∈ logForms A L' u i → IsInvCartierRep p i 0 x →
      ∃ M : ℕ, (((algebraMap B L' f ^ M) ^ p • x : ⋀[L']^i (Ω[L'⁄A])) :
        ExteriorAlgebra L' (Ω[L'⁄A])) ∈ exactLogForms A L' u i
  /-- The inverse Cartier map is injective. -/
  eq_zero : ∀ (i : ℕ) (y : ⋀[L']^i (Ω[L'⁄A])), IsInvCartierRep p i y 0 → y = 0
  /-- For a closed logarithmic form `x`, some `(f ^ M) ^ p • x` represents `C⁻¹` of a
  logarithmic form. -/
  exists_rep_of_closed : ∀ (i : ℕ) (x : ⋀[L']^i (Ω[L'⁄A])),
    (x : ExteriorAlgebra L' (Ω[L'⁄A])) ∈ logForms A L' u i → deRhamDifferential (A := A) i x = 0 →
      ∃ (M : ℕ) (W : ⋀[L']^i (Ω[L'⁄A])), (W : ExteriorAlgebra L' (Ω[L'⁄A])) ∈ logForms A L' u i ∧
        IsInvCartierRep p i W ((algebraMap B L' f ^ M) ^ p • x)

/-! ### From `L[1/f]` back to `L` -/

section Descent

variable {p : ℕ} [Fact p.Prime] {A B L L' : Type u} [CommRing A] [CommRing B] [CommRing L]
  [CommRing L'] [Algebra A L] [Algebra A L'] [Algebra L L'] [IsScalarTower A L L']
  [Algebra B L] [Algebra B L'] [IsScalarTower B L L'] {ι : Type*} (u : ι → B)

/-- The logarithmic forms are stable under multiplication by elements of `B`. -/
theorem coe_algebraMap_smul_mem_logForms {i : ℕ} (b : B) {y : ⋀[L]^i (Ω[L⁄A])}
    (hy : (y : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i) :
    ((algebraMap B L b • y : ⋀[L]^i (Ω[L⁄A])) : ExteriorAlgebra L (Ω[L⁄A])) ∈
      logForms A L u i := by
  rw [algebraMap_smul, Submodule.coe_smul_of_tower]
  exact Submodule.smul_mem _ _ hy

/-- The logarithmic forms are stable under multiplication by powers of elements of `B`. -/
theorem coe_algebraMap_pow_smul_mem_logForms {i : ℕ} (b : B) (n : ℕ) {y : ⋀[L]^i (Ω[L⁄A])}
    (hy : (y : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i) :
    ((algebraMap B L b ^ n • y : ⋀[L]^i (Ω[L⁄A])) : ExteriorAlgebra L (Ω[L⁄A])) ∈
      logForms A L u i := by
  rw [← map_pow]; exact coe_algebraMap_smul_mem_logForms u _ hy

/-- **Logarithmic forms of `B` on `L'` come from `L`**, when the `uⱼ` are units of `L`. -/
theorem exists_mapExteriorPower_eq_of_mem_logForms (hu : ∀ j, IsUnit (algebraMap B L (u j)))
    {i : ℕ} (y' : ⋀[L']^i (Ω[L'⁄A]))
    (hy' : (y' : ExteriorAlgebra L' (Ω[L'⁄A])) ∈ logForms A L' u i) :
    ∃ y : ⋀[L]^i (Ω[L⁄A]), (y : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i ∧
      mapExteriorPower A L L' i y = y' := by
  let S : Submodule B (⋀[L']^i (Ω[L'⁄A])) :=
    { carrier := {y' | ∃ y : ⋀[L]^i (Ω[L⁄A]),
        (y : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i ∧ mapExteriorPower A L L' i y = y'}
      zero_mem' := ⟨0, zero_mem _, map_zero _⟩
      add_mem' := by
        rintro _ _ ⟨x₁, hx₁, rfl⟩ ⟨x₂, hx₂, rfl⟩
        exact ⟨x₁ + x₂, by rw [Submodule.coe_add]; exact add_mem hx₁ hx₂, map_add _ _ _⟩
      smul_mem' := by
        rintro b _ ⟨x, hx, rfl⟩
        refine ⟨algebraMap B L b • x, coe_algebraMap_smul_mem_logForms u b hx, ?_⟩
        rw [mapExteriorPower_smul, ← IsScalarTower.algebraMap_apply, algebraMap_smul] }
  refine mem_of_mem_logForms S (fun v hv ↦ ?_) y' hy'
  have hgen : ∀ m, ∃ w ∈ logGenerators A L u, KaehlerDifferential.map A A L L' w = v m := by
    intro m
    rcases hv m with ⟨b, hb⟩ | ⟨j, hj⟩
    · exact ⟨_, D_mem_logGenerators u b, by rw [← hb, map_D, ← IsScalarTower.algebraMap_apply]⟩
    · exact ⟨_, dlog_mem_logGenerators u j, by
        rw [← hj, map_dlog (hu j), ← IsScalarTower.algebraMap_apply]⟩
  choose w hw e using hgen
  refine ⟨ιMulti L i w, by rw [ιMulti_apply_coe]; exact ιMulti_mem_logForms w hw, ?_⟩
  rw [mapExteriorPower_ιMulti]
  simp only [e]

variable (f : B) [IsLocalization.Away (algebraMap B L f) L']

omit [Algebra B L'] [IsScalarTower B L L'] in
/-- `mapExteriorPower A L L' i` exhibits `⋀^i Ω[L'⁄A]` as the localization of `⋀^i Ω[L⁄A]` at
the powers of `f`. -/
theorem isLocalizedModule_mapExteriorPower (i : ℕ) :
    IsLocalizedModule (Submonoid.powers (algebraMap B L f)) (mapExteriorPower A L L' i) :=
  IsLocalization.isLocalizedModule_of_exteriorPower L' (KaehlerDifferential.map A A L L') i
    (Submonoid.powers (algebraMap B L f)) _ (mapExteriorPower_ιMulti A L L' i)

/-- Every `i`-form on `L'` becomes, after multiplication by a power of `f`, the image of an
`i`-form on `L`. -/
theorem exists_mapExteriorPower_eq_algebraMap_pow_smul {i : ℕ} (y' : ⋀[L']^i (Ω[L'⁄A])) :
    ∃ (N : ℕ) (y : ⋀[L]^i (Ω[L⁄A])),
      mapExteriorPower A L L' i y = algebraMap B L' f ^ N • y' := by
  have := isLocalizedModule_mapExteriorPower (A := A) (L := L) (L' := L') f i
  obtain ⟨⟨y, _, N, rfl⟩, h⟩ := IsLocalizedModule.surj (Submonoid.powers (algebraMap B L f))
    (mapExteriorPower A L L' i) y'
  refine ⟨N, y, h.symm.trans ?_⟩
  rw [Submonoid.smul_def, ← algebraMap_smul L', map_pow, ← IsScalarTower.algebraMap_apply]

/-- A form on `L` with zero image in `L'` is killed by `(f^N)^p` for some `N`. -/
theorem exists_pow_pow_smul_eq_zero {i : ℕ} {y : ⋀[L]^i (Ω[L⁄A])}
    (hy : mapExteriorPower A L L' i y = 0) : ∃ N : ℕ, (algebraMap B L f ^ N) ^ p • y = 0 := by
  obtain ⟨N, hN⟩ := exists_pow_smul_eq_zero_of_mapExteriorPower_eq_zero (A := A) (L' := L')
      (algebraMap B L f) hy
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := (Fact.out : p.Prime).pos; omega⟩
  exact ⟨N, by rw [hq, pow_succ, mul_smul, hN, smul_zero]⟩

/-- **Exactness descends from `L[1/f]` up to a power of `f`.** -/
theorem exists_pow_smul_mem_exactForms [CharP L p] [CharP L' p] {i : ℕ} (x : ⋀[L]^i (Ω[L⁄A]))
    (h : twist p (mapExteriorPower A L L' i x) ∈ exactForms p A L' i) :
    ∃ K : ℕ, twist p ((algebraMap B L f ^ K) ^ p • x) ∈ exactForms p A L i := by
  set F := algebraMap B L f
  cases i with
  | zero =>
    obtain ⟨K, hK⟩ := exists_pow_pow_smul_eq_zero (p := p) (A := A) (L' := L') f
      ((twist_mem_exactForms_zero _).1 h)
    exact ⟨K, (twist_mem_exactForms_zero _).2 hK⟩
  | succ i =>
    obtain ⟨w', hw'⟩ := (twist_mem_exactForms_succ _).1 h
    obtain ⟨M, W, hW⟩ := exists_mapExteriorPower_eq_algebraMap_pow_smul (A := A) (L := L) f w'
    obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := (Fact.out : p.Prime).pos; omega⟩
    set W₁ := (F ^ M) ^ q • W
    have hW₁ : mapExteriorPower A L L' i W₁ = (algebraMap B L' f ^ M) ^ p • w' := by
      rw [mapExteriorPower_smul, hW, map_pow, map_pow, ← IsScalarTower.algebraMap_apply,
        smul_smul, hq, pow_succ]
    have hzero : mapExteriorPower A L L' (i + 1)
        (deRhamDifferential (A := A) i W₁ - (F ^ M) ^ p • x) = 0 := by
      rw [map_sub, mapExteriorPower_deRhamDifferential, hW₁, deRhamDifferential_pow_smul, hw',
        mapExteriorPower_smul, map_pow, map_pow, ← IsScalarTower.algebraMap_apply, sub_self]
    obtain ⟨K, hK⟩ := exists_pow_pow_smul_eq_zero (p := p) (A := A) (L' := L') f hzero
    refine ⟨K + M, (twist_mem_exactForms_succ _).2 ⟨(F ^ K) ^ p • W₁, ?_⟩⟩
    rw [deRhamDifferential_pow_smul, ← sub_eq_zero, ← hK, smul_sub, smul_smul, ← mul_pow,
      ← pow_add]

/-- **Logarithmic exactness descends from `L[1/f]` up to a power of `f`.** -/
theorem exists_pow_smul_mem_exactLogForms [CharP L p] (hu : ∀ j, IsUnit (algebraMap B L (u j)))
    {i : ℕ} (x : ⋀[L]^i (Ω[L⁄A]))
    (h : ((mapExteriorPower A L L' i x : ⋀[L']^i (Ω[L'⁄A])) : ExteriorAlgebra L' (Ω[L'⁄A])) ∈
      exactLogForms A L' u i) :
    ∃ K : ℕ, (((algebraMap B L f ^ K) ^ p • x : ⋀[L]^i (Ω[L⁄A])) :
      ExteriorAlgebra L (Ω[L⁄A])) ∈ exactLogForms A L u i := by
  set F := algebraMap B L f
  rcases h with h | ⟨j, w', rfl, hw', h⟩
  · obtain ⟨K, hK⟩ := exists_pow_pow_smul_eq_zero (p := p) (A := A) (L' := L') f
      (Subtype.coe_injective (h.trans (Submodule.coe_zero (p := ⋀[L']^i (Ω[L'⁄A]))).symm))
    exact ⟨K, by rw [hK]; exact zero_mem_exactLogForms u i⟩
  · obtain ⟨W, hW, rfl⟩ := exists_mapExteriorPower_eq_of_mem_logForms u hu w' hw'
    have hzero : mapExteriorPower A L L' (j + 1) (deRhamDifferential (A := A) j W - x) = 0 := by
      rw [map_sub, mapExteriorPower_deRhamDifferential, sub_eq_zero]
      exact Subtype.coe_injective h
    obtain ⟨K, hK⟩ := exists_pow_pow_smul_eq_zero (p := p) (A := A) (L' := L') f hzero
    refine ⟨K, Or.inr ⟨j, (F ^ K) ^ p • W, rfl, ?_, ?_⟩⟩
    · rw [← pow_mul]; exact coe_algebraMap_pow_smul_mem_logForms u f _ hW
    · have hK' : (F ^ K) ^ p • deRhamDifferential (A := A) j W = (F ^ K) ^ p • x :=
        sub_eq_zero.1 (by rw [← smul_sub]; exact hK)
      rw [deRhamDifferential_pow_smul, hK']

omit [IsLocalization.Away (algebraMap B L f) L'] in
/-- A nontrivial `L`-algebra `L'` has the characteristic `p` of `L`. -/
theorem charP_of_nontrivial [CharP L p] [Nontrivial L'] : CharP L' p :=
  (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 (by
    rw [← map_natCast (algebraMap L L'), CharP.cast_eq_zero, map_zero])

/-- If `L'` is the zero ring, then `mapExteriorPower A L L' i` is zero. -/
theorem mapExteriorPower_eq_zero_of_subsingleton [Subsingleton L'] {i : ℕ}
    (y : ⋀[L]^i (Ω[L⁄A])) : mapExteriorPower A L L' i y = 0 :=
  haveI : Subsingleton (⋀[L']^i (Ω[L'⁄A])) := Module.subsingleton L' _
  Subsingleton.elim _ _

omit [IsLocalization.Away (algebraMap B L f) L'] in
/-- `mapExteriorPower A L L' i` sends `f^n • y` to `f^n • mapExteriorPower A L L' i y`. -/
theorem mapExteriorPower_pow_smul {i : ℕ} (n : ℕ) (y : ⋀[L]^i (Ω[L⁄A])) :
    mapExteriorPower A L L' i (algebraMap B L f ^ n • y) =
      algebraMap B L' f ^ n • mapExteriorPower A L L' i y := by
  rw [mapExteriorPower_smul, map_pow, ← IsScalarTower.algebraMap_apply]

omit [Fact p.Prime] [IsLocalization.Away (algebraMap B L f) L'] in
/-- `mapExteriorPower A L L' i` sends `(f^n)^p • y` to `(f^n)^p • mapExteriorPower A L L' i y`.
-/
theorem mapExteriorPower_pow_pow_smul {i : ℕ} (n : ℕ) (y : ⋀[L]^i (Ω[L⁄A])) :
    mapExteriorPower A L L' i ((algebraMap B L f ^ n) ^ p • y) =
      (algebraMap B L' f ^ n) ^ p • mapExteriorPower A L L' i y := by
  rw [← pow_mul, ← pow_mul, mapExteriorPower_pow_smul]

section Steps

variable [CharP L p] (hu : ∀ j, IsUnit (algebraMap B L (u j)))
  (hloc : ∀ [CharP L' p], IsLocalLogCartier p A L' u f)

include hu hloc

/-- For a logarithmic form `y`, some `f^N • y` has a logarithmic representative of
`C⁻¹ (f^N • y)`. -/
theorem exists_pow_smul_isInvCartierRep_local {i : ℕ} (y : ⋀[L]^i (Ω[L⁄A]))
    (hy : (y : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i) :
    ∃ (N : ℕ) (x : ⋀[L]^i (Ω[L⁄A])), (x : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i ∧
      IsInvCartierRep p i (algebraMap B L f ^ N • y) x := by
  set F := algebraMap B L f
  rcases subsingleton_or_nontrivial L' with hL' | hL'
  · obtain ⟨N, hN⟩ := exists_pow_smul_eq_zero_of_mapExteriorPower_eq_zero (A := A) (L' := L')
      (algebraMap B L f)
      (mapExteriorPower_eq_zero_of_subsingleton y)
    exact ⟨N, 0, zero_mem _, by rw [hN]; exact IsInvCartierRep.zero⟩
  have : CharP L' p := charP_of_nontrivial (L := L)
  have hl : IsLocalLogCartier p A L' u f := hloc
  obtain ⟨M, z', hz', hrep'⟩ := hl.exists_rep i _
    (coe_mapExteriorPower_mem_logForms (B' := B) u hu y hy)
  obtain ⟨Z, hZ, rfl⟩ := exists_mapExteriorPower_eq_of_mem_logForms u hu z' hz'
  obtain ⟨R, hR⟩ := exists_isInvCartierRep (p := p) i (F ^ M • y)
  have hR' := hR.map (L' := L')
  rw [mapExteriorPower_pow_smul f M y] at hR'
  have hex := hR'.sub_mem_exactForms hrep'
  rw [← map_sub] at hex
  obtain ⟨K, hK⟩ := exists_pow_smul_mem_exactForms f _ hex
  refine ⟨K + M, (F ^ K) ^ p • Z, by rw [← pow_mul]; exact
    coe_algebraMap_pow_smul_mem_logForms u f _ hZ, ?_⟩
  have h := hR.smul (F ^ K)
  rw [smul_smul, ← pow_add] at h
  refine h.of_sub_mem_exactForms ?_
  rwa [← smul_sub]

/-- If a logarithmic form `x` represents `C⁻¹ 0`, then some `(f^N)^p • x` is the differential of
a logarithmic form. -/
theorem exists_pow_smul_mem_exactLogForms_local {i : ℕ} (x : ⋀[L]^i (Ω[L⁄A]))
    (hx : (x : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i) (h : IsInvCartierRep p i 0 x) :
    ∃ N : ℕ, (((algebraMap B L f ^ N) ^ p • x : ⋀[L]^i (Ω[L⁄A])) :
      ExteriorAlgebra L (Ω[L⁄A])) ∈ exactLogForms A L u i := by
  set F := algebraMap B L f
  rcases subsingleton_or_nontrivial L' with hL' | hL'
  · obtain ⟨N, hN⟩ := exists_pow_pow_smul_eq_zero (p := p) (A := A) (L' := L') f
      (mapExteriorPower_eq_zero_of_subsingleton x)
    exact ⟨N, by rw [hN]; exact zero_mem_exactLogForms u i⟩
  have : CharP L' p := charP_of_nontrivial (L := L)
  have hl : IsLocalLogCartier p A L' u f := hloc
  have h' := h.map (L' := L')
  rw [map_zero] at h'
  obtain ⟨M, hM⟩ := hl.mem_exactLogForms i _
    (coe_mapExteriorPower_mem_logForms (B' := B) u hu x hx) h'
  rw [← mapExteriorPower_pow_pow_smul f] at hM
  obtain ⟨K, hK⟩ := exists_pow_smul_mem_exactLogForms u f hu _ hM
  refine ⟨K + M, ?_⟩
  rwa [smul_smul, ← mul_pow, ← pow_add] at hK

omit hu in
/-- If `0` represents `C⁻¹ y`, then some `f^N • y` vanishes. -/
theorem exists_pow_smul_eq_zero_local {i : ℕ} (y : ⋀[L]^i (Ω[L⁄A]))
    (h : IsInvCartierRep p i y 0) : ∃ N : ℕ, algebraMap B L f ^ N • y = 0 := by
  rcases subsingleton_or_nontrivial L' with hL' | hL'
  · exact exists_pow_smul_eq_zero_of_mapExteriorPower_eq_zero (A := A) (L' := L')
      (algebraMap B L f)
      (mapExteriorPower_eq_zero_of_subsingleton y)
  have : CharP L' p := charP_of_nontrivial (L := L)
  have hl : IsLocalLogCartier p A L' u f := hloc
  have h' := h.map (L' := L')
  rw [map_zero] at h'
  exact exists_pow_smul_eq_zero_of_mapExteriorPower_eq_zero (A := A) (L' := L')
      (algebraMap B L f) (hl.eq_zero i _ h')

/-- For a closed logarithmic form `x`, some `(f^N)^p • x` represents `C⁻¹ W` for a logarithmic
form `W`. -/
theorem exists_isInvCartierRep_pow_smul_local {i : ℕ} (x : ⋀[L]^i (Ω[L⁄A]))
    (hx : (x : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i)
    (hcl : deRhamDifferential (A := A) i x = 0) :
    ∃ (N : ℕ) (W : ⋀[L]^i (Ω[L⁄A])), (W : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i ∧
      IsInvCartierRep p i W ((algebraMap B L f ^ N) ^ p • x) := by
  set F := algebraMap B L f
  rcases subsingleton_or_nontrivial L' with hL' | hL'
  · obtain ⟨N, hN⟩ := exists_pow_pow_smul_eq_zero (p := p) (A := A) (L' := L') f
      (mapExteriorPower_eq_zero_of_subsingleton x)
    exact ⟨N, 0, zero_mem _, by rw [hN]; exact IsInvCartierRep.zero⟩
  have : CharP L' p := charP_of_nontrivial (L := L)
  have hl : IsLocalLogCartier p A L' u f := hloc
  obtain ⟨M, W', hW', hrep'⟩ := hl.exists_rep_of_closed i _
    (coe_mapExteriorPower_mem_logForms (B' := B) u hu x hx)
    (by rw [← mapExteriorPower_deRhamDifferential, hcl, map_zero])
  obtain ⟨W₀, hW₀, rfl⟩ := exists_mapExteriorPower_eq_of_mem_logForms u hu W' hW'
  obtain ⟨R, hR⟩ := exists_isInvCartierRep (p := p) i W₀
  have hex := (hR.map (L' := L')).sub_mem_exactForms hrep'
  rw [← mapExteriorPower_pow_pow_smul f, ← map_sub] at hex
  obtain ⟨K, hK⟩ := exists_pow_smul_mem_exactForms f _ hex
  refine ⟨K + M, F ^ K • W₀, by rw [← map_pow]; exact
    coe_algebraMap_smul_mem_logForms u _ hW₀, ?_⟩
  refine (hR.smul (F ^ K)).of_sub_mem_exactForms ?_
  rwa [pow_add, mul_pow, mul_smul, ← smul_sub]

end Steps

end Descent

/-! ### Gluing -/

section Gluing

variable (p : ℕ) [Fact p.Prime] {A B L : Type u} [CommRing A] [CommRing B] [CommRing L]
  [Algebra A L] [Algebra B L] [CharP L p] {ι : Type*} (u : ι → B)

/-- **Partition of unity**: a property of elements of `B` stable under sums and multiples, and
holding near every maximal ideal, holds for `1`. -/
theorem of_forall_exists_notMem {Q : B → Prop} (h0 : Q 0) (hadd : ∀ a b, Q a → Q b → Q (a + b))
    (hmul : ∀ c b, Q b → Q (c * b)) (hQ : ∀ 𝔪 : Ideal B, 𝔪.IsMaximal → ∃ g ∉ 𝔪, Q g) : Q 1 := by
  let I : Ideal B :=
    { carrier := {g | Q g}
      zero_mem' := h0
      add_mem' := fun {a b} ha hb ↦ hadd a b ha hb
      smul_mem' := fun c g hg ↦ hmul c g hg }
  by_cases hI : I = ⊤
  · exact (hI ▸ Submodule.mem_top : (1 : B) ∈ I)
  · obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal I hI
    obtain ⟨g, hg, hgy⟩ := hQ 𝔪 h𝔪
    exact absurd (hle hgy) hg

omit [CharP L p] in
variable {u} in
/-- The exact logarithmic forms are closed under negation. -/
theorem neg_mem_exactLogForms {i : ℕ} {ω : ExteriorAlgebra L (Ω[L⁄A])}
    (h : ω ∈ exactLogForms A L u i) : -ω ∈ exactLogForms A L u i := by
  rcases h with rfl | ⟨j, x, rfl, hx, rfl⟩
  · rw [neg_zero]; exact zero_mem_exactLogForms u _
  · refine Or.inr ⟨j, -x, rfl, by rw [Submodule.coe_neg]; exact neg_mem hx, ?_⟩
    rw [map_neg, Submodule.coe_neg]

/-- The exact logarithmic forms are stable under multiplication by `p`-th powers of elements of
`B`. -/
theorem pow_smul_mem_exactLogForms (b : B) {i : ℕ} (y : ⋀[L]^i (Ω[L⁄A]))
    (h : (y : ExteriorAlgebra L (Ω[L⁄A])) ∈ exactLogForms A L u i) :
    ((algebraMap B L b ^ p • y : ⋀[L]^i (Ω[L⁄A])) : ExteriorAlgebra L (Ω[L⁄A])) ∈
      exactLogForms A L u i := by
  rcases h with h | ⟨j, x, rfl, hx, h⟩
  · left
    rw [Submodule.coe_smul, h, smul_zero]
  · right
    refine ⟨j, algebraMap B L b ^ p • x, rfl, ?_, ?_⟩
    · rw [← map_pow, algebraMap_smul, Submodule.coe_smul_of_tower]
      exact Submodule.smul_mem _ _ hx
    · rw [deRhamDifferential_pow_smul, Submodule.coe_smul, Submodule.coe_smul, h]

open Classical in
/-- A choice of logarithmic representative of `C⁻¹ ω` for every form `ω`, and `0` when there is
none. -/
def logCartierChoice (i : ℕ) (ω : ExteriorAlgebra L (Ω[L⁄A])) : ExteriorAlgebra L (Ω[L⁄A]) :=
  if h : ∃ z, z ∈ logForms A L u i ∧ ∃ x y : ⋀[L]^i (Ω[L⁄A]),
      (x : ExteriorAlgebra L (Ω[L⁄A])) = z ∧ (y : ExteriorAlgebra L (Ω[L⁄A])) = ω ∧
        IsInvCartierRep p i y x then h.choose else 0

section Global

variable {u} (hu : ∀ j, IsUnit (algebraMap B L (u j)))
  (hloc : ∀ 𝔪 : Ideal B, 𝔪.IsMaximal → ∃ f ∉ 𝔪,
    ∀ [CharP (Localization.Away (algebraMap B L f)) p],
      IsLocalLogCartier p A (Localization.Away (algebraMap B L f)) u f)

include hu hloc

omit hu hloc in
/-- A power of an element outside a maximal ideal lies outside it. -/
theorem pow_notMem_of_isMaximal {𝔪 : Ideal B} (h𝔪 : 𝔪.IsMaximal) {f : B} (hf : f ∉ 𝔪) (n : ℕ) :
    f ^ n ∉ 𝔪 :=
  fun h ↦ hf (h𝔪.isPrime.mem_of_pow_mem n h)

/-- Logarithmic forms have logarithmic representatives. -/
theorem exists_isInvCartierRep_of_mem_logForms {i : ℕ} (y : ⋀[L]^i (Ω[L⁄A]))
    (hy : (y : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i) :
    ∃ x : ⋀[L]^i (Ω[L⁄A]), (x : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i ∧
      IsInvCartierRep p i y x := by
  have := of_forall_exists_notMem (Q := fun b : B ↦ ∃ x : ⋀[L]^i (Ω[L⁄A]),
      (x : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i ∧
        IsInvCartierRep p i (algebraMap B L b • y) x)
    ⟨0, zero_mem _, by rw [map_zero, zero_smul]; exact IsInvCartierRep.zero⟩
    (fun a b ⟨x, hx, h⟩ ⟨x', hx', h'⟩ ↦ ⟨x + x', by rw [Submodule.coe_add]; exact add_mem hx hx',
      by rw [map_add, add_smul]; exact h.add h'⟩)
    (fun c b ⟨x, hx, h⟩ ↦ ⟨algebraMap B L c ^ p • x,
      coe_algebraMap_pow_smul_mem_logForms u c p hx,
      by rw [map_mul, mul_smul]; exact h.smul _⟩)
    (fun 𝔪 h𝔪 ↦ by
      obtain ⟨f, hf, hl⟩ := hloc 𝔪 h𝔪
      obtain ⟨N, x, hx, h⟩ := exists_pow_smul_isInvCartierRep_local
        (L' := Localization.Away (algebraMap B L f)) u f hu hl y hy
      exact ⟨f ^ N, pow_notMem_of_isMaximal h𝔪 hf N, x, hx, by rwa [map_pow]⟩)
  simpa using this

/-- A logarithmic form which is exact is the differential of a logarithmic form. -/
theorem coe_mem_exactLogForms_of_isInvCartierRep_zero {i : ℕ} (x : ⋀[L]^i (Ω[L⁄A]))
    (hx : (x : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i) (h : IsInvCartierRep p i 0 x) :
    (x : ExteriorAlgebra L (Ω[L⁄A])) ∈ exactLogForms A L u i := by
  have := of_forall_exists_notMem (Q := fun b : B ↦
      ((algebraMap B L b ^ p • x : ⋀[L]^i (Ω[L⁄A])) : ExteriorAlgebra L (Ω[L⁄A])) ∈
        exactLogForms A L u i)
    (by
      simp only [map_zero, zero_pow (Fact.out : p.Prime).ne_zero, zero_smul]
      exact zero_mem_exactLogForms u i)
    (fun a b ha hb ↦ by
      simp only [map_add, add_pow_char, add_smul, Submodule.coe_add] at ha hb ⊢
      exact add_mem_exactLogForms ha hb)
    (fun c b hb ↦ by
      simp only [map_mul, mul_pow, mul_smul] at hb ⊢
      exact pow_smul_mem_exactLogForms p u c _ hb)
    (fun 𝔪 h𝔪 ↦ by
      obtain ⟨f, hf, hl⟩ := hloc 𝔪 h𝔪
      obtain ⟨N, hN⟩ := exists_pow_smul_mem_exactLogForms_local
        (L' := Localization.Away (algebraMap B L f)) u f hu hl x hx h
      exact ⟨f ^ N, pow_notMem_of_isMaximal h𝔪 hf N, by rwa [map_pow]⟩)
  simpa using this

/-- The inverse Cartier map is injective. -/
theorem eq_zero_of_isInvCartierRep_zero {i : ℕ} (y : ⋀[L]^i (Ω[L⁄A]))
    (h : IsInvCartierRep p i y 0) : y = 0 := by
  have := of_forall_exists_notMem (Q := fun b : B ↦ algebraMap B L b • y = 0)
    (by rw [map_zero, zero_smul])
    (fun a b ha hb ↦ by rw [map_add, add_smul, ha, hb, add_zero])
    (fun c b hb ↦ by rw [map_mul, mul_smul, hb, smul_zero])
    (fun 𝔪 h𝔪 ↦ by
      obtain ⟨f, hf, hl⟩ := hloc 𝔪 h𝔪
      obtain ⟨N, hN⟩ := exists_pow_smul_eq_zero_local
        (L' := Localization.Away (algebraMap B L f)) u f hl y h
      exact ⟨f ^ N, pow_notMem_of_isMaximal h𝔪 hf N, by rwa [map_pow]⟩)
  simpa using this

/-- A closed logarithmic form represents the inverse Cartier image of a logarithmic form. -/
theorem exists_isInvCartierRep_of_closed {i : ℕ} (x : ⋀[L]^i (Ω[L⁄A]))
    (hx : (x : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i)
    (hcl : deRhamDifferential (A := A) i x = 0) :
    ∃ W : ⋀[L]^i (Ω[L⁄A]), (W : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i ∧
      IsInvCartierRep p i W x := by
  have := of_forall_exists_notMem (Q := fun b : B ↦ ∃ W : ⋀[L]^i (Ω[L⁄A]),
      (W : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i ∧
        IsInvCartierRep p i W (algebraMap B L b ^ p • x))
    ⟨0, zero_mem _, by
      rw [map_zero, zero_pow (Fact.out : p.Prime).ne_zero, zero_smul]; exact IsInvCartierRep.zero⟩
    (fun a b ⟨W, hW, h⟩ ⟨W', hW', h'⟩ ↦ ⟨W + W', by rw [Submodule.coe_add]; exact add_mem hW hW',
      by rw [map_add, add_pow_char, add_smul]; exact h.add h'⟩)
    (fun c b ⟨W, hW, h⟩ ↦ ⟨algebraMap B L c • W, coe_algebraMap_smul_mem_logForms u c hW,
      by rw [map_mul, mul_pow, mul_smul]; exact h.smul _⟩)
    (fun 𝔪 h𝔪 ↦ by
      obtain ⟨f, hf, hl⟩ := hloc 𝔪 h𝔪
      obtain ⟨N, W, hW, h⟩ := exists_isInvCartierRep_pow_smul_local
        (L' := Localization.Away (algebraMap B L f)) u f hu hl x hx hcl
      exact ⟨f ^ N, pow_notMem_of_isMaximal h𝔪 hf N, W, hW, by rwa [map_pow]⟩)
  simpa using this

omit hu hloc in
/-- Every logarithmic `i`-form is the coercion of an element of `⋀[L]^i Ω[L⁄A]`. -/
theorem exists_coe_eq_of_mem_logForms {i : ℕ} {ω : ExteriorAlgebra L (Ω[L⁄A])}
    (hω : ω ∈ logForms A L u i) :
    ∃ y : ⋀[L]^i (Ω[L⁄A]), (y : ExteriorAlgebra L (Ω[L⁄A])) = ω :=
  ⟨⟨ω, logForms_le u i hω⟩, rfl⟩

/-- `logCartierChoice` of a logarithmic form is a logarithmic representative. -/
theorem logCartierChoice_spec {i : ℕ} (y : ⋀[L]^i (Ω[L⁄A]))
    (hy : (y : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i) :
    ∃ x : ⋀[L]^i (Ω[L⁄A]), (x : ExteriorAlgebra L (Ω[L⁄A])) = logCartierChoice p u i y ∧
      (x : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i ∧ IsInvCartierRep p i y x := by
  obtain ⟨x₀, hx₀, h₀⟩ := exists_isInvCartierRep_of_mem_logForms p hu hloc y hy
  have hex : ∃ z, z ∈ logForms A L u i ∧ ∃ x y' : ⋀[L]^i (Ω[L⁄A]),
      (x : ExteriorAlgebra L (Ω[L⁄A])) = z ∧ (y' : ExteriorAlgebra L (Ω[L⁄A])) = y ∧
        IsInvCartierRep p i y' x := ⟨x₀, hx₀, x₀, y, rfl, rfl, h₀⟩
  obtain ⟨hz, x, y', hx, hy', h⟩ := hex.choose_spec
  obtain rfl : y' = y := Subtype.coe_injective hy'
  exact ⟨x, by rw [logCartierChoice, dite_eq_left hex, hx], hx ▸ hz, h⟩

/-- `logCartierChoice` takes logarithmic forms to closed logarithmic forms. -/
theorem logCartierChoice_mem_closedLogForms {i : ℕ} {ω : ExteriorAlgebra L (Ω[L⁄A])}
    (hω : ω ∈ logForms A L u i) : logCartierChoice p u i ω ∈ closedLogForms A L u i := by
  obtain ⟨y, rfl⟩ := exists_coe_eq_of_mem_logForms hω
  obtain ⟨x, hx, hxl, h⟩ := logCartierChoice_spec p hu hloc y hω
  exact ⟨hx ▸ hxl, x, hx, h.deRhamDifferential_eq_zero⟩

/-- `logCartierChoice` is additive modulo exact logarithmic forms. -/
theorem logCartierChoice_add_sub_mem_exactLogForms {i : ℕ}
    {ω η : ExteriorAlgebra L (Ω[L⁄A])} (hω : ω ∈ logForms A L u i) (hη : η ∈ logForms A L u i) :
    logCartierChoice p u i (ω + η) - (logCartierChoice p u i ω + logCartierChoice p u i η) ∈
      exactLogForms A L u i := by
  obtain ⟨y₁, rfl⟩ := exists_coe_eq_of_mem_logForms hω
  obtain ⟨y₂, rfl⟩ := exists_coe_eq_of_mem_logForms hη
  obtain ⟨x₁, hx₁, hl₁, h₁⟩ := logCartierChoice_spec p hu hloc y₁ hω
  obtain ⟨x₂, hx₂, hl₂, h₂⟩ := logCartierChoice_spec p hu hloc y₂ hη
  obtain ⟨x₃, hx₃, hl₃, h₃⟩ := logCartierChoice_spec p hu hloc (y₁ + y₂)
    (by rw [Submodule.coe_add]; exact add_mem hω hη)
  rw [← Submodule.coe_add, ← hx₁, ← hx₂, ← hx₃, ← Submodule.coe_add, ← Submodule.coe_sub]
  refine coe_mem_exactLogForms_of_isInvCartierRep_zero p hu hloc _ ?_ ?_
  · rw [Submodule.coe_sub, Submodule.coe_add]
    exact sub_mem hl₃ (add_mem hl₁ hl₂)
  · simpa using h₃.sub (h₁.add h₂)

/-- `logCartierChoice` is Frobenius-semilinear modulo exact logarithmic forms. -/
theorem logCartierChoice_smul_sub_mem_exactLogForms {i : ℕ} (b : B)
    {ω : ExteriorAlgebra L (Ω[L⁄A])} (hω : ω ∈ logForms A L u i) :
    logCartierChoice p u i (b • ω) - b ^ p • logCartierChoice p u i ω ∈
      exactLogForms A L u i := by
  obtain ⟨y, rfl⟩ := exists_coe_eq_of_mem_logForms hω
  obtain ⟨x, hx, hl, h⟩ := logCartierChoice_spec p hu hloc y hω
  have hb : b • (y : ExteriorAlgebra L (Ω[L⁄A])) =
      ((algebraMap B L b • y : ⋀[L]^i (Ω[L⁄A])) : ExteriorAlgebra L (Ω[L⁄A])) := by
    rw [algebraMap_smul, Submodule.coe_smul_of_tower]
  obtain ⟨x', hx', hl', h'⟩ :=
    logCartierChoice_spec p hu hloc _ (coe_algebraMap_smul_mem_logForms u b hω)
  have hbx : b ^ p • logCartierChoice p u i (y : ExteriorAlgebra L (Ω[L⁄A])) =
      ((algebraMap B L b ^ p • x : ⋀[L]^i (Ω[L⁄A])) : ExteriorAlgebra L (Ω[L⁄A])) := by
    rw [← hx, ← map_pow, algebraMap_smul, Submodule.coe_smul_of_tower]
  rw [hb, hbx, ← hx', ← Submodule.coe_sub]
  refine coe_mem_exactLogForms_of_isInvCartierRep_zero p hu hloc _ ?_ ?_
  · rw [Submodule.coe_sub]
    exact sub_mem hl' (coe_algebraMap_pow_smul_mem_logForms u b p hl)
  · simpa using h'.sub (h.smul (algebraMap B L b))

/-- `logCartierChoice` is multiplicative modulo exact logarithmic forms. -/
theorem logCartierChoice_mul_sub_mem_exactLogForms {i j : ℕ}
    {ω η : ExteriorAlgebra L (Ω[L⁄A])} (hω : ω ∈ logForms A L u i) (hη : η ∈ logForms A L u j) :
    logCartierChoice p u (i + j) (ω * η) - logCartierChoice p u i ω * logCartierChoice p u j η ∈
      exactLogForms A L u (i + j) := by
  obtain ⟨y₁, rfl⟩ := exists_coe_eq_of_mem_logForms hω
  obtain ⟨y₂, rfl⟩ := exists_coe_eq_of_mem_logForms hη
  obtain ⟨x₁, hx₁, hl₁, h₁⟩ := logCartierChoice_spec p hu hloc y₁ hω
  obtain ⟨x₂, hx₂, hl₂, h₂⟩ := logCartierChoice_spec p hu hloc y₂ hη
  obtain ⟨x₃, hx₃, hl₃, h₃⟩ := logCartierChoice_spec p hu hloc (wedgeMul i j y₁ y₂)
    (by rw [wedgeMul_apply_coe]; exact mul_mem_logForms hω hη)
  rw [← wedgeMul_apply_coe, ← hx₁, ← hx₂, ← hx₃, ← wedgeMul_apply_coe, ← Submodule.coe_sub]
  refine coe_mem_exactLogForms_of_isInvCartierRep_zero p hu hloc _ ?_ ?_
  · rw [Submodule.coe_sub, wedgeMul_apply_coe]
    exact sub_mem hl₃ (mul_mem_logForms hl₁ hl₂)
  · simpa using h₃.sub (h₁.wedge h₂)

/-- `logCartierChoice` sends `1` to `1`. -/
theorem logCartierChoice_zero_one :
    logCartierChoice p u 0 (1 : ExteriorAlgebra L (Ω[L⁄A])) = 1 := by
  let y₀ : ⋀[L]^0 (Ω[L⁄A]) := ιMulti L 0 fun k ↦ D A L (Fin.elim0 k)
  have hy₀ : (y₀ : ExteriorAlgebra L (Ω[L⁄A])) = 1 := by
    rw [ιMulti_apply_coe, ExteriorAlgebra.ιMulti_zero_apply]
  have hl₀ : (y₀ : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u 0 := by
    rw [ιMulti_apply_coe]; exact ιMulti_mem_logForms _ fun k ↦ Fin.elim0 k
  obtain ⟨x, hx, -, h⟩ := logCartierChoice_spec p hu hloc y₀ hl₀
  have h' := isInvCartierRep_ιMulti_D (p := p) (A := A) (Fin.elim0 : Fin 0 → L)
  calc logCartierChoice p u 0 1 = logCartierChoice p u 0 (y₀ : ExteriorAlgebra L (Ω[L⁄A])) := by
        rw [hy₀]
    _ = x := hx.symm
    _ = 1 := by rw [h.eq_of_zero h', ιMulti_apply_coe, ExteriorAlgebra.ιMulti_zero_apply]

/-- `logCartierChoice (db) = b^{p-1} db` modulo exact logarithmic forms. -/
theorem logCartierChoice_ι_D_sub_mem_exactLogForms (b : B) :
    logCartierChoice p u 1 (ExteriorAlgebra.ι L (D A L (algebraMap B L b))) -
      ExteriorAlgebra.ι L (algebraMap B L b ^ (p - 1) • D A L (algebraMap B L b)) ∈
        exactLogForms A L u 1 := by
  set c := algebraMap B L b
  have hl : ((ιMulti L 1 fun _ ↦ D A L c : ⋀[L]^1 (Ω[L⁄A])) : ExteriorAlgebra L (Ω[L⁄A])) ∈
      logForms A L u 1 := by
    rw [ιMulti_apply_coe]; exact ιMulti_mem_logForms _ fun _ ↦ D_mem_logGenerators u b
  obtain ⟨x, hx, hlx, h⟩ := logCartierChoice_spec p hu hloc _ hl
  have h' := isInvCartierRep_ιMulti_D (p := p) (A := A) (fun _ : Fin 1 ↦ c)
  rw [← coe_ιMulti_one, ← coe_ιMulti_one, ← hx, ← Submodule.coe_sub]
  refine coe_mem_exactLogForms_of_isInvCartierRep_zero p hu hloc _ ?_ ?_
  · rw [Submodule.coe_sub, ιMulti_one_smul, Submodule.coe_smul, ← map_pow]
    refine sub_mem hlx ?_
    rw [algebraMap_smul]
    exact Submodule.smul_mem _ _ hl
  · simpa using h.sub h'

/-- `logCartierChoice (dlog uₖ) = dlog uₖ` modulo exact logarithmic forms. -/
theorem logCartierChoice_ι_dlog_sub_mem_exactLogForms (k : ι) :
    logCartierChoice p u 1 (ExteriorAlgebra.ι L
        (Ring.inverse (algebraMap B L (u k)) • D A L (algebraMap B L (u k)))) -
      ExteriorAlgebra.ι L (Ring.inverse (algebraMap B L (u k)) • D A L (algebraMap B L (u k))) ∈
        exactLogForms A L u 1 := by
  set a := algebraMap B L (u k)
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := (Fact.out : p.Prime).pos; omega⟩
  have hscal : Ring.inverse a ^ p * a ^ (p - 1) = Ring.inverse a := by
    rw [hq, Nat.add_sub_cancel, pow_succ', mul_assoc, ← mul_pow,
      Ring.inverse_mul_cancel _ (hu k), one_pow, mul_one]
  have hl : ((ιMulti L 1 fun _ ↦ Ring.inverse a • D A L a : ⋀[L]^1 (Ω[L⁄A])) :
      ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u 1 := by
    rw [ιMulti_apply_coe]; exact ιMulti_mem_logForms _ fun _ ↦ dlog_mem_logGenerators u k
  obtain ⟨x, hx, hlx, h⟩ := logCartierChoice_spec p hu hloc _ hl
  have h' := (isInvCartierRep_ιMulti_D (p := p) (A := A) (fun _ : Fin 1 ↦ a)).smul
    (Ring.inverse a)
  rw [← ιMulti_one_smul, ← ιMulti_one_smul, smul_smul, hscal] at h'
  rw [← coe_ιMulti_one, ← hx, ← Submodule.coe_sub]
  refine coe_mem_exactLogForms_of_isInvCartierRep_zero p hu hloc _ ?_ ?_
  · rw [Submodule.coe_sub]; exact sub_mem hlx hl
  · simpa using h.sub h'

/-- `logCartierChoice` is injective modulo exact logarithmic forms. -/
theorem eq_zero_of_logCartierChoice_mem_exactLogForms {i : ℕ}
    {ω : ExteriorAlgebra L (Ω[L⁄A])} (hω : ω ∈ logForms A L u i)
    (hCω : logCartierChoice p u i ω ∈ exactLogForms A L u i) : ω = 0 := by
  obtain ⟨y, rfl⟩ := exists_coe_eq_of_mem_logForms hω
  obtain ⟨x, hx, -, h⟩ := logCartierChoice_spec p hu hloc y hω
  rw [← hx] at hCω
  have hxe := twist_mem_exactForms_of_coe_mem_exactLogForms p x hCω
  have h0 : IsInvCartierRep p i y 0 := h.of_sub_mem_exactForms (by
    rw [zero_sub, map_neg]; exact neg_mem hxe)
  rw [eq_zero_of_isInvCartierRep_zero p hu hloc y h0, Submodule.coe_zero]

/-- `logCartierChoice` is onto the closed logarithmic forms modulo exact logarithmic forms. -/
theorem exists_sub_logCartierChoice_mem_exactLogForms {i : ℕ}
    {z : ExteriorAlgebra L (Ω[L⁄A])} (hz : z ∈ closedLogForms A L u i) :
    ∃ ω ∈ logForms A L u i, z - logCartierChoice p u i ω ∈ exactLogForms A L u i := by
  obtain ⟨hz, x₀, rfl, hcl⟩ := hz
  obtain ⟨W, hW, hrep⟩ := exists_isInvCartierRep_of_closed p hu hloc x₀ hz hcl
  refine ⟨W, hW, ?_⟩
  obtain ⟨x, hx, hl, h⟩ := logCartierChoice_spec p hu hloc W hW
  rw [← hx, ← Submodule.coe_sub]
  refine coe_mem_exactLogForms_of_isInvCartierRep_zero p hu hloc _ ?_ ?_
  · rw [Submodule.coe_sub]; exact sub_mem hz hl
  · simpa using hrep.sub h

/-- **The logarithmic inverse Cartier isomorphism, glued from a cover.**

Let `A → L` and `B → L` be maps of rings with `L` of characteristic `p`, and `uⱼ ∈ B` with unit
images in `L`. Suppose that every maximal ideal of `B` avoids some `f` for which the logarithmic
inverse Cartier theorem holds on `L[1/f]` up to powers of `f` (`MMP.DeRham.IsLocalLogCartier`).
Then there is a map `C` on the logarithmic forms of `L` with values in the closed logarithmic
forms, additive, Frobenius-semilinear and multiplicative modulo the exact logarithmic forms, with
`C(db) = b^{p-1} db` and `C(dlog uⱼ) = dlog uⱼ`, injective modulo exact logarithmic forms and onto
the closed logarithmic forms modulo exact ones. -/
theorem exists_logInverseCartier_of_forall_isMaximal :
    ∃ C : ℕ → ExteriorAlgebra L (Ω[L⁄A]) → ExteriorAlgebra L (Ω[L⁄A]),
      (∀ i, ∀ ω ∈ logForms A L u i, C i ω ∈ closedLogForms A L u i) ∧
      (∀ i, ∀ ω ∈ logForms A L u i, ∀ η ∈ logForms A L u i,
        C i (ω + η) - (C i ω + C i η) ∈ exactLogForms A L u i) ∧
      (∀ i (b : B), ∀ ω ∈ logForms A L u i, C i (b • ω) - b ^ p • C i ω ∈ exactLogForms A L u i) ∧
      (∀ i j, ∀ ω ∈ logForms A L u i, ∀ η ∈ logForms A L u j,
        C (i + j) (ω * η) - C i ω * C j η ∈ exactLogForms A L u (i + j)) ∧
      C 0 1 = 1 ∧
      (∀ b : B, C 1 (ExteriorAlgebra.ι L (D A L (algebraMap B L b))) -
        ExteriorAlgebra.ι L (algebraMap B L b ^ (p - 1) • D A L (algebraMap B L b)) ∈
          exactLogForms A L u 1) ∧
      (∀ k : ι, C 1 (ExteriorAlgebra.ι L
          (Ring.inverse (algebraMap B L (u k)) • D A L (algebraMap B L (u k)))) -
        ExteriorAlgebra.ι L (Ring.inverse (algebraMap B L (u k)) • D A L (algebraMap B L (u k))) ∈
          exactLogForms A L u 1) ∧
      (∀ i, ∀ ω ∈ logForms A L u i, C i ω ∈ exactLogForms A L u i → ω = 0) ∧
      (∀ i, ∀ z ∈ closedLogForms A L u i, ∃ ω ∈ logForms A L u i,
        z - C i ω ∈ exactLogForms A L u i) :=
  ⟨logCartierChoice p u, fun _ _ hω ↦ logCartierChoice_mem_closedLogForms p hu hloc hω,
    fun _ _ hω _ hη ↦ logCartierChoice_add_sub_mem_exactLogForms p hu hloc hω hη,
    fun _ b _ hω ↦ logCartierChoice_smul_sub_mem_exactLogForms p hu hloc b hω,
    fun _ _ _ hω _ hη ↦ logCartierChoice_mul_sub_mem_exactLogForms p hu hloc hω hη,
    logCartierChoice_zero_one p hu hloc, logCartierChoice_ι_D_sub_mem_exactLogForms p hu hloc,
    logCartierChoice_ι_dlog_sub_mem_exactLogForms p hu hloc,
    fun _ _ hω ↦ eq_zero_of_logCartierChoice_mem_exactLogForms p hu hloc hω,
    fun _ _ hz ↦ exists_sub_logCartierChoice_mem_exactLogForms p hu hloc hz⟩

end Global

end Gluing

/-! ### The local hypothesis from coordinates -/

section Coordinates

variable (p : ℕ) [Fact p.Prime] {A B Bf L : Type u} [CommRing A] [CommRing B] [CommRing Bf]
  [CommRing L] [Algebra A L] [Algebra B L] [Algebra B Bf] [Algebra Bf L] [IsScalarTower B Bf L]
  [CharP L p]

omit [CharP L p] in
/-- `KaehlerDifferential.map A A L L` is the identity. -/
@[simp]
theorem kaehlerDifferential_map_self (w : Ω[L⁄A]) : KaehlerDifferential.map A A L L w = w := by
  have h : KaehlerDifferential.map A A L L = LinearMap.id :=
    LinearMap.ext_on_range (span_range_derivation A L) fun b ↦ by simp
  rw [h, LinearMap.id_apply]

omit [CharP L p] in
/-- `mapExteriorPower A L L i` is the identity. -/
@[simp]
theorem mapExteriorPower_self {i : ℕ} (y : ⋀[L]^i (Ω[L⁄A])) :
    mapExteriorPower A L L i y = y := by
  have h : mapExteriorPower A L L i = LinearMap.id := by
    refine exteriorPower.linearMap_ext ?_
    ext v
    simp [kaehlerDifferential_map_self]
  rw [h, LinearMap.id_apply]

omit [CharP L p] in
/-- The action of `b ∈ B` on the exterior algebra of `Ω[L⁄A]` is that of its image in `Bf`. -/
theorem smul_eq_algebraMap_smul (b : B) (ω : ExteriorAlgebra L (Ω[L⁄A])) :
    b • ω = algebraMap B Bf b • ω := by
  rw [← algebraMap_smul L b ω, ← algebraMap_smul L (algebraMap B Bf b) ω,
    ← IsScalarTower.algebraMap_apply]

variable {ι ι' : Type*} (u : ι → B) (u' : ι' → Bf)

omit [CharP L p] in
/-- Logarithmic forms of `B` are logarithmic forms of `Bf` when every pole is either a pole of
`Bf` or a unit of `Bf`. -/
theorem logForms_le_logForms
    (hpole : ∀ j, IsUnit (algebraMap B Bf (u j)) ∨ ∃ k, u' k = algebraMap B Bf (u j)) {i : ℕ}
    {ω : ExteriorAlgebra L (Ω[L⁄A])} (hω : ω ∈ logForms A L u i) : ω ∈ logForms A L u' i := by
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    refine ιMulti_mem_logForms_of_mem_span v fun m ↦ ?_
    rcases hv m with ⟨b, hb⟩ | ⟨j, hj⟩
    · rw [← hb]; dsimp only; rw [IsScalarTower.algebraMap_apply B Bf L]
      exact Submodule.subset_span (D_mem_logGenerators u' _)
    · rw [← hj]; dsimp only; rw [IsScalarTower.algebraMap_apply B Bf L]
      rcases hpole j with hunit | ⟨k, hk⟩
      · rw [← map_ringInverse_of_isUnit _ hunit, algebraMap_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (D_mem_logGenerators u' _))
      · rw [← hk]
        exact Submodule.subset_span (dlog_mem_logGenerators u' k)
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul b x _ hx => rw [smul_eq_algebraMap_smul (Bf := Bf)]; exact Submodule.smul_mem _ _ hx

omit [CharP L p] in
/-- Clearing denominators: a logarithmic form of `Bf = B[1/f]` becomes a logarithmic form of `B`
after multiplication by a power of `f`. -/
theorem exists_pow_smul_mem_logForms (f : B) [IsLocalization.Away f Bf]
    (hu : ∀ j, IsUnit (algebraMap B L (u j))) (hpole : ∀ k, ∃ j, u' k = algebraMap B Bf (u j))
    {i : ℕ} (y : ⋀[L]^i (Ω[L⁄A]))
    (hy : (y : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u' i) :
    ∃ N : ℕ, ((algebraMap B L f ^ N • y : ⋀[L]^i (Ω[L⁄A])) :
      ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i := by
  have hy' : (y : ExteriorAlgebra L (Ω[L⁄A])) ∈
      logForms A L (fun j ↦ algebraMap B Bf (u j)) i := by
    refine Submodule.span_le.2 ?_ hy
    rintro _ ⟨v, hv, rfl⟩
    refine ιMulti_mem_logForms v fun m ↦ ?_
    rcases hv m with h | ⟨k, hk⟩
    · exact Or.inl h
    · obtain ⟨j, hj⟩ := hpole k
      exact Or.inr ⟨j, by rw [← hk]; dsimp only; rw [hj]⟩
  obtain ⟨N, y₀, hy₀, e⟩ := exists_mapExteriorPower_eq_pow_smul (L := L) (L' := L) (B' := Bf) u f
    hu y hy'
  rw [mapExteriorPower_self] at e
  exact ⟨N, by rw [← e]; exact hy₀⟩

variable {n : ℕ} {P : Finset (Fin n)} {x : Fin n → Bf}
  (hP : ∀ j ∈ P, IsUnit (algebraMap Bf L (x j)))
  {bL : Module.Basis (Fin n) L (Ω[L⁄A])} (hb : ∀ j, bL j = D A L (algebraMap Bf L (x j)))
  (hu₁ : ∀ k, ∃ j ∈ P, x j = u' k) (hu₂ : ∀ j ∈ P, ∃ k, u' k = x j)
  (hcoord : ∀ (b : Bf) j, bL.repr (D A L (algebraMap Bf L b)) j ∈ Set.range (algebraMap Bf L))
  (hF : IsFrobeniusCoordinates p Bf x)
  (hFL : IsFrobeniusCoordinates p L (fun j ↦ algebraMap Bf L (x j)))

include hP hb hu₁ hu₂ hcoord hF hFL in
/-- **The local hypothesis from coordinates**: if the `xⱼ` are Frobenius coordinates of
`Bf = B[1/f]` whose images are Frobenius coordinates of `L`, the `dxⱼ` form a basis of `Ω[L⁄A]`
in which each `db` (`b ∈ Bf`) has coefficients from `Bf`, and the poles of `B` are coordinates or
units of `Bf`, then the logarithmic inverse Cartier theorem holds up to powers of `f`. -/
theorem isLocalLogCartier_of_coordinates (f : B) [IsLocalization.Away f Bf]
    (hu : ∀ j, IsUnit (algebraMap B L (u j)))
    (hpole : ∀ j, IsUnit (algebraMap B Bf (u j)) ∨ ∃ k, u' k = algebraMap B Bf (u j))
    (hpole' : ∀ k, ∃ j, u' k = algebraMap B Bf (u j)) :
    IsLocalLogCartier p A L u f := by
  have hle := fun {i : ℕ} {ω : ExteriorAlgebra L (Ω[L⁄A])} (h : ω ∈ logForms A L u i) ↦
    logForms_le_logForms (Bf := Bf) u u' hpole h
  have hclear := fun {i : ℕ} (y : ⋀[L]^i (Ω[L⁄A]))
    (h : (y : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u' i) ↦
    exists_pow_smul_mem_logForms u u' f hu hpole' y h
  set F := algebraMap B L f
  have hpow : ∀ {i : ℕ} (N : ℕ) {y : ⋀[L]^i (Ω[L⁄A])},
      ((F ^ N • y : ⋀[L]^i (Ω[L⁄A])) : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i →
      (((F ^ N) ^ p • y : ⋀[L]^i (Ω[L⁄A])) : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i := by
    intro i N y h
    obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := (Fact.out : p.Prime).pos; omega⟩
    rw [hq, pow_succ, mul_smul, ← pow_mul]
    exact coe_algebraMap_pow_smul_mem_logForms u f _ h
  have hrep : ∀ {i : ℕ} (y : ⋀[L]^i (Ω[L⁄A])),
      IsInvCartierRep p i y (cartierRep p A (fun j ↦ algebraMap Bf L (x j)) bL i y) :=
    fun y ↦ ⟨cartierRepClass p _ bL _ y, rfl,
      (inverseCartier_eq_cohomologyMk_cartierRep p hb _ y).symm⟩
  refine ⟨fun i y hy ↦ ?_, fun i x₀ hx₀ h ↦ ?_, fun i y h ↦ ?_, fun i x₀ hx₀ hcl ↦ ?_⟩
  · have hc := coe_cartierRep_mem_logForms p hP hb hu₁ hu₂ hcoord y (hle hy)
    obtain ⟨N, hN⟩ := hclear _ hc
    exact ⟨N, _, hpow N hN, (hrep y).smul _⟩
  · have hex := coe_mem_exactLogForms_of_twist_mem_exactForms p hP hb hu₁ hu₂ hcoord hF hFL x₀
      (hle hx₀) h.deRhamDifferential_eq_zero ((isInvCartierRep_zero_iff).1 h)
    rcases hex with h0 | ⟨j, w, rfl, hw, hdw⟩
    · exact ⟨0, by rw [show x₀ = 0 from Subtype.coe_injective h0, smul_zero]; exact
        zero_mem_exactLogForms u _⟩
    · obtain ⟨N, hN⟩ := hclear w hw
      refine ⟨N, Or.inr ⟨j, (F ^ N) ^ p • w, rfl, hpow N hN, ?_⟩⟩
      rw [deRhamDifferential_pow_smul, Submodule.coe_smul, hdw, Submodule.coe_smul]
  · obtain ⟨z, hz, ez⟩ := h
    have h0 : inverseCartier p A L i y = 0 := by
      rw [← ez, (cohomologyMk_eq_zero_iff z).2]
      rw [hz, map_zero]; exact zero_mem _
    exact (inverseCartier_bijective_of_isFrobeniusCoordinates p hb hFL i).1
      (h0.trans (map_zero _).symm)
  · obtain ⟨-, -, hdiff⟩ := projList_mem_logForms_of_closed (p := p) hP hb hu₁ hcoord
      (List.finRange n) i x₀ (hle hx₀) hcl
    obtain ⟨ω, hω, hπ⟩ :=
      exists_projList_eq_cartierRep_of_mem_logForms hP hb hu₁ hu₂ hcoord hF x₀ (hle hx₀)
    obtain ⟨N, hN⟩ := hclear ω hω
    refine ⟨N, _, hN, ((hrep ω).of_sub_mem_exactForms ?_).smul _⟩
    rw [← hπ]
    exact twist_mem_exactForms_of_coe_mem_exactLogForms p _ hdiff

end Coordinates

end MMP.DeRham

end
