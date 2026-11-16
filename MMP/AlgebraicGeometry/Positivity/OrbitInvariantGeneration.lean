/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import StacksFrontier.AlgebraicGeometry.SectionProduct.Basic
public import Mathlib.RingTheory.Polynomial.Vieta

/-!
# Finite orbit polynomials preserve generation

Let `X` be a scheme, `L` an invertible `𝒪_X`-module and
`Γ_*(X, L) = ⨁_{n ≥ 0} Γ(X, L^{⊗ n})` its graded section ring. Let a finite group `G` of order
`N` act on `Γ_*(X, L)` by graded ring automorphisms, and let `W ⊆ Γ(X, L)` be a set of sections
generating `L`, i.e. at every point some element of `W` does not vanish. For `s ∈ W` let
`σ_i(s) ∈ Γ(X, L^{⊗ i})` be the `i`-th elementary symmetric function of the `N` sections
`g • s`, `g ∈ G`. Then the `G`-invariant sections `σ_i(s)^{N!/i} ∈ Γ(X, L^{⊗ N!})`, for
`s ∈ W` and `1 ≤ i ≤ N`, generate `L^{⊗ N!}`.

The proof: `σ_i(s)` is homogeneous of degree `i` and `G`-invariant, because `G` permutes the
`g • s`. Since the factor `g = 1` of `∏_g (s - g • s)` vanishes, Vieta's formulas give
`s^N = -∑_{i=1}^{N} (-1)^i σ_i(s) s^{N-i}`. If every `σ_i(s)` with `i ≥ 1` vanished at `x`, so
would the right-hand side, hence `s^N`, hence `s`, since the nonvanishing locus of a product is
the intersection of the nonvanishing loci. So at a point where `s` does not vanish some
`σ_i(s)`, and with it `σ_i(s)^{N!/i}`, does not vanish.

## Main definitions

* `MMP.Fourfold.orbitMultiset`: the multiset of the translates `g • a`, `g ∈ G`, of an element
  of the section ring.
* `MMP.Fourfold.orbitEsymm`: `σ_i(s)`, the `i`-th elementary symmetric function of the
  translates of a section `s` of `L`.
* `MMP.Fourfold.orbitInvariantSection`: `σ_i(s)^{N!/i}`, as a section of `L^{⊗ N!}`.

## Main results

* `MMP.Fourfold.of_orbitEsymm`: `σ_i(s)` is homogeneous of degree `i`.
* `MMP.Fourfold.orbitEsymm_invariant`: `σ_i(s)` is `G`-invariant.
* `MMP.Fourfold.exists_orbitEsymm_mem_nonvanishingLocus`: if `s(x) ≠ 0`, then
  `σ_i(s)(x) ≠ 0` for some `1 ≤ i ≤ N`.
* `MMP.Fourfold.orbitInvariantSection_invariant_and_generates`: **the invariant sections
  `σ_i(s)^{N!/i}` obtained from `W` are `G`-invariant and generate `L^{⊗ N!}`.**

## Implementation notes

* The section ring is `Stacks.GradedSections.sectionRing L`, the direct sum over `n : ℕ` of
  `Stacks.GradedSections.powSections L n = Hom(𝒪_X, L^{⊗ n})`, which is `Γ(X, L^{⊗ n})`
  (`Stacks.SectionProduct.globalSection`); it is commutative for an invertible `L`
  (`Stacks.SectionRingGeometric.schemeSectionCommRing`). Here `L^{⊗ n}` is
  `Stacks.TensorPowers.natTensorPow L n`, which is the integer tensor power `L^{⊗ (n : ℤ)}` of
  Stacks Tag 01CU by `Stacks.SectionRingGeometric.natTensorPow_eq_tensorPow`. The space
  `H^0(X, L)` is the degree-one part `powSections L 1`.
* A section `t` of `L^{⊗ n}` *does not vanish at `x`* when `x` lies in
  `Stacks.Ample.nonvanishingLocus` of its global section, i.e. its germ is not in `𝔪_x L^{⊗ n}_x`;
  a set of sections *generates* `L^{⊗ n}` when every point lies in the nonvanishing locus of one
  of them.
* The action of `G` is a group homomorphism `ρ : G →* RingAut Γ_*(X, L)` whose automorphisms
  preserve every graded piece. Its restriction to degree one is the action on `H^0(X, L)`; the
  argument uses neither that `W` is `G`-stable nor that it is a linear subspace, nor that the
  action is linear over a base field, so these are not assumed. Likewise the argument works on
  any scheme: that `X` is reduced, projective and defined over `ℂ` is not used.
* The invariant section of `L^{⊗ N!}` is the degree-`N!` component of `σ_i(s)^{N!/i}` in the
  section ring; `orbitInvariantSection_invariant_and_generates` also records that
  `σ_i(s)^{N!/i}` equals that component, i.e. is homogeneous of degree `N!`.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV), for the section ring.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry

universe u v

namespace MMP.Fourfold

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive
  Stacks.SectionRingGeometric.schemeSectionCommRing

open Stacks.GradedSections Stacks.TensorPowers Stacks.SectionProduct Stacks.Ample

variable {X : Scheme.{u}}

/-- `globalSection` is additive: it sends `0` to `0`. -/
@[simp] theorem globalSection_zero (F : X.Modules) : globalSection X F 0 = 0 :=
  map_zero (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X F)

/-- `globalSection` is additive. -/
@[simp] theorem globalSection_add (F : X.Modules) (f f' : 𝟙_ X.Modules ⟶ F) :
    globalSection X F (f + f') = globalSection X F f + globalSection X F f' :=
  map_add (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X F) f f'

/-- `globalSection` commutes with negation. -/
@[simp] theorem globalSection_neg (F : X.Modules) (f : 𝟙_ X.Modules ⟶ F) :
    globalSection X F (-f) = -globalSection X F f :=
  map_neg (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X F) f

variable (L : X.Modules) [IsInvertibleModule X L]

/-! ### Homogeneous elements and their vanishing at a point -/

/-- The degree-`n` homogeneous elements of the section ring `Γ_*(X, L)`. -/
def homogeneousPart (n : ℕ) : AddSubgroup (sectionRing L) :=
  (DirectSum.of (powSections L) n).range

variable {L} in
omit [IsInvertibleModule X L] in
/-- Membership in `homogeneousPart`: being the image of a section of `L^{⊗ n}`. -/
theorem mem_homogeneousPart {n : ℕ} {y : sectionRing L} :
    y ∈ homogeneousPart L n ↔ ∃ u : powSections L n, DirectSum.of _ n u = y :=
  AddMonoidHom.mem_range

/-- The sections of `L^{⊗ n}` vanishing at the point `x`. -/
def vanishingSections (x : X) (n : ℕ) : AddSubgroup (powSections L n) where
  carrier := {u | x ∉ nonvanishingLocus (natTensorPow L n) (globalSection X _ u)}
  zero_mem' := by simp
  add_mem' {u v} hu hv := by
    simp only [Set.mem_ofPred_eq, globalSection_add] at hu hv ⊢
    intro h
    rcases nonvanishingLocus_add_subset _ _ _ h with h | h
    exacts [hu h, hv h]
  neg_mem' {u} hu := by simpa using hu

/-- The degree-`n` homogeneous elements of `Γ_*(X, L)` vanishing at `x`. -/
def vanishingPart (x : X) (n : ℕ) : AddSubgroup (sectionRing L) :=
  (vanishingSections L x n).map (DirectSum.of (powSections L) n)

variable {L}

omit [IsInvertibleModule X L] in
/-- Membership in `vanishingPart`: being the image of a section of `L^{⊗ n}` vanishing at `x`. -/
theorem mem_vanishingPart {x : X} {n : ℕ} {y : sectionRing L} :
    y ∈ vanishingPart L x n ↔ ∃ u : powSections L n,
      x ∉ nonvanishingLocus (natTensorPow L n) (globalSection X _ u) ∧
        DirectSum.of _ n u = y :=
  AddSubgroup.mem_map

omit [IsInvertibleModule X L] in
/-- Transport of `homogeneousPart` along an equality of degrees. -/
theorem homogeneousPart_congr {m n : ℕ} (h : m = n) :
    homogeneousPart L m = homogeneousPart L n :=
  congrArg (homogeneousPart L) h

omit [IsInvertibleModule X L] in
/-- Transport of `vanishingPart` along an equality of degrees. -/
theorem vanishingPart_congr {x : X} {m n : ℕ} (h : m = n) :
    vanishingPart L x m = vanishingPart L x n :=
  congrArg (vanishingPart L x) h

omit [IsInvertibleModule X L] in
/-- The unit of the section ring has degree zero. -/
theorem one_mem_homogeneousPart : (1 : sectionRing L) ∈ homogeneousPart L 0 :=
  mem_homogeneousPart.mpr ⟨_, (DirectSum.one_def (powSections L)).symm⟩

omit [IsInvertibleModule X L] in
/-- The product of homogeneous elements of degrees `m` and `n` has degree `m + n`. -/
theorem mul_mem_homogeneousPart {m n : ℕ} {y z : sectionRing L}
    (hy : y ∈ homogeneousPart L m) (hz : z ∈ homogeneousPart L n) :
    y * z ∈ homogeneousPart L (m + n) := by
  obtain ⟨u, rfl⟩ := mem_homogeneousPart.mp hy
  obtain ⟨v, rfl⟩ := mem_homogeneousPart.mp hz
  exact mem_homogeneousPart.mpr ⟨_, (DirectSum.of_mul_of u v).symm⟩

omit [IsInvertibleModule X L] in
/-- The `k`-th power of a homogeneous element of degree `m` has degree `m * k`. -/
theorem pow_mem_homogeneousPart {m : ℕ} {y : sectionRing L} (hy : y ∈ homogeneousPart L m) :
    ∀ k : ℕ, y ^ k ∈ homogeneousPart L (m * k)
  | 0 => by
    rw [pow_zero]
    exact one_mem_homogeneousPart
  | k + 1 => by
    rw [pow_succ, homogeneousPart_congr (Nat.mul_succ m k)]
    exact mul_mem_homogeneousPart (pow_mem_homogeneousPart hy k) hy

/-- A product of `k` elements of degree one is homogeneous of degree `k`. -/
theorem multiset_prod_mem_homogeneousPart (M : Multiset (sectionRing L))
    (hM : ∀ y ∈ M, y ∈ homogeneousPart L 1) :
    M.prod ∈ homogeneousPart L (Multiset.card M) := by
  induction M using Multiset.induction_on with
  | empty =>
    rw [Multiset.prod_zero, Multiset.card_zero]
    exact one_mem_homogeneousPart
  | cons a M ih =>
    rw [Multiset.prod_cons, Multiset.card_cons, homogeneousPart_congr (Nat.add_comm _ 1)]
    exact mul_mem_homogeneousPart (hM a (Multiset.mem_cons_self a M))
      (ih fun y hy => hM y (Multiset.mem_cons_of_mem hy))

/-- The `j`-th elementary symmetric function of elements of degree one is homogeneous of
degree `j`. -/
theorem esymm_mem_homogeneousPart (M : Multiset (sectionRing L))
    (hM : ∀ y ∈ M, y ∈ homogeneousPart L 1) (j : ℕ) :
    M.esymm j ∈ homogeneousPart L j := by
  refine AddSubgroup.multiset_sum_mem _ _ fun y hy => ?_
  obtain ⟨T, hT, rfl⟩ := Multiset.mem_map.mp hy
  obtain ⟨hTM, hcard⟩ := Multiset.mem_powersetCard.mp hT
  rw [← hcard]
  exact multiset_prod_mem_homogeneousPart T fun y hy => hM y (Multiset.mem_of_le hTM hy)

/-- A homogeneous element vanishing at `x` times any homogeneous element vanishes at `x`. -/
theorem mul_mem_vanishingPart {x : X} {m n : ℕ} {y z : sectionRing L}
    (hy : y ∈ vanishingPart L x m) (hz : z ∈ homogeneousPart L n) :
    y * z ∈ vanishingPart L x (m + n) := by
  obtain ⟨u, hu, rfl⟩ := mem_vanishingPart.mp hy
  obtain ⟨v, rfl⟩ := mem_homogeneousPart.mp hz
  refine mem_vanishingPart.mpr ⟨_, fun h => hu ?_, (DirectSum.of_mul_of u v).symm⟩
  exact ((nonvanishingLocus_mul L m n u v).subset h).1

/-- The homogeneous elements of degree `n` that do not vanish at `x`. -/
def nonvanishingPart (x : X) (n : ℕ) : Set (sectionRing L) :=
  {y | ∃ u : powSections L n,
    x ∈ nonvanishingLocus (natTensorPow L n) (globalSection X _ u) ∧ DirectSum.of _ n u = y}

omit [IsInvertibleModule X L] in
/-- Transport of `nonvanishingPart` along an equality of degrees. -/
theorem nonvanishingPart_congr {x : X} {m n : ℕ} (h : m = n) :
    nonvanishingPart (L := L) x m = nonvanishingPart x n :=
  congrArg (nonvanishingPart x) h

/-- A product of homogeneous elements not vanishing at `x` does not vanish at `x`. -/
theorem mul_mem_nonvanishingPart {x : X} {m n : ℕ} {y z : sectionRing L}
    (hy : y ∈ nonvanishingPart x m) (hz : z ∈ nonvanishingPart x n) :
    y * z ∈ nonvanishingPart x (m + n) := by
  obtain ⟨u, hu, rfl⟩ := hy
  obtain ⟨v, hv, rfl⟩ := hz
  exact ⟨_, (Set.ext_iff.mp (nonvanishingLocus_mul L m n u v) x).mpr ⟨hu, hv⟩,
    (DirectSum.of_mul_of u v).symm⟩

/-- A positive power of a homogeneous element not vanishing at `x` does not vanish at `x`. -/
theorem pow_mem_nonvanishingPart {x : X} {m : ℕ} {y : sectionRing L}
    (hy : y ∈ nonvanishingPart x m) {k : ℕ} (hk : 1 ≤ k) : y ^ k ∈ nonvanishingPart x (m * k) := by
  induction k, hk using Nat.le_induction with
  | base => simpa using hy
  | succ k _ ih =>
    rw [pow_succ, nonvanishingPart_congr (Nat.mul_succ m k)]
    exact mul_mem_nonvanishingPart ih hy

omit [IsInvertibleModule X L] in
/-- A homogeneous element of degree `n` cannot both vanish and not vanish at `x`. -/
theorem notMem_vanishingPart_of_mem_nonvanishingPart {x : X} {n : ℕ} {y : sectionRing L}
    (hy : y ∈ nonvanishingPart x n) : y ∉ vanishingPart L x n := by
  obtain ⟨u, hu, rfl⟩ := hy
  intro h
  obtain ⟨v, hv, he⟩ := mem_vanishingPart.mp h
  exact hv (DirectSum.of_injective n he ▸ hu)

/-! ### Orbit polynomials -/

variable {G : Type v} [Group G] [Fintype G]

/-- The multiset of the translates `ρ g a`, `g ∈ G`, of an element `a` of the section ring. -/
def orbitMultiset (ρ : G →* RingAut (sectionRing L)) (a : sectionRing L) :
    Multiset (sectionRing L) :=
  Finset.univ.val.map fun g => ρ g a

omit [IsInvertibleModule X L] in
/-- There are `|G|` translates, counted with multiplicity. -/
@[simp] theorem card_orbitMultiset (ρ : G →* RingAut (sectionRing L)) (a : sectionRing L) :
    Multiset.card (orbitMultiset ρ a) = Fintype.card G := by
  simp [orbitMultiset, Finset.card_univ]

omit [IsInvertibleModule X L] in
/-- The group permutes the translates. -/
theorem map_orbitMultiset (ρ : G →* RingAut (sectionRing L)) (a : sectionRing L) (g : G) :
    (orbitMultiset ρ a).map (ρ g) = orbitMultiset ρ a := by
  have : (fun h : G => ρ g (ρ h a)) = (fun h => ρ h a) ∘ Equiv.mulLeft g := by
    ext h
    simp [map_mul, RingAut.mul_apply]
  rw [orbitMultiset, Multiset.map_map, Function.comp_def, this, ← Multiset.map_map,
    Multiset.map_univ_val_equiv]

/-- `σ_i(s)`: the `i`-th elementary symmetric function of the translates `ρ g s`, `g ∈ G`, of a
section `s` of `L`, as an element of the section ring. -/
def orbitEsymm (ρ : G →* RingAut (sectionRing L)) (s : powSections L 1) (i : ℕ) :
    sectionRing L :=
  (orbitMultiset ρ (DirectSum.of _ 1 s)).esymm i

/-- A ring homomorphism commutes with elementary symmetric functions. -/
theorem map_multiset_esymm {R S F : Type*} [CommSemiring R] [CommSemiring S]
    [FunLike F R S] [RingHomClass F R S] (f : F) (M : Multiset R) (j : ℕ) :
    f (M.esymm j) = (M.map f).esymm j := by
  simp only [Multiset.esymm, map_multiset_sum, Multiset.powersetCard_map, Multiset.map_map,
    Function.comp_def, map_multiset_prod]

/-- **`σ_i(s)` is `G`-invariant.** -/
@[simp] theorem orbitEsymm_invariant (ρ : G →* RingAut (sectionRing L)) (s : powSections L 1)
    (i : ℕ) (g : G) : ρ g (orbitEsymm ρ s i) = orbitEsymm ρ s i :=
  (map_multiset_esymm (ρ g) _ i).trans
    (congrArg (Multiset.esymm · i) (map_orbitMultiset ρ _ g))

omit [IsInvertibleModule X L] in
/-- A homogeneous element of degree `n` is its own degree-`n` component. -/
theorem of_apply_of_mem_homogeneousPart {n : ℕ} {y : sectionRing L}
    (hy : y ∈ homogeneousPart L n) : DirectSum.of _ n (y n) = y := by
  obtain ⟨u, rfl⟩ := mem_homogeneousPart.mp hy
  rw [DirectSum.of_eq_same]

omit [IsInvertibleModule X L] in
/-- The translates of a section of `L` under a degree-preserving action are sections of `L`. -/
theorem mem_homogeneousPart_of_mem_orbitMultiset (ρ : G →* RingAut (sectionRing L))
    (hρ : ∀ (g : G) (n : ℕ) (u : powSections L n), ∃ v, ρ g (DirectSum.of _ n u) =
      DirectSum.of _ n v)
    (s : powSections L 1) {y : sectionRing L} (hy : y ∈ orbitMultiset ρ (DirectSum.of _ 1 s)) :
    y ∈ homogeneousPart L 1 := by
  obtain ⟨g, -, rfl⟩ := Multiset.mem_map.mp hy
  obtain ⟨v, hv⟩ := hρ g 1 s
  exact mem_homogeneousPart.mpr ⟨v, hv.symm⟩

/-- `σ_i(s)` lies in the degree-`i` part of the section ring. -/
theorem orbitEsymm_mem_homogeneousPart (ρ : G →* RingAut (sectionRing L))
    (hρ : ∀ (g : G) (n : ℕ) (u : powSections L n), ∃ v, ρ g (DirectSum.of _ n u) =
      DirectSum.of _ n v)
    (s : powSections L 1) (i : ℕ) : orbitEsymm ρ s i ∈ homogeneousPart L i :=
  esymm_mem_homogeneousPart _ (fun _ hy => mem_homogeneousPart_of_mem_orbitMultiset ρ hρ s hy) i

/-- **`σ_i(s)` is homogeneous of degree `i`**: it is a section of `L^{⊗ i}`. -/
theorem of_orbitEsymm (ρ : G →* RingAut (sectionRing L))
    (hρ : ∀ (g : G) (n : ℕ) (u : powSections L n), ∃ v, ρ g (DirectSum.of _ n u) =
      DirectSum.of _ n v)
    (s : powSections L 1) (i : ℕ) :
    DirectSum.of _ i (orbitEsymm ρ s i i) = orbitEsymm ρ s i :=
  of_apply_of_mem_homogeneousPart (orbitEsymm_mem_homogeneousPart ρ hρ s i)

/-- **Vieta's formula at a root.** If `a ∈ M`, then
`a^{|M|} + ∑_{j < |M|} (-1)^{j+1} e_{j+1}(M) a^{|M|-(j+1)} = 0`. -/
theorem pow_card_add_sum_esymm_mul_pow_eq_zero {R : Type*} [CommRing R] {M : Multiset R} {a : R}
    (ha : a ∈ M) :
    a ^ Multiset.card M + ∑ j ∈ Finset.range (Multiset.card M), (-1) ^ (j + 1) *
      (M.esymm (j + 1) * a ^ (Multiset.card M - (j + 1))) = 0 := by
  have h := congrArg (Polynomial.eval a) (Multiset.prod_X_sub_X_eq_sum_esymm M)
  have h0 : (M.map fun t => a - t).prod = 0 :=
    Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨a, ha, sub_self a⟩)
  rw [Polynomial.eval_multiset_prod, Multiset.map_map] at h
  simp only [Function.comp_def, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h
  rw [h0, Finset.sum_range_succ'] at h
  simp only [Polynomial.eval_add, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_one, Polynomial.eval_C,
    Polynomial.eval_X, Multiset.esymm_zero, pow_zero, one_mul, Nat.sub_zero] at h
  rw [add_comm]
  exact h.symm

/-- **Vieta's formula for the orbit.** With `a = s` and `N = |G|`,
`a^N + ∑_{j < N} (-1)^{j+1} σ_{j+1}(s) a^{N-(j+1)} = 0`. -/
theorem pow_card_add_sum_orbitEsymm_eq_zero (ρ : G →* RingAut (sectionRing L))
    (s : powSections L 1) :
    DirectSum.of _ 1 s ^ Fintype.card G +
      ∑ j ∈ Finset.range (Fintype.card G), (-1) ^ (j + 1) *
        (orbitEsymm ρ s (j + 1) * DirectSum.of _ 1 s ^ (Fintype.card G - (j + 1))) = 0 := by
  have hmem : DirectSum.of _ 1 s ∈ orbitMultiset ρ (DirectSum.of _ 1 s) :=
    Multiset.mem_map.mpr ⟨1, Finset.mem_univ_val _, by simp⟩
  have h := pow_card_add_sum_esymm_mul_pow_eq_zero hmem
  rwa [card_orbitMultiset] at h

/-- **At a point where `s` does not vanish, some `σ_i(s)`, `1 ≤ i ≤ |G|`, does not vanish.** -/
theorem exists_orbitEsymm_mem_nonvanishingLocus (ρ : G →* RingAut (sectionRing L))
    (hρ : ∀ (g : G) (n : ℕ) (u : powSections L n), ∃ v, ρ g (DirectSum.of _ n u) =
      DirectSum.of _ n v)
    (s : powSections L 1) (x : X)
    (hx : x ∈ nonvanishingLocus (natTensorPow L 1) (globalSection X _ s)) :
    ∃ i ∈ Finset.Icc 1 (Fintype.card G),
      x ∈ nonvanishingLocus (natTensorPow L i) (globalSection X _ (orbitEsymm ρ s i i)) := by
  set N := Fintype.card G
  set a : sectionRing L := DirectSum.of _ 1 s
  by_contra hcon
  push Not at hcon
  have hpow : a ^ N ∈ nonvanishingPart x N := by
    rw [← nonvanishingPart_congr (one_mul N)]
    exact pow_mem_nonvanishingPart ⟨s, hx, rfl⟩ Fintype.card_pos
  refine notMem_vanishingPart_of_mem_nonvanishingPart hpow ?_
  rw [eq_neg_of_add_eq_zero_left (pow_card_add_sum_orbitEsymm_eq_zero ρ s)]
  refine neg_mem (AddSubgroup.sum_mem _ fun j hj => ?_)
  rw [Finset.mem_range] at hj
  have hterm : orbitEsymm ρ s (j + 1) * a ^ (N - (j + 1)) ∈ vanishingPart L x N := by
    rw [← vanishingPart_congr (show j + 1 + 1 * (N - (j + 1)) = N by omega)]
    exact mul_mem_vanishingPart
      (mem_vanishingPart.mpr ⟨_, hcon _ (Finset.mem_Icc.mpr (by omega)), of_orbitEsymm ρ hρ s _⟩)
      (pow_mem_homogeneousPart (mem_homogeneousPart.mpr ⟨s, rfl⟩) _)
  rcases neg_one_pow_eq_or (sectionRing L) (j + 1) with h | h
  · rwa [h, one_mul]
  · rw [h, neg_one_mul]
    exact neg_mem hterm

/-- `σ_i(s)^{N!/i}`, `N = |G|`: the degree-`N!` component of the `(N!/i)`-th power of
`σ_i(s)`, a section of `L^{⊗ N!}`. -/
def orbitInvariantSection (ρ : G →* RingAut (sectionRing L)) (s : powSections L 1) (i : ℕ) :
    powSections L (Fintype.card G).factorial :=
  (orbitEsymm ρ s i ^ ((Fintype.card G).factorial / i)) (Fintype.card G).factorial

/-- For `1 ≤ i ≤ |G|`, `orbitInvariantSection ρ s i` is `σ_i(s)^{N!/i}` itself. -/
theorem of_orbitInvariantSection (ρ : G →* RingAut (sectionRing L))
    (hρ : ∀ (g : G) (n : ℕ) (u : powSections L n), ∃ v, ρ g (DirectSum.of _ n u) =
      DirectSum.of _ n v)
    (s : powSections L 1) {i : ℕ} (hi : i ∈ Finset.Icc 1 (Fintype.card G)) :
    DirectSum.of _ (Fintype.card G).factorial (orbitInvariantSection ρ s i) =
      orbitEsymm ρ s i ^ ((Fintype.card G).factorial / i) := by
  refine of_apply_of_mem_homogeneousPart ?_
  rw [Finset.mem_Icc] at hi
  rw [← homogeneousPart_congr (Nat.mul_div_cancel' (Nat.dvd_factorial hi.1 hi.2))]
  exact pow_mem_homogeneousPart (orbitEsymm_mem_homogeneousPart ρ hρ s i) _

/-- **Finite orbit polynomials preserve generation.** Let `L` be an invertible module on a scheme
`X`, let a finite group `G` act on the section ring `Γ_*(X, L)` by graded ring automorphisms, and
let `W ⊆ Γ(X, L)` generate `L`. For `s ∈ W` and `1 ≤ i ≤ N = |G|`, the section
`orbitInvariantSection ρ s i` of `L^{⊗ N!}` is `σ_i(s)^{N!/i}`, where `σ_i(s)` is the `i`-th
elementary symmetric function of the translates of `s`, and it is `G`-invariant; and these
invariant sections generate `L^{⊗ N!}`. -/
@[mmp "lem_fourfold_finite_orbit_invariant_generation"]
theorem orbitInvariantSection_invariant_and_generates (ρ : G →* RingAut (sectionRing L))
    (hρ : ∀ (g : G) (n : ℕ) (u : powSections L n), ∃ v, ρ g (DirectSum.of _ n u) =
      DirectSum.of _ n v)
    (W : Set (powSections L 1))
    (hW : ∀ x : X, ∃ s ∈ W, x ∈ nonvanishingLocus (natTensorPow L 1) (globalSection X _ s)) :
    (∀ s ∈ W, ∀ i ∈ Finset.Icc 1 (Fintype.card G),
      DirectSum.of _ (Fintype.card G).factorial (orbitInvariantSection ρ s i) =
          orbitEsymm ρ s i ^ ((Fintype.card G).factorial / i) ∧
        ∀ g : G, ρ g (DirectSum.of _ (Fintype.card G).factorial (orbitInvariantSection ρ s i)) =
          DirectSum.of _ (Fintype.card G).factorial (orbitInvariantSection ρ s i)) ∧
    ∀ x : X, ∃ s ∈ W, ∃ i ∈ Finset.Icc 1 (Fintype.card G),
      x ∈ nonvanishingLocus (natTensorPow L (Fintype.card G).factorial)
        (globalSection X _ (orbitInvariantSection ρ s i)) := by
  set N := Fintype.card G
  have hdeg : ∀ i ∈ Finset.Icc 1 N, i * (N.factorial / i) = N.factorial := fun i hi => by
    simp only [Finset.mem_Icc] at hi
    exact Nat.mul_div_cancel' (Nat.dvd_factorial hi.1 hi.2)
  have hof := fun s i (hi : i ∈ Finset.Icc 1 N) => of_orbitInvariantSection ρ hρ s hi
  refine ⟨fun s _ i hi => ⟨hof s i hi, fun g => ?_⟩, fun x => ?_⟩
  · rw [hof s i hi, map_pow, orbitEsymm_invariant]
  · obtain ⟨s, hsW, hx⟩ := hW x
    obtain ⟨i, hi, hxi⟩ := exists_orbitEsymm_mem_nonvanishingLocus ρ hρ s x hx
    refine ⟨s, hsW, i, hi, ?_⟩
    have hk : 1 ≤ N.factorial / i := by
      simp only [Finset.mem_Icc] at hi
      exact Nat.one_le_div_iff (by omega) |>.mpr (Nat.le_of_dvd (Nat.factorial_pos _)
        (Nat.dvd_factorial hi.1 hi.2))
    have hmem := pow_mem_nonvanishingPart
      (⟨_, hxi, of_orbitEsymm ρ hρ s i⟩ : orbitEsymm ρ s i ∈ nonvanishingPart x i) hk
    rw [nonvanishingPart_congr (hdeg i hi), ← hof s i hi] at hmem
    obtain ⟨v, hv, he⟩ := hmem
    rwa [DirectSum.of_injective _ he] at hv

end MMP.Fourfold
