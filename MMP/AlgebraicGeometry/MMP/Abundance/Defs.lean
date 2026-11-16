/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.MMP.MinimalModel.LogCanonicalModelDefs
public import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlops
public import MMP.AlgebraicGeometry.MMP.Abundance.Basic
public import MMP.AlgebraicGeometry.Singularities.Semismooth.Defs
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
public import MMP.AlgebraicGeometry.Morphisms.Birational.Transform

/-!
# Log elliptic fiber spaces, the abundance assumptions, slc curves and normalized sections

The definitions of FA Chapter 15 (log elliptic fiber spaces, eventually free divisors, free
pencils, trivially connected divisors, `(K_X + Δ_X)`-trivial flops, the assumptions of FA 15.4
and the Chow closure of the proof of FA 15.10) and of FA 12.2.9 (slc curves, the boundaries
`Δᵢ` on the components of their normalization, the normalization datum for elliptic curves and
normalized sections on a smooth curve).

## Conventions

FA works over `ℂ` (Chapter 15: a field of characteristic zero); the definitions are stated over
a field `k` with structure morphisms `s_X : X ⟶ Spec k`, and specialize to FA's for `k = ℂ`.
Varieties are `MMP.Mori.IsVariety` (integral, separated, of finite type), `ℚ`-divisors on normal
varieties are `MMP.Mori.QDivisor`, and a canonical divisor `K_X` of a variety of dimension `n` is
a divisor with `MMP.Mori.Divisor.IsCanonicalDivisor s_X n K_X`; the log canonical divisor is
`K_X + Δ_X` (`MMP.Mori.Divisor.toQDivisor K_X + Δ_X`). The intersection number `L · C` of a
`ℚ`-Cartier `ℚ`-divisor with a proper irreducible curve `C` (`MMP.Mori.ProperCurve`) is
`MMP.Mori.QDivisor.intersectionNumber` along the inclusion of `C`. A point of a complex variety
in FA's sense is a closed point.

`ℚ`-factoriality (`def_mmp_q_factorial`) is declared in `MMP.Foundations.Fourfold.Program`,
which imports this part of the library; it is inlined here: every Weil divisor has a positive
multiple which is Cartier.

## Main definitions

* `MMP.Flips.genericFiberDegree`, `MMP.Flips.IsGenericFiberDegree`: `D · E_g` (FA 15.1.1).
* `MMP.Flips.IsLogEllipticFiberSpace`, `MMP.Flips.IsEllipticFiberSpace`: FA 15.1.1.
* `MMP.Flips.IsEventuallyFree`: eventually free `ℚ`-divisors (FA 15.4).
* `MMP.Flips.IsComposedOfFreePencil`, `MMP.Flips.IsEventuallyFreePencil`: FA 15.7.1.
* `MMP.Flips.SatisfiesAbundanceAssumptions`: the assumptions of FA 15.4.
* `MMP.Flips.IsTriviallyConnected`: `(K_X + Δ_X)`-trivially connected divisors (FA 15.6).
* `MMP.Flips.IsChowClosure`: the Chow closure `(Z₀, Z̄, Ū)` of the proof of FA 15.10.
* `MMP.Flips.IsTrivialFlopDatum`, `MMP.Flips.IsTrivialFlop`: `(K_X + Δ_X)`-trivial flops
  (FA 15.4.4, 15.9).
* `MMP.Flips.IsSlcCurve`, `MMP.Flips.IsSlcComponentBoundary`: slc curves and the `Δᵢ`
  (FA 12.2.9).
* `MMP.Flips.GenusOneCurve`, `MMP.Flips.EllipticNormalizationDatum`: FA 12.2.9.1.
* `MMP.Flips.IsNormalizedSection`: normalized sections on a smooth curve (FA 12.2.9, 12.2.9.1).

## Main results

The facts the source text asserts in passing about three of these definitions:
* `MMP.Flips.IsGenericFiberDegree.genericFiber_spec`: the generic fibre `V_η` is a proper
  regular curve over `k(W)`, meeting each prime divisor in a finite set of closed points
  (FA 15.1.1).
* `MMP.Flips.IsSlcCurve.smooth_normalization`, `MMP.Flips.IsSlcCurve.isConnected_and_smooth`:
  the components `Cᵢ` of the normalization of an slc curve are smooth and connected (FA 12.2.9).
* `MMP.Flips.IsFlop.isTrivialFlopDatum`, `MMP.Flips.IsHFlop.isTrivialFlopDatum`: flops and
  `H`-flops, with their flopping contractions, are trivial flop data (FA 15.4.4, 15.9).

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 12.2.9,
  12.2.9.1, 15.1.1, 15.4, 15.4.4, 15.6, 15.7.1, 15.9, 15.10
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Flips

open MMP.Mori

/-! ### The degree on the generic fiber -/

section GenericFiber

variable {V W : Scheme.{u}}

/-- The degree over `k(W)` of the restriction of a prime divisor `E` of `V` to the generic fiber
`V_η` of `g : V ⟶ W`: `E ∩ V_η` is empty unless `g` maps the generic point `ξ_E` of `E` to the
generic point `η` of `W`, and is then the closed point `ξ_E` of `V_η`, of degree
`[κ(ξ_E) : κ(η)]` over `κ(η) = k(W)`. -/
@[mmp "def_fa15_generic_fiber_degree"]
def genericFiberPointDegree [IrreducibleSpace W] (g : V ⟶ W) (E : Mori.PrimeDivisor V) : ℕ :=
  open Classical in
  if g E.genericPoint = genericPoint W then
    letI := (g.residueFieldMap E.genericPoint).hom.toAlgebra
    Module.finrank (W.residueField (g E.genericPoint)) (V.residueField E.genericPoint)
  else 0

/-- **Degree on the generic fiber** (used in FA 15.1.1). For a `ℚ`-Weil divisor
`D = ∑ dᵢ Dᵢ` on `V` and `g : V ⟶ W`, the degree `D · E_g = deg_{k(W)}(D|_{V_η})` of the
restriction `D|_{V_η} = ∑ dᵢ (Dᵢ ∩ V_η)` to the generic fiber `V_η = V ×_W Spec k(W)`.

The points of `V_η` are the points of `V` over the generic point `η` of `W`. `Dᵢ ∩ V_η` is empty
unless `g(Dᵢ)` is dense in `W`, that is, unless `g` maps the generic point `ξᵢ` of `Dᵢ` to `η`;
then (`dim Dᵢ = dim W`) it is the point `ξᵢ`, with multiplicity one (`Dᵢ` is reduced and `V_η` is
a localization of `V`), of degree `[κ(ξᵢ) : k(W)]`. So
`D · E_g = ∑ {dᵢ [κ(ξᵢ) : k(W)] | g(ξᵢ) = η}` (`MMP.Flips.genericFiberPointDegree`). -/
@[mmp "def_fa15_generic_fiber_degree"]
def genericFiberDegree [IrreducibleSpace W] (g : V ⟶ W) (D : QDivisor V) : ℚ :=
  ∑ E ∈ D.support, D.coeff E * genericFiberPointDegree g E

variable {k : Type u} [Field k] (sV : V ⟶ Spec (.of k)) (sW : W ⟶ Spec (.of k))

/-- **Degree on the generic fiber** (used in FA 15.1.1). Let `V` be a normal variety, `W` a
variety and `g : V ⟶ W` a proper surjective morphism with `dim V = dim W + 1`. For a `ℚ`-Weil
divisor `D` on `V`, the rational number `d` is the *degree of `D` on the generic fiber*,
`d = D · E_g = deg_{k(W)}(D|_{V_η})` (`MMP.Flips.genericFiberDegree`). The setting hypotheses
are part of the predicate. -/
@[mmp "def_fa15_generic_fiber_degree"]
def IsGenericFiberDegree (g : V ⟶ W) (D : QDivisor V) (d : ℚ) : Prop :=
  IsNormalVariety k sV ∧ g ≫ sW = sV ∧ IsProper g ∧ Surjective g ∧
    topologicalKrullDim V = topologicalKrullDim W + 1 ∧
    ∃ hW : Mori.IsVariety k sW,
      haveI := hW.toIsIntegral
      d = genericFiberDegree g D

/-- `Dᵢ ∩ V_η` is empty unless `g(Dᵢ)` is dense in `W` (FA 15.1.1, the aside of
`def_fa15_generic_fiber_degree`): if some point of `Dᵢ` lies over the generic point of `W`, then
`g(Dᵢ)` is dense. -/
@[mmp "def_fa15_generic_fiber_degree"]
theorem dense_image_support_of_mem_genericFiber [IrreducibleSpace W] (g : V ⟶ W)
    (E : Mori.PrimeDivisor V) (h : ∃ x ∈ (E.support : Set V), g x = genericPoint W) :
    Dense (g '' (E.support : Set V)) := by
  obtain ⟨x, hx, hgx⟩ := h
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro y
  have hy : y ∈ closure ({genericPoint W} : Set W) := by
    rw [(genericPoint_spec W).def]; trivial
  have hη : genericPoint W ∈ g '' (E.support : Set V) := ⟨x, hx, hgx⟩
  exact closure_mono (Set.singleton_subset_iff.mpr hη) hy

/-- **The generic fibre** (the asides of FA 15.1.1, `def_fa15_generic_fiber_degree`). In the
setting of `MMP.Flips.IsGenericFiberDegree` (`V` a normal variety, `W` a variety, `g` proper and
surjective over `k`, `dim V = dim W + 1`), the generic fibre `V_η = V ×_W Spec k(W)`, whose points
are the points of `V` over the generic point `η` of `W` and whose local rings are the local rings
of `V` there (it is a localization of `V`):
* is proper over `k(W) = κ(η)`;
* is a curve: it has dimension one;
* is regular: each of its local rings, a local ring of the normal `V`, is a regular local ring;
* meets each prime divisor `Dᵢ` of `V` at most in the generic point of `Dᵢ` (so `Dᵢ ∩ V_η` is
  empty unless `g(Dᵢ)` is dense, `MMP.Flips.dense_image_support_of_mem_genericFiber`), a finite
  set of closed points of `V_η`. -/
@[mmp "def_fa15_generic_fiber_degree"]
theorem IsGenericFiberDegree.genericFiber_spec [IsIntegral W] {g : V ⟶ W} {D : QDivisor V}
    {d : ℚ} (h : IsGenericFiberDegree sV sW g D d) :
    IsProper (g.fiberToSpecResidueField (genericPoint W)) ∧
      topologicalKrullDim (g.base ⁻¹' {genericPoint W}) = 1 ∧
      (∀ x : V, g x = genericPoint W → IsRegularLocalRing (V.presheaf.stalk x)) ∧
      ∀ E : Mori.PrimeDivisor V,
        {x | x ∈ (E.support : Set V) ∧ g x = genericPoint W} ⊆ {E.genericPoint} ∧
        {x | x ∈ (E.support : Set V) ∧ g x = genericPoint W}.Finite ∧
        ∀ x : V, x ∈ (E.support : Set V) → ∀ hx : g x = genericPoint W,
          IsClosed ({⟨x, hx⟩} : Set (g.base ⁻¹' {genericPoint W})) := by
  obtain ⟨⟨hV, hVn⟩, hg, hp, hs, hdim, hW, -⟩ := h
  have := hV.toIsIntegral
  have := hV.toLocallyOfFiniteType
  have := hW.toLocallyOfFiniteType
  have : CompactSpace W := by
    have := hW.toQuasiCompact
    exact QuasiCompact.compactSpace_of_compactSpace sW
  have hs' : Function.Surjective g := hs.surj
  refine ⟨isProper_fiberToSpecResidueField g _, ?_, fun x hx =>
    isRegularLocalRing_stalk_of_mem_genericFiber sV sW g hg hdim hx, fun E => ⟨fun x hx =>
    (eq_genericPoint_of_mem_support_of_mem_genericFiber sV sW g hg hs' hdim E hx.1 hx.2).1,
    finite_support_inter_genericFiber sV sW g hg hs' hdim E, fun x hxE hx =>
    isClosed_singleton_genericFiber sV sW g hg hs' hdim E hxE hx⟩⟩
  rw [← (g.fiberHomeo (genericPoint W)).isHomeomorph.topologicalKrullDim_eq]
  exact topologicalKrullDim_genericFiber_eq_one sV sW g hg hs' hdim

end GenericFiber

/-! ### Log elliptic fiber spaces -/

section LogElliptic

variable (k : Type u) [Field k] {V W : Scheme.{u}} (sV : V ⟶ Spec (.of k))
  (sW : W ⟶ Spec (.of k)) [IsLocallyNoetherian V] [IsNormal V]

/-- **Log elliptic fiber space** (FA Def. 15.1.1). Let `(V, Δ_V)` be a log variety
(`MMP.Flips.IsLogVariety`, with `Δ_V` a `ℚ`-divisor) such that `K_V + Δ_V` is `ℚ`-Cartier, `K_V`
a canonical divisor of the variety `V` of dimension `n`, and `W` a variety. A proper morphism
`g : (V, Δ_V) ⟶ W` is a *log elliptic fiber space* if `g_* 𝒪_V = 𝒪_W`, the generic fiber
`V_η =: E_g` of `g` is an irreducible curve, and `(K_V + Δ_V) · E_g = 0`
(`MMP.Flips.genericFiberDegree`).

`g` being a proper morphism of varieties over `k` with `g_* 𝒪_V = 𝒪_W` is
`MMP.Flips.IsContraction`. The underlying space of the generic fiber is the subspace
`g⁻¹(η)` of `V`, `η` the generic point of `W`; it is an irreducible curve when this subspace is
irreducible of dimension one. -/
@[mmp "def_fa15_log_elliptic_fiber_space"]
structure IsLogEllipticFiberSpace (n : ℕ) (K : Divisor V) (Δ : QDivisor V) (g : V ⟶ W) :
    Prop where
  /-- `(V, Δ_V)` is a log variety. -/
  isLogVariety : IsLogVariety k sV (QDivisor.toRDivisor Δ)
  /-- `K_V` is a canonical divisor of `V`, of dimension `n`. -/
  isCanonicalDivisor : K.IsCanonicalDivisor sV n
  /-- `K_V + Δ_V` is `ℚ`-Cartier. -/
  isQCartier : (Divisor.toQDivisor K + Δ).IsQCartier
  /-- `W` is a variety and `g` is a proper morphism over `k` with `g_* 𝒪_V = 𝒪_W`. -/
  isContraction : IsContraction k sW sV g
  /-- The generic fiber `E_g` is irreducible. -/
  isIrreducible_genericFiber :
    haveI := isContraction.isVariety_target.toIsIntegral
    IsIrreducible (g.base ⁻¹' {genericPoint W})
  /-- The generic fiber `E_g` is a curve. -/
  dim_genericFiber :
    haveI := isContraction.isVariety_target.toIsIntegral
    topologicalKrullDim (g.base ⁻¹' {genericPoint W}) = 1
  /-- `(K_V + Δ_V) · E_g = 0`. -/
  genericFiberDegree_eq_zero :
    haveI := isContraction.isVariety_target.toIsIntegral
    genericFiberDegree g (Divisor.toQDivisor K + Δ) = 0

/-- **Elliptic fiber space** (FA Def. 15.1.1): a log elliptic fiber space with `Δ_V = 0`. -/
@[mmp "def_fa15_log_elliptic_fiber_space"]
def IsEllipticFiberSpace (n : ℕ) (K : Divisor V) (g : V ⟶ W) : Prop :=
  IsLogEllipticFiberSpace k sV sW n K 0 g

end LogElliptic

/-! ### Eventually free divisors and free pencils -/

section Free

variable (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [IsLocallyNoetherian X] [IsNormal X]

/-- **Eventually free** (implicit in FA 15.4, 15.4.4, 15.7.1). Let `X` be a normal variety and
`L` a `ℚ`-Weil divisor on `X`. `L` is *eventually free* if there is an integer `m > 0` such that
`mL` is an integral Cartier divisor `M` and `𝒪_X(M)` is generated by its global sections: the
linear system `|M|` is base point free (`MMP.Mori.Divisor.IsBasepointFree`). -/
@[mmp "def_fa15_eventually_free"]
def IsEventuallyFree (L : QDivisor X) : Prop :=
  ∃ hX : IsNormalVariety k sX,
    haveI := hX.1.toIsIntegral
    haveI := hX.1.toQuasiCompact
    haveI := QuasiCompact.compactSpace_of_compactSpace sX
    ∃ m : ℕ, 0 < m ∧ ∃ M : Divisor X, Divisor.toQDivisor M = (m : ℤ) • L ∧ M.IsCartier ∧
      M.IsBasepointFree

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (globalSectionsModule) in
/-- **Composed of a free pencil** (implicit in FA 15.7.1, 15.9.1, 15.13). Let `X` be a normal
projective variety and `M` a Cartier divisor on `X`. The complete linear system `|M|` is
*composed of a free pencil* if `𝒪_X(M)` is generated by global sections and the image of the
morphism `φ_{|M|} : X ⟶ ℙ(H⁰(X, 𝒪_X(M))^∨)` is a curve.

`φ_{|M|}` is `MMP.Mori.linearSystemMap` for a basis `b` of `H⁰(X, 𝒪_X(M))`; it is defined on the
open set `MMP.Mori.linearSystemLocus` of the points at which some section generates `𝒪_X(M)`,
which is all of `X` when `𝒪_X(M)` is generated by global sections. Its image is
`MMP.Mori.linearSystemImage`, the reduced closure of `φ_{|M|}(X)`, irreducible since `X` is; it
is a curve when it has dimension one. Another basis changes `φ_{|M|}` by an automorphism of
`ℙᴺ`. -/
@[mmp "def_fa15_composed_of_free_pencil"]
def IsComposedOfFreePencil (M : Divisor X) : Prop :=
  ∃ (hX : Mori.IsProjectiveVariety k sX) (hM : M.IsCartier),
    haveI := hX.toQuasiCompact
    haveI := QuasiCompact.compactSpace_of_compactSpace sX
    letI : X.Over (Spec (.of k)) := ⟨sX⟩
    haveI := hM.isInvertibleModule_divisorialSheaf
    letI := globalSectionsModule k X M.divisorialSheaf
    ∃ (ι : Type u) (b : Module.Basis ι k Γ(M.divisorialSheaf, ⊤)),
      linearSystemLocus k M.divisorialSheaf b = ⊤ ∧
        topologicalKrullDim (linearSystemImage k M.divisorialSheaf b) = 1

/-- **Eventually free and composed of a pencil** (implicit in FA 15.7.1, 15.9.1, 15.13). A
`ℚ`-Weil divisor `L` on a normal projective variety `X` is *eventually free and composed of a
pencil* if there is `m > 0` with `mL` an (integral) Cartier divisor `M` and `|M|` composed of a
free pencil. -/
@[mmp "def_fa15_composed_of_free_pencil"]
def IsEventuallyFreePencil (L : QDivisor X) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ∃ M : Divisor X, Divisor.toQDivisor M = (m : ℤ) • L ∧
    IsComposedOfFreePencil k sX M

end Free

/-! ### The assumptions of FA 15.4 -/

section Assumptions

/-- Some positive integer multiple `N • Δ` of a `ℚ`-divisor `Δ` is the image of an integral
divisor. -/
theorem exists_pos_smul_eq_toQDivisor {X : Scheme.{u}} (Δ : QDivisor X) :
    ∃ N : ℕ, 0 < N ∧ ∃ G : Divisor X, Divisor.toQDivisor G = (N : ℤ) • Δ := by
  classical
  set N : ℕ := ∏ E ∈ Δ.support, (Δ.coeff E).den with hN
  refine ⟨N, Finset.prod_pos fun E _ => (Δ.coeff E).den_pos, ?_⟩
  have h : ((N : ℤ) • Δ) ∈ Set.range (Divisor.toQDivisor (X := X)) := by
    rw [QDivisor.mem_range_toQDivisor_iff]
    intro E
    by_cases hE : E ∈ Δ.support
    · obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun E => (Δ.coeff E).den) hE
      refine ⟨(c : ℤ) * (Δ.coeff E).num, ?_⟩
      change ((N : ℤ) • Δ) E = _
      rw [Finsupp.smul_apply, zsmul_eq_mul, hN, hc]
      have := Rat.mul_den_eq_num (Δ.coeff E)
      change _ * Δ.coeff E = _
      push_cast
      rw [← this]
      ring
    · refine ⟨0, ?_⟩
      change ((N : ℤ) • Δ) E = _
      rw [Finsupp.smul_apply, Finsupp.notMem_support_iff.mp hE, smul_zero, Int.cast_zero]
  exact h

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]

/-- On a `ℚ`-factorial variety (every Weil divisor has a positive Cartier multiple), `K + Δ` is
`ℚ`-Cartier for every divisor `K` and every `ℚ`-divisor `Δ`. -/
theorem isQCartier_add_of_forall_isCartier {K : Divisor X} {Δ : QDivisor X}
    (h : ∀ D : Divisor X, ∃ m : ℕ, 0 < m ∧ ((m : ℤ) • D).IsCartier) :
    (Divisor.toQDivisor K + Δ).IsQCartier := by
  obtain ⟨N, hN, G, hG⟩ := exists_pos_smul_eq_toQDivisor Δ
  obtain ⟨m, hm, hc⟩ := h ((N : ℤ) • K + G)
  refine ⟨(m : ℤ) * N, by positivity, (m : ℤ) • ((N : ℤ) • K + G), ?_, hc⟩
  simp only [map_zsmul, map_add, hG, mul_smul, smul_add]

variable (k) (sX : X ⟶ Spec (.of k)) [IsIntegral X] [CompactSpace X] [LocallyOfFiniteType sX]
  [QuasiCompact sX]

/-- **The assumptions of FA Thm. 15.4** (as used in FA 15.5, 15.7, 15.9, 15.10, 15.13). A pair
`(X, Δ_X)`, with `K_X` a canonical divisor of `X`, *satisfies the assumptions of 15.4* if `X` is a
projective `ℚ`-factorial threefold, `Δ_X` is a boundary `ℚ`-divisor, `(X, Δ_X)` is a klt log
variety, and:
* (15.4.1) `K_X + Δ_X` is nef;
* (15.4.2) `dim |m(K_X + Δ_X)| ≥ 1` for some integer `m > 0` with `m(K_X + Δ_X)` Cartier;
* (15.4.3) there are a nonempty open `U ⊆ X`, a variety `Z` and a proper morphism
  `f_U : (U, Δ_X|_U) ⟶ Z` which is a log elliptic fiber space.

`ℚ`-factoriality (`def_mmp_q_factorial`, declared in `MMP.Foundations.Fourfold.Program`, which
imports this file) is inlined: `X` is a normal variety and every Weil divisor `D` has a multiple
`mD`, `m > 0`, which is Cartier. `dim |M| = h⁰(X, 𝒪_X(M)) - 1`, so (15.4.2) reads
`h⁰(X, 𝒪_X(M)) ≥ 2` for the Cartier divisor `M = m(K_X + Δ_X)`. In (15.4.3) the restrictions
`K_X|_U` (a canonical divisor of `U`) and `Δ_X|_U` are `MMP.Mori.DivisorWithCoeffs.restrict`
along the open immersion `U ⟶ X`; that `f_U` is a proper morphism to a variety is part of
`MMP.Flips.IsLogEllipticFiberSpace`. -/
@[mmp "def_fa15_log_elliptic_abundance_hypotheses"]
structure SatisfiesAbundanceAssumptions (K : Divisor X) (Δ : QDivisor X) : Prop where
  /-- `X` is a projective variety. -/
  isProjectiveVariety : Mori.IsProjectiveVariety k sX
  /-- `X` is `ℚ`-factorial (`def_mmp_q_factorial`). -/
  isQFactorial : IsNormalVariety k sX ∧ ∀ D : Divisor X, ∃ m : ℕ, 0 < m ∧ ((m : ℤ) • D).IsCartier
  /-- `X` is a threefold. -/
  dim_eq : topologicalKrullDim X = 3
  /-- `Δ_X` is a boundary. -/
  isBoundary : IsBoundary (QDivisor.toRDivisor Δ)
  /-- `(X, Δ_X)` is a klt log variety, `K_X` a canonical divisor. -/
  isKawamataLogTerminal : IsKawamataLogTerminal sX 3 K (QDivisor.toRDivisor Δ)
  /-- (15.4.1) `K_X + Δ_X` is nef. -/
  isNef : (Divisor.toQDivisor K + Δ).IsNef k sX
  /-- (15.4.2) `dim |m(K_X + Δ_X)| ≥ 1` for some `m > 0` with `m(K_X + Δ_X)` Cartier. -/
  exists_two_le_h0 : ∃ m : ℕ, 0 < m ∧ ∃ M : Divisor X,
    Divisor.toQDivisor M = (m : ℤ) • (Divisor.toQDivisor K + Δ) ∧ M.IsCartier ∧ 2 ≤ M.h0 k sX
  /-- (15.4.3) A log elliptic fiber space `f_U : (U, Δ_X|_U) ⟶ Z` on a nonempty open `U`. -/
  exists_isLogEllipticFiberSpace : ∃ (U : X.Opens) (_ : (U : Set X).Nonempty) (Z : Scheme.{u})
    (sZ : Z ⟶ Spec (.of k)) (fU : U.toScheme ⟶ Z),
    IsLogEllipticFiberSpace k (U.ι ≫ sX) sZ 3 (DivisorWithCoeffs.restrict U.ι K)
      (DivisorWithCoeffs.restrict U.ι Δ) fU

/-- Under the assumptions of FA 15.4, `K_X + Δ_X` is `ℚ`-Cartier (`X` is `ℚ`-factorial). -/
theorem SatisfiesAbundanceAssumptions.isQCartier {K : Divisor X} {Δ : QDivisor X}
    (h : SatisfiesAbundanceAssumptions k sX K Δ) : (Divisor.toQDivisor K + Δ).IsQCartier :=
  isQCartier_add_of_forall_isCartier h.isQFactorial.2

end Assumptions

/-! ### Trivially connected divisors -/

section TriviallyConnected

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- The union `C₁ ∪ ⋯ ∪ C_r` of finitely many proper irreducible curves `Cᵢ ⊆ X`: a proper curve
`C ⊆ X` (reduced, of pure dimension one) is the union of its irreducible components. -/
def curveUnion (S : Finset (ProperCurve sX)) : Set X :=
  ⋃ C ∈ S, closure {C.point}

/-- A point lies in `curveUnion sX S` iff it lies in the closure of the generic point of some
curve in `S`. -/
@[simp]
theorem mem_curveUnion {S : Finset (ProperCurve sX)} {x : X} :
    x ∈ curveUnion sX S ↔ ∃ C ∈ S, x ∈ closure {C.point} := by
  simp [curveUnion]

variable (k) [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]

/-- **`(K_X + Δ_X)`-trivially connected** (FA Def. 15.6). Let `X` be a normal proper variety of
dimension `n` with canonical divisor `K_X`, and `Δ_X` a `ℚ`-divisor with `K_X + Δ_X`
`ℚ`-Cartier. An effective divisor `D` on `X` is *`(K_X + Δ_X)`-trivially connected* if for any
two points `x₁, x₂ ∈ Supp D` there is a connected proper curve `C ⊆ Supp D` with `x₁, x₂ ∈ C`
such that `(K_X + Δ_X) · Cᵢ = 0` for every irreducible component `Cᵢ` of `C`.

Points are closed points (FA works with complex varieties). The curve `C` is given by its
irreducible components, a nonempty finite set `S` of proper irreducible curves
(`MMP.Mori.ProperCurve`), with `C = ⋃_{Cᵢ ∈ S} Cᵢ` (`MMP.Flips.curveUnion`). -/
@[mmp "def_fa15_trivially_connected"]
def IsTriviallyConnected (n : ℕ) (K : Divisor X) (Δ : QDivisor X) (D : Divisor X) : Prop :=
  IsNormalVariety k sX ∧ IsProper sX ∧ K.IsCanonicalDivisor sX n ∧
    ∃ hL : (Divisor.toQDivisor K + Δ).IsQCartier, D.IsEffective ∧
      ∀ x₁ ∈ (D.supp : Set X), ∀ x₂ ∈ (D.supp : Set X), IsClosed {x₁} → IsClosed {x₂} →
        ∃ S : Finset (ProperCurve sX), _root_.IsConnected (curveUnion sX S) ∧
          curveUnion sX S ⊆ D.supp ∧ x₁ ∈ curveUnion sX S ∧ x₂ ∈ curveUnion sX S ∧
          ∀ C ∈ S, (Divisor.toQDivisor K + Δ).intersectionNumber k sX C.ι C.dim_le hL = 0

end TriviallyConnected

/-! ### The Chow closure of the elliptic fibration -/

section ChowClosure

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {U : X.Opens}
  {Z Zbar : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)} {sZbar : Zbar ⟶ Spec (.of k)}

/-- The compatibility over `k` making `x ↦ (f_U(x), x)` a morphism to `Z̄ ×_k X`, for
`f_U : U ⟶ Z` over `k` and an open immersion `j : Z₀ ⟶ Z̄` over `k`. -/
theorem chowGraph_condition {fU : U.toScheme ⟶ Z} {Z₀ : Z.Opens} {j : Z₀.toScheme ⟶ Zbar}
    (hf : fU ≫ sZ = U.ι ≫ sX) (hj : j ≫ sZbar = Z₀.ι ≫ sZ) :
    ((fU ∣_ Z₀) ≫ j) ≫ sZbar = ((fU ⁻¹ᵁ Z₀).ι ≫ U.ι) ≫ sX := by
  rw [Category.assoc, hj, ← Category.assoc, morphismRestrict_ι, Category.assoc, hf,
    Category.assoc]

/-- The graph morphism `f_U⁻¹(Z₀) ⟶ Z̄ ×_k X`, `x ↦ (f_U(x), x)`, with `Z₀ ⊆ Z̄` through `j`. -/
def chowGraph {fU : U.toScheme ⟶ Z} {Z₀ : Z.Opens} {j : Z₀.toScheme ⟶ Zbar}
    (hf : fU ≫ sZ = U.ι ≫ sX) (hj : j ≫ sZbar = Z₀.ι ≫ sZ) :
    (fU ⁻¹ᵁ Z₀).toScheme ⟶ pullback sZbar sX :=
  pullback.lift ((fU ∣_ Z₀) ≫ j) ((fU ⁻¹ᵁ Z₀).ι ≫ U.ι) (chowGraph_condition hf hj)

variable (k sX) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [LocallyOfFiniteType sX] [QuasiCompact sX]

/-- **Chow closure** (FA proof of 15.10: `Z̄`, `Ū`, `g`, `u`). Let `(X, Δ_X)` satisfy the
assumptions of 15.4, with `f_U : U ⟶ Z` as in (15.4.3), and `L = K_X + Δ_X`. A *Chow closure*
of `f_U` is a tuple `(Z₀, Z̄, Ū)` where `Z₀ ⊆ Z` is a nonempty open subset, `Z̄` is a normal
projective variety containing `Z₀` as an open subset, and `Ū ⊆ Z̄ × X` is a closed subvariety
(integral), with projections `g : Ū ⟶ Z̄` and `u : Ū ⟶ X`, such that:
* (i) `g⁻¹(Z₀) = {(f_U(x), x) : x ∈ f_U⁻¹(Z₀)}` (as reduced schemes);
* (ii) every fiber of `g` is connected and of pure dimension one;
* (iii) for every closed `z̄ ∈ Z̄`, every irreducible curve contained in `u(g⁻¹(z̄))` is
  `L`-trivial;
* (iv) for every proper curve `Γ ⊂ X`, only finitely many `z̄ ∈ Z̄` satisfy `u(g⁻¹(z̄)) ⊆ Γ`.

`Z₀ ⊆ Z̄` is an open immersion `j : Z₀ ⟶ Z̄` over `k`; `Z̄ × X` is the fiber product over
`Spec k`, and `Ū` is given by its ideal sheaf. In (i) both sides are reduced locally closed
subschemes of `Z̄ × X` (`g⁻¹(Z₀)` is open in the integral `Ū`), so they are equal when their
underlying sets are: the image in `Z̄ × X` of `g⁻¹(j(Z₀))` is the image of the graph morphism
`MMP.Flips.chowGraph`. The fibers in (ii) are the subspaces `g⁻¹(z̄)`, for all points `z̄`; pure
dimension one means every irreducible component has dimension one. `L · C` is defined since `L`
is `ℚ`-Cartier (`MMP.Flips.SatisfiesAbundanceAssumptions.isQCartier`). A proper curve `Γ` in (iv)
is a union of finitely many proper irreducible curves (`MMP.Flips.curveUnion`). -/
@[mmp "def_fa15_chow_closure_family"]
structure IsChowClosure (K : Divisor X) (Δ : QDivisor X) (fU : U.toScheme ⟶ Z) (Z₀ : Z.Opens)
    (j : Z₀.toScheme ⟶ Zbar) (Ubar : (pullback sZbar sX).IdealSheafData) : Prop where
  /-- `(X, Δ_X)` satisfies the assumptions of 15.4. -/
  satisfiesAbundanceAssumptions : SatisfiesAbundanceAssumptions k sX K Δ
  /-- `f_U : (U, Δ_X|_U) ⟶ Z` is a log elliptic fiber space, as in (15.4.3). -/
  isLogEllipticFiberSpace : IsLogEllipticFiberSpace k (U.ι ≫ sX) sZ 3
    (DivisorWithCoeffs.restrict U.ι K) (DivisorWithCoeffs.restrict U.ι Δ) fU
  /-- `U` is nonempty, as in (15.4.3). -/
  nonempty_U : (U : Set X).Nonempty
  /-- `Z₀` is nonempty. -/
  nonempty : (Z₀ : Set Z).Nonempty
  /-- `Z̄` is a normal variety. -/
  isNormalVariety : IsNormalVariety k sZbar
  /-- `Z̄` is projective. -/
  isProjectiveVariety : Mori.IsProjectiveVariety k sZbar
  /-- `Z₀` is an open subset of `Z̄`. -/
  isOpenImmersion : IsOpenImmersion j
  /-- The inclusion `Z₀ ⊆ Z̄` is over `k`. -/
  comp_eq : j ≫ sZbar = Z₀.ι ≫ sZ
  /-- `Ū` is integral. -/
  isIntegral : IsIntegral Ubar.subscheme
  /-- (i) `g⁻¹(Z₀) = {(f_U(x), x) : x ∈ f_U⁻¹(Z₀)}`. -/
  image_preimage_eq : Ubar.subschemeι.base ''
      ((Ubar.subschemeι ≫ pullback.fst sZbar sX).base ⁻¹' Set.range j.base) =
    Set.range (chowGraph isLogEllipticFiberSpace.isContraction.comp_eq comp_eq).base
  /-- (ii) Every fiber of `g` is connected. -/
  isConnected_fiber : ∀ z : Zbar,
    _root_.IsConnected ((Ubar.subschemeι ≫ pullback.fst sZbar sX).base ⁻¹' {z})
  /-- (ii) Every fiber of `g` is of pure dimension one. -/
  dim_fiber : ∀ z : Zbar,
    ∀ Y ∈ irreducibleComponents ((Ubar.subschemeι ≫ pullback.fst sZbar sX).base ⁻¹' {z}),
      topologicalKrullDim Y = 1
  /-- (iii) Every irreducible curve in `u(g⁻¹(z̄))`, `z̄` closed, is `L`-trivial. -/
  intersectionNumber_eq_zero : ∀ z : Zbar, IsClosed {z} → ∀ C : ProperCurve sX,
    closure {C.point} ⊆ (Ubar.subschemeι ≫ pullback.snd sZbar sX).base ''
      ((Ubar.subschemeι ≫ pullback.fst sZbar sX).base ⁻¹' {z}) →
    (Divisor.toQDivisor K + Δ).intersectionNumber k sX C.ι C.dim_le
      satisfiesAbundanceAssumptions.isQCartier = 0
  /-- (iv) Only finitely many closed `z̄` have `u(g⁻¹(z̄))` inside a given proper curve. -/
  finite : ∀ S : Finset (ProperCurve sX), S.Nonempty →
    {z : Zbar | IsClosed {z} ∧ (Ubar.subschemeι ≫ pullback.snd sZbar sX).base ''
      ((Ubar.subschemeι ≫ pullback.fst sZbar sX).base ⁻¹' {z}) ⊆ curveUnion sX S}.Finite

end ChowClosure

/-! ### `(K_X + Δ_X)`-trivial flops -/

section Flop

variable (k : Type u) [Field k] {X Y T : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (sY : Y ⟶ Spec (.of k)) (sT : T ⟶ Spec (.of k))

/-- A morphism `f : Y ⟶ X` is an *isomorphism in codimension one*: there are closed subsets
`V ⊆ Y` and `W ⊆ X` of codimension `≥ 2` such that `f` restricts to an isomorphism
`Y ∖ V ⟶ X ∖ W` (the condition of `MMP.Flips.IsSmall`). -/
@[mmp "def_fa15_trivial_flop_datum"]
def IsIsoInCodimOne (f : Y ⟶ X) : Prop :=
  ∃ (V : Closeds Y) (W : Closeds X), 2 ≤ closedsCodimension V ∧ 2 ≤ closedsCodimension W ∧
    ∃ h : V.compl ≤ f ⁻¹ᵁ W.compl, IsIso (f.resLE W.compl V.compl h)

variable [IsLocallyNoetherian X] [IsNormal X]

/-- **`(K_X + Δ_X)`-trivial flop datum** (the flops of FA 15.4.4 and 15.9; FA 2.26.5.1, 6.8).
Let `(X, Δ_X)` be a log variety with `Δ_X` a `ℚ`-divisor and `K_X + Δ_X` `ℚ`-Cartier, `K_X` a
canonical divisor of `X` of dimension `n`. A *`(K_X + Δ_X)`-trivial flop datum* is a pair of small
proper birational morphisms `φ : X ⟶ T`, `φ⁺ : Y ⟶ T` with `T`, `Y` normal varieties and
`φ_* 𝒪_X = 𝒪_T`, such that `(K_X + Δ_X) · C = 0` for every proper curve `C ⊂ X` with `φ(C)` a
point.

Since `φ_* 𝒪_X = 𝒪_T`, `φ` is a small birational contraction (`MMP.Flips.IsSmall`, which records
that `X` and `T` are varieties, `φ` is proper over `k` and an isomorphism in codimension one). For
`φ⁺`, small means an isomorphism in codimension one (`MMP.Flips.IsIsoInCodimOne`). The condition
`(K_X + Δ_X) · C = 0` for the proper curves `C` contracted by `φ` is FA's: `K_X + Δ_X`, as an
`ℝ`-Cartier divisor, is numerically `φ`-trivial (`MMP.Flips.IsNumericallyTrivialOver`, with the
intersection numbers `MMP.Flips.IsRIntersectionNumber` of FA 2.x used by the flops of FA 2.26.5.1
and 6.8).

A `(K_X + Δ_X)`-flop in the sense of FA 2.26.5.1 (`MMP.Flips.IsFlop`, with `Δ_X = 0`) and an
`H`-flop with respect to `K_X + Δ_X` (`MMP.Flips.IsHFlop`), with their flopping contractions, are
such data (`MMP.Flips.IsFlop.isTrivialFlopDatum`, `MMP.Flips.IsHFlop.isTrivialFlopDatum`). -/
@[mmp "def_fa15_trivial_flop_datum"]
structure IsTrivialFlopDatum (n : ℕ) (K : Divisor X) (Δ : QDivisor X) (φ : X ⟶ T)
    (φp : Y ⟶ T) : Prop where
  /-- `(X, Δ_X)` is a log variety. -/
  isLogVariety : IsLogVariety k sX (QDivisor.toRDivisor Δ)
  /-- `K_X` is a canonical divisor of `X`, of dimension `n`. -/
  isCanonicalDivisor : K.IsCanonicalDivisor sX n
  /-- `K_X + Δ_X` is `ℚ`-Cartier. -/
  isQCartier : (Divisor.toQDivisor K + Δ).IsQCartier
  /-- `φ` is a small proper birational morphism with `φ_* 𝒪_X = 𝒪_T`. -/
  isSmall : IsSmall k sT sX φ
  /-- `φ` is birational. -/
  isBirationalMorphism : IsBirationalMorphism φ
  /-- `T` is normal. -/
  isNormal_target : IsNormal T
  /-- `Y` is a normal variety. -/
  isNormalVariety_flop : IsNormalVariety k sY
  /-- `φ⁺` is a morphism over `k`. -/
  comp_eq_flop : φp ≫ sT = sY
  /-- `φ⁺` is proper. -/
  isProper_flop : IsProper φp
  /-- `φ⁺` is birational. -/
  isBirationalMorphism_flop : IsBirationalMorphism φp
  /-- `φ⁺` is small. -/
  isIsoInCodimOne_flop : IsIsoInCodimOne φp
  /-- `(K_X + Δ_X) · C = 0` for every proper curve `C` with `φ(C)` a point: `K_X + Δ_X` is
  numerically `φ`-trivial. -/
  isNumericallyTrivialOver :
    haveI := isSmall.isVariety_source.toQuasiCompact
    IsNumericallyTrivialOver k sX φ (QDivisor.toRDivisor (Divisor.toQDivisor K + Δ))

/-- **The flop of a `(K_X + Δ_X)`-trivial flop datum** (FA 15.4.4, 15.9). The flop of
`(φ, φ⁺)` is the birational map `p = (φ⁺)⁻¹ ∘ φ : X ⤏ Y`: the map with `φ⁺ ∘ p = φ`
(`MMP.Flips.RationalMap.IsOver`), which determines `p` since `φ⁺` is birational. -/
@[mmp "def_fa15_trivial_flop_datum"]
def IsTrivialFlop (n : ℕ) (K : Divisor X) (Δ : QDivisor X) (φ : X ⟶ T) (φp : Y ⟶ T)
    (p : X.RationalMap Y) : Prop :=
  IsTrivialFlopDatum k sX sY sT n K Δ φ φp ∧ RationalMap.IsOver φ φp p

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- The boundary `Δ_Y := p_* Δ_X` on the target of the flop `p : X ⤏ Y` (FA 15.4.4): the
birational transform `MMP.Mori.RationalMap.transformDivisor`. -/
@[mmp "def_fa15_trivial_flop_datum"]
def flopDivisor (p : X.RationalMap Y) (Δ : QDivisor X) : QDivisor Y :=
  Mori.RationalMap.transformDivisor p Δ

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- The boundary `Δ_T := φ_* Δ_X` on the base `T` of a flop datum (FA 15.4.4): the birational
transform along `φ`. -/
@[mmp "def_fa15_trivial_flop_datum"]
def flopBaseDivisor (φ : X ⟶ T) (Δ : QDivisor X) : QDivisor T :=
  Mori.RationalMap.transformDivisor φ.toRationalMap Δ

/-- **A flop is a trivial flop datum** (FA 15.4.4, the parenthetical of
`def_fa15_trivial_flop_datum`). An `E`-flop `φ⁺ : Y ⟶ T` of `φ : X ⟶ T` in the sense of
FA 2.26.5.1 (`MMP.Flips.IsFlop`: a flip with respect to `E` with `K_X` `ℝ`-Cartier and numerically
`φ`-trivial), with its flopping contraction `φ`, is a `K_X`-trivial flop datum (`Δ_X = 0`): `K_X`
is `ℚ`-Cartier, being an `ℝ`-Cartier integral divisor, and the small contractions `φ`, `φ⁺` are
birational. -/
@[mmp "def_fa15_trivial_flop_datum"]
theorem IsFlop.isTrivialFlopDatum [CompactSpace X] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] [QuasiCompact sX] {n : ℕ} {K : Divisor X} {E : RDivisor X} {φ : X ⟶ T}
    {φp : Y ⟶ T} {p : X.RationalMap Y} (h : IsFlop k sX sT sY n K E φ φp p) :
    IsTrivialFlopDatum k sX sY sT n K 0 φ φp := by
  obtain ⟨hK, hKC, hnum, hflip⟩ := h
  have hR : QDivisor.toRDivisor (Divisor.toQDivisor K + 0) = Divisor.toRDivisor K := by
    rw [add_zero, QDivisor.toRDivisor_toQDivisor]
  exact
    { isLogVariety := ⟨hflip.isNormalVariety_source, fun _ => by simp⟩
      isCanonicalDivisor := hK
      isQCartier := QDivisor.isQCartier_of_isCartierCombination (by rw [hR]; exact hKC)
      isSmall := hflip.isSmall_source
      isBirationalMorphism := IsSmall.isBirationalMorphism sT sX hflip.isSmall_source
      isNormal_target := hflip.isNormalVariety_target.2
      isNormalVariety_flop := hflip.isNormalVariety_flip
      comp_eq_flop := hflip.isSmall.comp_eq
      isProper_flop := hflip.isProper
      isBirationalMorphism_flop := IsSmall.isBirationalMorphism sT sY hflip.isSmall
      isIsoInCodimOne_flop := hflip.isSmall.exists_isIso
      isNumericallyTrivialOver := by rw [hR]; exact hnum }

/-- **An `H`-flop is a trivial flop datum** (FA 15.9, the parenthetical of
`def_fa15_trivial_flop_datum`). An `H`-flop `φ⁺ : Y ⟶ T` of `φ : X ⟶ T` with respect to `K_X + B`
(`MMP.Flips.IsHFlop`), with `B = Δ_X` a `ℚ`-divisor, is, with its flopping contraction `φ`, a
`(K_X + Δ_X)`-trivial flop datum: `(X, Δ_X)` is lc, hence a log variety with `K_X + Δ_X`
`ℝ`-Cartier, hence `ℚ`-Cartier; `K_X + Δ_X` is numerically `φ`-trivial; and the small contractions
`φ`, `φ⁺` are birational. -/
@[mmp "def_fa15_trivial_flop_datum"]
theorem IsHFlop.isTrivialFlopDatum [IsIntegral X] [CompactSpace X] [LocallyOfFiniteType sX]
    [QuasiCompact sX] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {n : ℕ}
    {K : Divisor X} {Δ : QDivisor X} {H : QDivisor X} {φ : X ⟶ T} {φp : Y ⟶ T}
    {p : X.RationalMap Y} (h : IsHFlop k sX sT sY n K (QDivisor.toRDivisor Δ) H φ φp p) :
    IsTrivialFlopDatum k sX sY sT n K Δ φ φp := by
  obtain ⟨⟨hlog, hK, hKC, -⟩, -, hsmall, hnum, -, hflip⟩ := h
  have hR : QDivisor.toRDivisor (Divisor.toQDivisor K + Δ) =
      logCanonicalDivisor K (QDivisor.toRDivisor Δ) := by
    rw [map_add, QDivisor.toRDivisor_toQDivisor]
    rfl
  exact
    { isLogVariety := hlog
      isCanonicalDivisor := hK
      isQCartier := QDivisor.isQCartier_of_isCartierCombination (by rw [hR]; exact hKC)
      isSmall := hsmall
      isBirationalMorphism := IsSmall.isBirationalMorphism sT sX hsmall
      isNormal_target := hflip.isNormalVariety_target.2
      isNormalVariety_flop := hflip.isNormalVariety_flip
      comp_eq_flop := hflip.isSmall.comp_eq
      isProper_flop := hflip.isProper
      isBirationalMorphism_flop := IsSmall.isBirationalMorphism sT sY hflip.isSmall
      isIsoInCodimOne_flop := hflip.isSmall.exists_isIso
      isNumericallyTrivialOver := by rw [hR]; exact hnum }

end Flop

/-! ### Semi log canonical curves -/

section SlcCurve

variable {k : Type u} [Field k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k))

/-- **Semi log canonical curve** (FA Def. 12.2.9). An *slc curve* is a pair `(C, Δ)` of a curve
`C` every singular closed point of which is a double normal crossing point (a node) and a
boundary `Δ` on `C`.

A curve is a `1`-fold in the conventions of FA Chapter 12 (`MMP.Flips.IsNFold`: reduced,
separated, of finite type and of pure dimension one); a singular point is a point outside the
smooth locus `MMP.Mori.smoothLocus`; the boundary is `MMP.Flips.QWeilDivisor.IsBoundary`. The
normalization `n : C̄ = ⨆ᵢ Cᵢ ⟶ C` of an slc curve is `MMP.Flips.slcCurveNormalization`, and the
`Cᵢ` are the connected components of `C̄`. -/
@[mmp "def_fa12a_slc_curve"]
def IsSlcCurve (Δ : QWeilDivisor C) : Prop :=
  IsNFold sC 1 ∧
    (∀ x : C, IsClosed {x} → x ∉ smoothLocus sC → IsDoubleNormalCrossingPoint sC 1 x) ∧
    Δ.IsBoundary sC

variable (C) in
/-- The normalization `n : C̄ ⟶ C` of an slc curve (FA Def. 12.2.9):
`Stacks.AlgebraicGeometry.Normalization.normalization`, the relative normalization of `C` in
`⨿_η Spec κ(η)` over its generic points; `hC` (finitely many irreducible components on
quasi-compact opens) holds for the Noetherian `C`. The components `Cᵢ` of `C̄ = ⨆ᵢ Cᵢ` are its
connected components. -/
abbrev slcCurveNormalization
    (hC : ∀ U : C.Opens, IsCompact (U : Set C) → (irreducibleComponents U).Finite) :
    Stacks.AlgebraicGeometry.Normalization.normalizationScheme C hC ⟶ C :=
  Stacks.AlgebraicGeometry.Normalization.normalization C hC

/-- **The normalization of an slc curve is smooth** (FA 12.2.9, the aside of
`def_fa12a_slc_curve`). Over a perfect field `k` (FA: `ℂ`), the normalization `C̄ = ⨆ᵢ Cᵢ` of an
slc curve `C` is smooth over `k`: it is normal of dimension at most one, hence regular, and
regular schemes locally of finite type over a perfect field are smooth. -/
@[mmp "def_fa12a_slc_curve"]
theorem IsSlcCurve.smooth_normalization [PerfectField k] {Δ : QWeilDivisor C} (h : IsSlcCurve sC Δ)
    (hC : ∀ U : C.Opens, IsCompact (U : Set C) → (irreducibleComponents U).Finite) :
    Smooth (slcCurveNormalization C hC ≫ sC) := by
  obtain ⟨⟨hft, -, hdim⟩, -, -⟩ := h
  have : LocallyOfFiniteType sC := hft.2.1
  exact smooth_normalization_comp_of_dim_le_one sC (fun Z hZ => (hdim Z hZ).le) hC

/-- **The components `Cᵢ` of the normalization of an slc curve are smooth and connected**
(FA 12.2.9, the aside of `def_fa12a_slc_curve`): the connected component `Cᵢ` of a point `c` of
`C̄` is connected, and every open subscheme of `C̄` (such as a component `Cᵢ`, open in the
locally Noetherian `C̄`) is smooth over the perfect field `k`. -/
@[mmp "def_fa12a_slc_curve"]
theorem IsSlcCurve.isConnected_and_smooth [PerfectField k] {Δ : QWeilDivisor C}
    (h : IsSlcCurve sC Δ)
    (hC : ∀ U : C.Opens, IsCompact (U : Set C) → (irreducibleComponents U).Finite)
    (c : Stacks.AlgebraicGeometry.Normalization.normalizationScheme C hC)
    (U : (Stacks.AlgebraicGeometry.Normalization.normalizationScheme C hC).Opens)
    (hU : (U : Set (Stacks.AlgebraicGeometry.Normalization.normalizationScheme C hC)) =
      connectedComponent c) :
    _root_.IsConnected (U : Set (Stacks.AlgebraicGeometry.Normalization.normalizationScheme C hC)) ∧
      Smooth (U.ι ≫ slcCurveNormalization C hC ≫ sC) := by
  have := h.smooth_normalization sC hC
  exact ⟨hU ▸ isConnected_connectedComponent, inferInstance⟩

open scoped Classical in
/-- **The boundaries `Δᵢ`** (FA Def. 12.2.9). For an slc curve `(C, Δ)` with normalization
`n : C̄ = ⨆ᵢ Cᵢ ⟶ C`, `Δᵢ := n^*Δ|_{Cᵢ} + ∑_P P`, the sum over the points `P ∈ Cᵢ` with `n(P)` a
node of `C`.

The component `Cᵢ` is the connected component of a point `c` of `C̄`, and `Δᵢ` is recorded as a
`ℚ`-Weil divisor `Δc` on `C̄` supported on `Cᵢ` (prime Weil divisors of `C̄` are its points of
codimension one, the closed points of the curve `C̄`), characterized by its coefficients. The
normalization is an isomorphism over the smooth locus of `C`, where `n^*Δ` is the pull-back of
`Δ`; over the nodes `n^*Δ` is read as the strict transform, as in the boundary `Θ = n⁻¹_*Δ + D_n`
of FA 12.2.2 (`MMP.Flips.IsBoundaryOfNormalization`): the coefficient of `P` in `Δᵢ` is `1` if
`n(P)` is a node, and otherwise the coefficient of `n(P)` in `Δ`. This is `n^*Δ|_{Cᵢ} + ∑_P P`
when the support of `Δ` consists of smooth points, and it keeps `Δᵢ` a boundary. The hypothesis
that `(C, Δ)` is an slc curve is part of the predicate. -/
@[mmp "def_fa12a_slc_curve_component_boundary"]
def IsSlcComponentBoundary
    (hC : ∀ U : C.Opens, IsCompact (U : Set C) → (irreducibleComponents U).Finite)
    (Δ : QWeilDivisor C) (c : Stacks.AlgebraicGeometry.Normalization.normalizationScheme C hC)
    (Δc : QWeilDivisor (Stacks.AlgebraicGeometry.Normalization.normalizationScheme C hC)) : Prop :=
  IsSlcCurve sC Δ ∧
    ∀ P : WeilDivisorPrime (Stacks.AlgebraicGeometry.Normalization.normalizationScheme C hC),
      Δc P =
        if P.1.genericPoint ∈ connectedComponent c then
          (if IsDoubleNormalCrossingPoint sC 1 (slcCurveNormalization C hC P.1.genericPoint)
            then 1
            else ∑ Γ ∈ Δ.support,
              if slcCurveNormalization C hC P.1.genericPoint = Γ.1.genericPoint then Δ Γ else 0)
        else 0

end SlcCurve

/-! ### Normalized sections on a smooth curve -/

section NormalizedSections

variable (k : Type u) [Field k]

/-- A *smooth proper curve of genus `1`* over `k`: a smooth proper normal variety `X` of
dimension one (`X` is integral, hence connected) whose genus `h⁰(X, 𝒪_X(K_X))` is `1`, for a
canonical divisor `K_X` (all canonical divisors are linearly equivalent, so `h⁰` does not depend
on the choice). -/
structure GenusOneCurve where
  /-- The curve. -/
  X : Scheme.{u}
  /-- The structure morphism. -/
  s : X ⟶ Spec (.of k)
  /-- `X` is a normal variety over `k`. -/
  isNormalVariety : IsNormalVariety k s
  /-- `X` is smooth over `k`. -/
  isSmoothScheme : IsSmoothScheme s
  /-- `X` is proper over `k`. -/
  isProper : IsProper s
  /-- `X` has dimension one. -/
  dim_eq : topologicalKrullDim X = 1
  /-- Some canonical divisor `K_X` of `X` satisfies `h⁰(X, 𝒪_X(K_X)) = 1`. -/
  exists_h0_eq_one :
    haveI := isNormalVariety.1.toLocallyOfFiniteType
    haveI := LocallyOfFiniteType.isLocallyNoetherian s
    haveI := isNormalVariety.2
    ∃ K : Divisor X, K.IsCanonicalDivisor s 1 ∧ K.h0 k s = 1

namespace GenusOneCurve

variable {k} (E : GenusOneCurve k)

/-- The curve of a genus-one curve is integral. -/
instance : IsIntegral E.X := E.isNormalVariety.1.toIsIntegral

/-- The curve of a genus-one curve is locally Noetherian. -/
instance : IsLocallyNoetherian E.X :=
  haveI := E.isNormalVariety.1.toLocallyOfFiniteType
  LocallyOfFiniteType.isLocallyNoetherian E.s

/-- The curve of a genus-one curve is normal. -/
instance : IsNormal E.X := E.isNormalVariety.2

end GenusOneCurve

/-- **Normalization datum for elliptic curves** (FA Complement 12.2.9.1). A *normalization datum
for elliptic curves* is a family `ε = (ε_C)`, indexed by the smooth proper curves `C` of genus
`1`, of nonzero elements `ε_C ∈ H⁰(C, ω_C^{⊗12})` such that `φ^* ε_{C'} = ε_C` for every
isomorphism `φ : C ⟶ C'`.

`H⁰(C, ω_C^{⊗12})` is the group of global sections `MMP.Mori.pluricanonicalSections` of
`𝒪_C(12 K_C)`, rational `12`-canonical forms; isomorphisms are isomorphisms over `k`, and `φ^*` is
the pull-back of forms `MMP.Mori.pullbackRationalPluriForms`. -/
@[mmp "def_fa12a_elliptic_normalized_section_convention"]
structure EllipticNormalizationDatum where
  /-- The section `ε_C` for each smooth proper curve `C` of genus `1`. -/
  ε : ∀ C : GenusOneCurve k, RationalPluriForms C.s 1 12
  /-- `ε_C ∈ H⁰(C, ω_C^{⊗12})`. -/
  mem : ∀ C : GenusOneCurve k, ε C ∈ pluricanonicalSections C.s 1 12 0 ⊤
  /-- `ε_C ≠ 0`. -/
  ne_zero : ∀ C : GenusOneCurve k, ε C ≠ 0
  /-- `φ^* ε_{C'} = ε_C` for every isomorphism `φ : C ⟶ C'` over `k`. -/
  pullback_eq : ∀ (C C' : GenusOneCurve k) (φ : C.X ≅ C'.X) (h : φ.hom ≫ C'.s = C.s),
    (h ▸ pullbackRationalPluriForms C'.s φ.hom (ε C') : RationalPluriForms C.s 1 12) = ε C

variable {k}

/-- `σ = τ^{⊗j}` for `m`-canonical forms on a line `L` over `K`: `n = a j`, and for a basis `b` of
`L`, if `τ = c b^{⊗a}` then `σ = c^j b^{⊗n}` (this does not depend on `b`). -/
def IsTensorPowerOf {K L : Type*} [Field K] [AddCommGroup L] [Module K L] {a n : ℤ}
    (τ : ZTensorPower K L a) (j : ℕ) (σ : ZTensorPower K L n) : Prop :=
  n = a * j ∧ ∃ b : Module.Basis Unit K L,
    σ = ((ZTensorPower.basis b a).repr τ ()) ^ j • ZTensorPower.basis b n ()

/-- The rational `m`-canonical form `(dz/z)^{⊗m}` of a curve, for `z ∈ k(C)` (a local parameter
at a point). -/
def dlogPow {C : Scheme.{u}} (sC : C ⟶ Spec (.of k)) [IsIntegral C] (z : C.functionField)
    (m : ℕ) : RationalPluriForms sC 1 m :=
  letI := functionFieldAlgebra sC
  let ω : ⋀[C.functionField]^1 Ω[C.functionField⁄k] :=
    z⁻¹ • exteriorPower.ιMulti C.functionField 1 fun _ => KaehlerDifferential.D k C.functionField z
  (PiTensorProduct.tprod C.functionField (fun _ : Fin m => ω) :
    TensorPower C.functionField m (⋀[C.functionField]^1 Ω[C.functionField⁄k]))

variable (ε : EllipticNormalizationDatum k) {C : Scheme.{u}} (sC : C ⟶ Spec (.of k))
  [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]

/-- **Normalized sections on a smooth curve** (FA Def. 12.2.9 and Complement 12.2.9.1). Let `C₁`
be a smooth connected curve, `Δ₁ ≥ 0` a `ℚ`-divisor on `C₁`, `m > 0` with `mΔ₁` integral, and
`s₁ ∈ Γ(C₁, 𝒪(m(K_{C₁} + Δ₁)))`. `s₁` is *normalized* (with respect to the fixed `ε`) if:
* (a) when `C₁` is proper of genus `1`, `Δ₁ = 0` and `12 ∣ m`: `s₁ = ε_{C₁}^{m/12}`;
* (b) otherwise: for every `P ∈ ⌊Δ₁⌋` and a local parameter `z_P` at `P`, `s₁ - (dz_P/z_P)^m`
  vanishes at `P`.

A smooth connected curve is a smooth normal variety of dimension one (integral, hence
connected). `mΔ₁` is the integral divisor `G`, and `𝒪(m(K_{C₁} + Δ₁)) = ω_{C₁}^{⊗m}(mΔ₁)` is the
subsheaf `MMP.Mori.pluricanonicalSections` of rational `m`-canonical forms. `ε_{C₁}^{m/12}` is
the tensor power (`MMP.Flips.IsTensorPowerOf`). A point `P ∈ ⌊Δ₁⌋` is a prime divisor with
coefficient `≥ 1`; a local parameter at `P` is `z ∈ k(C₁)` of order one at `P`, a uniformizer of
the discrete valuation ring `𝒪_{C₁,P}`. A form `τ` *vanishes at `P`* if it lies in
`𝔪_P · 𝒪(m(K_{C₁} + Δ₁))_P`: the stalk at `P` consists of the forms with
`ord_P(τ) + coeff_P(mΔ₁) ≥ 0`, so this means `τ = 0` or `ord_P(τ) + coeff_P(mΔ₁) ≥ 1`. Condition
(b) is required for some local parameter `z_P` at each such `P`. The setting hypotheses are part
of the predicate. -/
@[mmp "def_fa12a_normalized_section_curve_component"]
structure IsNormalizedSection (Δ : QDivisor C) (m : ℕ) (G : Divisor C)
    (s : RationalPluriForms sC 1 m) : Prop where
  /-- `C₁` is a normal variety. -/
  isNormalVariety : IsNormalVariety k sC
  /-- `C₁` is smooth. -/
  isSmoothScheme : IsSmoothScheme sC
  /-- `C₁` is a curve. -/
  dim_eq : topologicalKrullDim C = 1
  /-- `Δ₁ ≥ 0`. -/
  isEffective : Δ.IsEffective
  /-- `m > 0`. -/
  pos : 0 < m
  /-- `G = mΔ₁`. -/
  toQDivisor_eq : Divisor.toQDivisor G = (m : ℤ) • Δ
  /-- `s₁ ∈ Γ(C₁, 𝒪(m(K_{C₁} + Δ₁)))`. -/
  mem : s ∈ pluricanonicalSections sC 1 m G ⊤
  /-- (a) If `C₁` is proper of genus `1`, `Δ₁ = 0` and `12 ∣ m`, then `s₁ = ε_{C₁}^{m/12}`. -/
  elliptic : ∀ (hp : IsProper sC)
    (hg : ∃ K : Divisor C, K.IsCanonicalDivisor sC 1 ∧ K.h0 k sC = 1), Δ = 0 → 12 ∣ m →
    letI := functionFieldAlgebra sC
    IsTensorPowerOf (K := C.functionField) (L := ⋀[C.functionField]^1 Ω[C.functionField⁄k])
      (a := 12) (n := m) (ε.ε ⟨C, sC, isNormalVariety, isSmoothScheme, hp, dim_eq, hg⟩ :
      PluriForms k C.functionField 1 12) (m / 12) (s : PluriForms k C.functionField 1 m)
  /-- (b) Otherwise, `s₁ - (dz_P/z_P)^m` vanishes at every `P ∈ ⌊Δ₁⌋`, for a local parameter
  `z_P` at `P`. -/
  vanishes : ¬ (IsProper sC ∧ (∃ K : Divisor C, K.IsCanonicalDivisor sC 1 ∧ K.h0 k sC = 1) ∧
      Δ = 0 ∧ 12 ∣ m) →
    ∀ P : Mori.PrimeDivisor C, 1 ≤ Δ.coeff P → ∃ z : C.functionField,
      C.ord z P.genericPoint = 1 ∧
      (s - dlogPow sC z m = 0 ∨ 1 ≤ P.ordForm (s - dlogPow sC z m) + G.coeff P)

end NormalizedSections

end MMP.Flips
