module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.FundamentalClassVarietyUnique
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.SingularStratumComplement
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.SingularStratumDimension
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.UnderlyingSpaceProperMap
public import MMP.AlgebraicGeometry.Chow.CycleClassOf
public import MMP.AlgebraicTopology.BorelMoore.TopHomologyBasis
public import MMP.AlgebraicTopology.BorelMoore.PushforwardSheets
public import MMP.AlgebraicGeometry.SubschemeOver
/-!
# The top homology of a complex scheme is free on its top-dimensional components (Fulton, §19.1)

Let `X` be a complex scheme of dimension `n` and `X_1, …, X_r` its `n`-dimensional irreducible
components. Then `H_{2n} X` is a free module with basis the cycle classes
`cl_X(X_1), …, cl_X(X_r)` (Fulton, Lemma 19.1.1, second assertion; components of dimension
`< n` contribute nothing to `H_{2n} X`).

Let `Z` be the union of the singular stratum `S_X` and of the components of dimension `≠ n`; then
`dim Z < n`, so restriction `H_{2n} X → H_{2n} (X - Z)` is injective, and `X - Z` is the disjoint
union of the open sets `U_j(ℂ)` of the `n`-dimensional components `X_j`. Hence a class of
`H_{2n} X` restricting to `0` on every `U_j(ℂ)` is `0`. For the inclusion `i_j : X_j → X`,
`cl_X(X_j)|_{U_j} = i_{j*}(cl(X_j)|_{U_j})` is, up to push-forward along homeomorphisms, the
fundamental class of the connected complex manifold `U_j(ℂ) ⊆ (X_j)_reg(ℂ)`, which freely
generates `H_{2n} U_j(ℂ)` by Poincaré duality, while `cl_X(X_i)|_{U_j} = 0` for `i ≠ j`
since `U_j` misses `X_i`. The `cl_X(X_j)` are therefore linearly independent and span.

## Main definitions

* `MMP.singularStratumComplementPointsOpens`: `U_j(ℂ)` as an open subset of
  `X(ℂ)`.

## Main results

* `MMP.linearIndependent_and_span_eq_top_of_isCycleClassOf`: the cycle classes of
  the `n`-dimensional components are linearly independent and span `H_{2n} X`.
* `MMP.exists_basis_isCycleClassOf`: `H_{2n} X` has a basis, indexed by the
  `n`-dimensional components, of cycle classes.
* `MMP.eq_zero_of_forall_restrict_singularStratumComplementPointsOpens`: a class
  of `H_{2n} X` vanishing on every `U_j(ℂ)` vanishes.
* `MMP.exists_linearEquiv_restrict_pushforward_eq`,
  `MMP.eq_zero_of_smul_restrict_pushforward_eq_zero`,
  `MMP.bijective_smul_restrict_pushforward`: the restriction of a cycle class
  `i_* cl(V)` to an open subset `W ⊆ i(V_reg(ℂ))`.
* `MMP.IsFundamentalClass.eq_zero_of_smul_eq_zero`: a fundamental class of a
  non-empty manifold has no torsion.

## Implementation notes

The statement is made for `dim X ≤ n` (with no `n`-dimensional component `H_{2n} X = 0`), and
the components are indexed by the irreducible components `Z` of `X` with
`dim Z = n`, each read with its reduced structure `irreducibleComponentScheme X Z` and its
inclusion `irreducibleComponentι X Z`; cycle classes are the predicate `IsCycleClassOf` along
that inclusion, so the statement holds for every choice of cycle classes, which exist and are
unique.

The Fulton-subvariety reading of components (`Subvariety.ofIrreducibleComponent`) is in
`MMP.AlgebraicGeometry.CycleMap.TopClassDetectedLocallyComponents`, which re-exports this file
for the remaining Fulton users. The coefficients are an arbitrary commutative ring `R`;
Fulton's are `ℤ`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, Lemma 19.1.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology
open MMP.UnderlyingSpace MMP.FundamentalClass
open scoped MMP.SubschemeOver

namespace MMP

open MMP.Intersection.Scheme (dimension)

universe u v

section Manifold

variable {R : Type u} [CommRing R] {H : Type v} [AddCommGroup H] [Module ℝ H]
  [TopologicalSpace H] [ContinuousAdd H] [ContinuousSMul ℝ H] [T2Space H]
  [LocallyConnectedSpace H] {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [ChartedSpace H M] {n : ℕ} {b : Module.Basis (Fin n) ℝ H}

/-- On a non-empty manifold, a fundamental class has no torsion: `r • μ = 0` forces `r = 0`. -/
theorem IsFundamentalClass.eq_zero_of_smul_eq_zero [Nonempty M]
    {μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of M) n}
    (hμ : IsFundamentalClass R b μ) {r : R} (hr : r • μ = 0) : r = 0 := by
  have := ChartedSpace.locallyConnectedSpace H M
  obtain ⟨x⟩ := ‹Nonempty M›
  let W : Opens M := ⟨connectedComponent x, isOpen_connectedComponent⟩
  have : ConnectedSpace W := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have h := PoincareDuality.topHomologyFreeOnFundamentalClass_of_manifold (R := R) (Y := W) b _
    (hμ.restrict W)
  apply h.1
  simp only [zero_smul, ← map_smul, hr, map_zero]

end Manifold

section CycleClass

variable (R : Type) [CommRing R] {X V : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]
  [V.Over (Spec (.of ℂ))] [IsComplexScheme V] [IsIntegral V]
  [LocallyOfFiniteType (V ↘ Spec (.of ℂ))] [QuasiCompact (V ↘ Spec (.of ℂ))] (i : V ⟶ X)
  [IsClosedImmersion i] [i.IsOver (Spec (.of ℂ))]

omit [IsIntegral V] [LocallyOfFiniteType (V ↘ Spec (.of ℂ))] [QuasiCompact (V ↘ Spec (.of ℂ))] in
/-- The push-forward along a closed immersion `i : V → X`, restricted to an open `W ⊆ X(ℂ)`
missing `i(V(ℂ))`, vanishes. -/
theorem restrict_pushforward_map_eq_zero_of_disjoint {j : ℤ}
    (c : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ V)) j)
    (W : Opens (UnderlyingSpace ℂ X))
    (hW : Disjoint (W : Set (UnderlyingSpace ℂ X)) (Set.range (mapFun (K := ℂ) i))) :
    borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ X)) W j
      (borelMooreHomology.pushforward R (ModuleCat.of R R) (TopCat.ofHom (map (K := ℂ) i))
        (isClosedEmbedding_map_of_isClosedImmersion i).isProperMap j c) = 0 :=
  borelMooreHomology.restrict_pushforward_eq_zero_of_disjoint R (ModuleCat.of R R)
    (TopCat.ofHom (map (K := ℂ) i)) (isClosedEmbedding_map_of_isClosedImmersion i).isProperMap W
    hW j c

/-- **The cycle class of a subvariety restricted to an open set of its regular part.** Let
`i : V → X` be a closed immersion of a complex variety `V` of dimension `k` into a complex
scheme, `c = cl(V)`, and `W ⊆ X(ℂ)` open with `W ⊆ i(V_reg(ℂ))`. Then `(i_* c)|_W` is the image,
under a linear isomorphism (push-forward along homeomorphisms), of a fundamental class of the
open subset `i⁻¹(W)` of the complex manifold `V_reg(ℂ)`. -/
theorem exists_linearEquiv_restrict_pushforward_eq {k : ℕ} {hk : (k : WithBot ℕ∞) = dimension V}
    {c : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ V)) (2 * k : ℕ)}
    (hc : IsVarietyFundamentalClass R hk c) (W : Opens (UnderlyingSpace ℂ X))
    (hW : (W : Set (UnderlyingSpace ℂ X)) ⊆ mapFun (K := ℂ) i '' regularPart ℂ V) :
    let := regularChartedSpace (𝕜 := ℂ) hk
    ∃ (L : borelMooreHomology R (ModuleCat.of R R)
        (TopCat.of (regularOpensInter (Opens.comap (map (K := ℂ) i) W))) (2 * k : ℕ) ≃ₗ[R]
        borelMooreHomology R (ModuleCat.of R R) (TopCat.of W) (2 * k : ℕ))
      (μ : borelMooreHomology R (ModuleCat.of R R)
        (TopCat.of (regularOpensInter (Opens.comap (map (K := ℂ) i) W))) (2 * k : ℕ)),
      IsFundamentalClass R (euclideanComplexOrientationBasis k) μ ∧
      borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ X)) W
        (2 * k : ℕ) (borelMooreHomology.pushforward R (ModuleCat.of R R)
          (TopCat.ofHom (map (K := ℂ) i)) (isClosedEmbedding_map_of_isClosedImmersion i).isProperMap
          (2 * k : ℕ) c) = L μ := by
  let := regularChartedSpace (𝕜 := ℂ) hk
  set f : TopCat.of (UnderlyingSpace ℂ V) ⟶ TopCat.of (UnderlyingSpace ℂ X) :=
    TopCat.ofHom (map (K := ℂ) i)
  have hf : IsClosedEmbedding f := isClosedEmbedding_map_of_isClosedImmersion i
  set W' : Opens (TopCat.of (UnderlyingSpace ℂ V)) := Opens.comap f.hom W
  have hreg : W' ≤ (regularOpens ℂ V : Opens (TopCat.of (UnderlyingSpace ℂ V))) := by
    intro q hq
    obtain ⟨q', hq', hqq'⟩ := hW hq
    exact hf.injective hqq' ▸ hq'
  have hbij : Function.Bijective (borelMooreHomology.restrictPreimage f W) := by
    refine ⟨fun x y hxy ↦ Subtype.ext (hf.injective (congrArg Subtype.val hxy)), fun p ↦ ?_⟩
    obtain ⟨q, -, hq⟩ := hW p.2
    exact ⟨⟨q, show mapFun (K := ℂ) i q ∈ W from hq ▸ p.2⟩, Subtype.ext hq⟩
  have hind : IsInducing (borelMooreHomology.restrictPreimage f W) := by
    rw [← IsInducing.subtypeVal.of_comp_iff]
    exact hf.isInducing.comp IsInducing.subtypeVal
  let e : W' ≃ₜ W := (Equiv.ofBijective _ hbij).toHomeomorphOfIsInducing hind
  have hb₂ := borelMooreHomology.bijective_pushforward_of_comp_eq_id R
    (borelMooreHomology.restrictPreimage f W) (TopCat.ofHom ⟨e.symm, e.symm.continuous⟩)
    (borelMooreHomology.isProperMap_restrictPreimage f W hf.isProperMap) e.symm.isProperMap
    (ConcreteCategory.hom_ext _ _ fun x ↦ e.symm_apply_apply x)
    (ConcreteCategory.hom_ext _ _ fun x ↦ e.apply_symm_apply x) (2 * k : ℕ)
  have hb₁ := borelMooreHomology.bijective_pushforward_of_comp_eq_id R
    (borelMooreHomology.subOpensInv _ hreg) (borelMooreHomology.subOpensMap _ hreg)
    (isProperMap_subOpensInv hreg) (borelMooreHomology.isProperMap_subOpensMap _ hreg)
    rfl rfl (2 * k : ℕ)
  refine ⟨(LinearEquiv.ofBijective _ hb₁).trans (LinearEquiv.ofBijective _ hb₂), _,
    hc.isFundamentalClass_restrict W', ?_⟩
  rw [borelMooreHomology.restrict_pushforward_apply,
    restrict_eq_pushforward_subOpensInv hreg]
  rfl

/-- If `W ⊆ i(V_reg(ℂ))` is a non-empty open set, `r • (i_* cl(V))|_W = 0` forces `r = 0`. -/
theorem eq_zero_of_smul_restrict_pushforward_eq_zero {k : ℕ} {hk : (k : WithBot ℕ∞) = dimension V}
    {c : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ V)) (2 * k : ℕ)}
    (hc : IsVarietyFundamentalClass R hk c) (W : Opens (UnderlyingSpace ℂ X))
    (hW : (W : Set (UnderlyingSpace ℂ X)) ⊆ mapFun (K := ℂ) i '' regularPart ℂ V)
    (hne : (W : Set (UnderlyingSpace ℂ X)).Nonempty) {r : R}
    (hr : r • borelMooreHomology.restrict R (ModuleCat.of R R)
      (Y := TopCat.of (UnderlyingSpace ℂ X)) W (2 * k : ℕ)
      (borelMooreHomology.pushforward R (ModuleCat.of R R) (TopCat.ofHom (map (K := ℂ) i))
        (isClosedEmbedding_map_of_isClosedImmersion i).isProperMap (2 * k : ℕ) c) = 0) :
    r = 0 := by
  let := regularChartedSpace (𝕜 := ℂ) hk
  obtain ⟨L, μ, hμ, heq⟩ := exists_linearEquiv_restrict_pushforward_eq R i hc W hW
  rw [heq, ← map_smul, LinearEquiv.map_eq_zero_iff] at hr
  obtain ⟨p, hp⟩ := hne
  obtain ⟨q, hq, rfl⟩ := hW hp
  have : Nonempty (regularOpensInter (Opens.comap (map (K := ℂ) i) W)) :=
    ⟨⟨⟨q, hq⟩, show mapFun (K := ℂ) i q ∈ W from hp⟩⟩
  exact hμ.eq_zero_of_smul_eq_zero hr

/-- If `W ⊆ i(V_reg(ℂ))` is open and `i⁻¹(W)` is connected, `(i_* cl(V))|_W` freely generates
`H_{2k} W`. -/
theorem bijective_smul_restrict_pushforward {k : ℕ} {hk : (k : WithBot ℕ∞) = dimension V}
    {c : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ V)) (2 * k : ℕ)}
    (hc : IsVarietyFundamentalClass R hk c) (W : Opens (UnderlyingSpace ℂ X))
    (hW : (W : Set (UnderlyingSpace ℂ X)) ⊆ mapFun (K := ℂ) i '' regularPart ℂ V)
    (hconn : IsConnected (mapFun (K := ℂ) i ⁻¹' (W : Set (UnderlyingSpace ℂ X)))) :
    Function.Bijective fun r : R ↦ r • borelMooreHomology.restrict R (ModuleCat.of R R)
      (Y := TopCat.of (UnderlyingSpace ℂ X)) W (2 * k : ℕ)
      (borelMooreHomology.pushforward R (ModuleCat.of R R) (TopCat.ofHom (map (K := ℂ) i))
        (isClosedEmbedding_map_of_isClosedImmersion i).isProperMap (2 * k : ℕ) c) := by
  let := regularChartedSpace (𝕜 := ℂ) hk
  set N := regularOpensInter (Opens.comap (map (K := ℂ) i) W)
  have hind : IsInducing fun x : N ↦ (x.1.1 : UnderlyingSpace ℂ V) :=
    IsInducing.subtypeVal.comp IsInducing.subtypeVal
  have hrange : Set.range (fun x : N ↦ (x.1.1 : UnderlyingSpace ℂ V)) =
      mapFun (K := ℂ) i ⁻¹' (W : Set (UnderlyingSpace ℂ X)) := by
    ext q
    refine ⟨fun ⟨x, hx⟩ ↦ hx ▸ x.2, fun hq ↦ ?_⟩
    obtain ⟨q', hq', hqq'⟩ := hW hq
    rw [(isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) i).injective hqq'] at hq'
    exact ⟨⟨⟨q, hq'⟩, hq⟩, rfl⟩
  have hpre : IsPreconnected (Set.univ : Set N) := by
    rw [← hind.isPreconnected_image, Set.image_univ, hrange]
    exact hconn.isPreconnected
  have : PreconnectedSpace N := ⟨hpre⟩
  obtain ⟨q, hq⟩ := hconn.nonempty
  obtain ⟨x, -⟩ : q ∈ Set.range (fun x : N ↦ (x.1.1 : UnderlyingSpace ℂ V)) := hrange ▸ hq
  have : ConnectedSpace N := { toNonempty := ⟨x⟩ }
  obtain ⟨L, μ, hμ, heq⟩ := exists_linearEquiv_restrict_pushforward_eq R i hc W hW
  have hfree := PoincareDuality.topHomologyFreeOnFundamentalClass_of_manifold (R := R) (Y := N)
    (euclideanComplexOrientationBasis k) μ hμ
  have hcomp : (fun r : R ↦ r • L μ) = L ∘ fun r ↦ r • μ :=
    funext fun r ↦ (map_smul L r μ).symm
  rw [heq, hcomp]
  exact L.bijective.comp hfree

end CycleClass

section Components

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]

/-- An irreducible component of a complex scheme, with its reduced structure, is a complex
scheme. -/
instance isComplexScheme_irreducibleComponentScheme (Z : irreducibleComponents X) :
    IsComplexScheme (irreducibleComponentScheme X Z) where
  toLocallyOfFiniteType := by
    rw [← comp_over (irreducibleComponentι X Z) (Spec (.of ℂ))]
    infer_instance
  toQuasiCompact := by
    rw [← comp_over (irreducibleComponentι X Z) (Spec (.of ℂ))]
    infer_instance
  exists_isClosedImmersion := by
    obtain ⟨W, _, _, j, hj, _⟩ := IsComplexScheme.exists_isClosedImmersion (X := X)
    exact ⟨W, inferInstance, inferInstance, irreducibleComponentι X Z ≫ j, inferInstance,
      inferInstance⟩

omit [IsComplexScheme X] in
/-- `dim Xⱼ`, for an irreducible component `Xⱼ` of `X`, is the dimension of its reduced
structure. -/
lemma topologicalKrullDim_eq_dimension_irreducibleComponentScheme (Z : irreducibleComponents X) :
    topologicalKrullDim Z.1 = dimension (irreducibleComponentScheme X Z) := by
  rw [dimension, (irreducibleComponentι X Z).isClosedEmbedding.toIsEmbedding.toHomeomorph
    |>.isHomeomorph.topologicalKrullDim_eq, range_irreducibleComponentι]

variable (X) in
/-- `Uⱼ(ℂ)`, for an irreducible component `Xⱼ` of `X`, as an open subset of `X(ℂ)`: the
`ℂ`-points of `X` whose closed point lies in `Uⱼ = X - (S_X ∪ ⋃_{l ≠ j} X_l)`. -/
def singularStratumComplementPointsOpens (Z : irreducibleComponents X) :
    Opens (UnderlyingSpace ℂ X) :=
  ⟨{p | p.toHom (IsLocalRing.closedPoint ℂ) ∈ singularStratumComplement X Z},
    isOpen_preimage_of_isOpen (isOpen_singularStratumComplement ℂ X Z)⟩

/-- `p ∈ Uⱼ(ℂ)` if and only if the closed point of `p` lies in `Uⱼ`. -/
@[simp]
lemma mem_singularStratumComplementPointsOpens {Z : irreducibleComponents X}
    {p : UnderlyingSpace ℂ X} : p ∈ singularStratumComplementPointsOpens X Z ↔
      p.toHom (IsLocalRing.closedPoint ℂ) ∈ singularStratumComplement X Z :=
  Iff.rfl

/-- The preimage of `Uⱼ(ℂ)` under `Xⱼ(ℂ) → X(ℂ)` is the set of `ℂ`-points of `Xⱼ` over `Uⱼ`. -/
lemma preimage_singularStratumComplementPointsOpens (Z : irreducibleComponents X) :
    mapFun (K := ℂ) (irreducibleComponentι X Z) ⁻¹'
        (singularStratumComplementPointsOpens X Z : Set (UnderlyingSpace ℂ X)) =
      singularStratumComplementPoints (K := ℂ) X Z := by
  ext q
  change (mapFun (K := ℂ) (irreducibleComponentι X Z) q).toHom
    (IsLocalRing.closedPoint ℂ) ∈ singularStratumComplement X Z ↔ _
  rw [toHom_mapFun]
  rfl

/-- `Uⱼ(ℂ)` is contained in the image of the regular part `(Xⱼ)_reg(ℂ)` in `X(ℂ)`. -/
lemma singularStratumComplementPointsOpens_subset (Z : irreducibleComponents X) :
    (singularStratumComplementPointsOpens X Z : Set (UnderlyingSpace ℂ X)) ⊆
      mapFun (K := ℂ) (irreducibleComponentι X Z) ''
        regularPart ℂ (irreducibleComponentScheme X Z) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ : p ∈ mapFun (K := ℂ) (irreducibleComponentι X Z) ''
      singularStratumComplementPoints (K := ℂ) X Z :=
    (image_mapFun_singularStratumComplementPoints (K := ℂ) X Z).symm ▸ hp
  exact ⟨q, singularStratumComplementPoints_subset_regularPart X Z hq, rfl⟩

/-- The preimage of `Uⱼ(ℂ)` under `Xⱼ(ℂ) → X(ℂ)` is connected. -/
lemma isConnected_preimage_singularStratumComplementPointsOpens (Z : irreducibleComponents X) :
    IsConnected (mapFun (K := ℂ) (irreducibleComponentι X Z) ⁻¹'
      (singularStratumComplementPointsOpens X Z : Set (UnderlyingSpace ℂ X))) := by
  rw [preimage_singularStratumComplementPointsOpens]
  exact isConnected_singularStratumComplementPoints X Z

/-- `Uⱼ(ℂ)` is non-empty. -/
lemma nonempty_singularStratumComplementPointsOpens (Z : irreducibleComponents X) :
    (singularStratumComplementPointsOpens X Z : Set (UnderlyingSpace ℂ X)).Nonempty := by
  obtain ⟨q, hq⟩ := (isConnected_preimage_singularStratumComplementPointsOpens Z).nonempty
  exact ⟨_, hq⟩

omit [IsComplexScheme X] in
/-- The image of `Xⱼ(ℂ) → X(ℂ)` is the set of `ℂ`-points of `X` whose closed point lies in
`Xⱼ`. -/
lemma range_mapFun_irreducibleComponentι (Z : irreducibleComponents X) :
    Set.range (mapFun (K := ℂ) (irreducibleComponentι X Z)) =
      {p | p.toHom (IsLocalRing.closedPoint ℂ) ∈ Z.1} := by
  rw [range_mapFun_of_isClosedImmersion, range_irreducibleComponentι]

/-- For `Xₗ ≠ Xⱼ`, the set `Uⱼ(ℂ)` is disjoint from the image of `Xₗ(ℂ) → X(ℂ)`. -/
lemma disjoint_singularStratumComplementPointsOpens {Z Z' : irreducibleComponents X} (h : Z' ≠ Z) :
    Disjoint (singularStratumComplementPointsOpens X Z : Set (UnderlyingSpace ℂ X))
      (Set.range (mapFun (K := ℂ) (irreducibleComponentι X Z'))) := by
  rw [range_mapFun_irreducibleComponentι]
  exact Set.disjoint_left.mpr fun p hp hp' ↦ hp (Or.inr (Set.mem_iUnion₂.mpr ⟨Z', h, hp'⟩))

/-- The union of `S_X` and of the irreducible components of dimension `≠ n` of a complex
scheme `X` of dimension `≤ n` has dimension `< n`. -/
lemma topologicalKrullDim_singularStratum_union_lt {n : ℕ} (hX : dimension X ≤ n) :
    topologicalKrullDim ↥(singularStratum X ∪ ⋃ Z : {Z : irreducibleComponents X //
      (n : WithBot ℕ∞) ≠ dimension (irreducibleComponentScheme X Z)}, Z.1.1) < n := by
  classical
  have := (finite_irreducibleComponents_of_isAlgebraicScheme ℂ X).to_subtype
  let κ := {Z : irreducibleComponents X //
    (n : WithBot ℕ∞) ≠ dimension (irreducibleComponentScheme X Z)}
  let : Fintype κ := Fintype.ofFinite _
  let A : Option κ → Set X := fun o ↦ match o with
    | none => singularStratum X
    | some Z => Z.1.1
  have hA : ∀ o, IsClosed (A o) := by
    rintro (_ | Z)
    · exact isClosed_singularStratum ℂ X
    · exact isClosed_of_mem_irreducibleComponents _ Z.1.2
  have hTA : singularStratum X ∪ ⋃ Z : κ, Z.1.1 ⊆
      ⋃ o ∈ (Finset.univ : Finset (Option κ)), A o := by
    rintro x (hx | hx)
    · exact Set.mem_biUnion (Finset.mem_univ none) hx
    · obtain ⟨Z, hZ⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_biUnion (Finset.mem_univ (some Z)) hZ
  have hAlt : ∀ o, topologicalKrullDim ↥(A o) < n := by
    rintro (_ | Z)
    · exact topologicalKrullDim_singularStratum_lt ℂ X hX
    · have hle : topologicalKrullDim ↥Z.1.1 ≤ n := (topologicalKrullDim_subspace_le X _).trans hX
      refine lt_of_le_of_ne hle fun h ↦ Z.2 ?_
      rw [← topologicalKrullDim_eq_dimension_irreducibleComponentScheme, h]
  have hle := topologicalKrullDim_le_of_subset_biUnion (Finset.univ : Finset (Option κ))
    ((isClosed_singularStratum ℂ X).union
      (isClosed_iUnion_of_finite fun Z ↦ isClosed_of_mem_irreducibleComponents _ Z.1.2)) hA
    hTA (c := Finset.univ.sup fun o ↦ topologicalKrullDim ↥(A o))
    (fun o _ ↦ (topologicalKrullDim_le_of_subset Set.inter_subset_right).trans
      (Finset.le_sup (f := fun o ↦ topologicalKrullDim ↥(A o)) (Finset.mem_univ o)))
  exact hle.trans_lt ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr fun o _ ↦ hAlt o)

/-- **Top-dimensional homology is detected on the sets `Uⱼ(ℂ)`** (Fulton, proof of
Lemma 19.1.1). Let `X` be a complex scheme of dimension `≤ n`. If `d ∈ H_{2n} X` restricts to `0`
on `Uⱼ(ℂ)` for every `n`-dimensional irreducible component `Xⱼ`, then `d = 0`. -/
theorem eq_zero_of_forall_restrict_singularStratumComplementPointsOpens (R : Type) [CommRing R]
    {n : ℕ} (hX : dimension X ≤ n)
    (d : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X)) (2 * n : ℕ))
    (hd : ∀ Z : irreducibleComponents X,
      (n : WithBot ℕ∞) = dimension (irreducibleComponentScheme X Z) →
      borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ X))
        (singularStratumComplementPointsOpens X Z) (2 * n : ℕ) d = 0) :
    d = 0 := by
  classical
  have := (finite_irreducibleComponents_of_isAlgebraicScheme ℂ X).to_subtype
  let : Fintype (irreducibleComponents X) := Fintype.ofFinite _
  let ι := {Z : irreducibleComponents X //
    (n : WithBot ℕ∞) = dimension (irreducibleComponentScheme X Z)}
  let κ := {Z : irreducibleComponents X //
    (n : WithBot ℕ∞) ≠ dimension (irreducibleComponentScheme X Z)}
  let T : Set X := singularStratum X ∪ ⋃ Z : κ, Z.1.1
  have hTc : IsClosed T := (isClosed_singularStratum ℂ X).union
    (isClosed_iUnion_of_finite fun Z ↦ isClosed_of_mem_irreducibleComponents _ Z.1.2)
  have hTdim : topologicalKrullDim ↥T < n := topologicalKrullDim_singularStratum_union_lt hX
  let T' : Closeds X := ⟨T, hTc⟩
  have hiso := IsComplexScheme.isIso_restrict_compl_of_setDimension_lt R X T' hTdim
  set U := borelMooreHomology.complOpens (Y := TopCat.of (UnderlyingSpace ℂ X))
    (isClosed_range_map_of_isClosedImmersion (Scheme.IdealSheafData.vanishingIdeal T').subschemeι)
  have hmemU : ∀ p : UnderlyingSpace ℂ X, p ∈ U ↔ p.toHom (IsLocalRing.closedPoint ℂ) ∉ T := by
    intro p
    change p ∉ Set.range (mapFun (K := ℂ) _) ↔ _
    rw [range_mapFun_of_isClosedImmersion]
    change ¬ (_ ∈ Set.range (Scheme.IdealSheafData.subschemeι _).base) ↔ _
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hinj : Function.Injective
      (borelMooreHomology.restrict R (ModuleCat.of R R) U (2 * n : ℕ)) := by
    rw [show ((2 * n : ℕ) : ℤ) = 2 * (n : ℤ) by omega]
    exact ((ConcreteCategory.isIso_iff_bijective _).1 hiso).1
  let W : ι → Opens (UnderlyingSpace ℂ X) := fun Z ↦ singularStratumComplementPointsOpens X Z.1
  have hle : ∀ Z : ι, W Z ≤ U := by
    intro Z p hp
    refine (hmemU p).mpr ?_
    rintro (hS | hS)
    · exact Set.disjoint_left.mp (disjoint_singularStratumComplement Z.1) hp hS
    · obtain ⟨Z', hZ'⟩ := Set.mem_iUnion.mp hS
      have hne : Z'.1 ≠ Z.1 := fun h ↦ Z'.2 (h ▸ Z.2)
      exact hp (Or.inr (Set.mem_iUnion₂.mpr ⟨Z'.1, hne, hZ'⟩))
  have hdisj : Pairwise (Function.onFun Disjoint fun Z : ι ↦
      ((borelMooreHomology.subOpens U (W Z) : Opens (TopCat.of U)) : Set (TopCat.of U))) := by
    intro Z Z' h
    exact Set.disjoint_left.mpr fun x h1 h2 ↦ Set.disjoint_left.mp
      (pairwise_disjoint_singularStratumComplement fun e ↦ h (Subtype.ext e))
      (show x.1 ∈ W Z from h1) (show x.1 ∈ W Z' from h2)
  have hcover : ∀ x : TopCat.of U, ∃ Z : ι, x ∈ borelMooreHomology.subOpens U (W Z) := by
    intro x
    have hx := (hmemU x.1).mp x.2
    have hS : x.1.toHom (IsLocalRing.closedPoint ℂ) ∈ (singularStratum X)ᶜ :=
      fun h ↦ hx (Or.inl h)
    rw [singularStratum_compl_eq_iUnion, Set.mem_iUnion] at hS
    obtain ⟨Z, hZ⟩ := hS
    by_cases hZn : (n : WithBot ℕ∞) = dimension (irreducibleComponentScheme X Z)
    · exact ⟨⟨Z, hZn⟩, hZ⟩
    · exact (hx <| Or.inr <|
        Set.mem_iUnion.mpr ⟨⟨Z, hZn⟩, singularStratumComplement_subset Z hZ⟩).elim
  apply hinj
  rw [map_zero, borelMooreHomology.eq_sum_pushforward_restrict R
    (fun Z : ι ↦ borelMooreHomology.subOpens U (W Z)) hdisj hcover _
    (borelMooreHomology.restrict R (ModuleCat.of R R) U (2 * n : ℕ) d)]
  refine Finset.sum_eq_zero fun Z _ ↦ ?_
  rw [borelMooreHomology.restrict_restrict_apply R _ U (hle Z), hd Z.1 Z.2, map_zero, map_zero]

/-- **The top homology of a complex scheme is free on its top-dimensional components** (Fulton,
Lemma 19.1.1, second assertion, with one generator for each `n`-dimensional component). Let `X`
be a complex scheme of dimension `≤ n`, and for each `n`-dimensional irreducible component `Xⱼ`
let `a_j = cl_X(Xⱼ) ∈ H_{2n} X` be its cycle class. Then the `a_j` are linearly independent and
span `H_{2n} X`: `H_{2n} X` is a free `R`-module with basis `cl_X(X₁), …, cl_X(X_r)`. -/
theorem linearIndependent_and_span_eq_top_of_isCycleClassOf (R : Type) [CommRing R] {n : ℕ}
    (hX : dimension X ≤ n)
    (a : {Z : irreducibleComponents X //
        (n : WithBot ℕ∞) = dimension (irreducibleComponentScheme X Z)} →
      borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X)) (2 * n : ℕ))
    (ha : ∀ Z, IsCycleClassOf R (irreducibleComponentι X Z.1) Z.2 (a Z)) :
    LinearIndependent R a ∧ Submodule.span R (Set.range a) = ⊤ := by
  classical
  have := (finite_irreducibleComponents_of_isAlgebraicScheme ℂ X).to_subtype
  let : Fintype (irreducibleComponents X) := Fintype.ofFinite _
  let ι := {Z : irreducibleComponents X //
    (n : WithBot ℕ∞) = dimension (irreducibleComponentScheme X Z)}
  let ρ : (Z : ι) → borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X))
      (2 * n : ℕ) →ₗ[R] borelMooreHomology R (ModuleCat.of R R)
        (TopCat.of (singularStratumComplementPointsOpens X Z.1)) (2 * n : ℕ) :=
    fun Z ↦ (borelMooreHomology.restrict R (ModuleCat.of R R)
    (Y := TopCat.of (UnderlyingSpace ℂ X)) (singularStratumComplementPointsOpens X Z.1)
    (2 * n : ℕ)).hom
  choose c hc hca using ha
  have hzero : ∀ Z Z' : ι, Z' ≠ Z → ρ Z (a Z') = 0 := by
    intro Z Z' h
    rw [← hca Z']
    exact restrict_pushforward_map_eq_zero_of_disjoint R _ _ _
      (disjoint_singularStratumComplementPointsOpens fun e ↦ h (Subtype.ext e))
  have hbij : ∀ Z : ι, Function.Bijective fun r : R ↦ r • ρ Z (a Z) := by
    intro Z
    rw [← hca Z]
    exact bijective_smul_restrict_pushforward R _ (hc Z) _
      (singularStratumComplementPointsOpens_subset Z.1)
      (isConnected_preimage_singularStratumComplementPointsOpens Z.1)
  have hsum : ∀ (g : ι → R) (Z : ι), ρ Z (∑ Z', g Z' • a Z') = g Z • ρ Z (a Z) := by
    intro g Z
    rw [map_sum, Finset.sum_eq_single Z (fun Z' _ h ↦ by rw [map_smul, hzero Z Z' h, smul_zero])
      (fun h ↦ absurd (Finset.mem_univ Z) h), map_smul]
  refine ⟨Fintype.linearIndependent_iff.2 fun g hg Z ↦ ?_, eq_top_iff.2 fun x _ ↦ ?_⟩
  · have h := congrArg (ρ Z) hg
    rw [hsum, map_zero] at h
    exact (hbij Z).1 (h.trans (zero_smul R _).symm)
  · choose r hr using fun Z : ι ↦ (hbij Z).2 (ρ Z x)
    have hd : x - ∑ Z, r Z • a Z = 0 := by
      refine eq_zero_of_forall_restrict_singularStratumComplementPointsOpens R hX _ fun Z hZ ↦ ?_
      change ρ ⟨Z, hZ⟩ _ = 0
      have h := hr ⟨Z, hZ⟩
      simp only at h
      rw [map_sub, hsum, h, sub_self]
    rw [sub_eq_zero.mp hd]
    exact Submodule.sum_mem _ fun Z _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨Z, rfl⟩)

/-- **The cycle classes of the top-dimensional components form a basis** (Fulton,
Lemma 19.1.1): for a complex scheme `X` of dimension `≤ n`, `H_{2n} X` has a basis indexed by the
`n`-dimensional irreducible components `Xⱼ`, whose `j`-th vector is the cycle class
`cl_X(Xⱼ)`. -/
theorem exists_basis_isCycleClassOf (R : Type) [CommRing R] {n : ℕ} (hX : dimension X ≤ n) :
    ∃ b : Module.Basis {Z : irreducibleComponents X //
        (n : WithBot ℕ∞) = dimension (irreducibleComponentScheme X Z)} R
        (borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X)) (2 * n : ℕ)),
      ∀ Z, IsCycleClassOf R (irreducibleComponentι X Z.1) Z.2 (b Z) := by
  choose c hc using fun Z : {Z : irreducibleComponents X //
      (n : WithBot ℕ∞) = dimension (irreducibleComponentScheme X Z)} ↦
    existsUnique_isVarietyFundamentalClass R Z.2
  let a := fun Z : {Z : irreducibleComponents X //
      (n : WithBot ℕ∞) = dimension (irreducibleComponentScheme X Z)} ↦
    borelMooreHomology.pushforward R (ModuleCat.of R R)
      (TopCat.ofHom (map (K := ℂ) (irreducibleComponentι X Z.1)))
      (isProperMap_map (K := ℂ) (irreducibleComponentι X Z.1)) (2 * n : ℕ) (c Z)
  have ha : ∀ Z, IsCycleClassOf R (irreducibleComponentι X Z.1) Z.2 (a Z) :=
    fun Z ↦ isCycleClassOf_pushforward _ (hc Z).1
  obtain ⟨hli, hsp⟩ := linearIndependent_and_span_eq_top_of_isCycleClassOf R hX a ha
  exact ⟨Module.Basis.mk hli hsp.ge, fun Z ↦ by simpa using ha Z⟩

end Components

end MMP
