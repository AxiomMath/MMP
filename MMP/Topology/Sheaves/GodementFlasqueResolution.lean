module

public import Mathlib.Topology.Homotopy.Basic
public import MMP.AlgebraicTopology.BorelMoore.Pushforward
public import MMP.AlgebraicTopology.BorelMoore.FiniteChains
public import MMP.Topology.Sheaves.Godement
import MMP.AlgebraicTopology.BorelMoore.LongExactQuasiIso
import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSections
import StacksFrontier.AlgebraicGeometry.AffineMorphismCohomology.AcyclicQuasiIso
import StacksFrontier.AlgebraicGeometry.RelativeLeray.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import Mathlib.CategoryTheory.Sites.LocalSite
public import StacksFrontier.Homology.Injectives.Sheaf.AbelianSheavesOnSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.DegreeOneFlasqueVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.CohomologyOnACofilteredLimit

/-!
# Borel–Moore homology of a compact pair, and the sheaf cohomology toolkit

This file collects two foundational comparisons used in the analytic part of the theory.

**Locally finite chains on the complement of a compact pair.** Let `P` be a compact metrizable
space, `D ⊆ P` a closed subset and `U = P - D`. Suppose that every open neighbourhood of `D`
contains an open neighbourhood `N` of `D` which deformation retracts onto `D`. Then the homology
of the complex of locally finite singular chains on `U` (the Borel–Moore homology of `U`) is the
homology `H_•(P, D)` of the pair. The comparison is induced by restriction of chains: restricting
a chain of `P` to the open subset `U` (after barycentric subdivision) kills every chain of `D`,
hence induces a map of complexes `C_•(P) / C_•(D) → C^lf_•(U)`, and this map is a
quasi-isomorphism. When `U` is compact, this is ordinary homology: every locally finite chain on
`U` is a finite chain.

**The sheaf cohomology toolkit.** Let `T` be a topological space and write `H^n(T, -)` for the
right derived functors of the global sections functor `Γ(T, -)` on sheaves of abelian groups on
`T`.

1. Abelian sheaves on `T`, and `𝒪_X`-modules on a scheme `X`, have enough injectives; injective
   objects of either category are flasque as abelian sheaves; the restriction of a flasque sheaf
   to an open subset is flasque; a flasque sheaf has vanishing higher cohomology on every open
   subset.
2. Given `φ : F ⟶ F'`, a resolution `F ⟶ A^•` and an injective resolution `F' ⟶ J^•`, there is a
   map of complexes `A^• ⟶ J^•` over `φ`, unique up to homotopy (this only uses exactness of
   `F ⟶ A^•`). If moreover each `A^q` has vanishing higher cohomology, there is an isomorphism
   `H^n(Γ(T, A^•)) ≅ H^n(T, F)` under which the map induced by any such comparison is `φ_*`.
   The Godement resolution is a flasque resolution, so it, any flasque resolution and any
   injective resolution compute `H^n(T, -)` with the same induced maps.
3. The hypercohomology `MMP.Analytic.hypercohomology` of a one-term complex `F[0]`, that is
   `MMP.Analytic.sheafCohomology`, is naturally isomorphic to `H^n(T, F)`. A degreewise short
   exact sequence of bounded complexes of sheaves gives a short exact sequence of the total
   complexes of Godement sections, hence a long exact hypercohomology sequence, and the pullback
   `MMP.Analytic.hypercohomologyPullback` is natural in the complex and commutes with the
   connecting maps. On one-term complexes, under the identifications above, the pullback followed
   by `θ_*` for `θ : f⁻¹ F ⟶ F'` is the map induced by any map of injective resolutions
   `J^• ⟶ f_* J'^•` over `F ⟶ f_* f⁻¹ F ⟶ f_* F'`.
4. (Grothendieck) Let `(T^q)` and `(S^q)` be cohomological δ-functors between abelian categories,
   the source having enough injectives, with `T^q(I) = 0` for `I` injective and `q ≥ 1`. Two
   morphisms of δ-functors `T ⟶ S` agreeing in degree zero agree in all degrees.

## Main results

* `MMP.Analytic.exists_quasiIso_cokernel_restrictChainMap`: the comparison quasi-isomorphism
  `C_•(P) / C_•(D) → C^lf_•(U)`, and, for compact `U`, bijectivity of the inclusion of finite
  chains into locally finite chains.
* `MMP.Analytic.sheafCohomology_toolkit`: the four statements of the toolkit.
* `MMP.Analytic.godementResolution_sections_shortExact`: for a short exact sequence of abelian
  sheaves, sections over any open `U` of each term of the Godement resolution form a short exact
  sequence; `MMP.Analytic.godementResolution_globalSections_shortExact` is the case `U = T`.

## Implementation notes

* On a compact space a locally finite chain is a finite chain, so the complex of locally finite
  singular chains of the compact spaces `P` and `D` is their singular chain complex; the relative
  complex of `(P, D)` is the cokernel of the push-forward
  `MMP.borelMooreHomology.chainMap` along the closed inclusion `D → P`, on which
  the restriction `MMP.borelMooreHomology.restrictChainMap` descends. The
  statement is made with coefficients in any module `M` over any commutative ring `R`; the
  source takes `M = R = ℚ`. A deformation retraction of `N` onto `D` is a retraction
  `r : N → D` whose composite with the inclusion `D → N` is homotopic to the identity of `N`
  relative to `D` (`ContinuousMap.HomotopicRel`).
* The source's remark that for compact `U` Borel–Moore homology is ordinary homology is stated
  on chains: the inclusion `MMP.borelMooreHomology.ofFinsupp` of finite singular
  chains of `U` into locally finite chains is bijective in every degree, hence (commuting with
  the differentials) an isomorphism of complexes. `ofFinsupp` is defined for coefficients `R`,
  so this part is stated for `M = R`.
* The quasi-isomorphism is proved by the cokernel criterion
  `MMP.ModuleCatComplex.quasiIso_cokernelDesc_of_forall`, fed by a proper homotopy of a closed
  neighbourhood of `D` into `D` fixing `D`, obtained from the deformation retraction.
* `H^n(T, F)` is `Functor.rightDerived` of `MMP.Analytic.globalSections`; it is additive, being
  definitionally the composite of `sheafToPresheaf` with evaluation at `⊤`, and the statement
  records that instance. The comparison of `H^n` of an injective resolution with `H^n(T, -)` is
  `InjectiveResolution.isoRightDerivedObj`.
* A resolution `F ⟶ A^•` is a quasi-isomorphism `F[0] ⟶ A^•` of `ℕ`-indexed cochain complexes,
  as in `InjectiveResolution`; the restriction of a sheaf to an open `U` is its inverse image
  along the inclusion `U ⟶ T`. The comparison maps out of `A^•` are built as in
  `InjectiveResolution.desc` and `InjectiveResolution.descHomotopy`, which only use exactness of
  the source.
* The isomorphism of (2) is characterised by the induced maps: taking `φ = 𝟙 F` and `J` an
  injective resolution of `F` determines it, and its naturality in the resolution follows. An
  acyclic resolution computes cohomology because `Γ` carries the comparison quasi-isomorphism
  between complexes of acyclic objects to a quasi-isomorphism.
* In (3) the isomorphisms `ℍ^n(S, F[0]) ≅ H^n(S, F)` are given for all spaces `S` at once, since
  the pullback compares two spaces; the Godement double complex of `F[0]` is concentrated in row
  zero. A map `f⁻¹ J^• ⟶ J'^•` over `θ` is recorded through the inverse image adjunction as a
  map `J^• ⟶ f_* J'^•` over the adjoint of `θ`.
* The long exact sequence of (3) is that of `ShortComplex.ShortExact.δ` on the total complexes
  (naturality in the sequence: `HomologicalComplex.HomologySequence.δ_naturality`); exactness of
  the total complexes comes from exactness of each Godement term `G(F)(U) = ∏_{x ∈ U} F_x` in
  `F` and of coproducts of abelian groups.
* In (4) a cohomological δ-functor is a family of additive functors `ℕ → C ⥤ D` with connecting
  maps for every short exact sequence, natural in the sequence, making the long sequence exact at
  every spot from `T^0(A)` on.

## References

* [A. Borel, J. C. Moore, *Homology theory for locally compact spaces*][borelmoore1960], §3.
* [A. Hatcher, *Algebraic Topology*][hatcher2002], §2.1 and §3.F.
* [R. Godement, *Topologie algébrique et théorie des faisceaux*]
* [A. Grothendieck, *Sur quelques points d'algèbre homologique*]
* [R. Hartshorne, *Algebraic Geometry*, III.1–III.2]
-/

@[expose] public section

namespace MMP.Analytic

universe u u₁ v₁ u₂ v₂

section BorelMoore

open CategoryTheory CategoryTheory.Limits AlgebraicTopology TopologicalSpace
open MMP.borelMooreHomology

/-- `(ComplexShape.down ℕ).next i = j` means `j + 1 = i`, or `i = j = 0`. -/
private lemma next_down_nat {i j : ℕ} (h : (ComplexShape.down ℕ).next i = j) :
    j + 1 = i ∨ (i = 0 ∧ j = 0) := by
  cases i with
  | zero => right; exact ⟨rfl, by rw [← h, ChainComplex.next_nat_zero]⟩
  | succ m => left; rw [← h, ChainComplex.next_nat_succ]

/-- **The cokernel criterion for `ℕ`-indexed chain complexes.** For a monomorphism `f : A ⟶ B`
and `g : B ⟶ D` with `f ≫ g = 0`, the induced map `coker f ⟶ D` is a quasi-isomorphism once, in
every degree `n`, (S) every cycle of `D` is, up to a boundary, the image of a chain of `B` whose
differential comes from `A`, and (I) such a chain of `B` whose image in `D` is a boundary is a
boundary up to a chain from `A`. -/
private lemma quasiIso_cokernelDesc_of_forall_nat {R : Type u} [CommRing R]
    {A B D : ChainComplex (ModuleCat.{u} R) ℕ} (f : A ⟶ B) [Mono f] (g : B ⟶ D) (w : f ≫ g = 0)
    (hS : ∀ n (z : D.X n), (∀ m, m + 1 = n → D.d n m z = 0) →
      ∃ b : B.X n, (∀ m, m + 1 = n → ∃ a : A.X m, B.d n m b = f.f m a) ∧
        ∃ e : D.X (n + 1), g.f n b - z = D.d (n + 1) n e)
    (hI : ∀ n (b : B.X n), (∀ m, m + 1 = n → ∃ a : A.X m, B.d n m b = f.f m a) →
      ∀ e : D.X (n + 1), g.f n b = D.d (n + 1) n e →
      ∃ b' : B.X (n + 1), ∃ a' : A.X n, b = B.d (n + 1) n b' + f.f n a') :
    QuasiIso (cokernel.desc f g w) := by
  refine MMP.ModuleCatComplex.quasiIso_cokernelDesc_of_forall _ _ w
    (fun i j k hj hk z hz ↦ ?_) (fun i j k hj hk b hb e he ↦ ?_) <;>
  rw [ChainComplex.prev] at hk <;> subst hk <;> rcases next_down_nat hj with rfl | ⟨rfl, rfl⟩
  · obtain ⟨b, hb, e, he⟩ := hS (j + 1) z fun m hm ↦ by cases Nat.succ_injective hm; exact hz
    exact ⟨b, hb j rfl, e, he⟩
  · obtain ⟨b, -, e, he⟩ := hS 0 z fun m hm ↦ by omega
    exact ⟨b, ⟨0, by simp [HomologicalComplex.shape]⟩, e, he⟩
  · exact hI (j + 1) b (fun m hm ↦ by cases Nat.succ_injective hm; exact hb) e he
  · exact hI 0 b (fun m hm ↦ by omega) e he

/-- The comparison map from the relative complex of a closed pair `(Y, X)` to the locally finite
chains of `Y - X` is a quasi-isomorphism, once closed neighbourhoods `N' ⊆ interior N` of `X`
carry a proper homotopy of `N` into `X` fixing `X`. -/
private lemma quasiIso_cokernelDesc_of_homotopy {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) {Y : TopCat.{u}} [T2Space Y] {X : Set Y} (hX : IsClosed X)
    {N N' : Set Y} (hN : IsClosed N) (hN' : IsClosed N') (hXN' : X ⊆ interior N')
    (hN'N : N' ⊆ interior N) {G : C(N × unitInterval, Y)} (hG : IsProperMap G)
    (hG0 : ∀ y, G (y, 0) = y) (hG1 : ∀ y, G (y, 1) ∈ X)
    (hGX : ∀ y : N, ∀ t, (y : Y) ∈ X → G (y, t) = y) :
    QuasiIso (cokernel.desc _ (restrictChainMap R M (complOpens hX))
      (chainMap_subspaceInclusion_comp_restrictChainMap R M hX)) := by
  have := mono_chainMap_subspaceInclusion R M hX
  refine quasiIso_cokernelDesc_of_forall_nat _ _ _
    (fun n z hz ↦ exists_restrictChainMap_sub_eq_d R M hX hN hN' hXN' hN'N hG hG0 hG1 hGX z hz)
    (fun n b hb e he ↦ exists_eq_d_add_of_restrictChainMap_eq_d R M hX hN hN' hXN' hN'N hG hG0
      hG1 hGX b (fun m hm ↦ ?_) e he)
  obtain ⟨a, ha⟩ := hb m hm
  rw [ha]
  exact isSupportedIn_chainMap_subsetInclusion hX a

/-- A closed subset of a compact metrizable space with an open neighbourhood deformation
retracting onto it has closed neighbourhoods `N' ⊆ interior N` and a proper homotopy of `N`
into it fixing it pointwise. -/
private lemma exists_deformation {P : TopCat.{u}} [CompactSpace P] [MetrizableSpace P]
    {D : Set P} (hD : IsClosed D) {N₀ : Set P} (hN₀ : IsOpen N₀) (hDN : D ⊆ N₀)
    (r : C(N₀, D))
    (H : ((⟨Set.inclusion hDN, continuous_inclusion hDN⟩ : C(D, N₀)).comp r).HomotopyRel
      (ContinuousMap.id N₀) (Set.range (Set.inclusion hDN))) :
    ∃ N N' : Set P, IsClosed N ∧ IsClosed N' ∧ D ⊆ interior N' ∧ N' ⊆ interior N ∧
      ∃ G : C(N × unitInterval, P), IsProperMap G ∧ (∀ y, G (y, 0) = y) ∧
        (∀ y, G (y, 1) ∈ D) ∧ (∀ y : N, ∀ t, (y : P) ∈ D → G (y, t) = y) := by
  obtain ⟨u₁, hu₁, hDu₁, hcu₁⟩ := normal_exists_closure_subset hD hN₀ hDN
  obtain ⟨u₂, hu₂, hDu₂, hcu₂⟩ := normal_exists_closure_subset hD hu₁ hDu₁
  let F := H.symm
  let G : C(closure u₁ × unitInterval, P) :=
    ⟨fun p ↦ (F (p.2, ⟨p.1.1, hcu₁ p.1.2⟩) : P), by fun_prop⟩
  have : CompactSpace (closure u₁ × unitInterval) := by
    haveI := isCompact_iff_compactSpace.1 (isClosed_closure (s := u₁)).isCompact
    infer_instance
  refine ⟨closure u₁, closure u₂, isClosed_closure, isClosed_closure,
    hDu₂.trans (interior_maximal subset_closure hu₂), hcu₂.trans
      (interior_maximal subset_closure hu₁), G, G.continuous.isProperMap, fun y ↦ ?_,
    fun y ↦ ?_, fun y t hy ↦ ?_⟩
  · change ((F (0, _) : N₀) : P) = y
    rw [F.apply_zero]; rfl
  · change ((F (1, _) : N₀) : P) ∈ D
    rw [F.apply_one]
    exact (r _).2
  · change ((F (t, _) : N₀) : P) = y
    rw [F.eq_fst t ⟨⟨y, hy⟩, rfl⟩]; rfl

/-- On a compact space every locally finite chain is finite: `ofFinsupp` is bijective. -/
private lemma bijective_ofFinsupp {R : Type u} [CommRing R] (X : TopCat.{u}) [CompactSpace X]
    (n : ℕ) : Function.Bijective (ofFinsupp (R := R) (X := X) (n := n)) := by
  refine ⟨fun f g h ↦ ?_, fun c ↦ ?_⟩
  · ext τ
    have := congrFun (congrArg Subtype.val h) ((SingularCochain.simplexEquiv X _).symm τ)
    simpa [ofFinsupp_apply] using this
  · have hc : (Function.support c.1).Finite := by
      refine (c.2.finite_inter_compact isCompact_univ).subset fun σ hσ ↦ ⟨hσ, ?_⟩
      obtain ⟨x, hx⟩ := nonempty_singularSimplexImage σ
      exact ⟨x, hx, trivial⟩
    exact ⟨toFinsupp c hc, ofFinsupp_toFinsupp c hc⟩

/-- **Locally finite chains on the complement of a compact pair.** Let `P` be compact
metrizable and `D ⊆ P` closed, such that every open neighbourhood of `D` contains an open
neighbourhood `N` of `D` admitting a deformation retraction onto `D`: a retraction
`r : N → D` whose composite with the inclusion is homotopic to the identity of `N` relative to
`D`. Then restriction of locally finite chains from `P` to the
open complement `U = P - D` vanishes on the chains of `D`, and the induced map from the relative
complex `C_•(P) / C_•(D)` to the complex of locally finite chains on `U` is a quasi-isomorphism:
`H^BM_•(U; M) ≅ H_•(P, D; M)`. If moreover `U` is compact, every locally finite chain on `U`
is finite: the inclusion `MMP.borelMooreHomology.ofFinsupp` of finite singular
chains into locally finite chains on `U` is bijective in every degree. -/
@[mmp "lem_mmp_bm_finite_pair_comparison"]
public theorem exists_quasiIso_cokernel_restrictChainMap {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) (P : TopCat.{u}) [CompactSpace P] [MetrizableSpace P]
    {D : Set P} (hD : IsClosed D)
    (hN : ∀ V : Set P, IsOpen V → D ⊆ V → ∃ N : Set P, IsOpen N ∧ N ⊆ V ∧ ∃ hDN : D ⊆ N,
      ∃ r : C(N, D), (∀ x : D, r (Set.inclusion hDN x) = x) ∧
        ((⟨Set.inclusion hDN, continuous_inclusion hDN⟩ : C(D, N)).comp r).HomotopicRel
          (ContinuousMap.id N) (Set.range (Set.inclusion hDN))) :
    ∃ f : cokernel (MMP.borelMooreHomology.chainMap R M
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of D ⟶ P)
          hD.isProperMap_subtypeVal) ⟶
        MMP.borelMooreChainComplex R M (TopCat.of (⟨Dᶜ, hD.isOpen_compl⟩ : Opens P)),
      cokernel.π _ ≫ f =
        MMP.borelMooreHomology.restrictChainMap R M ⟨Dᶜ, hD.isOpen_compl⟩ ∧
      QuasiIso f ∧
      (CompactSpace (Dᶜ : Set P) → ∀ n : ℕ, Function.Bijective
        (MMP.borelMooreHomology.ofFinsupp (R := R)
          (X := TopCat.of (⟨Dᶜ, hD.isOpen_compl⟩ : Opens P)) (n := n))) := by
  obtain ⟨N₀, hN₀, -, hDN, r, -, ⟨H⟩⟩ := hN Set.univ isOpen_univ (Set.subset_univ D)
  obtain ⟨N, N', hN, hN', hDN', hN'N, G, hG, hG0, hG1, hGX⟩ := exists_deformation hD hN₀ hDN r H
  refine ⟨cokernel.desc _ (restrictChainMap R M (complOpens hD))
      (chainMap_subspaceInclusion_comp_restrictChainMap R M hD), cokernel.π_desc _ _ _,
    quasiIso_cokernelDesc_of_homotopy M hD hN hN' hDN' hN'N hG hG0 hG1 hGX,
    fun _ ↦ bijective_ofFinsupp _⟩

end BorelMoore

section Toolkit

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry

attribute [-instance] Stacks.Cohomology.SpectralLimit.hasSheafifyOpensMax

/-- Flasqueness of presheaves is invariant under isomorphism. -/
private lemma isFlasque_of_iso {X : TopCat.{u}} {F G : TopCat.Presheaf AddCommGrpCat.{u} X}
    (e : F ≅ G) [F.IsFlasque] : G.IsFlasque where
  epi {U V} i := by
    have : G.map i = e.inv.app U ≫ F.map i ≫ e.hom.app V := by
      rw [← e.inv.naturality_assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [this]
    infer_instance

/-- The restriction of a flasque sheaf to an open subset is flasque. -/
private lemma isFlasque_pullback_inclusion {X : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    [hF : F.IsFlasque] (U : Opens X) :
    TopCat.Sheaf.IsFlasque ((TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion').obj F) := by
  have hf := U.isOpenEmbedding
  have h : TopCat.Presheaf.IsFlasque ((hf.sheafPullback AddCommGrpCat.{u}).obj F).obj :=
    ⟨fun i => by
      change Epi (F.obj.map (hf.isOpenMap.functor.map i.unop).op)
      exact hF.epi _⟩
  exact @isFlasque_of_iso _ _ _ ((sheafToPresheaf _ _).mapIso
    ((hf.sheafPullbackIso AddCommGrpCat.{u}).app F).symm) h

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- Global sections are additive, being sheaf-to-presheaf followed by evaluation at `⊤`. -/
theorem globalSections_additive (S : TopCat.{u}) : (globalSections S).Additive :=
  inferInstanceAs (sheafToPresheaf (Opens.grothendieckTopology S) AddCommGrpCat.{u} ⋙
    (evaluation (Opens S)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)).Additive

attribute [local instance] globalSections_additive

private theorem globalSections_preservesFiniteLimits (S : TopCat.{u}) :
    PreservesFiniteLimits (globalSections S) :=
  inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf (Opens.grothendieckTopology S)
    AddCommGrpCat.{u} ⋙ (evaluation (Opens S)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)))

attribute [local instance] globalSections_preservesFiniteLimits

/-- A flasque abelian sheaf has vanishing higher cohomology. -/
private lemma isZero_rightDerived_globalSections_of_isFlasque (S : TopCat.{u})
    (G : TopCat.Sheaf AddCommGrpCat.{u} S) (hG : G.IsFlasque)
    (n : ℕ) (hn : 0 < n) : IsZero (((globalSections S).rightDerived n).obj G) := by
  have hle := Functor.le_rightAcyclic (globalSections S)
    (fun H : TopCat.Sheaf AddCommGrpCat.{u} S => H.IsFlasque)
    (fun H => by
      obtain ⟨p⟩ := EnoughInjectives.presentation H
      let _ := p.injective
      exact ⟨p.J, Stacks.Cohomology.CechOne.isFlasque_of_injective p.J, p.f, p.mono⟩)
    (fun X hX h₁ h₂ => by
      let _ : X.X₁.IsFlasque := h₁
      let _ : X.X₂.IsFlasque := h₂
      refine ⟨TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hX, ?_⟩
      have hMap := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
        (globalSections S)).mp inferInstance X hX
      have : Mono (X.map (globalSections S)).f := hMap.2
      have : Epi (X.map (globalSections S)).g :=
        TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := ⊤) hX
      exact ⟨hMap.1⟩)
  exact (Stacks.Cohomology.rightAcyclic_iff_isZero_rightDerived (globalSections S) G).1
    (hle G hG) n hn

section Comparison

/-! The comparison of a resolution with an injective resolution. Only exactness of the source
resolution is used, exactly as in `InjectiveResolution.desc`. -/

open HomologicalComplex CochainComplex Injective

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {Z : C} {A : CochainComplex C ℕ}
  (ι : (single₀ C).obj Z ⟶ A) [QuasiIso ι]

include ι in
private lemma exact_succ' (n : ℕ) :
    (ShortComplex.mk _ _ (A.d_comp_d n (n + 1) (n + 2))).Exact := by
  have h : A.ExactAt (n + 1) := by
    rw [← quasiIsoAt_iff_exactAt ι (n + 1) (exactAt_succ_single_obj _ _)]
    infer_instance
  exact (HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp)
    (by simp only [CochainComplex.next]; rfl)).1 h

omit [QuasiIso ι] in
@[reassoc]
private lemma ι_f_zero_comp_d : ι.f 0 ≫ A.d 0 1 = 0 := by
  have h1 : ι.f 1 = 0 := (isZero_single_obj_X _ _ _ _ (by simp)).eq_of_src _ _
  rw [ι.comm, h1, comp_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def isLimitKernelFork' :
    IsLimit (KernelFork.ofι (f := A.d 0 1) _ (ι_f_zero_comp_d ι)) := by
  refine IsLimit.ofIsoLimit (A.cyclesIsKernel 0 1 (by simp)) (Iso.symm ?_)
  refine Fork.ext ((singleObjHomologySelfIso _ _ _).symm ≪≫
    isoOfQuasiIsoAt ι 0 ≪≫ A.isoHomologyπ₀.symm) ?_
  rw [← cancel_epi (singleObjHomologySelfIso (ComplexShape.up ℕ) _ _).hom,
    ← cancel_epi (isoHomologyπ₀ _).hom,
    ← cancel_epi (singleObjCyclesSelfIso (ComplexShape.up ℕ) _ _).inv]
  simp

private lemma exact₀' : (ShortComplex.mk _ _ (ι_f_zero_comp_d ι)).Exact :=
  ShortComplex.exact_of_f_is_kernel _ (isLimitKernelFork' ι)

private lemma mono_ι_f_zero : Mono (ι.f 0) :=
  mono_of_isLimit_fork (isLimitKernelFork' ι)

variable {Y : C} (f : Z ⟶ Y) (I : InjectiveResolution Y)

private noncomputable def descFZero' : A.X 0 ⟶ I.cocomplex.X 0 :=
  @factorThru _ _ _ _ _ _ (f ≫ I.ι.f 0) (ι.f 0) (mono_ι_f_zero ι)

private lemma ι_f_zero_comp_descFZero' : ι.f 0 ≫ descFZero' ι f I = f ≫ I.ι.f 0 :=
  @comp_factorThru _ _ _ _ _ _ (f ≫ I.ι.f 0) (ι.f 0) (mono_ι_f_zero ι)

private noncomputable def descFOne' : A.X 1 ⟶ I.cocomplex.X 1 :=
  (exact₀' ι).descToInjective (descFZero' ι f I ≫ I.cocomplex.d 0 1)
    (by
      change ι.f 0 ≫ descFZero' ι f I ≫ I.cocomplex.d 0 1 = 0
      rw [← Category.assoc, ι_f_zero_comp_descFZero']
      exact (Category.assoc f _ _).trans
        ((congrArg (f ≫ ·) I.ι_f_zero_comp_complex_d).trans comp_zero))

private lemma descFOne'_zero_comm :
    A.d 0 1 ≫ descFOne' ι f I = descFZero' ι f I ≫ I.cocomplex.d 0 1 :=
  (exact₀' ι).comp_descToInjective _ _

private noncomputable def desc' : A ⟶ I.cocomplex :=
  CochainComplex.mkHom _ _ (descFZero' ι f I) (descFOne' ι f I) (descFOne'_zero_comm ι f I).symm
    fun n ⟨g, g', w⟩ => ⟨(exact_succ' ι n).descToInjective
      (g' ≫ I.cocomplex.d (n + 1) (n + 2)) (by simp [reassoc_of% w.symm]),
      ((exact_succ' ι n).comp_descToInjective _ _).symm⟩

set_option backward.isDefEq.respectTransparency.types false in
private lemma desc'_commutes : ι ≫ desc' ι f I = (single₀ C).map f ≫ I.ι := by
  ext
  simp only [HomologicalComplex.comp_f, desc', CochainComplex.mkHom_f_0]
  rw [ι_f_zero_comp_descFZero']
  simp

private lemma desc'_id_commutes (I : InjectiveResolution Z) : ι ≫ desc' ι (𝟙 Z) I = I.ι := by
  simp [desc'_commutes]

variable {ι} {L : CochainComplex C ℕ} [∀ n, Injective (L.X n)]

private noncomputable def descHomotopyZeroZero' (g : A ⟶ L) (comm : ι ≫ g = 0) :
    A.X 1 ⟶ L.X 0 :=
  (exact₀' ι).descToInjective (g.f 0) (congr_fun (congr_arg HomologicalComplex.Hom.f comm) 0)

private lemma comp_descHomotopyZeroZero' (g : A ⟶ L) (comm : ι ≫ g = 0) :
    A.d 0 1 ≫ descHomotopyZeroZero' g comm = g.f 0 :=
  (exact₀' ι).comp_descToInjective _ _

private noncomputable def descHomotopyZeroOne' (g : A ⟶ L) (comm : ι ≫ g = 0) :
    A.X 2 ⟶ L.X 1 :=
  (exact_succ' ι 0).descToInjective (g.f 1 - descHomotopyZeroZero' g comm ≫ L.d 0 1)
    (by dsimp; rw [Preadditive.comp_sub, ← Category.assoc, comp_descHomotopyZeroZero' g comm,
          HomologicalComplex.Hom.comm, sub_self])

private lemma comp_descHomotopyZeroOne' (g : A ⟶ L) (comm : ι ≫ g = 0) :
    A.d 1 2 ≫ descHomotopyZeroOne' g comm =
      g.f 1 - descHomotopyZeroZero' g comm ≫ L.d 0 1 :=
  (exact_succ' ι 0).comp_descToInjective _ _

private noncomputable def descHomotopyZeroSucc' (g : A ⟶ L) (n : ℕ)
    (h : A.X (n + 1) ⟶ L.X n) (h' : A.X (n + 2) ⟶ L.X (n + 1))
    (w : g.f (n + 1) = A.d (n + 1) (n + 2) ≫ h' + h ≫ L.d n (n + 1)) :
    A.X (n + 3) ⟶ L.X (n + 2) :=
  (exact_succ' ι (n + 1)).descToInjective (g.f (n + 2) - h' ≫ L.d _ _) (by
      dsimp
      rw [Preadditive.comp_sub, ← HomologicalComplex.Hom.comm, w, Preadditive.add_comp,
        Category.assoc, Category.assoc, HomologicalComplex.d_comp_d, comp_zero,
        add_zero, sub_self])

private lemma comp_descHomotopyZeroSucc' (g : A ⟶ L) (n : ℕ)
    (h : A.X (n + 1) ⟶ L.X n) (h' : A.X (n + 2) ⟶ L.X (n + 1))
    (w : g.f (n + 1) = A.d (n + 1) (n + 2) ≫ h' + h ≫ L.d n (n + 1)) :
    A.d (n + 2) (n + 3) ≫ descHomotopyZeroSucc' (ι := ι) g n h h' w =
      g.f (n + 2) - h' ≫ L.d _ _ :=
  (exact_succ' ι (n + 1)).comp_descToInjective _ _

private noncomputable def descHomotopyZero' (g : A ⟶ L) (comm : ι ≫ g = 0) :
    Homotopy g 0 :=
  Homotopy.mkCoinductive _ (descHomotopyZeroZero' g comm)
    (by simp [comp_descHomotopyZeroZero'])
    (descHomotopyZeroOne' g comm) (by simp [comp_descHomotopyZeroOne'])
    (fun n ⟨h, h', w⟩ =>
      ⟨descHomotopyZeroSucc' (ι := ι) g n h h' (by simp only [w, add_comm]),
        by simp [comp_descHomotopyZeroSucc']⟩)

/-- Two maps from a resolution into an injective resolution over the same map are homotopic. -/
private noncomputable def homotopyOfComm {F' : C} {φ : Z ⟶ F'} {J : InjectiveResolution F'}
    (ι : (single₀ C).obj Z ⟶ A) [QuasiIso ι] (g g' : A ⟶ J.cocomplex)
    (hg : ι ≫ g = (single₀ C).map φ ≫ J.ι) (hg' : ι ≫ g' = (single₀ C).map φ ≫ J.ι) :
    Homotopy g g' :=
  Homotopy.equivSubZero.invFun (descHomotopyZero' (ι := ι) _ (by simp [hg, hg']))

/-- Two maps from a resolution into a complex of injectives which agree on the resolved object
are homotopic. -/
private noncomputable def homotopyOfCommZero (ι : (single₀ C).obj Z ⟶ A) [QuasiIso ι]
    (g g' : A ⟶ L) (h : ι.f 0 ≫ g.f 0 = ι.f 0 ≫ g'.f 0) : Homotopy g g' :=
  Homotopy.equivSubZero.invFun (descHomotopyZero' (ι := ι) _ (by
    ext
    simp only [HomologicalComplex.comp_f, HomologicalComplex.sub_f_apply, Preadditive.comp_sub,
      HomologicalComplex.zero_f_apply]
    rw [h, sub_self]))

end Comparison

/-- An acyclic resolution computes sheaf cohomology, compatibly with the comparison maps into
injective resolutions. -/
private theorem sheafCohomology_eq_of_acyclic_resolution (T : TopCat.{u}) :
    (∀ {F : TopCat.Sheaf AddCommGrpCat.{u} T}
        (A : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℕ)
        (ι : (CochainComplex.single₀ _).obj F ⟶ A), QuasiIso ι →
        (∀ (q n : ℕ), 0 < n → IsZero
          (((globalSections T).rightDerived n).obj (A.X q))) →
        ∀ n : ℕ, ∃ e : (HomologicalComplex.homologyFunctor _ _ n).obj
            (((globalSections T).mapHomologicalComplex _).obj A) ≅
            ((globalSections T).rightDerived n).obj F,
          ∀ {F' : TopCat.Sheaf AddCommGrpCat.{u} T} (φ : F ⟶ F') (J : InjectiveResolution F')
            (g : A ⟶ J.cocomplex), ι ≫ g = (CochainComplex.single₀ _).map φ ≫ J.ι →
            HomologicalComplex.homologyMap
                (((globalSections T).mapHomologicalComplex _).map g) n ≫
              (J.isoRightDerivedObj (globalSections T) n).inv =
            e.hom ≫ ((globalSections T).rightDerived n).map φ) := by
  intro F A ι hι hA n
  let Γ := globalSections T
  let J0 := injectiveResolution F
  let g0 : A ⟶ J0.cocomplex := desc' ι (𝟙 F) J0
  have hg0 : ι ≫ g0 = J0.ι := desc'_id_commutes ι J0
  have : QuasiIso g0 := by
    have : QuasiIso (ι ≫ g0) := by rw [hg0]; infer_instance
    exact quasiIso_of_comp_left ι g0
  have hAac : ∀ q, Γ.rightAcyclic (A.X q) := fun q =>
    (Stacks.Cohomology.rightAcyclic_iff_isZero_rightDerived Γ _).2 (hA q)
  have hJac : ∀ q, Γ.rightAcyclic (J0.cocomplex.X q) := fun q =>
    Stacks.Cohomology.Leray.rightAcyclic_of_injective Γ _ inferInstance
  have hiso : IsIso (HomologicalComplex.homologyMap ((Γ.mapHomologicalComplex _).map g0) n) := by
    convert Stacks.AcyclicQuasiIso.isIso_homologyMap_map Γ g0 hAac hJac n
  refine ⟨@asIso _ _ _ _ _ hiso ≪≫
    (J0.isoRightDerivedObj Γ n).symm, ?_⟩
  intro F' φ J g hg
  have h := InjectiveResolution.isoRightDerivedObj_inv_naturality φ J0 J
    (InjectiveResolution.desc φ J J0) (InjectiveResolution.desc_commutes_zero φ J J0) Γ n
  have key : HomologicalComplex.homologyMap ((Γ.mapHomologicalComplex _).map g) n =
      HomologicalComplex.homologyMap ((Γ.mapHomologicalComplex _).map g0) n ≫
        HomologicalComplex.homologyMap
          ((Γ.mapHomologicalComplex _).map (InjectiveResolution.desc φ J J0)) n := by
    rw [← HomologicalComplex.homologyMap_comp, ← Functor.map_comp]
    refine (Γ.mapHomotopy (homotopyOfComm ι g (g0 ≫ InjectiveResolution.desc φ J J0) hg ?_)
      ).homologyMap_eq n
    rw [reassoc_of% hg0, InjectiveResolution.desc_commutes]
  exact (congrArg (· ≫ (J.isoRightDerivedObj Γ n).inv) key).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (HomologicalComplex.homologyMap ((Γ.mapHomologicalComplex _).map g0) n ≫ ·)
        h.symm).trans (Category.assoc _ _ _).symm))

section GodementResolution

open CokernelCoresolution

/-- `f` followed by the cokernel projection and a monomorphism is exact. -/
private lemma exact_cokernel_π_comp_mono {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {X Y W : C} (f : X ⟶ Y) (m : cokernel f ⟶ W) [Mono m] :
    (ShortComplex.mk f (cokernel.π f ≫ m) (by simp)).Exact := by
  let α : ShortComplex.mk f (cokernel.π f) (by simp) ⟶
      ShortComplex.mk f (cokernel.π f ≫ m) (by simp) :=
    { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := m }
  have : Epi α.τ₁ := by dsimp [α]; infer_instance
  have : IsIso α.τ₂ := by dsimp [α]; infer_instance
  have : Mono α.τ₃ := by dsimp [α]; infer_instance
  rw [← ShortComplex.exact_iff_of_epi_of_isIso_of_mono α]
  exact ShortComplex.exact_cokernel f

/-- A coresolution built from cokernels and a pointwise monomorphic `η` is a resolution. -/
private lemma quasiIso_augmentation {C : Type u₁} [Category.{v₁} C] [Abelian C]
    (G : C ⥤ C) (η : 𝟭 C ⟶ G) (hη : ∀ X, Mono (η.app X)) (F : C) :
    QuasiIso (augmentation G η F) := ⟨fun n => by
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · have h := exact_cokernel_π_comp_mono (η.app F) (η.app (cokernel (η.app F)))
      have hm := hη F
      refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2 ⟨h, hm⟩
      exact ShortComplex.isoMk (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F)
        (Iso.refl _) (Iso.refl _)
        (by
          simp only [Functor.id_obj, CochainComplex.single₀ObjXSelf,
            CochainComplex.single₀_obj_zero, Iso.refl_hom,
            HomologicalComplex.shortComplexFunctor'_map_τ₂, augmentation_f_zero, Category.id_comp]
          exact (Category.id_comp _).trans (Category.comp_id _).symm)
        (by
          simp only [Functor.id_obj, Iso.refl_hom,
            HomologicalComplex.shortComplexFunctor'_obj_g, complex_d, d_zero]
          exact (Category.id_comp _).trans (Category.comp_id _).symm)
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt]
    · rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 1 + 1) (by simp) (by simp)]
      have h := exact_cokernel_π_comp_mono (d G η F n) (η.app (cokernel (d G η F n)))
      refine (ShortComplex.exact_iff_of_iso ?_).2 h
      refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
      · simp only [Iso.refl_hom, HomologicalComplex.shortComplexFunctor'_obj_f, complex_d]
        exact (Category.id_comp _).trans (Category.comp_id _).symm
      · simp only [Iso.refl_hom, HomologicalComplex.shortComplexFunctor'_obj_g, complex_d, d_succ]
        exact (Category.id_comp _).trans (Category.comp_id _).symm
    · apply CochainComplex.exactAt_succ_single_obj⟩

/-- The Godement sheaf of discontinuous sections is flasque: a family of germs over `V ⊆ U`
extends by zero to `U`. -/
private lemma isFlasque_godementFunctor_obj {T : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} T) :
    TopCat.Sheaf.IsFlasque ((godementFunctor T).obj F) :=
  ⟨fun {U V} i => (AddCommGrpCat.epi_iff_surjective _).2 fun t => by
    classical
    refine ⟨fun x => if h : x.1 ∈ V.unop then t ⟨x.1, h⟩ else 0, funext fun x => ?_⟩
    change (if h : x.1 ∈ V.unop then t ⟨x.1, h⟩ else 0) = t x
    rw [dif_pos x.2]⟩

/-- The unit `F ⟶ G(F)` of the Godement construction is a monomorphism: a section is determined
by its germs. -/
lemma mono_godementUnit_app {T : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} T) :
    Mono ((godementUnit T).app F) := by
  have : ∀ U, Mono (((godementUnit T).app F).hom.app U) := fun U =>
    (AddCommGrpCat.mono_iff_injective _).2 (godementUnit_app_hom_app_injective F U)
  have : Mono ((godementUnit T).app F).hom := NatTrans.mono_of_mono_app _
  exact Sheaf.Hom.mono_of_presheaf_mono _ _ _

/-- The Godement resolution is a flasque resolution. -/
private theorem godementResolution_flasque_resolution (T : TopCat.{u}) :
    (∀ F : TopCat.Sheaf AddCommGrpCat.{u} T, QuasiIso (godementAugmentation T F) ∧
        ∀ q : ℕ, TopCat.Sheaf.IsFlasque (((godementResolution T).obj F).X q)) := by
  refine fun F => ⟨quasiIso_augmentation (godementFunctor T) (godementUnit T)
    mono_godementUnit_app F, fun q => ?_⟩
  cases q <;> exact isFlasque_godementFunctor_obj _

end GodementResolution

section CoresolutionExact

/-! Exactness of the coresolution built from cokernels and an exact functor `G` with a pointwise
monomorphic unit: each term is an exact functor of the input. -/

open CokernelCoresolution

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]

/-- A morphism of short exact sequences whose third component is a monomorphism induces a short
exact sequence of cokernels (snake lemma). -/
private lemma cokernelRow_shortExact {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) [Mono φ.τ₃] :
    (ShortComplex.mk (cokernel.map φ.τ₁ φ.τ₂ S₁.f S₂.f φ.comm₁₂)
      (cokernel.map φ.τ₂ φ.τ₃ S₁.g S₂.g φ.comm₂₃)
      (by ext; simp [S₂.zero])).ShortExact := by
  let SI : ShortComplex.SnakeInput C :=
    { L₀ := ShortComplex.mk (kernel.map φ.τ₁ φ.τ₂ S₁.f S₂.f φ.comm₁₂)
        (kernel.map φ.τ₂ φ.τ₃ S₁.g S₂.g φ.comm₂₃)
        (by ext; simp [S₁.zero])
      L₁ := S₁
      L₂ := S₂
      L₃ := ShortComplex.mk (cokernel.map φ.τ₁ φ.τ₂ S₁.f S₂.f φ.comm₁₂)
        (cokernel.map φ.τ₂ φ.τ₃ S₁.g S₂.g φ.comm₂₃)
        (by ext; simp [S₂.zero])
      v₀₁ := { τ₁ := kernel.ι _, τ₂ := kernel.ι _, τ₃ := kernel.ι _ }
      v₁₂ := φ
      v₂₃ := { τ₁ := cokernel.π _, τ₂ := cokernel.π _, τ₃ := cokernel.π _ }
      w₀₂ := by ext <;> simp
      w₁₃ := by ext <;> simp
      h₀ := by
        apply ShortComplex.isLimitOfIsLimitπ <;>
          apply (KernelFork.isLimitMapConeEquiv _ _).2 <;> exact kernelIsKernel _
      h₃ := by
        apply ShortComplex.isColimitOfIsColimitπ <;>
          apply (CokernelCofork.isColimitMapCoconeEquiv _ _).2 <;> exact cokernelIsCokernel _
      L₁_exact := h₁.exact
      epi_L₁_g := h₁.epi_g
      L₂_exact := h₂.exact
      mono_L₂_f := h₂.mono_f }
  have hz : IsZero SI.L₀.X₃ := by
    dsimp [SI]; exact isZero_kernel_of_mono _
  have hm : Mono SI.L₃.f := SI.L₂'_exact.mono_g (hz.eq_of_src _ _)
  have : Epi SI.L₂.g := h₂.epi_g
  exact { exact := SI.L₃_exact, mono_f := hm, epi_g := SI.epi_L₃_g }

/-- The variant of `cokernelRow_shortExact` for the composite with an epimorphism of short
complexes. -/
private lemma cokernelRow_shortExact_of_epi {S₀ S₁ S₂ : ShortComplex C} (p : S₀ ⟶ S₁)
    (φ : S₁ ⟶ S₂) (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) [Epi p.τ₁] [Epi p.τ₂] [Epi p.τ₃]
    [Mono φ.τ₃] :
    (ShortComplex.mk (cokernel.map (p.τ₁ ≫ φ.τ₁) (p.τ₂ ≫ φ.τ₂) S₀.f S₂.f (p ≫ φ).comm₁₂)
      (cokernel.map (p.τ₂ ≫ φ.τ₂) (p.τ₃ ≫ φ.τ₃) S₀.g S₂.g (p ≫ φ).comm₂₃)
      (by ext; simp [S₂.zero])).ShortExact := by
  refine ShortComplex.shortExact_of_iso ?_ (cokernelRow_shortExact φ h₁ h₂)
  refine ShortComplex.isoMk (cokernelEpiComp _ _).symm (cokernelEpiComp _ _).symm
    (cokernelEpiComp _ _).symm ?_ ?_ <;>
  · rw [← cancel_epi (cokernel.π _)]
    simp [cokernelEpiComp]

variable (G : C ⥤ C) [G.PreservesZeroMorphisms] (η : 𝟭 C ⟶ G)

private lemma cokerDesc_comp {F F' F'' : C} (a : F ⟶ F') (b : F' ⟶ F'') (n : ℕ) :
    cokerDesc (stageHom (idLift G η) (a ≫ b) n) =
      cokerDesc (stageHom (idLift G η) a n) ≫ cokerDesc (stageHom (idLift G η) b n) := by
  refine coequalizer.hom_ext ?_
  change cokernel.π _ ≫ _ = cokernel.π _ ≫ _
  rw [π_cokerDesc, π_cokerDesc_assoc]
  change homX (idLift G η) (a ≫ b) n ≫ _ = homX (idLift G η) a n ≫ _
  rw [homX_comp, Category.assoc]
  erw [π_cokerDesc]

private lemma cokerDesc_zero (F F' : C) (n : ℕ) :
    cokerDesc (stageHom (idLift G η) (0 : F ⟶ F') n) = 0 := by
  refine coequalizer.hom_ext ?_
  change cokernel.π _ ≫ _ = cokernel.π _ ≫ _
  rw [π_cokerDesc, comp_zero]
  change homX (idLift G η) (0 : F ⟶ F') n ≫ _ = 0
  rw [homX_zero_hom, zero_comp]

variable (S : ShortComplex C)

/-- The short complex of the cokernels of the `n`-th stage maps. -/
private noncomputable def zRow (n : ℕ) : ShortComplex C :=
  ShortComplex.mk (cokerDesc (stageHom (idLift G η) S.f n))
    (cokerDesc (stageHom (idLift G η) S.g n)) (by
      rw [← cokerDesc_comp, S.zero, cokerDesc_zero])

/-- The short complex of the `n`-th terms of the coresolutions. -/
private noncomputable def xRow (n : ℕ) : ShortComplex C :=
  ShortComplex.mk (homX (idLift G η) S.f n) (homX (idLift G η) S.g n) (by
      rw [← homX_comp, S.zero, homX_zero_hom])

variable (hG : ∀ S : ShortComplex C, S.ShortExact → (S.map G).ShortExact)
  (hη : ∀ X, Mono (η.app X)) {S} (hS : S.ShortExact)

include hG hη hS in
private lemma zRow_shortExact (n : ℕ) : (zRow G η S n).ShortExact := by
  induction n with
  | zero =>
    let φ : S ⟶ S.map G := ShortComplex.Hom.mk (η.app _) (η.app _) (η.app _)
      (η.naturality S.f).symm (η.naturality S.g).symm
    have := hη S.X₃
    exact cokernelRow_shortExact φ hS (hG S hS)
  | succ n ih =>
    let Z := zRow G η S n
    let φ : Z ⟶ Z.map G := ShortComplex.Hom.mk (η.app _) (η.app _) (η.app _)
      (η.naturality Z.f).symm (η.naturality Z.g).symm
    have : Mono φ.τ₃ := hη _
    have hE : ∀ {X Y : C} (f : X ⟶ Y), Epi (cokernel.π f) := fun f => coequalizer.π_epi
    let p : xRow G η S n ⟶ Z := ShortComplex.Hom.mk (cokernel.π _) (cokernel.π _) (cokernel.π _)
      (by dsimp only [Z, zRow, xRow]; erw [π_cokerDesc]; rfl)
      (by dsimp only [Z, zRow, xRow]; erw [π_cokerDesc]; rfl)
    have : Epi p.τ₁ := hE _
    have : Epi p.τ₂ := hE _
    have : Epi p.τ₃ := hE _
    exact cokernelRow_shortExact_of_epi p φ ih (hG Z ih)

include hG hη hS in
/-- Each term of the coresolution is the image under `G` of a short exact sequence. -/
private lemma xRow_eq_map (n : ℕ) :
    ∃ Y : ShortComplex C, Y.ShortExact ∧ xRow G η S n = Y.map G := by
  cases n with
  | zero => exact ⟨S, hS, rfl⟩
  | succ n => exact ⟨zRow G η S n, zRow_shortExact G η hG hη hS n, rfl⟩

end CoresolutionExact

/-- The sections functor `Γ(U, -)` on sheaves of abelian groups on `S`; `globalSections S` is
`sectionsFunctor S (op ⊤)`. -/
abbrev sectionsFunctor (S : TopCat.{u}) (U : (Opens S)ᵒᵖ) :
    TopCat.Sheaf AddCommGrpCat.{u} S ⥤ AddCommGrpCat.{u} :=
  (sheafSections (Opens.grothendieckTopology S) AddCommGrpCat.{u}).obj U

/-- The sections functor `Γ(U, -)` preserves zero morphisms. -/
instance sectionsFunctor_preservesZeroMorphisms (S : TopCat.{u}) (U : (Opens S)ᵒᵖ) :
    (sectionsFunctor S U).PreservesZeroMorphisms :=
  inferInstanceAs ((sheafSections (Opens.grothendieckTopology S) AddCommGrpCat.{u}).obj
    U).PreservesZeroMorphisms

private lemma presheaf_shortExact_of_sections {J : Type*} [Category* J]
    (S : ShortComplex (J ⥤ AddCommGrpCat.{u}))
    (h : ∀ U, (S.map ((evaluation _ _).obj U)).ShortExact) : S.ShortExact := by
  have : ∀ U, Mono (S.f.app U) := fun U => (h U).mono_f
  have : ∀ U, Epi (S.g.app U) := fun U => (h U).epi_g
  have : Mono S.f := NatTrans.mono_of_mono_app _
  have : Epi S.g := NatTrans.epi_of_epi_app _
  refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
  rw [ShortComplex.exact_iff_isZero_homology]
  refine Functor.isZero _ fun U => ?_
  exact (ShortComplex.exact_iff_isZero_homology _ |>.1 (h U).exact).of_iso
    (S.mapHomologyIso ((evaluation _ _).obj U)).symm

private lemma sheaf_shortExact_of_sections {X : TopCat.{u}}
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X))
    (h : ∀ U, (S.map (sectionsFunctor X U)).ShortExact) : S.ShortExact :=
  ShortExact.reflects_shortExact_of_faithful
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (presheaf_shortExact_of_sections _ h)

private lemma godement_sections_shortExact (T : TopCat.{u})
    (Y : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T)) (hY : Y.ShortExact)
    (U : (Opens T)ᵒᵖ) : ((Y.map (godementFunctor T)).map (sectionsFunctor T U)).ShortExact := by
  have hst := fun x : T =>
    hY.map_of_exact (TopCat.Sheaf.forget _ T ⋙ TopCat.Presheaf.stalkFunctor _ x)
  have hinj := fun x : T => (AddCommGrpCat.mono_iff_injective _).1 (hst x).mono_f
  have hsurj := fun x : T => (AddCommGrpCat.epi_iff_surjective _).1 (hst x).epi_g
  have hex := fun x : T => (ShortComplex.ab_exact_iff _).1 (hst x).exact
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ab_exact_iff]
    intro s hs
    choose t ht using fun x : U.unop => hex x.1 (s x) (congrFun hs x)
    exact ⟨t, funext ht⟩
  · rw [AddCommGrpCat.mono_iff_injective]
    intro s s' hs
    exact funext fun x => hinj x.1 (congrFun hs x)
  · rw [AddCommGrpCat.epi_iff_surjective]
    intro s
    choose t ht using fun x : U.unop => hsurj x.1 (s x)
    exact ⟨t, funext ht⟩

/-- For a short exact sequence of abelian sheaves, the sections over any open `U` of the `n`-th
terms of their Godement resolutions form a short exact sequence of abelian groups. -/
theorem godementResolution_sections_shortExact (T : TopCat.{u})
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T)) (hS : S.ShortExact) (n : ℕ)
    (U : (Opens T)ᵒᵖ) :
    (S.map (godementResolution T ⋙ HomologicalComplex.eval _ _ n ⋙
      sectionsFunctor T U)).ShortExact := by
  obtain ⟨Y, hY, e⟩ := xRow_eq_map (godementFunctor T) (godementUnit T)
    (fun Y hY => sheaf_shortExact_of_sections _ (godement_sections_shortExact T Y hY))
    mono_godementUnit_app hS n
  change ((xRow (godementFunctor T) (godementUnit T) S n).map (sectionsFunctor T U)).ShortExact
  rw [e]
  exact godement_sections_shortExact T Y hY U

/-- For a short exact sequence of abelian sheaves, the global sections of the `n`-th terms of
their Godement resolutions form a short exact sequence of abelian groups. -/
theorem godementResolution_globalSections_shortExact (T : TopCat.{u})
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T)) (hS : S.ShortExact) (n : ℕ) :
    (S.map (godementResolution T ⋙ HomologicalComplex.eval _ _ n ⋙
      globalSections T)).ShortExact :=
  godementResolution_sections_shortExact T S hS n (op ⊤)

/-- Coproducts of short exact sequences of abelian groups are short exact. -/
private lemma sigma_shortExact {I : Type} (X₁ X₂ X₃ : I → AddCommGrpCat.{u})
    (f : ∀ i, X₁ i ⟶ X₂ i) (g : ∀ i, X₂ i ⟶ X₃ i) (w : ∀ i, f i ≫ g i = 0)
    (h : ∀ i, (ShortComplex.mk _ _ (w i)).ShortExact) :
    (ShortComplex.mk (Limits.Sigma.map f) (Limits.Sigma.map g) (by
      refine Sigma.hom_ext _ _ fun i => ?_
      simp [reassoc_of% w i])).ShortExact := by
  let S : ShortComplex (Discrete I ⥤ AddCommGrpCat.{u}) :=
    ShortComplex.mk (X₁ := Discrete.functor X₁) (X₂ := Discrete.functor X₂)
      (X₃ := Discrete.functor X₃) (Discrete.natTrans fun i => f i.as)
      (Discrete.natTrans fun i => g i.as)
      (by apply NatTrans.ext; funext ⟨i⟩; exact w i)
  have hS : S.ShortExact := presheaf_shortExact_of_sections S fun i => h i.as
  exact hS.map_of_exact colim

/-- The total complex of a degreewise short exact sequence of bicomplexes of abelian groups is
short exact. -/
private lemma total_shortExact {I₁ I₂ I₁₂ : Type} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
    (c₁₂ : ComplexShape I₁₂) [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
    (S : ShortComplex (HomologicalComplex₂ AddCommGrpCat.{u} c₁ c₂))
    (hS : ∀ i₁ i₂, (ShortComplex.mk ((S.f.f i₁).f i₂) ((S.g.f i₁).f i₂) (by
      rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, S.zero]; rfl)).ShortExact) :
    (ShortComplex.mk (HomologicalComplex₂.total.map S.f c₁₂)
      (HomologicalComplex₂.total.map S.g c₁₂) (by
        rw [← HomologicalComplex₂.total.map_comp, S.zero]
        ext n : 1
        exact HomologicalComplex₂.total.hom_ext _ fun _ _ _ => by simp)).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => ?_
  have h := sigma_shortExact (I := ComplexShape.π c₁ c₂ c₁₂ ⁻¹' {n})
    (fun i => (S.X₁.X i.1.1).X i.1.2) (fun i => (S.X₂.X i.1.1).X i.1.2)
    (fun i => (S.X₃.X i.1.1).X i.1.2) (fun i => (S.f.f i.1.1).f i.1.2)
    (fun i => (S.g.f i.1.1).f i.1.2) _ (fun i => hS i.1.1 i.1.2)
  refine ShortComplex.shortExact_of_iso (ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_) h
  · ext i
    simp
  · ext i
    simp

/-- A short complex of zero objects is short exact. -/
private lemma shortExact_of_isZero {C : Type*} [Category C] [Abelian C] (S : ShortComplex C)
    (h₁ : IsZero S.X₁) (h₂ : IsZero S.X₂) (h₃ : IsZero S.X₃) : S.ShortExact where
  exact := ShortComplex.exact_of_isZero_X₂ _ h₂
  mono_f := ⟨fun _ _ _ => h₁.eq_of_tgt _ _⟩
  epi_g := ⟨fun _ _ _ => h₃.eq_of_src _ _⟩

/-- Global sections of the Godement double complexes of a degreewise short exact sequence of
bounded complexes give a short exact sequence of total complexes. -/
private theorem total_godementSections_shortExact (T : TopCat.{u})
    (S : ShortComplex (CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ))
    (hS : ∀ i : ℤ, (S.map (HomologicalComplex.eval _ _ i)).ShortExact) :
    (ShortComplex.mk
            (HomologicalComplex₂.total.map
              (((godementSections T).mapHomologicalComplex _).map S.f) (ComplexShape.up ℤ))
            (HomologicalComplex₂.total.map
              (((godementSections T).mapHomologicalComplex _).map S.g) (ComplexShape.up ℤ))
            (by
              rw [← HomologicalComplex₂.total.map_comp, ← Functor.map_comp, S.zero,
                Functor.map_zero]
              ext n : 1
              exact HomologicalComplex₂.total.hom_ext _ fun _ _ _ => by simp)).ShortExact := by
  refine total_shortExact (ComplexShape.up ℤ) (S.map ((godementSections T).mapHomologicalComplex _))
    fun q p => ?_
  by_cases hp : ∃ m : ℕ, ComplexShape.embeddingUpNat.f m = p
  · obtain ⟨m, hm⟩ := hp
    have h0 := godementResolution_globalSections_shortExact T _ (hS q) m
    refine ShortComplex.shortExact_of_iso ((S.map (HomologicalComplex.eval _ _ q)).mapNatIso
      (Functor.isoWhiskerLeft (godementResolution T ⋙ (globalSections T).mapHomologicalComplex _)
        (ComplexShape.embeddingUpNat.extendFunctorCompEvalIso AddCommGrpCat.{u} hm)).symm) h0
  · push Not at hp
    refine shortExact_of_isZero _ ?_ ?_ ?_ <;>
      exact HomologicalComplex.isZero_extend_X _ _ _ hp

attribute [local instance] reflectsLimits_of_reflectsIsomorphisms in
/-- The inverse image of sheaves of abelian groups is left exact, `Opens.map f` being
representably flat. -/
private theorem pullback_preservesFiniteLimits {T T' : TopCat.{u}} (f : T' ⟶ T) :
    PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} f) := by
  unfold TopCat.Sheaf.pullback
  apply Functor.sheafPullbackConstruction.preservesFiniteLimits

section OneTerm

/-! The cohomology of a one-term complex. -/

/-- The inclusion of the zeroth row of a bicomplex into its total complex. -/
private noncomputable def rowZeroToTotal
    (B : HomologicalComplex₂ AddCommGrpCat.{u} (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (hB : ∀ q : ℤ, q ≠ 0 → IsZero (B.X q)) :
    B.X 0 ⟶ B.total (ComplexShape.up ℤ) where
  f p := B.ιTotal (ComplexShape.up ℤ) 0 p p (by simp)
  comm' p p' hpp' := by
    have h1 : IsZero ((B.X (0 + 1)).X p) :=
      (HomologicalComplex.eval _ _ p).map_isZero (hB _ (by simp))
    have hπ : ∀ a b : ℤ,
        ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, b) =
          a + b := fun _ _ => rfl
    have hp : p + 1 = p' := hpp'
    rw [HomologicalComplex₂.total_d, Preadditive.comp_add, HomologicalComplex₂.ι_D₁,
      HomologicalComplex₂.ι_D₂,
      HomologicalComplex₂.d₁_eq _ _ (show (ComplexShape.up ℤ).Rel 0 (0 + 1) from rfl)
        _ _ (by rw [hπ]; omega), HomologicalComplex₂.d₂_eq _ _ _ hpp' _
        (by rw [hπ]; omega)]
    rw [h1.eq_of_tgt ((B.d 0 (0 + 1)).f p) 0]
    simp

private lemma isIso_rowZeroToTotal
    (B : HomologicalComplex₂ AddCommGrpCat.{u} (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (hB : ∀ q : ℤ, q ≠ 0 → IsZero (B.X q)) : IsIso (rowZeroToTotal B hB) := by
  suffices h : ∀ p, IsIso ((rowZeroToTotal B hB).f p) from
    HomologicalComplex.Hom.isIso_of_components _
  intro p
  refine ⟨B.totalDesc (fun i₁ i₂ h => if h₁ : i₁ = 0 then
    (B.XXIsoOfEq _ _ _ h₁ (show i₂ = p by
      have h' : i₁ + i₂ = p := h
      omega)).hom
      else 0), ?_, ?_⟩
  · simp [rowZeroToTotal]
  · refine HomologicalComplex₂.total.hom_ext _ fun i₁ i₂ h => ?_
    by_cases h₁ : i₁ = 0
    · subst h₁
      have h₂ : i₂ = p := by
        have h' : 0 + i₂ = p := h
        omega
      subst h₂
      simp [rowZeroToTotal]
    · exact ((HomologicalComplex.eval _ _ i₂).map_isZero (hB _ h₁)).eq_of_src _ _

@[reassoc]
private lemma rowZeroToTotal_naturality
    {B B' : HomologicalComplex₂ AddCommGrpCat.{u} (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    (hB : ∀ q : ℤ, q ≠ 0 → IsZero (B.X q)) (hB' : ∀ q : ℤ, q ≠ 0 → IsZero (B'.X q))
    (φ : B ⟶ B') :
    rowZeroToTotal B hB ≫ HomologicalComplex₂.total.map φ (ComplexShape.up ℤ) =
      φ.f 0 ≫ rowZeroToTotal B' hB' := by
  ext p : 1
  simp [rowZeroToTotal]

end OneTerm

section SheafCohomologyIso

variable (S : TopCat.{u})

/-- The augmentation of the Godement resolution is natural. -/
@[reassoc]
private lemma godementAugmentation_naturality {F F' : TopCat.Sheaf AddCommGrpCat.{u} S}
    (a : F ⟶ F') :
    godementAugmentation S F ≫ (godementResolution S).map a =
      (CochainComplex.single₀ _).map a ≫ godementAugmentation S F' := by
  ext
  simp only [CochainComplex.single₀_obj_zero, godementResolution, godementAugmentation]
  exact ((godementUnit S).naturality a).symm

private lemma godementAugmentation_f_zero (F : TopCat.Sheaf AddCommGrpCat.{u} S) :
    (godementAugmentation S F).f 0 = (godementUnit S).app F := by
  rw [godementAugmentation, CokernelCoresolution.augmentation_f_zero]
  exact Category.id_comp _

private instance godementAugmentation_quasiIso (F : TopCat.Sheaf AddCommGrpCat.{u} S) :
    QuasiIso (godementAugmentation S F) :=
  (godementResolution_flasque_resolution S F).1

private lemma godementResolution_isZero_rightDerived (F : TopCat.Sheaf AddCommGrpCat.{u} S) :
    ∀ (q n : ℕ), 0 < n → IsZero
      (((globalSections S).rightDerived n).obj (((godementResolution S).obj F).X q)) :=
  fun q n hn => isZero_rightDerived_globalSections_of_isFlasque _ _
    ((godementResolution_flasque_resolution S F).2 q) n hn

/-- The identification of the cohomology of the global sections of the Godement resolution with
sheaf cohomology `R^nΓ(S, F)`. It is characterised by `MMP.Analytic.godementHomologyIso_spec`. -/
@[no_expose] noncomputable def godementHomologyIso (F : TopCat.Sheaf AddCommGrpCat.{u} S) (n : ℕ) :
    (((globalSections S).mapHomologicalComplex _).obj ((godementResolution S).obj F)).homology n ≅
      ((globalSections S).rightDerived n).obj F :=
  Classical.choose (sheafCohomology_eq_of_acyclic_resolution S _ (godementAugmentation S F)
    (godementResolution_flasque_resolution S F).1 (godementResolution_isZero_rightDerived S F) n)

/-- `MMP.Analytic.godementHomologyIso` is compatible with comparison maps: for `φ : F ⟶ F'`, an
injective resolution `J` of `F'` and a map `g` from the Godement resolution of `F` to `J` over
`φ`, the map induced by `g` on cohomology of global sections, followed by the identification
`H^n(Γ(S, J^•)) ≅ R^nΓ(S, F')`, is `godementHomologyIso` followed by `R^nΓ(S, φ)`. -/
lemma godementHomologyIso_spec (F : TopCat.Sheaf AddCommGrpCat.{u} S) (n : ℕ)
    {F' : TopCat.Sheaf AddCommGrpCat.{u} S} (φ : F ⟶ F') (J : InjectiveResolution F')
    (g : (godementResolution S).obj F ⟶ J.cocomplex)
    (hg : godementAugmentation S F ≫ g = (CochainComplex.single₀ _).map φ ≫ J.ι) :
    HomologicalComplex.homologyMap (((globalSections S).mapHomologicalComplex _).map g) n ≫
        (J.isoRightDerivedObj (globalSections S) n).inv =
      (godementHomologyIso S F n).hom ≫ ((globalSections S).rightDerived n).map φ :=
  Classical.choose_spec (sheafCohomology_eq_of_acyclic_resolution S _ (godementAugmentation S F)
    (godementResolution_flasque_resolution S F).1 (godementResolution_isZero_rightDerived S F) n)
    φ J g hg

private lemma godementHomologyIso_spec_id (F : TopCat.Sheaf AddCommGrpCat.{u} S) (n : ℕ)
    (J : InjectiveResolution F) (g : (godementResolution S).obj F ⟶ J.cocomplex)
    (hg : godementAugmentation S F ≫ g = J.ι) :
    HomologicalComplex.homologyMap (((globalSections S).mapHomologicalComplex _).map g) n ≫
        (J.isoRightDerivedObj (globalSections S) n).inv =
      (godementHomologyIso S F n).hom := by
  rw [godementHomologyIso_spec S F n (𝟙 F) J g (by simpa using hg), CategoryTheory.Functor.map_id,
    Category.comp_id]

private lemma godementHomologyIso_naturality {F F' : TopCat.Sheaf AddCommGrpCat.{u} S}
    (a : F ⟶ F') (n : ℕ) :
    HomologicalComplex.homologyMap
        (((globalSections S).mapHomologicalComplex _).map ((godementResolution S).map a)) n ≫
        (godementHomologyIso S F' n).hom =
      (godementHomologyIso S F n).hom ≫ ((globalSections S).rightDerived n).map a := by
  let J := injectiveResolution F'
  let g' := desc' (godementAugmentation S F') (𝟙 F') J
  have hg' : godementAugmentation S F' ≫ g' = J.ι := desc'_id_commutes _ J
  rw [← godementHomologyIso_spec_id S F' n J g' hg',
    ← godementHomologyIso_spec S F n a J ((godementResolution S).map a ≫ g')
      (by rw [godementAugmentation_naturality_assoc, hg'])]
  simp only [Functor.map_comp, HomologicalComplex.homologyMap_comp]
  exact (Category.assoc _ _ _).symm

/-- The one-term complex `F[0]`: its Godement double complex is concentrated in row zero. -/
private lemma isZero_godementSectionsDoubleComplex_single (F : TopCat.Sheaf AddCommGrpCat.{u} S)
    (q : ℤ) (hq : q ≠ 0) :
    IsZero ((godementSectionsDoubleComplex S
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)).X q) :=
  (godementSections S).map_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq)

/-- The total complex of the Godement double complex of `F[0]` is `Γ(S, G^•(F))`. -/
private noncomputable def totalSingleIso (F : TopCat.Sheaf AddCommGrpCat.{u} S) :
    (godementSectionsDoubleComplex S
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)).total (ComplexShape.up ℤ) ≅
      (godementSections S).obj F :=
  (@asIso _ _ _ _ (rowZeroToTotal _ (isZero_godementSectionsDoubleComplex_single S F))
    (isIso_rowZeroToTotal _ _)).symm ≪≫
    (godementSections S).mapIso (HomologicalComplex.singleObjXSelf _ 0 F)

private lemma totalSingleIso_naturality {F F' : TopCat.Sheaf AddCommGrpCat.{u} S} (a : F ⟶ F') :
    HomologicalComplex₂.total.map (((godementSections S).mapHomologicalComplex _).map
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map a)) (ComplexShape.up ℤ) ≫
        (totalSingleIso S F').hom =
      (totalSingleIso S F).hom ≫ (godementSections S).map a := by
  have hiso := isIso_rowZeroToTotal _ (isZero_godementSectionsDoubleComplex_single S F)
  rw [← cancel_epi (rowZeroToTotal _ (isZero_godementSectionsDoubleComplex_single S F))]
  simp only [totalSingleIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, Functor.mapIso_hom,
    Category.assoc, IsIso.hom_inv_id_assoc]
  rw [rowZeroToTotal_naturality_assoc _ (isZero_godementSectionsDoubleComplex_single S F')]
  simp only [IsIso.hom_inv_id_assoc, ← Functor.map_comp]
  congr 1
  simp [HomologicalComplex.single_map_f_self]

/-- Extension by zero from `ℕ` to `ℤ` does not change the cohomology of `Γ(S, G^•(F))`. -/
private noncomputable def godementSectionsHomologyIso (F : TopCat.Sheaf AddCommGrpCat.{u} S)
    (n : ℕ) :
    ((godementSections S).obj F).homology (n : ℤ) ≅
        (((globalSections S).mapHomologicalComplex _).obj
          ((godementResolution S).obj F)).homology n :=
  HomologicalComplex.extendHomologyIso _ ComplexShape.embeddingUpNat rfl

@[reassoc]
private lemma godementSectionsHomologyIso_naturality {F F' : TopCat.Sheaf AddCommGrpCat.{u} S}
    (a : F ⟶ F') (n : ℕ) :
    HomologicalComplex.homologyMap ((godementSections S).map a) n ≫
        (godementSectionsHomologyIso S F' n).hom =
      (godementSectionsHomologyIso S F n).hom ≫ HomologicalComplex.homologyMap
        (((globalSections S).mapHomologicalComplex _).map ((godementResolution S).map a)) n :=
  HomologicalComplex.extendHomologyIso_hom_naturality _ _ _

/-- `H^n(S, F) = ℍ^n(S, F[0])` is the cohomology of `Γ(S, G^•(F))`, the global sections of the
Godement resolution of `F`. -/
@[no_expose] noncomputable def sheafCohomologyGodementIso (F : TopCat.Sheaf AddCommGrpCat.{u} S)
    (n : ℕ) :
    (sheafCohomology S n).obj F ≅
        (((globalSections S).mapHomologicalComplex _).obj
          ((godementResolution S).obj F)).homology n :=
  HomologicalComplex.homologyMapIso (totalSingleIso S F) n ≪≫
    godementSectionsHomologyIso S F n

@[reassoc]
private lemma sheafCohomologyGodementIso_naturality {F F' : TopCat.Sheaf AddCommGrpCat.{u} S}
    (a : F ⟶ F') (n : ℕ) :
    (sheafCohomology S n).map a ≫ (sheafCohomologyGodementIso S F' n).hom =
      (sheafCohomologyGodementIso S F n).hom ≫ HomologicalComplex.homologyMap
        (((globalSections S).mapHomologicalComplex _).map ((godementResolution S).map a)) n := by
  have key : HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
      (((godementSections S).mapHomologicalComplex _).map
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map a)) (ComplexShape.up ℤ)) n ≫
      HomologicalComplex.homologyMap (totalSingleIso S F').hom n ≫
      (godementSectionsHomologyIso S F' n).hom =
      (HomologicalComplex.homologyMap (totalSingleIso S F).hom n ≫
      (godementSectionsHomologyIso S F n).hom) ≫ HomologicalComplex.homologyMap
        (((globalSections S).mapHomologicalComplex _).map ((godementResolution S).map a)) n := by
    rw [← HomologicalComplex.homologyMap_comp_assoc, totalSingleIso_naturality,
      HomologicalComplex.homologyMap_comp_assoc, Category.assoc]
    congr 1
    exact godementSectionsHomologyIso_naturality S a n
  exact key

/-- The identification `H^n(S, -) ≅ R^nΓ(S, -)` of the hypercohomology of one-term complexes with
the right derived functors of global sections: on `F` it is
`MMP.Analytic.sheafCohomologyGodementIso` followed by `MMP.Analytic.godementHomologyIso`. -/
noncomputable def sheafCohomologyIso (n : ℕ) :
    sheafCohomology S n ≅ (globalSections S).rightDerived n :=
  NatIso.ofComponents (fun F => sheafCohomologyGodementIso S F n ≪≫ godementHomologyIso S F n)
    (fun a => by
      simp only [Iso.trans_hom, Category.assoc]
      rw [← godementHomologyIso_naturality, sheafCohomologyGodementIso_naturality_assoc])

@[simp]
lemma sheafCohomologyIso_hom_app (n : ℕ) (F : TopCat.Sheaf AddCommGrpCat.{u} S) :
    (sheafCohomologyIso S n).hom.app F =
      (sheafCohomologyGodementIso S F n).hom ≫ (godementHomologyIso S F n).hom :=
  rfl

end SheafCohomologyIso

section SheafCohomologyPullback

variable {T T' : TopCat.{u}} (f : T' ⟶ T)

/-- In degree zero, the pullback of Godement resolutions over the augmentation is the adjunct of
the Godement unit of `f⁻¹ F`. -/
@[reassoc]
private lemma godementAugmentation_f_zero_comp_godementResolutionPullback_f_zero
    (F : TopCat.Sheaf AddCommGrpCat.{u} T) :
    (godementAugmentation T F).f 0 ≫ (godementResolutionPullback f F).f 0 =
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app F ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map ((godementUnit T').app _) := by
  rw [godementAugmentation, CokernelCoresolution.augmentation_f_zero]
  refine (Category.assoc _ _ _).trans ((Category.id_comp _).trans ?_)
  exact CokernelCoresolution.app_comp_homX_zero (godementPullbackLift f)
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app F)

private lemma isZero_godementSectionsDoubleComplex_pullback_single
    (F : TopCat.Sheaf AddCommGrpCat.{u} T) (q : ℤ) (hq : q ≠ 0) :
    IsZero ((godementSectionsDoubleComplex T' ((complexPullback f).obj
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F))).X q) :=
  (godementSections T').map_isZero ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).map_isZero
    (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq))

/-- The pullback on hypercohomology of `F[0]`, on the total complexes. -/
private lemma totalSingleIso_pullback (F : TopCat.Sheaf AddCommGrpCat.{u} T)
    (F' : TopCat.Sheaf AddCommGrpCat.{u} T')
    (θ : (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj F ⟶ F') :
    HomologicalComplex₂.total.map (godementSectionsDoubleComplexPullback f
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)) (ComplexShape.up ℤ) ≫
      HomologicalComplex₂.total.map (((godementSections T').mapHomologicalComplex _).map
        ((HomologicalComplex.singleMapHomologicalComplex
          (TopCat.Sheaf.pullback AddCommGrpCat.{u} f) (ComplexShape.up ℤ) 0).hom.app F))
        (ComplexShape.up ℤ) ≫
      HomologicalComplex₂.total.map (((godementSections T').mapHomologicalComplex _).map
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map θ)) (ComplexShape.up ℤ) ≫
      (totalSingleIso T' F').hom =
    (totalSingleIso T F).hom ≫ godementSectionsPullback f F ≫ (godementSections T').map θ := by
  have hiso := isIso_rowZeroToTotal _ (isZero_godementSectionsDoubleComplex_single T F)
  rw [← cancel_epi (rowZeroToTotal _ (isZero_godementSectionsDoubleComplex_single T F))]
  simp only [totalSingleIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, Functor.mapIso_hom,
    Category.assoc, IsIso.hom_inv_id_assoc]
  rw [rowZeroToTotal_naturality_assoc _
      (isZero_godementSectionsDoubleComplex_pullback_single f F),
    rowZeroToTotal_naturality_assoc _ (isZero_godementSectionsDoubleComplex_single T' _),
    rowZeroToTotal_naturality_assoc _ (isZero_godementSectionsDoubleComplex_single T' _)]
  simp only [IsIso.hom_inv_id_assoc]
  rw [godementSections_map_comp_godementSectionsPullback_assoc]
  change godementSectionsPullback f _ ≫ _ = godementSectionsPullback f _ ≫ _
  congr 1
  dsimp
  simp only [← Functor.map_comp]
  congr 1
  simp [HomologicalComplex.single_map_f_self]

@[reassoc]
private lemma godementSectionsHomologyIso_pullback (F : TopCat.Sheaf AddCommGrpCat.{u} T) (n : ℕ) :
    HomologicalComplex.homologyMap (godementSectionsPullback f F) n ≫
        (godementSectionsHomologyIso T' ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj F) n).hom =
      (godementSectionsHomologyIso T F n).hom ≫ HomologicalComplex.homologyMap
        (((globalSections T).mapHomologicalComplex _).map (godementResolutionPullback f F)) n :=
  HomologicalComplex.extendHomologyIso_hom_naturality _ _ _

/-- The pullback on `H^n(-, F)` read on the Godement resolutions: for `f : T' ⟶ T` and
`θ : f⁻¹ F ⟶ F'`, under `MMP.Analytic.sheafCohomologyGodementIso`, the pullback followed by
`H^n(T', θ)` is the map induced by the pullback of Godement resolutions followed by the map
induced by `θ`. -/
@[reassoc]
lemma sheafCohomologyGodementIso_pullback (F : TopCat.Sheaf AddCommGrpCat.{u} T)
    (F' : TopCat.Sheaf AddCommGrpCat.{u} T')
    (θ : (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj F ⟶ F') (n : ℕ) :
    sheafCohomologyPullback f F n ≫ (sheafCohomology T' n).map θ ≫
        (sheafCohomologyGodementIso T' F' n).hom =
      (sheafCohomologyGodementIso T F n).hom ≫ HomologicalComplex.homologyMap
        (((globalSections T).mapHomologicalComplex _).map (godementResolutionPullback f F)) n ≫
        HomologicalComplex.homologyMap
          (((globalSections T').mapHomologicalComplex _).map
            ((godementResolution T').map θ)) n := by
  have key : HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
        (godementSectionsDoubleComplexPullback f
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)) (ComplexShape.up ℤ)) n ≫
      HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
        (((godementSections T').mapHomologicalComplex _).map
        ((HomologicalComplex.singleMapHomologicalComplex
          (TopCat.Sheaf.pullback AddCommGrpCat.{u} f) (ComplexShape.up ℤ) 0).hom.app F))
        (ComplexShape.up ℤ)) n ≫
      HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
        (((godementSections T').mapHomologicalComplex _).map
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map θ)) (ComplexShape.up ℤ)) n ≫
      HomologicalComplex.homologyMap (totalSingleIso T' F').hom n ≫
      (godementSectionsHomologyIso T' F' n).hom =
      (HomologicalComplex.homologyMap (totalSingleIso T F).hom n ≫
        (godementSectionsHomologyIso T F n).hom) ≫ HomologicalComplex.homologyMap
        (((globalSections T).mapHomologicalComplex _).map (godementResolutionPullback f F)) n ≫
        HomologicalComplex.homologyMap
          (((globalSections T').mapHomologicalComplex _).map
            ((godementResolution T').map θ)) n := by
    simp only [← HomologicalComplex.homologyMap_comp_assoc]
    rw [totalSingleIso_pullback]
    simp only [HomologicalComplex.homologyMap_comp, Category.assoc]
    rw [godementSectionsHomologyIso_naturality, godementSectionsHomologyIso_pullback_assoc]
    exact congrArg (_ ≫ ·) (Category.assoc _ _ _)
  exact key

/-- The pullback on `H^n(-, F)` read on injective resolutions: for `f : T' ⟶ T`,
`θ : f⁻¹ F ⟶ F'`, injective resolutions `J` of `F` and `J'` of `F'`, and a map of complexes
`g : J ⟶ f_* J'` lifting the adjunct `F ⟶ f_* F'` of `θ`, under
`MMP.Analytic.sheafCohomologyIso` the pullback followed by `H^n(T', θ)` is the map
`R^nΓ(T, F) ⟶ R^nΓ(T', F')` induced by `g`. -/
theorem sheafCohomologyIso_pullback (F : TopCat.Sheaf AddCommGrpCat.{u} T)
    (F' : TopCat.Sheaf AddCommGrpCat.{u} T')
    (θ : (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj F ⟶ F')
    (J : InjectiveResolution F) (J' : InjectiveResolution F')
    (g : J.cocomplex ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex
      _).obj J'.cocomplex)
    (hg : J.ι.f 0 ≫ g.f 0 =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app F ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map θ) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map (J'.ι.f 0)) (n : ℕ) :
    sheafCohomologyPullback f F n ≫ (sheafCohomology T' n).map θ ≫
        (sheafCohomologyIso T' n).hom.app F' =
      (sheafCohomologyIso T n).hom.app F ≫
        (J.isoRightDerivedObj (globalSections T) n).hom ≫
        HomologicalComplex.homologyMap
          (((globalSections T).mapHomologicalComplex _).map g) n ≫
        (J'.isoRightDerivedObj (globalSections T') n).inv := by
  let g0 := desc' (godementAugmentation T F) (𝟙 F) J
  let g0' := desc' (godementAugmentation T' F') (𝟙 F') J'
  have : ∀ q, Injective ((((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex
      _).obj J'.cocomplex).X q) := fun _ =>
    have := pullback_preservesFiniteLimits f
    Injective.injective_of_adjoint
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f) _
  let β := godementResolutionPullback f F ≫
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).map
      ((godementResolution T').map θ ≫ g0')
  have hh : Homotopy (g0 ≫ g) β := homotopyOfCommZero (godementAugmentation T F) _ _ (by
    have h2 : (godementAugmentation T' F').f 0 ≫ g0'.f 0 = J'.ι.f 0 := by
      rw [← HomologicalComplex.comp_f, desc'_id_commutes]
    have h5 : (godementUnit T').app _ ≫ ((godementResolution T').map θ).f 0 =
        θ ≫ (godementUnit T').app F' := ((godementUnit T').naturality θ).symm
    rw [HomologicalComplex.comp_f, ← Category.assoc, ← HomologicalComplex.comp_f,
      desc'_id_commutes, hg]
    simp only [β, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
    rw [godementAugmentation_f_zero_comp_godementResolutionPullback_f_zero_assoc, Category.assoc]
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    congr 1
    refine ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map_comp _ _).symm.trans
      (Eq.trans ?_ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map_comp _ _))
    congr 1
    rw [← h2, godementAugmentation_f_zero]
    exact (h5 =≫ g0'.f 0).symm.trans (Category.assoc _ _ _))
  rw [sheafCohomologyIso_hom_app, sheafCohomologyIso_hom_app]
  rw [← godementHomologyIso_spec_id T F n J g0 (desc'_id_commutes _ J),
    ← godementHomologyIso_spec_id T' F' n J' g0' (desc'_id_commutes _ J')]
  have hH : HomologicalComplex.homologyMap
      (((globalSections T).mapHomologicalComplex _).map g0) n ≫ HomologicalComplex.homologyMap
        (((globalSections T).mapHomologicalComplex _).map g) n =
      HomologicalComplex.homologyMap
        (((globalSections T).mapHomologicalComplex _).map (godementResolutionPullback f F)) n ≫
      HomologicalComplex.homologyMap
        (((globalSections T').mapHomologicalComplex _).map ((godementResolution T').map θ)) n ≫
      HomologicalComplex.homologyMap (((globalSections T').mapHomologicalComplex _).map g0') n := by
    rw [← HomologicalComplex.homologyMap_comp, ← Functor.map_comp,
      ((globalSections T).mapHomotopy hh).homologyMap_eq n]
    simp only [β, Functor.map_comp, HomologicalComplex.homologyMap_comp]
    rfl
  simp only [Category.assoc]
  refine (sheafCohomologyGodementIso_pullback_assoc f F F' θ n _).trans (congrArg (_ ≫ ·) ?_)
  refine Eq.trans ?_ ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (Iso.inv_hom_id_assoc _ _))).symm
  exact (Category.assoc _ _ _).trans (((hH =≫ _).trans ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (Category.assoc _ _ _)))).symm.trans (Category.assoc _ _ _))

end SheafCohomologyPullback

/-- A degreewise short exact sequence of bounded complexes gives a short exact sequence of total
Godement complexes, with pullbacks commuting with the connecting maps. -/
private theorem hypercohomology_longExact (T : TopCat.{u}) :
    (∀ (S : ShortComplex (CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ)),
        (∀ i : ℤ, (S.map (HomologicalComplex.eval _ _ i)).ShortExact) →
        (∃ a b : ℤ, S.X₁.IsStrictlyGE a ∧ S.X₁.IsStrictlyLE b ∧ S.X₂.IsStrictlyGE a ∧
          S.X₂.IsStrictlyLE b ∧ S.X₃.IsStrictlyGE a ∧ S.X₃.IsStrictlyLE b) →
        ∃ hS : (ShortComplex.mk
            (HomologicalComplex₂.total.map
              (((godementSections T).mapHomologicalComplex _).map S.f) (ComplexShape.up ℤ))
            (HomologicalComplex₂.total.map
              (((godementSections T).mapHomologicalComplex _).map S.g) (ComplexShape.up ℤ))
            (by
              rw [← HomologicalComplex₂.total.map_comp, ← Functor.map_comp, S.zero,
                Functor.map_zero]
              ext n : 1
              exact HomologicalComplex₂.total.hom_ext _ fun _ _ _ => by simp)).ShortExact,
          ∀ {T' : TopCat.{u}} (f : T' ⟶ T),
            ∃ hS' : (ShortComplex.mk
                (HomologicalComplex₂.total.map (((godementSections T').mapHomologicalComplex _).map
                  ((complexPullback f).map S.f)) (ComplexShape.up ℤ))
                (HomologicalComplex₂.total.map (((godementSections T').mapHomologicalComplex _).map
                  ((complexPullback f).map S.g)) (ComplexShape.up ℤ))
                (by
                  rw [← HomologicalComplex₂.total.map_comp, ← Functor.map_comp,
                    ← Functor.map_comp, S.zero, Functor.map_zero, Functor.map_zero]
                  ext n : 1
                  exact HomologicalComplex₂.total.hom_ext _ fun _ _ _ => by simp)).ShortExact,
              ∀ n : ℤ, hS.δ n (n + 1) rfl ≫ hypercohomologyPullback f S.X₁ (n + 1) =
                hypercohomologyPullback f S.X₃ n ≫ hS'.δ n (n + 1) rfl) := by
  intro S hS _
  refine ⟨total_godementSections_shortExact T S hS, fun {T'} f => ?_⟩
  have hS' : ∀ i : ℤ,
      ((S.map (complexPullback f)).map (HomologicalComplex.eval _ _ i)).ShortExact :=
    have := pullback_preservesFiniteLimits f
    fun i => (hS i).map_of_exact (TopCat.Sheaf.pullback AddCommGrpCat.{u} f)
  refine ⟨total_godementSections_shortExact T' (S.map (complexPullback f)) hS', fun n => ?_⟩
  have hcomm : ∀ {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ} (φ : K ⟶ L),
      HomologicalComplex₂.total.map (((godementSections T).mapHomologicalComplex _).map φ)
          (ComplexShape.up ℤ) ≫
        HomologicalComplex₂.total.map (godementSectionsDoubleComplexPullback f L)
          (ComplexShape.up ℤ) =
      HomologicalComplex₂.total.map (godementSectionsDoubleComplexPullback f K)
          (ComplexShape.up ℤ) ≫
        HomologicalComplex₂.total.map
          (((godementSections T').mapHomologicalComplex _).map ((complexPullback f).map φ))
          (ComplexShape.up ℤ) := by
    intro K L φ
    rw [← HomologicalComplex₂.total.map_comp, ← HomologicalComplex₂.total.map_comp]
    congr 1
    ext q : 1
    exact godementSections_map_comp_godementSectionsPullback f (φ.f q)
  exact HomologicalComplex.HomologySequence.δ_naturality
    { τ₁ := HomologicalComplex₂.total.map (godementSectionsDoubleComplexPullback f S.X₁)
        (ComplexShape.up ℤ)
      τ₂ := HomologicalComplex₂.total.map (godementSectionsDoubleComplexPullback f S.X₂)
        (ComplexShape.up ℤ)
      τ₃ := HomologicalComplex₂.total.map (godementSectionsDoubleComplexPullback f S.X₃)
        (ComplexShape.up ℤ)
      comm₁₂ := (hcomm S.f).symm
      comm₂₃ := (hcomm S.g).symm }
    (total_godementSections_shortExact T S hS)
    (total_godementSections_shortExact T' (S.map (complexPullback f)) hS') n (n + 1) rfl

/-- **The sheaf cohomology toolkit.** For a topological space `T`, with `H^n(T, -)` the right
derived functors of `Γ(T, -)` on abelian sheaves:
(1) enough injectives for abelian sheaves and for `𝒪_X`-modules, injectives are flasque,
flasqueness restricts to opens and flasque sheaves are acyclic on every open;
(2) comparison of a resolution with an injective resolution, unique up to homotopy, and the
computation of `H^n(T, F)` by an acyclic resolution, with the Godement resolution flasque;
(3) hypercohomology of one-term complexes is `H^n(T, -)`, compatibly with pullbacks; the
hypercohomology long exact sequence of a degreewise short exact sequence of bounded complexes,
with pullbacks natural and commuting with connecting maps;
(4) uniqueness of morphisms of δ-functors out of an effaceable δ-functor. -/
@[mmp "lem_mmp_gaga_sheaf_cohomology_toolkit"]
public theorem sheafCohomology_toolkit (T : TopCat.{u}) :
    haveI : ∀ S : TopCat.{u}, (globalSections S).Additive := globalSections_additive
    -- (1) enough injectives, injectives are flasque, flasque sheaves are acyclic
    (EnoughInjectives (TopCat.Sheaf AddCommGrpCat.{u} T) ∧
      (∀ X : Scheme.{u}, EnoughInjectives X.Modules) ∧
      (∀ I : TopCat.Sheaf AddCommGrpCat.{u} T, Injective I → TopCat.Sheaf.IsFlasque I) ∧
      (∀ (X : Scheme.{u}) (M : X.Modules), Injective M →
        TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) ∧
      (∀ F : TopCat.Sheaf AddCommGrpCat.{u} T, TopCat.Sheaf.IsFlasque F → ∀ U : Opens T,
        TopCat.Sheaf.IsFlasque ((TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion').obj F)) ∧
      (∀ F : TopCat.Sheaf AddCommGrpCat.{u} T, TopCat.Sheaf.IsFlasque F → ∀ (U : Opens T) (n : ℕ),
        0 < n → IsZero
          (((globalSections ((Opens.toTopCat T).obj U)).rightDerived n).obj
            ((TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion').obj F)))) ∧
    -- (2) comparison with injective resolutions; acyclic resolutions compute cohomology
    ((∀ {F F' : TopCat.Sheaf AddCommGrpCat.{u} T} (φ : F ⟶ F')
        (A : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℕ)
        (ι : (CochainComplex.single₀ _).obj F ⟶ A), QuasiIso ι →
        ∀ J : InjectiveResolution F',
          ∃ g : A ⟶ J.cocomplex, ι ≫ g = (CochainComplex.single₀ _).map φ ≫ J.ι) ∧
      (∀ {F F' : TopCat.Sheaf AddCommGrpCat.{u} T} (φ : F ⟶ F')
        (A : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℕ)
        (ι : (CochainComplex.single₀ _).obj F ⟶ A), QuasiIso ι →
        ∀ (J : InjectiveResolution F') (g g' : A ⟶ J.cocomplex),
          ι ≫ g = (CochainComplex.single₀ _).map φ ≫ J.ι →
          ι ≫ g' = (CochainComplex.single₀ _).map φ ≫ J.ι → Nonempty (Homotopy g g')) ∧
      (∀ {F : TopCat.Sheaf AddCommGrpCat.{u} T}
        (A : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℕ)
        (ι : (CochainComplex.single₀ _).obj F ⟶ A), QuasiIso ι →
        (∀ (q n : ℕ), 0 < n → IsZero
          (((globalSections T).rightDerived n).obj (A.X q))) →
        ∀ n : ℕ, ∃ e : (HomologicalComplex.homologyFunctor _ _ n).obj
            (((globalSections T).mapHomologicalComplex _).obj A) ≅
            ((globalSections T).rightDerived n).obj F,
          ∀ {F' : TopCat.Sheaf AddCommGrpCat.{u} T} (φ : F ⟶ F') (J : InjectiveResolution F')
            (g : A ⟶ J.cocomplex), ι ≫ g = (CochainComplex.single₀ _).map φ ≫ J.ι →
            HomologicalComplex.homologyMap
                (((globalSections T).mapHomologicalComplex _).map g) n ≫
              (J.isoRightDerivedObj (globalSections T) n).inv =
            e.hom ≫ ((globalSections T).rightDerived n).map φ) ∧
      (∀ F : TopCat.Sheaf AddCommGrpCat.{u} T, QuasiIso (godementAugmentation T F) ∧
        ∀ q : ℕ, TopCat.Sheaf.IsFlasque (((godementResolution T).obj F).X q))) ∧
    -- (3) hypercohomology: one-term complexes, long exact sequence, pullback
    ((∃ E : ∀ (S : TopCat.{u}) (n : ℕ), sheafCohomology S n ≅
          (globalSections S).rightDerived n,
        ∀ {T' : TopCat.{u}} (f : T' ⟶ T) (F : TopCat.Sheaf AddCommGrpCat.{u} T)
          (F' : TopCat.Sheaf AddCommGrpCat.{u} T')
          (θ : (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj F ⟶ F')
          (J : InjectiveResolution F) (J' : InjectiveResolution F')
          (g : J.cocomplex ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex
            _).obj J'.cocomplex),
          J.ι.f 0 ≫ g.f 0 =
            ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app F ≫
              (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map θ) ≫
              (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map (J'.ι.f 0) →
          ∀ n : ℕ, sheafCohomologyPullback f F n ≫ (sheafCohomology T' n).map θ ≫
              (E T' n).hom.app F' =
            (E T n).hom.app F ≫
              (J.isoRightDerivedObj (globalSections T) n).hom ≫
              HomologicalComplex.homologyMap
                (((globalSections T).mapHomologicalComplex _).map g) n ≫
              (J'.isoRightDerivedObj (globalSections T') n).inv) ∧
      (∀ (S : ShortComplex (CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ)),
        (∀ i : ℤ, (S.map (HomologicalComplex.eval _ _ i)).ShortExact) →
        (∃ a b : ℤ, S.X₁.IsStrictlyGE a ∧ S.X₁.IsStrictlyLE b ∧ S.X₂.IsStrictlyGE a ∧
          S.X₂.IsStrictlyLE b ∧ S.X₃.IsStrictlyGE a ∧ S.X₃.IsStrictlyLE b) →
        ∃ hS : (ShortComplex.mk
            (HomologicalComplex₂.total.map
              (((godementSections T).mapHomologicalComplex _).map S.f) (ComplexShape.up ℤ))
            (HomologicalComplex₂.total.map
              (((godementSections T).mapHomologicalComplex _).map S.g) (ComplexShape.up ℤ))
            (by
              rw [← HomologicalComplex₂.total.map_comp, ← Functor.map_comp, S.zero,
                Functor.map_zero]
              ext n : 1
              exact HomologicalComplex₂.total.hom_ext _ fun _ _ _ => by simp)).ShortExact,
          ∀ {T' : TopCat.{u}} (f : T' ⟶ T),
            ∃ hS' : (ShortComplex.mk
                (HomologicalComplex₂.total.map (((godementSections T').mapHomologicalComplex _).map
                  ((complexPullback f).map S.f)) (ComplexShape.up ℤ))
                (HomologicalComplex₂.total.map (((godementSections T').mapHomologicalComplex _).map
                  ((complexPullback f).map S.g)) (ComplexShape.up ℤ))
                (by
                  rw [← HomologicalComplex₂.total.map_comp, ← Functor.map_comp,
                    ← Functor.map_comp, S.zero, Functor.map_zero, Functor.map_zero]
                  ext n : 1
                  exact HomologicalComplex₂.total.hom_ext _ fun _ _ _ => by simp)).ShortExact,
              ∀ n : ℤ, hS.δ n (n + 1) rfl ≫ hypercohomologyPullback f S.X₁ (n + 1) =
                hypercohomologyPullback f S.X₃ n ≫ hS'.δ n (n + 1) rfl) ∧
      (∀ {T' : TopCat.{u}} (f : T' ⟶ T)
        {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ} (φ : K ⟶ L) (n : ℤ),
        (hypercohomology T n).map φ ≫ hypercohomologyPullback f L n =
          hypercohomologyPullback f K n ≫ (hypercohomology T' n).map ((complexPullback f).map φ))) ∧
    -- (4) Grothendieck: morphisms out of an effaceable δ-functor are determined in degree zero
    (∀ {C : Type u₁} [Category.{v₁} C] [Abelian C] [EnoughInjectives C]
      {D : Type u₂} [Category.{v₂} D] [Abelian D]
      (T S : ℕ → C ⥤ D) [∀ q, (T q).Additive] [∀ q, (S q).Additive]
      (δT : ∀ (q : ℕ) (X : ShortComplex C), X.ShortExact → ((T q).obj X.X₃ ⟶ (T (q + 1)).obj X.X₁))
      (δS : ∀ (q : ℕ) (X : ShortComplex C), X.ShortExact → ((S q).obj X.X₃ ⟶ (S (q + 1)).obj X.X₁))
      (hTex : ∀ q X (hX : ShortComplex.ShortExact X), (X.map (T q)).Exact)
      (hTg : ∀ q X (hX : ShortComplex.ShortExact X), (T q).map X.g ≫ δT q X hX = 0)
      (hTgex : ∀ q X (hX : ShortComplex.ShortExact X), (ShortComplex.mk _ _ (hTg q X hX)).Exact)
      (hTf : ∀ q X (hX : ShortComplex.ShortExact X), δT q X hX ≫ (T (q + 1)).map X.f = 0)
      (hTfex : ∀ q X (hX : ShortComplex.ShortExact X), (ShortComplex.mk _ _ (hTf q X hX)).Exact)
      (hTnat : ∀ q (X Y : ShortComplex C) (hX : X.ShortExact) (hY : Y.ShortExact) (ψ : X ⟶ Y),
        δT q X hX ≫ (T (q + 1)).map ψ.τ₁ = (T q).map ψ.τ₃ ≫ δT q Y hY)
      (hSex : ∀ q X (hX : ShortComplex.ShortExact X), (X.map (S q)).Exact)
      (hSg : ∀ q X (hX : ShortComplex.ShortExact X), (S q).map X.g ≫ δS q X hX = 0)
      (hSgex : ∀ q X (hX : ShortComplex.ShortExact X), (ShortComplex.mk _ _ (hSg q X hX)).Exact)
      (hSf : ∀ q X (hX : ShortComplex.ShortExact X), δS q X hX ≫ (S (q + 1)).map X.f = 0)
      (hSfex : ∀ q X (hX : ShortComplex.ShortExact X), (ShortComplex.mk _ _ (hSf q X hX)).Exact)
      (hSnat : ∀ q (X Y : ShortComplex C) (hX : X.ShortExact) (hY : Y.ShortExact) (ψ : X ⟶ Y),
        δS q X hX ≫ (S (q + 1)).map ψ.τ₁ = (S q).map ψ.τ₃ ≫ δS q Y hY)
      (heff : ∀ (I : C), Injective I → ∀ q : ℕ, 0 < q → IsZero ((T q).obj I))
      (η η' : ∀ q, T q ⟶ S q)
      (hη : ∀ q X (hX : ShortComplex.ShortExact X),
        δT q X hX ≫ (η (q + 1)).app X.X₁ = (η q).app X.X₃ ≫ δS q X hX)
      (hη' : ∀ q X (hX : ShortComplex.ShortExact X),
        δT q X hX ≫ (η' (q + 1)).app X.X₁ = (η' q).app X.X₃ ≫ δS q X hX),
      η 0 = η' 0 → ∀ q, η q = η' q) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · infer_instance
  · intro X; infer_instance
  · intro I hI
    exact Stacks.Cohomology.CechOne.isFlasque_of_injective I
  · intro X M hM
    exact @Stacks.RelativeLeray.isFlasque_of_injective X.toRingedSpace M hM
  · intro F hF U
    exact isFlasque_pullback_inclusion F U
  · intro F hF U n hn
    exact isZero_rightDerived_globalSections_of_isFlasque _ _
      (isFlasque_pullback_inclusion F U) n hn
  · intro F F' φ A ι hι J
    exact ⟨desc' ι φ J, desc'_commutes ι φ J⟩
  · intro F F' φ A ι hι J g g' hg hg'
    exact ⟨homotopyOfComm ι g g' hg hg'⟩
  · exact sheafCohomology_eq_of_acyclic_resolution T
  · exact godementResolution_flasque_resolution T
  · exact ⟨fun S n => sheafCohomologyIso S n,
      fun f F F' θ J J' g hg n => sheafCohomologyIso_pullback f F F' θ J J' g hg n⟩
  · exact hypercohomology_longExact T
  · intro T' f K L φ n
    exact hypercohomology_map_comp_hypercohomologyPullback f φ n
  · intro C _ _ _ D _ _ T S _ _ δT δS hTex hTg hTgex hTf hTfex hTnat hSex hSg hSgex hSf hSfex
      hSnat heff η η' hη hη' h0 q
    induction q with
    | zero => exact h0
    | succ q ih =>
      ext A
      let X : ShortComplex C :=
        ShortComplex.mk (Injective.ι A) (cokernel.π _) (cokernel.condition _)
      have hX : X.ShortExact := { exact := ShortComplex.exact_cokernel _ }
      have hz : IsZero ((T (q + 1)).obj (Injective.under A)) :=
        heff _ inferInstance _ (Nat.succ_pos q)
      have : Epi (δT q X hX) :=
        (hTfex q X hX).epi_f (hz.eq_of_tgt _ _)
      rw [← cancel_epi (δT q X hX), hη, hη', ih]

end Toolkit

end MMP.Analytic
