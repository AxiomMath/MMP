module

public import MMP.AlgebraicTopology.CapProduct.RestrictionCycles
public import MMP.AlgebraicTopology.CapProduct.SupportLemmas
public import MMP.AlgebraicTopology.BorelMoore.RestrictionPushforward

/-!
# The neighbourhood cap product and restriction to an open subset

Let `X` be closed in a Hausdorff space `Y`, `N` a closed neighbourhood of `X`, `U ⊆ Y` open with
inclusion `j`. Then `N ∩ U` is a closed neighbourhood of `j⁻¹ X` in `U`, and the restriction of
`c ∩_N a ∈ H_{k-j} N` to the open subset `N ∩ U` of `N` is `j^* c ∩_{N ∩ U} a|_U`.

On chains, `c ∩_N a` is the class of `(φ ∩ ρ z)|_N` for the subdivision `ρ z` of `z` towards
`{Y - X, int N}`; its restriction to `N ∩ U` is `((φ ∩ ρ z)|_U)|_{N ∩ U}`; by
`MMP.BorelMooreCap.exists_d_eq_restrictChainMap_capChain_sub` this differs from
`(φ|_U ∩ (ρ z)|_U)|_{N ∩ U}` by a boundary supported in `int N ∩ U`, and `(ρ z)|_U` is a cycle
homologous to `z|_U` all of whose simplices lie in `U - X` or in `int N ∩ U`, which computes the
neighbourhood cap product of `U`.

## Main definitions

* `MMP.borelMooreHomology.opensInter`: `N ∩ U` as an open subset of `N`.
* `MMP.borelMooreHomology.opensInterHomeo`: its homeomorphism with `N ∩ U` as a
  subset of `U`, where `MMP.borelMooreHomology.setInter` is `N ∩ U` as a subset of `U`.
* `MMP.borelMooreHomology.opensInterMap`: `opensInterHomeo` as a morphism of `TopCat`.

## Main results

* `MMP.borelMooreHomology.pushforward_opensInterMap_restrict_capProductNbhd`:
  `(c ∩_N a)|_{N ∩ U} = j^* c ∩_{N ∩ U} a|_U`.
-/

@[expose] public noncomputable section

open CategoryTheory Set Topology Opposite Simplicial

universe u

namespace MMP

namespace borelMooreHomology

open SingularChain LocallyFiniteChain BorelMooreCross BorelMooreCap SingularCochain SingularCross

section opensInter

variable {Y : TopCat.{u}} (U : TopologicalSpace.Opens Y) (N : Set Y)

/-- `N ∩ U`, as an open subset of `N`. -/
abbrev opensInter : TopologicalSpace.Opens (TopCat.of N) :=
  TopologicalSpace.Opens.comap (subsetInclusion N).hom U

/-- `N ∩ U`, as a subset of `U`. -/
abbrev setInter : Set (TopCat.of U) := Subtype.val ⁻¹' N

/-- The two readings of `N ∩ U` are homeomorphic. -/
def opensInterHomeo : opensInter U N ≃ₜ setInter U N where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun y := ⟨⟨y.1.1, y.2⟩, y.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _)
  continuous_invFun :=
    (((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _)

/-- The homeomorphism `opensInterHomeo`, as a morphism of `TopCat`. -/
def opensInterMap : TopCat.of (opensInter U N) ⟶ TopCat.of (setInter U N) :=
  TopCat.ofHom (opensInterHomeo U N : C(opensInter U N, setInter U N))

/-- The map `opensInterMap U N` is proper. -/
lemma isProperMap_opensInterMap : IsProperMap (opensInterMap U N) :=
  (opensInterHomeo U N).isProperMap

variable {U N}

/-- If `N` is closed in `Y`, then `N ∩ U` is closed in `U`. -/
lemma isClosed_setInter (hN : IsClosed N) : IsClosed (setInter U N) :=
  hN.preimage continuous_subtype_val

end opensInter

section chains

variable (R : Type u) [CommRing R] {Y : TopCat.{u}} [T2Space Y] {U : TopologicalSpace.Opens Y}

omit [T2Space Y] in
/-- If the restriction coefficient of `σ` at a simplex `τ` of `U` is nonzero, then the image of `τ`
lies in the preimage of the image of `σ`. -/
lemma singularSimplexImage_subset_of_restrictKernel_ne_zero {n : ℕ} {σ : Simp Y n}
    {τ : Simp (TopCat.of U) n} (h : restrictKernel U n σ τ ≠ 0) :
    singularSimplexImage (TopCat.of U) τ ⊆ Subtype.val ⁻¹' singularSimplexImage Y σ := by
  intro x hx
  have : x.1 ∈ range (inclSimplex U τ) := by
    rw [range_inclSimplex]
    exact ⟨x, hx, rfl⟩
  exact (range_simplexEquiv σ).subset (range_subset_of_restrCoeff_ne_zero h this).1

/-- The restriction to `U` of a chain supported in `B` is supported in `B ∩ U`. -/
lemma isSupportedIn_restrictChainMap {B : Set Y} {n : ℕ} {c : (BM R Y).X n}
    (hc : IsSupportedIn R (ModuleCat.of R R) B c) :
    IsSupportedIn R (ModuleCat.of R R) (Subtype.val ⁻¹' B : Set (TopCat.of U))
      (((restrictChainMap R (ModuleCat.of R R) U).f n).hom c) := by
  intro τ hτ
  obtain ⟨σ, hσ⟩ : ∃ σ, restrictKernel U n σ τ • c.1 σ ≠ 0 := by
    by_contra h
    push Not at h
    exact hτ (finsum_eq_zero_of_forall_eq_zero h)
  exact fun x hx ↦ hc σ (smul_ne_zero_right hσ)
    (singularSimplexImage_subset_of_restrictKernel_ne_zero (smul_ne_zero_left hσ) hx)

/-- For a chain `c` supported in `N`, restricting `c|_N` to `N ∩ U` is restricting `c|_U` to
`N ∩ U`. -/
lemma chainMap_opensInterMap_restrictChainMap {N : Set Y} (hN : IsClosed N) {n : ℕ}
    {c : (BM R Y).X n} (hc : IsSupportedIn R (ModuleCat.of R R) N c) :
    ((chainMap R (ModuleCat.of R R) (opensInterMap U N) (isProperMap_opensInterMap U N)).f
        n).hom (((restrictChainMap R (ModuleCat.of R R) (opensInter U N)).f n).hom
          ((subsetRestrictMap R (ModuleCat.of R R) N n).hom c)) =
      (subsetRestrictMap R (ModuleCat.of R R) (setInter U N) n).hom
        (((restrictChainMap R (ModuleCat.of R R) U).f n).hom c) := by
  apply chainMap_subsetInclusion_injective R _ (isClosed_setInter hN) n
  rw [chainMap_subsetRestrictMap R _ (isClosed_setInter hN) (isSupportedIn_restrictChainMap R hc)]
  have h1 := chainMap_comp R (ModuleCat.of R R) (opensInterMap U N) (subsetInclusion (setInter U N))
    (isProperMap_opensInterMap U N) (isProperMap_subsetInclusion (isClosed_setInter hN))
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← HomologicalComplex.comp_f, ← h1]
  have h2 := congrArg (fun g ↦ (g.f n).hom ((subsetRestrictMap R (ModuleCat.of R R) N n).hom c))
    (chainMap_comp_restrictChainMap R (ModuleCat.of R R) (subsetInclusion N)
      (isProperMap_subsetInclusion hN) U)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  rw [chainMap_subsetRestrictMap R _ hN hc] at h2
  exact h2.symm

end chains

section homQ

variable {R : Type u} [CommRing R] {Y : TopCat.{u}} [T2Space Y] {U : TopologicalSpace.Opens Y}

variable {A N : Set Y} (hA : IsOpen A) (hN : IsClosed N) (hAN : A ∪ interior N = univ)
  (hAU : IsOpen (Subtype.val ⁻¹' A : Set (TopCat.of U)))
  (hANU : (Subtype.val ⁻¹' A : Set (TopCat.of U)) ∪ interior (setInter U N) = univ)

include hA hAN in
omit [T2Space Y] in
/-- The simplices of the subdivision towards `{A, int N}` lie in `A` or in `int N`. -/
lemma nbhdSubdiv_small {n : ℕ} (z : (BM R Y).X n) (σ : Simp Y n)
    (hσ : coeff R ((nbhdSubdiv R A N n).hom z) σ ≠ 0) :
    singularSimplexImage Y σ ⊆ A ∨ singularSimplexImage Y σ ⊆ interior N := by
  obtain ⟨V, hV, hσV⟩ := smallChainMapLF_small R (ModuleCat.of R R)
    (𝒰 := {A, interior N}) (by rintro V (rfl | rfl) <;> simp [hA])
    (by rwa [sUnion_insert, sUnion_singleton]) n z hσ
  rcases hV with rfl | rfl
  · exact Or.inl hσV
  · exact Or.inr hσV

include hA hAN in
/-- The restriction to `U` of the subdivision towards `{A, int N}` is small for
`{U ∩ A, int (N ∩ U)}`. -/
lemma restrictChainMap_nbhdSubdiv_small {n : ℕ} (z : (BM R Y).X n)
    (τ : Simp (TopCat.of U) n)
    (hτ : coeff R (((restrictChainMap R (ModuleCat.of R R) U).f n).hom
      ((nbhdSubdiv R A N n).hom z)) τ ≠ 0) :
    ∃ V ∈ ({Subtype.val ⁻¹' A, interior (setInter U N)} : Set (Set (TopCat.of U))),
      singularSimplexImage (TopCat.of U) τ ⊆ V := by
  obtain ⟨σ, hσ⟩ : ∃ σ, restrictKernel U n σ τ • coeff R ((nbhdSubdiv R A N n).hom z) σ ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hτ (finsum_eq_zero_of_forall_eq_zero h')
  have h1 := singularSimplexImage_subset_of_restrictKernel_ne_zero (smul_ne_zero_left hσ)
  rcases nbhdSubdiv_small hA hAN z σ (smul_ne_zero_right hσ) with h2 | h2
  · exact ⟨_, Or.inl rfl, h1.trans (preimage_mono h2)⟩
  · exact ⟨_, Or.inr rfl, (h1.trans (preimage_mono h2)).trans
      (preimage_interior_subset_interior_preimage continuous_subtype_val)⟩

/-- `z|_U - (ρ z)|_U` is a boundary. -/
lemma restrictChainMap_sub_restrictChainMap_nbhdSubdiv {n : ℕ} (z : Cyc (R := R) Y n) :
    ((restrictChainMap R (ModuleCat.of R R) U).f n).hom z.1 -
        ((restrictChainMap R (ModuleCat.of R R) U).f n).hom ((nbhdSubdiv R A N n).hom z.1) =
      ((BM R (TopCat.of U)).d (n + 1) n).hom
        (((restrictChainMap R (ModuleCat.of R R) U).f (n + 1)).hom
          ((smallHomotopyMap R (ModuleCat.of R R) {A, interior N} n).hom z.1)) := by
  have e := congrArg ((restrictChainMap R (ModuleCat.of R R) U).f n).hom
    (sub_smallChainMapLF_eq_d (R := R) {A, interior N} z.2)
  rw [map_sub] at e
  refine e.trans ?_
  have := congrArg (fun g ↦ g.hom ((smallHomotopyMap R (ModuleCat.of R R) {A, interior N} n).hom
    z.1)) ((restrictChainMap R (ModuleCat.of R R) U).comm (n + 1) n)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using this.symm

include hA hAN in
/-- The difference between the restriction to `U` of `φ ∩ ρ z` and `φ|_U ∩ (ρ z)|_U` is the
boundary of a chain supported in `N ∩ U`. -/
lemma exists_d_eq_restrictChainMap_capChain_nbhdSubdiv (p q n : ℕ) (h : p + q = n)
    (φ : relCocycles R A p) (z : Cyc (R := R) Y n) :
    ∃ u : (BM R (TopCat.of U)).X (q + 1),
      ((BM R (TopCat.of U)).d (q + 1) q).hom u =
        ((restrictChainMap R (ModuleCat.of R R) U).f q).hom
            (capChain R p q n h φ.1 ((nbhdSubdiv R A N n).hom z.1)) -
          capChain R p q n h (cochainPullback R (inclHom U) p φ.1)
            (((restrictChainMap R (ModuleCat.of R R) U).f n).hom
              ((nbhdSubdiv R A N n).hom z.1)) ∧
      IsSupportedIn R (ModuleCat.of R R) (setInter U N) u := by
  obtain ⟨u, hu, hus⟩ := exists_d_eq_restrictChainMap_capChain_sub (U := U) p q n h
    (A := A) (LinearMap.mem_ker.1 φ.2.2) φ.2.1 ⟨_, nbhdSubdiv_mem_cyc z.2⟩
  refine ⟨u, hu, fun ν hν ↦ ?_⟩
  obtain ⟨σ, hσ, hσA, hνσ⟩ := hus ν hν
  rcases nbhdSubdiv_small hA hAN z.1 σ hσ with h2 | h2
  · exact absurd h2 hσA
  · intro x hx
    have : x.1 ∈ range (inclSimplex U ν) := by
      rw [range_inclSimplex]
      exact ⟨x, hx, rfl⟩
    exact interior_subset (s := N) (h2 (hνσ this))

include hA hN hAN in
/-- **The neighbourhood cap product commutes with restriction, on cocycles modulo coboundaries.**
The restriction to `N ∩ U` of `x ∩_N [z]` is `j^* x ∩_{N ∩ U} [z|_U]`. -/
theorem homologyMap_restrict_capHomQNbhd (p q n : ℕ) (h : p + q = n) (x : relCohomology R A p)
    (b : borelMooreHomology R (ModuleCat.of R R) Y n) :
    (homologyMap R (restrictChainMap R (ModuleCat.of R R) (opensInter U N) ≫
        chainMap R (ModuleCat.of R R) (opensInterMap U N) (isProperMap_opensInterMap U N)) q).hom
      ((homologyEquiv R (TopCat.of N) q).symm (capHomQNbhd R hA hN hAN p q n h x
        (homologyEquiv R Y n b))) =
      (homologyEquiv R (TopCat.of (setInter U N)) q).symm
        (capHomQNbhd R hAU (isClosed_setInter hN) hANU p q n h
          (relCohomologyMap R (inclHom U) (fun _ h ↦ h) p x)
          (homologyEquiv R (TopCat.of U) n
            ((homologyMap R (restrictChainMap R (ModuleCat.of R R) U) n).hom b))) := by
  obtain ⟨y, rfl⟩ := (homologyEquiv R Y n).symm.surjective b
  rw [LinearEquiv.apply_symm_apply]
  induction x using Submodule.Quotient.induction_on with | H φ => ?_
  induction y using Submodule.Quotient.induction_on with | H z => ?_
  erw [homologyMap_homologyEquiv_symm_mk R (restrictChainMap R (ModuleCat.of R R) U),
    LinearEquiv.apply_symm_apply]
  erw [relCohomologyMap_mk, capHomQNbhd_mk, capHomQNbhd_mk, homologyMap_homologyEquiv_symm_mk]
  congr 1
  have hc := isSupportedIn_capChain_nbhdSubdiv (N := N) hA hAN p q n h φ.2.1 z.1
  have hwc := chainMap_mem_cyc R (restrictChainMap R (ModuleCat.of R R) U)
    ⟨_, nbhdSubdiv_mem_cyc (A := A) (N := N) z.2⟩
  have hwρ := smallChainMapLF_f_hom_of_small R _ _
    (restrictChainMap_nbhdSubdiv_small (U := U) hA hAN z.1)
  have hc' := capChain_nbhdSubdiv_restrict_mem_cyc hAU (isClosed_setInter hN) hANU p q n h
    (relCocyclesMap R (inclHom U) (fun _ h ↦ h) p φ) ⟨_, hwc⟩
  erw [hwρ] at hc'
  obtain ⟨u, hu, husupp⟩ :=
    exists_d_eq_restrictChainMap_capChain_nbhdSubdiv (U := U) hA hAN p q n h φ z
  have e1 := chainMap_opensInterMap_restrictChainMap R (U := U) hN hc
  refine Eq.trans ?_ (mk_restrict_capChain_of_small hAU (isClosed_setInter hN) hANU p q n h
    (relCocyclesMap R (inclHom U) (fun _ h ↦ h) p φ) ⟨_, chainMap_mem_cyc R _ z⟩ _
    (restrictChainMap_nbhdSubdiv_small (U := U) hA hAN z.1) _
    (restrictChainMap_sub_restrictChainMap_nbhdSubdiv z) hc')
  refine (Submodule.Quotient.eq _).2 (restrict_d_mem_bdry (isClosed_setInter hN) u
    husupp _ ?_)
  have key : (subsetRestrictMap R (ModuleCat.of R R) (setInter U N) q).hom
      (((restrictChainMap R (ModuleCat.of R R) U).f q).hom
        (capChain R p q n h φ.1 ((nbhdSubdiv R A N n).hom z.1))) -
      (subsetRestrictMap R (ModuleCat.of R R) (setInter U N) q).hom
        (capChain R p q n h (cochainPullback R (inclHom U) p φ.1)
          (((restrictChainMap R (ModuleCat.of R R) U).f n).hom
            ((nbhdSubdiv R A N n).hom z.1))) =
      (subsetRestrictMap R (ModuleCat.of R R) (setInter U N) q).hom
        (((BM R (TopCat.of U)).d (q + 1) q).hom u) := by
    rw [← map_sub, hu]
  refine Eq.trans ?_ key
  exact congrArg₂ (· - ·) e1 rfl

end homQ

section homology

variable (R : Type u) [CommRing R]

/-- The map induced on Borel–Moore homology by a composite of chain maps is the composite of the
induced maps. -/
lemma homologyMap_comp_homologyMap {X X' X'' : TopCat.{u}} (φ : BM R X ⟶ BM R X')
    (ψ : BM R X' ⟶ BM R X'') (i : ℤ) :
    homologyMap R φ i ≫ homologyMap R ψ i = homologyMap R (φ ≫ ψ) i := by
  have h₁ := HomologicalComplex.homologyMap_comp
    (HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat)
    (HomologicalComplex.extendMap ψ ComplexShape.embeddingDownNat) (-i)
  rw [← HomologicalComplex.extendMap_comp] at h₁
  exact h₁.symm

/-- **The neighbourhood cap product commutes with restriction** (Fulton §19.1; [BT] 2.2). For a
closed neighbourhood `N` of a closed subset `X` of a Hausdorff space `Y` and an open `U ⊆ Y` with
inclusion `j`, the restriction of `c ∩_N a` to the open subset `N ∩ U` of `N` is
`j^* c ∩_{N ∩ U} a|_U`, where `N ∩ U` is a closed neighbourhood of `j⁻¹ X` in `U`. -/
theorem pushforward_opensInterMap_restrict_capProductNbhd (Y : TopCat.{u}) [T2Space Y]
    (U : TopologicalSpace.Opens Y) {X N : Set Y} (hX : IsClosed X) (hN : IsClosed N)
    (hXN : X ⊆ interior N) (j k : ℤ) (c : cohomologyWithSupports R (ModuleCat.of R R) Y X j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y k) :
    (pushforward R (ModuleCat.of R R) (opensInterMap U N) (isProperMap_opensInterMap U N)
        (k - j)).hom ((restrict R (ModuleCat.of R R) (opensInter U N) (k - j)).hom
          (capProductNbhd R Y hX hN hXN j k c a)) =
      capProductNbhd R (TopCat.of U) (hX.preimage (inclHom U).hom.continuous)
        (isClosed_setInter hN) (preimage_subset_interior_preimage (inclHom U) hXN) j k
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (inclHom U) X j).hom c)
        ((restrict R (ModuleCat.of R R) U k).hom a) := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, pushforward_eq_homologyMap,
    show restrict R (ModuleCat.of R R) (opensInter U N) (k - j) =
      homologyMap R (restrictChainMap R (ModuleCat.of R R) (opensInter U N)) (k - j) from rfl,
    homologyMap_comp_homologyMap,
    show restrict R (ModuleCat.of R R) U k =
      homologyMap R (restrictChainMap R (ModuleCat.of R R) U) k from rfl]
  unfold capProductNbhd
  split_ifs with h
  · simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
      LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply, congrDegree_symm]
    rw [homologyMap_congrDegree, ← homologyMap_congrDegree R
      (restrictChainMap R (ModuleCat.of R R) U)]
    rw [cohomologyWithSupports.congrIndex_pullback, cohomologyWithSupports.pullback]
    rw [relativeSingularCohomologyEquiv_map (g := inclHom U) (A := Xᶜ)
      (A' := ((inclHom U).hom ⁻¹' X)ᶜ) (fun _ hx ↦ hx)]
    exact congrArg (congrDegree R (TopCat.of (setInter U N)) _)
      (homologyMap_restrict_capHomQNbhd (U := U) hX.isOpen_compl hN
        (compl_union_interior_eq_univ hXN)
        (hX.preimage (inclHom U).hom.continuous).isOpen_compl
        (compl_union_interior_eq_univ (preimage_subset_interior_preimage (inclHom U) hXN))
        j.toNat (k.toNat - j.toNat) k.toNat (by omega) _ _)
  · simp

end homology

/-- In an open subspace `U'` that is a normal space, a set `K` closed in `U'` and contained in an
open `O` has a neighbourhood `L ⊆ O ∩ U'` that is closed in `U'`. -/
lemma exists_isClosed_preimage_subset_nhds {Y : Type*} [TopologicalSpace Y] {U' : Set Y}
    (hU' : IsOpen U') [NormalSpace U'] {K O : Set Y} (hK : IsClosed (Subtype.val ⁻¹' K : Set U'))
    (hKU' : K ⊆ U') (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ L : Set Y, IsClosed (Subtype.val ⁻¹' L : Set U') ∧ L ⊆ U' ∧ L ⊆ O ∧ K ⊆ interior L := by
  obtain ⟨u, hu, hsu, hcl⟩ :=
    normal_exists_closure_subset hK (hO.preimage continuous_subtype_val) (preimage_mono hKO)
  refine ⟨Subtype.val '' closure u, ?_, ?_, ?_, ?_⟩
  · rw [Subtype.val_injective.preimage_image]
    exact isClosed_closure
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rintro _ ⟨x, hx, rfl⟩
    exact hcl hx
  · refine Subset.trans ?_ (interior_maximal (image_mono subset_closure)
      (hU'.isOpenMap_subtype_val u hu))
    intro k hk
    exact ⟨⟨k, hKU' hk⟩, hsu hk, rfl⟩

section top

variable (R : Type u) [CommRing R] {Y : TopCat.{u}} [T2Space Y]

omit [T2Space Y] in
/-- The inclusion of the open subset `⊤` into `Y` is proper. -/
lemma isProperMap_inclHom_top : IsProperMap (inclHom (⊤ : TopologicalSpace.Opens Y)) :=
  (Homeomorph.Set.univ Y).isProperMap

/-- Restricting to the whole space and pushing back is the identity, on chains. -/
lemma chainMap_inclHom_top_restrictChainMap {n : ℕ} (c : (BM R Y).X n) :
    ((chainMap R (ModuleCat.of R R) (inclHom (⊤ : TopologicalSpace.Opens Y))
      (isProperMap_inclHom_top (Y := Y))).f n).hom
        (((restrictChainMap R (ModuleCat.of R R) (⊤ : TopologicalSpace.Opens Y)).f n).hom c) =
      c := by
  classical
  set T := (⊤ : TopologicalSpace.Opens Y)
  have hinj : Function.Injective ((TopCat.toSSet.map (inclHom T)).app (op ⦋n⦌)) :=
    fun τ τ' h ↦ inclSimplex_injective T n (congrArg (SingularCochain.simplexEquiv Y _) h)
  apply Subtype.ext
  funext σ
  obtain ⟨τ, hτ⟩ := mem_range_inclSimplex T (τ := SingularCochain.simplexEquiv Y _ σ) (subset_univ _)
  have hσ : (TopCat.toSSet.map (inclHom T)).app (op ⦋n⦌) τ = σ :=
    (SingularCochain.simplexEquiv Y _).injective hτ
  change pushforwardFun ((TopCat.toSSet.map (inclHom T)).app _)
    (kernelFun (restrictKernel T n) c.1) σ = c.1 σ
  rw [← hσ, pushforwardFun_apply_of_injective hinj, kernelFun,
    finsum_eq_single _ ((TopCat.toSSet.map (inclHom T)).app _ τ) (fun σ' hσ' ↦ ?_)]
  · rw [restrictKernel, restrCoeff_of_range_subset (U := (T : Set Y)) (fun x _ ↦ by simp [T]),
      Finsupp.single_apply]
    split_ifs with hh
    · exact one_smul _ _
    · exact absurd rfl hh
  · rw [restrictKernel, restrCoeff_of_range_subset (U := (T : Set Y)) (fun x _ ↦ by simp [T]),
      Finsupp.single_apply]
    split_ifs with hh
    · exact absurd ((SingularCochain.simplexEquiv Y _).injective (hh.trans rfl)) hσ'
    · exact zero_smul _ _

/-- **Restriction to the whole space** is the identity, up to the homeomorphism `⊤ ≃ₜ Y`. -/
theorem pushforward_inclHom_top_restrict (i : ℤ)
    (a : borelMooreHomology R (ModuleCat.of R R) Y i) :
    (pushforward R (ModuleCat.of R R) (inclHom (⊤ : TopologicalSpace.Opens Y))
      (isProperMap_inclHom_top (Y := Y)) i).hom
        ((restrict R (ModuleCat.of R R) (⊤ : TopologicalSpace.Opens Y) i).hom a) = a := by
  have hc : restrictChainMap R (ModuleCat.of R R) (⊤ : TopologicalSpace.Opens Y) ≫
      chainMap R (ModuleCat.of R R) (inclHom (⊤ : TopologicalSpace.Opens Y))
        (isProperMap_inclHom_top (Y := Y)) = 𝟙 _ := by
    ext n c : 3
    exact chainMap_inclHom_top_restrictChainMap R c
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, pushforward_eq_homologyMap,
    show restrict R (ModuleCat.of R R) (⊤ : TopologicalSpace.Opens Y) i =
      homologyMap R (restrictChainMap R (ModuleCat.of R R) ⊤) i from rfl,
    homologyMap_comp_homologyMap, hc]
  simp only [homologyMap, HomologicalComplex.extendMap_id, HomologicalComplex.homologyMap_id]
  rfl

end top

end borelMooreHomology

end MMP
