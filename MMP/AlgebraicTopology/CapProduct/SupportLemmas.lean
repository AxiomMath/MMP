module

public import MMP.AlgebraicTopology.CapProduct.SupportRetraction
public import MMP.AlgebraicTopology.ThomClass.Natural
/-!
# Properties of the cap product with supports (Fulton, §19.1)

Let `X` be a closed subset of a space `Y` with arbitrarily small proper neighbourhood
deformations, and `∩ : H^j(Y, Y - X) ⊗ H_k Y → H_{k-j} X` the cap product of [BT] 3.1.7
(`MMP.borelMooreHomology.capProductSupport`).

*Forgetting supports.* For closed `X ⊆ X'`, `c ∈ H^j(Y, Y - X)` with image `c'` in
`H^j(Y, Y - X')` and `a ∈ H_k Y`, `ι_* (c ∩ a) = c' ∩ a` in `H_{k-j} X'`. On chains: a cocycle
`φ` vanishing on `Y - X` also vanishes on `Y - X'`, and the subdivisions of a cycle `z` towards
the covers `{Y - X', int N}` and `{Y - X, int N}` give homologous cycles `φ ∩ ρ z` of `N`. Then
take a deformation `G : L × [0, 1] → int N` of a closed neighbourhood `L` of `X` onto `X`, with
retraction `s`; for a retraction `r'` of `N` onto `X'`, `r' ∘ G` is a proper homotopy from
`r'|_L` to `ι ∘ s`.

*Projection formula.* For a proper `f : Y' → Y`, `X' = f⁻¹ X` and `f' : X' → X` the restriction,
`f'_* (f^* c ∩ a) = c ∩ f_* a`. On chains `f_♯ (f^♯ φ ∩ c) = φ ∩ f_♯ c`
(`BorelMooreCap.chainMap_capChain`). With closed neighbourhoods `L ⊆ int N` of `X`, the
push-forward of the subdivision `ρ' z` of a cycle of `Y'` towards `{f⁻¹(Y - X), int f⁻¹ L}` is
homologous to `f_♯ z` and has every simplex in `Y - X` or in `int N`, so it computes the
neighbourhood cap product in `N` (`BorelMooreCap.mk_restrict_capChain_of_small`). Then a
deformation `G` of a closed neighbourhood of `X'` onto `X'` inside `int f⁻¹ L`, with retraction
`s`, and a retraction `r` of `N` onto `X` give the proper homotopy `r ∘ f ∘ G` from `r ∘ f` to
`f' ∘ s`.

## Main results

* `MMP.borelMooreHomology.capProductNbhd_forget`: the neighbourhood cap product
  does not see the forgetful map.
* `MMP.borelMooreHomology.pushforward_subsetInclusionOfSubset_capProductSupport`:
  forgetting supports, `ι_* (c ∩ a) = c' ∩ a`.
* `MMP.borelMooreHomology.pushforward_preimageRestrict_capProductNbhd`: the
  projection formula for the neighbourhood cap product.
* `MMP.borelMooreHomology.pushforward_restrictPreimage_capProductSupportPullback`:
  the projection formula, `f'_* (f^* c ∩ a) = c ∩ f_* a`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* W. Fulton, R. MacPherson, *Categorical framework for the study of singular spaces*, 2.2, 3.1.7.
-/

@[expose] public noncomputable section

open CategoryTheory Set Topology Opposite Simplicial

universe u

namespace MMP

namespace cohomologyWithSupports

variable (R : Type u) [CommRing R]

/-- Transport along an equality of degrees commutes with the pull-back. -/
lemma congrIndex_pullback {Y' Y : TopCat.{u}} (f : Y' ⟶ Y) (X : Set Y) {k k' : ℤ} (hk : k = k')
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y X k) :
    congrIndex R Y' rfl hk ((pullback R _ f X k).hom c) =
      (pullback R _ f X k').hom (congrIndex R Y rfl hk c) := by
  subst hk
  rfl

/-- Transport along an equality of degrees commutes with the forgetful map. -/
lemma congrIndex_forget (Y : TopCat.{u}) {X X' : Set Y} (h : X ⊆ X') {k k' : ℤ} (hk : k = k')
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y X k) :
    congrIndex R Y rfl hk ((forget R _ Y h k).hom c) =
      (forget R _ Y h k').hom (congrIndex R Y rfl hk c) := by
  subst hk
  rfl

end cohomologyWithSupports

namespace SingularCochain

open SingularChain

variable {R : Type u} [CommRing R] {Y : TopCat.{u}}

/-- Pulling a cochain back along the identity leaves it unchanged. -/
@[simp]
lemma cochainPullback_id (n : ℕ) (φ : Simplex Y n → R) : cochainPullback R (𝟙 Y) n φ = φ :=
  rfl

end SingularCochain

namespace BorelMooreCap

open SingularCross BorelMooreCross SingularCochain SingularChain LocallyFiniteChain
  borelMooreHomology

variable {R : Type u} [CommRing R] {Y : TopCat.{u}}

/-- Hatcher's subdivision towards `{A, int N}` fixes the subdivision towards a refining cover
`{A', int N'}`, `A' ⊆ A`, `N' ⊆ N`. -/
lemma nbhdSubdiv_nbhdSubdiv_of_refines {A A' N N' : Set Y} (hA' : IsOpen A')
    (hAN' : A' ∪ interior N' = univ) (hA'A : A' ⊆ A) (hN'N : N' ⊆ N) {n : ℕ}
    (c : (BM R Y).X n) :
    (nbhdSubdiv R A N n).hom ((nbhdSubdiv R A' N' n).hom c) = (nbhdSubdiv R A' N' n).hom c := by
  refine smallChainMapLF_f_hom_of_small R _ _ fun σ hσ ↦ ?_
  obtain ⟨U, hU, hσU⟩ := smallChainMapLF_small R (ModuleCat.of R R)
    (𝒰 := {A', interior N'}) (by rintro U (rfl | rfl) <;> simp [hA'])
    (by rwa [sUnion_insert, sUnion_singleton]) n c hσ
  rcases hU with rfl | rfl
  · exact ⟨_, Or.inl rfl, hσU.trans hA'A⟩
  · exact ⟨_, Or.inr rfl, hσU.trans (interior_mono hN'N)⟩

/-- In `H_q N`, for a cocycle `φ` vanishing on `A`, the classes of `(φ ∩ ρ' z)|_N` and
`(φ ∩ ρ z)|_N` agree, for the subdivisions `ρ'`, `ρ` towards `{A', int N'}` and `{A, int N}`,
`A' ⊆ A`, `N' ⊆ N`. -/
lemma mk_restrict_capChain_nbhdSubdiv_of_refines {A A' N N' : Set Y} (hA : IsOpen A)
    (hA' : IsOpen A') (hN : IsClosed N) (hAN : A ∪ interior N = univ)
    (hAN' : A' ∪ interior N' = univ) (hA'A : A' ⊆ A) (hN'N : N' ⊆ N) (p q n : ℕ)
    (h : p + q = n) (φ : relCocycles R A p) (z : Cyc (R := R) Y n)
    (hc : (subsetRestrictMap R (ModuleCat.of R R) N q).hom
      (capChain R p q n h φ.1 ((nbhdSubdiv R A' N' n).hom z.1)) ∈
        Cyc (R := R) (TopCat.of N) q) :
    (Submodule.Quotient.mk ⟨_, hc⟩ : HomQ (R := R) (TopCat.of N) q) =
      Submodule.Quotient.mk (capCycNbhd R hA hN hAN p q n h φ z) := by
  refine (Submodule.Quotient.eq _).2 ?_
  set D' := (smallHomotopyMap R (ModuleCat.of R R) {A', interior N'} n).hom z.1
  have hz : (nbhdSubdiv R A' N' n).hom z.1 - (nbhdSubdiv R A N n).hom z.1 =
      -((BM R Y).d (n + 1) n).hom ((nbhdSubdiv R A N (n + 1)).hom D') := by
    have e := sub_smallChainMapLF_eq_d {A', interior N'} z.2
    rw [← nbhdSubdiv_d, ← nbhdSubdiv_nbhdSubdiv_of_refines hA' hAN' hA'A hN'N z.1, ← map_sub,
      ← map_neg, ← e, neg_sub]
  have hu := isSupportedIn_neg (isSupportedIn_capChain_nbhdSubdiv hA hAN
    p (q + 1) (n + 1) (by omega) φ.2.1 D')
  refine restrict_d_mem_bdry hN _ hu _ ?_
  change (subsetRestrictMap R (ModuleCat.of R R) N q).hom
      (capChain R p q n h φ.1 ((nbhdSubdiv R A' N' n).hom z.1)) -
    (subsetRestrictMap R (ModuleCat.of R R) N q).hom
      (capChain R p q n h φ.1 ((nbhdSubdiv R A N n).hom z.1)) = _
  rw [← map_sub, ← map_sub, hz, map_neg, ← d_capChain_relCocycle A p q n h φ]
  simp only [map_neg]

/-- The neighbourhood cap product does not see the forgetful map `H^p(Y, A) → H^p(Y, A')`,
`A' ⊆ A`. -/
theorem capHomQNbhd_relCohomologyMap_id {A A' N : Set Y} (hA : IsOpen A) (hA' : IsOpen A')
    (hN : IsClosed N) (hAN : A ∪ interior N = univ) (hAN' : A' ∪ interior N = univ)
    (hA'A : A' ⊆ A) (p q n : ℕ) (h : p + q = n) (x : relCohomology R A p)
    (y : HomQ (R := R) Y n) :
    capHomQNbhd R hA' hN hAN' p q n h (relCohomologyMap R (𝟙 Y) hA'A p x) y =
      capHomQNbhd R hA hN hAN p q n h x y := by
  induction x using Submodule.Quotient.induction_on with | H φ => ?_
  induction y using Submodule.Quotient.induction_on with | H z => ?_
  erw [relCohomologyMap_mk, capHomQNbhd_mk, capHomQNbhd_mk]
  exact mk_restrict_capChain_nbhdSubdiv_of_refines hA hA' hN hAN hAN' hA'A subset_rfl p q n h
    φ z _

end BorelMooreCap

namespace borelMooreHomology

open BorelMooreCap BorelMooreCross SingularCochain

variable (R : Type u) [CommRing R]

/-- The neighbourhood cap product with `c ∈ H^j(Y, Y - X)` is the one with its image
`c' ∈ H^j(Y, Y - X')` under the forgetful map, for closed `X ⊆ X'` and a closed neighbourhood
`N` of `X'`. -/
theorem capProductNbhd_forget (Y : TopCat.{u}) {X X' N : Set Y} (hX : IsClosed X)
    (hX' : IsClosed X') (hN : IsClosed N) (hXX' : X ⊆ X') (hX'N : X' ⊆ interior N) (j k : ℤ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y X j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y k) :
    capProductNbhd R Y hX' hN hX'N j k
        ((cohomologyWithSupports.forget R (ModuleCat.of R R) Y hXX' j).hom c) a =
      capProductNbhd R Y hX hN (hXX'.trans hX'N) j k c a := by
  unfold capProductNbhd
  split_ifs with h
  · simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
      LinearEquiv.trans_apply]
    congr 2
    rw [cohomologyWithSupports.congrIndex_forget, cohomologyWithSupports.forget]
    erw [relativeSingularCohomologyEquiv_map]
    exact LinearMap.ext fun y ↦ capHomQNbhd_relCohomologyMap_id (R := R) _ _ _ _ _ _ _ _ _ _ _ y
  · simp

/-- **Forgetting supports** (Fulton §19.1; [BT] 2.2). Let `X ⊆ X'` be closed subsets of a space
`Y`, both with arbitrarily small proper neighbourhood deformations, `ι : X → X'` the inclusion,
`c ∈ H^j(Y, Y - X)` with image `c' ∈ H^j(Y, Y - X')` under the forgetful map, and `a ∈ H_k Y`.
Then `ι_* (c ∩ a) = c' ∩ a` in `H_{k-j} X'`. -/
theorem pushforward_subsetInclusionOfSubset_capProductSupport (Y : TopCat.{u}) {X X' : Set Y}
    (hX : IsClosed X) (hX' : IsClosed X') (hXd : HasProperNeighbourhoodDeformations X)
    (hX'd : HasProperNeighbourhoodDeformations X') (hXX' : X ⊆ X') (j k : ℤ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y X j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y k) :
    (pushforward R (ModuleCat.of R R) (subsetInclusionOfSubset hXX')
        (isProperMap_subsetInclusionOfSubset hX hXX') (k - j)).hom
        (capProductSupport R Y hX hXd j k c a) =
      capProductSupport R Y hX' hX'd j k
        ((cohomologyWithSupports.forget R (ModuleCat.of R R) Y hXX' j).hom c) a := by
  obtain ⟨N, hN, hX'N, -, r, hr, hrX, -⟩ := hX'd univ Filter.univ_mem
  have hM : interior N ∈ 𝓝ˢ X := isOpen_interior.mem_nhdsSet.2 (hXX'.trans hX'N)
  obtain ⟨L, hL, hXL, hLM, s, hs, hsX, G, hG, hG0, hG1, -, hGM⟩ := hXd _ hM
  have hLN : L ⊆ N := hLM.trans interior_subset
  let s' : C(L, X') := ⟨fun y ↦ ⟨s y, hXX' (s y).2⟩, by fun_prop⟩
  have hs' : IsProperMap s' := (isProperMap_subsetInclusionOfSubset hX hXX').comp hs
  rw [capProductSupport_eq_capProductAlong R Y hX hXd hL hXL s hs hsX,
    capProductSupport_eq_capProductAlong R Y hX' hX'd hN hX'N r hr hrX]
  simp only [capProductAlong, LinearMap.compr₂_apply]
  rw [capProductNbhd_forget R Y hX hX' hN hXX' hX'N,
    ← pushforward_subsetInclusionOfSubset_capProductNbhd R Y hX hN (hXX'.trans hX'N) hL hXL hLN]
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← pushforward_comp,
    ← LinearMap.comp_apply (g := (pushforward R _ (subsetInclusionOfSubset hLN) _ _).hom),
    ← ModuleCat.hom_comp, ← pushforward_comp,
    pushforward_retraction_eq_of_homotopy R hL hLN r hr hrX s' hs' G hG hG0 hG1
      (fun q ↦ interior_subset (hGM q))]
  rfl

end borelMooreHomology

namespace BorelMooreCap

open SingularCross BorelMooreCross SingularCochain SingularChain LocallyFiniteChain
  borelMooreHomology

variable {R : Type u} [CommRing R] {Y' Y : TopCat.{u}}

/-! ### The cap product and proper push-forward on chains -/

section projection

variable (f : Y' ⟶ Y) (hf : IsProperMap f)

/-- Simplicial operators commute with post-composition. -/
lemma map_opS {a b : ℕ} (g : Fin (a + 1) → Fin (b + 1)) (σ : Simp Y' b) :
    (TopCat.toSSet.map f).app (op ⦋a⦌) (opS g σ) =
      opS g ((TopCat.toSSet.map f).app (op ⦋b⦌) σ) := by
  apply (simplexEquiv Y a).injective
  rw [simplexEquiv_opS]
  change f.hom.comp (simplexEquiv Y' a (opS g σ)) = _
  rw [simplexEquiv_opS]
  rfl

include hf in
/-- Push-forward along `f` commutes with the simplicial operators `pf`. -/
lemma chainMap_pf {a b : ℕ} (g : Fin (a + 1) → Fin (b + 1)) (c : (BM R Y').X b) :
    ((chainMap R (ModuleCat.of R R) f hf).f a).hom (pf R g c) =
      pf R g (((chainMap R (ModuleCat.of R R) f hf).f b).hom c) := by
  apply coeff_injective R
  rw [coeff_chainMap_f, coeff_pf, coeff_pf, coeff_chainMap_f,
    pushforwardFun_comp_of_finite (opS g) ((TopCat.toSSet.map f).app (op ⦋a⦌)) (coeff R c)
      (fun υ ↦ finite_fiber_of_isProperMap (coeff_mem R c) hf _
        (fun σ ↦ (singularSimplexImage_map f _).trans_subset (image_mono (image_opS_subset g σ)))
        υ (isCompact_singularSimplexImage υ) (nonempty_singularSimplexImage υ)),
    pushforwardFun_comp_of_finite ((TopCat.toSSet.map f).app (op ⦋b⦌)) (opS g) (coeff R c)
      (fun υ ↦ finite_fiber_of_isProperMap (coeff_mem R c) hf _
        (fun σ ↦ (image_opS_subset g _).trans (singularSimplexImage_map f σ).le)
        υ (isCompact_singularSimplexImage υ) (nonempty_singularSimplexImage υ))]
  exact congrArg (pushforwardFun · (coeff R c)) (funext fun σ ↦ map_opS f g σ)

/-- Pushing forward `(g ∘ F) * x` along `F` is multiplying the push-forward of `x` by `g`, at a
point `τ` whose fibre meets the support of `x` in a finite set. -/
lemma pushforwardFun_mul_comp {S T : Type*} (F : S → T) (g : T → R) (x : S → R) (τ : T)
    (hfin : {σ | x σ ≠ 0 ∧ F σ = τ}.Finite) :
    pushforwardFun F (fun σ ↦ g (F σ) * x σ) τ = g τ * pushforwardFun F x τ := by
  let F₀ := hfin.toFinset
  have hF : ∀ σ, x σ ≠ 0 → F σ = τ → σ ∈ F₀ := fun σ h1 h2 ↦
    hfin.mem_toFinset.2 ⟨h1, h2⟩
  have hF' : ∀ σ, (fun σ ↦ g (F σ) * x σ) σ ≠ 0 → F σ = τ → σ ∈ F₀ :=
    fun σ h1 h2 ↦ hF σ (fun h ↦ h1 (by simp [h])) h2
  rw [pushforwardFun_apply_eq_sum _ _ τ F₀ hF', pushforwardFun_apply_eq_sum _ _ τ F₀ hF,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  split_ifs with h
  · rw [h]
  · simp

include hf in
/-- Projection formula for the weights: pushing forward `c` multiplied by `g ∘ f_♯` is
multiplying the push-forward by `g`. -/
lemma chainMap_W {a : ℕ} (g : Simp Y a → R) (c : (BM R Y').X a) :
    ((chainMap R (ModuleCat.of R R) f hf).f a).hom
        (W R (g ∘ (TopCat.toSSet.map f).app (op ⦋a⦌)) c) =
      W R g (((chainMap R (ModuleCat.of R R) f hf).f a).hom c) := by
  apply coeff_injective R
  funext τ
  rw [coeff_chainMap_f, coeff_W, coeff_W, coeff_chainMap_f]
  exact pushforwardFun_mul_comp _ g _ τ (finite_fiber_of_isProperMap (coeff_mem R c) hf _
    (fun σ ↦ (singularSimplexImage_map f σ).le) τ (isCompact_singularSimplexImage τ)
    (nonempty_singularSimplexImage τ))

/-- The weight of the pull-back `f^♯ φ` along `e` is the weight of `φ` along `e` composed with
`f_♯` on simplices. -/
lemma wt_cochainPullback {a b : ℕ} (φ : Simplex Y a → R) (e : Fin (a + 1) → Fin (b + 1)) :
    wt (cochainPullback R f a φ) e = wt φ e ∘ (TopCat.toSSet.map f).app (op ⦋b⦌) :=
  rfl

include hf in
/-- **The projection formula on chains**: `f_♯ (f^♯ φ ∩ c) = φ ∩ f_♯ c`. -/
theorem chainMap_capChain (p q n : ℕ) (h : p + q = n) (φ : Simplex Y p → R)
    (c : (BM R Y').X n) :
    ((chainMap R (ModuleCat.of R R) f hf).f q).hom
        (capChain R p q n h (cochainPullback R f p φ) c) =
      capChain R p q n h φ (((chainMap R (ModuleCat.of R R) f hf).f n).hom c) := by
  rw [capChain_apply, capChain_apply, chainMap_pf, wt_cochainPullback, chainMap_W]

include hf in
/-- If `c` is supported in `N'` and `f '' N' ⊆ N`, then `f_♯ c` is supported in `N`. -/
lemma isSupportedIn_chainMap {n : ℕ} {N' : Set Y'} {N : Set Y} (hNN : f '' N' ⊆ N)
    {c : (BM R Y').X n} (hc : IsSupportedIn R (ModuleCat.of R R) N' c) :
    IsSupportedIn R (ModuleCat.of R R) N (((chainMap R (ModuleCat.of R R) f hf).f n).hom c) := by
  intro τ hτ
  obtain ⟨σ, hσ, rfl⟩ := support_pushforwardFun_subset _ _ hτ
  rw [singularSimplexImage_map]
  exact (image_mono (hc σ hσ)).trans hNN

end projection

end BorelMooreCap

namespace borelMooreHomology

open BorelMooreCap BorelMooreCross SingularCochain SingularChain LocallyFiniteChain

variable {R : Type u} [CommRing R] {Y' Y : TopCat.{u}}

/-- The restriction `f⁻¹ L → N` of a continuous `f : Y' → Y`, for `L ⊆ N`. -/
def preimageRestrict (f : Y' ⟶ Y) {L N : Set Y} (hLN : L ⊆ N) :
    TopCat.of (f ⁻¹' L) ⟶ TopCat.of N :=
  TopCat.ofHom ⟨fun y ↦ ⟨f y, hLN y.2⟩, (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- For proper `f` and closed `L ⊆ N`, the restriction `f⁻¹ L → N` of `f` is proper. -/
lemma isProperMap_preimageRestrict (f : Y' ⟶ Y) (hf : IsProperMap f) {L N : Set Y}
    (hL : IsClosed L) (hLN : L ⊆ N) : IsProperMap (preimageRestrict f hLN) :=
  (isProperMap_subsetInclusionOfSubset hL hLN).comp (hf.restrictPreimage L)

variable (R) in
/-- Restriction to subsets commutes with push-forward, for chains supported in `f⁻¹ L`. -/
lemma chainMap_preimageRestrict_subsetRestrictMap (f : Y' ⟶ Y) (hf : IsProperMap f)
    {L N : Set Y} (hL : IsClosed L) (hN : IsClosed N) (hLN : L ⊆ N) {n : ℕ}
    {c : (BM R Y').X n} (hc : IsSupportedIn R (ModuleCat.of R R) (f ⁻¹' L) c) :
    ((chainMap R (ModuleCat.of R R) (preimageRestrict f hLN)
        (isProperMap_preimageRestrict f hf hL hLN)).f n).hom
        ((subsetRestrictMap R (ModuleCat.of R R) (f ⁻¹' L) n).hom c) =
      (subsetRestrictMap R (ModuleCat.of R R) N n).hom
        (((chainMap R (ModuleCat.of R R) f hf).f n).hom c) := by
  have hL' : IsClosed (f ⁻¹' L) := hL.preimage f.hom.continuous
  apply chainMap_subsetInclusion_injective R _ hN n
  rw [chainMap_subsetRestrictMap R _ hN (isSupportedIn_chainMap f hf
    ((image_preimage_subset _ _).trans hLN) hc)]
  have e1 := chainMap_comp R (ModuleCat.of R R) (preimageRestrict f hLN) (subsetInclusion N)
    (isProperMap_preimageRestrict f hf hL hLN) (isProperMap_subsetInclusion hN)
  have e2 := chainMap_comp R (ModuleCat.of R R) (subsetInclusion (f ⁻¹' L)) f
    (isProperMap_subsetInclusion hL') hf
  have e3 : chainMap R (ModuleCat.of R R) (preimageRestrict f hLN ≫ subsetInclusion N)
      ((isProperMap_subsetInclusion hN).comp (isProperMap_preimageRestrict f hf hL hLN)) =
      chainMap R (ModuleCat.of R R) (subsetInclusion (f ⁻¹' L) ≫ f)
        (hf.comp (isProperMap_subsetInclusion hL')) := rfl
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← HomologicalComplex.comp_f, ← e1, e3, e2,
    HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    chainMap_subsetRestrictMap R _ hL' hc]

end borelMooreHomology

namespace BorelMooreCap

open SingularCross BorelMooreCross SingularCochain SingularChain LocallyFiniteChain
  borelMooreHomology

variable {R : Type u} [CommRing R] {Y' Y : TopCat.{u}}

/-- In `H_q N`, for a cocycle `φ` vanishing on `A` and a cycle `z`, the class of `(φ ∩ w)|_N` is
`[φ] ∩_N [z]` for every chain `w` homologous to `z` all of whose simplices lie in `A` or in
`int N`. -/
lemma mk_restrict_capChain_of_small {A N : Set Y} (hA : IsOpen A) (hN : IsClosed N)
    (hAN : A ∪ interior N = univ) (p q n : ℕ) (h : p + q = n) (φ : relCocycles R A p)
    (z : Cyc (R := R) Y n) (w : (BM R Y).X n)
    (hw : ∀ σ, coeff R w σ ≠ 0 → ∃ U ∈ ({A, interior N} : Set (Set Y)),
      singularSimplexImage Y σ ⊆ U)
    (u : (BM R Y).X (n + 1)) (hu : z.1 - w = ((BM R Y).d (n + 1) n).hom u)
    (hc : (subsetRestrictMap R (ModuleCat.of R R) N q).hom (capChain R p q n h φ.1 w) ∈
      Cyc (R := R) (TopCat.of N) q) :
    (Submodule.Quotient.mk ⟨_, hc⟩ : HomQ (R := R) (TopCat.of N) q) =
      Submodule.Quotient.mk (capCycNbhd R hA hN hAN p q n h φ z) := by
  refine (Submodule.Quotient.eq _).2 ?_
  have hρ : (nbhdSubdiv R A N n).hom w = w := smallChainMapLF_f_hom_of_small R _ _ hw
  have hz : w - (nbhdSubdiv R A N n).hom z.1 =
      -((BM R Y).d (n + 1) n).hom ((nbhdSubdiv R A N (n + 1)).hom u) := by
    rw [← nbhdSubdiv_d, ← map_neg, ← hu, neg_sub, map_sub, hρ]
  have hu' := isSupportedIn_neg (isSupportedIn_capChain_nbhdSubdiv hA hAN
    p (q + 1) (n + 1) (by omega) φ.2.1 u)
  refine restrict_d_mem_bdry hN _ hu' _ ?_
  change (subsetRestrictMap R (ModuleCat.of R R) N q).hom (capChain R p q n h φ.1 w) -
    (subsetRestrictMap R (ModuleCat.of R R) N q).hom
      (capChain R p q n h φ.1 ((nbhdSubdiv R A N n).hom z.1)) = _
  rw [← map_sub, ← map_sub, hz, map_neg, ← d_capChain_relCocycle A p q n h φ]
  simp only [map_neg]

/-- **The projection formula for the neighbourhood cap product, on cocycles modulo
coboundaries.** For a proper `f : Y' → Y`, `A' ⊆ f⁻¹ A` open and closed `L ⊆ int N`, the
push-forward along `f : f⁻¹ L → N` of `f^* x ∩_{f⁻¹ L} [z]` is `x ∩_N [f_♯ z]`. -/
theorem homologyMap_preimageRestrict_capHomQNbhd (f : Y' ⟶ Y) (hf : IsProperMap f)
    {A L N : Set Y} {A' : Set Y'} (hA : IsOpen A) (hA' : IsOpen A') (hA'f : A' ⊆ f ⁻¹' A)
    (hL : IsClosed L) (hN : IsClosed N) (hAN : A ∪ interior N = univ) (hLN : L ⊆ interior N)
    (hAL' : A' ∪ interior (f ⁻¹' L) = univ) (p q n : ℕ) (h : p + q = n)
    (x : relCohomology R A p) (b : borelMooreHomology R (ModuleCat.of R R) Y' n) :
    (homologyMap R (chainMap R (ModuleCat.of R R)
        (preimageRestrict f (hLN.trans interior_subset))
        (isProperMap_preimageRestrict f hf hL _)) q).hom
      ((homologyEquiv R (TopCat.of (f ⁻¹' L)) q).symm
        (capHomQNbhd R hA' (hL.preimage f.hom.continuous) hAL' p q n h
          (relCohomologyMap R f hA'f p x) (homologyEquiv R Y' n b))) =
      (homologyEquiv R (TopCat.of N) q).symm
        (capHomQNbhd R hA hN hAN p q n h x
          (homologyEquiv R Y n
            ((homologyMap R (chainMap R (ModuleCat.of R R) f hf) n).hom b))) := by
  obtain ⟨y, rfl⟩ := (homologyEquiv R Y' n).symm.surjective b
  rw [LinearEquiv.apply_symm_apply]
  induction x using Submodule.Quotient.induction_on with | H φ => ?_
  induction y using Submodule.Quotient.induction_on with | H z => ?_
  erw [homologyMap_homologyEquiv_symm_mk R (chainMap R (ModuleCat.of R R) f hf),
    LinearEquiv.apply_symm_apply]
  erw [relCohomologyMap_mk, capHomQNbhd_mk, capHomQNbhd_mk, homologyMap_homologyEquiv_symm_mk]
  congr 1
  set D' := (smallHomotopyMap R (ModuleCat.of R R) {A', interior (f ⁻¹' L)} n).hom z.1
  set w := ((chainMap R (ModuleCat.of R R) f hf).f n).hom
    ((nbhdSubdiv R A' (f ⁻¹' L) n).hom z.1)
  have hsupp := isSupportedIn_capChain_nbhdSubdiv hA' hAL' p q n h
    (cochainPullback_mem_vanishing f hA'f φ.2.1) z.1
  have e := (chainMap_preimageRestrict_subsetRestrictMap R f hf hL hN
    (hLN.trans interior_subset) hsupp).trans
    (congrArg _ (chainMap_capChain f hf p q n h φ.1 _))
  have hw : ∀ σ, coeff R w σ ≠ 0 → ∃ U ∈ ({A, interior N} : Set (Set Y)),
      singularSimplexImage Y σ ⊆ U := by
    intro τ hτ
    obtain ⟨σ, hσ, rfl⟩ := support_pushforwardFun_subset _ _ hτ
    obtain ⟨U, hU, hσU⟩ := smallChainMapLF_small R (ModuleCat.of R R)
      (𝒰 := {A', interior (f ⁻¹' L)}) (by rintro U (rfl | rfl) <;> simp [hA'])
      (by rwa [sUnion_insert, sUnion_singleton]) n z.1 hσ
    rw [singularSimplexImage_map]
    rcases hU with rfl | rfl
    · exact ⟨A, Or.inl rfl, (image_mono hσU).trans (image_subset_iff.2 hA'f)⟩
    · exact ⟨interior N, Or.inr rfl,
        (image_mono (hσU.trans interior_subset)).trans ((image_preimage_subset _ _).trans hLN)⟩
  have hu : ((chainMap R (ModuleCat.of R R) f hf).f n).hom z.1 - w =
      ((BM R Y).d (n + 1) n).hom (((chainMap R (ModuleCat.of R R) f hf).f (n + 1)).hom D') := by
    have hc := congrArg (fun g ↦ g.hom D') ((chainMap R (ModuleCat.of R R) f hf).comm (n + 1) n)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hc
    have e2 := congrArg ((chainMap R (ModuleCat.of R R) f hf).f n).hom
      (sub_smallChainMapLF_eq_d (R := R) {A', interior (f ⁻¹' L)} z.2)
    erw [map_sub] at e2
    exact e2.trans hc.symm
  refine Eq.trans ?_ (mk_restrict_capChain_of_small hA hN hAN p q n h φ
    ⟨_, chainMap_mem_cyc R _ z⟩ w hw _ hu
    (e ▸ chainMap_mem_cyc R _ (capCycNbhd R hA' (hL.preimage f.hom.continuous) hAL' p q n h
      ⟨cochainPullback R f p φ.1, cochainPullback_mem_relCocycles f hA'f φ.2⟩ z)))
  congr 1
  exact Subtype.ext e

end BorelMooreCap

namespace borelMooreHomology

open BorelMooreCap BorelMooreCross SingularCochain

variable (R : Type u) [CommRing R]

/-- If `X ⊆ int L`, then `f⁻¹ X ⊆ int (f⁻¹ L)` for continuous `f`. -/
lemma preimage_subset_interior_preimage {Y' Y : TopCat.{u}} (f : Y' ⟶ Y) {X L : Set Y}
    (hXL : X ⊆ interior L) : f ⁻¹' X ⊆ interior (f ⁻¹' L) :=
  (preimage_mono hXL).trans (preimage_interior_subset_interior_preimage f.hom.continuous)

/-- A proper deformation `G` of `L' ⊆ f⁻¹ L` onto `f⁻¹ X` makes the push-forward along
`L' → f⁻¹ L → N → X` (the last map a retraction `r`) equal to that along `L' → f⁻¹ X → X`. -/
lemma pushforward_preimageRestrict_retraction_eq_of_homotopy {Y' Y : TopCat.{u}} (f : Y' ⟶ Y)
    (hf : IsProperMap f) {X N L : Set Y} {L' : Set Y'} (hL : IsClosed L) (hL' : IsClosed L')
    (hL'L : L' ⊆ f ⁻¹' L) (hLN : L ⊆ N) (r : C(N, X)) (hr : IsProperMap r)
    (hrX : ∀ y : N, (y : Y) ∈ X → (r y : Y) = y) (s : C(L', f ⁻¹' X)) (hs : IsProperMap s)
    (G : C(L' × unitInterval, Y')) (hG : IsProperMap G) (hG0 : ∀ y, G (y, 0) = y)
    (hG1 : ∀ y, G (y, 1) = s y) (hGL : ∀ q, G q ∈ f ⁻¹' L) (j : ℤ) :
    pushforward R (ModuleCat.of R R)
        (subsetInclusionOfSubset hL'L ≫ preimageRestrict f hLN ≫ TopCat.ofHom r)
        ((hr.comp (isProperMap_preimageRestrict f hf hL _)).comp
          (isProperMap_subsetInclusionOfSubset hL' hL'L)) j =
      pushforward R (ModuleCat.of R R) (TopCat.ofHom s ≫ TopCat.ofHom (f.hom.restrictPreimage X))
        ((hf.restrictPreimage X).comp hs) j := by
  have hGN : ∀ q, f (G q) ∈ N := fun q ↦ hLN (hGL q)
  let GN : C(L' × unitInterval, f ⁻¹' L) := ⟨fun q ↦ ⟨G q, hGL q⟩, G.continuous.subtype_mk _⟩
  have hGN' : IsProperMap GN :=
    isProperMap_of_comp_of_inj GN.continuous continuous_subtype_val hG Subtype.val_injective
  let H : TopCat.Homotopy
      (subsetInclusionOfSubset hL'L ≫ preimageRestrict f hLN ≫ TopCat.ofHom r)
      (TopCat.ofHom s ≫ TopCat.ofHom (f.hom.restrictPreimage X)) :=
    { toFun := fun p ↦ r (preimageRestrict f hLN (GN (p.2, p.1)))
      continuous_toFun := r.continuous.comp ((preimageRestrict f _).hom.continuous.comp
        (GN.continuous.comp continuous_swap))
      map_zero_left := fun y ↦ by
        change r ⟨f (G (y, 0)), _⟩ = r ⟨f y, _⟩
        congr 1
        exact Subtype.ext (congrArg f (hG0 y))
      map_one_left := fun y ↦ by
        change r ⟨f (G (y, 1)), hGN _⟩ = ⟨f (s y), (s y).2⟩
        have e : (⟨f (G (y, 1)), hGN _⟩ : N) = ⟨f (s y), hG1 y ▸ hGN (y, 1)⟩ :=
          Subtype.ext (congrArg f (hG1 y))
        rw [e]
        exact Subtype.ext (hrX _ (s y).2) }
  have hH : IsProperMap H := hr.comp ((isProperMap_preimageRestrict f hf hL _).comp
    (hGN'.comp (Homeomorph.prodComm unitInterval L').isProperMap))
  exact pushforward_eq_of_properHomotopy R (ModuleCat.of R R) _ _ H hH j

/-- **The projection formula for the neighbourhood cap product.** For a proper `f : Y' → Y`, a
closed `X ⊆ Y` and closed neighbourhoods `L ⊆ int N` of `X`, the push-forward along
`f : f⁻¹ L → N` of `f^* c ∩_{f⁻¹ L} a` is `c ∩_N f_* a`. -/
theorem pushforward_preimageRestrict_capProductNbhd {Y' Y : TopCat.{u}} (f : Y' ⟶ Y)
    (hf : IsProperMap f) {X L N : Set Y} (hX : IsClosed X) (hL : IsClosed L) (hN : IsClosed N)
    (hXL : X ⊆ interior L) (hLN : L ⊆ interior N) (j k : ℤ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y X j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y' k) :
    (pushforward R (ModuleCat.of R R) (preimageRestrict f (hLN.trans interior_subset))
        (isProperMap_preimageRestrict f hf hL _) (k - j)).hom
      (capProductNbhd R Y' (hX.preimage f.hom.continuous) (hL.preimage f.hom.continuous)
        (preimage_subset_interior_preimage f hXL) j k
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) f X j).hom c) a) =
      capProductNbhd R Y hX hN (hXL.trans (interior_subset.trans hLN)) j k c
        ((pushforward R (ModuleCat.of R R) f hf k).hom a) := by
  unfold capProductNbhd
  split_ifs with h
  · simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
      LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply, congrDegree_symm,
      pushforward_eq_homologyMap]
    rw [homologyMap_congrDegree, ← homologyMap_congrDegree R (chainMap R (ModuleCat.of R R) f hf)]
    rw [cohomologyWithSupports.congrIndex_pullback, cohomologyWithSupports.pullback]
    erw [relativeSingularCohomologyEquiv_map]
    exact congrArg (congrDegree R (TopCat.of N) _)
      (homologyMap_preimageRestrict_capHomQNbhd f hf _ _ _ hL hN _ hLN _ _ _ _ _ _ _)
  · simp

/-- **Projection formula** (Fulton §19.1; [BT] 2.2 (A123)). Let `X` be closed in a space `Y`,
`f : Y' → Y` proper, `X' = f⁻¹ X`, `f' : X' → X` the restriction, `c ∈ H^j(Y, Y - X)` and
`a ∈ H_k Y'`, with `X` and `X'` having arbitrarily small proper neighbourhood deformations (the
setting of the cap products). Then `f'_* (f^* c ∩ a) = c ∩ f_* a` in `H_{k-j} X`. -/
theorem pushforward_restrictPreimage_capProductSupportPullback {Y' Y : TopCat.{u}}
    (f : Y' ⟶ Y) (hf : IsProperMap f) {X : Set Y} (hX : IsClosed X)
    (hXd : HasProperNeighbourhoodDeformations X)
    (hX'd : HasProperNeighbourhoodDeformations (f ⁻¹' X)) (j k : ℤ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y X j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y' k) :
    (pushforward R (ModuleCat.of R R) (TopCat.ofHom (f.hom.restrictPreimage X))
        (hf.restrictPreimage X) (k - j)).hom (capProductSupportPullback R f hX hX'd j k c a) =
      capProductSupport R Y hX hXd j k c ((pushforward R (ModuleCat.of R R) f hf k).hom a) := by
  obtain ⟨N, hN, hXN, -, r, hr, hrX, -⟩ := hXd univ Filter.univ_mem
  obtain ⟨L, hL, hXL, hLN, -⟩ := hXd (interior N) (isOpen_interior.mem_nhdsSet.2 hXN)
  have hX' : IsClosed (f ⁻¹' X) := hX.preimage f.hom.continuous
  have hX'L := preimage_subset_interior_preimage f hXL
  obtain ⟨L', hL', hX'L', hL'M, s, hs, hsX, G, hG, hG0, hG1, -, hGM⟩ :=
    hX'd _ (isOpen_interior.mem_nhdsSet.2 hX'L)
  have hL'L : L' ⊆ f ⁻¹' L := hL'M.trans interior_subset
  rw [capProductSupportPullback_apply,
    capProductSupport_eq_capProductAlong R Y' hX' hX'd hL' hX'L' s hs hsX,
    capProductSupport_eq_capProductAlong R Y hX hXd hN hXN r hr hrX]
  simp only [capProductAlong, LinearMap.compr₂_apply]
  rw [← pushforward_preimageRestrict_capProductNbhd R f hf hX hL hN hXL hLN,
    ← pushforward_subsetInclusionOfSubset_capProductNbhd R Y' hX' (hL.preimage f.hom.continuous)
      hX'L hL' hX'L' hL'L]
  have key := pushforward_preimageRestrict_retraction_eq_of_homotopy R f hf hL hL' hL'L
    (hLN.trans interior_subset) r hr hrX s hs G hG hG0 hG1 (fun q ↦ interior_subset (hGM q)) (k - j)
  have e1 := pushforward_comp R (ModuleCat.of R R) (TopCat.ofHom s)
    (TopCat.ofHom (f.hom.restrictPreimage X)) hs (hf.restrictPreimage X) (k - j)
  have e2 := pushforward_comp R (ModuleCat.of R R) (subsetInclusionOfSubset hL'L)
    (preimageRestrict f (hLN.trans interior_subset) ≫ TopCat.ofHom r)
    (isProperMap_subsetInclusionOfSubset hL' hL'L)
    (hr.comp (isProperMap_preimageRestrict f hf hL _)) (k - j)
  have e3 := pushforward_comp R (ModuleCat.of R R) (preimageRestrict f (hLN.trans interior_subset))
    (TopCat.ofHom r) (isProperMap_preimageRestrict f hf hL _) hr (k - j)
  rw [e2, e3, e1] at key
  have := congrArg (fun g ↦ ModuleCat.Hom.hom g (capProductNbhd R Y' hX' hL' hX'L' j k
    ((cohomologyWithSupports.pullback R (ModuleCat.of R R) f X j).hom c) a)) key
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
  exact this.symm

end borelMooreHomology

end MMP
