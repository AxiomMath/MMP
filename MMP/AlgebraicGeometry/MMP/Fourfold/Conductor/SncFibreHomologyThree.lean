module

import MMP.AlgebraicGeometry.SpecOverSpecSelf
public import MMP.Attr
public import MMP.AlgebraicGeometry.Analytic.CartierDivisorDictionary
public import MMP.AlgebraicGeometry.Chow.CycleClassTopDegree
public import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
public import MMP.AlgebraicGeometry.Divisor.SmoothWeilCartier
public import MMP.AlgebraicGeometry.IdealSheafSubscheme
public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.NormalThreefoldSlice
public import MMP.AlgebraicGeometry.ReducedSubschemeOver
public import MMP.AlgebraicGeometry.Singularities.Semismooth.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.AmpleNoRationalTail

/-!
# Degree-three homology of an antiample snc surface fibre

Let `W` be a smooth complex threefold and `E = ⋃ᵢ Eᵢ` a proper snc divisor on `W`, the support of
an effective divisor `D = ∑ mᵢ Eᵢ` with all `mᵢ > 0` such that `-D` is ample on every component
`Eᵢ`. Then the push-forwards along the inclusions `Eᵢ ⊆ E` give an isomorphism
`⨁ᵢ H_3(Eᵢ, ℚ) ≅ H_3(E, ℚ)`.

The proof uses the normalization excision sequence for `∐ Eᵢ → E`: the double locus and its
inverse image have dimension at most one, so the obstruction to bijectivity is the kernel of
`H_2(F) → H_2(∐ Eᵢ) ⊕ H_2(B)`, which the weighted curve identity for the antiample divisor `-D`
shows to be zero.

## Main results

* `MMP.Fourfold.bijective_sum_pushforward_rationalHomology_three`: the map
  `⨁ᵢ H_3(Eᵢ, ℚ) → H_3(E, ℚ)`, `(xᵢ)ᵢ ↦ ∑ᵢ (jᵢ)_* xᵢ`, is bijective.
* `MMP.Analytic.singularCohomology.mapCoeff_relativeSingularCohomology_map`: change of
  coefficients along a ring map commutes with pull-back on singular cohomology.
* `MMP.Fourfold.curveDiv`: for a double curve `η` of `D` through the component `E_P`, the prime
  divisor of `E_P` over `η`; it is a smooth curve (`MMP.Fourfold.isSmoothScheme_curveDiv`), and the
  curves over distinct double curves of the same type are disjoint
  (`MMP.Fourfold.disjoint_curveDiv`).
* `MMP.Fourfold.pushforward_capProductPullback_eq_invertibleCurveDegree_smul`: on a smooth
  projective complex curve, the push-forward to the point of `c₁(N) ∩ [C]` is `deg N` times the
  class of the point.
* `MMP.Fourfold.invertibleCurveDegree_eq_zero_of_mapCoeff_algebraicFirstChernClass_eq_zero`: on a
  smooth projective complex curve, an invertible sheaf whose first Chern class vanishes in
  `H²(C^an, ℚ)` has degree zero.

## Implementation notes

* `H_n(-, ℚ)` is `MMP.Fourfold.RationalHomology`, the rational Borel–Moore homology of the
  complex points; on the proper schemes `Eᵢ` and `E` it is singular homology.
* The components `Eᵢ` are the prime divisors in the support of `D`, with their reduced structure,
  and `E` is the reduced support `MMP.Mori.DivisorWithCoeffs.suppScheme D`. The inclusions
  `jᵢ : Eᵢ ⟶ E` are given as morphisms over `W` (the condition `jᵢ ≫ (E ⟶ W) = (Eᵢ ⟶ W)`), which
  determines them since `E ⟶ W` is a monomorphism; they are morphisms of complex schemes and
  proper, as the push-forward requires.
* "Projective" for `E` is properness of `E` over `ℂ`; together with the ampleness of `-D` on every
  component it makes every `Eᵢ` projective. "`-D` ample on `Eᵢ`" is ampleness of the pull-back of
  the invertible sheaf `𝒪_W(-D)` to `Eᵢ`.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MMP
open MMP.Intersection.Scheme (dimension)
open scoped MMP.SubschemeOver

namespace MMP.Fourfold

/-! ### Naturality of the connecting map of the Borel–Moore long exact sequence -/

section Naturality

variable {R : Type} [CommRing R]
  {A B D A' B' D' : HomologicalComplex (ModuleCat.{0} R) (ComplexShape.up ℤ)}

/-- Naturality of `MMP.ModuleCatComplex.quasiIsoConnecting` for a map of the data
`(A' → B' → D') ⟶ (A → B → D)`. -/
private theorem quasiIsoConnecting_naturality
    (f : A ⟶ B) (g : B ⟶ D) [Mono f] (w : f ≫ g = 0)
    (f' : A' ⟶ B') (g' : B' ⟶ D') [Mono f'] (w' : f' ≫ g' = 0)
    (α : A' ⟶ A) (β : B' ⟶ B) (γ : D' ⟶ D) (hαβ : f' ≫ β = α ≫ f) (hβγ : g' ≫ γ = β ≫ g)
    [QuasiIso (cokernel.desc f g w)] [QuasiIso (cokernel.desc f' g' w')] (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    MMP.ModuleCatComplex.quasiIsoConnecting f' g' w' i j hij ≫
        HomologicalComplex.homologyMap α j =
      HomologicalComplex.homologyMap γ i ≫
        MMP.ModuleCatComplex.quasiIsoConnecting f g w i j hij := by
  let c : cokernel f' ⟶ cokernel f := cokernel.map f' f α β hαβ
  let φ : ShortComplex.mk f' (cokernel.π f') (cokernel.condition f') ⟶
      ShortComplex.mk f (cokernel.π f) (cokernel.condition f) :=
    { τ₁ := α, τ₂ := β, τ₃ := c, comm₁₂ := hαβ.symm, comm₂₃ := by simp [c] }
  have hδ := HomologicalComplex.HomologySequence.δ_naturality φ
    (MMP.ModuleCatComplex.shortExact_cokernel f') (MMP.ModuleCatComplex.shortExact_cokernel f) i j hij
  have hc : c ≫ cokernel.desc f g w = cokernel.desc f' g' w' ≫ γ := by
    apply coequalizer.hom_ext
    simp [c, hβγ]
  have hH : HomologicalComplex.homologyMap c i ≫
      HomologicalComplex.homologyMap (cokernel.desc f g w) i =
      HomologicalComplex.homologyMap (cokernel.desc f' g' w') i ≫
        HomologicalComplex.homologyMap γ i := by
    rw [← HomologicalComplex.homologyMap_comp, hc, HomologicalComplex.homologyMap_comp]
  have hinv : inv (HomologicalComplex.homologyMap (cokernel.desc f' g' w') i) ≫
      HomologicalComplex.homologyMap c i = HomologicalComplex.homologyMap γ i ≫
      inv (HomologicalComplex.homologyMap (cokernel.desc f g w) i) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, ← hH, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  simp only [MMP.ModuleCatComplex.quasiIsoConnecting, Category.assoc]
  rw [hδ, ← Category.assoc, hinv, Category.assoc]

end Naturality

namespace borelMooreHomology'

open MMP.borelMooreHomology

variable (R : Type) [CommRing R] (M : ModuleCat.{0} R)
  {Y' Y : TopCat.{0}} [T2Space Y'] [T2Space Y] (f : Y' ⟶ Y) (hf : IsProperMap f)
  {X : Set Y} (hX : IsClosed X)

/-- The restriction `f⁻¹(X) → X` of `f`. -/
private def preimageMap : TopCat.of (f ⁻¹' X) ⟶ TopCat.of X :=
  TopCat.ofHom ⟨X.restrictPreimage f, f.hom.continuous.restrictPreimage⟩

include hf in
private lemma isProperMap_preimageMap : IsProperMap (preimageMap f (X := X)) :=
  hf.restrictPreimage X

/-- **Naturality of the Borel–Moore connecting map** for a proper map `f : Y' → Y` and a closed
`X ⊆ Y`: `(f|_{f⁻¹X})_* ∘ ∂' = ∂ ∘ (f|_{f⁻¹U})_*`. -/
private theorem connecting_naturality (hq : IsRelativeQuasiIso R M hX)
    (hq' : IsRelativeQuasiIso R M (hX.preimage f.hom.continuous)) (k : ℤ) :
    connecting R M (hX.preimage f.hom.continuous) hq' k ≫
        pushforward R M (preimageMap f (X := X)) (isProperMap_preimageMap f hf) k =
      pushforward R M (restrictPreimage f (complOpens hX))
          (isProperMap_restrictPreimage f _ hf) (k + 1) ≫ connecting R M hX hq k := by
  haveI : QuasiIso _ := hq
  haveI : QuasiIso _ := hq'
  refine quasiIsoConnecting_naturality (extIncl R M hX) (extRestrict R M hX) _
    (extIncl R M (hX.preimage f.hom.continuous)) (extRestrict R M (hX.preimage f.hom.continuous)) _
    (HomologicalComplex.extendMap (chainMap R M (preimageMap f (X := X))
      (isProperMap_preimageMap f hf)) ComplexShape.embeddingDownNat)
    (HomologicalComplex.extendMap (chainMap R M f hf) ComplexShape.embeddingDownNat)
    (HomologicalComplex.extendMap (chainMap R M (restrictPreimage f (complOpens hX))
      (isProperMap_restrictPreimage f _ hf)) ComplexShape.embeddingDownNat) ?_ ?_ _ _ _
  · rw [extIncl, extIncl, ← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
      ← chainMap_comp, ← chainMap_comp]
    rfl
  · rw [extRestrict, extRestrict, ← HomologicalComplex.extendMap_comp,
      chainMap_comp_restrictChainMap, HomologicalComplex.extendMap_comp]
    rfl

/-- A homeomorphism induces an injective push-forward. -/
private lemma pushforward_homeomorph_injective {Z Z' : TopCat.{0}} (e : Z ≃ₜ Z') (k : ℤ) :
    Function.Injective (pushforward R M (TopCat.ofHom ⟨e, e.continuous⟩) e.isProperMap k).hom := by
  have h : TopCat.ofHom ⟨e, e.continuous⟩ ≫ TopCat.ofHom ⟨e.symm, e.symm.continuous⟩ = 𝟙 Z :=
    TopCat.ext fun x ↦ e.symm_apply_apply x
  intro a b hab
  have key : ∀ c, (pushforward R M (TopCat.ofHom ⟨e.symm, e.symm.continuous⟩)
      e.symm.isProperMap k).hom
      ((pushforward R M (TopCat.ofHom ⟨e, e.continuous⟩) e.isProperMap k).hom c) = c := by
    intro c
    rw [← ModuleCat.comp_apply, ← pushforward_comp]
    simp only [h, pushforward_id]
    rfl
  rw [← key a, ← key b, hab]

/-- Push-forward along a homeomorphism followed by push-forward along its inverse. -/
private lemma pushforward_homeomorph_apply_symm {Z Z' : TopCat.{0}} (e : Z ≃ₜ Z') (k : ℤ)
    (c : borelMooreHomology R M Z' k) :
    (pushforward R M (TopCat.ofHom ⟨e, e.continuous⟩) e.isProperMap k).hom
      ((pushforward R M (TopCat.ofHom ⟨e.symm, e.symm.continuous⟩)
        e.symm.isProperMap k).hom c) = c := by
  have h : TopCat.ofHom ⟨e.symm, e.symm.continuous⟩ ≫ TopCat.ofHom ⟨e, e.continuous⟩ = 𝟙 Z' :=
    TopCat.ext fun x ↦ e.apply_symm_apply x
  rw [← ModuleCat.comp_apply, ← pushforward_comp]
  simp only [h, pushforward_id]
  rfl

end borelMooreHomology'

open MMP.Fourfold UnderlyingSpace

section Excision

open MMP.borelMooreHomology borelMooreHomology' Function

variable (R : Type) [CommRing R] (M : ModuleCat.{0} R)
  {ι : Type} [Fintype ι] [DecidableEq ι] {Y : TopCat.{0}} [T2Space Y]
  {X : ι → TopCat.{0}} [∀ Q, T2Space (X Q)] (j : ∀ Q, X Q ⟶ Y)
  (hj : ∀ Q, Topology.IsClosedEmbedding (j Q)) {XB : Set Y} (hXB : IsClosed XB)
  (hcov : ∀ y, ∃ Q, y ∈ Set.range (j Q))
  (hpair : ∀ Q R, Q ≠ R → Set.range (j Q) ∩ Set.range (j R) ⊆ XB)

include hcov hpair in
private lemma mem_range_iff_forall {Q : ι} {u : Y} (hu : u ∉ XB) :
    u ∈ Set.range (j Q) ↔ ∀ R, R ≠ Q → u ∉ Set.range (j R) := by
  constructor
  · intro hQ R hRQ hR
    exact hu (hpair Q R (Ne.symm hRQ) ⟨hQ, hR⟩)
  · intro h
    obtain ⟨R, hR⟩ := hcov u
    by_cases hRQ : R = Q
    · exact hRQ ▸ hR
    · exact absurd hR (h R hRQ)

include hj hcov hpair in
private lemma isOpen_piece (Q : ι) :
    IsOpen {u : complOpens hXB | u.1 ∈ Set.range (j Q)} := by
  have h : {u : complOpens hXB | u.1 ∈ Set.range (j Q)} =
      Subtype.val ⁻¹' (⋂ R ∈ (Finset.univ.erase Q : Finset ι), (Set.range (j R))ᶜ) := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_iInter, Finset.mem_erase,
      Finset.mem_univ, and_true, Set.mem_compl_iff]
    exact mem_range_iff_forall j hcov hpair u.2
  rw [h]
  refine IsOpen.preimage continuous_subtype_val ?_
  refine isOpen_biInter_finset fun R _ ↦ ?_
  exact (hj R).isClosed_range.isOpen_compl

/-- The piece `{u ∈ Y - X_B : u ∈ j_Q(X_Q)}` of the complement of the double locus. -/
private def piece (Q : ι) : TopologicalSpace.Opens (TopCat.of (complOpens hXB)) :=
  ⟨{u | u.1 ∈ Set.range (j Q)}, isOpen_piece j hj hXB hcov hpair Q⟩

include hpair in
private lemma pairwise_disjoint_piece :
    Pairwise (Disjoint on fun Q ↦ (piece j hj hXB hcov hpair Q : Set (complOpens hXB))) := by
  intro Q R hQR
  rw [Function.onFun, Set.disjoint_left]
  intro u hQ hR
  exact u.2 (hpair Q R hQR ⟨hQ, hR⟩)

private lemma mem_piece_cover (u : TopCat.of (complOpens hXB)) :
    ∃ Q, u ∈ piece j hj hXB hcov hpair Q :=
  hcov u.1

/-- The homeomorphism from `X_Q - j_Q⁻¹(X_B)` onto its piece. -/
private noncomputable def pieceHomeo (Q : ι) :
    (TopologicalSpace.Opens.comap (j Q).hom (complOpens hXB)) ≃ₜ
      (piece j hj hXB hcov hpair Q) := by
  let φ : (TopologicalSpace.Opens.comap (j Q).hom (complOpens hXB)) →
      (piece j hj hXB hcov hpair Q) := fun x ↦ ⟨⟨j Q x.1, x.2⟩, ⟨x.1, rfl⟩⟩
  have hφ : Topology.IsEmbedding φ := by
    have h1 : Topology.IsEmbedding (fun v : piece j hj hXB hcov hpair Q ↦ (v.1.1 : Y)) :=
      Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
    rw [← Topology.IsEmbedding.of_comp_iff h1]
    exact (hj Q).isEmbedding.comp Topology.IsEmbedding.subtypeVal
  refine hφ.toHomeomorphOfSurjective ?_
  rintro ⟨⟨u, hu⟩, ⟨x, hx⟩⟩
  refine ⟨⟨x, ?_⟩, ?_⟩
  · change j Q x ∈ complOpens hXB
    exact hx ▸ hu
  · exact Subtype.ext (Subtype.ext hx)

private lemma restrictPreimage_eq_pieceHomeo (Q : ι) :
    restrictPreimage (j Q) (complOpens hXB) =
      TopCat.ofHom ⟨pieceHomeo j hj hXB hcov hpair Q, 
          (pieceHomeo j hj hXB hcov hpair Q).continuous⟩ ≫
        clopenInclusion (piece j hj hXB hcov hpair Q) := by
  ext x
  rfl

private lemma pushforward_congr {Z Z' : TopCat.{0}} {f g : Z ⟶ Z'} (h : f = g) (hf : IsProperMap f)
    (hg : IsProperMap g) (k : ℤ) : pushforward R M f hf k = pushforward R M g hg k := by
  subst h; rfl

private lemma isClopen_piece (Q : ι) : IsClopen (piece j hj hXB hcov hpair Q : Set
    (complOpens hXB)) :=
  isClopen_of_disjoint_cover (Y := TopCat.of (complOpens hXB)) (piece j hj hXB hcov hpair)
    (pairwise_disjoint_piece j hj hXB hcov hpair) (mem_piece_cover j hj hXB hcov hpair) Q

private lemma isProperMap_clopenInclusion_piece (Q : ι) :
    IsProperMap (clopenInclusion (piece j hj hXB hcov hpair Q)) :=
  isProperMap_clopenInclusion (Y := TopCat.of (complOpens hXB)) (piece j hj hXB hcov hpair)
    (pairwise_disjoint_piece j hj hXB hcov hpair) (mem_piece_cover j hj hXB hcov hpair) Q

private lemma pushforward_restrictPreimage_eq (Q : ι) (k : ℤ) :
    pushforward R M (restrictPreimage (j Q) (complOpens hXB))
        (isProperMap_restrictPreimage (j Q) _ (hj Q).isProperMap) k =
      pushforward R M (TopCat.ofHom ⟨pieceHomeo j hj hXB hcov hpair Q,
          (pieceHomeo j hj hXB hcov hpair Q).continuous⟩)
          (pieceHomeo j hj hXB hcov hpair Q).isProperMap k ≫
        pushforward R M (clopenInclusion (piece j hj hXB hcov hpair Q))
          (isProperMap_clopenInclusion_piece j hj hXB hcov hpair Q) k := by
  rw [← pushforward_comp]
  exact pushforward_congr R M (restrictPreimage_eq_pieceHomeo j hj hXB hcov hpair Q) _ _ k

private lemma restrict_piece_pushforward_self (Q : ι) (k : ℤ) (a) :
    (restrict R M (piece j hj hXB hcov hpair Q) k).hom
      ((pushforward R M (restrictPreimage (j Q) (complOpens hXB))
        (isProperMap_restrictPreimage (j Q) _ (hj Q).isProperMap) k).hom a) =
      (pushforward R M (TopCat.ofHom ⟨pieceHomeo j hj hXB hcov hpair Q,
          (pieceHomeo j hj hXB hcov hpair Q).continuous⟩)
          (pieceHomeo j hj hXB hcov hpair Q).isProperMap k).hom a := by
  rw [pushforward_restrictPreimage_eq, ModuleCat.comp_apply, ← ModuleCat.comp_apply
    (pushforward R M (clopenInclusion _) _ k), pushforward_restrict_self R M _
    (isClopen_piece j hj hXB hcov hpair Q)]
  rfl

private lemma restrict_piece_pushforward_of_ne {P Q : ι} (hPQ : P ≠ Q) (k : ℤ) (a) :
    (restrict R M (piece j hj hXB hcov hpair Q) k).hom
      ((pushforward R M (restrictPreimage (j P) (complOpens hXB))
        (isProperMap_restrictPreimage (j P) _ (hj P).isProperMap) k).hom a) = 0 := by
  rw [pushforward_restrictPreimage_eq R M j hj hXB hcov hpair P, ModuleCat.comp_apply,
      ← ModuleCat.comp_apply
    (pushforward R M (clopenInclusion _) _ k), pushforward_restrict_of_disjoint R M _ _
    (isClopen_piece j hj hXB hcov hpair Q) (pairwise_disjoint_piece j hj hXB hcov hpair hPQ)]
  rfl

include hcov in
private lemma sum_pushforward_restrict_piece (k : ℤ)
    (u : borelMooreHomology R M (TopCat.of (complOpens hXB)) k) :
    ∑ Q, (pushforward R M (clopenInclusion (piece j hj hXB hcov hpair Q))
      (isProperMap_clopenInclusion_piece j hj hXB hcov hpair Q) k).hom
        ((restrict R M (piece j hj hXB hcov hpair Q) k).hom u) = u := by
  have h := congrArg (fun φ ↦ φ.hom u) (sum_restrict_pushforward R M
    (Y := TopCat.of (complOpens hXB)) (piece j hj hXB hcov hpair)
    (pairwise_disjoint_piece j hj hXB hcov hpair) (mem_piece_cover j hj hXB hcov hpair)
    (isProperMap_clopenInclusion_piece j hj hXB hcov hpair) k)
  simpa [ModuleCat.hom_sum, LinearMap.sum_apply] using h

private lemma restrict_piece_restrict_pushforward (P Q : ι) (k : ℤ)
    (a : borelMooreHomology R M (X P) k) :
    (restrict R M (piece j hj hXB hcov hpair Q) k).hom
      ((restrict R M (complOpens hXB) k).hom ((pushforward R M (j P) (hj P).isProperMap k).hom a)) =
      if h : P = Q then h ▸ (pushforward R M (TopCat.ofHom ⟨pieceHomeo j hj hXB hcov hpair P,
          (pieceHomeo j hj hXB hcov hpair P).continuous⟩)
          (pieceHomeo j hj hXB hcov hpair P).isProperMap k).hom
            ((restrict R M (TopologicalSpace.Opens.comap (j P).hom (complOpens hXB)) k).hom a)
      else 0 := by
  have e := restrict_pushforward_apply R M (j P) (hj P).isProperMap (complOpens hXB) k a
  erw [e]
  split_ifs with h
  · subst h
    exact restrict_piece_pushforward_self R M j hj hXB hcov hpair P k _
  · exact restrict_piece_pushforward_of_ne R M j hj hXB hcov hpair h k _

include hcov hpair in
/-- **Degree-three homology of a union of closed pieces with a double locus.** Let `Y` be the
union of the closed pieces `j_Q(X_Q)`, any two of which meet inside the closed set `X_B`, and let
`B_Q = j_Q⁻¹(X_B)`. Suppose the Borel–Moore long exact sequences of `(Y, X_B)` and `(X_Q, B_Q)`
exist, `H_3(X_B) = H_3(B_Q) = 0`, and no nonzero family `(w_Q) ∈ ∏_Q H_2(B_Q)` dies both in every
`H_2(X_Q)` and, summed, in `H_2(X_B)`. Then `∑_Q (j_Q)_* : ∏_Q H_3(X_Q) → H_3(Y)` is bijective. -/
private theorem bijective_sum_pushforward_of_forall_eq_zero
    (hq : IsRelativeQuasiIso R M hXB)
    (hqQ : ∀ Q, IsRelativeQuasiIso R M (hXB.preimage (j Q).hom.continuous))
    (h3 : ∀ a : borelMooreHomology R M (TopCat.of XB) ((2 : ℤ) + 1), a = 0)
    (h3Q : ∀ Q (a : borelMooreHomology R M (TopCat.of ((j Q) ⁻¹' XB)) ((2 : ℤ) + 1)), a = 0)
    (hcurve : ∀ w : ∀ Q, borelMooreHomology R M (TopCat.of ((j Q) ⁻¹' XB)) 2,
      (∀ Q, (pushforward R M (subspaceInclusion (X Q) ((j Q) ⁻¹' XB))
        (isProperMap_subspaceInclusion (hXB.preimage (j Q).hom.continuous)) 2).hom (w Q) = 0) →
      ∑ Q, (pushforward R M (preimageMap (j Q) (X := XB))
        (isProperMap_preimageMap (j Q) (hj Q).isProperMap) 2).hom (w Q) = 0 → w = 0) :
    Function.Bijective (∑ Q, (pushforward R M (j Q) (hj Q).isProperMap ((2 : ℤ) + 1)).hom ∘ₗ
      LinearMap.proj (R := R) (φ := fun Q ↦ borelMooreHomology R M (X Q) ((2 : ℤ) + 1)) Q) := by
  -- restriction to `X_Q - B_Q` is injective on `H_3(X_Q)`
  have hinjQ : ∀ Q (a : borelMooreHomology R M (X Q) ((2 : ℤ) + 1)),
      (restrict R M (TopologicalSpace.Opens.comap (j Q).hom (complOpens hXB))
          ((2 : ℤ) + 1)).hom a = 0 →
        a = 0 := by
    intro Q a ha
    obtain ⟨b, hb⟩ := (exact_pushforward_restrict (hqQ Q) ((2 : ℤ) + 1) a).1 ha
    rw [← hb, h3Q Q b, map_zero]
  have hinj : ∀ a : borelMooreHomology R M Y ((2 : ℤ) + 1),
      (restrict R M (complOpens hXB) ((2 : ℤ) + 1)).hom a = 0 → a = 0 := by
    intro a ha
    obtain ⟨b, hb⟩ := (exact_pushforward_restrict hq ((2 : ℤ) + 1) a).1 ha
    rw [← hb, h3 b, map_zero]
  have hcomp : ∀ (x : ∀ Q, borelMooreHomology R M (X Q) ((2 : ℤ) + 1)) Q,
      (restrict R M (piece j hj hXB hcov hpair Q) ((2 : ℤ) + 1)).hom
        ((restrict R M (complOpens hXB) ((2 : ℤ) + 1)).hom
          (∑ P, (borelMooreHomology.pushforward R M (j P) (hj P).isProperMap ((2 : ℤ) + 1)).hom
              (x P))) =
      (borelMooreHomology.pushforward R M (TopCat.ofHom ⟨pieceHomeo j hj hXB hcov hpair Q,
          (pieceHomeo j hj hXB hcov hpair Q).continuous⟩)
          (pieceHomeo j hj hXB hcov hpair Q).isProperMap ((2 : ℤ) + 1)).hom
            ((restrict R M (TopologicalSpace.Opens.comap (j Q).hom (complOpens hXB))
                ((2 : ℤ) + 1)).hom (x Q)) := by
    intro x Q
    rw [map_sum, map_sum, Finset.sum_eq_single Q]
    · rw [restrict_piece_restrict_pushforward, dif_pos rfl]
    · intro P _ hPQ
      rw [restrict_piece_restrict_pushforward, dif_neg hPQ]
    · exact fun h ↦ absurd (Finset.mem_univ Q) h
  have happly : ∀ x : ∀ Q, borelMooreHomology R M (X Q) ((2 : ℤ) + 1),
      (∑ Q, ⇑((borelMooreHomology.pushforward R M (j Q) (hj Q).isProperMap ((2 : ℤ) + 1)).hom ∘ₗ
        LinearMap.proj (R := R) (φ := fun Q ↦ borelMooreHomology R M (X Q) ((2 : ℤ) + 1)) Q)) x =
        ∑ P, (borelMooreHomology.pushforward R M (j P) (hj P).isProperMap ((2 : ℤ) + 1)).hom
            (x P) := by
    intro x
    simp [Finset.sum_apply]
  constructor
  · intro x x' hxx'
    rw [happly, happly] at hxx'
    have hx : ∑ P, (borelMooreHomology.pushforward R M (j P) (hj P).isProperMap ((2 : ℤ) + 1)).hom
        ((x - x') P) = 0 := by
      simp only [Pi.sub_apply, map_sub, Finset.sum_sub_distrib, hxx', sub_self]
    funext Q
    rw [← sub_eq_zero]
    have hinjE := pushforward_homeomorph_injective R M
      (Z := TopCat.of (TopologicalSpace.Opens.comap (j Q).hom (complOpens hXB)))
      (Z' := TopCat.of (piece j hj hXB hcov hpair Q)) (pieceHomeo j hj hXB hcov hpair Q)
      ((2 : ℤ) + 1)
    have key := hcomp (x - x') Q
    rw [hx, map_zero, map_zero] at key
    exact hinjQ Q _ (hinjE (key.symm.trans (map_zero _).symm))
  · intro y
    set u := (restrict R M (complOpens hXB) ((2 : ℤ) + 1)).hom y
    obtain ⟨uQ, huQdef⟩ : ∃ uQ : ∀ Q, borelMooreHomology R M
        (TopCat.of (TopologicalSpace.Opens.comap (j Q).hom (complOpens hXB))) ((2 : ℤ) + 1), ∀ Q,
            uQ Q =
      (borelMooreHomology.pushforward R M (TopCat.ofHom ⟨(pieceHomeo j hj hXB hcov hpair Q).symm,
          (pieceHomeo j hj hXB hcov hpair Q).symm.continuous⟩)
          (pieceHomeo j hj hXB hcov hpair Q).symm.isProperMap ((2 : ℤ) + 1)).hom
        ((restrict R M (piece j hj hXB hcov hpair Q) ((2 : ℤ) + 1)).hom u) := ⟨_, fun _ ↦ rfl⟩
    have huQ : ∀ Q, (borelMooreHomology.pushforward R M (restrictPreimage (j Q) (complOpens hXB))
        (isProperMap_restrictPreimage (j Q) _ (hj Q).isProperMap) ((2 : ℤ) + 1)).hom (uQ Q) =
        (borelMooreHomology.pushforward R M (clopenInclusion (piece j hj hXB hcov hpair Q))
          (isProperMap_clopenInclusion_piece j hj hXB hcov hpair Q) ((2 : ℤ) + 1)).hom
            ((restrict R M (piece j hj hXB hcov hpair Q) ((2 : ℤ) + 1)).hom u) := by
      intro Q
      have h := pushforward_homeomorph_apply_symm R M (Z := TopCat.of
        (TopologicalSpace.Opens.comap (j Q).hom (complOpens hXB)))
        (Z' := TopCat.of (piece j hj hXB hcov hpair Q)) (pieceHomeo j hj hXB hcov hpair Q)
        ((2 : ℤ) + 1) ((restrict R M (piece j hj hXB hcov hpair Q) ((2 : ℤ) + 1)).hom u)
      rw [pushforward_restrictPreimage_eq R M j hj hXB hcov hpair Q, ModuleCat.comp_apply,
        huQdef]
      exact congrArg _ h
    have hsum : ∑ Q, (borelMooreHomology.pushforward R M (restrictPreimage (j Q) (complOpens hXB))
        (isProperMap_restrictPreimage (j Q) _ (hj Q).isProperMap) ((2 : ℤ) + 1)).hom (uQ Q) =
          u := by
      simp only [huQ]
      exact sum_pushforward_restrict_piece R M j hj hXB hcov hpair _ u
    -- the connecting images vanish
    set w : ∀ Q, borelMooreHomology R M (TopCat.of ((j Q) ⁻¹' XB)) 2 := fun Q ↦
      (connecting R M (hXB.preimage (j Q).hom.continuous) (hqQ Q) 2).hom (uQ Q)
    have hw : w = 0 := by
      refine hcurve w (fun Q ↦ ?_) ?_
      · exact (exact_connecting_pushforward (hqQ Q) 2).apply_apply_eq_zero (uQ Q)
      · have hnat : ∀ Q, (borelMooreHomology.pushforward R M (preimageMap (j Q) (X := XB))
            (isProperMap_preimageMap (j Q) (hj Q).isProperMap) 2).hom (w Q) =
            (connecting R M hXB hq 2).hom ((borelMooreHomology.pushforward R M (restrictPreimage
                (j Q) (complOpens hXB))
              (isProperMap_restrictPreimage (j Q) _ (hj Q).isProperMap) ((2 : ℤ) + 1)).hom
                (uQ Q)) := by
          intro Q
          exact congrArg (fun φ ↦ φ.hom (uQ Q))
            (connecting_naturality R M (j Q) (hj Q).isProperMap hXB hq (hqQ Q) 2)
        rw [Finset.sum_congr rfl fun Q _ ↦ hnat Q, ← map_sum, hsum]
        exact (exact_restrict_connecting hq 2).apply_apply_eq_zero y
    have hext : ∀ Q, ∃ x : borelMooreHomology R M (X Q) ((2 : ℤ) + 1),
        (restrict R M (TopologicalSpace.Opens.comap (j Q).hom (complOpens hXB))
            ((2 : ℤ) + 1)).hom x = uQ Q := by
      intro Q
      have h0 : (connecting R M (hXB.preimage (j Q).hom.continuous) (hqQ Q) 2).hom (uQ Q) = 0 :=
        congrFun hw Q
      exact (exact_restrict_connecting (hqQ Q) 2 (uQ Q)).1 h0
    choose x hx using hext
    refine ⟨x, ?_⟩
    rw [happly]
    symm
    rw [← sub_eq_zero]
    apply hinj
    rw [map_sub, map_sum]
    have : ∀ Q, (restrict R M (complOpens hXB) ((2 : ℤ) + 1)).hom
        ((borelMooreHomology.pushforward R M (j Q) (hj Q).isProperMap ((2 : ℤ) + 1)).hom (x Q)) =
        (borelMooreHomology.pushforward R M (restrictPreimage (j Q) (complOpens hXB))
          (isProperMap_restrictPreimage (j Q) _ (hj Q).isProperMap) ((2 : ℤ) + 1)).hom (uQ Q) := by
      intro Q
      rw [← hx Q]
      exact restrict_pushforward_apply R M (j Q) (hj Q).isProperMap (complOpens hXB) _ (x Q)
    rw [Finset.sum_congr rfl fun Q _ ↦ this Q, hsum, sub_self]

end Excision

section Cycles

/-! ### Rational combinations of points and their cycle classes

A rational cycle of delta-dimension `k` on a complex scheme `X` is encoded by a finitely
supported function `β : X →₀ ℚ` supported on the points of delta-dimension `k` (Stacks' prime
cycles over `fieldChowSituation ℂ`, with rational coefficients); its class is
`∑ₓ β(x) cl_X(x) ∈ H_{2k}(X; ℚ)`. -/

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]

variable (X) in
/-- The points of delta-dimension `k` of a scheme over `ℂ`. -/
private abbrev dimPoints (k : ℕ) : Set X :=
  {x | Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
    (X ↘ Spec (.of ℂ)) x = k}

variable (X) in
/-- The class `∑ₓ β(x) cl_X(x) ∈ H_{2k}(X; ℚ)` of a rational combination of points. -/
private noncomputable abbrev pointsClass [IsComplexScheme X] (k : ℕ) :
    (X →₀ ℚ) →ₗ[ℚ] RationalHomology X (2 * k) :=
  Finsupp.linearCombination ℚ (Chow.pointCycleClassOrZero ℚ k)

/-- A closed immersion over `ℂ` preserves delta-dimensions. -/
private theorem relativeDimension_closedImmersion (f : Y ⟶ X) [IsClosedImmersion f]
    [f.IsOver (Spec (.of ℂ))] (y : Y) :
    Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (Y ↘ Spec (.of ℂ)) y =
      Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (X ↘ Spec (.of ℂ)) (f.base y) := by
  rw [← comp_over f (Spec (.of ℂ))]
  exact Stacks.Chow.relativeDimension_comp_closedImmersion _ f _ y

/-- Push-forward along a closed immersion maps combinations of points of delta-dimension `k` to
combinations of points of delta-dimension `k`. -/
private theorem mapDomain_mem_supported (f : Y ⟶ X) [IsClosedImmersion f]
    [f.IsOver (Spec (.of ℂ))] {k : ℕ} {β : Y →₀ ℚ}
    (hβ : β ∈ Finsupp.supported ℚ ℚ (dimPoints Y k)) :
    Finsupp.mapDomain f.base β ∈ Finsupp.supported ℚ ℚ (dimPoints X k) := by
  classical
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hx)
  change _ = _
  rw [← relativeDimension_closedImmersion f y]
  exact hβ hy

variable [IsComplexScheme X] [IsComplexScheme Y]

/-- **The class of points commutes with push-forward along a closed immersion.** -/
private theorem pushforward_pointsClass (f : Y ⟶ X) [IsClosedImmersion f]
    [f.IsOver (Spec (.of ℂ))] (k : ℕ) (β : Y →₀ ℚ) :
    (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (UnderlyingSpace.map
      (K := ℂ) f)) (UnderlyingSpace.isProperMap_map (K := ℂ) f) (2 * k : ℕ)).hom
        (pointsClass Y k β) = pointsClass X k (Finsupp.mapDomain f.base β) := by
  classical
  rw [Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply,
    Finsupp.linearCombination_apply, map_finsuppSum]
  refine Finsupp.sum_congr fun y _ ↦ ?_
  rw [map_smul, Function.comp_apply]
  congr 1
  by_cases hy : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (Y ↘ Spec (.of ℂ)) y = k
  · have h := Chow.pushforward_pointCycleClass ℚ f y hy
    rw [Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion, Nat.cast_one, one_smul] at h
    rw [Chow.pointCycleClassOrZero, dif_pos hy]
    exact h
  · have hx : ¬ Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (X ↘ Spec (.of ℂ)) (f.base y) = k := by
      rwa [← relativeDimension_closedImmersion f y]
    rw [Chow.pointCycleClassOrZero, dif_neg hy, Chow.pointCycleClassOrZero, dif_neg hx, map_zero]

end Cycles

section ComplexSchemes

variable {S Z : Scheme.{0}} [S.Over (Spec (.of ℂ))] [Z.Over (Spec (.of ℂ))]

/-- A scheme over `ℂ` with a closed immersion over `ℂ` into a complex scheme is a complex
scheme. -/
private theorem isComplexScheme_of_isClosedImmersion [IsComplexScheme S] (i : Z ⟶ S)
    [IsClosedImmersion i] [i.IsOver (Spec (.of ℂ))] : IsComplexScheme Z where
  toLocallyOfFiniteType := by
    rw [← comp_over (i) (Spec (.of ℂ))]
    infer_instance
  toQuasiCompact := by
    rw [← comp_over (i) (Spec (.of ℂ))]
    infer_instance
  exists_isClosedImmersion := by
    obtain ⟨V, _, _, j, hj, _⟩ := IsComplexScheme.exists_isClosedImmersion (X := S)
    exact ⟨V, inferInstance, inferInstance, i ≫ j, inferInstance, inferInstance⟩

/-- The relative quasi-isomorphism of the Borel–Moore long exact sequence holds for the
`ℂ`-points of a closed subscheme of a complex scheme. -/
private theorem isRelativeQuasiIso_range_map (R : Type) [CommRing R] (M : ModuleCat.{0} R)
    [IsComplexScheme S] (i : Z ⟶ S) [IsClosedImmersion i] [i.IsOver (Spec (.of ℂ))] :
    borelMooreHomology.IsRelativeQuasiIso R M (Y := TopCat.of (UnderlyingSpace ℂ S))
      (isClosed_range_map_of_isClosedImmersion i) := by
  obtain ⟨hYc, n, F, hF⟩ := hasBasis_contractible_and_exists_isClosedEmbedding S
  have : LocallyOfFiniteType (Z ↘ Spec (.of ℂ)) := by
    rw [← comp_over i (Spec (.of ℂ))]
    infer_instance
  have hi := isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) i
  let e : UnderlyingSpace ℂ Z ≃ₜ Set.range (map (K := ℂ) i) := hi.isEmbedding.toHomeomorph
  have hXc : HasOpenContractibleBasis (Set.range (map (K := ℂ) i)) :=
    (UnderlyingSpace.hasOpenContractibleBasis Z).of_homeomorph e
  exact borelMooreHomology.isRelativeQuasiIso_of_isClosedEmbedding R M (Y :=
    TopCat.of (UnderlyingSpace ℂ S)) hF (isClosed_range_map_of_isClosedImmersion i) hXc hYc

/-- The homeomorphism `Z(ℂ) ≃ i(Z(ℂ))` of a closed immersion. -/
private noncomputable def rangeHomeo (i : Z ⟶ S) [IsClosedImmersion i] [i.IsOver (Spec (.of ℂ))] :
    UnderlyingSpace ℂ Z ≃ₜ Set.range (map (K := ℂ) i) :=
  (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) i).isEmbedding.toHomeomorph

/-- Borel–Moore homology of `Z(ℂ)` above twice its dimension vanishes, read on `i(Z(ℂ))`. -/
private theorem eq_zero_of_dimension_le [IsComplexScheme S] (i : Z ⟶ S) [IsClosedImmersion i]
    [i.IsOver (Spec (.of ℂ))] {n : ℕ} (hZ : dimension Z ≤ n) {k : ℤ} (hk : 2 * (n : ℤ) < k)
    (a : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (Set.range (map (K := ℂ) i))) k) :
    a = 0 := by
  haveI := isComplexScheme_of_isClosedImmersion i
  have h0 := IsComplexScheme.isZero_borelMooreHomology_of_dimension_le (X := Z) ℚ hZ hk
  let e := rangeHomeo i
  have h := borelMooreHomology'.pushforward_homeomorph_apply_symm ℚ (ModuleCat.of ℚ ℚ)
    (Z := TopCat.of (UnderlyingSpace ℂ Z)) (Z' := TopCat.of (Set.range (map (K := ℂ) i))) e k a
  haveI := ModuleCat.subsingleton_of_isZero h0
  rw [← h, Subsingleton.elim ((borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom ⟨e.symm, e.symm.continuous⟩) e.symm.isProperMap k).hom a) 0, map_zero]

private theorem eq_zero_of_dimension_le' [IsComplexScheme S] (i : Z ⟶ S) [IsClosedImmersion i]
    [i.IsOver (Spec (.of ℂ))] {n : ℕ} (hZ : dimension Z ≤ n) {k : ℤ} (hk : 2 * (n : ℤ) < k)
    {T : Set (UnderlyingSpace ℂ S)} (hT : Set.range (map (K := ℂ) i) = T)
    (a : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of T) k) : a = 0 := by
  subst hT
  exact eq_zero_of_dimension_le i hZ hk a

private theorem mem_range_map_iff {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
    (i : X ⟶ Y) [IsClosedImmersion i] [i.IsOver (Spec (.of ℂ))] (p : UnderlyingSpace ℂ Y) :
    p ∈ Set.range (map (K := ℂ) i) ↔ p.toHom (IsLocalRing.closedPoint ℂ) ∈ Set.range i := by
  change p ∈ Set.range (mapFun (K := ℂ) i) ↔ _
  rw [range_mapFun_of_isClosedImmersion]
  rfl

end ComplexSchemes

section Reduction

open MMP.Mori

variable {R : Type} [CommRing R] {M : ModuleCat.{0} R}

private lemma isRelativeQuasiIso_congr {Y : TopCat.{0}} [T2Space Y] {X X' : Set Y} (hX : IsClosed X)
    (h : X = X') (hq : borelMooreHomology.IsRelativeQuasiIso R M hX) :
    borelMooreHomology.IsRelativeQuasiIso R M (h ▸ hX) := by
  subst h
  exact hq

/-- In a finite family of closed sets, the points lying in two distinct members form a closed
set. -/
theorem isClosed_setOf_exists_ne_mem_mem {X ι : Type*} [TopologicalSpace X] [Finite ι]
    {Z : ι → Set X} (hZ : ∀ i, IsClosed (Z i)) :
    IsClosed {x | ∃ i j, i ≠ j ∧ x ∈ Z i ∧ x ∈ Z j} := by
  have : {x | ∃ i j, i ≠ j ∧ x ∈ Z i ∧ x ∈ Z j} =
      ⋃ (p : ι × ι) (_ : p.1 ≠ p.2), Z p.1 ∩ Z p.2 := by
    ext x
    constructor
    · rintro ⟨i, j, h, h₁, h₂⟩
      exact Set.mem_iUnion₂.2 ⟨(i, j), h, h₁, h₂⟩
    · intro h
      obtain ⟨⟨i, j⟩, h, h₁, h₂⟩ := Set.mem_iUnion₂.1 h
      exact ⟨i, j, h, h₁, h₂⟩
  rw [this]
  exact isClosed_iUnion_of_finite fun p ↦ isClosed_iUnion_of_finite fun _ ↦
    (hZ p.1).inter (hZ p.2)

section Transfer

variable {E : Scheme.{0}} [E.Over (Spec (.of ℂ))] [IsComplexScheme E] {ι : Type} [Fintype ι]
  {EP : ι → Scheme.{0}} [∀ P, (EP P).Over (Spec (.of ℂ))] [∀ P, IsComplexScheme (EP P)]
  (j : ∀ P, EP P ⟶ E) [∀ P, IsClosedImmersion (j P)] [∀ P, (j P).IsOver (Spec (.of ℂ))]
  {B : Scheme.{0}} [B.Over (Spec (.of ℂ))] [IsComplexScheme B] (ιB : B ⟶ E)
  [IsClosedImmersion ιB] [ιB.IsOver (Spec (.of ℂ))]
  {BP : ι → Scheme.{0}} [∀ P, (BP P).Over (Spec (.of ℂ))] [∀ P, IsComplexScheme (BP P)]
  (ιBP : ∀ P, BP P ⟶ EP P) [∀ P, IsClosedImmersion (ιBP P)] [∀ P, (ιBP P).IsOver (Spec (.of ℂ))]
  (k : ∀ P, BP P ⟶ B) [∀ P, IsClosedImmersion (k P)] [∀ P, (k P).IsOver (Spec (.of ℂ))]

/-- The pushforward along `k_P` of the class read through the homeomorphism
`B_P(ℂ) ≃ j_P⁻¹(B(ℂ))`. -/
private theorem pushforward_preimageMap_eq (hk : ∀ P, k P ≫ ιB = ιBP P ≫ j P)
    (hrangeBP : ∀ P, Set.range (map (K := ℂ) (ιBP P)) =
      map (K := ℂ) (j P) ⁻¹' Set.range (map (K := ℂ) ιB)) (P : ι)
    (v : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ (BP P))) 2) :
    (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom ⟨rangeHomeo ιB,
      (rangeHomeo ιB).continuous⟩) (rangeHomeo ιB).isProperMap 2).hom
      ((borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (map (K := ℂ) (k P)))
        (UnderlyingSpace.isProperMap_map (K := ℂ) _) 2).hom v) =
    (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (borelMooreHomology'.preimageMap (TopCat.ofHom (map (K := ℂ) (j P))))
      (borelMooreHomology'.isProperMap_preimageMap _
        (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) (j P)).isProperMap) 2).hom
      ((borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom
        ⟨(rangeHomeo (ιBP P)).trans (Homeomorph.setCongr (hrangeBP P)),
        ((rangeHomeo (ιBP P)).trans (Homeomorph.setCongr (hrangeBP P))).continuous⟩)
        ((rangeHomeo (ιBP P)).trans (Homeomorph.setCongr (hrangeBP P))).isProperMap 2).hom v) := by
  rw [← ModuleCat.comp_apply, ← borelMooreHomology.pushforward_comp, ← ModuleCat.comp_apply,
    ← borelMooreHomology.pushforward_comp]
  have he : TopCat.ofHom (map (K := ℂ) (k P)) ≫ TopCat.ofHom ⟨rangeHomeo ιB,
      (rangeHomeo ιB).continuous⟩ = TopCat.ofHom
        ⟨(rangeHomeo (ιBP P)).trans (Homeomorph.setCongr (hrangeBP P)),
        ((rangeHomeo (ιBP P)).trans (Homeomorph.setCongr (hrangeBP P))).continuous⟩ ≫
      borelMooreHomology'.preimageMap (TopCat.ofHom (map (K := ℂ) (j P))) := by
    ext x
    change x.toHom ≫ k P ≫ ιB = x.toHom ≫ ιBP P ≫ j P
    rw [hk P]
  rw [pushforward_congr ℚ (ModuleCat.of ℚ ℚ) he]

/-- **Transfer of the curve condition** from rational curve cycles on the `B_P` to the
Borel–Moore classes on the subspaces `j_P⁻¹(B(ℂ)) ⊆ E_P(ℂ)`. -/
private theorem curveCondition_transfer (hk : ∀ P, k P ≫ ιB = ιBP P ≫ j P)
    (hrangeBP : ∀ P, Set.range (map (K := ℂ) (ιBP P)) =
      map (K := ℂ) (j P) ⁻¹' Set.range (map (K := ℂ) ιB))
    (hdimB : dimension B ≤ 1) (hdimBP : ∀ P, dimension (BP P) ≤ 1)
    (hcc : ∀ α : ∀ P, BP P →₀ ℚ, (∀ P, α P ∈ Finsupp.supported ℚ ℚ (dimPoints (BP P) 1)) →
      (∀ P, pointsClass (EP P) 1 (Finsupp.mapDomain (ιBP P).base (α P)) = 0) →
      ∑ P, Finsupp.mapDomain (k P).base (α P) = 0 → α = 0)
    (w : ∀ P, borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of ((TopCat.ofHom (map (K := ℂ) (j P))) ⁻¹' Set.range (map (K := ℂ) ιB))) 2)
    (hw1 : ∀ P, (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (subspaceInclusion (TopCat.of (UnderlyingSpace ℂ (EP P)))
        ((TopCat.ofHom (map (K := ℂ) (j P))) ⁻¹' Set.range (map (K := ℂ) ιB)))
      (borelMooreHomology.isProperMap_subspaceInclusion ((isClosed_range_map_of_isClosedImmersion
        ιB).preimage (TopCat.ofHom (map (K := ℂ) (j P))).hom.continuous)) 2).hom (w P) = 0)
    (hw2 : ∑ P, (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (borelMooreHomology'.preimageMap (TopCat.ofHom (map (K := ℂ) (j P))))
      (borelMooreHomology'.isProperMap_preimageMap _
        (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) (j P)).isProperMap) 2).hom (w P) = 0) :
    w = 0 := by
  let eQ : ∀ P, UnderlyingSpace ℂ (BP P) ≃ₜ
      ((TopCat.ofHom (map (K := ℂ) (j P))) ⁻¹' Set.range (map (K := ℂ) ιB)) := fun P ↦
    (rangeHomeo (ιBP P)).trans (Homeomorph.setCongr (hrangeBP P))
  obtain ⟨v, hv⟩ : ∃ v : ∀ P, borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of (UnderlyingSpace ℂ (BP P))) 2, ∀ P, v P =
      (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom ⟨(eQ P).symm,
        (eQ P).symm.continuous⟩) (eQ P).symm.isProperMap 2).hom (w P) := ⟨_, fun _ ↦ rfl⟩
  have hwv : ∀ P, w P = (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom ⟨eQ P, (eQ P).continuous⟩) (eQ P).isProperMap 2).hom (v P) := fun P ↦ by
    rw [hv P]
    exact (borelMooreHomology'.pushforward_homeomorph_apply_symm ℚ (ModuleCat.of ℚ ℚ)
      (Z := TopCat.of (UnderlyingSpace ℂ (BP P)))
      (Z' := TopCat.of ((TopCat.ofHom (map (K := ℂ) (j P))) ⁻¹' Set.range (map (K := ℂ) ιB)))
      (eQ P) 2 (w P)).symm
  have hv1 : ∀ P, (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (map (K := ℂ) (ιBP P)))
      (UnderlyingSpace.isProperMap_map (K := ℂ) _) 2).hom (v P) = 0 := by
    intro P
    have he : TopCat.ofHom (map (K := ℂ) (ιBP P)) =
        TopCat.ofHom ⟨eQ P, (eQ P).continuous⟩ ≫ subspaceInclusion _ _ := by
      ext x; rfl
    have hprop : IsProperMap (subspaceInclusion (TopCat.of (UnderlyingSpace ℂ (EP P)))
        ((TopCat.ofHom (map (K := ℂ) (j P))) ⁻¹' Set.range (map (K := ℂ) ιB))) :=
      borelMooreHomology.isProperMap_subspaceInclusion ((isClosed_range_map_of_isClosedImmersion
        ιB).preimage (TopCat.ofHom (map (K := ℂ) (j P))).hom.continuous)
    rw [pushforward_congr ℚ (ModuleCat.of ℚ ℚ) he _ (hprop.comp (eQ P).isProperMap),
      borelMooreHomology.pushforward_comp ℚ (ModuleCat.of ℚ ℚ) _ _ (eQ P).isProperMap hprop,
      ModuleCat.comp_apply, ← hwv P]
    exact hw1 P
  have hv2 : ∑ P, (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (map (K := ℂ) (k P)))
      (UnderlyingSpace.isProperMap_map (K := ℂ) _) 2).hom (v P) = 0 := by
    apply borelMooreHomology'.pushforward_homeomorph_injective ℚ (ModuleCat.of ℚ ℚ)
      (Z := TopCat.of (UnderlyingSpace ℂ B)) (Z' := TopCat.of (Set.range (map (K := ℂ) ιB)))
      (rangeHomeo ιB) 2
    rw [map_sum, map_zero, ← hw2]
    refine Finset.sum_congr rfl fun P _ ↦ ?_
    rw [pushforward_preimageMap_eq j ιB ιBP k hk hrangeBP P (v P), ← hwv P]
  choose α hαs hα using fun P ↦ Chow.exists_mem_supported_linearCombination_eq ℚ (hdimBP P) (v P)
  have hα0 : α = 0 := by
    refine hcc α hαs (fun P ↦ ?_) ?_
    · rw [← pushforward_pointsClass, hα P]
      exact hv1 P
    · refine Chow.eq_zero_of_linearCombination_pointCycleClassOrZero_eq_zero ℚ hdimB
        (Submodule.sum_mem _ fun P _ ↦ mapDomain_mem_supported (k P) (hαs P)) ?_
      rw [map_sum]
      simp only [← pushforward_pointsClass, hα]
      exact hv2
  funext P
  rw [hwv P, ← hα P, hα0, Pi.zero_apply, map_zero, map_zero, Pi.zero_apply]

end Transfer

/-- Every `ℂ`-point of the support `E` of a divisor lies on one of its components `E_P`. -/
theorem exists_mem_range_map_of_suppScheme {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    (D : Divisor W) (j : ∀ P : D.support, P.1.idealSheaf.subscheme ⟶ D.suppScheme)
    (hj : ∀ P, j P ≫ D.suppIdeal.subschemeι = P.1.idealSheaf.subschemeι)
    [∀ P, (j P).IsOver (Spec (.of ℂ))] [∀ P, IsClosedImmersion (j P)]
    (y : UnderlyingSpace ℂ D.suppScheme) :
    ∃ P : D.support, y ∈ Set.range (TopCat.ofHom (map (K := ℂ) (j P))) := by
  set e := y.toHom (IsLocalRing.closedPoint ℂ)
  have he : D.suppIdeal.subschemeι e ∈ (D.supp : Set W) := by
    rw [← DivisorWithCoeffs.coe_support_suppIdeal, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨e, rfl⟩
  rw [DivisorWithCoeffs.coe_supp, Set.mem_iUnion₂] at he
  obtain ⟨P, hP, hPe⟩ := he
  obtain ⟨a, ha⟩ : D.suppIdeal.subschemeι e ∈ Set.range (⟨P,
      hP⟩ : D.support).1.idealSheaf.subschemeι := by
    rwa [Scheme.IdealSheafData.range_subschemeι]
  refine ⟨⟨P, hP⟩, ?_⟩
  change y ∈ Set.range (map (K := ℂ) (j ⟨P, hP⟩))
  rw [mem_range_map_iff]
  refine ⟨a, D.suppIdeal.subschemeι.isClosedEmbedding.injective ?_⟩
  rw [← ha, ← hj ⟨P, hP⟩]
  rfl

/-- **Reduction to a condition on curve cycles.** For the inclusions `jᵢ : Eᵢ ⟶ E`, the map
`⨁ H_3(E_P) → H_3(E)` is bijective as soon as the double locus has dimension at most one and no
nonzero family of rational curve cycles `β_P` on the components, supported over the double
locus, has all classes `[β_P] = 0` in `H_2(E_P)` and push-forward sum `∑ β_P = 0` on `W`. -/
private theorem bijective_of_curveCondition {W : Scheme.{0}}
    [W.Over (Spec (.of ℂ))] [IsComplexScheme W] (D : Divisor W)
    (j : ∀ P : D.support, P.1.idealSheaf.subscheme ⟶ D.suppScheme)
    (hj : ∀ P, j P ≫ D.suppIdeal.subschemeι = P.1.idealSheaf.subschemeι)
    [∀ P, (j P).IsOver (Spec (.of ℂ))] [∀ P, IsProper (j P)]
    [∀ P : D.support, IsComplexScheme P.1.idealSheaf.subscheme]
    (hBW : topologicalKrullDim {x : W | ∃ P Q : D.support, P ≠ Q ∧ x ∈ P.1.support ∧
      x ∈ Q.1.support} ≤ 1)
    (hcc : ∀ β : ∀ P : D.support, P.1.idealSheaf.subscheme →₀ ℚ,
      (∀ P, ∀ x ∈ (β P).support, x ∈ dimPoints P.1.idealSheaf.subscheme 1 ∧
        ∃ Q : D.support, Q ≠ P ∧ P.1.idealSheaf.subschemeι x ∈ Q.1.support) →
      (∀ P, pointsClass P.1.idealSheaf.subscheme 1 (β P) = 0) →
      ∑ P, Finsupp.mapDomain P.1.idealSheaf.subschemeι.base (β P) = 0 → β = 0) :
    Function.Bijective (∑ P : D.support,
      (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (j P)))
        (UnderlyingSpace.isProperMap_map (K := ℂ) _) 3).hom ∘ₗ
        LinearMap.proj (R := ℚ)
          (φ := fun P : D.support => RationalHomology P.1.idealSheaf.subscheme 3) P) := by
  classical
  -- the support `E` and its components
  haveI : IsComplexScheme D.suppScheme :=
    isComplexScheme_of_isClosedImmersion D.suppIdeal.subschemeι
  haveI hjc : ∀ P, IsClosedImmersion (j P) := fun P ↦ by
    haveI : IsClosedImmersion (j P ≫ D.suppIdeal.subschemeι) := by rw [hj P]; infer_instance
    exact IsClosedImmersion.of_comp (j P) D.suppIdeal.subschemeι
  -- the double locus `B ⊆ E`
  let BsetE : Set D.suppScheme := {e | ∃ P Q : D.support, P ≠ Q ∧ e ∈ Set.range (j P) ∧
    e ∈ Set.range (j Q)}
  have hBsetE : IsClosed BsetE :=
    isClosed_setOf_exists_ne_mem_mem fun P ↦ (j P).isClosedEmbedding.isClosed_range
  let IB : D.suppScheme.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨BsetE, hBsetE⟩
  have hrangeB : Set.range IB.subschemeι = BsetE := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact Scheme.IdealSheafData.coe_support_vanishingIdeal _
  haveI : IsComplexScheme IB.subscheme := isComplexScheme_of_isClosedImmersion IB.subschemeι
  -- the double locus in `W`
  set BW : Set W := {x : W | ∃ P Q : D.support, P ≠ Q ∧ x ∈ P.1.support ∧ x ∈ Q.1.support}
    with hBW_def
  have hrangeP : ∀ P : D.support, Set.range P.1.idealSheaf.subschemeι = P.1.support := by
    intro P
    rw [Scheme.IdealSheafData.range_subschemeι]
  have hmemW : ∀ e ∈ BsetE, D.suppIdeal.subschemeι e ∈ BW := by
    rintro e ⟨P, Q, hPQ, ⟨a, rfl⟩, ⟨b, hb⟩⟩
    refine ⟨P, Q, hPQ, ?_, ?_⟩
    · rw [← hrangeP P, ← hj P]
      exact ⟨a, rfl⟩
    · rw [← hrangeP Q, ← hj Q, ← hb]
      exact ⟨b, rfl⟩
  have hdimB : dimension IB.subscheme ≤ 1 := by
    have hind : Topology.IsInducing (fun b : IB.subscheme ↦
        (⟨D.suppIdeal.subschemeι (IB.subschemeι b), hmemW _ (hrangeB ▸ ⟨b, rfl⟩)⟩ : BW)) :=
      ((D.suppIdeal.subschemeι.isClosedEmbedding.comp
        IB.subschemeι.isClosedEmbedding).isInducing).codRestrict _
    exact hind.topologicalKrullDim_le.trans hBW
  -- the preimages `B_P = j_P⁻¹(B)`
  let IBP : ∀ P : D.support, P.1.idealSheaf.subscheme.IdealSheafData := fun P ↦ IB.comap (j P)
  let k : ∀ P, (IBP P).subscheme ⟶ IB.subscheme := fun P ↦
    Scheme.IdealSheafData.subschemeMap (IBP P) IB (j P) (IB.le_map_comap (j P))
  have hk : ∀ P, k P ≫ IB.subschemeι = (IBP P).subschemeι ≫ j P := fun P ↦
    Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _
  haveI : ∀ P, (k P).IsOver (Spec (.of ℂ)) := fun P ↦ by
    constructor
    change k P ≫ (IB.subschemeι ≫ D.suppScheme ↘ Spec (.of ℂ)) =
      (IBP P).subschemeι ≫ P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)
    rw [← Category.assoc, hk P, Category.assoc, comp_over (j P)]
  haveI : ∀ P, IsClosedImmersion (k P) := fun P ↦ by
    haveI : IsClosedImmersion (k P ≫ IB.subschemeι) := by rw [hk P]; infer_instance
    exact IsClosedImmersion.of_comp (k P) IB.subschemeι
  haveI : ∀ P, IsComplexScheme (IBP P).subscheme := fun P ↦
    isComplexScheme_of_isClosedImmersion (IBP P).subschemeι
  have hsq : ∀ P, IsPullback (IBP P).subschemeι (k P) (j P) IB.subschemeι := fun P ↦
    isPullback_of_isClosedImmersion _ _ _ _ (hk P).symm (by
      rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι])
  have hrangeBP : ∀ P, Set.range (map (K := ℂ) (IBP P).subschemeι) =
      map (K := ℂ) (j P) ⁻¹' Set.range (map (K := ℂ) IB.subschemeι) := fun P ↦
    range_map_eq_preimage_of_isPullback (hsq P)
  have hmemBP : ∀ P (x : (IBP P).subscheme),
      P.1.idealSheaf.subschemeι ((IBP P).subschemeι x) ∈ BW := by
    intro P x
    have h1 : P.1.idealSheaf.subschemeι ((IBP P).subschemeι x) =
        D.suppIdeal.subschemeι (IB.subschemeι (k P x)) := by
      show ((IBP P).subschemeι ≫ P.1.idealSheaf.subschemeι) x =
        (k P ≫ IB.subschemeι ≫ D.suppIdeal.subschemeι) x
      rw [← hj P, ← Category.assoc, ← hk P, Category.assoc]
    rw [h1]
    exact hmemW _ (hrangeB ▸ ⟨_, rfl⟩)
  have hdimBP : ∀ P, dimension (IBP P).subscheme ≤ 1 := by
    intro P
    have hmem := hmemBP P
    have hind : Topology.IsInducing (fun x : (IBP P).subscheme ↦
        (⟨P.1.idealSheaf.subschemeι ((IBP P).subschemeι x), hmem x⟩ : BW)) :=
      ((P.1.idealSheaf.subschemeι.isClosedEmbedding.comp
        (IBP P).subschemeι.isClosedEmbedding).isInducing).codRestrict _
    exact hind.topologicalKrullDim_le.trans hBW
  -- the topological data
  have hpair : ∀ P Q : D.support, P ≠ Q →
      Set.range (TopCat.ofHom (map (K := ℂ) (j P))) ∩
        Set.range (TopCat.ofHom (map (K := ℂ) (j Q))) ⊆
        Set.range (map (K := ℂ) IB.subschemeι) := by
    rintro P Q hPQ y ⟨hyP, hyQ⟩
    change y ∈ Set.range (map (K := ℂ) (j P)) at hyP
    change y ∈ Set.range (map (K := ℂ) (j Q)) at hyQ
    rw [mem_range_map_iff] at hyP hyQ ⊢
    rw [hrangeB]
    exact ⟨P, Q, hPQ, hyP, hyQ⟩
  refine bijective_sum_pushforward_of_forall_eq_zero ℚ (ModuleCat.of ℚ ℚ)
    (X := fun P : D.support ↦ TopCat.of (UnderlyingSpace ℂ P.1.idealSheaf.subscheme))
    (Y := TopCat.of (UnderlyingSpace ℂ D.suppScheme))
    (fun P ↦ TopCat.ofHom (map (K := ℂ) (j P)))
    (fun P ↦ isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) (j P))
    (isClosed_range_map_of_isClosedImmersion IB.subschemeι)
    (exists_mem_range_map_of_suppScheme D j hj) hpair
    (isRelativeQuasiIso_range_map ℚ (ModuleCat.of ℚ ℚ) IB.subschemeι)
    (fun P ↦ isRelativeQuasiIso_congr _ (hrangeBP P)
      (isRelativeQuasiIso_range_map ℚ (ModuleCat.of ℚ ℚ) (IBP P).subschemeι))
    (eq_zero_of_dimension_le IB.subschemeι hdimB (by norm_num))
    (fun P ↦ eq_zero_of_dimension_le' (IBP P).subschemeι (hdimBP P) (by norm_num) (hrangeBP P))
    ?_
  -- the condition on curves
  intro w hw1 hw2
  refine curveCondition_transfer (fun P ↦ j P) IB.subschemeι (fun P ↦ (IBP P).subschemeι) k hk
    hrangeBP hdimB hdimBP ?_ w hw1 hw2
  intro α hαs hα1 hα2
  have hβ0 : (fun P ↦ Finsupp.mapDomain (IBP P).subschemeι.base (α P)) = 0 := by
    refine hcc _ (fun P x hx ↦ ⟨mapDomain_mem_supported _ (hαs P) hx, ?_⟩) hα1 ?_
    · obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hx)
      obtain ⟨P1, Q1, hPQ1, h1, h2⟩ := hmemBP P y
      by_cases hP1 : P1 = P
      · subst hP1
        exact ⟨Q1, Ne.symm hPQ1, h2⟩
      · exact ⟨P1, hP1, h1⟩
    · have hcomp : ∀ P, (IBP P).subschemeι ≫ P.1.idealSheaf.subschemeι =
          k P ≫ IB.subschemeι ≫ D.suppIdeal.subschemeι := fun P ↦ by
        rw [← hj P, ← Category.assoc, ← hk P, Category.assoc]
      have hmc : ∀ {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (γ : A →₀ ℚ),
          Finsupp.mapDomain g.base (Finsupp.mapDomain f.base γ) =
            Finsupp.mapDomain (f ≫ g).base γ := fun f g γ ↦ by
        rw [← Finsupp.mapDomain_comp]
        rfl
      calc ∑ P, Finsupp.mapDomain P.1.idealSheaf.subschemeι.base
            (Finsupp.mapDomain (IBP P).subschemeι.base (α P))
          = ∑ P, Finsupp.mapDomain (IB.subschemeι ≫ D.suppIdeal.subschemeι).base
              (Finsupp.mapDomain (k P).base (α P)) := by
            refine Finset.sum_congr rfl fun P _ ↦ ?_
            rw [hmc, hmc, hcomp P]
        _ = 0 := by rw [← Finsupp.mapDomain_finset_sum, hα2, Finsupp.mapDomain_zero]
  funext P
  exact Finsupp.mapDomain_injective (IBP P).subschemeι.isClosedEmbedding.injective
    ((congrFun hβ0 P).trans Finsupp.mapDomain_zero.symm)

end Reduction

section RegularParameters

open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {n : ℕ} {z : Fin n → R}

/-- The ideal generated by a subset of a regular system of parameters is prime. -/
private theorem isPrime_span_image_of_isRegularSystemOfParameters
    (hz : MMP.Mori.IsRegularSystemOfParameters z) (s : Finset (Fin n)) :
    (Ideal.span (z '' (s : Set (Fin n)))).IsPrime := by
  have := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
  obtain ⟨hreg, -, -⟩ := MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hz s
  have : IsDomain (R ⧸ Ideal.span (z '' (s : Set (Fin n)))) := IsRegularLocalRing.isDomain _
  exact (Ideal.Quotient.isDomain_iff_prime _).1 inferInstance

/-- A parameter outside a subset of a regular system of parameters is not in the ideal the
subset generates. -/
private theorem notMem_span_image_of_isRegularSystemOfParameters
    (hz : MMP.Mori.IsRegularSystemOfParameters z) {s : Finset (Fin n)} {i : Fin n} (hi : i ∉ s) :
    z i ∉ Ideal.span (z '' (s : Set (Fin n))) := by
  have := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
  intro hmem
  obtain ⟨hreg, -, hsop⟩ :=
    MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hz s
  have := hreg
  have hi' : i ∈ (sᶜ : Finset (Fin n)) := by simpa using hi
  obtain ⟨j, hj⟩ : ∃ j, (sᶜ).orderEmbOfFin rfl j = i := by
    rw [← Set.mem_range, Finset.range_orderEmbOfFin]
    exact hi'
  refine MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hsop j ?_
  simp only [hj]
  rwa [Ideal.Quotient.eq_zero_iff_mem]

end RegularParameters

section PointSNC

open MMP.Mori

variable {W : Scheme.{0}} (D : Divisor W)

open Classical in
/-- The components of `D` through `x`. -/
noncomputable def comps (x : W) : Finset D.support :=
    Finset.univ.filter fun P ↦ x ∈ P.1.support

variable {D}

/-- A component lies in `comps D x` exactly when its support contains `x`. -/
theorem mem_comps {x : W} {P : D.support} : P ∈ comps D x ↔ x ∈ P.1.support := by
  simp [comps]

variable {S : Scheme.{0}} {f : W ⟶ S} [IsLocallyNoetherian W]

/-- **Snc parameters at a point**, indexed by the components through the point. -/
private theorem exists_params (hsnc : D.IsSNC f) (x : W) :
    ∃ (n : ℕ) (z : Fin n → W.presheaf.stalk x) (j : comps D x → Fin n),
      IsRegularSystemOfParameters z ∧ Function.Injective j ∧
        ∀ P : comps D x, IdealSheafData.stalk P.1.1.idealSheaf x = Ideal.span {z (j P)} := by
  obtain ⟨n, z, j, hz, hj, hI⟩ := hsnc.2 x
  let e : comps D x → {E : MMP.Mori.PrimeDivisor W // E ∈ D.support ∧ x ∈ E.support} := fun P ↦
    ⟨P.1.1, P.1.2, mem_comps.1 P.2⟩
  refine ⟨n, z, j ∘ e, hz, ?_, fun P ↦ hI (e P)⟩
  intro P Q h
  exact Subtype.ext (Subtype.ext (congrArg
    (fun E : {E : MMP.Mori.PrimeDivisor W // E ∈ D.support ∧ x ∈ E.support} ↦ E.1) (hj h)))

/-- The number of components through a point is at most its coheight. -/
private theorem card_comps_le_coheight (hsnc : D.IsSNC f) (x : W) :
    ((comps D x).card : ℕ∞) ≤ Order.coheight x := by
  obtain ⟨n, z, j, hz, hj, -⟩ := exists_params hsnc x
  have hcard : (comps D x).card ≤ n := by
    simpa using Fintype.card_le_of_injective j hj
  have hn : (n : ℕ∞) = Order.coheight x := by
    have h1 := hz.2
    rw [ringKrullDim_stalk_eq_coheight] at h1
    exact_mod_cast h1.symm
  rw [← hn]
  exact_mod_cast hcard

/-- On a scheme of dimension `d`, `height x + coheight x ≤ d`. -/
private theorem height_add_coheight_le {d : ℕ} (hdim : topologicalKrullDim W = d) (x : W) :
    Order.height x + Order.coheight x ≤ d := by
  have hk : Order.krullDim W = d := by
    rw [← hdim, topologicalKrullDim]
    exact (Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints).symm
  have : Nonempty W := ⟨x⟩
  rw [Order.krullDim_eq_iSup_height_add_coheight_of_nonempty] at hk
  have h := le_iSup (fun a : W ↦ Order.height a + Order.coheight a) x
  have : ((⨆ a : W, Order.height a + Order.coheight a : ℕ∞) : WithBot ℕ∞) = (d : ℕ∞) := by
    exact_mod_cast hk
  have h2 : (⨆ a : W, Order.height a + Order.coheight a : ℕ∞) = d := by exact_mod_cast this
  rw [h2] at h
  exact h

open Classical in
/-- **The generization cut out by two components.** For two components `a ≠ b` of `D` through
`x`, the prime `I_{a,x} + I_{b,x}` of `𝒪_{W,x}` is the prime of a generization `η` of `x` whose
components are exactly `a` and `b`, and which generizes every generization of `x` on `a ∩ b`. -/
private theorem exists_pair_generization (hsnc : D.IsSNC f) (x : W) {a b : D.support}
    (ha : a ∈ comps D x) (hb : b ∈ comps D x) (hab : a ≠ b) :
    ∃ (η : W) (h : η ⤳ x),
      MMP.Intersection.primeOfSpecializes h =
        IdealSheafData.stalk a.1.idealSheaf x ⊔ IdealSheafData.stalk b.1.idealSheaf x ∧
      comps D η = {a, b} ∧
      ∀ y (hy : y ⤳ x), a ∈ comps D y → b ∈ comps D y → η ⤳ y := by
  classical
  obtain ⟨n, z, j, hz, hj, hI⟩ := exists_params hsnc x
  set sab : Finset (Fin n) := {j ⟨a, ha⟩, j ⟨b, hb⟩}
  have hq : Ideal.span (z '' (sab : Set (Fin n))) =
      IdealSheafData.stalk a.1.idealSheaf x ⊔ IdealSheafData.stalk b.1.idealSheaf x := by
    rw [hI ⟨a, ha⟩, hI ⟨b, hb⟩, Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq,
      Set.image_singleton, Ideal.span_insert]
  have hprime := isPrime_span_image_of_isRegularSystemOfParameters hz sab
  let P' : PrimeSpectrum (W.presheaf.stalk x) := ⟨_, hprime⟩
  set η := W.fromSpecStalk x P'
  have h : η ⤳ x := MMP.Resolution.specializes_fromSpecStalk x P'
  have hqη : MMP.Intersection.primeOfSpecializes h = Ideal.span (z '' (sab : Set (Fin n))) :=
    MMP.Resolution.primeOfSpecializes_fromSpecStalk x P' h
  refine ⟨η, h, hqη.trans hq, ?_, ?_⟩
  · ext P
    rw [mem_comps]
    constructor
    · intro hP
      have hPx : P ∈ comps D x := mem_comps.2 (h.mem_closed P.1.idealSheaf.support.isClosed hP)
      change η ∈ P.1.idealSheaf.support at hP
      rw [MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes _ h, hqη,
        hI ⟨P, hPx⟩, Ideal.span_singleton_le_iff_mem] at hP
      by_contra hne
      have hnot : j ⟨P, hPx⟩ ∉ sab := by
        simp only [sab, Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩
        · have := hj h'
          exact hne (by simp [show P = a from congrArg Subtype.val this])
        · have := hj h'
          exact hne (by simp [show P = b from congrArg Subtype.val this])
      exact notMem_span_image_of_isRegularSystemOfParameters hz hnot hP
    · intro hP
      change η ∈ P.1.idealSheaf.support
      rw [MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes _ h, hqη, hq]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hP
      rcases hP with rfl | rfl
      exacts [le_sup_left, le_sup_right]
  · intro y hy hay hby
    have hle : Ideal.span (z '' (sab : Set (Fin n))) ≤ MMP.Intersection.primeOfSpecializes hy := by
      rw [hq]
      refine sup_le ?_ ?_
      · exact (MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes _ hy).1
          (mem_comps.1 hay)
      · exact (MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes _ hy).1
          (mem_comps.1 hby)
    let Q' : PrimeSpectrum (W.presheaf.stalk x) :=
      ⟨MMP.Intersection.primeOfSpecializes hy, inferInstance⟩
    have hPQ : P' ⤳ Q' := (PrimeSpectrum.le_iff_specializes P' Q').1 hle
    have := hPQ.map (W.fromSpecStalk x).base.hom.continuous
    rwa [MMP.Intersection.fromSpecStalk_primeOfSpecializes hy] at this

private theorem enat_le_two_of_add_le {a b : ℕ∞} (h : a + b ≤ 3) (ha : 1 ≤ a) : b ≤ 2 := by
  induction a using ENat.recTopCoe with
  | top => simp at h
  | coe a =>
    induction b using ENat.recTopCoe with
    | top => simp at h
    | coe b =>
      norm_cast at h ha ⊢
      omega

private theorem enat_eq_zero_of_add_le {a b : ℕ∞} (h : a + b ≤ 3) (hb : 3 ≤ b) : a = 0 := by
  induction a using ENat.recTopCoe with
  | top => simp at h
  | coe a =>
    induction b using ENat.recTopCoe with
    | top => simp at h
    | coe b =>
      norm_cast at h hb ⊢
      omega

private theorem enat_le_one_of_add_le {a b : ℕ∞} (h : a + b ≤ 3) (hb : 2 ≤ b) : a ≤ 1 := by
  induction a using ENat.recTopCoe with
  | top => simp at h
  | coe a =>
    induction b using ENat.recTopCoe with
    | top => simp at h
    | coe b =>
      norm_cast at h hb ⊢
      omega

private theorem enat_eq_of_add_eq {a b c : ℕ∞} (e : a + c = b + 1) (hb : b + 1 ≤ 2) (hc : 1 ≤ c)
    (hba : b ≤ a) : a = b := by
  induction b using ENat.recTopCoe with
  | top => simp at hb
  | coe b =>
    have hne : ((b : ℕ∞) + 1) ≠ ⊤ := by
      rw [show ((b : ℕ∞) + 1) = ((b + 1 : ℕ) : ℕ∞) by push_cast; rfl]
      exact ENat.coe_ne_top _
    induction a using ENat.recTopCoe with
    | top => simp at e; exact absurd e.symm hne
    | coe a =>
      induction c using ENat.recTopCoe with
      | top => simp at e; exact absurd e.symm hne
      | coe c =>
        norm_cast at e hb hc hba ⊢
        omega

/-- In the specialization order of a scheme, a proper specialization is strictly smaller. -/
private theorem lt_of_specializes_of_ne {y x : W} (h : y ⤳ x) (hne : y ≠ x) : x < y :=
  lt_of_le_not_ge ((Scheme.le_iff_specializes).2 h) fun h' ↦
    hne (h.antisymm ((Scheme.le_iff_specializes).1 h')).eq

variable (D) in
/-- A *double curve* of `D`: a point of height one lying on at least two components. -/
def IsDoubleCurve (η : W) : Prop := Order.height η = 1 ∧ 2 ≤ (comps D η).card

variable (D) in
/-- A *triple point* of `D`: a point lying on exactly three components. -/
private def IsTriplePoint (t : W) : Prop := (comps D t).card = 3

/-- A double curve lies on exactly two components. -/
theorem IsDoubleCurve.card_comps (hsnc : D.IsSNC f) (hdim : topologicalKrullDim W = 3) {η : W}
    (h : IsDoubleCurve D η) : (comps D η).card = 2 := by
  have h1 := card_comps_le_coheight hsnc η
  have h2 := height_add_coheight_le hdim η
  have h3 : Order.coheight η ≤ 2 := enat_le_two_of_add_le (by exact_mod_cast h2) h.1.ge
  have : ((comps D η).card : ℕ∞) ≤ 2 := h1.trans h3
  have : (comps D η).card ≤ 2 := by exact_mod_cast this
  exact le_antisymm this h.2

/-- A triple point has height zero. -/
private theorem IsTriplePoint.height_eq_zero (hsnc : D.IsSNC f) (hdim : topologicalKrullDim W = 3)
    {t : W} (h : IsTriplePoint D t) : Order.height t = 0 := by
  have h1 := card_comps_le_coheight hsnc t
  have h2 := height_add_coheight_le hdim t
  rw [h] at h1
  exact enat_eq_zero_of_add_le (by exact_mod_cast h2) (by exact_mod_cast h1)

/-- Components pass to specializations. -/
private theorem comps_subset_of_specializes {y x : W} (h : y ⤳ x) : comps D y ⊆ comps D x := by
  intro P hP
  exact mem_comps.2 (h.mem_closed P.1.idealSheaf.support.isClosed (mem_comps.1 hP))

/-- Points with equal finite height in a specialization relation are equal. -/
private theorem eq_of_specializes_of_height_eq {y x : W} (h : y ⤳ x)
    (hh : Order.height x = Order.height y)
    (hfin : Order.height y ≠ ⊤) : y = x := by
  by_contra hne
  have hlt : x < y := lt_of_specializes_of_ne h hne
  have := Order.height_strictMono hlt (lt_top_iff_ne_top.2 (hh ▸ hfin))
  rw [hh] at this
  exact lt_irrefl _ this

open Classical in
/-- **The double curves through a triple point.** At a triple point `t`, each pair `a ≠ b` of
the three components through `t` meets along exactly one double curve through `t`. -/
private theorem existsUnique_doubleCurve (hsnc : D.IsSNC f) (hdim : topologicalKrullDim W
    = 3) {t : W}
    (ht : IsTriplePoint D t) {a b : D.support} (ha : a ∈ comps D t) (hb : b ∈ comps D t)
    (hab : a ≠ b) : ∃! η, (IsDoubleCurve D η ∧ η ⤳ t) ∧ comps D η = {a, b} := by
  obtain ⟨η, h, -, hcomps, hmax⟩ := exists_pair_generization hsnc t ha hb hab
  have hcard : (comps D η).card = 2 := by rw [hcomps, Finset.card_pair hab]
  have hne : η ≠ t := by
    rintro rfl
    rw [ht] at hcard
    exact absurd hcard (by norm_num)
  have hht := ht.height_eq_zero hsnc hdim
  have hlt : t < η := lt_of_specializes_of_ne h hne
  have hη1 : 1 ≤ Order.height η := by
    have := Order.height_strictMono hlt (by rw [hht]; exact WithTop.coe_lt_top 0)
    rw [hht] at this
    exact ENat.one_le_iff_ne_zero.2 (ne_of_gt (lt_of_le_of_lt zero_le this))
  have hη2 : Order.height η ≤ 1 := by
    have h1 := card_comps_le_coheight hsnc η
    have h2 := height_add_coheight_le hdim η
    rw [hcard] at h1
    exact enat_le_one_of_add_le (by exact_mod_cast h2) (by exact_mod_cast h1)
  have hdc : IsDoubleCurve D η := ⟨le_antisymm hη2 hη1, by rw [hcard]⟩
  refine ⟨η, ⟨⟨hdc, h⟩, hcomps⟩, ?_⟩
  rintro η' ⟨⟨hdc', h'⟩, hcomps'⟩
  have ha' : a ∈ comps D η' := by rw [hcomps']; simp
  have hb' : b ∈ comps D η' := by rw [hcomps']; simp
  have hηη' := hmax η' h' ha' hb'
  exact (eq_of_specializes_of_height_eq hηη' (by rw [hdc.1, hdc'.1])
    (by rw [hdc.1]; exact ENat.one_ne_top)).symm

/-- A point on two components has height at most one. -/
private theorem height_le_one_of_two_le (hsnc : D.IsSNC f) (hdim : topologicalKrullDim W
    = 3) {x : W}
    (hx : 2 ≤ (comps D x).card) : Order.height x ≤ 1 := by
  have h1 := card_comps_le_coheight hsnc x
  have h2 := height_add_coheight_le hdim x
  exact enat_le_one_of_add_le (by exact_mod_cast h2) (le_trans (by exact_mod_cast hx) h1)

/-- The points on two distinct components are the points of `comps` of cardinality `≥ 2`. -/
private theorem two_le_card_comps_iff {x : W} :
    2 ≤ (comps D x).card ↔ ∃ P Q : D.support, P ≠ Q ∧ x ∈ P.1.support ∧ x ∈ Q.1.support := by
  constructor
  · intro h
    obtain ⟨P, hP, Q, hQ, hPQ⟩ := Finset.one_lt_card.1 h
    exact ⟨P, Q, hPQ, mem_comps.1 hP, mem_comps.1 hQ⟩
  · rintro ⟨P, Q, hPQ, hP, hQ⟩
    exact Finset.one_lt_card.2 ⟨P, mem_comps.2 hP, Q, mem_comps.2 hQ, hPQ⟩

/-- A closed subset of a scheme all of whose points have height at most `n` has Krull dimension
at most `n`. -/
private theorem topologicalKrullDim_le_of_forall_height_le {B : Set W} (hB : IsClosed B)
    {n : ℕ∞} (h : ∀ x ∈ B, Order.height x ≤ n) : topologicalKrullDim B ≤ n := by
  let g : TopologicalSpace.IrreducibleCloseds B → W := fun Z ↦
    (Z.isIrreducible.image _ continuous_subtype_val.continuousOn).genericPoint
  have hg : ∀ Z : TopologicalSpace.IrreducibleCloseds B,
      closure ({g Z} : Set W) = Subtype.val '' (Z : Set B) := by
    intro Z
    have hcl : IsClosed (Subtype.val '' (Z : Set B)) :=
      hB.isClosedEmbedding_subtypeVal.isClosedMap _ Z.isClosed
    rw [(Z.isIrreducible.image _
        continuous_subtype_val.continuousOn).isGenericPoint_genericPoint_closure.def,
      hcl.closure_eq]
  have hgB : ∀ Z, g Z ∈ B := by
    intro Z
    have : g Z ∈ closure ({g Z} : Set W) := subset_closure rfl
    rw [hg Z] at this
    obtain ⟨y, -, hy⟩ := this
    exact hy ▸ y.2
  have hmono : StrictMono g := by
    intro Z Z' hZZ'
    have hsub : Subtype.val '' (Z : Set B) ⊆ Subtype.val '' (Z' : Set B) :=
      Set.image_mono hZZ'.le
    have hsp : g Z' ⤳ g Z := by
      rw [specializes_iff_mem_closure, hg Z']
      exact hsub (by rw [← hg Z]; exact subset_closure rfl)
    refine lt_of_specializes_of_ne hsp fun h ↦
      hZZ'.ne (TopologicalSpace.IrreducibleCloseds.ext ?_)
    exact Set.image_injective.2 Subtype.val_injective (by rw [← hg Z, ← hg Z', h])
  rw [topologicalKrullDim, Order.krullDim]
  refine iSup_le fun p ↦ ?_
  have hlen : (p.length : ℕ∞) ≤ Order.height (g p.last) := by
    simpa using Order.length_le_height (p := p.map g hmono) (x := g p.last) le_rfl
  exact_mod_cast hlen.trans (h _ (hgB p.last))

/-- **The double locus has dimension at most one.** -/
private theorem topologicalKrullDim_doubleLocus_le (hsnc : D.IsSNC f)
    (hdim : topologicalKrullDim W = 3) :
    topologicalKrullDim {x : W | ∃ P Q : D.support, P ≠ Q ∧ x ∈ P.1.support ∧
      x ∈ Q.1.support} ≤ 1 := by
  have := topologicalKrullDim_le_of_forall_height_le (n := 1)
    (isClosed_setOf_exists_ne_mem_mem fun P : D.support ↦ P.1.idealSheaf.support.isClosed)
    fun _ hx ↦ height_le_one_of_two_le hsnc hdim (two_le_card_comps_iff.2 hx)
  exact_mod_cast this

end PointSNC

section Algebra

open Finset

variable {ι 𝒟 𝒯 : Type*} [Fintype ι] [DecidableEq ι] [Fintype 𝒟] [DecidableEq 𝒟] [Fintype 𝒯]
  (m : ι → ℚ) (S : 𝒟 → Finset ι) (ST : 𝒯 → Finset ι) (inc : 𝒯 → 𝒟 → Prop) [DecidableRel inc]
  (β : ι → 𝒟 → ℚ) (δ : ι → 𝒟 → ℚ) (τ : ι → 𝒟 → 𝒟 → ℚ)

/-- The per-triple-point term of the weighted curve identity is nonpositive:
`m_P m_Q m_R (2ab/m_P - 2ac/m_Q + 2bc/m_R - a²m_R/(m_P m_Q) - b²m_Q/(m_P m_R)
- c²m_P/(m_Q m_R)) = -(a m_R - b m_Q + c m_P)²`. -/
private theorem triple_term_nonpos {mP mQ mR : ℚ} (hP : 0 < mP) (hQ : 0 < mQ) (hR : 0 < mR)
    (a b c : ℚ) :
    2 * a * b / mP - 2 * a * c / mQ + 2 * b * c / mR - a ^ 2 * mR / (mP * mQ)
      - b ^ 2 * mQ / (mP * mR) - c ^ 2 * mP / (mQ * mR) ≤ 0 := by
  have key : 2 * a * b / mP - 2 * a * c / mQ + 2 * b * c / mR - a ^ 2 * mR / (mP * mQ)
      - b ^ 2 * mQ / (mP * mR) - c ^ 2 * mP / (mQ * mR) =
      -(a * mR - b * mQ + c * mP) ^ 2 / (mP * mQ * mR) := by
    field_simp
    ring
  rw [key]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) (by positivity)

section WeightedCurveIdentity

variable {m S ST inc β δ τ}

omit [DecidableEq ι] [DecidableEq 𝒟] in
private theorem sum_inv_mul_tau_eq_zero (hβ0 : ∀ P η, P ∉ S η → β P η = 0)
    (hHZ : ∀ P η, P ∈ S η → ∑ η', β P η' * τ P η' η = 0) :
    ∑ P, ∑ η, ∑ η', (m P)⁻¹ * (β P η * β P η' * τ P η' η) = 0 := by
  classical
  refine Finset.sum_eq_zero fun P _ ↦ Finset.sum_eq_zero fun η _ ↦ ?_
  have : ∑ η', (m P)⁻¹ * (β P η * β P η' * τ P η' η) =
      (m P)⁻¹ * β P η * ∑ η', β P η' * τ P η' η := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun η' _ ↦ by ring
  rw [this]
  by_cases hP : P ∈ S η
  · rw [hHZ P η hP, mul_zero]
  · rw [hβ0 P η hP]
    ring

omit [Fintype ι] [Fintype 𝒟] in
private theorem inv_mul_mul_tau_eq (hβ0 : ∀ P η, P ∉ S η → β P η = 0)
    (hN2 : ∀ P η η', η ≠ η' → S η = S η' → P ∈ S η → τ P η' η = 0)
    (hN3 : ∀ P η η', S η ≠ S η' → P ∈ S η → P ∈ S η' →
      τ P η' η = (univ.filter fun t ↦ inc t η ∧ inc t η').card) (P : ι) (η η' : 𝒟) :
    (m P)⁻¹ * (β P η * β P η' * τ P η' η) =
      (if η = η' then (m P)⁻¹ * (β P η ^ 2 * τ P η η) else 0) +
      ∑ t, (if S η ≠ S η' ∧ inc t η ∧ inc t η' then (m P)⁻¹ * (β P η * β P η') else 0) := by
  by_cases he : η = η'
  · subst he
    simp [sq]
  rw [if_neg he, zero_add]
  by_cases hs : S η = S η'
  · simp only [hs, ne_eq, not_true_eq_false, false_and, if_false, Finset.sum_const_zero]
    by_cases hP : P ∈ S η
    · rw [hN2 P η η' he hs hP]
      ring
    · rw [hβ0 P η hP]
      ring
  have hsum : ∑ t, (if S η ≠ S η' ∧ inc t η ∧ inc t η' then
      (m P)⁻¹ * (β P η * β P η') else 0) =
      (m P)⁻¹ * (β P η * β P η') *
        ((univ.filter fun t ↦ inc t η ∧ inc t η').card : ℚ) := by
    rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    by_cases ht : inc t η ∧ inc t η'
    · simp [ht, hs]
    · simp [ht]
  rw [hsum]
  by_cases hP : P ∈ S η
  · by_cases hP' : P ∈ S η'
    · rw [hN3 P η η' hs hP hP']
      ring
    · rw [hβ0 P η' hP']
      ring
  · rw [hβ0 P η hP]
    ring

omit [Fintype 𝒟] [DecidableEq 𝒟] in
private theorem sum_inv_mul_sq_tau_eq (hm : ∀ P, 0 < m P) (hS : ∀ η, (S η).card = 2)
    (hβ0 : ∀ P η, P ∉ S η → β P η = 0)
    (hβanti : ∀ η P Q, P ≠ Q → S η = {P, Q} → β P η + β Q η = 0)
    (hN1 : ∀ η P Q, P ≠ Q → S η = {P, Q} → τ P η η = δ Q η)
    (hN4 : ∀ R η, R ∉ S η → δ R η = (univ.filter fun t ↦ inc t η ∧ R ∈ ST t).card) (η : 𝒟) :
    ∑ P, (m P)⁻¹ * (β P η ^ 2 * τ P η η) =
      (∑ P ∈ S η, β P η ^ 2) / (2 * ∏ P ∈ S η, m P) * ∑ R, m R * δ R η -
        ∑ t, (if inc t η then
          (∑ P ∈ S η, β P η ^ 2) / (2 * ∏ P ∈ S η, m P) * ∑ R ∈ ST t \ S η, m R else 0) := by
  set w := (∑ P ∈ S η, β P η ^ 2) / (2 * ∏ P ∈ S η, m P) with hw
  obtain ⟨P0, Q0, hne, hS0⟩ := Finset.card_eq_two.1 (hS η)
  have hcompl : ∑ R ∈ (S η)ᶜ, m R * δ R η =
      ∑ t, (if inc t η then ∑ R ∈ ST t \ S η, m R else 0) := by
    calc ∑ R ∈ (S η)ᶜ, m R * δ R η
        = ∑ R ∈ (S η)ᶜ, ∑ t, (if inc t η ∧ R ∈ ST t then m R else 0) := by
          refine Finset.sum_congr rfl fun R hR ↦ ?_
          rw [hN4 R η (Finset.mem_compl.1 hR), Finset.card_filter, Nat.cast_sum,
            Finset.mul_sum]
          refine Finset.sum_congr rfl fun t _ ↦ ?_
          split_ifs <;> simp
      _ = ∑ t, ∑ R ∈ (S η)ᶜ, (if inc t η ∧ R ∈ ST t then m R else 0) := Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun t _ ↦ ?_
          by_cases ht : inc t η
          · simp only [ht, true_and, if_true]
            rw [← Finset.sum_filter]
            congr 1
            ext R
            simp [Finset.mem_sdiff, and_comm]
          · simp [ht]
  have hDη : ∑ R, m R * δ R η = m P0 * δ P0 η + m Q0 * δ Q0 η +
      ∑ t, (if inc t η then ∑ R ∈ ST t \ S η, m R else 0) := by
    rw [← hcompl, ← Finset.sum_add_sum_compl (S η), hS0, Finset.sum_pair hne]
  have hGη : ∑ t, (if inc t η then w * ∑ R ∈ ST t \ S η, m R else 0) =
      w * ∑ t, (if inc t η then ∑ R ∈ ST t \ S η, m R else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    split_ifs <;> simp
  have hb : β Q0 η = - β P0 η := by linarith [hβanti η P0 Q0 hne hS0]
  have hwη : w = β P0 η ^ 2 / (m P0 * m Q0) := by
    simp only [hw, hS0, Finset.sum_pair hne, Finset.prod_pair hne, hb]
    have := hm P0
    have := hm Q0
    field_simp
    ring
  have hsupp : ∀ P ∈ (univ : Finset ι), P ∉ S η → (m P)⁻¹ * (β P η ^ 2 * τ P η η) = 0 := by
    intro P _ hP
    rw [hβ0 P η hP]
    ring
  rw [hGη, hDη, ← Finset.sum_subset (Finset.subset_univ (S η)) hsupp, hS0, Finset.sum_pair hne,
    hN1 η P0 Q0 hne hS0, hN1 η Q0 P0 hne.symm (by rw [hS0, Finset.pair_comm]), hwη, hb]
  have := hm P0
  have := hm Q0
  field_simp
  ring

omit [Fintype ι] [Fintype 𝒟] [Fintype 𝒯] [DecidableRel inc] in
private theorem inc_iff_mem_of_existsUnique (hS : ∀ η, (S η).card = 2)
    (hinc : ∀ t η, inc t η → S η ⊆ ST t) {t : 𝒯} {P Q R : ι} (hSTt : ST t = {P, Q, R})
    {η1 η2 η3 : 𝒟} (h1i : inc t η1) (h2i : inc t η2) (h3i : inc t η3)
    (h1u : ∀ η, inc t η ∧ S η = {P, Q} → η = η1) (h2u : ∀ η, inc t η ∧ S η = {P, R} → η = η2)
    (h3u : ∀ η, inc t η ∧ S η = {Q, R} → η = η3) (η : 𝒟) :
    inc t η ↔ η ∈ ({η1, η2, η3} : Finset 𝒟) := by
  constructor
  · intro hη
    have hsη : S η ⊆ {P, Q, R} := hSTt ▸ hinc t η hη
    obtain ⟨a, b, hab, hSab⟩ := Finset.card_eq_two.1 (hS η)
    have ha : a ∈ ({P, Q, R} : Finset ι) := hsη (by rw [hSab]; simp)
    have hb : b ∈ ({P, Q, R} : Finset ι) := hsη (by rw [hSab]; simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb ⊢
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · exact absurd rfl hab
    · exact Or.inl (h1u η ⟨hη, hSab⟩)
    · exact Or.inr (Or.inl (h2u η ⟨hη, hSab⟩))
    · exact Or.inl (h1u η ⟨hη, by rw [hSab, Finset.pair_comm]⟩)
    · exact absurd rfl hab
    · exact Or.inr (Or.inr (h3u η ⟨hη, hSab⟩))
    · exact Or.inr (Or.inl (h2u η ⟨hη, by rw [hSab, Finset.pair_comm]⟩))
    · exact Or.inr (Or.inr (h3u η ⟨hη, by rw [hSab, Finset.pair_comm]⟩))
    · exact absurd rfl hab
  · intro hη
    simp only [Finset.mem_insert, Finset.mem_singleton] at hη
    rcases hη with rfl | rfl | rfl
    exacts [h1i, h2i, h3i]

omit [Fintype ι] [Fintype 𝒯] in
private theorem sum_sum_ite_inc_eq {t : 𝒯} {η1 η2 η3 : 𝒟}
    (hincT : ∀ η, inc t η ↔ η ∈ ({η1, η2, η3} : Finset 𝒟))
    (h12 : S η1 ≠ S η2) (h13 : S η1 ≠ S η3) (h23 : S η2 ≠ S η3) (P' : ι) :
    ∑ η, ∑ η', (if S η ≠ S η' ∧ inc t η ∧ inc t η' then
      (m P')⁻¹ * (β P' η * β P' η') else 0) =
      (m P')⁻¹ * (2 * (β P' η1 * β P' η2) + 2 * (β P' η1 * β P' η3) +
        2 * (β P' η2 * β P' η3)) := by
  have hfil : univ.filter (inc t) = ({η1, η2, η3} : Finset 𝒟) := by
    ext η'
    simp [hincT η']
  have h1 : ∀ η, (∑ η', (if S η ≠ S η' ∧ inc t η ∧ inc t η' then
      (m P')⁻¹ * (β P' η * β P' η') else 0)) =
      if inc t η then ∑ η' ∈ ({η1, η2, η3} : Finset 𝒟),
        (if S η ≠ S η' then (m P')⁻¹ * (β P' η * β P' η') else 0) else 0 := by
    intro η
    by_cases hη : inc t η
    · rw [if_pos hη, ← Finset.sum_filter_add_sum_filter_not univ (inc t), hfil,
        Finset.sum_eq_zero (s := univ.filter fun η' ↦ ¬ inc t η')
          (fun η' hη' ↦ by simp [(Finset.mem_filter.1 hη').2]), add_zero]
      refine Finset.sum_congr rfl fun η' hη' ↦ ?_
      simp [hη, (hincT η').2 hη']
    · rw [if_neg hη]
      exact Finset.sum_eq_zero fun η' _ ↦ by simp [hη]
  simp_rw [h1]
  rw [← Finset.sum_filter, hfil]
  have hn1 : η1 ∉ ({η2, η3} : Finset 𝒟) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h ↦ h12 (congrArg S h), fun h ↦ h13 (congrArg S h)⟩
  have hn2 : η2 ∉ ({η3} : Finset 𝒟) := by
    simp only [Finset.mem_singleton]
    exact fun h ↦ h23 (congrArg S h)
  simp only [Finset.sum_insert hn1, Finset.sum_insert hn2, Finset.sum_singleton,
    ne_eq, not_true_eq_false, if_false, h12, h13, h23, Ne.symm h12, Ne.symm h13,
    Ne.symm h23, not_false_eq_true, if_true]
  ring

omit [Fintype ι] [Fintype 𝒟] [DecidableEq 𝒟] [Fintype 𝒯] in
private theorem ite_inc_weight_eq (hm : ∀ P, 0 < m P) {t : 𝒯} {η : 𝒟} {A B C : ι}
    (hη : inc t η) (hAB : A ≠ B) (hSη : S η = {A, B}) (hd : ST t \ S η = {C})
    (hβ : β B η = -β A η) :
    (if inc t η then (∑ P ∈ S η, β P η ^ 2) / (2 * ∏ P ∈ S η, m P) *
      ∑ R ∈ ST t \ S η, m R else 0) = β A η ^ 2 / (m A * m B) * m C := by
  rw [if_pos hη, hd, Finset.sum_singleton, hSη, Finset.sum_pair hAB, Finset.prod_pair hAB, hβ]
  have := hm A
  have := hm B
  field_simp
  ring

omit [Fintype 𝒯] in
private theorem triple_sum_eq (hβ0 : ∀ P η, P ∉ S η → β P η = 0)
    (hinc : ∀ t η, inc t η → S η ⊆ ST t) {t : 𝒯} {P Q R : ι} (hSTt : ST t = {P, Q, R})
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) {η1 η2 η3 : 𝒟}
    (h1i : inc t η1) (h2i : inc t η2) (h3i : inc t η3)
    (hincT : ∀ η, inc t η ↔ η ∈ ({η1, η2, η3} : Finset 𝒟))
    (h12 : S η1 ≠ S η2) (h13 : S η1 ≠ S η3) (h23 : S η2 ≠ S η3)
    (hβ1Q : β Q η1 = -β P η1) (hβ2R : β R η2 = -β P η2) (hβ3R : β R η3 = -β Q η3)
    (hβ1R : β R η1 = 0) (hβ2Q : β Q η2 = 0) (hβ3P : β P η3 = 0) :
    ∑ P', ∑ η, ∑ η', (if S η ≠ S η' ∧ inc t η ∧ inc t η' then
      (m P')⁻¹ * (β P' η * β P' η') else 0) =
      2 * β P η1 * β P η2 / m P - 2 * β P η1 * β Q η3 / m Q + 2 * β P η2 * β Q η3 / m R := by
  have hβout : ∀ P' η, P' ∉ ({P, Q, R} : Finset ι) → inc t η → β P' η = 0 :=
    fun P' η hP' hη ↦ hβ0 P' η fun h ↦ hP' (hSTt ▸ hinc t η hη h)
  simp_rw [sum_sum_ite_inc_eq hincT h12 h13 h23]
  rw [← Finset.sum_subset (Finset.subset_univ ({P, Q, R} : Finset ι)) (fun P' _ hP' ↦ by
    rw [hβout P' η1 hP' h1i, hβout P' η2 hP' h2i, hβout P' η3 hP' h3i]; ring)]
  rw [Finset.sum_insert (by simp [hPQ, hPR]), Finset.sum_insert (by simp [hQR]),
    Finset.sum_singleton, hβ1Q, hβ1R, hβ2Q, hβ2R, hβ3P, hβ3R]
  ring

omit [Fintype ι] [Fintype 𝒯] in
private theorem triple_weight_sum_eq (hm : ∀ P, 0 < m P) {t : 𝒯} {P Q R : ι}
    (hSTt : ST t = {P, Q, R}) (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) {η1 η2 η3 : 𝒟}
    (h1i : inc t η1) (h1S : S η1 = {P, Q}) (h2i : inc t η2) (h2S : S η2 = {P, R})
    (h3i : inc t η3) (h3S : S η3 = {Q, R})
    (hincT : ∀ η, inc t η ↔ η ∈ ({η1, η2, η3} : Finset 𝒟))
    (h12 : S η1 ≠ S η2) (h13 : S η1 ≠ S η3) (h23 : S η2 ≠ S η3)
    (hβ1Q : β Q η1 = -β P η1) (hβ2R : β R η2 = -β P η2) (hβ3R : β R η3 = -β Q η3) :
    ∑ η, (if inc t η then (∑ P ∈ S η, β P η ^ 2) / (2 * ∏ P ∈ S η, m P) *
      ∑ R ∈ ST t \ S η, m R else 0) =
      β P η1 ^ 2 * m R / (m P * m Q) + β P η2 ^ 2 * m Q / (m P * m R) +
        β Q η3 ^ 2 * m P / (m Q * m R) := by
  have hG0 : ∀ η ∈ (univ : Finset 𝒟), η ∉ ({η1, η2, η3} : Finset 𝒟) →
      (if inc t η then (∑ P ∈ S η, β P η ^ 2) / (2 * ∏ P ∈ S η, m P) *
        ∑ R ∈ ST t \ S η, m R else 0) = 0 :=
    fun η _ hη ↦ if_neg fun h ↦ hη ((hincT η).1 h)
  have hn1 : η1 ∉ ({η2, η3} : Finset 𝒟) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h ↦ h12 (congrArg S h), fun h ↦ h13 (congrArg S h)⟩
  have hn2 : η2 ∉ ({η3} : Finset 𝒟) := by
    simp only [Finset.mem_singleton]
    exact fun h ↦ h23 (congrArg S h)
  have hd1 : ST t \ S η1 = {R} := by
    rw [hSTt, h1S]
    ext
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    grind
  have hd2 : ST t \ S η2 = {Q} := by
    rw [hSTt, h2S]
    ext
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    grind
  have hd3 : ST t \ S η3 = {P} := by
    rw [hSTt, h3S]
    ext
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    grind
  rw [← Finset.sum_subset (Finset.subset_univ _) hG0, Finset.sum_insert hn1,
    Finset.sum_insert hn2, Finset.sum_singleton, ite_inc_weight_eq hm h1i hPQ h1S hd1 hβ1Q,
    ite_inc_weight_eq hm h2i hPR h2S hd2 hβ2R, ite_inc_weight_eq hm h3i hQR h3S hd3 hβ3R]
  have := hm P
  have := hm Q
  have := hm R
  field_simp
  ring

omit [Fintype 𝒯] [DecidableEq 𝒟] in
private theorem triple_sum_sub_weight_sum_nonpos (hm : ∀ P, 0 < m P)
    (hS : ∀ η, (S η).card = 2) (hST : ∀ t, (ST t).card = 3)
    (hinc : ∀ t η, inc t η → S η ⊆ ST t)
    (huniq : ∀ t (s : Finset ι), s ⊆ ST t → s.card = 2 → ∃! η, inc t η ∧ S η = s)
    (hβ0 : ∀ P η, P ∉ S η → β P η = 0)
    (hβanti : ∀ η P Q, P ≠ Q → S η = {P, Q} → β P η + β Q η = 0) (t : 𝒯) :
    ∑ P, ∑ η, ∑ η', (if S η ≠ S η' ∧ inc t η ∧ inc t η' then
      (m P)⁻¹ * (β P η * β P η') else 0) -
      ∑ η, (if inc t η then (∑ P ∈ S η, β P η ^ 2) / (2 * ∏ P ∈ S η, m P) *
        ∑ R ∈ ST t \ S η, m R else 0) ≤ 0 := by
  classical
  obtain ⟨P, Q, R, hPQ, hPR, hQR, hSTt⟩ := Finset.card_eq_three.1 (hST t)
  have hsub : ∀ a b, a ∈ ({P, Q, R} : Finset ι) → b ∈ ({P, Q, R} : Finset ι) →
      ({a, b} : Finset ι) ⊆ ST t := by
    intro a b ha hb
    rw [hSTt]
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact ha
    · rw [Finset.mem_singleton.1 hx]
      exact hb
  obtain ⟨η1, ⟨h1i, h1S⟩, h1u⟩ := huniq t {P, Q} (hsub P Q (by simp) (by simp))
    (Finset.card_pair hPQ)
  obtain ⟨η2, ⟨h2i, h2S⟩, h2u⟩ := huniq t {P, R} (hsub P R (by simp) (by simp))
    (Finset.card_pair hPR)
  obtain ⟨η3, ⟨h3i, h3S⟩, h3u⟩ := huniq t {Q, R} (hsub Q R (by simp) (by simp))
    (Finset.card_pair hQR)
  have h12 : S η1 ≠ S η2 := by
    rw [h1S, h2S]; intro h
    have : Q ∈ ({P, R} : Finset ι) := h ▸ (by simp)
    simp [hPQ.symm, hQR] at this
  have h13 : S η1 ≠ S η3 := by
    rw [h1S, h3S]; intro h
    have : P ∈ ({Q, R} : Finset ι) := h ▸ (by simp)
    simp [hPQ, hPR] at this
  have h23 : S η2 ≠ S η3 := by
    rw [h2S, h3S]; intro h
    have : P ∈ ({Q, R} : Finset ι) := h ▸ (by simp)
    simp [hPQ, hPR] at this
  have hincT := inc_iff_mem_of_existsUnique hS hinc hSTt h1i h2i h3i h1u h2u h3u
  have hβ1Q : β Q η1 = -β P η1 := by linarith [hβanti η1 P Q hPQ h1S]
  have hβ2R : β R η2 = -β P η2 := by linarith [hβanti η2 P R hPR h2S]
  have hβ3R : β R η3 = -β Q η3 := by linarith [hβanti η3 Q R hQR h3S]
  rw [triple_sum_eq hβ0 hinc hSTt hPQ hPR hQR h1i h2i h3i hincT h12 h13 h23 hβ1Q hβ2R hβ3R
      (hβ0 R η1 (by rw [h1S]; simp [hPR.symm, hQR.symm]))
      (hβ0 Q η2 (by rw [h2S]; simp [hPQ.symm, hQR])) (hβ0 P η3 (by rw [h3S]; simp [hPQ, hPR])),
    triple_weight_sum_eq hm hSTt hPQ hPR hQR h1i h1S h2i h2S h3i h3S hincT h12 h13 h23 hβ1Q hβ2R
      hβ3R]
  linarith [triple_term_nonpos (hm P) (hm Q) (hm R) (β P η1) (β P η2) (β Q η3)]

end WeightedCurveIdentity

include m S ST inc β δ τ in
/-- **The weighted curve identity, combinatorial form.** Components `P` with weights `m_P > 0`,
double curves `η` lying on exactly two components `S η`, and triple points `t` lying on exactly
three components `ST t`, each pair of which meets in exactly one double curve through `t`. Let
`β_P(η)` be opposite on the two components of each double curve, `τ_P(η', η)` the intersection
numbers of double curves on the component `P` and `δ_R(η)` the degree of `E_R` on `η`, subject
to the incidence relations of an snc divisor. If `∑_η' β_P(η') τ_P(η', η) = 0` for all
`P ∈ S η` and `∑_R m_R δ_R(η) < 0` for all `η`, then `β = 0`. -/
private theorem eq_zero_of_weighted_curve_identity (hm : ∀ P, 0 < m P)
    (hS : ∀ η, (S η).card = 2) (hST : ∀ t, (ST t).card = 3)
    (hinc : ∀ t η, inc t η → S η ⊆ ST t)
    (huniq : ∀ t (s : Finset ι), s ⊆ ST t → s.card = 2 → ∃! η, inc t η ∧ S η = s)
    (hβ0 : ∀ P η, P ∉ S η → β P η = 0)
    (hβanti : ∀ η P Q, P ≠ Q → S η = {P, Q} → β P η + β Q η = 0)
    (hN1 : ∀ η P Q, P ≠ Q → S η = {P, Q} → τ P η η = δ Q η)
    (hN2 : ∀ P η η', η ≠ η' → S η = S η' → P ∈ S η → τ P η' η = 0)
    (hN3 : ∀ P η η', S η ≠ S η' → P ∈ S η → P ∈ S η' →
      τ P η' η = (univ.filter fun t ↦ inc t η ∧ inc t η').card)
    (hN4 : ∀ R η, R ∉ S η → δ R η = (univ.filter fun t ↦ inc t η ∧ R ∈ ST t).card)
    (hN5 : ∀ η, ∑ R, m R * δ R η < 0)
    (hHZ : ∀ P η, P ∈ S η → ∑ η', β P η' * τ P η' η = 0) :
    β = 0 := by
  classical
  set w : 𝒟 → ℚ := fun η ↦ (∑ P ∈ S η, β P η ^ 2) / (2 * ∏ P ∈ S η, m P) with hw
  set D : 𝒟 → ℚ := fun η ↦ ∑ R, m R * δ R η
  set G : 𝒯 → 𝒟 → ℚ := fun t η ↦ if inc t η then w η * ∑ R ∈ ST t \ S η, m R else 0
  set F : 𝒯 → ℚ := fun t ↦ ∑ P, ∑ η, ∑ η',
    (if S η ≠ S η' ∧ inc t η ∧ inc t η' then (m P)⁻¹ * (β P η * β P η') else 0) with hF
  have hT : ∑ P, ∑ η, ∑ η', (m P)⁻¹ * (β P η * β P η' * τ P η' η) =
      ∑ η, ∑ P, (m P)⁻¹ * (β P η ^ 2 * τ P η η) + ∑ t, F t := by
    simp_rw [inv_mul_mul_tau_eq hβ0 hN2 hN3, Finset.sum_add_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    congr 1
    · exact Finset.sum_comm
    · simp only [hF]
      conv_lhs => enter [2, P, 2, η]; rw [Finset.sum_comm]
      conv_lhs => enter [2, P]; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
  have hdiag : ∀ η, ∑ P, (m P)⁻¹ * (β P η ^ 2 * τ P η η) = w η * D η - ∑ t, G t η :=
    sum_inv_mul_sq_tau_eq hm hS hβ0 hβanti hN1 hN4
  have htriple : ∀ t, F t - ∑ η, G t η ≤ 0 :=
    triple_sum_sub_weight_sum_nonpos hm hS hST hinc huniq hβ0 hβanti
  have hwnn : ∀ η, 0 ≤ w η := fun η ↦ by
    apply div_nonneg
    · exact Finset.sum_nonneg fun P _ ↦ sq_nonneg _
    · have := Finset.prod_pos fun P (_ : P ∈ S η) ↦ hm P
      positivity
  have hsum0 : ∑ η, w η * D η + ∑ t, (F t - ∑ η, G t η) = 0 := by
    rw [← sum_inv_mul_tau_eq_zero hβ0 hHZ, hT]
    simp_rw [hdiag, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun t η ↦ G t η)]
    ring
  have hle : ∀ η, w η * D η ≤ 0 := fun η ↦
    mul_nonpos_of_nonneg_of_nonpos (hwnn η) (hN5 η).le
  have hall : ∀ η, w η * D η = 0 := by
    have h1 : ∑ t, (F t - ∑ η, G t η) ≤ 0 := Finset.sum_nonpos fun t _ ↦ htriple t
    have h2 : ∑ η, w η * D η ≤ 0 := Finset.sum_nonpos fun η _ ↦ hle η
    exact fun η ↦ (Finset.sum_eq_zero_iff_of_nonpos fun η _ ↦ hle η).1 (by linarith) η
      (Finset.mem_univ _)
  funext P η
  by_cases hP : P ∈ S η
  · have hw0 : w η = 0 := (mul_eq_zero.1 (hall η)).resolve_right (hN5 η).ne
    have hnum : ∑ P ∈ S η, β P η ^ 2 = 0 := by
      have hprod := Finset.prod_pos fun P (_ : P ∈ S η) ↦ hm P
      rw [hw, div_eq_zero_iff] at hw0
      exact hw0.resolve_right (by positivity)
    simpa using (Finset.sum_eq_zero_iff_of_nonneg fun P _ ↦ sq_nonneg (β P η)).1 hnum P hP
  · exact hβ0 P η hP

include m S ST inc in
/-- Double counting of triple points on a double curve: the triple points `t` on `η` lying on a
component `R ∉ S η` are counted once by the curves `η'` of type `{P, R}` through them. -/
private theorem sum_card_filter_inc_eq (hinc : ∀ t η, inc t η → S η ⊆ ST t)
    (huniq : ∀ t (s : Finset ι), s ⊆ ST t → s.card = 2 → ∃! η, inc t η ∧ S η = s)
    {P R : ι} {η : 𝒟} (hP : P ∈ S η) (hRP : R ≠ P) :
    ∑ η' ∈ univ.filter (fun η' ↦ S η' = {P, R}),
        (univ.filter fun t ↦ inc t η ∧ inc t η').card =
      (univ.filter fun t ↦ inc t η ∧ R ∈ ST t).card := by
  classical
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  by_cases ht : inc t η ∧ R ∈ ST t
  · rw [if_pos ht]
    have hsub : ({P, R} : Finset ι) ⊆ ST t := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hinc t η ht.1 hP
      · exact ht.2
    obtain ⟨η', ⟨h1, h2⟩, h3⟩ := huniq t {P, R} hsub (Finset.card_pair (Ne.symm hRP))
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
    rw [Finset.card_eq_one]
    refine ⟨η', Finset.ext fun η'' ↦ ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hS'', -, hi⟩
      exact h3 η'' ⟨hi, hS''⟩
    · rintro rfl
      exact ⟨h2, ht.1, h1⟩
  · rw [if_neg ht]
    refine Finset.sum_eq_zero fun η' hη' ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hη'
    rw [if_neg]
    rintro ⟨h1, h2⟩
    apply ht
    refine ⟨h1, hinc t η' h2 ?_⟩
    rw [hη']
    simp

include m S ST inc β δ τ in
/-- **The weighted curve identity, with the degrees given componentwise**: as
`eq_zero_of_weighted_curve_identity`, with the degree `δ_R(η)` of `E_R` on a double curve `η`
on the component `P` given by the intersections on `P` with the curves of type `{P, R}`. -/
private theorem eq_zero_of_weighted_curve_identity' (hm : ∀ P, 0 < m P)
    (hS : ∀ η, (S η).card = 2) (hST : ∀ t, (ST t).card = 3)
    (hinc : ∀ t η, inc t η → S η ⊆ ST t)
    (huniq : ∀ t (s : Finset ι), s ⊆ ST t → s.card = 2 → ∃! η, inc t η ∧ S η = s)
    (hβ0 : ∀ P η, P ∉ S η → β P η = 0)
    (hβanti : ∀ η P Q, P ≠ Q → S η = {P, Q} → β P η + β Q η = 0)
    (hN2 : ∀ P η η', η ≠ η' → S η = S η' → P ∈ S η → τ P η' η = 0)
    (hN3 : ∀ P η η', S η ≠ S η' → P ∈ S η → P ∈ S η' →
      τ P η' η = (univ.filter fun t ↦ inc t η ∧ inc t η').card)
    (hN14 : ∀ P R η, P ∈ S η → R ≠ P →
      δ R η = ∑ η' ∈ univ.filter (fun η' ↦ S η' = {P, R}), τ P η' η)
    (hN5 : ∀ η, ∑ R, m R * δ R η < 0)
    (hHZ : ∀ P η, P ∈ S η → ∑ η', β P η' * τ P η' η = 0) :
    β = 0 := by
  classical
  refine eq_zero_of_weighted_curve_identity m S ST inc β δ τ hm hS hST hinc huniq hβ0 hβanti
    ?_ hN2 hN3 ?_ hN5 hHZ
  · intro η P Q hPQ hS'
    have hP : P ∈ S η := by rw [hS']; simp
    rw [hN14 P Q η hP (Ne.symm hPQ), Finset.sum_eq_single η]
    · intro η' hη' hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hη'
      exact hN2 P η η' (Ne.symm hne) (hS'.trans hη'.symm) hP
    · intro h
      exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ η, hS'⟩) h
  · intro R η hR
    obtain ⟨P, Q, hPQ, hS'⟩ := Finset.card_eq_two.1 (hS η)
    have hP : P ∈ S η := by rw [hS']; simp
    have hRP : R ≠ P := fun h ↦ hR (h ▸ hP)
    rw [hN14 P R η hP hRP]
    have hterm : ∀ η' ∈ univ.filter (fun η' ↦ S η' = {P, R}),
        τ P η' η = ((univ.filter fun t ↦ inc t η ∧ inc t η').card : ℚ) := by
      intro η' hη'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hη'
      refine hN3 P η η' ?_ hP (by rw [hη']; simp)
      intro h
      apply hR
      rw [h, hη']
      simp
    rw [Finset.sum_congr rfl hterm, ← Nat.cast_sum,
      sum_card_filter_inc_eq m S ST inc hinc huniq hP hRP]

end Algebra

section ClosedHeight

variable {X Y : Scheme.{0}} (f : X ⟶ Y) (hf : Topology.IsClosedEmbedding f)

include hf in
/-- A closed embedding of schemes preserves heights of points. -/
private theorem height_apply_of_isClosedEmbedding (y : X) :
    Order.height (f y) = Order.height y := by
  have hle : ∀ a b : X, f a ≤ f b ↔ a ≤ b := fun a b ↦ by
    rw [Scheme.le_iff_specializes, Scheme.le_iff_specializes]
    exact hf.isInducing.specializes_iff
  let g : Set.Iic y ↪o Set.Iic (f y) :=
    { toFun := fun z ↦ ⟨f z.1, (hle _ _).2 z.2⟩
      inj' := fun a b h ↦ Subtype.ext (hf.injective (congrArg Subtype.val h))
      map_rel_iff' := fun {a b} ↦ hle a.1 b.1 }
  have hsurj : Function.Surjective g := by
    rintro ⟨w, hw⟩
    have hsp : f y ⤳ w := Scheme.le_iff_specializes.1 hw
    have hmem : w ∈ Set.range f :=
      hsp.mem_closed hf.isClosed_range ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := hmem
    exact ⟨⟨z, (hle _ _).1 hw⟩, rfl⟩
  have e := Order.krullDim_eq_of_orderIso (OrderIso.ofSurjective g hsurj)
  rw [← Order.height_eq_krullDim_Iic, ← Order.height_eq_krullDim_Iic] at e
  exact_mod_cast e.symm

end ClosedHeight

section Surface

/-- The topological dimension of a scheme is the Krull dimension of its specialization order. -/
private theorem topologicalKrullDim_eq_krullDim' (X : Scheme.{0}) :
    topologicalKrullDim X = Order.krullDim X :=
  Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints

/-- The generic point of an integral scheme is maximal in the specialization order. -/
private theorem coheight_genericPoint_eq_zero (X : Scheme.{0}) [IsIntegral X] :
    Order.coheight (genericPoint X) = 0 :=
  Order.coheight_eq_zero.2 fun _ _ ↦
    (Scheme.le_iff_specializes).2 ((genericPoint_spec X).specializes trivial)

/-- A point of an integral scheme other than the generic point has positive coheight. -/
private theorem one_le_coheight_of_ne_genericPoint (X : Scheme.{0}) [IsIntegral X] {y : X}
    (hne : y ≠ genericPoint X) : 1 ≤ Order.coheight y := by
  have hsp : genericPoint X ⤳ y := (genericPoint_spec X).specializes trivial
  have hlt : y < genericPoint X := lt_of_le_not_ge ((Scheme.le_iff_specializes).2 hsp)
    fun h ↦ hne (hsp.antisymm ((Scheme.le_iff_specializes).1 h)).eq.symm
  simpa [coheight_genericPoint_eq_zero] using Order.coheight_add_one_le hlt

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsIntegral X]
  [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]

/-- On a complex surface, the generic point of a prime divisor has height one. -/
theorem height_genericPoint_primeDivisor (h2 : Order.krullDim X = 2)
    (C : MMP.Mori.PrimeDivisor X) : Order.height C.genericPoint = 1 := by
  have hform := MMP.height_add_coheight_eq_krullDim ℂ C.genericPoint
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint, h2] at hform
  exact ENat.add_left_injective_of_ne_top ENat.one_ne_top
    ((WithBot.coe_injective hform : _ = (2 : ℕ∞)).trans one_add_one_eq_two.symm)

/-- On a complex surface, a prime divisor is a curve. -/
theorem topologicalKrullDim_primeDivisor_eq (h2 : Order.krullDim X = 2)
    (C : MMP.Mori.PrimeDivisor X) : topologicalKrullDim C.idealSheaf.subscheme = 1 := by
  haveI := C.integral
  haveI : LocallyOfFiniteType (C.idealSheaf.subscheme ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (C.idealSheaf.subschemeι ≫ X ↘ Spec (.of ℂ))
    infer_instance
  rw [topologicalKrullDim_eq_krullDim',
    ← MMP.height_add_coheight_eq_krullDim ℂ (genericPoint C.idealSheaf.subscheme),
    coheight_genericPoint_eq_zero, add_zero, ← height_apply_of_isClosedEmbedding
      C.idealSheaf.subschemeι C.idealSheaf.subschemeι.isClosedEmbedding]
  change ((Order.height C.genericPoint : ℕ∞) : WithBot ℕ∞) = 1
  rw [height_genericPoint_primeDivisor h2 C]
  rfl

end Surface

section Component

open MMP.Mori

variable {W : Scheme.{0}} [W.Over (Spec (.of ℂ))] [MMP.IsComplexScheme W]
  [IsLocallyNoetherian W] {D : Divisor W} (hsnc : D.IsSNC (W ↘ Spec (.of ℂ)))
  (hdim : topologicalKrullDim W = 3)

open scoped MMP.SubschemeOver

/-- The range of the inclusion of a component is its support. -/
private theorem range_subschemeι_eq (P : D.support) :
    Set.range P.1.idealSheaf.subschemeι = P.1.support := by
  rw [Scheme.IdealSheafData.range_subschemeι]

/-- The generic point of a component is the image of the generic point of its scheme. -/
private theorem subschemeι_genericPoint (P : D.support) :
    haveI := P.1.integral
    P.1.idealSheaf.subschemeι (genericPoint P.1.idealSheaf.subscheme) = P.1.genericPoint :=
  rfl

/-- A component of `D`, with its reduced structure, is integral. -/
theorem isIntegral_component (P : D.support) : IsIntegral P.1.idealSheaf.subscheme :=
  P.1.integral

/-- A component of `D` is locally of finite type over `ℂ`. -/
theorem locallyOfFiniteType_component (P : D.support) :
    LocallyOfFiniteType (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) := by
  change LocallyOfFiniteType (P.1.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ))
  infer_instance

attribute [local instance] isIntegral_component locallyOfFiniteType_component

include hdim in
/-- A component has dimension at most two. -/
theorem krullDim_component_le (P : D.support) :
    Order.krullDim P.1.idealSheaf.subscheme ≤ 2 := by
  set E := P.1.idealSheaf.subscheme
  have h := MMP.height_add_coheight_eq_krullDim ℂ (genericPoint E)
  have hc := coheight_genericPoint_eq_zero E
  rw [hc, add_zero] at h
  rw [← h]
  have hh := height_apply_of_isClosedEmbedding P.1.idealSheaf.subschemeι
    P.1.idealSheaf.subschemeι.isClosedEmbedding (genericPoint E)
  rw [subschemeι_genericPoint] at hh
  rw [← hh]
  have h2 := height_add_coheight_le hdim P.1.genericPoint
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at h2
  have : Order.height P.1.genericPoint ≤ 2 := by
    induction h' : Order.height P.1.genericPoint using ENat.recTopCoe with
    | top => rw [h'] at h2; simp at h2
    | coe a =>
      rw [h'] at h2
      norm_cast at h2 ⊢
      omega
  exact WithBot.coe_le_coe.2 this

include hsnc hdim in
/-- **The point of a component over a double curve.** If the double curve `η` lies on the
component `P`, its preimage `y ∈ E_P` has height and coheight one, and `E_P` has dimension two. -/
theorem exists_curvePoint (P : D.support) {η : W} (hη : IsDoubleCurve D η)
    (hP : P ∈ comps D η) :
    ∃ y : P.1.idealSheaf.subscheme, P.1.idealSheaf.subschemeι y = η ∧ Order.height y = 1 ∧
      Order.coheight y = 1 ∧ Order.krullDim P.1.idealSheaf.subscheme = 2 := by
  set E := P.1.idealSheaf.subscheme
  obtain ⟨y, hy⟩ : η ∈ Set.range P.1.idealSheaf.subschemeι := by
    rw [range_subschemeι_eq]; exact mem_comps.1 hP
  have hhy : Order.height y = 1 := by
    rw [← height_apply_of_isClosedEmbedding P.1.idealSheaf.subschemeι
      P.1.idealSheaf.subschemeι.isClosedEmbedding y, hy]
    exact hη.1
  -- `y` is not the generic point of `E`
  have hne : y ≠ genericPoint E := by
    intro h
    obtain ⟨Q, hQ, hQP⟩ : ∃ Q ∈ comps D η, Q ≠ P := by
      have h2 := hη.2
      by_contra hcon
      push Not at hcon
      have : comps D η ⊆ {P} := fun Q hQ ↦ Finset.mem_singleton.2 (hcon Q hQ)
      have := Finset.card_le_card this
      simp at this
      omega
    have hgen : P.1.genericPoint ∈ Q.1.support := by
      rw [← subschemeι_genericPoint, ← h, hy]
      exact mem_comps.1 hQ
    exact hQP (Subtype.ext (MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support hgen).symm)
  have hc1 := one_le_coheight_of_ne_genericPoint E hne
  have hform := MMP.height_add_coheight_eq_krullDim ℂ y
  have hle := krullDim_component_le hdim P
  rw [hhy] at hform
  have hc : Order.coheight y = 1 := by
    have : ((1 + Order.coheight y : ℕ∞) : WithBot ℕ∞) ≤ 2 := hform ▸ hle
    have h' : (1 : ℕ∞) + Order.coheight y ≤ 2 := WithBot.coe_le_coe.1 this
    induction h'' : Order.coheight y using ENat.recTopCoe with
    | top => rw [h''] at h'; simp at h'
    | coe a =>
      rw [h''] at h' hc1
      norm_cast at h' hc1 ⊢
      omega
  refine ⟨y, hy, hhy, hc, ?_⟩
  rw [← hform, hc]
  rfl

include hsnc in
/-- A component has simple normal crossings with the other components. -/
private theorem hasSNCWith_component (P : D.support) :
    MMP.Resolution.HasSNCWith (fun R : {R : D.support // R ≠ P} ↦ R.1.1.idealSheaf)
      P.1.idealSheaf := by
  intro x hx
  obtain ⟨n, z, j, hz, hj, hI⟩ := exists_params hsnc x
  have hPx : P ∈ comps D x := mem_comps.2 hx
  let c : {i : {R : D.support // R ≠ P} // x ∈ (i.1.1.idealSheaf).support} → Fin n :=
    fun i ↦ j ⟨i.1.1, mem_comps.2 i.2⟩
  refine ⟨n, z, c, {j ⟨P, hPx⟩}, hz, ?_, ?_, ?_⟩
  · intro i
    exact hI ⟨i.1.1, mem_comps.2 i.2⟩
  · intro a b h
    have := hj h
    exact Subtype.ext (Subtype.ext (congrArg (fun Q : comps D x ↦ Q.1) this))
  · rw [Finset.coe_singleton, Set.image_singleton]
    exact hI ⟨P, hPx⟩

/-- No other component contains an irreducible component of a component. -/
private theorem not_subset_component (P : D.support) (R : {R : D.support // R ≠ P}) :
    ∀ W' ∈ MMP.Resolution.componentsOf (P.1.idealSheaf.support : Set W),
      ¬ W' ⊆ (R.1.1.idealSheaf.support : Set W) := by
  intro W' hW' hsub
  have hirr : IsIrreducible (P.1.idealSheaf.support : Set W) := by
    rw [show (P.1.idealSheaf.support : Set W) = P.1.support from rfl,
      AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure
  have hW'eq : W' = P.1.idealSheaf.support :=
    le_antisymm hW'.1.2 (hW'.2 ⟨hirr, le_rfl⟩ hW'.1.2)
  have hgen : P.1.genericPoint ∈ R.1.1.support := by
    apply hsub
    rw [hW'eq]
    show P.1.genericPoint ∈ P.1.support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  exact R.2 (Subtype.ext (MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support hgen).symm)

include hsnc in
/-- At each point `y` of a component `E_P` there is a regular system of parameters of the stalk
in which each other component through `y` is cut out by its own parameter. -/
theorem exists_component_coordinates (P : D.support) (y : P.1.idealSheaf.subscheme) :
    ∃ (m : ℕ) (w : Fin m → P.1.idealSheaf.subscheme.presheaf.stalk y)
      (c : {R : {R : D.support // R ≠ P} //
        y ∈ (R.1.1.idealSheaf.comap P.1.idealSheaf.subschemeι).support} → Fin m),
      IsRegularSystemOfParameters w ∧
        (∀ R, IdealSheafData.stalk (R.1.1.1.idealSheaf.comap P.1.idealSheaf.subschemeι) y =
          Ideal.span {w (c R)}) ∧ Function.Injective c :=
  MMP.Resolution.exists_coordinates_comap_subschemeι_of_hasSNCWith
    (hasSNCWith_component hsnc P) (not_subset_component P) y

include hsnc in
/-- A component is smooth over `ℂ`. -/
theorem isSmoothScheme_component (P : D.support) :
    IsSmoothScheme (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
  hsnc.1 P.1 P.2

/-- The generic point of a component lies on no other component. -/
private theorem genericPoint_notMem_comap (P : D.support) (R : {R : D.support // R ≠ P}) :
    genericPoint P.1.idealSheaf.subscheme ∉
      (R.1.1.idealSheaf.comap P.1.idealSheaf.subschemeι).support := by
  intro h
  rw [MMP.Resolution.mem_support_comap_iff, subschemeι_genericPoint] at h
  exact R.2 (Subtype.ext (MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support h).symm)

include hsnc hdim in
/-- **A component of `E_R ∩ E_P` is cut out by `E_R` near each of its points.** -/
theorem stalk_idealSheaf_eq_stalk_comap (P : D.support) (R : {R : D.support // R ≠ P})
    (C : MMP.Mori.PrimeDivisor P.1.idealSheaf.subscheme)
    (hC : C.genericPoint ∈ (R.1.1.idealSheaf.comap P.1.idealSheaf.subschemeι).support)
    {y : P.1.idealSheaf.subscheme} (hy : y ∈ C.support) :
    IdealSheafData.stalk C.idealSheaf y =
      IdealSheafData.stalk (R.1.1.idealSheaf.comap P.1.idealSheaf.subschemeι) y := by
  have hsmE := isSmoothScheme_component hsnc P
  have hgy := MMP.Resolution.Aux.genericPoint_specializes_of_mem_support C hy
  have hprime := MMP.Resolution.Aux.primeOfSpecializes_genericPoint
      (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) hsmE C hy
  rw [← hprime]
  have hyF : y ∈ (R.1.1.idealSheaf.comap P.1.idealSheaf.subschemeι).support :=
      hgy.mem_closed (R.1.1.idealSheaf.comap P.1.idealSheaf.subschemeι).support.isClosed hC
  obtain ⟨m, w, c, hw, hc, -⟩ := exists_component_coordinates hsnc P y
  have hFy := hc ⟨R, hyF⟩
  have hFprime : (IdealSheafData.stalk (R.1.1.idealSheaf.comap P.1.idealSheaf.subschemeι)
      y).IsPrime := by
    rw [hFy]
    have := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hw
    exact MMP.Resolution.isPrime_span_singleton_of_isRegularSystemOfParameters hw _
  have hle : IdealSheafData.stalk (R.1.1.idealSheaf.comap P.1.idealSheaf.subschemeι) y
      ≤ MMP.Intersection.primeOfSpecializes hgy :=
    (MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes
        (R.1.1.idealSheaf.comap P.1.idealSheaf.subschemeι) hgy).1 hC
  let Q' : PrimeSpectrum (P.1.idealSheaf.subscheme.presheaf.stalk y) := ⟨_, hFprime⟩
  set ξ := P.1.idealSheaf.subscheme.fromSpecStalk y Q'
  have hξ : ξ ⤳ y := MMP.Resolution.specializes_fromSpecStalk y Q'
  have hqξ : MMP.Intersection.primeOfSpecializes hξ = IdealSheafData.stalk
      (R.1.1.idealSheaf.comap P.1.idealSheaf.subschemeι) y :=
    MMP.Resolution.primeOfSpecializes_fromSpecStalk y Q' hξ
  have hξC : ξ ⤳ C.genericPoint :=
    MMP.Intersection.specializes_of_primeOfSpecializes_le hξ hgy (hqξ ▸ hle)
  have hξF : ξ ∈ (R.1.1.idealSheaf.comap P.1.idealSheaf.subschemeι).support :=
    (MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes
        (R.1.1.idealSheaf.comap P.1.idealSheaf.subschemeι) hξ).2 hqξ.ge
  have hξne : ξ ≠ genericPoint P.1.idealSheaf.subscheme := fun h ↦ genericPoint_notMem_comap P R
      (h ▸ hξF)
  have hcξ := one_le_coheight_of_ne_genericPoint _ hξne
  have hfξ := MMP.height_add_coheight_eq_krullDim ℂ ξ
  have hfC := MMP.height_add_coheight_eq_krullDim ℂ C.genericPoint
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at hfC
  have hle2 := krullDim_component_le hdim P
  have hhle : Order.height C.genericPoint ≤ Order.height ξ :=
    Order.height_mono ((Scheme.le_iff_specializes).2 hξC)
  have e : Order.height ξ + Order.coheight ξ = Order.height C.genericPoint + 1 := by
    have := hfξ.trans hfC.symm
    exact_mod_cast this
  have hb : Order.height C.genericPoint + 1 ≤ 2 := by
    have := hfC ▸ hle2
    exact WithBot.coe_le_coe.1 this
  have hheq : Order.height ξ = Order.height C.genericPoint :=
    enat_eq_of_add_eq e hb hcξ hhle
  have := eq_of_specializes_of_height_eq hξC hheq.symm (by
    intro ht; rw [hheq] at ht; rw [ht] at hb; simp at hb)
  rw [MMP.Resolution.primeOfSpecializes_congr this.symm hgy hξ, hqξ]

end Component

attribute [local instance] isIntegral_component locallyOfFiniteType_component

open Opposite Topology

section LocalEquation

open MMP.Mori DivisorWithCoeffs

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]

/-- **A local equation of a prime divisor on a smooth scheme**, with a generator of its ideal on an
affine neighbourhood: near a point of `P` the ideal of `P` is generated by one section `f`, and
the rational function `f` is a local equation of `1 · P`. -/
private theorem exists_isLocalEquation_single_of_mem_support {sX : X ⟶ Spec (.of k)}
    [LocallyOfFiniteType sX] (hsm : IsSmoothScheme sX) (P : MMP.Mori.PrimeDivisor X) {x : X}
    (hx : x ∈ P.support) :
    ∃ (W : X.Opens) (_ : IsAffineOpen W) (_ : x ∈ W) (f : Γ(X, W)) (φ : (RationalFunctions X)ˣ),
      (∀ y (hy : y ∈ W), IdealSheafData.stalk P.idealSheaf y =
        Ideal.span {(X.presheaf.germ W y hy).hom f}) ∧
      (∀ (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ W),
        (φ : RationalFunctions X) Z = (X.presheaf.germ W _ hZ).hom f) ∧
      Divisor.IsLocalEquation (Finsupp.single P 1 : Divisor X) W φ := by
  classical
  haveI := P.integral
  have hcart : Stacks.Divisors.IsEffectiveCartierDivisor P.idealSheaf :=
    MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm P
  obtain ⟨W, hW, hxW, f, hf, hspan⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor
      P.idealSheaf hcart x
  have hgerm : ∀ y (hy : y ∈ W), IdealSheafData.stalk P.idealSheaf y =
      Ideal.span {(X.presheaf.germ W y hy).hom f} := by
    intro y hy
    rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ P.idealSheaf y ⟨W, hW⟩ hy, hspan,
      Ideal.map_span, Set.image_singleton]
  have hnzd : ∀ y (hy : y ∈ W), (X.presheaf.germ W y hy).hom f ∈
      nonZeroDivisors (X.presheaf.stalk y) := fun y hy =>
    Stacks.Divisors.germ_mem_nonZeroDivisors hW hf y hy
  have hfield : ∀ Z : irreducibleComponents X,
      IsField (X.presheaf.stalk (componentGenericPoint X Z)) :=
    fun Z => RationalFunctions.isField_stalk X Z
  let u : ∀ Z : irreducibleComponents X, (X.presheaf.stalk (componentGenericPoint X Z))ˣ :=
    fun Z => if h : componentGenericPoint X Z ∈ W then
      (by
        letI := (hfield Z).toField
        exact (isUnit_iff_ne_zero.2 (nonZeroDivisors.ne_zero (hnzd _ h))).unit)
      else 1
  let φ : (RationalFunctions X)ˣ := (RationalFunctions.unitsEquiv X).symm u
  have hφZ : ∀ (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ W),
      (φ : RationalFunctions X) Z = (X.presheaf.germ W _ hZ).hom f := by
    intro Z hZ
    change ((u Z : (X.presheaf.stalk (componentGenericPoint X Z))ˣ) :
      X.presheaf.stalk (componentGenericPoint X Z)) = _
    simp only [u]
    rw [dif_pos hZ]
    rfl
  refine ⟨W, hW, hxW, f, φ, hgerm, hφZ, ?_⟩
  rintro E ⟨y, hyE, hyW⟩
  have hηW : E.genericPoint ∈ W := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hyE
    exact (specializes_iff_mem_closure.mpr hyE).mem_open W.isOpen hyW
  have hZW : componentGenericPoint X E.component ∈ W :=
    E.specializes_genericPoint.mem_open W.isOpen hηW
  have key : E.toComponent.hom ((X.presheaf.germ W _ hηW).hom f) =
      (φ : RationalFunctions X) E.component := by
    rw [hφZ _ hZW]
    exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
  by_cases hEP : P = E
  · subst hEP
    rw [coeff_single_self]
    have hmem : P.genericPoint ∈ P.support := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
    have hg0 := nonZeroDivisors.ne_zero (hnzd _ hηW)
    have hprime : Prime ((X.presheaf.germ W _ hηW).hom f) := by
      rw [← Ideal.span_singleton_prime hg0, ← hgerm _ hηW,
        ← MMP.Resolution.Aux.primeOfSpecializes_genericPoint sX hsm P hmem]
      exact Ideal.comap_isPrime _ _
    exact (P.ord_eq_one_of_irreducible hprime.irreducible key).symm
  · rw [coeff_single_of_ne hEP]
    have hnm : E.genericPoint ∉ P.support := fun h =>
      hEP (MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support P E h)
    have htop := (AlgebraicGeometry.IdealSheafData.stalk_eq_top_iff_notMem_support
      P.idealSheaf _).2 hnm
    rw [hgerm _ hηW, Ideal.span_singleton_eq_top] at htop
    exact (E.ord_eq_zero_of_isUnit htop key).symm

open Classical in
/-- **The pull-back of a prime divisor meeting transversally.** Let `f : X ⟶ Y` map the generic
points of `X` off a prime divisor `R` of a smooth scheme `Y`, and let `C` be a prime divisor of
`X` such that a generator of the ideal of `R` at `f(η_C)` restricts to a uniformizer of
`𝒪_{X,C}`. Then the coefficient of `C` in `f^*R` is `1` if `f(η_C) ∈ R` and `0` otherwise. -/
private theorem coeff_pullback_single {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of k)} [LocallyOfFiniteType sY] (hsm : IsSmoothScheme sY) [CompactSpace X]
    (f : X ⟶ Y) (R : MMP.Mori.PrimeDivisor Y)
    (hRc : Divisor.IsCartier (Finsupp.single R 1 : Divisor Y))
    (hB : ∀ Z : irreducibleComponents X,
      f (componentGenericPoint X Z) ∉ DivisorWithCoeffs.supp (Finsupp.single R (1 : ℤ)))
    (C : MMP.Mori.PrimeDivisor X)
    (hirr : f C.genericPoint ∈ R.support → ∀ g : Y.presheaf.stalk (f C.genericPoint),
      IdealSheafData.stalk R.idealSheaf (f C.genericPoint) = Ideal.span {g} →
        Irreducible ((f.stalkMap C.genericPoint).hom g)) :
    (Divisor.pullback (f := f) (Finsupp.single R (1 : ℤ)) hRc hB).coeff C =
      if f C.genericPoint ∈ R.support then 1 else 0 := by
  have hPgen : C.genericPoint ∈ C.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  by_cases hy : f C.genericPoint ∈ R.support
  · rw [if_pos hy]
    obtain ⟨W, -, hyW, g, ψ, hgerm, hψg, hψ⟩ :=
      exists_isLocalEquation_single_of_mem_support hsm R hy
    have hP : (C.support ∩ f ⁻¹ᵁ W).Nonempty := ⟨C.genericPoint, hPgen, hyW⟩
    rw [Divisor.isPullback_pullback hRc hB W ψ hψ C hP]
    set ηV := componentGenericPoint X C.component
    have hηVU : f ηV ∈ W := C.map_componentGenericPoint_mem f hP
    have hηE : f ηV ∉ R.support := fun h => hB C.component
      (DivisorWithCoeffs.mem_supp_iff.2 ⟨R, by simp [DivisorWithCoeffs.coeff], h⟩)
    have hunit : IsUnit (Y.presheaf.germ W (f ηV) hηVU g) := by
      rw [← Ideal.span_singleton_eq_top, ← hgerm]
      exact (AlgebraicGeometry.IdealSheafData.stalk_eq_top_iff_notMem_support
        R.idealSheaf _).2 hηE
    have hW' := mem_pointComponent (f ηV)
    have hcgp : componentGenericPoint Y (pointComponent (f ηV)) ∈ W :=
      ((isGenericPoint_componentGenericPoint Y _).specializes hW').mem_open W.isOpen hηVU
    have ha : (stalkToRationalFunctions Y hW').hom (hunit.unit : Y.presheaf.stalk (f ηV)) =
        (ψ : RationalFunctions Y) (pointComponent (f ηV)) := by
      rw [hψg _ hcgp, IsUnit.unit_spec]
      exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
    rw [pullbackComponent_eq hB hψ hηVU hW' hunit.unit ha]
    set b : X.presheaf.stalk C.genericPoint :=
      (f.stalkMap C.genericPoint).hom (Y.presheaf.germ W (f C.genericPoint) hyW g) with hb
    have hval : ((Units.map (f.stalkMap ηV).hom.toMonoidHom hunit.unit :
        (X.presheaf.stalk ηV)ˣ) : X.presheaf.stalk ηV) = C.toComponent.hom b := by
      change (f.stalkMap ηV).hom (Y.presheaf.germ W (f ηV) hηVU g) =
        (X.presheaf.stalkSpecializes _).hom
          ((f.stalkMap C.genericPoint).hom (Y.presheaf.germ W _ hyW g))
      rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply]
      exact (TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _).symm
    have hirr' : Irreducible b := hirr hy _ (hgerm _ hyW)
    have h := C.valuation_eq_exp_ordUnit (Units.map (f.stalkMap ηV).hom.toMonoidHom hunit.unit)
    rw [hval, C.valuation_toComponent_of_irreducible hirr'] at h
    exact (WithZero.exp_inj.1 h).symm
  · rw [if_neg hy]
    let U : Y.Opens := ⟨(R.support : Set Y)ᶜ, R.idealSheaf.support.isClosed.isOpen_compl⟩
    have h1 : Divisor.IsLocalEquation (Finsupp.single R 1) U 1 := by
      intro E' hE'
      rw [PrimeDivisor.ord_one]
      by_cases hEE : E' = R
      · subst hEE
        obtain ⟨x, hx, hxU⟩ := hE'
        exact absurd hx hxU
      · simp [DivisorWithCoeffs.coeff, Ne.symm hEE]
    have hP : (C.support ∩ f ⁻¹ᵁ U).Nonempty := ⟨C.genericPoint, hPgen, hy⟩
    rw [Divisor.isPullback_pullback hRc hB U 1 h1 C hP]
    have hW := mem_pointComponent (f (componentGenericPoint X C.component))
    rw [pullbackComponent_eq hB h1 (C.map_componentGenericPoint_mem _ hP) hW 1 (by simp),
      map_one, PrimeDivisor.ordUnit_one]

end LocalEquation

section DegreePullback

open MMP.Mori

universe v

variable {k : Type v} [Field k] {X Y C : Scheme.{v}} [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
  (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [QuasiCompact sX] [QuasiCompact sY]
  (f : X ⟶ Y) (hf : f ≫ sY = sX)

include hf in
/-- **The degree of a pulled-back Cartier divisor** along a curve `i : C ⟶ X` is the degree of
the divisor along `i ≫ f`. -/
private theorem degreeOn_pullback_divisor (D : Divisor Y) (hD : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ D.supp)
    (i : C ⟶ X) [IsProper (i ≫ sX)] (hdim : topologicalKrullDim C ≤ 1)
    [IsProper ((i ≫ f) ≫ sY)] :
    (D.pullback hD hB).degreeOn k sX i hdim (hD.isCartier_pullback f hB) =
      D.degreeOn k sY (i ≫ f) hdim hD := by
  obtain ⟨e⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso hD f hB
  haveI := hD.isInvertibleModule_divisorialSheaf
  haveI := (hD.isCartier_pullback f hB).isInvertibleModule_divisorialSheaf
  change MMP.Mori.degreeOn k sX i hdim (D.pullback hD hB).divisorialSheaf =
    MMP.Mori.degreeOn k sY (i ≫ f) hdim D.divisorialSheaf
  rw [degreeOn_eq_of_iso k sX i hdim e]
  exact degreeOn_pullback_eq_degreeOn_comp sX sY f i hf hdim _

end DegreePullback

section ResidueField

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}

private theorem fromSpecResidueField_toSpecΓ' (x : X) :
    X.fromSpecResidueField x ≫ X.toSpecΓ = Spec.map (X.Γevaluation x) := by
  rw [Scheme.fromSpecResidueField, Category.assoc, Scheme.fromSpecStalk_toSpecΓ,
    ← Spec.map_comp]
  rfl

/-- At a closed point of a scheme locally of finite type over an algebraically closed field `k`,
the residue field has degree one over `k`. -/
theorem finrank_residueField_of_isClosed (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] (x : X) (hx : IsClosed ({x} : Set X)) :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ X.Γevaluation x).hom.toAlgebra
    Module.finrank k (X.residueField x) = 1 := by
  letI : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ X.Γevaluation x).hom.toAlgebra
  have hinv : (residueFieldIsoBase p x hx).inv =
      (Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ X.Γevaluation x := by
    apply Spec.map_injective
    rw [SpecMap_residueFieldIsoBase_inv, Spec.map_comp, Spec.map_comp,
      ← fromSpecResidueField_toSpecΓ', Category.assoc, Category.assoc,
      ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  refine Module.finrank_of_bijective_algebraMap ?_
  rw [RingHom.algebraMap_toAlgebra, ← hinv]
  exact ConcreteCategory.bijective_of_isIso (residueFieldIsoBase p x hx).inv

/-- At a closed point, the stalk modulo its maximal ideal has dimension one over `k`. -/
private theorem finrank_stalk_quotient_maximalIdeal (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    letI := MMP.Mori.stalkAlgebra p x
    Module.finrank k (X.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) = 1 :=
  finrank_residueField_of_isClosed p x hx

end ResidueField

section LocalSum

open MMP.Mori

universe u

variable {k : Type u} [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
  [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]

/-- **The degree of a curve along another is the sum of the local intersection numbers**, on a
smooth surface. -/
private theorem degreeOn_single_eq_finsum (hY : MMP.Mori.IsVariety k sY) (hsm : IsSmoothScheme sY)
    (hdim : topologicalKrullDim Y = 2) {C D : MMP.Mori.PrimeDivisor Y} (hCD : C ≠ D)
    [hC : IsProper (C.idealSheaf.subschemeι ≫ sY)]
    (hdimC : topologicalKrullDim C.idealSheaf.subscheme ≤ 1) :
    (Divisor.degreeOn k sY C.idealSheaf.subschemeι hdimC (Finsupp.single D 1 : Divisor Y)
        (MMP.Fourfold.isCartier_of_isSmoothScheme hsm _) : ℚ) =
      ∑ᶠ y ∈ C.support ∩ D.support,
        (localIntersectionNumber sY y (Finsupp.single C 1) (Finsupp.single D 1) : ℚ) := by
  obtain ⟨-, hIN, -⟩ := isIntersectionNumber_finsum_localIntersectionNumber_of_ne sY hY hsm hdim
    hCD hC
  obtain ⟨_, hd, hQ, h⟩ := hIN
  rw [← h]
  have key : ∀ (E : QDivisor Y) (_ : E = Divisor.toQDivisor (Finsupp.single D 1))
      (hQ' : E.IsQCartier),
      E.intersectionNumber k sY C.idealSheaf.subschemeι hd hQ' =
        (Divisor.degreeOn k sY C.idealSheaf.subschemeι hdimC (Finsupp.single D 1 : Divisor Y)
          (MMP.Fourfold.isCartier_of_isSmoothScheme hsm _) : ℚ) := by
    rintro _ rfl hQ'
    exact QDivisor.intersectionNumber_toQDivisor k sY _ hd _ _ hQ'
  rw [key _ (by rw [MMP.Threefold.Resolution.toQDivisor_single, Int.cast_one]) hQ]

end LocalSum

section Curves

open MMP.Mori

variable {W : Scheme.{0}} [W.Over (Spec (.of ℂ))] [MMP.IsComplexScheme W]
  [IsLocallyNoetherian W] {D : Divisor W} (hsnc : D.IsSNC (W ↘ Spec (.of ℂ)))
  (hdim : topologicalKrullDim W = 3)

open scoped MMP.SubschemeOver

include hsnc hdim in
/-- **Curves of the same type are disjoint.** Two prime divisors of a component `E_P` lying in
the same `E_R ∩ E_P` and sharing a point are equal. -/
private theorem eq_of_mem_support_of_comap (P : D.support) (R : {R : D.support // R ≠ P})
    {C C' : MMP.Mori.PrimeDivisor P.1.idealSheaf.subscheme}
    (hC : C.genericPoint ∈ (R.1.1.idealSheaf.comap P.1.idealSheaf.subschemeι).support)
    (hC' : C'.genericPoint ∈ (R.1.1.idealSheaf.comap P.1.idealSheaf.subschemeι).support)
    {y : P.1.idealSheaf.subscheme} (hy : y ∈ C.support) (hy' : y ∈ C'.support) : C = C' := by
  have hsmE := isSmoothScheme_component hsnc P
  have h1 := stalk_idealSheaf_eq_stalk_comap hsnc hdim P R C hC hy
  have h2 := stalk_idealSheaf_eq_stalk_comap hsnc hdim P R C' hC' hy'
  have hg := MMP.Resolution.Aux.genericPoint_specializes_of_mem_support C hy
  have hg' := MMP.Resolution.Aux.genericPoint_specializes_of_mem_support C' hy'
  have hp := MMP.Resolution.Aux.primeOfSpecializes_genericPoint
    (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) hsmE C hy
  have hp' := MMP.Resolution.Aux.primeOfSpecializes_genericPoint
    (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) hsmE C' hy'
  have heq : MMP.Intersection.primeOfSpecializes hg = MMP.Intersection.primeOfSpecializes hg' := by
    rw [hp, hp', h1, h2]
  have hs1 := MMP.Intersection.specializes_of_primeOfSpecializes_le hg hg' heq.le
  have hs2 := MMP.Intersection.specializes_of_primeOfSpecializes_le hg' hg heq.ge
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hs1.antisymm hs2).eq

omit [W.Over (Spec (.of ℂ))] [MMP.IsComplexScheme W] [IsLocallyNoetherian W] in
/-- A point common to two distinct prime divisors of a surface is a closed point. -/
private theorem isClosed_singleton_of_mem_inter' {Y : Scheme.{0}} [IsLocallyNoetherian Y]
    [IsNormal Y]
    (hdim : topologicalKrullDim Y = 2)
    {C D : MMP.Mori.PrimeDivisor Y} (hCD : C ≠ D) {y : Y} (hy : y ∈ C.support ∩ D.support) :
    IsClosed ({y} : Set Y) := by
  have hne : y ≠ C.genericPoint := by
    rintro rfl
    exact hCD (MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support D C hy.2).symm
  have hle : y ≤ C.genericPoint := by
    have h := hy.1
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h
    exact specializes_iff_mem_closure.mpr h
  have hlt : y < C.genericPoint := lt_of_le_not_ge hle fun h =>
    hne (Specializes.antisymm (show y ⤳ C.genericPoint from h)
      (show C.genericPoint ⤳ y from hle)).eq
  have h2 := Order.coheight_add_one_le hlt
  rw [MMP.Mori.PrimeDivisor.coheight_genericPoint] at h2
  refine closure_subset_iff_isClosed.mp fun w hw => ?_
  have hwy : w ≤ y := specializes_iff_mem_closure.mpr hw
  by_contra hne
  have hlt' : w < y := lt_of_le_not_ge hwy fun h => hne (Specializes.antisymm
    (show w ⤳ y from h) (show y ⤳ w from hwy)).eq
  have h4 := Order.coheight_add_one_le hlt'
  have h5 := coheight_le_topologicalKrullDim w
  rw [hdim] at h5
  have h6 : (1 : ℕ∞) + 1 + 1 ≤ 2 :=
    (add_le_add h2 (le_refl (1 : ℕ∞))).trans (h4.trans (WithBot.coe_le_coe.mp h5))
  exact absurd h6 (by decide)

omit [W.Over (Spec (.of ℂ))] [MMP.IsComplexScheme W] [IsLocallyNoetherian W] in
private theorem localIdeal_single_one {Y : Scheme.{0}} (q : Y) (C : MMP.Mori.PrimeDivisor Y) :
    MMP.Mori.localIdeal q (Finsupp.single C 1 : Divisor Y) = IdealSheafData.stalk C.idealSheaf
        q := by
  classical
  rw [MMP.Mori.localIdeal, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.prod_singleton,
    Finsupp.single_eq_same]
  simp

include hsnc in
/-- Two curves of a component lying on two different other components are different. -/
private theorem ne_of_mem_comap {P : D.support} {Q R : {R : D.support // R ≠ P}} (hQR : Q ≠ R)
    {C C' : MMP.Mori.PrimeDivisor P.1.idealSheaf.subscheme}
    (hC : C.genericPoint ∈ (Q.1.1.idealSheaf.comap P.1.idealSheaf.subschemeι).support)
    (hC' : C'.genericPoint ∈ (R.1.1.idealSheaf.comap P.1.idealSheaf.subschemeι).support) :
    C ≠ C' := by
  rintro rfl
  obtain ⟨m, w, c, hw, -, hinj⟩ := exists_component_coordinates hsnc P C.genericPoint
  have hm : (m : ℕ∞) = 1 := by
    have h1 := hw.2
    rw [ringKrullDim_stalk_eq_coheight, AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at h1
    exact_mod_cast h1.symm
  have hm1 : m = 1 := by exact_mod_cast hm
  subst hm1
  have := hinj (Subsingleton.elim (c ⟨Q, hC⟩) (c ⟨R, hC'⟩))
  exact hQR (congrArg Subtype.val this)

include hsnc in
/-- **Transverse curves meet with multiplicity one.** Two curves `C ⊆ E_Q ∩ E_P` and
`C' ⊆ E_R ∩ E_P` of a surface component `E_P`, with `Q ≠ R`, have local intersection number one at
each common point. -/
private theorem localIntersectionNumber_eq_one {P : D.support} {Q R : {R : D.support // R ≠ P}}
    (hQR : Q ≠ R) {C C' : MMP.Mori.PrimeDivisor P.1.idealSheaf.subscheme}
    (hC : C.genericPoint ∈ (Q.1.1.idealSheaf.comap P.1.idealSheaf.subschemeι).support)
    (hC' : C'.genericPoint ∈ (R.1.1.idealSheaf.comap P.1.idealSheaf.subschemeι).support)
    (h2 : Order.krullDim P.1.idealSheaf.subscheme = 2) (hdim : topologicalKrullDim W = 3)
    {y : P.1.idealSheaf.subscheme} (hy : y ∈ C.support) (hy' : y ∈ C'.support) :
    MMP.Mori.localIntersectionNumber (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) y
      (Finsupp.single C 1) (Finsupp.single C' 1) = 1 := by
  have hCC := ne_of_mem_comap hsnc hQR hC hC'
  have hsmE := isSmoothScheme_component hsnc P
  haveI := MMP.Resolution.Aux.smooth_of_isSmoothScheme' _ hsmE
  haveI : IsNormal P.1.idealSheaf.subscheme :=
    isNormal_of_smooth_over_field (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ))
  have hdimE : topologicalKrullDim P.1.idealSheaf.subscheme = 2 := by
    rw [topologicalKrullDim_eq_krullDim', h2]
  have hcl := isClosed_singleton_of_mem_inter' hdimE hCC ⟨hy, hy'⟩
  have hht : Order.height y = 0 := by
    rw [Order.height_eq_zero]
    intro z hz
    have : z ∈ closure ({y} : Set _) := specializes_iff_mem_closure.mp hz
    rw [hcl.closure_eq] at this
    rw [Set.mem_singleton_iff.mp this]
  have hform := MMP.height_add_coheight_eq_krullDim ℂ y
  rw [hht, zero_add, h2] at hform
  obtain ⟨m, w, c, hw, hc, hinj⟩ := exists_component_coordinates hsnc P y
  have hc2 : Order.coheight y = 2 := WithBot.coe_injective (hform.trans rfl)
  have hm : m = 2 := by
    have h1 := hw.2
    rw [ringKrullDim_stalk_eq_coheight, hc2] at h1
    have h' : (m : ℕ∞) = 2 := by exact_mod_cast h1.symm
    exact_mod_cast h'
  subst hm
  have hgy := MMP.Resolution.Aux.genericPoint_specializes_of_mem_support C hy
  have hgy' := MMP.Resolution.Aux.genericPoint_specializes_of_mem_support C' hy'
  have hyQ : y ∈ (Q.1.1.idealSheaf.comap P.1.idealSheaf.subschemeι).support :=
    hgy.mem_closed (Q.1.1.idealSheaf.comap P.1.idealSheaf.subschemeι).support.isClosed hC
  have hyR : y ∈ (R.1.1.idealSheaf.comap P.1.idealSheaf.subschemeι).support :=
    hgy'.mem_closed (R.1.1.idealSheaf.comap P.1.idealSheaf.subschemeι).support.isClosed hC'
  have h1 := (stalk_idealSheaf_eq_stalk_comap hsnc hdim P Q C hC hy).trans (hc ⟨Q, hyQ⟩)
  have h1' := (stalk_idealSheaf_eq_stalk_comap hsnc hdim P R C' hC' hy').trans (hc ⟨R, hyR⟩)
  have hab : c ⟨Q, hyQ⟩ ≠ c ⟨R, hyR⟩ := fun h ↦ hQR (congrArg Subtype.val (hinj h))
  have hrange : Set.range w = {w (c ⟨Q, hyQ⟩), w (c ⟨R, hyR⟩)} := by
    ext v
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      have : i = c ⟨Q, hyQ⟩ ∨ i = c ⟨R, hyR⟩ := by omega
      rcases this with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
  have hmax : IdealSheafData.stalk C.idealSheaf y ⊔ IdealSheafData.stalk C'.idealSheaf y =
      IsLocalRing.maximalIdeal _ := by
    rw [h1, h1', ← hw.1, hrange, Ideal.span_insert]
  rw [MMP.Mori.localIntersectionNumber, localIdeal_single_one, localIdeal_single_one, hmax]
  exact finrank_stalk_quotient_maximalIdeal _ y hcl

include hsnc hdim in
/-- The prime divisor of a component `E_P` lying over a double curve `η` through `P`. -/
noncomputable def curveDiv (P : D.support) {η : W} (hη : IsDoubleCurve D η)
    (hP : P ∈ comps D η) : MMP.Mori.PrimeDivisor P.1.idealSheaf.subscheme :=
  AlgebraicGeometry.PrimeDivisor.ofCoheightOne (exists_curvePoint hsnc hdim P hη hP).choose
    (exists_curvePoint hsnc hdim P hη hP).choose_spec.2.2.1

/-- The generic point of `curveDiv` maps to the double curve `η` in `W`. -/
theorem curveDiv_genericPoint (P : D.support) {η : W} (hη : IsDoubleCurve D η)
    (hP : P ∈ comps D η) :
    P.1.idealSheaf.subschemeι (curveDiv hsnc hdim P hη hP).genericPoint = η := by
  simp only [curveDiv, MMP.Mori.PrimeDivisor.genericPoint,
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
  exact (exists_curvePoint hsnc hdim P hη hP).choose_spec.1

include hsnc hdim in
/-- A component through a double curve has dimension two. -/
theorem krullDim_eq_two_of_mem_comps (P : D.support) {η : W} (hη : IsDoubleCurve D η)
    (hP : P ∈ comps D η) : Order.krullDim P.1.idealSheaf.subscheme = 2 :=
  (exists_curvePoint hsnc hdim P hη hP).choose_spec.2.2.2

omit [W.Over (Spec (.of ℂ))] [MMP.IsComplexScheme W] [IsLocallyNoetherian W] in
/-- A point lies on the curve over `η` exactly when its image is a specialization of `η`. -/
private theorem mem_support_iff_specializes {P : D.support} (C : MMP.Mori.PrimeDivisor
    P.1.idealSheaf.subscheme)
    (y : P.1.idealSheaf.subscheme) :
    y ∈ C.support ↔ P.1.idealSheaf.subschemeι C.genericPoint ⤳ P.1.idealSheaf.subschemeι y := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure]
  exact (P.1.idealSheaf.subschemeι.isClosedEmbedding.toIsInducing.specializes_iff).symm

/-- A point of `E_P` lies on `curveDiv` exactly when its image in `W` is a specialization of
`η`. -/
theorem mem_support_curveDiv_iff (P : D.support) {η : W} (hη : IsDoubleCurve D η)
    (hP : P ∈ comps D η) (y : P.1.idealSheaf.subscheme) :
    y ∈ (curveDiv hsnc hdim P hη hP).support ↔ η ⤳ P.1.idealSheaf.subschemeι y := by
  rw [mem_support_iff_specializes, curveDiv_genericPoint]

/-- The curve over `η` on `E_P` lies on every other component through `η`. -/
theorem genericPoint_curveDiv_mem_comap (P : D.support) {η : W} (hη : IsDoubleCurve D η)
    (hP : P ∈ comps D η) {Q : D.support} (hQ : Q ∈ comps D η) :
    (curveDiv hsnc hdim P hη hP).genericPoint ∈
      (Q.1.idealSheaf.comap P.1.idealSheaf.subschemeι).support := by
  rw [MMP.Resolution.mem_support_comap_iff, curveDiv_genericPoint]
  exact mem_comps.1 hQ

include hsnc hdim in
/-- A curve of a two-dimensional component lying on another component is the curve over a double
curve. -/
theorem isDoubleCurve_of_mem_comap (P : D.support) {R : D.support} (hRP : R ≠ P)
    (C : MMP.Mori.PrimeDivisor P.1.idealSheaf.subscheme)
    (hC : C.genericPoint ∈ (R.1.idealSheaf.comap P.1.idealSheaf.subschemeι).support)
    (h2 : Order.krullDim P.1.idealSheaf.subscheme = 2) :
    IsDoubleCurve D (P.1.idealSheaf.subschemeι C.genericPoint) ∧
      P ∈ comps D (P.1.idealSheaf.subschemeι C.genericPoint) ∧
      R ∈ comps D (P.1.idealSheaf.subschemeι C.genericPoint) := by
  classical
  have hPm : P ∈ comps D (P.1.idealSheaf.subschemeι C.genericPoint) := by
    rw [mem_comps, ← range_subschemeι_eq]; exact ⟨_, rfl⟩
  have hRm : R ∈ comps D (P.1.idealSheaf.subschemeι C.genericPoint) := by
    rw [mem_comps]; exact (MMP.Resolution.mem_support_comap_iff _ _ _).1 hC
  refine ⟨⟨?_, ?_⟩, hPm, hRm⟩
  · rw [height_apply_of_isClosedEmbedding P.1.idealSheaf.subschemeι
      P.1.idealSheaf.subschemeι.isClosedEmbedding]
    exact height_genericPoint_primeDivisor h2 C
  · have hsub : ({P, R} : Finset D.support) ⊆ comps D (P.1.idealSheaf.subschemeι
      C.genericPoint) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hPm
      · exact hRm
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair (Ne.symm hRP)] at this

/-- A prime divisor of `E_P` whose generic point is a double curve is the curve over it. -/
theorem eq_curveDiv (P : D.support) (C : MMP.Mori.PrimeDivisor P.1.idealSheaf.subscheme)
    (hd : IsDoubleCurve D (P.1.idealSheaf.subschemeι C.genericPoint))
    (hP : P ∈ comps D (P.1.idealSheaf.subschemeι C.genericPoint)) :
    C = curveDiv hsnc hdim P hd hP :=
  AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (P.1.idealSheaf.subschemeι.isClosedEmbedding.injective
      (curveDiv_genericPoint hsnc hdim P hd hP).symm)

include hsnc hdim in
/-- Distinct curves over double curves of the same type are disjoint. -/
theorem disjoint_curveDiv (P : D.support) {η η' : W} (hη : IsDoubleCurve D η)
    (hη' : IsDoubleCurve D η') (hne : η ≠ η') (hS : comps D η = comps D η')
    (hP : P ∈ comps D η) :
    (curveDiv hsnc hdim P hη hP).support ∩ (curveDiv hsnc hdim P hη' (hS ▸ hP)).support = ∅ := by
  classical
  obtain ⟨A, B, hAB, hAB'⟩ := Finset.card_eq_two.1 (IsDoubleCurve.card_comps hsnc hdim hη)
  obtain ⟨Q, hQ, hQP⟩ : ∃ Q ∈ comps D η, Q ≠ P := by
    rw [hAB'] at hP ⊢
    simp only [Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with rfl | rfl
    · exact ⟨B, by simp, Ne.symm hAB⟩
    · exact ⟨A, by simp, hAB⟩
  rw [Set.eq_empty_iff_forall_notMem]
  rintro y ⟨hy, hy'⟩
  have h := eq_of_mem_support_of_comap hsnc hdim P ⟨Q, hQP⟩
    (genericPoint_curveDiv_mem_comap hsnc hdim P hη hP hQ)
    (genericPoint_curveDiv_mem_comap hsnc hdim P hη' (hS ▸ hP) (hS ▸ hQ)) hy hy'
  apply hne
  rw [← curveDiv_genericPoint hsnc hdim P hη hP, ← curveDiv_genericPoint hsnc hdim P hη'
      (hS ▸ hP), h]

include hsnc hdim in
/-- The common points of the curves over two double curves of different types through `P` are
the points over the triple points on both. -/
private theorem mem_inter_curveDiv_iff (P : D.support) {η η' : W} (hη : IsDoubleCurve D η)
    (hη' : IsDoubleCurve D η') (hP : P ∈ comps D η) (hP' : P ∈ comps D η')
    (hS : comps D η ≠ comps D η') (y : P.1.idealSheaf.subscheme) :
    y ∈ (curveDiv hsnc hdim P hη hP).support ∩ (curveDiv hsnc hdim P hη' hP').support ↔
      IsTriplePoint D (P.1.idealSheaf.subschemeι y) ∧ η ⤳ P.1.idealSheaf.subschemeι y ∧
        η' ⤳ P.1.idealSheaf.subschemeι y := by
  classical
  rw [Set.mem_inter_iff, mem_support_curveDiv_iff, mem_support_curveDiv_iff]
  refine ⟨fun ⟨h1, h2⟩ ↦ ⟨?_, h1, h2⟩, fun ⟨_, h1, h2⟩ ↦ ⟨h1, h2⟩⟩
  set x := P.1.idealSheaf.subschemeι y
  have hsub : comps D η ∪ comps D η' ⊆ comps D x :=
    Finset.union_subset (comps_subset_of_specializes h1) (comps_subset_of_specializes h2)
  have hA := IsDoubleCurve.card_comps hsnc hdim hη
  have hB := IsDoubleCurve.card_comps hsnc hdim hη'
  have hinter : (comps D η ∩ comps D η').card ≤ 1 := by
    by_contra hc
    push Not at hc
    have h2 : (comps D η ∩ comps D η').card = 2 := by
      have := Finset.card_le_card (Finset.inter_subset_left (s₁ := comps D η) (s₂ := comps D η'))
      omega
    apply hS
    have e1 := Finset.eq_of_subset_of_card_le (Finset.inter_subset_left (s₁ := comps D η)
      (s₂ := comps D η')) (by omega)
    have e2 := Finset.eq_of_subset_of_card_le (Finset.inter_subset_right (s₁ := comps D η)
      (s₂ := comps D η')) (by omega)
    rw [← e1, e2]
  have hunion := Finset.card_union_add_card_inter (comps D η) (comps D η')
  have h3 : 3 ≤ (comps D x).card := (by omega : 3 ≤ (comps D η ∪ comps D η').card).trans
    (Finset.card_le_card hsub)
  have hle := card_comps_le_coheight hsnc x
  have hle2 := height_add_coheight_le hdim x
  have hc3 : ((comps D x).card : ℕ∞) ≤ 3 := hle.trans (le_trans le_add_self hle2)
  have : (comps D x).card ≤ 3 := by exact_mod_cast hc3
  exact le_antisymm this h3

variable (hsm : IsSmoothScheme (W ↘ Spec (.of ℂ)))

include hsnc in
/-- A component is normal. -/
theorem isNormal_component (P : D.support) : IsNormal P.1.idealSheaf.subscheme := by
  have hsmE := isSmoothScheme_component hsnc P
  haveI := MMP.Resolution.Aux.smooth_of_isSmoothScheme' _ hsmE
  exact isNormal_of_smooth_over_field (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ))

/-- A proper component is a variety. -/
theorem isVariety_component (P : D.support)
    [IsProper (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ))] :
    MMP.Mori.IsVariety ℂ (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
  haveI := P.1.integral
  { }

include hsnc in
/-- A curve on a two-dimensional component has dimension at most one. -/
theorem topologicalKrullDim_curve_le (P : D.support)
    (h2 : Order.krullDim P.1.idealSheaf.subscheme = 2)
    (C : MMP.Mori.PrimeDivisor P.1.idealSheaf.subscheme) :
    topologicalKrullDim C.idealSheaf.subscheme ≤ 1 := by
  haveI := C.integral
  have hsmE := isSmoothScheme_component hsnc P
  exact Stacks.ResolutionOfSurfaces.topologicalKrullDim_subscheme_le_one
    (by rw [topologicalKrullDim_eq_krullDim', h2]) C.idealSheaf
    (MMP.Resolution.Aux.isEffectiveCartierDivisor_idealSheaf _ hsmE C)

include hsnc hdim in
/-- The curves on `E_P` over distinct double curves are distinct. -/
theorem curveDiv_ne (P : D.support) {η η' : W} (hη : IsDoubleCurve D η)
    (hη' : IsDoubleCurve D η') (hne : η ≠ η') (hP : P ∈ comps D η) (hP' : P ∈ comps D η') :
    curveDiv hsnc hdim P hη hP ≠ curveDiv hsnc hdim P hη' hP' := fun h ↦ hne (by
  rw [← curveDiv_genericPoint hsnc hdim P hη hP, ← curveDiv_genericPoint hsnc hdim P hη' hP', h])

include hsnc hdim hsm in
/-- **Curves of the same type do not meet**: `(C' · C) = 0` on `E_P` for distinct curves over
double curves of the same type. -/
private theorem degreeOn_curveDiv_eq_zero (P : D.support)
    [IsProper (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ))] {η η' : W} (hη : IsDoubleCurve D η)
    (hη' : IsDoubleCurve D η') (hne : η ≠ η') (hS : comps D η = comps D η')
    (hP : P ∈ comps D η) :
    haveI := isNormal_component hsnc P
    Divisor.degreeOn ℂ (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ))
      (curveDiv hsnc hdim P hη hP).idealSheaf.subschemeι
      (topologicalKrullDim_curve_le hsnc P (krullDim_eq_two_of_mem_comps hsnc hdim P hη hP) _)
      (Finsupp.single (curveDiv hsnc hdim P hη' (hS ▸ hP)) 1)
      (MMP.Fourfold.isCartier_of_isSmoothScheme (isSmoothScheme_component hsnc P) _) = 0 := by
  haveI := isNormal_component hsnc P
  have h2 := krullDim_eq_two_of_mem_comps hsnc hdim P hη hP
  have key := degreeOn_single_eq_finsum (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ))
    (isVariety_component P) (isSmoothScheme_component hsnc P)
    (by rw [topologicalKrullDim_eq_krullDim', h2])
    (curveDiv_ne hsnc hdim P hη hη' hne hP (hS ▸ hP))
    (topologicalKrullDim_curve_le hsnc P h2 _)
  rw [disjoint_curveDiv hsnc hdim P hη hη' hne hS hP, finsum_mem_empty] at key
  exact_mod_cast key

include hsnc hdim hsm in
/-- **Curves of different types meet transversally at the triple points**: `(C' · C)` on `E_P` is
the number of triple points on both double curves. -/
private theorem degreeOn_curveDiv_eq_ncard (P : D.support)
    [IsProper (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ))] {η η' : W} (hη : IsDoubleCurve D η)
    (hη' : IsDoubleCurve D η') (hS : comps D η ≠ comps D η')
    (hP : P ∈ comps D η) (hP' : P ∈ comps D η') :
    haveI := isNormal_component hsnc P
    (Divisor.degreeOn ℂ (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ))
      (curveDiv hsnc hdim P hη hP).idealSheaf.subschemeι
      (topologicalKrullDim_curve_le hsnc P (krullDim_eq_two_of_mem_comps hsnc hdim P hη hP) _)
      (Finsupp.single (curveDiv hsnc hdim P hη' hP') 1)
      (MMP.Fourfold.isCartier_of_isSmoothScheme (isSmoothScheme_component hsnc P) _) : ℚ) =
      ({t : W | IsTriplePoint D t ∧ η ⤳ t ∧ η' ⤳ t}.ncard : ℚ) := by
  classical
  haveI := isNormal_component hsnc P
  have h2 := krullDim_eq_two_of_mem_comps hsnc hdim P hη hP
  have hne : η ≠ η' := fun h ↦ hS (by rw [h])
  have hCC := curveDiv_ne hsnc hdim P hη hη' hne hP hP'
  have key := degreeOn_single_eq_finsum (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ))
    (isVariety_component P) (isSmoothScheme_component hsnc P)
    (by rw [topologicalKrullDim_eq_krullDim', h2]) hCC (topologicalKrullDim_curve_le hsnc P h2 _)
  rw [key]
  -- the two other components
  obtain ⟨A, B, hAB, hAB'⟩ := Finset.card_eq_two.1 (IsDoubleCurve.card_comps hsnc hdim hη)
  obtain ⟨Q, hQ, hQP, hSQ⟩ : ∃ Q ∈ comps D η, Q ≠ P ∧ comps D η = {P, Q} := by
    rw [hAB'] at hP ⊢
    simp only [Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with rfl | rfl
    · exact ⟨B, by simp, Ne.symm hAB, rfl⟩
    · exact ⟨A, by simp, hAB, Finset.pair_comm _ _⟩
  obtain ⟨A', B', hAB2, hAB2'⟩ := Finset.card_eq_two.1 (IsDoubleCurve.card_comps hsnc hdim hη')
  obtain ⟨R, hR, hRP, hSR⟩ : ∃ R ∈ comps D η', R ≠ P ∧ comps D η' = {P, R} := by
    rw [hAB2'] at hP' ⊢
    simp only [Finset.mem_insert, Finset.mem_singleton] at hP'
    rcases hP' with rfl | rfl
    · exact ⟨B', by simp, Ne.symm hAB2, rfl⟩
    · exact ⟨A', by simp, hAB2, Finset.pair_comm _ _⟩
  have hQR : (⟨Q, hQP⟩ : {R : D.support // R ≠ P}) ≠ ⟨R, hRP⟩ := by
    intro h
    apply hS
    rw [hSQ, hSR, show Q = R from congrArg Subtype.val h]
  have hloc : ∀ y ∈ (curveDiv hsnc hdim P hη hP).support ∩ (curveDiv hsnc hdim P hη' hP').support,
      (MMP.Mori.localIntersectionNumber (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) y
        (Finsupp.single (curveDiv hsnc hdim P hη hP) 1)
        (Finsupp.single (curveDiv hsnc hdim P hη' hP') 1) : ℚ) = 1 := by
    rintro y ⟨hy, hy'⟩
    rw [localIntersectionNumber_eq_one hsnc hQR
      (genericPoint_curveDiv_mem_comap hsnc hdim P hη hP hQ)
      (genericPoint_curveDiv_mem_comap hsnc hdim P hη' hP' hR) h2 hdim hy hy']
    rfl
  rw [finsum_mem_congr rfl hloc]
  have himage : P.1.idealSheaf.subschemeι ''
      ((curveDiv hsnc hdim P hη hP).support ∩ (curveDiv hsnc hdim P hη' hP').support) =
      {t : W | IsTriplePoint D t ∧ η ⤳ t ∧ η' ⤳ t} := by
    ext t
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (mem_inter_curveDiv_iff hsnc hdim P hη hη' hP hP' hS y).1 hy
    · rintro ⟨ht, h1, h2'⟩
      have htP : t ∈ Set.range P.1.idealSheaf.subschemeι := by
        rw [range_subschemeι_eq]
        exact mem_comps.1 (comps_subset_of_specializes h1 hP)
      obtain ⟨y, rfl⟩ := htP
      exact ⟨y, (mem_inter_curveDiv_iff hsnc hdim P hη hη' hP hP' hS y).2 ⟨ht, h1, h2'⟩, rfl⟩
  rw [← himage,
      Set.ncard_image_of_injective _ P.1.idealSheaf.subschemeι.isClosedEmbedding.injective]
  have hfin : ((curveDiv hsnc hdim P hη hP).support ∩
      (curveDiv hsnc hdim P hη' hP').support).Finite :=
    (isIntersectionNumber_finsum_localIntersectionNumber_of_ne
      (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) (isVariety_component P)
      (isSmoothScheme_component hsnc P) (by rw [topologicalKrullDim_eq_krullDim', h2]) hCC
      inferInstance).1
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_const, nsmul_eq_mul, mul_one,
    Set.ncard_eq_toFinset_card _ hfin]

omit [W.Over (Spec (.of ℂ))] [MMP.IsComplexScheme W] [IsLocallyNoetherian W] in
/-- On an integral scheme, a point of coheight zero is the generic point. -/
private theorem eq_genericPoint_of_coheight_eq_zero {X : Scheme.{0}} [IsIntegral X] {s : X}
    (hs : Order.coheight s = 0) : s = genericPoint X := by
  have hle : s ≤ genericPoint X := (genericPoint_spec X).specializes trivial
  exact (Specializes.antisymm (Order.coheight_eq_zero.mp hs hle) hle).eq

include hsnc hdim in
/-- The set of double curves of `D` is finite. -/
theorem finite_doubleCurve [∀ P : D.support, CompactSpace P.1.idealSheaf.subscheme] :
    {η : W | IsDoubleCurve D η}.Finite := by
  classical
  have hfin : ∀ P Q : D.support, Q ≠ P →
      {C : MMP.Mori.PrimeDivisor P.1.idealSheaf.subscheme |
        C.genericPoint ∈ (Q.1.idealSheaf.comap P.1.idealSheaf.subschemeι).support}.Finite := by
    intro P Q hQP
    haveI := P.1.integral
    haveI : IsNoetherian P.1.idealSheaf.subscheme := ⟨⟩
    refine MMP.Mori.finite_setOf_genericPoint_mem
      (Q.1.idealSheaf.comap P.1.idealSheaf.subschemeι).support.isClosed fun s hs h0 ↦ ?_
    rw [eq_genericPoint_of_coheight_eq_zero h0] at hs
    exact genericPoint_notMem_comap P ⟨Q, hQP⟩ hs
  refine (Set.finite_iUnion fun P : D.support ↦ Set.finite_iUnion fun Q : {Q : D.support // Q ≠ P} ↦
    ((hfin P Q.1 Q.2).image fun C ↦ P.1.idealSheaf.subschemeι C.genericPoint)).subset ?_
  intro η hη
  have h2 := hη.2
  obtain ⟨P, hP, Q, hQ, hPQ⟩ : ∃ P ∈ comps D η, ∃ Q ∈ comps D η, P ≠ Q := by
    by_contra hcon
    push Not at hcon
    obtain ⟨P, hP⟩ : (comps D η).Nonempty := Finset.card_pos.1 (by omega)
    have : comps D η ⊆ {P} := fun Q hQ ↦ Finset.mem_singleton.2 (hcon Q hQ P hP)
    have := Finset.card_le_card this
    simp at this
    omega
  simp only [Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq]
  refine ⟨P, ⟨Q, Ne.symm hPQ⟩, curveDiv hsnc hdim P hη hP,
    genericPoint_curveDiv_mem_comap hsnc hdim P hη hP hQ, curveDiv_genericPoint hsnc hdim P hη hP⟩

include hsnc hdim hsm in
/-- **There are finitely many triple points.** -/
private theorem finite_triplePoint [∀ P : D.support, IsProper (P.1.idealSheaf.subscheme ↘ Spec
    (.of ℂ))] :
    {t : W | IsTriplePoint D t}.Finite := by
  classical
  let Cv : (P : D.support) → Set (MMP.Mori.PrimeDivisor P.1.idealSheaf.subscheme) := fun P ↦
    {C : MMP.Mori.PrimeDivisor P.1.idealSheaf.subscheme | ∃ Q : D.support, Q ≠ P ∧
      C.genericPoint ∈ (Q.1.idealSheaf.comap P.1.idealSheaf.subschemeι).support}
  have hCv : ∀ P, (Cv P).Finite := by
    intro P
    haveI := P.1.integral
    haveI : CompactSpace P.1.idealSheaf.subscheme :=
      QuasiCompact.compactSpace_of_compactSpace (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ))
    haveI : IsNoetherian P.1.idealSheaf.subscheme := ⟨⟩
    refine (Set.finite_iUnion fun Q : {Q : D.support // Q ≠ P} ↦
      MMP.Mori.finite_setOf_genericPoint_mem
        (Q.1.1.idealSheaf.comap P.1.idealSheaf.subschemeι).support.isClosed fun s hs h0 ↦ ?_).subset
      ?_
    · rw [eq_genericPoint_of_coheight_eq_zero h0] at hs
      exact genericPoint_notMem_comap P Q hs
    · rintro C ⟨Q, hQ, hC⟩
      exact Set.mem_iUnion.2 ⟨⟨Q, hQ⟩, hC⟩
  have hinter : ∀ (P : D.support) (C C' : MMP.Mori.PrimeDivisor P.1.idealSheaf.subscheme),
      Order.krullDim P.1.idealSheaf.subscheme = 2 → C ≠ C' → (C.support ∩ C'.support).Finite := by
    intro P C C' h2 hCC
    haveI := isNormal_component hsnc P
    exact (isIntersectionNumber_finsum_localIntersectionNumber_of_ne
      (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) (isVariety_component P)
      (isSmoothScheme_component hsnc P) (by rw [topologicalKrullDim_eq_krullDim', h2]) hCC
      inferInstance).1
  refine (Set.finite_iUnion fun P : D.support ↦
    Set.Finite.biUnion (hCv P) fun C _ ↦ Set.Finite.biUnion (hCv P) fun C' _ ↦
      Set.finite_iUnion fun (h : Order.krullDim P.1.idealSheaf.subscheme = 2 ∧ C ≠ C') ↦
        ((hinter P C C' h.1 h.2).image P.1.idealSheaf.subschemeι)).subset ?_
  intro t ht
  obtain ⟨A, B, E, hAB, hAE, hBE, hABE⟩ := Finset.card_eq_three.1 (show
      (comps D t).card = 3 from ht)
  have hA : A ∈ comps D t := by rw [hABE]; simp
  have hB : B ∈ comps D t := by rw [hABE]; simp
  have hE : E ∈ comps D t := by rw [hABE]; simp
  obtain ⟨η, ⟨⟨hη, hηt⟩, hηc⟩, -⟩ := existsUnique_doubleCurve hsnc hdim ht hA hB hAB
  obtain ⟨η', ⟨⟨hη', hη't⟩, hη'c⟩, -⟩ := existsUnique_doubleCurve hsnc hdim ht hA hE hAE
  have hPη : A ∈ comps D η := by rw [hηc]; simp
  have hPη' : A ∈ comps D η' := by rw [hη'c]; simp
  have hS : comps D η ≠ comps D η' := by
    rw [hηc, hη'c]
    intro h
    have : B ∈ ({A, E} : Finset D.support) := h ▸ (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h1 | h1
    · exact hAB h1.symm
    · exact hBE h1
  have htA : t ∈ Set.range A.1.idealSheaf.subschemeι := by
    rw [range_subschemeι_eq]; exact mem_comps.1 hA
  obtain ⟨y, rfl⟩ := htA
  have hy := (mem_inter_curveDiv_iff hsnc hdim A hη hη' hPη hPη' hS y).2 ⟨ht, hηt, hη't⟩
  have hBA : B ≠ A := Ne.symm hAB
  have hEA : E ≠ A := Ne.symm hAE
  simp only [Set.mem_iUnion, Set.mem_image]
  refine ⟨A, curveDiv hsnc hdim A hη hPη, ⟨B, hBA,
    genericPoint_curveDiv_mem_comap hsnc hdim A hη hPη (by rw [hηc]; simp)⟩,
    curveDiv hsnc hdim A hη' hPη', ⟨E, hEA,
    genericPoint_curveDiv_mem_comap hsnc hdim A hη' hPη' (by rw [hη'c]; simp)⟩,
    ⟨krullDim_eq_two_of_mem_comps hsnc hdim A hη hPη,
      curveDiv_ne hsnc hdim A hη hη' (fun h ↦ hS (by rw [h])) hPη hPη'⟩, y, hy, rfl⟩

include hsnc hdim in
/-- **Transversality at a curve of `E_P ∩ E_R`.** A generator of the ideal of `E_R` at the generic
point of a curve of `E_P` lying on `E_R` restricts to a uniformizer of the local ring of `E_P`
along the curve. -/
private theorem irreducible_stalkMap_generator' {P : D.support} (R : {R : D.support // R ≠ P})
    (C : MMP.Mori.PrimeDivisor P.1.idealSheaf.subscheme)
    (hC : C.genericPoint ∈ (R.1.1.idealSheaf.comap P.1.idealSheaf.subschemeι).support)
    (g : W.presheaf.stalk (P.1.idealSheaf.subschemeι C.genericPoint))
    (hg : IdealSheafData.stalk R.1.1.idealSheaf (P.1.idealSheaf.subschemeι C.genericPoint) =
      Ideal.span {g}) :
    Irreducible ((P.1.idealSheaf.subschemeι.stalkMap C.genericPoint).hom g) := by
  have hsmE := isSmoothScheme_component hsnc P
  haveI := isNormal_component hsnc P
  have hCgen : C.genericPoint ∈ C.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have hmax : IdealSheafData.stalk C.idealSheaf C.genericPoint =
      IsLocalRing.maximalIdeal _ := by
    rw [← MMP.Resolution.Aux.primeOfSpecializes_genericPoint
      (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) hsmE C hCgen]
    change Ideal.comap _ _ = _
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  have hspan : Ideal.span {(P.1.idealSheaf.subschemeι.stalkMap C.genericPoint).hom g} =
      IsLocalRing.maximalIdeal _ := by
    rw [← hmax, stalk_idealSheaf_eq_stalk_comap hsnc hdim P R C hC hCgen,
      AlgebraicGeometry.IdealSheafData.stalk_comap, hg, Ideal.map_span, Set.image_singleton]
  haveI := C.isDiscreteValuationRing_localRing
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hspan.symm

omit [W.Over (Spec (.of ℂ))] [MMP.IsComplexScheme W] [IsLocallyNoetherian W] in
/-- The degree along a curve of a finite sum of Cartier divisors. -/
private theorem degreeOn_finset_sum {k : Type} [Field k] {X C : Scheme.{0}} (sX : X ⟶ Spec (.of k))
    [QuasiCompact sX] (i : C ⟶ X) [IsProper (i ≫ sX)] (hdim : topologicalKrullDim C ≤ 1)
    [IsLocallyNoetherian X] [IsNormal X] (hcart : ∀ B : Divisor X, B.IsCartier) {α : Type*}
    (s : Finset α) (f : α → Divisor X) :
    Divisor.degreeOn k sX i hdim (∑ a ∈ s, f a) (hcart _) =
      ∑ a ∈ s, Divisor.degreeOn k sX i hdim (f a) (hcart _) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact Divisor.degreeOn_zero' k sX i hdim
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih,
      Divisor.degreeOn_congr rfl (hcart _) ((hcart _).add (hcart _))]
    exact Divisor.degreeOn_add k sX i hdim _ _ _ _

open Classical in
/-- The degree on the curve over `η` of the curve over `η'`, on a component `E_P` through both;
zero if `P` is not on both. -/
private noncomputable def curveDeg (P : D.support) [IsProper (P.1.idealSheaf.subscheme ↘ Spec
    (.of ℂ))]
    (η η' : W) : ℤ :=
  if h : IsDoubleCurve D η ∧ P ∈ comps D η ∧ IsDoubleCurve D η' ∧ P ∈ comps D η' then
    haveI := isNormal_component hsnc P
    Divisor.degreeOn ℂ (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ))
      (curveDiv hsnc hdim P h.1 h.2.1).idealSheaf.subschemeι
      (topologicalKrullDim_curve_le hsnc P (krullDim_eq_two_of_mem_comps hsnc hdim P h.1 h.2.1) _)
      (Finsupp.single (curveDiv hsnc hdim P h.2.2.1 h.2.2.2) 1)
      (MMP.Fourfold.isCartier_of_isSmoothScheme (isSmoothScheme_component hsnc P) _)
  else 0

open Classical in
private theorem curveDeg_eq (P : D.support) [IsProper (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ))]
    {η η' : W} (hη : IsDoubleCurve D η) (hP : P ∈ comps D η) (hη' : IsDoubleCurve D η')
    (hP' : P ∈ comps D η') :
    haveI := isNormal_component hsnc P
    curveDeg hsnc hdim P η η' = Divisor.degreeOn ℂ (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ))
      (curveDiv hsnc hdim P hη hP).idealSheaf.subschemeι
      (topologicalKrullDim_curve_le hsnc P (krullDim_eq_two_of_mem_comps hsnc hdim P hη hP) _)
      (Finsupp.single (curveDiv hsnc hdim P hη' hP') 1)
      (MMP.Fourfold.isCartier_of_isSmoothScheme (isSmoothScheme_component hsnc P) _) := by
  rw [curveDeg, dif_pos ⟨hη, hP, hη', hP'⟩]

omit [MMP.IsComplexScheme W] [IsLocallyNoetherian W] in
private theorem isProper_curve_comp (P : D.support) [IsProper (P.1.idealSheaf.subscheme ↘ Spec
    (.of ℂ))]
    (C : MMP.Mori.PrimeDivisor P.1.idealSheaf.subscheme) :
    IsProper ((C.idealSheaf.subschemeι ≫ P.1.idealSheaf.subschemeι) ≫ W ↘ Spec (.of ℂ)) := by
  haveI : IsProper (P.1.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ)) :=
    ‹IsProper (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ))›
  rw [Category.assoc]; infer_instance

open Classical in
include hsnc hdim hsm in
/-- **The degree of `E_R` along a curve of `E_P`** is the sum of the intersection numbers on `E_P`
with the curves of `E_P ∩ E_R`. -/
private theorem degreeOn_single_comp_eq_sum [IsNormal W] (P : D.support)
    [IsProper (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ))] {η : W} (hη : IsDoubleCurve D η)
    (hP : P ∈ comps D η) (R : D.support) (hRP : R ≠ P) (F : Finset W)
    (hF : ∀ η', η' ∈ F ↔ IsDoubleCurve D η' ∧ comps D η' = {P, R}) :
    haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (W ↘ Spec (.of ℂ))
    haveI := isProper_curve_comp P (curveDiv hsnc hdim P hη hP)
    Divisor.degreeOn ℂ (W ↘ Spec (.of ℂ))
      ((curveDiv hsnc hdim P hη hP).idealSheaf.subschemeι ≫ P.1.idealSheaf.subschemeι)
      (topologicalKrullDim_curve_le hsnc P (krullDim_eq_two_of_mem_comps hsnc hdim P hη hP) _)
      (Finsupp.single R.1 1) (MMP.Fourfold.isCartier_of_isSmoothScheme hsm _) =
      ∑ η' ∈ F, curveDeg hsnc hdim P η η' := by
  classical
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (W ↘ Spec (.of ℂ))
  haveI := isNormal_component hsnc P
  haveI := P.1.integral
  haveI : CompactSpace P.1.idealSheaf.subscheme :=
    QuasiCompact.compactSpace_of_compactSpace (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ))
  have h2 := krullDim_eq_two_of_mem_comps hsnc hdim P hη hP
  set C := curveDiv hsnc hdim P hη hP with hCdef
  have hdimC := topologicalKrullDim_curve_le hsnc P h2 C
  have hRc : Divisor.IsCartier (Finsupp.single R.1 1 : Divisor W) :=
    MMP.Fourfold.isCartier_of_isSmoothScheme hsm _
  have hmemR : ∀ x : P.1.idealSheaf.subscheme, P.1.idealSheaf.subschemeι x ∈
      DivisorWithCoeffs.supp (Finsupp.single R.1 (1 : ℤ)) → P.1.idealSheaf.subschemeι x ∈
          R.1.support :=
    fun x hx ↦ DivisorWithCoeffs.supp_single_le R.1 (1 : ℤ) hx
  have hB : ∀ Z : irreducibleComponents P.1.idealSheaf.subscheme,
      P.1.idealSheaf.subschemeι (componentGenericPoint _ Z) ∉
        DivisorWithCoeffs.supp (Finsupp.single R.1 (1 : ℤ)) := by
    intro Z hZ
    have hgen : componentGenericPoint P.1.idealSheaf.subscheme Z =
        genericPoint P.1.idealSheaf.subscheme :=
      eq_genericPoint_of_coheight_eq_zero (Order.coheight_eq_zero.2 fun z hz ↦ by
        have h1 := (isGenericPoint_componentGenericPoint _ Z)
        have hZu : Z.1 = Set.univ := Set.eq_univ_of_univ_subset
          (Z.2.2 (IrreducibleSpace.isIrreducible_univ _) (Set.subset_univ _))
        have hz' : z ∈ Z.1 := hZu ▸ trivial
        exact h1.specializes hz')
    have := hmemR _ hZ
    rw [hgen] at this
    exact genericPoint_notMem_comap P ⟨R, hRP⟩
      ((MMP.Resolution.mem_support_comap_iff _ _ _).2 this)
  haveI := isProper_curve_comp P C
  have hpull := degreeOn_pullback_divisor (k := ℂ) (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ))
    (W ↘ Spec (.of ℂ)) P.1.idealSheaf.subschemeι rfl (Finsupp.single R.1 1) hRc hB
    C.idealSheaf.subschemeι hdimC
  rw [← hpull]
  -- the pulled-back divisor is the sum of the curves of `E_P ∩ E_R`
  let g : W → Divisor P.1.idealSheaf.subscheme := fun η' ↦
    if h : IsDoubleCurve D η' ∧ P ∈ comps D η' then
      Finsupp.single (curveDiv hsnc hdim P h.1 h.2) 1 else 0
  have hsmE := isSmoothScheme_component hsnc P
  have hpeq : Divisor.pullback (f := P.1.idealSheaf.subschemeι) (Finsupp.single R.1
      (1 : ℤ)) hRc hB =
      ∑ η' ∈ F, g η' := by
    refine DivisorWithCoeffs.ext' fun C' ↦ ?_
    rw [coeff_pullback_single hsm _ R.1 hRc hB C' (fun hy g hg ↦
      irreducible_stalkMap_generator' hsnc hdim ⟨R, hRP⟩ C'
        ((MMP.Resolution.mem_support_comap_iff _ _ _).2 hy) g hg)]
    rw [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]
    by_cases hy : P.1.idealSheaf.subschemeι C'.genericPoint ∈ R.1.support
    · rw [if_pos hy]
      have hC' : C'.genericPoint ∈ (R.1.idealSheaf.comap P.1.idealSheaf.subschemeι).support :=
        (MMP.Resolution.mem_support_comap_iff _ _ _).2 hy
      obtain ⟨hd, hPm, hRm⟩ := isDoubleCurve_of_mem_comap hsnc hdim P hRP C' hC' h2
      have hcomps : comps D (P.1.idealSheaf.subschemeι C'.genericPoint) = {P, R} := by
        symm
        refine Finset.eq_of_subset_of_card_le (fun x hx ↦ ?_) ?_
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hPm
          · exact hRm
        · rw [IsDoubleCurve.card_comps hsnc hdim hd, Finset.card_pair (Ne.symm hRP)]
      have hmemF := (hF _).2 ⟨hd, hcomps⟩
      rw [Finset.sum_eq_single (P.1.idealSheaf.subschemeι C'.genericPoint)]
      · simp only [g, dif_pos (And.intro hd hPm)]
        rw [← eq_curveDiv hsnc hdim P C' hd hPm, Finsupp.single_eq_same]
      · intro η' _ hne
        simp only [g]
        split_ifs with h
        · rw [Finsupp.single_apply, if_neg]
          intro heq
          apply hne
          rw [← heq, curveDiv_genericPoint]
        · rfl
      · intro h
        exact absurd hmemF h
    · rw [if_neg hy]
      refine (Finset.sum_eq_zero fun η' hη' ↦ ?_).symm
      simp only [g]
      split_ifs with h
      · rw [Finsupp.single_apply, if_neg]
        intro heq
        apply hy
        rw [← heq, curveDiv_genericPoint]
        have := ((hF η').1 hη').2
        exact mem_comps.1 (this ▸ (by simp : R ∈ ({P, R} : Finset D.support)))
      · rfl
  rw [Divisor.degreeOn_congr hpeq _ (MMP.Fourfold.isCartier_of_isSmoothScheme hsmE _),
    degreeOn_finset_sum _ _ _ (MMP.Fourfold.isCartier_of_isSmoothScheme hsmE)]
  refine Finset.sum_congr rfl fun η' hη' ↦ ?_
  obtain ⟨hd', hc'⟩ := (hF η').1 hη'
  have hP' : P ∈ comps D η' := by rw [hc']; simp
  simp only [g, dif_pos (And.intro hd' hP')]
  rw [curveDeg_eq hsnc hdim P hη hP hd' hP']

omit [W.Over (Spec (.of ℂ))] [MMP.IsComplexScheme W] [IsLocallyNoetherian W] in
/-- The ideal sheaf of a quasi-compact morphism from a reduced scheme is the vanishing ideal of
the closure of its image. -/
private theorem ker_eq_vanishingIdeal' {X Y : Scheme.{0}} (f : Y ⟶ X) [IsReduced Y] [QuasiCompact
    f] :
    f.ker = Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure
        (Set.range f)) := by
  rw [← Set.image_univ, ← Scheme.IdealSheafData.map_bot]
  have := Scheme.IdealSheafData.map_vanishingIdeal f ⊤
  rwa [Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot] at this

omit [W.Over (Spec (.of ℂ))] [MMP.IsComplexScheme W] [IsLocallyNoetherian W] in
/-- **The degree along a curve depends only on its ideal sheaf.** -/
private theorem degreeOn_eq_of_ker_eq {k : Type} [Field k] {X C C' : Scheme.{0}} (sX : X ⟶ Spec
    (.of k))
    (i : C ⟶ X) (i' : C' ⟶ X) [IsClosedImmersion i] [IsClosedImmersion i'] (h : i.ker = i'.ker)
    [IsProper (i ≫ sX)] [IsProper (i' ≫ sX)] (hdim : topologicalKrullDim C ≤ 1)
    (hdim' : topologicalKrullDim C' ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    MMP.Mori.degreeOn k sX i hdim L = MMP.Mori.degreeOn k sX i' hdim' L := by
  haveI := IsClosedImmersion.isIso_lift i' i h.symm
  set e := IsClosedImmersion.lift i' i h.symm.le
  have he : e ≫ i' = i := IsClosedImmersion.lift_fac i' i h.symm.le
  rw [MMP.Mori.degreeOn, MMP.Mori.degreeOn]
  let e1 : (Scheme.Modules.pullback i).obj L ≅
      (Scheme.Modules.pullback e).obj ((Scheme.Modules.pullback i').obj L) :=
    (Scheme.Modules.pullbackCongr he.symm).app L ≪≫
      ((Scheme.Modules.pullbackComp e i').symm.app L)
  rw [invertibleCurveDegree_eq_of_iso k (i ≫ sX) hdim e1]
  haveI : IsProper (e ≫ i' ≫ sX) := by rw [← Category.assoc, he]; infer_instance
  rw [invertibleCurveDegree_congr_structure (show i ≫ sX = e ≫ i' ≫ sX by
    rw [← he, Category.assoc]) hdim]
  exact invertibleCurveDegree_pullback_of_isIso e (i' ≫ sX) hdim hdim' _

omit [W.Over (Spec (.of ℂ))] [MMP.IsComplexScheme W] [IsLocallyNoetherian W] in
/-- **An ample invertible sheaf has positive degree on every integral proper curve** mapping to
the scheme by a closed immersion. -/
theorem degreeOn_pos_of_isAmple {k : Type} [Field k] {X C : Scheme.{0}} (sX : X ⟶ Spec
    (.of k))
    (i : C ⟶ X) [IsClosedImmersion i] [IsProper (i ≫ sX)] [IsIntegral C]
    (hdim : topologicalKrullDim C = 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (hL : Stacks.Ample.IsAmple X L) :
    0 < MMP.Mori.degreeOn k sX i hdim.le L := by
  have hL' := (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple X L).2 hL
  exact invertibleCurveDegree_pullback_pos_of_isAmple_of_isAffineHom k (i ≫ sX) hdim i L hL'

omit [MMP.IsComplexScheme W] [IsLocallyNoetherian W] in
/-- The ideal sheaf in `W` of the curve over a double curve `η`, read on a component through
`η`, is the vanishing ideal of the closure of `η`. -/
private theorem ker_curveDiv_comp (P : D.support) (C : MMP.Mori.PrimeDivisor
    P.1.idealSheaf.subscheme) :
    (C.idealSheaf.subschemeι ≫ P.1.idealSheaf.subschemeι).ker =
      Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure {P.1.idealSheaf.subschemeι C.genericPoint}) := by
  haveI := C.integral
  rw [ker_eq_vanishingIdeal']
  congr 1
  apply TopologicalSpace.Closeds.ext
  simp only [TopologicalSpace.Closeds.coe_closure]
  have hr : Set.range (C.idealSheaf.subschemeι ≫ P.1.idealSheaf.subschemeι) =
      P.1.idealSheaf.subschemeι '' Set.range C.idealSheaf.subschemeι := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, ⟨y, rfl⟩, (Scheme.Hom.comp_apply _ _ _).symm⟩
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨y, Scheme.Hom.comp_apply _ _ _⟩
  rw [hr, Scheme.IdealSheafData.range_subschemeι,
    show (C.idealSheaf.support : Set _) = C.support from rfl,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    P.1.idealSheaf.subschemeι.isClosedEmbedding.closure_image_eq, closure_closure,
    ← P.1.idealSheaf.subschemeι.isClosedEmbedding.closure_image_eq, Set.image_singleton]

include hsnc hdim in
/-- The degree along a double curve does not depend on the component it is read on. -/
private theorem degreeOn_curveDiv_comp_eq [IsNormal W] (P Q : D.support)
    [IsProper (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ))]
    [IsProper (Q.1.idealSheaf.subscheme ↘ Spec (.of ℂ))] {η : W} (hη : IsDoubleCurve D η)
    (hP : P ∈ comps D η) (hQ : Q ∈ comps D η) (L : W.Modules)
    [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L] :
    haveI := isProper_curve_comp P (curveDiv hsnc hdim P hη hP)
    haveI := isProper_curve_comp Q (curveDiv hsnc hdim Q hη hQ)
    MMP.Mori.degreeOn ℂ (W ↘ Spec (.of ℂ))
      ((curveDiv hsnc hdim P hη hP).idealSheaf.subschemeι ≫ P.1.idealSheaf.subschemeι)
      (topologicalKrullDim_curve_le hsnc P (krullDim_eq_two_of_mem_comps hsnc hdim P hη hP) _) L =
    MMP.Mori.degreeOn ℂ (W ↘ Spec (.of ℂ))
      ((curveDiv hsnc hdim Q hη hQ).idealSheaf.subschemeι ≫ Q.1.idealSheaf.subschemeι)
      (topologicalKrullDim_curve_le hsnc Q (krullDim_eq_two_of_mem_comps hsnc hdim Q hη hQ) _)
          L := by
  haveI := isProper_curve_comp P (curveDiv hsnc hdim P hη hP)
  haveI := isProper_curve_comp Q (curveDiv hsnc hdim Q hη hQ)
  refine degreeOn_eq_of_ker_eq _ _ _ ?_ _ _ L
  rw [ker_curveDiv_comp, ker_curveDiv_comp, curveDiv_genericPoint, curveDiv_genericPoint]

include hsnc hdim hsm in
/-- **The antiample divisor has negative degree on the double curves**: `(D · C) < 0`, as
`∑_R m_R (E_R · C)`. -/
private theorem sum_coeff_mul_degreeOn_neg [IsNormal W]
    [Stacks.Ample.IsInvertibleModule W (-D).divisorialSheaf]
    (hample : ∀ P ∈ D.support, Stacks.Ample.IsAmple P.idealSheaf.subscheme
      ((Scheme.Modules.pullback P.idealSheaf.subschemeι).obj (-D).divisorialSheaf))
    (P : D.support) [IsProper (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ))] {η : W}
    (hη : IsDoubleCurve D η) (hP : P ∈ comps D η) :
    haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (W ↘ Spec (.of ℂ))
    haveI := isProper_curve_comp P (curveDiv hsnc hdim P hη hP)
    ∑ R : D.support, D.coeff R.1 * Divisor.degreeOn ℂ (W ↘ Spec (.of ℂ))
      ((curveDiv hsnc hdim P hη hP).idealSheaf.subschemeι ≫ P.1.idealSheaf.subschemeι)
      (topologicalKrullDim_curve_le hsnc P (krullDim_eq_two_of_mem_comps hsnc hdim P hη hP) _)
      (Finsupp.single R.1 1) (MMP.Fourfold.isCartier_of_isSmoothScheme hsm _) < 0 := by
  classical
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (W ↘ Spec (.of ℂ))
  set C := curveDiv hsnc hdim P hη hP with hCdef
  haveI := isProper_curve_comp P C
  have h2 := krullDim_eq_two_of_mem_comps hsnc hdim P hη hP
  have hdimC := topologicalKrullDim_curve_le hsnc P h2 C
  have hcart : ∀ B : Divisor W, B.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm
  -- `D = ∑ m_R E_R`
  have hDsum : D = ∑ R ∈ D.support, D.coeff R • (Finsupp.single R 1 : Divisor W) := by
    conv_lhs => rw [← Finsupp.sum_single D]
    refine Finset.sum_congr rfl fun R _ ↦ ?_
    rw [Finsupp.smul_single_one]
    rfl
  have hdeg : Divisor.degreeOn ℂ (W ↘ Spec (.of ℂ)) (C.idealSheaf.subschemeι ≫
      P.1.idealSheaf.subschemeι) hdimC D (hcart D) =
      ∑ R : D.support, D.coeff R.1 * Divisor.degreeOn ℂ (W ↘ Spec (.of ℂ))
        (C.idealSheaf.subschemeι ≫ P.1.idealSheaf.subschemeι) hdimC (Finsupp.single R.1 1)
        (hcart _) := by
    rw [Divisor.degreeOn_congr hDsum _ (hcart _), degreeOn_finset_sum _ _ _ hcart,
      ← Finset.sum_coe_sort D.support]
    refine Finset.sum_congr rfl fun R _ ↦ ?_
    rw [Divisor.degreeOn_congr rfl (hcart _) ((hcart _).zsmul _),
      MMP.Fourfold.degreeOn_zsmul (W ↘ Spec (.of ℂ)) _ hdimC _ (hcart _)]
  rw [← hdeg]
  -- the degree of `-D` is positive by ampleness
  have hpos : 0 < Divisor.degreeOn ℂ (W ↘ Spec (.of ℂ)) (C.idealSheaf.subschemeι ≫
      P.1.idealSheaf.subschemeι) hdimC (-D) (hcart _) := by
    haveI := C.integral
    have hamp := hample P.1 P.2
    have hpb := degreeOn_pullback_eq_degreeOn_comp (k := ℂ)
      (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) (W ↘ Spec (.of ℂ)) P.1.idealSheaf.subschemeι
      C.idealSheaf.subschemeι rfl hdimC (-D).divisorialSheaf
    change 0 < MMP.Mori.degreeOn ℂ (W ↘ Spec (.of ℂ))
      (C.idealSheaf.subschemeι ≫ P.1.idealSheaf.subschemeι) hdimC (-D).divisorialSheaf
    rw [← hpb]
    exact degreeOn_pos_of_isAmple (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ))
      C.idealSheaf.subschemeι (topologicalKrullDim_primeDivisor_eq h2 C) _ hamp
  have hneg := MMP.Mori.Divisor.degreeOn_neg' ℂ (W ↘ Spec (.of ℂ))
    (C.idealSheaf.subschemeι ≫ P.1.idealSheaf.subschemeι) hdimC D (hcart D)
  rw [Divisor.degreeOn_congr rfl (hcart _) (hcart D).neg] at hpos
  omega

/-- The generic point of a curve on a two-dimensional component has delta-dimension one. -/
theorem relativeDimension_genericPoint_curve (P : D.support)
    (h2 : Order.krullDim P.1.idealSheaf.subscheme = 2)
    (C : MMP.Mori.PrimeDivisor P.1.idealSheaf.subscheme) :
    Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) C.genericPoint = ((1 : ℕ) : ℤ) := by
  haveI := isIntegral_component P
  haveI := locallyOfFiniteType_component P
  refine Stacks.Intersection.ExteriorProductProjections.relativeDimension_eq_of_topologicalKrullDim_closure
    ℂ _ _ 1 ?_
  rw [AlgebraicGeometry.topologicalKrullDim_closure_singleton_eq_height,
    height_genericPoint_primeDivisor h2 C]
  rfl

include hsnc hdim in
/-- **A point of delta-dimension one of `E_P` lying on another component is the generic point of
the curve over a double curve.** -/
theorem exists_eq_genericPoint_curveDiv (P : D.support) (y : P.1.idealSheaf.subscheme)
    (hy : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) y = ((1 : ℕ) : ℤ))
    {Q : D.support} (hQP : Q ≠ P) (hQ : P.1.idealSheaf.subschemeι y ∈ Q.1.support) :
    ∃ (hη : IsDoubleCurve D (P.1.idealSheaf.subschemeι y))
      (hP : P ∈ comps D (P.1.idealSheaf.subschemeι y)),
      y = (curveDiv hsnc hdim P hη hP).genericPoint := by
  classical
  haveI := locallyOfFiniteType_component P
  have hPm : P ∈ comps D (P.1.idealSheaf.subschemeι y) := by
    rw [mem_comps, ← range_subschemeι_eq]; exact ⟨_, rfl⟩
  have hQm : Q ∈ comps D (P.1.idealSheaf.subschemeι y) := mem_comps.2 hQ
  have hh : Order.height y = 1 := by
    have h1 := Stacks.Chow.topologicalKrullDim_closure_singleton_eq ℂ
      (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) y
    rw [AlgebraicGeometry.topologicalKrullDim_closure_singleton_eq_height, hy,
      Int.toNat_natCast] at h1
    exact_mod_cast h1
  have hη : IsDoubleCurve D (P.1.idealSheaf.subschemeι y) := by
    refine ⟨?_, ?_⟩
    · rw [height_apply_of_isClosedEmbedding P.1.idealSheaf.subschemeι
        P.1.idealSheaf.subschemeι.isClosedEmbedding, hh]
    · have hsub : ({P, Q} : Finset D.support) ⊆ comps D (P.1.idealSheaf.subschemeι y) := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hPm
        · exact hQm
      have := Finset.card_le_card hsub
      rwa [Finset.card_pair (Ne.symm hQP)] at this
  exact ⟨hη, hPm, (P.1.idealSheaf.subschemeι.isClosedEmbedding.injective
    (curveDiv_genericPoint hsnc hdim P hη hPm)).symm⟩

/-- The generic point of the curve of `E_P` over a double curve through `P`. -/
noncomputable def curvePoint (P : D.support) {η : W} (hη : IsDoubleCurve D η)
    (hP : P ∈ comps D η) : P.1.idealSheaf.subscheme :=
  (curveDiv hsnc hdim P hη hP).genericPoint

/-- The point `curvePoint` has delta-dimension one. -/
theorem relativeDimension_curvePoint (P : D.support) {η : W} (hη : IsDoubleCurve D η)
    (hP : P ∈ comps D η) :
    Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) (curvePoint hsnc hdim P hη hP) =
        ((1 : ℕ) : ℤ) :=
  relativeDimension_genericPoint_curve P (krullDim_eq_two_of_mem_comps hsnc hdim P hη hP) _

/-- The point `curvePoint` determines the double curve. -/
theorem curvePoint_injective (P : D.support) {η η' : W} (hη : IsDoubleCurve D η)
    (hP : P ∈ comps D η) (hη' : IsDoubleCurve D η') (hP' : P ∈ comps D η')
    (h : curvePoint hsnc hdim P hη hP = curvePoint hsnc hdim P hη' hP') : η = η' := by
  rw [← curveDiv_genericPoint hsnc hdim P hη hP, ← curveDiv_genericPoint hsnc hdim P hη' hP']
  exact congrArg P.1.idealSheaf.subschemeι.base h

open Classical in
include hsnc hdim in
/-- **A rational curve cycle on `E_P` supported on the double locus** is a combination of the
generic points of the curves over the double curves through `P`. -/
theorem eq_sum_curvePoint (P : D.support) (β : P.1.idealSheaf.subscheme →₀ ℚ)
    (hβ : ∀ x ∈ β.support,
      Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) x = ((1 : ℕ) : ℤ) ∧
      ∃ Q : D.support, Q ≠ P ∧ P.1.idealSheaf.subschemeι x ∈ Q.1.support)
    (F : Finset W) (hF : ∀ η, η ∈ F ↔ IsDoubleCurve D η ∧ P ∈ comps D η) :
    β = ∑ η ∈ F, if h : IsDoubleCurve D η ∧ P ∈ comps D η then
      β (curvePoint hsnc hdim P h.1 h.2) • Finsupp.single (curvePoint hsnc hdim P h.1 h.2) 1
    else 0 := by
  ext y
  rw [Finsupp.finset_sum_apply]
  by_cases hy : y ∈ β.support
  · obtain ⟨hy1, Q, hQP, hQ⟩ := hβ y hy
    obtain ⟨hη, hP, hyc⟩ := exists_eq_genericPoint_curveDiv hsnc hdim P y hy1 hQP hQ
    have hVc : y = curvePoint hsnc hdim P hη hP := hyc
    rw [Finset.sum_eq_single (P.1.idealSheaf.subschemeι y)]
    · rw [dif_pos ⟨hη, hP⟩, ← hVc, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul,
        mul_one]
    · intro η' _ hne
      split_ifs with h
      · rw [Finsupp.smul_apply, Finsupp.single_apply, if_neg, smul_zero]
        intro heq
        apply hne
        rw [hVc] at heq
        exact curvePoint_injective hsnc hdim P h.1 h.2 hη hP heq
      · rfl
    · exact fun h ↦ absurd ((hF _).2 ⟨hη, hP⟩) h
  · rw [Finsupp.notMem_support_iff.1 hy]
    refine (Finset.sum_eq_zero fun η' _ ↦ ?_).symm
    split_ifs with h
    · rw [Finsupp.smul_apply, Finsupp.single_apply]
      split_ifs with heq
      · rw [heq, Finsupp.notMem_support_iff.1 hy, zero_smul]
      · rw [smul_zero]
    · rfl

open Classical in
include hsnc hdim in
/-- **The cycles on the two branches of a double curve are opposite** when their push-forwards to
`W` cancel. -/
private theorem coeff_add_coeff_eq_zero_of_sum
    (β : ∀ P : D.support, P.1.idealSheaf.subscheme →₀ ℚ)
    (hsum : ∑ P, Finsupp.mapDomain P.1.idealSheaf.subschemeι.base (β P) = 0)
    {η : W} (hη : IsDoubleCurve D η) {P Q : D.support} (hPQ : P ≠ Q)
    (hP : P ∈ comps D η) (hQ : Q ∈ comps D η) (hS : comps D η = {P, Q}) :
    β P (curvePoint hsnc hdim P hη hP) + β Q (curvePoint hsnc hdim Q hη hQ) = 0 := by
  have hval : ∀ (R : D.support) (hR : R ∈ comps D η),
      Finsupp.mapDomain R.1.idealSheaf.subschemeι.base (β R) η =
        β R (curvePoint hsnc hdim R hη hR) := by
    intro R hR
    conv_lhs => rw [← curveDiv_genericPoint hsnc hdim R hη hR]
    exact Finsupp.mapDomain_apply_of_injective R.1.idealSheaf.subschemeι.isClosedEmbedding.injective _ _
  have h := congrArg (fun α : W →₀ ℚ ↦ α η) hsum
  simp only [Finsupp.finset_sum_apply, Finsupp.coe_zero, Pi.zero_apply] at h
  rw [Fintype.sum_eq_add P Q hPQ] at h
  · rwa [hval P hP, hval Q hQ] at h
  · rintro R ⟨hRP, hRQ⟩
    apply Finsupp.mapDomain_notin_range
    rintro ⟨y, hy⟩
    have hRm : R ∈ comps D η := by
      rw [mem_comps, ← hy, ← range_subschemeι_eq]; exact ⟨_, rfl⟩
    rw [hS] at hRm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hRm
    rcases hRm with h | h
    · exact hRP h
    · exact hRQ h

open Classical in
include hsnc hdim in
/-- A rational curve cycle supported on the double locus vanishes when its coefficients at the
generic points of the curves over the double curves vanish. -/
private theorem eq_zero_of_coeff_curvePoint_eq_zero (P : D.support)
    (β : P.1.idealSheaf.subscheme →₀ ℚ)
    (hβ : ∀ x ∈ β.support,
      Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) x = ((1 : ℕ) : ℤ) ∧
      ∃ Q : D.support, Q ≠ P ∧ P.1.idealSheaf.subschemeι x ∈ Q.1.support)
    (F : Finset W) (hF : ∀ η, η ∈ F ↔ IsDoubleCurve D η ∧ P ∈ comps D η)
    (hzero : ∀ η (hη : IsDoubleCurve D η) (hP : P ∈ comps D η),
      β (curvePoint hsnc hdim P hη hP) = 0) : β = 0 := by
  rw [eq_sum_curvePoint hsnc hdim P β hβ F hF]
  refine Finset.sum_eq_zero fun η _ ↦ ?_
  split_ifs with h
  · rw [hzero η h.1 h.2, zero_smul]
  · rfl

include hsnc hdim in
/-- **The curves over the double curves are smooth**: along such a curve the component `E_P` is
cut out by one regular parameter of the smooth surface. -/
theorem isSmoothScheme_curveDiv (P : D.support) {η : W} (hη : IsDoubleCurve D η)
    (hP : P ∈ comps D η) :
    IsSmoothScheme ((curveDiv hsnc hdim P hη hP).idealSheaf.subscheme ↘ Spec (.of ℂ)) := by
  classical
  set C := curveDiv hsnc hdim P hη hP with hCdef
  haveI := C.integral
  haveI : LocallyOfFiniteType (C.idealSheaf.subscheme ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (C.idealSheaf.subschemeι ≫ P.1.idealSheaf.subscheme ↘ Spec (.of ℂ))
    infer_instance
  haveI : IsLocallyNoetherian C.idealSheaf.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (C.idealSheaf.subscheme ↘ Spec (.of ℂ))
  obtain ⟨A, B, hAB, hAB'⟩ := Finset.card_eq_two.1 (IsDoubleCurve.card_comps hsnc hdim hη)
  obtain ⟨Q, hQ, hQP⟩ : ∃ Q ∈ comps D η, Q ≠ P := by
    rw [hAB'] at hP ⊢
    simp only [Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with rfl | rfl
    · exact ⟨B, by simp, Ne.symm hAB⟩
    · exact ⟨A, by simp, hAB⟩
  have hCQ := genericPoint_curveDiv_mem_comap hsnc hdim P hη hP hQ
  have hreg : ∀ y : C.idealSheaf.subscheme,
      IsRegularLocalRing (C.idealSheaf.subscheme.presheaf.stalk y) := by
    intro y
    have hy : C.idealSheaf.subschemeι y ∈ C.support := by
      rw [show (C.support : Set _) = Set.range C.idealSheaf.subschemeι from
        (Scheme.IdealSheafData.range_subschemeι _).symm]
      exact ⟨y, rfl⟩
    have hgy := MMP.Resolution.Aux.genericPoint_specializes_of_mem_support C hy
    have hyQ : C.idealSheaf.subschemeι y ∈
        (Q.1.idealSheaf.comap P.1.idealSheaf.subschemeι).support :=
      hgy.mem_closed (Q.1.idealSheaf.comap P.1.idealSheaf.subschemeι).support.isClosed hCQ
    obtain ⟨m, w, c, hw, hc, -⟩ := exists_component_coordinates hsnc P (C.idealSheaf.subschemeι y)
    have hI : IdealSheafData.stalk C.idealSheaf (C.idealSheaf.subschemeι y) =
        Ideal.span (w '' ((({c ⟨⟨Q, hQP⟩, hyQ⟩} : Finset (Fin m)) : Set (Fin m)))) := by
      refine (stalk_idealSheaf_eq_stalk_comap hsnc hdim P ⟨Q, hQP⟩ C hCQ hy).trans
        ((hc ⟨⟨Q, hQP⟩, hyQ⟩).trans ?_)
      rw [Finset.coe_singleton, Set.image_singleton]
    haveI := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hw
    obtain ⟨hR, -, -⟩ := MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hw
      {c ⟨⟨Q, hQP⟩, hyQ⟩}
    exact IsRegularLocalRing.of_ringEquiv
      ((Ideal.quotEquivOfEq hI.symm).trans (MMP.Flips.ResolutionInputs.stalkQuotientEquiv _ y))
  have hregX : IsRegular C.idealSheaf.subscheme :=
    ((isRegular_tfae C.idealSheaf.subscheme).out 1 2 rfl rfl).mpr ⟨inferInstance, hreg⟩
  exact MMP.Mori.isSmoothScheme_of_smooth
    (smooth_of_isRegular_over_perfectField (C.idealSheaf.subscheme ↘ Spec (.of ℂ)) hregX)

omit [W.Over (Spec (.of ℂ))] [MMP.IsComplexScheme W] [IsLocallyNoetherian W] in
/-- The intersection number with a curve of a finite `ℚ`-combination of Cartier divisors. -/
private theorem intersectionNumber_finset_sum {k : Type} [Field k] {X C : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] (i : C ⟶ X) [IsProper (i ≫ sX)]
    (hdim : topologicalKrullDim C ≤ 1) [IsLocallyNoetherian X] [IsNormal X]
    (hQ : ∀ B : QDivisor X, B.IsQCartier) {α : Type*} (s : Finset α) (c : α → ℚ)
    (f : α → Divisor X) (hc : ∀ a, (f a).IsCartier) :
    (∑ a ∈ s, c a • Divisor.toQDivisor (f a)).intersectionNumber k sX i hdim (hQ _) =
      ∑ a ∈ s, c a * (Divisor.degreeOn k sX i hdim (f a) (hc a) : ℚ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact MMP.Fourfold.intersectionNumber_zero sX i hdim
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      QDivisor.intersectionNumber_add' k sX i hdim _ _ (hQ _) (hQ _) (hQ _), ih,
      MMP.Fourfold.intersectionNumber_smul sX i hdim _ (hQ _) _ (hQ _),
      QDivisor.intersectionNumber_toQDivisor k sX i hdim _ (hc a) (hQ _)]

open Classical in
include hsnc hdim hsm in
/-- **The intersection of a homologically trivial curve cycle with a double curve vanishes**,
given that homologically trivial `ℚ`-divisors on `E_P` have zero intersection with curves. -/
private theorem sum_coeff_mul_curveDeg_eq_zero (P : D.support)
    [IsProper (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ))]
    (β : P.1.idealSheaf.subscheme →₀ ℚ)
    (hβ : ∀ x ∈ β.support,
      Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) x = ((1 : ℕ) : ℤ) ∧
      ∃ Q : D.support, Q ≠ P ∧ P.1.idealSheaf.subschemeι x ∈ Q.1.support)
    (hK : haveI := isNormal_component hsnc P
      ∀ Z : QDivisor P.1.idealSheaf.subscheme,
      Finsupp.linearCombination ℚ (fun C : MMP.Mori.PrimeDivisor P.1.idealSheaf.subscheme =>
          Finsupp.single C.genericPoint (1 : ℚ)) Z = β →
      Order.krullDim P.1.idealSheaf.subscheme = 2 →
      ∀ (C : MMP.Mori.PrimeDivisor P.1.idealSheaf.subscheme),
        IsSmoothScheme (C.idealSheaf.subscheme ↘ Spec (.of ℂ)) →
        ∀ (hdimC : topologicalKrullDim C.idealSheaf.subscheme ≤ 1) (hZ : Z.IsQCartier),
        Z.intersectionNumber ℂ (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) C.idealSheaf.subschemeι
          hdimC hZ = 0)
    {η : W} (hη : IsDoubleCurve D η) (hP : P ∈ comps D η) (F : Finset W)
    (hF : ∀ η, η ∈ F ↔ IsDoubleCurve D η ∧ P ∈ comps D η) :
    ∑ η' ∈ F, (if h : IsDoubleCurve D η' ∧ P ∈ comps D η' then
      β (curvePoint hsnc hdim P h.1 h.2) else 0) * (curveDeg hsnc hdim P η η' : ℚ) = 0 := by
  haveI := isNormal_component hsnc P
  haveI := P.1.integral
  haveI : CompactSpace P.1.idealSheaf.subscheme :=
    QuasiCompact.compactSpace_of_compactSpace (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ))
  have hsmE := isSmoothScheme_component hsnc P
  have hQ : ∀ B : QDivisor P.1.idealSheaf.subscheme, B.IsQCartier :=
    MMP.Fourfold.isQCartier_of_isSmoothScheme hsmE
  have hcart : ∀ B : Divisor P.1.idealSheaf.subscheme, B.IsCartier :=
    MMP.Fourfold.isCartier_of_isSmoothScheme hsmE
  let c : W → ℚ := fun η' ↦ if h : IsDoubleCurve D η' ∧ P ∈ comps D η' then
    β (curvePoint hsnc hdim P h.1 h.2) else 0
  let f : W → Divisor P.1.idealSheaf.subscheme := fun η' ↦
    if h : IsDoubleCurve D η' ∧ P ∈ comps D η' then
      Finsupp.single (curveDiv hsnc hdim P h.1 h.2) 1 else 0
  set Z : QDivisor P.1.idealSheaf.subscheme := ∑ η' ∈ F, c η' • Divisor.toQDivisor (f η')
  have h2 := krullDim_eq_two_of_mem_comps hsnc hdim P hη hP
  have hdimC := topologicalKrullDim_curve_le hsnc P h2 (curveDiv hsnc hdim P hη hP)
  -- the cycle of `Z` is `β`
  have hcyc : Finsupp.linearCombination ℚ (fun C : MMP.Mori.PrimeDivisor P.1.idealSheaf.subscheme =>
      Finsupp.single C.genericPoint (1 : ℚ)) Z = β := by
    rw [eq_sum_curvePoint hsnc hdim P β hβ F hF, map_sum]
    refine Finset.sum_congr rfl fun η' _ ↦ ?_
    rw [map_smul]
    simp only [c, f]
    split_ifs with h
    · rw [MMP.Threefold.Resolution.toQDivisor_single, Int.cast_one,
        Finsupp.linearCombination_single, one_smul]
      rfl
    · simp
  have hzero := hK Z hcyc h2 (curveDiv hsnc hdim P hη hP)
    (isSmoothScheme_curveDiv hsnc hdim P hη hP) hdimC (hQ _)
  rw [intersectionNumber_finset_sum _ _ hdimC hQ F c f (fun a ↦ hcart (f a))] at hzero
  refine Eq.trans (Finset.sum_congr rfl fun η' _ ↦ ?_) hzero
  simp only [c, f]
  split_ifs with h
  · rw [curveDeg_eq hsnc hdim P hη hP h.1 h.2]
  · rw [zero_mul, zero_mul]

end Curves

section Assembly

open MMP.Mori
open scoped MMP.SubschemeOver

variable {W : Scheme.{0}} [W.Over (Spec (.of ℂ))] [MMP.IsComplexScheme W]
  [IsLocallyNoetherian W] [IsNormal W]

private theorem ncard_eq_card_filter {α : Type*} {p q : α → Prop} [Fintype {a // p a}]
    [DecidablePred q] :
    {a | p a ∧ q a}.ncard = (Finset.univ.filter fun a : {a // p a} ↦ q a.1).card := by
  rw [← Set.ncard_coe_finset]
  have : ((Finset.univ.filter fun a : {a // p a} ↦ q a.1 : Finset _) : Set {a // p a}) =
      Subtype.val ⁻¹' {a | p a ∧ q a} := by
    ext a
    simp [a.2]
  rw [this, Set.ncard_preimage_of_injective_subset_range Subtype.val_injective]
  intro a ha
  exact ⟨⟨a, ha.1⟩, rfl⟩

open Classical in
/-- **No curve relation**, with the vanishing of the intersections of homologically trivial
divisors on the components as an input. -/
private theorem eq_zero_of_intersectionNumber_eq_zero (hsm : IsSmoothScheme (W ↘ Spec (.of ℂ)))
    (hdim : topologicalKrullDim W = 3) (D : Divisor W) (hD : ∀ P, 0 ≤ D.coeff P)
    (hsnc : D.IsSNC (W ↘ Spec (.of ℂ)))
    [∀ P : D.support, IsProper (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ))]
    [Stacks.Ample.IsInvertibleModule W (-D).divisorialSheaf]
    (hample : ∀ P ∈ D.support, Stacks.Ample.IsAmple P.idealSheaf.subscheme
      ((Scheme.Modules.pullback P.idealSheaf.subschemeι).obj (-D).divisorialSheaf))
    (β : ∀ P : D.support, P.1.idealSheaf.subscheme →₀ ℚ)
    (hβ : ∀ P, ∀ x ∈ (β P).support,
      Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) x = ((1 : ℕ) : ℤ) ∧
      ∃ Q : D.support, Q ≠ P ∧ P.1.idealSheaf.subschemeι x ∈ Q.1.support)
    (hK : ∀ P : D.support, haveI := isNormal_component hsnc P
      ∀ Z : QDivisor P.1.idealSheaf.subscheme,
      Finsupp.linearCombination ℚ (fun C : MMP.Mori.PrimeDivisor P.1.idealSheaf.subscheme =>
          Finsupp.single C.genericPoint (1 : ℚ)) Z = β P →
      Order.krullDim P.1.idealSheaf.subscheme = 2 →
      ∀ (C : MMP.Mori.PrimeDivisor P.1.idealSheaf.subscheme),
        IsSmoothScheme (C.idealSheaf.subscheme ↘ Spec (.of ℂ)) →
        ∀ (hdimC : topologicalKrullDim C.idealSheaf.subscheme ≤ 1) (hZ : Z.IsQCartier),
        Z.intersectionNumber ℂ (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) C.idealSheaf.subschemeι
          hdimC hZ = 0)
    (hsum : ∑ P, Finsupp.mapDomain P.1.idealSheaf.subschemeι.base (β P) = 0) :
    β = 0 := by
  classical
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (W ↘ Spec (.of ℂ))
  haveI : ∀ P : D.support, CompactSpace P.1.idealSheaf.subscheme := fun P ↦
    QuasiCompact.compactSpace_of_compactSpace (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ))
  have hfinD := finite_doubleCurve hsnc hdim (D := D)
  have hfinT := finite_triplePoint hsnc hdim hsm (D := D)
  letI : Fintype {η : W // IsDoubleCurve D η} := hfinD.fintype
  letI : Fintype {t : W // IsTriplePoint D t} := hfinT.fintype
  let S : {η : W // IsDoubleCurve D η} → Finset D.support := fun η ↦ comps D η.1
  let ST : {t : W // IsTriplePoint D t} → Finset D.support := fun t ↦ comps D t.1
  let inc : {t : W // IsTriplePoint D t} → {η : W // IsDoubleCurve D η} → Prop :=
    fun t η ↦ η.1 ⤳ t.1
  let m : D.support → ℚ := fun P ↦ (D.coeff P.1 : ℚ)
  let β' : D.support → {η : W // IsDoubleCurve D η} → ℚ := fun P η ↦
    if h : P ∈ comps D η.1 then β P (curvePoint hsnc hdim P η.2 h) else 0
  let τ : D.support → {η : W // IsDoubleCurve D η} → {η : W // IsDoubleCurve D η} → ℚ :=
    fun P η' η ↦ (curveDeg hsnc hdim P η.1 η'.1 : ℚ)
  have hne : ∀ η : {η : W // IsDoubleCurve D η}, (comps D η.1).Nonempty := fun η ↦
    Finset.card_pos.1 (by rw [IsDoubleCurve.card_comps hsnc hdim η.2]; norm_num)
  let P₀ : {η : W // IsDoubleCurve D η} → D.support := fun η ↦ (hne η).choose
  have hP₀ : ∀ η, P₀ η ∈ comps D η.1 := fun η ↦ (hne η).choose_spec
  let δ : D.support → {η : W // IsDoubleCurve D η} → ℚ := fun R η ↦
    haveI := isProper_curve_comp (P₀ η) (curveDiv hsnc hdim (P₀ η) η.2 (hP₀ η))
    (Divisor.degreeOn ℂ (W ↘ Spec (.of ℂ))
      ((curveDiv hsnc hdim (P₀ η) η.2 (hP₀ η)).idealSheaf.subschemeι ≫
        (P₀ η).1.idealSheaf.subschemeι)
      (topologicalKrullDim_curve_le hsnc (P₀ η)
        (krullDim_eq_two_of_mem_comps hsnc hdim (P₀ η) η.2 (hP₀ η)) _)
      (Finsupp.single R.1 1) (MMP.Fourfold.isCartier_of_isSmoothScheme hsm _) : ℚ)
  -- the finsets of double curves through a component
  let FP : D.support → Finset W := fun P ↦
    (Finset.univ.filter fun η : {η : W // IsDoubleCurve D η} ↦ P ∈ comps D η.1).map
      (Function.Embedding.subtype _)
  have hFP : ∀ P η, η ∈ FP P ↔ IsDoubleCurve D η ∧ P ∈ comps D η := by
    intro P η
    simp only [FP, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨η', h, rfl⟩
      exact ⟨η'.2, h⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨η, h1⟩, h2, rfl⟩
  have key : β' = 0 := by
    refine eq_zero_of_weighted_curve_identity' m S ST inc β' δ τ ?hm ?hS ?hST ?hinc ?huniq ?hβ0
      ?hβanti ?hN2 ?hN3 ?hN14 ?hN5 ?hHZ
    case hm =>
      intro P
      have h1 : D.coeff P.1 ≠ 0 := Finsupp.mem_support_iff.1 P.2
      have h2 := hD P.1
      simp only [m]
      exact_mod_cast lt_of_le_of_ne h2 (Ne.symm h1)
    case hS => exact fun η ↦ IsDoubleCurve.card_comps hsnc hdim η.2
    case hST => exact fun t ↦ t.2
    case hinc => exact fun t η h ↦ comps_subset_of_specializes h
    case huniq =>
      intro t s hs hcard
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hcard
      have ha : a ∈ comps D t.1 := hs (by simp)
      have hb : b ∈ comps D t.1 := hs (by simp)
      obtain ⟨η, ⟨⟨hη, hηt⟩, hηc⟩, huniq⟩ := existsUnique_doubleCurve hsnc hdim t.2 ha hb hab
      refine ⟨⟨η, hη⟩, ⟨hηt, hηc⟩, fun η' ⟨h1, h2⟩ ↦ Subtype.ext (huniq η'.1 ⟨⟨η'.2, h1⟩, h2⟩)⟩
    case hβ0 =>
      intro P η hP
      exact dif_neg hP
    case hβanti =>
      intro η P Q hPQ hS'
      have hP : P ∈ comps D η.1 := by
        change P ∈ S η; rw [hS']; simp
      have hQ : Q ∈ comps D η.1 := by
        change Q ∈ S η; rw [hS']; simp
      simp only [β', dif_pos hP, dif_pos hQ]
      exact coeff_add_coeff_eq_zero_of_sum hsnc hdim β hsum η.2 hPQ hP hQ hS'
    case hN2 =>
      intro P η η' hne' hS' hP
      have hP' : P ∈ comps D η'.1 := by change P ∈ S η'; rwa [← hS']
      simp only [τ]
      rw [curveDeg_eq hsnc hdim P η.2 hP η'.2 hP']
      have := degreeOn_curveDiv_eq_zero hsnc hdim hsm P η.2 η'.2
        (fun h ↦ hne' (Subtype.ext h)) hS' hP
      exact_mod_cast this
    case hN3 =>
      intro P η η' hS' hP hP'
      simp only [τ]
      rw [curveDeg_eq hsnc hdim P η.2 hP η'.2 hP',
        degreeOn_curveDiv_eq_ncard hsnc hdim hsm P η.2 η'.2 hS' hP hP']
      congr 1
      exact ncard_eq_card_filter
    case hN14 =>
      intro P R η hP hRP
      haveI := isProper_curve_comp P (curveDiv hsnc hdim P η.2 hP)
      have h1 : δ R η = (Divisor.degreeOn ℂ (W ↘ Spec (.of ℂ))
          ((curveDiv hsnc hdim P η.2 hP).idealSheaf.subschemeι ≫ P.1.idealSheaf.subschemeι)
          (topologicalKrullDim_curve_le hsnc P (krullDim_eq_two_of_mem_comps hsnc hdim P η.2 hP) _)
          (Finsupp.single R.1 1) (MMP.Fourfold.isCartier_of_isSmoothScheme hsm _) : ℚ) := by
        simp only [δ]
        congr 1
        haveI := (MMP.Fourfold.isCartier_of_isSmoothScheme hsm
          (Finsupp.single R.1 1 : Divisor W)).isInvertibleModule_divisorialSheaf
        exact degreeOn_curveDiv_comp_eq hsnc hdim (P₀ η) P η.2 (hP₀ η) hP _
      rw [h1, degreeOn_single_comp_eq_sum hsnc hdim hsm P η.2 hP R hRP
        ((Finset.univ.filter fun η' : {η : W // IsDoubleCurve D η} ↦ S η' = {P, R}).map
          (Function.Embedding.subtype _)) ?_]
      · rw [Finset.sum_map]
        push_cast
        rfl
      · intro η'
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Function.Embedding.coe_subtype, S]
        constructor
        · rintro ⟨η'', h, rfl⟩
          exact ⟨η''.2, h⟩
        · rintro ⟨h1, h2⟩
          exact ⟨⟨η', h1⟩, h2, rfl⟩
    case hN5 =>
      intro η
      have := sum_coeff_mul_degreeOn_neg hsnc hdim hsm hample (P₀ η) η.2 (hP₀ η)
      simp only [m, δ]
      exact_mod_cast this
    case hHZ =>
      intro P η hP
      have := sum_coeff_mul_curveDeg_eq_zero hsnc hdim hsm P (β P) (hβ P) (hK P) η.2 hP (FP P)
        (hFP P)
      rw [← this]
      simp only [FP]
      rw [Finset.sum_map, Finset.sum_filter]
      refine Finset.sum_congr rfl fun η' _ ↦ ?_
      by_cases h' : P ∈ comps D η'.1
      · rw [if_pos h']
        change β' P η' * τ P η' η =
          (if h : IsDoubleCurve D η'.1 ∧ P ∈ comps D η'.1 then
            β P (curvePoint hsnc hdim P h.1 h.2) else 0) * (curveDeg hsnc hdim P η.1 η'.1 : ℚ)
        rw [dif_pos ⟨η'.2, h'⟩]
        simp only [β', τ, dif_pos h']
      · rw [if_neg h']
        simp only [β', dif_neg h', zero_mul]
  funext P
  refine eq_zero_of_coeff_curvePoint_eq_zero hsnc hdim P (β P) (hβ P) (FP P) (hFP P)
    fun η hη hP ↦ ?_
  simpa [β', hP] using congrFun (congrFun key P) ⟨η, hη⟩

end Assembly

section Point

/-- `Spec ℂ` is a complex scheme. -/
instance isComplexScheme_spec : IsComplexScheme (Spec (.of ℂ)) :=
  haveI : IsSmoothVariety ℂ (Spec (.of ℂ) ↘ Spec (.of ℂ)) :=
    MMP.isSmoothVariety_of_eq_id (MMP.specOverSpec_over_self ℂ)
  IsComplexScheme.of_isSmoothVariety _

private theorem dimension_spec_le : dimension (Spec (.of ℂ)) ≤ ((0 : ℕ) : WithBot ℕ∞) := by
  change topologicalKrullDim (PrimeSpectrum ℂ) ≤ _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]
  rfl

/-- Every point of `Spec ℂ` has delta-dimension zero. -/
theorem relativeDimension_spec_eq_zero (p : Spec (.of ℂ)) :
    Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (Spec (.of ℂ) ↘ Spec (.of ℂ)) p = ((0 : ℕ) : ℤ) := by
  have h1 : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (Spec (.of ℂ) ↘ Spec (.of ℂ)) p ≤ ((0 : ℕ) : ℤ) :=
    Chow.relativeDimension_le_of_dimension_le dimension_spec_le p
  have h0 : (0 : ℤ) ≤ Stacks.Chow.relativeDimension
      (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (Spec (.of ℂ) ↘ Spec (.of ℂ)) p :=
    Stacks.Chow.relativeDimension_nonneg (Stacks.Chow.fieldChowSituation ℂ)
      (fun _ _ ↦ rfl) (Spec (.of ℂ) ↘ Spec (.of ℂ)) p
  rw [Nat.cast_zero] at h1 ⊢
  omega

/-- On `Spec ℂ`, if `r • [p] = 0` in `H_0(pt; ℚ)` for `r : ℚ`, then `r = 0`. -/
theorem eq_zero_of_smul_pointCycleClass_spec_eq_zero (p : Spec (.of ℂ)) {r : ℚ}
    (h : r • Chow.pointCycleClass ℚ p (relativeDimension_spec_eq_zero p) = 0) : r = 0 := by
  have h0 := Chow.eq_zero_of_linearCombination_pointCycleClassOrZero_eq_zero ℚ dimension_spec_le
    (Finsupp.single_mem_supported ℚ r (relativeDimension_spec_eq_zero p)) (by
      rw [Finsupp.linearCombination_single, Chow.pointCycleClassOrZero,
        dif_pos (relativeDimension_spec_eq_zero p)]
      exact h)
  exact Finsupp.single_eq_zero.1 h0

/-- On `Spec ℂ`, if `n • [p] = 0` in `H_0(pt; ℚ)` for `n : ℤ`, then `n = 0`. -/
theorem eq_zero_of_zsmul_pointCycleClass_spec_eq_zero (p : Spec (.of ℂ)) (n : ℤ)
    (h : n • Chow.pointCycleClass ℚ p (relativeDimension_spec_eq_zero p) = 0) : n = 0 := by
  rw [← Int.cast_smul_eq_zsmul ℚ] at h
  exact_mod_cast eq_zero_of_smul_pointCycleClass_spec_eq_zero p h

end Point

end MMP.Fourfold

namespace MMP.Analytic.singularCohomology

open MMP.SingularCochain

/-- **Change of coefficients commutes with pull-back** on singular cohomology: for a ring map
`f : R →+* S` and a continuous map `g : Y' ⟶ Y`, `mapCoeff f n (g^* x) = g^* (mapCoeff f n x)`. -/
theorem mapCoeff_relativeSingularCohomology_map {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) {Y' Y : TopCat.{0}} (g : Y' ⟶ Y)
    (h : (Set.univᶜ : Set Y') ⊆ g ⁻¹' Set.univᶜ) (n : ℕ)
    (x : singularCohomology R Y n) :
    singularCohomology.mapCoeff f n ((relativeSingularCohomology.map R (ModuleCat.of R R) g
      h n).hom x) =
    (relativeSingularCohomology.map S (ModuleCat.of S S) g h n).hom
      (singularCohomology.mapCoeff f n x) := by
  apply (relativeSingularCohomologyEquiv S (Set.univᶜ : Set Y') n).injective
  rw [relativeSingularCohomologyEquiv_map]
  simp only [singularCohomology.mapCoeff, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, LinearEquiv.apply_symm_apply]
  rw [relativeSingularCohomologyEquiv_map]
  generalize relativeSingularCohomologyEquiv R (Set.univᶜ : Set Y) n x = z
  induction z using Submodule.Quotient.induction_on with
  | H φ => rfl

end MMP.Analytic.singularCohomology

namespace MMP.Fourfold

open UnderlyingSpace Opposite Topology

attribute [local instance] isIntegral_component locallyOfFiniteType_component

section CurveDegree

open MMP.Mori MMP.Analytic

/-- A point of delta-dimension zero is closed. -/
private theorem isClosed_singleton_of_relativeDimension_eq_zero {X : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] {x : X}
    (hx : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) x = ((0 : ℕ) : ℤ)) : IsClosed ({x} : Set X) := by
  refine closure_subset_iff_isClosed.mp fun y hy ↦ ?_
  by_contra hne
  have hlt := Stacks.Chow.relativeDimension_lt_of_specializes (Stacks.Chow.fieldChowSituation ℂ)
    (X ↘ Spec (.of ℂ)) (specializes_iff_mem_closure.mpr hy) (Ne.symm hne)
  have h0 : (0 : ℤ) ≤ Stacks.Chow.relativeDimension
      (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) y :=
    Stacks.Chow.relativeDimension_nonneg (Stacks.Chow.fieldChowSituation ℂ)
      (fun _ _ ↦ rfl) (X ↘ Spec (.of ℂ)) y
  have hx' : Stacks.Chow.relativeDimension
      (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = 0 := by
    exact_mod_cast hx
  omega

/-- At a closed point of a scheme locally of finite type over `ℂ`, the structure morphism has
residue degree one. -/
private theorem residueDegree_eq_one_of_isClosed {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType p] (x : X) (hx : IsClosed ({x} : Set X)) : p.residueDegree x = 1 := by
  haveI : Subsingleton (Spec (.of ℂ)) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  haveI := Stacks.Chow.isIso_Γevaluation_of_isIntegral_of_subsingleton (Y := Spec (.of ℂ)) (p x)
  have hf := ConcreteCategory.bijective_of_isIso (C := CommRingCat)
    ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ (Spec (.of ℂ)).Γevaluation (p x))
  have hb := bijective_algebraMap_residueField_of_isClosed p x hx
  rw [RingHom.algebraMap_toAlgebra, ← Scheme.Γevaluation_naturality, ← Category.assoc,
    CommRingCat.hom_comp, RingHom.coe_comp] at hb
  let _ := (p.residueFieldMap x).hom.toAlgebra
  change Module.finrank ((Spec (.of ℂ)).residueField (p.base x)) (X.residueField x) = 1
  exact Module.finrank_of_bijective_algebraMap ((Function.Bijective.of_comp_iff _ hf).1 hb)

/-- The class of a rational combination of the prime cycles of the prime divisors of
delta-dimension `d` is the combination of their cycle classes. -/
private theorem rationalCycleClass_linearCombination {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsComplexScheme X] (d : ℕ) (Z : MMP.Mori.PrimeDivisor X →₀ ℚ) :
    Chow.rationalCycleClass X d (Finsupp.linearCombination ℚ (fun P : MMP.Mori.PrimeDivisor X =>
        if h : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
            (X ↘ Spec (.of ℂ)) P.genericPoint = d then
          Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) d
            P.genericPoint h
        else 0) Z) =
      Finsupp.linearCombination ℚ
        (fun P : MMP.Mori.PrimeDivisor X => Chow.pointCycleClassOrZero ℚ d P.genericPoint) Z := by
  induction Z using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
  | single P q =>
    rw [Finsupp.linearCombination_single, Finsupp.linearCombination_single, map_smul,
      Chow.pointCycleClassOrZero]
    split_ifs with h
    · rw [Chow.rationalCycleClass_rationalPointCycle]
    · rw [map_zero]

variable {C : Scheme.{0}} [C.Over (Spec (.of ℂ))] [IsComplexScheme C] [IsIntegral C]

/-- The structure morphism of a scheme over `Spec K` lies over `Spec K` (`Spec K ↘ Spec K = 𝟙`). -/
theorem isOver_structureMorphism_spec {K : Type} [Field K] (Y : Scheme.{0})
    [Y.Over (Spec (.of K))] : (Y ↘ Spec (.of K)).IsOver (Spec (.of K)) :=
  ⟨by rw [MMP.specOverSpec_over_self, Category.comp_id]⟩

attribute [local instance] isOver_structureMorphism_spec

/-- On a complex curve, the generic point of a prime divisor has delta-dimension zero. -/
theorem relativeDimension_genericPoint_primeDivisor (hdim1 : topologicalKrullDim C = 1)
    (P : MMP.Mori.PrimeDivisor C) :
    Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (C ↘ Spec (.of ℂ)) P.genericPoint = ((0 : ℕ) : ℤ) := by
  have hform := MMP.height_add_coheight_eq_krullDim ℂ P.genericPoint
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint,
    ← topologicalKrullDim_eq_krullDim' C, hdim1] at hform
  have h' : Order.height P.genericPoint + 1 = 1 := WithBot.coe_injective (hform.trans rfl)
  have h0 : Order.height P.genericPoint = 0 :=
    ENat.add_left_injective_of_ne_top ENat.one_ne_top (h'.trans (zero_add 1).symm)
  refine Stacks.Intersection.ExteriorProductProjections.relativeDimension_eq_of_topologicalKrullDim_closure
    ℂ _ _ 0 ?_
  rw [AlgebraicGeometry.topologicalKrullDim_closure_singleton_eq_height, h0]
  rfl

/-- **The degree of a line bundle on a smooth projective complex curve is topological**: the
push-forward to the point of `c₁(N) ∩ [C]` is `deg N` times the class of the point. Here `[C]` is
the cycle class `cl_C(x)` of a point `x` of delta-dimension one (on the integral curve `C`, its
generic point) and `c₁(N) ∩ -` is the cap product with the rational first Chern class pulled back
along `C(ℂ) ≃ C^an`. -/
theorem pushforward_capProductPullback_eq_invertibleCurveDegree_smul
    [IsProper (C ↘ Spec (.of ℂ))] (hsm : IsSmoothScheme (C ↘ Spec (.of ℂ)))
    (hdim1 : topologicalKrullDim C = 1) (hproj : MMP.Mori.IsProjectiveVariety ℂ (C ↘ Spec (.of ℂ)))
    (N : C.Modules) [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 N] (x : C)
    (hx : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (C ↘ Spec (.of ℂ)) x = ((1 : ℕ) : ℤ)) (p : Spec (.of ℂ)) :
    (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (C ↘ Spec (.of ℂ))))
      (UnderlyingSpace.isProperMap_map (K := ℂ) _) (2 * 0 : ℕ)).hom
      (BorelMooreCross.congrDegree ℚ (TopCat.of (UnderlyingSpace ℂ C))
        (by norm_num : ((2 * 1 : ℕ) : ℤ) - 2 = ((2 * 0 : ℕ) : ℤ))
        (borelMooreHomology.capProductPullback ℚ
          (TopCat.ofHom ⟨_, ComplexPoints.homeomorphUnderlyingSpace.symm.continuous⟩ :
            TopCat.of (UnderlyingSpace ℂ C) ⟶ Analytification.space (C ↘ Spec (.of ℂ)))
          Set.univ 2 ((2 * 1 : ℕ) : ℤ)
          (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass N))
          (Chow.pointCycleClass ℚ x hx))) =
      (invertibleCurveDegree ℂ (C ↘ Spec (.of ℂ)) hdim1.le N : ℚ) •
        Chow.pointCycleClass ℚ p (relativeDimension_spec_eq_zero p) := by
  classical
  haveI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (C ↘ Spec (.of ℂ))
  haveI : Smooth (C ↘ Spec (.of ℂ)) := MMP.Resolution.Aux.smooth_of_isSmoothScheme' _ hsm
  haveI : IsNormal C := isNormal_of_smooth_over_field (C ↘ Spec (.of ℂ))
  haveI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace (C ↘ Spec (.of ℂ))
  haveI : IsSmoothVariety ℂ (C ↘ Spec (.of ℂ)) := { }
  obtain ⟨hcart, -, -, -, hB, -⟩ :=
    Divisor.cartier_weil_dictionary_of_isSmoothVariety ℂ (C ↘ Spec (.of ℂ))
  obtain ⟨B, ⟨e⟩⟩ := hB N inferInstance
  haveI := (hcart B).isInvertibleModule_divisorialSheaf
  -- the degree of `𝒪_C(B)` is `deg B`
  have hdeg : invertibleCurveDegree ℂ (C ↘ Spec (.of ℂ)) hdim1.le N = B.sum fun _ a => a := by
    rw [← invertibleCurveDegree_eq_of_iso ℂ _ hdim1.le e]
    have hC : MMP.Mori.IsNormalVariety ℂ (C ↘ Spec (.of ℂ)) := ⟨{ }, inferInstance⟩
    have hι : IsIso (smoothLocus (C ↘ Spec (.of ℂ))).ι := by
      have h : smoothLocus (C ↘ Spec (.of ℂ)) = ⊤ := hsm
      generalize smoothLocus (C ↘ Spec (.of ℂ)) = U at h ⊢
      subst h
      rw [← Scheme.topIso_hom]
      infer_instance
    have hdim' : topologicalKrullDim (smoothLocus (C ↘ Spec (.of ℂ))).toScheme ≤ 1 := by
      rw [IsHomeomorph.topologicalKrullDim_eq _
        (Scheme.homeoOfIso (asIso (smoothLocus (C ↘ Spec (.of ℂ))).ι)).isHomeomorph, hdim1]
    have h1 := MMP.Flips.degreeOn_smoothLocus_eq_sum hC hsm inferInstance hdim1 hdim' B
    change invertibleCurveDegree ℂ ((smoothLocus (C ↘ Spec (.of ℂ))).ι ≫ (C ↘ Spec (.of ℂ))) hdim'
      ((Scheme.Modules.pullback (smoothLocus (C ↘ Spec (.of ℂ))).ι).obj B.divisorialSheaf) = _
      at h1
    rw [invertibleCurveDegree_pullback_of_isIso (smoothLocus (C ↘ Spec (.of ℂ))).ι
      (C ↘ Spec (.of ℂ)) hdim' hdim1.le] at h1
    exact h1
  -- the dictionary in dimension one: `[B] = c₁(𝒪_C(B)) ∩ [C]`
  have hrat := (MMP.Fourfold.smul_rationalCycleClass_eq_capProductPullback hproj hsm (d := 0)
    (by simpa using hdim1) (Divisor.toQDivisor B) one_pos B (by simp) x hx).1
  rw [algebraicFirstChernClass_eq_of_iso e, Nat.cast_one, one_smul,
    Chow.rationalCycleClass_rationalPointCycle, rationalCycleClass_linearCombination] at hrat
  -- push-forward of the zero cycle `B` to the point
  haveI : (C ↘ Spec (.of ℂ)).IsOver (Spec (.of ℂ)) :=
    ⟨by rw [MMP.specOverSpec_over_self, Category.comp_id]⟩
  haveI : Subsingleton (Spec (.of ℂ)) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  have hpt : ∀ q : Spec (.of ℂ), Chow.pointCycleClassOrZero ℚ 0 q =
      Chow.pointCycleClass ℚ p (relativeDimension_spec_eq_zero p) := by
    intro q
    obtain rfl := Subsingleton.elim q p
    rw [Chow.pointCycleClassOrZero, dif_pos (relativeDimension_spec_eq_zero q)]
  have key : ∀ B' : Divisor C, (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (C ↘ Spec (.of ℂ))))
      (UnderlyingSpace.isProperMap_map (K := ℂ) _) (2 * 0 : ℕ)).hom
        (Finsupp.linearCombination ℚ (fun P : MMP.Mori.PrimeDivisor C =>
          Chow.pointCycleClassOrZero ℚ 0 P.genericPoint) (Divisor.toQDivisor B')) =
      ((B'.sum fun _ a => a : ℤ) : ℚ) •
        Chow.pointCycleClass ℚ p (relativeDimension_spec_eq_zero p) := by
    intro B'
    induction B' using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb =>
      rw [map_add, map_add, map_add, ha, hb,
        Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Int.cast_add, add_smul]
    | single P n =>
      have hsingle : Divisor.toQDivisor (Finsupp.single P n) = Finsupp.single P (n : ℚ) := by
        change Finsupp.mapRange (Int.castAddHom ℚ) (map_zero _) _ = _
        rw [Finsupp.mapRange_single]
        rfl
      have hP := relativeDimension_genericPoint_primeDivisor hdim1 P
      have h := Chow.pushforward_pointCycleClass ℚ (C ↘ Spec (.of ℂ)) P.genericPoint hP
      rw [residueDegree_eq_one_of_isClosed _ _
        (isClosed_singleton_of_relativeDimension_eq_zero hP), Nat.cast_one, one_smul,
        hpt] at h
      rw [hsingle, Finsupp.linearCombination_single, map_smul, Finsupp.sum_single_index rfl,
        Chow.pointCycleClassOrZero, dif_pos hP]
      erw [h]
  refine (congrArg (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (C ↘ Spec (.of ℂ))))
      (UnderlyingSpace.isProperMap_map (K := ℂ) _) (2 * 0 : ℕ)).hom hrat).symm.trans ?_
  rw [key, hdeg]

/-- **A line bundle with rationally trivial first Chern class on a smooth projective complex curve
has degree zero.** -/
theorem invertibleCurveDegree_eq_zero_of_mapCoeff_algebraicFirstChernClass_eq_zero
    [IsProper (C ↘ Spec (.of ℂ))] (hsm : IsSmoothScheme (C ↘ Spec (.of ℂ)))
    (hdim1 : topologicalKrullDim C = 1) (hproj : MMP.Mori.IsProjectiveVariety ℂ (C ↘ Spec (.of ℂ)))
    (N : C.Modules) [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 N]
    (hN : singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass N) = 0) :
    invertibleCurveDegree ℂ (C ↘ Spec (.of ℂ)) hdim1.le N = 0 := by
  have hx : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (C ↘ Spec (.of ℂ)) (genericPoint C) = ((1 : ℕ) : ℤ) := by
    refine Stacks.Intersection.ExteriorProductProjections.relativeDimension_eq_of_topologicalKrullDim_closure
      ℂ _ _ 1 ?_
    rw [(genericPoint_spec C).def, show ((1 : ℕ) : WithBot ℕ∞) = 1 from rfl, ← hdim1]
    exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ C).isHomeomorph
  have h := pushforward_capProductPullback_eq_invertibleCurveDegree_smul hsm hdim1 hproj N _ hx
    ((C ↘ Spec (.of ℂ)).base (genericPoint C))
  rw [hN, LinearMap.map_zero₂, map_zero, map_zero, eq_comm] at h
  exact_mod_cast eq_zero_of_smul_pointCycleClass_spec_eq_zero _ h

end CurveDegree

section Geometry

open MMP.Mori

variable {W : Scheme.{0}} [W.Over (Spec (.of ℂ))] [IsComplexScheme W] [IsLocallyNoetherian W]
  [IsNormal W]

open Classical in
/-- **Homologically trivial `ℚ`-divisors on a smooth projective surface have zero intersection
with smooth curves**: if the class of the cycle of `Z` vanishes in `H_2(X, ℚ)`, then
`(Z · C) = 0`. -/
private theorem intersectionNumber_eq_zero_of_rationalCycleClass_eq_zero {X : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [IsComplexScheme X] [IsLocallyNoetherian X] [IsNormal X]
    [IsProper (X ↘ Spec (.of ℂ))] [IsIntegral X]
    (hsm : IsSmoothScheme (X ↘ Spec (.of ℂ))) (h2 : Order.krullDim X = 2)
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L)
    (Z : QDivisor X)
    (hZ : pointsClass X 1 (Finsupp.linearCombination ℚ
      (fun C : MMP.Mori.PrimeDivisor X => Finsupp.single C.genericPoint (1 : ℚ)) Z) = 0)
    (C : MMP.Mori.PrimeDivisor X) (hCsm : IsSmoothScheme (C.idealSheaf.subscheme ↘ Spec (.of ℂ)))
    (hdimC : topologicalKrullDim C.idealSheaf.subscheme ≤ 1) (hQ : Z.IsQCartier) :
    Z.intersectionNumber ℂ (X ↘ Spec (.of ℂ)) C.idealSheaf.subschemeι hdimC hQ = 0 := by
  obtain ⟨m, hm, M, hM, hMc⟩ := hQ.exists_pos
  rw [MMP.Mori.QDivisor.intersectionNumber_eq_of_smul ℂ _ _ hdimC Z hQ hm M hMc hM]
  suffices h : M.degreeOn ℂ (X ↘ Spec (.of ℂ)) C.idealSheaf.subschemeι hdimC hMc = 0 by
    rw [h]; simp
  haveI := C.integral
  haveI : IsComplexScheme C.idealSheaf.subscheme :=
    isComplexScheme_of_isClosedImmersion C.idealSheaf.subschemeι
  haveI : IsProper (C.idealSheaf.subscheme ↘ Spec (.of ℂ)) := by
    change IsProper (C.idealSheaf.subschemeι ≫ X ↘ Spec (.of ℂ))
    infer_instance
  haveI : LocallyOfFiniteType (X ↘ Spec (.of ℂ)) := inferInstance
  have hdim1 := topologicalKrullDim_primeDivisor_eq h2 C
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of ℂ))
  haveI := hMc.isInvertibleModule_divisorialSheaf
  haveI : IsSeparated (X ↘ Spec (.of ℂ)) := inferInstance
  -- `X` is projective and its divisor class `[Z]` is cut out by `c₁(𝒪_X(M))`
  haveI : AlgebraicGeometry.IsProperVariety ℂ (X ↘ Spec (.of ℂ)) := { }
  have hprojX : MMP.Mori.IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ)) :=
    (MMP.Foundations.isProjectiveVariety_of_isAmple_and_isProjective_and_exists_isVeryAmple ℂ).1
      X L hL
  have hdimX : topologicalKrullDim X = ((1 + 1 : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDim_eq_krullDim', h2]; rfl
  have hx : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) (genericPoint X) = ((1 + 1 : ℕ) : ℤ) := by
    refine Stacks.Intersection.ExteriorProductProjections.relativeDimension_eq_of_topologicalKrullDim_closure
      ℂ _ _ (1 + 1) ?_
    rw [(genericPoint_spec X).def, ← hdimX]
    exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph
  have hZ' : Chow.rationalCycleClass X 1 (Finsupp.linearCombination ℚ
      (fun P : MMP.Mori.PrimeDivisor X =>
        if h : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
            (X ↘ Spec (.of ℂ)) P.genericPoint = (1 : ℕ) then
          Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (1 : ℕ)
            P.genericPoint h
        else 0) Z) = 0 := by
    rw [rationalCycleClass_linearCombination, ← hZ, ← LinearMap.comp_apply]
    congr 1
    refine Finsupp.lhom_ext' fun C ↦ LinearMap.ext_ring ?_
    simp
  have hc1 := (MMP.Fourfold.smul_rationalCycleClass_eq_capProductPullback hprojX hsm hdimX Z hm M
    hM (genericPoint X) hx).2.1 hZ'
  -- restrict to the curve
  have hLC : Stacks.Ample.IsAmple C.idealSheaf.subscheme
      ((Scheme.Modules.pullback C.idealSheaf.subschemeι).obj L) :=
    Stacks.AmpleFiniteSurjective.isAmple_modulePullback_of_isFinite C.idealSheaf.subschemeι L hL
  haveI : AlgebraicGeometry.IsProperVariety ℂ (C.idealSheaf.subscheme ↘ Spec (.of ℂ)) := { }
  have hprojC : MMP.Mori.IsProjectiveVariety ℂ (C.idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
    (MMP.Foundations.isProjectiveVariety_of_isAmple_and_isProjective_and_exists_isVeryAmple ℂ).1
      _ _ hLC
  change invertibleCurveDegree ℂ (C.idealSheaf.subscheme ↘ Spec (.of ℂ)) hdim1.le
    ((Scheme.Modules.pullback C.idealSheaf.subschemeι).obj M.divisorialSheaf) = 0
  refine invertibleCurveDegree_eq_zero_of_mapCoeff_algebraicFirstChernClass_eq_zero hCsm hdim1
    hprojC _ ?_
  rw [MMP.Analytic.algebraicFirstChernClass_pullback C.idealSheaf.subschemeι
    (MMP.Analytic.ComplexPoints.analyticMap C.idealSheaf.subschemeι rfl) (fun _ => rfl)
    M.divisorialSheaf]
  refine (MMP.Analytic.singularCohomology.mapCoeff_relativeSingularCohomology_map
    (Int.castRingHom ℚ) _ _ 2 _).trans ?_
  rw [hc1, map_zero]

/-- **No curve relation.** In the setting of the main theorem, a family of rational curve cycles
on the components supported on the double locus, with zero classes in the `H_2(E_P, ℚ)` and zero
sum on `W`, vanishes. -/
private theorem eq_zero_of_pointsClass_eq_zero (hsm : IsSmoothScheme (W ↘ Spec (.of ℂ)))
    (hdim : topologicalKrullDim W = 3) (D : Divisor W) (hD : ∀ P, 0 ≤ D.coeff P) (hsnc : D.IsSNC (W ↘ Spec (.of ℂ)))
    (hproper : IsProper (D.suppIdeal.subschemeι ≫ (W ↘ Spec (.of ℂ))))
    [Stacks.Ample.IsInvertibleModule W (-D).divisorialSheaf]
    (hample : ∀ P ∈ D.support, Stacks.Ample.IsAmple P.idealSheaf.subscheme
      ((Scheme.Modules.pullback P.idealSheaf.subschemeι).obj (-D).divisorialSheaf))
    (j : ∀ P : D.support, P.1.idealSheaf.subscheme ⟶ D.suppScheme)
    (hj : ∀ P, j P ≫ D.suppIdeal.subschemeι = P.1.idealSheaf.subschemeι)
    [∀ P, IsProper (j P)]
    [∀ P : D.support, IsComplexScheme P.1.idealSheaf.subscheme]
    (β : ∀ P : D.support, P.1.idealSheaf.subscheme →₀ ℚ)
    (hβ : ∀ P, ∀ x ∈ (β P).support, x ∈ dimPoints P.1.idealSheaf.subscheme 1 ∧
      ∃ Q : D.support, Q ≠ P ∧ P.1.idealSheaf.subschemeι x ∈ Q.1.support)
    (hcl : ∀ P, pointsClass P.1.idealSheaf.subscheme 1 (β P) = 0)
    (hsum : ∑ P, Finsupp.mapDomain P.1.idealSheaf.subschemeι.base (β P) = 0) : β = 0 := by
  haveI : IsProper (D.suppIdeal.subschemeι ≫ (W ↘ Spec (.of ℂ))) := hproper
  haveI : ∀ P : D.support, IsProper (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) := fun P ↦ by
    change IsProper (P.1.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ))
    rw [← hj P, Category.assoc]
    infer_instance
  refine eq_zero_of_intersectionNumber_eq_zero hsm hdim D hD hsnc hample β hβ ?_ hsum
  intro P Z hZ h2 C hCsm hdimC hQ
  haveI := isNormal_component hsnc P
  haveI := P.1.integral
  exact intersectionNumber_eq_zero_of_rationalCycleClass_eq_zero (isSmoothScheme_component hsnc P)
    h2 _ (hample P.1 P.2) Z (by rw [hZ]; exact hcl P) C hCsm hdimC hQ

end Geometry

open MMP.Mori in
/-- **Degree three of an antiample snc surface fibre.** Let `W` be a smooth complex threefold and
`D = ∑ mᵢ Eᵢ` an effective divisor on `W` (`mᵢ > 0`) whose support `E` is a proper snc divisor,
such that `-D` is ample on every component `Eᵢ`. Let `jᵢ : Eᵢ ⟶ E` be the inclusions. Then the
map `⨁ᵢ H_3(Eᵢ, ℚ) → H_3(E, ℚ)`, `(xᵢ)ᵢ ↦ ∑ᵢ (jᵢ)_* xᵢ`, is bijective. -/
@[mmp "lem_mmp_conductor_threefold_fibre_homology_three"]
public theorem bijective_sum_pushforward_rationalHomology_three {W : Scheme.{0}}
    [W.Over (Spec (.of ℂ))] [IsComplexScheme W] [IsLocallyNoetherian W] [IsNormal W]
    (hsm : IsSmoothScheme (W ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim W = 3)
    (D : Divisor W) (hD : ∀ P, 0 ≤ D.coeff P) (hsnc : D.IsSNC (W ↘ Spec (.of ℂ)))
    (hproper : IsProper (D.suppIdeal.subschemeι ≫ (W ↘ Spec (.of ℂ))))
    [Stacks.Ample.IsInvertibleModule W (-D).divisorialSheaf]
    (hample : ∀ P ∈ D.support, Stacks.Ample.IsAmple P.idealSheaf.subscheme
      ((Scheme.Modules.pullback P.idealSheaf.subschemeι).obj (-D).divisorialSheaf))
    (j : ∀ P : D.support, P.1.idealSheaf.subscheme ⟶ D.suppScheme)
    (hj : ∀ P, j P ≫ D.suppIdeal.subschemeι = P.1.idealSheaf.subschemeι)
    [∀ P, (j P).IsOver (Spec (.of ℂ))] [∀ P, IsProper (j P)] :
    Function.Bijective (∑ P : D.support,
      (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (j P)))
        (UnderlyingSpace.isProperMap_map (K := ℂ) _) 3).hom ∘ₗ
        LinearMap.proj (R := ℚ)
          (φ := fun P : D.support => RationalHomology P.1.idealSheaf.subscheme 3) P) := by
  haveI : ∀ P : D.support, IsComplexScheme P.1.idealSheaf.subscheme := fun P ↦
    isComplexScheme_of_isClosedImmersion P.1.idealSheaf.subschemeι
  exact bijective_of_curveCondition D j hj (topologicalKrullDim_doubleLocus_le hsnc hdim)
    (fun β hβ hcl hsum ↦
      eq_zero_of_pointsClass_eq_zero hsm hdim D hD hsnc hproper hample j hj β hβ hcl hsum)

end MMP.Fourfold
