module

import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Unconditional
public import MMP.AlgebraicGeometry.MMP.Fourfold.Defs
public import MMP.AlgebraicGeometry.SpreadingOut.GenericFibreDimension
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeLineBundle
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegree
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.IntermediateFactorization
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.SpanRestrictInvertible
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.ReflectIso
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.DerivedChowFourierMukai
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.QcohPushforwardOpen.Basic

/-!
# Cartesian diagrams and their fibres

A diagram `Z : J ⥤ Over T` is *cartesian* over a diagram `Y : J ⥤ Over S` along `t : T ⟶ S`
when every vertex of `Z` is the base change of the corresponding vertex of `Y` and the squares
over the morphisms of `J` are pullback squares. This file collects what is used to compare a
diagram of `K`-schemes with the fibres of a model of it over a field-valued point:

* the properties of a fibre that the spreading-out theorem records (integrality, dimension and
  normality of the vertices; birationality and smallness of the morphisms; decompositions of
  fibre products as finite disjoint unions; crepant boundaries of log resolutions);
* a common closed embedding of finitely many projective schemes into one projective space;
* the descent of isomorphisms of modules of finite presentation from a limit to a stage
  (Stacks 01ZR) and a bound on the rank of an invertible sheaf of top differential forms;
* the behaviour of geometric integrality, normality and dimension under base change of fields;
* finite disjoint unions and their base change;
* dimension bounds on closed subsets that spread to the fibres;
* the biregularity of a birational morphism at the points of codimension at most one of a
  normal target.

## Main definitions

* `MMP.Spreading.IsCartesian`: a diagram over `T` is the base change of a diagram over `S`.
* `MMP.Spreading.FibreVert`, `MMP.Spreading.FibreMor`, `MMP.Spreading.FibreDecomp`,
  `MMP.Spreading.FibreCrepant`: the properties of a fibre of the model.
* `MMP.Spreading.IsLogResolutionAlong`: a log resolution whose boundary is given by finitely many
  prime divisors.

## Main results

* `MMP.Spreading.exists_common_embedding`: finitely many projective `K`-schemes embed into one
  projective space.
* `MMP.Spreading.IsCartesian.isIso_decompMap_iff`: decompositions of fibre products are detected
  after base change.
* `MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal`: a birational morphism to a
  normal scheme is biregular over the points of codimension at most one.

## References

* [EGA IV, 8.10, 9.7, 12.2]
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
-/

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace MMP.Spreading

noncomputable section

/-! ### Cartesian diagrams -/

section Cartesian

variable {J : Type u} [SmallCategory J]

/-- `q` exhibits the diagram `Z` over `T` as the base change of the diagram `Y` over `S` along
`t : T ⟶ S`: it is natural and every square is a pullback square. -/
public structure IsCartesian {S T : Scheme.{u}} (t : T ⟶ S) (Z : J ⥤ Over T) (Y : J ⥤ Over S)
    (q : ∀ j, (Z.obj j).left ⟶ (Y.obj j).left) : Prop where
  /-- The maps `q j` are natural in `j`. -/
  w : ∀ {j j' : J} (g : j ⟶ j'), (Z.map g).left ≫ q j' = q j ≫ (Y.map g).left
  /-- Each square formed by `q j`, the structure maps to `T` and `S`, and `t` is a pullback. -/
  isPullback : ∀ j, IsPullback (q j) (Z.obj j).hom (Y.obj j).hom t

/-- The base change of a diagram is cartesian over it. -/
public lemma isCartesian_pullback {S T : Scheme.{u}} (t : T ⟶ S) (Y : J ⥤ Over S) :
    IsCartesian t (Y ⋙ Over.pullback t) Y (fun j => pullback.fst (Y.obj j).hom t) where
  w g := by
    simp only [Functor.comp_obj, Over.pullback_obj_left, Functor.comp_map, Over.pullback_map_left]
    exact pullback.lift_fst _ _ _
  isPullback j := IsPullback.of_hasPullback _ _

/-- Cartesian diagrams compose. -/
public lemma IsCartesian.comp {S T U : Scheme.{u}} {t : T ⟶ S} {s : U ⟶ T} {Z : J ⥤ Over U}
    {Y' : J ⥤ Over T} {Y : J ⥤ Over S} {q' : ∀ j, (Z.obj j).left ⟶ (Y'.obj j).left}
    {q : ∀ j, (Y'.obj j).left ⟶ (Y.obj j).left} (h' : IsCartesian s Z Y' q')
    (h : IsCartesian t Y' Y q) : IsCartesian (s ≫ t) Z Y (fun j => q' j ≫ q j) where
  w g := by rw [← Category.assoc, h'.w, Category.assoc, h.w, Category.assoc]
  isPullback j := (h'.isPullback j).paste_horiz (h.isPullback j)

/-- The squares of a cartesian diagram over the arrows are pullback squares. -/
public lemma IsCartesian.isPullback_map {S T : Scheme.{u}} {t : T ⟶ S} {Z : J ⥤ Over T}
    {Y : J ⥤ Over S} {q : ∀ j, (Z.obj j).left ⟶ (Y.obj j).left} (h : IsCartesian t Z Y q)
    {j j' : J} (g : j ⟶ j') : IsPullback (q j) (Z.map g).left (Y.map g).left (q j') := by
  refine IsPullback.of_bot ?_ (h.w g).symm (h.isPullback j')
  rw [Over.w (Z.map g), Over.w (Y.map g)]
  exact h.isPullback j

/-- A cartesian diagram is isomorphic to the base change. -/
@[expose] public def IsCartesian.iso {S T : Scheme.{u}} {t : T ⟶ S} {Z : J ⥤ Over T}
    {Y : J ⥤ Over S} {q : ∀ j, (Z.obj j).left ⟶ (Y.obj j).left} (h : IsCartesian t Z Y q) :
    Z ≅ Y ⋙ Over.pullback t :=
  NatIso.ofComponents (fun j => Over.isoMk (h.isPullback j).isoPullback
    (by simp)) (fun {j j'} g => by
      ext
      apply pullback.hom_ext
      · simp only [Functor.comp_obj, Over.comp_left, Over.pullback_obj_left, Over.isoMk_hom_left,
          Category.assoc, IsPullback.isoPullback_hom_fst, h.w g, Functor.comp_map,
          Over.pullback_map_left]
        rw [pullback.lift_fst, ← Category.assoc, IsPullback.isoPullback_hom_fst]
      · simp only [Functor.comp_obj, Over.comp_left, Over.pullback_obj_left, Over.isoMk_hom_left,
          Category.assoc, IsPullback.isoPullback_hom_snd, Over.w, Functor.comp_map,
          Over.pullback_map_left]
        rw [pullback.lift_snd, IsPullback.isoPullback_hom_snd])

/-- The isomorphism of a cartesian diagram with the base change, followed by the first projection,
is the given map to the diagram below. -/
public lemma IsCartesian.iso_hom_app_left_fst {S T : Scheme.{u}} {t : T ⟶ S} {Z : J ⥤ Over T}
    {Y : J ⥤ Over S} {q : ∀ j, (Z.obj j).left ⟶ (Y.obj j).left} (h : IsCartesian t Z Y q)
    (j : J) : (h.iso.hom.app j).left ≫ pullback.fst (Y.obj j).hom t = q j := by
  simp [IsCartesian.iso]

end Cartesian

/-! ### The fibre conclusions -/

section Fibre

variable {J : Type u} [SmallCategory J] {K L : Type u} [Field K] [Field L]

/-- Integrality, dimension and normality of the vertices of a fibre. -/
@[expose] public def FibreVert (X : J ⥤ Over (Spec (.of K))) (Z : J ⥤ Over (Spec (.of L))) : Prop :=
  ∀ j, IsIntegral (Z.obj j).left ∧
    topologicalKrullDim (Z.obj j).left = topologicalKrullDim (X.obj j).left ∧
    (IsNormal (X.obj j).left → IsNormal (Z.obj j).left)

/-- Birationality and smallness of the morphisms of a fibre. -/
@[expose] public def FibreMor (X : J ⥤ Over (Spec (.of K))) (Z : J ⥤ Over (Spec (.of L))) : Prop :=
  ∀ {j j'} (g : j ⟶ j'),
    (Mori.IsBirationalMorphism (X.map g).left → Mori.IsBirationalMorphism (Z.map g).left) ∧
    (Fourfold.IsSmallMorphism (X.obj j).hom (X.obj j').hom (X.map g).left →
      Fourfold.IsSmallMorphism (Z.obj j).hom (Z.obj j').hom (Z.map g).left)

/-- Decompositions of fibre products as finite disjoint unions of vertices in a fibre. -/
@[expose] public def FibreDecomp (X : J ⥤ Over (Spec (.of K))) (Z : J ⥤ Over (Spec (.of L))) :
    Prop :=
  ∀ {j₁ j₂ j : J} (f : j₁ ⟶ j) (g : j₂ ⟶ j) (n : ℕ) (w : Fin n → J)
    (a : ∀ k, w k ⟶ j₁) (b : ∀ k, w k ⟶ j₂) (h : ∀ k, a k ≫ f = b k ≫ g),
    IsIso (Sigma.desc fun k => pullback.lift (f := (X.map f).left) (g := (X.map g).left)
      (X.map (a k)).left (X.map (b k)).left
      (by rw [← Over.comp_left, ← Over.comp_left, ← X.map_comp, ← X.map_comp, h k])) →
    IsIso (Sigma.desc fun k => pullback.lift (f := (Z.map f).left)
      (g := (Z.map g).left)
      (Z.map (a k)).left (Z.map (b k)).left
      (by rw [← Over.comp_left, ← Over.comp_left, ← Functor.map_comp, ← Functor.map_comp,
        h k]))

open Classical in
/-- The coefficients of a finite sum of multiples of prime divisors. -/
private lemma coeff_sum_single {X : Scheme.{u}} {m : ℕ} (P : Fin m → Mori.PrimeDivisor X)
    (q : Fin m → ℚ) (E : Mori.PrimeDivisor X) :
    (∑ l, Finsupp.single (P l) (q l) : Mori.QDivisor X).coeff E =
      ∑ l, if P l = E then q l else 0 := by
  change (∑ l, Finsupp.single (P l) (q l)) E = _
  rw [Finsupp.finset_sum_apply]
  exact Finset.sum_congr rfl fun l _ => Finsupp.single_apply

/-- Two finite sums of multiples of prime divisors with the same coefficients, along index
families with the same coincidences, have the same coefficients along corresponding primes. -/
public lemma coeff_sum_single_eq {X Y : Scheme.{u}} {m : ℕ} (P : Fin m → Mori.PrimeDivisor X)
    (Ps : Fin m → Mori.PrimeDivisor Y) (h : ∀ l l', P l = P l' ↔ Ps l = Ps l') (q : Fin m → ℚ)
    (l : Fin m) :
    (∑ l, Finsupp.single (P l) (q l) : Mori.QDivisor X).coeff (P l) =
      (∑ l, Finsupp.single (Ps l) (q l) : Mori.QDivisor Y).coeff (Ps l) := by
  classical
  rw [coeff_sum_single, coeff_sum_single]
  exact Finset.sum_congr rfl fun l' _ => by simp only [h l' l]

/-- The support of a finite sum of multiples of prime divisors is the union of the supports of
the primes with nonzero coefficient. -/
public lemma coe_supp_sum_single {X : Scheme.{u}} {m : ℕ} (P : Fin m → Mori.PrimeDivisor X)
    (q : Fin m → ℚ) :
    ((∑ l, Finsupp.single (P l) (q l) : Mori.QDivisor X).supp : Set X) =
      ⋃ l ∈ {l | (∑ l, Finsupp.single (P l) (q l) : Mori.QDivisor X).coeff (P l) ≠ 0},
        (P l).support := by
  classical
  ext x
  rw [SetLike.mem_coe, Mori.DivisorWithCoeffs.mem_supp_iff]
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
  refine ⟨fun ⟨E, hE, hx⟩ => ?_, fun ⟨l, hl, hx⟩ => ⟨P l, hl, hx⟩⟩
  obtain ⟨l, rfl⟩ : ∃ l, P l = E := by
    by_contra! hne
    exact hE ((coeff_sum_single P q E).trans (Finset.sum_eq_zero fun l _ => if_neg (hne l)))
  exact ⟨l, hE, hx⟩

/-- A projective log resolution `π` of `X` whose boundary is supported on the closed subset `C`:
a proper birational morphism from a smooth scheme, projective, with exceptional set of pure
codimension one, such that `Ex(π) ∪ π⁻¹(C)` is a simple normal crossing divisor. -/
public structure IsLogResolutionAlong {k : Type u} [Field k] {X W : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (C : TopologicalSpace.Closeds X) (π : W ⟶ X) : Prop where
  /-- `π` is a smooth resolution of `X`. -/
  isSmoothResolution : Mori.IsSmoothResolution sX π
  /-- The exceptional set of `π` has pure codimension one. -/
  isPureCodimOne : Mori.IsPureCodimOne (Mori.exceptionalSet π)
  /-- `Ex(π) ∪ π⁻¹(C)` is a simple normal crossing subset. -/
  isSNCSubset : Mori.IsSNCSubset (π ≫ sX) (Mori.exceptionalSet π ⊔ C.preimage π.continuous)
  /-- `π` is a projective morphism. -/
  isProjectiveMorphism : IsProjectiveMorphism π

/-- Being a projective log resolution of `(X, B)` depends only on the support of `B`. -/
public lemma isLogResolution_iff_along {k : Type u} [Field k] {X W : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (B : Mori.QDivisor X) (π : W ⟶ X) :
    Fourfold.IsLogResolution sX B π ↔ IsLogResolutionAlong sX B.supp π :=
  ⟨fun h => ⟨h.toIsLogResolution.toIsSmoothResolution,
      h.toIsLogResolution.isPureCodimOne_exceptionalSet,
      by simpa only [Mori.QDivisor.supp_toRDivisor] using h.toIsLogResolution.isSNCSubset,
      h.isProjectiveMorphism⟩,
    fun h => ⟨⟨h.isSmoothResolution, h.isPureCodimOne,
      by simpa only [Mori.QDivisor.supp_toRDivisor] using h.isSNCSubset⟩,
      h.isProjectiveMorphism⟩⟩

/-- Log resolutions along one morphism `μ` and their crepant boundaries in a fibre. -/
@[expose] public def FibreCrepantAt (X : J ⥤ Over (Spec (.of K)))
    (hint : ∀ j, IsIntegral (X.obj j).left)
    (Z : J ⥤ Over (Spec (.of L))) {j₀ j : J} (μ : j ⟶ j₀) : Prop :=
  ∀ [IsLocallyNoetherian (X.obj j₀).left]
    [IsNormal (X.obj j₀).left] (n : ℕ)
    {m : ℕ} {c : Fin m → J} (ι : ∀ l, c l ⟶ j₀)
    (P : Fin m → Mori.PrimeDivisor (X.obj j₀).left) (q : Fin m → ℚ)
    {m' : ℕ} {c' : Fin m' → J} (ι' : ∀ l, c' l ⟶ j)
    (P' : Fin m' → Mori.PrimeDivisor (X.obj j).left) (q' : Fin m' → ℚ),
    haveI := hint j₀
    (∀ l, (P l).support = Set.range (X.map (ι l)).left.base) →
    (∀ l, (P' l).support = Set.range (X.map (ι' l)).left.base) →
    Fourfold.IsLogResolution (X.obj j₀).hom (∑ l, Finsupp.single (P l) (q l)) (X.map μ).left →
    (∃ (K₀ : Mori.Divisor (X.obj j₀).left) (hW : _) (hμ : _),
      Mori.IsCrepantBoundary (X.obj j₀).hom n K₀ (∑ l, Finsupp.single (P l) (q l))
        (X.map μ).left hW hμ (∑ l, Finsupp.single (P' l) (q' l))) →
    ∀ [IsIntegral (Z.obj j₀).left]
      [IsLocallyNoetherian (Z.obj j₀).left]
      [IsNormal (Z.obj j₀).left],
    ∃ (Ps : Fin m → Mori.PrimeDivisor (Z.obj j₀).left)
      (Ps' : Fin m' → Mori.PrimeDivisor (Z.obj j).left),
      (∀ l, (Ps l).support = Set.range (Z.map (ι l)).left.base) ∧
      (∀ l, (Ps' l).support = Set.range (Z.map (ι' l)).left.base) ∧
      Fourfold.IsLogResolution (Z.obj j₀).hom
        (∑ l, Finsupp.single (Ps l) (q l)) (Z.map μ).left ∧
      ∃ (Ks : Mori.Divisor (Z.obj j₀).left) (hW : _) (hμ : _),
        Mori.IsCrepantBoundary (Z.obj j₀).hom n Ks
          (∑ l, Finsupp.single (Ps l) (q l)) (Z.map μ).left hW hμ
          (∑ l, Finsupp.single (Ps' l) (q' l))

/-- Log resolutions and their crepant boundaries in a fibre. -/
@[expose] public def FibreCrepant (X : J ⥤ Over (Spec (.of K)))
    (hint : ∀ j, IsIntegral (X.obj j).left)
    (Z : J ⥤ Over (Spec (.of L))) : Prop :=
  ∀ {j₀ j : J} (μ : j ⟶ j₀), FibreCrepantAt X hint Z μ

end Fibre

/-! ### A common projective embedding -/

section Embedding

/-- `ℙⁿ_S` embeds into `ℙ^{nm+n+m}_S` over `S`, as `ℙⁿ_S × {pt}` followed by the Segre
embedding. -/
private lemma exists_isClosedImmersion_projectiveSpaceOver (n m : ℕ) (S : Scheme.{u}) :
    ∃ a : projectiveSpaceOver n S ⟶ projectiveSpaceOver (n * m + n + m) S,
      IsClosedImmersion a ∧
        a ≫ (projectiveSpaceOver (n * m + n + m) S ↘ S) = projectiveSpaceOver n S ↘ S := by
  obtain ⟨e₁, he₁, he₁o⟩ := Stacks.AlgebraicGeometry.SegreProdIso.exists_segreEmbedding n m S
  let c : S ⟶ projectiveSpaceOver m S :=
    AffineSpace.homOfVector (𝟙 S) (fun _ : ULift.{u} {j : Fin (m + 1) // j ≠ 0} => 0) ≫
      projectiveSpaceOver.affineChart m 0 Equiv.ulift S
  have hc : c ≫ (projectiveSpaceOver m S ↘ S) = 𝟙 S := by
    rw [Category.assoc, projectiveSpaceOver.affineChart_over, AffineSpace.homOfVector_over]
  let a₁ : projectiveSpaceOver n S ⟶
      pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver m S ↘ S) :=
    pullback.lift (𝟙 _) ((projectiveSpaceOver n S ↘ S) ≫ c) (by rw [Category.assoc, hc]; simp)
  have : IsClosedImmersion a₁ := by
    have : IsClosedImmersion (a₁ ≫ pullback.fst (projectiveSpaceOver n S ↘ S)
        (projectiveSpaceOver m S ↘ S)) := by
      rw [pullback.lift_fst]
      infer_instance
    exact IsClosedImmersion.of_comp a₁ (pullback.fst _ _)
  refine ⟨a₁ ≫ e₁, inferInstance, ?_⟩
  rw [Category.assoc, he₁o, pullback.lift_fst_assoc, Category.id_comp]

variable {K : Type u} [Field K] {J : Type u} [SmallCategory J] [Fintype J]

/-- Finitely many projective `K`-schemes embed into one projective space over `K`. -/
public lemma exists_common_embedding (X : J ⥤ Over (Spec (.of K)))
    (hproj : ∀ j, IsProjective (X.obj j).hom) :
    ∃ (n : ℕ) (ιX : ∀ j, (X.obj j).left ⟶ projectiveSpaceOver n (Spec (.of K))),
      (∀ j, IsClosedImmersion (ιX j)) ∧
        ∀ j, ιX j ≫ (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K)) = (X.obj j).hom := by
  classical
  choose n i hi hio using fun j =>
    (isProjective_iff_isProjectiveMorphism_of_isAffine _).mp (hproj j)
  let P := ∏ j, (n j + 1)
  have hP : 0 < P := Finset.prod_pos fun j _ => Nat.succ_pos _
  have hemb : ∀ j, ∃ a : projectiveSpaceOver (n j) (Spec (.of K)) ⟶
      projectiveSpaceOver (P - 1) (Spec (.of K)), IsClosedImmersion a ∧
      a ≫ (projectiveSpaceOver (P - 1) (Spec (.of K)) ↘ Spec (.of K)) =
        projectiveSpaceOver (n j) (Spec (.of K)) ↘ Spec (.of K) := fun j => by
    have hdvd : n j + 1 ∣ P := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
    have hd : (n j + 1) * (P / (n j + 1)) = P := Nat.mul_div_cancel' hdvd
    have hpos : 0 < P / (n j + 1) := Nat.div_pos (Nat.le_of_dvd hP hdvd) (Nat.succ_pos _)
    obtain ⟨q, hq⟩ : ∃ q, P / (n j + 1) = q + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    have hN : n j * q + n j + q = P - 1 := by
      rw [hq] at hd
      have : n j * q + n j + q + 1 = (n j + 1) * (q + 1) := by ring
      omega
    rw [← hN]
    exact exists_isClosedImmersion_projectiveSpaceOver _ _ _
  choose a ha hao using hemb
  refine ⟨P - 1, fun j => i j ≫ a j, fun j => inferInstance, fun j => ?_⟩
  rw [Category.assoc, hao, hio]

end Embedding

/-- **Closed subschemes of finite presentation of a cofiltered limit descend to a stage**
(Stacks 01ZM, 01ZP): such a closed subscheme is the base change of a closed subscheme of some
stage. -/
public theorem exists_isClosedImmersion_model_of_isLimit
    {I : Type*} [Category I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (Z : Over c.pt) [IsClosedImmersion Z.hom] (hZ : FinitePresentation Z.hom) :
    ∃ (i : I) (Y : Over (D.obj i)), IsClosedImmersion Y.hom ∧
      Nonempty (Z ≅ (Over.pullback (c.π.app i)).obj Y) := by
  obtain ⟨i, Y, hY, ⟨e⟩⟩ :=
    AlgebraicGeometry.LimitFPObjectDescent.exists_model_of_finitePresentation D c hc Z hZ
  have : LocallyOfFinitePresentation Y.hom := hY.1
  have : QuasiCompact Y.hom := hY.2.1
  have : QuasiSeparated Y.hom := hY.2.2
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  let T : Over (D.obj i) := Over.mk (𝟙 _)
  have : CompactSpace T.left := inferInstanceAs (CompactSpace (D.obj i))
  have : QuasiSeparatedSpace T.left := inferInstanceAs (QuasiSeparatedSpace (D.obj i))
  have hT {V : Scheme.{u}} (q : V ⟶ D.obj i) : IsIso ((Over.pullback q).obj T).hom := by
    change IsIso (pullback.snd (𝟙 (D.obj i)) q)
    infer_instance
  let f : Y ⟶ T := Over.homMk Y.hom (by simp [T])
  have : LocallyOfFiniteType f.left := inferInstanceAs (LocallyOfFiniteType Y.hom)
  have hlim : IsClosedImmersion ((Over.pullback (c.π.app i)).obj Y).hom := by
    have hiso : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget c.pt).map e.inv))
    rw [show ((Over.pullback (c.π.app i)).obj Y).hom = e.inv.left ≫ Z.hom from e.inv.w.symm]
    infer_instance
  have : IsClosedImmersion ((Over.pullback (c.π.app i)).map f).left := by
    have := hT (c.π.app i)
    have : IsClosedImmersion (((Over.pullback (c.π.app i)).map f).left ≫
        ((Over.pullback (c.π.app i)).obj T).hom) := by
      rwa [((Over.pullback (c.π.app i)).map f).w]
    exact IsClosedImmersion.of_comp _ ((Over.pullback (c.π.app i)).obj T).hom
  obtain ⟨j, g, hg⟩ :=
    AlgebraicGeometry.exists_isClosedImmersion_baseChange_of_isLimit D c hc i Y T f
  have : IsClosedImmersion ((Over.pullback (D.map g)).map f).left := hg
  have hclosed : IsClosedImmersion ((Over.pullback (D.map g)).obj Y).hom := by
    have := hT (D.map g)
    rw [← ((Over.pullback (D.map g)).map f).w]
    infer_instance
  exact ⟨j, (Over.pullback (D.map g)).obj Y, hclosed,
    ⟨e ≪≫ eqToIso (congrArg (fun h ↦ (Over.pullback h).obj Y) (c.w g).symm) ≪≫
      (Over.pullbackComp (c.π.app j) (D.map g)).app Y⟩⟩

/-! ### Isomorphisms of modules descend to a stage -/

section ModuleIso

open Stacks.AlgebraicGeometry.ModuleLimits in
/-- **An isomorphism at the limit between pullbacks of modules of finite presentation on a stage
gives an isomorphism at a later stage** (Stacks 01ZR). -/
public lemma exists_iso_of_isLimit {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D)
    (hc : IsLimit c) [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] (i : I)
    (A B : (D.obj i).Modules) (hA : A.IsFinitePresentation) (hB : B.IsFinitePresentation)
    (φ : (Scheme.Modules.pullback (c.π.app i)).obj A ≅
      (Scheme.Modules.pullback (c.π.app i)).obj B) :
    ∃ (k : I) (e : k ⟶ i),
      Nonempty ((Scheme.Modules.pullback (D.map e)).obj A ≅
        (Scheme.Modules.pullback (D.map e)).obj B) := by
  obtain ⟨j, e, Φ, hΦ⟩ := exists_canonical_eq_of_isLimit D c hc i A B ‹_› ‹_› φ.hom
  have hΦ' : (Scheme.Modules.pullback (c.π.app j)).map Φ =
      canHom (c.π.app j) (D.map e) (c.π.app i) (c.w e) A ≫ φ.hom ≫
        inv (canHom (c.π.app j) (D.map e) (c.π.app i) (c.w e) B) := by
    rw [← Category.assoc, ← hΦ]
    simp
  have hiso : IsIso ((Scheme.Modules.pullback (c.π.app j)).map Φ) := by
    rw [hΦ']
    infer_instance
  have := isFinitePresentation_pullback (D.map e) A
  have := isFinitePresentation_pullback (D.map e) B
  obtain ⟨k, g, hg⟩ := exists_isIso_pullback_map_of_isLimit D c hc j _ _ Φ hiso
  exact ⟨k, g ≫ e, ⟨(canIso (D.map g) (D.map e) _ (D.map_comp g e).symm A).symm ≪≫
    asIso ((Scheme.Modules.pullback (D.map g)).map Φ) ≪≫
      canIso (D.map g) (D.map e) _ (D.map_comp g e).symm B⟩⟩

end ModuleIso

/-! ### A bound on the degree of an invertible sheaf of differential forms -/

section DifferentialFormsBound

/-- The linear equivalence of stalks induced by an isomorphism of sheaves of modules. -/
private def stalkLinearEquivOfIso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (x : X) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf x ≃ₗ[X.presheaf.stalk x]
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.val.presheaf x :=
  LinearEquiv.ofBijective (Stacks.SheafOfModules.FlatShortExact.stalkLinearMap e.hom x)
    ((ConcreteCategory.isIso_iff_bijective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
        ((PresheafOfModules.toPresheaf (structureSheafRing X.toRingedSpace).obj).mapIso
          ((SheafOfModules.forget _).mapIso e))).hom).mp inferInstance)

/-- If the sheaf `Ωⁿ_{X/S}` of an integral scheme `X` locally of finite type over `S` is
isomorphic to an invertible sheaf, then `n` is at most the dimension of `Ω_{X/S}` at the generic
point. -/
public lemma le_finrank_of_iso_relativeDifferentialForms {X S : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ S) [LocallyOfFiniteType f] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (n : ℕ) (e : L ≅ Scheme.Hom.relativeDifferentialForms f n) :
    n ≤ Module.finrank (X.presheaf.stalk (genericPoint X))
      ((Scheme.Hom.relativeDifferentials f).presheaf.stalk (genericPoint X)) := by
  have h1 :=
      Stacks.AlgebraicGeometry.ReflexiveModules.finrank_stalk_genericPoint_eq_one_of_isInvertible L
  have h2 : Module.finrank (X.presheaf.stalk (genericPoint X)) (L.presheaf.stalk (genericPoint X)) =
      Module.finrank (X.presheaf.stalk (genericPoint X))
        ((Scheme.Hom.relativeDifferentialForms f n).presheaf.stalk (genericPoint X)) :=
    LinearEquiv.finrank_eq (stalkLinearEquivOfIso e _)
  have h3 : Module.finrank (X.presheaf.stalk (genericPoint X))
        (((Scheme.Hom.relativeDifferentials f).exteriorPower n).presheaf.stalk (genericPoint X)) =
      Module.finrank (X.presheaf.stalk (genericPoint X))
        (⋀[X.presheaf.stalk (genericPoint X)]^n
          ((Scheme.Hom.relativeDifferentials f).presheaf.stalk (genericPoint X))) :=
    LinearEquiv.finrank_eq (SheafOfModules.exteriorPowerStalkEquiv
      (Scheme.Modules.exteriorAlgebra (Scheme.Hom.relativeDifferentials f))
      (Scheme.Modules.exteriorGenerator _) (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _) n
      (genericPoint X))
  have h4 := h1.symm.trans (h2.trans h3)
  have := Scheme.Hom.isFiniteType_relativeDifferentials f
  have hfin : Module.Finite (X.presheaf.stalk (genericPoint X))
      ((Scheme.Hom.relativeDifferentials f).presheaf.stalk (genericPoint X)) :=
    SheafOfModules.finite_stalk X.sheaf (Scheme.Hom.relativeDifferentials f) (genericPoint X)
  rw [exteriorPower.finrank_eq] at h4
  by_contra hn
  rw [Nat.choose_eq_zero_of_lt (not_le.mp hn)] at h4
  exact one_ne_zero h4

end DifferentialFormsBound

/-! ### Geometric properties of fibres -/

section GeometricFibres

/-- Two field extensions of a field have a common extension. -/
private lemma exists_field_algHom_algHom (F K K' : Type u) [Field F] [Field K] [Field K']
    [Algebra F K] [Algebra F K'] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra F L),
      Nonempty (K →ₐ[F] L) ∧ Nonempty (K' →ₐ[F] L) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (TensorProduct F K K')
  letI := Ideal.Quotient.field m
  exact ⟨_ ⧸ m, inferInstance, inferInstance,
    ⟨(Ideal.Quotient.mkₐ F m).comp Algebra.TensorProduct.includeLeft⟩,
    ⟨(Ideal.Quotient.mkₐ F m).comp Algebra.TensorProduct.includeRight⟩⟩

/-- The spectrum of a field extension is flat and surjective over the spectrum of the base. -/
public lemma flat_surjective_specMap {k L : Type u} [Field k] [Field L] (φ : k →+* L) :
    Flat (Spec.map (CommRingCat.ofHom φ)) ∧ Surjective (Spec.map (CommRingCat.ofHom φ)) :=
  ⟨Flat.SpecMap_iff.mpr (RingHom.Flat.of_isField (Field.toIsField _) _),
    ⟨fun _ => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩⟩

/-- A field-valued point factors through the residue field of its image point. -/
public lemma eq_specMap_comp_fromSpecResidueField {K : Type u} [Field K] {X : Scheme.{u}}
    (t : Spec (.of K) ⟶ X) :
    t = Spec.map (Scheme.SpecToEquivOfField K X t).2 ≫
      X.fromSpecResidueField (Scheme.SpecToEquivOfField K X t).1 :=
  ((Scheme.SpecToEquivOfField K X).symm_apply_apply t).symm

/-- A base change `T ×_Y X ⟶ T` is geometrically `P` as soon as `T` lands in a set of points of
`Y` over which the fibres of `X ⟶ Y` are geometrically `P`. -/
public lemma geometrically_pullback_snd_of_fibers {P : ObjectProperty Scheme.{u}}
    [P.IsClosedUnderIsomorphisms] {X Y T : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y) (U : Set Y)
    (hg : Set.range g.base ⊆ U) (hU : ∀ y ∈ U, geometrically P (f.fiberToSpecResidueField y)) :
    geometrically P (pullback.snd f g) := by
  rw [geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ y
  set e := Scheme.SpecToEquivOfField K Y (y ≫ g) with he
  have hy : y ≫ g = Spec.map e.2 ≫ Y.fromSpecResidueField e.1 :=
    eq_specMap_comp_fromSpecResidueField _
  have hsU : e.1 ∈ U := hg ⟨(y.base (IsLocalRing.closedPoint K)), rfl⟩
  refine P.prop_of_iso (pullbackLeftPullbackSndIso f g y).symm ?_
  refine P.prop_of_iso (pullback.congrHom rfl hy).symm ?_
  exact P.prop_of_iso (pullbackLeftPullbackSndIso f _ _)
    (pullback_of_geometrically (hU _ hsU) K (Spec.map e.2))

/-- **Geometric irreducibility is detected over a separably closed extension**: if
`X = Y ×_F K` is irreducible and `K ⊇ F` is separably closed, then `Y` is geometrically
irreducible over `F`. -/
public lemma geometricallyIrreducible_of_isPullback {F K : Type u} [Field F] [Field K]
    [IsSepClosed K] [Algebra F K] {Y X : Scheme.{u}} (f : Y ⟶ Spec (.of F))
    (g : X ⟶ Spec (.of K)) (p : X ⟶ Y)
    (h : IsPullback p g f (Spec.map (CommRingCat.ofHom (algebraMap F K)))) [IrreducibleSpace X] :
    GeometricallyIrreducible f := by
  constructor
  rw [geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K' _ y
  obtain ⟨φ, rfl⟩ := Spec.map_surjective y
  letI : Algebra F K' := φ.hom.toAlgebra
  obtain ⟨L, _, _, ⟨σ⟩, ⟨τ⟩⟩ := exists_field_algHom_algHom F K K'
  let σ' : Spec (.of L) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom σ.toRingHom)
  let τ' : Spec (.of L) ⟶ Spec (.of K') := Spec.map (CommRingCat.ofHom τ.toRingHom)
  have hσ : σ' ≫ Spec.map (CommRingCat.ofHom (algebraMap F K)) =
      Spec.map (CommRingCat.ofHom (algebraMap F L)) := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact σ.commutes x
  have hτ : τ' ≫ Spec.map φ = Spec.map (CommRingCat.ofHom (algebraMap F L)) := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact τ.commutes x
  have i1 : IrreducibleSpace (pullback (C := Scheme.{u}) g σ') :=
    pullback_of_geometrically (geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed K X g).1
      L _
  have i2 : IrreducibleSpace (pullback (C := Scheme.{u}) f
      (Spec.map (CommRingCat.ofHom (algebraMap F L)))) :=
    ObjectProperty.prop_of_iso (P := fun X : Scheme.{u} => IrreducibleSpace X)
      (((IsPullback.of_hasPullback g σ').paste_horiz h).isoPullback ≪≫
        pullback.congrHom rfl hσ) i1
  have i3 : IrreducibleSpace (pullback (C := Scheme.{u}) (pullback.snd f (Spec.map φ)) τ') :=
    ObjectProperty.prop_of_iso (P := fun X : Scheme.{u} => IrreducibleSpace X)
      ((pullback.congrHom rfl hτ).symm ≪≫ (pullbackLeftPullbackSndIso f _ _).symm) i2
  obtain ⟨-, h₄⟩ := flat_surjective_specMap τ.toRingHom
  have : Surjective (pullback.fst (pullback.snd f (Spec.map φ)) τ') :=
    MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback (pullback.snd f (Spec.map φ)) τ').flip h₄
  exact Function.Surjective.irreducibleSpace
    (pullback.fst (pullback.snd f (Spec.map φ)) τ').continuous
    (pullback.fst (pullback.snd f (Spec.map φ)) τ').surjective

/-- **Geometric integrality is detected over a separably closed extension** of a perfect
ground field: if `X = Y ×_F K` is integral, `K ⊇ F` separably closed and `F` perfect, then `Y`
is geometrically integral over `F`. -/
public lemma geometricallyIntegral_of_isPullback {F K : Type u} [Field F] [Field K]
    [IsSepClosed K] [PerfectField F] [Algebra F K] {Y X : Scheme.{u}} (f : Y ⟶ Spec (.of F))
    (g : X ⟶ Spec (.of K)) (p : X ⟶ Y)
    (h : IsPullback p g f (Spec.map (CommRingCat.ofHom (algebraMap F K)))) [IsIntegral X] :
    GeometricallyIntegral f := by
  obtain ⟨h₁, h₂⟩ := flat_surjective_specMap (algebraMap F K)
  have : Flat p := MorphismProperty.of_isPullback h.flip h₁
  have : Surjective p := MorphismProperty.of_isPullback h.flip h₂
  have : IsReduced Y := isReduced_of_flat_of_surjective p
  have : GeometricallyReduced f := geometricallyReduced_of_isReduced f
  have : GeometricallyIrreducible f := geometricallyIrreducible_of_isPullback f g p h
  exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f

/-- Extending the ground field does not change the dimension. -/
public lemma geometrically_topologicalKrullDim_eq {F : Type u} [Field F] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of F)) [LocallyOfFiniteType f] :
    geometrically (fun Z : Scheme.{u} => topologicalKrullDim Z = topologicalKrullDim Y) f := by
  rw [geometrically_iff_of_commRing]
  intro K _ _ Z fst snd h
  exact topologicalKrullDim_baseChange F K fst snd f h

/-- Integrality of schemes is invariant under isomorphism. -/
public lemma isClosedUnderIsomorphisms_isIntegral :
    ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme.{u}) IsIntegral :=
  ⟨fun e h => have := h; IsIntegral.of_isIso e.hom⟩

/-- Normality of schemes is invariant under isomorphism. -/
public lemma isClosedUnderIsomorphisms_isNormal :
    ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme.{u}) IsNormal :=
  ⟨fun {X Y} e h => isNormal_of_forall_exists_flat fun y => ⟨X, e.hom, inferInstance, h,
    ⟨e.inv y, by simp⟩⟩⟩

/-- The Krull dimension of a scheme is invariant under isomorphism. -/
public lemma isClosedUnderIsomorphisms_topologicalKrullDim (d : WithBot ℕ∞) :
    ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme.{u})
      (fun X => topologicalKrullDim X = d) :=
  ⟨fun e h => (Scheme.homeoOfIso e).isHomeomorph.topologicalKrullDim_eq.symm.trans h⟩

end GeometricFibres

/-! ### Decompositions of fibre products under base change -/

section Decomp

variable {J : Type u} [SmallCategory J]

/-- Finite coproducts commute with base change: if each `Z k` is the base change of `Y k` along
`t`, then `∐ Z k` is the base change of `∐ Y k`. -/
private lemma isPullback_sigmaMap {S T : Scheme.{u}} (t : T ⟶ S) {n : ℕ} (Y : Fin n → Over S)
    (Z : Fin n → Over T) (q : ∀ k, (Z k).left ⟶ (Y k).left)
    (hq : ∀ k, IsPullback (q k) (Z k).hom (Y k).hom t) :
    IsPullback (Limits.Sigma.map q) (Limits.Sigma.desc fun k => (Z k).hom)
      (Limits.Sigma.desc fun k => (Y k).hom) t := by
  have hw : ∀ k, (q k ≫ Limits.Sigma.ι (fun k => (Y k).left) k) ≫
      Limits.Sigma.desc (fun k => (Y k).hom) = (Z k).hom ≫ t := fun k => by
    simp [(hq k).w]
  let l : ∀ k, (Z k).left ⟶ pullback (Limits.Sigma.desc fun k => (Y k).hom) t := fun k =>
    pullback.lift (q k ≫ Limits.Sigma.ι (fun k => (Y k).left) k) (Z k).hom (hw k)
  have hl₁ : ∀ k, l k ≫ pullback.fst _ _ = q k ≫ Limits.Sigma.ι (fun k => (Y k).left) k :=
    fun k => pullback.lift_fst _ _ _
  have hl₂ : ∀ k, l k ≫ pullback.snd _ _ = (Z k).hom := fun k => pullback.lift_snd _ _ _
  have hl : ∀ k, IsPullback (l k) (q k) (pullback.fst (Limits.Sigma.desc fun k => (Y k).hom) t)
      (Limits.Sigma.ι (fun k => (Y k).left) k) := fun k =>
    IsPullback.of_right (by rw [hl₂, Limits.Sigma.ι_desc]; exact (hq k).flip) (hl₁ k)
      (IsPullback.of_hasPullback _ t).flip
  have h1 : Limits.Sigma.desc (fun k => Limits.Sigma.ι (fun k => (Y k).left) k) = 𝟙 _ := by
    ext
    simp
  have h2 := FinitaryPreExtensive.isIso_sigmaDesc_fst
    (fun k => Limits.Sigma.ι (fun k => (Y k).left) k)
    (pullback.fst (Limits.Sigma.desc fun k => (Y k).hom) t) (h1 ▸ inferInstance)
  have h3 : Limits.Sigma.desc l = Limits.Sigma.map (fun k => (hl k).isoPullback.hom) ≫
      Limits.Sigma.desc (fun k => pullback.fst
          (pullback.fst (Limits.Sigma.desc fun k => (Y k).hom) t)
        (Limits.Sigma.ι (fun k => (Y k).left) k)) := by
    refine Limits.Sigma.hom_ext _ _ fun k => ?_
    simp [(hl k).isoPullback_hom_fst]
  have : IsIso (Limits.Sigma.desc l) := by
    rw [h3]
    have : IsIso (Limits.Sigma.map (fun k => (hl k).isoPullback.hom)) :=
      (Limits.Sigma.mapIso (fun k => (hl k).isoPullback)).isIso_hom
    infer_instance
  refine IsPullback.of_iso_pullback ⟨by ext k; simp [(hq k).w]⟩ (asIso (Limits.Sigma.desc l)) ?_ ?_
  · ext k
    simp [hl₁]
  · ext k
    simp [hl₂]

/-- The comparison map from a finite coproduct of vertices to a fibre product of vertices. -/
@[expose] public def decompMap {S : Scheme.{u}} (D : J ⥤ Over S) {j₁ j₂ j : J}
    (f : j₁ ⟶ j) (g : j₂ ⟶ j) {n : ℕ} (w : Fin n → J) (a : ∀ k, w k ⟶ j₁)
    (b : ∀ k, w k ⟶ j₂) (h : ∀ k, a k ≫ f = b k ≫ g) :
    (∐ fun k => (D.obj (w k)).left) ⟶ pullback (D.map f).left (D.map g).left :=
  Limits.Sigma.desc fun k => pullback.lift (D.map (a k)).left (D.map (b k)).left
    (by rw [← Over.comp_left, ← Over.comp_left, ← Functor.map_comp, ← Functor.map_comp, h k])

/-- The underlying topological space of a finite coproduct of schemes is the disjoint union of
the underlying spaces. -/
@[expose] public def finiteSigmaHomeomorph {n : ℕ} (F : Fin n → Scheme.{u}) :
    (Σ i, F i) ≃ₜ (∐ F :) :=
  TopCat.homeoOfIso ((colimit.isoColimitCocone ⟨_, TopCat.sigmaCofanIsColimit _⟩).symm ≪≫
    (PreservesCoproduct.iso Scheme.forgetToTop F).symm)

/-- A disjoint union of finitely many quasi-separated spaces is quasi-separated. -/
public lemma quasiSeparatedSpace_finite_sigma
    {ι' : Type*} [Finite ι'] {X : ι' → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, QuasiSeparatedSpace (X i)] : QuasiSeparatedSpace (Σ i, X i) := by
  constructor
  intro U V hU hUc hV hVc
  have h (i : ι') : IsCompact (Sigma.mk i ⁻¹' (U ∩ V)) := by
    rw [Set.preimage_inter]
    exact QuasiSeparatedSpace.inter_isCompact _ _
      (isOpen_sigma_iff.mp hU i)
      (Topology.IsClosedEmbedding.sigmaMk.isCompact_preimage hUc)
      (isOpen_sigma_iff.mp hV i)
      (Topology.IsClosedEmbedding.sigmaMk.isCompact_preimage hVc)
  have hc := Set.isCompact_sigma (s := Set.univ) (t := fun i => Sigma.mk i ⁻¹' (U ∩ V))
    Set.finite_univ (fun i _ => h i)
  convert hc using 1
  ext x
  simp

/-- The number of summands of a decomposition of a fibre product into nonempty vertices is
bounded by the number of possible summands. -/
public lemma le_card_of_isIso_decompMap {S' : Scheme.{u}} [Fintype J]
    [∀ i j : J, Fintype (i ⟶ j)] (D : J ⥤ Over S') (hne : ∀ j, Nonempty (D.obj j).left)
    {j₁ j₂ j : J} (f : j₁ ⟶ j) (g : j₂ ⟶ j) {n : ℕ} (w : Fin n → J) (a : ∀ k, w k ⟶ j₁)
    (b : ∀ k, w k ⟶ j₂) (h : ∀ k, a k ≫ f = b k ≫ g) (hiso : IsIso (decompMap D f g w a b h)) :
    n ≤ Fintype.card (Σ v : J, (v ⟶ j₁) × (v ⟶ j₂)) := by
  classical
  let F : (Σ v : J, (v ⟶ j₁) × (v ⟶ j₂)) →
      Set (pullback (C := Scheme.{u}) (D.map f).left (D.map g).left) :=
    fun x => if hx : x.2.1 ≫ f = x.2.2 ≫ g then Set.range ⇑(pullback.lift (D.map x.2.1).left
      (D.map x.2.2).left (by rw [← Over.comp_left, ← Over.comp_left, ← Functor.map_comp,
        ← Functor.map_comp, hx])) else ∅
  have hF : ∀ k, F ⟨w k, a k, b k⟩ =
      Set.range ⇑(Limits.Sigma.ι (fun k => (D.obj (w k)).left) k ≫ decompMap D f g w a b h) := by
    intro k
    simp only [F, dif_pos (h k), decompMap, Limits.Sigma.ι_desc]
  have hinj := (decompMap D f g w a b h).isOpenEmbedding.injective
  have : Function.Injective
      (fun k : Fin n => (⟨w k, a k, b k⟩ : Σ v : J, (v ⟶ j₁) × (v ⟶ j₂))) := by
    intro k k' hkk'
    by_contra hne'
    obtain ⟨x⟩ := hne (w k)
    have h1 : (Limits.Sigma.ι (fun k => (D.obj (w k)).left) k ≫ decompMap D f g w a b h) x ∈
        F ⟨w k, a k, b k⟩ := by rw [hF]; exact ⟨x, rfl⟩
    rw [show (⟨w k, a k, b k⟩ : Σ v : J, (v ⟶ j₁) × (v ⟶ j₂)) = ⟨w k', a k', b k'⟩ from hkk',
      hF] at h1
    obtain ⟨y, hy⟩ := h1
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hy
    have := (sigmaι_eq_iff _ _ _ _ _).mp (hinj hy)
    exact hne' (congrArg Sigma.fst this).symm
  simpa using Fintype.card_le_of_injective _ this

variable {S T : Scheme.{u}} {t : T ⟶ S} {Z : J ⥤ Over T} {Y : J ⥤ Over S}
  {q : ∀ j, (Z.obj j).left ⟶ (Y.obj j).left}

/-- The comparison of fibre products of the vertices of a cartesian diagram. -/
private abbrev IsCartesian.pullbackMap (hc : IsCartesian t Z Y q) {j₁ j₂ j : J}
    (f : j₁ ⟶ j) (g : j₂ ⟶ j) :
    pullback (Z.map f).left (Z.map g).left ⟶ pullback (Y.map f).left (Y.map g).left :=
  pullback.map _ _ _ _ (q j₁) (q j₂) (q j) (hc.w f) (hc.w g)

/-- Fibre products of vertices commute with base change. -/
private lemma IsCartesian.isPullback_pullbackMap (hc : IsCartesian t Z Y q) {j₁ j₂ j : J}
    (f : j₁ ⟶ j) (g : j₂ ⟶ j) :
    IsPullback (hc.pullbackMap f g) (pullback.fst _ _ ≫ (Z.obj j₁).hom)
      (pullback.fst _ _ ≫ (Y.obj j₁).hom) t := by
  have outer := (IsPullback.of_hasPullback (Z.map f).left (Z.map g).left).flip.paste_horiz
    (hc.isPullback_map g)
  rw [hc.w f] at outer
  have top : IsPullback (hc.pullbackMap f g) (pullback.fst _ _) (pullback.fst _ _) (q j₁) :=
    IsPullback.of_right (by rwa [pullback.lift_snd]) (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback (Y.map f).left (Y.map g).left).flip
  exact top.paste_vert (hc.isPullback j₁)

variable (hc : IsCartesian t Z Y q) {j₁ j₂ j : J} (f : j₁ ⟶ j) (g : j₂ ⟶ j) {n : ℕ}
  (w : Fin n → J) (a : ∀ k, w k ⟶ j₁) (b : ∀ k, w k ⟶ j₂) (h : ∀ k, a k ≫ f = b k ≫ g)

private lemma decompMap_fst_hom {S' : Scheme.{u}} (D : J ⥤ Over S') :
    decompMap D f g w a b h ≫ pullback.fst _ _ ≫ (D.obj j₁).hom =
      Limits.Sigma.desc fun k => (D.obj (w k)).hom := by
  refine Limits.Sigma.hom_ext _ _ fun k => ?_
  simp only [decompMap, Limits.Sigma.ι_desc_assoc, Limits.Sigma.ι_desc, pullback.lift_fst_assoc,
    Over.w]

include hc in
private lemma IsCartesian.isPullback_sigmaMap_decomp :
    IsPullback (Limits.Sigma.map fun k => q (w k))
      (decompMap Z f g w a b h ≫ pullback.fst _ _ ≫ (Z.obj j₁).hom)
      (decompMap Y f g w a b h ≫ pullback.fst _ _ ≫ (Y.obj j₁).hom) t := by
  have s := isPullback_sigmaMap t (fun k => Y.obj (w k)) (fun k => Z.obj (w k)) (fun k => q (w k))
    (fun k => hc.isPullback (w k))
  rwa [← decompMap_fst_hom f g w a b h Z, ← decompMap_fst_hom f g w a b h Y] at s

/-- The comparison map of a cartesian diagram is the base change of the comparison map of the
diagram below. -/
private lemma IsCartesian.isPullback_decompMap :
    IsPullback (Limits.Sigma.map fun k => q (w k)) (decompMap Z f g w a b h)
      (decompMap Y f g w a b h) (hc.pullbackMap f g) := by
  refine IsPullback.of_bot (hc.isPullback_sigmaMap_decomp f g w a b h) ?_
    (hc.isPullback_pullbackMap f g)
  refine Limits.Sigma.hom_ext _ _ fun k => ?_
  simp only [decompMap, Limits.Sigma.ι_map_assoc, Limits.Sigma.ι_desc_assoc, Limits.Sigma.ι_desc]
  apply pullback.hom_ext
  · simp only [Category.assoc, IsCartesian.pullbackMap, pullback.map, pullback.lift_fst,
      pullback.lift_fst_assoc]
    exact (hc.w (a k)).symm
  · simp only [Category.assoc, IsCartesian.pullbackMap, pullback.map, pullback.lift_snd,
      pullback.lift_snd_assoc]
    exact (hc.w (b k)).symm

include hc in
/-- A base change of an isomorphic comparison map is an isomorphism. -/
public lemma IsCartesian.isIso_decompMap (hY : IsIso (decompMap Y f g w a b h)) :
    IsIso (decompMap Z f g w a b h) :=
  MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms Scheme.{u})
    (hc.isPullback_decompMap f g w a b h) hY

/-- The comparison map of a diagram over `S`, as a morphism over `S`. -/
public abbrev decompOver {S' : Scheme.{u}} (D : J ⥤ Over S') :
    Over.mk (decompMap D f g w a b h ≫ pullback.fst _ _ ≫ (D.obj j₁).hom) ⟶
      Over.mk (pullback.fst (D.map f).left (D.map g).left ≫ (D.obj j₁).hom) :=
  Over.homMk (decompMap D f g w a b h)

include hc in
/-- The comparison map of a cartesian diagram is an isomorphism exactly when the base change of
the comparison map of the diagram below is. -/
public lemma IsCartesian.isIso_decompMap_iff :
    IsIso (decompMap Z f g w a b h) ↔
      IsIso ((Over.pullback t).map (decompOver f g w a b h Y)).left := by
  have s := hc.isPullback_sigmaMap_decomp f g w a b h
  have hm := hc.isPullback_decompMap f g w a b h
  have hp := hc.isPullback_pullbackMap f g
  refine (MorphismProperty.isomorphisms Scheme.{u}).arrow_mk_iso_iff
    (Arrow.isoMk s.isoPullback hp.isoPullback ?_)
  apply pullback.hom_ext
  · simp only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom, Category.assoc,
      Over.pullback_map_left, pullback.lift_fst, Over.homMk_left]
    erw [IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_fst]
    exact hm.w
  · simp only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom, Category.assoc,
      Over.pullback_map_left, pullback.lift_snd]
    erw [IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_hom_snd]

/-- If `ψ₁` and `ψ₂` are base changes of `φ` along `b₁` and `b₂ = c ≫ b₁`, then `ψ₂` is a base
change of `ψ₁` along `c`. -/
public lemma isPullback_of_isPullback_comp {C : Type*} [Category C] {A₁ A₂ B₁ B₂ P Q : C}
    {ψ₁ : A₁ ⟶ B₁} {ψ₂ : A₂ ⟶ B₂} {φ : P ⟶ Q} {a₁ : A₁ ⟶ P} {b₁ : B₁ ⟶ Q} {a₂ : A₂ ⟶ P}
    {b₂ : B₂ ⟶ Q} (h₁ : IsPullback a₁ ψ₁ φ b₁) (h₂ : IsPullback a₂ ψ₂ φ b₂) (c : B₂ ⟶ B₁)
    (hc : c ≫ b₁ = b₂) : ∃ a : A₂ ⟶ A₁, IsPullback a ψ₂ ψ₁ c :=
  ⟨h₁.lift a₂ (ψ₂ ≫ c) (by rw [Category.assoc, hc, h₂.w]),
    IsPullback.of_right (by rwa [h₁.lift_fst, hc]) (h₁.lift_snd _ _ _) h₁⟩

include hc in
/-- The restriction of a morphism of a cartesian diagram to the preimage of an open is the base
change of the restriction below. -/
public lemma IsCartesian.isPullback_restrict {j j' : J} (g : j ⟶ j') (V : (Y.obj j).left.Opens) :
    IsPullback (q j ∣_ V) ((q j ⁻¹ᵁ V).ι ≫ (Z.map g).left) (V.ι ≫ (Y.map g).left) (q j') :=
  (isPullback_morphismRestrict (q j) V).paste_vert (hc.isPullback_map g)

/-- A morphism of irreducible schemes that restricts to an open immersion on a nonempty open is
birational. -/
public theorem isBirationalMorphism_of_isOpenImmersion_ι_comp' {X' Y' : Scheme.{u}}
    [IrreducibleSpace X'] [IrreducibleSpace Y'] (f' : X' ⟶ Y') (W : X'.Opens)
    [IsOpenImmersion (W.ι ≫ f')] (hW : (W : Set X').Nonempty) : Mori.IsBirationalMorphism f' := by
  let O := (W.ι ≫ f').opensRange
  have hrange : Set.range (W.ι ≫ f').base = O := rfl
  have hle : W ≤ f' ⁻¹ᵁ O := fun w hw => (hrange ▸ ⟨⟨w, hw⟩, rfl⟩ : f'.base w ∈ (O : Set Y'))
  have hc := f'.resLE_comp_ι hle
  have : IsOpenImmersion (f'.resLE O W hle ≫ O.ι) := hc ▸ inferInstance
  have := IsOpenImmersion.of_comp (f'.resLE O W hle) O.ι
  have : Surjective (f'.resLE O W hle) := by
    refine ⟨fun y => ?_⟩
    obtain ⟨w, hw⟩ : O.ι.base y ∈ Set.range (W.ι ≫ f').base := by
      rw [hrange, ← Scheme.Opens.range_ι O]
      exact ⟨y, rfl⟩
    exact ⟨w, O.ι.isOpenEmbedding.injective (by rw [← Scheme.Hom.comp_apply, hc, hw])⟩
  obtain ⟨w, hw⟩ := hW
  exact MMP.Flips.isBirationalMorphism_of_isIso_resLE f' W O ⟨w, hw⟩
    ⟨_, ⟨⟨w, hw⟩, rfl⟩⟩ hle (isIso_of_mono_of_strongEpi _)

include hc in
/-- The restriction of a morphism of a cartesian diagram over the preimage of an open of the
target is the base change of the restriction below. -/
public lemma IsCartesian.isPullback_restrictTarget {j j' : J} (g : j ⟶ j')
    (V : (Y.obj j').left.Opens) :
    IsPullback ((q j).resLE ((Y.map g).left ⁻¹ᵁ V) ((Z.map g).left ⁻¹ᵁ (q j' ⁻¹ᵁ V))
        (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hc.w g]))
      ((Z.map g).left ∣_ (q j' ⁻¹ᵁ V)) ((Y.map g).left ∣_ V) (q j' ∣_ V) := by
  have outer := (AlgebraicGeometry.isPullback_morphismRestrict (Z.map g).left
    (q j' ⁻¹ᵁ V)).flip.paste_horiz (hc.isPullback_map g)
  refine IsPullback.of_right ?_ ?_ (AlgebraicGeometry.isPullback_morphismRestrict
    (Y.map g).left V).flip
  · rwa [Scheme.Hom.resLE_comp_ι, morphismRestrict_ι]
  · rw [← cancel_mono V.ι, Category.assoc, Category.assoc, morphismRestrict_ι, morphismRestrict_ι,
      Scheme.Hom.resLE_comp_ι_assoc, morphismRestrict_ι_assoc, hc.w g]

end Decomp

/-- The preimage of a finite supremum of closed sets is the union of the preimages. -/
public lemma preimage_coe_finset_sup {X Y : Type*} [TopologicalSpace Y] {ι : Type*}
    (f : X → Y) (s : Finset ι) (g : ι → TopologicalSpace.Closeds Y) :
    f ⁻¹' ((s.sup g : TopologicalSpace.Closeds Y) : Set Y) = ⋃ i ∈ s, f ⁻¹' (g i : Set Y) := by
  simp only [TopologicalSpace.Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion,
    Set.preimage_iUnion]
  rfl

/-- The image of the second projection of a pullback square is the preimage of the image of the
opposite side. -/
public lemma range_snd_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) :
    Set.range snd.base = g.base ⁻¹' Set.range f.base := by
  simpa only [Set.preimage_univ, Set.image_univ] using
    Scheme.image_preimage_eq_of_isPullback h Set.univ

/-- The closed subscheme cut out by the inverse image of an ideal sheaf is the pullback of the
closed subscheme. -/
public lemma isPullback_comap {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) :
    IsPullback (I.comap f).subschemeι ((I.comapIso f).hom ≫ pullback.snd f I.subschemeι) f
      I.subschemeι :=
  IsPullback.of_iso_pullback ⟨by rw [Category.assoc, ← pullback.condition,
      ← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]⟩ (I.comapIso f)
    (Scheme.IdealSheafData.comapIso_hom_fst I f) rfl

/-- Inverse images of ideal sheaves commute with finite suprema. -/
public lemma comap_finset_sup {X Y : Scheme.{u}} {ι : Type*} (s : Finset ι)
    (I : ι → Y.IdealSheafData) (f : X ⟶ Y) :
    (s.sup I).comap f = s.sup fun i => (I i).comap f := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Scheme.IdealSheafData.comap_bot f
  | insert i s _ ih => rw [Finset.sup_insert, Scheme.IdealSheafData.comap_sup, ih,
      Finset.sup_insert]

/-- A property of morphisms respecting isomorphisms holds for one second projection of a pullback
square as soon as it holds for another one of the same cospan. -/
public lemma prop_snd_of_isPullback {C : Type*} [Category C] (P : MorphismProperty C)
    [P.RespectsIso] {Q Q' X Y Z : C} {fst : Q ⟶ X} {snd : Q ⟶ Y} {fst' : Q' ⟶ X} {snd' : Q' ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g)
    (hs : P snd) : P snd' := by
  rw [← h'.isoIsPullback_hom_snd X Y h]
  exact (MorphismProperty.cancel_left_of_respectsIso P _ _).mpr hs

/-- Images commute with base change: in a pullback square, the preimage of the image of a subset
is the image of its preimage. -/
public lemma preimage_image_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (T : Set X) :
    g.base ⁻¹' (f.base '' T) = snd.base '' (fst.base ⁻¹' T) :=
  (Scheme.image_preimage_eq_of_isPullback h T).symm

/-! ### Dimensions of closed subsets of the fibres -/

section FibreDimension

/-- A base change of `g : W ⟶ Spec R` along `Spec K ⟶ Spec R` is a base change of the base
change of `g` to any intermediate field `R → F → K`. -/
public lemma exists_isPullback_snd_specMap {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    {W X : Scheme.{u}} (g : W ⟶ Spec (.of R)) (F : Type u) [Field F] [Algebra R F] [Algebra F K]
    [IsScalarTower R F K] {p : X ⟶ W} {s : X ⟶ Spec (.of K)}
    (hp : IsPullback p s g (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :
    ∃ a : X ⟶ pullback g (Spec.map (CommRingCat.ofHom (algebraMap R F))),
      IsPullback a s (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R F))))
        (Spec.map (CommRingCat.ofHom (algebraMap F K))) :=
  isPullback_of_isPullback_comp (IsPullback.of_hasPullback _ _) hp _ <| by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

/-- The base change of the reduced closed subscheme on `D` along `g` has the dimension of the
preimage of `D`. -/
public lemma topologicalKrullDim_pullback_subschemeι {Y F : Scheme.{u}}
    (D : TopologicalSpace.Closeds Y) (g : F ⟶ Y) :
    topologicalKrullDim
        (pullback (C := Scheme.{u}) (Scheme.IdealSheafData.vanishingIdeal D).subschemeι g) =
      topologicalKrullDim (g ⁻¹' D) := by
  have hι : Set.range (Scheme.IdealSheafData.vanishingIdeal D).subschemeι = D := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    simp
  rw [← Stacks.AlgebraicGeometry.ComponentDegrees.topologicalKrullDim_range_eq
    (pullback.snd _ g), Scheme.Pullback.range_snd, hι]

/-- **Dimension bounds on closed subsets spread to the fibres.** Let `Y` be of finite presentation
over a Noetherian domain `R` with base change `X` to a field `K ⊇ R`, and let `D ⊆ Y` be closed.
If the preimage of `D` in `X` has dimension at most `e`, then outside a proper closed subset of
`Spec R` the preimage of `D` in every field-valued fibre has dimension at most `e`. -/
public lemma exists_forall_topologicalKrullDim_preimage_le {R K : Type u} [CommRing R]
    [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [FaithfulSMul R K] {Y X : Scheme.{u}}
    (f₀ : Y ⟶ Spec (.of R)) (hf₀ : FinitePresentation f₀) (p : X ⟶ Y) (s : X ⟶ Spec (.of K))
    (hp : IsPullback p s f₀ (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (D : TopologicalSpace.Closeds Y) (e : ℕ)
    (hD : topologicalKrullDim (p ⁻¹' D) ≤ e) :
    ∃ r : R, r ≠ 0 ∧ ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of R)),
      r ∉ (t.base (IsLocalRing.closedPoint L)).asIdeal → ∀ {F : Scheme.{u}} (fst : F ⟶ Y)
        (snd : F ⟶ Spec (.of L)), IsPullback fst snd f₀ t →
          topologicalKrullDim (fst ⁻¹' D) ≤ e := by
  classical
  let I := Scheme.IdealSheafData.vanishingIdeal D
  let ι := I.subschemeι
  have := hf₀.1
  have := hf₀.2.1
  have := hf₀.2.2
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f₀
  let f := ι ≫ f₀
  have : LocallyOfFinitePresentation f :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f₀
  have : QuasiSeparatedSpace Y := (quasiSeparated_iff_quasiSeparatedSpace f₀).mp inferInstance
  have : CompactSpace I.subscheme := QuasiCompact.compactSpace_of_compactSpace ι
  have : QuasiSeparatedSpace I.subscheme := quasiSeparatedSpace_of_quasiSeparated ι
  let F := FractionRing R
  letI : Algebra F K := (IsFractionRing.lift (FaithfulSMul.algebraMap_injective R K)).toAlgebra
  have : IsScalarTower R F K := .of_algebraMap_eq fun x =>
    (IsFractionRing.lift_algebraMap (FaithfulSMul.algebraMap_injective R K) x).symm
  let αF : Spec (.of F) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R F))
  obtain ⟨_, hG⟩ := exists_isPullback_snd_specMap f F
    ((IsPullback.of_hasPullback ι p).paste_vert hp)
  have : LocallyOfFiniteType (pullback.snd f αF) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f αF) inferInstance
  have hgen : topologicalKrullDim (pullback (C := Scheme.{u}) f αF) ≤ e := by
    rw [← @topologicalKrullDim_baseChange F K _ _ _ _ _ _ _ (pullback.snd f αF) hG ‹_›]
    exact (topologicalKrullDim_pullback_subschemeι D p).trans_le hD
  obtain ⟨r, hr, H⟩ :=
    MMP.Threefold.Bridges.exists_forall_fiberDimension_le_of_genericFibre F f e hgen
  refine ⟨r, hr, fun L _ t ht F' fst snd hF => ?_⟩
  rw [← topologicalKrullDim_pullback_subschemeι D fst]
  set ε := Scheme.SpecToEquivOfField L (Spec (.of R)) t with hε
  letI alg : Algebra ((Spec (.of R)).residueField ε.1) L := ε.2.hom.toAlgebra
  obtain ⟨_, hQ'⟩ := isPullback_of_isPullback_comp
    (IsPullback.of_hasPullback f ((Spec (.of R)).fromSpecResidueField ε.1))
    ((IsPullback.of_hasPullback ι fst).paste_vert hF) (Spec.map ε.2)
    (eq_specMap_comp_fromSpecResidueField t).symm
  have hl : LocallyOfFiniteType (f.fiberToSpecResidueField ε.1) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f _) inferInstance
  rw [@topologicalKrullDim_baseChange ((Spec (.of R)).residueField ε.1) L _ _ alg _ _ _ _
    (f.fiberToSpecResidueField ε.1) hQ' hl]
  exact H ε.1 ht

/-- **Emptiness of closed subsets spreads to the fibres**: the companion of
`exists_forall_topologicalKrullDim_preimage_le` for an empty preimage over `K`. -/
public lemma exists_forall_preimage_eq_empty {R K : Type u} [CommRing R]
    [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [FaithfulSMul R K] {Y X : Scheme.{u}}
    (f₀ : Y ⟶ Spec (.of R)) (hf₀ : FinitePresentation f₀) (p : X ⟶ Y) (s : X ⟶ Spec (.of K))
    (hp : IsPullback p s f₀ (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (D : TopologicalSpace.Closeds Y) (hD : p ⁻¹' D = ∅) :
    ∃ r : R, r ≠ 0 ∧ ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of R)),
      r ∉ (t.base (IsLocalRing.closedPoint L)).asIdeal → ∀ {F : Scheme.{u}} (fst : F ⟶ Y)
        (snd : F ⟶ Spec (.of L)), IsPullback fst snd f₀ t → fst ⁻¹' D = ∅ := by
  classical
  let I := Scheme.IdealSheafData.vanishingIdeal D
  let ι := I.subschemeι
  have hι : Set.range ι = D := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    simp [I]
  have := hf₀.1
  have := hf₀.2.1
  have := hf₀.2.2
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f₀
  let f := ι ≫ f₀
  have : LocallyOfFinitePresentation f :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f₀
  have : QuasiSeparatedSpace Y := (quasiSeparated_iff_quasiSeparatedSpace f₀).mp inferInstance
  have : CompactSpace I.subscheme := QuasiCompact.compactSpace_of_compactSpace ι
  have : QuasiSeparatedSpace I.subscheme := quasiSeparatedSpace_of_quasiSeparated ι
  let F := FractionRing R
  letI : Algebra F K := (IsFractionRing.lift (FaithfulSMul.algebraMap_injective R K)).toAlgebra
  have : IsScalarTower R F K := .of_algebraMap_eq fun x =>
    (IsFractionRing.lift_algebraMap (FaithfulSMul.algebraMap_injective R K) x).symm
  let αF : Spec (.of F) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R F))
  obtain ⟨a, hG⟩ := exists_isPullback_snd_specMap f F
    ((IsPullback.of_hasPullback ι p).paste_vert hp)
  obtain ⟨-, hαK⟩ := flat_surjective_specMap (algebraMap F K)
  have hsurj : Surjective a := MorphismProperty.of_isPullback hG.flip hαK
  have hempty : IsEmpty (pullback (C := Scheme.{u}) f αF) := by
    refine ⟨fun z => ?_⟩
    obtain ⟨z', -⟩ := hsurj.surj z
    have : (pullback.snd ι p) z' ∈ p ⁻¹' D := by
      change p ((pullback.snd ι p) z') ∈ (D : Set Y)
      rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, ← hι]
      exact ⟨_, rfl⟩
    simpa [hD] using this
  obtain ⟨r, hr, H⟩ := MMP.Threefold.Bridges.exists_isEmpty_of_isEmpty_genericFibre F f hempty
  refine ⟨r, hr, fun L _ t ht F' fst snd hF => ?_⟩
  ext x
  simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
  intro hx
  rw [← hι] at hx
  obtain ⟨z, hz⟩ := hx
  obtain ⟨q, hq₁, hq₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := ι) (g := fst) z x hz
  apply ht
  have := H (pullback.fst ι fst q)
  change r ∈ (f₀ (ι (pullback.fst ι fst q))).asIdeal at this
  rw [hq₁, hz, ← Scheme.Hom.comp_apply, hF.w, Scheme.Hom.comp_apply] at this
  rwa [Subsingleton.elim (snd x) (IsLocalRing.closedPoint L)] at this

/-- **Inclusions of closed subsets spread to the fibres**: the companion of
`exists_forall_preimage_eq_empty` for an inclusion of preimages over `K`. -/
public lemma exists_forall_preimage_subset {R K : Type u} [CommRing R]
    [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [FaithfulSMul R K] {Y X : Scheme.{u}}
    (f₀ : Y ⟶ Spec (.of R)) (hf₀ : FinitePresentation f₀) (p : X ⟶ Y) (s : X ⟶ Spec (.of K))
    (hp : IsPullback p s f₀ (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (C₁ C₂ : TopologicalSpace.Closeds Y) (h : p ⁻¹' C₁ ⊆ p ⁻¹' C₂) :
    ∃ r : R, r ≠ 0 ∧ ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of R)),
      r ∉ (t.base (IsLocalRing.closedPoint L)).asIdeal → ∀ {F : Scheme.{u}} (fst : F ⟶ Y)
        (snd : F ⟶ Spec (.of L)), IsPullback fst snd f₀ t → fst ⁻¹' C₁ ⊆ fst ⁻¹' C₂ := by
  have := hf₀.1
  have := hf₀.2.1
  have := hf₀.2.2
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f₀
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f₀
  have : IsNoetherian Y := ⟨⟩
  let U : Y.Opens := ⟨(C₂ : Set Y)ᶜ, C₂.isClosed.isOpen_compl⟩
  have hU : FinitePresentation (U.ι ≫ f₀) := ⟨inferInstance, inferInstance, inferInstance⟩
  let D : TopologicalSpace.Closeds U := ⟨U.ι.base ⁻¹' C₁, C₁.isClosed.preimage U.ι.continuous⟩
  have hrestr : ∀ {F T : Scheme.{u}} (fst : F ⟶ Y) (snd : F ⟶ T) (t : T ⟶ Spec (.of R)),
      IsPullback fst snd f₀ t → IsPullback (fst ∣_ U) ((fst ⁻¹ᵁ U).ι ≫ snd) (U.ι ≫ f₀) t :=
    fun fst snd t hF => (AlgebraicGeometry.isPullback_morphismRestrict fst U).paste_vert hF
  obtain ⟨r, hr, H⟩ := exists_forall_preimage_eq_empty (R := R) (K := K) (U.ι ≫ f₀) hU (p ∣_ U)
    _ (hrestr p s _ hp) D (by
      refine Set.eq_empty_of_forall_notMem fun ⟨x, hx⟩ hD => ?_
      have h1 : p x ∈ (C₁ : Set Y) := by
        change ((p ∣_ U) ≫ U.ι).base ⟨x, hx⟩ ∈ (C₁ : Set Y) at hD
        rwa [morphismRestrict_ι] at hD
      exact hx (h h1))
  refine ⟨r, hr, fun L _ t ht F fst snd hF x hx => ?_⟩
  by_contra hx₂
  have H' := H L t ht _ _ (hrestr fst snd t hF)
  let y : (fst ⁻¹ᵁ U).toScheme := ⟨x, show fst x ∈ ((C₂ : Set Y)ᶜ) from hx₂⟩
  have : y ∈ (fst ∣_ U).base ⁻¹' (D : Set U) := by
    change ((fst ∣_ U) ≫ U.ι).base y ∈ (C₁ : Set Y)
    rwa [morphismRestrict_ι]
  simpa [H'] using this

private lemma add_one_eq_iff {a : WithBot ℕ∞} {c : ℕ∞} {d : ℕ} (h : a + (c : WithBot ℕ∞) = d)
    (hd : 1 ≤ d) : a = ((d - 1 : ℕ) : WithBot ℕ∞) ↔ c = 1 := by
  induction a using WithBot.recBotCoe with
  | bot => simp at h
  | coe a =>
    have h' : a + c = (d : ℕ∞) := by exact_mod_cast h
    induction a using ENat.recTopCoe with
    | top => simp at h'
    | coe n =>
      induction c using ENat.recTopCoe with
      | top => simp at h'
      | coe m =>
        have h'' : n + m = d := by exact_mod_cast h'
        constructor
        · intro hn
          have : n = d - 1 := ENat.coe_inj.mp (WithBot.coe_inj.mp hn)
          exact_mod_cast (show m = 1 by omega)
        · intro hm
          have : m = 1 := by exact_mod_cast hm
          exact congrArg (fun x : ℕ => ((x : ℕ∞) : WithBot ℕ∞)) (show n = d - 1 by omega)

/-- In an integral scheme of dimension `d ≥ 1` locally of finite type over a field, an
irreducible closed subset of dimension `d - 1` is the support of a prime divisor. -/
public lemma exists_primeDivisor_support_eq {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY] {d : ℕ}
    (hd : topologicalKrullDim Y = d) (hd1 : 1 ≤ d) {T : Set Y} (hT : IsClosed T)
    (hirr : IsIrreducible T) (hdim : topologicalKrullDim T = ((d - 1 : ℕ) : WithBot ℕ∞)) :
    ∃ P : AlgebraicGeometry.PrimeDivisor Y, P.support = T := by
  have hξ : closure ({hirr.genericPoint} : Set Y) = T := by
    rw [hirr.isGenericPoint_genericPoint_closure.def, hT.closure_eq]
  have h := (Flips.topologicalKrullDim_closure_singleton_add_coheight sY hirr.genericPoint).trans hd
  rw [hξ] at h
  have h1 : Order.coheight hirr.genericPoint = 1 := (add_one_eq_iff h hd1).mp hdim
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h1, ?_⟩
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne, hξ]

/-- The support of a prime divisor of an integral scheme of dimension `d` locally of finite type
over a field has dimension `d - 1`, and `1 ≤ d`. -/
public lemma topologicalKrullDim_support {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY] {d : ℕ}
    (hd : topologicalKrullDim Y = d) (P : AlgebraicGeometry.PrimeDivisor Y) :
    1 ≤ d ∧ topologicalKrullDim P.support = ((d - 1 : ℕ) : WithBot ℕ∞) := by
  have h := (Flips.topologicalKrullDim_closure_singleton_add_coheight sY P.genericPoint).trans hd
  rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure, P.coheight_genericPoint] at h
  have hd1 : 1 ≤ d := by
    by_contra hlt
    obtain rfl : d = 0 := by omega
    induction h' : topologicalKrullDim P.support using WithBot.recBotCoe with
    | bot => rw [h'] at h; simp at h
    | coe a =>
      rw [h'] at h
      have : a + 1 = 0 := mod_cast h
      exact absurd this (by simp)
  exact ⟨hd1, (add_one_eq_iff (by exact_mod_cast h) hd1).mpr rfl⟩

private lemma le_sub_of_add_eq {a : WithBot ℕ∞} {c : ℕ∞} {d r : ℕ} (h : a + (c : WithBot ℕ∞) = d)
    (hc : (r : ℕ∞) ≤ c) : r ≤ d ∧ a ≤ ((d - r : ℕ) : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => simp at h
  | coe a =>
    have h' : a + c = (d : ℕ∞) := by exact_mod_cast h
    induction a using ENat.recTopCoe with
    | top => simp at h'
    | coe n =>
      induction c using ENat.recTopCoe with
      | top => simp at h'
      | coe m =>
        have h'' : n + m = d := by exact_mod_cast h'
        have hm : r ≤ m := by exact_mod_cast hc
        exact ⟨by omega, WithBot.coe_le_coe.mpr (ENat.coe_le_coe.mpr (by omega))⟩

private lemma le_of_add_eq_of_le_sub {a : WithBot ℕ∞} {c : ℕ∞} {d r : ℕ}
    (h : a + (c : WithBot ℕ∞) = d) (ha : a ≤ ((d - r : ℕ) : WithBot ℕ∞)) (hd : r ≤ d) :
    (r : ℕ∞) ≤ c := by
  induction a using WithBot.recBotCoe with
  | bot => simp at h
  | coe a =>
    have h' : a + c = (d : ℕ∞) := by exact_mod_cast h
    have ha' : a ≤ ((d - r : ℕ) : ℕ∞) := WithBot.coe_le_coe.mp ha
    induction a using ENat.recTopCoe with
    | top => simp at h'
    | coe n =>
      induction c using ENat.recTopCoe with
      | top => exact le_top
      | coe m =>
        have h'' : n + m = d := by exact_mod_cast h'
        have hn : n ≤ d - r := ENat.coe_le_coe.mp ha'
        exact_mod_cast (show r ≤ m by omega)

/-- On an integral scheme of dimension `d` locally of finite type over a field, the points of a
closed subset have coheight at least `r` exactly when it is empty or of dimension at most
`d - r`. -/
public lemma forall_le_coheight_iff {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY] {d : ℕ}
    (hd : topologicalKrullDim Y = d) {C : Set Y} (hC : IsClosed C) (r : ℕ) :
    (∀ x ∈ C, (r : ℕ∞) ≤ Order.coheight x) ↔
      (C = ∅ ∨ (r ≤ d ∧ topologicalKrullDim C ≤ ((d - r : ℕ) : WithBot ℕ∞))) := by
  constructor
  · intro H
    rcases C.eq_empty_or_nonempty with hC0 | ⟨x₀, hx₀⟩
    · exact Or.inl hC0
    have key : ∀ x ∈ C, r ≤ d ∧
        topologicalKrullDim (closure ({x} : Set Y)) ≤ ((d - r : ℕ) : WithBot ℕ∞) := fun x hx =>
      le_sub_of_add_eq ((Flips.topologicalKrullDim_closure_singleton_add_coheight sY x).trans hd)
        (H x hx)
    exact Or.inr ⟨(key x₀ hx₀).1, topologicalKrullDim_le_of_forall_closure hC fun y hy =>
      (key y hy).2⟩
  · rintro (hC0 | ⟨hrd, hdim⟩) x hx
    · simp [hC0] at hx
    have hsub : closure ({x} : Set Y) ⊆ C := closure_minimal (Set.singleton_subset_iff.mpr hx) hC
    have hle : topologicalKrullDim (closure ({x} : Set Y)) ≤ ((d - r : ℕ) : WithBot ℕ∞) :=
      ((Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le).trans hdim
    exact le_of_add_eq_of_le_sub
      ((Flips.topologicalKrullDim_closure_singleton_add_coheight sY x).trans hd) hle hrd

end FibreDimension

/-! ### Proper birational morphisms onto normal schemes in codimension one -/

section BiregularCodimOne

/-- If `U ↪ X' ⟶ X` is an open immersion for a nonempty open `U` of an integral `X'` and `μ` is
separated, then `μ` is an isomorphism over the image of `U`. -/
private theorem isBiregular_opensRange {X' X : Scheme.{u}} [IsIntegral X'] (μ : X' ⟶ X)
    [IsSeparated μ] (U : X'.Opens) (hU : (U : Set X').Nonempty) [IsOpenImmersion (U.ι ≫ μ)] :
    Mori.IsBiregular μ (U.ι ≫ μ).opensRange := by
  set V := (U.ι ≫ μ).opensRange
  have hUV : U ≤ μ ⁻¹ᵁ V := fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩
  let e := (U.ι ≫ μ).isoOpensRange
  let s : V.toScheme ⟶ (μ ⁻¹ᵁ V).toScheme := e.inv ≫ X'.homOfLE hUV
  have hs : s ≫ μ ∣_ V = 𝟙 _ := by
    rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, Category.id_comp]
    simp only [s, Category.assoc, Scheme.homOfLE_ι_assoc]
    rw [Iso.inv_comp_eq]
    exact ((U.ι ≫ μ).isoOpensRange_hom_ι).symm
  have : IsClosedImmersion (s ≫ μ ∣_ V) := hs ▸ inferInstance
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s (μ ∣_ V)
  obtain ⟨x, hx⟩ := hU
  have : Nonempty (μ ⁻¹ᵁ V).toScheme := ⟨⟨x, hUV hx⟩⟩
  have : IsIntegral (μ ⁻¹ᵁ V).toScheme := isIntegral_of_isOpenImmersion (μ ⁻¹ᵁ V).ι
  have hrange : Set.range s = Set.univ :=
    IsClopen.eq_univ ⟨s.isClosedEmbedding.isClosed_range, s.isOpenEmbedding.isOpen_range⟩
      ⟨_, Set.mem_range_self (e.hom ⟨x, hx⟩)⟩
  have : IsIso s := (isIso_iff_isOpenImmersion_and_surjective s).mpr
    ⟨inferInstance, ⟨Set.range_eq_univ.mp hrange⟩⟩
  have : IsIso (s ≫ μ ∣_ V) := hs ▸ inferInstance
  change IsIso (μ ∣_ V)
  exact IsIso.of_isIso_comp_left s (μ ∣_ V)

/-- At a point of coheight at most one of a normal locally Noetherian integral scheme, the local
ring is a valuation ring. -/
private theorem valuationRing_stalk_of_coheight_le_one {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {y : X} (hy : Order.coheight y ≤ 1) :
    ValuationRing (X.presheaf.stalk y) := by
  rcases hy.lt_or_eq with h0 | h1
  · obtain rfl : y = genericPoint X := (Specializes.antisymm
      (Order.coheight_eq_zero.mp (Order.lt_one_iff.mp h0) (genericPoint_specializes y))
      (genericPoint_specializes y)).eq
    change ValuationRing X.functionField
    infer_instance
  · have := Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk h1
    infer_instance

/-- **A proper birational morphism onto a normal scheme is an isomorphism in codimension one**:
the points of coheight at most one lie in its biregular locus. -/
public theorem mem_biregularLocus_of_coheight_le_one_of_isNormal {X' X : Scheme.{u}}
    [IsIntegral X'] [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (μ : X' ⟶ X)
    [IsProper μ] (hμ : Mori.IsBirationalMorphism μ) {y : X} (hy : Order.coheight y ≤ 1) :
    y ∈ Mori.biregularLocus μ := by
  have : IsDominant μ := hμ.isDominant
  have := valuationRing_stalk_of_coheight_le_one hy
  obtain ⟨x', hx', hiso⟩ :=
    MMP.Intersection.exists_isIso_stalkMap_of_valuationRing μ hμ.functionFieldMap_bijective y
  have hfin : (irreducibleComponents X).Finite := by
    rw [irreducibleComponents_eq_singleton]
    exact Set.finite_singleton _
  obtain ⟨U, hxU, hU⟩ := exists_isOpenImmersion_res_of_isIso_stalkMap μ x' hfin hiso
  exact Mori.le_biregularLocus (isBiregular_opensRange μ U ⟨x', hxU⟩) ⟨⟨x', hxU⟩, hx'⟩

end BiregularCodimOne

end

end MMP.Spreading
