module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveNumber
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.Morphisms.Birational.Transform
import StacksFrontier.AlgebraicGeometry.EnriquesSeveriZariski.Multiplication
import MMP.AlgebraicGeometry.MMP.Surface.LcNefBigSemiample
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
import MMP.AlgebraicGeometry.MMP.Contraction.SemiampleSupportingDivisor
import MMP.AlgebraicGeometry.Resolution.CommonLogResolution
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Singularities.Adjunction.CartierCodimTwo
import MMP.AlgebraicGeometry.Morphisms.GenericallyFinite
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
import MMP.AlgebraicGeometry.Intersection.OneCycles
import MMP.AlgebraicGeometry.Cohomology.ProperCoherentSections
import MMP.AlgebraicGeometry.Positivity.RelativeBigDecomposition
import StacksFrontier.AlgebraicGeometry.Constructions.ProjPointOfRingHom
public import MMP.AlgebraicGeometry.Modules.FiniteLocallyFreeRankOne

/-!
# The adjoint ample model of a projective lc surface

Let `(V, B)` be an lc pair, with `B` an effective `ℚ`-divisor, on a normal projective complex
surface `V`, and let `f : V ⟶ Z` be a morphism to a projective variety such that `D = K_V + B` is
`f`-nef and `f`-big. Then `f` factors as `V ⟶ V' ⟶ Z` through a projective birational morphism
`h : V ⟶ V'` onto a normal projective surface with `h_* 𝒪_V = 𝒪_{V'}`, such that for some integer
`k > 0` the divisor `k(K_{V'} + h_* B)` is Cartier and `f'`-ample and pulls back to `kD`. Here
`K_{V'} = h_* K_V` is a canonical divisor of `V'`, and `(V', h_* B)` is again lc.

## Main results

* `MMP.Mori.IsLcPair.exists_isRelativelyAmple_of_isRelativelyNef_of_isRelativelyBig`: the
  adjoint ample model of `(V, B)` over `Z`.

## Implementation notes

Push-forward along `h` is the birational transform `MMP.Mori.RationalMap.transformDivisor` of
`h` regarded as a rational map, applied to the canonical divisor `K` and to `B`. The equality
`kD = h^* (k(K_{V'} + h_* B))` is recorded twice: as the pull-back
`MMP.Mori.Divisor.IsPullback` of the Cartier divisor `L = k(K_{V'} + h_* B)`, and as an
isomorphism `𝒪_V(kD) ≅ h^* 𝒪_{V'}(L)` of invertible sheaves. `h_* 𝒪_V = 𝒪_{V'}` is written
`∀ U, IsIso (h.app U)`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KM98]
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace Proof_lem_mmp_surface_projective_adjoint_ample_model

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- The birational transform of divisors commutes with regarding a divisor as a `ℚ`-divisor. -/
private theorem toQDivisor_transformDivisor {X Y : Scheme.{0}} (φ : RationalMap X Y)
    (D : Divisor X) :
    Divisor.toQDivisor (RationalMap.transformDivisor φ D) =
      RationalMap.transformDivisor φ (Divisor.toQDivisor D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' h h' => rw [map_add, map_add, map_add, h, h', map_add]
  | single E r =>
    have hs : ∀ {W : Scheme.{0}} (F : MMP.Mori.PrimeDivisor W),
        Divisor.toQDivisor (Finsupp.single F r) = Finsupp.single F (r : ℚ) := by
      intro W F
      ext P
      by_cases hP : F = P
      · subst hP; simp [DivisorWithCoeffs.coeff_single_self]
      · simp [DivisorWithCoeffs.coeff_single_of_ne hP]
    simp only [RationalMap.transformDivisor, DivisorWithCoeffs.mapPrimeDivisors_single, hs]
    rcases φ.transformPrimeDivisor E with _ | E'
    · simp
    · exact hs E'

/-- On an integral Noetherian scheme every Cartier divisor has a Weil divisor. -/
private theorem exists_isWeilDivisorOfCartier {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [CompactSpace X] (A : X.CartierDivisor) :
    ∃ w : Divisor X, MMP.Intersection.IsWeilDivisorOfCartier A w := by
  letI : IsNoetherian X := ⟨⟩
  have h0 : ∀ s ∈ MMP.Intersection.cartierSupport A, Order.coheight s = 0 → False := by
    intro s hs h0
    have : Ring.KrullDimLE 0 (X.presheaf.stalk s) := krullDimLE_of_coheight_le (by simp [h0])
    have : IsArtinianRing (X.presheaf.stalk s) := isArtinianRing_iff_krullDimLE_zero.mpr this
    exact MMP.Intersection.notMem_cartierSupport_of_isArtinianRing A s hs
  have hfin := finite_setOf_genericPoint_mem
    (MMP.Intersection.isClosed_cartierSupport A) h0
  refine ⟨Finsupp.ofSupportFinite (fun P => MMP.Intersection.primeDivisorOrder P A)
    (hfin.subset fun P hP => ?_), fun P => ?_⟩
  · by_contra h
    have hg : (MMP.Intersection.primeDivisorSubvariety P).genericPoint = P.genericPoint := rfl
    refine hP ((MMP.Intersection.isOrderAlong_primeDivisorOrder A P).eq_zero_of_not_subset
      fun h' => h ?_)
    show P.genericPoint ∈ MMP.Intersection.cartierSupport A
    rw [← hg]
    exact MMP.Intersection.genericPoint_mem_cartierSupport_iff.mpr h'
  · rw [DivisorWithCoeffs.coeff_apply, Finsupp.ofSupportFinite_coe]
    exact MMP.Intersection.isOrderAlong_primeDivisorOrder A P

/-- Relative basepoint freeness: some positive multiple `M = k (K + B)` is a Cartier divisor
whose sheaf is that of an `f`-free Cartier divisor `R`. -/
private theorem exists_isRelativelyFreeCartier_sheaf_iso
    {V Z : Scheme.{0}} {sV : V ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [QuasiCompact sV]
    {K : Divisor V} {B : QDivisor V} (hB : 0 ≤ B) (hlc : IsLcPair sV 2 K B)
    (hV : MMP.Mori.IsProjectiveVariety ℂ sV) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (f : V ⟶ Z) (hf : f ≫ sZ = sV)
    (hnef : QDivisor.IsRelativelyNef sV f (Divisor.toQDivisor K + B))
    (hbig : QDivisor.IsRelativelyBig f (Divisor.toQDivisor K + B)) :
    ∃ k : ℕ, 0 < k ∧ ∃ M : Divisor V, M.IsCartier ∧
      Divisor.toQDivisor M = (k : ℚ) • (Divisor.toQDivisor K + B) ∧
      ∃ R : V.CartierDivisor, IsRelativelyFreeCartier f R ∧
        Nonempty (MMP.CartierDivisor.sheaf R ≅ M.divisorialSheaf) := by
  have : CompactSpace V := (quasiCompact_iff_compactSpace sV).mp inferInstance
  have hdim : topologicalKrullDim V = 2 := by
    have := hlc.1.2.1.topologicalKrullDim_eq
    exact_mod_cast this
  have hBe : B.IsEffective := fun E => by rw [DivisorWithCoeffs.coeff_apply]; exact hB E
  obtain ⟨C, hC, m, hm, hint, hfree⟩ :=
    MMP.Fourfold.QDivisor.isRelativelySemiample_of_isLcPair_of_isRelativelyNef_of_isRelativelyBig
      sV sZ hV hdim hZ f hf K B hBe hlc hnef hbig
  set R := MMP.Mori.KCartierDivisor.realization ((m : ℚ) • C) hint with hR
  obtain ⟨w, hw⟩ := exists_isWeilDivisorOfCartier R
  refine ⟨m, hm, w, hw.isCartier, ?_, R, hfree, hw.nonempty_sheaf_iso_divisorialSheaf⟩
  refine DivisorWithCoeffs.ext' fun P => ?_
  rw [DivisorWithCoeffs.coeff_smul, hC P, Divisor.coeff_toQDivisor,
    ← (hw P).primeDivisorOrder_eq, hR, KCartierDivisor.realization, map_finsuppSum]
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [Finsupp.sum, map_zsmul, smul_eq_mul, Int.cast_sum, Int.cast_mul, Finset.mul_sum,
    Finsupp.support_smul_eq hm']
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [← Classical.choose_spec (hint E), Finsupp.smul_apply, smul_eq_mul, mul_assoc]

/-- The projection of `ℙ(G) = Proj_Z(Sym G)` is proper when `G` is quasi-coherent of finite
type. -/
private theorem isProper_relativeProj_toBase {Z : Scheme.{0}} (G : Z.Modules) [G.IsQuasicoherent]
    [G.IsFiniteType] :
    IsProper (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
      (Stacks.SymGraded.schemeSheafGradedAlgebra G
        (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent G))).toBase := by
  have h := Stacks.RelativeProj.isProper_projectiveBundleToBase_of_isFiniteType Z G
  rw [← Stacks.RelativeProj.bundlePresentationIso_inv_comp_toBase G] at h
  exact (MorphismProperty.cancel_left_of_respectsIso @IsProper _ _).mp h

/-- An `f`-ample Cartier divisor is ample over an affine neighbourhood of every point. -/
private theorem isRelativelyAmple_of_isRelativelyAmpleCartier {X Y : Scheme.{0}}
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X} {W : Divisor Y}
    (hW : MMP.Flips.IsRelativelyAmpleCartier f W) : W.IsRelativelyAmple f hW.1 := by
  obtain ⟨hWc, hamp⟩ := hW
  have := hWc.isInvertibleModule_divisorialSheaf
  intro y
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
  exact ⟨V, hV, hyV, hamp V hV⟩

/-- A projective morphism in the sense of EGA onto a scheme H-projective over a field is
H-projective, the target carrying an ample invertible sheaf. -/
private theorem isProjectiveMorphism_of_isProjective_of_isProjectiveMorphism {k : Type}
    [Field k] {Y Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of k)) (hsZ : IsProjectiveMorphism sZ)
    (f : Y ⟶ Z) (hf : IsProjective f) : IsProjectiveMorphism f := by
  haveI := Stacks.Ample.isInvertibleModule_unit (Spec (.of k))
  obtain ⟨L, hL, hLa⟩ := exists_isAmple_of_isQuasiProjective sZ _
    (Stacks.Ample.isAmple_unitModule_of_isAffine _)
    (isQuasiProjective_of_isHQuasiProjective _
      (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.1 hsZ).1)
  haveI := hL
  exact isProjectiveMorphism_of_isProjective f L hLa hf

/-- The Stein factor `V ⟶ V' ⟶ Z` of the morphism defined by a relatively free Cartier divisor
`R` with `𝒪(R) ≅ 𝒪_V(M)`, with `𝒪_V(M) ≅ h^* 𝒪_{V'}(A)` for an `f'`-ample Cartier divisor `A`. -/
private theorem exists_steinFactor
    {V Z : Scheme.{0}} {sV : V ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    (hVn : IsNormalVariety ℂ sV)
    (hV : MMP.Mori.IsProjectiveVariety ℂ sV) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (f : V ⟶ Z) (hf : f ≫ sZ = sV) {M : Divisor V} (R : V.CartierDivisor)
    (hfree : IsRelativelyFreeCartier f R)
    (eR : MMP.CartierDivisor.sheaf R ≅ M.divisorialSheaf) :
    ∃ (V' : Scheme.{0}) (_ : IsIntegral V') (_ : IsLocallyNoetherian V') (_ : IsNormal V')
      (_ : CompactSpace V') (h : V ⟶ V') (f' : V' ⟶ Z),
      h ≫ f' = f ∧ IsNormalVariety ℂ (f' ≫ sZ) ∧ MMP.Mori.IsProjectiveVariety ℂ (f' ≫ sZ) ∧
        IsProjectiveMorphism h ∧ (∀ U : V'.Opens, IsIso (h.app U)) ∧
        ∃ (A : Divisor V') (hA : A.IsCartier), A.IsRelativelyAmple f' hA ∧
          Nonempty (M.divisorialSheaf ≅ (Scheme.Modules.pullback h).obj A.divisorialSheaf) := by
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sV := hV
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sZ := hZ
  haveI : AlgebraicGeometry.IsVariety ℂ sV := hV.toIsVariety
  haveI : AlgebraicGeometry.IsVariety ℂ sZ := hZ.toIsVariety
  haveI : IsProper sV := isProper_of_isProjectiveMorphism _ hV.isProjective
  haveI : IsProper sZ := isProper_of_isProjectiveMorphism _ hZ.isProjective
  haveI : IsProper f := by
    haveI : IsProper (f ≫ sZ) := hf ▸ inferInstance
    exact IsProper.of_comp f sZ
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have key := IsRelativelyFreeCartier.steinFactor_isRelativelyAmpleCartier sV sZ hVn
    (inferInstance : AlgebraicGeometry.IsVariety ℂ sZ) f hf R hfree
  dsimp only at key
  obtain ⟨⟨Φ, hΦ, e, hdef⟩, hall⟩ := key
  obtain ⟨hΦp, hall⟩ := hall Φ hΦ e hdef
  haveI : ((Scheme.Modules.pushforward f).obj
      (MMP.CartierDivisor.sheaf R)).IsQuasicoherent :=
    ProperCoherentFiniteType.isQuasicoherent_pushforward f _ inferInstance
  haveI : ((Scheme.Modules.pushforward f).obj
      (MMP.CartierDivisor.sheaf R)).IsFiniteType :=
    (AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f
      (MMP.CartierDivisor.sheaf R)).isFiniteType
  set π := (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
      (Stacks.SymGraded.schemeSheafGradedAlgebra ((Scheme.Modules.pushforward f).obj
        (MMP.CartierDivisor.sheaf R))
      (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent _))).toBase with hπ
  haveI : IsProper π := isProper_relativeProj_toBase _
  obtain ⟨V', h, τ, ⟨hSt⟩, hhp, -, hO, -, hτ, -, hproj, -, -, -⟩ :=
    MMP.Resolution.Bridges.exists_steinFactorization_of_isVariety sV (π ≫ sZ) Φ
      (by rw [← Category.assoc, hΦ, hf])
  obtain ⟨hV'n, -, -, i1, i2, i3, A, hA, -, ⟨eA⟩⟩ := hall V' h τ hSt
  haveI := i1
  haveI := hτ
  have hhf : h ≫ τ ≫ π = f := by rw [← Category.assoc, hSt.comp, hΦ]
  haveI : AlgebraicGeometry.IsVariety ℂ ((τ ≫ π) ≫ sZ) := by
    rw [Category.assoc]; exact hV'n.1
  have hA' := isRelativelyAmple_of_isRelativelyAmpleCartier hA
  have hf'p : IsProjectiveMorphism (τ ≫ π) := by
    haveI := hA.1.isInvertibleModule_divisorialSheaf
    haveI : CompactSpace Z := (quasiCompact_iff_compactSpace sZ).mp inferInstance
    haveI : IsNoetherian Z := ⟨⟩
    exact isProjectiveMorphism_of_isProjective_of_isProjectiveMorphism sZ hZ.isProjective _
      (MMP.isProjective_of_isProper_of_isRelativelyAmple (τ ≫ π) A.divisorialSheaf hA')
  have hV'p : MMP.Mori.IsProjectiveVariety ℂ ((τ ≫ π) ≫ sZ) :=
    (AlgebraicGeometry.isProjectiveVariety_iff ℂ _).mpr ⟨inferInstance, hf'p.comp hZ.isProjective⟩
  haveI : IsQuasiProjectiveVariety ℂ sV := IsProjectiveVariety.isQuasiProjectiveVariety ℂ sV
  have hhproj : IsProjectiveMorphism h :=
    MMP.isProjectiveMorphism_of_isProper_of_isQuasiProjectiveVariety sV ((τ ≫ π) ≫ sZ) h
      (by rw [← Category.assoc, hhf, hf])
  refine ⟨V', hV'n.1.toIsIntegral, i1, i2, i3, h, τ ≫ π, hhf, by rwa [Category.assoc], hV'p, hhproj,
    hO, A, hA.1, hA', ⟨eR.symm ≪≫ eA⟩⟩

section FiberRank

variable {X : Scheme.{0}} {F G : X.Modules}

/-- `PresheafOfModules.germ_smul`, with the ring stalk written as `X.presheaf.germ`. -/
private lemma germ_smul (M : X.Modules) (y : X) (W : X.Opens) (hy : y ∈ W) (r : Γ(X, W))
    (m : Γ(M, W)) :
    TopCat.Presheaf.germ M.val.presheaf W y hy (r • m) =
      X.presheaf.germ W y hy r • TopCat.Presheaf.germ M.val.presheaf W y hy m :=
  PresheafOfModules.germ_smul M.val y W hy r m

/-- The map on stalks (as abelian groups) induced by a morphism of modules. -/
private noncomputable def stalkMapAb (φ : F ⟶ G) (y : X) :
    TopCat.Presheaf.stalk (C := Ab.{0}) F.val.presheaf y ⟶
      TopCat.Presheaf.stalk (C := Ab.{0}) G.val.presheaf y :=
  (TopCat.Presheaf.stalkFunctor Ab.{0} y).map φ.mapPresheaf

private lemma stalkMapAb_germ (φ : F ⟶ G) (y : X) {W : X.Opens} (hy : y ∈ W) (ξ : Γ(F, W)) :
    stalkMapAb φ y (TopCat.Presheaf.germ F.val.presheaf W y hy ξ) =
      TopCat.Presheaf.germ G.val.presheaf W y hy (φ.app W ξ) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply W y hy φ.mapPresheaf ξ

private lemma stalkMapAb_smul (φ : F ⟶ G) (y : X) (ρ : X.presheaf.stalk y)
    (n : TopCat.Presheaf.stalk (C := Ab.{0}) F.val.presheaf y) :
    stalkMapAb φ y (ρ • n) = ρ • stalkMapAb φ y n := by
  obtain ⟨V, hyV, ξ, hξ⟩ := X.presheaf.exists_germ_eq ρ
  obtain ⟨W, hWV, hyW, ζ, hζ⟩ := TopCat.Presheaf.exists_le_germ_eq F.val.presheaf n hyV
  subst hξ
  subst hζ
  have key : ∀ (r : Γ(X, W)) (m : Γ(F, W)),
      stalkMapAb φ y (X.presheaf.germ W y hyW r •
          TopCat.Presheaf.germ F.val.presheaf W y hyW m) =
        X.presheaf.germ W y hyW r •
          stalkMapAb φ y (TopCat.Presheaf.germ F.val.presheaf W y hyW m) := by
    intro r m
    rw [← germ_smul F y W hyW r m, stalkMapAb_germ φ y hyW,
      stalkMapAb_germ φ y hyW m, ← germ_smul G y W hyW r (φ.app W m)]
    congr 1
    exact Scheme.Modules.Hom.app_smul φ r m
  rw [← X.presheaf.germ_res_apply (homOfLE hWV) y hyW ξ]
  exact key _ ζ

private lemma stalkMapAb_inv_hom (e : F ≅ G) (x : X)
    (n : TopCat.Presheaf.stalk (C := Ab.{0}) F.val.presheaf x) :
    stalkMapAb e.inv x (stalkMapAb e.hom x n) = n := by
  obtain ⟨W, hW, ζ, rfl⟩ := TopCat.Presheaf.germ_exist F.val.presheaf n
  have h1 := stalkMapAb_germ e.hom x hW (ζ : Γ(F, W))
  have h2 := stalkMapAb_germ e.inv x hW (e.hom.app W (ζ : Γ(F, W)))
  have h3 : e.inv.app W (e.hom.app W (ζ : Γ(F, W))) = ζ := by
    have := ConcreteCategory.congr_hom (show e.hom.app W ≫ e.inv.app W = 𝟙 _ from by
      rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id]; rfl) ζ
    exact this
  rw [h1, h2, h3]

/-- The fibre rank is invariant under isomorphism of modules. -/
private theorem fiberRank_congr (e : F ≅ G) (x : X) :
    Scheme.Modules.fiberRank F x = Scheme.Modules.fiberRank G x := by
  unfold Scheme.Modules.fiberRank
  let eS : TopCat.Presheaf.stalk (C := Ab.{0}) F.val.presheaf x ≃ₗ[X.presheaf.stalk x]
      TopCat.Presheaf.stalk (C := Ab.{0}) G.val.presheaf x :=
    { toFun := stalkMapAb e.hom x
      map_add' := map_add _
      map_smul' := fun ρ n => stalkMapAb_smul e.hom x ρ n
      invFun := stalkMapAb e.inv x
      left_inv := stalkMapAb_inv_hom e x
      right_inv := stalkMapAb_inv_hom e.symm x }
  exact (TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl (X.residueField x) _) eS).finrank_eq

end FiberRank

/-- `𝒪_Y(mA) ≅ 𝒪_Y(A)^{⊗ m}` for a Cartier divisor `A`. -/
private noncomputable def divisorialSheafNsmulIso {V : Scheme.{0}} [IsLocallyNoetherian V]
    [IsNormal V] [CompactSpace V] {A : Divisor V} (hA : A.IsCartier) (m : ℕ) :
    haveI := hA.isInvertibleModule_divisorialSheaf
    (m • A).divisorialSheaf ≅ Stacks.Ample.tensorPowModule V A.divisorialSheaf (m : ℤ) := by
  haveI := hA.isInvertibleModule_divisorialSheaf
  induction m with
  | zero =>
    exact eqToIso (by rw [zero_smul]) ≪≫ Divisor.divisorialSheafZeroIso ≪≫
      (Stacks.Ample.tensorPowModuleZeroIso V A.divisorialSheaf).symm
  | succ n ih =>
    exact eqToIso (by rw [succ_nsmul]) ≪≫
      ((hA.nsmul n).divisorialSheafTensorIso hA).symm ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso ih).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj _).mapIso
        (Stacks.Ample.tensorPowModuleOneIso V A.divisorialSheaf).symm ≪≫
      Stacks.Ample.tensorPowModuleAddIso V A.divisorialSheaf (n : ℤ) 1 ≪≫
      eqToIso (by push_cast; rfl)

/-- **Generic ranks across a contraction.** If `h : V ⟶ V'` has `h_* 𝒪_V = 𝒪_{V'}` and
`𝒪_V(M) ≅ h^* 𝒪_{V'}(A)` for a Cartier divisor `A`, then `f_* 𝒪_V(jM)` and `f'_* 𝒪_{V'}(jA)` have
the same generic rank, for `f = h ≫ f'`. -/
private theorem relativeGenericRank_comp_eq
    {V V' Z : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    [IsIntegral V'] [IsLocallyNoetherian V'] [IsNormal V'] [CompactSpace V']
    (h : V ⟶ V') (f' : V' ⟶ Z) [IsDominant h] (hO : ∀ U : V'.Opens, IsIso (h.app U))
    {M : Divisor V} {A : Divisor V'} (hA : A.IsCartier)
    (e : M.divisorialSheaf ≅ (Scheme.Modules.pullback h).obj A.divisorialSheaf) (j : ℕ) :
    relativeGenericRank (h ≫ f') ((j : ℤ) • M).divisorialSheaf =
      relativeGenericRank f' ((j : ℤ) • A).divisorialSheaf := by
  have hB := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant h A
  obtain ⟨W, hW⟩ := hA.exists_isPullback (f := h) hB
  have eW := hW.divisorialSheafIso (hBc := hA)
  have hMW := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso (e ≪≫ eW.symm)
  have hjMW : ∀ n : ℕ, (((n : ℤ) • M)).LinearlyEquivalent ((n : ℤ) • W) := by
    intro n
    induction n with
    | zero => simpa using Divisor.LinearlyEquivalent.refl (0 : Divisor V)
    | succ n ih =>
      rw [Nat.cast_succ, add_smul, add_smul, one_smul, one_smul]
      exact ih.add hMW
  have hjW := hW.zsmul hA (j : ℤ)
    (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant h _)
  have e1 : ((j : ℤ) • M).divisorialSheaf ≅
      (Scheme.Modules.pullback h).obj ((j : ℤ) • A).divisorialSheaf :=
    (hjMW j).divisorialSheafIso ≪≫ hjW.divisorialSheafIso (hBc := hA.zsmul (j : ℤ))
  have hAj := (hA.zsmul (j : ℤ)).isInvertibleModule_divisorialSheaf
  haveI : IsIso h.c := NatIso.isIso_of_isIso_app _
  haveI := Scheme.Modules.isIso_unit_app_of_isIso_c h ((j : ℤ) • A).divisorialSheaf
  have e2 : (Scheme.Modules.pushforward (h ≫ f')).obj ((j : ℤ) • M).divisorialSheaf ≅
      (Scheme.Modules.pushforward f').obj ((j : ℤ) • A).divisorialSheaf :=
    (Scheme.Modules.pushforwardComp h f').symm.app _ ≪≫
      (Scheme.Modules.pushforward f').mapIso ((Scheme.Modules.pushforward h).mapIso e1 ≪≫
        (asIso ((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app _)).symm)
  unfold relativeGenericRank
  rw [fiberRank_congr e2, Scheme.Hom.comp_apply, AlgebraicGeometry.map_genericPoint_of_isDominant]

/-- **Generic ranks of multiples of a Cartier divisor grow at most like the generic fibre
dimension.** For a proper `f' : V' ⟶ Z` from a normal integral scheme and a Cartier divisor `A`,
if the generic fibre of `f'` has dimension at most `e`, then `f'_* 𝒪(jA)` has generic rank at most
`C jᵉ`. -/
private theorem exists_relativeGenericRank_le_pow
    {V' Z : Scheme.{0}} [IsIntegral V'] [IsLocallyNoetherian V'] [IsNormal V'] [CompactSpace V']
    (f' : V' ⟶ Z) [IsProper f'] {A : Divisor V'} (hA : A.IsCartier) {e : ℕ}
    (he : topologicalKrullDim (f'.fiber (f' (genericPoint V'))) ≤ e) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, 0 < j →
      (relativeGenericRank f' ((j : ℤ) • A).divisorialSheaf : ℝ) ≤ C * (j : ℝ) ^ e := by
  have hp : IsProper (f'.fiberToSpecResidueField (f' (genericPoint V'))) :=
    MMP.Flips.isProper_fiberToSpecResidueField (g := f') _
  haveI := hA.isInvertibleModule_divisorialSheaf
  set Lb := (Scheme.Modules.pullback (f'.fiberι (f' (genericPoint V')))).obj A.divisorialSheaf
  haveI : Stacks.Ample.IsInvertibleModule (f'.fiber (f' (genericPoint V'))) Lb :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback _ _
  have hcoh := @Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit
    (Z.residueField (f' (genericPoint V'))) _ _
    (f'.fiberToSpecResidueField (f' (genericPoint V'))) hp
  have hsupp : topologicalKrullDim (_root_.SheafOfModules.supp
      (SheafOfModules.unit (f'.fiber (f' (genericPoint V'))).ringCatSheaf)) ≤ e :=
    (topologicalKrullDim_subspace_le _ _).trans he
  obtain ⟨C, hC, hb⟩ :=
    @MMP.Foundations.exists_finrank_cohomologyOverField_zero_twistedSheaf_le_pow
      (Z.residueField (f' (genericPoint V'))) _ _
      (f'.fiberToSpecResidueField (f' (genericPoint V'))) hp Lb _
      (SheafOfModules.unit (f'.fiber (f' (genericPoint V'))).ringCatSheaf) hcoh e hsupp
  refine ⟨C, hC, fun j hj => ?_⟩
  have hjA := (hA.zsmul (j : ℤ)).isInvertibleModule_divisorialSheaf
  rw [relativeGenericRank_eq_finrank_fibre f' _]
  have iso :
      (Scheme.Modules.pullback (f'.fiberι (f' (genericPoint V')))).obj
          ((j : ℤ) • A).divisorialSheaf ≅
        twistedSheaf (SheafOfModules.unit (f'.fiber (f' (genericPoint V'))).ringCatSheaf)
          (fun _ : Fin 1 => Lb) (fun _ => (j : ℤ)) :=
    (Scheme.Modules.pullback (f'.fiberι (f' (genericPoint V')))).mapIso
        (eqToIso (by rw [natCast_zsmul]) ≪≫ divisorialSheafNsmulIso hA j) ≪≫
      Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso (f'.fiberι (f' (genericPoint V')))
        A.divisorialSheaf j ≪≫
      (Stacks.RelativeVeryAmple.tensorPowModuleCongr _ Lb (zero_add (j : ℤ))).symm ≪≫
      (Stacks.Ample.tensorPowModuleAddIso _ Lb 0 (j : ℤ)).symm ≪≫
      Stacks.RelativeVeryAmple.tensorModulesMapIso _ (Stacks.Ample.tensorPowModuleZeroIso _ Lb)
        (Stacks.PowerFamilyBridge.tensorPowerIsoTensorPow _
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf _) Lb (j : ℤ)).symm
  rw [AlgebraicGeometry.finrank_cohomologyOverField_eq_of_iso
    (Z.residueField (f' (genericPoint V'))) (f'.fiberToSpecResidueField (f' (genericPoint V')))
    iso 0]
  exact_mod_cast hb j (by exact_mod_cast hj)

/-- The dimension formula for a dominant morphism onto the closure of its image: `X` has the
dimension of `closure f(X)` plus that of the generic fibre. -/
private theorem topologicalKrullDim_eq_add_fiber {k : Type} [Field k] {X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX]
    [LocallyOfFiniteType sY] (f : X ⟶ Y) (hf : f ≫ sY = sX) [QuasiCompact f] :
    topologicalKrullDim X = topologicalKrullDim (closure (Set.range f.base)) +
      topologicalKrullDim (f.fiber (f (genericPoint X))) := by
  have hLY : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have hLX : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hfact : f.toImage ≫ f.imageι = f := Scheme.Hom.toImage_imageι f
  haveI : LocallyOfFiniteType (f.toImage ≫ f.imageι ≫ sY) := by
    rw [← Category.assoc, hfact, hf]
    infer_instance
  haveI : LocallyOfFiniteType f.toImage := LocallyOfFiniteType.of_comp (g := f.imageι ≫ sY)
      inferInstance
  haveI : IsLocallyNoetherian f.image := LocallyOfFiniteType.isLocallyNoetherian (f.imageι ≫ sY)
  haveI : IrreducibleSpace f.image := (irreducibleSpace_def _).2 (by
      have h := ((IrreducibleSpace.isIrreducible_univ X).image _
          f.toImage.continuous.continuousOn).closure
      rwa [Set.image_univ, (IsDominant.denseRange (f := f.toImage)).closure_eq] at h)
  obtain ⟨O, hO, hne, hform⟩ :=
      exists_isOpen_nonempty_topologicalKrullDimAt_eq_add_fiber_of_irreducibleSpace f.toImage
  have hξ : genericPoint X ∈ O := by
    obtain ⟨w, hw⟩ := hne
    exact ((genericPoint_spec X).mem_open_set_iff hO).2 ⟨w, ⟨trivial, hw⟩⟩
  have h1 := hform _ hξ
  have e1 : topologicalKrullDim X = topologicalKrullDimAt X (genericPoint X) :=
    topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X sX _
  have e2 : topologicalKrullDim f.image =
      topologicalKrullDimAt f.image (f.toImage (genericPoint X)) :=
    topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k f.image (f.imageι ≫ sY) _
  have e3 : topologicalKrullDim f.image = topologicalKrullDim (closure (Set.range f.base)) := by
    let e := f.imageι.isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr (Scheme.Hom.range_imageι f))
    exact IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph
  have hset :
      (f.toImage ⁻¹' {f.toImage (genericPoint X)} : Set X) = f ⁻¹' {f (genericPoint X)} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      rw [← hfact]
      simp only [Scheme.Hom.comp_apply]
      rw [h]
    · intro h
      rw [← hfact] at h
      simp only [Scheme.Hom.comp_apply] at h
      exact f.imageι.injective h
  have hirr : IsIrreducible (f.toImage ⁻¹' {f.toImage (genericPoint X)} : Set X) := by
    rw [← isIrreducible_iff_closure]
    have : closure (f.toImage ⁻¹' {f.toImage (genericPoint X)} : Set X) = Set.univ := by
      apply Set.eq_univ_of_univ_subset
      rw [← (genericPoint_spec X).def]
      exact closure_mono (by simp)
    exact this ▸ IrreducibleSpace.isIrreducible_univ X
  haveI : IrreducibleSpace (f.toImage.fiber (f.toImage (genericPoint X))) := by
    refine (irreducibleSpace_def _).2 ?_
    haveI : IrreducibleSpace ↥(f.toImage ⁻¹' {f.toImage (genericPoint X)} : Set X) :=
      Subtype.irreducibleSpace hirr
    let φ := f.toImage.fiberHomeo (f.toImage (genericPoint X))
    have h := (IrreducibleSpace.isIrreducible_univ
      ↥(f.toImage ⁻¹' {f.toImage (genericPoint X)} : Set X)).image φ.symm
      φ.symm.continuous.continuousOn
    rwa [Set.image_univ, φ.symm.surjective.range_eq] at h
  have e4 : topologicalKrullDim (f.toImage.fiber (f.toImage (genericPoint X))) =
      topologicalKrullDimAt (f.toImage.fiber (f.toImage (genericPoint X)))
        (f.toImage.asFiber (genericPoint X)) :=
    have := Scheme.Hom.locallyOfFiniteType_fiberToSpecResidueField f.toImage
      (f.toImage (genericPoint X))
    topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible
      (f.image.residueField (f.toImage (genericPoint X)))
      (f.toImage.fiber (f.toImage (genericPoint X)))
      (f.toImage.fiberToSpecResidueField _) _
  have e5 : topologicalKrullDim (f.toImage.fiber (f.toImage (genericPoint X))) =
      topologicalKrullDim (f.fiber (f (genericPoint X))) := by
    let e := (f.toImage.fiberHomeo (f.toImage (genericPoint X))).trans
      ((Homeomorph.setCongr hset).trans (f.fiberHomeo (f (genericPoint X))).symm)
    exact IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph
  rw [e1, h1, ← e4, ← e2, e3, e5]

/-- The dimension formula in natural numbers: with `a = dim X` and `b = dim closure f(X)`, we have
`b ≤ a` and the generic fibre has dimension `a - b`. -/
private theorem exists_dim_generic_fibre {k : Type} [Field k] {X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX]
    [LocallyOfFiniteType sY] (f : X ⟶ Y) (hf : f ≫ sY = sX) [QuasiCompact f] [CompactSpace X] :
    ∃ a b : ℕ, topologicalKrullDim X = a ∧ topologicalKrullDim (closure (Set.range f.base)) = b ∧
      b ≤ a ∧ topologicalKrullDim (f.fiber (f (genericPoint X))) = ((a - b : ℕ) : ℕ∞) := by
  have h := topologicalKrullDim_eq_add_fiber sX sY f hf
  have h1 := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sX
  have hbot : topologicalKrullDim X ≠ ⊥ := fun hb =>
    ((Order.krullDim_eq_bot_iff.mp hb).false (TopologicalSpace.IrreducibleCloseds.closureSingleton
        (genericPoint X))).elim
  induction hX : topologicalKrullDim X using WithBot.recBotCoe with
  | bot => exact absurd hX hbot
  | coe a' =>
    induction hB : topologicalKrullDim (closure (Set.range f.base)) using WithBot.recBotCoe with
    | bot =>
      rw [hX, hB] at h
      simp at h
    | coe B =>
      induction hD : topologicalKrullDim (f.fiber (f (genericPoint X))) using WithBot.recBotCoe with
      | bot =>
        rw [hX, hB, hD] at h
        simp at h
      | coe D =>
        rw [hX, hB, hD, ← WithBot.coe_add, WithBot.coe_inj] at h
        have ha : a' ≠ ⊤ := by
          rintro rfl
          exact h1 hX
        have hB' : B ≠ ⊤ := by
          rintro rfl
          rw [top_add] at h
          exact ha h
        have hD' : D ≠ ⊤ := by
          rintro rfl
          rw [add_top] at h
          exact ha h
        lift a' to ℕ using ha
        lift B to ℕ using hB'
        lift D to ℕ using hD'
        have h' : a' = B + D := by exact_mod_cast h
        refine ⟨a', B, rfl, rfl, by omega, ?_⟩
        rw [show D = a' - B by omega]

/-- If `e < d`, then `C (n m₀)^e ≤ c (n k)^d` for some `n > 0` with `n k ≥ k₀`. -/
private theorem exists_mul_pow_le_mul_pow {c C : ℝ} (hc : 0 < c) (hC : 0 < C) {k m₀ d e : ℕ}
    (hk : 0 < k) (hm₀ : 0 < m₀) (hde : e < d) (k₀ : ℤ) :
    ∃ n : ℕ, 0 < n ∧ k₀ ≤ ((n * k : ℕ) : ℤ) ∧
      C * ((n * m₀ : ℕ) : ℝ) ^ e ≤ c * ((n * k : ℕ) : ℝ) ^ d := by
  set n : ℕ := k₀.toNat + ⌈C * (m₀ : ℝ) ^ e / c⌉₊ + 1 with hn
  have hn1 : 1 ≤ n := by omega
  refine ⟨n, hn1, ?_, ?_⟩
  · calc k₀ ≤ (n : ℤ) := by
          have := Int.self_le_toNat k₀
          push_cast [hn]
          omega
      _ ≤ ((n * k : ℕ) : ℤ) := by exact_mod_cast Nat.le_mul_of_pos_right n hk
  · have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hnC : C * (m₀ : ℝ) ^ e / c ≤ n := by
      have := Nat.le_ceil (C * (m₀ : ℝ) ^ e / c)
      have h2' : ⌈C * (m₀ : ℝ) ^ e / c⌉₊ ≤ n := by rw [hn]; omega
      have h2 : ((⌈C * (m₀ : ℝ) ^ e / c⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr h2'
      linarith
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    calc C * ((n * m₀ : ℕ) : ℝ) ^ e = (C * (m₀ : ℝ) ^ e) * (n : ℝ) ^ e := by push_cast; ring
      _ ≤ (c * n) * (n : ℝ) ^ e := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [div_le_iff₀ hc] at hnC
          linarith
      _ = c * (n : ℝ) ^ (e + 1) := by ring
      _ ≤ c * (n : ℝ) ^ d := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hnR hde) hc.le
      _ ≤ c * ((n * k : ℕ) : ℝ) ^ d := by
          gcongr; push_cast; nlinarith

/-- **The Stein factor of a relatively big divisor has full dimension.** If `h : V ⟶ V'` is a
proper morphism with `h_* 𝒪_V = 𝒪_{V'}`, `𝒪_V(M) ≅ h^* 𝒪_{V'}(A)` with `A` Cartier, and a positive
multiple `M = kD` of `D` is big over `Z` for `h ≫ f'`, then `dim V' = dim V`: otherwise the generic
rank of `f_* 𝒪_V(nM) = f'_* 𝒪_{V'}(nA)` would grow at most like the dimension of the generic
fibre of `f'`, which is smaller than that of the generic fibre of `f`. -/
private theorem topologicalKrullDim_eq_of_isRelativelyBig
    {V Z V' : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)}
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    [IsIntegral V'] [IsLocallyNoetherian V'] [IsNormal V'] [CompactSpace V']
    (h : V ⟶ V') (f' : V' ⟶ Z) (hV : MMP.Mori.IsVariety ℂ (h ≫ f' ≫ sZ))
    (hV' : MMP.Mori.IsVariety ℂ (f' ≫ sZ)) (hZ : MMP.Mori.IsVariety ℂ sZ)
    [IsProper h] [IsProper f'] (hO : ∀ U : V'.Opens, IsIso (h.app U))
    {D : QDivisor V} (hbig : QDivisor.IsRelativelyBig (h ≫ f') D) {k : ℕ} (hk : 0 < k)
    {M : Divisor V} (hM : Divisor.toQDivisor M = (k : ℚ) • D)
    {A : Divisor V'} (hA : A.IsCartier)
    (e : M.divisorialSheaf ≅ (Scheme.Modules.pullback h).obj A.divisorialSheaf) :
    topologicalKrullDim V' = topologicalKrullDim V := by
  haveI : Surjective h := Scheme.Hom.surjective_of_isIso_app h hO
  haveI : IsDominant h := inferInstance
  haveI : LocallyOfFiniteType sZ := hZ.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (f' ≫ sZ) := hV'.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (h ≫ f' ≫ sZ) := hV.toLocallyOfFiniteType
  obtain ⟨a, b, ha, hb, hba, -⟩ :=
    exists_dim_generic_fibre (h ≫ f' ≫ sZ) sZ (h ≫ f') (Category.assoc _ _ _)
  obtain ⟨a', b', ha', hb', hba', hfib'⟩ := exists_dim_generic_fibre (f' ≫ sZ) sZ f' rfl
  obtain ⟨a'', b'', ha'', hb'', hba'', -⟩ := exists_dim_generic_fibre (h ≫ f' ≫ sZ) (f' ≫ sZ) h rfl
  -- `closure h(V) = V'` and `(h ≫ f')(V) = f'(V')`
  have hrh : closure (Set.range h.base) = Set.univ := by
    rw [(Scheme.Hom.surjective h).range_eq, closure_univ]
  have hrf : Set.range (h ≫ f').base = Set.range f'.base := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, (Scheme.Hom.surjective h).range_eq,
      Set.image_univ]
  have hbb : b = b' := by
    have := hb.symm.trans (hrf ▸ hb')
    exact_mod_cast this
  have ha'a : a' ≤ a := by
    have h1 : topologicalKrullDim (closure (Set.range h.base)) = topologicalKrullDim V' := by
      rw [hrh]
      exact IsHomeomorph.topologicalKrullDim_eq (Homeomorph.Set.univ V')
        (Homeomorph.Set.univ V').isHomeomorph
    have h2 : (b'' : WithBot ℕ∞) = a' := by rw [← hb'', h1, ha']
    have h3 : (a'' : WithBot ℕ∞) = a := by rw [← ha'', ha]
    have : b'' = a' := by exact_mod_cast h2
    have : a'' = a := by exact_mod_cast h3
    omega
  obtain ⟨m₀, hm₀, D₀, hD₀, hD₀c, a₀, b₀, ha₀, hb₀, c, hc, k₀, hgrow⟩ := hbig
  have ha₀a : a₀ = a := by exact_mod_cast ha₀.symm.trans ha
  have hb₀b : b₀ = b := by exact_mod_cast hb₀.symm.trans hb
  rw [ha₀a, hb₀b] at hgrow
  obtain ⟨C, hC, hbd⟩ := exists_relativeGenericRank_le_pow f' hA (e := a' - b')
    (by rw [hfib']; rfl)
  -- `k D₀ = m₀ M`
  have hdiv : (k : ℤ) • D₀ = (m₀ : ℤ) • M := Divisor.toQDivisor_injective (by
    rw [map_zsmul, map_zsmul, hD₀, hM, ← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ,
      smul_smul, smul_smul]
    push_cast; rw [mul_comm])
  have hrank : ∀ n : ℕ, relativeGenericRank (h ≫ f') (((n * k : ℕ) : ℤ) • D₀).divisorialSheaf =
      relativeGenericRank f' (((n * m₀ : ℕ) : ℤ) • A).divisorialSheaf := by
    intro n
    have : ((n * k : ℕ) : ℤ) • D₀ = ((n * m₀ : ℕ) : ℤ) • M := by
      push_cast; rw [mul_smul, hdiv, ← mul_smul]
    rw [this]
    exact relativeGenericRank_comp_eq h f' hO hA e _
  by_contra hne
  have hlt : a' < a := by
    rcases lt_or_eq_of_le ha'a with hlt | heq
    · exact hlt
    · exact absurd (by rw [ha', ha, heq]) hne
  obtain ⟨n, hn, hnk, hle⟩ := exists_mul_pow_le_mul_pow hc hC hk hm₀
    (show a' - b' < a - b by omega) k₀
  have h1 := hgrow _ hnk
  have h2 := hbd (n * m₀) (Nat.mul_pos hn hm₀)
  rw [hrank n] at h1
  push_cast at h1 h2 hle
  linarith

/-- **A contraction between varieties of the same dimension is birational.** A proper morphism
`h : V ⟶ V'` of varieties with `h_* 𝒪_V = 𝒪_{V'}` and `dim V = dim V'` is generically finite,
hence finite over a nonempty affine open of `V'`, over which `h_* 𝒪_V = 𝒪_{V'}` makes it an
isomorphism. -/
private theorem isBirationalMorphism_of_topologicalKrullDim_eq {k : Type} [Field k]
    {V V' : Scheme.{0}} {sV' : V' ⟶ Spec (.of k)} (h : V ⟶ V')
    (hV : MMP.Mori.IsVariety k (h ≫ sV')) (hV' : MMP.Mori.IsVariety k sV') [IsProper h]
    (hO : ∀ U : V'.Opens, IsIso (h.app U))
    (hdim : topologicalKrullDim V = topologicalKrullDim V') :
    IsBirationalMorphism h := by
  have : IsIntegral V := hV.toIsIntegral
  have : IsIntegral V' := hV'.toIsIntegral
  have : LocallyOfFiniteType sV' := hV'.toLocallyOfFiniteType
  have : LocallyOfFiniteType (h ≫ sV') := hV.toLocallyOfFiniteType
  have : LocallyOfFiniteType h := LocallyOfFiniteType.of_comp (g := sV') inferInstance
  have hsurj : Surjective h := Scheme.Hom.surjective_of_isIso_app h hO
  have hfin := MMP.Mori.finite_functionField_of_topologicalKrullDim_eq sV' h hdim
  let : Algebra V'.functionField V.functionField := (dominantFunctionFieldMap h).toAlgebra
  have h0 : Algebra.trdeg V'.functionField V.functionField = 0 := by
    have : Module.Finite V'.functionField V.functionField := by
      convert hfin using 3
      exact congrArg RingHom.toAlgebra (MMP.Mori.dominantFunctionFieldMap_eq_functionFieldMap h)
    exact trdeg_eq_zero_iff.mpr (Algebra.IsAlgebraic.of_finite _ _)
  obtain ⟨U, hne, hU⟩ := (exists_affineOpen_isFinite_restrict_iff_eq_genericPoint h
    (Or.inr inferInstance)).mpr (eq_genericPoint_of_trdeg_functionField_eq_zero h h0)
  have hUa : IsAffineOpen (⊤ : (U : V'.Opens).toScheme.Opens) := by
    have : IsAffine (U : V'.Opens).toScheme := U.2
    exact isAffineOpen_top _
  have hiso₁ : IsIso ((h ∣_ (U : V'.Opens)) ∣_ ⊤) := by
    rw [isIso_morphismRestrict_iff_isIso_app _ hUa, morphismRestrict_app]
    have h1 := hO ((U : V'.Opens).ι ''ᵁ ⊤)
    refine @IsIso.comp_isIso _ _ _ _ _ _ _ h1 ?_
    exact (V.presheaf.mapIso
      (eqToIso (image_morphismRestrict_preimage h (U : V'.Opens) ⊤)).op).isIso_hom
  have hiso : IsIso (h ∣_ (U : V'.Opens)) := by
    have e := morphismRestrictRestrict h (U : V'.Opens) ⊤
    rw [Scheme.Opens.ι_image_top] at e
    exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff e).mp hiso₁
  rw [← Scheme.Hom.resLE_eq_morphismRestrict] at hiso
  obtain ⟨y, hy⟩ := hne
  obtain ⟨x, rfl⟩ := hsurj.surj y
  exact MMP.Flips.isBirationalMorphism_of_isIso_resLE h _ _ ⟨x, hy⟩ ⟨_, hy⟩ le_rfl hiso

/-- The Stein factor of a relatively big adjoint divisor is birational: by
`topologicalKrullDim_eq_of_isRelativelyBig` it has the dimension of `V`, and a contraction between
varieties of the same dimension is birational. -/
private theorem isBirationalMorphism_of_isRelativelyBig
    {V Z V' : Scheme.{0}} {sV : V ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    [IsIntegral V'] [IsLocallyNoetherian V'] [IsNormal V'] [CompactSpace V']
    (hV : MMP.Mori.IsProjectiveVariety ℂ sV) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (f : V ⟶ Z) (hf : f ≫ sZ = sV)
    {D : QDivisor V} (hbig : QDivisor.IsRelativelyBig f D) {k : ℕ} (hk : 0 < k)
    {M : Divisor V} (hM : Divisor.toQDivisor M = (k : ℚ) • D)
    (h : V ⟶ V') (f' : V' ⟶ Z) (hhf : h ≫ f' = f)
    (hV'p : MMP.Mori.IsProjectiveVariety ℂ (f' ≫ sZ))
    (hh : IsProjectiveMorphism h) (hO : ∀ U : V'.Opens, IsIso (h.app U))
    {A : Divisor V'} (hA : A.IsCartier)
    (e : M.divisorialSheaf ≅ (Scheme.Modules.pullback h).obj A.divisorialSheaf) :
    IsBirationalMorphism h := by
  subst hhf hf
  haveI : IsProper h := isProper_of_isProjectiveMorphism h hh
  haveI : IsProper (f' ≫ sZ) := isProper_of_isProjectiveMorphism _ hV'p.isProjective
  haveI : IsSeparated sZ := hZ.toIsVariety.toIsSeparated
  haveI : IsProper f' := IsProper.of_comp f' sZ
  haveI : CompactSpace V :=
    (quasiCompact_iff_compactSpace ((h ≫ f') ≫ sZ)).mp hV.toIsVariety.toQuasiCompact
  have hVv : MMP.Mori.IsVariety ℂ (h ≫ f' ≫ sZ) := by
    rw [← Category.assoc]; exact hV.toIsVariety
  exact isBirationalMorphism_of_topologicalKrullDim_eq h hVv hV'p.toIsVariety hO
    (topologicalKrullDim_eq_of_isRelativelyBig h f' hVv hV'p.toIsVariety hZ.toIsVariety hO
      hbig hk hM hA e).symm

/-- Push-forward along a birational contraction `h` with `h_* 𝒪_V = 𝒪_{V'}`: if
`𝒪_V(M) ≅ h^* 𝒪_{V'}(A)` with `A` Cartier, then `h_* M ∼ A` and `M = h^* (h_* M)`. -/
private theorem linearlyEquivalent_and_isPullback_transformDivisor
    {V V' : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    [IsIntegral V'] [IsLocallyNoetherian V'] [IsNormal V'] [CompactSpace V']
    {sV' : V' ⟶ Spec (.of ℂ)} (hV'n : IsNormalVariety ℂ sV')
    (h : V ⟶ V') (hVn : IsNormalVariety ℂ (h ≫ sV')) [IsProper h] (hb : IsBirationalMorphism h)
    {M : Divisor V} {A : Divisor V'} (hA : A.IsCartier)
    (e : M.divisorialSheaf ≅ (Scheme.Modules.pullback h).obj A.divisorialSheaf) :
    Divisor.LinearlyEquivalent (RationalMap.transformDivisor h.toRationalMap M) A ∧
      ∃ hM, Divisor.IsPullback h (RationalMap.transformDivisor h.toRationalMap M) hM M := by
  haveI := hb.isDominant
  have hB := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant h A
  obtain ⟨W, hW⟩ := hA.exists_isPullback (f := h) hB
  have eW := hW.divisorialSheafIso (hBc := hA)
  obtain ⟨φ, hφ⟩ := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso (e ≪≫ eW.symm)
  obtain ⟨ψ, hψ, rfl⟩ := MMP.Fourfold.exists_pullbackRationalFunction_eq hb φ
  have hMW : M = W + principalDivisor (pullbackRationalFunction h ψ hψ) := by
    rw [← hφ]; abel
  have hT : RationalMap.transformDivisor h.toRationalMap M = A + principalDivisor ψ := by
    rw [hMW, map_add, MMP.Positivity.transformDivisor_of_isPullback_divisor hV'n hVn hb hA hW,
      MMP.Positivity.transformDivisor_principalDivisor_pullback hV'n hVn hb ψ hψ]
  refine ⟨⟨ψ, by rw [hT]; abel⟩,
    MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant h _, ?_⟩
  refine Divisor.IsPullback.of_eq (hB₁ :=
    MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant h _) hT.symm ?_
  rw [hMW]
  exact Divisor.IsPullback.add hA (Divisor.isCartier_principalDivisor ψ) _ hW
    (Divisor.isPullback_principalDivisor ψ hψ)

/-- Relative ampleness of a Cartier divisor depends only on its linear equivalence class. -/
private theorem isRelativelyAmple_of_linearlyEquivalent {X Y : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] (f : X ⟶ Y) {L A : Divisor X}
    (hLA : L.LinearlyEquivalent A) (hA : A.IsCartier) (hL : L.IsCartier)
    (hAa : A.IsRelativelyAmple f hA) : L.IsRelativelyAmple f hL := by
  haveI := hA.isInvertibleModule_divisorialSheaf
  haveI := hL.isInvertibleModule_divisorialSheaf
  intro y
  obtain ⟨V, hV, hyV, hamp⟩ := hAa y
  refine ⟨V, hV, hyV, ?_⟩
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _
    ((RingedSpaceModuleAdjunction.modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).mapIso
      hLA.divisorialSheafIso.symm)).1 hamp

/-- The total discrepancy of an lc pair in dimension at least two is at least `-1`
(Kollár–Mori 2.31(1)). -/
private theorem neg_one_le_totalDiscrep {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {d : ℕ} {K : Divisor X}
    {Δ : QDivisor X} (h : IsLcPair sX d K Δ) (hd : 2 ≤ d) : -1 ≤ totalDiscrep sX d K Δ := by
  by_contra hlt
  push Not at hlt
  have h2 := h.2
  rw [discrep_eq_bot_of_totalDiscrep_lt_neg_one h.1 hd hlt] at h2
  exact ((EReal.bot_lt_coe (-1)).trans_eq (by simp)).not_ge h2

/-- Every discrepancy of an lc pair in dimension at least two, over an exceptional divisor or not,
is at least `-1`. -/
private theorem neg_one_le_of_isDiscrepancy {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {d : ℕ} {K : Divisor X}
    {Δ : QDivisor X} (h : IsLcPair sX d K Δ) (hd : 2 ≤ d) {E : DivisorOver ℂ sX} {a : ℚ}
    (ha : IsDiscrepancy sX d K Δ E a) : (-1 : EReal) ≤ ((a : ℝ) : EReal) := by
  by_cases hE : E.IsExceptional
  · exact h.2.trans (discrep_le hE ha)
  · obtain ⟨P, -, hP⟩ := MMP.Mori.DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff h.1 E hE
    obtain rfl := ha.eq hP
    have hX := h.1.1
    exact (neg_one_le_totalDiscrep h hd).trans (totalDiscrep_le_neg_coeff hX
      (MMP.Positivity.IsPair.exists_isDiscrepancy h.1.isPair h.1.2.1
        (DivisorOver.ofPrimeDivisor ℂ hX P)))

/-- Crepant invariance: the push-forward of an lc pair along a birational contraction on which
the adjoint divisor is the pull-back of a Cartier divisor is lc. -/
private theorem isLcPair_transformDivisor
    {V V' : Scheme.{0}} {sV : V ⟶ Spec (.of ℂ)} {sV' : V' ⟶ Spec (.of ℂ)}
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [QuasiCompact sV]
    [IsIntegral V'] [IsLocallyNoetherian V'] [IsNormal V'] [CompactSpace V']
    {K : Divisor V} {B : QDivisor V} (hlc : IsLcPair sV 2 K B)
    (h : V ⟶ V') (hh : h ≫ sV' = sV) [IsProper h] (hb : IsBirationalMorphism h)
    (hV' : IsNormalVariety ℂ sV') {k : ℕ} (hk : 0 < k) {M : Divisor V} {L : Divisor V'}
    (hM : Divisor.toQDivisor M = (k : ℚ) • (Divisor.toQDivisor K + B)) (hL : L.IsCartier)
    (hLM : Divisor.toQDivisor L = (k : ℚ) • (Divisor.toQDivisor
      (RationalMap.transformDivisor h.toRationalMap K) +
        RationalMap.transformDivisor h.toRationalMap B))
    (hpb : ∃ hM, Divisor.IsPullback h L hM M) :
    IsLcPair sV' 2 (RationalMap.transformDivisor h.toRationalMap K)
      (RationalMap.transformDivisor h.toRationalMap B) := by
  subst hh
  set K' : Divisor V' := RationalMap.transformDivisor h.toRationalMap K with hK'
  set B' := RationalMap.transformDivisor h.toRationalMap B with hB'
  haveI := hb.isDominant
  have hVn : IsNormalVariety ℂ (h ≫ sV') := hlc.1.1
  haveI : CompactSpace V := (quasiCompact_iff_compactSpace (h ≫ sV')).mp inferInstance
  haveI : LocallyOfFiniteType sV' := hV'.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (h ≫ sV') := hVn.1.toLocallyOfFiniteType
  have hK := hlc.1.2.1
  -- `V'` is a surface with canonical divisor `K' = h_* K`
  have hdim : topologicalKrullDim V' = (2 : ℕ) := by
    haveI := hV'.1
    haveI := hVn.1
    rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sV' (h ≫ sV') hb]
    exact hK.topologicalKrullDim_eq
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor sV' hV' hdim
  have hK'c : K'.IsCanonicalDivisor sV' 2 :=
    MMP.Fourfold.Oai4C1.Main.isCanonicalDivisor_transformDivisor hV' hVn hb hK₀ hK
  -- `K' + B'` is `ℚ`-Cartier
  have hQ : (Divisor.toQDivisor K' + B').IsQCartier :=
    ⟨k, by exact_mod_cast hk.ne', L, by rw [hLM, ← Int.cast_smul_eq_zsmul ℚ]; push_cast; rfl, hL⟩
  have hP : IsPairWith sV' 2 K' B' := ⟨hV', hK'c, hQ⟩
  -- `K + B` is the pull-back of `K' + B'`
  obtain ⟨hMs, hLpb⟩ := hpb
  have hpbQ : ∃ hQB, (Divisor.toQDivisor K' + B').IsPullback h hQB (Divisor.toQDivisor K + B) := by
    refine ⟨MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' h _,
      fun m hm D hD hDc => ?_⟩
    have hgen := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant h
    obtain ⟨D', hD'⟩ := hDc.exists_isPullback (f := h) (hgen D)
    refine ⟨D', ?_, hD'⟩
    -- `k D = m L`, so `k D' = m M` by uniqueness of pull-backs
    have hkD : (k : ℤ) • D = (m : ℤ) • L := Divisor.toQDivisor_injective (by
      rw [map_zsmul, map_zsmul, hD, hLM, smul_comm, ← Int.cast_smul_eq_zsmul ℚ (k : ℤ)]
      push_cast; rfl)
    have h1 := hD'.zsmul hDc (k : ℤ) (hgen _)
    have h2 := hLpb.zsmul hL (m : ℤ) (hgen _)
    have hkD' : (k : ℤ) • D' = (m : ℤ) • M :=
      Divisor.IsPullback.eq (hL.zsmul (m : ℤ)) (h1.of_eq hkD) h2
    have h3 := congrArg Divisor.toQDivisor hkD'
    rw [map_zsmul, map_zsmul, hM] at h3
    refine DivisorWithCoeffs.ext' fun P => ?_
    have h4 := congrArg (fun G : QDivisor V => G.coeff P) h3
    simp only [DivisorWithCoeffs.coeff_smul, zsmul_eq_mul, smul_eq_mul, Int.cast_natCast] at h4 ⊢
    have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
    apply mul_left_cancel₀ hk0
    linear_combination h4
  have hcrep := MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hP.isPair h hVn hb hK'c hK
    (Or.inr ⟨inferInstance, rfl, hpbQ⟩)
  refine ⟨hP, le_discrep_iff.mpr fun D a _ ha => ?_⟩
  obtain ⟨E, hE⟩ := MMP.Mori.exists_divisorOver_comap_eq hVn hb D
  exact neg_one_le_of_isDiscrepancy hlc le_rfl ((hcrep.2 E D hE a).mpr ha)

end Proof_lem_mmp_surface_projective_adjoint_ample_model

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

open Proof_lem_mmp_surface_projective_adjoint_ample_model in
/-- **The adjoint ample model of a projective lc surface.** Let `(V, B)` be an lc pair, `B ≥ 0`,
with canonical divisor `K` on a normal projective complex surface, and `f : V ⟶ Z` a morphism to a
projective variety such that `K + B` is `f`-nef and `f`-big. Then there are a normal projective
surface `V'`, a projective birational morphism `h : V ⟶ V'` with `h_* 𝒪_V = 𝒪_{V'}`, a morphism
`f' : V' ⟶ Z` with `h ≫ f' = f`, and an integer `k > 0` such that, with `K' = h_* K` and
`B' = h_* B`, the pair `(V', B')` is lc with canonical divisor `K'`, `L = k(K' + B')` is an
`f'`-ample Cartier divisor, and `k(K + B)` is the pull-back `h^* L`, with
`𝒪_V(k(K + B)) ≅ h^* 𝒪_{V'}(L)`. -/
@[mmp "lem_mmp_surface_projective_adjoint_ample_model"]
public theorem IsLcPair.exists_isRelativelyAmple_of_isRelativelyNef_of_isRelativelyBig
    {V Z : Scheme.{0}} {sV : V ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [QuasiCompact sV]
    {K : Divisor V} {B : QDivisor V} (hB : 0 ≤ B) (hlc : IsLcPair sV 2 K B)
    (hV : IsProjectiveVariety ℂ sV) (hZ : IsProjectiveVariety ℂ sZ)
    (f : V ⟶ Z) (hf : f ≫ sZ = sV)
    (hnef : QDivisor.IsRelativelyNef sV f (Divisor.toQDivisor K + B))
    (hbig : QDivisor.IsRelativelyBig f (Divisor.toQDivisor K + B)) :
    ∃ (V' : Scheme.{0}) (_ : IsIntegral V') (_ : IsLocallyNoetherian V') (_ : IsNormal V')
      (_ : CompactSpace V') (sV' : V' ⟶ Spec (.of ℂ)) (h : V ⟶ V') (f' : V' ⟶ Z),
      h ≫ f' = f ∧ f' ≫ sZ = sV' ∧ IsNormalVariety ℂ sV' ∧ IsProjectiveVariety ℂ sV' ∧
        IsProjectiveMorphism h ∧ IsBirationalMorphism h ∧ (∀ U : V'.Opens, IsIso (h.app U)) ∧
        IsLcPair sV' 2 (RationalMap.transformDivisor h.toRationalMap K)
          (RationalMap.transformDivisor h.toRationalMap B) ∧
        ∃ k : ℕ, 0 < k ∧ ∃ (L : Divisor V') (hL : L.IsCartier),
          Divisor.toQDivisor L = (k : ℚ) • (Divisor.toQDivisor
            (RationalMap.transformDivisor h.toRationalMap K) +
              RationalMap.transformDivisor h.toRationalMap B) ∧
          L.IsRelativelyAmple f' hL ∧
          ∃ M : Divisor V, Divisor.toQDivisor M = (k : ℚ) • (Divisor.toQDivisor K + B) ∧
            (∃ hM, L.IsPullback h hM M) ∧
            Nonempty (M.divisorialSheaf ≅ (Scheme.Modules.pullback h).obj L.divisorialSheaf) := by
  obtain ⟨k, hk, M, hMc, hM, R, hfree, ⟨eR⟩⟩ :=
    exists_isRelativelyFreeCartier_sheaf_iso hB hlc hV hZ f hf hnef hbig
  obtain ⟨V', _, _, _, _, h, f', hhf, hV'n, hV'p, hh, hO, A, hA, hAa, ⟨e⟩⟩ :=
    exists_steinFactor hlc.1.1 hV hZ f hf R hfree eR
  have hb : IsBirationalMorphism h :=
    isBirationalMorphism_of_isRelativelyBig hV hZ f hf hbig hk hM h f' hhf hV'p hh hO hA e
  have : IsProper h := isProper_of_isProjectiveMorphism h hh
  have : CompactSpace V := (quasiCompact_iff_compactSpace sV).mp inferInstance
  have hsV : h ≫ f' ≫ sZ = sV := by rw [← Category.assoc, hhf, hf]
  obtain ⟨hLA, hpb⟩ := linearlyEquivalent_and_isPullback_transformDivisor hV'n h
    (by rw [hsV]; exact hlc.1.1) hb hA e
  set L : Divisor V' := RationalMap.transformDivisor h.toRationalMap M with hLdef
  have hL : L.IsCartier := Divisor.IsCartier.of_linearlyEquivalent hLA hA
  have hLM : Divisor.toQDivisor L = (k : ℚ) • (Divisor.toQDivisor
      (RationalMap.transformDivisor h.toRationalMap K) +
        RationalMap.transformDivisor h.toRationalMap B) := by
    rw [hLdef, toQDivisor_transformDivisor, hM, RationalMap.transformDivisor,
      DivisorWithCoeffs.mapPrimeDivisors_smul, map_add, ← RationalMap.transformDivisor,
      toQDivisor_transformDivisor]
  refine ⟨V', inferInstance, inferInstance, inferInstance, inferInstance, f' ≫ sZ, h, f', hhf,
    rfl, hV'n, hV'p, hh, hb, hO,
    isLcPair_transformDivisor hlc h hsV hb hV'n hk hM hL hLM hpb, k, hk, L, hL, hLM,
    isRelativelyAmple_of_linearlyEquivalent f' hLA hA hL hAa, M, hM, hpb,
    ⟨e ≪≫ (Scheme.Modules.pullback h).mapIso hLA.divisorialSheafIso.symm⟩⟩

end MMP.Mori
