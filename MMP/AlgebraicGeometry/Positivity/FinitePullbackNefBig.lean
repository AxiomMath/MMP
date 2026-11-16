module

public import MMP.AlgebraicGeometry.Intersection.Nef
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
public import MMP.AlgebraicGeometry.Morphisms.FiniteFunctionField

/-!
# Finite pull-backs of nef and big `ℚ`-divisors

Let `p : Z ⟶ X` be a finite surjective morphism of normal projective varieties over a field `k`
and `M` a nef and big `ℚ`-Cartier `ℚ`-divisor on `X`. Then the pull-back `p^*M` is nef and big:
nefness follows from the projection formula for curves, and bigness from
`((p^*eM)ⁿ) = deg p · ((eM)ⁿ) > 0` for a Cartier multiple `eM`, together with the criterion that
a nef Cartier divisor of positive top self-intersection is big.

## Main results

* `MMP.Mori.QDivisor.IsPullback.isNef_and_isBig_of_isFinite`

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Thm. 2.64, Step 2
-/

@[expose] public section

/-!
## Proof: Finite pull-backs of nef and big `ℚ`-divisors

Let `p : Z ⟶ X` be a finite surjective morphism of normal projective varieties over a field `k`
and `M` a nef and big `ℚ`-Cartier `ℚ`-divisor on `X`, with pull-back `P = p^*M`. Then `P` is nef
and big.

Nefness is the projection formula for curves: for a curve `C ⊆ Z`, `(P · C) = 0` if `p(C)` is a
point and `(P · C) = [k(C) : k(p(C))] (M · p(C)) ≥ 0` otherwise. For bigness, choose `m > 0` with
`D = mM` a big Cartier divisor; then `mP` is the Cartier divisor `D' = p^*D`, and pulling back
sections embeds `H⁰(X, 𝒪_X(jD))` into `H⁰(Z, 𝒪_Z(jD'))` for every `j`, while `dim Z = dim X`
since `k(Z)` is a finite extension of `k(X)`.

## Implementation notes

The source deduces bigness from `((p^*eM)ⁿ) = deg p · ((eM)ⁿ) > 0` and the criterion that a nef
Cartier divisor with positive top self-intersection is big, which is stated over an algebraically
closed field of characteristic zero. The growth of `h⁰(Z, 𝒪_Z(j p^*D))` is bounded below directly
by the injectivity of pull-back of sections along the dominant morphism `p`, which works over any
field.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Thm. 2.64, Step 2
-/

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.FourfoldProofs.Km2cFinitePullbackNefBigProof

variable {k : Type} [Field k]

/-- A finite dominant morphism of integral schemes of finite type over a field preserves the
dimension, since the extension of function fields is finite. -/
private theorem topologicalKrullDim_eq_of_isFinite {X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (h : Y ⟶ X) [IsIntegral X] [IsIntegral Y] [IsFinite h]
    [IsDominant h] [LocallyOfFiniteType sX] [LocallyOfFiniteType (h ≫ sX)] :
    topologicalKrullDim Y = topologicalKrullDim X := by
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra (h ≫ sX)
  letI := functionFieldMapAlgebra h
  haveI := isScalarTower_functionFieldMap sX h
  haveI : Module.Finite X.functionField Y.functionField := by
    convert MMP.moduleFinite_functionField_of_isFinite h using 3
    exact congrArg RingHom.toAlgebra (dominantFunctionFieldMap_eq_functionFieldMap h).symm
  haveI : Algebra.IsAlgebraic X.functionField Y.functionField := Algebra.IsAlgebraic.of_finite _ _
  rw [← toENat_trdeg_functionField (sX := h ≫ sX), ← toENat_trdeg_functionField (sX := sX),
    ← trdeg_add_eq k X.functionField (A := Y.functionField),
    trdeg_eq_zero (R := X.functionField) (A := Y.functionField), add_zero]

open Opposite in
/-- Restricting a section of a module twice is restricting it once. -/
private theorem map_map_homOfLE {X : Scheme.{0}} (L : X.Modules) {P Q R : X.Opens} (h₁ : Q ≤ P)
    (h₂ : P ≤ R) (σ : Γ(L, R)) :
    L.presheaf.map (homOfLE h₁).op (L.presheaf.map (homOfLE h₂).op σ) =
      L.presheaf.map (homOfLE (h₁.trans h₂)).op σ := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restricting a section of a module to its own open does nothing. -/
private theorem map_homOfLE_refl {X : Scheme.{0}} (L : X.Modules) {W : X.Opens} (σ : Γ(L, W)) :
    L.presheaf.map (homOfLE (le_refl W)).op σ = σ := by
  rw [show homOfLE (le_refl W) = 𝟙 W from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- A generator of an invertible module over every open inside `K` pulls back, along the unit of
`b^* ⊣ b_*`, to a generator over every open inside `b⁻¹ K`. -/
private theorem bijective_smul_unit_app {X Y : Scheme.{0}} (b : X ⟶ Y) (A : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y A] {K : Y.Opens} (a : Γ(A, K))
    (ha : ∀ (W : Y.Opens) (hW : W ≤ K),
      Function.Bijective (fun c : Γ(Y, W) => c • A.presheaf.map (homOfLE hW).op a))
    (W : X.Opens) (hW : W ≤ b ⁻¹ᵁ K) :
    Function.Bijective (fun c : Γ(X, W) =>
      c • ((Scheme.Modules.pullback b).obj A).presheaf.map (homOfLE hW).op
        (((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app A).app K a)) := by
  have hpb : Stacks.Ample.IsInvertibleModule X
      ((RingedSpaceModuleAdjunction.modulePullback b.toLRSHom.toShHom).obj A) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback b A
  have hpb' : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property
      ((RingedSpaceModuleAdjunction.modulePullback b.toLRSHom.toShHom).obj A) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hpb
  refine Stacks.SheafOfModules.bijective_smul_of_forall_germ_notMem_maximalIdeal_smul_top
    (X := X.toRingedSpace) _
    (Stacks.RingedSpace.pullbackUnit b.toLRSHom.toShHom A (Opposite.op K) a) _ hW fun x hx => ?_
  have h1 := Scheme.Modules.germ_notMem_maximalSmul_of_bijective_smul A a ha (b.base x) (hW hx)
  rwa [← Stacks.NonvanishingLocusRestrict.mem_maximalSmul_germ_pullbackUnit_iff b A a x (hW hx),
    Stacks.NonvanishingPullback.mem_maximalSmul_iff] at h1

/-- A global section of an invertible module on an integral scheme vanishing on a nonempty open
vanishes. -/
private theorem eq_zero_of_map_eq_zero {X : Scheme.{0}} [IsIntegral X] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {V : X.Opens} (hV : (V : Set X).Nonempty)
    (s : Γ(L, ⊤)) (hs : L.presheaf.map (homOfLE le_top : V ⟶ ⊤).op s = 0) : s = 0 := by
  have hL : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).mpr ‹_›
  have key : ∀ x : X, ∃ (K : X.Opens) (_ : x ∈ K),
      L.presheaf.map (homOfLE le_top : K ⟶ ⊤).op s = 0 := by
    intro x
    obtain ⟨K, hx, a, ha⟩ : ∃ (K : X.Opens) (_ : x ∈ K) (a : Γ(L, K)), ∀ (W : X.Opens)
        (hW : W ≤ K), Function.Bijective
          (fun c : Γ(X, W) => c • L.presheaf.map (homOfLE hW).op a) :=
      @Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible X.toRingedSpace _ L hL x
    refine ⟨K, hx, ?_⟩
    obtain ⟨g, hg⟩ := (ha K le_rfl).2 (L.presheaf.map (homOfLE le_top : K ⟶ ⊤).op s)
    simp only [map_homOfLE_refl] at hg
    obtain ⟨z, hz⟩ := nonempty_preirreducible_inter K.2 V.2 ⟨x, hx⟩ hV
    have : Nonempty (K ⊓ V : X.Opens) := ⟨⟨z, hz⟩⟩
    have hg0 : g = 0 := by
      refine map_injective_of_isIntegral X (homOfLE inf_le_left : K ⊓ V ⟶ K) ?_
      rw [map_zero]
      refine (ha (K ⊓ V) inf_le_left).1 ?_
      dsimp only
      rw [zero_smul, ← Scheme.Modules.map_smul, hg, map_map_homOfLE,
        ← map_map_homOfLE L (inf_le_right : K ⊓ V ≤ V) (le_top : V ≤ ⊤), hs, map_zero]
    rw [← hg, hg0, zero_smul]
  choose K hxK hK using key
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨L.presheaf, L.isSheaf⟩ K ⊤
    (fun x => homOfLE le_top) (fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxK x⟩) s 0
    fun x => ?_
  change L.presheaf.map (homOfLE le_top : K x ⟶ ⊤).op s =
    L.presheaf.map (homOfLE le_top : K x ⟶ ⊤).op 0
  rw [hK x, map_zero]

/-- Pull-back of sections of an invertible sheaf along a dominant quasi-compact morphism of
integral schemes is injective on global sections. -/
private theorem unit_app_top_injective {Y T : Scheme.{0}} [IsIntegral Y] [IsIntegral T]
    (g : Y ⟶ T) [IsDominant g] [QuasiCompact g] (M : T.Modules)
    [Stacks.Ample.IsInvertibleModule T M] :
    Function.Injective (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app ⊤) := by
  have hMinv : Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf
      (structureSheafRing T.toRingedSpace).property M :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ M).mpr ‹_›
  set L := (Scheme.Modules.pullback g).obj M
  set η := (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M
  rw [injective_iff_map_eq_zero]
  intro s hs
  obtain ⟨y0⟩ : Nonempty Y := inferInstance
  obtain ⟨K, hyK, a, ha⟩ : ∃ (K : T.Opens) (_ : g y0 ∈ K) (a : Γ(M, K)), ∀ (W : T.Opens)
      (hW : W ≤ K), Function.Bijective
        (fun c : Γ(T, W) => c • M.presheaf.map (homOfLE hW).op a) :=
    @Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible T.toRingedSpace _ M hMinv (g y0)
  obtain ⟨U, -, hyU, hUK⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens hyK
  set e : Γ(L, g ⁻¹ᵁ U) := η.app U (M.presheaf.map (homOfLE hUK).op a)
  have hgen := bijective_smul_unit_app g M (M.presheaf.map (homOfLE hUK).op a)
    (fun W hW => by simpa only [map_map_homOfLE] using ha W (hW.trans hUK)) (g ⁻¹ᵁ U) le_rfl
  set t := M.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s
  obtain ⟨f, hf⟩ := (ha U hUK).2 t
  have hηt : η.app U t = 0 :=
    (PresheafOfModules.naturality_apply η.val (homOfLE le_top : U ⟶ ⊤).op s).trans
      ((congrArg _ hs).trans (map_zero _))
  have hgf : g.app U f = 0 := by
    refine hgen.1 ?_
    change g.app U f • L.presheaf.map (homOfLE (le_refl (g ⁻¹ᵁ U))).op e =
      (0 : Γ(Y, g ⁻¹ᵁ U)) • L.presheaf.map (homOfLE (le_refl (g ⁻¹ᵁ U))).op e
    rw [map_homOfLE_refl, zero_smul]
    refine Eq.trans ?_ hηt
    rw [← hf, Scheme.Modules.Hom.app_smul]
    rfl
  have : IsSchemeTheoreticallyDominant g := .of_isDominant _
  have hf0 : f = 0 := g.app_injective U (by rw [hgf, map_zero])
  have ht0 : t = 0 := by rw [← hf, hf0]; exact zero_smul _ _
  exact eq_zero_of_map_eq_zero M ⟨g y0, hyU⟩ s ht0

/-- `scalarsToGlobalSections k sX` is `(Scheme.ΓSpecIso _).inv` followed by `sX.appLE ⊤ ⊤`. -/
private theorem scalarsToGlobalSections_eq_appLE {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) :
    scalarsToGlobalSections k sX =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ ⊤ (by simp)).hom :=
  congrArg (fun f => ((Scheme.ΓSpecIso _).inv ≫ f).hom) sX.appLE_eq_app.symm

/-- The global sections of `𝒪_Y(D)`, `D` Cartier on a proper `k`-scheme, are finite over `k`. -/
private theorem finite_divisorialSubmodule_top {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k))
    [IsProper sY] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {D : Divisor Y}
    (hD : D.IsCartier) :
    letI := Module.compHom (D.divisorialSubmodule ⊤) (scalarsToGlobalSections k sY);
    Module.Finite k (D.divisorialSubmodule ⊤) := by
  have := hD.isInvertibleModule_divisorialSheaf
  have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k sY
    D.divisorialSheaf 1
  have := finiteDimensional_cohomologyOverField_of_isProper k sY D.divisorialSheaf 0
  have e := (cohomologyOverFieldZeroLinearIso k sY D.divisorialSheaf).toLinearEquiv
  letI := Module.compHom (D.divisorialSubmodule ⊤)
    ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appLE ⊤ ⊤ (by simp)).hom
  rw [scalarsToGlobalSections_eq_appLE sY]
  exact Module.Finite.equiv e

/-- **Pulling back sections.** For a dominant quasi-compact morphism `g : Y ⟶ X` of integral
normal schemes, `Y` proper over `k`, and Cartier divisors `D` on `X` and `D'` on `Y` with
`𝒪_Y(D') ≅ g^*𝒪_X(D)`, `h⁰(X, 𝒪_X(D)) ≤ h⁰(Y, 𝒪_Y(D'))`. -/
private theorem h0_le_h0_of_iso_pullback {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] (sX : X ⟶ Spec (.of k)) (g : Y ⟶ X) [IsDominant g] [QuasiCompact g]
    [IsProper (g ≫ sX)] {D : Divisor X} (hD : D.IsCartier) {D' : Divisor Y} (hD' : D'.IsCartier)
    (e : D'.divisorialSheaf ≅ (Scheme.Modules.pullback g).obj D.divisorialSheaf) :
    D.h0 k sX ≤ D'.h0 k (g ≫ sX) := by
  have := hD.isInvertibleModule_divisorialSheaf
  have hsc : ∀ c, g.appTop (scalarsToGlobalSections k sX c) =
      scalarsToGlobalSections k (g ≫ sX) c := by
    intro c
    simp only [scalarsToGlobalSections, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
      RingHom.comp_apply]
  set M := D.divisorialSheaf
  let η := (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M
  letI := Module.compHom Γ(M, ⊤) (scalarsToGlobalSections k sX)
  letI := Module.compHom (D'.divisorialSubmodule ⊤) (scalarsToGlobalSections k (g ≫ sX))
  have : Module.Finite k (D'.divisorialSubmodule ⊤) := finite_divisorialSubmodule_top (g ≫ sX) hD'
  let φ : Γ(M, ⊤) →ₗ[k] D'.divisorialSubmodule ⊤ :=
    { toFun s := e.inv.app ⊤ (η.app ⊤ s)
      map_add' s t := by rw [map_add]; exact map_add _ _ _
      map_smul' c s := by
        change e.inv.app ⊤ (η.app ⊤ (scalarsToGlobalSections k sX c • s)) =
          (scalarsToGlobalSections k (g ≫ sX) c •
            (e.inv.app ⊤ (η.app ⊤ s) : D'.divisorialSubmodule ⊤))
        rw [Scheme.Modules.Hom.app_smul, ← hsc c]
        exact Scheme.Modules.Hom.app_smul e.inv _ _ }
  have h2 : ∀ x, e.hom.app ⊤ (e.inv.app ⊤ x) = x := fun x => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id]; rfl
  have hφ : Function.Injective φ := fun s t hst =>
    unit_app_top_injective g M <| (h2 _).symm.trans ((congrArg (e.hom.app ⊤) hst).trans (h2 _))
  unfold Divisor.h0
  letI := Module.compHom (D.divisorialSubmodule ⊤) (scalarsToGlobalSections k sX)
  exact LinearMap.finrank_le_finrank_of_injective (f := (φ : D.divisorialSubmodule ⊤ →ₗ[k] _)) hφ

/-- **The pull-back of a big divisor along a dominant morphism preserving dimension is big.**
Pulling back sections embeds `H⁰(X, 𝒪_X(mH))` into `H⁰(Y, 𝒪_Y(mH'))` for `H'` the pull-back of
the Cartier divisor `H` along `g`. -/
private theorem isBig_of_isPullback {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] (sX : X ⟶ Spec (.of k)) (g : Y ⟶ X) [IsDominant g] [QuasiCompact g]
    [IsProper (g ≫ sX)] {H : Divisor X} {H' : Divisor Y}
    (hn : topologicalKrullDim X = topologicalKrullDim Y)
    (hH : H.IsCartier) {hHg : ∀ Z : irreducibleComponents Y, g (componentGenericPoint Y Z) ∉ H.supp}
    (hH' : H.IsPullback g hHg H') (hbig : H.IsBig k sX) : H'.IsBig k (g ≫ sX) := by
  have hH'c := hH'.isCartier hH
  obtain ⟨d, hdX, c, hc, k₀, hk⟩ := hbig
  refine ⟨d, hn.symm.trans hdX, c, hc, k₀, fun m hm => (hk m hm).trans_le ?_⟩
  have hBm : ∀ Z, g (componentGenericPoint Y Z) ∉ (m • H).supp := fun Z hZ => hHg Z (by
    obtain ⟨E, hE, hx⟩ := DivisorWithCoeffs.mem_supp_iff.mp hZ
    exact DivisorWithCoeffs.mem_supp_iff.mpr
      ⟨E, fun h => hE (by rw [DivisorWithCoeffs.coeff_smul, h, smul_zero]), hx⟩)
  exact_mod_cast h0_le_h0_of_iso_pullback sX g (hH.zsmul m) (hH'c.zsmul m)
    ((hH'.zsmul hH m hBm).divisorialSheafIso (hBc := hH.zsmul m))

end MMP.FourfoldProofs.Km2cFinitePullbackNefBigProof

namespace MMP.Mori

namespace QDivisor

/-- **The pull-back of a nef and big `ℚ`-divisor along a finite surjective morphism is nef and
big.** Let `p : Z ⟶ X` be a finite surjective morphism of normal projective varieties over `k`
and `M` a nef and big `ℚ`-Cartier `ℚ`-divisor on `X`, with pull-back `P = p^*M`. Then `P` is nef
and big. -/
@[mmp "lem_km2c_finite_pullback_nef_big"]
public theorem IsPullback.isNef_and_isBig_of_isFinite {k : Type} [Field k]
    {X Z : Scheme.{0}} (sX : X ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [hXp : IsProjectiveVariety k sX] [hZp : IsProjectiveVariety k sZ] [IsNormal X] [IsNormal Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z] [CompactSpace X] [CompactSpace Z]
    (p : Z ⟶ X) (hp : p ≫ sX = sZ) [IsFinite p] [Surjective p]
    {M : QDivisor X} (hnef : M.IsNef k sX) (hbig : M.IsBig k sX)
    (hMp : ∀ C : irreducibleComponents Z, p (componentGenericPoint Z C) ∉ M.supp)
    {P : QDivisor Z} (hP : M.IsPullback p hMp P) :
    P.IsNef k sZ ∧ P.IsBig k sZ := by
  obtain ⟨hXv, hXpm⟩ := (MMP.Mori.isProjectiveVariety_iff k sX).mp hXp
  obtain ⟨hZv, hZpm⟩ := (MMP.Mori.isProjectiveVariety_iff k sZ).mp hZp
  haveI : IsProper sX := isProper_of_isProjectiveMorphism _ hXpm
  haveI : IsProper sZ := isProper_of_isProjectiveMorphism _ hZpm
  have hMq := hnef.isQCartier
  refine ⟨⟨hP.isQCartier hMq, fun C i _ _ _ hC => ?_⟩, ?_⟩
  · haveI : AlgebraicGeometry.IsCurve k (i ≫ sZ) :=
      (AlgebraicGeometry.isCurve_iff k _).mpr ⟨{}, hC⟩
    by_cases hpt : ∃ x : X, Set.range (i ≫ p) = {x}
    · exact (intersectionNumber_pullback_eq_zero k sZ sX p hp i hMq hP hpt).symm.le
    have hc : (i ≫ p) ≫ sX = i ≫ sZ := by rw [Category.assoc, hp]
    haveI : IsProper ((i ≫ p) ≫ sX) := by rw [hc]; infer_instance
    haveI : AlgebraicGeometry.IsCurve k ((i ≫ p) ≫ sX) := by rw [hc]; infer_instance
    haveI : IsProper (i ≫ p) := IsProper.of_comp (i ≫ p) sX
    haveI : IsProper ((i ≫ p).imageι ≫ sX) := isProper_imageι_comp (i ≫ p) sX
    have hcurve := isCurve_imageι_comp sX (i ≫ p) hpt
    haveI : IsIntegral (i ≫ p).image := hcurve.toIsIntegral
    rw [intersectionNumber_pullback_eq_degreeOver_mul k sZ sX p hp i hMq hP hcurve]
    exact mul_nonneg (by positivity)
      (hnef.2 _ (i ≫ p).imageι hcurve.topologicalKrullDim_eq_one)
  · obtain ⟨m, hm, D, hD, hDc, hDbig⟩ := hbig
    have hDm : Divisor.toQDivisor D = ((m : ℕ) : ℤ) • M := by
      rw [hD, natCast_zsmul, Nat.cast_smul_eq_nsmul]
    obtain ⟨D', hD', hpb⟩ := hP m hm D hDm hDc
    refine ⟨m, hm, D', by rw [hD', natCast_zsmul, Nat.cast_smul_eq_nsmul], hpb.isCartier hDc, ?_⟩
    haveI : IsIntegral X := hXv.toIsIntegral
    haveI : IsIntegral Z := hZv.toIsIntegral
    haveI : LocallyOfFiniteType (p ≫ sX) := by rw [hp]; infer_instance
    haveI : IsProper (p ≫ sX) := by rw [hp]; infer_instance
    subst hp
    exact MMP.FourfoldProofs.Km2cFinitePullbackNefBigProof.isBig_of_isPullback sX p
      (MMP.FourfoldProofs.Km2cFinitePullbackNefBigProof.topologicalKrullDim_eq_of_isFinite sX p).symm
      hDc hpb hDbig

end QDivisor

end MMP.Mori
