module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.Nef
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Divisor.Pullback
import MMP.AlgebraicGeometry.Positivity.AmpleNumerical
import MMP.AlgebraicGeometry.Resolution.ProjectiveLogResolution
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.MMP.BasepointFree.RelativelyFreeTwist
import MMP.AlgebraicGeometry.Divisor.SmoothWeilCartier
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalAntiampleDivisor
import MMP.AlgebraicGeometry.Morphisms.ValuativeCentre
import MMP.AlgebraicGeometry.Positivity.BigAmplePlusEffective
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
import MMP.AlgebraicGeometry.Divisor.SNC
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.Resolution.SNCWeight.StratumBlowup
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafSections

/-!
# Approximating the pull-back of a nef and big divisor by ample divisors

Let `X` be a normal projective variety over an algebraically closed field `k` of characteristic
zero, `D` a nef and big Cartier divisor on `X` and `Δ` an `ℝ`-divisor on `X`. Then there are a
log resolution `f : Y ⟶ X` of `(X, Δ)`, an effective snc `ℚ`-divisor `E'` on `Y` and ample
`ℚ`-divisors `A'ₙ` on `Y` such that `f^*D ≡ A'ₙ + (1/n) E'` for every integer `n > 0`.

The proof takes a projective log resolution `g : X' ⟶ X` of `(X, Δ)`. The pull-back `D₁ = g^*D`
is nef and big on the smooth projective `X'`, so `m D₁ ∼ a + e` with `a` ample and `e`
effective (Kodaira's lemma). Take a projective log resolution `h : Y ⟶ X'` of `(X', e + Δ')`,
`Δ'` the reduced divisor on `Ex(g) ∪ g⁻¹(Supp Δ)`; then `f = g ∘ h` is a log resolution of
`(X, Δ)`. Since `X'` is smooth, hence `ℚ`-factorial, there is an effective `h`-exceptional
Cartier divisor `D_F` with `-D_F` `h`-ample, and `G = ν h^*a - D_F` is ample for some `ν > 0`.
With `N = ν m` and `E'' = ν h^*e + D_F`, the divisors `N f^*D` and `G + E''` have the same
degree on every curve. Hence, with `E' = (1/N) E''` (effective, and snc since its support lies
in `Ex(h) ∪ h⁻¹(Supp(e + Δ'))`) and `A'ₙ = (1/(nN)) G + ((n-1)/n) f^*D` (ample plus nef, hence
ample), `f^*D ≡ A'ₙ + (1/n) E'`.

## Main results

* `MMP.Mori.exists_isLogResolution_numericallyEquivalent_isAmple_add_smul`: the statement above.
* `MMP.Mori.Divisor.h0_le_of_iso_pullback`: `h⁰(X, 𝒪_X(D)) ≤ h⁰(V, 𝒪_V(D'))` when
  `𝒪_V(D') ≅ u^* 𝒪_X(D)` for a dominant `u : V ⟶ X` of normal integral `k`-schemes with `V`
  proper over `k`.
* `MMP.Mori.Divisor.finite_divisorialSubmodule_top`: `H⁰(Y, 𝒪_Y(D))` is finite-dimensional
  for `D` Cartier on a proper `k`-scheme `Y`.
* `MMP.Mori.unit_app_top_injective`: pulling back global sections of an invertible sheaf along
  a dominant quasi-compact morphism of integral schemes is injective.

## Implementation notes

All numerical identities on `Y` are checked through degrees of invertible sheaves along curves:
for a pull-back `u^*B` of a Cartier divisor, `deg_C 𝒪(u^*B) = deg_{u ∘ C} 𝒪(B)`, so the linear
equivalence `m D₁ ∼ a + e` on `X'` is used only through the isomorphism
`𝒪_{X'}(m D₁) ≅ 𝒪_{X'}(a + e)`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Prop. 2.61,
  (1) ⇒ (4)
-/

public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

section Helpers

variable {k : Type} [Field k]

/-! ### Varieties -/

/-- The Weil divisor `[τ]` of a Cartier divisor `τ`, as an additive map. -/
private noncomputable def weilOfCartier (X : Scheme.{0}) [IsNoetherian X] [IsIntegral X] :
    X.CartierDivisor →+ Divisor X :=
  AddMonoidHom.mk' (fun τ => weilDivisorEquivFinsupp (cartierWeilDivisor τ)) fun a b =>
    Finsupp.ext fun Z => by
      change cartierMultiplicity (a + b) Z.genericPoint =
        cartierMultiplicity a Z.genericPoint + cartierMultiplicity b Z.genericPoint
      unfold cartierMultiplicity
      rw [map_add, map_add]
      rfl

/-- The source of a projective smooth resolution of a normal projective variety is a projective
variety. -/
private theorem isProjectiveVariety_comp {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) (hXp : MMP.Mori.IsProjectiveVariety k sX) {f : Y ⟶ X}
    (hf : IsSmoothResolution sX f) (hfp : IsProjectiveMorphism f) :
    MMP.Mori.IsProjectiveVariety k (f ≫ sX) := by
  rw [MMP.Mori.isProjectiveVariety_iff] at hXp ⊢
  exact ⟨(hf.isNormalVariety hX).1.1, hfp.comp hXp.2⟩

/-- The source of a smooth resolution of a normal variety is a smooth variety. -/
private theorem isSmoothVariety_of_isSmoothResolution {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) {f : Y ⟶ X} (hf : IsSmoothResolution sX f) :
    IsSmoothVariety k (f ≫ sX) := by
  have hv := (hf.isNormalVariety hX).1.1
  haveI : LocallyOfFiniteType (f ≫ sX) := hv.toLocallyOfFiniteType
  haveI : LocallyOfFinitePresentation (f ≫ sX) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  exact (isSmoothVariety_iff k _).mpr ⟨hv, (isSmoothScheme_iff _).mp hf.isSmoothScheme⟩

/-! ### Degrees along curves -/

/-- The degree along a curve of a divisor depends only on the isomorphism class of its sheaf. -/
private theorem degreeOn_eq_of_divisorialSheaf_iso {X C : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] (φ : C ⟶ X) [IsProper (φ ≫ sX)]
    (hdim : topologicalKrullDim C ≤ 1) {D D' : Divisor X} (hD : D.IsCartier) (hD' : D'.IsCartier)
    (e : (haveI := QuasiCompact.compactSpace_of_compactSpace sX; D.divisorialSheaf) ≅
      (haveI := QuasiCompact.compactSpace_of_compactSpace sX; D'.divisorialSheaf)) :
    D.degreeOn k sX φ hdim hD = D'.degreeOn k sX φ hdim hD' := by
  haveI := QuasiCompact.compactSpace_of_compactSpace sX
  haveI := hD.isInvertibleModule_divisorialSheaf
  haveI := hD'.isInvertibleModule_divisorialSheaf
  exact degreeOn_eq_of_iso k sX φ hdim e

/-- The degree along a curve depends only on the morphism. -/
private theorem degreeOn_congr_hom {X C : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
    [IsLocallyNoetherian X] [IsNormal X] {φ φ' : C ⟶ X} (h : φ = φ') [IsProper (φ ≫ sX)]
    [IsProper (φ' ≫ sX)] (hdim : topologicalKrullDim C ≤ 1) (D : Divisor X) (hD : D.IsCartier) :
    D.degreeOn k sX φ hdim hD = D.degreeOn k sX φ' hdim hD := by
  subst h
  rfl

/-- `deg_C 𝒪_V(u^*B) = deg_{u ∘ C} 𝒪_W(B)` for the pull-back of a Cartier divisor. -/
private theorem degreeOn_eq_of_isPullback {V W C : Scheme.{0}} {sV : V ⟶ Spec (.of k)}
    {sW : W ⟶ Spec (.of k)} [QuasiCompact sV] [QuasiCompact sW] [IsLocallyNoetherian V]
    [IsNormal V] [IsIntegral V] [IsLocallyNoetherian W] [IsNormal W] (u : V ⟶ W)
    (hu : u ≫ sW = sV) {B : Divisor W} (hBc : B.IsCartier)
    {hB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ B.supp}
    {B' : Divisor V} (h : B.IsPullback u hB B') (hB'c : B'.IsCartier) (φ : C ⟶ V)
    [IsProper (φ ≫ sV)] [IsProper ((φ ≫ u) ≫ sW)] (hdim : topologicalKrullDim C ≤ 1) :
    B'.degreeOn k sV φ hdim hB'c = B.degreeOn k sW (φ ≫ u) hdim hBc := by
  haveI := QuasiCompact.compactSpace_of_compactSpace sV
  haveI := QuasiCompact.compactSpace_of_compactSpace sW
  haveI := hBc.isInvertibleModule_divisorialSheaf
  haveI := hB'c.isInvertibleModule_divisorialSheaf
  change MMP.Mori.degreeOn k sV φ hdim B'.divisorialSheaf = MMP.Mori.degreeOn k sW (φ ≫ u) hdim
    B.divisorialSheaf
  rw [degreeOn_eq_of_iso k sV φ hdim (h.divisorialSheafIso (hBc := hBc))]
  exact degreeOn_pullback_eq_degreeOn_comp sV sW u φ hu hdim _

/-- **The degree identity on `Y`.** Let `g : X' ⟶ X`, `h : Y ⟶ X'`, `D₁ = g^*D`, and suppose
`𝒪_{X'}(m D₁) ≅ 𝒪_{X'}(a + e)`. Then along every curve on `Y`,
`deg h^*a + deg h^*e = m · deg (g ∘ h)^*D`. -/
private theorem degreeOn_add_eq_mul_degreeOn_of_iso {X X' Y C : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX']
    [IsLocallyNoetherian X'] [IsNormal X'] [IsIntegral X'] [CompactSpace X'] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y]
    (g : X' ⟶ X) (hg : g ≫ sX = sX') (h : Y ⟶ X') (hh : h ≫ sX' = sY)
    {D : Divisor X} (hDc : D.IsCartier)
    {hB₁ : ∀ Z : irreducibleComponents X', g (componentGenericPoint X' Z) ∉ D.supp}
    {D₁ : Divisor X'} (hD₁ : D.IsPullback g hB₁ D₁) (hD₁c : D₁.IsCartier)
    {hBf : ∀ Z : irreducibleComponents Y, (h ≫ g) (componentGenericPoint Y Z) ∉ D.supp}
    {fD : Divisor Y} (hfD : D.IsPullback (h ≫ g) hBf fD) (hfDc : fD.IsCartier)
    {a e : Divisor X'} (hac : a.IsCartier) (hec : e.IsCartier) {m : ℕ}
    (eae : (m • D₁).divisorialSheaf ≅ (a + e).divisorialSheaf)
    {hBa : ∀ Z : irreducibleComponents Y, h (componentGenericPoint Y Z) ∉ a.supp}
    {b : Divisor Y} (hb : a.IsPullback h hBa b) (hbc : b.IsCartier)
    {hBe : ∀ Z : irreducibleComponents Y, h (componentGenericPoint Y Z) ∉ e.supp}
    {be : Divisor Y} (hbe : e.IsPullback h hBe be) (hbec : be.IsCartier)
    (i : C ⟶ Y) [IsProper (i ≫ sY)] (hdim : topologicalKrullDim C ≤ 1) :
    b.degreeOn k sY i hdim hbc + be.degreeOn k sY i hdim hbec =
      m * fD.degreeOn k sY i hdim hfDc := by
  haveI : IsProper ((i ≫ h) ≫ sX') := by simp only [Category.assoc, hh]; infer_instance
  haveI : IsProper ((i ≫ h ≫ g) ≫ sX) := by simp only [Category.assoc, hg, hh]; infer_instance
  haveI : IsProper (((i ≫ h) ≫ g) ≫ sX) := by simp only [Category.assoc, hg, hh]; infer_instance
  have hmae := degreeOn_eq_of_divisorialSheaf_iso (sX := sX') (i ≫ h) hdim (hD₁c.nsmul m)
    (hac.add hec) eae
  rw [Divisor.degreeOn_nsmul' k sX' (i ≫ h) hdim D₁ hD₁c m,
    Divisor.degreeOn_add k sX' (i ≫ h) hdim a e hac hec] at hmae
  rw [degreeOn_eq_of_isPullback h hh hac hb hbc i hdim,
    degreeOn_eq_of_isPullback h hh hec hbe hbec i hdim, ← hmae,
    degreeOn_eq_of_isPullback g hg hDc hD₁ hD₁c (i ≫ h) hdim,
    degreeOn_eq_of_isPullback (h ≫ g) (by rw [Category.assoc, hg, hh]) hDc hfD hfDc i hdim,
    degreeOn_congr_hom (Category.assoc i h g) hdim D hDc]

/-- If `D = e • F` as `ℚ`-divisors, then `D P = e * F P` for every prime divisor `P`. -/
private theorem coeff_eq_mul_of_toQDivisor_eq_smul {Y : Scheme.{0}} {D : Divisor Y}
    {F : QDivisor Y} {e : ℕ} (h : Divisor.toQDivisor D = (e : ℚ) • F)
    (P : MMP.Mori.PrimeDivisor Y) : (D P : ℚ) = e * F P :=
  (by simpa using congrArg (· P) h : Divisor.toQDivisor D P = e * F P)

/-- A nef Cartier divisor has nonnegative degree along every proper curve mapping to `X`. -/
private theorem degreeOn_nonneg_of_isNef {X C : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    (hX : MMP.Mori.IsVariety k sX) [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    {D : Divisor X} (hD : D.IsNef k sX) (hDc : D.IsCartier) (φ : C ⟶ X)
    [MMP.Mori.IsCurve k (φ ≫ sX)] [IsProper (φ ≫ sX)] (hdim : topologicalKrullDim C ≤ 1) :
    0 ≤ D.degreeOn k sX φ hdim hDc := by
  haveI : IsSeparated sX := hX.toIsSeparated
  haveI : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  haveI := QuasiCompact.compactSpace_of_compactSpace sX
  haveI := hDc.isInvertibleModule_divisorialSheaf
  obtain ⟨_, hD⟩ := hD
  change 0 ≤ MMP.Mori.degreeOn k sX φ hdim D.divisorialSheaf
  by_cases hpt : ∃ x : X, Set.range φ = {x}
  · rw [degreeOn_eq_zero_of_range_eq_singleton sX φ _ hpt]
  · rw [degreeOn_eq_degreeOver_mul sX φ _ hpt]
    haveI : IsProper φ := IsProper.of_comp φ sX
    haveI : IsProper (φ.imageι ≫ sX) := isProper_imageι_comp φ sX
    have hc : MMP.Mori.IsCurve k (φ.imageι ≫ sX) := isCurve_imageι_comp sX φ hpt
    haveI : IsIntegral φ.image := ((MMP.Mori.isCurve_iff k _).mp hc).1.toIsIntegral
    have := hD φ.image φ.imageι ((MMP.Mori.isCurve_iff k _).mp hc).2
    exact mul_nonneg (by positivity) this

/-- The pull-back of a nef Cartier divisor is nef. -/
private theorem isNef_of_isPullback {X V : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    {sV : V ⟶ Spec (.of k)} (hX : MMP.Mori.IsVariety k sX) [QuasiCompact sX]
    [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sV] [IsLocallyNoetherian V] [IsNormal V]
    [IsIntegral V] [IsSeparated sV] [LocallyOfFiniteType sV] (u : V ⟶ X) (hu : u ≫ sX = sV)
    {D : Divisor X} (hD : D.IsNef k sX)
    {hB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ D.supp}
    {D' : Divisor V} (h : D.IsPullback u hB D') : D'.IsNef k sV := by
  obtain ⟨hDc, -⟩ := id hD
  have hD'c : D'.IsCartier := h.isCartier hDc
  refine ⟨hD'c, fun C i _ _ _ hC => ?_⟩
  haveI : IsProper ((i ≫ u) ≫ sX) := by rw [Category.assoc, hu]; infer_instance
  rw [degreeOn_eq_of_isPullback u hu hDc h hD'c i hC.le]
  haveI : MMP.Mori.IsCurve k ((i ≫ u) ≫ sX) := by
    rw [Category.assoc, hu]
    exact (MMP.Mori.isCurve_iff k _).mpr ⟨(MMP.Mori.isVariety_iff k _).mpr
      ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, hC⟩
  exact degreeOn_nonneg_of_isNef hX hD hDc (i ≫ u) hC.le

/-! ### Bigness -/

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
  rw [← Stacks.NonvanishingLocusRestrict.mem_maximalSmul_germ_pullbackUnit_iff b A a x
    (hW hx)] at h1
  rwa [Stacks.NonvanishingPullback.mem_maximalSmul_iff] at h1

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
theorem unit_app_top_injective {Y T : Scheme.{0}} [IsIntegral Y] [IsIntegral T]
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
  obtain ⟨U, hUaff, hyU, hUK⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens hyK
  set e : Γ(L, g ⁻¹ᵁ U) := η.app U (M.presheaf.map (homOfLE hUK).op a)
  have hgen := bijective_smul_unit_app g M (M.presheaf.map (homOfLE hUK).op a)
    (fun W hW => by simpa only [map_map_homOfLE] using ha W (hW.trans hUK)) (g ⁻¹ᵁ U) le_rfl
  set t := M.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s
  obtain ⟨f, hf⟩ := (ha U hUK).2 t
  have hηt : η.app U t = 0 := by
    refine (PresheafOfModules.naturality_apply η.val (homOfLE le_top : U ⟶ ⊤).op s).trans ?_
    change _ = (0 : _)
    erw [hs, map_zero]
    rfl
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
  have ht0 : t = 0 := by
    rw [← hf, hf0]
    exact zero_smul _ _
  exact eq_zero_of_map_eq_zero M ⟨g y0, hyU⟩ s ht0

/-- `scalarsToGlobalSections k sX` is `(ΓSpecIso k).inv ≫ sX.appLE ⊤ ⊤ _`. -/
private theorem scalarsToGlobalSections_eq_appLE {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) :
    scalarsToGlobalSections k sX =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ ⊤ (by simp)).hom := by
  have : sX.appLE ⊤ ⊤ (by simp) = sX.appTop := by
    simp [Scheme.Hom.appLE]
    exact Category.comp_id _
  rw [this]
  rfl

/-- The global sections of `𝒪_Y(D)`, `D` Cartier on a proper `k`-scheme, are finite over `k`. -/
theorem Divisor.finite_divisorialSubmodule_top {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k))
    [IsProper sY] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {D : Divisor Y}
    (hD : D.IsCartier) :
    letI := Module.compHom (D.divisorialSubmodule ⊤) (scalarsToGlobalSections k sY);
    Module.Finite k (D.divisorialSubmodule ⊤) := by
  have := hD.isInvertibleModule_divisorialSheaf
  have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k sY
    D.divisorialSheaf 1
  have := finiteDimensional_cohomologyOverField_of_isProper k sY D.divisorialSheaf 0
  have e := (cohomologyOverFieldZeroLinearIso k sY D.divisorialSheaf).toLinearEquiv
  have key : ∀ ψ : k →+* Γ(Y, ⊤),
      ψ = ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appLE ⊤ ⊤ (by simp)).hom →
        (letI := Module.compHom (D.divisorialSubmodule ⊤) ψ;
          Module.Finite k (D.divisorialSubmodule ⊤)) := by
    rintro ψ rfl
    have := Module.Finite.equiv e
    exact this
  exact key _ (scalarsToGlobalSections_eq_appLE sY)

/-- `h⁰(X, 𝒪_X(D)) ≤ h⁰(V, 𝒪_V(D'))` when `𝒪_V(D') ≅ u^* 𝒪_X(D)` for a dominant quasi-compact
`k`-morphism `u : V ⟶ X` of normal integral schemes with `V` proper over `k`. -/
theorem Divisor.h0_le_of_iso_pullback {X V : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    {sV : V ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral V] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V] [IsProper sV]
    (u : V ⟶ X) (hu : u ≫ sX = sV) [IsDominant u] [QuasiCompact u] {D : Divisor X}
    (hDc : D.IsCartier) {D' : Divisor V} (hD'c : D'.IsCartier)
    (E : D'.divisorialSheaf ≅ (Scheme.Modules.pullback u).obj D.divisorialSheaf) :
    Divisor.h0 k sX D ≤ Divisor.h0 k sV D' := by
  have hsc : ∀ c, u.appTop (scalarsToGlobalSections k sX c) = scalarsToGlobalSections k sV c := by
    intro c
    subst hu
    simp only [scalarsToGlobalSections, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
      RingHom.comp_apply]
  haveI := hDc.isInvertibleModule_divisorialSheaf
  set M := D.divisorialSheaf with hM
  let η := (Scheme.Modules.pullbackPushforwardAdjunction u).unit.app M
  letI := Module.compHom Γ(M, ⊤) (scalarsToGlobalSections k sX)
  letI := Module.compHom (D'.divisorialSubmodule ⊤) (scalarsToGlobalSections k sV)
  have : Module.Finite k (D'.divisorialSubmodule ⊤) := finite_divisorialSubmodule_top sV hD'c
  let φ : Γ(M, ⊤) →ₗ[k] D'.divisorialSubmodule ⊤ :=
    { toFun s := E.inv.app ⊤ (η.app ⊤ s)
      map_add' s t := by
        rw [map_add]
        exact map_add _ _ _
      map_smul' c s := by
        change E.inv.app ⊤ (η.app ⊤ (scalarsToGlobalSections k sX c • s)) =
          (scalarsToGlobalSections k sV c • (E.inv.app ⊤ (η.app ⊤ s) : D'.divisorialSubmodule ⊤))
        rw [Scheme.Modules.Hom.app_smul, ← hsc c]
        exact Scheme.Modules.Hom.app_smul E.inv _ _ }
  have h2 : ∀ x, E.hom.app ⊤ (E.inv.app ⊤ x) = x := fun x => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, E.inv_hom_id]
    rfl
  have hφ : Function.Injective φ := fun s t hst => by
    refine unit_app_top_injective u M ?_
    have := congrArg (E.hom.app ⊤) hst
    change E.hom.app ⊤ (E.inv.app ⊤ (η.app ⊤ s)) = E.hom.app ⊤ (E.inv.app ⊤ (η.app ⊤ t)) at this
    exact (h2 _).symm.trans (this.trans (h2 _))
  change Module.finrank k Γ(M, ⊤) ≤ Module.finrank k (D'.divisorialSubmodule ⊤)
  exact LinearMap.finrank_le_finrank_of_injective hφ

/-- The pull-back of a big Cartier divisor along a birational morphism of projective normal
varieties is big. -/
private theorem isBig_of_isPullback {X V : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    {sV : V ⟶ Spec (.of k)} (hXp : MMP.Mori.IsProjectiveVariety k sX)
    (hVp : MMP.Mori.IsProjectiveVariety k sV) [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian V] [IsNormal V] (u : V ⟶ X) (hu : u ≫ sX = sV)
    (hub : IsBirationalMorphism u) {D : Divisor X} (hDc : D.IsCartier) (hD : D.IsBig k sX)
    {hB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ D.supp}
    {D' : Divisor V} (h : D.IsPullback u hB D') : D'.IsBig k sV := by
  have hXv := ((MMP.Mori.isProjectiveVariety_iff k sX).mp hXp).1
  have hVv := ((MMP.Mori.isProjectiveVariety_iff k sV).mp hVp).1
  haveI : IsIntegral X := hXv.toIsIntegral
  haveI : IsIntegral V := hVv.toIsIntegral
  haveI : QuasiCompact sX := hXv.toQuasiCompact
  haveI : QuasiCompact sV := hVv.toQuasiCompact
  haveI : IsSeparated sX := hXv.toIsSeparated
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  haveI : IsProper sV := isProper_of_isProjectiveMorphism _
    ((MMP.Mori.isProjectiveVariety_iff k sV).mp hVp).2
  haveI : IsDominant u := hub.isDominant
  haveI : QuasiCompact (u ≫ sX) := hu ▸ inferInstance
  haveI : QuasiCompact u := QuasiCompact.of_comp u sX
  haveI := hXv
  haveI := hVv
  have hdim : topologicalKrullDim X = topologicalKrullDim V :=
    MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX sV hub
  obtain ⟨n, hn, c, hc, k₀, hk⟩ := hD
  refine ⟨n, hdim ▸ hn, c, hc, k₀, fun j hj => (hk j hj).trans_le ?_⟩
  have hBj : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ (j • D).supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' u _
  have hpj := h.zsmul hDc j hBj
  exact_mod_cast Divisor.h0_le_of_iso_pullback u hu (hDc.zsmul j) (hpj.isCartier (hDc.zsmul j))
    (hpj.divisorialSheafIso (hBc := hDc.zsmul j))

/-! ### Ample plus effective on a smooth projective variety -/

/-- An `R`-linear equivalence between `R`-modules that are `k`-vector spaces through a ring map
`φ : k →+* R` preserves the `k`-dimension. -/
private theorem finrank_compHom_eq {R : Type} [CommRing R] (φ : k →+* R) {M N : Type}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (g : M ≃ₗ[R] N) :
    (letI := Module.compHom M φ; Module.finrank k M) =
      (letI := Module.compHom N φ; Module.finrank k N) := by
  letI := Module.compHom M φ
  letI := Module.compHom N φ
  let g' : M ≃ₗ[k] N :=
    { g.toEquiv with map_add' := g.map_add, map_smul' := fun c x => g.map_smul (φ c) x }
  exact g'.finrank_eq

/-- The `Γ(X, 𝒪_X)`-linear isomorphism `Γ(X, L) ≃ Γ(X, L')` induced by an isomorphism `L ≅ L'`. -/
private noncomputable def sectionsLinearEquiv {X : Scheme.{0}} {L L' : X.Modules} (e : L ≅ L') :
    Γ(L, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(L', ⊤) where
  toFun := e.hom.app ⊤
  invFun := e.inv.app ⊤
  map_add' := map_add _
  map_smul' _ s := Scheme.Modules.Hom.app_smul e.hom _ s
  left_inv s := by
    change ((e.hom ≫ e.inv).app ⊤) s = s
    rw [Iso.hom_inv_id]
    rfl
  right_inv s := by
    change ((e.inv ≫ e.hom).app ⊤) s = s
    rw [Iso.inv_hom_id]
    rfl

/-- `weilDivisorEquivFinsupp (cartierWeilDivisor D)` is a Weil divisor of the Cartier divisor
`D`. -/
private theorem isWeilDivisorOfCartier_cartierWeilDivisor {S : Scheme.{0}} [IsIntegral S]
    [IsNoetherian S] (D : S.CartierDivisor) :
    MMP.Intersection.IsWeilDivisorOfCartier D (weilDivisorEquivFinsupp (cartierWeilDivisor D)) := by
  intro P
  have hcoh : Order.coheight (MMP.Mori.PrimeDivisor.genericPoint P) = 1 :=
    AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P
  haveI : Ring.KrullDimLE 1
      (S.presheaf.stalk (MMP.Intersection.primeDivisorSubvariety P).genericPoint) :=
    krullDimLE_of_coheight_le hcoh.le
  obtain ⟨N, hN⟩ :=
    MMP.Intersection.exists_isOrderAlong D (MMP.Intersection.primeDivisorSubvariety P)
  convert hN using 1
  have hN' := hN
  unfold MMP.Intersection.IsOrderAlong at hN'
  dsimp only [MMP.Intersection.primeDivisorSubvariety_genericPoint] at hN'
  obtain ⟨a, b, ha, hb, ⟨g, hg, hgab⟩, la, lb, hla, hlb, rfl⟩ := hN'
  change cartierMultiplicity D (MMP.Mori.PrimeDivisor.genericPoint P) = _
  rw [MMP.Intersection.cartierMultiplicity_eq_ord_of_isLocalEquationAt hg]
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap (S.presheaf.stalk _) S.functionField b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have key : totalQuotientStalkToFunctionField _ g *
      algebraMap (S.presheaf.stalk _) S.functionField b =
      algebraMap (S.presheaf.stalk _) S.functionField a := by
    have := congrArg (totalQuotientStalkToFunctionField _) hgab.2
    rw [map_mul, MMP.Intersection.totalQuotientStalkToFunctionField_stalkToTotalQuotient,
      MMP.Intersection.totalQuotientStalkToFunctionField_stalkToTotalQuotient] at this
    rwa [mul_comm]
  have hTg := MMP.Intersection.totalQuotientStalkToFunctionField_ne_zero_of_isLocalEquationAt hg
  have hord := S.ord_mul (x := MMP.Mori.PrimeDivisor.genericPoint P) hTg hbK
  rw [key, ord_algebraMap_stalk _ hcoh a ha0, ord_algebraMap_stalk _ hcoh b hb0] at hord
  erw [hla, hlb, ENat.toNat_coe, ENat.toNat_coe] at hord
  omega

/-- **Kodaira's lemma** on a smooth projective variety: a big divisor `D` has a multiple `mD`
with `𝒪(mD) ≅ 𝒪(a + e)`, `a` ample and `e` effective. -/
private theorem exists_isAmple_add_nonneg {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))
    [IsSmoothVariety k sX] (hXp : MMP.Mori.IsProjectiveVariety k sX) [IsLocallyNoetherian X]
    [CompactSpace X] [IsNormal X] (D : Divisor X) (hD : D.IsBig k sX) :
    ∃ m : ℕ, 0 < m ∧ ∃ (a e : Divisor X) (ha : a.IsCartier), a.IsAmple ha ∧ 0 ≤ e ∧
      Nonempty ((m • D).divisorialSheaf ≅ (a + e).divisorialSheaf) := by
  have hXv := (isSmoothVariety_iff k sX).mp ‹_›
  haveI : IsIntegral X := hXv.1.toIsIntegral
  haveI : IsNoetherian X := ⟨⟩
  obtain ⟨hcart, -, hbij, hiso, -, -⟩ := Divisor.cartier_weil_dictionary_of_isSmoothVariety k sX
  have hiso' : ∀ τ : X.CartierDivisor,
      Nonempty ((weilOfCartier X τ).divisorialSheaf ≅ MMP.CartierDivisor.sheaf τ) := hiso
  obtain ⟨τ, hτ⟩ := hbij.2 D
  change weilOfCartier X τ = D at hτ
  obtain ⟨n, hn, c, hc, k₀, hk⟩ := hD
  have hh0 : ∀ j : ℕ, cartierH0 k sX (j • τ) = Divisor.h0 k sX ((j : ℤ) • D) := by
    intro j
    obtain ⟨e⟩ := hiso' (j • τ)
    rw [map_nsmul, hτ, ← natCast_zsmul] at e
    exact finrank_compHom_eq (scalarsToGlobalSections k sX) (sectionsLinearEquiv e.symm)
  have hinf : {m : ℕ | c * (m : ℝ) ^ n < (cartierH0 k sX (m • τ) : ℝ)}.Infinite := by
    refine Set.infinite_of_forall_exists_gt fun a => ⟨max (a + 1) k₀.toNat, ?_,
      lt_of_lt_of_le (Nat.lt_succ_self a) (le_max_left _ _)⟩
    simp only [Set.mem_setOf_eq]
    rw [hh0]
    have hle : k₀ ≤ ((max (a + 1) k₀.toNat : ℕ) : ℤ) :=
      (Int.self_le_toNat k₀).trans (by exact_mod_cast le_max_right _ _)
    have := hk _ hle
    push_cast at this ⊢
    exact this
  obtain ⟨m, hm, A, E, -, hAamp, hE, hlin⟩ :=
    exists_linearlyEquivalent_ample_add_effective sX hXp hn τ ⟨c, hc, hinf⟩
  refine ⟨m, hm, weilOfCartier X A, weilOfCartier X E, hcart _, ?_, ?_, ?_⟩
  · obtain ⟨eA⟩ := hiso' A
    haveI := (hcart (weilOfCartier X A)).isInvertibleModule_divisorialSheaf
    exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ eA).mpr hAamp
  · intro P
    change (0 : ℤ) ≤
      DivisorWithCoeffs.coeff (weilDivisorEquivFinsupp (cartierWeilDivisor E) : Divisor X) P
    exact (isWeilDivisorOfCartier_cartierWeilDivisor E P).nonneg_of_isEffective hE
  · obtain ⟨φ, hφ⟩ := MMP.Intersection.mem_principalSubgroup_iff.mp hlin
    have e1 : MMP.CartierDivisor.sheaf (A + E) ≅ MMP.CartierDivisor.sheaf (m • τ) :=
      MMP.CartierDivisor.sheafAddPrincipalIso (A + E) φ ≪≫
        eqToIso (by rw [hφ, add_sub_cancel])
    obtain ⟨eτ⟩ := hiso' (m • τ)
    obtain ⟨eAE⟩ := hiso' (A + E)
    rw [map_nsmul, hτ] at eτ
    rw [map_add] at eAE
    exact ⟨eτ ≪≫ e1.symm ≪≫ eAE.symm⟩

/-! ### Relatively ample plus a pull-back of an ample divisor -/

/-- Relative ampleness of an invertible sheaf is invariant under isomorphism. -/
private theorem isRelativelyAmple_of_iso {X Y : Scheme.{0}} (f : X ⟶ Y) {L L' : X.Modules}
    [Stacks.Ample.IsInvertibleModule X L] [Stacks.Ample.IsInvertibleModule X L'] (e : L ≅ L')
    (h : IsRelativelyAmple f L) : IsRelativelyAmple f L' := by
  intro y
  obtain ⟨V, hV, hyV, hamp⟩ := h y
  exact ⟨V, hV, hyV, (Stacks.RelativeVeryAmple.isAmple_congr _ _
    ((RingedSpaceModuleAdjunction.modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).mapIso e)).1 hamp⟩

/-- For `h : Y ⟶ X` a morphism of smooth projective varieties, `L` an `h`-ample divisor on `Y`
and `a` an ample divisor on `X`, `L + ν h^*a` is ample for some `ν > 0`. -/
private theorem exists_isAmple_add_nsmul {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    {sY : Y ⟶ Spec (.of k)} [IsSmoothVariety k sX] [IsSmoothVariety k sY]
    (hXp : MMP.Mori.IsProjectiveVariety k sX) (hYp : MMP.Mori.IsProjectiveVariety k sY)
    [IsLocallyNoetherian X] [CompactSpace X] [IsNormal X] [IsLocallyNoetherian Y]
    [CompactSpace Y] [IsNormal Y] (h : Y ⟶ X) (hh : h ≫ sX = sY) {a : Divisor X}
    (ha : a.IsCartier) (hamp : a.IsAmple ha)
    {hB : ∀ Z : irreducibleComponents Y, h (componentGenericPoint Y Z) ∉ a.supp}
    {b : Divisor Y} (hb : a.IsPullback h hB b) {L : Divisor Y} (hL : L.IsCartier)
    (hLamp : L.IsRelativelyAmple h hL) :
    ∃ ν : ℕ, 0 < ν ∧ ∃ hG : (L + ν • b).IsCartier, (L + ν • b).IsAmple hG := by
  have hXv := (isSmoothVariety_iff k sX).mp ‹_›
  have hYv := (isSmoothVariety_iff k sY).mp ‹_›
  haveI : IsIntegral X := hXv.1.toIsIntegral
  haveI : IsIntegral Y := hYv.1.toIsIntegral
  haveI : IsNoetherian X := ⟨⟩
  haveI : IsNoetherian Y := ⟨⟩
  obtain ⟨-, -, hbijX, hisoX, -, -⟩ := Divisor.cartier_weil_dictionary_of_isSmoothVariety k sX
  obtain ⟨hcartY, -, hbijY, hisoY, -, -⟩ :=
    Divisor.cartier_weil_dictionary_of_isSmoothVariety k sY
  have hisoX' : ∀ τ : X.CartierDivisor,
      Nonempty ((weilOfCartier X τ).divisorialSheaf ≅ MMP.CartierDivisor.sheaf τ) := hisoX
  have hisoY' : ∀ τ : Y.CartierDivisor,
      Nonempty ((weilOfCartier Y τ).divisorialSheaf ≅ MMP.CartierDivisor.sheaf τ) := hisoY
  obtain ⟨M, hM⟩ := hbijX.2 a
  obtain ⟨Lc, hLc⟩ := hbijY.2 L
  obtain ⟨Bc, hBc⟩ := hbijY.2 b
  change weilOfCartier X M = a at hM
  change weilOfCartier Y Lc = L at hLc
  change weilOfCartier Y Bc = b at hBc
  obtain ⟨eM⟩ := hisoX' M
  obtain ⟨eL⟩ := hisoY' Lc
  obtain ⟨eB⟩ := hisoY' Bc
  rw [hM] at eM
  rw [hLc] at eL
  rw [hBc] at eB
  haveI := ha.isInvertibleModule_divisorialSheaf
  haveI := hL.isInvertibleModule_divisorialSheaf
  haveI := (hcartY b).isInvertibleModule_divisorialSheaf
  have hMamp : Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf M) :=
    (Stacks.RelativeVeryAmple.isAmple_congr _ _ eM).mp hamp
  have hLamp' : IsRelativelyAmple h (MMP.CartierDivisor.sheaf Lc) :=
    isRelativelyAmple_of_iso h eL hLamp
  have hB : Nonempty (MMP.CartierDivisor.sheaf Bc ≅
      (Scheme.Modules.pullback h).obj (MMP.CartierDivisor.sheaf M)) :=
    ⟨eB.symm ≪≫ hb.divisorialSheafIso (hBc := ha) ≪≫ (Scheme.Modules.pullback h).mapIso eM⟩
  obtain ⟨ν, hν, hν1⟩ := ((MMP.Foundations.isAmple_add_zsmul_pullback k hYp hXp hh hMamp hLamp'
    hB).and (Filter.eventually_ge_atTop 1)).exists
  lift ν to ℕ using (by omega)
  refine ⟨ν, by omega, hcartY _, ?_⟩
  obtain ⟨e⟩ := hisoY' (Lc + (ν : ℤ) • Bc)
  rw [map_add, map_zsmul, hLc, hBc, natCast_zsmul] at e
  haveI := (hcartY (L + ν • b)).isInvertibleModule_divisorialSheaf
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mpr hν

/-! ### Snc divisors -/

/-- A `ℚ`-divisor whose prime components lie in an snc divisor is snc. -/
private theorem isSNC_of_subset {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)}
    [LocallyOfFinitePresentation sY] (hsm : IsSmoothScheme sY) {S : TopologicalSpace.Closeds Y}
    (hS : IsSNCSubset sY S) {E : QDivisor Y}
    (hE : ∀ P : MMP.Mori.PrimeDivisor Y, E P ≠ 0 → (P.support : Set Y) ⊆ S) : E.IsSNC sY := by
  classical
  rcases hS with rfl | ⟨s, hs, hsnc⟩
  · refine (DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme (R := ℤ) sY hsm).of_support_subset ?_
    intro P hP
    exact absurd (hE P (Finsupp.mem_support_iff.mp hP)
      (MMP.Flips.primeDivisor_genericPoint_mem_support P)) (by simp)
  · refine hsnc.of_support_subset ?_
    intro P hP
    obtain ⟨F, hFs, hPF⟩ :=
      MMP.Fourfold.SNCWeight.PrimeDivisorUnion.exists_subset_of_isIrreducible (s := s)
        (A := fun F : MMP.Mori.PrimeDivisor Y => (F.support : Set Y))
        (fun F _ => MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isClosed_support F)
        (MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isIrreducible_support P)
        (by rw [hs]; exact hE P (Finsupp.mem_support_iff.mp hP))
    rw [MMP.Fourfold.SNCWeight.PrimeDivisorUnion.eq_of_support_subset hPF,
      Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
    simp [Finsupp.single_apply, hFs]

/-- There is an `ℝ`-divisor whose support contains both the snc divisor `S` and the support of
the effective divisor `e`. -/
private theorem exists_rDivisor_le_supp {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)}
    {S : TopologicalSpace.Closeds Y} (hS : IsSNCSubset sY S) (e : Divisor Y) (he : 0 ≤ e) :
    ∃ Δ' : RDivisor Y, S ≤ Δ'.supp ∧ e.supp ≤ Δ'.supp := by
  classical
  rcases hS with rfl | ⟨s, hs, -⟩
  · exact ⟨Divisor.toRDivisor e, bot_le, by rw [Divisor.supp_toRDivisor]⟩
  set R : Divisor Y := ∑ E ∈ s, Finsupp.single E (1 : ℤ) with hR
  have hR1 : ∀ E ∈ s, R E = 1 := fun E hE => by
    rw [hR, Finsupp.finset_sum_apply]
    simp [Finsupp.single_apply, hE]
  have hR0 : 0 ≤ R := fun E => by
    rw [hR, Finsupp.finset_sum_apply]
    exact Finset.sum_nonneg fun F _ => by
      rw [Finsupp.single_apply]; split_ifs <;> simp
  refine ⟨Divisor.toRDivisor (e + R), ?_, ?_⟩
  · intro x hx
    rw [Divisor.supp_toRDivisor]
    have hx' : x ∈ (S : Set Y) := hx
    rw [← hs, Set.mem_iUnion₂] at hx'
    obtain ⟨E, hE, hxE⟩ := hx'
    refine DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, ?_, hxE⟩
    rw [DivisorWithCoeffs.coeff_apply, Finsupp.add_apply, hR1 E hE]
    have := he E
    simp only [Finsupp.coe_zero, Pi.zero_apply] at this
    omega
  · intro x hx
    rw [Divisor.supp_toRDivisor]
    obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
    refine DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, ?_, hxE⟩
    rw [DivisorWithCoeffs.coeff_apply] at hE ⊢
    rw [Finsupp.add_apply]
    have h1 := he E
    have h2 := hR0 E
    simp only [Finsupp.coe_zero, Pi.zero_apply] at h1 h2
    omega

/-! ### Intersection numbers of rational multiples -/

/-- `(q D · C) = q · deg_C 𝒪(D)` for a Cartier divisor `D` and `q ∈ ℚ`. -/
private theorem intersectionNumber_smul_toQDivisor {X C : Scheme.{0}} (sX : X ⟶ Spec (.of k))
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] (i : C ⟶ X) [IsProper (i ≫ sX)]
    (hdim : topologicalKrullDim C ≤ 1) (D : Divisor X) (hD : D.IsCartier) (q : ℚ)
    (hq : (q • Divisor.toQDivisor D).IsQCartier) :
    (q • Divisor.toQDivisor D).intersectionNumber k sX i hdim hq =
      q * D.degreeOn k sX i hdim hD := by
  rw [QDivisor.intersectionNumber_smul k sX i hdim q _ (QDivisor.isQCartier_toQDivisor hD) hq,
    QDivisor.intersectionNumber_toQDivisor k sX i hdim D hD]

end Helpers

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- **Kollár–Mori 2.61 (1) ⇒ (4).** Let `X` be a normal projective variety over an algebraically
closed field `k` of characteristic zero, `D` a nef and big Cartier divisor on `X` and `Δ` an
`ℝ`-divisor on `X`. Then there are a log resolution `f : Y ⟶ X` of `(X, Δ)`, an effective snc
`ℚ`-divisor `E'` on `Y` and ample `ℚ`-divisors `A' n` on `Y` with `f^*D ≡ A' n + (1/n) E'` for
every integer `n > 0`. -/
@[mmp "lem_km2c_log_resolution_ample_approximation"]
theorem exists_isLogResolution_numericallyEquivalent_isAmple_add_smul {k : Type}
    [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))
    [IsProjectiveVariety k sX] [IsLocallyNoetherian X] [IsNormal X] (D : Divisor X)
    (hnef : D.IsNef k sX) (hbig : D.IsBig k sX) (Δ : RDivisor X) :
    ∃ (Y : Scheme.{0}) (f : Y ⟶ X), IsLogResolution sX Δ f ∧
      ∃ (_ : IsLocallyNoetherian Y) (_ : IsNormal Y) (_ : CompactSpace Y)
        (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp)
        (fD : Divisor Y) (E' : QDivisor Y) (A' : ℕ → QDivisor Y),
        D.IsPullback f hB fD ∧ 0 ≤ E' ∧ E'.IsSNC (f ≫ sX) ∧
          ∀ n : ℕ, 0 < n → (A' n).IsAmple ∧
            (Divisor.toQDivisor fD).NumericallyEquivalent k (f ≫ sX)
              (A' n + (n : ℚ)⁻¹ • E') := by
  have hXp : IsProjectiveVariety k sX := inferInstance
  /- The variety `X`. -/
  have hXv : MMP.Mori.IsVariety k sX := ((MMP.Mori.isProjectiveVariety_iff k sX).mp hXp).1
  have hXN : IsNormalVariety k sX := ⟨hXv, inferInstance⟩
  haveI : IsIntegral X := hXv.toIsIntegral
  haveI : QuasiCompact sX := hXv.toQuasiCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨hDc, -⟩ := id hnef
  /- Step 1: a projective log resolution `g : X' ⟶ X` of `(X, Δ)`. -/
  obtain ⟨X', g, hg, hgp⟩ := exists_isLogResolution_isProjectiveMorphism sX hXN Δ
  have hX'N : IsNormalVariety k (g ≫ sX) := (hg.toIsSmoothResolution.isNormalVariety hXN).1
  have hX'p : MMP.Mori.IsProjectiveVariety k (g ≫ sX) :=
    isProjectiveVariety_comp hXN hXp hg.toIsSmoothResolution hgp
  haveI : IsSmoothVariety k (g ≫ sX) :=
    isSmoothVariety_of_isSmoothResolution hXN hg.toIsSmoothResolution
  haveI : IsIntegral X' := hX'N.1.toIsIntegral
  haveI : IsNormal X' := hX'N.2
  haveI : QuasiCompact (g ≫ sX) := hX'N.1.toQuasiCompact
  haveI : LocallyOfFiniteType (g ≫ sX) := hX'N.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sX)
  haveI : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  haveI : IsNoetherian X' := ⟨⟩
  have hX'cart := (Divisor.cartier_weil_dictionary_of_isSmoothVariety k (g ≫ sX)).1
  have hgb := hg.isBirationalMorphism
  haveI : IsDominant g := hgb.isDominant
  have hBg : ∀ Z : irreducibleComponents X', g (componentGenericPoint X' Z) ∉ D.supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' g D
  obtain ⟨D₁, hD₁⟩ := hDc.exists_isPullback hBg
  have hD₁big : D₁.IsBig k (g ≫ sX) := isBig_of_isPullback hXp hX'p g rfl hgb hDc hbig hD₁
  obtain ⟨m, hm, a, e, hac, hamp, he0, ⟨eae⟩⟩ :=
    exists_isAmple_add_nonneg (g ≫ sX) hX'p D₁ hD₁big
  /- The boundary `Δ''` of the second resolution and `h : Y ⟶ X'`. -/
  obtain ⟨Δ'', hΔ''1, hΔ''2⟩ := exists_rDivisor_le_supp hg.isSNCSubset e he0
  obtain ⟨Y, h, hh, hhp⟩ := exists_isLogResolution_isProjectiveMorphism (g ≫ sX) hX'N Δ''
  have hf : IsLogResolution sX Δ (h ≫ g) := hg.comp hΔ''1 hh
  have ht : h ≫ g ≫ sX = (h ≫ g) ≫ sX := (Category.assoc _ _ _).symm
  have hYN : IsNormalVariety k ((h ≫ g) ≫ sX) :=
    ht ▸ (hh.toIsSmoothResolution.isNormalVariety hX'N).1
  haveI hYp : MMP.Mori.IsProjectiveVariety k ((h ≫ g) ≫ sX) :=
    ht ▸ isProjectiveVariety_comp hX'N hX'p hh.toIsSmoothResolution hhp
  haveI : IsSmoothVariety k ((h ≫ g) ≫ sX) :=
    ht ▸ isSmoothVariety_of_isSmoothResolution hX'N hh.toIsSmoothResolution
  haveI : IsIntegral Y := hYN.1.toIsIntegral
  haveI : IsNormal Y := hYN.2
  haveI : QuasiCompact ((h ≫ g) ≫ sX) := hYN.1.toQuasiCompact
  haveI : LocallyOfFiniteType ((h ≫ g) ≫ sX) := hYN.1.toLocallyOfFiniteType
  haveI : IsSeparated ((h ≫ g) ≫ sX) := hYN.1.toIsSeparated
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian ((h ≫ g) ≫ sX)
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace ((h ≫ g) ≫ sX)
  haveI : IsNoetherian Y := ⟨⟩
  obtain ⟨hYcart, -, -, -, -, hYq⟩ :=
    Divisor.cartier_weil_dictionary_of_isSmoothVariety k ((h ≫ g) ≫ sX)
  have hhb := hh.isBirationalMorphism
  haveI : IsDominant h := hhb.isDominant
  haveI : IsDominant (h ≫ g) := hf.isBirationalMorphism.isDominant
  /- Step 2: an anti-ample exceptional divisor `D_F` and the ample `G = ν h^*a - D_F`. -/
  have hQ : MMP.Fourfold.IsQFactorial (g ≫ sX) :=
    ⟨hX'N, fun B => ⟨1, one_pos, hX'cart _⟩⟩
  obtain ⟨F, e₀, he₀, hF0, hFex, DF, hDFc, hDF, hDFamp⟩ :=
    exists_isRelativelyAmple_neg_smul_of_isExceptional (g ≫ sX) ((h ≫ g) ≫ sX) hQ hYN h ht
      hhp hhb
  have hBa : ∀ Z : irreducibleComponents Y, h (componentGenericPoint Y Z) ∉ a.supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' h a
  have hBe : ∀ Z : irreducibleComponents Y, h (componentGenericPoint Y Z) ∉ e.supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' h e
  have hec : e.IsCartier := hX'cart e
  obtain ⟨b, hb⟩ := hac.exists_isPullback hBa
  obtain ⟨be, hbe⟩ := hec.exists_isPullback hBe
  obtain ⟨ν, hν, hGc, hGamp⟩ :=
    exists_isAmple_add_nsmul hX'p hYp h ht hac hamp hb hDFc.neg hDFamp
  set G : Divisor Y := -DF + ν • b with hG
  set E'' : Divisor Y := ν • be + DF with hE''
  set N : ℕ := ν * m with hN
  have hNpos : 0 < N := Nat.mul_pos hν hm
  /- The pull-back `f^*D` and the degree identity `N f^*D ≡ G + E''`. -/
  have hBf : ∀ Z : irreducibleComponents Y, (h ≫ g) (componentGenericPoint Y Z) ∉ D.supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' (h ≫ g) D
  obtain ⟨fD, hfD⟩ := hDc.exists_isPullback hBf
  have hfDc : fD.IsCartier := hYcart fD
  have hfDnef : fD.IsNef k ((h ≫ g) ≫ sX) := isNef_of_isPullback hXv (h ≫ g) rfl hnef hfD
  have hkey : ∀ (C : Scheme.{0}) (i : C ⟶ Y) [IsProper (i ≫ (h ≫ g) ≫ sX)]
      (hdim : topologicalKrullDim C ≤ 1),
      G.degreeOn k ((h ≫ g) ≫ sX) i hdim hGc + E''.degreeOn k ((h ≫ g) ≫ sX) i hdim (hYcart _) =
        (N : ℤ) * fD.degreeOn k ((h ≫ g) ≫ sX) i hdim hfDc := by
    intro C i _ hdim
    have hGE : G + E'' = ν • (b + be) := by rw [hG, hE'', smul_add]; abel
    rw [← Divisor.degreeOn_add, Divisor.degreeOn_congr hGE _ ((hYcart _).nsmul ν),
      Divisor.degreeOn_nsmul' k _ i hdim (b + be) (hYcart _) ν,
      Divisor.degreeOn_add k _ i hdim b be (hYcart _) (hYcart _),
      degreeOn_add_eq_mul_degreeOn_of_iso g rfl h ht hDc hD₁ (hX'cart D₁) hfD hfDc hac hec eae hb
        (hYcart b) hbe (hYcart be) i hdim, hN]
    push_cast
    ring
  /- Step 3: the divisors `E'` and `A'ₙ`. -/
  set c : ℚ := (N : ℚ)⁻¹ with hc
  refine ⟨Y, h ≫ g, hf, inferInstance, inferInstance, inferInstance, hBf, fD,
    c • Divisor.toQDivisor E'',
    fun n => ((n : ℚ)⁻¹ * c) • Divisor.toQDivisor G +
      (((n - 1 : ℕ) : ℚ) / n) • Divisor.toQDivisor fD, hfD, ?_, ?_, ?_⟩
  · /- `E' = (1/N) E''` is effective. -/
    have hbe0 : 0 ≤ be := fun P => MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn hec
      (V := ⊤) (fun Q _ => he0 Q) hbe P
      ⟨P.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support P, trivial⟩
    have hDF0 : 0 ≤ DF := fun P => by
      have : (0 : ℚ) ≤ DF P := by
        rw [coeff_eq_mul_of_toQDivisor_eq_smul hDF P]
        exact mul_nonneg (by positivity) (hF0 P)
      exact_mod_cast this
    have hE0 : 0 ≤ E'' := add_nonneg (nsmul_nonneg hbe0 ν) hDF0
    intro P
    change (0 : ℚ) ≤ c * (E'' P : ℚ)
    exact mul_nonneg (by rw [hc]; positivity) (by exact_mod_cast hE0 P)
  · /- `E'` is snc: its components lie in `Ex(h) ∪ h⁻¹(Supp Δ'')`. -/
    refine isSNC_of_subset hf.isSmoothScheme (ht ▸ hh.isSNCSubset) fun P hP => ?_
    have hP' : E'' P ≠ 0 := fun h0 => hP (by
      change c * (E'' P : ℚ) = 0
      rw [h0, Int.cast_zero, mul_zero])
    have hE''P : E'' P = ν * be P + DF P := by rw [hE'']; simp
    by_cases hbP : be P = 0
    · have hDFP : DF P ≠ 0 := by rwa [hE''P, hbP, mul_zero, zero_add] at hP'
      have hFP : F P ≠ 0 := fun h0 => hDFP (by
        have := coeff_eq_mul_of_toQDivisor_eq_smul hDF P
        rw [h0, mul_zero] at this
        exact_mod_cast this)
      intro x hx
      exact (le_sup_left : exceptionalSet h ≤ _)
        (MMP.Positivity.support_subset_exceptionalSet P (hFex P hFP) hx)
    · intro x hx
      refine (le_sup_right : _ ≤ exceptionalSet h ⊔ _) ?_
      have hx' := MMP.Flips.supp_subset_preimage_supp_of_isPullback hec hbe
        (DivisorWithCoeffs.support_subset_supp hbP hx)
      exact hΔ''2 hx'
  · /- `A'ₙ` is ample and `f^*D ≡ A'ₙ + (1/n) E'`. -/
    intro n hn
    dsimp only
    have hn' : (0 : ℚ) < n := by exact_mod_cast hn
    have hN' : (0 : ℚ) < N := by exact_mod_cast hNpos
    set c₁ : ℚ := (n : ℚ)⁻¹ * c with hc₁
    set c₂ : ℚ := ((n - 1 : ℕ) : ℚ) / n with hc₂
    have hc₂0 : 0 ≤ c₂ := by rw [hc₂]; positivity
    have hnN : 0 < n * N := Nat.mul_pos hn hNpos
    have hc₁N : ((n * N : ℕ) : ℚ) * c₁ = 1 := by
      rw [hc₁, hc]; push_cast; field_simp
    have hA : (c₁ • Divisor.toQDivisor G).IsAmple :=
      ⟨n * N, hnN, G, by rw [smul_smul, hc₁N, one_smul], hGc, hGamp⟩
    obtain ⟨hfDc', hfDdeg⟩ := hfDnef
    have hNnef : (c₂ • Divisor.toQDivisor fD).IsNef k ((h ≫ g) ≫ sX) :=
      ⟨hYq _, fun C i _ _ _ hC => by
        rw [intersectionNumber_smul_toQDivisor _ i hC.le fD hfDc c₂ (hYq _)]
        exact mul_nonneg hc₂0 (by exact_mod_cast hfDdeg C i hC)⟩
    have hDeq : Divisor.toQDivisor (G + ((n - 1) * N) • fD) =
        ((n * N : ℕ) : ℚ) • (c₁ • Divisor.toQDivisor G + c₂ • Divisor.toQDivisor fD) := by
      rw [map_add, map_nsmul, smul_add, smul_smul, smul_smul, hc₁N, one_smul,
        ← Nat.cast_smul_eq_nsmul ℚ]
      congr 2
      rw [hc₂, Nat.cast_mul, Nat.cast_mul]
      field_simp
      rw [hN]
      push_cast
      ring
    refine ⟨⟨n * N, hnN, _, hDeq, hYcart _,
      QDivisor.isAmple_of_numericallyEquivalent_add_of_isNef ((h ≫ g) ≫ sX) hA hNnef
        (QDivisor.NumericallyEquivalent.refl (hYq _)) (n * N) hnN _ hDeq (hYcart _)⟩, ?_⟩
    rw [smul_smul]
    refine ⟨hYq _, hYq _, fun C i _ _ _ hC => ?_⟩
    rw [QDivisor.intersectionNumber_toQDivisor k _ i hC.le fD hfDc,
      QDivisor.intersectionNumber_add' k _ i hC.le _ _ (hYq _) (hYq _),
      QDivisor.intersectionNumber_add' k _ i hC.le _ _ (hYq _) (hYq _),
      intersectionNumber_smul_toQDivisor _ i hC.le G hGc,
      intersectionNumber_smul_toQDivisor _ i hC.le fD hfDc,
      intersectionNumber_smul_toQDivisor _ i hC.le E'' (hYcart _)]
    have hk : (G.degreeOn k ((h ≫ g) ≫ sX) i hC.le hGc : ℚ) +
        (E''.degreeOn k ((h ≫ g) ≫ sX) i hC.le (hYcart _) : ℚ) =
          (N : ℚ) * (fD.degreeOn k ((h ≫ g) ≫ sX) i hC.le hfDc : ℚ) := by
      exact_mod_cast hkey C i hC.le
    have hsplit : ∀ x y z : ℚ, c₁ * x + c₂ * z + c₁ * y = c₁ * (x + y) + c₂ * z :=
      fun _ _ _ => by ring
    rw [hsplit, hk, hc₁, hc₂, hc, Nat.cast_sub (by omega), Nat.cast_one]
    field_simp
    ring

end MMP.Mori
