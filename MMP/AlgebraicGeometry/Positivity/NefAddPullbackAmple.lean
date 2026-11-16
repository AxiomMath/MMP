module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.Nef
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.AlgebraicGeometry.Singularities.LogResolution.Basic
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorPullbackSheaf
import MMP.AlgebraicGeometry.Positivity.NefBigOfAmpleApproximation

/-!
# A nef divisor plus the pull-back of an ample divisor is nef and big

Let `f : Y ⟶ X` be a birational morphism of projective varieties over a field `k`, with `Y`
normal, `M` a nef `ℚ`-Cartier `ℚ`-divisor on `Y`, `H` an ample Cartier divisor on `X` and
`r > 0`. Then `M + r f^*H` is nef and big.

The Weil divisor `G` of `f^*H` is Cartier with `𝒪_Y(G) ≅ f^*𝒪_X(H)`, so by the projection
formula it has nonnegative degree on every curve: `G` is nef. The ample divisor `H` is big, hence
so is `f^*H` by birational invariance of bigness, and so is `G`. Kodaira's lemma writes
`G ≡ Aₙ + (1/n)E` with `Aₙ` ample and `E` effective Cartier for all large `n`. With `eM` Cartier
and `r = p/q`, the Cartier divisor `D = q (eM) + ep G = eq (M + rG)` satisfies
`D ≡ (q (eM) + ep Aₙ) + (1/n)(ep E)`, where `q (eM) + ep Aₙ` is ample as a nef divisor plus an
ample one. So `D` is nef and big, and so is `M + rG = (eq)⁻¹ D`.

## Main results

* `MMP.Mori.QDivisor.IsNef.isNef_and_isBig_add_smul_pullback`: `M + r f^*H` is nef and big.

## Implementation notes

`X` need not be normal, so `H` is a Cartier divisor `X.CartierDivisor`, with
`𝒪_X(H) = MMP.CartierDivisor.sheaf H` ample. Its pull-back
`MMP.CartierDivisor.pullback f H hH` to the integral scheme `Y` is defined since
`f(Y) ⊄ Supp H` (`f` is dominant), and it enters the `ℚ`-divisor `M + r f^*H` through its Weil
divisor `G`, characterised by `MMP.Intersection.IsWeilDivisorOfCartier`: every coefficient of
`G` is the order of `f^*H` along the corresponding prime divisor. The scalar `r` is allowed to be
any positive rational.

Birational invariance of bigness is stated for pull-backs by local fractions
(`MMP.Intersection.IsPullback`); the pull-back `MMP.CartierDivisor.pullback` is one, since on
the integral scheme `Y` the pulled-back local equation at `y` is the fraction `f^♯a / f^♯b` of any
representation `a / b` of a local equation of `H` at `f(y)`, as one checks in the function field
of `Y`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Cor. 2.68
-/

public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

section Pullback

open Opposite MMP.Intersection MMP.CartierDivisorPullback

/-- The only associated point of an integral locally Noetherian scheme is its generic point. -/
private theorem eq_genericPoint_of_mem_schemeAssociatedPoints {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] {ξ : X} (h : ξ ∈ Stacks.Divisors.schemeAssociatedPoints X) :
    ξ = genericPoint X := by
  have h1 : ξ ∈ Stacks.Divisors.schemeWeaklyAssociatedPoints X := by
    rwa [Stacks.Divisors.schemeAssociatedPoints,
      associatedPoints_eq_weaklyAssociatedPoints X (SheafOfModules.unit X.ringCatSheaf)] at h
  rw [weaklyAssociatedPointsOfScheme_eq_genericPoints] at h1
  have h2 : closure ({ξ} : Set X) ∈ ({Set.univ} : Set (Set X)) := by
    rwa [← irreducibleComponents_eq_singleton]
  exact (show IsGenericPoint ξ Set.univ from h2).eq (genericPoint_spec X)

/-- On an integral scheme, the image of `s ∈ 𝒪_{Y,y}` in `𝓜_{Y,y}` is the germ of the rational
function `s` (the specialization of `s` to the generic point). -/
private theorem stalkToTotalQuotient_eq_germ {Y : Scheme.{0}} [IsIntegral Y] {V : Y.Opens}
    {y : Y} (hy : y ∈ V) (s : Y.presheaf.stalk y) :
    stalkToTotalQuotient y s = Y.totalQuotientSheaf.presheaf.germ V y hy
      (functionFieldToK V (Y.presheaf.stalkSpecializes
        ((genericPoint_spec Y).specializes (Set.mem_univ y)) s)) := by
  obtain ⟨W, hyW, t, rfl⟩ := Y.presheaf.germ_exist s
  have hyVW : y ∈ V ⊓ W := ⟨hy, hyW⟩
  have hξ : genericPoint Y ∈ V ⊓ W := genericPoint_mem hyVW
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply,
    ← Y.totalQuotientSheaf.presheaf.germ_res_apply (homOfLE inf_le_left : V ⊓ W ⟶ V) y hyVW]
  have h1 : Y.totalQuotientSheaf.presheaf.map (homOfLE inf_le_left : V ⊓ W ⟶ V).op
      (functionFieldToK V (Y.presheaf.germ W (genericPoint Y) hξ.2 t)) =
        functionFieldToK (V ⊓ W) (Y.presheaf.germ W (genericPoint Y) hξ.2 t) :=
    (NatTrans.naturality_apply (functionFieldToTotalQuotientSheaf Y)
      (homOfLE inf_le_left : V ⊓ W ⟶ V).op _).symm
  rw [h1, ← Y.presheaf.germ_res_apply (homOfLE inf_le_right : V ⊓ W ⟶ W) _ hξ t,
    functionFieldToTotalQuotientSheaf_germ, ← Y.presheaf.germ_res_apply
      (homOfLE inf_le_right : V ⊓ W ⟶ W) y hyVW t]
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _ _ _

/-- **The pull-back is a pull-back by local fractions.** For a morphism `f : Y ⟶ X` of
locally Noetherian schemes with `Y` integral and `f(Y) ⊄ Supp D`, the pull-back `f^*D` is
a pull-back of `D` in the sense of `MMP.Intersection.IsPullback`. -/
private theorem isPullback_cartierDivisor_pullback {X Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : Y ⟶ X) (D : X.CartierDivisor)
    (hD : ¬ Set.range f ⊆ MMP.Intersection.cartierSupport D) :
    MMP.Intersection.IsPullback f D (MMP.CartierDivisor.pullback f D hD) := by
  have hξ : f (genericPoint Y) ∉ cartierSupport D :=
    (MMP.CartierDivisor.genericPoint_notMem_cartierSupport_iff f D).mpr hD
  have hcond : PullbackCondition f D := fun η hη =>
    eq_genericPoint_of_mem_schemeAssociatedPoints hη ▸ hξ
  refine ⟨hcond, fun y => ?_⟩
  obtain ⟨_, U, hyU, σ, hσ, rfl⟩ := exists_isLocalEquationAt D (f y)
  obtain ⟨a, b, hab, ha, hb⟩ :=
    exists_isFraction_stalkMap_mem_nonZeroDivisors hcond y ⟨U, hyU, σ, hσ, rfl⟩
  have hspec : genericPoint Y ⤳ y := (genericPoint_spec Y).specializes (Set.mem_univ y)
  have hηU : f (genericPoint Y) ∈ U := (hspec.map f.continuous).mem_open U.isOpen hyU
  obtain ⟨a₀, ha₀⟩ := MMP.CartierDivisor.exists_isGermUnit_of_not_range_subset f D hD hσ hηU
  set τ := ofFunctionField (f ⁻¹ᵁ U) (pullbackGerm f a₀)
  have hτ : IsLocalEquationOn (MMP.CartierDivisor.pullback f D hD) (f ⁻¹ᵁ U) τ :=
    MMP.CartierDivisor.isLocalEquationOn_pullback f D hD hσ hηU ha₀
  refine ⟨a, b, ⟨_, ⟨U, hyU, σ, hσ, rfl⟩, hab⟩, ha, hb, _, ⟨f ⁻¹ᵁ U, hyU, τ, hτ, rfl⟩,
    isUnit_stalkToTotalQuotient_of_mem_nonZeroDivisors hb, ?_⟩
  have hspX : f (genericPoint Y) ⤳ f y := hspec.map f.continuous
  have hnat : ∀ c : X.presheaf.stalk (f y),
      stalkToTotalQuotient _ (X.presheaf.stalkSpecializes hspX c) =
        X.totalQuotientSheaf.presheaf.stalkSpecializes hspX (stalkToTotalQuotient (f y) c) :=
    fun c => (ConcreteCategory.congr_hom
      (TopCat.Presheaf.stalkSpecializes_stalkFunctor_map X.toTotalQuotientSheaf.hom hspX) c)
  have hkey : X.presheaf.stalkSpecializes hspX b * a₀.val =
      X.presheaf.stalkSpecializes hspX a := by
    apply stalkToTotalQuotient_injective X (f (genericPoint Y))
    rw [map_mul, hnat, hnat, ha₀]
    have hg : TopCat.Presheaf.germ X.totalQuotientSheaf.obj U (f (genericPoint Y)) hηU σ.val =
        X.totalQuotientSheaf.presheaf.stalkSpecializes hspX
          (X.totalQuotientSheaf.presheaf.germ U (f y) hyU σ.val) :=
      (TopCat.Presheaf.germ_stalkSpecializes_apply _ hyU hspX _).symm
    rw [hg, ← map_mul, hab.2]
  have hcomm : ∀ c : X.presheaf.stalk (f y),
      Y.presheaf.stalkSpecializes hspec (f.stalkMap y c) =
        f.stalkMap (genericPoint Y) (X.presheaf.stalkSpecializes hspX c) :=
    fun c => (ConcreteCategory.congr_hom (Scheme.Hom.stalkSpecializes_stalkMap f _ _ hspec) c).symm
  have hyU' : y ∈ f ⁻¹ᵁ U := hyU
  rw [stalkToTotalQuotient_eq_germ hyU', stalkToTotalQuotient_eq_germ hyU', ← map_mul]
  congr 1
  have hpg : ((pullbackGerm f a₀ : Y.functionFieldˣ) : Y.functionField) =
      f.stalkMap (genericPoint Y) a₀.val := rfl
  change functionFieldToK (f ⁻¹ᵁ U) _ *
    functionFieldToK (f ⁻¹ᵁ U) (pullbackGerm f a₀).val = _
  rw [hpg, ← map_mul, hcomm, hcomm, ← map_mul, hkey]

end Pullback

section Big

open MMP.Intersection

/-- The Weil divisor of `n D` is `n` times the Weil divisor of `D`. -/
private theorem isWeilDivisorOfCartier_nsmul {X : Scheme.{0}} {D : X.CartierDivisor}
    {w : Divisor X} (h : IsWeilDivisorOfCartier D w) (n : ℕ) :
    IsWeilDivisorOfCartier (n • D) (n • w) := by
  induction n with
  | zero => exact fun P => by simpa using isOrderAlong_zero (primeDivisorSubvariety P)
  | succ n ih =>
    intro P
    rw [succ_nsmul, succ_nsmul, DivisorWithCoeffs.coeff_add]
    exact (ih P).add (h P)

/-- An `R`-linear equivalence between `R`-modules that are `k`-vector spaces through a ring map
`φ : k →+* R` preserves the `k`-dimension. -/
private theorem finrank_compHom_eq {k : Type} [Field k] {R : Type} [CommRing R]
    (φ : k →+* R) {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (g : M ≃ₗ[R] N) :
    (letI := Module.compHom M φ; Module.finrank k M) =
      (letI := Module.compHom N φ; Module.finrank k N) := by
  letI := Module.compHom M φ
  letI := Module.compHom N φ
  let g' : M ≃ₗ[k] N :=
    { g.toEquiv with map_add' := g.map_add, map_smul' := fun c x => g.map_smul (φ c) x }
  exact g'.finrank_eq

/-- A big Cartier divisor on a normal integral scheme has a big Weil divisor. -/
private theorem isBig_of_isBigCartier {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of k)) {D : X.CartierDivisor}
    {w : Divisor X} (h : IsWeilDivisorOfCartier D w) (hD : IsBigCartier k sX D) :
    w.IsBig k sX := by
  obtain ⟨d, hd, c, hc, k₀, hk⟩ := hD
  refine ⟨d, hd, c, hc, max k₀ 0, fun m hm => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = j := ⟨m.toNat, by omega⟩
  have hj := hk j (le_of_max_le_left hm)
  rw [natCast_zsmul] at hj ⊢
  have he : cartierH0 k sX (j • D) = (j • w).h0 k sX :=
    finrank_compHom_eq (scalarsToGlobalSections k sX)
      (Scheme.Modules.sectionsLinearEquivOfIso
        (isWeilDivisorOfCartier_nsmul h j).sheafIsoDivisorialSheaf ⊤)
  rwa [he] at hj

end Big

section Nef

/-- An ample invertible sheaf has nonnegative degree along every proper curve mapping to `T`. -/
private theorem degreeOn_nonneg_of_isAmple {k : Type} [Field k] {C T : Scheme.{0}}
    (sT : T ⟶ Spec (.of k)) [IsSeparated sT] [LocallyOfFiniteType sT] (φ : C ⟶ T)
    [AlgebraicGeometry.IsCurve k (φ ≫ sT)] [IsProper (φ ≫ sT)] (L : T.Modules)
    [SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2 L] (hL : Stacks.Ample.IsAmple T L) :
    0 ≤ degreeOn k sT φ (IsCurve.topologicalKrullDim_eq_one (f := φ ≫ sT)).le L := by
  by_cases hpt : ∃ x : T, Set.range φ = {x}
  · rw [degreeOn_eq_zero_of_range_eq_singleton sT φ L hpt]
  · rw [degreeOn_eq_degreeOver_mul sT φ L hpt]
    have : IsProper φ := IsProper.of_comp φ sT
    have : IsProper (φ.imageι ≫ sT) := isProper_imageι_comp φ sT
    have : AlgebraicGeometry.IsCurve k (φ.imageι ≫ sT) := isCurve_imageι_comp sT φ hpt
    have h1 := isAmple_pullback_of_isFinite φ.imageι L
      ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple T L).mpr hL)
    have := MMP.Mori.isInvertible_pullback_obj φ.imageι L
    have h2 := invertibleCurveDegree_pos_of_isAmple_of_isCurve k (φ.imageι ≫ sT)
      (topologicalKrullDim_image_le_one sT φ) _ h1
    exact mul_nonneg (by positivity) h2.le

/-- A Cartier divisor `D` on `Y` with `𝒪_Y(D) ≅ g^*L`, `L` ample on `T`, is nef. -/
private theorem isNef_of_iso_pullback {k : Type} [Field k] {Y T : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) (sT : T ⟶ Spec (.of k))
    [IsLocallyNoetherian Y] [IsNormal Y] [QuasiCompact sY] [IsSeparated sT]
    [LocallyOfFiniteType sT] (g : Y ⟶ T) (hg : g ≫ sT = sY)
    (L : T.Modules) [SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2 L]
    (hL : Stacks.Ample.IsAmple T L) (D : Divisor Y) (hD : D.IsCartier)
    (e : D.divisorialSheaf ≅ (Scheme.Modules.pullback g).obj L) :
    D.IsNef k sY := by
  refine ⟨hD, fun C i _ _ _ hC => ?_⟩
  have := QuasiCompact.compactSpace_of_compactSpace sY
  have := hD.isInvertibleModule_divisorialSheaf
  have hc : (i ≫ g) ≫ sT = i ≫ sY := by rw [Category.assoc, hg]
  have : IsProper ((i ≫ g) ≫ sT) := hc ▸ inferInstance
  have : AlgebraicGeometry.IsCurve k ((i ≫ g) ≫ sT) := by
    rw [hc]
    exact { topologicalKrullDim_eq_one := hC }
  have h1 : D.degreeOn k sY i hC.le hD = degreeOn k sT (i ≫ g)
      (IsCurve.topologicalKrullDim_eq_one (f := (i ≫ g) ≫ sT)).le L := by
    rw [← degreeOn_pullback_eq_degreeOn_comp sY sT g i hg]
    exact degreeOn_eq_of_iso k sY i hC.le e
  rw [h1]
  exact degreeOn_nonneg_of_isAmple sT (i ≫ g) L hL

end Nef

section Multiples

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X]

/-- A `ℚ`-divisor with a positive multiple that is a Cartier divisor is `ℚ`-Cartier. -/
private theorem isQCartier_of_toQDivisor_eq_smul {B : QDivisor X} {m : ℕ} (hm : 0 < m)
    {F : Divisor X} (hF : F.IsCartier) (h : Divisor.toQDivisor F = (m : ℚ) • B) :
    B.IsQCartier :=
  ⟨m, by exact_mod_cast hm.ne', F, by rw [h, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast], hF⟩

/-- `(B · C) = deg_C 𝒪_X(F) / m` when `F = mB` is a Cartier divisor. -/
private theorem intersectionNumber_eq_div {C : Scheme.{0}} (i : C ⟶ X) [IsProper (i ≫ sX)]
    (hdim : topologicalKrullDim C ≤ 1) {B : QDivisor X} {m : ℕ} (hm : 0 < m) {F : Divisor X}
    (hF : F.IsCartier) (h : Divisor.toQDivisor F = (m : ℚ) • B) (hB : B.IsQCartier) :
    B.intersectionNumber k sX i hdim hB = (F.degreeOn k sX i hdim hF : ℚ) / m :=
  QDivisor.intersectionNumber_eq_of_smul k sX i hdim B hB hm F hF
    (by rw [h, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast])

/-- A `ℚ`-divisor `B` with a positive multiple `F = mB` a Cartier divisor is nef if and only if
`F` is. -/
private theorem isNef_iff_of_toQDivisor_eq_smul {B : QDivisor X} {m : ℕ} (hm : 0 < m)
    {F : Divisor X} (hF : F.IsCartier) (h : Divisor.toQDivisor F = (m : ℚ) • B) :
    B.IsNef k sX ↔ F.IsNef k sX := by
  have hB := isQCartier_of_toQDivisor_eq_smul hm hF h
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  rw [QDivisor.isNef_iff B hB]
  refine ⟨fun H => ⟨hF, fun C i _ _ _ hC => ?_⟩, fun ⟨_, H⟩ C i _ _ _ hC => ?_⟩
  · have h1 := H C i hC
    rw [intersectionNumber_eq_div i hC.le hm hF h hB] at h1
    have h2 := mul_nonneg h1 hm'.le
    rw [div_mul_cancel₀ _ hm'.ne'] at h2
    exact_mod_cast h2
  · rw [intersectionNumber_eq_div i hC.le hm hF h hB]
    exact div_nonneg (by exact_mod_cast H C i hC) hm'.le

/-- A natural multiple of a `ℚ`-Cartier `ℚ`-divisor is `ℚ`-Cartier. -/
private theorem isQCartier_natCast_smul {B : QDivisor X} (hB : B.IsQCartier) (c : ℕ) :
    ((c : ℚ) • B).IsQCartier := by
  obtain ⟨m, hm, F, hF, hFc⟩ := hB.exists_pos
  exact ⟨m, by omega, c • F, by rw [map_nsmul, hF, ← Nat.cast_smul_eq_nsmul ℚ, smul_comm],
    hFc.nsmul c⟩

/-- `((c B) · C) = c (B · C)` for a natural number `c`. -/
private theorem intersectionNumber_natCast_smul {C : Scheme.{0}} (i : C ⟶ X) [IsProper (i ≫ sX)]
    (hdim : topologicalKrullDim C ≤ 1) {B : QDivisor X} (hB : B.IsQCartier) (c : ℕ)
    (h : ((c : ℚ) • B).IsQCartier) :
    ((c : ℚ) • B).intersectionNumber k sX i hdim h = c * B.intersectionNumber k sX i hdim hB := by
  obtain ⟨m, hm, F, hF, hFc⟩ := hB.exists_pos
  rw [QDivisor.intersectionNumber_eq_of_smul k sX i hdim _ hB hm F hFc hF,
    QDivisor.intersectionNumber_eq_of_smul k sX i hdim _ h hm (c • F) (hFc.nsmul c)
      (by rw [map_nsmul, hF, ← Nat.cast_smul_eq_nsmul ℚ, smul_comm]),
    Divisor.degreeOn_nsmul' k sX i hdim F hFc c]
  push_cast
  ring

/-- Numerical equivalence is compatible with `B ↦ F + c B` for `F` `ℚ`-Cartier and `c ∈ ℕ`. -/
private theorem numericallyEquivalent_add_natCast_smul {F B₁ B₂ : QDivisor X}
    (hF : F.IsQCartier) (h : B₁.NumericallyEquivalent k sX B₂) (c : ℕ) :
    (F + (c : ℚ) • B₁).NumericallyEquivalent k sX (F + (c : ℚ) • B₂) := by
  obtain ⟨h₁, h₂, h⟩ := h
  refine ⟨hF.add (isQCartier_natCast_smul h₁ c), hF.add (isQCartier_natCast_smul h₂ c),
    fun C i _ _ _ hC => ?_⟩
  rw [QDivisor.intersectionNumber_add' k sX i hC.le _ _ hF (isQCartier_natCast_smul h₁ c),
    QDivisor.intersectionNumber_add' k sX i hC.le _ _ hF (isQCartier_natCast_smul h₂ c),
    intersectionNumber_natCast_smul i hC.le h₁, intersectionNumber_natCast_smul i hC.le h₂,
    h C i hC]

end Multiples

/-- A nef Cartier divisor `F` plus a positive multiple `cA` of an ample `ℚ`-divisor is ample:
`F + cA = c (A + c⁻¹ F)` with `c⁻¹ F` nef. -/
private theorem isAmple_toQDivisor_add_natCast_smul {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsProjectiveVariety k sX] [IsNormal X] [IsLocallyNoetherian X]
    [CompactSpace X] [QuasiCompact sX] {F : Divisor X} (hF : F.IsNef k sX) {A : QDivisor X}
    (hA : A.IsAmple) {c : ℕ} (hc : 0 < c) :
    (Divisor.toQDivisor F + (c : ℚ) • A).IsAmple := by
  obtain ⟨m, hm, Dn, hDn, hDnc, -⟩ := id hA
  have hc' : (c : ℚ) ≠ 0 := by positivity
  have hm' : (m : ℚ) ≠ 0 := by positivity
  have hN : ((c : ℚ)⁻¹ • Divisor.toQDivisor F).IsNef k sX :=
    (isNef_iff_of_toQDivisor_eq_smul hc hF.1
      (by rw [smul_smul, mul_inv_cancel₀ hc', one_smul])).2 hF
  have hFc : (m • F + c • Dn).IsCartier := (hF.1.nsmul _).add (hDnc.nsmul _)
  refine ⟨m, hm, _, ?_, hFc, QDivisor.isAmple_of_numericallyEquivalent_add_of_isNef sX hA hN
    (.refl ((isQCartier_of_toQDivisor_eq_smul hm hDnc hDn).add hN.isQCartier)) (m * c)
    (by positivity) _ ?_ hFc⟩ <;>
  · simp only [map_add, map_nsmul, hDn, ← Nat.cast_smul_eq_nsmul ℚ]
    match_scalars <;> push_cast <;> field_simp

/-- A positive rational number is a quotient `p / q` of positive natural numbers. -/
private theorem exists_nat_div_eq_of_pos {r : ℚ} (hr : 0 < r) :
    ∃ p : ℕ, 0 < p ∧ ∃ q : ℕ, 0 < q ∧ r = p / q := by
  refine ⟨r.num.toNat, by have := Rat.num_pos.mpr hr; omega, r.den, r.den_pos, ?_⟩
  have h : ((r.num.toNat : ℕ) : ℚ) = (r.num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_pos.mpr hr).le
  rw [h, Rat.num_div_den]

namespace QDivisor

/-- A nef `ℚ`-divisor `M` plus a positive multiple `r G` of a nef and big divisor `G` on a normal
projective variety is nef and big. -/
theorem IsNef.isNef_and_isBig_add_smul_of_isNef_of_isBig {k : Type} [Field k] {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [IsProjectiveVariety k sY] [IsLocallyNoetherian Y] [IsNormal Y]
    [QuasiCompact sY] {M : QDivisor Y} (hM : M.IsNef k sY) {G : Divisor Y}
    (hGnef : G.IsNef k sY) (hGbig : G.IsBig k sY) {r : ℚ} (hr : 0 < r) :
    (M + r • Divisor.toQDivisor G).IsNef k sY ∧ (M + r • Divisor.toQDivisor G).IsBig k sY := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have hGc : G.IsCartier := hGnef.1
  obtain ⟨E, k₀, A, hE0, hEc, hk₀, hA⟩ :=
    exists_numericallyEquivalent_isAmple_add_smul sY G hGnef hGbig
  obtain ⟨hMq, hMnef⟩ := hM
  obtain ⟨e, he, DM, hDM, hDMc⟩ := hMq.exists_pos
  obtain ⟨p, hp, q, hq, rfl⟩ := exists_nat_div_eq_of_pos hr
  have hDM' : Divisor.toQDivisor DM = (e : ℚ) • M := by
    rw [hDM, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast]
  set D : Divisor Y := q • DM + (e * p) • G with hDdef
  have hDc : D.IsCartier := (hDMc.nsmul q).add (hGc.nsmul (e * p))
  have hDsplit : Divisor.toQDivisor D = Divisor.toQDivisor (q • DM) +
      ((e * p : ℕ) : ℚ) • Divisor.toQDivisor G := by
    rw [hDdef, map_add, map_nsmul _ (e * p), Nat.cast_smul_eq_nsmul]
  have hDeq : Divisor.toQDivisor D =
      ((e * q : ℕ) : ℚ) • (M + ((p : ℚ) / q) • Divisor.toQDivisor G) := by
    have hq' : (q : ℚ) ≠ 0 := by positivity
    rw [hDsplit, map_nsmul, hDM', ← Nat.cast_smul_eq_nsmul ℚ q]
    match_scalars <;> push_cast <;> field_simp
  have hqDMnef : (q • DM).IsNef k sY :=
    (isNef_iff_of_toQDivisor_eq_smul (m := e * q) (by positivity) (hDMc.nsmul q) (by
      rw [map_nsmul, hDM', ← Nat.cast_smul_eq_nsmul ℚ]
      match_scalars
      push_cast
      ring)).1 ⟨hMq, hMnef⟩
  set A' : ℕ → QDivisor Y := fun n =>
    Divisor.toQDivisor (q • DM) + ((e * p : ℕ) : ℚ) • A n with hA'def
  set E' : QDivisor Y := Divisor.toQDivisor ((e * p) • E) with hE'def
  have hinf : {n : ℕ | (A' n).IsAmple ∧ (Divisor.toQDivisor D).NumericallyEquivalent
      k sY (A' n + (n : ℚ)⁻¹ • E')}.Infinite := by
    refine (Set.Ici_infinite k₀).mono fun n hn => ?_
    obtain ⟨hAn, hnum⟩ := hA n hn
    refine ⟨isAmple_toQDivisor_add_natCast_smul sY hqDMnef hAn (by positivity), ?_⟩
    have h : A' n + (n : ℚ)⁻¹ • E' = Divisor.toQDivisor (q • DM) +
        ((e * p : ℕ) : ℚ) • (A n + (n : ℚ)⁻¹ • Divisor.toQDivisor E) := by
      rw [hA'def, hE'def, map_nsmul _ (e * p) E,
        ← Nat.cast_smul_eq_nsmul ℚ _ (Divisor.toQDivisor E)]
      module
    rw [hDsplit, h]
    exact numericallyEquivalent_add_natCast_smul
      (QDivisor.isQCartier_toQDivisor (hDMc.nsmul q)) hnum _
  have hE' : 0 ≤ E' := Finsupp.le_def.2 fun P => by
    have h : (0 : ℤ) ≤ ((e * p) • E) P := Finsupp.le_def.1 (nsmul_nonneg hE0 (e * p)) P
    change (0 : ℚ) ≤ (((e * p) • E) P : ℚ)
    exact_mod_cast h
  have key := Divisor.isNef_and_isBig_of_numericallyEquivalent_isAmple_add_smul sY D hDc
    E' hE' (QDivisor.isQCartier_toQDivisor (hEc.nsmul _)) A' hinf
  exact ⟨(isNef_iff_of_toQDivisor_eq_smul (by positivity) hDc hDeq).2 key.1,
    ⟨e * q, by positivity, D, hDeq, hDc, key.2⟩⟩

/-- **Nef plus the pull-back of an ample divisor is nef and big.** Let `f : Y ⟶ X` be a
birational `k`-morphism from a normal projective variety `Y` to a projective variety `X`, `M` a
nef `ℚ`-Cartier `ℚ`-divisor on `Y`, `H` an ample Cartier divisor on `X`, with Weil divisor `G` of
its pull-back `f^*H`, and `r > 0` rational. Then `M + r f^*H` is nef and big. -/
@[mmp "lem_km2c_nef_plus_nef_big_is_nef_big"]
theorem IsNef.isNef_and_isBig_add_smul_pullback {k : Type} [Field k]
    {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [IsProjectiveVariety k sX] [IsProjectiveVariety k sY] [IsLocallyNoetherian Y] [IsNormal Y]
    (f : Y ⟶ X) (hf : f ≫ sX = sY) (hbir : IsBirationalMorphism f)
    {M : QDivisor Y} (hM : M.IsNef k sY)
    (H : X.CartierDivisor)
    (hamp : Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf H))
    (hH : ¬ Set.range f ⊆ MMP.Intersection.cartierSupport H) {G : Divisor Y}
    (hG : MMP.Intersection.IsWeilDivisorOfCartier
      (MMP.CartierDivisor.pullback f H hH) G)
    {r : ℚ} (hr : 0 < r) :
    (M + r • Divisor.toQDivisor G).IsNef k sY ∧ (M + r • Divisor.toQDivisor G).IsBig k sY := by
  have hXv : AlgebraicGeometry.IsVariety k sX :=
    ((AlgebraicGeometry.isProjectiveVariety_iff k sX).1 ‹_›).1
  have hYv : AlgebraicGeometry.IsVariety k sY :=
    ((AlgebraicGeometry.isProjectiveVariety_iff k sY).1 ‹_›).1
  have : IsIntegral X := hXv.toIsIntegral
  have : IsIntegral Y := hYv.toIsIntegral
  have := hXv.toIsSeparated
  have := hXv.toLocallyOfFiniteType
  have : IsProper sX := (IsProjectiveMorphism.isProjective
    (AlgebraicGeometry.IsProjectiveVariety.isProjective (k := k) (f := sX))).isProper
  have : IsProper sY := (IsProjectiveMorphism.isProjective
    (AlgebraicGeometry.IsProjectiveVariety.isProjective (k := k) (f := sY))).isProper
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hGnef : G.IsNef k sY := isNef_of_iso_pullback sY sX f hf _ hamp G hG.isCartier
    (hG.sheafIsoDivisorialSheaf.symm ≪≫ MMP.CartierDivisor.pullbackSheafIso f H hH)
  have hHbig : IsBigCartier k sX H :=
    isBigCartier_of_linearlyEquivalent_add (A := H) (E := 0) ‹_› one_pos hamp
      MMP.Intersection.isEffective_zero (by simpa using
        MMP.Intersection.LinearlyEquivalent.refl H)
  have hPbig := (isBigCartier_iff_of_isPullback
    ((AlgebraicGeometry.isProperVariety_iff k sX).2 ⟨hXv, inferInstance⟩)
    ((AlgebraicGeometry.isProperVariety_iff k sY).2 ⟨hYv, inferInstance⟩) f hf hbir
    (isPullback_cartierDivisor_pullback f H hH)).mp hHbig
  exact hM.isNef_and_isBig_add_smul_of_isNef_of_isBig sY hGnef
    (isBig_of_isBigCartier sY hG hPbig) hr

end QDivisor

end MMP.Mori
