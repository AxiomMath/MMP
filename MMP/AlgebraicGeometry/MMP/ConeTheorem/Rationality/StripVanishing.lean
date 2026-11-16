module

public import MMP.AlgebraicGeometry.Vanishing.KawamataViehwegRoundUp
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.BelowNefThreshold
public import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
public import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction

@[expose] public section

universe u

section

/-!
# Vanishing of higher cohomology just above the nef threshold

Let `(X, Δ, a, H)` be a rationality datum with nef threshold `r`, `g : Y ⟶ X` a log resolution
of `(X, Δ)` with `Y` projective, `H' = g^*H`, `B' = g^*(a(K_X + Δ))` and `A` the `ℚ`-divisor with
`K_Y = g^*(K_X + Δ) + A`. For integers `x ≥ 1` and `y` with `0 < ay - rx < 1` we have `y ≥ 1`,
so `B = xH + (ay - 1)(K_X + Δ)` is nef and big; its pull-back
`N = x H' + y B' - K_Y + A` is then nef (degrees on curves are nonnegative multiples of degrees
on their images) and big (pulling back sections is injective). The support of `A` lies in
`Ex(g) ∪ g⁻¹(Supp Δ)`, an snc divisor, so Kawamata–Viehweg vanishing for the round-up gives
`Hⁱ(Y, 𝒪_Y(K_Y + ⌈N⌉)) = 0` for `i > 0`, and `K_Y + ⌈N⌉ = x H' + y B' + ⌈A⌉`.

## Main results

* `MMP.Mori.IsRationalityDatum.cohomology_subsingleton_of_isLogResolution`

## Implementation notes

The canonical divisor `K_Y` is chosen as `div(g^*ω)` for a rational top form `ω` with
`K_X = div(ω)`; for this choice the crepant boundary `-A` satisfies
`a(K_Y - A) = g^*(a(K_X + Δ))` as divisors.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.4, Step 6
-/

open CategoryTheory AlgebraicGeometry MMP.Mori Opposite

namespace MMP.FourfoldProofs.Km3bRationalityStripVanishingProof

section Sections

variable {k : Type u} [Field k]

/-- Restricting a section of a module twice is restricting it once. -/
private theorem map_map_homOfLE {X : Scheme.{u}} (L : X.Modules) {P Q R : X.Opens} (h₁ : Q ≤ P)
    (h₂ : P ≤ R) (σ : Γ(L, R)) :
    L.presheaf.map (homOfLE h₁).op (L.presheaf.map (homOfLE h₂).op σ) =
      L.presheaf.map (homOfLE (h₁.trans h₂)).op σ := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restricting a section of a module to its own open does nothing. -/
private theorem map_homOfLE_refl {X : Scheme.{u}} (L : X.Modules) {W : X.Opens} (σ : Γ(L, W)) :
    L.presheaf.map (homOfLE (le_refl W)).op σ = σ := by
  rw [show homOfLE (le_refl W) = 𝟙 W from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- A generator of an invertible module over every open inside `K` pulls back, along the unit of
`b^* ⊣ b_*`, to a generator over every open inside `b⁻¹ K`. -/
private theorem bijective_smul_unit_app {X Y : Scheme.{u}} (b : X ⟶ Y) (A : Y.Modules)
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
    (X := X.toRingedSpace) _ (Stacks.RingedSpace.pullbackUnit b.toLRSHom.toShHom A (op K) a)
    _ hW fun x hx => ?_
  have h1 := Scheme.Modules.germ_notMem_maximalSmul_of_bijective_smul A a ha (b.base x) (hW hx)
  rw [← Stacks.NonvanishingLocusRestrict.mem_maximalSmul_germ_pullbackUnit_iff b A a x
    (hW hx)] at h1
  rwa [Stacks.NonvanishingPullback.mem_maximalSmul_iff] at h1

/-- A global section of an invertible module on an integral scheme vanishing on a nonempty open
vanishes. -/
private theorem eq_zero_of_map_eq_zero {X : Scheme.{u}} [IsIntegral X] (L : X.Modules)
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
private theorem unit_app_top_injective {Y T : Scheme.{u}} [IsIntegral Y] [IsIntegral T]
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
  have ht0 : t = 0 := by rw [← hf, hf0]; exact zero_smul _ _
  exact eq_zero_of_map_eq_zero M ⟨g y0, hyU⟩ s ht0

/-- The `k`-structure on global sections, written through `Scheme.Hom.appLE`. -/
private theorem scalarsToGlobalSections_eq' {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) :
    scalarsToGlobalSections k sX =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ ⊤ (by simp)).hom := by
  rw [show sX.appLE ⊤ ⊤ _ = sX.app ⊤ from sX.appLE_eq_app]
  rfl

/-- The global sections of `𝒪_X(D)`, `D` Cartier on a proper `k`-scheme, are finite over `k`. -/
private theorem finite_divisorialSubmodule_top {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsProper sX] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {D : Divisor X} (hD : D.IsCartier) :
    letI := Module.compHom (D.divisorialSubmodule ⊤) (scalarsToGlobalSections k sX);
    Module.Finite k (D.divisorialSubmodule ⊤) := by
  have := hD.isInvertibleModule_divisorialSheaf
  have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k sX
    D.divisorialSheaf 1
  have := finiteDimensional_cohomologyOverField_of_isProper k sX D.divisorialSheaf 0
  rw [scalarsToGlobalSections_eq' sX]
  letI := Module.compHom (D.divisorialSubmodule ⊤)
    ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ ⊤ (by simp)).hom
  exact .equiv (cohomologyOverFieldZeroLinearIso k sX D.divisorialSheaf).toLinearEquiv

/-- **Pulling back sections.** For a dominant morphism `g : Y ⟶ X` of integral normal schemes,
`Y` proper over `k`, and Cartier divisors `D` on `X` and `D'` on `Y` with
`𝒪_Y(D') ≅ g^*𝒪_X(D)`, `h⁰(X, 𝒪_X(D)) ≤ h⁰(Y, 𝒪_Y(D'))`. -/
private theorem h0_le_h0_of_iso_pullback {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
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
  have hφ : Function.Injective φ := fun s t hst => by
    refine unit_app_top_injective g M ?_
    have := congrArg (e.hom.app ⊤) hst
    change e.hom.app ⊤ (e.inv.app ⊤ (η.app ⊤ s)) = e.hom.app ⊤ (e.inv.app ⊤ (η.app ⊤ t)) at this
    exact (h2 _).symm.trans (this.trans (h2 _))
  unfold Divisor.h0
  letI := Module.compHom (D.divisorialSubmodule ⊤) (scalarsToGlobalSections k sX)
  exact LinearMap.finrank_le_finrank_of_injective (f := (φ : D.divisorialSubmodule ⊤ →ₗ[k] _)) hφ

end Sections

section Pullback

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] [CompactSpace X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
  [CompactSpace Y] {sX : X ⟶ Spec (.of k)} [IsProper sX] {g : Y ⟶ X} [IsProper g] [IsDominant g]
  {H : Divisor X} {H' : Divisor Y}

/-- **The pull-back of a big divisor is big.** Pulling back sections embeds `H⁰(X, 𝒪_X(mH))`
into `H⁰(Y, 𝒪_Y(mH'))` for `H'` the pull-back of `H` along `g`. -/
private theorem isBig_of_isPullback (hn : topologicalKrullDim X = topologicalKrullDim Y)
    (hH : H.IsCartier) (hH'c : H'.IsCartier)
    {hHg : ∀ Z : irreducibleComponents Y, g (componentGenericPoint Y Z) ∉ H.supp}
    (hH' : H.IsPullback g hHg H') (hbig : H.IsBig k sX) : H'.IsBig k (g ≫ sX) := by
  obtain ⟨d, hdX, c, hc, k₀, hk⟩ := hbig
  refine ⟨d, hn.symm.trans hdX, c, hc, k₀, fun m hm => (hk m hm).trans_le ?_⟩
  have hBm : ∀ Z, g (componentGenericPoint Y Z) ∉ (m • H).supp := fun Z hZ => hHg Z (by
    obtain ⟨E, hE, hx⟩ := DivisorWithCoeffs.mem_supp_iff.mp hZ
    exact DivisorWithCoeffs.mem_supp_iff.mpr
      ⟨E, fun h => hE (by rw [DivisorWithCoeffs.coeff_smul, h, smul_zero]), hx⟩)
  exact_mod_cast h0_le_h0_of_iso_pullback sX g (hH.zsmul m) (hH'c.zsmul m)
    ((hH'.zsmul hH m hBm).divisorialSheafIso (hBc := hH.zsmul m))

end Pullback

section Nef

variable {k : Type u} [Field k]

/-- If `u ≫ s_W = s_V` and the curve `C ⊆ V` is not contracted by `u`, its image `u(C)` is a
proper curve in `W`. -/
private theorem isCurve_imageι_of_comp_eq {V W C : Scheme.{u}} {sV : V ⟶ Spec (.of k)}
    {sW : W ⟶ Spec (.of k)} [AlgebraicGeometry.IsVariety k sW] {u : V ⟶ W} (hu : u ≫ sW = sV)
    (i : C ⟶ V) [AlgebraicGeometry.IsCurve k (i ≫ sV)] [IsProper (i ≫ sV)]
    (hpt : ¬ ∃ w : W, Set.range (i ≫ u) = {w}) :
    IsProper ((i ≫ u).imageι ≫ sW) ∧ AlgebraicGeometry.IsCurve k ((i ≫ u).imageι ≫ sW) := by
  have e : (i ≫ u) ≫ sW = i ≫ sV := by rw [Category.assoc, hu]
  have : IsProper ((i ≫ u) ≫ sW) := e ▸ inferInstance
  have : AlgebraicGeometry.IsCurve k ((i ≫ u) ≫ sW) := e ▸ inferInstance
  have : IsProper (i ≫ u) := IsProper.of_comp (i ≫ u) sW
  exact ⟨isProper_imageι_comp (i ≫ u) sW, isCurve_imageι_comp sW (i ≫ u) hpt⟩

/-- **The pull-back of a nef `ℚ`-divisor is nef.** For a morphism `u : V ⟶ W` of normal varieties
over `k` and a curve `C ⊆ V`, `(u^*L · C)` is `0` if `u(C)` is a point and a nonnegative multiple
of `(L · u(C))` otherwise. -/
private theorem isNef_of_isPullback {V W : Scheme.{u}} {sV : V ⟶ Spec (.of k)}
    {sW : W ⟶ Spec (.of k)} [AlgebraicGeometry.IsVariety k sV]
    [AlgebraicGeometry.IsVariety k sW] [IsLocallyNoetherian V] [IsNormal V]
    [IsLocallyNoetherian W] [IsNormal W] {u : V ⟶ W} (hu : u ≫ sW = sV) {L : QDivisor W}
    (hL : L.IsNef k sW)
    {hLB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp}
    {L' : QDivisor V} (h : L.IsPullback u hLB L') : L'.IsNef k sV := by
  refine ⟨h.isQCartier hL.1, fun C i _ _ _ hC => ?_⟩
  have : AlgebraicGeometry.IsCurve k (i ≫ sV) := { topologicalKrullDim_eq_one := hC }
  by_cases hpt : ∃ w : W, Set.range (i ≫ u) = {w}
  · exact (intersectionNumber_pullback_eq_zero k sV sW u hu i hL.1 h hpt).ge
  · obtain ⟨_, hcurve⟩ := isCurve_imageι_of_comp_eq hu i hpt
    haveI : IsIntegral (i ≫ u).image := hcurve.toIsIntegral
    rw [intersectionNumber_pullback_eq_degreeOver_mul k sV sW u hu i hL.1 h hcurve]
    exact mul_nonneg (by positivity)
      (hL.2 _ (i ≫ u).imageι hcurve.topologicalKrullDim_eq_one)

end Nef

section NefBig

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] [CompactSpace X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
  [CompactSpace Y] {sX : X ⟶ Spec (.of k)} [IsProper sX] [AlgebraicGeometry.IsVariety k sX]
  {g : Y ⟶ X} [IsProper g] [IsDominant g] [AlgebraicGeometry.IsVariety k (g ≫ sX)]

/-- **The pull-back of a nef and big `ℚ`-divisor is nef and big**, along a dominant proper
morphism `g : Y ⟶ X` of normal varieties of the same dimension on whose source every divisor is
Cartier. -/
private theorem isNef_and_isBig_of_isPullback (hn : topologicalKrullDim X = topologicalKrullDim Y)
    (hC : ∀ D : Divisor Y, D.IsCartier) {B : QDivisor X}
    {hB : ∀ Z : irreducibleComponents Y, g (componentGenericPoint Y Z) ∉ B.supp} {N : QDivisor Y}
    (hN : B.IsPullback g hB N) (hnef : B.IsNef k sX) (hbig : B.IsBig k sX) :
    N.IsNef k (g ≫ sX) ∧ N.IsBig k (g ≫ sX) := by
  refine ⟨isNef_of_isPullback rfl hnef hN, ?_⟩
  obtain ⟨m, hm, D, hD, hDc, hDb⟩ := hbig
  obtain ⟨D', hD', hDp⟩ := hN m hm D (by rw [hD, natCast_zsmul, Nat.cast_smul_eq_nsmul]) hDc
  exact ⟨m, hm, D', by rw [hD', natCast_zsmul, Nat.cast_smul_eq_nsmul], hC _,
    isBig_of_isPullback hn hDc (hC _) hDp hDb⟩

end NefBig

/-- A nef threshold of `H` with respect to `P` is nonnegative when `H` itself is nef. -/
private theorem nonneg_of_isNefThreshold {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    {H P : QDivisor X} {r : ℝ} (hr : QDivisor.IsNefThreshold k sX H P r) (hH : H.IsNef k sX) :
    0 ≤ r := by
  obtain ⟨hHq, hPq, -⟩ := hr.1
  exact not_lt.1 fun hr0 => hr.2 0 hr0 ⟨hHq, hPq, fun C i _ _ _ hC => by
    rw [zero_mul, add_zero]
    exact_mod_cast hH.2 C i hC⟩

/-- **Pull-back of a rescaled `ℚ`-divisor.** Let `f : Y ⟶ X` map generic points of components of
`Y` outside every divisor, `B` a `ℚ`-divisor on `X`, `a > 0`, and `M` a Cartier divisor with
`M = aB` and pull-back `M'`. A `ℚ`-divisor `N` with `aN = M'` is the pull-back of `B`. -/
private theorem isPullback_of_toQDivisor_eq_smul {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X}
    (hgen : ∀ (C : Divisor X) (Z : irreducibleComponents Y), f (componentGenericPoint Y Z) ∉ C.supp)
    {B : QDivisor X} (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ B.supp)
    {a : ℕ} (ha : 0 < a) {M : Divisor X} (hMc : M.IsCartier)
    (hM : Divisor.toQDivisor M = (a : ℤ) • B) {M' : Divisor Y}
    (hM' : M.IsPullback f (hgen M) M') {N : QDivisor Y}
    (hN : Divisor.toQDivisor M' = (a : ℤ) • N) : B.IsPullback f hB N := by
  intro m hm D hD hDc
  refine ⟨D.pullback hDc (hgen D), ?_, Divisor.isPullback_pullback hDc _⟩
  have e1 : (a : ℤ) • D = (m : ℤ) • M := Divisor.toQDivisor_injective (by
    rw [map_zsmul, map_zsmul, hD, hM, smul_smul, smul_smul, mul_comm])
  have p1 := (Divisor.isPullback_pullback hDc (hgen D)).zsmul hDc (a : ℤ) (hgen _)
  have p2 := hM'.zsmul hMc (m : ℤ) (hgen _)
  have e2 : (a : ℤ) • D.pullback hDc (hgen D) = (m : ℤ) • M' :=
    (p1.of_eq (hB₂ := hgen _) e1).eq (hMc.zsmul (m : ℤ)) p2
  have e3 := congrArg Divisor.toQDivisor e2
  rw [map_zsmul, map_zsmul, hN, smul_comm] at e3
  exact smul_right_injective _ (by exact_mod_cast ha.ne' : (a : ℤ) ≠ 0) e3

/-- The round-down of a `ℚ`-divisor with integral coefficients is the divisor itself. -/
private theorem roundDown_toQDivisor {X : Scheme.{u}} (D : Divisor X) :
    (Divisor.toQDivisor D).roundDown = D := by
  ext E
  change ((Divisor.toQDivisor D).roundDown).coeff E = D.coeff E
  rw [DivisorWithCoeffs.coeff_roundDown, Divisor.coeff_toQDivisor, Int.floor_intCast]

/-- With `N = (D - K_Y) + A` for integral `D, K_Y`, the round-up satisfies
`K_Y + ⌈N⌉ = D + ⌈A⌉`. -/
private theorem add_roundUp_toQDivisor_sub_add {Y : Scheme.{u}} (D KY : Divisor Y)
    (A : QDivisor Y) : KY + (Divisor.toQDivisor (D - KY) + A).roundUp = D + A.roundUp := by
  ext P
  simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_roundUp,
    Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_sub]
  rw [Int.ceil_intCast_add]
  ring

/-! ### The support of the crepant boundary -/

section Crepant

variable {k : Type u} [Field k] [CharZero k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
  {f : Y ⟶ X}

/-- **The support of the crepant boundary.** For a birational morphism `f : Y ⟶ X` from a
normal variety, every prime divisor in the support of the crepant boundary `Δ_Y` is
`f`-exceptional or lies over `Supp Δ`. -/
private theorem genericPoint_mem_exceptionalSet_or_mem_of_mem_support (hP : IsPairWith sX n K Δ)
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) {ΔY : QDivisor Y}
    (hΔY : IsCrepantBoundary sX n K Δ f hY hf ΔY) {G : MMP.Mori.PrimeDivisor Y}
    (hG : G ∈ ΔY.support) :
    G.genericPoint ∈ (exceptionalSet f : Set Y) ∨ f G.genericPoint ∈ (Δ.supp : Set X) := by
  by_cases hGe : (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX).IsExceptional
  · exact Or.inl (MMP.Positivity.support_subset_exceptionalSet G hGe
      (MMP.Flips.primeDivisor_genericPoint_mem_support G))
  · obtain ⟨P, hc, hd⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hP _ hGe
    have hη : f G.genericPoint = P.genericPoint := by
      refine (inseparable_iff_closure_eq.2 ?_).eq
      rw [← DivisorOver.center_eq_closure_genericPoint (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX), hc,
        AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    have hc' : ΔY.coeff G = Δ.coeff P := neg_injective ((hΔY G).eq hd)
    refine Or.inr ?_
    rw [hη, DivisorWithCoeffs.coe_supp]
    refine Set.mem_iUnion₂.2 ⟨P, ?_, MMP.Flips.primeDivisor_genericPoint_mem_support P⟩
    rwa [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply, ← hc',
      DivisorWithCoeffs.coeff_apply, ← Finsupp.mem_support_iff]

/-- **The crepant boundary of a log resolution is snc.** If `g : Y ⟶ X` is a log resolution of
the pair `(X, Δ)` and `-A` is the crepant boundary of `(X, Δ)` on `Y`, then `A` is supported on
the snc divisor `Ex(g) ∪ g⁻¹(Supp Δ)`. -/
private theorem isSNC_of_isCrepantBoundary_neg [IsLocallyNoetherian Y] [IsNormal Y]
    (hP : IsPairWith sX n K Δ) (hg : IsLogResolution sX (QDivisor.toRDivisor Δ) f)
    (hY : IsNormalVariety k (f ≫ sX)) {A : QDivisor Y}
    (hA : IsCrepantBoundary sX n K Δ f hY hg.isBirationalMorphism (-A)) : A.IsSNC (f ≫ sX) := by
  classical
  have hsm : IsSmoothScheme (f ≫ sX) := hg.isSmoothScheme
  have hmem : ∀ G ∈ A.support, G.genericPoint ∈
      ((exceptionalSet f ⊔ (QDivisor.toRDivisor Δ).supp.preimage f.continuous : _) : Set Y) := by
    intro G hG
    have hG' : G ∈ (-A).support := by rwa [Finsupp.support_neg]
    rcases genericPoint_mem_exceptionalSet_or_mem_of_mem_support hP hY hg.isBirationalMorphism hA
      hG' with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      change f G.genericPoint ∈ ((QDivisor.toRDivisor Δ).supp : Set X)
      rwa [QDivisor.supp_toRDivisor]
  rcases hg.isSNCSubset with h0 | ⟨s, hs, hsnc⟩
  · have hA0 : A.support = ∅ := Finset.eq_empty_of_forall_notMem fun G hG => by
      have := hmem G hG
      rw [h0] at this
      exact this
    haveI : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
    haveI : LocallyOfFinitePresentation (f ≫ sX) :=
      (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := f ≫ sX)).mpr inferInstance
    exact (DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme (R := ℤ) (f ≫ sX) hsm).of_support_subset
      (by rw [hA0]; exact Finset.empty_subset _)
  · refine hsnc.of_support_subset fun G hG => ?_
    have h := hmem G hG
    rw [← hs] at h
    obtain ⟨E, hE, hgen⟩ := Set.mem_iUnion₂.mp h
    rw [MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hgen] at hE
    rw [Finsupp.mem_support_iff, Finsupp.finsetSum_apply]
    simp [Finsupp.single_apply, hE]

/-- **The pull-back of `a(K_X + Δ)` is `a(K_Y - A)`.** Let `g : Y ⟶ X` be a log resolution of
the pair `(X, Δ)` and `-A` the crepant boundary of `(X, Δ)` on `Y`. For `a > 0` with `a(K_X + Δ)`
a Cartier divisor `R`, the canonical divisor `K_Y = div(g^*ω)`, where `K_X = div(ω)`, satisfies
`g^*R = a(K_Y - A)`. -/
private theorem exists_isCanonicalDivisor_toQDivisor_eq_smul [CompactSpace X]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (hP : IsPairWith sX n K Δ)
    (hg : IsLogResolution sX (QDivisor.toRDivisor Δ) f) (hYn : IsNormalVariety k (f ≫ sX))
    {A : QDivisor Y} (hA : IsCrepantBoundary sX n K Δ f hYn hg.isBirationalMorphism (-A))
    {a : ℕ} (ha : 0 < a) {R : Divisor X} (hRc : R.IsCartier)
    (hRQ : Divisor.toQDivisor R = (a : ℤ) • (Divisor.toQDivisor K + Δ))
    {hRf : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ R.supp}
    {B' : Divisor Y} (hB' : R.IsPullback f hRf B') :
    ∃ KY : Divisor Y, KY.IsCanonicalDivisor (f ≫ sX) n ∧
      Divisor.toQDivisor B' = (a : ℤ) • (Divisor.toQDivisor KY + -A) := by
  have hbir := hg.isBirationalMorphism
  have hK : K.IsCanonicalDivisor sX n := hP.2.1
  have : IsDominant f := hbir.isDominant
  have : AlgebraicGeometry.IsVariety k sX := hP.1.1
  have : AlgebraicGeometry.IsVariety k (f ≫ sX) := hYn.1
  have : LocallyOfFiniteType sX := hP.1.1.toLocallyOfFiniteType
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hP.1 hK
  have hτ0 := MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' f
    hbir.functionFieldMap_bijective
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hK.topologicalKrullDim_eq) hω0
  obtain ⟨K₀, hK₀⟩ := exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sX) hg.isSmoothScheme
    ((MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (f ≫ sX) hbir).symm.trans
      hK.topologicalKrullDim_eq)
  have hKY : (divisorOfForm (pullbackRationalPluriForms sX f ω)).IsCanonicalDivisor (f ≫ sX) n :=
    hK₀.of_linearlyEquivalent (by
      simpa only [one_zsmul] using
        MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hYn hK₀ hτ0)
  obtain ⟨hcart, -, -⟩ := IsPair.isPullback_of_isCrepantBoundary hP.isPair f hYn hbir hK hKY
    (Or.inl ⟨ω, hω0, by ext Γ; exact hωK Γ, rfl⟩) hA
  obtain ⟨DY, hDYQ, -, _, hDYp⟩ := hcart a ha R hRQ hRc
  rw [hDYp.eq hRc hB'] at hDYQ
  exact ⟨_, hKY, hDYQ⟩

end Crepant

end MMP.FourfoldProofs.Km3bRationalityStripVanishingProof

end

section

/-!
# Vanishing of higher cohomology just above the nef threshold

Let `(X, Δ, a, H)` be a rationality datum with nef threshold `r` of `H` with respect to
`K_X + Δ`, let `g : Y ⟶ X` be a log resolution of `(X, Δ)` with `Y` projective, and let `A` be
the `ℚ`-divisor on `Y` with `K_Y = g^*(K_X + Δ) + A`. For integers `x ≥ 1` and `y` with
`0 < ay - rx < 1`,
`Hⁱ(Y, 𝒪_Y(x g^*H + y g^*(a(K_X + Δ)) + ⌈A⌉)) = 0` for every `i > 0`.
Indeed `y ≥ 1`, so `B = xH + (ay - 1)(K_X + Δ)` is nef and big, hence so is `g^*B`, and
`x g^*H + y g^*(a(K_X + Δ)) + A - K_Y = g^*B` with `A` supported on the snc divisor
`Ex(g) ∪ g⁻¹(Supp Δ)`; Kawamata–Viehweg vanishing in its round-up form concludes.

## Main results

* `MMP.Mori.IsRationalityDatum.cohomology_subsingleton_of_isLogResolution`: the statement above.

## Implementation notes

As in `MMP.Mori.IsRationalityDatum.coeff_eulerPolynomial_of_isLogResolution`, the pull-backs
`g^*H` and `g^*(a(K_X + Δ))` are divisors `H'` and `B'` on `Y` satisfying
`MMP.Mori.Divisor.IsPullback`, the integral divisor `a(K_X + Δ)` being `⌊a(K_X + Δ)⌋`. As in
`MMP.Mori.IsStripAdaptedResolution`, the relation `K_Y = g^*(K_X + Δ) + A` says that `-A` is the
crepant boundary of `(X, Δ)` on `Y` (`MMP.Mori.IsCrepantBoundary`). The inequalities
`0 < ay - rx < 1` are read in `ℝ`, and the vanishing of `Hⁱ` is the subsingleton property of the
`k`-vector space `cohomologyOverField`. The ground field is algebraically closed of
characteristic zero, as Kawamata–Viehweg vanishing requires.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Theorem 3.5, 3.4 Step 6
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MMP.FourfoldProofs.Km3bRationalityStripVanishingProof

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori

/-- **Vanishing just above the nef threshold** (Kollár–Mori 3.4, Step 6).
Let `(X, Δ, a, H)` be a rationality datum with nef threshold `r` of `H` with respect to
`K_X + Δ`, `g : Y ⟶ X` a log resolution of `(X, Δ)` with `Y` projective, `H'` and `B'` the
pull-backs of `H` and of `a(K_X + Δ)` to `Y`, and `A` a `ℚ`-divisor on `Y` with
`K_Y = g^*(K_X + Δ) + A` (that is, `-A` is the crepant boundary of `(X, Δ)` on `Y`). Then for
integers `x ≥ 1` and `y` with `0 < ay - rx < 1`, `Hⁱ(Y, 𝒪_Y(x H' + y B' + ⌈A⌉)) = 0` for every
`i > 0`. -/
@[mmp "lem_km3b_rationality_strip_vanishing"]
public theorem IsRationalityDatum.cohomology_subsingleton_of_isLogResolution
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX]
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {a : ℤ} {H : Divisor X}
    (hd : IsRationalityDatum sX n K Δ a H) {r : ℝ}
    (hr : QDivisor.IsNefThreshold k sX (Divisor.toQDivisor H) (Divisor.toQDivisor K + Δ) r)
    {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {g : Y ⟶ X}
    (hg : IsLogResolution sX (QDivisor.toRDivisor Δ) g) (_hY : IsProjectiveVariety k (g ≫ sX))
    {A : QDivisor Y}
    (hA : ∃ hYn : IsNormalVariety k (g ≫ sX),
      IsCrepantBoundary sX n K Δ g hYn hg.isBirationalMorphism (-A))
    {hHg : ∀ Z : irreducibleComponents Y, g (componentGenericPoint Y Z) ∉ H.supp}
    {H' : Divisor Y} (hH' : H.IsPullback g hHg H')
    {hBg : ∀ Z : irreducibleComponents Y,
      g (componentGenericPoint Y Z) ∉ (a • (Divisor.toQDivisor K + Δ)).roundDown.supp}
    {B' : Divisor Y} (hB' : (a • (Divisor.toQDivisor K + Δ)).roundDown.IsPullback g hBg B')
    {x y : ℤ} (hx : 1 ≤ x) (hxy : 0 < (a * y : ℝ) - r * x) (hxy' : (a * y : ℝ) - r * x < 1)
    {i : ℕ} (hi : 0 < i) :
    Subsingleton (cohomologyOverField k (g ≫ sX)
      (x • H' + y • B' + DivisorWithCoeffs.roundUp A).divisorialSheaf i) := by
  obtain ⟨hYn, hcrep⟩ := hA
  obtain ⟨a₀, rfl⟩ := Int.eq_ofNat_of_zero_le hd.pos.le
  have ha₀ : 0 < a₀ := by exact_mod_cast hd.pos
  have hP : IsPairWith sX n K Δ := hd.isKltPair.1
  have hsm : IsSmoothScheme (g ≫ sX) := hg.isSmoothScheme
  have : IsProper g := hg.isProper
  have : IsDominant g := hg.isBirationalMorphism.isDominant
  have : IsIntegral Y := hYn.1.toIsIntegral
  have : AlgebraicGeometry.IsProperVariety k sX := hd.isProperVariety
  have : AlgebraicGeometry.IsVariety k sX := hP.1.1
  have : AlgebraicGeometry.IsVariety k (g ≫ sX) := hYn.1
  have : LocallyOfFiniteType sX := hP.1.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (g ≫ sX) := hYn.1.toLocallyOfFiniteType
  have hgen : ∀ (C : Divisor X) (Z : irreducibleComponents Y),
      g (componentGenericPoint Y Z) ∉ C.supp :=
    MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant g
  -- `R = a(K_X + Δ)` is Cartier, and `B' = g^*R = a(K_Y - A)`
  obtain ⟨D₀, hRQ, hRc⟩ := hd.isCartierDivisor
  obtain rfl : ((a₀ : ℤ) • (Divisor.toQDivisor K + Δ)).roundDown = D₀ := by
    rw [← hRQ, roundDown_toQDivisor]
  set R := ((a₀ : ℤ) • (Divisor.toQDivisor K + Δ)).roundDown
  obtain ⟨KY, hKY, hB'Q⟩ :=
    exists_isCanonicalDivisor_toQDivisor_eq_smul hP hg hYn hcrep ha₀ hRc hRQ hB'
  -- `ay ≥ 1`, since `r ≥ 0`
  have hHc := hd.isCartier_H
  have hr0 := nonneg_of_isNefThreshold hr ((QDivisor.isNef_toQDivisor_iff H hHc).mpr hd.isNef_H)
  have hay : (0 : ℤ) < a₀ * y := by
    have : (0 : ℝ) ≤ r * x := mul_nonneg hr0 (by exact_mod_cast (by omega : (0 : ℤ) ≤ x))
    have : (0 : ℝ) < ((a₀ * y : ℤ) : ℝ) := by
      push_cast at hxy ⊢
      linarith
    exact_mod_cast this
  -- `B = xH + (ay - 1)(K_X + Δ)` is nef and big
  set t : ℤ := a₀ * y - 1 with ht
  set BQ : QDivisor X := (x : ℚ) • Divisor.toQDivisor H + (t : ℚ) • (Divisor.toQDivisor K + Δ)
    with hBQ
  have hBnb : BQ.IsNef k sX ∧ BQ.IsBig k sX :=
    MMP.Positivity.IsRationalityDatum.isNef_and_isBig_of_lt hd hr (x := (x : ℚ)) (t := (t : ℚ))
      (by exact_mod_cast (by omega : (0 : ℤ) < x)) (by exact_mod_cast (by omega : (0 : ℤ) ≤ t))
      (by
        rw [ht]
        push_cast at hxy' ⊢
        linarith)
  -- `aB` is the Cartier divisor `M = ax H + (ay - 1)R`, with pull-back `M'`
  set M : Divisor X := ((a₀ : ℤ) * x) • H + t • R with hM
  have hMc : M.IsCartier := (hHc.zsmul _).add (hRc.zsmul _)
  have hMQ : Divisor.toQDivisor M = (a₀ : ℤ) • BQ := by
    rw [hM, hBQ, map_add, map_zsmul, map_zsmul, hRQ]
    module
  set M' : Divisor Y := ((a₀ : ℤ) * x) • H' + t • B' with hM'
  have hM'p : M.IsPullback g (hgen M) M' :=
    (hH'.zsmul hHc _ (hgen _)).add (hHc.zsmul _) (hRc.zsmul _) (hgen _) (hB'.zsmul hRc t (hgen _))
  -- `N = x H' + y B' - K_Y + A` is the pull-back of `B`, hence nef and big
  set N : QDivisor Y := Divisor.toQDivisor (x • H' + y • B' - KY) + A with hN
  have hNM : Divisor.toQDivisor M' = (a₀ : ℤ) • N := by
    rw [hM', hN, map_add, map_sub, map_add, map_zsmul, map_zsmul, map_zsmul, map_zsmul, hB'Q, ht]
    module
  have hBQg : ∀ Z : irreducibleComponents Y, g (componentGenericPoint Y Z) ∉ BQ.supp := fun Z => by
    rw [← QDivisor.supp_eq_of_toQDivisor_eq (m := (a₀ : ℤ)) (by exact_mod_cast ha₀.ne') hMQ]
    exact hgen M Z
  obtain ⟨hnef, hbig⟩ := isNef_and_isBig_of_isPullback
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (g ≫ sX)
      hg.isBirationalMorphism)
    (MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm)
    (isPullback_of_toQDivisor_eq_smul hgen hBQg ha₀ hMc hMQ hM'p hNM) hBnb.1 hBnb.2
  -- Kawamata–Viehweg vanishing for `K_Y + ⌈N⌉ = x H' + y B' + ⌈A⌉`
  have hKV := subsingleton_derivedCohomologyOverField_divisorialSheaf_canonical_add_roundUp
    (g ≫ sX) hsm hKY (x • H' + y • B' - KY) A (isSNC_of_isCrepantBoundary_neg hP hg hYn hcrep)
    hnef hbig (i : ℤ) (by exact_mod_cast hi)
  rw [add_roundUp_toQDivisor_sub_add] at hKV
  exact (Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField k (g ≫ sX) _
    i).toEquiv.subsingleton

end MMP.Mori

end
