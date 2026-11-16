module

public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# Zariski's lemma for divisors over a prime divisor of the base

Let `f : X ⟶ Z` be a proper surjective morphism of normal complex varieties with
`f_* 𝒪_X = 𝒪_Z`, and let `C ⊆ Z` be a prime divisor. Let `G` be a `ℚ`-Cartier `ℚ`-divisor on
`X` every component of which maps onto `C`. If `(G · Γ) ≥ 0` for every proper curve `Γ ⊆ X`
contracted by `f` to a point of a dense open subset `C° ⊆ C`, then over some open subset
`U ⊆ Z` meeting `C` the divisor `C|_U` is Cartier and `G|_{f⁻¹ U} = r · f^*(C|_U)` for some
`r ∈ ℚ`.

## Main results

* `MMP.Mori.exists_restrictOpen_eq_smul_of_isPullback_of_intersectionNumber_nonneg`: Zariski's
  lemma over a prime divisor of the base.

## Implementation notes

`f_* 𝒪_X = 𝒪_Z` is written `∀ U, IsIso (f.app U)`. A dense open subset of the irreducible
closed set `C` is the trace `C ∩ V` of an open `V ⊆ Z` meeting `C`. A component `E` of `G`
maps onto `C` when `f '' E = C`. The restriction of divisors to an open subscheme is
`MMP.Mori.DivisorWithCoeffs.restrictOpen`, the restriction of `f` over `U` is `f ∣_ U`, and the
pull-back of the Cartier divisor `C|_U` is characterised by `MMP.Mori.Divisor.IsPullback`.

The proof takes a local equation `φ` of `C` near its generic point and `F = div(f^*φ)`, shrinks
to an open `U` over which `F|_{f⁻¹U} = f^*(C|_U)`, puts `t = max gᵢ/mᵢ` over the components and
shows `D = tF - G` vanishes over `U`: otherwise, at a general closed point `c` of `C` (Chevalley's
theorem), the connected fibre `f⁻¹(c)` contains a proper curve `γ` meeting `Supp D` without lying
in it, with `(D · γ) > 0` and `(D · γ) = -(G · γ) ≤ 0`. The open `U` is cut out of `Z` by removing
the closures of the images of the components of `div(f^*φ)` not lying over `η_C`. The auxiliary
lemmas live in the namespace `Proof_lem_mmp_log_elliptic_vertical_divisor_zariski`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][FA], Chapter 15
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace Proof_lem_mmp_log_elliptic_vertical_divisor_zariski

section Topology

/-- **Constructible sets near a generic point.** A constructible set `s` either contains or misses
the trace on an irreducible closed set `P` of some open neighbourhood of the generic point `η` of
`P`, according as `η ∈ s` or not. -/
private theorem exists_isOpen_of_isConstructible {T : Type*} [TopologicalSpace T] {s : Set T}
    (hs : Topology.IsConstructible s) {P : Set T} {η : T} (hη : IsGenericPoint η P) :
    ∃ N : Set T, IsOpen N ∧ η ∈ N ∧ (η ∈ s → P ∩ N ⊆ s) ∧ (η ∉ s → P ∩ N ⊆ sᶜ) := by
  induction hs using Topology.IsConstructible.empty_union_induction with
  | open_retrocompact U hU _ =>
    by_cases h : η ∈ U
    · exact ⟨U, hU, h, fun _ x hx => hx.2, fun h' => absurd h h'⟩
    · refine ⟨Set.univ, isOpen_univ, trivial, fun h' => absurd h' h, fun _ x hx hxU => h ?_⟩
      exact (hη.mem_open_set_iff hU).mpr ⟨x, hx.1, hxU⟩
  | union s _ t _ ihs iht =>
    obtain ⟨N₁, hN₁, hη₁, hs₁, hs₁'⟩ := ihs
    obtain ⟨N₂, hN₂, hη₂, ht₂, ht₂'⟩ := iht
    refine ⟨N₁ ∩ N₂, hN₁.inter hN₂, ⟨hη₁, hη₂⟩, fun h x hx => ?_, fun h x hx => ?_⟩
    · rcases h with h | h
      · exact Or.inl (hs₁ h ⟨hx.1, hx.2.1⟩)
      · exact Or.inr (ht₂ h ⟨hx.1, hx.2.2⟩)
    · rintro (h' | h')
      · exact hs₁' (fun h'' => h (Or.inl h'')) ⟨hx.1, hx.2.1⟩ h'
      · exact ht₂' (fun h'' => h (Or.inr h'')) ⟨hx.1, hx.2.2⟩ h'
  | compl s _ ih =>
    obtain ⟨N, hN, hηN, h₁, h₂⟩ := ih
    exact ⟨N, hN, hηN, h₂, fun h => by simpa using h₁ (not_not.mp h)⟩

end Topology

section Generization

/-- In an integral scheme, a point strictly generalizing the generic point of a prime divisor is
the generic point of the scheme. -/
private theorem eq_genericPoint_of_specializes {Z : Scheme.{u}} [IsIntegral Z]
    (P : MMP.Mori.PrimeDivisor Z) {y : Z} (h : y ⤳ P.genericPoint) (hne : y ≠ P.genericPoint) :
    y = genericPoint Z := by
  by_contra hy
  have hηy : genericPoint Z ⤳ y := (genericPoint_spec Z).specializes trivial
  have h1 : P.genericPoint < y := lt_of_le_not_ge h fun h' => hne (Specializes.antisymm h h').eq
  have h2 : y < genericPoint Z := lt_of_le_not_ge hηy fun h' => hy (Specializes.antisymm h' hηy).eq
  have h3 := Order.coheight_add_one_le h1
  rw [P.coheight_genericPoint] at h3
  have h6 : (1 : ℕ∞) ≤ Order.coheight y := le_trans (by simp) (Order.coheight_add_one_le h2)
  have h5 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr) h3
  exact absurd h5 (by decide)

end Generization

section FibreCurves

/-- In a Noetherian quasi-sober space, a closed connected set `F` that meets a closed set `S`
without lying in it contains a point outside `S` specializing to a point of `S`. -/
private theorem exists_specializes_of_isConnected {Y : Type*} [TopologicalSpace Y]
    [TopologicalSpace.NoetherianSpace Y] [QuasiSober Y] {F S : Set Y} (hF : IsClosed F)
    (hFc : IsConnected F) (hS : IsClosed S) (hmeet : (F ∩ S).Nonempty) (hsub : ¬ F ⊆ S) :
    ∃ η ∈ F, η ∉ S ∧ ∃ s ∈ S, η ⤳ s := by
  set T := F \ S
  obtain ⟨s, hsT, hsS⟩ : (closure T ∩ S).Nonempty := by
    obtain ⟨y, hyF, hyS⟩ := Set.not_subset.mp hsub
    obtain ⟨w, -, hw⟩ := isPreconnected_closed_iff.mp hFc.isPreconnected _ _
      isClosed_closure hS (fun a ha => (em (a ∈ S)).symm.imp
        (fun haS => subset_closure (show a ∈ T from ⟨ha, haS⟩)) id)
      ⟨y, hyF, subset_closure (show y ∈ T from ⟨hyF, hyS⟩)⟩ hmeet
    exact ⟨w, hw⟩
  obtain ⟨Z, hZfin, hZcl, hZirr, hZeq⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible
      (isClosed_closure : IsClosed (closure T))
  have hsub' : closure T ⊆ ⋃₀ {t ∈ Z | (t ∩ T).Nonempty} := by
    refine closure_minimal (fun y hy => ?_) ?_
    · obtain ⟨z, hz, hyz⟩ : y ∈ ⋃₀ Z := hZeq ▸ subset_closure hy
      exact ⟨z, ⟨hz, y, hyz, hy⟩, hyz⟩
    · exact (hZfin.subset (Set.sep_subset _ _)).isClosed_sUnion fun t ht => hZcl t ht.1
  obtain ⟨z, ⟨hzZ, t, htz, htT⟩, hsz⟩ := hsub' hsT
  obtain ⟨ζ, hζ⟩ := QuasiSober.sober (hZirr z hzZ) (hZcl z hzZ)
  have hzT : z ⊆ closure T := hZeq ▸ Set.subset_sUnion_of_mem hzZ
  exact ⟨ζ, closure_minimal Set.sdiff_subset hF (hzT hζ.mem),
    fun hζS => htT.2 ((hζ.specializes htz).mem_closed hS hζS), s, hsS, hζ.specializes hsz⟩

/-- The fibre of a proper morphism `f` of `k`-schemes of finite type over a closed point is proper
over `k`. -/
private theorem isProper_fiberι_comp {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X) [IsProper f] (hX : IsNormalVariety k sX) (x : X)
    (hx : IsClosed ({x} : Set X)) : IsProper (f.fiberι x ≫ f ≫ sX) := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  have : LocallyOfFiniteType (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hx
  have : IsFinite (X.fromSpecResidueField x ≫ sX) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  have : IsProper (f.fiberToSpecResidueField x) :=
    inferInstanceAs (IsProper (Limits.pullback.snd f (X.fromSpecResidueField x)))
  rw [Scheme.Hom.fiber_fac_assoc]
  infer_instance

/-- An injective morphism `ι : W ⟶ Y` to a separated `k`-scheme of finite type maps a proper curve
of `W` onto a proper curve of `Y`. -/
private theorem isProperCurve_of_injective {k : Type u} [Field k] {W Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsSeparated sY] [LocallyOfFiniteType sY] (ι : W ⟶ Y)
    (hι : Function.Injective ι) (C : ProperCurve (ι ≫ sY)) : IsProperCurve sY (ι C.point) := by
  have hφsY : (C.ι ≫ ι) ≫ sY = C.ι ≫ ι ≫ sY := Category.assoc _ _ _
  have : AlgebraicGeometry.IsCurve k ((C.ι ≫ ι) ≫ sY) := hφsY ▸ C.isCurve
  have : IsProper ((C.ι ≫ ι) ≫ sY) := by
    rw [hφsY]
    infer_instance
  have hnc : ¬ ∃ z, Set.range (C.ι ≫ ι) = {z} := by
    rintro ⟨z, hz⟩
    have : Subsingleton C.scheme := ⟨fun a b => C.ι.isEmbedding.injective (hι (by
      have ha : (C.ι ≫ ι) a ∈ ({z} : Set Y) := hz ▸ ⟨a, rfl⟩
      have hb : (C.ι ≫ ι) b ∈ ({z} : Set Y) := hz ▸ ⟨b, rfl⟩
      simpa using ha.trans hb.symm))⟩
    have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
    rw [C.dim_eq] at h0
    exact absurd h0 (by decide)
  have hker := C.ker_comp ι
  constructor
  · have h1 := (MMP.Mori.isCurve_imageι_comp sY (C.ι ≫ ι) hnc).topologicalKrullDim_eq_one
    change topologicalKrullDim (C.ι ≫ ι).ker.subscheme = 1 at h1
    rwa [hker] at h1
  · have h1 : IsProper ((C.ι ≫ ι).imageι ≫ sY) := isProper_imageι_comp _ sY
    change IsProper ((C.ι ≫ ι).ker.subschemeι ≫ sY) at h1
    rwa [hker] at h1

/-- If the fibre of `f` over a closed point is connected and meets a closed set `S` without lying
in it, it contains a proper curve contracted by `f` that meets `S` without lying in it. -/
private theorem exists_properCurve_isContractedBy {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) (hX : IsNormalVariety k sX)
    (hY : IsNormalVariety k sY) (f : Y ⟶ X) (hf : f ≫ sX = sY) [IsProper f] (x : X)
    (hx : IsClosed ({x} : Set X)) (hconn : _root_.IsConnected (f.base ⁻¹' {x})) {S : Set Y}
    (hS : IsClosed S) (hmeet : (f.base ⁻¹' {x} ∩ S).Nonempty) (hsub : ¬ f.base ⁻¹' {x} ⊆ S) :
    ∃ C : ProperCurve sY, C.IsContractedBy f ∧ closure {C.point} ⊆ f.base ⁻¹' {x} ∧
      ¬ Set.range C.ι ⊆ S ∧ (Set.range C.ι ∩ S).Nonempty := by
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : QuasiCompact sY := hY.1.toQuasiCompact
  have : IsSeparated sY := hY.1.toIsSeparated
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsNoetherian Y := {}
  have hFcl : IsClosed (f.base ⁻¹' {x}) := hx.preimage f.continuous
  obtain ⟨η, hηF, hηS, s, hsS, hηs⟩ := exists_specializes_of_isConnected hFcl hconn hS hmeet hsub
  obtain ⟨p, hps, hpc⟩ := nonempty_inter_closedPoints
    ⟨s, (show s ∈ closure {s} from subset_closure rfl)⟩ isClosed_closure.isLocallyClosed
  have hηp : η ⤳ p := hηs.trans (specializes_iff_mem_closure.mpr hps)
  have hpS : p ∈ S := (specializes_iff_mem_closure.mpr hps).mem_closed hS hsS
  have hpF : p ∈ f.base ⁻¹' {x} := hηp.mem_closed hFcl hηF
  let ι := f.fiberι x
  let sF := ι ≫ sY
  have : IsProper sF := by simpa [sF, ι, hf] using isProper_fiberι_comp sX f hX x hx
  have : IsLocallyNoetherian (f.fiber x) := LocallyOfFiniteType.isLocallyNoetherian sF
  have hrι : Set.range ι = f.base ⁻¹' {x} := f.range_fiberι x
  obtain ⟨η', hη'⟩ : η ∈ Set.range ι := hrι ▸ hηF
  obtain ⟨p', hp'⟩ : p ∈ Set.range ι := hrι ▸ hpF
  have hemb : Topology.IsEmbedding ι := ι.isEmbedding
  have hη'p' : η' ⤳ p' := by rwa [← hemb.isInducing.specializes_iff, hη', hp']
  have hp'c : IsClosed ({p'} : Set (f.fiber x)) := by
    have : ({p'} : Set (f.fiber x)) = ι ⁻¹' {p} := by
      ext z
      simp [← hp', hemb.injective.eq_iff]
    rw [this]
    exact (mem_closedPoints_iff.mp hpc).preimage ι.continuous
  obtain ⟨y', -, hy'p', hy'S, hy'⟩ := MMP.Fourfold.exists_isProperCurve_of_specializes sF hη'p'
    hp'c (hS.preimage ι.continuous) (by simpa [hp'] using hpS)
    (by simpa [hη'] using hηS)
  let C' : ProperCurve sF := ⟨y', hy'⟩
  let C : ProperCurve sY := ⟨ι y', isProperCurve_of_injective sY ι hemb.injective C'⟩
  have hrC : Set.range C.ι = closure {ι y'} := C.range_ι
  have hclF : closure {ι y'} ⊆ f.base ⁻¹' {x} := by
    rw [← C'.range_comp ι rfl, ← hrι]
    rintro _ ⟨w, rfl⟩
    exact ⟨C'.ι w, by simp⟩
  have hCf : C.IsContractedBy f := fun z hz => by
    have h1 := hclF hz
    have h2 := hclF (subset_closure rfl : ι y' ∈ closure {ι y'})
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h1 h2
    exact h1.trans h2.symm
  refine ⟨C, hCf, hclF, ?_, p, ?_, hpS⟩
  · rw [hrC]
    exact fun h => hy'S (h (subset_closure rfl))
  · rw [hrC, ← hp']
    exact specializes_iff_mem_closure.mp (hy'p'.map ι.continuous)

end FibreCurves

section LocalDegree

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X]

/-- The image of a prime divisor of an open subscheme `V` has its generic point in `V`. -/
private theorem genericPoint_primeDivisorMap_ι_mem (V : X.Opens)
    (E : MMP.Mori.PrimeDivisor V.toScheme) :
    MMP.Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap V.ι E) ∈ V := by
  rw [show MMP.Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap V.ι E) =
    V.ι E.genericPoint from OpenWeilRestriction.genericPoint_primeDivisorMap V.ι E]
  exact E.genericPoint.2

/-- The generic point of a nonempty open subscheme of an integral scheme lies outside the support
of every divisor. -/
private theorem ι_componentGenericPoint_notMem_supp (D : Divisor X) (U : X.Opens) [Nonempty U]
    (Z : irreducibleComponents U.toScheme) : U.ι (componentGenericPoint U.toScheme Z) ∉ D.supp := by
  rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, genericPoint_eq_of_isOpenImmersion]
  exact MMP.Fourfold.genericPoint_notMem_supp D

/-- If every coefficient of `D'` on `U` equals the coefficient of `D` at the image prime divisor,
then `v ∈ Supp D'` iff `U.ι v ∈ Supp D`. -/
private theorem mem_supp_pullback_ι_iff (D : Divisor X) (U : X.Opens) [Nonempty U]
    (D' : Divisor U.toScheme)
    (hcoeff : ∀ E : MMP.Mori.PrimeDivisor U.toScheme,
      D'.coeff E = D.coeff (OpenWeilRestriction.primeDivisorMap U.ι E)) (v : U.toScheme) :
    v ∈ D'.supp ↔ U.ι v ∈ D.supp := by
  refine ⟨fun hv => ?_, fun hv => ?_⟩
  · obtain ⟨E, hE, hvE⟩ := DivisorWithCoeffs.mem_supp_iff.1 hv
    refine DivisorWithCoeffs.mem_supp_iff.2 ⟨OpenWeilRestriction.primeDivisorMap U.ι E,
      by rwa [← hcoeff], ?_⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hvE ⊢
    rw [OpenWeilRestriction.genericPoint_primeDivisorMap]
    exact specializes_iff_mem_closure.mp
      ((specializes_iff_mem_closure.mpr hvE).map U.ι.continuous)
  · obtain ⟨P, hP, hvP⟩ := DivisorWithCoeffs.mem_supp_iff.1 hv
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hvP
    have hsp : P.genericPoint ⤳ U.ι v := specializes_iff_mem_closure.mpr hvP
    have hPU : MMP.Mori.PrimeDivisor.genericPoint P ∈ U := hsp.mem_open U.isOpen v.2
    obtain ⟨E, rfl⟩ := MMP.Threefold.Resolution.exists_primeDivisorMap_eq U P hPU
    refine DivisorWithCoeffs.mem_supp_iff.2 ⟨E, by rwa [hcoeff], ?_⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    rw [show MMP.Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap U.ι E) =
      U.ι E.genericPoint from OpenWeilRestriction.genericPoint_primeDivisorMap U.ι E] at hsp
    exact specializes_iff_mem_closure.mp (U.ι.isOpenEmbedding.isInducing.specializes_iff.mp hsp)

/-- **Positivity of the degree, locally.** Let `D` be a Cartier divisor on a normal integral
scheme `X` quasi-compact over `k`, effective along the prime divisors meeting an open `U`, and
`C ⊆ U` a proper curve not contained in `Supp D` but meeting it. Then `deg_C 𝒪_X(D) > 0`. -/
private theorem degreeOn_pos_of_nonneg_of_closure_subset (D : Divisor X) (hD : D.IsCartier)
    (U : X.Opens) (hU : ∀ E : MMP.Mori.PrimeDivisor X, E.genericPoint ∈ U → 0 ≤ D.coeff E)
    (C : ProperCurve sX) (hCU : closure {C.point} ⊆ (U : Set X)) (hCD : C.point ∉ D.supp)
    (hmeet : (closure {C.point} ∩ (D.supp : Set X)).Nonempty) :
    0 < D.degreeOn k sX C.ι C.dim_le hD := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : AlgebraicGeometry.IsNoetherian X := {}
  have : Nonempty U := ⟨⟨C.point, hCU (subset_closure rfl)⟩⟩
  have : CompactSpace U := isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact _)
  have hB := ι_componentGenericPoint_notMem_supp D U
  set D' := Divisor.pullback (f := U.ι) D hD hB
  have hp := Divisor.isPullback_pullback (f := U.ι) hD hB
  have hD'c : D'.IsCartier := hp.isCartier hD
  have hcoeff : ∀ E : MMP.Mori.PrimeDivisor U.toScheme,
      D'.coeff E = D.coeff (OpenWeilRestriction.primeDivisorMap U.ι E) := fun E =>
    MMP.Positivity.coeff_eq_of_isPullback E _
      (OpenWeilRestriction.genericPoint_primeDivisorMap U.ι E).symm hD hp
  have hD'0 : 0 ≤ D' := fun E => by
    change 0 ≤ D'.coeff E
    rw [hcoeff E]
    exact hU _ (genericPoint_primeDivisorMap_ι_mem U E)
  have hsupp := mem_supp_pullback_ι_iff D U D' hcoeff
  obtain ⟨CV, hCV⟩ := MMP.Threefold.Resolution.exists_properCurve_of_closure_subset k U C hCU
  obtain ⟨e, he⟩ := MMP.Threefold.Resolution.exists_curveSubschemeAt_iso U.ι CV.point hCV (by
    rwa [Scheme.Opens.range_ι])
  have : IsProper ((CV.ι ≫ U.ι) ≫ sX) := by
    rw [Category.assoc]
    infer_instance
  have := hD.isInvertibleModule_divisorialSheaf
  have := hD'c.isInvertibleModule_divisorialSheaf
  have h1 := MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp k sX C.ι (CV.ι ≫ U.ι) C.dim_le
    CV.dim_le e.symm (by rw [Iso.symm_hom, Iso.inv_comp_eq]; exact he.symm) D.divisorialSheaf
  have h2 := MMP.Threefold.Resolution.degreeOn_comp k sX U.ι CV.ι CV.dim_le D.divisorialSheaf
  have h3 := MMP.Mori.degreeOn_eq_of_iso k (U.ι ≫ sX) CV.ι CV.dim_le
    (hp.divisorialSheafIso (hBc := hD)).symm
  have hdeg : D.degreeOn k sX C.ι C.dim_le hD = D'.degreeOn k (U.ι ≫ sX) CV.ι CV.dim_le hD'c :=
    h1.trans (h2.trans h3)
  rw [hdeg]
  have hrange : ∀ v : U.toScheme, v ∈ Set.range CV.ι ↔ U.ι v ∈ closure {C.point} := by
    intro v
    rw [CV.range_ι, ← hCV, ← specializes_iff_mem_closure, ← specializes_iff_mem_closure]
    exact U.ι.isOpenEmbedding.isInducing.specializes_iff.symm
  obtain ⟨c₀, hc₀⟩ := MMP.Threefold.Mori.exists_ι_eq_point CV.point
  have hne : ∃ c, CV.ι c ∉ D'.supp :=
    ⟨c₀, by rwa [show CV.ι c₀ = CV.point from hc₀, hsupp, hCV]⟩
  obtain ⟨hnn, hiff⟩ := MMP.Threefold.Mori.degreeOn_nonneg_and_eq_zero_iff (U.ι ≫ sX) CV.ι
    CV.dim_le D' hD'c hD'0 hne
  refine lt_of_le_of_ne hnn fun h0 => ?_
  obtain ⟨x, hxC, hxD⟩ := hmeet
  obtain ⟨v, rfl⟩ : x ∈ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    exact hCU hxC
  obtain ⟨c, hc⟩ := (hrange v).2 hxC
  exact hiff.1 h0.symm c (by rwa [hc, hsupp])

/-- **Positivity of the intersection number, locally.** Let `D` be a `ℚ`-Cartier `ℚ`-divisor on a
normal integral scheme `X` quasi-compact over `k`, effective along the prime divisors meeting an
open `U`, and `C ⊆ U` a proper curve not contained in `Supp D` but meeting it. Then
`(D · C) > 0`. -/
private theorem intersectionNumber_pos_of_nonneg_of_closure_subset (D : QDivisor X)
    (hD : D.IsQCartier) (U : X.Opens)
    (hU : ∀ E : MMP.Mori.PrimeDivisor X, E.genericPoint ∈ U → 0 ≤ D.coeff E)
    (C : ProperCurve sX) (hCU : closure {C.point} ⊆ (U : Set X)) (hCD : C.point ∉ D.supp)
    (hmeet : (closure {C.point} ∩ (D.supp : Set X)).Nonempty) :
    0 < D.intersectionNumber k sX C.ι C.dim_le hD := by
  obtain ⟨m, hm, E, hE, hEc⟩ := hD.exists_pos
  have hEsupp : E.supp = D.supp := QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hm.ne') hE
  have hE0 : ∀ P : MMP.Mori.PrimeDivisor X, P.genericPoint ∈ U → 0 ≤ E.coeff P := fun P hP => by
    have h1 := congrArg (fun A : QDivisor X => A P) hE
    simp only [Finsupp.smul_apply, zsmul_eq_mul] at h1
    have : (0 : ℚ) ≤ (E P : ℚ) := by
      rw [show ((E P : ℤ) : ℚ) = Divisor.toQDivisor E P from (Divisor.coeff_toQDivisor E P).symm,
        h1]
      exact mul_nonneg (by positivity) (hU P hP)
    exact_mod_cast this
  have hpos := degreeOn_pos_of_nonneg_of_closure_subset sX E hEc U hE0 C hCU (hEsupp ▸ hCD)
    (hEsupp ▸ hmeet)
  rw [QDivisor.intersectionNumber_eq_of_smul k sX C.ι C.dim_le D hD hm E hEc hE]
  exact div_pos (by exact_mod_cast hpos) (by exact_mod_cast hm)

/-- A principal divisor has intersection number `0` with every proper curve. -/
private theorem intersectionNumber_principalDivisor_eq_zero [CompactSpace X] (ψ : (RationalFunctions X)ˣ)
    (C : ProperCurve sX) :
    (Divisor.toQDivisor (principalDivisor ψ)).intersectionNumber k sX C.ι C.dim_le
      (QDivisor.isQCartier_toQDivisor (Divisor.isCartier_principalDivisor ψ)) = 0 := by
  have hc := Divisor.isCartier_principalDivisor ψ
  have := hc.isInvertibleModule_divisorialSheaf
  have := (Divisor.isCartier_zero (X := X)).isInvertibleModule_divisorialSheaf
  have h1 : (principalDivisor ψ).degreeOn k sX C.ι C.dim_le hc =
      (0 : Divisor X).degreeOn k sX C.ι C.dim_le Divisor.isCartier_zero :=
    degreeOn_eq_of_iso k sX C.ι C.dim_le
      (Divisor.linearlyEquivalent_principalDivisor_zero ψ).divisorialSheafIso
  rw [QDivisor.intersectionNumber_toQDivisor k sX C.ι C.dim_le _ hc, h1,
    Divisor.degreeOn_zero' k sX C.ι C.dim_le, Int.cast_zero]

end LocalDegree

section QCartier

/-- A rational multiple of a `ℚ`-Cartier `ℚ`-divisor is `ℚ`-Cartier. -/
private theorem isQCartier_smul {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : QDivisor X} (hD : D.IsQCartier) (q : ℚ) : (q • D).IsQCartier := by
  obtain ⟨m, hm, E, hE, hEc⟩ := hD
  refine ⟨m * q.den, mul_ne_zero hm (by exact_mod_cast q.den_pos.ne'), q.num • E, ?_,
    hEc.zsmul _⟩
  rw [map_zsmul, hE, smul_smul]
  refine Finsupp.ext fun P => ?_
  change ((q.num * m : ℤ) : ℚ) * D P = ((m * q.den : ℤ) : ℚ) * (q * D P)
  push_cast
  rw [← Rat.mul_den_eq_num q]
  ring

end QCartier

section Zariski

/-- A prime divisor `E` whose image is the prime divisor `C` maps its generic point to that of
`C`. -/
private theorem map_genericPoint_eq_of_image_support_eq {X Z : Scheme.{u}} (f : X ⟶ Z)
    {E : MMP.Mori.PrimeDivisor X} {C : MMP.Mori.PrimeDivisor Z}
    (h : f '' E.support = C.support) : f E.genericPoint = C.genericPoint := by
  obtain ⟨x, hx, hfx⟩ : C.genericPoint ∈ f '' E.support :=
    h ▸ MMP.Positivity.PrimeDivisor.genericPoint_mem_support' C
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hx
  have h2 : f E.genericPoint ∈ C.support :=
    h ▸ ⟨E.genericPoint, MMP.Positivity.PrimeDivisor.genericPoint_mem_support' E, rfl⟩
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h2
  exact ((hfx ▸ (specializes_iff_mem_closure.mpr hx).map f.continuous).antisymm
    (specializes_iff_mem_closure.mpr h2)).eq

/-- A proper morphism sending the generic point of a prime divisor `E` to that of `C` maps `E`
onto a set containing `C`. -/
private theorem support_subset_image_of_map_genericPoint_eq {X Z : Scheme.{u}} (f : X ⟶ Z)
    [IsProper f] {E : MMP.Mori.PrimeDivisor X} {C : MMP.Mori.PrimeDivisor Z}
    (h : f E.genericPoint = C.genericPoint) : (C.support : Set Z) ⊆ f '' (E.support : Set X) := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact closure_minimal (Set.singleton_subset_iff.mpr
    ⟨E.genericPoint, MMP.Positivity.PrimeDivisor.genericPoint_mem_support' E, h⟩)
    (f.isClosedMap _ E.idealSheaf.support.isClosed)

/-- Let `S` be a finite set of prime divisors containing every component of `D` meeting an open
`W`. The union `T` of the supports of the components of `D` in `S` is a closed subset of `Supp D`
containing `Supp D ∩ W`, and misses the generic point of every prime divisor that is not a
component of `D`. -/
private theorem exists_isClosed_supp_of_coeff_eq_zero {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] (D : QDivisor X) (W : X.Opens) (S : Finset (MMP.Mori.PrimeDivisor X))
    (hDS : ∀ E : MMP.Mori.PrimeDivisor X, E.genericPoint ∈ W → E ∉ S → D.coeff E = 0) :
    ∃ T : Set X, IsClosed T ∧ (∀ x ∈ T, x ∈ D.supp) ∧ (∀ x ∈ (W : Set X), x ∈ D.supp → x ∈ T) ∧
      (∀ E ∈ S, D.coeff E ≠ 0 → (E.support : Set X) ⊆ T) ∧
      ∀ E : MMP.Mori.PrimeDivisor X, D.coeff E = 0 → E.genericPoint ∉ T := by
  classical
  refine ⟨⋃ E ∈ S.filter (fun E => D.coeff E ≠ 0), E.support,
    Set.Finite.isClosed_biUnion (Finset.finite_toSet _) fun E _ => E.idealSheaf.support.isClosed,
    fun x hx => ?_, fun x hxW hx => ?_,
    fun E hE hE0 x hx => Set.mem_iUnion₂.mpr ⟨E, Finset.mem_filter.mpr ⟨hE, hE0⟩, hx⟩,
    fun E₀ hDE₀ h => ?_⟩
  · obtain ⟨E, hE, hxE⟩ := Set.mem_iUnion₂.mp hx
    exact DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, (Finset.mem_filter.mp hE).2, hxE⟩
  · obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
    have hsp : E.genericPoint ⤳ x := specializes_iff_mem_closure.mpr (by
      rwa [← AlgebraicGeometry.PrimeDivisor.support_eq_closure])
    have hES : E ∈ S := by_contra fun hES => hE (hDS E (hsp.mem_open W.isOpen hxW) hES)
    exact Set.mem_iUnion₂.mpr ⟨E, Finset.mem_filter.mpr ⟨hES, hE⟩, hxE⟩
  · obtain ⟨E, hE, hxE⟩ := Set.mem_iUnion₂.mp h
    have hsp : E.genericPoint ⤳ E₀.genericPoint := specializes_iff_mem_closure.mpr (by
      rwa [← AlgebraicGeometry.PrimeDivisor.support_eq_closure])
    obtain rfl := MMP.Positivity.PrimeDivisor.eq_of_genericPoint_specializes hsp
    exact (Finset.mem_filter.mp hE).2 hDE₀

/-- If `F` is numerically trivial on proper curves, then `((tF - G) · γ) = -(G · γ)`. -/
private theorem intersectionNumber_smul_sub_eq_neg {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    {F : Divisor X} (hFc : F.IsCartier)
    (hFΓ : ∀ Γ : ProperCurve sX, (Divisor.toQDivisor F).intersectionNumber k sX Γ.ι Γ.dim_le
      (QDivisor.isQCartier_toQDivisor hFc) = 0)
    {G : QDivisor X} (hG : G.IsQCartier) (t : ℚ)
    (hD : (t • Divisor.toQDivisor F - G).IsQCartier) (γ : ProperCurve sX) :
    (t • Divisor.toQDivisor F - G).intersectionNumber k sX γ.ι γ.dim_le hD =
      -G.intersectionNumber k sX γ.ι γ.dim_le hG := by
  have hFq := QDivisor.isQCartier_toQDivisor hFc
  have htFq : (t • Divisor.toQDivisor F).IsQCartier := isQCartier_smul hFq t
  have hnG : ((-1 : ℚ) • G).IsQCartier := isQCartier_smul hG (-1)
  have hDeq : t • Divisor.toQDivisor F - G = t • Divisor.toQDivisor F + (-1 : ℚ) • G := by
    rw [neg_one_smul, sub_eq_add_neg]
  rw [MMP.Fourfold.intersectionNumber_congr sX γ.ι γ.dim_le hD (htFq.add hnG) hDeq,
    QDivisor.intersectionNumber_add' k sX γ.ι γ.dim_le _ _ htFq hnG,
    MMP.Fourfold.intersectionNumber_smul sX γ.ι γ.dim_le _ hFq t htFq,
    MMP.Fourfold.intersectionNumber_smul sX γ.ι γ.dim_le _ hG (-1) hnG, hFΓ]
  ring

/-- **Rigidity over a prime divisor.** Let `f : X ⟶ Z` be a proper morphism of normal varieties
with `f_* 𝒪_X = 𝒪_Z`, `C ⊆ Z` a prime divisor, `U ∋ η_C` open, and `D` a `ℚ`-Cartier
`ℚ`-divisor, effective over `f⁻¹ U`, whose components over `f⁻¹ U` lie in a finite set `S` of
prime divisors over `η_C`, with `(D · Γ) ≤ 0` for every proper curve `Γ` contracted to a point of
a dense open of `C`. If some `E₀ ∈ S` is not a component of `D`, then `D` vanishes over `f⁻¹ U`. -/
private theorem coeff_eq_zero_of_intersectionNumber_nonpos {k : Type u} [Field k]
    {X Z : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) [QuasiCompact sX]
    [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Z] [IsNormal Z]
    (hX : IsNormalVariety k sX) (hZ : IsNormalVariety k sZ) (f : X ⟶ Z) (hf : f ≫ sZ = sX)
    [IsProper f] (hO : ∀ U : Z.Opens, IsIso (f.app U)) (C : MMP.Mori.PrimeDivisor Z)
    {U : Z.Opens} (hηU : C.genericPoint ∈ U) (S : Finset (MMP.Mori.PrimeDivisor X))
    (hS : ∀ E ∈ S, f E.genericPoint = C.genericPoint) (D : QDivisor X) (hD : D.IsQCartier)
    (hD0 : ∀ E : MMP.Mori.PrimeDivisor X, E.genericPoint ∈ f ⁻¹ᵁ U → 0 ≤ D.coeff E)
    (hDS : ∀ E : MMP.Mori.PrimeDivisor X, E.genericPoint ∈ f ⁻¹ᵁ U → E ∉ S → D.coeff E = 0)
    (hnef : ∃ V : Z.Opens, ((C.support : Set Z) ∩ V).Nonempty ∧
      ∀ Γ : ProperCurve sX, Γ.IsContractedBy f → f Γ.point ∈ (C.support : Set Z) ∩ V →
        D.intersectionNumber k sX Γ.ι Γ.dim_le hD ≤ 0)
    {E₀ : MMP.Mori.PrimeDivisor X} (hE₀S : E₀ ∈ S) (hDE₀ : D.coeff E₀ = 0)
    (E : MMP.Mori.PrimeDivisor X) (hE : E.genericPoint ∈ f ⁻¹ᵁ U) : D.coeff E = 0 := by
  have : IsIntegral X := hX.isIntegral
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  have : QuasiCompact sZ := hZ.1.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  have : AlgebraicGeometry.IsNoetherian X := {}
  have : AlgebraicGeometry.IsNoetherian Z := {}
  have : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace sZ
  set W : X.Opens := f ⁻¹ᵁ U
  by_contra hED
  have hES : E ∈ S := by_contra fun hES => hED (hDS E hE hES)
  obtain ⟨T, hT, hTD, hDT, hTS, hT₀⟩ := exists_isClosed_supp_of_coeff_eq_zero D W S hDS
  have hgenC : IsGenericPoint C.genericPoint (C.support : Set Z) :=
    (AlgebraicGeometry.PrimeDivisor.support_eq_closure C).symm
  have hO₀ : Topology.IsConstructible ((E₀.support : Set X) \ T) :=
    (Topology.isConstructible_compl.mp ((NoetherianSpace.isCompact _).isConstructible
      E₀.idealSheaf.support.isClosed.isOpen_compl)).inter
      ((NoetherianSpace.isCompact _).isConstructible hT.isOpen_compl)
  have hηO₀ : C.genericPoint ∈ f '' ((E₀.support : Set X) \ T) :=
    ⟨E₀.genericPoint, ⟨MMP.Positivity.PrimeDivisor.genericPoint_mem_support' E₀, hT₀ E₀ hDE₀⟩,
      hS E₀ hE₀S⟩
  obtain ⟨N, hN, hηN, hN₁, -⟩ :=
    exists_isOpen_of_isConstructible (f.isConstructible_image hO₀) hgenC
  obtain ⟨V, hVne, hVnef⟩ := hnef
  have hηV : C.genericPoint ∈ V := (hgenC.mem_open_set_iff V.isOpen).mpr hVne
  obtain ⟨c, ⟨hcC, hcN, hcV, hcU⟩, hcl⟩ := nonempty_inter_closedPoints
    (⟨C.genericPoint, MMP.Positivity.PrimeDivisor.genericPoint_mem_support' C, hηN, hηV, hηU⟩ :
      ((C.support : Set Z) ∩ (N ∩ ((V : Set Z) ∩ U))).Nonempty)
    (C.idealSheaf.support.isClosed.isLocallyClosed.inter
      (hN.inter (V.isOpen.inter U.isOpen)).isLocallyClosed)
  obtain ⟨x₁, ⟨-, hx₁T⟩, hfx₁⟩ := hN₁ hηO₀ ⟨hcC, hcN⟩
  obtain ⟨y₁, hy₁, hfy₁⟩ := support_subset_image_of_map_genericPoint_eq f (hS E hES) hcC
  obtain ⟨γ, hγc, hγF, hγT, hγmeet⟩ := exists_properCurve_isContractedBy sZ sX hZ hX f hf c
    (mem_closedPoints_iff.mp hcl) (f.isConnected_preimage_singleton_of_isIso_app hO c) hT
    ⟨y₁, hfy₁, hTS E hES hED hy₁⟩ fun h => hx₁T (h hfx₁)
  have hγW : closure {γ.point} ⊆ (W : Set X) := fun x hx => show f x ∈ U from hγF hx ▸ hcU
  have hγT' : γ.point ∉ T := fun h => hγT (by
    rw [γ.range_ι]
    exact closure_minimal (Set.singleton_subset_iff.mpr h) hT)
  have hpos := intersectionNumber_pos_of_nonneg_of_closure_subset sX D hD W hD0 γ hγW
    (fun h => hγT' (hDT _ (hγW (subset_closure rfl)) h))
    (by obtain ⟨x, hx, hxT⟩ := hγmeet; exact ⟨x, γ.range_ι ▸ hx, hTD x hxT⟩)
  have hDγ := hVnef γ hγc (by rw [hγF (subset_closure rfl)]; exact ⟨hcC, hcV⟩)
  linarith

/-- **Zariski's lemma over an open of the base.** Let `f : X ⟶ Z` be a proper morphism of normal
varieties with `f_* 𝒪_X = 𝒪_Z`, `C ⊆ Z` a prime divisor, `U ∋ η_C` open, and `F` a Cartier divisor,
numerically trivial on proper curves, whose components over `U` are exactly the prime divisors
lying over `η_C`, all with positive coefficient (for instance the principal divisor `div(f^*φ)` of
a local equation `φ` of `C`). If `G` is a `ℚ`-Cartier `ℚ`-divisor all of whose components lie over
`η_C`, with `(G · Γ) ≥ 0` for every proper curve `Γ` contracted to a point of a dense open of `C`,
then `G = tF` over `U` for some `t ∈ ℚ`. -/
private theorem exists_coeff_eq_mul_of_intersectionNumber_nonneg {k : Type u} [Field k]
    {X Z : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Z] [IsNormal Z] (hX : IsNormalVariety k sX)
    (hZ : IsNormalVariety k sZ) (f : X ⟶ Z) (hf : f ≫ sZ = sX) [IsProper f]
    (hO : ∀ U : Z.Opens, IsIso (f.app U)) (C : MMP.Mori.PrimeDivisor Z) {U : Z.Opens}
    (hηU : C.genericPoint ∈ U) (F : Divisor X) (hFc : F.IsCartier)
    (hFΓ : ∀ Γ : ProperCurve sX, (Divisor.toQDivisor F).intersectionNumber k sX Γ.ι Γ.dim_le
      (QDivisor.isQCartier_toQDivisor hFc) = 0)
    (hF0 : ∀ E : MMP.Mori.PrimeDivisor X, E.genericPoint ∈ f ⁻¹ᵁ U →
      f E.genericPoint ≠ C.genericPoint → F.coeff E = 0)
    (hFpos : ∀ E : MMP.Mori.PrimeDivisor X, f E.genericPoint = C.genericPoint → 0 < F.coeff E)
    (G : QDivisor X) (hG : G.IsQCartier)
    (hGC : ∀ E : MMP.Mori.PrimeDivisor X, G.coeff E ≠ 0 → f E.genericPoint = C.genericPoint)
    (hnef : ∃ V : Z.Opens, ((C.support : Set Z) ∩ V).Nonempty ∧
      ∀ Γ : ProperCurve sX, Γ.IsContractedBy f → f Γ.point ∈ (C.support : Set Z) ∩ V →
        0 ≤ G.intersectionNumber k sX Γ.ι Γ.dim_le hG) :
    ∃ t : ℚ, ∀ E : MMP.Mori.PrimeDivisor X, E.genericPoint ∈ f ⁻¹ᵁ U →
      G.coeff E = t * F.coeff E := by
  classical
  set W : X.Opens := f ⁻¹ᵁ U
  set S := F.support.filter (fun E => E.genericPoint ∈ W)
  have hmemS : ∀ E, E ∈ S ↔ E.genericPoint ∈ W ∧ f E.genericPoint = C.genericPoint := fun E => by
    rw [Finset.mem_filter, Finsupp.mem_support_iff]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2, by_contra fun h => h1 (hF0 E h2 h)⟩,
      fun ⟨h1, h2⟩ => ⟨(hFpos E h2).ne', h1⟩⟩
  have hG0 : ∀ E, E.genericPoint ∈ W → E ∉ S → G.coeff E = 0 := fun E hE hES =>
    by_contra fun h => hES ((hmemS E).mpr ⟨hE, hGC E h⟩)
  have hF0' : ∀ E, E.genericPoint ∈ W → E ∉ S → F.coeff E = 0 := fun E hE hES =>
    by_contra fun h => hES (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr h, hE⟩)
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · exact ⟨0, fun E hE => by rw [zero_mul, hG0 E hE (by simp [hSe])]⟩
  set t := S.sup' hSne (fun E => G.coeff E / (F.coeff E : ℚ)) with htdef
  refine ⟨t, ?_⟩
  have hFpos' : ∀ E ∈ S, (0 : ℚ) < F.coeff E := fun E hE => by
    exact_mod_cast hFpos E ((hmemS E).mp hE).2
  set D : QDivisor X := t • Divisor.toQDivisor F - G with hDdef
  have hDE : ∀ E, D.coeff E = t * F.coeff E - G.coeff E := fun E => by
    rw [hDdef, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul,
      Divisor.coeff_toQDivisor, smul_eq_mul]
  have hDS : ∀ E, E.genericPoint ∈ W → E ∉ S → D.coeff E = 0 := fun E hE hES => by
    simp [hDE, hF0' E hE hES, hG0 E hE hES]
  have hD0 : ∀ E, E.genericPoint ∈ W → 0 ≤ D.coeff E := fun E hE => by
    by_cases hES : E ∈ S
    · have h1 := Finset.le_sup' (fun E => G.coeff E / (F.coeff E : ℚ)) hES
      rw [div_le_iff₀ (hFpos' E hES)] at h1
      rw [hDE]
      linarith
    · rw [hDS E hE hES]
  obtain ⟨E₀, hE₀S, hE₀t⟩ := S.exists_mem_eq_sup' hSne (fun E => G.coeff E / (F.coeff E : ℚ))
  have hDE₀ : D.coeff E₀ = 0 := by
    rw [hDE, htdef, hE₀t, div_mul_cancel₀ _ (hFpos' E₀ hE₀S).ne', sub_self]
  suffices hall : ∀ E, E.genericPoint ∈ W → D.coeff E = 0 from fun E hE => by
    linarith [hDE E, hall E hE]
  obtain ⟨V, hVne, hVnef⟩ := hnef
  have hDq : D.IsQCartier := by
    rw [hDdef, sub_eq_add_neg, ← neg_one_smul ℚ G]
    exact (isQCartier_smul (QDivisor.isQCartier_toQDivisor hFc) t).add (isQCartier_smul hG (-1))
  exact coeff_eq_zero_of_intersectionNumber_nonpos sX sZ hX hZ f hf hO C hηU S
    (fun E hE => ((hmemS E).mp hE).2) D hDq hD0 hDS
    ⟨V, hVne, fun Γ hΓ hΓV => (intersectionNumber_smul_sub_eq_neg sX hFc hFΓ hG t hDq Γ).trans_le
      (neg_nonpos.mpr (hVnef Γ hΓ hΓV))⟩ hE₀S hDE₀

end Zariski

section PullbackComp

/-- **Pull-back of Cartier divisors along a composite**: `g^*(f^*L) = (f ∘ g)^*L`. -/
private theorem divisor_isPullback_comp {X Y Z : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian Z] [IsNormal Z]
    {f : Y ⟶ X} {g : Z ⟶ Y} {L : Divisor X} {L' : Divisor Y}
    {L'' : Divisor Z} {hB : ∀ W : irreducibleComponents Y, f (componentGenericPoint Y W) ∉ L.supp}
    {hB' : ∀ W : irreducibleComponents Z, g (componentGenericPoint Z W) ∉ L'.supp}
    (h : L.IsPullback f hB L') (h' : L'.IsPullback g hB' L'')
    (hB'' : ∀ W : irreducibleComponents Z, (g ≫ f) (componentGenericPoint Z W) ∉ L.supp) :
    L.IsPullback (g ≫ f) hB'' L'' := by
  intro U φ hφ E hE
  have hψ := h.isLocalEquation hφ
  rw [h' (f ⁻¹ᵁ U) _ hψ E hE]
  congr 1
  set z := componentGenericPoint Z E.component
  have hzU : f (g z) ∈ U := E.map_componentGenericPoint_mem (g ≫ f) hE
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hzU (hB'' _)
    (MMP.Fourfold.mem_irreducibleComponent_of_irreducibleSpace (pointComponent ((g ≫ f) z)) _)
  rw [pullbackComponent_eq hB'' hφ hzU _ a ha]
  set W := pointComponent (g z)
  have hspec : componentGenericPoint Y W ⤳ g z :=
    (isGenericPoint_componentGenericPoint Y W).specializes (mem_pointComponent _)
  have hWU : f (componentGenericPoint Y W) ∈ U :=
    (f.base.hom.map_specializes hspec).mem_open U.isOpen hzU
  have hb : (stalkToRationalFunctions Y (mem_pointComponent (g z))).hom
      (Units.map (f.stalkMap (g z)).hom.toMonoidHom a) =
      ((pullbackLocalEquation f hB hφ : (RationalFunctions Y)ˣ) : RationalFunctions Y) W := by
    have e1 := congrArg Units.val (pullbackLocalEquation_apply f hB hφ W hWU)
    refine Eq.trans ?_ e1.symm
    rw [pullbackComponent_eq hB hφ hWU
      (MMP.Fourfold.mem_irreducibleComponent_of_irreducibleSpace (pointComponent ((g ≫ f) z)) _)
      (Units.map (X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec)).hom.toMonoidHom a)
      ?_]
    · change (stalkToRationalFunctions Y _).hom ((f.stalkMap (g z)).hom a.val) =
        (f.stalkMap _).hom ((X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec)).hom
          a.val)
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, stalkToRationalFunctions,
        Scheme.Hom.stalkSpecializes_stalkMap]
    · change (X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec) ≫
        X.presheaf.stalkSpecializes _).hom a.val = _
      rw [TopCat.Presheaf.stalkSpecializes_comp]
      exact ha
  rw [pullbackComponent_eq hB' hψ _ (mem_pointComponent (g z)) _ hb]
  ext
  change _ = ((g ≫ f).stalkMap z).hom a.val
  rw [Scheme.Hom.stalkMap_comp]
  rfl

/-- A pull-back `f^*B` has no component lying over the complement of `Supp B`. -/
private theorem coeff_eq_zero_of_isPullback_of_notMem_supp {X Z : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Z] [IsNormal Z] {f : X ⟶ Z}
    {B : Divisor Z} {hB : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ B.supp}
    {F : Divisor X} (h : B.IsPullback f hB F) (E : MMP.Mori.PrimeDivisor X)
    (hE : f E.genericPoint ∉ B.supp) : F.coeff E = 0 := by
  set Wc : Z.Opens := ⟨(B.supp : Set Z)ᶜ, B.supp.isClosed.isOpen_compl⟩
  have hloc : B.IsLocalEquation Wc 1 := by
    rintro P ⟨x, hxP, hxW⟩
    rw [PrimeDivisor.ord_one]
    by_contra hne
    exact hxW (DivisorWithCoeffs.support_subset_supp hne hxP)
  have hEW : (E.support ∩ f ⁻¹ᵁ Wc).Nonempty :=
    (E.genericPoint_mem_iff _).mp (show f E.genericPoint ∈ Wc from hE)
  rw [h Wc 1 hloc E hEW, pullbackComponent_eq hB hloc _ (mem_pointComponent _) 1 (by simp),
    map_one, PrimeDivisor.ordUnit_one]

/-- A pull-back `f^*B` is positive along every prime divisor lying over the generic point of a
prime divisor `C` with which `B` agrees near `η_C`. -/
private theorem coeff_pos_of_isPullback {X Z : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z] {f : X ⟶ Z}
    (C : MMP.Mori.PrimeDivisor Z) {U₀ : Z.Opens}
    (hηU₀ : C.genericPoint ∈ U₀) {B : Divisor Z}
    (hagree : ∀ P : MMP.Mori.PrimeDivisor Z, (P.support ∩ U₀).Nonempty →
      B.coeff P = DivisorWithCoeffs.coeff (Finsupp.single C 1 : Divisor Z) P)
    {hB : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ B.supp}
    {F : Divisor X} (h : B.IsPullback f hB F) (E : MMP.Mori.PrimeDivisor X)
    (hE : f E.genericPoint = C.genericPoint) : 0 < F.coeff E := by
  obtain ⟨U₁, ϖ₁, φ₁, hyU₁, hϖ₁m, hφ₁W, hφ₁⟩ :=
    MMP.Fourfold.exists_isLocalEquation_single_of_eq C (f E.genericPoint) hE.symm
  have hloc : B.IsLocalEquation (U₁ ⊓ U₀) φ₁ := fun P hP => by
    rw [hagree P (hP.mono (Set.inter_subset_inter_right _ fun x hx => hx.2)),
      hφ₁ P (hP.mono (Set.inter_subset_inter_right _ fun x hx => hx.1))]
  have hyU : f E.genericPoint ∈ U₁ ⊓ U₀ := ⟨hyU₁, hE ▸ hηU₀⟩
  have hEU : (E.support ∩ f ⁻¹ᵁ (U₁ ⊓ U₀)).Nonempty := (E.genericPoint_mem_iff _).mp hyU
  rw [h _ φ₁ hloc E hEU]
  have hWc := mem_pointComponent (f E.genericPoint)
  have h1 := MMP.Fourfold.pullbackComponent_val_eq_stalkMap f hB hloc hWc ϖ₁ (hφ₁W _ hWc)
    E.genericPoint_mem_component (E.map_componentGenericPoint_mem f hEU)
  exact MMP.Fourfold.PrimeDivisor.ordUnit_pos_of_mem_maximalIdeal E
    (map_nonunit (f.stalkMap E.genericPoint).hom ϖ₁ hϖ₁m) h1.symm

/-- If `f^*B` has no component over the complement of `Supp B`, then, near the generic point of
a prime divisor `C`, every component of `f^*B` lies over `η_C`. -/
private theorem exists_genericPoint_mem_coeff_eq_zero {X Z : Scheme.{u}} [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [IsLocallyNoetherian X] [IsNormal X] (f : X ⟶ Z)
    (C : MMP.Mori.PrimeDivisor Z) (B : Divisor Z) (F : Divisor X)
    (hF : ∀ E : MMP.Mori.PrimeDivisor X, f E.genericPoint ∉ B.supp → F.coeff E = 0) :
    ∃ V : Z.Opens, C.genericPoint ∈ V ∧ ∀ E : MMP.Mori.PrimeDivisor X, f E.genericPoint ∈ V →
      f E.genericPoint ≠ C.genericPoint → F.coeff E = 0 := by
  classical
  set Bad : Set Z := ⋃ E ∈ F.support.filter (fun E => f E.genericPoint ≠ C.genericPoint),
    closure {f E.genericPoint}
  have hBad : IsClosed Bad :=
    Set.Finite.isClosed_biUnion (Finset.finite_toSet _) fun _ _ => isClosed_closure
  have hηBad : C.genericPoint ∉ Bad := by
    intro h
    obtain ⟨E, hE, hη⟩ := Set.mem_iUnion₂.mp h
    obtain ⟨hEs, hne⟩ := Finset.mem_filter.mp hE
    have hgen := eq_genericPoint_of_specializes C (specializes_iff_mem_closure.mpr hη) hne
    have hsupp : f E.genericPoint ∈ B.supp :=
      by_contra fun h' => Finsupp.mem_support_iff.mp hEs (hF E h')
    rw [hgen] at hsupp
    exact MMP.Fourfold.genericPoint_notMem_supp B hsupp
  exact ⟨⟨Badᶜ, hBad.isOpen_compl⟩, hηBad, fun E hEV hfE => by_contra fun hne =>
    (show f E.genericPoint ∉ Bad from hEV) (Set.mem_iUnion₂.mpr
      ⟨E, Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hne, hfE⟩, subset_closure rfl⟩)⟩

/-- **Restriction of a pull-back.** Let `B` be a Cartier divisor on `Z` agreeing with the prime
divisor `C` over an open `U`, and `F = f^*B`. Then `C|_U` is Cartier, and its pull-back along
`f ∣_ U` is `F|_{f⁻¹ U}`. -/
private theorem exists_isPullback_restrictOpen {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Z] [IsNormal Z]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Z] (f : X ⟶ Z)
    (hgen : f (genericPoint X) = genericPoint Z) (C : MMP.Mori.PrimeDivisor Z) (U : Z.Opens)
    [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] {B : Divisor Z} (hBc : B.IsCartier)
    (hagree : ∀ P : MMP.Mori.PrimeDivisor Z, (P.support ∩ U).Nonempty →
      B.coeff P = DivisorWithCoeffs.coeff (Finsupp.single C 1 : Divisor Z) P)
    {hB : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ B.supp}
    {F : Divisor X} (hFc : F.IsCartier) (h₁ : B.IsPullback f hB F) :
    Divisor.IsCartier (DivisorWithCoeffs.restrictOpen U (Finsupp.single C 1 : Divisor Z)) ∧
      ∃ (hB' : ∀ W : irreducibleComponents (f ⁻¹ᵁ U).toScheme,
          (f ∣_ U) (componentGenericPoint _ W) ∉ DivisorWithCoeffs.supp
            (DivisorWithCoeffs.restrictOpen U (Finsupp.single C 1 : Divisor Z)))
        (F' : Divisor (f ⁻¹ᵁ U).toScheme),
        Divisor.IsPullback (f ∣_ U)
            (DivisorWithCoeffs.restrictOpen U (Finsupp.single C 1 : Divisor Z)) hB' F' ∧
          ∀ E' : MMP.Mori.PrimeDivisor (f ⁻¹ᵁ U).toScheme,
            F'.coeff E' = F.coeff (OpenWeilRestriction.primeDivisorMap (f ⁻¹ᵁ U).ι E') := by
  set W : X.Opens := f ⁻¹ᵁ U
  have : CompactSpace U := isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact _)
  have : CompactSpace W := isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact _)
  have hgW : ∀ Z' : irreducibleComponents W.toScheme,
      W.ι (componentGenericPoint W.toScheme Z') = genericPoint X := fun Z' => by
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, genericPoint_eq_of_isOpenImmersion]
  have hBU := ι_componentGenericPoint_notMem_supp B U
  set BU := Divisor.pullback (f := U.ι) B hBc hBU
  have h₃ : B.IsPullback U.ι hBU BU := Divisor.isPullback_pullback (f := U.ι) hBc hBU
  have hBUeq : BU = DivisorWithCoeffs.restrictOpen U (Finsupp.single C 1 : Divisor Z) := by
    ext P'
    have h := MMP.Positivity.coeff_eq_of_isPullback P' (OpenWeilRestriction.primeDivisorMap U.ι P')
      (OpenWeilRestriction.genericPoint_primeDivisorMap U.ι P').symm hBc h₃
    change BU.coeff P' = DivisorWithCoeffs.coeff _ P'
    rw [DivisorWithCoeffs.coeff_restrictOpen, h,
      hagree _ ((PrimeDivisor.genericPoint_mem_iff _ _).mp
        (genericPoint_primeDivisorMap_ι_mem U P'))]
  have hBUc : BU.IsCartier := h₃.isCartier hBc
  have hBW := ι_componentGenericPoint_notMem_supp F W
  set FW := Divisor.pullback (f := W.ι) F hFc hBW
  have h₂ : F.IsPullback W.ι hBW FW := Divisor.isPullback_pullback (f := W.ι) hFc hBW
  set g := f ∣_ U
  have hgι : g ≫ U.ι = W.ι ≫ f := morphismRestrict_ι f U
  have hgg : ∀ Z' : irreducibleComponents W.toScheme,
      g (componentGenericPoint W.toScheme Z') = genericPoint U.toScheme := fun Z' => by
    apply U.ι.isOpenEmbedding.injective
    have e := congrArg (fun h : W.toScheme ⟶ Z => h (componentGenericPoint W.toScheme Z')) hgι
    simp only [Scheme.Hom.comp_apply] at e
    rw [e, hgW, hgen, genericPoint_eq_of_isOpenImmersion]
  have hBg : ∀ Z' : irreducibleComponents W.toScheme,
      g (componentGenericPoint W.toScheme Z') ∉ BU.supp := fun Z' =>
    (hgg Z').symm ▸ MMP.Fourfold.genericPoint_notMem_supp BU
  set F' := Divisor.pullback (f := g) BU hBUc hBg
  have h₄ : BU.IsPullback g hBg F' := Divisor.isPullback_pullback (f := g) hBUc hBg
  have hB'' : ∀ Z' : irreducibleComponents W.toScheme,
      (W.ι ≫ f) (componentGenericPoint W.toScheme Z') ∉ B.supp := fun Z' => by
    simpa only [Scheme.Hom.comp_apply, hgW, hgen] using MMP.Fourfold.genericPoint_notMem_supp B
  have c1 : ∀ (h : W.toScheme ⟶ Z) (hh : g ≫ U.ι = h)
      (hBh : ∀ Z' : irreducibleComponents W.toScheme,
        h (componentGenericPoint W.toScheme Z') ∉ B.supp), B.IsPullback h hBh F' := by
    rintro h rfl hBh
    exact divisor_isPullback_comp h₃ h₄ hBh
  refine ⟨hBUeq ▸ hBUc, fun Z' => by rw [← hBUeq]; exact hBg Z', F',
    Divisor.IsPullback.of_eq hBUeq h₄, fun E' => ?_⟩
  rw [(c1 _ hgι hB'').eq hBc (divisor_isPullback_comp h₁ h₂ hB'')]
  exact MMP.Positivity.coeff_eq_of_isPullback E' (OpenWeilRestriction.primeDivisorMap W.ι E')
    (OpenWeilRestriction.genericPoint_primeDivisorMap W.ι E').symm hFc h₂

end PullbackComp

end Proof_lem_mmp_log_elliptic_vertical_divisor_zariski

namespace MMP.Mori

open Proof_lem_mmp_log_elliptic_vertical_divisor_zariski

/-- **Zariski's lemma over a prime divisor.** Let `f : X ⟶ Z` be a proper surjective morphism of
normal complex varieties with `f_* 𝒪_X = 𝒪_Z`, `C` a prime divisor of `Z`, and `G` a
`ℚ`-Cartier `ℚ`-divisor on `X` all of whose components map onto `C`. Suppose `(G · Γ) ≥ 0` for
every proper curve `Γ` contracted by `f` to a point of `C ∩ V`, for an open `V` meeting `C`.
Then there are an open `U ⊆ Z` meeting `C` on which `C` is Cartier, and `r : ℚ`, with
`G|_{f⁻¹ U} = r · f^*(C|_U)`. -/
@[mmp "lem_mmp_log_elliptic_vertical_divisor_zariski"]
public theorem exists_restrictOpen_eq_smul_of_isPullback_of_intersectionNumber_nonneg
    {X Z : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ))
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Z] [IsNormal Z]
    (hX : IsNormalVariety ℂ sX) (hZ : IsNormalVariety ℂ sZ)
    (f : X ⟶ Z) (hf : f ≫ sZ = sX) [IsProper f] [Surjective f]
    (hO : ∀ U : Z.Opens, IsIso (f.app U))
    (C : PrimeDivisor Z) (G : QDivisor X) (hG : G.IsQCartier)
    (hGC : ∀ E : PrimeDivisor X, G.coeff E ≠ 0 → f '' E.support = C.support)
    (hnef : ∃ V : Z.Opens, ((C.support : Set Z) ∩ V).Nonempty ∧
      ∀ Γ : ProperCurve sX, Γ.IsContractedBy f → f Γ.point ∈ (C.support : Set Z) ∩ V →
        0 ≤ G.intersectionNumber ℂ sX Γ.ι Γ.dim_le hG) :
    ∃ U : Z.Opens, ((C.support : Set Z) ∩ U).Nonempty ∧
      Divisor.IsCartier (DivisorWithCoeffs.restrictOpen U (Finsupp.single C 1 : Divisor Z)) ∧
      ∃ (r : ℚ) (hB : ∀ W : irreducibleComponents (f ⁻¹ᵁ U).toScheme,
          (f ∣_ U) (componentGenericPoint _ W) ∉ DivisorWithCoeffs.supp
            (DivisorWithCoeffs.restrictOpen U (Finsupp.single C 1 : Divisor Z)))
        (F : Divisor (f ⁻¹ᵁ U).toScheme),
        Divisor.IsPullback (f ∣_ U)
            (DivisorWithCoeffs.restrictOpen U (Finsupp.single C 1 : Divisor Z)) hB F ∧
          G.restrictOpen (f ⁻¹ᵁ U) = r • Divisor.toQDivisor F := by
  classical
  have : IsIntegral X := hX.isIntegral
  have : IsIntegral Z := hZ.isIntegral
  have : QuasiCompact sZ := hZ.1.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  have : AlgebraicGeometry.IsNoetherian X := {}
  have : AlgebraicGeometry.IsNoetherian Z := {}
  have hgen : f (genericPoint X) = genericPoint Z := map_genericPoint_of_isDominant f
  obtain ⟨U₀, ϖ, φ, hηU₀, hϖm, hφW, hφ⟩ :=
    MMP.Fourfold.exists_isLocalEquation_single_of_eq C C.genericPoint rfl
  set B₀ : Divisor Z := principalDivisor φ
  have hB₀c : B₀.IsCartier := Divisor.isCartier_principalDivisor φ
  have hB₀ : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ B₀.supp := fun W => by
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, hgen]
    exact MMP.Fourfold.genericPoint_notMem_supp B₀
  set ψ := pullbackRationalFunction f φ hB₀
  set Fx : Divisor X := principalDivisor ψ
  have hFxc : Fx.IsCartier := Divisor.isCartier_principalDivisor ψ
  have h₁ : B₀.IsPullback f hB₀ Fx := Divisor.isPullback_principalDivisor φ hB₀
  have hagree : ∀ P : MMP.Mori.PrimeDivisor Z, (P.support ∩ U₀).Nonempty →
      B₀.coeff P = DivisorWithCoeffs.coeff (Finsupp.single C 1 : Divisor Z) P := fun P hP => by
    rw [coeff_principalDivisor, hφ P hP]
  obtain ⟨V, hηV, hV⟩ := exists_genericPoint_mem_coeff_eq_zero f C B₀ Fx
    (coeff_eq_zero_of_isPullback_of_notMem_supp h₁)
  set U : Z.Opens := U₀ ⊓ V
  have hηU : C.genericPoint ∈ U := ⟨hηU₀, hηV⟩
  obtain ⟨t, ht⟩ := exists_coeff_eq_mul_of_intersectionNumber_nonneg sX sZ hX hZ f hf hO C hηU Fx
    hFxc (intersectionNumber_principalDivisor_eq_zero sX ψ)
    (fun E hEW => hV E (show f E.genericPoint ∈ U from hEW).2)
    (coeff_pos_of_isPullback C hηU₀ hagree h₁) G hG
    (fun E hE => map_genericPoint_eq_of_image_support_eq f (hGC E hE)) hnef
  obtain ⟨x₀, hx₀⟩ := f.surjective C.genericPoint
  have : Nonempty U := ⟨⟨_, hηU⟩⟩
  have : Nonempty (f ⁻¹ᵁ U) := ⟨⟨x₀, show f x₀ ∈ U from hx₀ ▸ hηU⟩⟩
  obtain ⟨hCart, hB, F', hF', hF'coeff⟩ := exists_isPullback_restrictOpen f hgen C U hB₀c
    (fun P hP => hagree P (hP.mono (Set.inter_subset_inter_right _ fun x hx => hx.1))) hFxc h₁
  refine ⟨U, ⟨C.genericPoint, MMP.Positivity.PrimeDivisor.genericPoint_mem_support' C, hηU⟩,
    hCart, t, hB, F', hF', ?_⟩
  ext E'
  have hE' := ht _ (genericPoint_primeDivisorMap_ι_mem (f ⁻¹ᵁ U) E')
  change DivisorWithCoeffs.coeff (G.restrictOpen (f ⁻¹ᵁ U)) E' =
    DivisorWithCoeffs.coeff (t • Divisor.toQDivisor F') E'
  rw [DivisorWithCoeffs.coeff_restrictOpen, DivisorWithCoeffs.coeff_smul,
    Divisor.coeff_toQDivisor, hF'coeff, hE', smul_eq_mul]

end MMP.Mori

end
