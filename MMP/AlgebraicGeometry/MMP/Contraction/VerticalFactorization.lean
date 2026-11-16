module
public import MMP.AlgebraicGeometry.MMP.Fourfold.Defs
public import MMP.AlgebraicGeometry.ProjectiveBundle.UniversalProperty
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor

/-!
# A vertical contraction factors the morphism

Let `U` be a projective variety over `k`, `h : U ⟶ Z` a projective morphism of `k`-schemes and
`R` an extremal ray of `NE̅(U)` all of whose curves are contracted by `h`. If `g : U ⟶ V` is the
contraction of `R`, then `h` factors through `g`: there is a morphism `h' : V ⟶ Z`, necessarily
unique, with `h = g ≫ h'`. Every curve in a fibre of `g` has class in `R`, hence is contracted
by `h`, so `h` is constant on the (connected) fibres of `g`, and `g_* 𝒪_U = 𝒪_V` gives the
factorization.

## Main results

* `MMP.Fourfold.existsUnique_comp_eq_of_isContractionOfRay`: the factorization `h = g ≫ h'`.

## Implementation notes

The factorization is stated with uniqueness, which holds because a contraction is surjective
with `𝒪_V ≅ g_* 𝒪_U`, hence an epimorphism of schemes. Normality of `U` is part of
`IsContractionOfRay`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

universe u

namespace MMP.Fourfold

open MMP.Mori

/-- The fibre of a continuous closed map through a closed point is closed. -/
private theorem isClosed_preimage_singleton_apply {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) (hfc : IsClosedMap f) {p : X}
    (hp : IsClosed ({p} : Set X)) : IsClosed (f ⁻¹' {f p}) :=
  (by simpa using hfc _ hp : IsClosed ({f p} : Set Y)).preimage hf

section Fibres

variable {k : Type u} [Field k] {U V Z : Scheme.{u}} {sU : U ⟶ Spec (.of k)} [IsProper sU]
  [IsLocallyNoetherian U] {g : U ⟶ V} {h : U ⟶ Z}
  (hcurve : ∀ C : ProperCurve sU, C.IsContractedBy g → C.IsContractedBy h)
  (hgc : IsClosedMap g) (hhc : IsClosedMap h)

include hcurve hhc in
/-- If `{y}⁻` lies in a fibre of `g`, then `h y = h p` for every closed point `p` of `{y}⁻`. -/
private theorem apply_eq_of_specializes {w : V} {y p : U}
    (hy : closure ({y} : Set U) ⊆ g ⁻¹' {w}) (hyp : y ⤳ p) (hp : IsClosed ({p} : Set U)) :
    h y = h p := by
  by_contra hne
  obtain ⟨c, hyc, hcp, hcZ, hc⟩ := exists_isProperCurve_of_specializes sU hyp hp
    (isClosed_preimage_singleton_apply h.continuous hhc hp) rfl hne
  have hcy : closure ({c} : Set U) ⊆ closure {y} :=
    closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hyc))
      isClosed_closure
  have hgC : (⟨c, hc⟩ : ProperCurve sU).IsContractedBy g := fun x hx => by
    have h1 := hy (hcy hx)
    have h2 := hy (hcy (subset_closure rfl))
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h1 h2
    rw [h1, h2]
  exact hcZ (hcurve _ hgC p (specializes_iff_mem_closure.mp hcp)).symm

include hcurve hhc in
/-- If `{y}⁻` lies in a fibre of `g`, then `h` is constant on `{y}⁻`. -/
private theorem apply_eq_of_mem_closure [CompactSpace U] {w : V} {y x : U}
    (hy : closure ({y} : Set U) ⊆ g ⁻¹' {w}) (hx : x ∈ closure ({y} : Set U)) : h x = h y := by
  obtain ⟨p, hp, hpc⟩ := (isClosed_closure (s := ({x} : Set U))).exists_closed_singleton
    ⟨x, subset_closure rfl⟩
  have hxy : closure ({x} : Set U) ⊆ closure {y} :=
    closure_minimal (Set.singleton_subset_iff.mpr hx) isClosed_closure
  rw [apply_eq_of_specializes hcurve hhc (hxy.trans hy) (specializes_iff_mem_closure.mpr hp) hpc,
    apply_eq_of_specializes hcurve hhc hy (specializes_iff_mem_closure.mpr (hxy hp)) hpc]

include hcurve hgc hhc in
/-- Two closed points in the same fibre of `g` have the same image under `h`, when the fibres of
`g` are connected. -/
private theorem apply_eq_of_isClosed [NoetherianSpace U]
    (hconn : ∀ v : V, _root_.IsPreconnected (g ⁻¹' {v})) {p q : U}
    (hp : IsClosed ({p} : Set U)) (hpq : g p = g q) : h p = h q := by
  classical
  set F := g ⁻¹' {g p}
  have hF : IsClosed F := isClosed_preimage_singleton_apply g.continuous hgc hp
  obtain ⟨S, hS, hFS⟩ := NoetherianSpace.exists_finset_irreducible ⟨F, hF⟩
  have hFS' : F = ⋃ t ∈ S, (t : Set U) := by
    have := congrArg (fun T : Closeds U => (T : Set U)) hFS
    rwa [Closeds.coe_finset_sup, Finset.sup_eq_iSup] at this
  have hgen : ∀ t ∈ S, ∃ y : U, closure {y} = (t : Set U) := fun t ht =>
    QuasiSober.sober (hS ⟨t, ht⟩) t.isClosed
  have : Nonempty U := ⟨p⟩
  choose! η hη using hgen
  have htF : ∀ t ∈ S, closure {η t} ⊆ F := fun t ht => by
    rw [hη t ht, hFS']
    exact Set.subset_biUnion_of_mem (u := fun t : Closeds U => (t : Set U)) ht
  let vals : Set Z := (fun t => h (η t)) '' (S : Set (Closeds U))
  have hvals : vals.Finite := S.finite_toSet.image _
  have hvalc : ∀ z ∈ vals, IsClosed ({z} : Set Z) := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨p', hp', hp'c⟩ := (isClosed_closure (s := ({η t} : Set U))).exists_closed_singleton
      ⟨η t, subset_closure rfl⟩
    have := hhc _ hp'c
    rwa [Set.image_singleton, apply_eq_of_mem_closure hcurve hhc (htF t ht) hp'] at this
  have hcover : F ⊆ h ⁻¹' {h p} ∪ h ⁻¹' (⋃ z ∈ vals \ {h p}, {z}) := by
    intro x hx
    rw [hFS'] at hx
    obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hx
    have hxη : h x = h (η t) :=
      apply_eq_of_mem_closure hcurve hhc (htF t ht) ((hη t ht).symm ▸ hxt)
    by_cases hxp : h x = h p
    · exact Or.inl hxp
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨h x, ⟨⟨t, ht, hxη.symm⟩, hxp⟩, rfl⟩)
  have hu : IsClosed (h ⁻¹' {h p}) := isClosed_preimage_singleton_apply h.continuous hhc hp
  have hv : IsClosed (h ⁻¹' (⋃ z ∈ vals \ {h p}, {z})) :=
    ((hvals.diff).isClosed_biUnion fun z hz => hvalc z hz.1).preimage h.continuous
  have hdisj : F ∩ (h ⁻¹' {h p} ∩ h ⁻¹' (⋃ z ∈ vals \ {h p}, {z})) = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion,
      Set.mem_diff, Set.mem_empty_iff_false, iff_false, not_and]
    rintro - hx ⟨z, ⟨-, hz⟩, rfl⟩
    exact hz hx
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp (hconn (g p)) _ _ hu hv hcover hdisj
    with hsub | hsub
  · exact (hsub (show q ∈ F from hpq.symm)).symm
  · have := hsub (show p ∈ F from rfl)
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_diff, Set.mem_singleton_iff] at this
    obtain ⟨z, ⟨-, hz⟩, rfl⟩ := this
    exact absurd rfl hz

include hcurve hgc hhc in
/-- `h` is constant on every fibre of `g`, when the fibres of `g` are connected. -/
private theorem apply_eq_of_apply_eq [NoetherianSpace U] [JacobsonSpace U]
    (hconn : ∀ v : V, _root_.IsPreconnected (g ⁻¹' {v})) {x x' : U} (hxx : g x = g x') :
    h x = h x' := by
  suffices H : ∀ x x' : U, g x = g x' → h x ⤳ h x' from
    (H x x' hxx).antisymm (H x' x hxx.symm) |>.eq
  intro x x' hxx
  by_contra hn
  have hC : IsClosed (h ⁻¹' closure {h x}) := isClosed_closure.preimage h.continuous
  have hx'O : x' ∈ (h ⁻¹' closure {h x})ᶜ := fun H => hn (specializes_iff_mem_closure.mpr H)
  have hx' : x' ∈ closure (closure {x'} ∩ closedPoints U) := by
    rw [JacobsonSpace.closure_inter_closedPoints isClosed_closure]
    exact subset_closure rfl
  obtain ⟨p, hpO, hpx', hpc⟩ := mem_closure_iff.mp hx' _ hC.isOpen_compl hx'O
  rw [mem_closedPoints_iff] at hpc
  have hgp : g p ∈ g '' closure {x} := by
    have hsub : closure {g x} ⊆ g '' closure {x} :=
      closure_minimal (Set.singleton_subset_iff.mpr ⟨x, subset_closure rfl, rfl⟩)
        (hgc _ isClosed_closure)
    refine hsub (specializes_iff_mem_closure.mp ?_)
    rw [hxx]
    exact (specializes_iff_mem_closure.mpr hpx').map g.continuous
  obtain ⟨q₀, hq₀, hgq₀⟩ := hgp
  obtain ⟨q, ⟨hqx, hgq⟩, hqc⟩ := (isClosed_closure.inter
    (isClosed_preimage_singleton_apply g.continuous hgc hpc) :
    IsClosed (closure {x} ∩ g ⁻¹' {g p})).exists_closed_singleton ⟨q₀, hq₀, hgq₀⟩
  have hpq : h q = h p := apply_eq_of_isClosed hcurve hgc hhc hconn hqc hgq
  have hqC : h q ∈ closure {h x} :=
    specializes_iff_mem_closure.mp ((specializes_iff_mem_closure.mpr hqx).map h.continuous)
  exact hpO (show h p ∈ closure {h x} from hpq ▸ hqC)

end Fibres

/-- **A vertical contraction factors the morphism.** If `U` is a projective variety, `R` an
extremal ray of `NE̅(U)` all of whose curves are contracted by a projective morphism
`h : U ⟶ Z` of `k`-schemes, and `g : U ⟶ V` is the contraction of `R`, then `h = g ≫ h'` for a
unique `h' : V ⟶ Z`. -/
@[mmp "lem_oai4_vertical_ray_b"]
public theorem existsUnique_comp_eq_of_isContractionOfRay {k : Type u} [Field k]
    {U V Z : Scheme.{u}} {sU : U ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} (hU : MMP.Mori.IsProjectiveVariety k sU)
    {h : U ⟶ Z} (hh : IsProjectiveMorphism h) (hZ : h ≫ sZ = sU)
    {R : Set (NumericalCurveClasses sU)}
    (hR : IsExtremalRay ℝ (closedConeOfCurves sU : Set (NumericalCurveClasses sU)) R)
    (hRh : ∀ C : ProperCurve sU, OneCycle.numericalClass sU (C.cycle ℝ) ∈ R → C.IsContractedBy h)
    {g : U ⟶ V} (hg : IsContractionOfRay sU sV R g) :
    ∃! h' : V ⟶ Z, g ≫ h' = h := by
  have : IsProper sU := isProper_of_isProjectiveMorphism _ hU.isProjective
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian sU
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace sU
  have : IsNoetherian U := (isNoetherian_iff U).mpr ⟨inferInstance, inferInstance⟩
  have : JacobsonSpace U := LocallyOfFiniteType.jacobsonSpace sU
  have : IsProper g := isProper_of_isProjectiveMorphism _ hg.isProjectiveMorphism
  have : IsProper h := isProper_of_isProjectiveMorphism _ hh
  have : IsIso g.c := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ g.c fun U => hg.isIso_app U.unop
  exact MMP.existsUnique_comp_eq_of_isIso_c g h fun x x' hxx =>
    apply_eq_of_apply_eq (fun C hC => hRh C ((hg.isContractedBy_iff C).mp hC))
    g.isClosedMap h.isClosedMap
    (fun v => (g.isConnected_preimage_singleton_of_isIso_app hg.isIso_app v).isPreconnected) hxx

end MMP.Fourfold

end
