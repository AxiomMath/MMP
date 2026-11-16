module
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.ProjectiveBundle.UniversalProperty

/-!
# A projective contraction factors any morphism constant on its contracted curves

Let `q : X ⟶ V` be a projective surjective morphism of projective varieties over a field `k`
whose structure-sheaf map `q.c : 𝒪_V ⟶ q_* 𝒪_X` is an isomorphism. If a morphism `f : X ⟶ S`
to a projective `k`-variety contracts every proper curve of `X` that `q` contracts, then `f`
factors uniquely through `q`: there is a unique `h : V ⟶ S` with `q ≫ h = f`.

The fibres of `q` are connected, so `f` is constant on the closed points of a fibre (a
non-constant image would be witnessed by a proper curve inside the fibre); since `X` is
Jacobson this extends to all points, and the rigidity factorization
`MMP.existsUnique_comp_eq_of_isIso_c` gives the unique `h`.

## Main results

* `MMP.Mori.existsUnique_comp_eq_of_isContractedBy`: the factorization `q ≫ h = f`, unique.

## Implementation notes

The canonical isomorphism `𝒪_V ≃ q_* 𝒪_X` is Mathlib's structure-sheaf map `q.c` of the
morphism `q`, required to be an isomorphism. Composition is diagrammatic, so `f = h ∘ q` reads
`q ≫ h = f`. The source works over `ℂ`; the statement is made over an arbitrary field `k`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

universe u

namespace MMP.Mori

section Fibres

open MMP.Fourfold

variable {k : Type u} [Field k] {U V Z : Scheme.{u}} {sU : U ⟶ Spec (.of k)} [IsProper sU]
  [IsLocallyNoetherian U] {g : U ⟶ V} {h : U ⟶ Z}
  (hcurve : ∀ C : ProperCurve sU, C.IsContractedBy g → C.IsContractedBy h)
  (hgc : IsClosedMap g) (hhc : IsClosedMap h)

include hcurve hhc in
/-- If `{y}⁻` lies in a fibre of `g`, then `h y = h p` for every closed point `p` of `{y}⁻`:
otherwise a proper curve through `p` inside `{y}⁻` would leave the closed set `h⁻¹(h p)`. -/
private theorem apply_eq_of_specializes {w : V} {y p : U}
    (hy : closure ({y} : Set U) ⊆ g ⁻¹' {w}) (hyp : y ⤳ p) (hp : IsClosed ({p} : Set U)) :
    h y = h p := by
  by_contra hne
  obtain ⟨c, hyc, hcp, hcZ, hc⟩ := exists_isProperCurve_of_specializes sU hyp hp
    ((Set.image_singleton ▸ hhc _ hp : IsClosed {h p}).preimage h.continuous) rfl hne
  have hcy : closure ({c} : Set U) ⊆ closure {y} := specializes_iff_closure_subset.mp hyc
  refine hcZ (hcurve ⟨c, hc⟩ (fun x hx => ?_) p hcp.mem_closure).symm
  rw [hy (hcy hx), hy (hcy (subset_closure rfl))]

include hcurve hhc in
/-- If `{y}⁻` lies in a fibre of `g`, then `h` is constant on `{y}⁻`. -/
private theorem apply_eq_of_mem_closure [CompactSpace U] {w : V} {y x : U}
    (hy : closure ({y} : Set U) ⊆ g ⁻¹' {w}) (hx : x ∈ closure ({y} : Set U)) : h x = h y := by
  obtain ⟨p, hp, hpc⟩ :=
    (isClosed_closure (s := ({x} : Set U))).exists_closed_singleton ⟨x, subset_closure rfl⟩
  have hxy : closure ({x} : Set U) ⊆ closure {y} :=
    closure_minimal (Set.singleton_subset_iff.mpr hx) isClosed_closure
  rw [apply_eq_of_specializes hcurve hhc (hxy.trans hy) (specializes_iff_mem_closure.mpr hp) hpc,
    apply_eq_of_specializes hcurve hhc hy (specializes_iff_mem_closure.mpr (hxy hp)) hpc]

include hcurve hhc in
/-- If `{y}⁻` lies in a fibre of `g`, then `h y` is a closed point. -/
private theorem isClosed_singleton_apply [CompactSpace U] {w : V} {y : U}
    (hy : closure ({y} : Set U) ⊆ g ⁻¹' {w}) : IsClosed ({h y} : Set Z) := by
  obtain ⟨p, hp, hpc⟩ :=
    (isClosed_closure (s := ({y} : Set U))).exists_closed_singleton ⟨y, subset_closure rfl⟩
  rw [← apply_eq_of_mem_closure hcurve hhc hy hp]
  exact Set.image_singleton ▸ hhc _ hpc

include hcurve hgc hhc in
/-- Two closed points in the same fibre `F` of `g` have the same image under `h`, when the fibres
of `g` are connected: `h '' F` is a finite set of closed points (one value on each of the finitely
many irreducible components of `F`), hence discrete, and it is preconnected. -/
private theorem apply_eq_of_isClosed [NoetherianSpace U]
    (hconn : ∀ v : V, _root_.IsPreconnected (g ⁻¹' {v})) {p q : U}
    (hp : IsClosed ({p} : Set U)) (hpq : g p = g q) : h p = h q := by
  set F := g ⁻¹' {g p}
  have hF : IsClosed F := (Set.image_singleton ▸ hgc _ hp : IsClosed {g p}).preimage g.continuous
  obtain ⟨S, hSf, hSc, hSi, hFS⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hF
  have hfin : (h '' F).Finite := by
    rw [hFS, Set.sUnion_eq_biUnion, Set.image_iUnion₂]
    refine hSf.biUnion fun t ht => Set.Subsingleton.finite ?_
    obtain ⟨η, hη⟩ := QuasiSober.sober (hSi t ht) (hSc t ht)
    have hηF : closure {η} ⊆ F := hη ▸ hFS ▸ Set.subset_sUnion_of_mem ht
    rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
    rw [← hη] at hx hx'
    rw [apply_eq_of_mem_closure hcurve hhc hηF hx, apply_eq_of_mem_closure hcurve hhc hηF hx']
  have hdisc : _root_.IsDiscrete (h '' F) := hfin.isDiscrete_of_subset_closedPoints <| by
    rintro _ ⟨x, hx, rfl⟩
    exact isClosed_singleton_apply hcurve hhc
      (closure_minimal (Set.singleton_subset_iff.mpr hx) hF)
  exact ((hconn _).image h h.continuous.continuousOn).isDiscrete_iff_subsingleton.mp hdisc
    ⟨p, rfl, rfl⟩ ⟨q, hpq.symm, rfl⟩

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
  obtain ⟨q₀, hq₀, hgq₀⟩ : g p ∈ g '' closure {x} :=
    closure_minimal (Set.singleton_subset_iff.mpr
      (show g x' ∈ g '' closure {x} from ⟨x, subset_closure rfl, hxx⟩)) (hgc _ isClosed_closure)
      ((specializes_iff_mem_closure.mpr hpx').map g.continuous).mem_closure
  obtain ⟨q, ⟨hqx, hgq⟩, hqc⟩ := (isClosed_closure.inter
    ((Set.image_singleton ▸ hgc _ hpc : IsClosed {g p}).preimage g.continuous) :
    IsClosed (closure {x} ∩ g ⁻¹' {g p})).exists_closed_singleton ⟨q₀, hq₀, hgq₀⟩
  refine hpO (show h p ∈ closure {h x} from
    apply_eq_of_isClosed hcurve hgc hhc hconn hqc hgq ▸ ?_)
  exact ((specializes_iff_mem_closure.mpr hqx).map h.continuous).mem_closure

end Fibres

/-- **A projective contraction factors any morphism constant on its contracted curves.** Let
`q : X ⟶ V` be a projective surjection of projective `k`-varieties with `q.c : 𝒪_V ⟶ q_* 𝒪_X`
an isomorphism, and `f : X ⟶ S` a morphism to a projective `k`-variety. If every proper curve
of `X` contracted by `q` is contracted by `f`, then `q ≫ h = f` for a unique `h : V ⟶ S`. -/
@[mmp "lem_mmp_projective_contraction_curve_factorization"]
public theorem existsUnique_comp_eq_of_isContractedBy {k : Type u} [Field k]
    {X V S : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)}
    {sS : S ⟶ Spec (.of k)} (hX : IsProjectiveVariety k sX) (hV : IsProjectiveVariety k sV)
    (hS : IsProjectiveVariety k sS) {q : X ⟶ V} (hq : IsProjectiveMorphism q)
    [Surjective q] [IsIso q.c] (hqV : q ≫ sV = sX) {f : X ⟶ S} (hfS : f ≫ sS = sX)
    (hf : ∀ C : ProperCurve sX, C.IsContractedBy q → C.IsContractedBy f) :
    ∃! h : V ⟶ S, q ≫ h = f := by
  have : IsProper sX := isProper_of_isProjectiveMorphism _ hX.isProjective
  have : IsProper sS := isProper_of_isProjectiveMorphism _ hS.isProjective
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := (isNoetherian_iff X).mpr ⟨inferInstance, inferInstance⟩
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  have : IsProper q := isProper_of_isProjectiveMorphism _ hq
  have : IsProper (f ≫ sS) := hfS ▸ inferInstance
  have : IsProper f := IsProper.of_comp f sS
  refine MMP.existsUnique_comp_eq_of_isIso_c q f fun x x' hxx => ?_
  exact apply_eq_of_apply_eq hf q.isClosedMap f.isClosedMap
    (fun v => (q.isConnected_preimage_singleton_of_isIso_app
      (fun W => inferInstance) v).isPreconnected) hxx

end MMP.Mori

end
