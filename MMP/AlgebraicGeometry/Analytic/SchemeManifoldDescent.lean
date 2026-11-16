module

public import MMP.AlgebraicGeometry.Analytic.PluriformDensity
public import MMP.AlgebraicGeometry.Analytic.Analytification
public import MMP.AlgebraicGeometry.Analytic.SchemeManifold
import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.LocallyContractible
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ClassicalTopologyCharts

/-!
# Descent of product germs along a proper modification

Let `φ : T ⟶ B` be a finite étale morphism of separated schemes of finite type over `ℂ`. Its
realization `T^an → B^an` is a local homeomorphism (étaleness) and a proper map (finiteness), so
its fibres are compact and discrete, hence finite, and it is a covering map. Over a connected
open `Δ ⊆ B^an`, two continuous sections of `T^an → B^an` agreeing at one point agree everywhere.

This is what descends a product germ: if `π : Z → X` is proper, surjective and injective off the
preimage `E` of a centre `τ ⊆ X` which covers `B`, and a neighbourhood of `E` over a disk `Δ` is a
product over `Δ` preserving `E`, then pushing the product forward along `π` gives a product germ of
`(X, τ)` at every point of `τ`: the sheets of `E` through a fibre of `π` follow the same sheet of
`τ`, by uniqueness of lifts.

## Main results

* `MMP.Analytic.ComplexPoints.isCoveringMap_realize_of_isFinite_of_etale`: finite étale
  morphisms realize to covering maps.
* `MMP.Analytic.ComplexPoints.mem_range_realize_iff_of_isClosedImmersion`: the `ℂ`-points of a
  closed subscheme are the `ℂ`-points lying over it;
  `MMP.Analytic.ComplexPoints.eq_of_realize_eq_of_isIso_restrict`: a morphism which is an
  isomorphism over an open realizes to a map injective over that open.
* `MMP.Analytic.ComplexPoints.exists_homeomorph_prod_of_isProperMap`: a product structure over a
  disk near the preimage of a centre descends along a proper surjective map which is injective
  off the centre and covers the centre by a covering map, to a product germ at a point of the
  centre.

## References

* [Serre, *Géométrie algébrique et géométrie analytique*]
-/

open CategoryTheory AlgebraicGeometry Topology

namespace MMP.Analytic.ComplexPoints

section Covering

variable {T B : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)} {sB : B ⟶ Spec (.of ℂ)}

/-- The fibres of a local homeomorphism are discrete. -/
private lemma isDiscrete_preimage_singleton {E Y : Type*} [TopologicalSpace E]
    [TopologicalSpace Y] {p : E → Y} (hp : IsLocalHomeomorph p) (y : Y) :
    IsDiscrete (p ⁻¹' {y}) := by
  refine ⟨discreteTopology_iff_isOpen_singleton.2 fun t ↦ ?_⟩
  obtain ⟨e, he, rfl⟩ := hp t.1
  refine isOpen_induced_iff.2 ⟨e.source, e.open_source, ?_⟩
  ext t'
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  refine ⟨fun h ↦ Subtype.ext (e.injOn h he (t'.2.trans t.2.symm)), fun h ↦ h ▸ he⟩

/-- **Finite étale morphisms realize to covering maps.** For a finite étale morphism `φ : T ⟶ B`
of separated schemes of finite type over `ℂ`, the realized map `T^an → B^an` is a covering
map. -/
public theorem isCoveringMap_realize_of_isFinite_of_etale [LocallyOfFiniteType sT]
    [QuasiCompact sT] [IsSeparated sT] [LocallyOfFiniteType sB] [QuasiCompact sB]
    (φ : T ⟶ B) (hφ : φ ≫ sB = sT) [IsFinite φ] [Etale φ] :
    IsCoveringMap (realize φ hφ) := by
  have hloc := isLocalHomeomorph_realize_of_etale φ hφ
  have hprop := (isSeparatedMap_and_isProperMap_realize φ hφ).2
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  refine hprop.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn (fun b _ ↦ ?_)
    hloc.isLocalHomeomorphOn
  exact (hprop.isCompact_preimage isCompact_singleton).finite
    (isDiscrete_preimage_singleton hloc b)

end Covering

section SchemeInputs

variable {Z X T B : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sB : B ⟶ Spec (.of ℂ)}

/-- The `ℂ`-points of a closed subscheme `T ⊆ X` are the `ℂ`-points of `X` lying over `T`. -/
public theorem mem_range_realize_iff_of_isClosedImmersion (iT : T ⟶ X) [IsClosedImmersion iT]
    (y : ComplexPoints sX) :
    y ∈ Set.range (realize (sX := iT ≫ sX) iT rfl) ↔ toScheme y ∈ Set.range iT := by
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  letI : T.Over (Spec (.of ℂ)) := ⟨iT ≫ sX⟩
  haveI : iT.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨_, rfl⟩
  · intro hy
    have hmem : homeomorphUnderlyingSpace (X := X) y ∈
        Set.range (MMP.UnderlyingSpace.mapFun (K := ℂ) iT) := by
      rw [MMP.UnderlyingSpace.range_mapFun_of_isClosedImmersion]
      change y.hom (IsLocalRing.closedPoint ℂ) ∈ Set.range iT
      rw [Subsingleton.elim (IsLocalRing.closedPoint ℂ) (default : Spec (.of ℂ))]
      exact hy
    obtain ⟨q, hq⟩ := hmem
    refine ⟨(homeomorphUnderlyingSpace (X := T)).symm q, ?_⟩
    apply (homeomorphUnderlyingSpace (X := X)).injective
    rw [← hq]
    exact MMP.UnderlyingSpace.ext rfl

/-- **Injectivity off the centre.** If `f : Z ⟶ X` restricts to an isomorphism over an open
`U ⊆ X`, then `f^an` is injective over `U(ℂ)`. -/
public theorem eq_of_realize_eq_of_isIso_restrict (f : Z ⟶ X) (U : X.Opens) [IsIso (f ∣_ U)]
    {z z' : ComplexPoints (f ≫ sX)} (hz : toScheme (realize f rfl z) ∈ U)
    (h : realize f rfl z = realize f rfl z') : z = z' := by
  have hz' : toScheme (realize f rfl z') ∈ U := h ▸ hz
  have H : ∀ w : ComplexPoints (f ≫ sX), toScheme (realize f rfl w) ∈ U →
      Set.range w.hom ⊆ Set.range (f ⁻¹ᵁ U).ι := by
    rintro w hw _ ⟨q, rfl⟩
    rw [Subsingleton.elim q default, Scheme.Opens.range_ι]
    exact hw
  have hl := IsOpenImmersion.lift_fac (f ⁻¹ᵁ U).ι z.hom (H z hz)
  have hl' := IsOpenImmersion.lift_fac (f ⁻¹ᵁ U).ι z'.hom (H z' hz')
  have hzz : z.hom ≫ f = z'.hom ≫ f := congrArg (fun y : ComplexPoints sX ↦ y.hom) h
  rw [← hl, ← hl', Category.assoc, Category.assoc, ← morphismRestrict_ι,
    ← Category.assoc, ← Category.assoc, cancel_mono, cancel_mono] at hzz
  ext1
  rw [← hl, ← hl', hzz]

end SchemeInputs

section Descent

variable {Zs Xs Bs : Type*} [TopologicalSpace Zs] [TopologicalSpace Xs] [TopologicalSpace Bs]

/-- **Uniqueness of lifts into a covering.** If `h|τ : τ → B` is a covering map, two continuous
maps from a preconnected space into `τ` with the same image under `h` agreeing at one point
agree everywhere. -/
public theorem eq_of_isCoveringMap_of_mem {D : Type*} [TopologicalSpace D] [PreconnectedSpace D]
    {h : Xs → Bs} {τ : Set Xs} (hcov : IsCoveringMap (fun t : τ ↦ h t)) {f g : D → Xs}
    (hf : Continuous f) (hg : Continuous g) (hfτ : ∀ t, f t ∈ τ) (hgτ : ∀ t, g t ∈ τ)
    (hfg : ∀ t, h (f t) = h (g t)) {t₀ : D} (h₀ : f t₀ = g t₀) : f = g := by
  have key := hcov.eq_of_comp_eq (g₁ := fun t ↦ (⟨f t, hfτ t⟩ : τ))
    (g₂ := fun t ↦ (⟨g t, hgτ t⟩ : τ)) (hf.subtype_mk _) (hg.subtype_mk _) (funext hfg) t₀
    (Subtype.ext h₀)
  exact funext fun t ↦ congrArg Subtype.val (congrFun key t)

/-- If `h|τ : τ → B` is a local homeomorphism, then `x ∈ τ` has an open neighbourhood meeting
`τ ∩ h⁻¹ {h x}` only in `x`. -/
public theorem exists_isOpen_forall_eq_of_isLocalHomeomorph {h : Xs → Bs} {τ : Set Xs}
    (hloc : IsLocalHomeomorph (fun t : τ ↦ h t)) {x : Xs} (hxτ : x ∈ τ) :
    ∃ V : Set Xs, IsOpen V ∧ x ∈ V ∧ ∀ y ∈ τ, y ∈ V → h y = h x → y = x := by
  obtain ⟨e, hxe, he⟩ := hloc ⟨x, hxτ⟩
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.1 e.open_source
  refine ⟨V, hVo, show (⟨x, hxτ⟩ : τ) ∈ Subtype.val ⁻¹' V from hV ▸ hxe,
    fun y hyτ hyV hyx ↦ ?_⟩
  have hy : (⟨y, hyτ⟩ : τ) ∈ e.source := by
    rw [← hV]
    exact hyV
  have hee : e ⟨y, hyτ⟩ = e ⟨x, hxτ⟩ := by
    rw [← congrFun he, ← congrFun he]
    exact hyx
  exact congrArg Subtype.val (e.injOn hy hxe hee)

/-- If `π` is a closed map and `h|τ : τ → B` a local homeomorphism, a point `x ∈ τ` over `b` has an
open neighbourhood `V` meeting `τ ∩ h⁻¹ {b}` only in `x` whose preimage under `π` lies in any given
open `O` containing `π⁻¹ τ ∩ (h ∘ π)⁻¹ {b}`. -/
public theorem exists_isOpen_forall_mem_of_isClosedMap {π : Zs → Xs} (hπ : IsClosedMap π)
    {h : Xs → Bs} {τ : Set Xs} (hloc : IsLocalHomeomorph (fun t : τ ↦ h t)) {x : Xs}
    (hxτ : x ∈ τ) {b : Bs} (hxb : h x = b) {O : Set Zs} (hO : IsOpen O)
    (hEO : π ⁻¹' τ ∩ (h ∘ π) ⁻¹' {b} ⊆ O) :
    ∃ V : Set Xs, IsOpen V ∧ x ∈ V ∧ (∀ z, π z ∈ V → z ∈ O) ∧
      ∀ y ∈ τ, y ∈ V → h y = h x → y = x := by
  obtain ⟨V₁, hV₁o, hxV₁, hiso⟩ := exists_isOpen_forall_eq_of_isLocalHomeomorph hloc hxτ
  refine ⟨V₁ ∩ (π '' Oᶜ)ᶜ, hV₁o.inter (hπ _ hO.isClosed_compl).isOpen_compl,
    ⟨hxV₁, fun ⟨z, hzO, hzx⟩ ↦ hzO (hEO ⟨show π z ∈ τ from hzx ▸ hxτ,
      show h (π z) = b from hzx ▸ hxb⟩)⟩,
    fun z hz ↦ by_contra fun h' ↦ hz.2 ⟨z, h', rfl⟩, fun y hy hyV ↦ hiso y hy hyV.1⟩

/-- Let `Φ : U_b × Δ ≃ₜ U` be a homeomorphism over a preconnected `Δ` preserving `π⁻¹ τ`, where
`h|τ` is a covering map. If two points of `U_b` over `τ` have the same image under `π ∘ Φ` at one
time `t₀`, they have the same image at every time `t`. -/
public theorem apply_eq_of_isCoveringMap {π : Zs → Xs} (hπ : Continuous π) {h : Xs → Bs}
    {τ : Set Xs} (hcov : IsCoveringMap (fun t : τ ↦ h t)) {Δ : Set Bs} [PreconnectedSpace Δ]
    {Ub U : Set Zs} (Φ : Ub × Δ ≃ₜ U) (hΦg : ∀ p, h (π (Φ p)) = p.2)
    (hΦE : ∀ p, π (Φ p) ∈ τ ↔ π p.1 ∈ τ) {w w' : Ub} (hw : π w ∈ τ) (hw' : π w' ∈ τ)
    {t₀ : Δ} (h₀ : π (Φ (w, t₀)) = π (Φ (w', t₀))) (t : Δ) :
    π (Φ (w, t)) = π (Φ (w', t)) := by
  have hc : ∀ u : Ub, Continuous fun t : Δ ↦ π (Φ (u, t)) := fun u ↦
    hπ.comp (continuous_subtype_val.comp
      (Φ.continuous.comp (continuous_const.prodMk continuous_id)))
  exact congrFun (eq_of_isCoveringMap_of_mem hcov (hc w) (hc w') (fun _ ↦ (hΦE _).2 hw)
    (fun _ ↦ (hΦE _).2 hw') (fun t ↦ (hΦg (w, t)).trans (hΦg (w', t)).symm) h₀) t

/-- In the setting of `apply_eq_of_isCoveringMap`, if `U` contains `π⁻¹ τ ∩ (h ∘ π)⁻¹ Δ` and `Φ`
is the identity over `b`, every point of `Zs` with the same image under `π` as a point `Φ p` over
`τ` is of the form `Φ p'` with `p'` at the same time as `p` and `π p'.1 = π p.1`. -/
public theorem exists_apply_eq_of_isCoveringMap {π : Zs → Xs} (hπ : Continuous π) {h : Xs → Bs}
    {τ : Set Xs} (hcov : IsCoveringMap (fun t : τ ↦ h t)) {Δ : Set Bs} [PreconnectedSpace Δ]
    {b : Bs} (hbΔ : b ∈ Δ) {Ub U : Set Zs} (hEU : π ⁻¹' τ ∩ (h ∘ π) ⁻¹' Δ ⊆ U)
    (Φ : Ub × Δ ≃ₜ U) (hΦg : ∀ p, h (π (Φ p)) = p.2)
    (hΦb : ∀ z : Ub, (Φ (z, ⟨b, hbΔ⟩) : Zs) = z) (hΦE : ∀ p, π (Φ p) ∈ τ ↔ π p.1 ∈ τ)
    {p : Ub × Δ} {z : Zs} (hτ : π (Φ p) ∈ τ) (hz : π z = π (Φ p)) :
    ∃ p' : Ub × Δ, (Φ p' : Zs) = z ∧ p'.2 = p.2 ∧ π p'.1 = π p.1 := by
  obtain ⟨u, t⟩ := p
  have hzU : z ∈ U := hEU ⟨show π z ∈ τ by rw [hz]; exact hτ,
    show h (π z) ∈ Δ by rw [hz, hΦg]; exact t.2⟩
  obtain ⟨pr, hΦpr⟩ : ∃ pr, (Φ pr : Zs) = z := ⟨Φ.symm ⟨z, hzU⟩, by rw [Φ.apply_symm_apply]⟩
  have ht : pr.2 = t := Subtype.ext (by rw [← hΦg pr, hΦpr, hz, hΦg])
  have hag := apply_eq_of_isCoveringMap hπ hcov Φ hΦg hΦE ((hΦE _).1 hτ)
    ((hΦE pr).1 (by rw [hΦpr, hz]; exact hτ)) (t₀ := t) (by
      rw [← ht]
      change π (Φ (u, pr.2)) = π (Φ pr)
      rw [ht, hΦpr]
      exact hz.symm) ⟨b, hbΔ⟩
  rw [hΦb, hΦb] at hag
  exact ⟨pr, hΦpr, ht, hag.symm⟩

/-- In the setting of `exists_apply_eq_of_isCoveringMap`, with `π` injective off `π⁻¹ τ`, the
image under `Φ` of a set `S ⊆ U_b × Δ` whose membership depends only on the time and on the image
under `π` of the first coordinate is saturated for `π`. -/
public theorem mem_image_of_isCoveringMap {π : Zs → Xs} (hπ : Continuous π) {h : Xs → Bs}
    {τ : Set Xs} (hinj : ∀ z z', π z ∉ τ → π z = π z' → z = z')
    (hcov : IsCoveringMap (fun t : τ ↦ h t)) {Δ : Set Bs} [PreconnectedSpace Δ]
    {b : Bs} (hbΔ : b ∈ Δ) {Ub U : Set Zs} (hEU : π ⁻¹' τ ∩ (h ∘ π) ⁻¹' Δ ⊆ U)
    (Φ : Ub × Δ ≃ₜ U) (hΦg : ∀ p, h (π (Φ p)) = p.2)
    (hΦb : ∀ z : Ub, (Φ (z, ⟨b, hbΔ⟩) : Zs) = z) (hΦE : ∀ p, π (Φ p) ∈ τ ↔ π p.1 ∈ τ)
    {S : Set (Ub × Δ)} (hS : ∀ p p' : Ub × Δ, p'.2 = p.2 → π p'.1 = π p.1 → p ∈ S → p' ∈ S)
    {z : Zs} (hz : π z ∈ π '' (Subtype.val '' (Φ '' S))) : z ∈ Subtype.val '' (Φ '' S) := by
  obtain ⟨_, ⟨_, ⟨p, hp, rfl⟩, rfl⟩, hza⟩ := hz
  by_cases hτ : π (Φ p) ∈ τ
  · obtain ⟨p', hp', ht, hu⟩ :=
      exists_apply_eq_of_isCoveringMap hπ hcov hbΔ hEU Φ hΦg hΦb hΦE hτ hza.symm
    exact ⟨Φ p', ⟨p', hS p p' ht hu hp, rfl⟩, hp'⟩
  · exact ⟨Φ p, ⟨p, hp, rfl⟩, hinj _ _ hτ hza⟩

/-- In the setting of `mem_image_of_isCoveringMap`, with `π` proper and surjective and `U` open,
the image under `π` of `Φ '' S` is open for every open `S ⊆ U_b × Δ` saturated as there. -/
public theorem isOpen_image_of_isCoveringMap {π : Zs → Xs} (hπ : IsProperMap π)
    (hπs : Function.Surjective π) {h : Xs → Bs} {τ : Set Xs}
    (hinj : ∀ z z', π z ∉ τ → π z = π z' → z = z')
    (hcov : IsCoveringMap (fun t : τ ↦ h t)) {Δ : Set Bs} [PreconnectedSpace Δ]
    {b : Bs} (hbΔ : b ∈ Δ) {Ub U : Set Zs} (hUo : IsOpen U) (hEU : π ⁻¹' τ ∩ (h ∘ π) ⁻¹' Δ ⊆ U)
    (Φ : Ub × Δ ≃ₜ U) (hΦg : ∀ p, h (π (Φ p)) = p.2)
    (hΦb : ∀ z : Ub, (Φ (z, ⟨b, hbΔ⟩) : Zs) = z) (hΦE : ∀ p, π (Φ p) ∈ τ ↔ π p.1 ∈ τ)
    {S : Set (Ub × Δ)} (hSo : IsOpen S)
    (hS : ∀ p p' : Ub × Δ, p'.2 = p.2 → π p'.1 = π p.1 → p ∈ S → p' ∈ S) :
    IsOpen (π '' (Subtype.val '' (Φ '' S))) := by
  refine (hπ.isClosedMap.isQuotientMap hπ.continuous hπs).isOpen_preimage.1 ?_
  rw [show π ⁻¹' (π '' (Subtype.val '' (Φ '' S))) = Subtype.val '' (Φ '' S) from
    Set.Subset.antisymm (fun _ ↦ mem_image_of_isCoveringMap hπ.continuous hinj hcov hbΔ hEU Φ
      hΦg hΦb hΦE hS) (Set.subset_preimage_image _ _)]
  exact hUo.isOpenMap_subtype_val _ (Φ.isOpenMap _ hSo)

/-- In the setting of `isOpen_image_of_isCoveringMap`, a map `ψ : A × Δ → X`, with `e : A → X` an
embedding into an open `V₀`, is open if each `ψ q` is `π (Φ (u, q.2))` for some `u` over `e q.1`,
and each `π (Φ (u, t))` with `π u ∈ V₀` is `ψ (a, t)` for some `a` with `e a = π u`. -/
public theorem isOpenMap_of_isCoveringMap {π : Zs → Xs} (hπ : IsProperMap π)
    (hπs : Function.Surjective π) {h : Xs → Bs} {τ : Set Xs}
    (hinj : ∀ z z', π z ∉ τ → π z = π z' → z = z')
    (hcov : IsCoveringMap (fun t : τ ↦ h t)) {Δ : Set Bs} [PreconnectedSpace Δ]
    {b : Bs} (hbΔ : b ∈ Δ) {Ub U : Set Zs} (hUo : IsOpen U) (hEU : π ⁻¹' τ ∩ (h ∘ π) ⁻¹' Δ ⊆ U)
    (Φ : Ub × Δ ≃ₜ U) (hΦg : ∀ p, h (π (Φ p)) = p.2)
    (hΦb : ∀ z : Ub, (Φ (z, ⟨b, hbΔ⟩) : Zs) = z) (hΦE : ∀ p, π (Φ p) ∈ τ ↔ π p.1 ∈ τ)
    {A : Type*} [TopologicalSpace A] {e : A → Xs} (he : IsEmbedding e) {V₀ : Set Xs}
    (hV₀o : IsOpen V₀) (heV : ∀ a, e a ∈ V₀) {ψ : A × Δ → Xs}
    (hψ₁ : ∀ q, ∃ u : Ub, π u = e q.1 ∧ ψ q = π (Φ (u, q.2)))
    (hψ₂ : ∀ (u : Ub) (t : Δ), π u ∈ V₀ → ∃ a, e a = π u ∧ ψ (a, t) = π (Φ (u, t))) :
    IsOpenMap ψ := by
  intro O' hO'
  obtain ⟨W', hW'o, hW'⟩ := (he.prodMap IsEmbedding.subtypeVal).isInducing.isOpen_iff.1 hO'
  have hc₁ : Continuous fun q : Ub × Δ ↦ π q.1 :=
    hπ.continuous.comp (continuous_subtype_val.comp continuous_fst)
  let S : Set (Ub × Δ) := {q | π q.1 ∈ V₀ ∧ (π q.1, (q.2 : Bs)) ∈ W'}
  have hSo : IsOpen S := (hV₀o.preimage hc₁).inter
    (hW'o.preimage (hc₁.prodMk (continuous_subtype_val.comp continuous_snd)))
  have himage : ψ '' O' = π '' (Subtype.val '' (Φ '' S)) := by
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨u, hu, hψq⟩ := hψ₁ q
      rw [← hW'] at hq
      refine ⟨Φ (u, q.2), ⟨_, ⟨(u, q.2), ⟨hu ▸ heV _, ?_⟩, rfl⟩, rfl⟩, hψq.symm⟩
      rw [hu]
      exact hq
    · rintro ⟨_, ⟨_, ⟨⟨u, t⟩, hS, rfl⟩, rfl⟩, rfl⟩
      obtain ⟨a, ha, hψa⟩ := hψ₂ u t hS.1
      refine ⟨(a, t), ?_, hψa⟩
      rw [← hW']
      change (e a, (t : Bs)) ∈ W'
      rw [ha]
      exact hS.2
  rw [himage]
  exact isOpen_image_of_isCoveringMap hπ hπs hinj hcov hbΔ hUo hEU Φ hΦg hΦb hΦE hSo
    fun p p' ht hu hp ↦ ⟨by rw [hu]; exact hp.1, by rw [hu, ht]; exact hp.2⟩

/-- An open embedding `ψ : U₀ × Δ → X` over `Δ`, restricting to the identity on the slice over `b`
and meeting `τ` exactly in `{x} × Δ`, is a homeomorphism of its range onto `U₀ × Δ` with the
properties of a product germ of `(X, τ)` at `x`. -/
public theorem exists_homeomorph_range_of_isOpenEmbedding {h : Xs → Bs} {τ : Set Xs} {x : Xs}
    {b : Bs} (hxb : h x = b) {Δ : Set Bs} (hbΔ : b ∈ Δ) {U₀ : Set (h ⁻¹' {b})}
    (hx₀ : (⟨x, hxb⟩ : h ⁻¹' {b}) ∈ U₀) {ψ : U₀ × Δ → Xs} (hψ : IsOpenEmbedding ψ)
    (hψh : ∀ q, h (ψ q) = q.2) (hψb : ∀ y₀ : U₀, ψ (y₀, ⟨b, hbΔ⟩) = y₀.1.1)
    (hψτ : ∀ q, ψ q ∈ τ ↔ q.1 = ⟨⟨x, hxb⟩, hx₀⟩) :
    ∃ (hxU : x ∈ Set.range ψ) (φ : Set.range ψ ≃ₜ U₀ × Δ),
      φ ⟨x, hxU⟩ = (⟨⟨x, hxb⟩, hx₀⟩, ⟨b, hbΔ⟩) ∧
      (∀ y : Set.range ψ, ((φ y).2 : Bs) = h y) ∧
      (∀ y : Set.range ψ, (y : Xs) ∈ τ ↔ (φ y).1 = ⟨⟨x, hxb⟩, hx₀⟩) ∧
      ∀ (y : Set.range ψ) (hy : h y = b), ((φ y).1 : h ⁻¹' {b}) = ⟨y, hy⟩ := by
  let φ : Set.range ψ ≃ₜ U₀ × Δ := hψ.isEmbedding.toHomeomorph.symm
  have hφ : ∀ y : Set.range ψ, ψ (φ y) = y := fun y ↦
    congrArg Subtype.val (hψ.isEmbedding.toHomeomorph.apply_symm_apply y)
  refine ⟨⟨(⟨⟨x, hxb⟩, hx₀⟩, ⟨b, hbΔ⟩), hψb _⟩, φ, ?_, fun y ↦ ?_, fun y ↦ ?_, fun y hy ↦ ?_⟩
  · apply hψ.injective
    rw [hφ, hψb]
  · rw [← hψh (φ y), hφ]
  · rw [← hφ y, hψτ]
  · have h2 : (φ y).2 = ⟨b, hbΔ⟩ := Subtype.ext (by rw [← hψh (φ y), hφ]; exact hy)
    have h1 := hφ y
    rw [show φ y = ((φ y).1, ⟨b, hbΔ⟩) from Prod.ext rfl h2, hψb] at h1
    exact Subtype.ext h1

/-- **Descent of a product germ along a proper map.** Let `π : Z → X` be proper and surjective,
`h : X → B` continuous, `τ ⊆ X` with `π` injective off `π⁻¹ τ` and `h|τ : τ → B` a covering map,
and `x ∈ τ` over `b`. Suppose that over a preconnected `Δ ∋ b`, a neighbourhood `U` of
`E_Δ = π⁻¹ τ ∩ (h ∘ π)⁻¹ Δ` is the product `U_b × Δ` of a neighbourhood `U_b` of `E_b` in the fibre
over `b` with `Δ`, by a homeomorphism `Φ` over `Δ` which is the identity on `U_b` and preserves
`E`. Then the germ of `(X, τ)` at `x` is the product of the germ of the slice `(X_b, {x})` with
`Δ`: there are open `U' ∋ x` in `X`, `U₀ ∋ x` in `X_b` and a homeomorphism `U' ≃ₜ U₀ × Δ` over
`Δ`, sending `x` to `(x, b)` and `τ ∩ U'` to `{x} × Δ`, and the identity on the slice. -/
public theorem exists_homeomorph_prod_of_isProperMap {π : Zs → Xs} (hπ : IsProperMap π)
    (hπs : Function.Surjective π) {h : Xs → Bs} {τ : Set Xs}
    (hinj : ∀ z z', π z ∉ τ → π z = π z' → z = z')
    (hcov : IsCoveringMap (fun t : τ ↦ h t)) {x : Xs} (hxτ : x ∈ τ) {b : Bs} (hxb : h x = b)
    {Δ : Set Bs} (hΔc : IsPreconnected Δ) (hbΔ : b ∈ Δ)
    {O Ub U : Set Zs} (hO : IsOpen O) (hUb : Ub = O ∩ (h ∘ π) ⁻¹' {b})
    (hEb : π ⁻¹' τ ∩ (h ∘ π) ⁻¹' {b} ⊆ Ub) (hUo : IsOpen U)
    (hEU : π ⁻¹' τ ∩ (h ∘ π) ⁻¹' Δ ⊆ U) (Φ : Ub × Δ ≃ₜ U)
    (hΦg : ∀ p, h (π (Φ p)) = p.2) (hΦb : ∀ z : Ub, (Φ (z, ⟨b, hbΔ⟩) : Zs) = z)
    (hΦE : ∀ p, π (Φ p) ∈ τ ↔ π p.1 ∈ τ) :
    ∃ (U' : Set Xs) (U₀ : Set (h ⁻¹' {b})) (_ : IsOpen U') (_ : IsOpen U₀) (hxU : x ∈ U')
      (hx₀ : (⟨x, hxb⟩ : h ⁻¹' {b}) ∈ U₀) (φ : U' ≃ₜ U₀ × Δ),
      φ ⟨x, hxU⟩ = (⟨⟨x, hxb⟩, hx₀⟩, ⟨b, hbΔ⟩) ∧
      (∀ y : U', ((φ y).2 : Bs) = h y) ∧
      (∀ y : U', (y : Xs) ∈ τ ↔ (φ y).1 = ⟨⟨x, hxb⟩, hx₀⟩) ∧
      ∀ (y : U') (hy : h y = b), ((φ y).1 : h ⁻¹' {b}) = ⟨y, hy⟩ := by
  classical
  subst hUb
  haveI : PreconnectedSpace Δ := Subtype.preconnectedSpace hΔc
  obtain ⟨V₀, hV₀o, hxV₀, hV₀O, hiso⟩ := exists_isOpen_forall_mem_of_isClosedMap hπ.isClosedMap
    hcov.isLocalHomeomorph hxτ hxb hO fun _ hz ↦ (hEb hz).1
  let F : Set Xs := h ⁻¹' {b}
  let πF : π ⁻¹' F → F := F.restrictPreimage π
  let U₀ : Set F := Subtype.val ⁻¹' V₀
  have hU₀o : IsOpen U₀ := hV₀o.preimage continuous_subtype_val
  have hx₀ : (⟨x, hxb⟩ : F) ∈ U₀ := hxV₀
  let W : Set (π ⁻¹' F) := πF ⁻¹' U₀
  let π' : W → U₀ := U₀.restrictPreimage πF
  have hπ'p : IsProperMap π' := (hπ.restrictPreimage F).restrictPreimage U₀
  have hπ's : Function.Surjective π' := by
    rintro ⟨⟨y, hyF⟩, hyV⟩
    obtain ⟨z, rfl⟩ := hπs y
    exact ⟨⟨⟨z, hyF⟩, hyV⟩, rfl⟩
  let inUb : W → ↥(O ∩ (h ∘ π) ⁻¹' {b}) := fun w ↦ ⟨w.1.1, hV₀O _ w.2, w.1.2⟩
  have hinUb : Continuous inUb :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  let ψt : W × Δ → Xs := fun q ↦ π (Φ (inUb q.1, q.2))
  have hψt : Continuous ψt := hπ.continuous.comp (continuous_subtype_val.comp
    (Φ.continuous.comp (hinUb.prodMap continuous_id)))
  have hind : ∀ (w w' : W), π' w = π' w' → ∀ t : Δ, ψt (w, t) = ψt (w', t) := by
    intro w w' hww t
    have hπw : π (inUb w) = π (inUb w') := congrArg (fun y : U₀ ↦ (y.1.1 : Xs)) hww
    by_cases hτw : π (inUb w) ∈ τ
    · exact apply_eq_of_isCoveringMap hπ.continuous hcov Φ hΦg hΦE hτw (hπw ▸ hτw)
        (t₀ := ⟨b, hbΔ⟩) (by rw [hΦb, hΦb]; exact hπw) t
    · have hww' : inUb w = inUb w' := Subtype.ext (hinj _ _ hτw hπw)
      simp only [ψt, hww']
  choose sec hsec using hπ's
  let ψ : U₀ × Δ → Xs := fun q ↦ ψt (sec q.1, q.2)
  have hψp : ∀ q : W × Δ, ψ (Prod.map π' id q) = ψt q := fun q ↦
    hind _ _ (hsec (π' q.1)) q.2
  have hψh : ∀ q, h (ψ q) = q.2 := fun q ↦ hΦg _
  have hψb : ∀ y₀ : U₀, ψ (y₀, ⟨b, hbΔ⟩) = y₀.1.1 := fun y₀ ↦ by
    change π (Φ (inUb (sec y₀), ⟨b, hbΔ⟩)) = _
    rw [hΦb]
    exact congrArg (fun y : U₀ ↦ (y.1.1 : Xs)) (hsec y₀)
  have hψτ : ∀ q : U₀ × Δ, ψ q ∈ τ ↔ (q.1.1.1 : Xs) ∈ τ := by
    intro q
    change π (Φ (inUb (sec q.1), q.2)) ∈ τ ↔ _
    rw [hΦE]
    change (π' (sec q.1)).1.1 ∈ τ ↔ _
    rw [hsec]
  have hτU₀ : ∀ y : U₀, (y.1.1 : Xs) ∈ τ → y = ⟨⟨x, hxb⟩, hx₀⟩ := fun y hy ↦
    Subtype.ext (Subtype.ext (hiso _ hy y.2 ((show h _ = b from y.1.2).trans hxb.symm)))
  have hψc : Continuous ψ :=
    ((hπ'p.prodMap isProperMap_id).isClosedMap.isQuotientMap
      (hπ'p.prodMap isProperMap_id).continuous
      fun q ↦ ⟨(sec q.1, q.2), Prod.ext (hsec q.1) rfl⟩).continuous_iff.2
      (by rw [show ψ ∘ Prod.map π' id = ψt from funext hψp]; exact hψt)
  have hψinj : Function.Injective ψ := by
    rintro ⟨y₀, t⟩ ⟨y₁, t'⟩ heq
    obtain rfl : t = t' := Subtype.ext (by rw [← hψh (y₀, t), ← hψh (y₁, t'), heq])
    by_cases hτ : ψ (y₀, t) ∈ τ
    · rw [hτU₀ y₀ ((hψτ _).1 hτ), hτU₀ y₁ ((hψτ _).1 (heq ▸ hτ))]
    · have h3 : inUb (sec y₀) = inUb (sec y₁) :=
        congrArg Prod.fst (Φ.injective (Subtype.ext (hinj _ _ hτ heq)))
      rw [← hsec y₀, ← hsec y₁]
      exact Prod.ext (Subtype.ext (Subtype.ext
        (congrArg (fun u : ↥(O ∩ (h ∘ π) ⁻¹' {b}) ↦ π u) h3))) rfl
  have hψo : IsOpenMap ψ := isOpenMap_of_isCoveringMap hπ hπs hinj hcov hbΔ hUo hEU Φ hΦg hΦb
    hΦE (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal) hV₀o (fun y ↦ y.2)
    (fun q ↦ ⟨inUb (sec q.1), congrArg (fun y : U₀ ↦ (y.1.1 : Xs)) (hsec q.1), rfl⟩)
    fun u t hu ↦ ⟨π' ⟨⟨u.1, u.2.2⟩, hu⟩, rfl, hψp (⟨⟨u.1, u.2.2⟩, hu⟩, t)⟩
  have hψemb := IsOpenEmbedding.of_continuous_injective_isOpenMap hψc hψinj hψo
  obtain ⟨hxU, φ, hφ⟩ := exists_homeomorph_range_of_isOpenEmbedding hxb hbΔ hx₀ hψemb hψh hψb
    fun q ↦ (hψτ q).trans ⟨hτU₀ _, fun h ↦ by rw [h]; exact hxτ⟩
  exact ⟨_, U₀, hψemb.isOpen_range, hU₀o, hxU, hx₀, φ, hφ⟩

end Descent

end MMP.Analytic.ComplexPoints
