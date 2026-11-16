module

public import MMP.AlgebraicTopology.PoincareDuality.ManifoldLocal
public import MMP.AlgebraicTopology.PoincareDuality.Box
public import MMP.AlgebraicTopology.PoincareDuality.Punctured
public import MMP.AlgebraicTopology.PoincareDuality.Localize
public import MMP.AlgebraicTopology.PoincareDuality.LocalInjective

/-!
# Local injectivity in the top degree on a manifold, from the case of `ℝⁿ`

Hatcher's Lemma 3.27(b) in the top degree: on an `n`-manifold `Y`, a relative cycle `c` of
`(Y, Y - K)` (for `K` compact) whose image in `H_n(Y, Y - x)` vanishes for every `x ∈ K` is a
relative boundary for `K`. Here it is deduced from the same statement on `ℝⁿ`, taken as a
hypothesis: for `K` inside a chart, the cycle is moved into the chart by the theorem of small
chains and transported to `ℝⁿ`; for general `K`, the pieces `K ∩ C` with `C` compact in a chart
are glued by the Mayer–Vietoris step, using the vanishing of `H_{n+1}(Y, Y - A)` for compact
`A`.

The transports are stated for one chain at a time:

* `MMP.SingularChain.isRelBoundary_postcomp`: push-forward along a continuous
  map (in particular along a homeomorphism, and from an open subspace to `Y`);
* `MMP.SingularChain.IsRelBoundary.of_postcomp_subtypeVal`: excision from `Y`
  to an open subspace;
* `MMP.SingularChain.exists_isRelBoundary_sub_postcomp_subtypeVal`: a relative
  cycle for `K ⊆ U` is homologous rel `K` to a chain of `U`.

## Main results

* `MMP.SingularChain.isRelBoundary_of_isCompact_of_chartedSpace`: the transport from `ℝⁿ`
  to an `n`-manifold;
* `MMP.SingularChain.isRelBoundary_of_isCompact_of_forall_mem`: Hatcher's Lemma 3.27(b) in the
  top degree on an `n`-manifold.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002], §3.3, Lemma 3.27.
-/

@[expose] public noncomputable section

open Finsupp Set Topology

namespace MMP

namespace SingularChain

variable {R : Type*} [CommRing R] {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]

section transport

/-- Push-forward of a relative boundary for `K` along `f` is a relative boundary for any `L`
with `f⁻¹ L ⊆ K`. -/
lemma isRelBoundary_postcomp {m : ℕ} (f : C(Y, Z)) {K : Set Y} {L : Set Z} (hLK : f ⁻¹' L ⊆ K)
    {c : Chain R Y m} (hc : IsRelBoundary R m K c) :
    IsRelBoundary R m L (postcomp R f m c) := by
  obtain ⟨w, hw⟩ := hc
  refine ⟨postcomp R f (m + 1) w, ?_⟩
  rw [← postcomp_bd, ← map_sub]
  exact postcomp_mem_inside f (U := Kᶜ) (V := Lᶜ)
    (fun y (hy : y ∈ Kᶜ) ↦ show f y ∈ Lᶜ from fun hfy ↦ hy (hLK hfy)) hw

/-- Push-forward from a subspace `U`: a relative boundary of `U` for `U ∩ K` is a relative
boundary of `Y` for `K`. -/
lemma isRelBoundary_postcomp_subtypeVal {m : ℕ} {U K : Set Y} {c : Chain R U m}
    (hc : IsRelBoundary R m ((↑) ⁻¹' K) c) :
    IsRelBoundary R m K (postcomp R (ContinuousMap.subtypeVal U) m c) :=
  isRelBoundary_postcomp _ (fun _ hy ↦ hy) hc

/-- Excision for one chain: for `U` open and `K ⊆ U` closed in `Y`, a chain of `U`
whose push-forward is a relative boundary of `Y` for `K` is a relative boundary of `U` for
`U ∩ K`. -/
theorem IsRelBoundary.of_postcomp_subtypeVal {m : ℕ} {U K : Set Y} (hU : IsOpen U)
    (hK : IsClosed K) (hKU : K ⊆ U) {c : Chain R U m}
    (h : IsRelBoundary R m K (postcomp R (ContinuousMap.subtypeVal U) m c)) :
    IsRelBoundary R m ((↑) ⁻¹' K) c := by
  set ι := ContinuousMap.subtypeVal U
  set 𝒰 : Set (Set Y) := {U, Kᶜ}
  have h𝒰 : ∀ V ∈ 𝒰, IsOpen V := by
    rintro V (rfl | rfl)
    · exact hU
    · exact hK.isOpen_compl
  have hcY : postcomp R ι m c ∈ inside R m U :=
    postcomp_mem_inside ι (U := univ) (fun x _ ↦ x.2) (mem_inside_univ c)
  obtain ⟨w, hw⟩ := h
  generalize hcYdef : postcomp R ι m c = cY at hcY hw
  generalize hfdef : cY - bd R m w = f at hw
  have hcov : w ∈ inside R (m + 1) (⋃₀ 𝒰) := by
    have : ⋃₀ 𝒰 = univ := by
      simp only [𝒰, sUnion_insert, sUnion_singleton]
      exact eq_univ_of_forall fun y ↦ (em (y ∈ K)).imp (fun h ↦ hKU h) id
    rw [this]
    exact mem_inside_univ w
  obtain ⟨wU, hwU, wK, hwK, hsplit⟩ :=
    exists_add_of_mem_small_pair (smallChainMap_mem_small h𝒰 (m + 1) hcov)
  have hbdw : bd R m w = cY - f := by rw [← hfdef]; abel
  have hDf : smallHomotopy R 𝒰 m f ∈ inside R (m + 1) Kᶜ :=
    smallHomotopy_mem_inside_of_mem 𝒰 hw
  have hDc : smallHomotopy R 𝒰 m cY ∈ inside R (m + 1) U :=
    smallHomotopy_mem_inside_of_mem 𝒰 hcY
  have hv : wU + smallHomotopy R 𝒰 m cY ∈ inside R (m + 1) U :=
    Submodule.add_mem _ hwU hDc
  obtain ⟨v', hv'⟩ := exists_postcomp_subtypeVal_eq hv
  refine ⟨v', ?_⟩
  -- `cY - ∂ (wU + D cY) = ∂ wK - ∂ D f + f`
  have key : cY - bd R m (wU + smallHomotopy R 𝒰 m cY) =
      bd R m wK - bd R m (smallHomotopy R 𝒰 m f) + f := by
    have h1 := congrArg (bd R m) hsplit
    rw [smallChainMap_succ, map_sub, map_sub, bd_bd, sub_zero, hbdw, map_sub, map_sub,
      map_add] at h1
    rw [map_add]
    generalize bd R m (smallHomotopy R 𝒰 m cY) = P at h1 ⊢
    generalize bd R m (smallHomotopy R 𝒰 m f) = Q at h1 ⊢
    have h2 := sub_eq_iff_eq_add.1 (sub_eq_iff_eq_add.1 h1)
    rw [h2]
    abel
  have hmem : postcomp R ι m (c - bd R m v') ∈ inside R m Kᶜ := by
    rw [map_sub, postcomp_bd, hv', hcYdef, key]
    exact Submodule.add_mem _ (Submodule.sub_mem _ (bd_mem_inside hwK) (bd_mem_inside hDf)) hw
  exact mem_inside_preimage_of_postcomp_mem_inside Subtype.val_injective hmem

/-- Converse excision for one chain along an open embedding `f : Y → Z`, for `L ⊆ f(Y)` closed
in `Z`. -/
theorem IsRelBoundary.of_postcomp_isOpenEmbedding {m : ℕ} {f : C(Y, Z)} (hf : IsOpenEmbedding f)
    {L : Set Z} (hL : IsClosed L) (hLf : L ⊆ range f) {c : Chain R Y m}
    (h : IsRelBoundary R m L (postcomp R f m c)) : IsRelBoundary R m (f ⁻¹' L) c := by
  set g : Y ≃ₜ range f := hf.isEmbedding.toHomeomorph
  have hfg : f = (ContinuousMap.subtypeVal (range f)).comp (g : C(Y, range f)) := by
    ext y; rfl
  rw [hfg, ← postcomp_comp] at h
  have h1 := IsRelBoundary.of_postcomp_subtypeVal hf.isOpen_range hL hLf h
  have h2 := isRelBoundary_postcomp (g.symm : C(range f, Y)) (L := f ⁻¹' L) (fun v hv ↦ by
    have hv' : f (g.symm v) ∈ L := hv
    have : f (g.symm v) = v := congrArg Subtype.val (g.apply_symm_apply v)
    rw [this] at hv'
    exact hv') h1
  rwa [postcomp_comp, show (g.symm : C(range f, Y)).comp (g : C(Y, range f)) =
    ContinuousMap.id Y by ext; simp, postcomp_id] at h2

/-- A relative cycle of `(Y, Y - K)` for `K ⊆ U` closed and `U` open is homologous rel `K` to
(the push-forward of) a relative cycle of `(U, U - K)`. -/
theorem exists_isRelBoundary_sub_postcomp_subtypeVal {m : ℕ} {U K : Set Y} (hU : IsOpen U)
    (hK : IsClosed K) (hKU : K ⊆ U) {c : Chain R Y (m + 1)} (hc : bd R m c ∈ inside R m Kᶜ) :
    ∃ c' : Chain R U (m + 1),
      IsRelBoundary R (m + 1) K (c - postcomp R (ContinuousMap.subtypeVal U) (m + 1) c') ∧
      bd R m c' ∈ inside R m ((↑) ⁻¹' K : Set U)ᶜ := by
  set ι := ContinuousMap.subtypeVal U
  set 𝒰 : Set (Set Y) := {U, Kᶜ}
  have h𝒰 : ∀ V ∈ 𝒰, IsOpen V := by
    rintro V (rfl | rfl)
    · exact hU
    · exact hK.isOpen_compl
  have hcov : c ∈ inside R (m + 1) (⋃₀ 𝒰) := by
    have : ⋃₀ 𝒰 = univ := by
      simp only [𝒰, sUnion_insert, sUnion_singleton]
      exact eq_univ_of_forall fun y ↦ (em (y ∈ K)).imp (fun h ↦ hKU h) id
    rw [this]
    exact mem_inside_univ c
  obtain ⟨a, ha, b, hb, hsplit⟩ :=
    exists_add_of_mem_small_pair (smallChainMap_mem_small h𝒰 (m + 1) hcov)
  rw [smallChainMap_succ] at hsplit
  have hDbd : smallHomotopy R 𝒰 m (bd R m c) ∈ inside R (m + 1) Kᶜ :=
    smallHomotopy_mem_inside_of_mem 𝒰 hc
  have hbda : bd R m a ∈ inside R m Kᶜ := by
    have : bd R m a = bd R m c - bd R m (smallHomotopy R 𝒰 m (bd R m c)) - bd R m b := by
      have := congrArg (bd R m) hsplit
      rw [map_sub, map_sub, bd_bd, sub_zero, map_add] at this
      rw [this]; abel
    rw [this]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ hc (bd_mem_inside hDbd)) (bd_mem_inside hb)
  obtain ⟨a', rfl⟩ := exists_postcomp_subtypeVal_eq ha
  have hbda' : bd R m a' ∈ inside R m ((↑) ⁻¹' K : Set U)ᶜ := by
    rw [← postcomp_bd] at hbda
    exact mem_inside_preimage_of_postcomp_mem_inside Subtype.val_injective hbda
  refine ⟨a', ⟨smallHomotopy R 𝒰 (m + 1) c, ?_⟩, hbda'⟩
  have : c - postcomp R ι (m + 1) a' - bd R (m + 1) (smallHomotopy R 𝒰 (m + 1) c) =
      b + smallHomotopy R 𝒰 m (bd R m c) := by
    generalize postcomp R ι (m + 1) a' = A at hsplit ⊢
    generalize bd R (m + 1) (smallHomotopy R 𝒰 (m + 1) c) = P at hsplit ⊢
    generalize smallHomotopy R 𝒰 m (bd R m c) = Q at hsplit ⊢
    have hA : A = c - P - Q - b := by rw [hsplit]; abel
    rw [hA]; abel
  rw [this]
  exact Submodule.add_mem _ hb hDbd

/-- Local injectivity transported back along an open embedding `F : V → W`: if it holds in
`W` for compact sets, it holds in `V` for compact sets. -/
theorem isRelBoundary_of_isOpenEmbedding {V W : Type*} [TopologicalSpace V] [TopologicalSpace W]
    [T2Space W] {m : ℕ} {F : C(V, W)} (hF : IsOpenEmbedding F)
    (hW : ∀ L : Set W, IsCompact L → ∀ c : Chain R W (m + 1),
      bd R m c ∈ inside R m Lᶜ → (∀ y ∈ L, IsRelBoundary R (m + 1) {y} c) →
        IsRelBoundary R (m + 1) L c)
    {K : Set V} (hK : IsCompact K) {c : Chain R V (m + 1)} (hc : bd R m c ∈ inside R m Kᶜ)
    (hloc : ∀ x ∈ K, IsRelBoundary R (m + 1) {x} c) : IsRelBoundary R (m + 1) K c := by
  have hL : IsCompact (F '' K) := hK.image F.continuous
  have hpre : F ⁻¹' (F '' K) ⊆ K := (hF.injective.preimage_image K).subset
  have hbdL : bd R m (postcomp R F (m + 1) c) ∈ inside R m (F '' K)ᶜ := by
    rw [← postcomp_bd]
    exact postcomp_mem_inside F (U := Kᶜ) (V := (F '' K)ᶜ)
      (fun x (hx : x ∈ Kᶜ) ↦ show F x ∈ (F '' K)ᶜ from fun hFx ↦ hx (hpre hFx)) hc
  have hlocL : ∀ y ∈ F '' K, IsRelBoundary R (m + 1) {y} (postcomp R F (m + 1) c) := by
    rintro _ ⟨x, hx, rfl⟩
    exact isRelBoundary_postcomp F (K := ({x} : Set V)) (L := ({F x} : Set W))
      (fun z (hz : F z = F x) ↦ (hF.injective hz : z = x))
      (hloc x hx)
  have := IsRelBoundary.of_postcomp_isOpenEmbedding hF hL.isClosed (image_subset_range _ _)
    (hW _ hL _ hbdL hlocL)
  rwa [hF.injective.preimage_image] at this

end transport

section manifold

variable {H : Type*} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H]
  [ContinuousAdd H] [ContinuousSMul ℝ H] [T2Space H]

/-- **Local injectivity in the top degree inside a chart**, from the case of `ℝⁿ`: for `K`
compact inside the source of a chart `e : Y → H ≅ ℝⁿ`, a relative cycle of `(Y, Y - K)` that is
a relative boundary for every point of `K` is a relative boundary for `K`. -/
theorem isRelBoundary_of_subset_source [T2Space Y] {n n' : ℕ} (b : Module.Basis (Fin n) ℝ H)
    (heucl : ∀ K : Set (Fin n → ℝ), IsCompact K → ∀ c : Chain R (Fin n → ℝ) (n' + 1),
      bd R n' c ∈ inside R n' Kᶜ → (∀ x ∈ K, IsRelBoundary R (n' + 1) {x} c) →
        IsRelBoundary R (n' + 1) K c)
    (e : OpenPartialHomeomorph Y H) {K : Set Y} (hK : IsCompact K) (hKs : K ⊆ e.source)
    {c : Chain R Y (n' + 1)} (hc : bd R n' c ∈ inside R n' Kᶜ)
    (hloc : ∀ x ∈ K, IsRelBoundary R (n' + 1) {x} c) : IsRelBoundary R (n' + 1) K c := by
  set ι := ContinuousMap.subtypeVal e.source
  obtain ⟨c₁, hc₁, hbd₁⟩ :=
    exists_isRelBoundary_sub_postcomp_subtypeVal e.open_source hK.isClosed hKs hc
  -- the local hypotheses for the chain `c₁` of the chart source
  have hloc₁ : ∀ x : e.source, (x : Y) ∈ K → IsRelBoundary R (n' + 1) {x} c₁ := by
    intro x hx
    have h1 : IsRelBoundary R (n' + 1) {(x : Y)} (postcomp R ι (n' + 1) c₁) := by
      have := (hloc x hx).sub (hc₁.mono (singleton_subset_iff.2 hx))
      rwa [sub_sub_cancel] at this
    have h2 := IsRelBoundary.of_postcomp_subtypeVal e.open_source isClosed_singleton
      (singleton_subset_iff.2 x.2) h1
    convert h2 using 1
    ext y
    simp [Subtype.ext_iff]
  -- the open embedding of the chart source into `ℝⁿ`
  obtain ⟨F, hF⟩ : ∃ F : C(e.source, Fin n → ℝ), IsOpenEmbedding F :=
    ⟨((basisHomeomorph b : C(H, Fin n → ℝ)).comp (ContinuousMap.subtypeVal e.target)).comp
      (e.toHomeomorphSourceTarget : C(e.source, e.target)),
      ((basisHomeomorph b).isOpenEmbedding.comp e.open_target.isOpenEmbedding_subtypeVal).comp
        e.toHomeomorphSourceTarget.isOpenEmbedding⟩
  have hK₁ : IsCompact ((↑) ⁻¹' K : Set e.source) := by
    rw [IsInducing.subtypeVal.isCompact_iff, Subtype.image_preimage_coe,
      inter_eq_right.2 hKs]
    exact hK
  have hback : IsRelBoundary R (n' + 1) ((↑) ⁻¹' K : Set e.source) c₁ :=
    isRelBoundary_of_isOpenEmbedding hF heucl hK₁ hbd₁ fun x hx ↦ hloc₁ x hx
  have hY : IsRelBoundary R (n' + 1) K (postcomp R ι (n' + 1) c₁) :=
    isRelBoundary_postcomp_subtypeVal hback
  have := hc₁.add hY
  rwa [sub_add_cancel] at this

/-- **Hatcher, Lemma 3.27(b), top degree, on a manifold, from the case of `ℝⁿ`.** Let `Y` be a
locally compact Hausdorff space modelled on `H ≅ ℝⁿ` and `n ≤ n' + 1`. If on `ℝⁿ` every relative
cycle of `(ℝⁿ, ℝⁿ - K)` in degree `n' + 1` (for `K` compact) that is a relative boundary for
each point of `K` is a relative boundary for `K`, then the same holds on `Y`. -/
theorem isRelBoundary_of_isCompact_of_chartedSpace [T2Space Y] [LocallyCompactSpace Y]
    [ChartedSpace H Y] {n n' : ℕ} (b : Module.Basis (Fin n) ℝ H) (hn : n ≤ n' + 1)
    (heucl : ∀ K : Set (Fin n → ℝ), IsCompact K → ∀ c : Chain R (Fin n → ℝ) (n' + 1),
      bd R n' c ∈ inside R n' Kᶜ → (∀ x ∈ K, IsRelBoundary R (n' + 1) {x} c) →
        IsRelBoundary R (n' + 1) K c)
    {K : Set Y} (hK : IsCompact K) {c : Chain R Y (n' + 1)} (hc : bd R n' c ∈ inside R n' Kᶜ)
    (hloc : ∀ x ∈ K, IsRelBoundary R (n' + 1) {x} c) : IsRelBoundary R (n' + 1) K c := by
  classical
  have hvan : ∀ A : Set Y, IsCompact A → RelVanishing R Y (n' + 1) A := fun A hA ↦
    relVanishing_of_isCompact_of_chartedSpace b
      (fun a c k hk ↦ relVanishing_Icc (fun n hn j hj ↦ cycleVanishing_compl_zero n hn j hj)
        _ a c k hk) hA (n' + 1) hn
  have hC : ∀ x : Y, ∃ C : Set Y, IsCompact C ∧ C ∈ 𝓝 x ∧ C ⊆ (chartAt H x).source :=
    fun x ↦ by
      obtain ⟨C, hC, hxC, hCU⟩ :=
        exists_compact_subset (chartAt H x).open_source (mem_chart_source H x)
      exact ⟨C, hC, mem_interior_iff_mem_nhds.1 hxC, hCU⟩
  choose C hCc hCn hCU using hC
  obtain ⟨t, -, hcov⟩ := hK.elim_nhds_subcover C fun x _ ↦ hCn x
  have hKC : ∀ x, IsCompact (K ∩ C x) := fun x ↦ hK.inter_right (hCc x).isClosed
  have hpiece : ∀ x, IsRelBoundary R (n' + 1) (K ∩ C x) c := fun x ↦
    isRelBoundary_of_subset_source b heucl (chartAt H x) (hKC x)
      (inter_subset_right.trans (hCU x))
      (inside_mono n' (compl_subset_compl.2 inter_subset_left) hc) (fun y hy ↦ hloc y hy.1)
  have hunion : ∀ s : Finset Y, IsCompact (⋃ x ∈ s, K ∩ C x) ∧
      IsRelBoundary R (n' + 1) (⋃ x ∈ s, K ∩ C x) c := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty]
      exact ⟨isCompact_empty, isRelBoundary_of_mem_inside (by
        rw [compl_empty]; exact mem_inside_univ c)⟩
    · intro a s _ ih
      rw [Finset.set_biUnion_insert]
      exact ⟨(hKC a).union ih.1, isRelBoundary_union (hKC a).isClosed ih.1.isClosed
        (hvan _ ((hKC a).inter_right ih.1.isClosed)) (hpiece a) ih.2⟩
  refine (hunion t).2.mono fun y hy ↦ ?_
  obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 (hcov hy)
  exact mem_iUnion₂.2 ⟨x, hx, hy, hyx⟩

/-- **Hatcher, Lemma 3.27(b), top degree, on a manifold.** On a locally compact Hausdorff space
`Y` modelled on `H ≅ ℝⁿ`, a chain `c` of degree `n' + 1 ≥ n` whose boundary lies in `Y - K`, `K`
compact, and which is a relative boundary for every point of `K`, is a relative boundary for
`K`: the map `H_{n'+1}(Y, Y - K) → ∏_{x ∈ K} H_{n'+1}(Y, Y - x)` is injective. -/
theorem isRelBoundary_of_isCompact_of_forall_mem [T2Space Y] [LocallyCompactSpace Y]
    [ChartedSpace H Y] {n n' : ℕ} (b : Module.Basis (Fin n) ℝ H) (hn : n ≤ n' + 1)
    {K : Set Y} (hK : IsCompact K) {c : Chain R Y (n' + 1)} (hc : bd R n' c ∈ inside R n' Kᶜ)
    (hloc : ∀ x ∈ K, IsRelBoundary R (n' + 1) {x} c) : IsRelBoundary R (n' + 1) K c :=
  isRelBoundary_of_isCompact_of_chartedSpace b hn
    (fun _ hK' _ hc' hloc' ↦ isRelBoundary_of_isCompact hn hK' hc' hloc') hK hc hloc

end manifold

end SingularChain

end MMP
