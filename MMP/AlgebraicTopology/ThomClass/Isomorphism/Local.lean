module

public import MMP.AlgebraicTopology.ThomClass.Isomorphism.Product

/-!
# Generic steps of Thom's theorem: subspaces, fibre generators, Mayer–Vietoris for freeness

* Transfer of relative-homology vanishing and generation from a subspace `S` (as a space) to the
  chains of the ambient space lying in `S`.
* In `W × (ℝⁿ, ℝⁿ - 0)`, `n ≥ 1`, the fibrewise relative cycles are, up to relative boundaries,
  combinations of the oriented simplices `{x} × Δₙ`
  (`MMP.SingularChain.relHomologyGenerated_prod_localGenerator`).
* `AugFree S A k Γ`: a combination of simplices of `Γ` in `S` that is a relative boundary of
  `(S, S ∩ A)` has coefficient sum `0`; the Mayer–Vietoris step for this property.

## References

* [J. Milnor, J. Stasheff, *Characteristic classes*][milnorstasheff1974], §10.
-/

@[expose] public noncomputable section

open Finsupp Set

namespace MMP

namespace SingularChain

variable {R : Type*} [CommRing R] {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]

section subtype

variable (S : Set Y)

/-- The inclusion of a subspace, as a continuous map. -/
def subtypeValMap : C(S, Y) := ⟨Subtype.val, continuous_subtype_val⟩

variable {S}

/-- Two maps agreeing on `T` have the same pushforward on chains lying in `T`. -/
lemma postcomp_eq_of_eqOn {f g : C(Y, Z)} {T : Set Y} (hfg : EqOn f g T) {k : ℕ}
    {c : Chain R Y k} (hc : c ∈ inside R k T) : postcomp R f k c = postcomp R g k c := by
  simp only [postcomp, lmapDomain_apply]
  refine Finsupp.mapDomain_congr fun σ hσ ↦ ContinuousMap.ext fun t ↦ ?_
  exact hfg ((mem_supported R c).1 hc hσ ⟨t, rfl⟩)

/-- A chain of `Y` lying in `S` is the image of a chain of the subspace `S`. -/
lemma exists_postcomp_subtypeValMap_eq {k : ℕ} {c : Chain R Y k} (hc : c ∈ inside R k S) :
    ∃ c' : Chain R S k, postcomp R (subtypeValMap S) k c' = c := by
  classical
  induction c using Finsupp.induction with
  | zero => exact ⟨0, map_zero _⟩
  | single_add σ a f hσ ha ih =>
    have hsupp : (single σ a + f).support = insert σ f.support := by
      rw [Finsupp.support_add_eq (by simpa [Finsupp.support_single_ne_zero _ ha] using hσ),
        Finsupp.support_single_ne_zero _ ha]
      rfl
    have hmem : ∀ τ ∈ (single σ a + f).support, range τ ⊆ S := fun τ hτ ↦
      (mem_supported R _).1 hc hτ
    obtain ⟨f', hf'⟩ := ih ((mem_supported R f).2 fun τ hτ ↦
      hmem τ (by rw [hsupp]; exact Finset.mem_insert_of_mem hτ))
    have hσS : ∀ t, σ t ∈ S := fun t ↦ hmem σ (by rw [hsupp]; exact Finset.mem_insert_self _ _)
      ⟨t, rfl⟩
    refine ⟨single ⟨fun t ↦ ⟨σ t, hσS t⟩, σ.continuous.subtype_mk _⟩ a + f', ?_⟩
    rw [map_add, hf', postcomp_single]
    rfl

/-- A chain of the subspace `S` whose image lies in `T` lies in the preimage of `T`. -/
lemma mem_inside_preimage_of_postcomp {k : ℕ} {c : Chain R S k} {T : Set Y}
    (hc : postcomp R (subtypeValMap S) k c ∈ inside R k T) :
    c ∈ inside R k (Subtype.val ⁻¹' T) := by
  classical
  refine (mem_supported R c).2 fun σ hσ ↦ ?_
  have hinj : Function.Injective fun σ : Simplex S k ↦ (subtypeValMap S).comp σ :=
    fun σ τ h ↦ ContinuousMap.ext fun t ↦ Subtype.ext (DFunLike.congr_fun h t)
  have : (subtypeValMap S).comp σ ∈ (postcomp R (subtypeValMap S) k c).support := by
    rw [postcomp, lmapDomain_apply, Finsupp.mapDomain_support_of_injective hinj]
    exact Finset.mem_image_of_mem _ hσ
  rintro _ ⟨t, rfl⟩
  exact (mem_supported R _).1 hc this ⟨t, rfl⟩

/-- A chain of the subspace `S` whose image is a relative cycle of `(Y, A)` is a relative cycle
of `(S, S ∩ A)`. -/
lemma mem_relativeCycles_preimage_of_postcomp {k : ℕ} {c : Chain R S k} {A : Set Y}
    (hc : postcomp R (subtypeValMap S) k c ∈ relativeCycles R A k) :
    c ∈ relativeCycles R (Subtype.val ⁻¹' A) k := by
  cases k with
  | zero => trivial
  | succ k =>
    rw [mem_relativeCycles_succ] at hc ⊢
    rw [← postcomp_bd] at hc
    exact mem_inside_preimage_of_postcomp hc

/-- **Vanishing on a subspace gives vanishing for the chains in it.** -/
theorem RelHomologyVanishing.of_subtype {A : Set Y} {k : ℕ}
    (h : RelHomologyVanishing R (univ : Set S) (Subtype.val ⁻¹' A) k) :
    RelHomologyVanishing R S A k := fun c hc hcz ↦ by
  obtain ⟨c', rfl⟩ := exists_postcomp_subtypeValMap_eq hc
  exact IsRelBoundaryIn.map (subtypeValMap S) (fun p _ ↦ p.2) (fun p hp ↦ ⟨p.2, hp.2⟩)
    (h c' (mem_inside_univ _) (mem_relativeCycles_preimage_of_postcomp hcz))

/-- **Generation on a subspace gives generation for the chains in it.** -/
theorem RelHomologyGenerated.of_subtype {A : Set Y} {k : ℕ} {G : Submodule R (Chain R S k)}
    {G' : Submodule R (Chain R Y k)} (hG : G.map (postcomp R (subtypeValMap S) k) ≤ G')
    (h : RelHomologyGenerated R (univ : Set S) (Subtype.val ⁻¹' A) k G) :
    RelHomologyGenerated R S A k G' := fun c hc hcz ↦ by
  obtain ⟨c', rfl⟩ := exists_postcomp_subtypeValMap_eq hc
  obtain ⟨g, hg, hcg⟩ := h c' (mem_inside_univ _) (mem_relativeCycles_preimage_of_postcomp hcz)
  refine ⟨_, hG ⟨g, hg, rfl⟩, ?_⟩
  rw [← map_sub]
  exact IsRelBoundaryIn.map (subtypeValMap S) (fun p _ ↦ p.2) (fun p hp ↦ ⟨p.2, hp.2⟩) hcg

end subtype

section localGenerator

variable {W : Type*} [TopologicalSpace W]

/-- The fibre inclusion `z ↦ (x, z)`. -/
def fibreInclusion (x : W) (n : ℕ) : C(Fin n → ℝ, W × (Fin n → ℝ)) :=
  ⟨fun z ↦ (x, z), continuous_const.prodMk continuous_id⟩

variable (R W) in
/-- The combinations of the oriented simplices `{x} × Δₙ`. -/
def localFibreGenerators (n : ℕ) : Submodule R (Chain R (W × (Fin n → ℝ)) n) :=
  Submodule.span R (range fun x : W ↦ single ((fibreInclusion x n).comp (localGenerator n)) 1)

/-- A relative cycle of `W × (ℝⁿ, ℝⁿ - 0)` in one fibre is, up to a relative boundary, a multiple
of `{x} × Δₙ` (`n ≥ 1`). -/
lemma exists_localFibreGenerators_of_mem_fibreCycles (m : ℕ)
    {f : Chain R (W × (Fin (m + 1) → ℝ)) (m + 1)}
    (hf : f ∈ fibreCycles R Prod.fst univ (punctured W (m + 1)) (m + 1)) :
    ∃ g ∈ localFibreGenerators R W (m + 1),
      IsRelBoundaryIn R univ (punctured W (m + 1)) (m + 1) (f - g) := by
  induction hf using Submodule.iSup_induction' with
  | mem x f hfx =>
    obtain ⟨hfx, hfxz⟩ := hfx
    rw [univ_inter] at hfx
    have hid : postcomp R ((fibreInclusion x (m + 1)).comp ContinuousMap.snd) (m + 1) f = f := by
      refine (postcomp_eq_of_eqOn (g := ContinuousMap.id _) (fun p hp ↦ ?_) hfx).trans
        (postcomp_id _ _)
      obtain ⟨p1, p2⟩ := p
      change ((x, p2) : W × _) = (p1, p2)
      rw [show p1 = x from hp]
    have hc : bd R m (postcomp R ContinuousMap.snd (m + 1) f) ∈
        inside R m ({0}ᶜ : Set (Fin (m + 1) → ℝ)) := by
      rw [← postcomp_bd]
      exact postcomp_mem_inside _ (fun p hp ↦ hp) (mem_relativeCycles_succ.1 hfxz)
    obtain ⟨r, w, hw⟩ := exists_sub_smul_localGenerator_mem (R := R) m _ hc
    refine ⟨r • single ((fibreInclusion x (m + 1)).comp (localGenerator (m + 1))) 1,
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩), ?_⟩
    refine ⟨postcomp R (fibreInclusion x (m + 1)) (m + 2) w, mem_inside_univ _, ?_⟩
    rw [univ_inter]
    have := postcomp_mem_inside (R := R) (fibreInclusion x (m + 1))
      (V := punctured W (m + 1)) (fun z hz ↦ hz) hw
    rw [map_sub, map_sub, map_smul, postcomp_single, postcomp_comp, hid, postcomp_bd]
      at this
    exact this
  | zero => exact ⟨0, Submodule.zero_mem _, by rw [sub_zero]; exact isRelBoundaryIn_zero⟩
  | add f₁ f₂ _ _ h₁ h₂ =>
    obtain ⟨g₁, hg₁, h₁⟩ := h₁
    obtain ⟨g₂, hg₂, h₂⟩ := h₂
    refine ⟨g₁ + g₂, Submodule.add_mem _ hg₁ hg₂, ?_⟩
    convert h₁.add h₂ using 1
    abel

/-- **`H_n(W × ℝⁿ, W × (ℝⁿ - 0); R)`, `n ≥ 1`, is generated by the simplices `{x} × Δₙ`.** -/
theorem relHomologyGenerated_prod_localGenerator (m : ℕ) :
    RelHomologyGenerated R (univ : Set (W × (Fin (m + 1) → ℝ))) (punctured W (m + 1)) (m + 1)
      (localFibreGenerators R W (m + 1)) := fun c hc hcz ↦ by
  obtain ⟨f, hf, hcf⟩ := relHomologyGenerated_prod_punctured (R := R) (W := W) (m + 1) c hc hcz
  obtain ⟨g, hg, hfg⟩ := exists_localFibreGenerators_of_mem_fibreCycles m hf
  refine ⟨g, hg, ?_⟩
  convert hcf.add hfg using 1
  abel

end localGenerator

section augFree

variable (R) in
/-- The combinations of simplices of `Γ` lying in `S`. -/
abbrev spanIn {k : ℕ} (Γ : Set (Simplex Y k)) (S : Set Y) : Submodule R (Chain R Y k) :=
  supported R R (Γ ∩ {σ | range σ ⊆ S})

/-- `spanIn R Γ S` is monotone in `S`. -/
lemma spanIn_mono {k : ℕ} {Γ : Set (Simplex Y k)} {S S' : Set Y} (h : S ⊆ S') :
    spanIn R Γ S ≤ spanIn R Γ S' :=
  supported_mono fun _ hσ ↦ ⟨hσ.1, hσ.2.trans h⟩

/-- Combinations of simplices of `Γ` in `S` are chains lying in `S`. -/
lemma spanIn_le_inside {k : ℕ} {Γ : Set (Simplex Y k)} {S : Set Y} :
    spanIn R Γ S ≤ inside R k S :=
  supported_mono fun _ hσ ↦ hσ.2

variable (R) in
/-- A combination of simplices of `Γ` in `S` which is a relative boundary of `(S, S ∩ A)` has
coefficient sum `0`. -/
def AugFree (S A : Set Y) (k : ℕ) (Γ : Set (Simplex Y k)) : Prop :=
  ∀ g ∈ spanIn R Γ S, IsRelBoundaryIn R S A k g → aug R k g = 0

/-- `AugFree` holds for the empty subspace. -/
lemma augFree_empty {A : Set Y} {k : ℕ} (Γ : Set (Simplex Y k)) :
    AugFree R (∅ : Set Y) A k Γ := fun g hg _ ↦ by
  rw [eq_zero_of_mem_inside_empty (spanIn_le_inside hg), map_zero]

/-- The boundary of a chain subordinate to the cover `𝒰` is subordinate to `𝒰`. -/
lemma bd_mem_small {𝒰 : Set (Set Y)} {k : ℕ} {c : Chain R Y (k + 1)} (hc : c ∈ small R (k + 1) 𝒰) :
    bd R k c ∈ small R k 𝒰 := by
  refine VertexChain.mem_of_mem_supported (bd R k) (small R k 𝒰) (fun σ hσ ↦ ?_) hc
  rw [bd_single]
  obtain ⟨U, hU, hσU⟩ := hσ
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _
    (single_mem_supported R _ ⟨U, hU, by rw [ContinuousMap.coe_comp]; exact (Set.range_comp_subset_range _ _).trans hσU⟩)

/-- The subdivision `ρ` fixes chains whose simplices each lie in a member of the cover. -/
lemma smallChainMap_eq_self_of_mem_small' {𝒰 : Set (Set Y)} {k : ℕ} {c : Chain R Y k}
    (hc : c ∈ small R k 𝒰) : smallChainMap R 𝒰 k c = c := by
  cases k with
  | zero => rw [smallChainMap_zero, smallHomotopy_eq_zero_of_mem_small hc, map_zero, sub_zero]
  | succ k => exact smallChainMap_eq_self_of_mem_small hc (bd_mem_small hc)

/-- A combination of simplices of `Γ` in `U ∪ V`, each lying in `U` or in `V`, splits. -/
lemma exists_add_of_mem_spanIn_union {k : ℕ} {Γ : Set (Simplex Y k)} {U V : Set Y}
    (hΓ : ∀ σ ∈ Γ, range σ ⊆ U ∪ V → range σ ⊆ U ∨ range σ ⊆ V) {g : Chain R Y k}
    (hg : g ∈ spanIn R Γ (U ∪ V)) :
    ∃ gU ∈ spanIn R Γ U, ∃ gV ∈ spanIn R Γ V, g = gU + gV := by
  classical
  refine ⟨g.filter (fun σ ↦ range σ ⊆ U), ?_, g.filter (fun σ ↦ ¬ range σ ⊆ U), ?_,
    (filter_pos_add_filter_neg g _).symm⟩
  · rw [mem_supported, support_filter, Finset.coe_filter]
    exact fun σ hσ ↦ ⟨((mem_supported R g).1 hg hσ.1).1, hσ.2⟩
  · rw [mem_supported, support_filter, Finset.coe_filter]
    rintro σ ⟨hσ, hσU⟩
    have h := (mem_supported R g).1 hg hσ
    exact ⟨h.1, (hΓ σ h.1 h.2).resolve_left hσU⟩

/-- **The Mayer–Vietoris step for freeness of the coefficient sum.** For `U`, `V` open, if every
simplex of `Γ` in `U ∪ V` lies in `U` or in `V`, the simplices of `Γ` are relative cycles, and
`H_k(U ∩ V, U ∩ V ∩ A)` is generated by the simplices of `Γ` in `U ∩ V`, then `AugFree` passes
from `U` and `V` to `U ∪ V`. -/
theorem AugFree.union {A U V : Set Y} {k : ℕ} {Γ : Set (Simplex Y k)} (hU : IsOpen U)
    (hV : IsOpen V) (hΓ : ∀ σ ∈ Γ, range σ ⊆ U ∪ V → range σ ⊆ U ∨ range σ ⊆ V)
    (hΓz : ∀ σ ∈ Γ, single σ (1 : R) ∈ relativeCycles R A k)
    (hUa : AugFree R U A k Γ) (hVa : AugFree R V A k Γ)
    (hUV : RelHomologyGenerated R (U ∩ V) A k (spanIn R Γ (U ∩ V))) :
    AugFree R (U ∪ V) A k Γ := by
  rintro g hg ⟨w, hw, hgw⟩
  set 𝒰 : Set (Set Y) := {U, V}
  have h𝒰 := isOpen_pair hU hV
  have hgs : g ∈ small R k 𝒰 := supported_mono (fun σ hσ ↦ by
    rcases hΓ σ hσ.1 hσ.2 with h | h
    · exact ⟨U, by simp [𝒰], h⟩
    · exact ⟨V, by simp [𝒰], h⟩) hg
  have hρ : smallChainMap R 𝒰 k (g - bd R k w) = g - bd R k (smallChainMap R 𝒰 (k + 1) w) := by
    rw [map_sub, smallChainMap_eq_self_of_mem_small' hgs, bd_smallChainMap]
  obtain ⟨eU, heU, eV, heV, he⟩ := exists_add_of_mem_small_pair_inter (A := A)
    (smallChainMap_mem_small h𝒰 k (mem_inside_sUnion_pair'
      (Submodule.sub_mem _ (spanIn_le_inside hg) (bd_mem_inside hw))))
    (smallChainMap_mem_inside 𝒰 k (inside_mono _ inter_subset_right hgw))
  obtain ⟨wU, hwU, wV, hwV, hwe⟩ := exists_add_of_mem_small_pair
    (smallChainMap_mem_small h𝒰 (k + 1) (mem_inside_sUnion_pair' hw))
  obtain ⟨gU, hgU, gV, hgV, rfl⟩ := exists_add_of_mem_spanIn_union hΓ hg
  rw [hρ, hwe, map_add] at he
  -- `z = g_U - ∂ w_U - e_U = -(g_V - ∂ w_V - e_V)` lies in `U ∩ V`
  have hz : gU - bd R k wU - eU = -(gV - bd R k wV - eV) := by
    rw [eq_neg_iff_add_eq_zero]
    rw [show gU - bd R k wU - eU + (gV - bd R k wV - eV) =
      (gU + gV - (bd R k wU + bd R k wV)) - (eU + eV) by abel, he, sub_self]
  have heU' := inside_mono (R := R) (n := k) inter_subset_left heU
  have heV' := inside_mono (R := R) (n := k) inter_subset_left heV
  have hzUV : gU - bd R k wU - eU ∈ inside R k (U ∩ V) := by
    rw [inside_inter]
    refine ⟨Submodule.sub_mem _ (Submodule.sub_mem _ (spanIn_le_inside hgU)
      (bd_mem_inside hwU)) heU', ?_⟩
    rw [hz]
    exact Submodule.neg_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _ (spanIn_le_inside hgV)
      (bd_mem_inside hwV)) heV')
  have hspan : ∀ {S : Set Y} {c : Chain R Y k}, c ∈ spanIn R Γ S → c ∈ relativeCycles R A k := by
    intro S c hc
    rw [spanIn, supported_eq_span_single] at hc
    refine Submodule.span_le.2 ?_ hc
    rintro _ ⟨σ, hσ, rfl⟩
    exact hΓz σ hσ.1
  have hzz : gU - bd R k wU - eU ∈ relativeCycles R A k :=
    Submodule.sub_mem _ (Submodule.sub_mem _ (hspan hgU) (bd_mem_relativeCycles k wU))
      (inside_le_relativeCycles k (inside_mono _ inter_subset_right heU))
  obtain ⟨h, hh, y, hy, hzhy⟩ := hUV _ hzUV hzz
  rw [inside_inter] at hy
  have hzhyU : gU - bd R k wU - eU - h - bd R k y ∈ inside R k (U ∩ A) :=
    inside_mono _ (show U ∩ V ∩ A ⊆ U ∩ A from fun p hp ↦ ⟨hp.1.1, hp.2⟩) hzhy
  have hzhyV : gU - bd R k wU - eU - h - bd R k y ∈ inside R k (V ∩ A) :=
    inside_mono _ (show U ∩ V ∩ A ⊆ V ∩ A from fun p hp ↦ ⟨hp.1.2, hp.2⟩) hzhy
  have h1 : aug R k (gU - h) = 0 := by
    refine hUa _ (Submodule.sub_mem _ hgU (spanIn_mono inter_subset_left hh))
      ⟨wU + y, Submodule.add_mem _ hwU hy.1, ?_⟩
    convert Submodule.add_mem _ heU hzhyU using 1
    rw [map_add]
    abel
  have h2 : aug R k (gV + h) = 0 := by
    refine hVa _ (Submodule.add_mem _ hgV (spanIn_mono inter_subset_right hh))
      ⟨wV - y, Submodule.sub_mem _ hwV hy.2, ?_⟩
    have hgV' : gV = -(gU - bd R k wU - eU) + bd R k wV + eV := by
      rw [hz]; abel
    convert Submodule.sub_mem _ heV hzhyV using 1
    rw [hgV', map_sub]
    abel
  rw [map_sub] at h1
  rw [map_add] at h2
  rw [map_add]
  linear_combination h1 + h2

end augFree

end SingularChain

end MMP
