module

public import MMP.AlgebraicTopology.PoincareDuality.Excision

/-!
# Localizing the vanishing of singular homology

Two chain-level tools for Hatcher's Lemma 3.27, in the finite chain model of
`MMP.AlgebraicTopology.SingularHomology.Excision.SmallChains`.

* Converse excision: for `U ⊆ Y` open and `K ⊆ U` closed in `Y`, the vanishing of
  `H_{m+1}(Y, Y - K; R)` gives the vanishing of `H_{m+1}(U, U - K; R)`. A chain `c` of `U`
  with boundary in `U - K` is pushed to `Y`, where `c = ∂ w + f` with `f` in `Y - K`; the theorem
  of small chains for the cover `{U, Y - K}` splits `ρ w` into a part in `U` and a part in
  `Y - K`, and the part in `U` together with `D c` lifts back to `U`.
* Absolute homology `H_{m+1}(A; R)` computed with chains of `Y` lying in `A`
  (`CycleVanishing`), its Mayer–Vietoris step for open `U`, `V`, and its transport along
  homeomorphisms and between a subspace and the chains of `Y` inside it.

## Main definitions

* `MMP.SingularChain.IsBoundaryIn`: boundaries of chains lying in `A`.
* `MMP.SingularChain.CycleVanishing`: `H_{m+1}(A; R) = 0`.

## Main results

* `MMP.SingularChain.RelVanishing.subtype`: converse excision.
* `MMP.SingularChain.CycleVanishing.union`: Mayer–Vietoris for the vanishing.
* `MMP.SingularChain.CycleVanishing.of_homeomorph`: transport along `Y ≃ₜ Z`.
* `MMP.SingularChain.cycleVanishing_univ_subtype_iff`: subspace chains versus
  chains of `Y` inside `A`.
* `MMP.SingularChain.cycleVanishing_univ_iff_range`: transport along an embedding.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002], §2.1, Prop. 2.21 and §3.3, Lemma 3.27.
-/

@[expose] public noncomputable section

open Finsupp Set

namespace MMP

namespace SingularChain

variable {R : Type*} [CommRing R] {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]

section postcomp

/-- Push-forward of chains along an injective map is injective. -/
lemma postcomp_injective {f : C(Y, Z)} (hf : Function.Injective f) (n : ℕ) :
    Function.Injective (postcomp R f n) := by
  have hinj : Function.Injective fun σ : Simplex Y n ↦ f.comp σ := fun σ τ h ↦
    ContinuousMap.ext fun t ↦ hf (DFunLike.congr_fun h t)
  intro c d h
  simp only [postcomp, lmapDomain_apply] at h
  exact mapDomain_injective hinj h

end postcomp

section converseExcision

/-- Converse excision: for `U` open and `K ⊆ U` closed in `Y`, the vanishing of
`H_{m+1}(Y, Y - K)` gives the vanishing of `H_{m+1}(U, U - K)`. -/
theorem RelVanishing.subtype {m : ℕ} {U K : Set Y} (hU : IsOpen U) (hK : IsClosed K)
    (hKU : K ⊆ U) (h : RelVanishing R Y m K) : RelVanishing R U m ((↑) ⁻¹' K) := by
  intro c hc
  set ι := ContinuousMap.subtypeVal U
  set 𝒰 : Set (Set Y) := {U, Kᶜ}
  have h𝒰 : ∀ V ∈ 𝒰, IsOpen V := by
    rintro V (rfl | rfl)
    · exact hU
    · exact hK.isOpen_compl
  have hcY : postcomp R ι (m + 1) c ∈ inside R (m + 1) U :=
    postcomp_mem_inside ι (U := univ) (fun x _ ↦ x.2) (mem_inside_univ c)
  have hbdY : bd R m (postcomp R ι (m + 1) c) ∈ inside R m Kᶜ := by
    rw [← postcomp_bd]
    exact postcomp_mem_inside ι (fun x hx ↦ hx) hc
  obtain ⟨w, hw⟩ := h _ hbdY
  generalize hcYdef : postcomp R ι (m + 1) c = cY at hcY hbdY hw
  generalize hfdef : cY - bd R (m + 1) w = f at hw
  have hcov : w ∈ inside R (m + 2) (⋃₀ 𝒰) := by
    have : ⋃₀ 𝒰 = univ := by
      simp only [𝒰, sUnion_insert, sUnion_singleton]
      exact eq_univ_of_forall fun y ↦ (em (y ∈ K)).imp (fun h ↦ hKU h) id
    rw [this]
    exact mem_inside_univ w
  obtain ⟨wU, hwU, wK, hwK, hsplit⟩ :=
    exists_add_of_mem_small_pair (smallChainMap_mem_small h𝒰 (m + 2) hcov)
  have hbdw : bd R (m + 1) w = cY - f := by
    rw [← hfdef]
    abel
  have hDf : smallHomotopy R 𝒰 (m + 1) f ∈ inside R (m + 2) Kᶜ :=
    smallHomotopy_mem_inside_of_mem 𝒰 hw
  have hDc : smallHomotopy R 𝒰 (m + 1) cY ∈ inside R (m + 2) U :=
    smallHomotopy_mem_inside_of_mem 𝒰 hcY
  have hv : wU + smallHomotopy R 𝒰 (m + 1) cY ∈ inside R (m + 2) U :=
    Submodule.add_mem _ hwU hDc
  obtain ⟨v', hv'⟩ := exists_postcomp_subtypeVal_eq hv
  refine ⟨v', ?_⟩
  have key : cY - bd R (m + 1) (wU + smallHomotopy R 𝒰 (m + 1) cY) =
      bd R (m + 1) wK - bd R (m + 1) (smallHomotopy R 𝒰 (m + 1) f) + f := by
    have h1 := congrArg (bd R (m + 1)) hsplit
    rw [smallChainMap_succ, map_sub, map_sub, bd_bd, sub_zero, hbdw, map_sub, map_sub,
      map_add] at h1
    rw [map_add]
    generalize bd R (m + 1) (smallHomotopy R 𝒰 (m + 1) cY) = P at h1 ⊢
    generalize bd R (m + 1) (smallHomotopy R 𝒰 (m + 1) f) = Q at h1 ⊢
    have h2 := sub_eq_iff_eq_add.1 (sub_eq_iff_eq_add.1 h1)
    rw [h2]
    abel
  have hmem : postcomp R ι (m + 1) (c - bd R (m + 1) v') ∈ inside R (m + 1) Kᶜ := by
    rw [map_sub, postcomp_bd, hv', hcYdef, key]
    exact Submodule.add_mem _ (Submodule.sub_mem _ (bd_mem_inside hwK) (bd_mem_inside hDf)) hw
  exact mem_inside_preimage_of_postcomp_mem_inside Subtype.val_injective hmem

end converseExcision

section cycles

variable (R) in
/-- `c` is the boundary of a chain lying in `A`. -/
def IsBoundaryIn (m : ℕ) (A : Set Y) (c : Chain R Y m) : Prop :=
  ∃ w ∈ inside R (m + 1) A, bd R m w = c

variable (R Y) in
/-- `H_{m+1}(A; R) = 0`, computed with chains of `Y` lying in `A`: every `(m+1)`-cycle lying in
`A` is the boundary of a chain lying in `A`. -/
def CycleVanishing (m : ℕ) (A : Set Y) : Prop :=
  ∀ c ∈ inside R (m + 1) A, bd R m c = 0 → IsBoundaryIn R (m + 1) A c

/-- Mayer–Vietoris for the vanishing of absolute homology: for `U`, `V` open, the vanishing of
`H_{m+2}(U)`, `H_{m+2}(V)` and `H_{m+1}(U ∩ V)` gives the vanishing of `H_{m+2}(U ∪ V)`. -/
theorem CycleVanishing.union {m : ℕ} {U V : Set Y} (hU : IsOpen U) (hV : IsOpen V)
    (h₁ : CycleVanishing R Y (m + 1) U) (h₂ : CycleVanishing R Y (m + 1) V)
    (h₁₂ : CycleVanishing R Y m (U ∩ V)) : CycleVanishing R Y (m + 1) (U ∪ V) := by
  intro z hz hbz
  set 𝒰 : Set (Set Y) := {U, V}
  have h𝒰 : ∀ W ∈ 𝒰, IsOpen W := by
    rintro W (rfl | rfl)
    · exact hU
    · exact hV
  have hz' : z ∈ inside R (m + 2) (⋃₀ 𝒰) := by
    simpa [𝒰] using hz
  obtain ⟨a, ha, b, hb, hsplit⟩ :=
    exists_add_of_mem_small_pair (smallChainMap_mem_small h𝒰 (m + 2) hz')
  rw [smallChainMap_succ, hbz, map_zero, sub_zero] at hsplit
  have hab : bd R (m + 1) a = -bd R (m + 1) b := by
    have := congrArg (bd R (m + 1)) hsplit
    rw [map_sub, bd_bd, hbz, sub_zero, map_add] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  have hbaUV : bd R (m + 1) a ∈ inside R (m + 1) (U ∩ V) := by
    rw [inside_inter]
    refine ⟨bd_mem_inside ha, ?_⟩
    rw [hab]
    exact Submodule.neg_mem _ (bd_mem_inside hb)
  obtain ⟨d, hd, hbd⟩ := h₁₂ _ hbaUV (bd_bd m a)
  rw [inside_inter] at hd
  obtain ⟨eU, heU, hbeU⟩ := h₁ (a - d) (Submodule.sub_mem _ ha hd.1)
    (by rw [map_sub, hbd, sub_self])
  obtain ⟨eV, heV, hbeV⟩ := h₂ (b + d) (Submodule.add_mem _ hb hd.2)
    (by rw [map_add, hbd, hab, add_neg_cancel])
  refine ⟨smallHomotopy R 𝒰 (m + 2) z + eU + eV, ?_, ?_⟩
  · refine Submodule.add_mem _ (Submodule.add_mem _ (smallHomotopy_mem_inside_of_mem 𝒰 hz) ?_) ?_
    · exact inside_mono _ subset_union_left heU
    · exact inside_mono _ subset_union_right heV
  · rw [map_add, map_add, hbeU, hbeV]
    calc _ = bd R (m + 1 + 1) (smallHomotopy R 𝒰 (m + 1 + 1) z) + (a + b) := by abel
      _ = z := by
        rw [← hsplit]
        abel

/-- Transport of the vanishing of `H_{m+1}(A)` along a homeomorphism `e : Y ≃ Z`. -/
theorem CycleVanishing.of_homeomorph {m : ℕ} (e : Y ≃ₜ Z) {A : Set Y}
    (h : CycleVanishing R Y m A) : CycleVanishing R Z m (e '' A) := by
  intro c hc hbc
  have hc₀ : postcomp R (e.symm : C(Z, Y)) (m + 1) c ∈ inside R (m + 1) A := by
    refine postcomp_mem_inside _ (fun z hz ↦ ?_) hc
    obtain ⟨y, hy, rfl⟩ := hz
    simpa using hy
  have hbc₀ : bd R m (postcomp R (e.symm : C(Z, Y)) (m + 1) c) = 0 := by
    rw [← postcomp_bd, hbc, map_zero]
  obtain ⟨w, hw, hbw⟩ := h _ hc₀ hbc₀
  refine ⟨postcomp R (e : C(Y, Z)) (m + 2) w,
    postcomp_mem_inside _ (fun y hy ↦ mem_image_of_mem e hy) hw, ?_⟩
  rw [← postcomp_bd, hbw, postcomp_comp]
  have : (e : C(Y, Z)).comp (e.symm : C(Z, Y)) = ContinuousMap.id Z := by
    ext z
    simp
  rw [this, postcomp_id]

/-- The vanishing of `H_{m+1}(A)` is invariant under homeomorphisms. -/
theorem cycleVanishing_homeomorph_image_iff {m : ℕ} (e : Y ≃ₜ Z) {A : Set Y} :
    CycleVanishing R Z m (e '' A) ↔ CycleVanishing R Y m A := by
  refine ⟨fun h ↦ ?_, CycleVanishing.of_homeomorph e⟩
  rw [← e.symm_image_image A]
  exact CycleVanishing.of_homeomorph e.symm h

/-- The homology of the subspace `A` versus chains of `Y` lying in `A`: `H_{m+1}` of the space
`A` vanishes iff every `(m+1)`-cycle of `Y` lying in `A` bounds a chain lying in `A`. -/
theorem cycleVanishing_univ_subtype_iff {m : ℕ} {A : Set Y} :
    CycleVanishing R A m univ ↔ CycleVanishing R Y m A := by
  set ι := ContinuousMap.subtypeVal A
  have hinj : ∀ n, Function.Injective (postcomp R ι n) :=
    postcomp_injective Subtype.val_injective
  have hmaps : MapsTo ι univ A := fun x _ ↦ x.2
  constructor
  · intro h c hc hbc
    obtain ⟨c', rfl⟩ := exists_postcomp_subtypeVal_eq hc
    have hbc' : bd R m c' = 0 := by
      apply hinj m
      rw [postcomp_bd, hbc, map_zero]
    obtain ⟨w', -, hbw'⟩ := h c' (mem_inside_univ c') hbc'
    exact ⟨postcomp R ι (m + 2) w', postcomp_mem_inside ι hmaps (mem_inside_univ w'),
      by rw [← postcomp_bd, hbw']⟩
  · intro h c' _ hbc'
    obtain ⟨w, hw, hbw⟩ := h (postcomp R ι (m + 1) c')
      (postcomp_mem_inside ι hmaps (mem_inside_univ c')) (by rw [← postcomp_bd, hbc', map_zero])
    obtain ⟨w', rfl⟩ := exists_postcomp_subtypeVal_eq hw
    refine ⟨w', mem_inside_univ w', hinj (m + 1) ?_⟩
    rw [postcomp_bd, hbw]

/-- Along an embedding `f : Y → Z`: `H_{m+1}(Y)` vanishes iff every `(m+1)`-cycle of `Z` lying in
the image of `f` bounds a chain lying in the image. -/
theorem cycleVanishing_univ_iff_range {m : ℕ} {f : Y → Z} (hf : Topology.IsEmbedding f) :
    CycleVanishing R Y m univ ↔ CycleVanishing R Z m (range f) := by
  have h := cycleVanishing_homeomorph_image_iff (R := R) (m := m) hf.toHomeomorph (A := univ)
  rw [image_univ_of_surjective hf.toHomeomorph.surjective] at h
  exact h.symm.trans cycleVanishing_univ_subtype_iff

end cycles

end SingularChain

end MMP
