module

public import MMP.AlgebraicGeometry.Singularities.Snc.RelativeSncOfSnc
public import MMP.AlgebraicGeometry.Morphisms.FiniteCoheight

/-!
# The reduced inverse image of a divisor under a finite cover

Let `g : V' ⟶ V` be a finite morphism of integral schemes of the same finite dimension, locally
of finite type over a field `k`, with `V'` smooth of relative dimension `n` over `k`, and let `𝒮`
be a finite set of prime divisors of `V` whose union `Z` is such that `g⁻¹ Z` has a weak chart
around every point of `V'`. The *reduced inverse image* `S'` of `∑_{E ∈ 𝒮} E` is the reduced
divisor whose components are the prime divisors `E'` of `V'` with `g(η_{E'}) = η_E` for some
`E ∈ 𝒮`. Its support is `g⁻¹ Z`: a point of `g⁻¹ Z` specializes from a point `ξ` of `g⁻¹ Z` of
codimension one (by the chart), and `g ξ` has codimension one (finite morphisms of varieties of
the same dimension preserve codimension) and lies on some `E ∈ 𝒮`, so it is `η_E`. The charts
then make `S'` a relative simple normal crossing divisor.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_isRelativeSNC_reducedPreimage`: the statement
  above.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology MMP.Mori MMP.Mori.Divisor.LogSpreadingProof

open Classical in
/-- **The reduced inverse image is a relative snc divisor.** Let `g : V' ⟶ V` be a finite morphism
of integral schemes of the same finite dimension over a field `k`, with `π : V ⟶ Spec k` locally
of finite type and `g ≫ π` smooth of relative dimension `n`, and let `𝒮` be a finite set of prime
divisors of `V` such that `g⁻¹(⋃_{E ∈ 𝒮} E)` has a weak chart around every point. Then the
reduced divisor `S'` with `S' E' = 1` exactly when `g(η_{E'}) = η_E` for some `E ∈ 𝒮` is a relative
snc divisor for `g ≫ π`. -/
theorem exists_isRelativeSNC_reducedPreimage {k : Type} [Field k] {n : ℕ} {V V' : Scheme.{0}}
    (π : V ⟶ Spec (.of k)) [IsIntegral V] [IsIntegral V'] [LocallyOfFiniteType π]
    (g : V' ⟶ V) [IsFinite g] [SmoothOfRelativeDimension n (g ≫ π)]
    (hdim : topologicalKrullDim V' = topologicalKrullDim V) (hfin : topologicalKrullDim V ≠ ⊤)
    (𝒮 : Finset (MMP.Mori.PrimeDivisor V))
    (hchart : ∀ y : V', ∃ c : WeakChart (g ≫ π) n (g ⁻¹' (⋃ E ∈ 𝒮,
      AlgebraicGeometry.PrimeDivisor.support E)), y ∈ (c.W : Set V')) :
    ∃ S' : Divisor V', S'.IsRelativeSNC n (g ≫ π) ∧
      ∀ E' : MMP.Mori.PrimeDivisor V', S' E' =
        if ∃ E ∈ 𝒮, g E'.genericPoint = E.genericPoint then 1 else 0 := by
  set Z : Set V' := g ⁻¹' (⋃ E ∈ 𝒮, AlgebraicGeometry.PrimeDivisor.support E) with hZdef
  set T₀ : Set V := (fun E : MMP.Mori.PrimeDivisor V => E.genericPoint) '' (𝒮 : Set _)
  have hfinE : {E' : MMP.Mori.PrimeDivisor V' | g E'.genericPoint ∈ T₀}.Finite :=
    Set.Finite.preimage (f := fun E' : MMP.Mori.PrimeDivisor V' => E'.genericPoint)
      AlgebraicGeometry.PrimeDivisor.genericPoint_injective.injOn (g.finite_preimage (𝒮.finite_toSet.image _))
  let S' : Divisor V' := Finsupp.onFinset hfinE.toFinset
    (fun E' => if ∃ E ∈ 𝒮, g E'.genericPoint = E.genericPoint then 1 else 0) (by
      intro E' h
      rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      by_contra hne
      exact h (if_neg fun ⟨E, hE, h⟩ => hne ⟨E, hE, h.symm⟩))
  have hS' : ∀ E', S' E' = if ∃ E ∈ 𝒮, g E'.genericPoint = E.genericPoint then 1 else 0 :=
    fun E' => Finsupp.onFinset_apply
  have hsupp : (S'.supp : Set V') = Z := by
    apply subset_antisymm
    · rw [coe_supp_eq_biUnion]
      intro y hy
      simp only [Set.mem_iUnion, exists_prop] at hy
      obtain ⟨E', hE', hyE'⟩ := hy
      have hcond : ∃ E ∈ 𝒮, g E'.genericPoint = E.genericPoint := by
        by_contra hne
        exact Finsupp.mem_support_iff.mp hE' (by simp only [hS', hne, ite_false])
      obtain ⟨E, hE, hgE⟩ := hcond
      have hη : E'.genericPoint ∈ Z := by
        rw [hZdef, Set.mem_preimage, hgE]
        refine Set.mem_biUnion hE ?_
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact subset_closure rfl
      have hcl : E'.support ⊆ Z := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        refine closure_minimal (Set.singleton_subset_iff.2 hη) ?_
        exact (isClosed_biUnion_finset fun E _ =>
          E.idealSheaf.support.isClosed).preimage g.continuous
      exact hcl hyE'
    · intro y hy
      obtain ⟨c, hyc⟩ := hchart y
      obtain ⟨𝔮, -, hsp, hcoh, hξZ⟩ := exists_coheight_one_specializes (g ≫ π) c y hy hyc
      set ξ := c.W.2.fromSpec 𝔮
      obtain ⟨E, hE, hξE⟩ : ∃ E ∈ 𝒮, g ξ ∈ AlgebraicGeometry.PrimeDivisor.support E := by
        simpa only [hZdef, Set.mem_preimage, Set.mem_iUnion, exists_prop] using hξZ
      have hcohg : Order.coheight (g ξ) = 1 := by
        rw [coheight_map_eq_of_isFinite π g hdim hfin ξ, hcoh]
      have hspE : E.genericPoint ⤳ g ξ := by
        rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact hξE
      have hgξ : E.genericPoint = g ξ := eq_of_specializes_of_coheight_eq_one hspE
        (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E) hcohg
      set E' := AlgebraicGeometry.PrimeDivisor.ofCoheightOne ξ hcoh
      have hE'η : E'.genericPoint = ξ :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
      have hE'S : E' ∈ S'.support := by
        have hcond : ∃ E ∈ 𝒮, g E'.genericPoint = E.genericPoint := ⟨E, hE, by
          rw [hE'η]; exact hgξ.symm⟩
        rw [Finsupp.mem_support_iff, hS', if_pos hcond]
        exact one_ne_zero
      rw [coe_supp_eq_biUnion]
      refine Set.mem_biUnion hE'S ?_
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, hE'η,
        ← specializes_iff_mem_closure]
      exact hsp
  refine ⟨S', ⟨fun E' hE' => ?_, fun y => ?_⟩, hS'⟩
  · rw [Finsupp.mem_support_iff, hS'] at hE'
    rw [hS', if_pos (by_contra fun h => hE' (if_neg h))]
  · obtain ⟨c, hyc⟩ := hchart y
    exact exists_snc_chart (g ≫ π) S' (exists_mem_support_genericPoint_eq S') (c.ofEq hsupp.symm)
      y hyc

end MMP.FourfoldProofs.FractionalLogComplexProof
