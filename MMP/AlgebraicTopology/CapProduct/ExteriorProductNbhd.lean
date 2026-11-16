module

public import MMP.AlgebraicTopology.CapProduct.Support
public import MMP.AlgebraicTopology.CapProduct.ExteriorProductChains
public import MMP.AlgebraicTopology.CapProduct.ExteriorProductNormalize

/-!
# Cap products with pulled-back classes and exterior products, near a closed set

Let `A ⊆ Y` be open and `N ⊆ Y` closed with `A ∪ int N = Y`, `pr : X × Y → Y` the projection,
`A' = pr⁻¹ A` and `N' = pr⁻¹ N ≅ X × N`. On cohomology classes modulo coboundaries and homology
classes modulo boundaries, the neighbourhood cap product satisfies
`pr^* x ∩_{N'} (y × b) = y × (x ∩_N b)`.

## Main results

* `MMP.BorelMooreCap.homologyMap_crossHomQ_capHomQNbhd`: through `X × N ≅ pr⁻¹ N`,
  `y × (x ∩_N b) = pr^* x ∩_{pr⁻¹ N} (y × b)`.
* `MMP.BorelMooreCap.capHomQNbhd_relCohomologyMap_crossHomQ_eq_zero_of_lt`: the cap product
  `pr^* x ∩_{pr⁻¹ N} (y × b)` vanishes when `deg b < deg x`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Set Simplicial AlgebraicTopology MMP.LatticePath
  MMP.SingularCross MMP.LocallyFiniteChain
  MMP.BorelMooreCross MMP.SingularCochain
  MMP.SingularChain MMP.borelMooreHomology

universe u

namespace MMP

namespace BorelMooreCap

variable {R : Type u} [CommRing R] {X Y : TopCat.{u}}

/-- The simplices of a cross product of locally finite chains lie in products of simplices of
the factors. -/
lemma exists_of_coeff_crossChain_ne_zero {n p q : ℕ} (w : (BM R X).X p) (z : (BM R Y).X q)
    {ρ : Simp (TopCat.of (X × Y)) n} (hρ : coeff R (crossChain R n p q w z) ρ ≠ 0) :
    ∃ σ τ, coeff R w σ ≠ 0 ∧ coeff R z τ ≠ 0 ∧
      singularSimplexImage _ ρ ⊆ singularSimplexImage X σ ×ˢ singularSimplexImage Y τ := by
  obtain ⟨st, hst⟩ : ∃ st, lfTensor (coeff R w) (coeff R z) st *
      ((crossFamily n p q st ρ : ℤ) : R) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hρ (finsum_eq_zero_of_forall_eq_zero hc)
  refine ⟨st.1, st.2, fun h ↦ hst (by simp [lfTensor, h]), fun h ↦ hst (by simp [lfTensor, h]),
    singularSimplexImage_subset_of_mem_support n st.1 st.2 fun h ↦ hst ?_⟩
  change _ * ((crossSimplex n st.1 st.2 ρ : ℤ) : R) = 0
  rw [h, Int.cast_zero, mul_zero]

variable (X) in
/-- The preimage `pr⁻¹ S ⊆ X × Y` of `S ⊆ Y`. -/
abbrev prPre (S : Set Y) : Set (TopCat.of (X × Y)) := prSnd X Y ⁻¹' S

/-- The preimage under the projection of an open set is open. -/
lemma isOpen_prPre {S : Set Y} (hS : IsOpen S) : IsOpen (prPre X S) :=
  hS.preimage (prSnd X Y).hom.continuous

/-- The preimage under the projection of a closed set is closed. -/
lemma isClosed_prPre {S : Set Y} (hS : IsClosed S) : IsClosed (prPre X S) :=
  hS.preimage (prSnd X Y).hom.continuous

variable (X) in
/-- The identification `X × S ≅ pr⁻¹ S`. -/
def prodPreimage (S : Set Y) : TopCat.of (X × S) ⟶ TopCat.of (prPre X S) :=
  TopCat.ofHom ⟨fun x ↦ ⟨(x.1, x.2.1), x.2.2⟩, by fun_prop⟩

/-- Composing `X × S ≅ pr⁻¹ S` with the inclusion `pr⁻¹ S ⊆ X × Y` gives `id × ι`. -/
lemma prodPreimage_comp_subsetInclusion (S : Set Y) :
    prodPreimage X S ≫ subsetInclusion (prPre X S) =
      SingularCross.prodHom (𝟙 X) (subsetInclusion S) :=
  rfl

/-- For closed `S`, the map `X × S → pr⁻¹ S` is proper. -/
lemma isProperMap_prodPreimage {S : Set Y} (hS : IsClosed S) :
    IsProperMap (prodPreimage X S) := by
  refine isProperMap_of_comp_of_inj (prodPreimage X S).hom.continuous continuous_subtype_val ?_
    Subtype.val_injective
  exact isProperMap_prodHom (f := 𝟙 X) (by simp) (isProperMap_subsetInclusion hS)

/-- If `u` is supported in `N`, then `w × u` is supported in `pr⁻¹ N`. -/
lemma isSupportedIn_crossChain {N : Set Y} {p q : ℕ} (w : (BM R X).X p) {u : (BM R Y).X q}
    (hu : IsSupportedIn R (ModuleCat.of R R) N u) :
    IsSupportedIn R (ModuleCat.of R R) (prPre X N) (crossChain R (p + q) p q w u) := by
  intro ρ hρ
  obtain ⟨σ, τ, -, hτ, hsub⟩ := exists_of_coeff_crossChain_ne_zero w u hρ
  exact fun x hx ↦ hu τ hτ (hsub hx).2

/-- On chains supported in `N`: `(id × ι)` commutes with restriction, through `X × N ≅ pr⁻¹ N`. -/
lemma chainMap_prodPreimage_crossChain_subsetRestrictMap {N : Set Y} (hN : IsClosed N)
    {p q : ℕ} (w : (BM R X).X p) {u : (BM R Y).X q}
    (hu : IsSupportedIn R (ModuleCat.of R R) N u) :
    ((chainMap R (ModuleCat.of R R) (prodPreimage X N) (isProperMap_prodPreimage hN)).f
        (p + q)).hom
        (crossChain R (p + q) p q w ((subsetRestrictMap R (ModuleCat.of R R) N q).hom u)) =
      (subsetRestrictMap R (ModuleCat.of R R) (prPre X N) (p + q)).hom
        (crossChain R (p + q) p q w u) := by
  have hN' : IsClosed (prPre X N) := isClosed_prPre hN
  apply chainMap_subsetInclusion_injective R (ModuleCat.of R R) hN' (p + q)
  rw [chainMap_subsetRestrictMap R _ hN' (isSupportedIn_crossChain w hu)]
  have e := chainMap_comp R (ModuleCat.of R R) (prodPreimage X N) (subsetInclusion (prPre X N))
    (isProperMap_prodPreimage hN) (isProperMap_subsetInclusion hN')
  have e2 := congrArg (fun φ ↦ (φ.f (p + q)).hom
    (crossChain R (p + q) p q w ((subsetRestrictMap R (ModuleCat.of R R) N q).hom u))) e
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at e2
  rw [← e2]
  have e3 := chainMap_prodHom_crossChain (R := R) (𝟙 X) (subsetInclusion N)
    (by simp) (isProperMap_subsetInclusion hN) (p + q) p q w
    ((subsetRestrictMap R (ModuleCat.of R R) N q).hom u)
  rwa [chainMap_subsetRestrictMap R _ hN hu, chainMap_id] at e3

variable {A N : Set Y} (hA : IsOpen A) (hN : IsClosed N) (hAN : A ∪ interior N = univ)

include hAN in
/-- If `A ∪ int N = Y`, then `pr⁻¹ A ∪ int (pr⁻¹ N) = X × Y`. -/
lemma prPre_union_interior_eq_univ : prPre X A ∪ interior (prPre X N) = univ := by
  refine eq_univ_of_forall fun x ↦ ?_
  rcases (eq_univ_iff_forall.1 hAN) x.2 with h | h
  · exact Or.inl h
  · exact Or.inr (preimage_interior_subset_interior_preimage continuous_snd h)

include hA hAN in
/-- Every class of `H_n Y` is represented by a cycle small for `{A, int N}`. -/
lemma exists_small_rep {n : ℕ} (b : HomQ (R := R) Y n) :
    ∃ z : Cyc (R := R) Y n, Submodule.Quotient.mk z = b ∧
      ∀ σ, coeff R z.1 σ ≠ 0 → ∃ U ∈ ({A, interior N} : Set (Set Y)),
        singularSimplexImage Y σ ⊆ U := by
  induction b using Submodule.Quotient.induction_on with | H z => ?_
  refine ⟨⟨_, nbhdSubdiv_mem_cyc (A := A) (N := N) z.2⟩, (Submodule.Quotient.eq _).2 ?_,
    fun σ hσ ↦ smallChainMapLF_small R (ModuleCat.of R R)
      (by rintro U (rfl | rfl) <;> simp [hA]) (by rwa [sUnion_insert, sUnion_singleton]) n z.1 hσ⟩
  have h := mem_bdry_of (z - ⟨_, nbhdSubdiv_mem_cyc (A := A) (N := N) z.2⟩) _
    (sub_smallChainMapLF_eq_d (R := R) {A, interior N} z.2).symm
  convert Submodule.neg_mem _ h using 1
  exact (neg_sub _ _).symm

/-- Every relative cohomology class has a representative vanishing on degenerate simplices. -/
lemma exists_isNormalized_rep {j : ℕ} (x : relCohomology R A j) :
    ∃ ψ : relCocycles R A j, IsNormalized ψ.1 ∧ Submodule.Quotient.mk ψ = x := by
  induction x using Submodule.Quotient.induction_on with | H φ => ?_
  obtain ⟨ψ, hψ, hψn, hφψ⟩ := exists_isNormalized_sub_mem_relCoboundaries A j φ.1 φ.2
  exact ⟨⟨ψ, hψ⟩, hψn, ((Submodule.Quotient.eq _).2 (show φ - ⟨ψ, hψ⟩ ∈
    (relCoboundaries R A j).comap (relCocycles R A j).subtype from hφψ)).symm⟩

/-- The cross product of a chain with a chain small for `{A, int N}` is small for
`{pr⁻¹ A, int pr⁻¹ N}`. -/
lemma small_crossChain {p n : ℕ} (w : (BM R X).X p) {z : (BM R Y).X n}
    (hz : ∀ σ, coeff R z σ ≠ 0 → ∃ U ∈ ({A, interior N} : Set (Set Y)),
      singularSimplexImage Y σ ⊆ U) :
    ∀ ρ, (crossChain R (p + n) p n w z).1 ρ ≠ 0 →
      ∃ U ∈ ({prPre X A, interior (prPre X N)} : Set (Set (TopCat.of (X × Y)))),
        singularSimplexImage _ ρ ⊆ U := by
  intro ρ hρ
  obtain ⟨σ, τ, -, hτ, hsub⟩ := exists_of_coeff_crossChain_ne_zero w z hρ
  obtain ⟨U, hU, hτU⟩ := hz τ hτ
  rcases hU with hU | hU
  · rw [hU] at hτU
    exact ⟨prPre X A, Or.inl rfl, fun x hx ↦ hτU (hsub hx).2⟩
  · rw [hU] at hτU
    exact ⟨interior (prPre X N), Or.inr rfl, fun x hx ↦
      preimage_interior_subset_interior_preimage continuous_snd (hτU (hsub hx).2)⟩

/-- The neighbourhood cap product of `pr^* [ψ]` and `[w] × [z]` on representatives. -/
lemma capHomQNbhd_relCohomologyMap_crossHomQ_mk (p j n r : ℕ) (hr : j + r = p + n)
    (ψ : relCocycles R A j) (w : Cyc (R := R) X p) (z : Cyc (R := R) Y n) :
    capHomQNbhd R (isOpen_prPre (X := X) hA) (isClosed_prPre (X := X) hN)
        (prPre_union_interior_eq_univ hAN) j r (p + n) hr
        (relCohomologyMap R (prSnd X Y) (subset_refl _) j (Submodule.Quotient.mk ψ))
        (crossHomQ R X Y p n (Submodule.Quotient.mk w) (Submodule.Quotient.mk z)) =
      Submodule.Quotient.mk (capCycNbhd R (isOpen_prPre (X := X) hA) (isClosed_prPre (X := X) hN)
        (prPre_union_interior_eq_univ hAN) j r (p + n) hr
        ⟨cochainPullback R (prSnd X Y) j ψ.1, cochainPullback_mem_relCocycles _ (subset_refl _) ψ.2⟩
        ⟨crossChain R (p + n) p n w.1 z.1, crossChain_mem_cyc p n w z⟩) :=
  rfl

/-- **The neighbourhood cap product with a pulled-back class and an exterior product**, on
classes of cocycles and cycles: through `X × N ≅ pr⁻¹ N`,
`y × (x ∩_N b) = pr^* x ∩_{pr⁻¹ N} (y × b)`. -/
theorem homologyMap_crossHomQ_capHomQNbhd (p j q n r : ℕ) (hq : j + q = n) (hr : j + r = p + n)
    {A' : Set (TopCat.of (X × Y))} (hA' : IsOpen A') (hAN' : A' ∪ interior (prPre X N) = univ)
    (hA'A : A' ⊆ prSnd X Y ⁻¹' A) (hA'eq : A' = prPre X A)
    (x : relCohomology R A j) (y : HomQ (R := R) X p) (b : HomQ (R := R) Y n) :
    (homologyMap R (chainMap R (ModuleCat.of R R) (prodPreimage X N) (isProperMap_prodPreimage hN))
        ((p : ℤ) + (q : ℤ))).hom
      ((homologyEquiv R (TopCat.of (X × N)) (p + q)).symm
        (crossHomQ R X (TopCat.of N) p q y (capHomQNbhd R hA hN hAN j q n hq x b))) =
      congrDegree R (TopCat.of (prPre X N)) (by omega : ((r : ℕ) : ℤ) = ((p + q : ℕ) : ℤ))
        ((homologyEquiv R (TopCat.of (prPre X N)) r).symm
          (capHomQNbhd R hA' (isClosed_prPre (X := X) hN) hAN' j r (p + n) hr
            (relCohomologyMap R (prSnd X Y) hA'A j x) (crossHomQ R X Y p n y b))) := by
  subst hA'eq
  obtain rfl : n = j + q := hq.symm
  obtain rfl : r = p + q := by omega
  obtain ⟨ψ, hψn, rfl⟩ := exists_isNormalized_rep x
  obtain ⟨w, rfl⟩ : ∃ w : Cyc (R := R) X p, Submodule.Quotient.mk w = y :=
    Submodule.Quotient.mk_surjective _ y
  obtain ⟨z, rfl, hz⟩ := exists_small_rep (R := R) hA hAN b
  rw [congrDegree_self, LinearEquiv.refl_apply]
  refine Eq.trans (homologyMap_homologyEquiv_symm_mk R _ (p + q)
    ⟨crossChain R (p + q) p q w.1 (capCycNbhd R hA hN hAN j q (j + q) rfl ψ z).1,
      crossChain_mem_cyc p q w (capCycNbhd R hA hN hAN j q (j + q) rfl ψ z)⟩) ?_
  refine Eq.trans ?_ (congrArg _
    (capHomQNbhd_relCohomologyMap_crossHomQ_mk hA hN hAN p j (j + q) (p + q) hr ψ w z).symm)
  congr 2
  apply Subtype.ext
  have hρz : (nbhdSubdiv R A N (j + q)).hom z.1 = z.1 :=
    smallChainMapLF_f_hom_of_small R (ModuleCat.of R R) z.1 hz
  have hρ' : (nbhdSubdiv R (prPre X A) (prPre X N) (p + (j + q))).hom
      (crossChain R (p + (j + q)) p (j + q) w.1 z.1) =
        crossChain R (p + (j + q)) p (j + q) w.1 z.1 :=
    smallChainMapLF_f_hom_of_small R (ModuleCat.of R R) _ (small_crossChain w.1 hz)
  have hsupp := isSupportedIn_capChain_nbhdSubdiv hA hAN j q (j + q) rfl ψ.2.1 z.1
  rw [hρz] at hsupp
  change ((chainMap R (ModuleCat.of R R) (prodPreimage X N) (isProperMap_prodPreimage hN)).f
      (p + q)).hom (crossChain R (p + q) p q w.1 ((subsetRestrictMap R (ModuleCat.of R R) N q).hom
        (capChain R j q (j + q) rfl ψ.1 ((nbhdSubdiv R A N (j + q)).hom z.1)))) =
    (subsetRestrictMap R (ModuleCat.of R R) (prPre X N) (p + q)).hom
      (capChain R j (p + q) (p + (j + q)) hr (cochainPullback R (prSnd X Y) j ψ.1)
        ((nbhdSubdiv R (prPre X A) (prPre X N) (p + (j + q))).hom
          (crossChain R (p + (j + q)) p (j + q) w.1 z.1)))
  rw [hρz, hρ', capChain_cochainPullback_crossChain R p q j ψ.1 hψn w.1 z.1,
    chainMap_prodPreimage_crossChain_subsetRestrictMap hN w.1 hsupp]

include hA hAN in
/-- The neighbourhood cap product `pr^* x ∩ (y × b)` vanishes when `deg b < deg x`. -/
theorem capHomQNbhd_relCohomologyMap_crossHomQ_eq_zero_of_lt (p j n r : ℕ) (hr : j + r = p + n)
    {A' : Set (TopCat.of (X × Y))} (hA' : IsOpen A') (hAN' : A' ∪ interior (prPre X N) = univ)
    (hA'A : A' ⊆ prSnd X Y ⁻¹' A) (hA'eq : A' = prPre X A)
    (hn : n < j) (x : relCohomology R A j) (y : HomQ (R := R) X p) (b : HomQ (R := R) Y n) :
    capHomQNbhd R hA' (isClosed_prPre (X := X) hN) hAN' j r (p + n) hr
        (relCohomologyMap R (prSnd X Y) hA'A j x) (crossHomQ R X Y p n y b) = 0 := by
  subst hA'eq
  obtain ⟨ψ, hψn, rfl⟩ := exists_isNormalized_rep x
  obtain ⟨w, rfl⟩ : ∃ w : Cyc (R := R) X p, Submodule.Quotient.mk w = y :=
    Submodule.Quotient.mk_surjective _ y
  obtain ⟨z, rfl, hz⟩ := exists_small_rep (R := R) hA hAN b
  refine (capHomQNbhd_relCohomologyMap_crossHomQ_mk hA hN hAN p j n r hr ψ w z).trans ?_
  have hρ' : (nbhdSubdiv R (prPre X A) (prPre X N) (p + n)).hom
      (crossChain R (p + n) p n w.1 z.1) = crossChain R (p + n) p n w.1 z.1 :=
    smallChainMapLF_f_hom_of_small R (ModuleCat.of R R) _ (small_crossChain w.1 hz)
  have h0 : capCycNbhd R (isOpen_prPre (X := X) hA) (isClosed_prPre (X := X) hN)
      (prPre_union_interior_eq_univ hAN) j r (p + n) hr
      ⟨cochainPullback R (prSnd X Y) j ψ.1, cochainPullback_mem_relCocycles _ (subset_refl _) ψ.2⟩
      ⟨crossChain R (p + n) p n w.1 z.1, crossChain_mem_cyc p n w z⟩ = 0 := by
    apply Subtype.ext
    change (subsetRestrictMap R (ModuleCat.of R R) (prPre X N) r).hom
        (capChain R j r (p + n) hr (cochainPullback R (prSnd X Y) j ψ.1)
          ((nbhdSubdiv R (prPre X A) (prPre X N) (p + n)).hom
            (crossChain R (p + n) p n w.1 z.1))) = 0
    rw [hρ', capChain_cochainPullback_crossChain_eq_zero_of_lt R p n j r hr hn ψ.1 hψn w.1 z.1,
      map_zero]
  rw [h0]
  exact Submodule.Quotient.mk_zero _

end BorelMooreCap

end MMP
