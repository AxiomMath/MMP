module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.InverseImageModuleRestriction
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Retract.Degeneration
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Restrict.Data

/-!
# Degeneration from retracts on the pieces of a finite clopen cover

Let `π : V ⟶ Spec ℂ` be projective and `V = ⨆ᵢ Uᵢ` a finite cover by disjoint open and closed
subschemes, and let `K` be a complex of sheaves of `π⁻¹𝒪`-modules on `V`. A section of `K` is the
sum of the extensions by zero of its restrictions to the `Uᵢ`, so `K` is a retract of
`⨁ᵢ ιᵢ_*(K|_{Uᵢ})`. If each `K|_{Uᵢ}` is a retract of the direct image
`gᵢ_* Ω^•_{Vᵢ'}(log Sᵢ')(-Sᵢ')`
along a finite cover `gᵢ : Vᵢ' ⟶ Uᵢ` by a smooth projective `Vᵢ'`, then `K` is a retract of
`⨁ᵢ ιᵢ_* gᵢ_* Ω^•_{Vᵢ'}(log Sᵢ')(-Sᵢ')`. Hypercohomology and the Hodge groups are unchanged by
the affine direct images `ιᵢ_*` and `gᵢ_*`, and add over the finite biproduct, so this complex
degenerates at `E₁`, and so does its retract `K`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.finite_and_finrank_biproduct`: dimensions add over a
  finite biproduct.
* `MMP.FourfoldProofs.FractionalLogComplexProof.finrank_hyp_eq_sum_of_retract_biproduct`:
  `E₁`-degeneration passes to retracts of finite biproducts of degenerating complexes.
* `MMP.FourfoldProofs.FractionalLogComplexProof.finite_and_finrank_hyp_piece`: `E₁`-degeneration for
  `ι_* g_* Ω^•_{V'}(log S')(-S')` on `V`, for a cover `g` of an open and closed piece.
* `MMP.FourfoldProofs.FractionalLogComplexProof.finrank_hyp_eq_sum_of_retract_pieces`: `E₁`-degeneration
  for a complex whose restrictions to the pieces are retracts of such direct images.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open MMP.Mori.Divisor.LogSpreadingProof (Hc)
open MMP.FourfoldProofs.LogDegenerationProof (single0)

/-- **Dimensions add over a finite biproduct.** For an additive functor `G` to modules over a
field and a finite family `X` with finite dimensional images, `G(⨁ X)` is finite dimensional of
dimension `∑ⱼ dim G(Xⱼ)`. -/
theorem finite_and_finrank_biproduct {R : Type} [CommRing R] (hR : IsField R) {C : Type*}
    [Category C] [Preadditive C] [HasFiniteBiproducts C] (G : C ⥤ ModuleCat.{0} R) [G.Additive]
    {J : Type} [Fintype J] (X : J → C) (hX : ∀ j, Module.Finite R (G.obj (X j))) :
    Module.Finite R (G.obj (⨁ X)) ∧
      Module.finrank R (G.obj (⨁ X)) = ∑ j, Module.finrank R (G.obj (X j)) := by
  let e : G.obj (⨁ X) ≃ₗ[R] (∀ j, G.obj (X j)) :=
    (G.mapBiproduct X ≪≫ ModuleCat.biproductIsoPi _).toLinearEquiv
  let := hR.toField
  exact ⟨Module.Finite.equiv e.symm, e.finrank_eq.trans (Module.finrank_pi_fintype R)⟩

section Biproduct

variable {Y T : Scheme.{0}} (h : Y ⟶ T)

/-- Complexes of sheaves of `π⁻¹𝒪_T`-modules have finite biproducts. -/
instance hasFiniteBiproducts_cochainComplex_invRing :
    HasFiniteBiproducts (CochainComplex (SheafOfModules.{0} (invRing h)) ℕ) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- **`E₁`-degeneration passes to retracts of finite biproducts.** Let `K` be a retract of a finite
biproduct `⨁ⱼ Xⱼ` of complexes of sheaves of `π⁻¹𝒪_T`-modules indexed by `ℕ`, with `Γ(T, ⊤)` a
field. If the Hodge groups `H^{k-p}(Xⱼᵖ)`, `p ≤ k`, are finite dimensional and
`dim ℍ^k(Xⱼ) = ∑_{p ≤ k} dim H^{k-p}(Xⱼᵖ)` for every `j`, then the same equality holds for `K`. -/
theorem finrank_hyp_eq_sum_of_retract_biproduct (hT : IsField Γ(T, ⊤)) {J : Type} [Finite J]
    (X : J → CochainComplex (SheafOfModules.{0} (invRing h)) ℕ)
    {K : CochainComplex (SheafOfModules.{0} (invRing h)) ℕ} (a : K ⟶ ⨁ X) (r : ⨁ X ⟶ K)
    (har : a ≫ r = 𝟙 K) (k : ℕ)
    (hfin : ∀ j, ∀ p ∈ Finset.range (k + 1),
      Module.Finite Γ(T, ⊤) (Hc h (single0 h ((X j).X p)) ((k - p : ℕ) : ℤ)))
    (heq : ∀ j, Module.finrank Γ(T, ⊤) (Hc h ⟨(X j).extend ComplexShape.embeddingUpNat, 0,
          CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ k) =
        ∑ p ∈ Finset.range (k + 1),
          Module.finrank Γ(T, ⊤) (Hc h (single0 h ((X j).X p)) ((k - p : ℕ) : ℤ))) :
    Module.finrank Γ(T, ⊤) (Hc h ⟨K.extend ComplexShape.embeddingUpNat, 0,
          CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ k) =
        ∑ p ∈ Finset.range (k + 1),
          Module.finrank Γ(T, ⊤) (Hc h (single0 h (K.X p)) ((k - p : ℕ) : ℤ)) := by
  have := Fintype.ofFinite J
  have hterm : ∀ p ∈ Finset.range (k + 1),
      Module.Finite Γ(T, ⊤) (Hc h (single0 h ((⨁ X).X p)) ((k - p : ℕ) : ℤ)) ∧
      Module.finrank Γ(T, ⊤) (Hc h (single0 h ((⨁ X).X p)) ((k - p : ℕ) : ℤ)) =
        ∑ j, Module.finrank Γ(T, ⊤) (Hc h (single0 h ((X j).X p)) ((k - p : ℕ) : ℤ)) := by
    intro p hp
    let G := hypSheafFunctor h ((k - p : ℕ) : ℤ)
    let e : G.obj ((⨁ X).X p) ≃ₗ[Γ(T, ⊤)] G.obj (⨁ fun j => (X j).X p) :=
      (G.mapIso ((HomologicalComplex.eval _ _ p).mapBiproduct X)).toLinearEquiv
    have i₀ := finite_and_finrank_hypSheafFunctor h ((⨁ X).X p) ((k - p : ℕ) : ℤ)
    have i₁ := fun j => finite_and_finrank_hypSheafFunctor h ((X j).X p) ((k - p : ℕ) : ℤ)
    obtain ⟨_, hr⟩ := finite_and_finrank_biproduct hT G (fun j => (X j).X p)
      (fun j => (i₁ j).1.1 (hfin j p hp))
    refine ⟨i₀.1.2 (Module.Finite.equiv e.symm), ?_⟩
    rw [i₀.2, e.finrank_eq, hr]
    exact Finset.sum_congr rfl fun j _ => ((i₁ j).2).symm
  obtain ⟨-, hA⟩ := finite_and_finrank_biproduct hT (hypComplexFunctor h k) X fun j =>
    (finite_and_finrank_hyp_le_sum h hT (X j) k (hfin j)).1
  rw [hypComplexFunctor_obj] at hA
  refine finrank_hyp_eq_sum_of_retract h hT a r har k (fun p hp => (hterm p hp).1) ?_
  rw [hA]
  refine (Finset.sum_congr rfl fun j _ => heq j).trans ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p hp => ((hterm p hp).2).symm

end Biproduct

/-! ### The pieces -/

/-- **`E₁`-degeneration for `ι_* g_* Ω^•_{V'}(log S')(-S')`.** Let `π : V ⟶ Spec ℂ` be projective,
`U` an open and closed subscheme of `V` with inclusion `ι`, and `g : V' ⟶ U` finite with
`V' ⟶ Spec ℂ` smooth projective and `S'` a relative simple normal crossing divisor on `V'`. Then
the Hodge groups of `ι_* g_* Ω^•_{V'}(log S')(-S')` are finite dimensional and its hypercohomology
has dimension `∑_{p ≤ k} dim H^{k-p}`. -/
theorem finite_and_finrank_hyp_piece (n : ℕ) {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ))
    (hπ : IsProjective π) (U : V.Opens) (hU : IsClosed (U : Set V)) {V' : Scheme.{0}}
    (g : V' ⟶ U.toScheme) [IsFinite g] [SmoothOfRelativeDimension n (g ≫ U.ι ≫ π)]
    (S' : MMP.Mori.Divisor V') (hS' : S'.IsRelativeSNC n (g ≫ U.ι ≫ π))
    (hgπ : IsProjective (g ≫ U.ι ≫ π)) (k : ℕ) :
    (∀ p (j : ℤ), Module.Finite Γ(Spec (CommRingCat.of ℂ), ⊤)
      (Hc π (single0 π ((relDirectImage U.ι π).obj ((relDirectImage g (U.ι ≫ π)).obj
        ((MMP.Mori.Divisor.relativeLogDeRhamComplex n (g ≫ U.ι ≫ π) S' hS' S'.suppIdeal).X p))))
        j)) ∧
    Module.finrank Γ(Spec (CommRingCat.of ℂ), ⊤) (Hc π
        ⟨(((relDirectImage U.ι π).mapHomologicalComplex _).obj
          (((relDirectImage g (U.ι ≫ π)).mapHomologicalComplex _).obj
            (MMP.Mori.Divisor.relativeLogDeRhamComplex n (g ≫ U.ι ≫ π) S' hS'
              S'.suppIdeal))).extend ComplexShape.embeddingUpNat, 0,
          CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ k) =
      ∑ p ∈ Finset.range (k + 1), Module.finrank Γ(Spec (CommRingCat.of ℂ), ⊤)
        (Hc π (single0 π ((relDirectImage U.ι π).obj ((relDirectImage g (U.ι ≫ π)).obj
          ((MMP.Mori.Divisor.relativeLogDeRhamComplex n (g ≫ U.ι ≫ π) S' hS'
            S'.suppIdeal).X p)))) ((k - p : ℕ) : ℤ)) := by
  have hπU : IsProjective (U.ι ≫ π) := isProjective_opens_ι_comp U π hπ hU
  have : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion U.ι (by
    rwa [Scheme.Opens.range_ι])
  have := isAffineHom_diagonal_of_isProjective π hπ
  have := isAffineHom_diagonal_of_isProjective (U.ι ≫ π) hπU
  have hY := exists_relDirectImage_X_iso_pushforward g (U.ι ≫ π) _
    (exists_relativeLogDeRhamComplex_X_iso_pushforward n (U.ι ≫ π) g S' hS')
  have hterm : ∀ p (j : ℤ),
      Module.Finite Γ(Spec (CommRingCat.of ℂ), ⊤)
        (Hc π (single0 π ((relDirectImage U.ι π).obj ((relDirectImage g (U.ι ≫ π)).obj
          ((MMP.Mori.Divisor.relativeLogDeRhamComplex n (g ≫ U.ι ≫ π) S' hS'
            S'.suppIdeal).X p)))) j) ∧
      Module.finrank Γ(Spec (CommRingCat.of ℂ), ⊤)
        (Hc π (single0 π ((relDirectImage U.ι π).obj ((relDirectImage g (U.ι ≫ π)).obj
          ((MMP.Mori.Divisor.relativeLogDeRhamComplex n (g ≫ U.ι ≫ π) S' hS'
            S'.suppIdeal).X p)))) j) =
        Module.finrank Γ(Spec (CommRingCat.of ℂ), ⊤)
          (Hc (U.ι ≫ π) (single0 (U.ι ≫ π) ((relDirectImage g (U.ι ≫ π)).obj
            ((MMP.Mori.Divisor.relativeLogDeRhamComplex n (g ≫ U.ι ≫ π) S' hS'
              S'.suppIdeal).X p))) j) := by
    intro p j
    obtain ⟨e⟩ := nonempty_Hc_single0_relDirectImage_iso U.ι π _ (hY p) j
    have : Module.Finite Γ(Spec (CommRingCat.of ℂ), ⊤) (Hc (U.ι ≫ π) (single0 (U.ι ≫ π)
        ((((relDirectImage g (U.ι ≫ π)).mapHomologicalComplex _).obj
          (MMP.Mori.Divisor.relativeLogDeRhamComplex n (g ≫ U.ι ≫ π) S' hS'
            S'.suppIdeal)).X p)) j) :=
      (finite_and_finrank_Hc_single0_relDirectImage n (U.ι ≫ π) g S' hS' hπU hgπ p j).1
    exact ⟨Module.Finite.equiv e.toLinearEquiv.symm, e.toLinearEquiv.finrank_eq⟩
  refine ⟨fun p j => (hterm p j).1, ?_⟩
  obtain ⟨e⟩ := nonempty_Hc_relDirectImage_iso U.ι π _ hY k
  rw [e.toLinearEquiv.finrank_eq, finrank_hyp_relDirectImage_eq_sum n (U.ι ≫ π) g S' hS' hπU hgπ k]
  exact Finset.sum_congr rfl fun p _ => ((hterm p _).2).symm

/-- **`E₁`-degeneration from retracts on the pieces.** Let `π : V ⟶ Spec ℂ` be projective,
`V = ⨆ᵢ Uᵢ` a finite cover by disjoint open and closed subschemes, and `K` a complex of sheaves
of `π⁻¹𝒪`-modules on `V` each of whose restrictions `K|_{Uᵢ}` is a retract of
`gᵢ_* Ω^•_{Vᵢ'}(log Sᵢ')(-Sᵢ')` for a finite `gᵢ : Vᵢ' ⟶ Uᵢ` with `Vᵢ'` smooth projective over `ℂ`.
Then `dim ℍ^k(V, K) = ∑_{p ≤ k} dim H^{k-p}(V, Kᵖ)`. -/
theorem finrank_hyp_eq_sum_of_retract_pieces (n : ℕ) {V : Scheme.{0}}
    (π : V ⟶ Spec (CommRingCat.of ℂ)) (hπ : IsProjective π) {ι : Type} [Finite ι]
    (U : ι → V.Opens) (hU : ∀ i, IsClosed (U i : Set V))
    (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j)) (hcov : ∀ x : V, ∃ i, x ∈ U i)
    (K : CochainComplex (SheafOfModules.{0} (invRing π)) ℕ)
    (V' : ι → Scheme.{0}) (g : ∀ i, V' i ⟶ (U i).toScheme) (hg : ∀ i, IsFinite (g i))
    (hsm : ∀ i, SmoothOfRelativeDimension n (g i ≫ (U i).ι ≫ π))
    (S' : ∀ i, MMP.Mori.Divisor (V' i))
    (hS' : ∀ i, haveI := hsm i; (S' i).IsRelativeSNC n (g i ≫ (U i).ι ≫ π))
    (hgπ : ∀ i, IsProjective (g i ≫ (U i).ι ≫ π))
    (a : ∀ i, ((relRestrict π (U i)).mapHomologicalComplex _).obj K ⟶
      ((relDirectImage (g i) ((U i).ι ≫ π)).mapHomologicalComplex _).obj
        (@MMP.Mori.Divisor.relativeLogDeRhamComplex n _ _ (g i ≫ (U i).ι ≫ π) (hsm i) (S' i)
          (hS' i) (S' i).suppIdeal))
    (r : ∀ i, ((relDirectImage (g i) ((U i).ι ≫ π)).mapHomologicalComplex _).obj
        (@MMP.Mori.Divisor.relativeLogDeRhamComplex n _ _ (g i ≫ (U i).ι ≫ π) (hsm i) (S' i)
          (hS' i) (S' i).suppIdeal) ⟶ ((relRestrict π (U i)).mapHomologicalComplex _).obj K)
    (har : ∀ i, a i ≫ r i = 𝟙 _) (k : ℕ) :
    Module.finrank Γ(Spec (CommRingCat.of ℂ), ⊤) (Hc π ⟨K.extend ComplexShape.embeddingUpNat, 0,
          CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ k) =
        ∑ p ∈ Finset.range (k + 1),
          Module.finrank Γ(Spec (CommRingCat.of ℂ), ⊤)
            (Hc π (single0 π (K.X p)) ((k - p : ℕ) : ℤ)) := by
  classical
  have := Fintype.ofFinite ι
  let X : ι → CochainComplex (SheafOfModules.{0} (invRing π)) ℕ := fun i =>
    ((relDirectImage (U i).ι π).mapHomologicalComplex _).obj
      (((relDirectImage (g i) ((U i).ι ≫ π)).mapHomologicalComplex _).obj
        (@MMP.Mori.Divisor.relativeLogDeRhamComplex n _ _ (g i ≫ (U i).ι ≫ π) (hsm i) (S' i)
          (hS' i) (S' i).suppIdeal))
  let A : K ⟶ ⨁ X := ∑ i, relRestrictUnitCx π (U i) K ≫
    ((relDirectImage (U i).ι π).mapHomologicalComplex _).map (a i) ≫ biproduct.ι X i
  let R : ⨁ X ⟶ K := ∑ i, biproduct.π X i ≫
    ((relDirectImage (U i).ι π).mapHomologicalComplex _).map (r i) ≫
      relRestrictExtCx π (U i) (hU i) K
  have hAR : A ≫ R = 𝟙 K := by
    rw [← sum_relRestrictUnitCx_comp_relRestrictExtCx π U hU hdisj hcov K]
    simp only [A, R, Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · rw [biproduct.ι_π_self_assoc, ← Functor.map_comp_assoc, har i, CategoryTheory.Functor.map_id,
        Category.id_comp]
    · intro j _ hji
      rw [biproduct.ι_π_ne_assoc _ hji, zero_comp, comp_zero, comp_zero]
    · exact fun h => (h (Finset.mem_univ i)).elim
  have hpiece := fun i => haveI := hg i; haveI := hsm i
    finite_and_finrank_hyp_piece n π hπ (U i) (hU i) (g i) (S' i) (hS' i) (hgπ i) k
  exact finrank_hyp_eq_sum_of_retract_biproduct π isField_Γ_spec_complex X A R hAR k
    (fun i p _ => (hpiece i).1 p _) (fun i => (hpiece i).2)

end MMP.FourfoldProofs.FractionalLogComplexProof
