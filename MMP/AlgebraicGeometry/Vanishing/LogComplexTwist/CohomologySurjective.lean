module

public import MMP.AlgebraicGeometry.Cohomology.Duality.SmoothSerreDuality
public import MMP.AlgebraicGeometry.Vanishing.LogComplexTwist.DegreeZero
public import MMP.AlgebraicGeometry.Cohomology.StupidTruncationEdgeSurjective
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Degeneration

/-!
# Surjectivity on cohomology of the inclusion of a twist of the fractional logarithmic complex

Let `π : V ⟶ Spec ℂ` be smooth projective with `V` integral, `D` a relative simple normal
crossing divisor and `B = Bn/N` a `ℚ`-divisor with coefficients in `[0, 1)` and support `D`. Let
`C^•` be the fractional logarithmic complex `𝒪_V(-M) · Ω^•_V(log D)` of an `N`-th root `𝒪_V(M)`
of `𝒪_V(Bn)`, and `C'^•` the one of a divisor `M'` with `-M' ≤ -M` and the same open
`V ∖ (D ∪ Supp M)`. If the inclusion `C'^• ⟶ C^•` is a quasi-isomorphism, then the inclusion
`𝒪_V(-M') ⟶ 𝒪_V(-M)` of the degree-zero terms is surjective on `H^q(V, -)` for every `q`: the
spectral sequence of `C^•` degenerates at `E₁`, so the edge map `ℍ^q(C^•) ⟶ H^q(C^0)` is onto,
and it factors through `H^q(C'^0) ⟶ H^q(C^0)` up to the isomorphism `ℍ^q(C'^•) ≅ ℍ^q(C^•)`.

The Hodge groups `H^j(V, C^p)` entering the dimension count are finite dimensional, `C^•` being a
retract of the direct image of a logarithmic de Rham complex along a finite cover.

In negative degrees the cohomology of a sheaf vanishes, so every map is onto there.

## Main results

* `MMP.LcBpf.finite_Hc_single0_X_of_isCModel`: the Hodge groups of a model of `C^•` are finite
  dimensional.
* `MMP.LcBpf.surjective_homology_map_divisorialSheafInclusion_of_isTwistInclusion`: the inclusion
  `𝒪_V(-M') ⟶ 𝒪_V(-M)` is onto on `H^q(V, -)`.
* `MMP.LcBpf.subsingleton_homology_derivedGlobalSectionsOver_single_of_neg`: `H^i(X, ℱ) = 0` for
  `i < 0`.
* `MMP.LcBpf.surjective_homology_map_of_neg`: every map of sheaves is onto on `H^i(X, -)` for
  `i < 0`.

## References

* [H. Esnault, E. Viehweg, *Lectures on vanishing theorems*][EsnaultViehweg1992]
* [J. Kollár and S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998],
  proof of Theorem 2.47
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace MMP.LcBpf

open MMP.Mori MMP.FourfoldProofs.FractionalLogComplexProof MMP.FourfoldProofs.LogDegenerationProof
  MMP.Mori.Divisor.LogSpreadingProof

section Edge

variable (n : ℕ) {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ))
  [SmoothOfRelativeDimension n π] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
  [CompactSpace V]

/-- **The Hodge groups of `C^•` are finite dimensional.** For a model `K` of the fractional
logarithmic complex on an integral `V`, each `H^j(V, K^p)` is a finite-dimensional `ℂ`-vector
space. -/
theorem finite_Hc_single0_X_of_isCModel (hπ : IsProjective π) (D : Divisor V)
    (hD : D.IsRelativeSNC n π) (S Bn : Divisor V) (hS : 0 ≤ S)
    (hSB : ∀ E, D E = S E + if Bn E = 0 then 0 else 1) (N : ℕ) (hN : 0 < N)
    (hB : ∀ E, 0 ≤ Bn E ∧ Bn E < N) (M : Divisor V) (ψ : (RationalFunctions V)ˣ)
    (hψ : (N : ℤ) • M = Bn + principalDivisor ψ) (u : Γ(V, cU' D M))
    (hu : (toRationalFunctionsPresheaf V).app (op (cU' D M)) u = ratRes (cU' D M) ψ)
    {K : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ}
    {F : ℕ → V.Modules}
    {e : ∀ p, K.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
      (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F p)}
    {ι : ∀ (p : ℕ) (W : V.Opens), (F p).val.obj (op W) →
      ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
        (op (OO D M W))}
    (hK : IsCModel n π D hD S M N u K F e ι) (p : ℕ) (j : ℤ) :
    Module.Finite Γ(Spec (CommRingCat.of ℂ), ⊤) (Hc π (single0 π (K.X p)) j) := by
  obtain ⟨V', g, _, _, S', hS', hgπ, a, r, har⟩ :=
    retract_of_isIntegral n π hπ D hD S Bn hS hSB N hN hB M ψ hψ u hu K F e ι hK
  have h1 := (finite_and_finrank_Hc_single0_relDirectImage n π g S' hS' hπ hgπ p j).1
  rw [(finite_and_finrank_hypSheafFunctor π _ j).1] at h1
  rw [(finite_and_finrank_hypSheafFunctor π _ j).1]
  have hsurj : Function.Surjective ((hypSheafFunctor π j).map (r.f p)).hom := by
    intro x
    refine ⟨((hypSheafFunctor π j).map (a.f p)).hom x, ?_⟩
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, ← HomologicalComplex.comp_f, har]
    simp
    rfl
  haveI : Module.Finite Γ(Spec (CommRingCat.of ℂ), ⊤)
      ((hypSheafFunctor π j).obj ((((relDirectImage g π).mapHomologicalComplex _).obj
        (Divisor.relativeLogDeRhamComplex n (g ≫ π) S' hS' S'.suppIdeal)).X p)) := h1
  exact Module.Finite.of_surjective ((hypSheafFunctor π j).map (r.f p)).hom hsurj

/-- **The inclusion of the degree-zero terms of a twist of `C^•` is onto on cohomology.** Let `K` be a model
of `C^•` for `M` and `K'` a model for `M'`, both with `S = 0`, with `-M' ≤ -M` and the same open
`V ∖ (D ∪ Supp M)`, and `φ : K' ⟶ K` a quasi-isomorphism commuting with the embeddings into
the forms. If `B = Bn/N` has coefficients in `[0, 1)` and support `D`, then
`𝒪_V(-M') ⟶ 𝒪_V(-M)` is surjective on `H^q(V, -)`. -/
theorem surjective_homology_map_divisorialSheafInclusion_of_isTwistInclusion
    [HasDerivedCategory V.Modules] [HasDerivedCategory (ModuleCat.{0} ℂ)]
    (hπ : IsProjective π) (D : Divisor V) (hD : D.IsRelativeSNC n π) (Bn : Divisor V)
    (hSB : ∀ E, D E = (0 : Divisor V) E + if Bn E = 0 then 0 else 1) (N : ℕ) (hN : 0 < N)
    (hB : ∀ E, 0 ≤ Bn E ∧ Bn E < N) (M : Divisor V) (ψ : (RationalFunctions V)ˣ)
    (hψ : (N : ℤ) • M = Bn + principalDivisor ψ) (u : Γ(V, cU' D M))
    (hu : (toRationalFunctionsPresheaf V).app (op (cU' D M)) u = ratRes (cU' D M) ψ)
    {K : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ}
    {F : ℕ → V.Modules}
    {e : ∀ p, K.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
      (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F p)}
    {ι : ∀ (p : ℕ) (W : V.Opens), (F p).val.obj (op W) →
      ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
        (op (OO D M W))}
    (hK : IsCModel n π D hD 0 M N u K F e ι)
    {M' : Divisor V} {N' : ℕ} {u' : Γ(V, cU' D M')}
    {K' : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ}
    {F' : ℕ → V.Modules}
    {e' : ∀ p, K'.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
      (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F' p)}
    {ι' : ∀ (p : ℕ) (W : V.Opens), (F' p).val.obj (op W) →
      ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
        (op (OO D M' W))}
    (hK' : IsCModel n π D hD 0 M' N' u' K' F' e' ι') (hM : cU' D M' = cU' D M)
    (hle : -M' ≤ -M) (φ : K' ⟶ K) [QuasiIso φ] (hφ : IsTwistInclusion π D M M' hM e e' ι ι' φ)
    (q : ℕ) :
    Function.Surjective ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℂ) q).map
      ((derivedGlobalSectionsOver π).map
        ((DerivedCategory.singleFunctor V.Modules 0).map
          (Divisor.divisorialSheafInclusion hle)))).hom := by
  have hdeg := (Divisor.finrank_hypercohomology_eq_sum_of_fractionalLogComplex n π hπ D hD 0 Bn
    le_rfl hSB N hN hB M ψ hψ u hu).2 K F e ι hK q
  exact surjective_derivedGlobalSectionsOver_map_of_quasiIso π
    (SheafOfModules.underlyingRingHom (φ := AlgebraicGeometry.inverseImageStructureMap π)) φ
    (Divisor.divisorialSheafInclusion hle) (degreeZeroRestrictIso hK') (degreeZeroRestrictIso hK)
    (degreeZeroRestrictIso_comp_twist hK hK' hM hle φ hφ) q
    (fun p _ => finite_Hc_single0_X_of_isCModel n π hπ D hD 0 Bn le_rfl hSB N hN hB M ψ hψ u hu
      hK p _) hdeg

end Edge

section Congr

/-- For `A = A'`, the images under any functor `G` of the inclusions `𝒪_X(A) ⟶ 𝒪_X(B)` and
`𝒪_X(A') ⟶ 𝒪_X(B)` are surjective together. -/
theorem surjective_map_divisorialSheafInclusion_congr {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] {R : Type} [Ring R] (G : X.Modules ⥤ ModuleCat.{0} R) {A A' B : Divisor X}
    (hA : A = A') (h : A ≤ B) (h' : A' ≤ B) :
    Function.Surjective (G.map (Divisor.divisorialSheafInclusion h)).hom ↔
      Function.Surjective (G.map (Divisor.divisorialSheafInclusion h')).hom := by
  subst hA
  rfl

end Congr

section Negative

open scoped Stacks.SmallDerivedModel

/-- **Cohomology vanishes in negative degrees**: `H^i(X, ℱ) = 0` for `i < 0`. -/
theorem subsingleton_homology_derivedGlobalSectionsOver_single_of_neg {k : Type} [Field k]
    {X : Scheme.{0}} (f : X ⟶ Spec (.of k)) (F : X.Modules) {i : ℤ} (hi : i < 0) :
    Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{0} k) i).obj
      ((derivedGlobalSectionsOver f).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F))) := by
  letI : Linear k X.Modules := Scheme.Modules.linearOverBase f
  letI : Functor.Linear k (globalSectionsOver f) := globalSectionsOver_linear_linearOverBase f
  haveI := DerivedCategory.TStructure.t.isGE_shift
    ((DerivedCategory.singleFunctor X.Modules 0).obj F) 0 i (-i) (by omega)
  haveI : Subsingleton (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor X.Modules 0).obj (Stacks.Ample.unitModule X))
      ((DerivedCategory.singleFunctor X.Modules 0).obj F) i) :=
    ⟨fun a b => by
      rw [DerivedCategory.TStructure.t.zero a 0 (-i) (by omega),
        DerivedCategory.TStructure.t.zero b 0 (-i) (by omega)]⟩
  exact (Stacks.Duality.nonempty_derivedCohomologyOverFieldLinearEquivExtUnit f
    ((DerivedCategory.singleFunctor X.Modules 0).obj F) i).some.toEquiv.subsingleton

/-- **Every map is onto on `H^i(X, -)` for `i < 0`**, the target being zero. -/
theorem surjective_homology_map_of_neg {k : Type} [Field k] {X : Scheme.{0}}
    (f : X ⟶ Spec (.of k)) {F G : X.Modules} (g : F ⟶ G) {i : ℤ} (hi : i < 0) :
    Function.Surjective ((DerivedCategory.homologyFunctor (ModuleCat.{0} k) i).map
      ((derivedGlobalSectionsOver f).map
        ((DerivedCategory.singleFunctor X.Modules 0).map g))).hom := by
  haveI := subsingleton_homology_derivedGlobalSectionsOver_single_of_neg f G hi
  exact fun y => ⟨0, Subsingleton.elim _ _⟩

end Negative

end MMP.LcBpf
