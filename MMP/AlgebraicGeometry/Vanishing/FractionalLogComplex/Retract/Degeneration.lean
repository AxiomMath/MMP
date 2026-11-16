module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Retract.Defs
public import MMP.AlgebraicGeometry.Cohomology.HypercohomologyAffineDirectImage
public import MMP.AlgebraicGeometry.DeRham.Logarithmic.HodgeDeRhamDegeneration
public import MMP.AlgebraicGeometry.DeRham.Logarithmic.DeligneIllusieReduction

/-!
# Degeneration of a retract of the direct image of a logarithmic complex

Let `π : V ⟶ Spec ℂ` be smooth projective, `g : V' ⟶ V` finite with `g ≫ π` smooth projective,
and `S'` a relative simple normal crossing divisor on `V'`. The logarithmic Hodge-to-de Rham
spectral sequence of `Ω^•_{V'}(log S')(-S')` degenerates at `E₁`; since `g` is affine, the
hypercohomology and the Hodge groups of the direct image `g_* Ω^•_{V'}(log S')(-S')` are those of
`Ω^•_{V'}(log S')(-S')`, so the direct image degenerates at `E₁` as well, and so does every
retract of it in the category of complexes of sheaves of `π⁻¹𝒪`-modules.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.finrank_hyp_relDirectImage_eq_sum`: degeneration at
  `E₁` for `g_* Ω^•_{V'}(log S')(-S')`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.fracDegeneration_of_retract`: `FracDegeneration` for
  the models of `C^•` that are retracts of `g_* Ω^•_{V'}(log S')(-S')`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology
open MMP.Mori.Divisor.LogSpreadingProof (Hc)
open MMP.FourfoldProofs.LogDegenerationProof (single0)

/-- A projective scheme over an affine scheme has affine diagonal over the terminal scheme. -/
theorem isAffineHom_diagonal_of_isProjective {V : Scheme.{u}} {R : CommRingCat.{u}}
    (π : V ⟶ Spec R) (hπ : IsProjective π) :
    IsAffineHom (pullback.diagonal (terminal.from V)) := by
  have : IsProper π := hπ.isProper
  have e : terminal.from V = π ≫ terminal.from (Spec R) := terminal.hom_ext _ _
  have : IsSeparated (terminal.from V) := by rw [e]; infer_instance
  infer_instance

/-- `Γ(Spec k, ⊤)` is a field for a field `k`. -/
theorem isField_Γ_spec_complex {k : Type u} [Field k] : IsField Γ(Spec (CommRingCat.of k), ⊤) :=
  MulEquiv.isField (Field.toIsField k)
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv

section Degeneration

variable (n : ℕ) {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ)) {V' : Scheme.{0}}
  (g : V' ⟶ V) [IsFinite g] [SmoothOfRelativeDimension n (g ≫ π)]
  (S' : MMP.Mori.Divisor V') (hS' : S'.IsRelativeSNC n (g ≫ π))

omit [IsFinite g] in
/-- Each term of `Ω^•_{V'}(log S')(-S')` is isomorphic to the pushforward along the inverse-image
base map of `g ≫ π` of a quasi-coherent `𝒪_{V'}`-module. -/
theorem exists_relativeLogDeRhamComplex_X_iso_pushforward (q : ℕ) :
    ∃ M : V'.Modules, M.IsQuasicoherent ∧
      Nonempty ((MMP.Mori.Divisor.relativeLogDeRhamComplex n (g ≫ π) S' hS' S'.suppIdeal).X q ≅
        (_root_.pushforward (Stacks.DeRhamDirectImage.toInverseImageBase (g ≫ π))).obj M) :=
  ⟨_, MMP.Mori.Divisor.LogSpreadingProof.G1.logModule_isQuasicoherent hS' true q,
    MMP.Mori.Divisor.LogSpreadingProof.G1.exists_iso_relativeLogDeRhamComplex_X hS' true q⟩

/-- The Hodge groups of the direct image `g_* Ω^p_{V'}(log S')(-S')` are finite dimensional and
have the dimensions of those of `Ω^p_{V'}(log S')(-S')`. -/
theorem finite_and_finrank_Hc_single0_relDirectImage (hπ : IsProjective π)
    (hgπ : IsProjective (g ≫ π)) (q : ℕ) (j : ℤ) :
    Module.Finite Γ(Spec (CommRingCat.of ℂ), ⊤) (Hc π (single0 π ((relDirectImage g π).obj
        ((MMP.Mori.Divisor.relativeLogDeRhamComplex n (g ≫ π) S' hS' S'.suppIdeal).X q))) j) ∧
      Module.finrank Γ(Spec (CommRingCat.of ℂ), ⊤) (Hc π (single0 π ((relDirectImage g π).obj
          ((MMP.Mori.Divisor.relativeLogDeRhamComplex n (g ≫ π) S' hS' S'.suppIdeal).X q))) j) =
        Module.finrank Γ(Spec (CommRingCat.of ℂ), ⊤) (Hc (g ≫ π) (single0 (g ≫ π)
          ((MMP.Mori.Divisor.relativeLogDeRhamComplex n (g ≫ π) S' hS' S'.suppIdeal).X q)) j) := by
  have := isAffineHom_diagonal_of_isProjective π hπ
  have := isAffineHom_diagonal_of_isProjective (g ≫ π) hgπ
  have : IsProper (g ≫ π) := hgπ.isProper
  obtain ⟨e⟩ := nonempty_Hc_single0_relDirectImage_iso g π _
    (exists_relativeLogDeRhamComplex_X_iso_pushforward n π g S' hS' q) j
  have : Module.Finite Γ(Spec (CommRingCat.of ℂ), ⊤) (Hc (g ≫ π) (single0 (g ≫ π)
      ((MMP.Mori.Divisor.relativeLogDeRhamComplex n (g ≫ π) S' hS' S'.suppIdeal).X q)) j) :=
    MMP.FourfoldProofs.LogDegenerationProof.finite_hyp_relativeLogDeRhamComplex_X n
      (Field.toIsField ℂ) (g ≫ π) S' hS' true q j
  exact ⟨Module.Finite.equiv e.toLinearEquiv.symm, e.toLinearEquiv.finrank_eq⟩

/-- **`E₁`-degeneration for the direct image** `g_* Ω^•_{V'}(log S')(-S')`: the dimension of its
`k`-th hypercohomology equals `∑_{p ≤ k} dim H^{k-p}(g_* Ω^p_{V'}(log S')(-S'))`. -/
theorem finrank_hyp_relDirectImage_eq_sum (hπ : IsProjective π) (hgπ : IsProjective (g ≫ π))
    (k : ℕ) :
    Module.finrank Γ(Spec (CommRingCat.of ℂ), ⊤) (Hc π ⟨(((relDirectImage g π).mapHomologicalComplex
        _).obj (MMP.Mori.Divisor.relativeLogDeRhamComplex n (g ≫ π) S' hS' S'.suppIdeal)).extend
          ComplexShape.embeddingUpNat, 0,
          CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ k) =
      ∑ p ∈ Finset.range (k + 1), Module.finrank Γ(Spec (CommRingCat.of ℂ), ⊤)
        (Hc π (single0 π ((((relDirectImage g π).mapHomologicalComplex _).obj
          (MMP.Mori.Divisor.relativeLogDeRhamComplex n (g ≫ π) S' hS' S'.suppIdeal)).X p))
          ((k - p : ℕ) : ℤ)) := by
  have := isAffineHom_diagonal_of_isProjective π hπ
  have := isAffineHom_diagonal_of_isProjective (g ≫ π) hgπ
  obtain ⟨e⟩ := nonempty_Hc_relDirectImage_iso g π _
    (exists_relativeLogDeRhamComplex_X_iso_pushforward n π g S' hS') k
  refine e.toLinearEquiv.finrank_eq.trans (Eq.trans ?_ (Finset.sum_congr rfl fun p _ =>
    (finite_and_finrank_Hc_single0_relDirectImage n π g S' hS' hπ hgπ p
      ((k - p : ℕ) : ℤ)).2).symm)
  exact MMP.Mori.Divisor.finrank_hypercohomology_relativeLogDeRhamComplex_eq_sum n (g ≫ π) hgπ
    S' hS' true k

end Degeneration

/-- **`FracDegeneration` from retracts.** If every model of `C^•` is a retract of
`g_* Ω^•_{V'}(log S')(-S')` in the category of complexes of sheaves of `π⁻¹𝒪`-modules, then every
model of `C^•` degenerates at `E₁`. -/
theorem fracDegeneration_of_retract (n : ℕ) {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ))
    [SmoothOfRelativeDimension n π] [IsLocallyNoetherian V] [IsNormal V]
    (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n π) (S M : MMP.Mori.Divisor V) (N : ℕ)
    (u : Γ(V, cU' D M)) {V' : Scheme.{0}} (g : V' ⟶ V) [IsFinite g]
    [SmoothOfRelativeDimension n (g ≫ π)] (S' : MMP.Mori.Divisor V')
    (hS' : S'.IsRelativeSNC n (g ≫ π)) (hπ : IsProjective π) (hgπ : IsProjective (g ≫ π))
    (hret : ∀ K F e ι, IsCModel n π D hD S M N u K F e ι →
      ∃ (i : K ⟶ ((relDirectImage g π).mapHomologicalComplex _).obj
          (MMP.Mori.Divisor.relativeLogDeRhamComplex n (g ≫ π) S' hS' S'.suppIdeal))
        (r : ((relDirectImage g π).mapHomologicalComplex _).obj
          (MMP.Mori.Divisor.relativeLogDeRhamComplex n (g ≫ π) S' hS' S'.suppIdeal) ⟶ K),
        i ≫ r = 𝟙 K) :
    FracDegeneration n π D hD S M N u := by
  intro K F e ι hK k
  obtain ⟨i, r, hir⟩ := hret K F e ι hK
  exact finrank_hyp_eq_sum_of_retract π isField_Γ_spec_complex i r hir k
    (fun p _ => (finite_and_finrank_Hc_single0_relDirectImage n π g S' hS' hπ hgπ p _).1)
    (finrank_hyp_relDirectImage_eq_sum n π g S' hS' hπ hgπ k)

end MMP.FourfoldProofs.FractionalLogComplexProof
