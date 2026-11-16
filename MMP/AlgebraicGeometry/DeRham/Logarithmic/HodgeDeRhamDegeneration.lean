module
public import MMP.Attr
public import MMP.AlgebraicGeometry.DeRham.Logarithmic.RelativeLogDeRhamComplex
import MMP.AlgebraicGeometry.DeRham.Logarithmic.DeligneIllusieReduction

/-!
# Degeneration of the logarithmic Hodge-to-de Rham spectral sequence

Let `V` be a smooth projective variety over `ℂ` and `S` a reduced simple normal crossing divisor
on `V`. The Hodge-to-de Rham spectral sequences
`E_1^{i,q} = H^q(V, Ω^i_V(log S)) ⇒ ℍ^{i+q}(V, Ω^•_V(log S))` and
`E_1^{i,q} = H^q(V, Ω^i_V(log S)(-S)) ⇒ ℍ^{i+q}(V, Ω^•_V(log S)(-S))`, the spectral sequences of
the stupid filtrations, both degenerate at `E₁`. The proof spreads `(V, S)` out over a finitely
generated subring of `ℂ`, reduces modulo a large prime and applies the decomposition theorem of
Deligne and Illusie to a lift over the Witt vectors of length two.

## Main results

* `MMP.Mori.Divisor.finrank_hypercohomology_relativeLogDeRhamComplex_eq_sum`: for both
  complexes, `dim_ℂ ℍ^k(V, Ω^•) = ∑_{p+q=k} dim_ℂ H^q(V, Ω^p)` for every `k`.

## Implementation notes

* The variety is a scheme `V` with a morphism `π : V ⟶ Spec ℂ` smooth of relative dimension `n`
  and projective; integrality is not needed. A reduced snc divisor is a relative snc divisor
  over `Spec ℂ` (`MMP.Mori.Divisor.IsRelativeSNC`, which includes reducedness). The complexes
  are `MMP.Mori.Divisor.relativeLogDeRhamComplex` for the ideals `⊤` and `S.suppIdeal`; the
  Boolean `twist` selects the second.
* Degeneration at `E₁` is stated as the equality
  `dim ℍ^k(V, K) = ∑_{p ≤ k} dim H^{k-p}(V, K^p)`. All these spaces are finite dimensional because
  `V` is projective, and `E_∞` is a subquotient of `E_1` of the same total dimension exactly
  when every differential `d_r`, `r ≥ 1`, vanishes, so the equality is equivalent to
  degeneration at `E₁`.
* Hypercohomology is the right derived functor of global sections on sheaves of
  `π⁻¹𝒪_{Spec ℂ}`-modules, read over `Γ(Spec ℂ, ⊤) = ℂ`, as in
  `MMP.Mori.Divisor.exists_isRelativeSNC_model_finrank_hypercohomology_eq`; the Hodge group
  `H^q(V, K^p)` is the hypercohomology of `K^p` placed in degree `0`.

## References

* [P. Deligne, L. Illusie, *Relèvements modulo p² et décomposition du complexe de de
  Rham*][DeligneIllusie1987]
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

open CategoryTheory AlgebraicGeometry Opposite

attribute [local instance] HasDerivedCategory.standard

namespace MMP.Mori.Divisor

/-- **Logarithmic Hodge-to-de Rham degeneration.** Let `π : V ⟶ Spec ℂ` be smooth of relative
dimension `n` and projective, and `S` a (reduced) simple normal crossing divisor on `V`. Then for
`K = Ω^•_V(log S)` and for `K = Ω^•_V(log S)(-S)` the Hodge-to-de Rham spectral sequence
`H^q(V, K^p) ⇒ ℍ^{p+q}(V, K)` degenerates at `E₁`:
`dim_ℂ ℍ^k(V, K) = ∑_{p ≤ k} dim_ℂ H^{k-p}(V, K^p)` for every `k`. -/
@[mmp "lem_mmp_lc_bpf_log_degeneration"]
public theorem finrank_hypercohomology_relativeLogDeRhamComplex_eq_sum (n : ℕ) {V : Scheme.{0}}
    (π : V ⟶ Spec (CommRingCat.of ℂ)) [SmoothOfRelativeDimension n π] (hπ : IsProjective π)
    (S : Divisor V) (hS : S.IsRelativeSNC n π) (twist : Bool) (k : ℕ) :
    -- `ℍ^j(V, L)` over `Γ(Spec ℂ, ⊤) = ℂ`, for a bounded below complex of `π⁻¹𝒪`-modules
    let H : CochainComplex.Plus (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) →
        ℤ → ModuleCat.{0} Γ(Spec (CommRingCat.of ℂ), ⊤) := fun L j =>
      let Γd := (SheafOfModules.evaluation.{0} (SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj (Spec (CommRingCat.of ℂ)).sheaf))
          (op ⊤)).rightDerivedFunctorPlus
      let Mj := (DerivedCategory.homologyFunctor _ j).obj
        (DerivedCategory.Plus.ι.obj (Γd.obj (DerivedCategory.Plus.Q.obj L)))
      (ModuleCat.restrictScalars.{0} (show Γ(Spec (CommRingCat.of ℂ), ⊤) →+*
          ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj
            (Spec (CommRingCat.of ℂ)).sheaf).obj.obj (op ⊤) from
        (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{0} π.base).unit.app
          (Spec (CommRingCat.of ℂ)).sheaf).hom.app (op ⊤)).hom)).obj Mj
    -- `Ω^•_V(log S)`, resp. `Ω^•_V(log S)(-S)`
    let K := relativeLogDeRhamComplex n π S hS (bif twist then S.suppIdeal else ⊤)
    Module.finrank Γ(Spec (CommRingCat.of ℂ), ⊤)
        (H ⟨K.extend ComplexShape.embeddingUpNat, 0,
          CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ k) =
      ∑ p ∈ Finset.range (k + 1), Module.finrank Γ(Spec (CommRingCat.of ℂ), ⊤)
        (H ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (K.X p), 0,
          (CochainComplex.isStrictlyGE_iff _ 0).2 fun i hi =>
            HomologicalComplex.isZero_single_obj_X _ 0 _ i (by omega)⟩ ((k - p : ℕ) : ℤ)) :=
  MMP.FourfoldProofs.LogDegenerationProof.solution n π hπ S hS twist k

end MMP.Mori.Divisor
