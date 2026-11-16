module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Construction

/-!
# Restriction of divisors to an open subscheme

For an open `U` of a scheme `X`, a prime divisor `E` of `U` is the trace of the prime divisor of
`X` with the same generic point, `MMP.FourfoldProofs.FractionalLogComplexProof.primeDivisorOfOpens`;
this map is injective, and the restriction of a divisor `D` of `X` to `U` is
`E ↦ D (primeDivisorOfOpens U E)`.

## Main definitions

* `MMP.FourfoldProofs.FractionalLogComplexProof.primeDivisorOfOpens`: prime divisors of `U` as prime
  divisors of `X`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.restrictDivisor`: the restriction of a divisor to `U`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.restrictSection`: the restriction of a function on
  `U' = X ∖ (D ∪ Supp M)` to `U' ∩ U`, the `U'` of the restricted data.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.mem_supp_restrictDivisor_iff`,
  `MMP.FourfoldProofs.FractionalLogComplexProof.cU'_restrictDivisor`: supports restrict.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Order Opposite

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology

universe u

variable {X : Scheme.{u}} (U : X.Opens)

/-- The prime divisor of `X` with the generic point of a prime divisor of the open `U`. -/
noncomputable def primeDivisorOfOpens (E : MMP.Mori.PrimeDivisor U) : MMP.Mori.PrimeDivisor X :=
  AlgebraicGeometry.PrimeDivisor.ofCoheightOne (U.ι E.genericPoint)
    ((Topology.IsOpenEmbedding.coheight_eq (x := E.genericPoint) U.ι.base
      U.ι.isOpenEmbedding).trans (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E))

/-- The generic point of `primeDivisorOfOpens U E` is the image in `X` of the generic point of
`E`. -/
theorem genericPoint_primeDivisorOfOpens (E : MMP.Mori.PrimeDivisor U) :
    (primeDivisorOfOpens U E).genericPoint = U.ι E.genericPoint :=
  AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _

/-- `primeDivisorOfOpens U` is injective. -/
theorem primeDivisorOfOpens_injective : Function.Injective (primeDivisorOfOpens U) := by
  intro E F h
  apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
  have h1 := congrArg AlgebraicGeometry.PrimeDivisor.genericPoint h
  change (primeDivisorOfOpens U E).genericPoint = (primeDivisorOfOpens U F).genericPoint at h1
  rw [genericPoint_primeDivisorOfOpens, genericPoint_primeDivisorOfOpens] at h1
  exact U.ι.isOpenEmbedding.injective h1

/-- The restriction of a divisor `D` on `X` to the open `U`: its coefficient at a prime divisor `E`
of `U` is the coefficient of `D` at `primeDivisorOfOpens U E`. -/
noncomputable def restrictDivisor {R : Type*} [Zero R] (D : MMP.Mori.DivisorWithCoeffs R X) :
    MMP.Mori.DivisorWithCoeffs R U :=
  D.comapDomain (primeDivisorOfOpens U) (primeDivisorOfOpens_injective U).injOn

/-- The coefficient of `restrictDivisor U D` at a prime divisor `E` of `U` is the coefficient of
`D` at `primeDivisorOfOpens U E`. -/
@[simp]
theorem restrictDivisor_apply {R : Type*} [Zero R] (D : MMP.Mori.DivisorWithCoeffs R X)
    (E : MMP.Mori.PrimeDivisor U) : restrictDivisor U D E = D (primeDivisorOfOpens U E) :=
  Finsupp.comapDomain_apply _ _ _ _

/-- A point of `U` lies on a prime divisor of `U` exactly when its image lies on the
corresponding prime divisor of `X`. -/
theorem mem_support_primeDivisorOfOpens_iff (E : MMP.Mori.PrimeDivisor U) (x : U.toScheme) :
    U.ι x ∈ (primeDivisorOfOpens U E).support ↔ x ∈ E.support := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  rw [show AlgebraicGeometry.PrimeDivisor.genericPoint (primeDivisorOfOpens U E) =
    U.ι (AlgebraicGeometry.PrimeDivisor.genericPoint E) from genericPoint_primeDivisorOfOpens U E,
    ← specializes_iff_mem_closure, ← specializes_iff_mem_closure]
  exact U.ι.isOpenEmbedding.isInducing.specializes_iff

/-- A prime divisor of `X` through a point of `U` comes from a prime divisor of `U`. -/
theorem exists_primeDivisorOfOpens_eq (E : MMP.Mori.PrimeDivisor X) {x : U.toScheme}
    (hx : U.ι x ∈ E.support) : ∃ E' : MMP.Mori.PrimeDivisor U, primeDivisorOfOpens U E' = E := by
  have h1 : E.genericPoint ⤳ U.ι x := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hx
  have hmem : E.genericPoint ∈ Set.range U.ι.base :=
    h1.mem_open U.ι.isOpenEmbedding.isOpen_range ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hmem
  have hcoh : coheight y = 1 := by
    rw [← Topology.IsOpenEmbedding.coheight_eq (x := y) U.ι.base U.ι.isOpenEmbedding, hy]
    exact AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hcoh,
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective ?_⟩
  change (primeDivisorOfOpens U _).genericPoint = E.genericPoint
  rw [genericPoint_primeDivisorOfOpens]
  exact (congrArg U.ι (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y hcoh)).trans hy

/-- A point `x` of `U` lies in the support of `restrictDivisor U D` iff `U.ι x` lies in the
support of `D`. -/
theorem mem_supp_restrictDivisor_iff {R : Type*} [Zero R] (D : MMP.Mori.DivisorWithCoeffs R X)
    (x : U.toScheme) : x ∈ (restrictDivisor U D).supp ↔ U.ι x ∈ D.supp := by
  rw [MMP.Mori.DivisorWithCoeffs.mem_supp_iff, MMP.Mori.DivisorWithCoeffs.mem_supp_iff]
  constructor
  · rintro ⟨E, hE, hx⟩
    exact ⟨primeDivisorOfOpens U E, hE, (mem_support_primeDivisorOfOpens_iff U E x).2 hx⟩
  · rintro ⟨E, hE, hx⟩
    obtain ⟨E', rfl⟩ := exists_primeDivisorOfOpens_eq U E hx
    exact ⟨E', hE, (mem_support_primeDivisorOfOpens_iff U E' x).1 hx⟩

/-- `cU'` of the restrictions of `D` and `M` to `U` is the preimage under `U.ι` of `cU' D M`. -/
theorem cU'_restrictDivisor (D M : MMP.Mori.Divisor X) :
    cU' (restrictDivisor U D) (restrictDivisor U M) = U.ι ⁻¹ᵁ cU' D M := by
  ext x
  change x ∉ ((restrictDivisor U D).supp ⊔ (restrictDivisor U M).supp :
      TopologicalSpace.Closeds U) ↔ U.ι x ∉ (D.supp ⊔ M.supp : TopologicalSpace.Closeds X)
  exact not_congr (or_congr (mem_supp_restrictDivisor_iff U D x)
    (mem_supp_restrictDivisor_iff U M x))

/-- The restriction of a section of `𝒪_X` over `cU' D M` to a section of `𝒪_U` over
`cU' (restrictDivisor U D) (restrictDivisor U M)`. -/
noncomputable def restrictSection (D M : MMP.Mori.Divisor X) (u : Γ(X, cU' D M)) :
    Γ(U.toScheme, cU' (restrictDivisor U D) (restrictDivisor U M)) :=
  U.toScheme.presheaf.map (homOfLE (cU'_restrictDivisor U D M).le).op (U.ι.app (cU' D M) u)

/-- An open subscheme of a scheme smooth of relative dimension `n` is smooth of relative
dimension `n`. -/
instance smoothOfRelativeDimension_opens_ι (n : ℕ) {T : Scheme.{u}} (f : X ⟶ T)
    [SmoothOfRelativeDimension n f] : SmoothOfRelativeDimension n (U.ι ≫ f) := by
  have h := (inferInstance : SmoothOfRelativeDimension (0 + n) (U.ι ≫ f))
  rwa [zero_add] at h

end MMP.FourfoldProofs.FractionalLogComplexProof
