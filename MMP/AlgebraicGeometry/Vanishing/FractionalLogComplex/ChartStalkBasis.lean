module

public import MMP.AlgebraicGeometry.DeRham.FormsSectionsAlgebra

/-!
# The coordinate differentials of a chart at the points of the chart

Let `W` be an affine open of a scheme `X` over a field `k` whose Kähler differentials, relative to
an affine open `V` of `Spec k`, have the basis `dt₁, …, dtₙ` for coordinates `tᵢ ∈ Γ(X, W)`, as in
a chart of a relative simple normal crossing divisor. Since `V = Spec k`, this is a basis of
`Ω_{Γ(X, W)/k}`, and its image in the Kähler differentials of every local ring `𝒪_{X,x}`, `x ∈ W`,
is the basis `d tᵢ` of `Ω_{𝒪_{X,x}/k}`: the local ring is a localization of `Γ(X, W)`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_basis_D_section_of_chart`: the basis over `k`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_basis_D_stalk_of_chart`: the basis at a point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite KaehlerDifferential

namespace MMP.FourfoldProofs.FractionalLogComplexProof

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **A chart basis is a basis over `k`.** If `W` is nonempty and the differentials `d tᵢ` form a
basis of `Ω_{Γ(X, W)/Γ(Spec k, V)}`, then they form a basis of `Ω_{Γ(X, W)/k}`. -/
theorem exists_basis_D_section_of_chart {n : ℕ} (W : X.affineOpens) [Nonempty (W : X.Opens)]
    (V : (Spec (.of k)).affineOpens) (e : (W : X.Opens) ≤ f ⁻¹ᵁ (V : (Spec (.of k)).Opens))
    (t : Fin n → Γ(X, W))
    (hb : letI := (f.appLE V W e).hom.toAlgebra
      ∃ b : Module.Basis (Fin n) Γ(X, W) Ω[Γ(X, W)⁄Γ(Spec (.of k), V)],
        ∀ i, b i = KaehlerDifferential.D Γ(Spec (.of k), V) Γ(X, W) (t i)) :
    letI := MMP.Mori.sectionAlgebra f W
    ∃ b : Module.Basis (Fin n) Γ(X, W) Ω[Γ(X, W)⁄k], ∀ i, b i = D k Γ(X, W) (t i) := by
  obtain ⟨V, hVa⟩ := V
  have hV : V = ⊤ := by
    obtain ⟨⟨x, hx⟩⟩ := ‹Nonempty (W : X.Opens)›
    exact eq_top_iff.2 fun z _ => Subsingleton.elim (f x) z ▸ e hx
  subst hV
  let := MMP.Mori.sectionAlgebra f W
  obtain ⟨b, hb⟩ := hb
  refine ⟨b.map (MMP.DeRham.kaehlerSpecEquiv f W), fun i => ?_⟩
  change (MMP.DeRham.kaehlerSpecEquiv f W) (b i) = _
  exact (congrArg (MMP.DeRham.kaehlerSpecEquiv f W) (hb i)).trans
    (MMP.DeRham.kaehlerBaseEquiv_d _ _ _ (t i))

/-- **A chart basis at a point.** At every point `x` of the chart, the differentials `d tᵢ` of the
germs of the coordinates are a basis of `Ω_{𝒪_{X,x}/k}`. -/
theorem exists_basis_D_stalk_of_chart {n : ℕ} (W : X.affineOpens)
    (V : (Spec (.of k)).affineOpens) (e : (W : X.Opens) ≤ f ⁻¹ᵁ (V : (Spec (.of k)).Opens))
    (t : Fin n → Γ(X, W))
    (hb : letI := (f.appLE V W e).hom.toAlgebra
      ∃ b : Module.Basis (Fin n) Γ(X, W) Ω[Γ(X, W)⁄Γ(Spec (.of k), V)],
        ∀ i, b i = KaehlerDifferential.D Γ(Spec (.of k), V) Γ(X, W) (t i))
    {x : X} (hx : x ∈ (W : X.Opens)) :
    letI := MMP.Mori.stalkAlgebra f x
    ∃ b : Module.Basis (Fin n) (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k],
      ∀ i, b i = D k (X.presheaf.stalk x) (X.presheaf.germ (W : X.Opens) x hx (t i)) := by
  have : Nonempty (W : X.Opens) := ⟨⟨x, hx⟩⟩
  let := MMP.Mori.sectionAlgebra f W
  let := MMP.Mori.stalkAlgebra f x
  obtain ⟨b, hb'⟩ := exists_basis_D_section_of_chart f W V e t hb
  let x' : (W : X.Opens) := ⟨x, hx⟩
  let : Algebra Γ(X, W) (X.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk X.presheaf x'
  have := MMP.Mori.isScalarTower_section_stalk f W x'
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (W.2.primeIdealOf x').asIdeal :=
    W.2.isLocalization_stalk x'
  have : Algebra.FormallyEtale Γ(X, W) (X.presheaf.stalk x) :=
    Algebra.FormallyEtale.of_isLocalization (W.2.primeIdealOf x').asIdeal.primeCompl
  have hbc := KaehlerDifferential.isBaseChange_of_formallyEtale k Γ(X, W) (X.presheaf.stalk x)
  refine ⟨hbc.basis b, fun i => ?_⟩
  rw [IsBaseChange.basis_apply, hb', KaehlerDifferential.map_D]
  rfl

end MMP.FourfoldProofs.FractionalLogComplexProof
