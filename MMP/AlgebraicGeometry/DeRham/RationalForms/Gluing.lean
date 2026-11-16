module

public import MMP.AlgebraicGeometry.Divisor.AlgebraicHartogsUnits
public import MMP.AlgebraicGeometry.DeRham.RationalForms.Separation

/-!
# Forms with a prescribed rational form

Let `X` be an integral scheme, smooth over a field `k`, with function field `K`, and `β` a
rational `q`-form, an element of `⋀^q Ω_{K/k}`. If every point of an open `O` has an affine
neighbourhood `W ⊆ O` carrying a form whose rational form is `β`, then there is a form `ω` on `O`
whose restriction to every non-empty affine open inside `O` has rational form `β`: the local forms
agree on overlaps, since a form is determined by its rational forms
(`MMP.FourfoldProofs.FractionalLogComplexProof.eq_of_ratForm_eq`), and glue.

The local forms come from the algebraic Hartogs property of the normal scheme `X`: a rational
function lying in the local ring `𝒪_{X,E}` of every prime divisor `E` meeting a non-empty open
`W` is regular on `W`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_germToFunctionField_eq_of_forall_localRing`:
  algebraic Hartogs, with the local rings of the prime divisors.
* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_form_of_forall_ratForm_eq`: the gluing.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite KaehlerDifferential TopologicalSpace

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology

universe u

/-- **Algebraic Hartogs**, with the local rings of the prime divisors: on a normal integral
locally Noetherian scheme, a rational function in the local ring `𝒪_{X,E}` of every prime divisor
`E` meeting the non-empty open `W` is regular on `W`. -/
theorem exists_germToFunctionField_eq_of_forall_localRing {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (W : X.Opens) [Nonempty W] (φ : X.functionField)
    (h : ∀ E : MMP.Mori.PrimeDivisor X, (E.support ∩ W).Nonempty →
      φ ∈ (algebraMap E.localRing X.functionField).range) :
    ∃ s : Γ(X, W), X.germToFunctionField W s = φ := by
  rcases eq_or_ne φ 0 with rfl | hφ
  · exact ⟨0, map_zero _⟩
  refine MMP.Threefold.Bridges.exists_germToFunctionField_eq_of_forall_zero_le_ord W φ
    fun E hE => ?_
  have hv := (E.divisorialValuation_le_one_iff φ).2 (h E hE)
  rw [E.divisorialValuation_eq_exp_neg_ord hφ, ← WithZero.exp_zero, WithZero.exp_le_exp] at hv
  linarith

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- Restricting twice is restricting once. -/
theorem forms_map_map (q : ℕ) {O₁ O₂ O₃ : X.Opens} (h₁ : O₂ ≤ O₁) (h₂ : O₃ ≤ O₂)
    (θ : Γ(sX.relativeDifferentialForms (q : ℤ), O₁)) :
    (sX.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE h₂).op
        ((sX.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE h₁).op θ) =
      (sX.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE (h₂.trans h₁)).op θ := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- **Gluing forms with a prescribed rational form.** On an integral scheme smooth over `k`, if
every point of the open `O` has an affine neighbourhood `W ⊆ O` carrying a `q`-form with rational
form `β`, then some `q`-form on `O` has rational form `β` on every non-empty affine open inside
`O`. -/
theorem exists_form_of_forall_ratForm_eq [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension m sX]
    (q : ℕ) {O : X.Opens}
    (β : letI := MMP.Mori.functionFieldAlgebra sX; ⋀[X.functionField]^q Ω[X.functionField⁄k])
    (h : ∀ x ∈ O, ∃ W : X.affineOpens, x ∈ (W : X.Opens) ∧ (W : X.Opens) ≤ O ∧
      ∃ ω : Γ(sX.relativeDifferentialForms (q : ℤ), W),
        ∀ _ : Nonempty (W : X.Opens), ratForm sX q W ω = β) :
    ∃ θ : Γ(sX.relativeDifferentialForms (q : ℤ), O),
      ∀ (W : X.affineOpens) (hW : (W : X.Opens) ≤ O) [Nonempty (W : X.Opens)],
        ratForm sX q W ((sX.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hW).op θ) =
          β := by
  choose Wx hxW hWO ωx hωx using h
  let U : O → X.Opens := fun x => (Wx x.1 x.2 : X.Opens)
  let F : TopCat.Sheaf Ab.{u} X :=
    ⟨(sX.relativeDifferentialForms (q : ℤ)).presheaf,
      (sX.relativeDifferentialForms (q : ℤ)).isSheaf⟩
  have hloc : ∀ (x : O) (W : X.affineOpens) (hW : (W : X.Opens) ≤ U x) [Nonempty (W : X.Opens)],
      ratForm sX q W ((sX.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hW).op
        (ωx x.1 x.2)) = β := by
    intro x W hW _
    have : Nonempty ((Wx x.1 x.2 : X.affineOpens) : X.Opens) := ⟨⟨x.1, hxW x.1 x.2⟩⟩
    rw [ratForm_restrict sX q hW]
    exact hωx x.1 x.2 this
  have hcomp' : ∀ x y : O,
      (sX.relativeDifferentialForms (q : ℤ)).presheaf.map
          (homOfLE (inf_le_left : U x ⊓ U y ≤ U x)).op (ωx x.1 x.2) =
        (sX.relativeDifferentialForms (q : ℤ)).presheaf.map
          (homOfLE (inf_le_right : U x ⊓ U y ≤ U y)).op (ωx y.1 y.2) := by
    intro x y
    refine eq_of_ratForm_eq sX (m := m) q _ _ fun W hW _ => ?_
    rw [forms_map_map, forms_map_map, hloc x W, hloc y W]
  have hcomp : TopCat.Presheaf.IsCompatible F.1 U fun x => ωx x.1 x.2 := hcomp'
  obtain ⟨θ, hθ, -⟩ := F.existsUnique_gluing' U O (fun x => homOfLE (hWO x.1 x.2))
    (fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxW x hx⟩) (fun x => ωx x.1 x.2) hcomp
  refine ⟨θ, fun W hW _ => ?_⟩
  obtain ⟨⟨x, hxW'⟩⟩ := ‹Nonempty (W : X.Opens)›
  have hxO : x ∈ O := hW hxW'
  obtain ⟨_, ⟨W₃, hW₃, rfl⟩, hxW₃, hW₃le⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ ((W : X.Opens) ⊓ U ⟨x, hxO⟩ : X.Opens) from ⟨hxW', hxW x hxO⟩)
      ((W : X.Opens) ⊓ U ⟨x, hxO⟩).isOpen
  let W' : X.affineOpens := ⟨W₃, hW₃⟩
  have h1 : (W' : X.Opens) ≤ W := fun y hy => (hW₃le hy).1
  have h2 : (W' : X.Opens) ≤ U ⟨x, hxO⟩ := fun y hy => (hW₃le hy).2
  have : Nonempty (W' : X.Opens) := ⟨⟨x, hxW₃⟩⟩
  rw [← ratForm_restrict sX q h1, forms_map_map, ← hloc ⟨x, hxO⟩ W' h2, ← hθ ⟨x, hxO⟩,
    forms_map_map]

end MMP.FourfoldProofs.FractionalLogComplexProof
