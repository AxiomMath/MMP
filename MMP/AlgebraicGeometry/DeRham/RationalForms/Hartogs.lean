module

public import MMP.AlgebraicGeometry.DeRham.RationalForms.Gluing
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.AdaptedBases

/-!
# Algebraic Hartogs for differential forms

Let `X` be a normal integral scheme, smooth over a field `k`, with function field `K`. A rational
`q`-form `β ∈ ⋀^q Ω_{K/k}` which, at every prime divisor `E` meeting an open `O`, comes from a
form of the local ring `𝒪_{X,E}`, is the rational form of a `q`-form on `O`.

On an affine open `W` on which `Ω_{X/k}` is free with basis `b`, the forms of `Γ(X, W)`, of a
local ring `𝒪_{X,E}` and of `K` are those whose coordinates in the wedges of `b` lie in
`Γ(X, W)`, `𝒪_{X,E}` and `K`; so the statement on `W` is the algebraic Hartogs property of the
coordinates. The forms on the affine opens glue
(`MMP.FourfoldProofs.FractionalLogComplexProof.exists_form_of_forall_ratForm_eq`).

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.mem_range_mapExteriorPower_iff`: the forms coming from
  `A` are those with coordinates in `A`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_form_of_forall_primeDivisor`: algebraic Hartogs
  for forms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite KaehlerDifferential

namespace MMP.FourfoldProofs.FractionalLogComplexProof

universe u

section Algebra

variable (k : Type u) [Field k] {A B : Type u} [CommRing A] [CommRing B] [Algebra k A]
  [Algebra k B] [Algebra A B] [IsScalarTower k A B]

/-- The wedges of a base-changed basis of the Kähler differentials are the images of the wedges. -/
theorem exteriorPower_isBaseChange_basis_apply
    (h : IsBaseChange B (KaehlerDifferential.map k k A B)) {ι : Type*} [LinearOrder ι]
    (b : Module.Basis ι A Ω[A⁄k]) (p : ℕ) (s : Set.powersetCard ι p) :
    (h.basis b).exteriorPower p s = mapExteriorPower k A B p (b.exteriorPower p s) := by
  rw [exteriorPower.basis_apply, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorPower.ιMulti_family, mapExteriorPower_ιMulti]
  congr 1
  funext i
  simp [IsBaseChange.basis_apply]

/-- The coordinates of the image of a form of `A` are the images of its coordinates. -/
theorem repr_mapExteriorPower (h : IsBaseChange B (KaehlerDifferential.map k k A B))
    {ι : Type*} [LinearOrder ι] (b : Module.Basis ι A Ω[A⁄k]) (p : ℕ) (α : ⋀[A]^p (Ω[A⁄k]))
    (s : Set.powersetCard ι p) :
    ((h.basis b).exteriorPower p).repr (mapExteriorPower k A B p α) s =
      algebraMap A B ((b.exteriorPower p).repr α s) := by
  classical
  have key : ((((h.basis b).exteriorPower p).coord s).restrictScalars A).comp
      (mapExteriorPower k A B p) = (Algebra.linearMap A B).comp ((b.exteriorPower p).coord s) := by
    refine (b.exteriorPower p).ext fun t => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
      Module.Basis.coord_apply, Module.Basis.repr_self, Algebra.linearMap_apply,
      ← exteriorPower_isBaseChange_basis_apply k h b p t]
    rw [Finsupp.single_apply, Finsupp.single_apply]
    split_ifs <;> simp
  exact congrArg (fun φ => φ α) key

/-- **The forms coming from `A` are those with coordinates in `A`.** -/
theorem mem_range_mapExteriorPower_iff (h : IsBaseChange B (KaehlerDifferential.map k k A B))
    {ι : Type*} [LinearOrder ι] [Finite ι] (b : Module.Basis ι A Ω[A⁄k]) (p : ℕ)
    (β : ⋀[B]^p (Ω[B⁄k])) :
    β ∈ Set.range (mapExteriorPower k A B p) ↔
      ∀ s, ((h.basis b).exteriorPower p).repr β s ∈ (algebraMap A B).range := by
  classical
  have := Fintype.ofFinite ι
  constructor
  · rintro ⟨α, rfl⟩ s
    exact ⟨_, (repr_mapExteriorPower k h b p α s).symm⟩
  · intro hβ
    choose a ha using hβ
    refine ⟨∑ s, a s • b.exteriorPower p s, ?_⟩
    rw [map_sum]
    conv_rhs => rw [← ((h.basis b).exteriorPower p).sum_repr β]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [LinearMap.map_smul, ← exteriorPower_isBaseChange_basis_apply k h b p s, ← ha s,
      algebraMap_smul]

end Algebra

section Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- **Algebraic Hartogs for forms on an affine open with a basis of differentials.** If `W` is a
nonempty affine open on which `Ω_{Γ(X, W)/k}` has a finite basis, a rational `q`-form which at
every prime divisor `E` meeting `W` comes from a form of `𝒪_{X,E}` is the rational form of a
`q`-form on `W`. -/
theorem exists_ratForm_eq_of_forall_primeDivisor [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (q : ℕ) (W : X.affineOpens) [Nonempty (W : X.Opens)] {ι : Type*}
    [LinearOrder ι] [Finite ι]
    (b : letI := MMP.Mori.sectionAlgebra sX W; Module.Basis ι Γ(X, W) Ω[Γ(X, W)⁄k])
    (β : letI := MMP.Mori.functionFieldAlgebra sX; ⋀[X.functionField]^q Ω[X.functionField⁄k])
    (hβ : ∀ E : MMP.Mori.PrimeDivisor X, (E.support ∩ W).Nonempty →
      letI := MMP.Mori.stalkAlgebra sX E.genericPoint
      letI := MMP.Mori.functionFieldAlgebra sX
      haveI := MMP.Mori.isScalarTower_stalk_functionField sX E.genericPoint
      β ∈ Set.range (mapExteriorPower k E.localRing X.functionField q)) :
    ∃ ω : Γ(sX.relativeDifferentialForms (q : ℤ), W), ratForm sX q W ω = β := by
  classical
  let := MMP.Mori.sectionAlgebra sX W
  let := MMP.Mori.functionFieldAlgebra sX
  have := MMP.Mori.isScalarTower_section_functionField sX W
  have := functionField_isFractionRing_of_isAffineOpen X (W : X.Opens) W.2
  have hWK := isBaseChange_kaehler_fractionRing k (A := Γ(X, W)) (K := X.functionField)
  have hcoord : ∀ s, ((hWK.basis b).exteriorPower q).repr β s ∈
      (algebraMap Γ(X, W) X.functionField).range := by
    intro s
    obtain ⟨c, hc⟩ := exists_germToFunctionField_eq_of_forall_localRing (W : X.Opens)
      (((hWK.basis b).exteriorPower q).repr β s) fun E hE => by
        have hmem : E.genericPoint ∈ (W : X.Opens) := E.genericPoint_mem_of_nonempty hE
        let x : (W : X.Opens) := ⟨E.genericPoint, hmem⟩
        let := MMP.Mori.stalkAlgebra sX E.genericPoint
        let : Algebra Γ(X, W) E.localRing := TopCat.Presheaf.algebra_section_stalk X.presheaf x
        have := MMP.Mori.isScalarTower_stalk_functionField sX E.genericPoint
        have := MMP.Mori.isScalarTower_section_stalk sX (W : X.Opens) x
        have : IsScalarTower Γ(X, W) E.localRing X.functionField :=
          IsScalarTower.of_algebraMap_eq fun a =>
            (Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hmem a).symm
        have : IsLocalization.AtPrime E.localRing (W.2.primeIdealOf x).asIdeal :=
          W.2.isLocalization_stalk x
        have : Algebra.FormallyEtale Γ(X, W) E.localRing :=
          Algebra.FormallyEtale.of_isLocalization (W.2.primeIdealOf x).asIdeal.primeCompl
        have hWE := KaehlerDifferential.isBaseChange_of_formallyEtale k Γ(X, W) E.localRing
        have hEK := isBaseChange_kaehler_fractionRing k (A := E.localRing)
          (K := X.functionField)
        have hb : hEK.basis (hWE.basis b) = hWK.basis b := by
          refine Module.Basis.eq_of_apply_eq fun i => ?_
          rw [IsBaseChange.basis_apply, IsBaseChange.basis_apply, IsBaseChange.basis_apply,
            map_map_eq]
        have := (mem_range_mapExteriorPower_iff k hEK (hWE.basis b) q β).1 (hβ E hE) s
        rwa [hb] at this
    exact ⟨c, hc⟩
  obtain ⟨α, hα⟩ := (mem_range_mapExteriorPower_iff k hWK b q β).2 hcoord
  refine ⟨(MMP.DeRham.formsAlgEquiv sX q W).symm α, ?_⟩
  rwa [ratForm_apply, LinearEquiv.apply_symm_apply]

/-- **Algebraic Hartogs for forms.** On a normal integral scheme smooth over `k`, a rational
`q`-form which at every prime divisor `E` meeting the open `O` comes from a form of `𝒪_{X,E}` is
the rational form of a `q`-form on `O`. -/
theorem exists_form_of_forall_primeDivisor [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {m : ℕ} [SmoothOfRelativeDimension m sX] (q : ℕ) {O : X.Opens}
    (β : letI := MMP.Mori.functionFieldAlgebra sX; ⋀[X.functionField]^q Ω[X.functionField⁄k])
    (hβ : ∀ E : MMP.Mori.PrimeDivisor X, (E.support ∩ O).Nonempty →
      letI := MMP.Mori.stalkAlgebra sX E.genericPoint
      letI := MMP.Mori.functionFieldAlgebra sX
      haveI := MMP.Mori.isScalarTower_stalk_functionField sX E.genericPoint
      β ∈ Set.range (mapExteriorPower k E.localRing X.functionField q)) :
    ∃ θ : Γ(sX.relativeDifferentialForms (q : ℤ), O),
      ∀ (W : X.affineOpens) (hW : (W : X.Opens) ≤ O) [Nonempty (W : X.Opens)],
        ratForm sX q W ((sX.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hW).op θ) =
          β := by
  refine exists_form_of_forall_ratForm_eq sX (m := m) q β fun x hx => ?_
  obtain ⟨W, hxW, hWO, hfree⟩ := exists_affine_free_kaehler sX (m := m) hx
  refine ⟨W, hxW, hWO, ?_⟩
  have : Nonempty (W : X.Opens) := ⟨⟨x, hxW⟩⟩
  let := MMP.Mori.sectionAlgebra sX W
  have : Smooth sX := SmoothOfRelativeDimension.smooth m sX
  have : Algebra.FiniteType k Γ(X, W) := MMP.Mori.finiteType_sectionAlgebra sX W.2
  let b := (Module.Free.chooseBasis Γ(X, W) Ω[Γ(X, W)⁄k]).reindex
    (Fintype.equivFin (Module.Free.ChooseBasisIndex Γ(X, W) Ω[Γ(X, W)⁄k]))
  obtain ⟨ω, hω⟩ := exists_ratForm_eq_of_forall_primeDivisor sX q W b β fun E hE =>
    hβ E (hE.mono fun y hy => ⟨hy.1, hWO hy.2⟩)
  exact ⟨ω, fun _ => hω⟩

end Scheme

end MMP.FourfoldProofs.FractionalLogComplexProof
