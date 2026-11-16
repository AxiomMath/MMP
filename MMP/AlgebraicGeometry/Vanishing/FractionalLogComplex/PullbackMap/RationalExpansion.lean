module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Place.ChartForms
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.DeRham.RationalForms.Gluing

/-!
# The rational form of a section of the fractional logarithmic complex near a point

Let `D` be a relative simple normal crossing divisor on a smooth integral `X` over `k`, `S` and
`M` divisors, and `θ` a section over `W` of `C^p = 𝒪_X(-M) · Ω^p_X(log D)(-S)`, a form on
`U ∩ W ∩ U'` (`U = X ∖ D`, `U' = X ∖ (D ∪ Supp M)`). Near every point `x ∈ W` there are an affine
open `W₃ ∋ x` inside a chart of `D` at `x`, with coordinates `tₗ`, sections `gᵢ` of `𝒪_X(-M)` over
`W₃` and functions `c_{i,K}` on `W₃` in the ideal of `S` such that the rational form of `θ` is

`∑ᵢ gᵢ ∑_K c_{i,K} β_K`,

`β_K` the wedges of the rational chart forms `tₗ⁻¹ dtₗ` (`l < r`) and `dtₗ` (`l ≥ r`), the first
`r` coordinates being local equations of the components of `D` through `x`. This is the input of
the analysis of the pull-back `θ ↦ g^*θ / z` at the prime divisors of a cover.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.genericPoint_mem_cU'`: the generic point lies in
  `U'`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_ratForm_expansion`: the local expansion of the
  rational form.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite KaehlerDifferential TopologicalSpace

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The generic point of an integral scheme lies in `U' = X ∖ (D ∪ Supp M)`. -/
theorem genericPoint_mem_cU' [IsIntegral X] (D M : MMP.Mori.Divisor X) :
    genericPoint X ∈ cU' D M := by
  change genericPoint X ∉ (D.supp ⊔ M.supp : Closeds X)
  rintro (h | h)
  · exact MMP.Fourfold.genericPoint_notMem_supp D h
  · exact MMP.Fourfold.genericPoint_notMem_supp M h

/-- A non-empty open meets `U'`. -/
theorem nonempty_inf_cU' [IsIntegral X] (D M : MMP.Mori.Divisor X) {W : X.Opens}
    (hW : Nonempty W) : Nonempty (W ⊓ cU' D M : X.Opens) := by
  obtain ⟨⟨y, hy⟩⟩ := hW
  exact ⟨⟨genericPoint X, ((genericPoint_spec X).mem_open_set_iff W.isOpen).2 ⟨y, trivial, hy⟩,
    genericPoint_mem_cU' D M⟩⟩

/-- **The local expansion of the rational form of a section of `C^p`.** Near every point `x ∈ W`
there are an affine open `W₃ ∋ x` inside a chart `WD` of `D` at `x`, sections `gᵢ` of `𝒪_X(-M)`
over `W₃` and functions `c_{i,K}` on `W₃` in the ideal of `S` such that on every non-empty affine
open of `U ∩ W₃ ∩ U'` the rational form of `θ`, in `k(X)`, is `∑ᵢ gᵢ ∑_K c_{i,K} β_K`. -/
theorem exists_ratForm_expansion [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (n : ℕ)
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f] (D : MMP.Mori.Divisor X)
    (hD : D.IsRelativeSNC n f) (S M : MMP.Mori.Divisor X) [Nonempty (cU D)] (p : ℕ)
    (W : X.Opens)
    (θ : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.obj
      (op (OO D M W)))
    (hθ : Cond n f D hD S M p W θ) {x : X} (hx : x ∈ W) :
    ∃ (W₃ : X.affineOpens) (hx₃ : x ∈ (W₃ : X.Opens)), (W₃ : X.Opens) ≤ W ∧
    ∃ (WD : X.affineOpens) (hxD : x ∈ (WD : X.Opens)) (t : Fin n → Γ(X, WD)) (r : ℕ)
      (_ : r ≤ n) (j : Fin r → MMP.Mori.PrimeDivisor X), (W₃ : X.Opens) ≤ WD ∧
      (∀ i, j i ∈ D.support ∧ x ∈ (j i).support) ∧
    ∃ (m : ℕ) (g : Fin m → Γ(X, (W₃ : X.Opens) ⊓ cU' D M))
      (c : Fin m → {K : Finset (Fin n) // K.card = p} → Γ(X, W₃)),
      (∀ i, DivCond (D := D) (M := M) (W₃ : X.Opens) (g i)) ∧
      (∀ i K, c i K ∈ S.suppIdeal.ideal W₃) ∧
      haveI : Nonempty (WD : X.Opens) := ⟨⟨x, hxD⟩⟩
      haveI : Nonempty (W₃ : X.Opens) := ⟨⟨x, hx₃⟩⟩
      haveI := nonempty_inf_cU' D M (W := (W₃ : X.Opens)) ⟨⟨x, hx₃⟩⟩
      letI := MMP.Mori.functionFieldAlgebra f
      ∀ (O : (cU D).toScheme.affineOpens) (hO : (O : (cU D).toScheme.Opens) ≤ OO D M W)
        [Nonempty (O : (cU D).toScheme.Opens)],
        (O : (cU D).toScheme.Opens) ≤ (cU D).ι ⁻¹ᵁ (W₃ : X.Opens) →
        openFormsMap (cU D) f p (ratForm ((cU D).ι ≫ f) p O
            ((((cU D).ι ≫ f).relativeDifferentialForms (p : ℤ)).presheaf.map
              (homOfLE hO).op θ)) =
          ∑ i, X.germToFunctionField _ (g i) • ∑ K, X.germToFunctionField W₃ (c i K) •
            exteriorPower.ιMulti X.functionField p
              fun l => chartForm f WD t r (K.1.orderEmbOfFin K.2 l) := by
  classical
  obtain ⟨W'', hW'', hxW'', hrep⟩ := (cond_iff n f D hD S M p W θ).1 hθ x hx
  obtain ⟨WD, Vb, e, t, hxWD, hb, r, hr, j, hj, hjD, hDW⟩ := hD.2 x
  obtain ⟨W₃, hxW₃, hW₃⟩ := G1.exists_affineOpens_le (X := X)
    (show x ∈ (W'' : X.Opens) ⊓ WD from ⟨hxW'', hxWD⟩)
  have h₃'' : (W₃ : X.Opens) ≤ W'' := hW₃.trans inf_le_left
  have h₃D : (W₃ : X.Opens) ≤ WD := hW₃.trans inf_le_right
  obtain ⟨m, g, η, hg, hη, heq⟩ := LocalRep.restrict n f D hD S M h₃'' hrep
  -- the inverses of the equations of the components on `U`
  have hu : ∀ i : Fin r, IsUnit ((cU D).ι.app WD (t (Fin.castLE hr i))) := fun i =>
    B1.isUnit_res_of_ideal_eq D (hjD i).1 (hjD i).2.2
  set s : Fin r → Γ((cU D).toScheme, (cU D).ι ⁻¹ᵁ (WD : X.Opens)) := fun i => ↑(hu i).unit⁻¹
  have hs : ∀ i, s i * (cU D).ι.app WD (t (Fin.castLE hr i)) = 1 := fun i => (hu i).val_inv_mul
  set θD : Fin n → (TB ((cU D).ι ≫ f)).Total (op ((cU D).ι ⁻¹ᵁ (WD : X.Opens))) := fun i =>
    if h : (i : ℕ) < r then
      sm ((cU D).ι ≫ f) _ (s ⟨i, h⟩) * δ ((cU D).ι ≫ f) _ ((cU D).ι.app WD (t i))
    else δ ((cU D).ι ≫ f) _ ((cU D).ι.app WD (t i)) with hθD
  obtain ⟨-, hiff, -, -⟩ := (MMP.Mori.Divisor.relativeLogForms_free_and_deRhamD_mem n f D hD).2
    x WD Vb e t hxWD hb r hr j hj hjD hDW s hs p W₃ h₃D
  have hc : ∀ i, ∃ c : {K : Finset (Fin n) // K.card = p} → Γ(X, W₃),
      (∀ K, c K ∈ S.suppIdeal.ideal W₃) ∧
      (TB ((cU D).ι ≫ f)).incl (p : ℤ) (η i) =
        ∑ K, sm ((cU D).ι ≫ f) _ (((cU D).ι.app W₃).hom (c K)) *
          ((K.1.sort (· ≤ ·)).map fun l =>
            (TB ((cU D).ι ≫ f)).totalRestrict
              ((Opens.map (cU D).ι.base).map (homOfLE h₃D)).op (θD l)).prod := fun i =>
    (hiff S.suppIdeal (η i)).1 (hη i)
  choose c hcI hcE using hc
  refine ⟨W₃, hxW₃, h₃''.trans hW'', WD, hxWD, t, r, hr, j, h₃D,
    fun i => ⟨(hjD i).1, (hjD i).2.1⟩, m, g, c, hg, hcI, ?_⟩
  have : Nonempty (WD : X.Opens) := ⟨⟨x, hxWD⟩⟩
  have : Nonempty (W₃ : X.Opens) := ⟨⟨x, hxW₃⟩⟩
  have := nonempty_inf_cU' D M (W := (W₃ : X.Opens)) ⟨⟨x, hxW₃⟩⟩
  let := MMP.Mori.functionFieldAlgebra f
  let := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
  intro O hO _ hO₃
  have hOO : (O : (cU D).toScheme.Opens) ≤ OO D M W₃ := fun z hz => ⟨hO₃ hz, (hO hz).2⟩
  have : Nonempty (OO D M W₃) := by
    obtain ⟨⟨z, hz⟩⟩ := ‹Nonempty (O : (cU D).toScheme.Opens)›
    exact ⟨⟨z, hOO hz⟩⟩
  -- the restriction of `θ` to `O` through `U ∩ W₃ ∩ U'`
  set ω₃ : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.obj
      (op (OO D M W₃)) :=
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.map
    (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_inf_right (cU' D M) h₃''))).op
    (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.map
      (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_inf_right (cU' D M) hW''))).op θ) with hω₃
  have hθO : (((cU D).ι ≫ f).relativeDifferentialForms (p : ℤ)).presheaf.map (homOfLE hO).op θ =
      (((cU D).ι ≫ f).relativeDifferentialForms (p : ℤ)).presheaf.map (homOfLE hOO).op ω₃ := by
    rw [hω₃]
    exact ((forms_map_map ((cU D).ι ≫ f) p _ _ _).trans
      (forms_map_map ((cU D).ι ≫ f) p _ _ θ)).symm
  -- the rational form of `θ` on `O` is `∑ᵢ gᵢ ηᵢ`
  have hsum : ratForm ((cU D).ι ≫ f) p O
      ((((cU D).ι ≫ f).relativeDifferentialForms (p : ℤ)).presheaf.map (homOfLE hO).op θ) =
      ∑ i, (cU D).toScheme.germToFunctionField O
        ((cU D).toScheme.presheaf.map (homOfLE hOO).op
          ((cU D).ι.app ((W₃ : X.Opens) ⊓ cU' D M) (g i))) •
        ratForm ((cU D).ι ≫ f) p O
          ((((cU D).ι ≫ f).relativeDifferentialForms (p : ℤ)).presheaf.map (homOfLE hO₃).op
            (η i)) := by
    apply Subtype.ext
    have h1 := ratTotal_totalRestrict_sum ((cU D).ι ≫ f) hOO Finset.univ
      (fun i => (cU D).ι.app ((W₃ : X.Opens) ⊓ cU' D M) (g i))
      (fun i => (TB ((cU D).ι ≫ f)).incl (p : ℤ)
        (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.map
          (homOfLE (Scheme.Hom.preimage_mono _ inf_le_left)).op (η i)))
      (fun i => [i]) (fun i => by
        erw [← incl_map]
        exact incl_mem_nonnegForms _ _ _ _)
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h1
    have h2 : ratTotal ((cU D).ι ≫ f) O ((TB ((cU D).ι ≫ f)).totalRestrict (homOfLE hOO).op
        ((TB ((cU D).ι ≫ f)).incl (p : ℤ) ω₃)) =
        (ratForm ((cU D).ι ≫ f) p O
          ((((cU D).ι ≫ f).relativeDifferentialForms (p : ℤ)).presheaf.map
            (homOfLE hO).op θ) : _) := by
      rw [hθO, ← incl_map f D (homOfLE hOO).op (p : ℤ) ω₃]
      have h3 := ratTotal_incl ((cU D).ι ≫ f) O p
        (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.map
          (homOfLE hOO).op ω₃)
      rw [piece_map_eq_presheaf_map] at h3
      exact h3
    rw [← h2]
    refine (congrArg (fun z => ratTotal ((cU D).ι ≫ f) O
      ((TB ((cU D).ι ≫ f)).totalRestrict (homOfLE hOO).op z)) heq).trans (h1.trans ?_)
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, Algebra.smul_def]
    refine congrArg (algebraMap _ _ _ * ·) ?_
    refine (congrArg (ratTotal ((cU D).ι ≫ f) O) (incl_map f D (homOfLE hOO).op (p : ℤ)
      (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.map
        (homOfLE (Scheme.Hom.preimage_mono _ inf_le_left)).op (η i))).symm).trans ?_
    have h3 := ratTotal_incl ((cU D).ι ≫ f) O p
      (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.map
        (homOfLE hOO).op
        (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.map
          (homOfLE (Scheme.Hom.preimage_mono _ inf_le_left)).op (η i)))
    refine h3.trans ?_
    exact congrArg (fun w => ((ratForm ((cU D).ι ≫ f) p O w :
        ⋀[(cU D).toScheme.functionField]^p Ω[(cU D).toScheme.functionField⁄k]) :
        ExteriorAlgebra (cU D).toScheme.functionField Ω[(cU D).toScheme.functionField⁄k]))
      (forms_map_map ((cU D).ι ≫ f) p _ _ (η i))
  rw [hsum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [openFormsMap_smul, germToFunctionField_map hOO, openFunctionFieldEquiv_germ]
  congr 1
  exact openFormsMap_ratForm_eq_sum f D WD t hr s hs θD hθD p W₃ h₃D (c i) (η i) (hcE i) O hO₃

end MMP.FourfoldProofs.FractionalLogComplexProof
