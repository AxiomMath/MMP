module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Place.ChartLattices
public import MMP.AlgebraicGeometry.Morphisms.SmoothLocalRings
public import MMP.RingTheory.Kaehler.TraceAdaptedBasis
public import MMP.AlgebraicGeometry.DeRham.RationalForms.Gluing

/-!
# The lattice of a logarithmic form at a codimension-one point

Let `D` be a relative simple normal crossing divisor on a integral scheme `Y` smooth of
relative dimension `n` over a field `k` of characteristic zero, and `ω` a section of
`I · Ω^p_Y(log D)` over an open `W₀`. At a point `y ∈ W₀` off `D` whose local ring is a discrete
valuation ring with uniformizer `s`, the rational form of `ω`, in `k(Y)`, lies in the wedges of
the regular forms `ds, dy₁, …, dyₘ` of an adapted basis of `Ω_{𝒪_{Y,y}/k}`, with `n = m + 1`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_adapted_mem_wedgeSpan_regular`: off the
  divisor, at a point whose maximal ideal is `(s)`: the rational form lies in the wedges of the
  regular forms `ds, dy₁, …, dyₘ`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_adapted_eq_smul_log`: at the generic point of a
  component, for a section of `Ω^p_Y(log D)(-D)`: `s η` with `η` in the wedges of the logarithmic
  forms `s⁻¹ ds, dy₁, …, dyₘ`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite KaehlerDifferential TopologicalSpace IsLocalRing

namespace MMP.FourfoldProofs.FractionalLogComplexProof

universe u

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}

/-- **The regular lattice at a codimension-one point off the divisor.** At a point `y ∈ W₀` off
`D` whose stalk has maximal ideal `(s)`, `s ≠ 0`, the rational form of a section `ω` of
`I · Ω^p(log D)` over `W₀` lies in the `p`-th wedges of `ds, dy₁, …, dyₘ`, the images of an
adapted basis of `Ω_{𝒪_{Y,y}/k}`, with `n = m + 1`. -/
theorem exists_adapted_mem_wedgeSpan_regular [IsIntegral Y]
    (n : ℕ) (f : Y ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f] (D : MMP.Mori.Divisor Y)
    (hD : D.IsRelativeSNC n f) [Nonempty (cU D)] (I : Y.IdealSheafData) (p : ℕ) {W₀ : Y.Opens}
    {ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.obj
      (op ((cU D).ι ⁻¹ᵁ W₀))}
    (hω : ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I p W₀)
    (O : (cU D).toScheme.affineOpens) (hO : (O : (cU D).toScheme.Opens) ≤ (cU D).ι ⁻¹ᵁ W₀)
    [Nonempty (O : (cU D).toScheme.Opens)] {y : Y} (hyW₀ : y ∈ W₀)
    (hDy : ∀ F ∈ D.support, y ∉ F.support) {s : Y.presheaf.stalk y}
    (hmR : maximalIdeal (Y.presheaf.stalk y) = Ideal.span {s}) (hs : s ≠ 0) :
    letI := MMP.Mori.functionFieldAlgebra f
    letI := MMP.Mori.stalkAlgebra f y
    haveI := MMP.Mori.isScalarTower_stalk_functionField f y
    ∃ (m : ℕ) (_ : n = m + 1) (yv : Fin m → Y.presheaf.stalk y)
      (bR : Module.Basis (Fin (m + 1)) (Y.presheaf.stalk y) Ω[Y.presheaf.stalk y⁄k]),
      (∀ i, bR i = KaehlerDifferential.D k (Y.presheaf.stalk y)
        ((Fin.cons s yv : Fin (m + 1) → Y.presheaf.stalk y) i))
      ∧ openFormsMap (cU D) f p (ratForm ((cU D).ι ≫ f) p O
          ((((cU D).ι ≫ f).relativeDifferentialForms (p : ℤ)).presheaf.map (homOfLE hO).op ω)) ∈
        wedgeSpan (Y.presheaf.stalk y) (Submodule.span (Y.presheaf.stalk y)
          (Set.range fun j => KaehlerDifferential.D k Y.functionField
            (algebraMap (Y.presheaf.stalk y) Y.functionField
              ((Fin.cons s yv : Fin (m + 1) → Y.presheaf.stalk y) j)))) p := by
  classical
  let := MMP.Mori.functionFieldAlgebra f
  let := MMP.Mori.stalkAlgebra f y
  have := MMP.Mori.isScalarTower_stalk_functionField f y
  have : SmoothOfRelativeDimension n ((cU D).ι ≫ f) := by
    have h := (inferInstance : SmoothOfRelativeDimension (0 + n) ((cU D).ι ≫ f))
    rwa [zero_add] at h
  obtain ⟨Wc, Vb, e, t, hyc, hb, r, hr, j, hj, hjD, hDW⟩ := hD.2 y
  obtain ⟨W'', hyW'', hW''⟩ := G1.exists_affineOpens_le (X := Y)
    (show y ∈ (Wc : Y.Opens) ⊓ W₀ from ⟨hyc, hyW₀⟩)
  have hW''c : (W'' : Y.Opens) ≤ Wc := hW''.trans inf_le_left
  have hW''₀ : (W'' : Y.Opens) ≤ W₀ := hW''.trans inf_le_right
  have hω'' := G1.relativeLogForms_restrict n f D hD I (p : ℤ) hW''₀ hω
  let s' : Fin r → Γ((cU D).toScheme, (cU D).ι ⁻¹ᵁ (Wc : Y.Opens)) := fun i =>
    ((B1.isUnit_res_of_ideal_eq D (hjD i).1 (hjD i).2.2).unit⁻¹ :
      (Γ((cU D).toScheme, (cU D).ι ⁻¹ᵁ (Wc : Y.Opens)))ˣ).val
  have hs' : ∀ i, s' i * (cU D).ι.app Wc (t (Fin.castLE hr i)) = 1 := fun i =>
    (B1.isUnit_res_of_ideal_eq D (hjD i).1 (hjD i).2.2).val_inv_mul
  obtain ⟨-, hiff, -, -⟩ := (MMP.Mori.Divisor.relativeLogForms_free_and_deRhamD_mem n f D hD).2 y
    Wc Vb e t hyc hb r hr j hj hjD hDW s' hs' p W'' hW''c
  obtain ⟨c, -, hcombo⟩ := (hiff I _).1 hω''
  obtain ⟨⟨u₀, hu₀⟩⟩ := ‹Nonempty (cU D)›
  obtain ⟨z, hzW, hzU⟩ : ((W'' : Y.Opens) ⊓ cU D : Y.Opens).1.Nonempty :=
    nonempty_preirreducible_inter (W'' : Y.Opens).isOpen (cU D).isOpen ⟨y, hyW''⟩ ⟨u₀, hu₀⟩
  let z' : (cU D).toScheme := ⟨z, hzU⟩
  obtain ⟨O'', hzO'', hO''⟩ := G1.exists_affineOpens_le (X := (cU D).toScheme)
    (show z' ∈ (cU D).ι ⁻¹ᵁ (W'' : Y.Opens) from hzW)
  have : Nonempty (O'' : (cU D).toScheme.Opens) := ⟨⟨z', hzO''⟩⟩
  obtain ⟨b0, -⟩ := exists_basis_D_stalk_of_chart f Wc Vb e t hb hyc
  have hreg := openFormsMap_ratForm_mem_wedgeSpan_regular f D Wc t hr j (fun i => (hjD i).2.2) s'
    hs' _ rfl p W'' hW''c c _ hcombo O'' hO'' hyW'' (fun i => hDy _ (hjD i).1) b0
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have := essFiniteType_stalkAlgebra f y
  obtain ⟨hfs, -, -⟩ := formallySmooth_free_finite_stalk f (m := n) y
  obtain ⟨m, yv, c', hc'⟩ := exists_basis_D_cons k b0 hmR hs
  have hnm : n = m + 1 := by simpa using Fintype.card_congr (b0.indexEquiv c')
  refine ⟨m, hnm, yv, c', hc', ?_⟩
  have hspan : Submodule.span (Y.presheaf.stalk y)
      (Set.range (KaehlerDifferential.map k k (Y.presheaf.stalk y) Y.functionField ∘ b0)) =
      Submodule.span (Y.presheaf.stalk y) (Set.range fun j' => KaehlerDifferential.D k
        Y.functionField (algebraMap (Y.presheaf.stalk y) Y.functionField
          ((Fin.cons s yv : Fin (m + 1) → Y.presheaf.stalk y) j'))) := by
    rw [span_map_basis_eq k b0 c']
    congr 2
    funext j'
    rw [Function.comp_apply, hc', KaehlerDifferential.map_D]
  rw [← hspan]
  have hO''₀ : (O'' : (cU D).toScheme.Opens) ≤ (cU D).ι ⁻¹ᵁ W₀ :=
    hO''.trans (Scheme.Hom.preimage_mono _ hW''₀)
  rw [ratForm_eq_of_le ((cU D).ι ≫ f) p ω hO hO''₀]
  convert hreg using 4
  exact (forms_map_map ((cU D).ι ≫ f) p (Scheme.Hom.preimage_mono _ hW''₀) hO'' ω).symm

omit [CharZero k] in
/-- **The twisted logarithmic lattice at the generic point of a component.** At the generic
point of a component `E'` of `D` lying in `W₀`, the stalk has maximal ideal `(s)`, and the rational
form of a section of `Ω^p(log D)(-D)` over `W₀` is `s • η` with `η` in the `p`-th wedges of the
logarithmic forms `s⁻¹ ds, dy₁, …, dyₘ`, where `n = m + 1`. -/
theorem exists_adapted_eq_smul_log [IsIntegral Y]
    (n : ℕ) (f : Y ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f] (D : MMP.Mori.Divisor Y)
    (hD : D.IsRelativeSNC n f) [Nonempty (cU D)] (p : ℕ) {W₀ : Y.Opens}
    {ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.obj
      (op ((cU D).ι ⁻¹ᵁ W₀))}
    (hω : ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD D.suppIdeal p W₀)
    (O : (cU D).toScheme.affineOpens) (hO : (O : (cU D).toScheme.Opens) ≤ (cU D).ι ⁻¹ᵁ W₀)
    [Nonempty (O : (cU D).toScheme.Opens)] {E' : MMP.Mori.PrimeDivisor Y} (hE' : E' ∈ D.support)
    (hE'W₀ : E'.genericPoint ∈ W₀) :
    letI := MMP.Mori.functionFieldAlgebra f
    letI := MMP.Mori.stalkAlgebra f E'.genericPoint
    haveI := MMP.Mori.isScalarTower_stalk_functionField f E'.genericPoint
    ∃ (s : Y.presheaf.stalk E'.genericPoint)
      (_ : maximalIdeal (Y.presheaf.stalk E'.genericPoint) = Ideal.span {s})
      (m : ℕ) (_ : n = m + 1) (yv : Fin m → Y.presheaf.stalk E'.genericPoint)
      (bR : Module.Basis (Fin (m + 1)) (Y.presheaf.stalk E'.genericPoint)
        Ω[Y.presheaf.stalk E'.genericPoint⁄k]),
      (∀ i, bR i = KaehlerDifferential.D k (Y.presheaf.stalk E'.genericPoint)
        ((Fin.cons s yv : Fin (m + 1) → Y.presheaf.stalk E'.genericPoint) i)) ∧
      ∃ η ∈ wedgeSpan (Y.presheaf.stalk E'.genericPoint)
          (Submodule.span (Y.presheaf.stalk E'.genericPoint) (Set.range (Fin.cons
            ((algebraMap (Y.presheaf.stalk E'.genericPoint) Y.functionField s)⁻¹ •
              KaehlerDifferential.D k Y.functionField
                (algebraMap (Y.presheaf.stalk E'.genericPoint) Y.functionField s))
            fun l => KaehlerDifferential.D k Y.functionField
              (algebraMap (Y.presheaf.stalk E'.genericPoint) Y.functionField (yv l))
            : Fin (m + 1) → Ω[Y.functionField⁄k]))) p,
        openFormsMap (cU D) f p (ratForm ((cU D).ι ≫ f) p O
            ((((cU D).ι ≫ f).relativeDifferentialForms (p : ℤ)).presheaf.map (homOfLE hO).op ω)) =
          algebraMap (Y.presheaf.stalk E'.genericPoint) Y.functionField s • η := by
  classical
  let := MMP.Mori.functionFieldAlgebra f
  have : SmoothOfRelativeDimension n ((cU D).ι ≫ f) := by
    have h := (inferInstance : SmoothOfRelativeDimension (0 + n) ((cU D).ι ≫ f))
    rwa [zero_add] at h
  obtain ⟨Wc, Vb, e, t, hyc, hb, r, hr, j, hj, hjD, hDW⟩ := hD.2 E'.genericPoint
  have hηE' : E'.genericPoint ∈ E'.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  obtain ⟨i₀, hi₀⟩ := exists_eq_of_mem_chart t hr j (fun i => (hjD i).2.2) hDW hE' hyc hηE'
  have hother : ∀ i, i ≠ i₀ → E'.genericPoint ∉ (j i).support := fun i hi h =>
    hi (hj ((eq_of_genericPoint_mem_support h).symm.trans hi₀.symm))
  subst hi₀
  obtain ⟨W'', hyW'', hW''⟩ := G1.exists_affineOpens_le (X := Y)
    (show (j i₀).genericPoint ∈ (Wc : Y.Opens) ⊓ W₀ from ⟨hyc, hE'W₀⟩)
  have hW''c : (W'' : Y.Opens) ≤ Wc := hW''.trans inf_le_left
  have hW''₀ : (W'' : Y.Opens) ≤ W₀ := hW''.trans inf_le_right
  have hω'' := G1.relativeLogForms_restrict n f D hD D.suppIdeal (p : ℤ) hW''₀ hω
  let s' : Fin r → Γ((cU D).toScheme, (cU D).ι ⁻¹ᵁ (Wc : Y.Opens)) := fun i =>
    ((B1.isUnit_res_of_ideal_eq D (hjD i).1 (hjD i).2.2).unit⁻¹ :
      (Γ((cU D).toScheme, (cU D).ι ⁻¹ᵁ (Wc : Y.Opens)))ˣ).val
  have hs' : ∀ i, s' i * (cU D).ι.app Wc (t (Fin.castLE hr i)) = 1 := fun i =>
    (B1.isUnit_res_of_ideal_eq D (hjD i).1 (hjD i).2.2).val_inv_mul
  obtain ⟨-, hiff, -, -⟩ := (MMP.Mori.Divisor.relativeLogForms_free_and_deRhamD_mem n f D hD).2
    (j i₀).genericPoint Wc Vb e t hyc hb r hr j hj hjD hDW s' hs' p W'' hW''c
  obtain ⟨c, hc, hcombo⟩ := (hiff D.suppIdeal _).1 hω''
  obtain ⟨⟨u₀, hu₀⟩⟩ := ‹Nonempty (cU D)›
  obtain ⟨z, hzW, hzU⟩ : ((W'' : Y.Opens) ⊓ cU D : Y.Opens).1.Nonempty :=
    nonempty_preirreducible_inter (W'' : Y.Opens).isOpen (cU D).isOpen ⟨_, hyW''⟩ ⟨u₀, hu₀⟩
  let z' : (cU D).toScheme := ⟨z, hzU⟩
  obtain ⟨O'', hzO'', hO''⟩ := G1.exists_affineOpens_le (X := (cU D).toScheme)
    (show z' ∈ (cU D).ι ⁻¹ᵁ (W'' : Y.Opens) from hzW)
  have : Nonempty (O'' : (cU D).toScheme.Opens) := ⟨⟨z', hzO''⟩⟩
  obtain ⟨m, yv, bR, hbR, η, hη, heq⟩ := exists_openFormsMap_ratForm_eq_smul_log f D Wc Vb e t hb hr
    j (fun i => (hjD i).2.2) hDW s' hs' _ rfl p W'' hW''c c hc _ hcombo O'' hO'' hyW'' i₀ hother
  obtain ⟨b0, -⟩ := exists_basis_D_stalk_of_chart f Wc Vb e t hb hyc
  have hnm : n = m + 1 := by simpa using Fintype.card_congr (b0.indexEquiv bR)
  have hmR := maximalIdeal_localRing_eq_span (j i₀) Wc hyc (hjD i₀).2.2
  refine ⟨_, hmR, m, hnm, yv, bR, hbR, η, hη, ?_⟩
  have hO''₀ : (O'' : (cU D).toScheme.Opens) ≤ (cU D).ι ⁻¹ᵁ W₀ :=
    hO''.trans (Scheme.Hom.preimage_mono _ hW''₀)
  rw [ratForm_eq_of_le ((cU D).ι ≫ f) p ω hO hO''₀]
  convert heq using 3
  exact (forms_map_map ((cU D).ι ≫ f) p (Scheme.Hom.preimage_mono _ hW''₀) hO'' ω).symm

end MMP.FourfoldProofs.FractionalLogComplexProof
