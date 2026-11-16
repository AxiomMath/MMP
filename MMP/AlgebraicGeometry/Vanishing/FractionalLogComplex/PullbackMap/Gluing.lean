module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.PullbackMap.ChartCoefficients
public import MMP.AlgebraicGeometry.DeRham.RationalForms.OpenSubscheme
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.ChartHomogeneity

/-!
# Twisted logarithmic forms with a prescribed rational form

Let `S` be a relative simple normal crossing divisor on a normal integral scheme `Y` smooth over
`k`, `O ⊆ Y` an open, and `β` a rational `p`-form which, at every prime divisor `E` meeting `O`,
lies in the wedges of the regular lattice of `𝒪_{Y,E}` and, when `E` is a component of `S`, in
the maximal ideal times the wedges of the logarithmic lattice. Then `β` is the rational form of a
section of `Ω^p_Y(log S)(-S)` over `O`: on the charts of `S` it is a combination of the chart basis
with coefficients in the ideal of `S`
(`MMP.FourfoldProofs.FractionalLogComplexProof.exists_chart_coeffs_of_le`), these local combinations are
twisted logarithmic forms, and, having the same rational form, they glue on `O ∖ S`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_local_relativeLogForm_of_le`: the local forms
  of `Ω^p_Y(log D)(-S)` for `S` with support in `D`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_local_relativeLogForm`: the local forms.
* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_relativeLogForm_of_forall_primeDivisor`: the
  glued form.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite KaehlerDifferential TopologicalSpace IsLocalRing

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology

universe u

variable {k : Type u} [Field k] {Y : Scheme.{u}}

/-- **Local sections of `Ω^p_Y(log D)(-S)` with rational form `β`.** If every component of `S`
is a component of the relative SNC divisor `D` and `β` satisfies the lattice conditions at every
prime divisor meeting `O`, then every `x ∈ O` has an affine neighbourhood `W' ≤ O` carrying a
section of `Ω^p_Y(log D)(-S)` with rational form `β`. -/
theorem exists_local_relativeLogForm_of_le [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (n : ℕ) (f : Y ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f] (D S : MMP.Mori.Divisor Y)
    (hD : D.IsRelativeSNC n f) (hSD : ∀ E ∈ S.support, E ∈ D.support) [Nonempty (cU D)]
    (p : ℕ) (O : Y.Opens)
    (β : letI := MMP.Mori.functionFieldAlgebra f; ⋀[Y.functionField]^p Ω[Y.functionField⁄k])
    (hβ : ∀ E : MMP.Mori.PrimeDivisor Y, (E.support ∩ O).Nonempty →
      letI := MMP.Mori.functionFieldAlgebra f
      letI := MMP.Mori.stalkAlgebra f E.genericPoint
      haveI := MMP.Mori.isScalarTower_stalk_functionField f E.genericPoint
      (E ∉ D.support → β ∈ wedgeSpan E.localRing (regLattice k E.localRing) p) ∧
      (E ∈ D.support → β ∈ wedgeSpan E.localRing (logLattice k E.localRing) p) ∧
      (E ∈ S.support → β ∈ maximalIdeal E.localRing •
          wedgeSpan E.localRing (logLattice k E.localRing) p))
    {x : Y} (hx : x ∈ O) :
    ∃ (W' : Y.affineOpens), x ∈ (W' : Y.Opens) ∧ (W' : Y.Opens) ≤ O ∧
      ∃ y ∈ MMP.Mori.Divisor.relativeLogForms n f D hD S.suppIdeal p (W' : Y.Opens),
        letI := MMP.Mori.functionFieldAlgebra f
        ∀ (O' : (cU D).toScheme.affineOpens)
          (hO' : (O' : (cU D).toScheme.Opens) ≤ (cU D).ι ⁻¹ᵁ (W' : Y.Opens))
          [Nonempty (O' : (cU D).toScheme.Opens)],
          openFormsMap (cU D) f p (ratForm ((cU D).ι ≫ f) p O'
            ((((cU D).ι ≫ f).relativeDifferentialForms (p : ℤ)).presheaf.map
              (homOfLE hO').op y)) = β := by
  classical
  obtain ⟨Wc, Vb, e, t, hxWc, hb, r, hr, j, hj, hjD, hDW⟩ := hD.2 x
  obtain ⟨W', hxW', hW'⟩ := G1.exists_affineOpens_le (X := Y)
    (show x ∈ (Wc : Y.Opens) ⊓ O from ⟨hxWc, hx⟩)
  have hW'c : (W' : Y.Opens) ≤ Wc := hW'.trans inf_le_left
  have : Nonempty (Wc : Y.Opens) := ⟨⟨x, hxWc⟩⟩
  have : Nonempty (W' : Y.Opens) := ⟨⟨x, hxW'⟩⟩
  -- the coefficients in the chart basis
  obtain ⟨c, hcI, hcβ⟩ := exists_chart_coeffs_of_le f D S hSD Wc Vb e t hb hr j
    (fun i => (hjD i).2.2) hDW W' hW'c p β fun E hE =>
      hβ E (hE.mono fun _ h => ⟨h.1, (hW'.trans inf_le_right) h.2⟩)
  -- the chart basis on `Y ∖ D`
  have hu : ∀ i : Fin r, IsUnit ((cU D).ι.app Wc (t (Fin.castLE hr i))) := fun i =>
    B1.isUnit_res_of_ideal_eq D (hjD i).1 (hjD i).2.2
  set s : Fin r → Γ((cU D).toScheme, (cU D).ι ⁻¹ᵁ (Wc : Y.Opens)) := fun i => ↑(hu i).unit⁻¹
  have hs : ∀ i, s i * (cU D).ι.app Wc (t (Fin.castLE hr i)) = 1 := fun i => (hu i).val_inv_mul
  set θS : Fin n → (TB ((cU D).ι ≫ f)).Total (op ((cU D).ι ⁻¹ᵁ (Wc : Y.Opens))) := fun i =>
    if h : (i : ℕ) < r then
      sm ((cU D).ι ≫ f) _ (s ⟨i, h⟩) * δ ((cU D).ι ≫ f) _ ((cU D).ι.app Wc (t i))
    else δ ((cU D).ι ≫ f) _ ((cU D).ι.app Wc (t i)) with hθS
  -- the combination `∑_K c_K θ_K` is a form
  obtain ⟨y, hy⟩ := exists_incl_eq_sum_sm_mul_prod ((cU D).ι ≫ f)
    (O := (cU D).ι ⁻¹ᵁ (W' : Y.Opens))
    (fun i => (TB ((cU D).ι ≫ f)).totalRestrict
      ((Opens.map (cU D).ι.base).map (homOfLE hW'c)).op (θS i))
    (fun i => by
      rw [hθS]
      by_cases h : (i : ℕ) < r
      · refine ⟨(cU D).toScheme.presheaf.map ((Opens.map (cU D).ι.base).map (homOfLE hW'c)).op
            (s ⟨i, h⟩),
          (cU D).toScheme.presheaf.map ((Opens.map (cU D).ι.base).map (homOfLE hW'c)).op
            ((cU D).ι.app Wc (t i)), ?_⟩
        simp only [h, dite_true]
        rw [Stacks.GradedAlgebra.totalRestrict_mul, totalRestrict_sm, totalRestrict_δ]
      · refine ⟨1, (cU D).toScheme.presheaf.map ((Opens.map (cU D).ι.base).map (homOfLE hW'c)).op
            ((cU D).ι.app Wc (t i)), ?_⟩
        simp only [h, dite_false]
        rw [totalRestrict_δ, map_one, one_mul])
    Finset.univ (fun K => ((cU D).ι.app W').hom (c K)) (fun K => K.1.sort (· ≤ ·)) p
    (fun K _ => by rw [Finset.length_sort, K.2])
  refine ⟨W', hxW', hW'.trans inf_le_right, y, ?_, fun O' hO' _ => ?_⟩
  · exact mem_relativeLogForms_of_ratTotal_eq n f D hD x Wc Vb e t hxWc hb r hr j hj hjD hDW s hs
      θS hθS p W' hW'c S.suppIdeal y c hcI fun O hO _ => by rw [hy]
  · rw [openFormsMap_ratForm_eq_sum f D Wc t hr s hs θS hθS p W' hW'c c y hy O' hO', hcβ]

/-- **Local twisted logarithmic forms with rational form `β`.** If `β` lies in the wedges of the
regular lattice at every prime divisor meeting `O`, and in the maximal ideal times the wedges of
the logarithmic lattice along the components of `S`, then every `x ∈ O` has an affine
neighbourhood `W' ≤ O` carrying a section of `Ω^p_Y(log S)(-S)` with rational form `β`. -/
theorem exists_local_relativeLogForm [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (n : ℕ) (f : Y ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f] (S : MMP.Mori.Divisor Y)
    (hS : S.IsRelativeSNC n f) [Nonempty (cU S)] (p : ℕ) (O : Y.Opens)
    (β : letI := MMP.Mori.functionFieldAlgebra f; ⋀[Y.functionField]^p Ω[Y.functionField⁄k])
    (hβ : ∀ E : MMP.Mori.PrimeDivisor Y, (E.support ∩ O).Nonempty →
      letI := MMP.Mori.functionFieldAlgebra f
      letI := MMP.Mori.stalkAlgebra f E.genericPoint
      haveI := MMP.Mori.isScalarTower_stalk_functionField f E.genericPoint
      β ∈ wedgeSpan E.localRing (regLattice k E.localRing) p ∧
        (E ∈ S.support → β ∈ maximalIdeal E.localRing •
          wedgeSpan E.localRing (logLattice k E.localRing) p))
    {x : Y} (hx : x ∈ O) :
    ∃ (W' : Y.affineOpens), x ∈ (W' : Y.Opens) ∧ (W' : Y.Opens) ≤ O ∧
      ∃ y ∈ MMP.Mori.Divisor.relativeLogForms n f S hS S.suppIdeal p (W' : Y.Opens),
        letI := MMP.Mori.functionFieldAlgebra f
        ∀ (O' : (cU S).toScheme.affineOpens)
          (hO' : (O' : (cU S).toScheme.Opens) ≤ (cU S).ι ⁻¹ᵁ (W' : Y.Opens))
          [Nonempty (O' : (cU S).toScheme.Opens)],
          openFormsMap (cU S) f p (ratForm ((cU S).ι ≫ f) p O'
            ((((cU S).ι ≫ f).relativeDifferentialForms (p : ℤ)).presheaf.map
              (homOfLE hO').op y)) = β :=
  exists_local_relativeLogForm_of_le n f S S hS (fun _ h => h) p O β (fun E hE =>
    ⟨fun _ => (hβ E hE).1, fun h => Submodule.smul_le_right ((hβ E hE).2 h), (hβ E hE).2⟩) hx

/-- **A twisted logarithmic form with a prescribed rational form.** A rational `p`-form `β`
which, at every prime divisor `E` meeting the open `O`, lies in the wedges of the regular lattice
and, along the components of `S`, in the maximal ideal times the wedges of the logarithmic lattice,
is the rational form of a section of `Ω^p_Y(log S)(-S)` over `O`. -/
theorem exists_relativeLogForm_of_forall_primeDivisor [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (n : ℕ) (f : Y ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
    (S : MMP.Mori.Divisor Y) (hS : S.IsRelativeSNC n f) [Nonempty (cU S)] (p : ℕ) (O : Y.Opens)
    (β : letI := MMP.Mori.functionFieldAlgebra f; ⋀[Y.functionField]^p Ω[Y.functionField⁄k])
    (hβ : ∀ E : MMP.Mori.PrimeDivisor Y, (E.support ∩ O).Nonempty →
      letI := MMP.Mori.functionFieldAlgebra f
      letI := MMP.Mori.stalkAlgebra f E.genericPoint
      haveI := MMP.Mori.isScalarTower_stalk_functionField f E.genericPoint
      β ∈ wedgeSpan E.localRing (regLattice k E.localRing) p ∧
        (E ∈ S.support → β ∈ maximalIdeal E.localRing •
          wedgeSpan E.localRing (logLattice k E.localRing) p)) :
    ∃ θ' ∈ MMP.Mori.Divisor.relativeLogForms n f S hS S.suppIdeal p O,
      letI := MMP.Mori.functionFieldAlgebra f
      ∀ (O' : (cU S).toScheme.affineOpens)
        (hO' : (O' : (cU S).toScheme.Opens) ≤ (cU S).ι ⁻¹ᵁ O)
        [Nonempty (O' : (cU S).toScheme.Opens)],
        openFormsMap (cU S) f p (ratForm ((cU S).ι ≫ f) p O'
          ((((cU S).ι ≫ f).relativeDifferentialForms (p : ℤ)).presheaf.map
            (homOfLE hO').op θ')) = β := by
  classical
  let := MMP.Mori.functionFieldAlgebra f
  have : SmoothOfRelativeDimension n ((cU S).ι ≫ f) := by
    have h := (inferInstance : SmoothOfRelativeDimension (0 + n) ((cU S).ι ≫ f))
    rwa [zero_add] at h
  obtain ⟨β', hβ'⟩ := (openFormsMap_bijective (cU S) f p).2 β
  have hinj := (openFormsMap_bijective (cU S) f p).1
  choose W' hxW' hW'O y hy hyβ using fun x (hx : x ∈ O) =>
    exists_local_relativeLogForm n f S hS p O β hβ hx
  -- the local forms on `O ∖ S` have rational form `β'`
  have hglue : ∀ u ∈ (cU S).ι ⁻¹ᵁ O, ∃ Wa : (cU S).toScheme.affineOpens,
      u ∈ (Wa : (cU S).toScheme.Opens) ∧ (Wa : (cU S).toScheme.Opens) ≤ (cU S).ι ⁻¹ᵁ O ∧
      ∃ ω : Γ(((cU S).ι ≫ f).relativeDifferentialForms (p : ℤ), Wa),
        ∀ _ : Nonempty (Wa : (cU S).toScheme.Opens), ratForm ((cU S).ι ≫ f) p Wa ω = β' := by
    intro u hu
    set x : Y := (cU S).ι u
    have hx : x ∈ O := hu
    obtain ⟨_, ⟨Wa, hWa, rfl⟩, huWa, hle⟩ :=
      (cU S).toScheme.isBasis_affineOpens.exists_subset_of_mem_open
        (show u ∈ (cU S).ι ⁻¹ᵁ (W' x hx : Y.Opens) from hxW' x hx)
        ((cU S).ι ⁻¹ᵁ (W' x hx : Y.Opens)).isOpen
    let Wa' : (cU S).toScheme.affineOpens := ⟨Wa, hWa⟩
    have hle' : (Wa' : (cU S).toScheme.Opens) ≤ (cU S).ι ⁻¹ᵁ (W' x hx : Y.Opens) := hle
    refine ⟨Wa', huWa, hle'.trans (Scheme.Hom.preimage_mono _ (hW'O x hx)),
      (((cU S).ι ≫ f).relativeDifferentialForms (p : ℤ)).presheaf.map (homOfLE hle').op
        (y x hx), fun _ => hinj ?_⟩
    rw [hβ']
    exact hyβ x hx Wa' hle'
  obtain ⟨θ', hθ'⟩ := exists_form_of_forall_ratForm_eq ((cU S).ι ≫ f) (m := n) p β' hglue
  refine ⟨θ', ?_, fun O' hO' _ => by rw [hθ' O' hO', hβ']⟩
  -- near every point, `θ'` is a local twisted logarithmic form
  refine G1.relativeLogForms_of_local n f S hS S.suppIdeal p fun x hx => ⟨W' x hx, hW'O x hx,
    hxW' x hx, ?_⟩
  have e : G1.rs f S p (hW'O x hx) θ' = y x hx := by
    refine eq_of_ratForm_eq ((cU S).ι ≫ f) (m := n) p _ _ fun Wa hWa _ => hinj ?_
    rw [hyβ x hx Wa hWa, ← hβ', ← hθ' Wa (hWa.trans (Scheme.Hom.preimage_mono _ (hW'O x hx)))]
    exact congrArg (fun w => openFormsMap (cU S) f p (ratForm ((cU S).ι ≫ f) p Wa w))
      (forms_map_map ((cU S).ι ≫ f) p _ _ θ')
  rw [e]
  exact hy x hx

end MMP.FourfoldProofs.FractionalLogComplexProof
